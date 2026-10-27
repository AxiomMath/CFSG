module

public import CFSG.Quasithin.Background.GoldschmidtE23SymFam
public import CFSG.Quasithin.Background.GoldschmidtE23NatX
public import CFSG.Quasithin.Background.GoldschmidtE23SymAl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank G6 Equiv

namespace GE23

section Ctx

variable {V : Type} [CommGroup V] [Finite V] {X T M : Subgroup (MulAut V)}
  {Ps : Set (Subgroup (MulAut V))}

structure SymCtx (X T M : Subgroup (MulAut V)) : Prop where
  hB : B69.BlkCtx X T M
  hmp : MinParabolic X T M
  hFF : IsFFModule X
  hns : ¬ Group.IsSolvable ↥X
  hone : ¬ IsStrongFFModule X
  hk2 : ∀ {H : Subgroup (MulAut V)} {k : ℕ}, SymBlk X H k → k = 2
  hsym : ∀ L, CFSG.Open.IsComponentOf L X → SymBlk X (B69.blk X L) 2

namespace SymCtx

variable (hC : SymCtx X T M)

include hC

theorem sc : B69.StructConcl X T M (B69.blkFamily X) :=
  B69.structConcl_of_blkCtx hC.hB hC.hmp hC.hFF

theorem blk_sym {H : Subgroup (MulAut V)} (hH : H ∈ B69.blkFamily X) : SymBlk X H 2 := by
  obtain ⟨L, hL, rfl⟩ := B69.mem_blkFamily.1 hH
  exact hC.hsym L hL

theorem le_ffJ' {H : Subgroup (MulAut V)} (hH : H ∈ B69.blkFamily X) : H ≤ ffJ X := by
  rw [(hC.sc).2.1]
  exact le_iSup₂_of_le (f := fun H' (_ : H' ∈ B69.blkFamily X) => H') H hH le_rfl

theorem le_normalizer {H : Subgroup (MulAut V)} (hH : H ∈ B69.blkFamily X) :
    ffJ X ≤ Subgroup.normalizer (H : Set (MulAut V)) := by
  rw [(hC.sc).2.1]
  refine iSup₂_le fun H' hH' => ?_
  by_cases hHH : H' = H
  · subst hHH
    exact Subgroup.le_normalizer
  · intro y hy
    have hc : y ∈ Subgroup.centralizer (H : Set (MulAut V)) := by
      refine Subgroup.mem_centralizer_iff.2 fun z hz => ?_
      exact ((hC.sc).2.2.1 H' hH' H hH hHH y hy z hz).symm
    exact Subgroup.centralizer_le_normalizer (H : Set (MulAut V)) hc

theorem isSylow_inf {H : Subgroup (MulAut V)} (hH : H ∈ B69.blkFamily X) :
    IsSylowTwoOf (T ⊓ H) H := by
  have h1 : IsSylowTwoOf (T ⊓ ffJ X) (ffJ X) :=
    B6.isSylowTwoOf_inf_normal hC.hmp.isSylow (B6.ffJ_le X) (B6.le_normalizer_ffJ X)
  have h2 := B6.isSylowTwoOf_inf_normal h1 (hC.le_ffJ' hH) (hC.le_normalizer hH)
  rwa [inf_assoc, inf_eq_right.2 (hC.le_ffJ' hH)] at h2

theorem exists_spec : ∃ (ψ : Subgroup (MulAut V) → Perm (Fin 5) →* MulAut V)
    (β : Subgroup (MulAut V) → ↥(coreMod 5) →* V),
    ∀ H ∈ B69.blkFamily X, SymSpec H (T ⊓ H) (ψ H) (β H) := by
  classical
  have hex : ∀ H : Subgroup (MulAut V), ∃ (ψ : Perm (Fin 5) →* MulAut V)
      (β : ↥(coreMod 5) →* V), H ∈ B69.blkFamily X → SymSpec H (T ⊓ H) ψ β := by
    intro H
    by_cases hH : H ∈ B69.blkFamily X
    · obtain ⟨ψ, β, h⟩ := exists_symSpec hC.hB (hC.blk_sym hH) (hC.isSylow_inf hH)
      exact ⟨ψ, β, fun _ => h⟩
    · exact ⟨1, 1, fun h => absurd h hH⟩
  choose ψ β h using hex
  exact ⟨ψ, β, h⟩

end SymCtx

structure SymData (X T M : Subgroup (MulAut V)) (Ps : Set (Subgroup (MulAut V)))
    (ψ : Subgroup (MulAut V) → Perm (Fin 5) →* MulAut V)
    (β : Subgroup (MulAut V) → ↥(coreMod 5) →* V) : Prop where
  ctx : SymCtx X T M
  stable : IsStableFF T Ps
  spec : ∀ H ∈ B69.blkFamily X, SymSpec H (T ⊓ H) (ψ H) (β H)

namespace SymData

variable {ψ : Subgroup (MulAut V) → Perm (Fin 5) →* MulAut V}
  {β : Subgroup (MulAut V) → ↥(coreMod 5) →* V} (hD : SymData X T M Ps ψ β)

include hD

theorem fam : SymFam (B69.blkFamily X) ψ β where
  spec H hH := by
    have h := hD.spec H hH
    exact ⟨h.ψ_inj, h.ψ_range, h.β_inj, h.β_range, h.equiv, rfl⟩
  hcomm := (hD.ctx.sc).2.2.1
  hind := (hD.ctx.sc).2.2.2.1
  hother := fun H hH H' hH' hne y hy u hu =>
    commSub_eq_bot_iff.1 ((hD.ctx.sc).2.2.2.2.2.2.1 H hH H' hH' (Ne.symm hne)) hu y hy
  hind0 := by
    intro H hH
    refine le_bot_iff.1 ?_
    rintro v ⟨hv1, hv2⟩
    have h1 := (hD.ctx.sc).2.2.2.2.2.1 H hH
    have hvC : v ∈ fixV (ffJ X) := by
      rw [← h1]
      exact ⟨Subgroup.mem_sup_left hv1, Subgroup.mem_sup_left hv2⟩
    have : v = 1 := (hD.spec H hH).fixed_trivial hv1 fun x hx => hvC x (hD.ctx.le_ffJ' hH hx)
    rw [this]
    exact Subgroup.one_mem _
  hsplit := fun v => blocks_split hD.ctx.hB hD.ctx.hmp hD.ctx.hFF hD.ctx.hk2
    (B69.blkFamily X) (fun _ h => h) v

theorem inf_ffJ_eq : T ⊓ ffJ X = ⨆ H ∈ B69.blkFamily X, d8.map (ψ H) := by
  classical
  have hsc := hD.ctx.sc
  have hsyl : IsSylowTwoOf (⨆ H ∈ B69.blkFamily X, T ⊓ H) (ffJ X) := by
    rw [hsc.2.1]
    exact isSylowTwoOf_iSup (B69.blkFamily X) (fun H => H) (fun H => T ⊓ H)
      (fun H hH => hD.ctx.isSylow_inf hH) hsc.2.2.1 hsc.2.2.2.1
  have hT2 : IsPGroup 2 T := hD.ctx.hmp.isSylow.2.1
  have hle : (⨆ H ∈ B69.blkFamily X, T ⊓ H) ≤ T ⊓ ffJ X :=
    iSup₂_le fun H hH => le_inf inf_le_left (inf_le_right.trans (hD.ctx.le_ffJ' hH))
  have heq : T ⊓ ffJ X = ⨆ H ∈ B69.blkFamily X, T ⊓ H :=
    eq_of_isSylowTwoOf_le hsyl hle inf_le_right (hT2.to_le inf_le_left)
  rw [heq]
  exact iSup_congr fun H => iSup_congr fun hH => (hD.spec H hH).syl

theorem offender_struct {B : Subgroup (MulAut V)} (hB : IsFFStarOffender T B) :
    Nat.card ↥B * Nat.card ↥(fixV B) = Nat.card V ∧
    B = ⨆ H ∈ B69.blkFamily X, (restrPerm (β H) B).map (ψ H) ∧
    ∀ H ∈ B69.blkFamily X, restrPerm (β H) B ≤ e4 ∧
      Nat.card ↥(restrPerm (β H) B) * Nat.card ↥(fixΔ (restrPerm (β H) B)) = 16 := by
  have hBX : IsFFStarOffender X B := isFFStarOffender_mono hD.ctx.hmp.isSylow.1 hB
  have hBD : B ≤ ⨆ H ∈ B69.blkFamily X, d8.map (ψ H) := by
    rw [← hD.inf_ffJ_eq]
    exact le_inf hB.1 (B19.le_ffJ hBX)
  have hk := hD.fam.key hBD hB.2.2.1
  have heq : Nat.card ↥B * Nat.card ↥(fixV B) = Nat.card V :=
    le_antisymm hk.1 (card_le_of_offender hBX)
  exact ⟨heq, hk.2 heq⟩

end SymData

end Ctx

end GE23

end CFSG.Quasithin

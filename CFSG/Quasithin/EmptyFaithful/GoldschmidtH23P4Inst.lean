module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Act
public import CFSG.Quasithin.EmptyFaithful.SBc17Out
public import CFSG.Quasithin.Background.F1Models

public section

namespace CFSG.Quasithin.H23P4

open CFSG.QuasithinUnique CFSG.Quasithin.H23Out CFSG.Quasithin
open scoped Pointwise commutatorElement

section Quot

variable {L : Type*} [Group L] (Q : Subgroup L) [Q.Normal] [Q.Characteristic]

def quotAut (φ : MulAut L) : MulAut (L ⧸ Q) :=
  QuotientGroup.congr Q Q φ (by
    rw [Subgroup.map_equiv_eq_comap_symm]
    exact (inferInstance : Q.Characteristic).fixed φ.symm)

theorem quotAut_mk (φ : MulAut L) (x : L) :
    quotAut Q φ (x : L ⧸ Q) = ((φ x : L) : L ⧸ Q) :=
  QuotientGroup.congr_mk _ _ _ _ _

def quotAutHom : MulAut L →* MulAut (L ⧸ Q) where
  toFun := quotAut Q
  map_one' := by
    ext x
    induction x using QuotientGroup.induction_on
    simp [quotAut_mk]
  map_mul' φ ψ := by
    ext x
    induction x using QuotientGroup.induction_on
    simp [quotAut_mk]

end Quot

section Main

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem action_data {L S Y : Subgroup G} (hS2 : IsPGroup 2 S) (hSyl : IsSylowTwoOf (S ⊓ L) L)
    (hY5 : IsPGroup 5 Y) (hYN : Y ≤ Subgroup.normalizer (L : Set G))
    (hSY : (S : Set G) * Y = Y * S) :
    ∃ (ρ : ↥(Subgroup.normalizer (L : Set G)) →* MulAut (↥L ⧸ CFSG.pCore 2 ↥L))
      (S₀ : Subgroup (↥L ⧸ CFSG.pCore 2 ↥L)),
      IsPGroup 2 ((S ⊓ Subgroup.normalizer (L : Set G)).subgroupOf
        (Subgroup.normalizer (L : Set G))) ∧
      IsPGroup 5 (Y.subgroupOf (Subgroup.normalizer (L : Set G))) ∧
      (((S ⊓ Subgroup.normalizer (L : Set G)).subgroupOf (Subgroup.normalizer (L : Set G)) :
          Set ↥(Subgroup.normalizer (L : Set G))) *
        (Y.subgroupOf (Subgroup.normalizer (L : Set G)) : Set ↥(Subgroup.normalizer (L : Set G))) =
        (Y.subgroupOf (Subgroup.normalizer (L : Set G)) :
          Set ↥(Subgroup.normalizer (L : Set G))) *
        ((S ⊓ Subgroup.normalizer (L : Set G)).subgroupOf (Subgroup.normalizer (L : Set G)) :
          Set ↥(Subgroup.normalizer (L : Set G)))) ∧
      IsSylowTwoOf S₀ ⊤ ∧
      (∀ s ∈ S₀, (MulAut.conj s : MulAut (↥L ⧸ CFSG.pCore 2 ↥L)) ∈
        ((S ⊓ Subgroup.normalizer (L : Set G)).subgroupOf
          (Subgroup.normalizer (L : Set G))).map ρ) ∧
      (∀ k : ↥(Subgroup.normalizer (L : Set G)), ρ k = 1 → (k : G) ∈ SBc17.cMod L) := by
  classical
  set N : Subgroup G := Subgroup.normalizer (L : Set G) with hN
  set Q : Subgroup ↥L := CFSG.pCore 2 ↥L with hQ
  let ρ : ↥N →* MulAut (↥L ⧸ Q) := (quotAutHom Q).comp (Subgroup.normalizerMonoidHom L)
  have hρ : ∀ (k : ↥N) (x : ↥L),
      ρ k (x : ↥L ⧸ Q) = ((Subgroup.normalizerMonoidHom L k x : ↥L) : ↥L ⧸ Q) :=
    fun k x => quotAut_mk Q _ x
  have hXN : S ⊓ N ≤ N := inf_le_right
  refine ⟨ρ, ((S ⊓ L).subgroupOf L).map (QuotientGroup.mk' Q),
    (hS2.to_le inf_le_left).comap_subtype (K := N), hY5.comap_subtype (K := N),
    mul_comm_subgroupOf hXN hYN (mul_comm_inf_of_le hSY hYN), ?_, ?_, ?_⟩
  · rw [isSylowTwoOf_top_iff]
    refine ⟨(hSyl.2.1.comap_subtype (K := L)).map _, fun h2 => hSyl.2.2 (h2.trans ?_)⟩
    exact Subgroup.index_map_dvd _ (QuotientGroup.mk'_surjective Q)
  · rintro _ ⟨l, hl, rfl⟩
    have hlN : (l : G) ∈ N := Subgroup.le_normalizer l.2
    have hl' : (l : G) ∈ S ⊓ L := Subgroup.mem_subgroupOf.1 hl
    refine ⟨⟨l, hlN⟩, show (l : G) ∈ S ⊓ N from ⟨hl'.1, hlN⟩, ?_⟩
    ext y
    induction y using QuotientGroup.induction_on with | _ x => ?_
    rw [hρ]
    apply congrArg (QuotientGroup.mk (s := Q))
    apply Subtype.ext
    rw [SBc17.coe_normalizerMonoidHom L hlN]
    simp
  · intro k hk
    refine SBc17.mem_cMod.2 ⟨k.2, fun x hx => ?_⟩
    set xL : ↥L := ⟨x, hx⟩ with hxL
    have h1 := congrArg (fun φ : MulAut (↥L ⧸ Q) => φ (xL : ↥L ⧸ Q)) hk
    simp only [MulAut.one_apply] at h1
    rw [hρ] at h1
    have h2 : QuotientGroup.mk' Q (xL * (Subgroup.normalizerMonoidHom L k xL)⁻¹) = 1 := by
      simp only [map_mul, map_inv, QuotientGroup.mk'_apply]
      rw [h1]
      exact mul_inv_cancel _
    have h3 := (SBc17.map_eq_one_iff_mem_pCoreOf (α := QuotientGroup.mk' Q)
      (by rw [QuotientGroup.ker_mk']) _).1 h2
    have h4 : ((xL * (Subgroup.normalizerMonoidHom L k xL)⁻¹ : ↥L) : G) = ⁅x, (k : G)⁆ := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, SBc17.coe_normalizerMonoidHom L k.2]
      simp only [commutatorElement_def, hxL]
      group
    rwa [h4] at h3

theorem le_cMod_of_rowOK {L S Y : Subgroup G} (hS2 : IsPGroup 2 S)
    (hSyl : IsSylowTwoOf (S ⊓ L) L) (hY5 : IsPGroup 5 Y)
    (hYN : Y ≤ Subgroup.normalizer (L : Set G)) (hSY : (S : Set G) * Y = Y * S)
    (hrow : RowOK (↥L ⧸ CFSG.pCore 2 ↥L)) : Y ≤ SBc17.cMod L := by
  obtain ⟨ρ, S₀, hX', hY', hXY', hS₀, hsub, hker⟩ := action_data hS2 hSyl hY5 hYN hSY
  have key := trivial_of_overgroup hrow.center hrow.out hrow.idx ρ hX' hY' hXY' hS₀ hsub
  intro y hy
  exact hker ⟨y, hYN hy⟩ (key (show (⟨y, hYN hy⟩ : ↥(Subgroup.normalizer (L : Set G))) ∈
    Y.subgroupOf (Subgroup.normalizer (L : Set G)) from hy))

end Main

end CFSG.Quasithin.H23P4

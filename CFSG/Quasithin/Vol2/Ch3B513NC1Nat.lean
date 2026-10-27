module

public import CFSG.Quasithin.Vol2.Ch3B513NC1Small
public import CFSG.Quasithin.Background.B4L3Coord

public section

namespace CFSG.Quasithin.B513N

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

section Fix

variable {d : ℕ} {K : Type} [Field K] [Finite K]

theorem card_fix_natAct_le (Γ : Subgroup (Matrix.GeneralLinearGroup (Fin d) K)) {γ : ↥Γ}
    (hγ : γ ≠ 1) :
    Nat.card {x : Multiplicative (Fin d → K) // natAct Γ γ x = x} ≤ Nat.card K ^ (d - 1) := by
  classical
  let T : (Fin d → K) →ₗ[K] (Fin d → K) :=
    Matrix.mulVecLin (((γ : ↥Γ) : Matrix.GeneralLinearGroup (Fin d) K) : Matrix (Fin d) (Fin d) K) -
      LinearMap.id
  have hmem : ∀ x : Multiplicative (Fin d → K),
      natAct Γ γ x = x ↔ Multiplicative.toAdd x ∈ LinearMap.ker T := by
    intro x
    rw [LinearMap.mem_ker]
    simp only [T, LinearMap.sub_apply, Matrix.mulVecLin_apply, LinearMap.id_apply, sub_eq_zero]
    constructor
    · intro h
      have := congrArg Multiplicative.toAdd h
      exact this
    · intro h
      exact Multiplicative.toAdd.injective h
  have hS : LinearMap.ker T ≠ ⊤ := by
    intro htop
    apply hγ
    apply natAct_faithful Γ γ
    intro m
    have h1 : natAct Γ γ m = m := (hmem m).2 (htop ▸ Submodule.mem_top)
    rw [h1, mul_inv_cancel]
  have hlt : Module.finrank K (LinearMap.ker T) < d := by
    have := Submodule.finrank_lt hS
    rwa [Module.finrank_fin_fun] at this
  have e : {x : Multiplicative (Fin d → K) // natAct Γ γ x = x} ≃ ↥(LinearMap.ker T) :=
    { toFun := fun x => ⟨Multiplicative.toAdd x.1, (hmem x.1).1 x.2⟩
      invFun := fun y => ⟨Multiplicative.ofAdd y.1, (hmem _).2 y.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Module.natCard_eq_pow_finrank (K := K)]
  exact Nat.pow_le_pow_right Nat.card_pos (by omega)

end Fix

variable {W : Type} [CommGroup W] [Finite W]

theorem hasGood_of_nat_cent (hW : ∀ w : W, w ^ 2 = 1) {G L : Subgroup (MulAut W)}
    (hne : G ≠ ⊥) (hJ : G = ffJ G) (hGL : G ≤ L) {d : ℕ} {K : Type} [Field K] [Finite K]
    {Γ : Subgroup (Matrix.GeneralLinearGroup (Fin d) K)} {Z : Subgroup W}
    {π : (FFModel.nat Γ).Gam →* ↥L} (hr : (FFModel.nat Γ).RealizesVia L (commV L) Z π)
    (hd : 1 ≤ d) (hbound : Nat.card Z * Nat.card K ^ (d - 1) ≤ Nat.card K ^ 2) : HasGood G := by
  obtain ⟨D, hD⟩ := exists_isFFStarMin hne hJ
  have hDL : D ≤ L := hD.1.1.trans hGL
  obtain ⟨d₀, hd₀, hd₀1⟩ : ∃ x ∈ D, x ≠ 1 := by
    by_contra h
    push Not at h
    exact hD.1.2.1 (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (h x hx))
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hr
  obtain ⟨γ, hγ⟩ := hr.1 ⟨d₀, hDL hd₀⟩
  have hγ1 : γ ≠ 1 := by
    rintro rfl
    apply hd₀1
    have := congrArg Subtype.val hγ
    rw [map_one] at this
    exact this.symm
  set F : Subgroup W := fixV D ⊓ commV L with hF
  have hFU : F ≤ commV L := inf_le_right
  have hFcard : Nat.card F ≤ Nat.card Z * Nat.card K ^ (d - 1) := by
    let g : ↥F →* Multiplicative (Fin d → K) := β.comp (Subgroup.inclusion hFU)
    have hker : Nat.card g.ker ≤ Nat.card Z := by
      refine Nat.card_le_card_of_injective (fun x => ⟨(x.1 : W), (hβk _).1 x.2⟩) ?_
      intro x y hxy
      have h1 : ((x : ↥F) : W) = ((y : ↥F) : W) := congrArg (fun t : ↥Z => (t : W)) hxy
      exact Subtype.ext (Subtype.ext h1)
    have hrange : Nat.card g.range ≤ Nat.card K ^ (d - 1) := by
      refine le_trans ?_ (card_fix_natAct_le Γ hγ1)
      refine Nat.card_le_card_of_injective (fun y => ⟨(y : Multiplicative (Fin d → K)), ?_⟩) ?_
      · obtain ⟨x, hx⟩ := y.2
        rw [← hx]
        have hfix : d₀ (x : W) = x := x.2.1 d₀ hd₀
        have hu : ((π γ : ↥L) : MulAut W) ((x : W)) ∈ commV L := by
          rw [show ((π γ : ↥L) : MulAut W) = d₀ from congrArg Subtype.val hγ, hfix]
          exact hFU x.2
        have h1 := hβe γ ⟨x, hFU x.2⟩ hu
        have h2 : (⟨((π γ : ↥L) : MulAut W) (x : W), hu⟩ : ↥(commV L)) = ⟨x, hFU x.2⟩ := by
          apply Subtype.ext
          show ((π γ : ↥L) : MulAut W) (x : W) = x
          rw [show ((π γ : ↥L) : MulAut W) = d₀ from congrArg Subtype.val hγ, hfix]
        rw [h2] at h1
        exact h1.symm
      · intro y z hyz
        have h1 : (y : Multiplicative (Fin d → K)) = z :=
          congrArg (fun t : {x : Multiplicative (Fin d → K) // natAct Γ γ x = x} => t.1) hyz
        exact Subtype.ext h1
    calc Nat.card F = Nat.card g.ker * Nat.card g.range := (Subgroup.card_ker_mul_card_range g).symm
      _ ≤ Nat.card Z * Nat.card K ^ (d - 1) := Nat.mul_le_mul hker hrange
  have hUcard : Nat.card (commV L) = Nat.card Z * Nat.card K ^ d := card_commV_of_nat hr
  have hDK : Nat.card K ≤ Nat.card D := by
    have h1 : (fixV D).relIndex (commV L) * Nat.card F = Nat.card (commV L) :=
      Subgroup.relIndex_mul_card (fixV D) (commV L)
    have h2 : (fixV D).relIndex (commV L) ≤ (fixV D).index := by
      have := Subgroup.relIndex_le_of_le_right (H := fixV D) (le_top : commV L ≤ ⊤)
        (by rw [Subgroup.relIndex_top_right]; exact Subgroup.index_ne_zero_of_finite)
      rwa [Subgroup.relIndex_top_right] at this
    have h3 : (fixV D).index ≤ Nat.card D := index_fixV_le_card hD.1
    have hZpos : 0 < Nat.card Z := Nat.card_pos
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have h4 : Nat.card Z * Nat.card K ^ d ≤
        (fixV D).relIndex (commV L) * (Nat.card Z * Nat.card K ^ (d - 1)) := by
      rw [← hUcard, ← h1]
      exact Nat.mul_le_mul_left _ hFcard
    have hdk : Nat.card K ^ d = Nat.card K * Nat.card K ^ (d - 1) := by
      rw [← pow_succ']
      congr 1
      omega
    rw [hdk] at h4
    have h5 : Nat.card K ≤ (fixV D).relIndex (commV L) := by
      have hpos : 0 < Nat.card Z * Nat.card K ^ (d - 1) := Nat.mul_pos hZpos (pow_pos hKpos _)
      have : Nat.card K * (Nat.card Z * Nat.card K ^ (d - 1)) ≤
          (fixV D).relIndex (commV L) * (Nat.card Z * Nat.card K ^ (d - 1)) := by
        calc Nat.card K * (Nat.card Z * Nat.card K ^ (d - 1))
            = Nat.card Z * (Nat.card K * Nat.card K ^ (d - 1)) := by ring
          _ ≤ _ := h4
      exact Nat.le_of_mul_le_mul_right this hpos
    exact h5.trans (h2.trans h3)
  refine hasGood_of_offender_le hW hD (commV_mono hDL) ?_
  calc Nat.card F ≤ Nat.card Z * Nat.card K ^ (d - 1) := hFcard
    _ ≤ Nat.card K ^ 2 := hbound
    _ ≤ Nat.card D ^ 2 := Nat.pow_le_pow_left hDK 2

end CFSG.Quasithin.B513N

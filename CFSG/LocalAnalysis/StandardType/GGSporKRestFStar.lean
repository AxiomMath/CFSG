module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.ComponentClassification.OuterAutomorphisms

theorem ggSporKRest_index_fstar_le {W : Type} [Group W] [Finite W] :
    (CFSG.generalizedFitting W).index ≤ Nat.card (Outer ↥(CFSG.generalizedFitting W)) := by
  let F : Subgroup W := CFSG.generalizedFitting W
  haveI hFnormal : F.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := W)).2
  let φ : W →* MulAut ↥F := MulAut.conjNormal
  let ψ : W →* Outer ↥F := (QuotientGroup.mk' (inner ↥F)).comp φ
  have hker : ψ.ker = F := by
    ext w
    rw [MonoidHom.mem_ker]
    constructor
    · intro hw
      have hφ : (φ w : Outer ↥F) = 1 := by
        change (QuotientGroup.mk' (inner ↥F)) (φ w) = 1 at hw
        rwa [QuotientGroup.mk'_apply] at hw
      obtain ⟨f, hf⟩ := (QuotientGroup.eq_one_iff (φ w)).mp hφ
      have hfw : ∀ y : ↥F, (f : W) * (y : W) * (f : W)⁻¹ = w * (y : W) * w⁻¹ := by
        intro y
        have h1 : MulAut.conj f y = MulAut.conjNormal w y := by
          have := congrArg (fun e : MulAut ↥F => e y) hf
          simpa using this
        have h2 := congrArg Subtype.val h1
        rw [MulAut.conj_apply, MulAut.conjNormal_apply] at h2
        simpa using h2
      have hcent : (f : W)⁻¹ * w ∈ Subgroup.centralizer (F : Set W) := by
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have h := hfw ⟨y, hy⟩
        have h2 : (y : W) * (f : W)⁻¹ * w = (f : W)⁻¹ * w * (y : W) := by
          calc (y : W) * (f : W)⁻¹ * w
              = (f : W)⁻¹ * ((f : W) * (y : W) * (f : W)⁻¹) * w := by group
            _ = (f : W)⁻¹ * (w * (y : W) * w⁻¹) * w := by rw [h]
            _ = (f : W)⁻¹ * w * (y : W) := by group
        simpa [mul_assoc] using h2
      have hcF : (f : W)⁻¹ * w ∈ F :=
        CFSG.centralizer_generalizedFitting_le W hcent
      have hmul : (f : W) * ((f : W)⁻¹ * w) = w := by group
      rw [← hmul]
      exact F.mul_mem f.property hcF
    · intro hw
      change (QuotientGroup.mk' (inner ↥F)) (φ w) = 1
      rw [QuotientGroup.mk'_apply]
      refine (QuotientGroup.eq_one_iff (φ w)).mpr ⟨⟨w, hw⟩, ?_⟩
      exact (MulAut.conjNormal_val (H := F) (h := ⟨w, hw⟩)).symm
  change F.index ≤ Nat.card (Outer ↥F)
  rw [Subgroup.index_eq_card]
  have hquot : Nat.card (W ⧸ F) = Nat.card (W ⧸ ψ.ker) := by rw [hker]
  rw [hquot]
  exact Nat.card_le_card_of_injective (QuotientGroup.kerLift ψ)
    (QuotientGroup.kerLift_injective ψ)

theorem ggSporKRest_mem_fstar_of_pow_eq_one {W : Type} [Group W] [Finite W] {m : ℕ} (hm : Odd m)
    (hOut : Nat.card (Outer ↥(CFSG.generalizedFitting W)) ≤ 2) {x : W} (hx : x ^ m = 1) :
    x ∈ CFSG.generalizedFitting W := by
  let F : Subgroup W := CFSG.generalizedFitting W
  haveI hFnormal : F.Normal := (CFSG.LocalCores.generalized_fitting_characteristic (G := W)).2
  have hindex : F.index ≤ 2 := le_trans (ggSporKRest_index_fstar_le (W := W)) hOut
  letI : Fintype (W ⧸ F) := Fintype.ofFinite (W ⧸ F)
  have hcard : Fintype.card (W ⧸ F) ≤ 2 := by
    rw [← Nat.card_eq_fintype_card, (Subgroup.index_eq_card F).symm]
    exact hindex
  let q : W ⧸ F := (QuotientGroup.mk' F) x
  have hq2 : q ^ 2 = 1 := by
    have hpow : q ^ Fintype.card (W ⧸ F) = 1 := pow_card_eq_one
    have hpos : 0 < Fintype.card (W ⧸ F) := Fintype.card_pos_iff.mpr inferInstance
    rcases (by omega : Fintype.card (W ⧸ F) = 1 ∨ Fintype.card (W ⧸ F) = 2) with h1 | h2
    · rw [h1, pow_one] at hpow
      rw [hpow, one_pow]
    · rwa [h2] at hpow
  have hqm : q ^ m = 1 := by
    change ((QuotientGroup.mk' F) x) ^ m = 1
    rw [← map_pow, hx, map_one]
  obtain ⟨k, hk⟩ := hm
  have hq1 : q = 1 := by
    have h := hqm
    rw [hk, pow_succ, pow_mul, hq2, one_pow, one_mul] at h
    exact h
  have hxF : x ∈ F := (QuotientGroup.eq_one_iff x).mp (by
    change ((QuotientGroup.mk' F) x) = 1
    exact hq1)
  exact hxF

theorem ggSporKRest_pGroup_le_fstar {W : Type} [Group W] [Finite W] {p : ℕ} (hp : Odd p)
    (hOut : Nat.card (Outer ↥(CFSG.generalizedFitting W)) ≤ 2) {P : Subgroup W}
    (hP : IsPGroup p P) : P ≤ CFSG.generalizedFitting W := by
  intro x hx
  obtain ⟨n, hn⟩ := hP ⟨x, hx⟩
  have hxpow : x ^ (p ^ n) = 1 := by
    have := congrArg Subtype.val hn
    simpa using this
  exact ggSporKRest_mem_fstar_of_pow_eq_one (W := W) (m := p ^ n) hp.pow hOut hxpow

end CFSG.StandardType.SporadicShape

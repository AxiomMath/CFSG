module

public import CFSG.Quasithin.EmptyFaithful.S146zClaim

public section

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7 CFSG.Quasithin.CosetGeom
open scoped commutatorElement

namespace CFSG.Quasithin.ThreeC

section Num

variable {G : Type} [Group G] [Finite G]

theorem mIdx_centralizerMod_le_add {Z U X A₁ D Dg : Subgroup G}
    (hUab : IsElemAbelian 2 U) (hXab : IsElemAbelian 2 X)
    (hUN : U ≤ Subgroup.normalizer (Z : Set G))
    (hA₁X : A₁ ≤ X) (hA₁c : Nat.card A₁ = 2) (hD : D = centralizerMod A₁ U X)
    (hA₁Z : A₁ ⊓ Z = ⊥)
    (hDgX : Dg ≤ X) (hDg : ∀ x ∈ Dg, ∀ v ∈ U, x * v * x⁻¹ * v⁻¹ ∈ Z) :
    mIdx U (centralizerMod Z U X) ≤ mIdx U D + mIdx X Dg := by
  classical
  have hUp2 : IsPGroup 2 U := isPGroup_of_isElemAbelian hUab
  have hXp2 : IsPGroup 2 X := isPGroup_of_isElemAbelian hXab
  have hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x := fun x hx y hy => isElemAbelian_comm hXab hx hy
  have hDU : D ≤ U := hD ▸ centralizerMod_le_left _ _ _
  have hDp2 : IsPGroup 2 D := hUp2.to_le hDU
  set CX := X ⊓ Subgroup.centralizer (D : Set G) with hCX
  set CD := D ⊓ Subgroup.centralizer (X : Set G) with hCD
  set CU := centralizerMod Z U X with hCU
  have hcomm : ⁅D, X⁆ ≤ A₁ := by
    rw [Subgroup.commutator_le]
    intro d hd x hx
    have hd' : d ∈ centralizerMod A₁ U X := hD ▸ hd
    exact hd'.2.2 x hx
  have hCXc : A₁ ≤ Subgroup.centralizer (D : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro d hd
    have hd' : d ∈ centralizerMod A₁ U X := hD ▸ hd
    have hdN : d ∈ Subgroup.normalizer (A₁ : Set G) := hd'.2.1
    rw [normalizer_eq_centralizer_of_card_eq_two hA₁c] at hdN
    exact (Subgroup.mem_centralizer_iff.mp hdN a ha).symm
  have hCYc : A₁ ≤ Subgroup.centralizer (X : Set G) := by
    intro a ha
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    exact hXc x hx a (hA₁X ha)
  have hpair := relIndex_eq_of_commutator_le (X := D) (Y := X) (C := A₁) hXab hA₁c hcomm hCXc hCYc
  have hmDX : mIdx D CD = mIdx X CX := by
    have e1 := HypF98.relIndex_eq_two_pow_mIdx (Y := CD) hDp2
    have e2 := HypF98.relIndex_eq_two_pow_mIdx (Y := CX) hXp2
    rw [e1, e2] at hpair
    exact Nat.pow_right_injective (le_refl 2) hpair
  have hCDle : CD ≤ CU := by
    intro d hd
    refine ⟨hDU hd.1, hUN (hDU hd.1), fun e he => ?_⟩
    have := Subgroup.mem_centralizer_iff.mp hd.2 e he
    have e1 : d * e * d⁻¹ * e⁻¹ = 1 := by
      calc d * e * d⁻¹ * e⁻¹ = (e * d) * d⁻¹ * e⁻¹ := by rw [this]
        _ = 1 := by group
    rw [e1]; exact Z.one_mem
  have hf1 : mIdx U CU ≤ mIdx U D + mIdx D CD := by
    have h1 : mIdx U CU ≤ mIdx U CD := mIdx_anti_of_le (X := U) hCDle
    have h2 : mIdx U CD = mIdx U D + mIdx D CD := mIdx_add hUp2 hDU (inf_le_left : CD ≤ D)
    omega
  have hDgCX : Dg ≤ CX := by
    intro x hx
    refine ⟨hDgX hx, Subgroup.mem_centralizer_iff.mpr fun d hd => ?_⟩
    have hdD : d ∈ centralizerMod A₁ U X := hD ▸ hd
    have hA : d * x * d⁻¹ * x⁻¹ ∈ A₁ := hdD.2.2 x (hDgX hx)
    have hZ : d * x * d⁻¹ * x⁻¹ ∈ Z := by
      have h1 := hDg x hx d (hDU hd)
      have e : d * x * d⁻¹ * x⁻¹ = (x * d * x⁻¹ * d⁻¹)⁻¹ := by group
      rw [e]; exact Z.inv_mem h1
    have h3 : d * x * d⁻¹ * x⁻¹ ∈ A₁ ⊓ Z := ⟨hA, hZ⟩
    rw [hA₁Z, Subgroup.mem_bot] at h3
    calc d * x = (d * x * d⁻¹ * x⁻¹) * (x * d) := by group
      _ = x * d := by rw [h3]; group
  have hCXle : mIdx X CX ≤ mIdx X Dg := mIdx_anti_of_le (X := X) hDgCX
  omega

end Num

end CFSG.Quasithin.ThreeC

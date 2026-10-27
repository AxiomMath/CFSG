module

public import CFSG.HardMathSupport.Dickson.I271.SporGenAux.ON7Extra

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.HardMathSupport.Dickson.I271 (SevenLine)

variable {X : Type*} [Group X] {p : ℕ} [Fact p.Prime] {w : X} {F : Subgroup X}

omit [Fact (Nat.Prime p)] in
theorem sevenLine_zpowers_pow_eq_one (h : SevenLine p w F) {x : X}
    (hx : x ∈ Subgroup.zpowers w) : x ^ p = 1 := by
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
  rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, h.pow_eq, one_zpow]

private theorem sevenLine_fix_mod_fixes_F (h : SevenLine p w F) (hp2 : p ≠ 2) {α : MulAut X}
    (hα2 : α * α = 1) (hαw : α w = w) (hT : ∀ f ∈ F, α f * f⁻¹ ∈ Subgroup.zpowers w) :
    ∀ f ∈ F, α f = f := by
  have hαα : ∀ x : X, α (α x) = x := by
    intro x
    have h := congrArg (fun u : MulAut X => u x) hα2
    simpa [MulAut.mul_apply] using h
  have hfixZ : ∀ x ∈ Subgroup.zpowers w, α x = x := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← hk, map_zpow, hαw]
  have hcop2 : Nat.Coprime 2 p := ((Fact.out : p.Prime).odd_of_ne_two hp2).coprime_two_left
  intro f hf
  set φ : X := α f * f⁻¹ with hφ
  have hφZ : φ ∈ Subgroup.zpowers w := by rw [hφ]; exact hT f hf
  have hφfix : α φ = φ := hfixZ φ hφZ
  have hfm : φ * f = α f := by rw [hφ]; group
  have hφsq : φ * φ = 1 := by
    have h3 : f = φ * φ * f := by
      calc f = α (α f) := (hαα f).symm
        _ = α (φ * f) := by rw [← hfm]
        _ = α φ * α f := by rw [map_mul]
        _ = φ * α f := by rw [hφfix]
        _ = φ * (φ * f) := by rw [← hfm]
        _ = φ * φ * f := by group
    exact mul_right_cancel (b := f) (by simpa using h3.symm)
  have hφ1 : φ = 1 :=
    orderOf_eq_one_iff.1 <| Nat.eq_one_of_dvd_coprimes hcop2
      (orderOf_dvd_of_pow_eq_one (by rwa [pow_two]))
      (orderOf_dvd_of_pow_eq_one (sevenLine_zpowers_pow_eq_one h hφZ))
  rw [hφ1, one_mul] at hfm
  exact hfm.symm

theorem sevenLine_fix_of_fix_mod (h : SevenLine p w F) (hp2 : p ≠ 2) {α : MulAut X}
    (hα2 : α * α = 1) (hαw : α w = w) (hT : ∀ f ∈ F, α f * f⁻¹ ∈ Subgroup.zpowers w) :
    ∀ c ∈ Subgroup.centralizer ({w} : Set X), α c = c := by
  have hαα : ∀ x : X, α (α x) = x := by
    intro x
    have h := congrArg (fun u : MulAut X => u x) hα2
    simpa [MulAut.mul_apply] using h
  have hfixZ : ∀ x ∈ Subgroup.zpowers w, α x = x := by
    intro x hx
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hx
    rw [← hk, map_zpow, hαw]
  have hcop2 : Nat.Coprime 2 p := ((Fact.out : p.Prime).odd_of_ne_two hp2).coprime_two_left
  have hfixF := sevenLine_fix_mod_fixes_F h hp2 hα2 hαw hT
  intro c hc
  have hαcC : α c ∈ Subgroup.centralizer ({w} : Set X) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hc ⊢
    have h := congrArg α hc
    rwa [map_mul, map_mul, hαw] at h
  have hsC : c⁻¹ * α c ∈ Subgroup.centralizer ({w} : Set X) :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ hc) hαcC
  have hs_comm : ∀ f ∈ F, (c⁻¹ * α c) * f = f * (c⁻¹ * α c) := by
    intro f hf
    have hcf : c * f * c⁻¹ ∈ F := h.norm c hc f hf
    have hfix := hfixF _ hcf
    have hfix' : α (c * f * c⁻¹) = α c * f * (α c)⁻¹ := by
      rw [map_mul, map_mul, map_inv, hfixF f hf]
    rw [hfix'] at hfix
    calc (c⁻¹ * α c) * f = c⁻¹ * (α c * f * (α c)⁻¹) * α c := by group
      _ = c⁻¹ * (c * f * c⁻¹) * α c := by rw [hfix]
      _ = f * (c⁻¹ * α c) := by group
  have hsZ : c⁻¹ * α c ∈ Subgroup.zpowers w := h.cent _ hsC hs_comm
  have hsfix : α (c⁻¹ * α c) = c⁻¹ * α c := hfixZ _ hsZ
  have hαc : α c = c * (c⁻¹ * α c) := by group
  have hs2 : (c⁻¹ * α c) * (c⁻¹ * α c) = 1 := by
    have h3 : c = c * ((c⁻¹ * α c) * (c⁻¹ * α c)) := by
      calc c = α (α c) := (hαα c).symm
        _ = α (c * (c⁻¹ * α c)) := by rw [← hαc]
        _ = α c * α (c⁻¹ * α c) := by rw [map_mul]
        _ = α c * (c⁻¹ * α c) := by rw [hsfix]
        _ = (c * (c⁻¹ * α c)) * (c⁻¹ * α c) := by rw [hαc]; group
        _ = c * ((c⁻¹ * α c) * (c⁻¹ * α c)) := by group
    exact mul_left_cancel (a := c) (by simpa using h3.symm)
  have hs1 : c⁻¹ * α c = 1 :=
    orderOf_eq_one_iff.1 <| Nat.eq_one_of_dvd_coprimes hcop2
      (orderOf_dvd_of_pow_eq_one (by rwa [pow_two]))
      (orderOf_dvd_of_pow_eq_one (sevenLine_zpowers_pow_eq_one h hsZ))
  rw [hαc, hs1, mul_one]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

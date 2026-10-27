module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP7R
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP8R3

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Open U42F431
open CFSG.Quasithin.H13.F431.U42 (P45)

@[expose] def aU : PL := UL.getD 6 []

@[expose] def bU : PL := UL.getD 2 []

theorem U_dphi_mem : ∀ x, dphi aU bU x ∈ UL := by decide +kernel

theorem U_dphi_mul : ∀ x y : DihedralGroup 4,
    dphi aU bU (x * y) = comp (dphi aU bU x) (dphi aU bU y) := by decide +kernel

theorem U_dphi_inj : ∀ x y : DihedralGroup 4, dphi aU bU x = dphi aU bU y → x = y := by
  decide +kernel

theorem Uh_equiv_D8 : Nonempty (↥Uh ≃* DihedralGroup 4) := by
  have hmem : ∀ x, dphi aU bU x ∈ Thl := fun x => (UL_check.2.2.2.2.1 _ (U_dphi_mem x)).1
  let φ := dhom aU bU hmem U_dphi_mul
  have hinj : Function.Injective φ := by
    intro x y hxy
    apply U_dphi_inj
    have h1 := repL_dhom aU bU hmem U_dphi_mul x
    have h2 := repL_dhom aU bU hmem U_dphi_mul y
    have : (φ x : Ah) = φ y := hxy
    rw [this] at h1
    exact repL_unique h1 h2
  have hle : φ.range ≤ Uh := by
    rintro _ ⟨x, rfl⟩
    exact ⟨dphi aU bU x, U_dphi_mem x, repL_dhom aU bU hmem U_dphi_mul x⟩
  have hcard : Nat.card ↥φ.range = Nat.card ↥Uh := by
    rw [card_Uh, ← Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv, DihedralGroup.nat_card]
  have hrange : φ.range = Uh := Subgroup.eq_of_le_of_card_ge hle hcard.ge
  exact ⟨(MulEquiv.subgroupCongr hrange.symm).trans (MonoidHom.ofInjective hinj).symm⟩

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem UG_equiv_D8 (c : AutCtx G M₁ M₂ z) : Nonempty (↥(UG c) ≃* DihedralGroup 4) := by
  obtain ⟨e⟩ := Uh_equiv_D8
  exact ⟨(imgGEquiv c.iso Uh_le_Bh).symm.trans e⟩

end CFSG.Quasithin.H13.F431.U42Aut

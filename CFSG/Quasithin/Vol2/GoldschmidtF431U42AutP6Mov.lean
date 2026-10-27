module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP6Syl

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin CFSG.QuasithinUnique U42F431

variable {G : Type} [Group G] [Finite G] {M₁ M₂ : Subgroup G} {z : G}

theorem exists_moving
    (c : AutCtx G M₁ M₂ z) {R : Subgroup G} (hR : IsSylowTwoOf R (cenOf (c.iso.toG fhB)))
    (hTR : c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≤ R)
    (hne : c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) ≠ R) :
    ∃ n ∈ R ⊓ Subgroup.normalizer
        ((c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) : Subgroup G) : Set G), n * z * n⁻¹ ≠ z := by
  by_contra hcon
  push Not at hcon
  set Tf : Subgroup G := c.iso.imgG That ⊓ cenOf (c.iso.toG fhB) with hTf
  set N : Subgroup G := R ⊓ Subgroup.normalizer (Tf : Set G) with hN
  have hN2 : IsPGroup 2 N := hR.2.1.to_le inf_le_left
  have hTfN : Tf ≤ N := le_inf hTR Subgroup.le_normalizer
  have hNE : N ≤ M₁ ⊓ cenOf (c.iso.toG fhB) := by
    intro n hn
    have hz : n * z = z * n := by
      calc n * z = (n * z * n⁻¹) * n := by group
        _ = z * n := by rw [hcon n hn]
    exact ⟨c.cz (Subgroup.mem_centralizer_singleton_iff.2 hz), hR.1 hn.1⟩
  have hSyl : IsSylowTwoOf Tf N := B6.isSylowTwoOf_mono (isSylowTwoOf_Tf_E1 c.iso) hTfN hNE
  have hNTf : N ≤ Tf :=
    B6.le_of_isPGroup_of_odd_relIndex (H := N) (N := Tf) (T := N) le_rfl hN2 hTfN inf_le_right
      hSyl.2.2
  have hRTf : R ≤ Tf := le_of_normalizer_inf_le hR.2.1 hTR hNTf
  exact hne (le_antisymm hTR hRTf)

end CFSG.Quasithin.H13.F431.U42Aut

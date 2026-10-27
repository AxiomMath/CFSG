module

public import CFSG.Quasithin.Recognition.GoldschmidtF112FA5Frame

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7

namespace FA5

set_option linter.unusedSectionVars false

structure ZData {G : Type} [Group G] (L1 L2 S Z : Subgroup G) : Prop where
  le_S : Z ≤ S
  central : ∀ z ∈ Z, ∀ s ∈ S, z * s = s * z
  sq : ∀ z ∈ Z, z * z = 1
  norm : ∀ b ∈ bigB L1 L2 S, ∀ z ∈ Z, b * z * b⁻¹ ∈ Z

namespace Frame

variable {G : Type} [Group G] [Finite G] {L1 L2 S D X Z : Subgroup G} (F : Frame L1 L2 S D X)
  (hZ : ZData L1 L2 S Z)
include F hZ

theorem Z_le_Q1 : Z ≤ Q1 L1 L2 S := by
  intro z hz
  have hzS : z ∈ S := hZ.le_S hz
  refine F.charTwo_P1 ⟨F.mem_P1_of_mem_S hzS, Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro y hy
  exact (hZ.central z hz y (F.Q1_le_S hy)).symm

theorem Z_le_Q2 : Z ≤ Q2 L1 L2 S := by
  intro z hz
  have hzS : z ∈ S := hZ.le_S hz
  refine F.charTwo_P2 ⟨(le_sup_right : bigB L1 L2 S ≤ P2 L1 L2 S) (F.mem_B_of_mem_S hzS),
    Subgroup.mem_centralizer_iff.mpr ?_⟩
  intro y hy
  exact (hZ.central z hz y (F.Q2_le_S hy)).symm

abbrev Z1 (L1 L2 S Z : Subgroup G) : Subgroup G := conjClosure Z (P1 L1 L2 S)

abbrev Z2 (L1 L2 S Z : Subgroup G) : Subgroup G := conjClosure Z (P2 L1 L2 S)

theorem Z1_le_Q1 : Z1 L1 L2 S Z ≤ Q1 L1 L2 S := by
  refine conjClosure_le fun h hh z hz => ?_
  have := (Subgroup.mem_normalizer_iff.mp (P1_le_normalizer_Q1 L1 L2 S hh) z).mp (F.Z_le_Q1 hZ hz)
  exact this

theorem Z1_comm : ∀ a ∈ Z1 L1 L2 S Z, ∀ y ∈ Q1 L1 L2 S, a * y = y * a := by
  have : Z1 L1 L2 S Z ≤ Subgroup.centralizer (Q1 L1 L2 S : Set G) := by
    refine conjClosure_le fun h hh z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : h⁻¹ * y * h ∈ Q1 L1 L2 S := by
      have := (Subgroup.mem_normalizer_iff.mp
        (P1_le_normalizer_Q1 L1 L2 S ((P1 L1 L2 S).inv_mem hh)) y).mp hy
      simpa using this
    have hc := hZ.central z hz _ (F.Q1_le_S hy')
    calc y * (h * z * h⁻¹) = h * ((h⁻¹ * y * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * y * h)) * h⁻¹ := by rw [← hc]
      _ = (h * z * h⁻¹) * y := by group
  intro a ha y hy
  exact ((Subgroup.mem_centralizer_iff.mp (this ha)) y hy).symm

theorem Z2_le_Q2 : Z2 L1 L2 S Z ≤ Q2 L1 L2 S := by
  refine conjClosure_le fun h hh z hz => ?_
  have := (Subgroup.mem_normalizer_iff.mp (P2_le_normalizer_Q2 L1 L2 S hh) z).mp (F.Z_le_Q2 hZ hz)
  exact this

theorem Z2_comm : ∀ a ∈ Z2 L1 L2 S Z, ∀ y ∈ Q2 L1 L2 S, a * y = y * a := by
  have : Z2 L1 L2 S Z ≤ Subgroup.centralizer (Q2 L1 L2 S : Set G) := by
    refine conjClosure_le fun h hh z hz => ?_
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : h⁻¹ * y * h ∈ Q2 L1 L2 S := by
      have := (Subgroup.mem_normalizer_iff.mp
        (P2_le_normalizer_Q2 L1 L2 S ((P2 L1 L2 S).inv_mem hh)) y).mp hy
      simpa using this
    have hc := hZ.central z hz _ (F.Q2_le_S hy')
    calc y * (h * z * h⁻¹) = h * ((h⁻¹ * y * h) * z) * h⁻¹ := by group
      _ = h * (z * (h⁻¹ * y * h)) * h⁻¹ := by rw [← hc]
      _ = (h * z * h⁻¹) * y := by group
  intro a ha y hy
  exact ((Subgroup.mem_centralizer_iff.mp (this ha)) y hy).symm

theorem Z2_sq : ∀ a ∈ Z2 L1 L2 S Z, a * a = 1 := by
  have hel : IsElemAbelian 2 (Z2 L1 L2 S Z) := by
    refine isElemAbelian_closure _ ?_ ?_
    · rintro _ ⟨h, hh, z, hz, rfl⟩ _ ⟨h', hh', z', hz', rfl⟩
      have hmem : h * z * h⁻¹ ∈ Z2 L1 L2 S Z := mem_conjClosure hh hz
      have hmem' : h' * z' * h'⁻¹ ∈ Z2 L1 L2 S Z := mem_conjClosure hh' hz'
      exact (F.Z2_comm hZ _ hmem' _ (F.Z2_le_Q2 hZ hmem)).symm
    · rintro _ ⟨h, hh, z, hz, rfl⟩
      have : (h * z * h⁻¹) ^ 2 = 1 := by
        rw [conj_pow, pow_two, hZ.sq z hz]
        group
      exact this
  intro a ha
  have := isElemAbelian_pow_eq_one hel ha
  simpa [pow_two] using this

theorem conj_Z_eq {p z : G} (hp : p ∈ P1 L1 L2 S) (hz : z ∈ Z) :
    ∃ x ∈ X, ∃ z' ∈ Z, p * z * p⁻¹ = x * z' * x⁻¹ := by
  obtain ⟨x, hx, b, hb, rfl⟩ := F.exists_mul p hp
  refine ⟨x, hx, b * z * b⁻¹, hZ.norm b hb z hz, by group⟩

end Frame

end FA5

end CFSG.Quasithin

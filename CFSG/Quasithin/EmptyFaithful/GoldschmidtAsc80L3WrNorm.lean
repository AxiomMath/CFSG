module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtAsc80L3WrCen

public section

namespace CFSG.Quasithin.E2P.Asc80

open Matrix CFSG.Quasithin.A38c15 CFSG.Quasithin.B6 CFSG.QuasithinUnique
open scoped MatrixGroups

variable {p : ℕ} [Fact p.Prime]

theorem piL_xE_mem_evenC {i : (ZMod p)ˣ} (hi4 : i ^ 4 = 1) : piL p (xE i) ∈ evenC p := by
  have hm : ((i, 1) : (ZMod p)ˣ × (ZMod p)ˣ) ∈ fourK p := by
    rw [fourK, MonoidHom.mem_ker, powMonoidHom_apply, Prod.pow_def]
    exact Prod.ext hi4 (one_pow 4)
  exact ⟨xE i, ⟨(i, 1), hm, rfl⟩, rfl⟩

theorem piL_xO_mem_commutator {i : (ZMod p)ˣ} (hi4 : i ^ 4 = 1) {U : Subgroup (PSL3 p)}
    (hE : evenC p ≤ U) (hUm : U ≤ monoC p) (hUD : ¬ U ≤ diagC p) :
    piL p (xO i) ∈ ⁅U, U⁆ := by
  obtain ⟨s, hsU, hsD⟩ := Set.not_subset.mp hUD
  obtain ⟨g, hgm, rfl⟩ := hUm hsU
  obtain ⟨h02, h12, h20, h21, ⟨h01, h10⟩ | ⟨h00, h11⟩⟩ := hgm
  · exact absurd ⟨g, ⟨h01, h02, h10, h12, h20, h21⟩, rfl⟩ hsD
  · have hx := xE_mul_eq i h02 h12 h20 h21 h00 h11
    have h1 : xE i * g * (xE i)⁻¹ = xO i * g := mul_inv_eq_iff_eq_mul.mpr hx
    have hc : xE i * g * (xE i)⁻¹ * g⁻¹ = xO i := by
      rw [h1]
      simp
    have hmem := Subgroup.commutator_mem_commutator (hE (piL_xE_mem_evenC hi4)) hsU
    rw [commutatorElement_def] at hmem
    have e : piL p (xE i) * piL p g * (piL p (xE i))⁻¹ * (piL p g)⁻¹ = piL p (xO i) := by
      rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hc]
    rwa [e] at hmem

theorem commutator_le_diagC {U : Subgroup (PSL3 p)} (hUm : U ≤ monoC p) : ⁅U, U⁆ ≤ diagC p :=
  (Subgroup.commutator_mono hUm hUm).trans commutator_monoC_le_diagC

theorem centralizer_commutator_eq_diagC (hp2 : p ≠ 2) {i : (ZMod p)ˣ}
    (hi : (i : ZMod p) ^ 2 = -1) {U : Subgroup (PSL3 p)} (hE : evenC p ≤ U) (hUm : U ≤ monoC p)
    (hUD : ¬ U ≤ diagC p) :
    Subgroup.centralizer ((⁅U, U⁆ : Subgroup (PSL3 p)) : Set (PSL3 p)) = diagC p := by
  apply le_antisymm
  · intro g hg
    obtain ⟨g, rfl⟩ := piL_surjective g
    have h := Subgroup.mem_centralizer_iff.mp hg _
      (piL_xO_mem_commutator (pow_four_eq_one hi) hE hUm hUD)
    exact ⟨g, mem_diagT_of_commute_xO hp2 hi h.symm, rfl⟩
  · intro g hg
    exact Subgroup.mem_centralizer_iff.mpr fun h hh => diagC_comm (commutator_le_diagC hUm hh) hg

theorem exists_wreathed_normalizer (hp : p % 4 = 1) :
    ∃ U : Subgroup (PSL3 p), IsSylowTwoOf U ⊤ ∧ U ≤ leviC p ∧ ⁅U, U⁆ ≠ ⊥ ∧
      (∀ a ∈ ⁅U, U⁆, ∀ b ∈ ⁅U, U⁆, a * b = b * a) ∧
      ¬ Subgroup.normalizer (Subgroup.centralizer ((⁅U, U⁆ : Subgroup (PSL3 p)) : Set (PSL3 p)) :
          Set (PSL3 p)) ≤ leviC p := by
  have hp2 : p ≠ 2 := fun h => by
    rw [h] at hp
    omega
  obtain ⟨i0, hi0⟩ := ZMod.exists_sq_eq_neg_one_iff.mpr (by omega : p % 4 ≠ 3)
  have hi00 : i0 ≠ 0 := fun h => by
    rw [h] at hi0
    simp at hi0
  obtain ⟨i, hi⟩ : ∃ i : (ZMod p)ˣ, (i : ZMod p) ^ 2 = -1 :=
    ⟨Units.mk0 i0 hi00, by
      show i0 ^ 2 = -1
      rw [hi0]
      ring⟩
  obtain ⟨U, hU, hUm, hEU, hUD⟩ := exists_wreathed_sylow hp
  refine ⟨U, hU, hUm.trans monoC_le_leviC, ?_, fun a ha b hb =>
    diagC_comm (commutator_le_diagC hUm ha) (commutator_le_diagC hUm hb), ?_⟩
  · intro hbot
    have hmem := piL_xO_mem_commutator (pow_four_eq_one hi) hEU hUm hUD
    rw [hbot] at hmem
    have hk : xO i ∈ Subgroup.center SL(3, ZMod p) := by
      rw [← ker_piL]
      exact Subgroup.mem_bot.mp hmem
    obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hk
    have e00 := congrFun (congrFun hr 0) 0
    have e11 := congrFun (congrFun hr 1) 1
    rw [coe_xO] at e00 e11
    simp only [Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.cons_val_zero,
      Matrix.cons_val_one] at e00 e11
    rw [val_inv_eq_neg hi] at e11
    have h2i : (2 : ZMod p) * (i : ZMod p) = 0 := by linear_combination e11 - e00
    exact (Units.ne_zero i) ((mul_eq_zero.mp h2i).resolve_left (two_ne_zero_zmod hp2))
  · intro hN
    have hw : piL p (w13 p) ∈ Subgroup.normalizer (Subgroup.centralizer
        ((⁅U, U⁆ : Subgroup (PSL3 p)) : Set (PSL3 p)) : Set (PSL3 p)) := by
      rw [centralizer_commutator_eq_diagC hp2 hi hEU hUm hUD]
      exact piL_w13_mem_normalizer
    exact piL_w13_not_mem_leviC (hN hw)

end CFSG.Quasithin.E2P.Asc80

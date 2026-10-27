module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4E9
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4RowM4HeisConj
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit Subgroup

private theorem m4_commute_z_of_mem_closure {G : Type*} [Group G] {n : ℕ} {x y : Fin n → G}
    {z : G} (h : HeisCfg 3 n x y z) {g : G}
    (hg : g ∈ Subgroup.closure (Set.range x ∪ Set.range y ∪ {z})) : g * z = z * g := by
  induction hg using Subgroup.closure_induction with
  | mem g hg =>
      simp only [Set.mem_union, Set.mem_range, Set.mem_singleton_iff] at hg
      rcases hg with (⟨i, rfl⟩ | ⟨i, rfl⟩) | hg
      · exact h.zx i
      · exact h.zy i
      · rw [hg]
  | one => simp
  | mul a b _ _ ha hb => rw [mul_assoc, hb, ← mul_assoc, ha, mul_assoc]
  | inv a _ ha =>
      calc a⁻¹ * z = a⁻¹ * (z * a) * a⁻¹ := by group
        _ = a⁻¹ * (a * z) * a⁻¹ := by rw [← ha]
        _ = z * a⁻¹ := by group

private theorem m4_cube_eq_of_heis {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {n : ℕ} {x y : Fin n → MulAut W} {z : MulAut W}
    (h : HeisCfg 3 n x y z) (hy : ∀ i, y i ^ 3 = 1) {u : MulAut W}
    (hu : u ∈ Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}))
    (huz : u ∉ zpowers z) (hu3 : u ^ 3 = 1) :
    (fixV (zpowers u ⊔ zpowers z)).index ^ 3 =
        (fixV (zpowers z)).index * (fixV (zpowers u)).index *
          (fixV (zpowers (u * z))).index * (fixV (zpowers (u * z ^ 2))).index ∧
      (fixV (zpowers (u * z))).index = (fixV (zpowers u)).index ∧
      (fixV (zpowers (u * z ^ 2))).index = (fixV (zpowers u)).index := by
  have hz3 : z ^ 3 = 1 := h.zp
  have hu1 : u ≠ 1 := fun h1 => huz (h1 ▸ (zpowers z).one_mem)
  have hcomm : u * z = z * u := m4_commute_z_of_mem_closure h hu
  have hbaz : ∀ j < 3, z ≠ u ^ j := by
    intro j hj
    interval_cases j
    · simpa using h.z1
    · intro hzu
      apply huz
      rw [show u = z from by simpa using hzu.symm]
      exact Subgroup.mem_zpowers z
    · intro hz2
      apply huz
      have hzu1 : u * z = 1 := by
        have h : z * u = 1 := by
          rw [hz2, ← pow_succ, show 2 + 1 = 3 by norm_num, hu3]
        exact hcomm.trans h
      have hu_eq : u = z⁻¹ := eq_inv_of_mul_eq_one_left hzu1
      have hz2' : z ^ 2 = z⁻¹ := by
        apply eq_inv_of_mul_eq_one_right
        rw [← pow_succ', show 2 + 1 = 3 by norm_num, hz3]
      rw [show u = z ^ 2 by rw [hu_eq, ← hz2']]
      exact Subgroup.pow_mem (zpowers z) (Subgroup.mem_zpowers z) 2
  obtain ⟨q, hq, hqconj⟩ := exists_conj_eq_mul_of_mem_heis h hy hu huz
  have h1 : (fixV (zpowers (u * z))).index = (fixV (zpowers u)).index := by
    have h := CFSG.Quasithin.FixVLat.index_fixV_zpowers_conj q⁻¹ u
    rwa [inv_inv, hqconj] at h
  have hqconj2 : q⁻¹ * (u * z) * q = u * z ^ 2 := by
    have hqz : q⁻¹ * z * q = z := by
      have hc : q * z = z * q := m4_commute_z_of_mem_closure h hq
      calc q⁻¹ * z * q = q⁻¹ * (z * q) := by group
        _ = q⁻¹ * (q * z) := by rw [← hc]
        _ = z := by group
    calc q⁻¹ * (u * z) * q = (q⁻¹ * u * q) * (q⁻¹ * z * q) := by group
      _ = (u * z) * z := by rw [hqconj, hqz]
      _ = u * z ^ 2 := by rw [pow_two, mul_assoc]
  have h2 : (fixV (zpowers (u * z ^ 2))).index = (fixV (zpowers u)).index := by
    have h := CFSG.Quasithin.FixVLat.index_fixV_zpowers_conj q⁻¹ (u * z)
    rw [inv_inv, hqconj2] at h
    exact h.trans h1
  refine ⟨?_, h1, h2⟩
  rw [index_fixV_cube_eq_prod_of_e9 hW hu3 hz3 hu1 hcomm hbaz]
  ac_rfl

theorem two_pow_four_mul_le_index_cube_of_heis_conj {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {n : ℕ} {x y : Fin n → MulAut W} {z : MulAut W}
    (h : HeisCfg 3 n x y z) (hy : ∀ i, y i ^ 3 = 1) {e : ℕ}
    (hz : 2 ^ e ≤ (fixV (zpowers z)).index) {u : MulAut W}
    (hu : u ∈ Subgroup.closure (Set.range x ∪ Set.range y ∪ {z}))
    (huz : u ∉ zpowers z) (hconj : ∃ g : MulAut W, g * z * g⁻¹ = u) :
    2 ^ (4 * e) ≤ (fixV (zpowers u ⊔ zpowers z)).index ^ 3 := by
  obtain ⟨g, hg⟩ := hconj
  have hu3 : u ^ 3 = 1 := by
    rw [← hg]
    simp [h.zp]
  have hdzu : (fixV (zpowers u)).index = (fixV (zpowers z)).index := by
    have h := CFSG.Quasithin.FixVLat.index_fixV_zpowers_conj g z
    rwa [hg] at h
  obtain ⟨hcube, h1, h2⟩ := m4_cube_eq_of_heis hW h hy hu huz hu3
  have hfinal : (fixV (zpowers u ⊔ zpowers z)).index ^ 3 = (fixV (zpowers z)).index ^ 4 := by
    rw [hcube, h1, h2, hdzu]
    ring
  calc 2 ^ (4 * e) = (2 ^ e) ^ 4 := by rw [Nat.mul_comm 4 e, pow_mul]
    _ ≤ (fixV (zpowers z)).index ^ 4 := Nat.pow_le_pow_left hz 4
    _ = (fixV (zpowers u ⊔ zpowers z)).index ^ 3 := hfinal.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

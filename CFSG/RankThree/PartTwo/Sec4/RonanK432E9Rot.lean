module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432SylowCenter
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

theorem listRow_of_E9_rotation {S : Type} [Group S] [Finite S] {a b r : S}
    (hab : a * b = b * a) (hrot : r * a * r⁻¹ = b) (hrot' : r * b * r⁻¹ = a⁻¹)
    (hQ : Nat.card (Subgroup.closure ({a, b} : Set S)) = 9) (hS : ¬ 27 ∣ Nat.card S) :
    ListRow S := by
  set Q : Subgroup S := Subgroup.closure ({a, b} : Set S) with hQdef
  have haQ : a ∈ Q := Subgroup.subset_closure (by simp)
  have hbQ : b ∈ Q := Subgroup.subset_closure (by simp)
  have hcentab : ∀ x ∈ Q, x * a = a * x ∧ x * b = b * x := by
    intro x hx
    have hsub : Q ≤ Subgroup.centralizer ({a, b} : Set S) := by
      rw [hQdef, Subgroup.closure_le]
      intro y hy
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro z hz
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy hz
      rcases hy with rfl | rfl <;> rcases hz with rfl | rfl
      · rfl
      · exact hab.symm
      · exact hab
      · rfl
    have := Subgroup.mem_centralizer_iff.mp (hsub hx)
    exact ⟨(this a (by simp)).symm, (this b (by simp)).symm⟩
  have hcomm : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
    intro x hx y hy
    have hsub : Q ≤ Subgroup.centralizer ({x} : Set S) := by
      rw [hQdef, Subgroup.closure_le]
      intro z hz
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      subst hw
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
      rcases hz with rfl | rfl
      · exact (hcentab w hx).1
      · exact (hcentab w hx).2
    have := Subgroup.mem_centralizer_iff.mp (hsub hy) x (Set.mem_singleton x)
    exact this
  have hrQ : ∀ x ∈ Q, r * x * r⁻¹ ∈ Q := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · rw [hrot]; exact hbQ
      · rw [hrot']; exact inv_mem haQ
    | one => simpa using Q.one_mem
    | mul y z _ _ hy hz =>
      have : r * (y * z) * r⁻¹ = (r * y * r⁻¹) * (r * z * r⁻¹) := by group
      rw [this]; exact Q.mul_mem hy hz
    | inv y _ hy =>
      have : r * y⁻¹ * r⁻¹ = (r * y * r⁻¹)⁻¹ := by group
      rw [this]; exact Q.inv_mem hy
  have hinv : ∀ x ∈ Q, r * r * x * (r * r)⁻¹ = x⁻¹ := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem y hy =>
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl
      · calc r * r * y * (r * r)⁻¹ = r * (r * y * r⁻¹) * r⁻¹ := by group
          _ = y⁻¹ := by rw [hrot, hrot']
      · calc r * r * y * (r * r)⁻¹ = r * (r * y * r⁻¹) * r⁻¹ := by group
          _ = y⁻¹ := by
            rw [hrot']
            calc r * a⁻¹ * r⁻¹ = (r * a * r⁻¹)⁻¹ := by group
              _ = y⁻¹ := by rw [hrot]
    | one => simp
    | mul y z hyQ hzQ hy hz =>
      have e : r * r * (y * z) * (r * r)⁻¹ = (r * r * y * (r * r)⁻¹) * (r * r * z * (r * r)⁻¹) := by
        group
      rw [e, hy, hz, ← mul_inv_rev, hcomm y hyQ z hzQ]
    | inv y _ hy =>
      have key : ∀ t w : S, t * w⁻¹ * t⁻¹ = (t * w * t⁻¹)⁻¹ := fun t w => by group
      rw [key, hy]
  have hQ' : Nat.card Q = 3 ^ 2 := by rw [hQ]; norm_num
  have hS' : ¬ 3 ^ (2 + 1) ∣ Nat.card S := by norm_num; exact hS
  refine listRow_of_sylow_center 2 Q hQ' hS' fun u huQ huo _ => ?_
  refine ⟨r, ?_, ?_⟩
  · exact hcomm _ (hrQ u huQ) u huQ
  · intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hcalc : r * r * u * (r * r)⁻¹ = u ^ (k * k) := by
      have e1 : r * r * u * (r * r)⁻¹ = r * (r * u * r⁻¹) * r⁻¹ := by group
      have e2 : r * (u ^ k) * r⁻¹ = (r * u * r⁻¹) ^ k := (conj_zpow).symm
      rw [e1, ← hk, e2, ← hk, ← zpow_mul]
    have h2 : u ^ (k * k) = u⁻¹ := hcalc.symm.trans (hinv u huQ)
    have h3 : u ^ (k * k + 1) = 1 := by
      rw [zpow_add_one, h2, inv_mul_cancel]
    have h4 : (orderOf u : ℤ) ∣ k * k + 1 := orderOf_dvd_iff_zpow_eq_one.mpr h3
    rw [huo] at h4
    have h5 : (((k * k + 1 : ℤ)) : ZMod 3) = 0 :=
      (ZMod.intCast_zmod_eq_zero_iff_dvd _ 3).mpr (by exact_mod_cast h4)
    push_cast at h5
    have h6 : ∀ x : ZMod 3, x * x + 1 ≠ 0 := by decide
    exact h6 _ h5

end CFSG.RankThree.PartTwo.Sec4.RonanK432

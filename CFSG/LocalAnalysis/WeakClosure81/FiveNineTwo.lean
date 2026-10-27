module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.LargeExtraspecial.S9TIInput
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

private theorem b5_FiveNineTwo_isSolvable_of_closure_pair {Γ : Type*} [Group Γ] {t s : Γ}
    (ht : t * t = 1)
    (hs : s * s = 1) (hgen : Subgroup.closure ({t, s} : Set Γ) = ⊤) : Group.IsSolvable Γ := by
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have key : ∀ g : Γ, g * g = 1 → g * (t * s) * g⁻¹ = (t * s)⁻¹ →
      ∀ h ∈ Subgroup.zpowers (t * s), g * h * g⁻¹ ∈ Subgroup.zpowers (t * s) := by
    intro g _ hg h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    rw [← conj_zpow, hg, inv_zpow']
    exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hnorm : ∀ g : Γ, g * g = 1 → g * (t * s) * g⁻¹ = (t * s)⁻¹ →
      g ∈ Subgroup.normalizer ((Subgroup.zpowers (t * s) : Subgroup Γ) : Set Γ) := by
    intro g hgg hg
    rw [Subgroup.mem_normalizer_iff]
    intro h
    refine ⟨fun hh => key g hgg hg h hh, fun hh => ?_⟩
    have h2 := key g hgg hg _ hh
    have hginv : g⁻¹ = g := inv_eq_of_mul_eq_one_right hgg
    have : g * (g * h * g⁻¹) * g⁻¹ = h := by
      rw [hginv]
      calc g * (g * h * g) * g = (g * g) * h * (g * g) := by group
        _ = h := by rw [hgg]; simp
    rwa [this] at h2
  have htn : t ∈ Subgroup.normalizer ((Subgroup.zpowers (t * s) : Subgroup Γ) : Set Γ) := by
    refine hnorm t ht ?_
    rw [ht']
    calc t * (t * s) * t = (t * t) * s * t := by group
      _ = (t * s)⁻¹ := by rw [ht]; simp [mul_inv_rev, hs', ht']
  have hsn : s ∈ Subgroup.normalizer ((Subgroup.zpowers (t * s) : Subgroup Γ) : Set Γ) := by
    refine hnorm s hs ?_
    rw [hs']
    calc s * (t * s) * s = s * t * (s * s) := by group
      _ = (t * s)⁻¹ := by rw [hs]; simp [mul_inv_rev, hs', ht']
  have hCn : (Subgroup.zpowers (t * s)).Normal := by
    rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← hgen, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · exact htn
    · simpa using hsn
  have hQ : ∀ x : Γ ⧸ Subgroup.zpowers (t * s),
      x ∈ Subgroup.zpowers (QuotientGroup.mk' (Subgroup.zpowers (t * s)) t) := by
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk'_surjective _ x
    have hg : g ∈ Subgroup.closure ({t, s} : Set Γ) := by rw [hgen]; trivial
    induction hg using Subgroup.closure_induction with
    | mem y hy =>
      rcases hy with rfl | hy
      · exact Subgroup.mem_zpowers _
      · rw [Set.mem_singleton_iff] at hy
        subst hy
        have h1 : QuotientGroup.mk' (Subgroup.zpowers (t * y)) (t * y) = 1 :=
          (QuotientGroup.eq_one_iff _).2 (Subgroup.mem_zpowers _)
        have h2 : QuotientGroup.mk' (Subgroup.zpowers (t * y)) y =
            (QuotientGroup.mk' (Subgroup.zpowers (t * y)) t)⁻¹ := by
          rw [map_mul] at h1
          exact (eq_inv_of_mul_eq_one_right h1)
        rw [h2]
        exact Subgroup.inv_mem _ (Subgroup.mem_zpowers _)
    | one => exact Subgroup.one_mem _
    | mul x y _ _ hx hy => rw [map_mul]; exact Subgroup.mul_mem _ hx hy
    | inv x _ hx => rw [map_inv]; exact Subgroup.inv_mem _ hx
  have hcommQ : ∀ x y : Γ ⧸ Subgroup.zpowers (t * s), x * y = y * x := by
    intro x y
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 (hQ x)
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (hQ y)
    rw [← hi, ← hj]
    exact (Commute.refl _).zpow_zpow i j |>.eq
  haveI : Group.IsSolvable (Γ ⧸ Subgroup.zpowers (t * s)) := isSolvable_of_comm hcommQ
  haveI : Group.IsSolvable ↥(Subgroup.zpowers (t * s)) := by
    refine isSolvable_of_comm ?_
    intro a b
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.1 a.2
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 b.2
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hi, ← hj]
    exact ((Commute.refl _).zpow_zpow i j).eq
  exact solvable_of_ker_le_range (Subgroup.zpowers (t * s)).subtype
    (QuotientGroup.mk' (Subgroup.zpowers (t * s))) (by simp [QuotientGroup.ker_mk'])

theorem isSolvable_sup_zpowers_of_mul_self_eq_one {t s : G} (ht : t * t = 1) (hs : s * s = 1) :
    Group.IsSolvable ↥(zpowers t ⊔ zpowers s) := by
  have hD : zpowers t ⊔ zpowers s = Subgroup.closure ({t, s} : Set G) := by
    rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
      ← Subgroup.zpowers_eq_closure]
  rw [hD]
  have htD : t ∈ Subgroup.closure ({t, s} : Set G) := Subgroup.subset_closure (by simp)
  have hsD : s ∈ Subgroup.closure ({t, s} : Set G) := Subgroup.subset_closure (by simp)
  refine b5_FiveNineTwo_isSolvable_of_closure_pair (t := ⟨t, htD⟩) (s := ⟨s, hsD⟩) ?_ ?_ ?_
  · exact Subtype.ext ht
  · exact Subtype.ext hs
  · have := Subgroup.closure_closure_coe_preimage (k := ({t, s} : Set G))
    convert this using 2
    ext x
    simp [Subtype.ext_iff]

end CFSG.LocalAnalysis.WeakClosure81

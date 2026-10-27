module

public import CFSG.LocalAnalysis.StandardType.GGTriD4LineWeylData
import CFSG.LocalAnalysis.StandardType.GGTableBStdSub

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

private theorem mulAutConj_apply_apply {G : Type*} [Group G] (β : MulAut G) (a : MulAut G)
    (x : G) : (MulAut.conj β : MulAut (MulAut G)) a x = β (a (β⁻¹ x)) := by
  rw [MulAut.conj_apply, MulAut.mul_apply, MulAut.mul_apply]

private theorem mulAutConj_conjAut {G : Type*} [Group G] (β : MulAut G) (m : G) :
    (MulAut.conj β : MulAut (MulAut G)) (MulAut.conj m) = MulAut.conj (β m) := by
  ext x
  simp only [MulAut.conj_apply, MulAut.mul_apply, map_mul, map_inv]
  simp

private theorem apply_apply_inv {G : Type*} [Group G] (β : MulAut G) (a : MulAut G) (x : G) :
    a (β⁻¹ x) = β⁻¹ (((MulAut.conj β : MulAut (MulAut G)) a) x) := by
  rw [mulAutConj_apply_apply]
  simp

private theorem conj_mem_zpowers_iff {G : Type*} [Group G] (β : MulAut G) (x y : MulAut G) :
    (MulAut.conj β : MulAut (MulAut G)) x ∈
        Subgroup.zpowers ((MulAut.conj β : MulAut (MulAut G)) y) ↔
      x ∈ Subgroup.zpowers y := by
  rw [Subgroup.mem_zpowers_iff, Subgroup.mem_zpowers_iff]
  constructor
  · rintro ⟨k, hk⟩
    exact ⟨k, (MulAut.conj β).injective (by rw [map_zpow]; exact hk)⟩
  · rintro ⟨k, hk⟩
    exact ⟨k, by rw [← map_zpow, hk]⟩

private theorem ggFix_conj {G : Type*} [Group G] (β : MulAut G) (a : MulAut G) :
    ggFix ((MulAut.conj β : MulAut (MulAut G)) a) = (ggFix a).map β.toMonoidHom := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · intro hx
    refine ⟨β⁻¹ x, ?_, ?_⟩
    · change a (β⁻¹ x) = β⁻¹ x
      have hβ : β (a (β⁻¹ x)) = x := by
        rw [← mulAutConj_apply_apply]
        exact hx
      calc a (β⁻¹ x) = β⁻¹ (β (a (β⁻¹ x))) := by simp
        _ = β⁻¹ x := by rw [hβ]
    · simp
  · rintro ⟨y, hy, rfl⟩
    change (MulAut.conj β : MulAut (MulAut G)) a (β y) = β y
    rw [mulAutConj_apply_apply, MulAut.inv_apply, MulEquiv.symm_apply_apply]
    exact congrArg β (show a y = y from hy)

private theorem mul_mulAut_apply_inv {G : Type*} [Group G] (β : MulAut G) (a : MulAut G)
    (m : G) :
    β⁻¹ m * (a (β⁻¹ m))⁻¹ =
      β⁻¹ (m * (((MulAut.conj β : MulAut (MulAut G)) a) m)⁻¹) := by
  rw [apply_apply_inv]
  simp only [map_mul, map_inv]

private theorem conjAut_map_conj_inv {G : Type*} [Group G] (β : MulAut G) (a : MulAut G)
    (m : G) :
    (MulAut.conj β : MulAut (MulAut G))
        (MulAut.conj (β⁻¹ m) * a * (MulAut.conj (β⁻¹ m))⁻¹) =
      MulAut.conj m * (MulAut.conj β) a * (MulAut.conj m)⁻¹ := by
  rw [map_mul, map_mul, map_inv, mulAutConj_conjAut]
  simp

theorem triD4LineAlt_of_conj {n : ℕ} (K : Type) [Field K] (β : MulAut (GGTriD4R n K))
    (A : Subgroup (MulAut (GGTriD4R n K))) (a₀ : MulAut (GGTriD4R n K)) :
    triD4LineAlt n K (A.map (MulAut.conj β).toMonoidHom) (MulAut.conj β a₀) →
      triD4LineAlt n K A a₀ := by
  intro h
  unfold triD4LineAlt at h ⊢
  rcases h with ⟨m', hclause, hnot⟩ | ⟨f', hf'A', hf', hfix⟩
  · refine Or.inl ⟨β⁻¹ m', ?_, ?_⟩
    · intro a ha
      constructor
      · have ha' : (MulAut.conj β) a ∈ A.map (MulAut.conj β).toMonoidHom :=
          Subgroup.mem_map_of_mem (MulAut.conj β).toMonoidHom ha
        have hx := (hclause ((MulAut.conj β) a) ha').1
        rw [mul_mulAut_apply_inv, ← map_pow, hx, map_one]
      · intro a'' ha''
        have ha' : (MulAut.conj β) a ∈ A.map (MulAut.conj β).toMonoidHom :=
          Subgroup.mem_map_of_mem (MulAut.conj β).toMonoidHom ha
        have ha''' : (MulAut.conj β) a'' ∈ A.map (MulAut.conj β).toMonoidHom :=
          Subgroup.mem_map_of_mem (MulAut.conj β).toMonoidHom ha''
        have hx := (hclause ((MulAut.conj β) a) ha').2 ((MulAut.conj β) a'') ha'''
        rw [mul_mulAut_apply_inv, apply_apply_inv, hx]
    · intro hmem
      apply hnot
      rw [← conjAut_map_conj_inv]
      exact (conj_mem_zpowers_iff β _ a₀).mpr hmem
  · have hfinv : (MulAut.conj β : MulAut (MulAut (GGTriD4R n K)))
        ((MulAut.conj β)⁻¹ f') = f' := by
      rw [MulAut.inv_apply, MulEquiv.apply_symm_apply]
    refine Or.inr ⟨(MulAut.conj β)⁻¹ f', ?_, ?_, ?_⟩
    · obtain ⟨a, ha, haeq⟩ := Subgroup.mem_map.mp hf'A'
      have haeq' : (MulAut.conj β) a = f' := haeq
      have hfa : (MulAut.conj β)⁻¹ f' = a := by
        rw [← haeq', MulAut.inv_apply, MulEquiv.symm_apply_apply]
      rw [hfa]
      exact ha
    · intro hmem
      apply hf'
      have := (conj_mem_zpowers_iff β ((MulAut.conj β)⁻¹ f') a₀).mpr hmem
      rwa [hfinv] at this
    · intro J₁ hJ l hl
      have hJ' : IsComponentOf (J₁.map β.toMonoidHom) (ggFix ((MulAut.conj β) a₀)) := by
        rw [ggFix_conj]
        exact isComponentOf_map_of_injective β.toMonoidHom β.injective hJ
      have hl' : β l ∈ J₁.map β.toMonoidHom := Subgroup.mem_map_of_mem β.toMonoidHom hl
      have hfl := hfix (J₁.map β.toMonoidHom) hJ' (β l) hl'
      have h2 : β (((MulAut.conj β)⁻¹ f') l) = β l := by
        have hthis : β (((MulAut.conj β)⁻¹ f') l) = f' (β l) := by
          have h := mulAutConj_apply_apply β ((MulAut.conj β)⁻¹ f') (β l)
          rw [hfinv] at h
          simpa only [MulAut.inv_apply, MulEquiv.symm_apply_apply] using h.symm
        rw [hthis, hfl]
      exact β.injective h2

end CFSG.StandardType

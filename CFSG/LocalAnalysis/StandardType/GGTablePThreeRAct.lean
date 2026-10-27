module

public import CFSG.LocalAnalysis.StandardType.GGTablePThreeSplitR

public section

namespace CFSG.StandardType.TablePThreeKG

open CFSG CFSG.Assembly

private theorem mulAut_eq_of_perfect_of_mem_center {X : Type*} [Group X] (a : MulAut X)
    (J : Subgroup X) (hJ : commutator J = ⊤)
    (h : ∀ j ∈ J, j⁻¹ * a j ∈ Subgroup.center X) : ∀ j ∈ J, a j = j := by
  haveI : Group.IsPerfect J := ⟨hJ⟩
  let f : J → Subgroup.center X := fun j => ⟨(j : X)⁻¹ * a (j : X), h j j.2⟩
  have hf_one : f 1 = 1 := by
    apply Subtype.ext
    simp [f]
  have hf_mul : ∀ p q : J, f (p * q) = f p * f q := by
    intro p q
    apply Subtype.ext
    have hp : (p : X)⁻¹ * a (p : X) ∈ Subgroup.center X := h p p.2
    have hpq : (q : X)⁻¹ * ((p : X)⁻¹ * a (p : X))
        = ((p : X)⁻¹ * a (p : X)) * (q : X)⁻¹ :=
      (Subgroup.mem_center_iff.mp hp) (q : X)⁻¹
    simp only [f, Subgroup.coe_mul, map_mul, mul_inv_rev, Subtype.coe_mk]
    calc ((q : X)⁻¹ * (p : X)⁻¹) * (a (p : X) * a (q : X))
        = (q : X)⁻¹ * (((p : X)⁻¹ * a (p : X)) * a (q : X)) := by group
      _ = ((q : X)⁻¹ * ((p : X)⁻¹ * a (p : X))) * a (q : X) := by group
      _ = (((p : X)⁻¹ * a (p : X)) * (q : X)⁻¹) * a (q : X) := by rw [hpq]
      _ = ((p : X)⁻¹ * a (p : X)) * ((q : X)⁻¹ * a (q : X)) := by group
  let φ : J →* Subgroup.center X :=
    { toFun := f, map_one' := hf_one, map_mul' := hf_mul }
  haveI hperf : Group.IsPerfect φ.range := Group.IsPerfect.range (f := φ)
  haveI hcomm : IsMulCommutative φ.range := inferInstance
  haveI : Subsingleton φ.range :=
    Group.IsPerfect.subsingleton_of_isMulCommutative (G := φ.range)
  have hbot : φ.range = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    exact congrArg Subtype.val (Subsingleton.elim (⟨x, hx⟩ : φ.range) 1)
  have hφ : φ = 1 := MonoidHom.range_eq_bot_iff.mp hbot
  intro j hj
  have h1 : φ ⟨j, hj⟩ = 1 := by rw [hφ]; rfl
  have h2 : (j : X)⁻¹ * a j = 1 := by
    have := congrArg Subtype.val h1
    simpa [φ, f] using this
  exact (inv_mul_eq_one.mp h2).symm

theorem leafRAct_holds :
    ∀ (X : Type) [Group X] (R : Type) [Group R] (θ : X ⧸ Subgroup.center X ≃* R) (J : Subgroup X),
      commutator J = ⊤ →
      (∀ a : MulAut X, (∀ j ∈ J, a j ∈ J) →
          ∀ j ∈ J.map (proj θ), ggInducedAut θ a j ∈ J.map (proj θ)) ∧
        ∀ a : MulAut X, (∀ j ∈ J.map (proj θ), ggInducedAut θ a j = j) → ∀ j ∈ J, a j = j := by
  intro X _ R _ θ J hJ
  refine ⟨?_, ?_⟩
  · intro a ha j hj
    rw [Subgroup.mem_map] at hj ⊢
    obtain ⟨x, hx, rfl⟩ := hj
    refine ⟨a x, ha x hx, ?_⟩
    exact (ggInducedAut_apply θ a x).symm
  · intro a ha j hj
    refine mulAut_eq_of_perfect_of_mem_center a J hJ ?_ j hj
    intro k hk
    have hfix : ggInducedAut θ a (proj θ k) = proj θ k :=
      ha (proj θ k) (Subgroup.mem_map.mpr ⟨k, hk, rfl⟩)
    have h1 : θ ((a k : X) : X ⧸ Subgroup.center X) = θ ((k : X) : X ⧸ Subgroup.center X) := by
      rw [← ggInducedAut_apply θ a k]
      exact hfix
    have h2 : ((a k : X) : X ⧸ Subgroup.center X) = ((k : X) : X ⧸ Subgroup.center X) :=
      θ.injective h1
    have h3 : ((a k)⁻¹ * k) ∈ Subgroup.center X := QuotientGroup.eq.mp h2
    have h4 : k⁻¹ * a k ∈ Subgroup.center X := by
      have := inv_mem h3
      simpa [mul_inv_rev, inv_inv] using this
    exact h4

end CFSG.StandardType.TablePThreeKG

end

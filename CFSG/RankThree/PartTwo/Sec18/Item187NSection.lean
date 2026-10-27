module

public import Mathlib.GroupTheory.PGroup

public section

open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

section Section

variable {G : Type} [Group G] [Finite G]

private theorem map_normalizerMonoidHom_subgroupOf {W₀ W₁ : Subgroup G} {g : G}
    (hg0 : g ∈ Subgroup.normalizer (W₀ : Set G)) (hg1 : g ∈ Subgroup.normalizer (W₁ : Set G)) :
    (W₀.subgroupOf W₁).map ((W₁.normalizerMonoidHom ⟨g, hg1⟩ : MulAut ↥W₁) : ↥W₁ →* ↥W₁) =
      W₀.subgroupOf W₁ := by
  ext y
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨z, hz, rfl⟩
    rw [Subgroup.mem_subgroupOf] at hz ⊢
    exact (Subgroup.mem_normalizer_iff.mp hg0 _).mp hz
  · intro hy
    rw [Subgroup.mem_subgroupOf] at hy
    have e : g * ((g⁻¹ * (y : G)) * g) * g⁻¹ = y := by group
    have hW1 : g⁻¹ * (y : G) * g ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp hg1 _).mpr (by rw [e]; exact y.2)
    have hW0 : g⁻¹ * (y : G) * g ∈ W₀ :=
      (Subgroup.mem_normalizer_iff.mp hg0 _).mpr (by rw [e]; exact hy)
    refine ⟨⟨g⁻¹ * (y : G) * g, hW1⟩, Subgroup.mem_subgroupOf.mpr hW0, Subtype.ext e⟩

noncomputable def secAct {Γ W₀ W₁ : Subgroup G} [(W₀.subgroupOf W₁).Normal]
    (h₀ : Γ ≤ Subgroup.normalizer (W₀ : Set G)) (h₁ : Γ ≤ Subgroup.normalizer (W₁ : Set G)) :
    ↥Γ →* MulAut (↥W₁ ⧸ W₀.subgroupOf W₁) where
  toFun g := QuotientGroup.congr (W₀.subgroupOf W₁) (W₀.subgroupOf W₁)
    (W₁.normalizerMonoidHom ⟨(g : G), h₁ g.2⟩)
    (map_normalizerMonoidHom_subgroupOf (h₀ g.2) (h₁ g.2))
  map_one' := by
    apply MulEquiv.ext
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [QuotientGroup.congr_mk, MulAut.one_apply]
    congr 1
    exact Subtype.ext (by simp)
  map_mul' a b := by
    apply MulEquiv.ext
    intro x
    obtain ⟨u, rfl⟩ := QuotientGroup.mk_surjective x
    rw [MulAut.mul_apply, QuotientGroup.congr_mk, QuotientGroup.congr_mk,
      QuotientGroup.congr_mk]
    congr 1
    exact Subtype.ext (by simp [mul_assoc])

theorem secAct_mk {Γ W₀ W₁ : Subgroup G} [(W₀.subgroupOf W₁).Normal]
    (h₀ : Γ ≤ Subgroup.normalizer (W₀ : Set G)) (h₁ : Γ ≤ Subgroup.normalizer (W₁ : Set G))
    (g : ↥Γ) (w : ↥W₁) (hw : (g : G) * w * (g : G)⁻¹ ∈ W₁) :
    secAct h₀ h₁ g (QuotientGroup.mk w) =
      QuotientGroup.mk ⟨(g : G) * w * (g : G)⁻¹, hw⟩ := by
  have e : secAct h₀ h₁ g = QuotientGroup.congr (W₀.subgroupOf W₁) (W₀.subgroupOf W₁)
      (W₁.normalizerMonoidHom ⟨(g : G), h₁ g.2⟩)
      (map_normalizerMonoidHom_subgroupOf (h₀ g.2) (h₁ g.2)) := rfl
  rw [e, QuotientGroup.congr_mk]
  congr 1

theorem normal_subgroupOf_of_le_normalizer {W₀ W₁ : Subgroup G} (hW01 : W₀ ≤ W₁)
    (h10 : W₁ ≤ Subgroup.normalizer (W₀ : Set G)) : (W₀.subgroupOf W₁).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer hW01).mpr h10

theorem acts_trivially_of_normal_pGroup {Q Γ W₀ W₁ : Subgroup G} (hQ : IsPGroup 2 Q)
    (hQΓ : Q ≤ Γ) (hΓQ : Γ ≤ Subgroup.normalizer (Q : Set G)) (hW₁ : IsPGroup 2 W₁)
    (hW01 : W₀ ≤ W₁) (hΓ₀ : Γ ≤ Subgroup.normalizer (W₀ : Set G))
    (hΓ₁ : Γ ≤ Subgroup.normalizer (W₁ : Set G)) (h10 : W₁ ≤ Subgroup.normalizer (W₀ : Set G))
    (hirr : ∀ U : Subgroup G, W₀ ≤ U → U ≤ W₁ → Γ ≤ Subgroup.normalizer (U : Set G) →
      U = W₀ ∨ U = W₁) :
    ∀ q ∈ Q, ∀ x ∈ W₁, q * x * q⁻¹ * x⁻¹ ∈ W₀ := by
  haveI : (W₀.subgroupOf W₁).Normal := normal_subgroupOf_of_le_normalizer hW01 h10
  have hconj : ∀ y ∈ W₁, ∀ w ∈ W₀, y * w * y⁻¹ ∈ W₀ := fun y hy w hw =>
    (Subgroup.mem_normalizer_iff.mp (h10 hy) w).mp hw
  have hconjΓ : ∀ γ ∈ Γ, ∀ w ∈ W₀, γ * w * γ⁻¹ ∈ W₀ := fun γ hγ w hw =>
    (Subgroup.mem_normalizer_iff.mp (hΓ₀ hγ) w).mp hw
  have hconjQ : ∀ γ ∈ Γ, ∀ q ∈ Q, γ⁻¹ * q * γ ∈ Q := fun γ hγ q hq =>
    (Subgroup.mem_normalizer_iff.mp (hΓQ hγ) (γ⁻¹ * q * γ)).mpr (by
      rw [show γ * (γ⁻¹ * q * γ) * γ⁻¹ = q by group]
      exact hq)
  obtain ⟨U, hU⟩ : ∃ U : Subgroup G,
      ∀ x, x ∈ U ↔ (x ∈ W₁ ∧ ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ W₀) := by
    refine ⟨{ carrier := {x | x ∈ W₁ ∧ ∀ q ∈ Q, q * x * q⁻¹ * x⁻¹ ∈ W₀}
              mul_mem' := ?_
              one_mem' := ?_
              inv_mem' := ?_ }, fun x => Iff.rfl⟩
    · rintro x y ⟨hx, hxQ⟩ ⟨hy, hyQ⟩
      refine ⟨W₁.mul_mem hx hy, fun q hq => ?_⟩
      have e : q * (x * y) * q⁻¹ * (x * y)⁻¹ =
          (q * x * q⁻¹ * x⁻¹) * (x * (q * y * q⁻¹ * y⁻¹) * x⁻¹) := by group
      rw [e]
      exact W₀.mul_mem (hxQ q hq) (hconj x hx _ (hyQ q hq))
    · exact ⟨W₁.one_mem, fun q _ => by simpa using W₀.one_mem⟩
    · rintro x ⟨hx, hxQ⟩
      refine ⟨W₁.inv_mem hx, fun q hq => ?_⟩
      have e : q * x⁻¹ * q⁻¹ * x⁻¹⁻¹ = x⁻¹ * (q * x * q⁻¹ * x⁻¹)⁻¹ * x⁻¹⁻¹ := by group
      rw [e]
      exact hconj x⁻¹ (W₁.inv_mem hx) _ (W₀.inv_mem (hxQ q hq))
  have hW0U : W₀ ≤ U := fun w hw => (hU w).mpr ⟨hW01 hw, fun q hq =>
    W₀.mul_mem (hconjΓ q (hQΓ hq) w hw) (W₀.inv_mem hw)⟩
  have hUW1 : U ≤ W₁ := fun u hu => ((hU u).mp hu).1
  have hconjU : ∀ γ ∈ Γ, ∀ u ∈ U, γ * u * γ⁻¹ ∈ U := by
    intro γ hγ u hu
    obtain ⟨huW, huQ⟩ := (hU u).mp hu
    refine (hU _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hΓ₁ hγ) u).mp huW, fun q hq => ?_⟩
    have e : γ * ((γ⁻¹ * q * γ) * u * (γ⁻¹ * q * γ)⁻¹ * u⁻¹) * γ⁻¹ =
        q * (γ * u * γ⁻¹) * q⁻¹ * (γ * u * γ⁻¹)⁻¹ := by group
    rw [← e]
    exact hconjΓ γ hγ _ (huQ _ (hconjQ γ hγ q hq))
  have hΓU : Γ ≤ Subgroup.normalizer (U : Set G) := by
    intro γ hγ
    rw [Subgroup.mem_normalizer_iff]
    intro u
    refine ⟨fun hu => hconjU γ hγ u hu, fun hu => ?_⟩
    have h := hconjU γ⁻¹ (Γ.inv_mem hγ) _ hu
    have e : γ⁻¹ * (γ * u * γ⁻¹) * γ⁻¹⁻¹ = u := by group
    rwa [e] at h
  intro q hq x hx
  by_cases hsub : W₁ ≤ W₀
  · exact W₀.mul_mem (hconjΓ q (hQΓ hq) x (hsub hx)) (W₀.inv_mem (hsub hx))
  obtain ⟨x₁, hx₁, hx₁W⟩ := SetLike.not_le_iff_exists.mp hsub
  obtain ⟨xf, hxfW, hxfQ, hxf⟩ : ∃ xf : G, xf ∈ W₁ ∧ (∀ q ∈ Q, q * xf * q⁻¹ * xf⁻¹ ∈ W₀) ∧
      xf ∉ W₀ := by
    letI : MulAction ↥Q (↥W₁ ⧸ W₀.subgroupOf W₁) :=
      MulAction.compHom _ ((secAct hΓ₀ hΓ₁).comp (Subgroup.inclusion hQΓ))
    have hWb2 : IsPGroup 2 (↥W₁ ⧸ W₀.subgroupOf W₁) := hW₁.to_quotient _
    have hWbnt : 1 < Nat.card (↥W₁ ⧸ W₀.subgroupOf W₁) := by
      rw [Finite.one_lt_card_iff_nontrivial]
      refine ⟨⟨QuotientGroup.mk ⟨x₁, hx₁⟩, 1, fun h => hx₁W ?_⟩⟩
      exact Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff _).mp h)
    have hdvd : 2 ∣ Nat.card (↥W₁ ⧸ W₀.subgroupOf W₁) := by
      rcases hWb2.card_eq_or_dvd with h | h
      · omega
      · exact h
    have h1 : (1 : ↥W₁ ⧸ W₀.subgroupOf W₁) ∈
        MulAction.fixedPoints ↥Q (↥W₁ ⧸ W₀.subgroupOf W₁) := by
      rw [MulAction.mem_fixedPoints]
      intro g
      show (secAct hΓ₀ hΓ₁).comp (Subgroup.inclusion hQΓ) g 1 = 1
      exact map_one _
    obtain ⟨b, hbfix, hb1⟩ :=
      IsPGroup.exists_fixed_point_of_prime_dvd_card_of_fixed_point hQ _ hdvd h1
    obtain ⟨xf, rfl⟩ := QuotientGroup.mk_surjective b
    refine ⟨(xf : G), xf.2, fun q hq => ?_, fun h => hb1
      ((QuotientGroup.eq_one_iff xf).mpr (Subgroup.mem_subgroupOf.mpr h)).symm⟩
    have hfix : secAct hΓ₀ hΓ₁ ⟨q, hQΓ hq⟩ (QuotientGroup.mk xf) = QuotientGroup.mk xf :=
      MulAction.mem_fixedPoints.mp hbfix ⟨q, hq⟩
    have hw : q * (xf : G) * q⁻¹ ∈ W₁ :=
      (Subgroup.mem_normalizer_iff.mp (hΓ₁ (hQΓ hq)) xf).mp xf.2
    rw [secAct_mk hΓ₀ hΓ₁ ⟨q, hQΓ hq⟩ xf hw] at hfix
    have hmem : (xf : G)⁻¹ * (q * xf * q⁻¹) ∈ W₀ :=
      Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp hfix.symm)
    have h2 := hconj xf xf.2 _ hmem
    have e : (xf : G) * ((xf : G)⁻¹ * (q * (xf : G) * q⁻¹)) * (xf : G)⁻¹ =
        q * (xf : G) * q⁻¹ * (xf : G)⁻¹ := by group
    rwa [e] at h2
  rcases hirr U hW0U hUW1 hΓU with hUe | hUe
  · exfalso
    have hxU : xf ∈ U := (hU xf).mpr ⟨hxfW, hxfQ⟩
    rw [hUe] at hxU
    exact hxf hxU
  · have hxU : x ∈ U := by
      rw [hUe]
      exact hx
    exact ((hU x).mp hxU).2 q hq

theorem exists_factor_hom {K T W : Type*} [Group K] [Group T] [Group W] (π : K →* T)
    (hπ : Function.Surjective π) (f : K →* MulAut W) (hker : π.ker ≤ f.ker) :
    ∃ ρ : T →* MulAut W, ∀ x : K, ρ (π x) = f x :=
  ⟨π.liftOfRightInverse (Function.surjInv hπ) (Function.rightInverse_surjInv hπ) ⟨f, hker⟩,
    fun x => π.liftOfRightInverse_comp_apply (Function.surjInv hπ)
      (Function.rightInverse_surjInv hπ) ⟨f, hker⟩ x⟩

end Section

end CFSG.RankThree.PartTwo.Sec18.Item187Proof

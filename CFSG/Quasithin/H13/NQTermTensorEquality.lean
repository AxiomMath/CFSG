module

public import CFSG.LocalAnalysis.SteinbergCEIsotypicMultiplicity
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyGL3Normalizer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2
public import CFSG.Quasithin.H13.NQTermTransvectionSaturation

public section

namespace CFSG.Quasithin.H13.NQTerm

open Module CFSG.QuasithinUnique.Setup.Family
open scoped TensorProduct

theorem natCard_GL32 : Nat.card GL32 = 168 := by
  rw [Matrix.card_GL_field]
  simp [Fin.prod_univ_three, ZMod.card]

theorem natCard_gl_of_finrank {U : Type*} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] (hU : finrank (ZMod 2) U = 3) :
    Nat.card (LinearMap.GeneralLinearGroup (ZMod 2) U) = 168 := by
  rw [← natCard_GL32]
  exact Nat.card_congr
    (Units.mapEquiv (LinearMap.toMatrixAlgEquiv (Module.finBasisOfFinrankEq (ZMod 2) U hU)
      ).toMulEquiv).toEquiv

theorem natCard_fixedSub_of_modIso_repV {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    {ρ : GL32 →* (E ≃ₗ[ZMod 2] E)} (h : ModIso repV ρ) (B : Subgroup GL32) :
    Nat.card (fixedSub ρ B) = Nat.card (fixVec3 B) := by
  obtain ⟨e, he⟩ := h
  refine Nat.card_congr
    { toFun := fun x => ⟨e.symm x.1, fun g hg => ?_⟩
      invFun := fun v => ⟨e v.1, mem_fixedSub.mpr fun g hg => ?_⟩
      left_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
      right_inv := fun v => Subtype.ext (e.symm_apply_apply v.1) }
  · apply e.injective
    have h1 : e (repV g (e.symm x.1)) = ρ g (e (e.symm x.1)) := he g _
    rw [e.apply_symm_apply] at h1
    rw [← repV_apply, h1, e.apply_symm_apply]
    exact mem_fixedSub.mp x.2 g hg
  · have h1 : e (repV g v.1) = ρ g (e v.1) := he g _
    rw [← h1, repV_apply, v.2 g hg]

theorem natCard_fixedSub_of_modIso_repDual {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    {ρ : GL32 →* (E ≃ₗ[ZMod 2] E)} (h : ModIso repDual ρ) (B : Subgroup GL32) :
    Nat.card (fixedSub ρ B) = Nat.card (fixDual3 B) := by
  obtain ⟨e, he⟩ := h
  refine Nat.card_congr
    { toFun := fun x => ⟨e.symm x.1, fun g hg => ?_⟩
      invFun := fun v => ⟨e v.1, mem_fixedSub.mpr fun g hg => ?_⟩
      left_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
      right_inv := fun v => Subtype.ext (e.symm_apply_apply v.1) }
  · apply e.injective
    have h1 : e (repDual g (e.symm x.1)) = ρ g (e (e.symm x.1)) := he g _
    rw [e.apply_symm_apply] at h1
    rw [← repDual_apply, h1, e.apply_symm_apply]
    exact mem_fixedSub.mp x.2 g hg
  · have h1 : e (repDual g v.1) = ρ g (e v.1) := he g _
    rw [← h1, repDual_apply, v.2 g hg]

theorem eq_zero_or_id_of_comm_repV {f : (Fin 3 → ZMod 2) →ₗ[ZMod 2] (Fin 3 → ZMod 2)}
    (hf : ∀ (g : GL32) v, f (repV g v) = repV g (f v)) : f = 0 ∨ f = LinearMap.id := by
  have hM : ∀ i j : Fin 3, i ≠ j → LinearMap.toMatrix' f * Matrix.single i j 1 =
      Matrix.single i j 1 * LinearMap.toMatrix' f := by
    intro i j hij
    apply transvec_conj_comm _ i j hij
    exact toMatrix_intertwine f _ _ fun u => hf (transvecGL i j hij) u
  rcases eq_zero_or_one_of_comm _ hM with h0 | h1
  · exact .inl (LinearMap.ext fun u => toMatrix_zero_apply f h0 u)
  · exact .inr (LinearMap.ext fun u => toMatrix_one_apply f h1 u)

theorem eq_zero_or_id_of_modIso {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    {ρ : GL32 →* (E ≃ₗ[ZMod 2] E)} (hρ : ModIso repV ρ ∨ ModIso repDual ρ)
    {φ : E →ₗ[ZMod 2] E} (hφ : ∀ g x, φ (ρ g x) = ρ g (φ x)) : φ = 0 ∨ φ = LinearMap.id := by
  have key : ∀ (e : (Fin 3 → ZMod 2) ≃ₗ[ZMod 2] E),
      (∀ (g : GL32) v, (e.symm.toLinearMap ∘ₗ φ ∘ₗ e.toLinearMap) (repV g v) =
        repV g ((e.symm.toLinearMap ∘ₗ φ ∘ₗ e.toLinearMap) v)) → φ = 0 ∨ φ = LinearMap.id := by
    intro e he
    rcases eq_zero_or_id_of_comm_repV he with h0 | h1
    · left
      apply LinearMap.ext
      intro x
      have h2 := LinearMap.congr_fun h0 (e.symm x)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        LinearMap.zero_apply] at h2
      rw [LinearMap.zero_apply, ← e.symm.map_eq_zero_iff]
      exact h2
    · right
      apply LinearMap.ext
      intro x
      have h2 := LinearMap.congr_fun h1 (e.symm x)
      simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply,
        LinearMap.id_apply] at h2
      rw [LinearMap.id_apply]
      exact e.symm.injective h2
  rcases hρ with ⟨e, he⟩ | ⟨e, he⟩
  · refine key e fun g v => ?_
    have h1 : e (repV g (e.symm (φ (e v)))) = ρ g (e (e.symm (φ (e v)))) := he g _
    have h2 : e (repV g v) = ρ g (e v) := he g v
    rw [LinearEquiv.apply_symm_apply] at h1
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [h2, hφ, ← h1, LinearEquiv.symm_apply_apply]
  · refine key e fun g v => ?_
    have hg : repV g = repDual (tauHom g) := by
      rw [repDual, MonoidHom.comp_apply, tauHom_tauHom]
    have h1 : e (repDual (tauHom g) (e.symm (φ (e v)))) =
        ρ (tauHom g) (e (e.symm (φ (e v)))) := he _ _
    have h2 : e (repDual (tauHom g) v) = ρ (tauHom g) (e v) := he _ v
    rw [LinearEquiv.apply_symm_apply] at h1
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe]
    rw [hg, h2, hφ, ← h1, LinearEquiv.symm_apply_apply]

theorem exists_H32_mulEquiv {G : Type*} [Group G] {Y : Subgroup G} [Y.Normal]
    (eY : Y ≃* GL32) (hCY : ∀ d : G, (∀ y ∈ Y, d * y = y * d) → d = 1) {d₀ : G}
    (hd₀ : d₀ ∉ Y) : ∃ Ψ : H32 ≃* G, ∀ g, Ψ (sIncl g) = (eY.symm g : G) := by
  classical
  let α : G →* MulAut GL32 := (MulAut.congr eY).toMonoidHom.comp MulAut.conjNormal
  have hα : ∀ (d : G) (x : GL32), ((eY.symm (α d x) : Y) : G) = d * (eY.symm x : G) * d⁻¹ := by
    intro d x
    simp [α, MulAut.congr_apply, MulAut.conjNormal_apply]
  have hαinj : ∀ d : G, α d = 1 → d = 1 := by
    intro d hd
    apply hCY d
    intro y hy
    have h1 := hα d (eY ⟨y, hy⟩)
    rw [hd, MulAut.one_apply, MulEquiv.symm_apply_apply] at h1
    calc d * y = d * y * d⁻¹ * d := by group
      _ = y * d := by rw [← h1]
  have hαY : ∀ y : Y, α y = MulAut.conj (eY y) := by
    intro y
    refine MulEquiv.ext fun x => ?_
    apply eY.symm.injective
    apply Subtype.ext
    rw [hα]
    simp [MulAut.conj_apply]
  have hαconj : ∀ (d : G) (s : GL32), α d = MulAut.conj s → d = (eY.symm s : G) := by
    intro d s hds
    have h1 : α (d * ((eY.symm s : Y) : G)⁻¹) = 1 := by
      rw [map_mul, map_inv, hds, hαY, MulEquiv.apply_symm_apply, mul_inv_cancel]
    have h2 := hαinj _ h1
    calc d = d * ((eY.symm s : Y) : G)⁻¹ * (eY.symm s : G) := by group
      _ = _ := by rw [h2, one_mul]
  obtain ⟨s, hs⟩ : ∃ s, α d₀ = MulAut.conj s *
      CFSG.ComponentClassification.CatalogueBGraphForm.glGraphAut 3 (ZMod 2) := by
    rcases aut_GL32_cases (α d₀) with ⟨s, hs⟩ | hs
    · exact absurd (by rw [hαconj d₀ s hs]; exact (eY.symm s).2) hd₀
    · exact hs
  rw [glGraphAut_eq_tauAut] at hs
  set t : G := ((eY.symm s : Y) : G)⁻¹ * d₀ with ht
  have hαt : α t = tauAut := by
    rw [ht, map_mul, map_inv, hαY, MulEquiv.apply_symm_apply, hs, ← mul_assoc, inv_mul_cancel,
      one_mul]
  have htt : t * t = 1 := hαinj _ (by rw [map_mul, hαt, tauAut_mul_self])
  have htY : t ∉ Y := by
    intro htY
    have h1 := hαY ⟨t, htY⟩
    rw [hαt] at h1
    apply glGraphAut_ne_conj (eY ⟨t, htY⟩)
    rw [glGraphAut_eq_tauAut]
    exact h1
  let f₁ : GL32 →* G := Y.subtype.comp eY.symm.toMonoidHom
  let f₂ : Multiplicative (ZMod 2) →* G := invHom t htt
  have hcomp : ∀ g : Multiplicative (ZMod 2),
      f₁.comp (tauAction g).toMonoidHom = (MulAut.conj (f₂ g)).toMonoidHom.comp f₁ := by
    have hc : ∀ x : Multiplicative (ZMod 2), x = 1 ∨ x = Multiplicative.ofAdd 1 := by decide
    intro g
    rcases hc g with rfl | rfl
    · ext x
      simp [f₁, f₂, invHom_one]
    · ext x
      have h1 := hα t x
      rw [hαt, tauAut_apply] at h1
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, f₂, invHom_gen,
        MulAut.conj_apply, tauAction_gen, f₁, Subgroup.coe_subtype]
      exact h1
  let Ψ := SemidirectProduct.lift f₁ f₂ hcomp
  have hΨs : ∀ g, Ψ (sIncl g) = (eY.symm g : G) := fun g => SemidirectProduct.lift_inl _ _ _ g
  have hΨt : Ψ tGen = t := by
    change Ψ (SemidirectProduct.inr (Multiplicative.ofAdd 1)) = t
    rw [SemidirectProduct.lift_inr]
    exact invHom_gen t htt
  have hinj : Function.Injective Ψ := by
    rw [injective_iff_map_eq_one]
    intro h hh
    rcases exists_eq_sIncl_mul h with h1 | h1
    · rw [h1, hΨs] at hh
      have h2 : eY.symm h.left = 1 := Subtype.ext hh
      have h3 : h.left = 1 := by rw [← eY.apply_symm_apply h.left, h2, map_one]
      rw [h1, h3, map_one]
    · exfalso
      rw [h1, map_mul, hΨs, hΨt] at hh
      apply htY
      rw [eq_inv_of_mul_eq_one_right hh]
      exact Y.inv_mem (eY.symm h.left).2
  have hsurj : Function.Surjective Ψ := by
    intro d
    rcases aut_GL32_cases (α d) with ⟨s', hs'⟩ | ⟨s', hs'⟩
    · exact ⟨sIncl s', by rw [hΨs, hαconj d s' hs']⟩
    · rw [glGraphAut_eq_tauAut] at hs'
      refine ⟨sIncl s' * tGen, ?_⟩
      have h1 : α (d * t⁻¹) = MulAut.conj s' := by
        rw [map_mul, map_inv, hαt, hs', mul_inv_cancel_right]
      have h2 := hαconj _ s' h1
      rw [map_mul, hΨs, hΨt, ← h2, inv_mul_cancel_right]
  exact ⟨MulEquiv.ofBijective Ψ ⟨hinj, hsurj⟩, hΨs⟩

section Res

variable {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] {D : Subgroup (Module.End (ZMod 2) S)ˣ}
  {I : Submodule (ZMod 2) S} (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End (ZMod 2) S) v ∈ I)

@[expose] def resHom : D →* Module.End (ZMod 2) I where
  toFun := LocalAnalysis.CommutingFactor.resD hDI
  map_one' := LinearMap.ext fun _ => Subtype.ext rfl
  map_mul' _ _ := LinearMap.ext fun _ => Subtype.ext rfl

@[expose] noncomputable def resEquivHom : D →* (I ≃ₗ[ZMod 2] I) :=
  (LinearMap.GeneralLinearGroup.generalLinearEquiv (ZMod 2) I).toMonoidHom.comp
    (resHom hDI).toHomUnits

end Res

theorem card_eq_two_pow_finrank {M : Type*} [AddCommGroup M] [Module (ZMod 2) M] [Finite M] :
    Nat.card M = 2 ^ finrank (ZMod 2) M :=
  (FiniteField.pow_finrank_eq_natCard 2 M).symm

theorem exists_irreducible_invariant {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    [FiniteDimensional (ZMod 2) S] [Nontrivial S] (D : Subgroup (Module.End (ZMod 2) S)ˣ) :
    ∃ I : Submodule (ZMod 2) S, (∀ d ∈ D, ∀ v ∈ I, (d : Module.End (ZMod 2) S) v ∈ I) ∧
      I ≠ ⊥ ∧ ∀ U ≤ I, (∀ d ∈ D, ∀ v ∈ U, (d : Module.End (ZMod 2) S) v ∈ U) →
        U = ⊥ ∨ U = I := by
  classical
  have hex : ∃ n, ∃ W : Submodule (ZMod 2) S,
      (∀ d ∈ D, ∀ v ∈ W, (d : Module.End (ZMod 2) S) v ∈ W) ∧ W ≠ ⊥ ∧
        finrank (ZMod 2) W = n :=
    ⟨_, ⊤, fun _ _ _ _ => Submodule.mem_top, top_ne_bot, rfl⟩
  obtain ⟨W, hWD, hW0, hWn⟩ := Nat.find_spec hex
  refine ⟨W, hWD, hW0, fun U hUW hUD => ?_⟩
  by_cases hU : U = ⊥
  · exact .inl hU
  · refine .inr (Submodule.eq_of_le_of_finrank_le hUW ?_)
    rw [hWn]
    exact Nat.find_min' hex ⟨U, hUD, hU, rfl⟩

theorem nontrivial_GL32 : Nontrivial GL32 :=
  Finite.one_lt_card_iff_nontrivial.mp (by rw [natCard_GL32]; norm_num)

theorem lt_finrank_of_not_le {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    [FiniteDimensional (ZMod 2) S] {D Y A : Subgroup (Module.End (ZMod 2) S)ˣ}
    {I : Submodule (ZMod 2) S} (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End (ZMod 2) S) v ∈ I)
    (hfaith : ∀ d ∈ D, (∀ v ∈ I, (d : Module.End (ZMod 2) S) v = v) → d = 1)
    (hYD : Y ≤ D) (hYn : ∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) (eY : Y ≃* GL32)
    (hCY : ∀ d ∈ D, (∀ y ∈ Y, d * y = y * d) → d = 1) (hAD : A ≤ D) (hA1 : A ≠ ⊥)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    {d₀ : (Module.End (ZMod 2) S)ˣ} (hd₀ : d₀ ∈ D) (hd₀Y : d₀ ∉ Y) {a : ℕ}
    (ha : Nat.card A = 2 ^ a) :
    a + finrank (ZMod 2) ↥(I ⊓ LocalAnalysis.CommutingFactor.fixedSub A) <
      finrank (ZMod 2) I := by
  set C := LocalAnalysis.CommutingFactor.fixedSub A
  have : Finite I := Module.finite_of_finite (ZMod 2)
  have : Finite ↥(I ⊓ C) := Module.finite_of_finite (ZMod 2)
  have := nontrivial_GL32
  have : (Y.subgroupOf D).Normal :=
    ⟨fun n hn g => Subgroup.mem_subgroupOf.mpr
      (hYn g g.2 n (Subgroup.mem_subgroupOf.mp hn))⟩
  have hCY' : ∀ d : D, (∀ y ∈ Y.subgroupOf D, d * y = y * d) → d = 1 := by
    intro d hd
    refine Subtype.ext (hCY d d.2 fun y hy => ?_)
    exact congrArg Subtype.val (hd ⟨y, hYD hy⟩ (Subgroup.mem_subgroupOf.mpr hy))
  obtain ⟨Ψ, hΨ⟩ := exists_H32_mulEquiv ((Subgroup.subgroupOfEquivOfLe hYD).trans eY) hCY'
    (d₀ := ⟨d₀, hd₀⟩) fun h => hd₀Y (Subgroup.mem_subgroupOf.mp h)
  obtain ⟨ρH, hρH⟩ : ∃ ρH : H32 →* (I ≃ₗ[ZMod 2] I), ∀ (h : H32) (v : I),
      ((ρH h v : I) : S) = ((Ψ h).1 : Module.End (ZMod 2) S) v :=
    ⟨(resEquivHom hDI).comp Ψ.toMonoidHom, fun _ _ => rfl⟩
  obtain ⟨A', hA'mem⟩ : ∃ A' : Subgroup H32, ∀ h, h ∈ A' ↔ (Ψ h).1 ∈ A :=
    ⟨(A.subgroupOf D).comap Ψ.toMonoidHom, fun _ => Iff.rfl⟩
  have hmemA' : ∀ b (hb : b ∈ A), Ψ.symm ⟨b, hAD hb⟩ ∈ A' := by
    intro b hb
    rw [hA'mem, MulEquiv.apply_symm_apply]
    exact hb
  have hA'0 : A' ≠ ⊥ := by
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    intro hbot
    have h1 := hmemA' b hb
    rw [hbot, Subgroup.mem_bot] at h1
    apply hb1
    have h2 : (⟨b, hAD hb⟩ : D) = 1 := by
      rw [← Ψ.apply_symm_apply ⟨b, hAD hb⟩, h1, map_one]
    have h3 : b = 1 := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hcomm' : ∀ x ∈ A', ∀ y ∈ A', x * y = y * x := by
    intro x hx y hy
    apply Ψ.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact hAc _ ((hA'mem x).mp hx) _ ((hA'mem y).mp hy)
  have hsq' : ∀ x ∈ A', x ^ 2 = 1 := by
    intro x hx
    apply Ψ.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2 _ ((hA'mem x).mp hx)
  have hS : ∃ (g : GL32) (x : I), ρH (sIncl g) x ≠ x := by
    by_contra hcon
    push Not at hcon
    obtain ⟨g, hg⟩ := exists_ne (1 : GL32)
    apply hg
    have h1 : (eY.symm g).1 = 1 := by
      refine hfaith _ (hYD (eY.symm g).2) fun v hv => ?_
      have h2 := congrArg Subtype.val (hcon g ⟨v, hv⟩)
      rw [hρH, hΨ] at h2
      exact h2
    have h3 : eY.symm g = 1 := Subtype.ext h1
    rw [← eY.apply_symm_apply g, h3, map_one]
  have hFF := GL3_ext_excludes_FF ρH hS A' hA'0 hcomm' hsq'
  have hcardA' : Nat.card A' = Nat.card A :=
    Nat.card_congr
      { toFun := fun h => ⟨(Ψ h).1, (hA'mem h).mp h.2⟩
        invFun := fun b => ⟨Ψ.symm ⟨b.1, hAD b.2⟩, hmemA' b.1 b.2⟩
        left_inv := fun h => Subtype.ext (Ψ.symm_apply_apply h.1)
        right_inv := fun b => Subtype.ext (by
          change (Ψ (Ψ.symm ⟨b.1, hAD b.2⟩)).1 = b.1
          rw [MulEquiv.apply_symm_apply]) }
  have hfixA' : Nat.card (fixedSub ρH A') = Nat.card ↥(I ⊓ C) :=
    Nat.card_congr
      { toFun := fun y => ⟨(y.1 : S), Submodule.mem_inf.mpr ⟨y.1.2,
          LocalAnalysis.CommutingFactor.mem_fixedSub.mpr fun b hb => by
            have h1 := congrArg Subtype.val (mem_fixedSub.mp y.2 _ (hmemA' b hb))
            rw [hρH, MulEquiv.apply_symm_apply] at h1
            exact h1⟩⟩
        invFun := fun v => ⟨⟨v.1, (Submodule.mem_inf.mp v.2).1⟩, mem_fixedSub.mpr fun h hh =>
          Subtype.ext ((hρH h _).trans (LocalAnalysis.CommutingFactor.mem_fixedSub.mp
            (Submodule.mem_inf.mp v.2).2 _ ((hA'mem h).mp hh)))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  rw [hcardA', hfixA', ha, card_eq_two_pow_finrank (M := I),
    card_eq_two_pow_finrank (M := ↥(I ⊓ C)), ← pow_add,
    Nat.pow_lt_pow_iff_right one_lt_two] at hFF
  exact hFF

theorem natCard_fixedSub_of_modIso_repA {E : Type*} [AddCommGroup E] [Module (ZMod 2) E]
    {ρ : GL32 →* (E ≃ₗ[ZMod 2] E)} (h : ModIso repA ρ) (B : Subgroup GL32) :
    Nat.card (fixedSub ρ B) = Nat.card (fixTrace3 B) := by
  obtain ⟨e, he⟩ := h
  refine Nat.card_congr
    { toFun := fun x => ⟨((e.symm x.1 : ProperTwoGeneratedCore.BinaryThreeSpace.traceZero) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)),
        (e.symm x.1).2, fun g hg => ?_⟩
      invFun := fun X => ⟨e ⟨X.1, X.2.1⟩, mem_fixedSub.mpr fun g hg => ?_⟩
      left_inv := fun x => Subtype.ext (e.apply_symm_apply x.1)
      right_inv := fun X => Subtype.ext (by
        change ((e.symm (e ⟨X.1, X.2.1⟩) : ProperTwoGeneratedCore.BinaryThreeSpace.traceZero) :
          Matrix (Fin 3) (Fin 3) (ZMod 2)) = X.1
        rw [e.symm_apply_apply]) }
  · have h1 : e (repA g (e.symm x.1)) = ρ g (e (e.symm x.1)) := he g _
    rw [e.apply_symm_apply, mem_fixedSub.mp x.2 g hg] at h1
    have h2 : repA g (e.symm x.1) = e.symm x.1 := by
      apply e.injective
      rw [h1, e.apply_symm_apply]
    exact congrArg Subtype.val h2
  · have h1 : e (repA g ⟨X.1, X.2.1⟩) = ρ g (e ⟨X.1, X.2.1⟩) := he g _
    have h2 : repA g ⟨X.1, X.2.1⟩ = ⟨X.1, X.2.1⟩ := Subtype.ext (X.2.2 g hg)
    rw [← h1, h2]

theorem gl3_cases {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    [FiniteDimensional (ZMod 2) S] {D Y A : Subgroup (Module.End (ZMod 2) S)ˣ}
    {I : Submodule (ZMod 2) S} (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End (ZMod 2) S) v ∈ I)
    (hI0 : I ≠ ⊥)
    (hIirr : ∀ U ≤ I, (∀ d ∈ D, ∀ v ∈ U, (d : Module.End (ZMod 2) S) v ∈ U) → U = ⊥ ∨ U = I)
    (hfaith : ∀ d ∈ D, (∀ v ∈ I, (d : Module.End (ZMod 2) S) v = v) → d = 1)
    (hYD : Y ≤ D) (hDY : D ≤ Y) (eY : Y ≃* GL32) (hAY : A ≤ Y) (hA1 : A ≠ ⊥)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hA2 : ∀ a ∈ A, a ^ 2 = 1) {a : ℕ}
    (ha : Nat.card A = 2 ^ a) :
    (finrank (ZMod 2) I = 3 ∧
        (∀ φ ∈ LocalAnalysis.CommutingFactor.commutantD hDI, φ = 0 ∨ φ = LinearMap.id) ∧
        ((a = 1 ∧ finrank (ZMod 2) ↥(I ⊓ LocalAnalysis.CommutingFactor.fixedSub A) = 2) ∨
          (a = 2 ∧ (finrank (ZMod 2) ↥(I ⊓ LocalAnalysis.CommutingFactor.fixedSub A) = 1 ∨
            finrank (ZMod 2) ↥(I ⊓ LocalAnalysis.CommutingFactor.fixedSub A) = 2)))) ∨
      (finrank (ZMod 2) I = 8 ∧
        ((a = 1 ∧ finrank (ZMod 2) ↥(I ⊓ LocalAnalysis.CommutingFactor.fixedSub A) = 4) ∨
          (a = 2 ∧ finrank (ZMod 2) ↥(I ⊓ LocalAnalysis.CommutingFactor.fixedSub A) = 2))) := by
  set C := LocalAnalysis.CommutingFactor.fixedSub A
  have : Finite I := Module.finite_of_finite (ZMod 2)
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hI0
  have : Finite ↥(I ⊓ C) := Module.finite_of_finite (ZMod 2)
  have := nontrivial_GL32
  obtain ⟨ρG, hρG⟩ : ∃ ρG : GL32 →* (I ≃ₗ[ZMod 2] I), ∀ (g : GL32) (v : I),
      ((ρG g v : I) : S) = ((eY.symm g).1 : Module.End (ZMod 2) S) v :=
    ⟨(resEquivHom hDI).comp ((Subgroup.inclusion hYD).comp eY.symm.toMonoidHom),
      fun _ _ => rfl⟩
  have hirrG : IsIrrRep ρG := by
    refine isIrrRep_of inferInstance fun N hN => ?_
    have hNinv : ∀ d ∈ D, ∀ v ∈ N.map I.subtype,
        (d : Module.End (ZMod 2) S) v ∈ N.map I.subtype := by
      rintro d hd _ ⟨w, hw, rfl⟩
      refine Submodule.mem_map.mpr ⟨ρG (eY ⟨d, hDY hd⟩) w, hN _ w hw, ?_⟩
      have h1 := hρG (eY ⟨d, hDY hd⟩) w
      rw [MulEquiv.symm_apply_apply] at h1
      exact h1
    have hinj := Submodule.map_injective_of_injective I.injective_subtype
    rcases hIirr _ (Submodule.map_subtype_le I N) hNinv with h | h
    · exact .inl (hinj (by rw [h, Submodule.map_bot]))
    · exact .inr (hinj (by rw [h, Submodule.map_subtype_top]))
  obtain ⟨B, hBmem⟩ : ∃ B : Subgroup GL32, ∀ g, g ∈ B ↔ (eY.symm g).1 ∈ A :=
    ⟨(A.subgroupOf Y).map eY.toMonoidHom, fun g => ⟨fun hg => by
      obtain ⟨y, hy, hyg⟩ := Subgroup.mem_map.mp hg
      rw [← hyg]
      change (eY.symm (eY y)).1 ∈ A
      rw [MulEquiv.symm_apply_apply]
      exact Subgroup.mem_subgroupOf.mp hy,
      fun h => Subgroup.mem_map.mpr ⟨eY.symm g, Subgroup.mem_subgroupOf.mpr h,
        eY.apply_symm_apply g⟩⟩⟩
  have hB0 : B ≠ ⊥ := by
    obtain ⟨⟨b, hb⟩, hb1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hA1
    intro hbot
    have h1 : eY ⟨b, hAY hb⟩ ∈ B := by
      rw [hBmem, MulEquiv.symm_apply_apply]
      exact hb
    rw [hbot, Subgroup.mem_bot] at h1
    apply hb1
    have h2 : (⟨b, hAY hb⟩ : Y) = 1 := by
      rw [← eY.symm_apply_apply ⟨b, hAY hb⟩, h1, map_one]
    have h3 : b = 1 := congrArg Subtype.val h2
    exact Subtype.ext h3
  have hBc : ∀ g ∈ B, ∀ h ∈ B, g * h = h * g := by
    intro g hg h hh
    apply eY.symm.injective
    apply Subtype.ext
    rw [map_mul, map_mul, Subgroup.coe_mul, Subgroup.coe_mul]
    exact hAc _ ((hBmem g).mp hg) _ ((hBmem h).mp hh)
  have hBsq : ∀ g ∈ B, g ^ 2 = 1 := by
    intro g hg
    apply eY.symm.injective
    apply Subtype.ext
    rw [map_pow, map_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hA2 _ ((hBmem g).mp hg)
  have hfix := GL3_elementary_abelian_fixed_codimensions hB0 hBc hBsq
  have hcardB : Nat.card B = 2 ^ a := by
    rw [← ha]
    exact Nat.card_congr
      { toFun := fun g => ⟨(eY.symm g).1, (hBmem g).mp g.2⟩
        invFun := fun b => ⟨eY ⟨b.1, hAY b.2⟩, (hBmem _).mpr (by
          rw [MulEquiv.symm_apply_apply]
          exact b.2)⟩
        left_inv := fun g => Subtype.ext (eY.apply_symm_apply g.1)
        right_inv := fun b => Subtype.ext (by
          change (eY.symm (eY ⟨b.1, hAY b.2⟩)).1 = b.1
          rw [MulEquiv.symm_apply_apply]) }
  have hfixB : Nat.card (fixedSub ρG B) = Nat.card ↥(I ⊓ C) :=
    Nat.card_congr
      { toFun := fun y => ⟨(y.1 : S), Submodule.mem_inf.mpr ⟨y.1.2,
          LocalAnalysis.CommutingFactor.mem_fixedSub.mpr fun b hb => by
            have h1 := congrArg Subtype.val (mem_fixedSub.mp y.2 (eY ⟨b, hAY hb⟩)
              ((hBmem _).mpr (by rw [MulEquiv.symm_apply_apply]; exact hb)))
            rw [hρG, MulEquiv.symm_apply_apply] at h1
            exact h1⟩⟩
        invFun := fun v => ⟨⟨v.1, (Submodule.mem_inf.mp v.2).1⟩, mem_fixedSub.mpr fun g hg =>
          Subtype.ext ((hρG g _).trans (LocalAnalysis.CommutingFactor.mem_fixedSub.mp
            (Submodule.mem_inf.mp v.2).2 _ ((hBmem g).mp hg)))⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
  have hab : (Nat.card B = 2 → a = 1) ∧ (Nat.card B = 4 → a = 2) :=
    ⟨fun h => Nat.pow_right_injective le_rfl ((hcardB.symm.trans h).trans (pow_one 2).symm),
      fun h => Nat.pow_right_injective le_rfl ((hcardB.symm.trans h).trans (by norm_num))⟩
  unfold FixedCodimData at hfix
  have hcase : (ModIso repV ρG ∨ ModIso repDual ρG) ∨ ModIso repA ρG := by
    rcases irreducible_binary_GL3_classification ρG hirrG with h | h | h | h
    · exfalso
      obtain ⟨e, he⟩ := h
      obtain ⟨g, hg⟩ := exists_ne (1 : GL32)
      apply hg
      have h1 : (eY.symm g).1 = 1 := by
        refine hfaith _ (hYD (eY.symm g).2) fun v hv => ?_
        have h2 : e (e.symm ⟨v, hv⟩) = ρG g (e (e.symm ⟨v, hv⟩)) := he g _
        rw [LinearEquiv.apply_symm_apply] at h2
        have h3 := congrArg Subtype.val h2.symm
        rw [hρG] at h3
        exact h3
      have h3 : eY.symm g = 1 := Subtype.ext h1
      rw [← eY.apply_symm_apply g, h3, map_one]
    · exact .inl (.inl h)
    · exact .inl (.inr h)
    · exact .inr h
  rcases hcase with hV | hA
  · left
    have h1 : Nat.card Vec3 = Nat.card I := by
      rcases hV with h | h
      · exact card_eq_of_modIso h
      · exact card_eq_of_modIso h
    have hfixV : Nat.card ↥(I ⊓ C) = Nat.card (fixVec3 B) ∨
        Nat.card ↥(I ⊓ C) = Nat.card (fixDual3 B) := by
      rcases hV with h | h
      · exact .inl (hfixB.symm.trans (natCard_fixedSub_of_modIso_repV h B))
      · exact .inr (hfixB.symm.trans (natCard_fixedSub_of_modIso_repDual h B))
    refine ⟨finrank_eq_of_natCard_eq (h1.symm.trans (natCard_Vec3.trans (by norm_num))),
      fun φ hφ => ?_, ?_⟩
    · refine eq_zero_or_id_of_modIso hV fun g x => ?_
      have hd : ∀ w : I, ρG g w =
          LocalAnalysis.CommutingFactor.resD hDI ⟨(eY.symm g).1, hYD (eY.symm g).2⟩ w :=
        fun w => Subtype.ext (hρG g w)
      rw [hd, hd]
      exact (LinearMap.congr_fun ((LocalAnalysis.CommutingFactor.mem_commutantD hDI).mp hφ
        ⟨(eY.symm g).1, hYD (eY.symm g).2⟩) x).symm
    · rcases hfix with ⟨hB2, hV4, hD4, -⟩ | ⟨hB4, hVD, -⟩
      · refine .inl ⟨hab.1 hB2, finrank_eq_of_natCard_eq ?_⟩
        rcases hfixV with h | h
        · exact (h.trans hV4).trans (by norm_num)
        · exact (h.trans hD4).trans (by norm_num)
      · refine .inr ⟨hab.2 hB4, ?_⟩
        rcases hVD with ⟨hV', hD'⟩ | ⟨hV', hD'⟩ <;> rcases hfixV with h | h
        · exact .inl (finrank_eq_of_natCard_eq ((h.trans hV').trans (by norm_num)))
        · exact .inr (finrank_eq_of_natCard_eq ((h.trans hD').trans (by norm_num)))
        · exact .inr (finrank_eq_of_natCard_eq ((h.trans hV').trans (by norm_num)))
        · exact .inl (finrank_eq_of_natCard_eq ((h.trans hD').trans (by norm_num)))
  · right
    have hfA : Nat.card ↥(I ⊓ C) = Nat.card (fixTrace3 B) :=
      hfixB.symm.trans (natCard_fixedSub_of_modIso_repA hA B)
    refine ⟨finrank_eq_of_natCard_eq ((card_eq_of_modIso hA).symm.trans
      (natCard_traceZero.trans (by norm_num))), ?_⟩
    rcases hfix with ⟨hB2, -, -, hT⟩ | ⟨hB4, -, hT⟩
    · exact .inl ⟨hab.1 hB2, finrank_eq_of_natCard_eq ((hfA.trans hT).trans (by norm_num))⟩
    · exact .inr ⟨hab.2 hB4, finrank_eq_of_natCard_eq ((hfA.trans hT).trans (by norm_num))⟩

theorem eq_seven_of_dvd {s : ℕ} (hs : s.Prime) (hs5 : 5 ≤ s) (h : s * (s ^ 2 - 1) / 2 ∣ 168) :
    s = 7 := by
  have h2 : 2 ∣ s ^ 2 - 1 := two_dvd_sq_sub_one_of_odd (hs.odd_of_ne_two (by omega))
  have h3 : s ∣ 168 := by
    refine Dvd.dvd.trans ?_ h
    rw [Nat.mul_div_assoc _ h2]
    exact Dvd.intro _ rfl
  have h4 : s ∣ 2 ^ 3 * 3 * 7 := h3
  rcases (Nat.Prime.dvd_mul hs).mp h4 with h5 | h5
  · rcases (Nat.Prime.dvd_mul hs).mp h5 with h6 | h6
    · have := Nat.le_of_dvd (by norm_num) (hs.dvd_of_dvd_pow h6)
      omega
    · have := Nat.le_of_dvd (by norm_num) h6
      omega
  · rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp h5 with h6 | h6
    · omega
    · exact h6

open CFSG.LocalAnalysis.CommutingFactor (resD homD evalHom homAct) in
theorem exists_tensor_package {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    {X D Y : Subgroup (Module.End (ZMod 2) S)ˣ} (hXD : ∀ x ∈ X, ∀ d ∈ D, x * d = d * x)
    {I : Submodule (ZMod 2) S} (hDI : ∀ d ∈ D, ∀ v ∈ I, (d : Module.End (ZMod 2) S) v ∈ I)
    (hfaith : ∀ d ∈ D, (∀ v ∈ I, (d : Module.End (ZMod 2) S) v = v) → d = 1)
    (hYD : Y ≤ D) (hbij : Function.Bijective (evalHom hDI))
    (hhinj : Function.Injective (homAct hXD hDI)) :
    ∃ (ρX : X →* LinearMap.GeneralLinearGroup (ZMod 2) (homD hDI))
      (ρY : Y →* LinearMap.GeneralLinearGroup (ZMod 2) I)
      (Φ : homD hDI ⊗[ZMod 2] I ≃ₗ[ZMod 2] S),
      Function.Injective ρX ∧ Function.Injective ρY ∧
      (∀ (x : X) (u : homD hDI) (v : I),
        (((ρX x : homD hDI →ₗ[ZMod 2] homD hDI) u : homD hDI) : I →ₗ[ZMod 2] S) v =
          (x.1 : Module.End (ZMod 2) S) ((u : I →ₗ[ZMod 2] S) v)) ∧
      (∀ (y : Y) (v : I),
        (((ρY y : I →ₗ[ZMod 2] I) v : I) : S) = (y.1 : Module.End (ZMod 2) S) v) ∧
      (∀ (y : Y) (w : I), (ρY y : I →ₗ[ZMod 2] I) w = resD hDI (Subgroup.inclusion hYD y) w) ∧
      (∀ (u : homD hDI) (v : I), Φ (u ⊗ₜ v) = (u : I →ₗ[ZMod 2] S) v) ∧
      (∀ (x : X) (u : homD hDI) (v : I),
        Φ ((ρX x : homD hDI →ₗ[ZMod 2] homD hDI) u ⊗ₜ v) =
          (x.1 : Module.End (ZMod 2) S) (Φ (u ⊗ₜ v))) ∧
      (∀ (y : Y) (u : homD hDI) (v : I), Φ (u ⊗ₜ (ρY y : I →ₗ[ZMod 2] I) v) =
          (y.1 : Module.End (ZMod 2) S) (Φ (u ⊗ₜ v))) := by
  have hΦ : ∀ (u : homD hDI) (v : I),
      ((TensorProduct.comm (ZMod 2) (homD hDI) I).trans
        (LinearEquiv.ofBijective _ hbij)) (u ⊗ₜ v) = (u : I →ₗ[ZMod 2] S) v := by
    intro u v
    rw [LinearEquiv.trans_apply, TensorProduct.comm_tmul, LinearEquiv.ofBijective_apply,
      LocalAnalysis.CommutingFactor.evalHom_tmul]
  refine ⟨(homAct hXD hDI).toHomUnits, (resHom hDI).toHomUnits.comp (Subgroup.inclusion hYD),
    (TensorProduct.comm (ZMod 2) (homD hDI) I).trans (LinearEquiv.ofBijective _ hbij),
    fun x y h => hhinj (congrArg Units.val h), ?_, fun _ _ _ => rfl, fun _ _ => rfl,
    fun _ _ => rfl, hΦ, fun x u v => ?_, fun y u v => ?_⟩
  · rw [injective_iff_map_eq_one]
    intro y hy
    refine Subtype.ext (hfaith _ (hYD y.2) fun v hv => ?_)
    have h1 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) I =>
      (((g : I →ₗ[ZMod 2] I) ⟨v, hv⟩ : I) : S)) hy
    exact h1
  · rw [hΦ, hΦ]
    exact LocalAnalysis.CommutingFactor.homAct_apply hXD hDI x u v
  · rw [hΦ, hΦ]
    exact (LocalAnalysis.CommutingFactor.mem_homD hDI).mp u.2 (Subgroup.inclusion hYD y) v

theorem eq_axisGroup_of_card_four {I : Type*} [AddCommGroup I] [Module (ZMod 2) I]
    [FiniteDimensional (ZMod 2) I] (hI : finrank (ZMod 2) I = 3)
    {A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) I)} (hA2 : ∀ a ∈ A, a ^ 2 = 1)
    (hcard : Nat.card A = 4) {H : Submodule (ZMod 2) I}
    (hH : ∀ v, v ∈ H ↔ ∀ a ∈ A, (a : I →ₗ[ZMod 2] I) v = v) (hH2 : finrank (ZMod 2) H = 2) :
    ∃ f : Module.Dual (ZMod 2) I, f ≠ 0 ∧ LinearMap.ker f = H ∧
      (∀ f' : Module.Dual (ZMod 2) I, f' ≠ 0 → LinearMap.ker f' = H → f' = f) ∧
      A = axisGroup f := by
  have : Finite I := Module.finite_of_finite (ZMod 2)
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) I) :=
    LocalAnalysis.CommutingFactor.finite_endUnits
  have hHtop : H < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro h
    rw [h, finrank_top, hI] at hH2
    omega
  obtain ⟨f, hf0, hfH⟩ := Submodule.exists_dual_map_eq_bot_of_lt_top hHtop inferInstance
  have hHker : LinearMap.ker f = H := by
    have hle : H ≤ LinearMap.ker f := fun v hv => by
      rw [LinearMap.mem_ker]
      have h1 : f v ∈ H.map f := Submodule.mem_map_of_mem hv
      rw [hfH, Submodule.mem_bot] at h1
      exact h1
    refine (Submodule.eq_of_le_of_finrank_le hle ?_).symm
    have h1 := finrank_ker_add_one hf0
    omega
  have hfuniq : ∀ f' : Module.Dual (ZMod 2) I, f' ≠ 0 → LinearMap.ker f' = H → f' = f := by
    intro f' _ hf'
    apply LinearMap.ext
    intro v
    have hiff : f' v = 0 ↔ f v = 0 := by
      rw [← LinearMap.mem_ker, ← LinearMap.mem_ker, hf', hHker]
    rcases zmod_two_cases (f' v) with h1 | h1 <;> rcases zmod_two_cases (f v) with h2 | h2
    · rw [h1, h2]
    · exact absurd (hiff.mp h1) (by rw [h2]; decide)
    · exact absurd (hiff.mpr h2) (by rw [h1]; decide)
    · rw [h1, h2]
  obtain ⟨x₀, hx₀⟩ := exists_eq_one_of_ne_zero hf0
  have hmem : A ≤ axisGroup f := by
    intro L hL
    obtain ⟨u, hu⟩ : ∃ u : I, u = (L : I →ₗ[ZMod 2] I) x₀ - x₀ := ⟨_, rfl⟩
    have hfix : ∀ w ∈ LinearMap.ker f, (L : I →ₗ[ZMod 2] I) w = w := by
      intro w hw
      rw [hHker] at hw
      exact (hH w).mp hw L hL
    have hL1 : ∀ w, (L : I →ₗ[ZMod 2] I) w = w + f w • u := by
      intro w
      have hk : w - f w • x₀ ∈ LinearMap.ker f := by
        rw [LinearMap.mem_ker, map_sub, map_smul, hx₀, smul_eq_mul, mul_one]
        exact sub_self _
      have h1 := hfix _ hk
      rw [map_sub, map_smul] at h1
      rw [hu, smul_sub]
      calc (L : I →ₗ[ZMod 2] I) w
          = ((L : I →ₗ[ZMod 2] I) w - f w • (L : I →ₗ[ZMod 2] I) x₀) +
              f w • (L : I →ₗ[ZMod 2] I) x₀ := by abel
        _ = (w - f w • x₀) + f w • (L : I →ₗ[ZMod 2] I) x₀ := by rw [h1]
        _ = w + (f w • (L : I →ₗ[ZMod 2] I) x₀ - f w • x₀) := by abel
    have hfu : f u = 0 := by
      have hLL : (L : I →ₗ[ZMod 2] I) ((L : I →ₗ[ZMod 2] I) x₀) = x₀ := by
        have h2 : L * L = 1 := by
          rw [← pow_two]
          exact hA2 L hL
        have h3 := congrArg (fun g : LinearMap.GeneralLinearGroup (ZMod 2) I =>
          (g : I →ₗ[ZMod 2] I) x₀) h2
        exact h3
      have h4 := hL1 ((L : I →ₗ[ZMod 2] I) x₀)
      rw [hLL] at h4
      have h5 : (L : I →ₗ[ZMod 2] I) x₀ = x₀ + u := by
        rw [hu]
        abel
      rw [h5, map_add, hx₀, add_smul, one_smul] at h4
      have h6 : f u • u = 0 := by
        have h7 := add_self_eq_zero_of_zmod_two u
        calc f u • u = x₀ + u + (u + f u • u) - x₀ - (u + u) := by abel
          _ = 0 := by
            rw [← h4, h7]
            abel
      rcases smul_eq_zero.mp h6 with h7 | h7
      · exact h7
      · rw [h7, map_zero]
    show ∃ (u : I) (hu : f u = 0), L = tvGL u f hu
    exact ⟨u, hfu, Units.ext (LinearMap.ext fun w => (hL1 w).trans (tvGL_apply hfu w).symm)⟩
  have hcardAx : Nat.card (axisGroup f) = Nat.card (LinearMap.ker f) := by
    refine (Nat.card_eq_of_bijective (fun u : LinearMap.ker f =>
      (⟨tvGL u.1 f (LinearMap.mem_ker.mp u.2), tvGL_mem_axisGroup _⟩ : axisGroup f))
        ⟨fun u w huw => ?_, ?_⟩).symm
    · have h1 := congrArg (fun g : axisGroup f =>
        ((g : LinearMap.GeneralLinearGroup (ZMod 2) I) : I →ₗ[ZMod 2] I) x₀) huw
      simp only [tvGL_apply, hx₀, one_smul] at h1
      exact Subtype.ext (add_left_cancel h1)
    · rintro ⟨g, u, hu, rfl⟩
      exact ⟨⟨u, LinearMap.mem_ker.mpr hu⟩, rfl⟩
  have hcardker : Nat.card (LinearMap.ker f) = 2 ^ 2 := by
    rw [card_eq_two_pow_finrank, hHker, hH2]
  refine ⟨f, hf0, hHker, hfuniq, Subgroup.eq_of_le_of_card_ge hmem ?_⟩
  exact ((hcardAx.trans hcardker).trans ((by norm_num : (2 : ℕ) ^ 2 = 4).trans hcard.symm)).le

theorem exists_axis_of_image {S : Type*} [AddCommGroup S] [Module (ZMod 2) S]
    [FiniteDimensional (ZMod 2) S] {Y A : Subgroup (Module.End (ZMod 2) S)ˣ}
    {I : Submodule (ZMod 2) S} (hI3 : finrank (ZMod 2) I = 3) (hAY : A ≤ Y)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) (hcard : Nat.card A = 4)
    (ρY : Y →* LinearMap.GeneralLinearGroup (ZMod 2) I) (hρYinj : Function.Injective ρY)
    (hρY : ∀ (y : Y) (v : I),
      (((ρY y : I →ₗ[ZMod 2] I) v : I) : S) = (y.1 : Module.End (ZMod 2) S) v)
    (hm2 : finrank (ZMod 2) ↥(I ⊓ LocalAnalysis.CommutingFactor.fixedSub A) = 2) :
    ∃ (H : Submodule (ZMod 2) I) (f : Module.Dual (ZMod 2) I),
      finrank (ZMod 2) H = 2 ∧ f ≠ 0 ∧ LinearMap.ker f = H ∧
      (∀ f' : Module.Dual (ZMod 2) I, f' ≠ 0 → LinearMap.ker f' = H → f' = f) ∧
      (A.subgroupOf Y).map ρY = axisGroup f := by
  set C := LocalAnalysis.CommutingFactor.fixedSub A
  have hA'2 : ∀ g ∈ (A.subgroupOf Y).map ρY, g ^ 2 = 1 := by
    rintro _ ⟨y, hy, rfl⟩
    have hy2 : y ^ 2 = 1 := Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hA2 _ (Subgroup.mem_subgroupOf.mp hy))
    rw [← map_pow, hy2, map_one]
  have hA'card : Nat.card ((A.subgroupOf Y).map ρY) = 4 := by
    rw [Subgroup.card_map_of_injective hρYinj,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAY).toEquiv, hcard]
  obtain ⟨H, hHmem, hH2⟩ : ∃ H : Submodule (ZMod 2) I,
      (∀ v : I, v ∈ H ↔ ∀ g ∈ (A.subgroupOf Y).map ρY, (g : I →ₗ[ZMod 2] I) v = v) ∧
        finrank (ZMod 2) H = 2 := by
    refine ⟨(I ⊓ C).comap I.subtype, fun v => ⟨fun hv => ?_, fun hv => ?_⟩, by
      rw [(Submodule.comapSubtypeEquivOfLe (inf_le_left : I ⊓ C ≤ I)).finrank_eq, hm2]⟩
    · rintro _ ⟨y, hy, rfl⟩
      apply Subtype.ext
      rw [hρY]
      exact LocalAnalysis.CommutingFactor.mem_fixedSub.mp
        (Submodule.mem_inf.mp (Submodule.mem_comap.mp hv)).2 _ (Subgroup.mem_subgroupOf.mp hy)
    · refine Submodule.mem_comap.mpr (Submodule.mem_inf.mpr ⟨v.2,
        LocalAnalysis.CommutingFactor.mem_fixedSub.mpr fun b hb => ?_⟩)
      have h1 := congrArg Subtype.val (hv (ρY ⟨b, hAY hb⟩)
        (Subgroup.mem_map.mpr ⟨⟨b, hAY hb⟩, Subgroup.mem_subgroupOf.mpr hb, rfl⟩))
      rw [hρY] at h1
      exact h1
  obtain ⟨f, hf0, hker, huniq, heq⟩ := eq_axisGroup_of_card_four hI3 hA'2 hA'card hHmem hH2
  exact ⟨H, f, hH2, hf0, hker, huniq, heq⟩

open CFSG.LocalAnalysis.CommutingFactor (homD evalHom homAct commutantD) in
theorem near_maximal_mixed_GL3_action_forces_the_nine_dimensional_tensor_equality
    {s : ℕ} [Fact s.Prime] (hs5 : 5 ≤ s)
    {S : Type*} [AddCommGroup S] [Module (ZMod 2) S] [FiniteDimensional (ZMod 2) S]
    [Nontrivial S] {X D Y A : Subgroup (Module.End (ZMod 2) S)ˣ}
    (hXD : ∀ x ∈ X, ∀ d ∈ D, x * d = d * x)
    (hirr : ∀ W : Submodule (ZMod 2) S,
      (∀ g ∈ X ⊔ D, ∀ v ∈ W, (g : Module.End (ZMod 2) S) v ∈ W) → W = ⊥ ∨ W = ⊤)
    (hX1 : X ≠ ⊥) (hXp : Group.IsPerfect X)
    (eX : X ≃* LocalAnalysis.ComponentInitial.LinearFlag.projectiveSL 2 (ZMod s))
    (hYn : ∀ d ∈ D, ∀ y ∈ Y, d * y * d⁻¹ ∈ Y) (eY : Y ≃* GL (Fin 3) (ZMod 2))
    (hCY : ∀ d ∈ D, (∀ y ∈ Y, d * y = y * d) → d = 1)
    (hDYA : D = Y ⊔ A) (hA1 : A ≠ ⊥) (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a)
    (hA2 : ∀ a ∈ A, a ^ 2 = 1) {j : ℕ} (hj : j ≤ 1)
    (hc : finrank (ZMod 2) S - finrank (ZMod 2) (LocalAnalysis.CommutingFactor.fixedSub A) ≤
      j + Nat.log 2 (Nat.card A)) :
    s = 7 ∧ D = Y ∧ j = 1 ∧ Nat.card A = 4 ∧
      finrank (ZMod 2) S - finrank (ZMod 2) (LocalAnalysis.CommutingFactor.fixedSub A) = 3 ∧
      ∃ (I : Submodule (ZMod 2) S) (U : Submodule (ZMod 2) (I →ₗ[ZMod 2] S))
        (ρX : X →* LinearMap.GeneralLinearGroup (ZMod 2) U)
        (ρY : Y →* LinearMap.GeneralLinearGroup (ZMod 2) I)
        (Φ : U ⊗[ZMod 2] I ≃ₗ[ZMod 2] S),
        finrank (ZMod 2) U = 3 ∧ finrank (ZMod 2) I = 3 ∧ finrank (ZMod 2) S = 9 ∧
        Function.Bijective ρX ∧ Function.Bijective ρY ∧
        (∀ (x : X) (u : U) (v : I), (((ρX x : U →ₗ[ZMod 2] U) u : U) : I →ₗ[ZMod 2] S) v =
          (x.1 : Module.End (ZMod 2) S) ((u : I →ₗ[ZMod 2] S) v)) ∧
        (∀ (y : Y) (v : I), (((ρY y : I →ₗ[ZMod 2] I) v : I) : S) =
          (y.1 : Module.End (ZMod 2) S) v) ∧
        (∀ (u : U) (v : I), Φ (u ⊗ₜ v) = (u : I →ₗ[ZMod 2] S) v) ∧
        (∀ (x : X) (u : U) (v : I), Φ ((ρX x : U →ₗ[ZMod 2] U) u ⊗ₜ v) =
          (x.1 : Module.End (ZMod 2) S) (Φ (u ⊗ₜ v))) ∧
        (∀ (y : Y) (u : U) (v : I), Φ (u ⊗ₜ (ρY y : I →ₗ[ZMod 2] I) v) =
          (y.1 : Module.End (ZMod 2) S) (Φ (u ⊗ₜ v))) ∧
        (∃ Ψ : (Fin 3 → I) ≃ₗ[ZMod 2] S, ∀ (y : Y) (v : Fin 3 → I),
          Ψ (fun i => (ρY y : I →ₗ[ZMod 2] I) (v i)) = (y.1 : Module.End (ZMod 2) S) (Ψ v)) ∧
        ∃ (H : Submodule (ZMod 2) I) (f : Module.Dual (ZMod 2) I),
          finrank (ZMod 2) H = 2 ∧ f ≠ 0 ∧ LinearMap.ker f = H ∧
          (∀ f' : Module.Dual (ZMod 2) I, f' ≠ 0 → LinearMap.ker f' = H → f' = f) ∧
          (A.subgroupOf Y).map ρY = axisGroup f := by
  classical
  have hs : s.Prime := Fact.out
  have hYD : Y ≤ D := by rw [hDYA]; exact le_sup_left
  have hAD : A ≤ D := by rw [hDYA]; exact le_sup_right
  obtain ⟨I, hDI, hI0, hIirr⟩ := exists_irreducible_invariant D
  obtain ⟨r, Φ₀, -, hΦ₀, hfaith, -, -, -, -, hcod, hr2, hr3, htens⟩ :=
    LocalAnalysis.CommutingFactor.commuting_factor_irreducible_modules_have_isotypic_multiplicity
      hXD hirr hDI hI0 hIirr
  have hr2' : 2 ≤ r := hr2 hX1 hXp
  have : Nontrivial I := Submodule.nontrivial_iff_ne_bot.mpr hI0
  have : Finite (Module.End (ZMod 2) S)ˣ := LocalAnalysis.CommutingFactor.finite_endUnits
  have hcodA := hcod A hAD
  set C := LocalAnalysis.CommutingFactor.fixedSub A
  have hcI : 1 ≤ finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C) := by
    by_contra h0
    have heq : I ⊓ C = I := Submodule.eq_of_le_of_finrank_le inf_le_left (by omega)
    apply hA1
    rw [eq_bot_iff]
    intro b hb
    rw [Subgroup.mem_bot]
    refine hfaith b (hAD hb) fun v hv => ?_
    have hv' : v ∈ I ⊓ C := by rw [heq]; exact hv
    exact LocalAnalysis.CommutingFactor.mem_fixedSub.mp (Submodule.mem_inf.mp hv').2 b hb
  obtain ⟨a, ha⟩ : ∃ a, Nat.card A = 2 ^ a := by
    refine IsPGroup.exists_card_eq (p := 2) fun g => ⟨1, Subtype.ext ?_⟩
    simpa using hA2 g g.2
  rw [ha, Nat.log_pow one_lt_two] at hc
  have key : r * (finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C)) ≤ j + a := by
    rw [← hcodA]
    exact hc
  have h2c : 2 * (finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C)) ≤
      r * (finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C)) := Nat.mul_le_mul hr2' le_rfl
  have hDY : D ≤ Y := by
    intro d₀ hd₀
    by_contra hd₀Y
    have : a + finrank (ZMod 2) ↥(I ⊓ C) < finrank (ZMod 2) I :=
      lt_finrank_of_not_le hDI hfaith hYD hYn eY hCY hAD hA1 hAc hA2 hd₀ hd₀Y ha
    omega
  have hAY : A ≤ Y := hAD.trans hDY
  obtain ⟨hI3, hmem01, hcases⟩ : finrank (ZMod 2) I = 3 ∧
      (∀ φ ∈ commutantD hDI, φ = 0 ∨ φ = LinearMap.id) ∧
      ((a = 1 ∧ finrank (ZMod 2) ↥(I ⊓ C) = 2) ∨
        (a = 2 ∧ (finrank (ZMod 2) ↥(I ⊓ C) = 1 ∨ finrank (ZMod 2) ↥(I ⊓ C) = 2))) :=
    (gl3_cases hDI hI0 hIirr hfaith hYD hDY eY hAY hA1 hAc hA2 ha).resolve_right fun h => by
      obtain ⟨hI8, hcases⟩ : finrank (ZMod 2) I = 8 ∧ ((a = 1 ∧ finrank (ZMod 2) ↥(I ⊓ C) = 4) ∨
          (a = 2 ∧ finrank (ZMod 2) ↥(I ⊓ C) = 2)) := h
      rcases hcases with ⟨ha1, hm⟩ | ⟨ha2, hm⟩ <;> omega
  have hcomm2 : Nat.card (commutantD hDI) = 2 := by
    rw [Nat.card_eq_two_iff]
    refine ⟨0, 1, fun h => zero_ne_one (α := Module.End (ZMod 2) I) (congrArg Subtype.val h),
      Set.eq_univ_of_forall fun φ => ?_⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff]
    rcases hmem01 φ.1 φ.2 with h | h
    · exact .inl (Subtype.ext h)
    · exact .inr (Subtype.ext (h.trans Module.End.one_eq_id.symm))
  have hr3' : 3 ≤ r := hr3 (Nat.card_zmod 2) hcomm2 hX1 hXp
  obtain ⟨hr, hj1, ha2, hm2⟩ : r = 3 ∧ j = 1 ∧ a = 2 ∧ finrank (ZMod 2) ↥(I ⊓ C) = 2 := by
    rcases hcases with ⟨ha1, hm⟩ | ⟨ha2, hm | hm⟩
    · exfalso
      have hc1 : finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C) = 1 := by omega
      rw [hc1] at key
      omega
    · exfalso
      have hc2 : finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C) = 2 := by omega
      rw [hc2] at key
      omega
    · have hc1 : finrank (ZMod 2) I - finrank (ZMod 2) ↥(I ⊓ C) = 1 := by omega
      rw [hc1] at key
      exact ⟨by omega, by omega, ha2, hm⟩
  subst hr
  have hbot : commutantD hDI = ⊥ := by
    rw [eq_bot_iff]
    intro φ hφ
    rcases hmem01 φ hφ with h | h
    · rw [h]
      exact Subalgebra.zero_mem _
    · rw [h, ← Module.End.one_eq_id]
      exact Subalgebra.one_mem _
  obtain ⟨hbij, -, -, hhinj, -, -⟩ := htens hbot
  have hS9 : finrank (ZMod 2) S = 9 := by
    have h1 := Φ₀.finrank_eq
    rw [LocalAnalysis.CommutingFactor.finrank_fin_fun_eq, hI3] at h1
    omega
  have hU3 : finrank (ZMod 2) (homD hDI) = 3 := by
    have h1 := (LinearEquiv.ofBijective (evalHom hDI) hbij).finrank_eq
    rw [Module.finrank_tensorProduct, hI3, hS9] at h1
    omega
  obtain ⟨ρX, ρY, Φ, hρXinj, hρYinj, hρX, hρY, hres, hΦ, hΦX, hΦY⟩ :=
    exists_tensor_package hXD hDI hfaith hYD hbij hhinj
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) (homD hDI)) :=
    LocalAnalysis.CommutingFactor.finite_endUnits
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) I) :=
    LocalAnalysis.CommutingFactor.finite_endUnits
  have hcardX : Nat.card X = s * (s ^ 2 - 1) / 2 := by
    rw [Nat.card_congr eX.toEquiv, p2_card (by omega : s ≠ 2)]
  have hdvd : Nat.card X ∣ 168 := by
    rw [← natCard_gl_of_finrank hU3]
    exact Subgroup.card_dvd_of_injective ρX hρXinj
  have hs7 : s = 7 := eq_seven_of_dvd hs hs5 (by rw [← hcardX]; exact hdvd)
  have hcardX7 : Nat.card X = 168 := by norm_num [hcardX, hs7]
  obtain ⟨H, f, hH2, hf0, hHker, hfuniq, himage⟩ :=
    exists_axis_of_image hI3 hAY hA2 (by norm_num [ha, ha2]) ρY hρYinj hρY hm2
  refine ⟨hs7, le_antisymm hDY hYD, hj1, by norm_num [ha, ha2], by omega, I, homD hDI, ρX, ρY,
    Φ, hU3, hI3, hS9,
    hρXinj.bijective_of_nat_card_le ((natCard_gl_of_finrank hU3).trans hcardX7.symm).le,
    hρYinj.bijective_of_nat_card_le ((natCard_gl_of_finrank hI3).trans
      (natCard_GL32.symm.trans (Nat.card_congr eY.toEquiv).symm)).le,
    hρX, hρY, hΦ, hΦX, hΦY,
    ⟨Φ₀, fun y v => (congrArg Φ₀ (funext fun i => hres y (v i))).trans (hΦ₀ _ v)⟩,
    H, f, hH2, hf0, hHker, hfuniq, himage⟩

end CFSG.Quasithin.H13.NQTerm

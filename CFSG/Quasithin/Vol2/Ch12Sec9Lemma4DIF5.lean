module

public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIFacts2
public import CFSG.Quasithin.Vol2.Ch12Sec9Lemma4DIF1Stab
public import CFSG.LargeExtraspecial.S45QLin

public section

namespace CFSG.Quasithin.H13.C1294

open Module CFSG.Open CFSG.Quasithin

private theorem f5_finite_gl (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [Module.Finite (ZMod 2) W] : Finite (W ≃ₗ[ZMod 2] W) := by
  haveI : Finite W := Module.finite_of_finite (ZMod 2)
  exact Finite.of_injective (fun e : W ≃ₗ[ZMod 2] W => (e : W → W))
    fun a b h => LinearEquiv.ext fun x => congrFun h x

private theorem f5_card_gl (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 3) :
    Nat.card (W ≃ₗ[ZMod 2] W) = 168 := by
  let e := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.basisMatrixEquiv
    (Module.finBasisOfFinrankEq (ZMod 2) W hW)
  rw [Nat.card_congr e.toEquiv, Matrix.card_GL_field, Fin.prod_univ_three, ZMod.card]
  norm_num

private theorem f5_simple_gl (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 3) :
    IsSimpleGroup (W ≃ₗ[ZMod 2] W) := by
  haveI := CFSG.LargeExtraspecial.S45Q.isSimpleGroup_top_of_three_le (V := W) (by omega)
  exact (Subgroup.topEquiv :
    (⊤ : Subgroup (W ≃ₗ[ZMod 2] W)) ≃* (W ≃ₗ[ZMod 2] W)).symm.isSimpleGroup

private theorem f5_o2_top (W : Type) [AddCommGroup W] [Module (ZMod 2) W]
    [FiniteDimensional (ZMod 2) W] (hW : finrank (ZMod 2) W = 3) :
    oTwoUpper (⊤ : Subgroup (W ≃ₗ[ZMod 2] W)) = ⊤ := by
  haveI := f5_simple_gl W hW
  haveI := f5_finite_gl W
  have hnorm : (oTwoUpper (⊤ : Subgroup (W ≃ₗ[ZMod 2] W))).Normal := by
    refine ⟨fun n hn g => conj_mem_oTwoUpper ?_ hn⟩
    have htop : Subgroup.normalizer ((⊤ : Subgroup (W ≃ₗ[ZMod 2] W)) : Set (W ≃ₗ[ZMod 2] W)) = ⊤ :=
      Subgroup.normalizer_eq_top_iff.2 inferInstance
    rw [htop]
    exact Subgroup.mem_top g
  haveI := hnorm
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := W ≃ₗ[ZMod 2] W) 3
    (by rw [f5_card_gl W hW]; norm_num)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (oTwoUpper (⊤ : Subgroup (W ≃ₗ[ZMod 2] W))) with h | h
  · exfalso
    have hxO : x ∈ oTwoUpper (⊤ : Subgroup (W ≃ₗ[ZMod 2] W)) :=
      mem_oTwoUpper_of_odd (Subgroup.mem_top x) (by rw [hx]; exact ⟨1, rfl⟩)
    rw [h, Subgroup.mem_bot] at hxO
    rw [hxO, orderOf_one] at hx
    norm_num at hx
  · exact h

private theorem f5_finrank_quot {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] {V₁ : Submodule (ZMod 2) V} (hV : finrank (ZMod 2) V = 4)
    (h1 : finrank (ZMod 2) V₁ = 1) : finrank (ZMod 2) (V ⧸ V₁) = 3 := by
  have := Submodule.finrank_quotient_add_finrank V₁
  omega

private theorem f5_finrank_image {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
    [Module.Finite (ZMod 2) V] {V₁ X : Submodule (ZMod 2) V} (hV₁X : V₁ ≤ X)
    (h1 : finrank (ZMod 2) V₁ = 1) (h3 : finrank (ZMod 2) X = 3) :
    finrank (ZMod 2) (X.map V₁.mkQ) = 2 := by
  let f : X →ₗ[ZMod 2] (V ⧸ V₁) := V₁.mkQ ∘ₗ X.subtype
  have hr : LinearMap.range f = X.map V₁.mkQ := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  have hk : LinearMap.ker f = V₁.comap X.subtype := by
    ext x
    simp [f]
  have hk1 : finrank (ZMod 2) (LinearMap.ker f) = 1 := by
    rw [hk, (Submodule.comapSubtypeEquivOfLe hV₁X).finrank_eq, h1]
  have key := LinearMap.finrank_range_add_finrank_ker f
  rw [hr, hk1, h3] at key
  omega

private theorem f5_exists_two_dim {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] {Y : Submodule (ZMod 2) U} (hU : finrank (ZMod 2) U = 3)
    (hY : finrank (ZMod 2) Y = 2) :
    ∃ B : Submodule (ZMod 2) U, finrank (ZMod 2) B = 2 ∧ ∃ c ∈ B, c ∉ Y := by
  have hYtop : Y ≠ ⊤ := by
    intro h
    rw [h, finrank_top] at hY
    omega
  obtain ⟨c, hc⟩ : ∃ c : U, c ∉ Y := by
    by_contra hcon
    push_neg at hcon
    exact hYtop (eq_top_iff.2 fun c _ => hcon c)
  have hYbot : Y ≠ ⊥ := by
    intro h
    rw [h, finrank_bot] at hY
    omega
  obtain ⟨x, hxY, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hYbot
  have hli : LinearIndependent (ZMod 2) ![x, c] := by
    rw [LinearIndependent.pair_iff]
    intro s t hst
    rcases (by decide : ∀ t : ZMod 2, t = 0 ∨ t = 1) t with rfl | rfl
    · rw [zero_smul, add_zero] at hst
      rcases smul_eq_zero.1 hst with h | h
      · exact ⟨h, rfl⟩
      · exact absurd h hx0
    · exfalso
      apply hc
      rw [one_smul] at hst
      have hc' : c = -(s • x) := by
        rw [eq_neg_iff_add_eq_zero, add_comm]
        exact hst
      rw [hc']
      exact Y.neg_mem (Y.smul_mem s hxY)
  refine ⟨Submodule.span (ZMod 2) (Set.range ![x, c]), ?_, c,
    Submodule.subset_span ⟨1, by simp⟩, hc⟩
  rw [finrank_span_eq_card hli]
  simp

private theorem f5_moves {U : Type} [AddCommGroup U] [Module (ZMod 2) U]
    [FiniteDimensional (ZMod 2) U] {Y : Submodule (ZMod 2) U} (hU : finrank (ZMod 2) U = 3)
    (hY : finrank (ZMod 2) Y = 2) :
    ∃ e : U ≃ₗ[ZMod 2] U, ∃ z ∈ Y, e z ∉ Y := by
  obtain ⟨B, hB, c, hcB, hc⟩ := f5_exists_two_dim hU hY
  obtain ⟨e, he⟩ := CFSG.Monster.B.TwoA.exists_linearEquiv_map_eq (hY.trans hB.symm)
  have hcm : c ∈ Y.map (e : U →ₗ[ZMod 2] U) := by
    rw [he]
    exact hcB
  obtain ⟨z, hz, hez⟩ := Submodule.mem_map.1 hcm
  have h3 : e z = c := hez
  exact ⟨e, z, hz, by rw [h3]; exact hc⟩

theorem factF5_holds : FactF5 := by
  unfold FactF5
  intro V _ _ hV V₁ hV₁ X hX hV₁X H0
  haveI : Module.Finite (ZMod 2) V := Module.finite_of_finrank_pos (by omega)
  haveI : Finite (V ≃ₗ[ZMod 2] V) := f5_finite_gl V
  have hU : finrank (ZMod 2) (V ⧸ V₁) = 3 := f5_finrank_quot hV hV₁
  have hO2 := f5_o2_top (V ⧸ V₁) hU
  let ψ : stabS V₁ →* ((V ⧸ V₁) ≃ₗ[ZMod 2] (V ⧸ V₁)) := quotHom V₁
  have hψ : Function.Surjective ψ := quotHom_surjective V₁
  have hmap : (oTwoUpper (⊤ : Subgroup (stabS V₁))).map ψ = ⊤ := by
    have h := oTwoUpper_map ψ (⊤ : Subgroup (stabS V₁))
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.2 hψ, hO2] at h
    exact h.symm
  have hsub : oTwoUpper (stabS V₁) =
      (oTwoUpper (⊤ : Subgroup (stabS V₁))).map (stabS V₁).subtype := by
    have h := oTwoUpper_map (stabS V₁).subtype (⊤ : Subgroup (stabS V₁))
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h
    exact h
  have hall : ∀ u : (V ⧸ V₁) ≃ₗ[ZMod 2] (V ⧸ V₁), ∃ m : stabS V₁,
      (m : V ≃ₗ[ZMod 2] V) ∈ oTwoUpper (stabS V₁) ∧ ψ m = u := by
    intro u
    have hu : u ∈ (oTwoUpper (⊤ : Subgroup (stabS V₁))).map ψ := by
      rw [hmap]
      exact Subgroup.mem_top u
    obtain ⟨m, hm, hmu⟩ := Subgroup.mem_map.1 hu
    refine ⟨m, ?_, hmu⟩
    rw [hsub]
    exact Subgroup.mem_map_of_mem _ hm
  have hinv : ∀ u : (V ⧸ V₁) ≃ₗ[ZMod 2] (V ⧸ V₁), ∀ z ∈ X.map V₁.mkQ,
      u z ∈ X.map V₁.mkQ := by
    intro u z hz
    obtain ⟨m, hm, hmu⟩ := hall u
    obtain ⟨x, hxX, rfl⟩ := Submodule.mem_map.1 hz
    refine Submodule.mem_map.2 ⟨(m : V ≃ₗ[ZMod 2] V) x, (H0 _ hm x).1 hxX, ?_⟩
    rw [← hmu]
    exact (quotHom_apply m x).symm
  have hXb : finrank (ZMod 2) (X.map V₁.mkQ) = 2 := f5_finrank_image hV₁X hV₁ hX
  obtain ⟨e, z, hz, hez⟩ := f5_moves hU hXb
  exact hez (hinv e z hz)

end CFSG.Quasithin.H13.C1294

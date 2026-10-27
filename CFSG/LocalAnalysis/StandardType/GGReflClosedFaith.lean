module

public import CFSG.LocalAnalysis.StandardType.GGReflClosedIndep

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nFA_exists_sub_smul {K : Type*} [Field K] {V : Type*} [AddCommGroup V]
    [Module K V] [Module.Free K V] [Module.Finite K V] (T : V →ₗ[K] V)
    (hfin : Module.finrank K (LinearMap.range (T - LinearMap.id)) ≤ 1) :
    ∃ (v : V) (f : Module.Dual K V), ∀ w, T w = w - f w • v := by
  classical
  let D : V →ₗ[K] V := T - LinearMap.id
  have hfinD : Module.finrank K (LinearMap.range D) ≤ 1 := hfin
  obtain ⟨v, hv⟩ :=
    (finrank_le_one_iff (K := K) (V := ↥(LinearMap.range D))).mp hfinD
  by_cases hv0 : (v : V) = 0
  · have hrange_bot : LinearMap.range D = ⊥ := by
      rw [Submodule.eq_bot_iff]
      intro w hw
      obtain ⟨c, hc⟩ := hv ⟨w, hw⟩
      have hc' : c • (v : V) = w := congrArg Subtype.val hc
      rw [hv0, smul_zero] at hc'
      exact hc'.symm
    have hD : D = 0 := LinearMap.range_eq_bot.mp hrange_bot
    have hT : T = LinearMap.id := sub_eq_zero.mp (by simpa [D] using hD)
    exact ⟨0, 0, fun w => by rw [hT]; simp⟩
  · obtain ⟨φ, hφ⟩ := Module.Projective.exists_dual_eq_one K hv0
    refine ⟨(v : V), -(φ.comp D), fun w => ?_⟩
    obtain ⟨c, hc⟩ := hv ⟨D w, ⟨w, rfl⟩⟩
    have hcval : c • (v : V) = D w := congrArg Subtype.val hc
    have hφw : (φ.comp D) w = c := by
      rw [LinearMap.comp_apply, ← hcval, map_smul, hφ, smul_eq_mul, mul_one]
    rw [LinearMap.neg_apply, neg_smul, sub_neg_eq_add, hφw, hcval,
      show D w = T w - w from rfl]
    abel

private theorem l05nFA_dual_linearCombination {ι : Type} [Fintype ι] {C : Matrix ι ι ℤ}
    {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (h : ι → V) (f : ι → Module.Dual (ZMod p) V)
    (hfh : ∀ i j, f i (h j) = ((C i j : ℤ) : ZMod p)) (i : ι) (c : ι → ZMod p) :
    f i (Fintype.linearCombination (ZMod p) h c) = ∑ j, ((C i j : ℤ) : ZMod p) * c j := by
  rw [Fintype.linearCombination_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, hfh, smul_eq_mul, mul_comm]

theorem ggReflClosed_of_faithful {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] [Finite V] {Λ : Type} [Fintype Λ] [DecidableEq Λ] (hp : p ≠ 2)
    {C : Matrix Λ Λ ℤ} (hFT : TauCeti.IsFiniteType C) {M : CoxeterMatrix Λ}
    (hC : GGIntCartan M C) (h : Λ → V) (α : Λ → Module.Dual (ZMod p) V)
    (hpair : ∀ i j, α i (h j) = (C i j : ZMod p)) (s : Λ → V ≃ₗ[ZMod p] V)
    (hs : ∀ i v, s i v = v - α i v • h i)
    (f : M.Group ≃* ↥(Subgroup.closure (Set.range s)))
    (hf : ∀ i, (f (M.simple i) : V ≃ₗ[ZMod p] V) = s i) :
    GGReflClosed s := by
  classical
  let h' : Λ → (Λ → ZMod p) := fun i => Pi.single i (1 : ZMod p)
  let α' : Λ → (Λ → ZMod p) →ₗ[ZMod p] ZMod p := fun i =>
    { toFun := fun v => ∑ j, ((C i j : ℤ) : ZMod p) * v j
      map_add' := by intro a b; simp [mul_add, Finset.sum_add_distrib]
      map_smul' := by
        intro c a
        simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply, Finset.mul_sum]
        refine Finset.sum_congr rfl fun x _ => ?_
        ring }
  have hα' : ∀ i, α' i (h' i) = 2 := by
    intro i
    change (∑ k, ((C i k : ℤ) : ZMod p) * h' i k) = 2
    rw [Finset.sum_eq_single i]
    · simp only [h', Pi.single_eq_same, mul_one, hC.1 i]
      norm_num
    · intro b _ hb
      simp only [h', Pi.single_eq_of_ne hb, mul_zero]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hpair' : ∀ i j, α' i (h' j) = (C i j : ZMod p) := by
    intro i j
    change (∑ k, ((C i k : ℤ) : ZMod p) * h' j k) = (C i j : ZMod p)
    rw [Finset.sum_eq_single j]
    · simp only [h', Pi.single_eq_same, mul_one]
    · intro b _ hb
      simp only [h', Pi.single_eq_of_ne hb, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hind' : LinearIndependent (ZMod p) h' := by
    have hb := (Pi.basisFun (ZMod p) Λ).linearIndependent
    convert hb using 1
    funext i
    rw [Pi.basisFun_apply]
  let s' : Λ → (Λ → ZMod p) ≃ₗ[ZMod p] (Λ → ZMod p) := fun i => Module.reflection (hα' i)
  have hs' : ∀ i v, s' i v = v - α' i v • h' i := fun i v => Module.reflection_apply v (hα' i)
  have hRC' : GGReflClosed s' :=
    ggReflClosed_of_indep hp hFT hC h' α' hpair' hind' s' hs'
  let π : (Λ → ZMod p) →ₗ[ZMod p] V := Fintype.linearCombination (ZMod p) h
  have hπsingle : ∀ i, π (h' i) = h i := by
    intro i
    show Fintype.linearCombination (ZMod p) h (Pi.single i 1) = h i
    rw [Fintype.linearCombination_apply, Finset.sum_eq_single i]
    · rw [Pi.single_eq_same, one_smul]
    · intro b _ hb
      rw [Pi.single_eq_of_ne hb, zero_smul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  have hπα : ∀ i v', α' i v' = α i (π v') := fun i v' =>
    (l05nFA_dual_linearCombination h α hpair i v').symm
  have hπs : ∀ i v', π (s' i v') = s i (π v') := by
    intro i v'
    rw [hs' i v', map_sub, map_smul, hπsingle i, hs i (π v'), ← hπα i v']
  let W := Subgroup.closure (Set.range s)
  let W' := Subgroup.closure (Set.range s')
  let ρ : M.Group →* (V ≃ₗ[ZMod p] V) := (Subgroup.subtype W).comp f
  have hρsimple : ∀ i, ρ (M.simple i) = s i := by
    intro i
    change (f (M.simple i) : V ≃ₗ[ZMod p] V) = s i
    exact hf i
  let hlift' : M.IsLiftable (fun i => Module.reflection (hα' i)) :=
    isLiftable_reflection_of_intCartan hC h' α' hα' hpair'
  let ρ' : M.Group →* ((Λ → ZMod p) ≃ₗ[ZMod p] (Λ → ZMod p)) :=
    M.toCoxeterSystem.lift ⟨fun i => Module.reflection (hα' i), hlift'⟩
  have hρ'simple : ∀ i, ρ' (M.simple i) = s' i :=
    fun i => CoxeterSystem.lift_apply_simple M.toCoxeterSystem hlift' i
  have hinj' : Function.Injective ρ' :=
    ggCartanFaithful_of_isFiniteType (hα := hα') (hP := hpair') hp hFT hC hind'
  have hrange' : ρ'.range = W' := by
    rw [MonoidHom.range_eq_map, ← M.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp]
    congr 1
  let g : M.Group ≃* W' := (MonoidHom.ofInjective hinj').trans (MulEquiv.subgroupCongr hrange')
  have hg_apply : ∀ t, ((g t : W') : (Λ → ZMod p) ≃ₗ[ZMod p] (Λ → ZMod p)) = ρ' t := by
    intro t
    rw [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply, MonoidHom.ofInjective_apply]
  let Φ : W' ≃* W := g.symm.trans f
  let Φc : W' →* (V ≃ₗ[ZMod p] V) := (Subgroup.subtype W).comp Φ
  have hΦsimple : ∀ i, (Φ ⟨s' i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : V ≃ₗ[ZMod p] V) = s i := by
    intro i
    have hgi : g (M.simple i) = ⟨s' i, Subgroup.subset_closure ⟨i, rfl⟩⟩ := by
      apply Subtype.ext
      rw [hg_apply, hρ'simple]
    rw [MulEquiv.trans_apply, ← hgi, MulEquiv.symm_apply_apply]
    exact hf i
  have hπρ : ∀ t : M.Group, ∀ v' : (Λ → ZMod p), π (ρ' t v') = ρ t (π v') := by
    intro t
    induction t using M.toCoxeterSystem.simple_induction_left with
    | one => intro v'; simp
    | mul_simple_left w i ih =>
      intro v'
      rw [map_mul, LinearEquiv.mul_apply, map_mul, LinearEquiv.mul_apply]
      rw [CoxeterMatrix.toCoxeterSystem_simple]
      rw [hρ'simple, hρsimple i, hπs i ((ρ' w) v'), ih v']
  let Cmod : Matrix Λ Λ (ZMod p) := C.map (Int.castRingHom (ZMod p))
  have hα'Cmod : ∀ i v', α' i v' = Cmod.mulVec v' i := by
    intro i v'
    change (∑ j, ((C i j : ℤ) : ZMod p) * v' j) = Cmod.mulVec v' i
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    change ((C i j : ℤ) : ZMod p) * v' j = (C.map (Int.castRingHom (ZMod p))) i j * v' j
    rw [Matrix.map_apply]
    rfl
  have hkerπ : ∀ v', π v' = 0 → Cmod.mulVec v' = 0 := by
    intro v' hv'
    funext i
    rw [← hα'Cmod i v', hπα i v', hv']
    exact map_zero (α i)
  have hfixsimple : ∀ v', Cmod.mulVec v' = 0 → ∀ i, ρ' (M.simple i) v' = v' := by
    intro v' hv' i
    rw [hρ'simple, hs' i v', hα'Cmod i v', hv']
    simp
  have hfixofC : ∀ v', Cmod.mulVec v' = 0 → ∀ t, ρ' t v' = v' := by
    intro v' hv' t
    induction t using M.toCoxeterSystem.simple_induction_left with
    | one => simp
    | mul_simple_left w i ih =>
      rw [map_mul, LinearEquiv.mul_apply]
      rw [CoxeterMatrix.toCoxeterSystem_simple]
      rw [ih, hfixsimple v' hv' i]
  intro r hr hr2 hr1 hform
  obtain ⟨v, φ, hvf⟩ := hform
  have hv0 : v ≠ 0 := by
    intro h0
    apply hr1
    ext w
    simp [hvf w, h0]
  let t : M.Group := f.symm ⟨r, hr⟩
  have hftW : f t = ⟨r, hr⟩ := MulEquiv.apply_symm_apply f ⟨r, hr⟩
  have hft : (f t : V ≃ₗ[ZMod p] V) = r := by rw [hftW]
  have hW2 : (⟨r, hr⟩ : W) ^ 2 = 1 := by
    apply Subtype.ext
    change r ^ 2 = 1
    exact hr2
  have ht2 : t * t = 1 := by
    apply f.injective
    rw [map_mul, map_one, hftW, ← pow_two]
    exact hW2
  let t' : W' := g t
  have ht'_coe : (t' : (Λ → ZMod p) ≃ₗ[ZMod p] (Λ → ZMod p)) = ρ' t := by
    change ((g t : W') : (Λ → ZMod p) ≃ₗ[ZMod p] (Λ → ZMod p)) = ρ' t
    exact hg_apply t
  have ht'2L : (t' : (Λ → ZMod p) ≃ₗ[ZMod p] (Λ → ZMod p)) ^ 2 = 1 := by
    change (ρ' t) ^ 2 = 1
    rw [pow_two, ← map_mul, ht2, map_one]
  have ht'1 : t' ≠ 1 := by
    intro h1
    have ht1 : t = 1 := by
      apply g.injective
      rw [map_one]
      exact h1
    apply hr1
    have h2 : f t = 1 := by rw [ht1, map_one]
    rw [hftW] at h2
    exact Subtype.ext_iff.mp h2
  have ht'1L : (t' : (Λ → ZMod p) ≃ₗ[ZMod p] (Λ → ZMod p)) ≠ 1 :=
    fun h1 => ht'1 (Subtype.ext h1)
  let Tl : (Λ → ZMod p) →ₗ[ZMod p] (Λ → ZMod p) := (ρ' t).toLinearMap
  have hTl2 : ∀ x, Tl (Tl x) = x := by
    intro x
    have h := congrArg (fun e : (Λ → ZMod p) ≃ₗ[ZMod p] (Λ → ZMod p) => e x)
      (show ρ' t * ρ' t = 1 by rw [← map_mul, ht2, map_one])
    simpa [Tl, LinearEquiv.mul_apply] using h
  have hπ_Tl : ∀ y, π (Tl y) = r (π y) := by
    intro y
    change π (ρ' t y) = r (π y)
    rw [hπρ t y, show ρ t = r from hft]
  have hinj_on : ∀ z ∈ LinearMap.range (Tl - LinearMap.id), π z = 0 → z = 0 := by
    intro z hz hπz
    obtain ⟨y, rfl⟩ := hz
    have hneg : Tl (Tl y - y) = -(Tl y - y) := by
      rw [map_sub, hTl2 y]
      abel
    have hCz : Cmod.mulVec (Tl y - y) = 0 := hkerπ _ hπz
    have hfixz : ρ' t (Tl y - y) = Tl y - y := hfixofC _ hCz t
    have h1 : Tl (Tl y - y) = Tl y - y := hfixz
    have hneg2 : Tl y - y = -(Tl y - y) := h1.symm.trans hneg
    have h2z : (2 : ZMod p) • (Tl y - y) = 0 := by
      rw [two_smul]
      exact eq_neg_iff_add_eq_zero.mp hneg2
    rcases smul_eq_zero.mp h2z with h | h
    · exact absurd h (zmod_two_ne_zero hp)
    · exact h
  have hmap_le : ∀ x ∈ LinearMap.range (Tl - LinearMap.id),
      π x ∈ Submodule.span (ZMod p) ({v} : Set V) := by
    intro x hx
    obtain ⟨y, rfl⟩ := hx
    have h1 : π (Tl y - y) = -(φ (π y) • v) := by
      rw [map_sub, hπ_Tl y, hvf (π y)]
      abel
    show π (Tl y - y) ∈ Submodule.span (ZMod p) ({v} : Set V)
    rw [h1]
    exact Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  have hinj_comp : Function.Injective
      (π.comp (LinearMap.range (Tl - LinearMap.id)).subtype) := by
    intro x y hxy
    apply Subtype.ext
    have hπxy : π ((x : Λ → ZMod p) - y) = 0 := by
      change π (x : Λ → ZMod p) = π (y : Λ → ZMod p) at hxy
      rw [map_sub, hxy, sub_self]
    have hmem : (x : Λ → ZMod p) - y ∈ LinearMap.range (Tl - LinearMap.id) :=
      Submodule.sub_mem _ x.2 y.2
    exact sub_eq_zero.mp (hinj_on _ hmem hπxy)
  have hfin : Module.finrank (ZMod p) (LinearMap.range (Tl - LinearMap.id)) ≤ 1 := by
    have h1 : Module.finrank (ZMod p) (LinearMap.range (Tl - LinearMap.id)) =
        Module.finrank (ZMod p)
          (LinearMap.range (π.comp (LinearMap.range (Tl - LinearMap.id)).subtype)) :=
      (LinearMap.finrank_range_of_inj hinj_comp).symm
    rw [h1]
    have h2 : LinearMap.range (π.comp (LinearMap.range (Tl - LinearMap.id)).subtype) ≤
        Submodule.span (ZMod p) ({v} : Set V) := by
      rintro z ⟨y, rfl⟩
      exact hmap_le y y.2
    calc Module.finrank (ZMod p)
          (LinearMap.range (π.comp (LinearMap.range (Tl - LinearMap.id)).subtype))
        ≤ Module.finrank (ZMod p) (Submodule.span (ZMod p) ({v} : Set V)) :=
          Submodule.finrank_mono h2
      _ = 1 := finrank_span_singleton hv0
  obtain ⟨v', f', hv'f'⟩ := l05nFA_exists_sub_smul Tl hfin
  have hform' : ∃ (v : Λ → ZMod p) (f : Module.Dual (ZMod p) (Λ → ZMod p)),
      ∀ w, (t' : (Λ → ZMod p) ≃ₗ[ZMod p] (Λ → ZMod p)) w = w - f w • v := by
    refine ⟨v', f', fun w => ?_⟩
    rw [ht'_coe]
    exact hv'f' w
  obtain ⟨u', hu'W', i, ht'eq⟩ :=
    hRC' (t' : (Λ → ZMod p) ≃ₗ[ZMod p] (Λ → ZMod p)) t'.2 ht'2L ht'1L hform'
  refine ⟨(Φ ⟨u', hu'W'⟩ : V ≃ₗ[ZMod p] V), (Φ ⟨u', hu'W'⟩).2, i, ?_⟩
  have hΦeq : (Φ ⟨t', t'.2⟩ : V ≃ₗ[ZMod p] V) =
      (Φ ⟨u', hu'W'⟩ : V ≃ₗ[ZMod p] V) * s i *
        (Φ ⟨u', hu'W'⟩ : V ≃ₗ[ZMod p] V)⁻¹ := by
    have hEq : (⟨t', t'.2⟩ : W') =
        (⟨u', hu'W'⟩ : W') * (⟨s' i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : W') *
          (⟨u', hu'W'⟩ : W')⁻¹ := Subtype.ext ht'eq
    calc (Φ ⟨t', t'.2⟩ : V ≃ₗ[ZMod p] V) = Φc ⟨t', t'.2⟩ := rfl
      _ = Φc ((⟨u', hu'W'⟩ : W') * (⟨s' i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : W') *
            (⟨u', hu'W'⟩ : W')⁻¹) := by rw [hEq]
      _ = Φc (⟨u', hu'W'⟩ : W') * Φc (⟨s' i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : W') *
            (Φc (⟨u', hu'W'⟩ : W'))⁻¹ := by rw [map_mul, map_mul, map_inv]
      _ = (Φ ⟨u', hu'W'⟩ : V ≃ₗ[ZMod p] V) * s i *
            (Φ ⟨u', hu'W'⟩ : V ≃ₗ[ZMod p] V)⁻¹ := by
            rw [show Φc (⟨s' i, Subgroup.subset_closure ⟨i, rfl⟩⟩ : W') = s i
              from hΦsimple i]
            rfl
  have hΦt' : (Φ ⟨t', t'.2⟩ : V ≃ₗ[ZMod p] V) = r := by
    change (Φ (g t) : V ≃ₗ[ZMod p] V) = r
    rw [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
    exact hft
  exact hΦt'.symm.trans hΦeq

end CFSG.StandardType

end

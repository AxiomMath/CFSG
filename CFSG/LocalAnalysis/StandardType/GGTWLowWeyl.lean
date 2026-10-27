module

public import CFSG.LocalAnalysis.StandardType.GGWeylESystem
public import CFSG.LocalAnalysis.StandardType.GGTWLowStmt

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem l05nD9_transport {N : ℕ} {Γ : Type}
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V) {A : Subgroup (MulAut ↥Bs)}
    (θ : V ≃ₗ[ZMod 3] GGTWE 3 N) (gens : Set (V ≃ₗ[ZMod 3] V))
    (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure gens)
    (S : Set (Module.End (ZMod 3) (GGTWE 3 N)))
    (hS₁ : ∀ g ∈ gens, ∃ y ∈ S,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hS₂ : ∀ y ∈ S, ∃ g ∈ gens,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (c f : Γ → GGTWE 3 N) (hcf : ∀ i, ggTWdot (f i) (c i) = 2)
    (s : Γ → Module.End (ZMod 3) (GGTWE 3 N)) (hs_eq : ∀ i, s i = ggTWRefl (c i) (f i))
    (hsgen : Submonoid.closure (Set.range s) = Submonoid.closure S) :
    ∃ (x : Γ → V) (β : Γ → Module.Dual (ZMod 3) V) (hβx : ∀ i, β i (x i) = 2)
      (φ : Γ → MulAut ↥Bs),
      (∀ i, x i = θ.symm (c i)) ∧
      (∀ i, β i = (ggTWform (f i)).comp θ.toLinearMap) ∧
      (∀ i, (Module.reflection (hβx i) : V →ₗ[ZMod 3] V) =
        θ.symm.toLinearMap ∘ₗ s i ∘ₗ θ.toLinearMap) ∧
      (∀ i, ggLin (p := 3) ι (φ i) = Module.reflection (hβx i)) ∧
      Subgroup.closure (Set.range φ) = A ∧
      Subgroup.closure (Set.range (fun i => Module.reflection (hβx i))) =
        Subgroup.closure gens ∧
      Nat.card ↥(Submonoid.closure S) ≤ Nat.card ↥A := by
  classical
  haveI : Finite (Additive ↥Bs) := inferInstance
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Finite (V → V) := inferInstance
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  let x : Γ → V := fun i => θ.symm (c i)
  let β : Γ → Module.Dual (ZMod 3) V := fun i => (ggTWform (f i)).comp θ.toLinearMap
  have hβx : ∀ i, β i (x i) = 2 := by
    intro i
    change ggTWform (f i) (θ (θ.symm (c i))) = 2
    rw [LinearEquiv.apply_symm_apply]
    rw [show ggTWform (f i) (c i) = ggTWdot (f i) (c i) by
      simp [ggTWform, ggTWdot, ggDepAform, ggDepAdot]]
    exact hcf i
  let e : Γ → V ≃ₗ[ZMod 3] V := fun i => Module.reflection (hβx i)
  have he : ∀ i, (e i : V →ₗ[ZMod 3] V) =
      θ.symm.toLinearMap ∘ₗ s i ∘ₗ θ.toLinearMap := by
    intro i
    apply LinearMap.ext
    intro v
    change (Module.reflection (hβx i) : V →ₗ[ZMod 3] V) v =
      (θ.symm.toLinearMap ∘ₗ s i ∘ₗ θ.toLinearMap) v
    have hrefl : (Module.reflection (hβx i) : V →ₗ[ZMod 3] V) v = v - β i v • x i :=
      Module.reflection_apply v (hβx i)
    rw [hrefl]
    change v - (ggTWform (f i)) (θ v) • x i = θ.symm (s i (θ v))
    rw [show s i (θ v) = θ v - ggTWdot (f i) (θ v) • c i by
      rw [hs_eq i]
      simp [ggTWRefl, ggDepARefl, ggDepAform, ggDepAdot, LinearMap.smulRight_apply,
        smul_eq_mul]]
    rw [map_sub, map_smul, LinearEquiv.symm_apply_apply]
    change v - (ggTWform (f i)) (θ v) • (θ.symm (c i)) =
      v - ggTWdot (f i) (θ v) • (θ.symm (c i))
    rw [show ggTWform (f i) (θ v) = ggTWdot (f i) (θ v) by
      simp [ggTWform, ggTWdot, ggDepAform, ggDepAdot]]
  set Φ : Module.End (ZMod 3) (GGTWE 3 N) ≃+* Module.End (ZMod 3) V :=
    θ.symm.conjRingEquiv with hΦ
  have hΦ_apply : ∀ y, (Φ y : V →ₗ[ZMod 3] V) =
      θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap := by
    intro y
    ext v
    rw [LinearEquiv.conjRingEquiv_apply_apply]
    rfl
  have hA_fact : ∀ y ∈ Submonoid.closure S, ∃ g ∈ Subgroup.closure gens,
      (g : V →ₗ[ZMod 3] V) = Φ y := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem z hz =>
        obtain ⟨g, hg, hgz⟩ := hS₂ z hz
        exact ⟨g, Subgroup.subset_closure hg, by rw [hgz, hΦ_apply]⟩
    | one => exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩
    | mul a b _ _ iha ihb =>
        obtain ⟨ga, hga, hgae⟩ := iha
        obtain ⟨gb, hgb, hgbe⟩ := ihb
        exact ⟨ga * gb, Subgroup.mul_mem _ hga hgb,
          by rw [map_mul, LinearEquiv.coe_toLinearMap_mul, hgae, hgbe]⟩
  have hB_fact : ∀ y ∈ Submonoid.closure (Set.range s),
      ∃ h ∈ Subgroup.closure (Set.range e), (h : V →ₗ[ZMod 3] V) = Φ y := by
    intro y hy
    induction hy using Submonoid.closure_induction with
    | mem z hz =>
        obtain ⟨i, rfl⟩ := hz
        exact ⟨e i, Subgroup.subset_closure ⟨i, rfl⟩, by rw [he i, hΦ_apply]⟩
    | one => exact ⟨1, Subgroup.one_mem _, by rw [map_one]; rfl⟩
    | mul a b _ _ iha ihb =>
        obtain ⟨ha, hha, hhae⟩ := iha
        obtain ⟨hb, hhb, hhbe⟩ := ihb
        exact ⟨ha * hb, Subgroup.mul_mem _ hha hhb,
          by rw [map_mul, LinearEquiv.coe_toLinearMap_mul, hhae, hhbe]⟩
  have hle1 : Subgroup.closure (Set.range e) ≤ Subgroup.closure gens := by
    rw [Subgroup.closure_le]
    rintro _ ⟨i, rfl⟩
    have hsi : s i ∈ Submonoid.closure S := by
      rw [← hsgen]
      exact Submonoid.subset_closure ⟨i, rfl⟩
    obtain ⟨g, hg, hge⟩ := hA_fact (s i) hsi
    have hcoe : (e i : V →ₗ[ZMod 3] V) = (g : V →ₗ[ZMod 3] V) := by
      rw [he i, hge, hΦ_apply]
    have hee : e i = g := LinearEquiv.ext fun v =>
      congrArg (fun T : V →ₗ[ZMod 3] V => T v) hcoe
    simpa [hee] using hg
  have hle2 : Subgroup.closure gens ≤ Subgroup.closure (Set.range e) := by
    rw [Subgroup.closure_le]
    intro g hg
    obtain ⟨y, hyS, hyeq⟩ := hS₁ g hg
    have hy : y ∈ Submonoid.closure (Set.range s) := by
      rw [hsgen]
      exact Submonoid.subset_closure hyS
    obtain ⟨h, hh, hhe⟩ := hB_fact y hy
    have hcoe : (g : V →ₗ[ZMod 3] V) = (h : V →ₗ[ZMod 3] V) := by
      rw [hyeq, hhe, hΦ_apply]
    have hgh : g = h := LinearEquiv.ext fun v =>
      congrArg (fun T : V →ₗ[ZMod 3] V => T v) hcoe
    simpa [hgh] using hh
  have hgeneq : Subgroup.closure (Set.range e) = Subgroup.closure gens :=
    le_antisymm hle1 hle2
  have hcardS : Nat.card ↥(Submonoid.closure S) ≤ Nat.card ↥(Subgroup.closure gens) := by
    let F : ↥(Submonoid.closure S) → ↥(Subgroup.closure gens) := fun y =>
      ⟨Classical.choose (hA_fact y y.2), (Classical.choose_spec (hA_fact y y.2)).1⟩
    have hFeq : ∀ y : ↥(Submonoid.closure S),
        ((F y : ↥(Subgroup.closure gens)) : V →ₗ[ZMod 3] V) = Φ y :=
      fun y => (Classical.choose_spec (hA_fact y y.2)).2
    have hFinj : Function.Injective F := by
      intro y1 y2 h
      have h1 : ((F y1 : ↥(Subgroup.closure gens)) : V →ₗ[ZMod 3] V) =
          ((F y2 : ↥(Subgroup.closure gens)) : V →ₗ[ZMod 3] V) := by rw [h]
      rw [hFeq y1, hFeq y2] at h1
      exact Subtype.ext (Φ.injective h1)
    exact Nat.card_le_card_of_injective F hFinj
  have hcardAeq : Nat.card ↥A = Nat.card ↥(Subgroup.closure gens) := by
    rw [← hA]
    exact Nat.card_congr (Subgroup.equivMapOfInjective A (ggLin (p := 3) ι)
      (ggLin_injective (p := 3) ι)).toEquiv
  have hcardS_le : Nat.card ↥(Submonoid.closure S) ≤ Nat.card ↥A := by
    rw [hcardAeq]
    exact hcardS
  have heA : ∀ i, e i ∈ A.map (ggLin (p := 3) ι) := by
    intro i
    rw [hA]
    exact hle1 (Subgroup.subset_closure ⟨i, rfl⟩)
  choose φ hφA hφlin using fun i => Subgroup.mem_map.mp (heA i)
  have hmap_e : (Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range e) := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap, Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      change ggLin (p := 3) ι (φ i) ∈ Subgroup.closure (Set.range e)
      rw [hφlin i]
      exact Subgroup.subset_closure ⟨i, rfl⟩
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact Subgroup.mem_map.mpr ⟨φ i, Subgroup.subset_closure ⟨i, rfl⟩, hφlin i⟩
  have hmap_eq : (Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι) =
      Subgroup.closure gens := by
    rw [hmap_e, hgeneq]
  have hφclosure : Subgroup.closure (Set.range φ) = A := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hφA i
    · intro a ha
      have hmem : ggLin (p := 3) ι a ∈
          (Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι) := by
        rw [hmap_eq, ← hA]
        exact Subgroup.mem_map.mpr ⟨a, ha, rfl⟩
      obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.mp hmem
      have hb_eq : b = a := ggLin_injective (p := 3) ι hba
      simpa [hb_eq] using hb
  exact ⟨x, β, hβx, φ, (fun i => rfl), (fun i => rfl), he, hφlin, hφclosure, hgeneq, hcardS_le⟩

theorem ggTWLow_weyl_E6
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V) {A : Subgroup (MulAut ↥Bs)}
    (θ : V ≃ₗ[ZMod 3] GGTWE 3 6) (gens : Set (V ≃ₗ[ZMod 3] V))
    (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure gens)
    (S : Set (Module.End (ZMod 3) (GGTWE 3 6)))
    (hS₁ : ∀ g ∈ gens, ∃ y ∈ S,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hS₂ : ∀ y ∈ S, ∃ g ∈ gens,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hOut : GGTWLowE6Outcome S) : GGWeylReflectionGroup 3 A := by
  obtain ⟨hcardS_eq, s, hsrefl, hsgen, hrel⟩ := hOut
  choose c f hcf hs_eq using hsrefl
  obtain ⟨x, β, hβx, φ, _hx, _hβ, he, hφlin, hφclosure, _hgeneq, hcardS_le⟩ :=
    l05nD9_transport (ι := ι) (A := A) (θ := θ) (gens := gens) hA S hS₁ hS₂ c f hcf s hs_eq hsgen
  have hrefl : ∀ i, GGIsReflection 3 (φ i) := fun i =>
    ggIsReflection_of_eq_reflection (p := 3) (by norm_num) ι (hβx i) (hφlin i)
  have hrelφ : CoxeterMatrix.E₆.IsLiftable φ := by
    intro i j
    apply ggLin_injective (p := 3) ι
    rw [map_pow, map_mul, hφlin i, hφlin j, map_one]
    let Φ : Module.End (ZMod 3) (GGTWE 3 6) ≃+* Module.End (ZMod 3) V := θ.symm.conjRingEquiv
    have heΦ : ∀ i, (Module.reflection (hβx i) : V →ₗ[ZMod 3] V) = Φ (s i) := by
      intro i
      rw [he i]
      ext v
      rw [LinearEquiv.conjRingEquiv_apply_apply]
      rfl
    let coeEnd : (V ≃ₗ[ZMod 3] V) →* Module.End (ZMod 3) V :=
      { toFun := fun e => (e : V →ₗ[ZMod 3] V)
        map_one' := rfl
        map_mul' := fun a b => LinearEquiv.coe_toLinearMap_mul }
    have hcoeEnd_inj : Function.Injective coeEnd := by
      intro a b h
      exact LinearEquiv.ext (fun v => congrArg (fun T : V →ₗ[ZMod 3] V => T v) h)
    refine hcoeEnd_inj ?_
    rw [map_pow, map_mul, map_one]
    rw [show coeEnd (Module.reflection (hβx i)) = Φ (s i) from heΦ i,
      show coeEnd (Module.reflection (hβx j)) = Φ (s j) from heΦ j,
      ← map_mul, ← map_pow, hrel i j, map_one]
  have hcard : 51840 ≤ Nat.card ↥A := hcardS_eq.trans hcardS_le
  exact ggWeylReflectionGroup_of_E6_system (p := 3) φ hrelφ hrefl hφclosure hcard

private theorem l05nD9_card_weyl_E8 :
    Nat.card CoxeterMatrix.E₈.Group = 696729600 := by
  have hmat : CFSG.LieType.RootSystem.coxeterMatrix
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E8) =
        CoxeterMatrix.E₈ :=
    coxeterMatrix_eq_of_ggIntCartan
      (CFSG.LieType.Chevalley.isFiniteType_cartan CFSG.Blueprint.Chevalley.Tag.E8)
      (by
        rw [show CFSG.Blueprint.Chevalley.Tag.cartan CFSG.Blueprint.Chevalley.Tag.E8 =
            CartanMatrix.E 8 from CFSG.LieType.Chevalley.cartanE_eq 8]
        exact ggIntCartan_E₈)
  rw [← hmat]
  exact NoOffExc.card_weyl_E8

theorem ggTWLow_weyl_E8
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V) {A : Subgroup (MulAut ↥Bs)}
    (θ : V ≃ₗ[ZMod 3] GGTWE 3 9) (gens : Set (V ≃ₗ[ZMod 3] V))
    (hA : A.map (ggLin (p := 3) ι) = Subgroup.closure gens)
    (S : Set (Module.End (ZMod 3) (GGTWE 3 9)))
    (hS₁ : ∀ g ∈ gens, ∃ y ∈ S,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hS₂ : ∀ y ∈ S, ∃ g ∈ gens,
      (g : V →ₗ[ZMod 3] V) = θ.symm.toLinearMap ∘ₗ y ∘ₗ θ.toLinearMap)
    (hOut : GGTWLowE8Outcome S) : GGWeylReflectionGroup 3 A := by
  obtain ⟨hh, αα, hdiag, hpair, hgen⟩ := hOut
  haveI : Finite (Additive ↥Bs) := inferInstance
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Finite (V → V) := inferInstance
  haveI : Finite (V ≃ₗ[ZMod 3] V) :=
    Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  let s : Fin 8 → Module.End (ZMod 3) (GGTWE 3 9) := fun i => ggTWRefl (hh i) (αα i)
  have hs_eq : ∀ i, s i = ggTWRefl (hh i) (αα i) := fun _ => rfl
  obtain ⟨x, β, hβx, φ, _hx, _hβ, _he, hφlin, hφclosure, hgeneq, _hcardS_le⟩ :=
    l05nD9_transport (ι := ι) (A := A) (θ := θ) (gens := gens) hA S hS₁ hS₂ hh αα hdiag s hs_eq hgen
  have hP : ∀ i j, β i (x j) = ((CartanMatrix.E 8 i j : ℤ) : ZMod 3) := by
    intro i j
    rw [show β i = (ggTWform (αα i)).comp θ.toLinearMap from _hβ i]
    rw [show x j = θ.symm (hh j) from _hx j]
    change ggTWform (αα i) (θ (θ.symm (hh j))) = ((CartanMatrix.E 8 i j : ℤ) : ZMod 3)
    rw [LinearEquiv.apply_symm_apply]
    rw [show ggTWform (αα i) (hh j) = ggTWdot (αα i) (hh j) by
      simp [ggTWform, ggTWdot, ggDepAform, ggDepAdot]]
    exact hpair i j
  have hAeq : Nat.card ↥A = Nat.card ↥(Subgroup.closure gens) := by
    rw [← hA]
    exact Nat.card_congr (Subgroup.equivMapOfInjective A (ggLin (p := 3) ι)
      (ggLin_injective (p := 3) ι)).toEquiv
  have hdet8 : (CartanMatrix.E 8).det = 1 := by
    rw [← CFSG.LieType.Chevalley.cartanE_eq 8]
    exact CFSG.LieType.Chevalley.det_cartan_E8
  have hdet : (Matrix.of fun i j => β i (x j)).det ≠ 0 := by
    have hmap : (Matrix.of fun i j => β i (x j)) =
        (Int.castRingHom (ZMod 3)).mapMatrix (CartanMatrix.E 8) := by
      ext i j
      rw [RingHom.mapMatrix_apply]
      exact hP i j
    rw [hmap, ← RingHom.map_det, hdet8]
    norm_num
  have hind : LinearIndependent (ZMod 3) x := linearIndependent_of_det_ne_zero x β hdet
  have hM8 : GGIsWeylMatrixFixed CoxeterMatrix.E₈ :=
    Or.inr (Or.inr (Or.inr (Or.inl ⟨Equiv.refl _, rfl⟩)))
  have hlinLift : CoxeterMatrix.E₈.IsLiftable (fun i => Module.reflection (hβx i)) :=
    isLiftable_reflection_of_intCartan ggIntCartan_E₈ x β hβx hP
  have hinj : Function.Injective (CoxeterMatrix.E₈.toCoxeterSystem.lift
      ⟨fun i => Module.reflection (hβx i), hlinLift⟩) :=
    ggCartanFaithfulInputFixed_holds 3 (by norm_num) (by norm_num) (Fin 8)
      CoxeterMatrix.E₈ (CartanMatrix.E 8) hM8 ggIntCartan_E₈ V x β hβx hP hind
  let F := CoxeterMatrix.E₈.toCoxeterSystem.lift
      ⟨fun i => Module.reflection (hβx i), hlinLift⟩
  have hFrange : F.range =
      Subgroup.closure (Set.range (fun i => Module.reflection (hβx i))) := by
    rw [MonoidHom.range_eq_map, ← CoxeterMatrix.E₈.toCoxeterSystem.subgroup_closure_range_simple,
      MonoidHom.map_closure, ← Set.range_comp]
    congr 1
  have hcardE : 696729600 ≤
      Nat.card ↥(Subgroup.closure (Set.range (fun i => Module.reflection (hβx i)))) := by
    rw [← l05nD9_card_weyl_E8]
    let G' : CoxeterMatrix.E₈.Group →
        ↥(Subgroup.closure (Set.range (fun i => Module.reflection (hβx i)))) := fun w =>
      ⟨F w, by rw [← hFrange]; exact MonoidHom.mem_range.mpr ⟨w, rfl⟩⟩
    have hG' : Function.Injective G' := by
      intro w1 w2 h
      exact hinj (Subtype.ext_iff.mp h)
    exact Nat.card_le_card_of_injective G' hG'
  have hcard : 696729600 ≤ Nat.card ↥A := by
    rw [hAeq, ← hgeneq]
    exact hcardE
  exact ggWeylReflectionGroup_of_E8_pairing (p := 3) (by norm_num) ι φ x β hβx hφlin hP
    hφclosure hcard

end CFSG.StandardType

end

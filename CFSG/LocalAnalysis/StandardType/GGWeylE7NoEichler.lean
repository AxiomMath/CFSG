module

public import CFSG.LocalAnalysis.StandardType.GGWeylE7Sylow
public import CFSG.LocalAnalysis.StandardType.GGQ2EichlerDefs
public import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.E78Sylow
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelCLLWeyl
public import CFSG.LocalAnalysis.StandardType.GGFrameRouteA4Thm

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Module QTwoLin
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.RootSystem

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private lemma ggE7S_diag (i : Fin 7) : (((CartanMatrix.E 7 i i : ℤ) : ZMod 3)) = 2 := by
  revert i
  decide +kernel

private lemma ggE7S_mul_pow (x : Matrix (Fin 7) (Fin 7) (ZMod 3)) (hx : x ∈ ggE7SylowSet)
    (j : Fin 4) (n : ℕ) : x * ggE7SylowGen j ^ n ∈ ggE7SylowSet := by
  induction n with
  | zero => simpa using hx
  | succ n ih =>
      have h := ggE7SylowSet_mul_gen (x * ggE7SylowGen j ^ n) ih j
      simpa [pow_succ, mul_assoc] using h

private lemma ggE7S_set_mul (x y : Matrix (Fin 7) (Fin 7) (ZMod 3))
    (hx : x ∈ ggE7SylowSet) (hy : y ∈ ggE7SylowSet) : x * y ∈ ggE7SylowSet := by
  rw [ggE7SylowSet, Finset.mem_image] at hy
  obtain ⟨p, -, rfl⟩ := hy
  have h0 := ggE7S_mul_pow x hx 0 (p.1 : ℕ)
  have h1 := ggE7S_mul_pow (x * ggE7SylowGen 0 ^ (p.1 : ℕ)) h0 1 (p.2.1 : ℕ)
  have h2 := ggE7S_mul_pow (x * ggE7SylowGen 0 ^ (p.1 : ℕ) *
    ggE7SylowGen 1 ^ (p.2.1 : ℕ)) h1 2 (p.2.2.1 : ℕ)
  have h3 := ggE7S_mul_pow (x * ggE7SylowGen 0 ^ (p.1 : ℕ) *
    ggE7SylowGen 1 ^ (p.2.1 : ℕ) * ggE7SylowGen 2 ^ (p.2.2.1 : ℕ)) h2 3 (p.2.2.2 : ℕ)
  simpa [mul_assoc] using h3

private lemma ggE7S_set_pow (x : Matrix (Fin 7) (Fin 7) (ZMod 3)) (hx : x ∈ ggE7SylowSet)
    (n : ℕ) : x ^ n ∈ ggE7SylowSet := by
  induction n with
  | zero => simpa using ggE7SylowSet_one_mem
  | succ n ih =>
      have h := ggE7S_set_mul (x ^ n) x ih hx
      simpa [pow_succ] using h

private lemma ggE7S_gen_mem (j : Fin 4) : ggE7SylowGen j ∈ ggE7SylowSet := by
  fin_cases j
  · exact Finset.mem_image.mpr ⟨(1, 0, 0, 0), Finset.mem_univ _, by decide +kernel⟩
  · exact Finset.mem_image.mpr ⟨(0, 1, 0, 0), Finset.mem_univ _, by decide +kernel⟩
  · exact Finset.mem_image.mpr ⟨(0, 0, 1, 0), Finset.mem_univ _, by decide +kernel⟩
  · exact Finset.mem_image.mpr ⟨(0, 0, 0, 1), Finset.mem_univ _, by decide +kernel⟩

private lemma ggE7S_symm_mul_self {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (e : U ≃ₗ[ZMod 3] U) : e.symm * e = 1 := by
  ext v
  rw [LinearEquiv.mul_apply, LinearEquiv.symm_apply_apply]
  rfl

private lemma ggE7S_inv_eq_pow {G : Type*} [Group G] [Finite G] (a : G) :
    a⁻¹ = a ^ (orderOf a - 1) := by
  have h1 : a * a ^ (orderOf a - 1) = 1 := by
    rw [← pow_succ', Nat.sub_add_cancel (Nat.succ_le_of_lt (orderOf_pos a)), pow_orderOf_eq_one]
  exact inv_eq_of_mul_eq_one_right h1

private lemma ggE7S_eichler_pow_three {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {g : V ≃ₗ[ZMod 3] V} (hE : GGEichler g) : g ^ 3 = 1 := by
  have hkey : ∀ v : V, g (g (g v)) = v := by
    intro v
    have h1 := hE.2 (g v)
    have h2 := hE.2 v
    have h3 : g (g v) + g v = -v := by
      rw [eq_neg_iff_add_eq_zero]
      exact h2
    have h1' : g (g (g v)) + (g (g v) + g v) = 0 := by
      simpa [add_assoc] using h1
    rw [h3, add_neg_eq_zero] at h1'
    exact h1'
  ext v
  show (g * g * g) v = v
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hkey]

private lemma ggE7S_toMatrix_refl {U : Type} [AddCommGroup U] [Module (ZMod 3) U]
    (h : Fin 7 → U) (α : Fin 7 → Module.Dual (ZMod 3) U)
    (hb : LinearIndependent (ZMod 3) h)
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (hα : ∀ i, α i (h i) = 2)
    (hαAB : ∀ i j, α i (h j) = ((CartanMatrix.E 7 i j : ℤ) : ZMod 3)) (i : Fin 7) :
    LinearMap.toMatrix (Basis.mk hb hspan.ge) (Basis.mk hb hspan.ge)
      (Module.reflection (hα i) : U →ₗ[ZMod 3] U) = ggE7Refl i := by
  let b : Basis (Fin 7) (ZMod 3) U := Basis.mk hb hspan.ge
  have hbc : ∀ c, b c = h c := fun c => by simp only [b, Module.Basis.mk_apply]
  have hrep : ∀ c, b.repr (b c) = Finsupp.single c 1 := fun c =>
    (Module.Basis.apply_eq_iff (i := c) (x := b c)).mp rfl
  ext a c
  rw [LinearMap.toMatrix_apply, ggE7Refl, Matrix.sub_apply, Matrix.one_apply, Matrix.of_apply]
  rw [show (Module.reflection (hα i) : U →ₗ[ZMod 3] U) (b c) =
      b c - α i (b c) • h i from Module.reflection_apply (h := hα i) (b c)]
  rw [map_sub, map_smul]
  simp only [Finsupp.sub_apply, Finsupp.smul_apply]
  rw [hrep c, show b.repr (h i) = b.repr (b i) from by rw [hbc i], hrep i,
    Finsupp.single_apply, Finsupp.single_apply]
  rw [hbc c, hαAB i c]
  simp only [smul_eq_mul]
  fin_cases a <;> fin_cases c <;> fin_cases i <;> decide +kernel

theorem ggWeylE7NoEichler_holds :
    GGWeylE7NoEichler := by
  classical
  intro U instACG instMod h α hb hspan hαAB g hg hE
  have hFact3 : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hα : ∀ i : Fin 7, α i (h i) = 2 := by
    intro i
    rw [hαAB i i]
    exact ggE7S_diag i
  have hfin : Finite U := by
    have hmod : Module.Finite (ZMod 3) (↥(Submodule.span (ZMod 3) (Set.range h))) :=
      Module.Finite.span_of_finite (ZMod 3) (Set.finite_range h)
    rw [hspan] at hmod
    have htop : Module.Finite (ZMod 3) (↥(⊤ : Submodule (ZMod 3) U)) := hmod
    have hfintop : Finite (↥(⊤ : Submodule (ZMod 3) U)) := Module.finite_of_finite (ZMod 3)
    exact Finite.of_surjective (Subtype.val : ↥(⊤ : Submodule (ZMod 3) U) → U)
      (fun u => ⟨⟨u, Submodule.mem_top⟩, rfl⟩)
  have hFinU : Finite U := hfin
  have hFinGL : Finite (U ≃ₗ[ZMod 3] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod 3] U => (e : U → U))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  let M : CoxeterMatrix (Fin 7) := CoxeterMatrix.E₇
  have hcardM : Nat.card M.Group = 2903040 := by
    change Nat.card (CoxeterMatrix.E₇.Group) = 2903040
    rw [FrameRoute.coxeterE7_eq]
    exact CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.card_weylGroup_E7'
  have hC : GGIntCartan M (CartanMatrix.E 7) := ggIntCartan_E₇
  let r : Fin 7 → (U ≃ₗ[ZMod 3] U) := fun i => Module.reflection (hα i)
  have hL : M.IsLiftable r := isLiftable_reflection_of_intCartan hC h α hα hαAB
  let ρ : M.Group →* (U ≃ₗ[ZMod 3] U) := M.toCoxeterSystem.lift ⟨r, hL⟩
  let W : Subgroup (U ≃ₗ[ZMod 3] U) := ggQ2WeylOf h α
  have hgen : Set.range r = {t | ∃ j, ∀ v, t v = v - α j v • h j} := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨i, fun v => Module.reflection_apply (h := hα i) v⟩
    · rintro ⟨j, hj⟩
      exact ⟨j, LinearEquiv.ext fun v => by rw [hj v, Module.reflection_apply]⟩
  have hρrange : ρ.range = W := by
    have hrange : ρ.range = Subgroup.closure (Set.range r) := by
      apply le_antisymm
      · intro x hx
        rw [MonoidHom.mem_range] at hx
        obtain ⟨y, rfl⟩ := hx
        have hy : y ∈ Subgroup.closure (Set.range M.toCoxeterSystem.simple) := by
          rw [CoxeterSystem.subgroup_closure_range_simple]
          trivial
        refine Subgroup.closure_induction
          (p := fun y _ => ρ y ∈ Subgroup.closure (Set.range r)) ?_ ?_ ?_ ?_ hy
        · rintro z ⟨i, rfl⟩
          rw [CoxeterSystem.lift_apply_simple]
          exact Subgroup.subset_closure ⟨i, rfl⟩
        · rw [map_one]
          exact Subgroup.one_mem _
        · intro a b _ _ ha hb
          rw [map_mul]
          exact Subgroup.mul_mem _ ha hb
        · intro a _ ha
          rw [map_inv]
          exact Subgroup.inv_mem _ ha
      · refine (Subgroup.closure_le (k := Set.range r) (K := ρ.range)).mpr ?_
        rintro _ ⟨i, rfl⟩
        exact ⟨M.toCoxeterSystem.simple i, by rw [CoxeterSystem.lift_apply_simple]⟩
    rw [hrange]
    show Subgroup.closure (Set.range r) = ggQ2WeylOf h α
    rw [ggQ2WeylOf, hgen]
  have hdvd : Nat.card W ∣ 2903040 := by
    rw [← hρrange]
    have := Subgroup.card_range_dvd ρ
    rwa [hcardM] at this
  let w0 : U ≃ₗ[ZMod 3] U := (([0, 2] : List (Fin 7)).map r).prod
  let w1 : U ≃ₗ[ZMod 3] U := (([5, 4] : List (Fin 7)).map r).prod
  let w2 : U ≃ₗ[ZMod 3] U :=
    (([1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3] : List (Fin 7)).map r).prod
  let w3 : U ≃ₗ[ZMod 3] U :=
    (([0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5] : List (Fin 7)).map r).prod
  let b : Basis (Fin 7) (ZMod 3) U := Basis.mk hb hspan.ge
  let Φ : (U ≃ₗ[ZMod 3] U) →* Matrix (Fin 7) (Fin 7) (ZMod 3) :=
    { toFun := fun e => LinearMap.toMatrix b b (e : U →ₗ[ZMod 3] U)
      map_one' := by
        rw [LinearEquiv.coe_toLinearMap_one, LinearMap.toMatrix_id]
      map_mul' := fun e₁ e₂ => by
        rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul] }
  have hΦcoe : ∀ e : U ≃ₗ[ZMod 3] U,
      Φ e = LinearMap.toMatrix b b (e : U →ₗ[ZMod 3] U) := fun _ => rfl
  have hΦcoe' : ∀ e : U ≃ₗ[ZMod 3] U,
      Φ e = LinearMap.toMatrixAlgEquiv b (e : U →ₗ[ZMod 3] U) := fun _ => rfl
  have hΦinj : Function.Injective Φ := by
    intro x y hxy
    apply LinearEquiv.ext
    intro v
    have h2 : (x : U →ₗ[ZMod 3] U) = (y : U →ₗ[ZMod 3] U) := by
      have hxy' : LinearMap.toMatrix b b (x : U →ₗ[ZMod 3] U) =
          LinearMap.toMatrix b b (y : U →ₗ[ZMod 3] U) := by
        simpa only [hΦcoe] using hxy
      have h' := congrArg (Matrix.toLin b b) hxy'
      rwa [Matrix.toLin_toMatrix, Matrix.toLin_toMatrix] at h'
    exact congrArg (fun f : U →ₗ[ZMod 3] U => f v) h2
  have hΦr : ∀ i : Fin 7, Φ (r i) = ggE7Refl i := fun i =>
    ggE7S_toMatrix_refl h α hb hspan hα hαAB i
  have hΦlist : ∀ l : List (Fin 7), Φ ((l.map r).prod) = (l.map ggE7Refl).prod := by
    intro l
    induction l with
    | nil => simp
    | cons a t ih =>
        simp only [List.map_cons, List.prod_cons, MonoidHom.map_mul, ih, hΦr a]
  have hΦw0 : Φ w0 = ggE7SylowGen 0 := by
    change Φ ((([0, 2] : List (Fin 7)).map r).prod) = ggE7Prod [0, 2]
    rw [hΦlist, ggE7Prod]
  have hΦw1 : Φ w1 = ggE7SylowGen 1 := by
    change Φ ((([5, 4] : List (Fin 7)).map r).prod) = ggE7Prod [5, 4]
    rw [hΦlist, ggE7Prod]
  have hΦw2 : Φ w2 = ggE7SylowGen 2 := by
    change Φ ((([1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3] :
      List (Fin 7)).map r).prod) =
      ggE7Prod [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3]
    rw [hΦlist, ggE7Prod]
  have hΦw3 : Φ w3 = ggE7SylowGen 3 := by
    change Φ ((([0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5] : List (Fin 7)).map r).prod) =
      ggE7Prod [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]
    rw [hΦlist, ggE7Prod]
  let S : Subgroup (U ≃ₗ[ZMod 3] U) := Subgroup.closure ({w0, w1, w2, w3} : Set (U ≃ₗ[ZMod 3] U))
  have hw0 : w0 ∈ S := Subgroup.subset_closure (by simp)
  have hw1 : w1 ∈ S := Subgroup.subset_closure (by simp)
  have hw2 : w2 ∈ S := Subgroup.subset_closure (by simp)
  have hw3 : w3 ∈ S := Subgroup.subset_closure (by simp)
  have hmem : ∀ x ∈ S, Φ x ∈ ggE7SylowSet := by
    intro x hx
    refine Subgroup.closure_induction (p := fun x _ => Φ x ∈ ggE7SylowSet) ?_ ?_ ?_ ?_ hx
    · intro y hy
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
      rcases hy with rfl | rfl | rfl | rfl
      · rw [hΦw0]; exact ggE7S_gen_mem 0
      · rw [hΦw1]; exact ggE7S_gen_mem 1
      · rw [hΦw2]; exact ggE7S_gen_mem 2
      · rw [hΦw3]; exact ggE7S_gen_mem 3
    · rw [map_one]; exact ggE7SylowSet_one_mem
    · intro y z _ _ hy hz
      rw [map_mul]
      exact ggE7S_set_mul _ _ hy hz
    · intro y _ hy
      rw [ggE7S_inv_eq_pow y, map_pow]
      exact ggE7S_set_pow _ hy (orderOf y - 1)
  have hcover : ∀ z ∈ ggE7SylowSet, ∃ x ∈ S, Φ x = z := by
    intro z hz
    rw [ggE7SylowSet, Finset.mem_image] at hz
    obtain ⟨p, -, rfl⟩ := hz
    refine ⟨w0 ^ (p.1 : ℕ) * w1 ^ (p.2.1 : ℕ) * w2 ^ (p.2.2.1 : ℕ) * w3 ^ (p.2.2.2 : ℕ), ?_, ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
        (Subgroup.pow_mem _ hw0 _) (Subgroup.pow_mem _ hw1 _))
        (Subgroup.pow_mem _ hw2 _)) (Subgroup.pow_mem _ hw3 _)
    · simp only [map_mul, map_pow, hΦw0, hΦw1, hΦw2, hΦw3]
  have hcardS : Nat.card S = 81 := by
    have hbij : Function.Bijective
        (fun x : S => (⟨Φ x, hmem x x.2⟩ : {z // z ∈ ggE7SylowSet})) := by
      constructor
      · intro x y hxy
        apply Subtype.ext
        apply hΦinj
        exact congrArg Subtype.val hxy
      · intro z
        obtain ⟨x, hx, hxe⟩ := hcover z z.2
        exact ⟨⟨x, hx⟩, Subtype.ext hxe⟩
    have h1 : Nat.card S = Nat.card {z : Matrix (Fin 7) (Fin 7) (ZMod 3) //
        z ∈ ggE7SylowSet} := Nat.card_congr (Equiv.ofBijective _ hbij)
    have h2 : Nat.card {z : Matrix (Fin 7) (Fin 7) (ZMod 3) // z ∈ ggE7SylowSet} = 81 := by
      rw [Nat.card_eq_fintype_card]
      exact (Fintype.card_coe ggE7SylowSet).trans ggE7SylowSet_card
    rw [h1, h2]
  have hr : ∀ i : Fin 7, r i ∈ W := by
    intro i
    dsimp only [W, ggQ2WeylOf]
    exact Subgroup.subset_closure ⟨i, fun v => Module.reflection_apply (h := hα i) v⟩
  have hlist : ∀ l : List (Fin 7), (l.map r).prod ∈ W := by
    intro l
    refine Subgroup.list_prod_mem (K := W) (l := l.map r) ?_
    intro x hx
    obtain ⟨i, -, rfl⟩ := List.mem_map.mp hx
    exact hr i
  have hw0W : w0 ∈ W := by simpa only [w0] using hlist [0, 2]
  have hw1W : w1 ∈ W := by simpa only [w1] using hlist [5, 4]
  have hw2W : w2 ∈ W := by
    simpa only [w2] using hlist [1, 3, 2, 0, 4, 3, 1, 2, 3, 4, 5, 4, 3, 2, 1, 3, 4, 0, 2, 3]
  have hw3W : w3 ∈ W := by
    simpa only [w3] using hlist [0, 2, 3, 4, 5, 1, 3, 4, 2, 3, 0, 2, 1, 3, 4, 5]
  have hSW : S ≤ W := by
    dsimp only [S]
    refine (Subgroup.closure_le (k := ({w0, w1, w2, w3} : Set (U ≃ₗ[ZMod 3] U)))
      (K := W)).mpr ?_
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl
    · exact hw0W
    · exact hw1W
    · exact hw2W
    · exact hw3W
  have hFinW : Finite W :=
    Finite.of_injective (fun x : W => (x : U ≃ₗ[ZMod 3] U)) Subtype.coe_injective
  have hFinSyl : Finite (Sylow 3 W) :=
    Finite.of_injective (fun P : Sylow 3 W => (P : Subgroup W))
      (fun _ _ h => Sylow.ext h)
  have h81 : 3 ^ 4 ∣ Nat.card W := by
    have h := Subgroup.card_dvd_of_le hSW
    rw [hcardS] at h
    norm_num at h ⊢
    exact h
  let SW : Subgroup W := S.subgroupOf W
  have hcardSW : Nat.card SW = 81 := by
    have h1 : Nat.card SW = Nat.card S := Nat.card_congr
      { toFun := fun x => ⟨(x : W), Subgroup.mem_subgroupOf.mp x.2⟩
        invFun := fun s => ⟨⟨s, hSW s.2⟩, Subgroup.mem_subgroupOf.mpr s.2⟩
        left_inv := fun x => by ext; rfl
        right_inv := fun s => by ext; rfl }
    rw [h1, hcardS]
  have hfac : (Nat.card W).factorization 3 = 4 := by
    have hWpos : Nat.card W ≠ 0 := Nat.card_pos.ne'
    have hle : (Nat.card W).factorization 3 ≤ 4 := by
      by_contra h
      have h5 : 5 ≤ (Nat.card W).factorization 3 := by omega
      have hdvd5 : 3 ^ 5 ∣ Nat.card W :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hWpos).mpr h5
      exact (by norm_num : ¬ 3 ^ 5 ∣ 2903040) (hdvd5.trans hdvd)
    have hge : 4 ≤ (Nat.card W).factorization 3 :=
      (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hWpos).mp h81
    omega
  have hcardEq : Nat.card SW = 3 ^ (Nat.card W).factorization 3 := by
    rw [hcardSW, hfac]
    norm_num
  let hSylow : Sylow 3 W := Sylow.ofCard SW hcardEq
  have hSWcoe : (hSylow : Subgroup W) = SW := by
    change (Sylow.ofCard SW hcardEq : Subgroup W) = SW
    exact Sylow.coe_ofCard SW hcardEq
  let gW : W := ⟨g, hg⟩
  have hg3 : g ^ 3 = 1 := ggE7S_eichler_pow_three hE
  have hgW3 : gW ^ 3 = 1 := by
    apply Subtype.ext
    change g ^ 3 = 1
    exact hg3
  have hgWne : gW ≠ 1 := by
    intro h
    exact hE.1 (Subtype.ext_iff.mp h)
  have horder : orderOf gW = 3 :=
    (orderOf_eq_prime_iff).mpr ⟨hgW3, hgWne⟩
  have hP3 : IsPGroup 3 (Subgroup.zpowers gW) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, horder]
    norm_num
  obtain ⟨P, hgP⟩ := IsPGroup.exists_le_sylow hP3
  have hPre : MulAction.IsPretransitive W (Sylow 3 W) := Sylow.isPretransitive_of_finite
  obtain ⟨k, hk⟩ := MulAction.IsPretransitive.exists_smul_eq (M := W) P hSylow
  have hgWP : gW ∈ P := hgP (Subgroup.mem_zpowers gW)
  let gW' : W := k * gW * k⁻¹
  have hgW'S : gW' ∈ (hSylow : Subgroup W) := by
    rw [← hk]
    change gW' ∈ (MulAut.conj k) '' (P : Set W)
    exact ⟨gW, hgWP, MulAut.conj_apply k gW⟩
  have hgW'S_sub : (gW' : U ≃ₗ[ZMod 3] U) ∈ S := by
    have h1 : gW' ∈ SW := by rwa [hSWcoe] at hgW'S
    exact Subgroup.mem_subgroupOf.mp h1
  have hgW'ne : gW' ≠ 1 := by
    intro h
    apply hgWne
    have := congrArg (fun x : W => k⁻¹ * x * k) h
    simpa [gW', mul_assoc] using this
  have hΦne : Φ (gW' : U ≃ₗ[ZMod 3] U) ≠ 1 := by
    intro h
    refine hgW'ne (Subtype.ext (hΦinj ?_))
    rw [h]
    exact (map_one Φ).symm
  have hconjE : GGEichler ((k : U ≃ₗ[ZMod 3] U) * g * (k : U ≃ₗ[ZMod 3] U).symm) := by
    constructor
    · intro h
      apply hE.1
      have h1 : (k : U ≃ₗ[ZMod 3] U) * g = (k : U ≃ₗ[ZMod 3] U) := by
        have := congrArg (fun x => x * (k : U ≃ₗ[ZMod 3] U)) h
        rw [mul_assoc, ggE7S_symm_mul_self, mul_one, one_mul] at this
        exact this
      exact mul_left_cancel
        (show (k : U ≃ₗ[ZMod 3] U) * g = (k : U ≃ₗ[ZMod 3] U) * 1 by simpa using h1)
    · intro v
      have hk2 := hE.2 ((k : U ≃ₗ[ZMod 3] U).symm v)
      have := congrArg (fun w => (k : U ≃ₗ[ZMod 3] U) w) hk2
      simpa [LinearEquiv.mul_apply, map_add, LinearEquiv.apply_symm_apply, mul_assoc] using this
  have hgW'coe : (gW' : U ≃ₗ[ZMod 3] U) =
      (k : U ≃ₗ[ZMod 3] U) * g * (k : U ≃ₗ[ZMod 3] U).symm := by
    dsimp only [gW', gW]
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    rfl
  have hgE' : GGEichler (gW' : U ≃ₗ[ZMod 3] U) := hgW'coe.symm ▸ hconjE
  have hlin : (gW' : U →ₗ[ZMod 3] U) * (gW' : U →ₗ[ZMod 3] U) +
      (gW' : U →ₗ[ZMod 3] U) + 1 = 0 := by
    ext v
    simpa [Module.End.coe_mul, LinearMap.add_apply, LinearMap.id_apply] using hgE'.2 v
  have hmat : Φ (gW' : U ≃ₗ[ZMod 3] U) * Φ (gW' : U ≃ₗ[ZMod 3] U) +
      Φ (gW' : U ≃ₗ[ZMod 3] U) + 1 = 0 := by
    apply (Matrix.toLinAlgEquiv b).injective
    simpa only [map_add, map_mul, map_one, map_zero, hΦcoe',
      Matrix.toLinAlgEquiv_toMatrixAlgEquiv] using hlin
  exact (ggE7SylowSet_noEichler (Φ (gW' : U ≃ₗ[ZMod 3] U))
    (hmem _ hgW'S_sub) hΦne) hmat

end CFSG.StandardType

end
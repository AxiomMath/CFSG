module

public import CFSG.LocalAnalysis.StandardType.GGInterfaceDefs
public import CFSG.LieType.Steinberg.PartB

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Steinberg

namespace PsiDiag

theorem prod_zpow_eq_zpow_sum {M : Type*} [CommGroup M] {ι : Type*} (s : Finset ι) (a : M)
    (f : ι → ℤ) : ∏ i ∈ s, a ^ f i = a ^ ∑ i ∈ s, f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih => rw [Finset.prod_insert hj, Finset.sum_insert hj, ih, zpow_add]

theorem pow_two_pow_injective {k : Type*} [Field k] [CharP k 2] (a : ℕ) :
    Function.Injective fun t : kˣ => t ^ (2 ^ a) := by
  induction a with
  | zero => intro s t h; simpa using h
  | succ a ih =>
    intro s t h
    apply ih
    apply Units.ext
    apply CharTwo.sq_injective (R := k)
    have h1 : ((s ^ 2 ^ (a + 1) : kˣ) : k) = ((t ^ 2 ^ (a + 1) : kˣ) : k) := congrArg Units.val h
    show ((s ^ 2 ^ a : kˣ) : k) ^ 2 = ((t ^ 2 ^ a : kˣ) : k) ^ 2
    simp only [Units.val_pow_eq_pow_val] at h1 ⊢
    rw [← pow_mul, ← pow_mul, ← pow_succ]
    exact h1

theorem exists_prod_zpow_cartan_eq {k : Type*} [Field k] [Finite k] [CharP k 2] {I : Type*}
    [Fintype I] [DecidableEq I] (A : Matrix I I ℤ) {a : ℕ} (hdet : A.det = 2 ^ a) (e : I → kˣ) :
    ∃ s : I → kˣ, ∀ j, ∏ i, s i ^ A i j = e j := by
  have hinj := pow_two_pow_injective (k := k) a
  have hsurj : Function.Surjective fun t : kˣ => t ^ (2 ^ a) :=
    Finite.injective_iff_surjective.mp hinj
  choose ρ hρ using hsurj
  have hρ' : ∀ b, ρ b ^ 2 ^ a = b := hρ
  obtain ⟨B, hBA⟩ : ∃ B : Matrix I I ℤ, B * A = A.det • (1 : Matrix I I ℤ) :=
    ⟨_, Matrix.adjugate_mul A⟩
  refine ⟨fun i => ρ (∏ l, e l ^ B l i), fun j => hinj ?_⟩
  show (∏ i, ρ (∏ l, e l ^ B l i) ^ A i j) ^ 2 ^ a = e j ^ 2 ^ a
  have hN : ((2 ^ a : ℕ) : ℤ) = A.det := by rw [hdet]; push_cast; rfl
  rw [← zpow_natCast, ← Finset.prod_zpow]
  have h1 : ∀ i, (ρ (∏ l, e l ^ B l i) ^ A i j) ^ ((2 ^ a : ℕ) : ℤ) =
      ∏ l, e l ^ (B l i * A i j) := by
    intro i
    rw [← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hρ', ← Finset.prod_zpow]
    refine Finset.prod_congr rfl fun l _ => ?_
    rw [← zpow_mul]
  rw [Finset.prod_congr rfl fun i _ => h1 i, Finset.prod_comm]
  have h2 : ∀ l, ∏ i, e l ^ (B l i * A i j) = e l ^ (A.det * (1 : Matrix I I ℤ) l j) := by
    intro l
    rw [prod_zpow_eq_zpow_sum]
    congr 1
    have := congrFun (congrFun hBA l) j
    rw [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul] at this
    exact this
  rw [Finset.prod_congr rfl fun l _ => h2 l, ← zpow_natCast, hN]
  rw [Finset.prod_eq_single j]
  · rw [Matrix.one_apply_eq, mul_one]
  · intro l _ hl
    rw [Matrix.one_apply_ne hl, mul_zero, zpow_zero]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

variable {K : Type*} [Group K] {D : UniversalRootDatum K} {k : Type*} [Field k]
  {x : (Fin D.rank → ℤ) → k → K}
  {C : (Fin D.rank → ℤ) → (Fin D.rank → ℤ) → ℕ × ℕ → ℤ}
  {O : CommOrder (CFSG.LieType.Steinberg.RootSystem.ofCartan D.isFiniteType D.divisible)}

theorem reflection_mem_roots (i : Fin D.rank) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    reflection D.cartan i γ ∈ D.roots := by
  have h := weylAction_mem_roots D.isFiniteType
    ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) hγ
  rwa [weylAction_simple] at h

theorem weyl_one (hE : ChevalleyExtras D k x C O) (i : Fin D.rank) {β : Fin D.rank → ℤ}
    (hβ : β ∈ D.roots) :
    ∃ ε : k, ε * ε = 1 ∧ ∀ u : k,
      weylElement x i 1 * x β u * (weylElement x i 1)⁻¹ = x (reflection D.cartan i β) (ε * u) := by
  obtain ⟨ε, hε, hw⟩ := hE.weyl i β hβ
  refine ⟨ε, by rcases hε with rfl | rfl <;> norm_num, fun u => ?_⟩
  rw [hw 1 u, one_zpow, Units.val_one, mul_one]

@[expose] noncomputable def torusElt (x : (Fin D.rank → ℤ) → k → K) (i : Fin D.rank) (s : kˣ) : K :=
  weylElement x i s * (weylElement x i 1)⁻¹

theorem torusElt_conj (hE : ChevalleyExtras D k x C O) (i : Fin D.rank) (s : kˣ)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (v : k) :
    torusElt x i s * x γ v * (torusElt x i s)⁻¹ =
      x γ (((s ^ coroot D.cartan i γ : kˣ) : k) * v) := by
  have hii : D.cartan i i = 2 := D.isFiniteType.apply_self i
  set β := reflection D.cartan i γ with hβdef
  have hβ : β ∈ D.roots := reflection_mem_roots i hγ
  have hββ : reflection D.cartan i β = γ := by
    rw [hβdef, ← Module.End.mul_apply, reflection_mul_self hii, Module.End.one_apply]
  have hcor : coroot D.cartan i β = -coroot D.cartan i γ := coroot_reflection hii γ
  obtain ⟨ε, hε, hw⟩ := hE.weyl i β hβ
  rw [hββ] at hw
  have hεε : (ε : k) * ε = 1 := by rcases hε with rfl | rfl <;> norm_num
  have h1 : (weylElement x i 1)⁻¹ * x γ v * weylElement x i 1 = x β (ε * v) := by
    have h := hw 1 (ε * v)
    rw [one_zpow, Units.val_one, mul_one, ← mul_assoc, hεε, one_mul] at h
    rw [← h]
    group
  calc torusElt x i s * x γ v * (torusElt x i s)⁻¹
      = weylElement x i s * ((weylElement x i 1)⁻¹ * x γ v * weylElement x i 1) *
          (weylElement x i s)⁻¹ := by
        simp only [torusElt]
        group
    _ = weylElement x i s * x β (ε * v) * (weylElement x i s)⁻¹ := by rw [h1]
    _ = x γ ((ε : k) * ((s ^ (-(∑ j, D.cartan i j * β j)) : kˣ) : k) * (ε * v)) := hw s _
    _ = x γ (((s ^ coroot D.cartan i γ : kˣ) : k) * v) := by
        rw [← coroot_apply, hcor, neg_neg]
        congr 1
        linear_combination (((s ^ coroot D.cartan i γ : kˣ) : k) * v) * hεε

theorem list_prod_conj {ι : Type*} (L : List ι) (f : ι → K) (g : ι → kˣ) (γ : Fin D.rank → ℤ)
    (hf : ∀ i ∈ L, ∀ v, f i * x γ v * (f i)⁻¹ = x γ ((g i : k) * v)) (v : k) :
    (L.map f).prod * x γ v * ((L.map f).prod)⁻¹ = x γ ((((L.map g).prod : kˣ) : k) * v) := by
  induction L generalizing v with
  | nil => simp
  | cons a L ih =>
    have ih' := ih (fun i hi => hf i (List.mem_cons_of_mem a hi))
    simp only [List.map_cons, List.prod_cons, mul_inv_rev, Units.val_mul]
    calc f a * (L.map f).prod * x γ v * (((L.map f).prod)⁻¹ * (f a)⁻¹)
        = f a * ((L.map f).prod * x γ v * ((L.map f).prod)⁻¹) * (f a)⁻¹ := by group
      _ = f a * x γ ((((L.map g).prod : kˣ) : k) * v) * (f a)⁻¹ := by rw [ih']
      _ = x γ ((g a : k) * ((((L.map g).prod : kˣ) : k) * v)) := hf a List.mem_cons_self _
      _ = x γ ((g a : k) * (((L.map g).prod : kˣ) : k) * v) := by rw [mul_assoc]

@[expose] noncomputable def torusProd (x : (Fin D.rank → ℤ) → k → K) (s : Fin D.rank → kˣ) : K :=
  ((List.finRange D.rank).map fun i => torusElt x i (s i)).prod

theorem torusProd_conj (hE : ChevalleyExtras D k x C O) (s : Fin D.rank → kˣ)
    {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) (v : k) :
    torusProd x s * x γ v * (torusProd x s)⁻¹ =
      x γ (((∏ i, s i ^ coroot D.cartan i γ : kˣ) : k) * v) := by
  rw [Fin.prod_univ_def]
  exact list_prod_conj _ _ (fun i => s i ^ coroot D.cartan i γ) γ
    (fun i _ v => torusElt_conj hE i (s i) hγ v) v

theorem inv_conj_of_conj {t : K} {γ : Fin D.rank → ℤ} {ν : kˣ}
    (h : ∀ v, t * x γ v * t⁻¹ = x γ ((ν : k) * v)) (v : k) :
    t⁻¹ * x γ v * t = x γ (((ν⁻¹ : kˣ) : k) * v) := by
  have h1 := h (((ν⁻¹ : kˣ) : k) * v)
  rw [← mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_mul] at h1
  rw [← h1]
  group

theorem coe_sl2Upper (c : k) : ((sl2Upper c : Matrix.SpecialLinearGroup (Fin 2) k) :
    Matrix (Fin 2) (Fin 2) k) = !![1, c; 0, 1] := rfl

theorem coe_sl2Lower (c : k) : ((sl2Lower c : Matrix.SpecialLinearGroup (Fin 2) k) :
    Matrix (Fin 2) (Fin 2) k) = !![1, 0; c, 1] := rfl

theorem sl2_eq_one_of_mem_center [CharP k 2] {M : Matrix.SpecialLinearGroup (Fin 2) k}
    (hM : M ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) k)) : M = 1 := by
  obtain ⟨r, hr, hrM⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hM
  rw [Fintype.card_fin] at hr
  have h1 : r = 1 := CharTwo.sq_injective (by simpa using hr)
  apply Subtype.ext
  rw [← hrM, h1, map_one, Matrix.SpecialLinearGroup.coe_one]

theorem injective_comp_of_ker_le_center [CharP k 2] {G : Type*} [Group G]
    (φ : Matrix.SpecialLinearGroup (Fin 2) k →* K) (hφ : Function.Injective φ) (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) : Function.Injective (ψ.comp φ) := by
  rw [injective_iff_map_eq_one]
  intro M hM
  have hc : φ M ∈ Subgroup.center K := hker (by simpa [MonoidHom.mem_ker] using hM)
  apply sl2_eq_one_of_mem_center
  rw [Subgroup.mem_center_iff]
  intro N
  apply hφ
  rw [map_mul, map_mul]
  exact Subgroup.mem_center_iff.mp hc (φ N)

theorem eq_one_of_conj_sl2 {G : Type*} [Group G] (Φ : Matrix.SpecialLinearGroup (Fin 2) k →* G)
    (hΦ : Function.Injective Φ) {d : G} {e : k}
    (hu : ∀ c, d⁻¹ * Φ (sl2Upper c) * d = Φ (sl2Upper c))
    (hl : ∀ c, d⁻¹ * Φ (sl2Lower c) * d = Φ (sl2Lower (e * c))) : e = 1 := by
  let Φ' : Matrix.SpecialLinearGroup (Fin 2) k →* G := (MulAut.conj d⁻¹).toMonoidHom.comp Φ
  have hΦ' : ∀ M, Φ' M = d⁻¹ * Φ M * d := fun M => by simp [Φ']
  have hU : Φ' (sl2Upper 1) = Φ (sl2Upper 1) := (hΦ' _).trans (hu 1)
  have hL : Φ' (sl2Lower (-1)) = Φ (sl2Lower (-e)) := (hΦ' _).trans (by rw [hl, mul_neg_one])
  have hw : sl2Upper (1 : k) * sl2Lower (-1) * sl2Upper 1 * sl2Upper 1 =
      sl2Lower (-1) * (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1) := by
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower, Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp
  have h1 : Φ (sl2Upper 1 * sl2Lower (-e) * sl2Upper 1 * sl2Upper 1) =
      Φ (sl2Lower (-e) * (sl2Upper 1 * sl2Lower (-e) * sl2Upper 1)) := by
    have h := congrArg Φ' hw
    simp only [map_mul, hU, hL] at h
    simpa only [map_mul] using h
  have h2 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
    (M : Matrix (Fin 2) (Fin 2) k) 0 1) (hΦ h1)
  simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower,
    Matrix.mul_fin_two] at h2
  simp at h2
  linear_combination -h2

theorem eq_of_conj_sl2 {G : Type*} [Group G] (Φ : Matrix.SpecialLinearGroup (Fin 2) k →* G)
    (hΦ : Function.Injective Φ) {d : G} {φ : k → k}
    (hu : ∀ c, d⁻¹ * Φ (sl2Upper c) * d = Φ (sl2Upper c))
    (hl : ∀ c, d⁻¹ * Φ (sl2Lower c) * d = Φ (sl2Lower (φ c))) (c : k) : φ c = c := by
  let Φ' : Matrix.SpecialLinearGroup (Fin 2) k →* G := (MulAut.conj d⁻¹).toMonoidHom.comp Φ
  have hΦ' : ∀ M, Φ' M = d⁻¹ * Φ M * d := fun M => by simp [Φ']
  have hw : ∀ c : k, sl2Upper (1 : k) * sl2Lower (-1) * sl2Upper 1 * sl2Upper c =
      sl2Lower (-c) * (sl2Upper 1 * sl2Lower (-1) * sl2Upper 1) := by
    intro c
    ext i j
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower, Matrix.mul_fin_two]
    fin_cases i <;> fin_cases j <;> simp
  have hU' : ∀ c, Φ' (sl2Upper c) = Φ (sl2Upper c) := fun c => (hΦ' _).trans (hu c)
  have hL' : ∀ c, Φ' (sl2Lower c) = Φ (sl2Lower (φ c)) := fun c => (hΦ' _).trans (hl c)
  have key : ∀ c : k, sl2Upper (1 : k) * sl2Lower (φ (-1)) * sl2Upper 1 * sl2Upper c =
      sl2Lower (φ (-c)) * (sl2Upper 1 * sl2Lower (φ (-1)) * sl2Upper 1) := by
    intro c
    apply hΦ
    have h := congrArg Φ' (hw c)
    simp only [map_mul, hU', hL'] at h
    simpa only [map_mul] using h
  have h1 : φ (-1) = -1 := by
    have h2 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
      (M : Matrix (Fin 2) (Fin 2) k) 0 1) (key 1)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower,
      Matrix.mul_fin_two] at h2
    simp at h2
    linear_combination h2
  have h2 : ∀ c : k, φ (-c) = -c := by
    intro c
    have h3 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
      (M : Matrix (Fin 2) (Fin 2) k) 1 1) (key c)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_sl2Upper, coe_sl2Lower,
      Matrix.mul_fin_two, h1] at h3
    simp at h3
    linear_combination -h3
  simpa using h2 (-c)

theorem conj_eq_iff {G : Type*} [Group G] {d y : G} : d⁻¹ * y * d = y ↔ y * d = d * y := by
  constructor
  · intro h
    calc y * d = d * (d⁻¹ * y * d) := by group
      _ = d * y := by rw [h]
  · intro h
    rw [mul_assoc, h]
    group

theorem mem_fix_iff {G : Type*} [Group G] (ψ : K →* G) {d : G} {z : K} :
    z ∈ (Subgroup.centralizer ({d} : Set G)).comap ψ ↔ d⁻¹ * ψ z * d = ψ z := by
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, conj_eq_iff]

theorem fix_weylAction (hE : ChevalleyExtras D k x C O) {G : Type*} [Group G] (ψ : K →* G)
    {d : G} (hpos : ∀ i c, d⁻¹ * ψ (x (Pi.single i 1) c) * d = ψ (x (Pi.single i 1) c))
    (hneg : ∀ i c, d⁻¹ * ψ (x (-Pi.single i 1) c) * d = ψ (x (-Pi.single i 1) c))
    (ω : List (Fin D.rank)) (j : Fin D.rank) (v : k) :
    x (weylAction D.isFiniteType ((coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd ω)
      (Pi.single j 1)) v ∈ (Subgroup.centralizer ({d} : Set G)).comap ψ := by
  induction ω generalizing v with
  | nil =>
    rw [mem_fix_iff]
    simpa using hpos j v
  | cons i ω ih =>
    set γ' := weylAction D.isFiniteType
      ((coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd ω) (Pi.single j 1) with hγ'
    have hγ'r : γ' ∈ D.roots := Set.mem_union_left _ ⟨_, j, rfl⟩
    rw [CoxeterSystem.wordProd_cons, weylAction_mul_apply, weylAction_simple, ← hγ']
    obtain ⟨ε, hε, hw⟩ := weyl_one hE i hγ'r
    have hx : x (reflection D.cartan i γ') v =
        weylElement x i 1 * x γ' (ε * v) * (weylElement x i 1)⁻¹ := by
      rw [hw, ← mul_assoc, hε, one_mul]
    have hW : weylElement x i 1 ∈ (Subgroup.centralizer ({d} : Set G)).comap ψ := by
      refine mul_mem (mul_mem ?_ ?_) ?_
      · exact (mem_fix_iff ψ).mpr (hpos i _)
      · exact (mem_fix_iff ψ).mpr (hneg i _)
      · exact (mem_fix_iff ψ).mpr (hpos i _)
    rw [hx]
    exact mul_mem (mul_mem hW (ih _)) (inv_mem hW)

theorem conj_eq_of_affine {k A : Type*} [Field k] [Ring A] [Algebra k A] (ι : K →* A)
    (hι : Function.Injective ι) {X : Subgroup K} {y : k → K} (hX : ∀ g, g ∈ X ↔ ∃ c, y c = g)
    {N : A} (hN : ∀ c, ι (y c) = 1 + c • N) {h : K}
    (hh : h ∈ Subgroup.normalizer (X : Set K)) :
    ∃ χ : k, ∀ c, h * y c * h⁻¹ = y (χ * c) := by
  obtain ⟨χ, hχ⟩ := (hX _).mp ((Subgroup.mem_normalizer_iff.mp hh _).mp ((hX _).mpr ⟨1, rfl⟩))
  have hHH : ι h * ι h⁻¹ = 1 := by rw [← map_mul, mul_inv_cancel, map_one]
  have hE : ι h * N * ι h⁻¹ = χ • N := by
    have h1 := congrArg ι hχ
    rw [map_mul, map_mul, hN, hN, one_smul, mul_add, add_mul, mul_one, hHH] at h1
    exact add_left_cancel h1.symm
  refine ⟨χ, fun c => hι ?_⟩
  rw [map_mul, map_mul, hN, hN, mul_add, add_mul, mul_one, hHH, mul_smul_comm, smul_mul_assoc, hE,
    smul_smul, mul_comm]

theorem exists_mul_psi_mem_centralizer (hE : ChevalleyExtras D k x C O) [Finite k] [CharP k 2]
    (hdiv : D.divisible = ∅) (hgen : ⨆ γ ∈ D.roots, D.rootGroup γ = ⊤) {a : ℕ}
    (hdet : D.cartan.det = 2 ^ a) {G : Type*} [Group G] (ψ : K →* G)
    (hker : ψ.ker ≤ Subgroup.center K) {d : G}
    (hpos : ∀ i, ∃ χ : k, ∀ c,
      d⁻¹ * ψ (x (Pi.single i 1) c) * d = ψ (x (Pi.single i 1) (χ * c)))
    (hneg : ∀ i, ∃ φ : k → k, ∀ c,
      d⁻¹ * ψ (x (-Pi.single i 1) c) * d = ψ (x (-Pi.single i 1) (φ c))) :
    ∃ u : K, d * ψ u ∈ Subgroup.centralizer (ψ.range : Set G) := by
  choose χ hχ using hpos
  choose χ' hχ' using hneg
  choose φ hφinj hφu hφl using hE.rankOne
  have hΦ : ∀ i, Function.Injective (ψ.comp (φ i)) := fun i =>
    injective_comp_of_ker_le_center (φ i) (hφinj i) ψ hker
  have hx0 : ∀ γ ∈ D.roots, x γ 0 = 1 := by
    intro γ hγ
    have h := (hE.param γ hγ).2.1 0 0
    rw [add_zero] at h
    exact left_eq_mul.mp h
  have hχ0 : ∀ i, χ i ≠ 0 := by
    intro i h0
    have h := hχ i 1
    rw [h0, zero_mul, hx0 _ (single_mem_roots i), map_one] at h
    have h' : ψ (x (Pi.single i 1) 1) = 1 := by
      calc ψ (x (Pi.single i 1) 1) = d * (d⁻¹ * ψ (x (Pi.single i 1) 1) * d) * d⁻¹ := by group
        _ = 1 := by rw [h]; group
    have h'' : (ψ.comp (φ i)) (sl2Upper 1) = (ψ.comp (φ i)) 1 := by
      rw [MonoidHom.comp_apply, hφu, h', map_one]
    have h3 := congrArg (fun M : Matrix.SpecialLinearGroup (Fin 2) k =>
      (M : Matrix (Fin 2) (Fin 2) k) 0 1) (hΦ i h'')
    simp [sl2Upper] at h3
  let e : Fin D.rank → kˣ := fun i => Units.mk0 (χ i) (hχ0 i)
  obtain ⟨s, hs⟩ := exists_prod_zpow_cartan_eq D.cartan hdet e
  set T := torusProd x s with hTdef
  have hTpos : ∀ i v, T * x (Pi.single i 1) v * T⁻¹ = x (Pi.single i 1) (((e i : kˣ) : k) * v) := by
    intro i v
    rw [hTdef, torusProd_conj hE s (single_mem_roots i) v]
    simp only [coroot_single]
    rw [hs i]
  set d' := d * ψ T with hd'
  have hconj : ∀ z, d'⁻¹ * ψ z * d' = ψ T⁻¹ * (d⁻¹ * ψ z * d) * ψ T := by
    intro z
    rw [hd', map_inv]
    group
  have hfpos : ∀ i c, d'⁻¹ * ψ (x (Pi.single i 1) c) * d' = ψ (x (Pi.single i 1) c) := by
    intro i c
    rw [hconj, hχ, ← map_mul, ← map_mul, inv_conj_of_conj (hTpos i)]
    congr 2
    show (((Units.mk0 (χ i) (hχ0 i))⁻¹ : kˣ) : k) * (χ i * c) = c
    rw [Units.val_inv_eq_inv_val, Units.val_mk0, ← mul_assoc, inv_mul_cancel₀ (hχ0 i), one_mul]
  have hfneg : ∀ i c, d'⁻¹ * ψ (x (-Pi.single i 1) c) * d' = ψ (x (-Pi.single i 1) c) := by
    intro i
    set ν : kˣ := ∏ j, s j ^ coroot D.cartan j (-Pi.single i 1) with hν
    have hTneg : ∀ v, T * x (-Pi.single i 1) v * T⁻¹ = x (-Pi.single i 1) ((ν : k) * v) :=
      fun v => torusProd_conj hE s (neg_single_mem_roots i) v
    have hl : ∀ c, d'⁻¹ * ψ (x (-Pi.single i 1) c) * d' =
        ψ (x (-Pi.single i 1) (((ν⁻¹ : kˣ) : k) * χ' i c)) := by
      intro c
      rw [hconj, hχ', ← map_mul, ← map_mul, inv_conj_of_conj hTneg]
    have he1 : ∀ c, ((ν⁻¹ : kˣ) : k) * χ' i c = c := by
      refine eq_of_conj_sl2 (ψ.comp (φ i)) (hΦ i) (d := d') (fun c => ?_) (fun c => ?_)
      · rw [MonoidHom.comp_apply, hφu]
        exact hfpos i c
      · rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hφl, hφl]
        exact hl c
    intro c
    rw [hl, he1]
  have hall : ∀ γ ∈ D.roots, ∀ v, x γ v ∈ (Subgroup.centralizer ({d'} : Set G)).comap ψ := by
    rintro γ (⟨w, j, rfl⟩ | ⟨w, j, hj, -⟩) v
    · obtain ⟨ω, rfl⟩ := (coxeterMatrix D.isFiniteType).toCoxeterSystem.wordProd_surjective w
      exact fix_weylAction hE ψ hfpos hfneg ω j v
    · rw [hdiv] at hj
      exact absurd hj (Set.notMem_empty j)
  have hS : ⨆ γ ∈ D.roots, D.rootGroup γ ≤ (Subgroup.centralizer ({d'} : Set G)).comap ψ := by
    refine iSup₂_le fun γ hγ z hz => ?_
    obtain ⟨c, rfl⟩ := ((hE.param γ hγ).1 z).mp hz
    exact hall γ hγ c
  rw [hgen] at hS
  refine ⟨T, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨z, rfl⟩
  exact Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_comap.mp (hS (Subgroup.mem_top z)))

theorem exists_mem_centralizer_of_ggPsiInnerDiag (hE : ChevalleyExtras D k x C O) [Finite k]
    [CharP k 2] (hdiv : D.divisible = ∅) (hgen : ⨆ γ ∈ D.roots, D.rootGroup γ = ⊤) {a : ℕ}
    (hdet : D.cartan.det = 2 ^ a)
    (hlin : ∀ i, ∀ h ∈ ggTorus D, ∃ χ : k, ∀ c,
      h * x (Pi.single i 1) c * h⁻¹ = x (Pi.single i 1) (χ * c))
    {G : Type*} [Group G] (ψ : K →* G) (hker : ψ.ker ≤ Subgroup.center K) {c : G}
    (hc : GGPsiInnerDiag D ψ c) :
    ∃ g ∈ ψ.range, c * g ∈ Subgroup.centralizer (ψ.range : Set G) := by
  obtain ⟨g, hg, hγ⟩ := hc
  have key : ∀ i, ∃ χ : k, ∀ c', (c * g)⁻¹ * ψ (x (Pi.single i 1) c') * (c * g) =
      ψ (x (Pi.single i 1) (χ * c')) := by
    intro i
    obtain ⟨h, hh, hz⟩ := hγ _ (single_mem_roots i)
    obtain ⟨χ, hχ⟩ := hlin i h hh
    exact ⟨χ, fun c' => by
      rw [hz _ (((hE.param _ (single_mem_roots i)).1 _).mpr ⟨c', rfl⟩), hχ]⟩
  have keyn : ∀ i, ∃ φ : k → k, ∀ c', (c * g)⁻¹ * ψ (x (-Pi.single i 1) c') * (c * g) =
      ψ (x (-Pi.single i 1) (φ c')) := by
    intro i
    obtain ⟨h, hh, hz⟩ := hγ _ (neg_single_mem_roots i)
    have hN : h ∈ Subgroup.normalizer (D.rootGroup (-Pi.single i 1) : Set K) := by
      simp only [ggTorus, Subgroup.mem_iInf] at hh
      exact hh _ (neg_single_mem_roots i)
    have hmem : ∀ c', ∃ c'', x (-Pi.single i 1) c'' =
        h * x (-Pi.single i 1) c' * h⁻¹ := fun c' =>
      ((hE.param _ (neg_single_mem_roots i)).1 _).mp ((Subgroup.mem_normalizer_iff.mp hN _).mp
        (((hE.param _ (neg_single_mem_roots i)).1 _).mpr ⟨c', rfl⟩))
    choose φ hφ using hmem
    exact ⟨φ, fun c' => by
      rw [hz _ (((hE.param _ (neg_single_mem_roots i)).1 _).mpr ⟨c', rfl⟩), hφ]⟩
  obtain ⟨u, hu⟩ := exists_mul_psi_mem_centralizer hE hdiv hgen hdet ψ hker key keyn
  exact ⟨g * ψ u, mul_mem hg ⟨u, rfl⟩, by rwa [← mul_assoc]⟩

end PsiDiag

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGQ2LinStatements
import CFSG.LocalAnalysis.StandardType.GGQ2LinBlocksBasic
import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIdem

public section

namespace CFSG.StandardType.GGQ2Frame.LinBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition Matrix
open CFSG.Open (StatedSp)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

noncomputable section

variable {K : Type} [Field K]
variable {t : ℕ}
variable {ε : Fin 2}

private noncomputable def commonZeros {t : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V t)) :
    Finset (Fin t) := by
  classical
  exact Finset.univ.filter fun i => ∀ u : U, (u : PlaneRaw.V t) i = 0

private theorem mem_commonZeros {t : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V t)) (i : Fin t) :
    i ∈ commonZeros U ↔ ∀ u : U, (u : PlaneRaw.V t) i = 0 := by
  classical
  simp [commonZeros]

private def keyFix {t : ℕ} : PlaneRaw.Code t → Bool
  | .zero _ => true
  | .extension _ => false

private def iInterFinset {ι : Type} (s : Finset ι) (W : ι → Finset (Fin t)) : Finset (Fin t) :=
  Finset.univ.filter fun j => ∀ i ∈ s, j ∈ W i

private theorem iInterFinset_empty {ι : Type} (W : ι → Finset (Fin t)) :
    iInterFinset ∅ W = Finset.univ := by
  ext j; simp [iInterFinset]

private theorem iInterFinset_insert {ι : Type} [DecidableEq ι] (s : Finset ι) (a : ι)
    (_ha : a ∉ s) (W : ι → Finset (Fin t)) :
    iInterFinset (insert a s) W = W a ∩ iInterFinset s W := by
  ext j
  simp [iInterFinset, Finset.mem_insert, forall_eq_or_imp]

private theorem planeIdem_mul (t : ℕ) (ε : Fin 2) (S T : Finset (Fin t)) (fix fix' : Bool) :
    (planeIdem t ε S fix : Matrix (LinIdx t ε) (LinIdx t ε) K) *
        (planeIdem t ε T fix' : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      (planeIdem t ε (S ∩ T) (fix && fix') : Matrix (LinIdx t ε) (LinIdx t ε) K) := by
  rw [planeIdem_eq_fromBlocks_smul, planeIdem_eq_fromBlocks_smul,
    planeIdem_eq_fromBlocks_smul, Matrix.fromBlocks_multiply, ← SpBlocks.planeIdem_inter]
  ext a b
  rcases a with (i | i) | i <;> rcases b with (j | j) | j <;>
    simp only [Matrix.fromBlocks]
  all_goals split_ifs <;> simp_all

private theorem planeIdem_univ_true (t : ℕ) (ε : Fin 2) :
    (planeIdem t ε Finset.univ true : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      (1 : Matrix (LinIdx t ε) (LinIdx t ε) K) := by
  rw [planeIdem_eq_fromBlocks_smul, SpBlocks.planeIdem_univ]
  simp [Matrix.fromBlocks_one]

private theorem planeIdem_mul_true (t : ℕ) (ε : Fin 2) (S T : Finset (Fin t)) :
    (planeIdem t ε (S ∩ T) true : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      planeIdem t ε S true * planeIdem t ε T true := by
  rw [planeIdem_mul, Bool.true_and]

private theorem planeIdem_mul_any_false (t : ℕ) (ε : Fin 2) (S T : Finset (Fin t)) (fix : Bool) :
    (planeIdem t ε (S ∩ T) false : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      planeIdem t ε S fix * planeIdem t ε T false := by
  rw [planeIdem_mul, Bool.and_false]

private theorem planeIdem_iInter_mem_true {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Subalgebra K (Matrix (LinIdx t ε) (LinIdx t ε) K)) (W : ι → Finset (Fin t))
    (hW : ∀ i, planeIdem t ε (W i) true ∈ A) :
    planeIdem t ε (iInterFinset (Finset.univ : Finset ι) W) true ∈ A := by
  classical
  have key : ∀ s : Finset ι, planeIdem t ε (iInterFinset s W) true ∈ A := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
        rw [iInterFinset_empty, planeIdem_univ_true]
        exact A.one_mem
    | insert a s ha ih =>
        rw [iInterFinset_insert s a ha W, planeIdem_mul_true]
        exact A.mul_mem (hW a) ih
  simpa using key Finset.univ

private theorem planeIdem_iInter_mem_mixed {ι : Type} [Fintype ι] [DecidableEq ι]
    (A : Subalgebra K (Matrix (LinIdx t ε) (LinIdx t ε) K)) (W : ι → Finset (Fin t))
    (fix : ι → Bool) (hW : ∀ i, planeIdem t ε (W i) (fix i) ∈ A)
    (hfalse : ∃ i, fix i = false) :
    planeIdem t ε (iInterFinset (Finset.univ : Finset ι) W) false ∈ A := by
  classical
  obtain ⟨i0, hi0⟩ := hfalse
  set s0 := Finset.univ.erase i0 with hs0
  have hnot : i0 ∉ s0 := by simp [hs0]
  have key : ∀ s : Finset ι, s ⊆ s0 →
      planeIdem t ε (iInterFinset (insert i0 s) W) false ∈ A := by
    intro s hs
    induction s using Finset.induction_on with
    | empty =>
        rw [iInterFinset_insert ∅ i0 (by simp) W, iInterFinset_empty, Finset.inter_univ]
        simpa [hi0] using hW i0
    | insert a s ha ih =>
        have ha0 : a ≠ i0 := by
          intro h; subst h; exact hnot (hs (by simp [ha]))
        have ha' : a ∉ insert i0 s := by simp [ha, ha0]
        rw [Finset.insert_comm i0 a]
        rw [iInterFinset_insert (insert i0 s) a ha' W, planeIdem_mul_any_false]
        exact A.mul_mem (hW a) (ih (by intro x hx; exact hs (by simp [hx])))
  have huniv : insert i0 s0 = Finset.univ := by
    ext x
    simp [hs0]
  simpa [huniv] using key s0 (Finset.Subset.refl s0)

private theorem planeIdem_compl_true [Finite K] [CharP K 2] (t : ℕ) (ε : Fin 2)
    (S : Finset (Fin t)) :
    (planeIdem t ε Sᶜ true : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      1 + planeIdem t ε S false := by
  rw [planeIdem_eq_fromBlocks_smul, planeIdem_eq_fromBlocks_smul, SpBlocks.planeIdem_compl]
  rw [show (1 : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      fromBlocks 1 0 0 1 by rw [Matrix.fromBlocks_one]]
  rw [Matrix.fromBlocks_add]
  congr 1
  · rw [sub_eq_add_neg, SpBlocks.neg_eq_self_of_charTwo]
  all_goals simp

private theorem planeIdem_support_eq_tau_mul_self_add [Finite K] [CharP K 2]
    (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (t : ℕ) (ε : Fin 2) (u : PlaneRaw.V t) :
    (planeIdem t ε (PlaneRaw.vSupport u) false : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) *
        ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) +
      ((tau ζ t ε u : GL (LinIdx t ε) K) : Matrix (LinIdx t ε) (LinIdx t ε) K) := by
  rw [planeIdem_eq_fromBlocks_smul, coe_tau_eq_fromBlocks_spTau]
  rw [Matrix.fromBlocks_multiply, Matrix.fromBlocks_add]
  simp only [Matrix.zero_mul, Matrix.mul_zero, add_zero, zero_add]
  congr 1
  · rw [SpBlocks.tau_mul_self_add hK hζ u]
    simp [PlaneRaw.vSupport]
  · simp [SpBlocks.add_self_eq_zero_of_charTwo]

private theorem keyIdem_zero_mem_adjoin [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (t : ℕ) (ε : Fin 2) (U : Submodule (ZMod 3) (PlaneRaw.V t)) (S : Finset (Fin t))
    (hc : PlaneRaw.occurs U (.zero S)) :
    keyIdem t ε (.zero S) ∈ Algebra.adjoin K (Units.val '' torusSet ζ t ε U) := by
  classical
  set A := Algebra.adjoin K (Units.val '' torusSet ζ t ε U) with hA
  have hS : S = commonZeros U := by
    ext i
    rw [mem_commonZeros]
    exact (hc i)
  have hW : ∀ u : U, planeIdem t ε ((PlaneRaw.vSupport (u : PlaneRaw.V t))ᶜ) true ∈ A := by
    intro u
    have h1 : (planeIdem t ε (PlaneRaw.vSupport (u : PlaneRaw.V t)) false :
        Matrix (LinIdx t ε) (LinIdx t ε) K) ∈ A := by
      have hg : (((tau ζ t ε (u : PlaneRaw.V t) : GL (LinIdx t ε) K)) :
          Matrix (LinIdx t ε) (LinIdx t ε) K) ∈ A :=
        Algebra.subset_adjoin ⟨_, ⟨u, u.2, rfl⟩, rfl⟩
      rw [planeIdem_support_eq_tau_mul_self_add hK hζ t ε (u : PlaneRaw.V t)]
      exact A.add_mem (A.mul_mem hg hg) hg
    rw [planeIdem_compl_true]
    exact A.add_mem A.one_mem h1
  have h := planeIdem_iInter_mem_true A (fun u : U =>
    (PlaneRaw.vSupport (u : PlaneRaw.V t))ᶜ) hW
  have hInter : iInterFinset (Finset.univ : Finset U) (fun u : U =>
      (PlaneRaw.vSupport (u : PlaneRaw.V t))ᶜ) = S := by
    rw [hS]
    ext i
    simp [iInterFinset, commonZeros, PlaneRaw.vSupport]
  simpa [keyIdem, hInter] using h

private theorem keyIdem_extension_mem_adjoin [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (t : ℕ) (ε : Fin 2) (U : Submodule (ZMod 3) (PlaneRaw.V t)) (e : PlaneRaw.V t)
    (hc : PlaneRaw.occurs U (.extension e)) :
    keyIdem t ε (.extension e) ∈ Algebra.adjoin K (Units.val '' torusSet ζ t ε U) := by
  classical
  obtain ⟨-, χ, hχ, hsupp, hout⟩ := hc
  set A := Algebra.adjoin K (Units.val '' torusSet ζ t ε U) with hA
  have happ : ∀ (i : Fin t) (u : U), PlaneRaw.evalRestr U i u = (u : PlaneRaw.V t) i :=
    fun _ _ => rfl
  let W : U → Finset (Fin t) := fun u =>
    if χ u ≠ 0 then PlaneRaw.vSupport (u : PlaneRaw.V t)
    else (PlaneRaw.vSupport (u : PlaneRaw.V t))ᶜ
  let fix : U → Bool := fun u => decide (χ u = 0)
  have hW : ∀ u : U, planeIdem t ε (W u) (fix u) ∈ A := by
    intro u
    by_cases hu : χ u = 0
    · have h1 : planeIdem t ε (PlaneRaw.vSupport (u : PlaneRaw.V t)) false ∈ A := by
        have hg : (((tau ζ t ε (u : PlaneRaw.V t) : GL (LinIdx t ε) K)) :
            Matrix (LinIdx t ε) (LinIdx t ε) K) ∈ A :=
          Algebra.subset_adjoin ⟨_, ⟨u, u.2, rfl⟩, rfl⟩
        rw [planeIdem_support_eq_tau_mul_self_add hK hζ t ε (u : PlaneRaw.V t)]
        exact A.add_mem (A.mul_mem hg hg) hg
      have h2 : planeIdem t ε (PlaneRaw.vSupport (u : PlaneRaw.V t))ᶜ true ∈ A := by
        rw [planeIdem_compl_true]
        exact A.add_mem A.one_mem h1
      simpa [W, fix, hu] using h2
    · have h2 : planeIdem t ε (PlaneRaw.vSupport (u : PlaneRaw.V t)) false ∈ A := by
        have hg : (((tau ζ t ε (u : PlaneRaw.V t) : GL (LinIdx t ε) K)) :
            Matrix (LinIdx t ε) (LinIdx t ε) K) ∈ A :=
          Algebra.subset_adjoin ⟨_, ⟨u, u.2, rfl⟩, rfl⟩
        rw [planeIdem_support_eq_tau_mul_self_add hK hζ t ε (u : PlaneRaw.V t)]
        exact A.add_mem (A.mul_mem hg hg) hg
      simpa [W, fix, hu] using h2
  have hfalse : ∃ u : U, fix u = false := by
    obtain ⟨u₁, hu₁⟩ : ∃ u : U, χ u ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hχ (LinearMap.ext hcon)
    exact ⟨u₁, by simp [fix, hu₁]⟩
  have h := planeIdem_iInter_mem_mixed A W fix hW hfalse
  have heq : PlaneRaw.Code.extSupport e = iInterFinset (Finset.univ : Finset U) W := by
    ext j
    simp only [PlaneRaw.Code.extSupport, iInterFinset, Finset.mem_filter, Finset.mem_univ,
      true_and]
    constructor
    · intro hej u
      have hj : (u : PlaneRaw.V t) j = e j * χ u := by
        rw [← happ, hsupp j hej, LinearMap.smul_apply, smul_eq_mul]
      simp only [W]
      split_ifs with hu
      · simp [hj, hej, hu, PlaneRaw.vSupport]
      · simp only [not_not] at hu
        simp [hj, hu, PlaneRaw.vSupport]
    · intro hall
      by_contra hej
      obtain ⟨hne1, hne2⟩ := hout j hej
      obtain ⟨u₁, hu₁⟩ : ∃ u : U, χ u ≠ 0 := by
        by_contra hcon
        push Not at hcon
        exact hχ (LinearMap.ext hcon)
      set u₀ : U := (χ u₁)⁻¹ • u₁ with hu₀
      have hχ₀ : χ u₀ = 1 := by
        rw [hu₀, map_smul, smul_eq_mul, inv_mul_cancel₀ hu₁]
      have hmem : ∀ u : U, (χ u ≠ 0 → (u : PlaneRaw.V t) j ≠ 0) ∧
          (χ u = 0 → (u : PlaneRaw.V t) j = 0) := by
        intro u
        have h := hall u
        simp only [W] at h
        split_ifs at h with hu
        · simp only [PlaneRaw.vSupport, Finset.mem_filter, Finset.mem_univ, true_and] at h
          have h' : (u : PlaneRaw.V t) j ≠ 0 := by simpa using h
          exact ⟨fun _ => h', fun h0 => absurd h0 hu⟩
        · simp only [PlaneRaw.vSupport, Finset.mem_compl, Finset.mem_filter, Finset.mem_univ,
            true_and, not_not] at h
          have h' : (u : PlaneRaw.V t) j = 0 := by simpa using h
          exact ⟨fun h0 => absurd (not_not.mp hu) h0, fun _ => h'⟩
      set a := (u₀ : PlaneRaw.V t) j with ha
      have ha0 : a ≠ 0 := (hmem u₀).1 (by rw [hχ₀]; exact one_ne_zero)
      have hψ : PlaneRaw.evalRestr U j = a • χ := by
        ext u
        rw [happ, LinearMap.smul_apply, smul_eq_mul]
        have hv := (hmem (u - χ u • u₀)).2 (by rw [map_sub, map_smul, hχ₀, smul_eq_mul,
          mul_one, sub_self])
        rw [Submodule.coe_sub, Submodule.coe_smul, Pi.sub_apply, Pi.smul_apply,
          smul_eq_mul, sub_eq_zero] at hv
        rw [hv, ha, mul_comm]
      have h12 : ∀ b : ZMod 3, b ≠ 0 → b = 1 ∨ b = -1 := by decide
      rcases h12 a ha0 with h1 | h1
      · exact hne1 (by rw [hψ, h1, one_smul])
      · exact hne2 (by rw [hψ, h1]; ext u; simp)
  change keyIdem t ε (.extension e) ∈ A
  rw [keyIdem, heq]
  exact h

private theorem keyIdem_mem_adjoin [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (t : ℕ) (ε : Fin 2) (U : Submodule (ZMod 3) (PlaneRaw.V t)) (c : PlaneRaw.Code t)
    (hc : PlaneRaw.occurs U c) :
    keyIdem t ε c ∈ Algebra.adjoin K (Units.val '' torusSet ζ t ε U) := by
  cases c with
  | zero S => exact keyIdem_zero_mem_adjoin hK hζ t ε U S hc
  | extension e => exact keyIdem_extension_mem_adjoin hK hζ t ε U e hc

private noncomputable def zetaMat (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K) :
    Matrix (Fin 2) (Fin 2) K :=
  (ζ (Multiplicative.ofAdd 1) : SpecialLinearGroup (Fin 2) K)

private noncomputable def blockMat (t : ℕ) (Z : Matrix (Fin 2) (Fin 2) K) (α β : Fin t → K) :
    Matrix (Fin t ⊕ Fin t) (Fin t ⊕ Fin t) K :=
  WitSpNs.planeMat fun j => α j • (1 : Matrix (Fin 2) (Fin 2) K) + β j • Z

private theorem blockMat_add (t : ℕ) (Z : Matrix (Fin 2) (Fin 2) K) (α β α' β' : Fin t → K) :
    blockMat t Z (α + α') (β + β') = blockMat t Z α β + blockMat t Z α' β' := by
  simp only [blockMat]
  rw [SpBlocks.planeMat_add]
  congr 1
  funext j
  simp only [Pi.add_apply, add_smul]
  abel

private theorem blockMat_mul (t : ℕ) (Z : Matrix (Fin 2) (Fin 2) K) (hZ : Z * Z = 1 + Z)
    (α β α' β' : Fin t → K) :
    blockMat t Z (fun j => α j * α' j + β j * β' j)
      (fun j => α j * β' j + β j * α' j + β j * β' j) =
      blockMat t Z α β * blockMat t Z α' β' := by
  simp only [blockMat]
  rw [WitSpNs.planeMat_mul]
  congr 1
  funext j
  exact (SpBlocks.blk_mul hZ _ _ _ _).symm

private theorem exists_blocks_of_mem_adjoin [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (t : ℕ) (ε : Fin 2) (U : Submodule (ZMod 3) (PlaneRaw.V t))
    {a : Matrix (LinIdx t ε) (LinIdx t ε) K}
    (ha : a ∈ Algebra.adjoin K (Units.val '' torusSet ζ t ε U)) :
    ∃ (α β : Fin t → K) (γ : K),
      a = Matrix.fromBlocks (blockMat t (zetaMat ζ) α β) 0 0
        (γ • (1 : Matrix (Fin ε.val) (Fin ε.val) K)) ∧
      (∀ i j, (PlaneRaw.evalRestr U i = PlaneRaw.evalRestr U j → α i = α j ∧ β i = β j) ∧
        (PlaneRaw.evalRestr U i = -PlaneRaw.evalRestr U j → α i = α j + β j ∧ β i = β j)) ∧
      (∀ j, PlaneRaw.evalRestr U j = 0 → α j = γ ∧ β j = 0) := by
  have hZ : zetaMat ζ * zetaMat ζ = 1 + zetaMat ζ := SpBlocks.zeta_one_mul_self hK hζ
  have h2K : (2 : K) = 0 := CharTwo.two_eq_zero
  induction ha using Algebra.adjoin_induction with
  | mem x hx =>
    obtain ⟨g, ⟨u, hu, rfl⟩, rfl⟩ := hx
    refine ⟨fun j => if u j = 1 then 0 else 1, fun j => if u j = 0 then 0 else 1, 1,
      ?_, fun i j => ⟨fun h => ?_, fun h => ?_⟩, fun j hj => ?_⟩
    · rw [coe_tau_eq_fromBlocks_planeMat]
      simp only [blockMat]
      congr 1
      · congr 1
        funext j
        exact SpBlocks.coe_zeta_eq hK hζ (u j)
      · simp
    · have hij := congrArg (fun f => f ⟨u, hu⟩) h
      simp only [SpBlocks.evalRestr_apply'] at hij
      simp only [hij, and_self]
    · have hij := congrArg (fun f => f ⟨u, hu⟩) h
      simp only [LinearMap.neg_apply, SpBlocks.evalRestr_apply'] at hij
      simp only [hij]
      exact SpBlocks.zeta_coeff_neg (u j)
    · have huj : u j = 0 := by
        have := congrArg (fun f => f ⟨u, hu⟩) hj
        simpa [SpBlocks.evalRestr_apply'] using this
      simp [huj]
  | algebraMap r =>
    refine ⟨fun _ => r, fun _ => 0, r, ?_, fun i j => ⟨fun _ => ⟨rfl, rfl⟩, fun _ => ⟨?_, rfl⟩⟩,
      fun j _ => ⟨rfl, rfl⟩⟩
    · rw [Algebra.algebraMap_eq_smul_one]
      rw [← Matrix.fromBlocks_one, Matrix.fromBlocks_smul]
      congr 1
      · simp only [blockMat]
        rw [show (fun j : Fin t => r • (1 : Matrix (Fin 2) (Fin 2) K) + (0 : K) • zetaMat ζ) =
            fun _ => r • (1 : Matrix (Fin 2) (Fin 2) K) by
          funext j
          rw [zero_smul, add_zero]]
        rw [← SpBlocks.planeMat_smul, WitSpNs.planeMat_one]
      all_goals simp
    · rw [add_zero]
  | add x y _ _ hx hy =>
    obtain ⟨α, β, γ, rfl, hαβ, hγ⟩ := hx
    obtain ⟨α', β', γ', rfl, hαβ', hγ'⟩ := hy
    refine ⟨α + α', β + β', γ + γ', ?_, fun i j => ⟨fun h => ?_, fun h => ?_⟩,
      fun j hj => ?_⟩
    · rw [Matrix.fromBlocks_add]
      apply Matrix.fromBlocks_inj.mpr
      exact ⟨(blockMat_add t (zetaMat ζ) α β α' β').symm, by simp, by simp, by rw [add_smul]⟩
    · obtain ⟨h1, h2⟩ := (hαβ i j).1 h
      obtain ⟨h1', h2'⟩ := (hαβ' i j).1 h
      simp only [Pi.add_apply, h1, h2, h1', h2', and_self]
    · obtain ⟨h1, h2⟩ := (hαβ i j).2 h
      obtain ⟨h1', h2'⟩ := (hαβ' i j).2 h
      refine ⟨?_, by simp only [Pi.add_apply, h2, h2']⟩
      simp only [Pi.add_apply]
      rw [h1, h1']
      ring
    · obtain ⟨h1, h2⟩ := hγ j hj
      obtain ⟨h1', h2'⟩ := hγ' j hj
      simp [Pi.add_apply, h1, h2, h1', h2']
  | mul x y _ _ hx hy =>
    obtain ⟨α, β, γ, rfl, hαβ, hγ⟩ := hx
    obtain ⟨α', β', γ', rfl, hαβ', hγ'⟩ := hy
    refine ⟨fun j => α j * α' j + β j * β' j,
      fun j => α j * β' j + β j * α' j + β j * β' j, γ * γ', ?_,
      fun i j => ⟨fun h => ?_, fun h => ?_⟩, fun j hj => ?_⟩
    · rw [Matrix.fromBlocks_multiply]
      apply Matrix.fromBlocks_inj.mpr
      refine ⟨?_, by simp, by simp, ?_⟩
      · rw [Matrix.zero_mul, add_zero]
        exact (blockMat_mul t (zetaMat ζ) hZ α β α' β').symm
      · rw [Matrix.zero_mul, zero_add, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul,
          smul_smul]
    · obtain ⟨h1, h2⟩ := (hαβ i j).1 h
      obtain ⟨h1', h2'⟩ := (hαβ' i j).1 h
      simp only [h1, h2, h1', h2', and_self]
    · obtain ⟨h1, h2⟩ := (hαβ i j).2 h
      obtain ⟨h1', h2'⟩ := (hαβ' i j).2 h
      simp only [h1, h2, h1', h2']
      exact ⟨by ring, by linear_combination (β j * β' j) * h2K⟩
    · obtain ⟨h1, h2⟩ := hγ j hj
      obtain ⟨h1', h2'⟩ := hγ' j hj
      refine ⟨?_, ?_⟩
      · change α j * α' j + β j * β' j = γ * γ'
        rw [h1, h2, h1', h2']; ring
      · change α j * β' j + β j * α' j + β j * β' j = 0
        rw [h1, h2, h1', h2']; ring

private theorem exists_planeIdem_of_isIdempotentElem [Finite K] [CharP K 2]
    (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    (t : ℕ) (ε : Fin 2) (U : Submodule (ZMod 3) (PlaneRaw.V t))
    {e : Matrix (LinIdx t ε) (LinIdx t ε) K}
    (he : e ∈ Algebra.adjoin K (Units.val '' torusSet ζ t ε U))
    (hidem : IsIdempotentElem e) :
    ∃ (T : Finset (Fin t)) (fix : Bool), e = planeIdem t ε T fix ∧
      (∀ i j, (PlaneRaw.evalRestr U i = PlaneRaw.evalRestr U j ∨
        PlaneRaw.evalRestr U i = -PlaneRaw.evalRestr U j) → j ∈ T → i ∈ T) ∧
      (∀ j, PlaneRaw.evalRestr U j = 0 → (j ∈ T ↔ fix = true)) := by
  classical
  obtain ⟨α, β, γ, heq, hαβ, hγ⟩ := exists_blocks_of_mem_adjoin hK hζ t ε U he
  have hZ : zetaMat ζ * zetaMat ζ = 1 + zetaMat ζ := SpBlocks.zeta_one_mul_self hK hζ
  have hsq : ∀ x : K, x * x = x := fun x => by
    rcases SpBlocks.eq_zero_or_eq_one hK x with h | h <;> simp [h]
  have htl : blockMat t (zetaMat ζ) α β * blockMat t (zetaMat ζ) α β =
      blockMat t (zetaMat ζ) α β := by
    have h1 : e * e = e := hidem.eq
    rw [heq, Matrix.fromBlocks_multiply] at h1
    have h2 := (Matrix.fromBlocks_inj.mp h1).1
    simpa [Matrix.zero_mul, add_zero] using h2
  have hblk : ∀ j, β j = 0 ∧ (α j = 0 ∨ α j = 1) := by
    intro j
    have h2 : blockMat t (zetaMat ζ) α β =
        blockMat t (zetaMat ζ) (fun j => α j * α j + β j * β j)
          (fun j => α j * β j + β j * α j + β j * β j) := by
      rw [blockMat_mul t (zetaMat ζ) hZ α β α β]
      exact htl.symm
    have h2' : WitSpNs.planeMat (fun j => α j • (1 : Matrix (Fin 2) (Fin 2) K) +
        β j • zetaMat ζ) =
        WitSpNs.planeMat (fun j => (α j * α j + β j * β j) • (1 : Matrix (Fin 2) (Fin 2) K) +
          (α j * β j + β j * α j + β j * β j) • zetaMat ζ) := h2
    have h3 := congrFun (WitSpNs.planeMat_injective h2') j
    have h4 := (SpBlocks.blk_inj hK hZ h3).1
    rw [hsq, hsq] at h4
    exact ⟨by simpa using h4, SpBlocks.eq_zero_or_eq_one hK _⟩
  let T : Finset (Fin t) := Finset.univ.filter fun j => α j = 1
  let fix : Bool := decide (γ = 1)
  refine ⟨T, fix, ?_, ?_, ?_⟩
  · have hβ0 : ∀ j, β j = 0 := fun j => (hblk j).1
    have hblock : blockMat t (zetaMat ζ) α β = SpBlocks.planeIdem t T := by
      simp only [blockMat, SpBlocks.planeIdem_eq_planeMat]
      congr 1
      funext j
      rw [hβ0 j, zero_smul, add_zero]
      by_cases hj : α j = 1
      · simp [T, hj]
      · rcases (hblk j).2 with h0 | h1
        · simp [T, h0]
        · exact absurd h1 hj
    rw [heq, hblock, planeIdem_eq_fromBlocks_smul]
    congr 1
    rcases SpBlocks.eq_zero_or_eq_one hK γ with h | h <;> simp [fix, h]
  · intro i j hij hj
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
    rcases hij with h | h
    · rw [((hαβ i j).1 h).1, hj]
    · rw [((hαβ i j).2 h).1, (hblk j).1, add_zero, hj]
  · intro j hj
    obtain ⟨ha, hb⟩ := hγ j hj
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and]
    rw [ha]
    rcases SpBlocks.eq_zero_or_eq_one hK γ with h | h <;> simp [fix, h]

private theorem planeIdem_inl_lin (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) (fix : Bool)
    (j : Fin t) :
    (planeIdem t ε S fix : Matrix (LinIdx t ε) (LinIdx t ε) K)
      (Sum.inl (Sum.inl j)) (Sum.inl (Sum.inl j)) = if j ∈ S then 1 else 0 := by
  by_cases hj : j ∈ S <;> simp [planeIdem, Matrix.diagonal, hj]

private theorem planeIdem_inr_lin (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) (fix : Bool)
    (i : Fin ε.val) :
    (planeIdem t ε S fix : Matrix (LinIdx t ε) (LinIdx t ε) K)
      (Sum.inr i) (Sum.inr i) = if fix then 1 else 0 := by
  by_cases hf : fix <;> simp [planeIdem, Matrix.diagonal, hf]

private theorem isIdempotentElem_planeIdem (t : ℕ) (ε : Fin 2) (S : Finset (Fin t)) (fix : Bool) :
    IsIdempotentElem (planeIdem t ε S fix : Matrix (LinIdx t ε) (LinIdx t ε) K) := by
  rw [IsIdempotentElem, planeIdem_mul, Finset.inter_self, Bool.and_self]

private theorem planeIdem_empty_false (t : ℕ) (ε : Fin 2) :
    (planeIdem t ε ∅ false : Matrix (LinIdx t ε) (LinIdx t ε) K) = 0 := by
  rw [planeIdem_eq_fromBlocks_smul, SpBlocks.planeIdem_empty]
  ext a b
  rcases a with (i | i) | i <;> rcases b with (j | j) | j <;>
    simp [Matrix.fromBlocks]

private theorem planeIdem_fix_irrelevant (t : ℕ) (ε : Fin 2) (hε : ε.val = 0)
    (T : Finset (Fin t)) (f g : Bool) :
    (planeIdem t ε T f : Matrix (LinIdx t ε) (LinIdx t ε) K) = planeIdem t ε T g := by
  rw [planeIdem_eq_fromBlocks_smul, planeIdem_eq_fromBlocks_smul]
  congr 1
  have hε' : ε = 0 := Fin.ext hε
  rw [hε']
  ext i j
  exact Fin.elim0 i

private theorem subset_of_planeIdem_mul_eq {t : ℕ} {ε : Fin 2} {S T : Finset (Fin t)}
    {f g : Bool} (h : (planeIdem t ε T f : Matrix (LinIdx t ε) (LinIdx t ε) K) *
      planeIdem t ε S g = planeIdem t ε T f) : T ⊆ S := by
  intro j hj
  rw [planeIdem_mul] at h
  have h1 := congrFun (congrFun h (Sum.inl (Sum.inl j))) (Sum.inl (Sum.inl j))
  rw [planeIdem_inl_lin, planeIdem_inl_lin] at h1
  rw [if_pos hj] at h1
  by_contra hjS
  rw [if_neg fun h' => hjS (Finset.mem_inter.mp h').2] at h1
  exact zero_ne_one h1

private theorem keyIdem_ne_zero [Finite K] [CharP K 2]
    {t : ℕ} {ε : Fin 2} {c : PlaneRaw.Code t} (h : 0 < keyDim ε c) :
    (keyIdem t ε c : Matrix (LinIdx t ε) (LinIdx t ε) K) ≠ 0 := by
  intro hzero
  cases c with
  | zero S =>
    have h0eq : (keyIdem t ε (.zero S) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
        (planeIdem t ε S true : Matrix (LinIdx t ε) (LinIdx t ε) K) := rfl
    rw [h0eq] at hzero
    by_cases hS : S.Nonempty
    · obtain ⟨j, hj⟩ := hS
      have h1 : (planeIdem t ε S true : Matrix (LinIdx t ε) (LinIdx t ε) K)
          (Sum.inl (Sum.inl j)) (Sum.inl (Sum.inl j)) = if j ∈ S then 1 else 0 :=
        planeIdem_inl_lin t ε S true j
      rw [hzero, Matrix.zero_apply] at h1
      simp [hj] at h1
    · have hε : ε.val = 1 := by
        simp only [keyDim] at h
        have h0 : S = ∅ := Finset.not_nonempty_iff_eq_empty.mp hS
        rw [h0] at h
        simp at h
        omega
      let i : Fin ε.val := ⟨0, by omega⟩
      have h1 : (planeIdem t ε S true : Matrix (LinIdx t ε) (LinIdx t ε) K)
          (Sum.inr i) (Sum.inr i) = if true then 1 else 0 :=
        planeIdem_inr_lin t ε S true i
      rw [hzero, Matrix.zero_apply] at h1
      simp at h1
  | extension e =>
    have heq : (keyIdem t ε (.extension e) : Matrix (LinIdx t ε) (LinIdx t ε) K) =
        (planeIdem t ε (PlaneRaw.Code.extSupport e) false :
          Matrix (LinIdx t ε) (LinIdx t ε) K) := rfl
    rw [heq] at hzero
    have hne : (PlaneRaw.Code.extSupport e).Nonempty := by
      simp only [keyDim] at h
      exact Finset.card_pos.mp (by omega)
    obtain ⟨j, hj⟩ := hne
    have h1 : (planeIdem t ε (PlaneRaw.Code.extSupport e) false :
        Matrix (LinIdx t ε) (LinIdx t ε) K)
        (Sum.inl (Sum.inl j)) (Sum.inl (Sum.inl j)) =
        if j ∈ PlaneRaw.Code.extSupport e then 1 else 0 :=
      planeIdem_inl_lin t ε (PlaneRaw.Code.extSupport e) false j
    rw [hzero, Matrix.zero_apply] at h1
    simp [hj] at h1

theorem linIsPrimIdemInKeyIdem_holds : LinIsPrimIdemInKeyIdem := by
  intro K _ _ _ ζ t ε hK hζ U c hc hdim
  let A := Algebra.adjoin K (Units.val '' torusSet ζ t ε U)
  let P : Matrix (LinIdx t ε) (LinIdx t ε) K := keyIdem t ε c
  have hPmem : P ∈ A := keyIdem_mem_adjoin hK hζ t ε U c hc
  have hPidem : IsIdempotentElem P := by
    cases c with
    | zero S =>
        change IsIdempotentElem (planeIdem t ε S true : Matrix (LinIdx t ε) (LinIdx t ε) K)
        exact isIdempotentElem_planeIdem t ε S true
    | extension e =>
        change IsIdempotentElem (planeIdem t ε (PlaneRaw.Code.extSupport e) false :
          Matrix (LinIdx t ε) (LinIdx t ε) K)
        exact isIdempotentElem_planeIdem t ε (PlaneRaw.Code.extSupport e) false
  have hPne : P ≠ 0 := keyIdem_ne_zero hdim
  refine ⟨hPmem, hPidem, hPne, ?_⟩
  intro e' he' hidem' hmul'
  obtain ⟨T, fix, heq, hT, hfix⟩ := exists_planeIdem_of_isIdempotentElem hK hζ t ε U he' hidem'
  have hP : (P : Matrix (LinIdx t ε) (LinIdx t ε) K) =
      planeIdem t ε c.support (keyFix c) := by
    cases c <;> rfl
  have hmul : (planeIdem t ε T fix : Matrix (LinIdx t ε) (LinIdx t ε) K) *
      planeIdem t ε c.support (keyFix c) = planeIdem t ε T fix := by
    simpa [P, heq, hP] using hmul'
  have hsub : T ⊆ c.support := subset_of_planeIdem_mul_eq hmul
  rcases T.eq_empty_or_nonempty with hT0 | ⟨i, hi⟩
  · rw [hT0] at heq hfix
    rw [heq]
    by_cases hfixf : fix = false
    · left
      rw [hfixf, planeIdem_empty_false]
    · rw [Bool.not_eq_false] at hfixf
      by_cases hε : ε.val = 0
      · left
        rw [planeIdem_fix_irrelevant t ε hε ∅ fix false, planeIdem_empty_false]
      · have hε1 : ε.val = 1 := by omega
        let i0 : Fin ε.val := ⟨0, by omega⟩
        have hkey : keyFix c = true := by
          have h1 := congrFun (congrFun hmul (Sum.inr i0)) (Sum.inr i0)
          rw [planeIdem_mul] at h1
          rw [planeIdem_inr_lin, planeIdem_inr_lin] at h1
          simp only [hfixf] at h1
          split_ifs at h1 with h
          · exact h
          · simp at h1
        right
        cases c with
        | zero S =>
          have hS : S = ∅ := by
            by_contra hne
            obtain ⟨j, hj⟩ := Finset.nonempty_iff_ne_empty.mpr hne
            have hψ : PlaneRaw.evalRestr U j = 0 := by
              ext u
              rw [SpBlocks.evalRestr_apply']
              exact (hc j).mp hj u
            have := (hfix j hψ).2 hfixf
            simp at this
          rw [hfixf, hS]
          rfl
        | extension e =>
          simp [keyFix] at hkey
  · have hiS : i ∈ c.support := hsub hi
    have hTsub : c.support ⊆ T := by
      intro j hj
      exact hT j i (SpBlocks.evalRestr_eq_or_eq_neg_of_mem_support U hc hj hiS) hi
    have hTeq : T = c.support := Finset.Subset.antisymm hsub hTsub
    right
    rw [heq, hTeq]
    by_cases hε : ε.val = 0
    · simpa [P, hP] using planeIdem_fix_irrelevant t ε hε c.support fix (keyFix c)
    · have hflag : fix = keyFix c := by
        cases c with
        | zero S =>
          have hψi : PlaneRaw.evalRestr U i = 0 := by
            ext u
            rw [SpBlocks.evalRestr_apply']
            exact (hc i).mp hiS u
          have h1 := (hfix i hψi).1 hi
          rw [h1]
          rfl
        | extension e =>
          have hε1 : ε.val = 1 := by omega
          let i0 : Fin ε.val := ⟨0, by omega⟩
          have h1 := congrFun (congrFun hmul (Sum.inr i0)) (Sum.inr i0)
          rw [planeIdem_mul] at h1
          rw [planeIdem_inr_lin, planeIdem_inr_lin] at h1
          simp [keyFix] at h1
          cases fix with
          | false => rfl
          | true => simp at h1
      rw [hflag]
      exact hP.symm

private theorem evalRestr_eq_zero_iff {t : ℕ} (U : Submodule (ZMod 3) (PlaneRaw.V t))
    (j : Fin t) :
    PlaneRaw.evalRestr U j = 0 ↔ ∀ u : U, (u : PlaneRaw.V t) j = 0 := by
  constructor
  · intro h u
    have := congrArg (fun f => f u) h
    simpa [SpBlocks.evalRestr_apply'] using this
  · intro h
    ext u
    simpa [SpBlocks.evalRestr_apply'] using h u

theorem linExistsCodeOfIsPrimIdemIn_holds : LinExistsCodeOfIsPrimIdemIn := by
  intro K _ _ _ ζ t ε hK hζ U P hP
  obtain ⟨hPmem, hPidem, hPne, hPmin⟩ := hP
  obtain ⟨T, fix, heq, hT, hfix⟩ := exists_planeIdem_of_isIdempotentElem hK hζ t ε U hPmem hPidem
  by_cases hex : ∃ i ∈ T, PlaneRaw.evalRestr U i ≠ 0
  · obtain ⟨i, hi, hψi⟩ := hex
    obtain ⟨c, hc, hsupp⟩ := SpBlocks.exists_code_support_eq U i
    have hiS : i ∈ c.support := (hsupp i).2 (Or.inl rfl)
    have hcsupp : c.support ⊆ T := by
      intro j hj
      exact hT j i ((hsupp j).1 hj) hi
    have hcext : ∃ e, c = PlaneRaw.Code.extension e := by
      cases c with
      | zero S =>
          have hψ0 : PlaneRaw.evalRestr U i = 0 := by
            exact (evalRestr_eq_zero_iff U i).mpr ((hc i).mp hiS)
          exact absurd hψ0 hψi
      | extension e => exact ⟨e, rfl⟩
    obtain ⟨e, rfl⟩ := hcext
    have hidem_c : IsIdempotentElem (keyIdem t ε (.extension e) :
        Matrix (LinIdx t ε) (LinIdx t ε) K) := by
      exact isIdempotentElem_planeIdem t ε (PlaneRaw.Code.extSupport e) false
    have hne_c : (keyIdem t ε (.extension e) : Matrix (LinIdx t ε) (LinIdx t ε) K) ≠ 0 := by
      intro h0
      have h1 : (planeIdem t ε (PlaneRaw.Code.extSupport e) false :
          Matrix (LinIdx t ε) (LinIdx t ε) K)
          (Sum.inl (Sum.inl i)) (Sum.inl (Sum.inl i)) =
          if i ∈ PlaneRaw.Code.extSupport e then 1 else 0 :=
        planeIdem_inl_lin t ε (PlaneRaw.Code.extSupport e) false i
      have h0' : (planeIdem t ε (PlaneRaw.Code.extSupport e) false :
          Matrix (LinIdx t ε) (LinIdx t ε) K) = 0 := h0
      have hiS' : i ∈ PlaneRaw.Code.extSupport e := hiS
      rw [h0', Matrix.zero_apply, if_pos hiS'] at h1
      exact zero_ne_one h1
    have hmulP : keyIdem t ε (.extension e) * P = keyIdem t ε (.extension e) := by
      rw [heq]
      change (planeIdem t ε (PlaneRaw.Code.extSupport e) false :
          Matrix (LinIdx t ε) (LinIdx t ε) K) * planeIdem t ε T fix =
        planeIdem t ε (PlaneRaw.Code.extSupport e) false
      have hcsupp' : PlaneRaw.Code.extSupport e ⊆ T := hcsupp
      rw [planeIdem_mul, Finset.inter_eq_left.mpr hcsupp', Bool.false_and]
    have hmem_c : keyIdem t ε (.extension e) ∈
        Algebra.adjoin K (Units.val '' torusSet ζ t ε U) :=
      keyIdem_mem_adjoin (K := K) hK hζ t ε U (.extension e) hc
    rcases hPmin _ hmem_c hidem_c hmulP with h0 | hEq
    · exact absurd h0 hne_c
    · refine ⟨.extension e, hc, ?_, hEq.symm⟩
      simp only [keyDim]
      have hi' : i ∈ PlaneRaw.Code.extSupport e := hiS
      have hpos : 0 < (PlaneRaw.Code.extSupport e).card := Finset.card_pos.mpr ⟨i, hi'⟩
      omega
  · push Not at hex
    have hTzero : ∀ i ∈ T, PlaneRaw.evalRestr U i = 0 := hex
    rcases T.eq_empty_or_nonempty with hT0 | ⟨i, hi⟩
    · have hfix_true : fix = true := by
        by_contra hf
        have hf' : fix = false := by
          cases fix <;> simp_all
        rw [heq, hT0, hf', planeIdem_empty_false] at hPne
        exact hPne rfl
      have hε1 : ε.val = 1 := by
        by_contra hε
        have hε0 : ε.val = 0 := by omega
        rw [heq, hT0, hfix_true, planeIdem_fix_irrelevant t ε hε0 ∅ true false,
          planeIdem_empty_false] at hPne
        exact hPne rfl
      have hZ : commonZeros U = ∅ := by
        ext j
        simp only [Finset.notMem_empty, iff_false]
        intro hj
        have hψ : PlaneRaw.evalRestr U j = 0 :=
          (evalRestr_eq_zero_iff U j).mpr ((mem_commonZeros U j).mp hj)
        have := (hfix j hψ).2 hfix_true
        rw [hT0] at this
        simp at this
      refine ⟨.zero ∅, ?_, ?_, ?_⟩
      · intro j
        simp only [Finset.notMem_empty, false_iff]
        intro h
        have hj : j ∈ commonZeros U := (mem_commonZeros U j).mpr h
        rw [hZ] at hj
        simp at hj
      · simp only [keyDim]
        omega
      · rw [heq, hT0, hfix_true]
        rfl
    · have hfix_true : fix = true := by
        have hψ := hTzero i hi
        exact (hfix i hψ).1 hi
      have hTcommon : T = commonZeros U := by
        ext j
        constructor
        · intro hj
          exact (mem_commonZeros U j).mpr ((evalRestr_eq_zero_iff U j).mp (hTzero j hj))
        · intro hj
          have hψ : PlaneRaw.evalRestr U j = 0 :=
            (evalRestr_eq_zero_iff U j).mpr ((mem_commonZeros U j).mp hj)
          exact (hfix j hψ).2 hfix_true
      refine ⟨.zero (commonZeros U), ?_, ?_, ?_⟩
      · exact fun j => mem_commonZeros U j
      · simp only [keyDim]
        have hpos : 0 < (commonZeros U).card := by
          rw [← hTcommon]
          exact Finset.card_pos.mpr ⟨i, hi⟩
        omega
      · rw [heq, hTcommon, hfix_true]
        rfl

end

end CFSG.StandardType.GGQ2Frame.LinBlocks

end

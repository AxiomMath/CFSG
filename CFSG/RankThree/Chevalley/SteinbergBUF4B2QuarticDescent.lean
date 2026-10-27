module

public import CFSG.RankThree.Chevalley.SteinbergBUF4B2LeviProduct
public import CFSG.RankThree.SteinbergR3EEvenQuarticCoboundary
public import CFSG.LieType.Chevalley.GraphFixedHighestRoot
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2Faithful
public import CFSG.RankThree.Chevalley.SteinbergBNF4NativeB2Onto

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley Matrix SteinbergBN EvenQuartic
open CFSG.LocalAnalysis.ComponentInitial.FourGroupEvenCanonical
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {M : Type} [Field M]

theorem f4J0_eq_antiJ [CharP M 2] : f4J0 M = antiJ M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [f4J0, antiJ_apply, CharTwo.neg_eq]

theorem matrixIsometryGroup_f4J0_eq_spJ [CharP M 2] : matrixIsometryGroup (f4J0 M) = spJ M := by
  ext g
  rw [mem_matrixIsometryGroup, mem_spJ, f4J0_eq_antiJ]

theorem exists_word_f4B2 {ε : ℤ} (hε : ε = 1 ∨ ε = -1) :
    ∃ ω : List (Fin Tag.F4.rank),
      (coxeterSystem Tag.F4).wordProd ω = (simple Tag.F4 1 * simple Tag.F4 2) ^ ε ∧
        (ω = [1, 2] ∨ ω = [2, 1]) := by
  rcases hε with rfl | rfl
  · refine ⟨[1, 2], ?_, Or.inl rfl⟩
    rw [zpow_one, CoxeterSystem.wordProd_cons, CoxeterSystem.wordProd_singleton]
  · refine ⟨[2, 1], ?_, Or.inr rfl⟩
    rw [_root_.zpow_neg, zpow_one, _root_.mul_inv_rev, CoxeterSystem.wordProd_cons,
      CoxeterSystem.wordProd_singleton, simple, simple, CoxeterSystem.inv_simple,
      CoxeterSystem.inv_simple]

theorem canonicalRep_conj_eq_list_prod_conj [CharP M 2] {v : WeylGroup Tag.F4}
    {ω : List (Fin Tag.F4.rank)} {J : Set (Fin Tag.F4.rank)}
    (hv : ∀ k ∈ J, v • (Pi.single k 1 : Fin Tag.F4.rank → ℤ) =
      (coxeterSystem Tag.F4).wordProd ω • Pi.single k 1)
    {x : ModGL Tag.F4 M} (hx : x ∈ subsystemGroup Tag.F4 M J) :
    canonicalRep (coxeterSystem Tag.F4) M v * x * (canonicalRep (coxeterSystem Tag.F4) M v)⁻¹ =
      (ω.map fun i => weylElt Tag.F4 M i 1).prod * x *
        ((ω.map fun i => weylElt Tag.F4 M i 1).prod)⁻¹ := by
  have h2 : (2 : M) = 0 := CharTwo.two_eq_zero
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, c, rfl | rfl⟩ := hx
    · rw [← pinnedX_single, canonicalRep_mul_pinnedX_mul_inv_of_two h2 v (isRoot_single _ k),
        list_prod_weylElt_conj_pinnedX_of_charTwo ω (isRoot_single _ k), hv k hk]
    · rw [← pinnedX_neg_single,
        canonicalRep_mul_pinnedX_mul_inv_of_two h2 v (isRoot_neg_single _ k),
        list_prod_weylElt_conj_pinnedX_of_charTwo ω (isRoot_neg_single _ k), smul_neg, smul_neg,
        hv k hk]
  | one => simp
  | mul x y _ _ hx hy =>
    calc canonicalRep (coxeterSystem Tag.F4) M v * (x * y) *
          (canonicalRep (coxeterSystem Tag.F4) M v)⁻¹ =
        canonicalRep (coxeterSystem Tag.F4) M v * x *
            (canonicalRep (coxeterSystem Tag.F4) M v)⁻¹ *
          (canonicalRep (coxeterSystem Tag.F4) M v * y *
            (canonicalRep (coxeterSystem Tag.F4) M v)⁻¹) := by group
      _ = (ω.map fun i => weylElt Tag.F4 M i 1).prod * x *
            ((ω.map fun i => weylElt Tag.F4 M i 1).prod)⁻¹ *
          ((ω.map fun i => weylElt Tag.F4 M i 1).prod * y *
            ((ω.map fun i => weylElt Tag.F4 M i 1).prod)⁻¹) := by rw [hx, hy]
      _ = _ := by group
  | inv x _ hx =>
    calc canonicalRep (coxeterSystem Tag.F4) M v * x⁻¹ *
          (canonicalRep (coxeterSystem Tag.F4) M v)⁻¹ =
        (canonicalRep (coxeterSystem Tag.F4) M v * x *
          (canonicalRep (coxeterSystem Tag.F4) M v)⁻¹)⁻¹ := by group
      _ = ((ω.map fun i => weylElt Tag.F4 M i 1).prod * x *
          ((ω.map fun i => weylElt Tag.F4 M i 1).prod)⁻¹)⁻¹ := by rw [hx]
      _ = _ := by group

theorem list_prod_weylElt_mem_f4B2 {ω : List (Fin Tag.F4.rank)} (hω : ω = [1, 2] ∨ ω = [2, 1]) :
    (ω.map fun i => weylElt Tag.F4 M i 1).prod ∈ subsystemGroup Tag.F4 M {1, 2} := by
  refine list_prod_mem fun x hx => ?_
  obtain ⟨i, hi, rfl⟩ := List.mem_map.1 hx
  have hiJ : i = 1 ∨ i = 2 := by
    rcases hω with rfl | rfl
    · simpa using hi
    · simpa [or_comm] using hi
  exact weylElt_mem_subsystemGroup hiJ 1

theorem cyc4_symm_apply (i : Fin 4) : cyc4.symm i = ![2, 0, 3, 1] i := rfl

theorem blockMat_f4B2Weight_weylElt_one [CharP M 2] :
    blockMat f4B2Weight (weylElt Tag.F4 M 1 1) =
        !![1, 0, 0, 0; 0, 0, 1, 0; 0, 1, 0, 0; 0, 0, 0, 1] ∧
      blockMat f4B2Weight (weylElt Tag.F4 M 2 1) =
        !![0, 1, 0, 0; 1, 0, 0, 0; 0, 0, 0, 1; 0, 0, 1, 0] := by
  have hl := left_mem_pair (1 : Fin Tag.F4.rank) 2
  have hr := right_mem_pair (1 : Fin Tag.F4.rank) 2
  have hB := isSliceBlock_f4B2Weight
  constructor
  · rw [Blueprint.Chevalley.weylElt_eq_xUnit_mul, hB.blockMat_mul' (xUnit_mem_subsystemGroup hl _),
      hB.blockMat_mul' (yUnit_mem_subsystemGroup hl _), inv_one, Units.val_one,
      f4B2BlockMat_x1, f4B2BlockMat_y1, f4B2_weyl1, CharTwo.neg_eq]
  · rw [Blueprint.Chevalley.weylElt_eq_xUnit_mul, hB.blockMat_mul' (xUnit_mem_subsystemGroup hr _),
      hB.blockMat_mul' (yUnit_mem_subsystemGroup hr _), inv_one, Units.val_one,
      f4B2BlockMat_x2, f4B2BlockMat_y2, f4B2_weyl2, CharTwo.neg_eq]

theorem blockMat_f4B2Weight_word [CharP M 2] :
    blockMat f4B2Weight (([1, 2] : List (Fin Tag.F4.rank)).map fun i => weylElt Tag.F4 M i 1).prod =
        cyc4.permMatrix M ∧
      blockMat f4B2Weight
          (([2, 1] : List (Fin Tag.F4.rank)).map fun i => weylElt Tag.F4 M i 1).prod =
        (cyc4⁻¹).permMatrix M := by
  have hl := left_mem_pair (1 : Fin Tag.F4.rank) 2
  have hr := right_mem_pair (1 : Fin Tag.F4.rank) 2
  have hB := isSliceBlock_f4B2Weight
  obtain ⟨h1, h2⟩ := blockMat_f4B2Weight_weylElt_one (M := M)
  simp only [List.map_cons, List.map_nil, List.prod_cons, List.prod_nil, mul_one]
  constructor
  · rw [hB.blockMat_mul' (weylElt_mem_subsystemGroup hr 1), h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
        cyc4_apply]
  · rw [hB.blockMat_mul' (weylElt_mem_subsystemGroup hl 1), h1, h2]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_four, Equiv.Perm.permMatrix, PEquiv.toMatrix_apply,
        cyc4_inv_apply]

theorem cyc4_spJ_condition (R : Type) [CommRing R] :
    (cyc4.permMatrix R)ᵀ * antiJ R * cyc4.permMatrix R = antiJ R ∧
      ((cyc4⁻¹).permMatrix R)ᵀ * antiJ R * (cyc4⁻¹).permMatrix R = antiJ R := by
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Equiv.Perm.permMatrix, Matrix.mul_apply, Fin.sum_univ_four, PEquiv.toMatrix_apply,
        antiJ_apply, cyc4_apply, cyc4_symm_apply]
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Equiv.Perm.permMatrix, Matrix.mul_apply, Fin.sum_univ_four, PEquiv.toMatrix_apply,
        antiJ_apply, cyc4_apply, cyc4_inv_apply]

theorem cyc4_eq_conj_finRotate : cyc4 = Equiv.swap 2 3 * finRotate 4 * (Equiv.swap 2 3)⁻¹ := by
  ext i
  rw [Equiv.Perm.mul_apply, Equiv.Perm.mul_apply, Equiv.swap_inv, finRotate_apply]
  fin_cases i <;> simp [cyc4_apply, Equiv.swap_apply_def]

theorem cycleType_cyc4 : cyc4.cycleType = {4} ∧ (cyc4⁻¹).cycleType = {4} := by
  have h : cyc4.cycleType = {4} := by
    rw [cyc4_eq_conj_finRotate, Equiv.Perm.cycleType_conj]
    exact cycleType_finRotate (n := 2)
  exact ⟨h, by rw [Equiv.Perm.cycleType_inv, h]⟩

theorem rootSL2_single_mem_subsystemGroup [CharP M 2] {J : Set (Fin Tag.F4.rank)}
    {k : Fin Tag.F4.rank} (hk : k ∈ J) (A : SL2 M) :
    rootSL2 Tag.F4 M (Pi.single k 1) A ∈ subsystemGroup Tag.F4 M J := by
  have hA : A ∈ Subgroup.closure (Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Upper M) ∪
      Set.range (CFSG.LocalAnalysis.ComponentInitial.sl2Lower M)) := by
    rw [CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower]
    exact Subgroup.mem_top A
  induction hA using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with ⟨c, rfl⟩ | ⟨c, rfl⟩
    · change rootSL2 Tag.F4 M (Pi.single k 1) (uSL c) ∈ _
      rw [rootSL2_uSL_of_charTwo (isRoot_single _ k), pinnedX_single]
      exact xUnit_mem_subsystemGroup hk c
    · change rootSL2 Tag.F4 M (Pi.single k 1) (vSL c) ∈ _
      rw [rootSL2_vSL_of_charTwo (isRoot_single _ k), pinnedX_neg_single]
      exact yUnit_mem_subsystemGroup hk c
  | one => rw [map_one]; exact one_mem _
  | mul x y _ _ hx hy => rw [map_mul]; exact mul_mem hx hy
  | inv x _ hx => rw [map_inv]; exact inv_mem hx

theorem even_F4_native_B2_quartic_descent_and_full_Levi_direct_product
    (K : Type) [Field K] [Fintype K] [CharP K 2] (K₄ : Type) [Field K₄] [Algebra K K₄]
    [FiniteDimensional K K₄] (h4 : Module.finrank K K₄ = 4)
    (σ : K₄ ≃+* K₄) (hσ : ∀ b, σ b = b ^ Fintype.card K)
    (Z L : Subgroup (ModGL Tag.F4 K₄))
    (hZ : ∀ h, h ∈ Z ↔ h ∈ torusGroup Tag.F4 K₄ ∧ torusRootChar h (Pi.single 1 1) = 1 ∧
      torusRootChar h (Pi.single 2 1) = 1)
    (hL : L = torusGroup Tag.F4 K₄ ⊔ subsystemGroup Tag.F4 K₄ {1, 2})
    (v : WeylGroup Tag.F4) (ε : ℤ) (hε : ε = 1 ∨ ε = -1)
    (hv : ∀ α : Fin Tag.F4.rank → ℤ, α 0 = 0 → α 3 = 0 →
      v • α = ((simple Tag.F4 1 * simple Tag.F4 2) ^ ε) • α)
    (θ : ModGL Tag.F4 K₄ →* ModGL Tag.F4 K₄)
    (hθ : ∀ g, θ g = canonicalRep (coxeterSystem Tag.F4) K₄ v *
      Units.map (entrywiseHom σ.toRingHom) g * (canonicalRep (coxeterSystem Tag.F4) K₄ v)⁻¹) :
    (∃ e : Z × subsystemGroup Tag.F4 K₄ {1, 2} ≃* L,
      ∀ p, (e p : ModGL Tag.F4 K₄) = p.1 * p.2) ∧
    (Subgroup.center L).map L.subtype = Z ∧ Odd (Nat.card Z) ∧
    ∃ a ∈ subsystemGroup Tag.F4 K₄ {1, 2}, ∃ QK : Subgroup (ModGL Tag.F4 K₄),
      (∀ g, g ∈ QK ↔ ∃ y ∈ subsystemGroup Tag.F4 K {1, 2},
        g = a * baseChangeGL (algebraMap K K₄) y * a⁻¹) ∧
      subsystemGroup Tag.F4 K₄ {1, 2} ⊓ θ.eqLocus (MonoidHom.id _) = QK ∧
      Nonempty (QK ≃* spJ K) ∧
      L ⊓ θ.eqLocus (MonoidHom.id _) = (Z ⊓ θ.eqLocus (MonoidHom.id _)) ⊔ QK ∧
      (∃ e : ↥(Z ⊓ θ.eqLocus (MonoidHom.id _)) × QK ≃* ↥(L ⊓ θ.eqLocus (MonoidHom.id _)),
        ∀ p, (e p : ModGL Tag.F4 K₄) = p.1 * p.2) ∧
      ∀ A : SL2 K, a * rootSL2 Tag.F4 K₄ (Pi.single 1 1)
          (Matrix.SpecialLinearGroup.map (algebraMap K K₄) A) * a⁻¹ ∈
        subsystemGroup Tag.F4 K₄ {1, 2} ⊓ θ.eqLocus (MonoidHom.id _) := by
  classical
  have : CharP K₄ 2 := charP_of_injective_algebraMap (algebraMap K K₄).injective 2
  have : Finite K₄ := Module.finite_of_finite K
  refine ⟨exists_levi_prod_mulEquiv hZ hL, map_center_levi hZ hL, odd_card_char hZ, ?_⟩
  have hl := left_mem_pair (1 : Fin Tag.F4.rank) 2
  have hr := right_mem_pair (1 : Fin Tag.F4.rank) 2
  have hZL : Z ≤ L := (char_sup_subsystemGroup hZ hL) ▸ le_sup_left
  have hQL : subsystemGroup Tag.F4 K₄ {1, 2} ≤ L := (char_sup_subsystemGroup hZ hL) ▸ le_sup_right
  have hfixE : ∀ g, g ∈ θ.eqLocus (MonoidHom.id _) ↔ θ g = g := fun g => Iff.rfl
  obtain ⟨ω, hωw, hω⟩ := exists_word_f4B2 hε
  have hmQ := list_prod_weylElt_mem_f4B2 (M := K₄) hω
  have hvω : ∀ k ∈ ({1, 2} : Set (Fin Tag.F4.rank)), v • (Pi.single k 1 : Fin Tag.F4.rank → ℤ) =
      (coxeterSystem Tag.F4).wordProd ω • Pi.single k 1 := by
    intro k hk
    rw [hωw]
    rcases hk with rfl | rfl
    · exact hv _ rfl rfl
    · exact hv _ rfl rfl
  have hσQ : ∀ x ∈ subsystemGroup Tag.F4 K₄ {1, 2},
      Units.map (entrywiseHom σ.toRingHom) x ∈ subsystemGroup Tag.F4 K₄ {1, 2} := fun x hx =>
    baseChangeGL_mem_subsystemGroup σ.toRingHom hx
  have hθQ : ∀ x ∈ subsystemGroup Tag.F4 K₄ {1, 2}, θ x =
      (ω.map fun i => weylElt Tag.F4 K₄ i 1).prod * Units.map (entrywiseHom σ.toRingHom) x *
        ((ω.map fun i => weylElt Tag.F4 K₄ i 1).prod)⁻¹ := fun x hx => by
    rw [hθ, canonicalRep_conj_eq_list_prod_conj hvω (hσQ x hx)]
  have hθQmem : ∀ x ∈ subsystemGroup Tag.F4 K₄ {1, 2}, θ x ∈ subsystemGroup Tag.F4 K₄ {1, 2} :=
    fun x hx => by
      rw [hθQ x hx]
      exact mul_mem (mul_mem hmQ (hσQ x hx)) (inv_mem hmQ)
  have hθonto : ∀ y ∈ subsystemGroup Tag.F4 K₄ {1, 2},
      ∃ y' ∈ subsystemGroup Tag.F4 K₄ {1, 2}, θ y' = y := by
    intro y hy
    have hy' : Units.map (entrywiseHom σ.symm.toRingHom)
        (((ω.map fun i => weylElt Tag.F4 K₄ i 1).prod)⁻¹ * y *
          (ω.map fun i => weylElt Tag.F4 K₄ i 1).prod) ∈ subsystemGroup Tag.F4 K₄ {1, 2} :=
      baseChangeGL_mem_subsystemGroup σ.symm.toRingHom (mul_mem (mul_mem (inv_mem hmQ) hy) hmQ)
    refine ⟨_, hy', ?_⟩
    rw [hθQ _ hy', exactEntrywiseAut_right_inv]
    group
  have hθH : ∀ h ∈ torusGroup Tag.F4 K₄, θ h ∈ torusGroup Tag.F4 K₄ := fun h hh => by
    rw [hθ]
    exact (Subgroup.mem_normalizer_iff.1 (canonicalRep_mem_normalizer v) _).1
      (entrywise_mem_torusGroup (σ := σ) hh)
  have hθZ : ∀ z ∈ Z, θ z ∈ Z := by
    intro z hz
    have hθzH := hθH z (le_torusGroup_of_char hZ hz)
    have hcomm : ∀ y ∈ subsystemGroup Tag.F4 K₄ {1, 2}, θ z * y = y * θ z := by
      intro y hy
      obtain ⟨y', hy'Q, rfl⟩ := hθonto y hy
      rw [← map_mul, ← map_mul, commute_of_mem_char hZ hz hy'Q]
    exact (hZ _).2 ⟨hθzH,
      torusRootChar_eq_one_of_commute hθzH fun c => hcomm _ (xUnit_mem_subsystemGroup hl c),
      torusRootChar_eq_one_of_commute hθzH fun c => hcomm _ (xUnit_mem_subsystemGroup hr c)⟩
  have hrθ : ∀ x : subsystemGroup Tag.F4 K₄ {1, 2},
      ((f4B2Rep K₄ ⟨θ x, hθQmem x x.2⟩ : matrixIsometryGroup (f4J0 K₄)) : GL (Fin 4) K₄) =
        (f4B2Rep K₄ ⟨_, hmQ⟩ : GL (Fin 4) K₄) * glAut σ (f4B2Rep K₄ x : GL (Fin 4) K₄) *
          (f4B2Rep K₄ ⟨_, hmQ⟩ : GL (Fin 4) K₄)⁻¹ := by
    intro x
    have e : (⟨θ x, hθQmem x x.2⟩ : subsystemGroup Tag.F4 K₄ {1, 2}) =
        ⟨_, hmQ⟩ * ⟨_, hσQ x x.2⟩ * (⟨_, hmQ⟩ : subsystemGroup Tag.F4 K₄ {1, 2})⁻¹ :=
      Subtype.ext (hθQ x x.2)
    rw [e, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
    congr 2
    apply Units.ext
    rw [coe_glAut, coe_f4B2Rep, coe_f4B2Rep]
    exact blockMat_baseChangeGL σ.toRingHom isSliceBlock_f4B2Weight.isRoot _
  obtain ⟨π, hπ, hJπ, hπm⟩ : ∃ π : Equiv.Perm (Fin 4), π.cycleType = {4} ∧
      (π.permMatrix K)ᵀ * antiJ K * π.permMatrix K = antiJ K ∧
      (((f4B2Rep K₄ ⟨_, hmQ⟩ : matrixIsometryGroup (f4J0 K₄)) : GL (Fin 4) K₄) :
        Matrix (Fin 4) (Fin 4) K₄) = π.permMatrix K₄ := by
    rcases hω with rfl | rfl
    · exact ⟨cyc4, cycleType_cyc4.1, (cyc4_spJ_condition K).1,
        (blockMat_f4B2Weight_word (M := K₄)).1⟩
    · exact ⟨cyc4⁻¹, cycleType_cyc4.2, (cyc4_spJ_condition K).2,
        (blockMat_f4B2Weight_word (M := K₄)).2⟩
  obtain ⟨P, hPS, -, hPM, -, hfix⟩ :=
    even_quartic_symplectic_four_cycle_coboundary h4 σ hσ π hπ hJπ
  have hM₀ : ((f4B2Rep K₄ ⟨_, hmQ⟩ : matrixIsometryGroup (f4J0 K₄)) : GL (Fin 4) K₄) =
      P * (glAut σ P)⁻¹ := Units.ext (hπm.trans hPM)
  have hPS' : P ∈ matrixIsometryGroup (f4J0 K₄) := by
    rw [matrixIsometryGroup_f4J0_eq_spJ]
    exact hPS
  obtain ⟨a, ha⟩ := f4B2Rep_surjective (K := K₄) ⟨P, hPS'⟩
  have haP : ((f4B2Rep K₄ a : matrixIsometryGroup (f4J0 K₄)) : GL (Fin 4) K₄) = P := by rw [ha]
  have hbc : ∀ y : subsystemGroup Tag.F4 K {1, 2},
      ((f4B2Rep K₄ ⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K K₄) y.2⟩ :
          matrixIsometryGroup (f4J0 K₄)) : GL (Fin 4) K₄) =
        Matrix.GeneralLinearGroup.map (algebraMap K K₄)
          (f4B2Rep K y : GL (Fin 4) K) := by
    intro y
    ext i j
    rw [Matrix.GeneralLinearGroup.map_apply, coe_f4B2Rep, coe_f4B2Rep,
      blockMat_baseChangeGL _ isSliceBlock_f4B2Weight.isRoot, Matrix.map_apply]
  have hfixQ : ∀ g (hg : g ∈ subsystemGroup Tag.F4 K₄ {1, 2}), θ g = g ↔
      ∃ y ∈ subsystemGroup Tag.F4 K {1, 2}, g = a * baseChangeGL (algebraMap K K₄) y * a⁻¹ := by
    intro g hg
    have hgS : ((f4B2Rep K₄ ⟨g, hg⟩ : matrixIsometryGroup (f4J0 K₄)) : GL (Fin 4) K₄) ∈
        spJ K₄ := by
      rw [← matrixIsometryGroup_f4J0_eq_spJ]
      exact (f4B2Rep K₄ ⟨g, hg⟩).2
    have key : θ g = g ↔
        ((f4B2Rep K₄ ⟨θ g, hθQmem g hg⟩ : matrixIsometryGroup (f4J0 K₄)) : GL (Fin 4) K₄) =
          (f4B2Rep K₄ ⟨g, hg⟩ : GL (Fin 4) K₄) := by
      constructor
      · intro h
        have e : (⟨θ g, hθQmem g hg⟩ : subsystemGroup Tag.F4 K₄ {1, 2}) = ⟨g, hg⟩ :=
          Subtype.ext h
        rw [e]
      · intro h
        exact congrArg Subtype.val (f4B2Rep_injective (Subtype.ext h))
    rw [key, hrθ ⟨g, hg⟩, hM₀, hfix _ hgS]
    constructor
    · rintro ⟨h, hh, hgh⟩
      have hh' : h ∈ matrixIsometryGroup (f4J0 K) := by
        rw [matrixIsometryGroup_f4J0_eq_spJ]
        exact hh
      obtain ⟨y, hy⟩ := f4B2Rep_surjective (K := K) ⟨h, hh'⟩
      refine ⟨y, y.2, ?_⟩
      have hm : a * ⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K K₄) y.2⟩ * a⁻¹ =
          (⟨g, hg⟩ : subsystemGroup Tag.F4 K₄ {1, 2}) := by
        apply f4B2Rep_injective
        apply Subtype.ext
        rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          haP, hbc, hy, hgh]
      have hv := congrArg Subtype.val hm
      rw [Subgroup.coe_mul, Subgroup.coe_mul] at hv
      exact hv.symm
    · rintro ⟨y, hy, rfl⟩
      refine ⟨f4B2Rep K ⟨y, hy⟩, ?_, ?_⟩
      · rw [← matrixIsometryGroup_f4J0_eq_spJ]
        exact (f4B2Rep K ⟨y, hy⟩).2
      · have e : (⟨_, hg⟩ : subsystemGroup Tag.F4 K₄ {1, 2}) =
            a * ⟨_, baseChangeGL_mem_subsystemGroup (algebraMap K K₄) hy⟩ * a⁻¹ := rfl
        rw [e, map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv,
          haP]
        exact congrArg (fun X => P * X * P⁻¹) (hbc ⟨y, hy⟩)
  set φ : ModGL Tag.F4 K →* ModGL Tag.F4 K₄ :=
    (MulAut.conj (a : ModGL Tag.F4 K₄)).toMonoidHom.comp (baseChangeGL (algebraMap K K₄)) with hφ
  have hφinj : Function.Injective φ :=
    (MulAut.conj (a : ModGL Tag.F4 K₄)).injective.comp
      (baseChangeGL_injective (algebraMap K K₄))
  have hQK : ∀ g, g ∈ (subsystemGroup Tag.F4 K {1, 2}).map φ ↔
      ∃ y ∈ subsystemGroup Tag.F4 K {1, 2}, g = a * baseChangeGL (algebraMap K K₄) y * a⁻¹ := by
    intro g
    rw [Subgroup.mem_map]
    exact ⟨fun ⟨y, hy, hyg⟩ => ⟨y, hy, hyg.symm⟩, fun ⟨y, hy, hyg⟩ => ⟨y, hy, hyg.symm⟩⟩
  have hQfix : subsystemGroup Tag.F4 K₄ {1, 2} ⊓ θ.eqLocus (MonoidHom.id _) =
      (subsystemGroup Tag.F4 K {1, 2}).map φ := by
    ext g
    rw [Subgroup.mem_inf, hfixE, hQK]
    constructor
    · rintro ⟨hg, hfg⟩
      exact (hfixQ g hg).1 hfg
    · rintro ⟨y, hy, rfl⟩
      have hg : a * baseChangeGL (algebraMap K K₄) y * a⁻¹ ∈ subsystemGroup Tag.F4 K₄ {1, 2} :=
        mul_mem (mul_mem a.2 (baseChangeGL_mem_subsystemGroup _ hy)) (inv_mem a.2)
      exact ⟨hg, (hfixQ _ hg).2 ⟨y, hy, rfl⟩⟩
  have hQKQ : (subsystemGroup Tag.F4 K {1, 2}).map φ ≤ subsystemGroup Tag.F4 K₄ {1, 2} :=
    hQfix ▸ inf_le_left
  have hLfix : L ⊓ θ.eqLocus (MonoidHom.id _) =
      (Z ⊓ θ.eqLocus (MonoidHom.id _)) ⊔ (subsystemGroup Tag.F4 K {1, 2}).map φ := by
    refine le_antisymm ?_ (sup_le (inf_le_inf_right _ hZL)
      (hQfix ▸ inf_le_inf_right _ hQL))
    intro g hg
    obtain ⟨hgL, hgf⟩ := Subgroup.mem_inf.1 hg
    rw [hfixE] at hgf
    obtain ⟨z, hz, x, hx, rfl⟩ := exists_char_mul_of_mem_levi hZ hL hgL
    rw [map_mul] at hgf
    obtain ⟨hz', hx'⟩ := eq_of_char_mul_eq hZ (hθZ z hz) hz (hθQmem x hx) hx hgf
    refine mul_mem (Subgroup.mem_sup_left (Subgroup.mem_inf.2 ⟨hz, hz'⟩))
      (Subgroup.mem_sup_right ?_)
    rw [← hQfix]
    exact Subgroup.mem_inf.2 ⟨hx, hx'⟩
  refine ⟨a, a.2, (subsystemGroup Tag.F4 K {1, 2}).map φ, hQK, hQfix,
    ⟨((subsystemGroup Tag.F4 K {1, 2}).equivMapOfInjective φ hφinj).symm.trans
      ((MulEquiv.ofBijective (f4B2Rep K) ⟨f4B2Rep_injective, f4B2Rep_surjective⟩).trans
        (MulEquiv.subgroupCongr matrixIsometryGroup_f4J0_eq_spJ))⟩, hLfix,
    exists_prod_mulEquiv_of_commute (fun z hz x hx => commute_of_mem_char hZ hz.1 (hQKQ hx))
      ?_ hLfix.symm, fun A => ?_⟩
  · rw [eq_bot_iff, ← char_inf_subsystemGroup hZ]
    exact inf_le_inf inf_le_left hQKQ
  · rw [← baseChangeGL_rootSL2_of_charTwo (algebraMap K K₄) (isRoot_single _ 1), hQfix, hQK]
    exact ⟨_, rootSL2_single_mem_subsystemGroup hl A, rfl⟩

end CFSG.RankThree.Chevalley

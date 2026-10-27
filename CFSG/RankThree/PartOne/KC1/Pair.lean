module

public import CFSG.RankThree.PartOne.KE.E8A4Sigma
public import CFSG.RankThree.PartOne.KC1.Unitary

public noncomputable section

namespace CFSG.RankThree.PartOne.KC1

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KE
open CFSG.RankThree.E6 (chainRoot)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped MatrixGroups

set_option linter.unusedSectionVars false


section Rep

variable {L : Type} [Field L]

variable (L) in
@[expose] def wr (ω : List (Fin Tag.E8.rank)) : ModGL Tag.E8 L :=
  (ω.map fun i => weylElt Tag.E8 L i 1).prod

theorem wr_append (a b : List (Fin Tag.E8.rank)) : wr L (a ++ b) = wr L a * wr L b := by
  simp [wr, List.map_append, List.prod_append]

theorem wr_mem_monomial (ω : List (Fin Tag.E8.rank)) :
    wr L ω ∈ monomialSubgroup Tag.E8 L :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hg
    exact weylElt_mem_monomialSubgroup i

theorem wr_weylImage (ω : List (Fin Tag.E8.rank)) :
    weylQuotientHom Tag.E8 L ⟨wr L ω, wr_mem_monomial ω⟩ = (coxeterSystem Tag.E8).wordProd ω :=
  weylQuotientHom_eq (mapsRootLines_list_prod ω)

theorem units_map_entrywiseHom_weylElt_one (σ : L →+* L) (i : Fin Tag.E8.rank) :
    Units.map (entrywiseHom σ) (weylElt Tag.E8 L i 1) = weylElt Tag.E8 L i 1 := by
  rw [CFSG.Blueprint.Chevalley.weylElt_eq_xUnit_mul, map_mul, map_mul, units_map_entrywiseHom_xUnit,
    units_map_entrywiseHom_yUnit, inv_one, Units.val_one]
  simp only [map_one, map_neg]

theorem wr_fixed (σ : L →+* L) (ω : List (Fin Tag.E8.rank)) :
    Units.map (entrywiseHom σ) (wr L ω) = wr L ω := by
  unfold wr
  rw [map_list_prod, List.map_map]
  exact congrArg List.prod (List.map_congr_left fun i _ => units_map_entrywiseHom_weylElt_one σ i)

theorem wr_conj_pinnedX [CharP L 2] (ω : List (Fin Tag.E8.rank)) {β : Fin Tag.E8.rank → ℤ}
    (hβ : IsRoot Tag.E8 β) (c : L) :
    wr L ω * pinnedX Tag.E8 L β c * (wr L ω)⁻¹ =
      pinnedX Tag.E8 L ((coxeterSystem Tag.E8).wordProd ω • β) c :=
  list_prod_weylElt_conj_pinnedX_of_charTwo ω hβ c

theorem units_map_entrywiseHom_pinnedX (σ : L →+* L) (α : Fin Tag.E8.rank → ℤ) (c : L) :
    Units.map (entrywiseHom σ) (pinnedX Tag.E8 L α c) = pinnedX Tag.E8 L α (σ c) :=
  Units.ext (entrywise_pinnedX σ α c)

theorem e8rhoJ4_transvection_char2 [CharP L 2] {i j : Fin 5} (hij : i ≠ j) (t : L) :
    e8rhoJ4 L (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E8 L (chainRoot e8a4chain i j) t := by
  obtain ⟨e, he, h⟩ := e8a4RootFamily_all (K := L) i j hij
  have hee : ((e : ℤ) : L) * ((e : ℤ) : L) = 1 := by rcases he with rfl | rfl <;> simp
  have he1 : ((e : ℤ) : L) = 1 := by
    rcases he with rfl | rfl
    · simp
    · simp [CharTwo.neg_eq]
  have hmem := pinnedX_mem_e8a4Group (K := L) (e8a4chainRoot_mem_parabolicRoots hij)
    (((e : ℤ) : L) * t)
  have hrep : e8a4Rep L ⟨pinnedX Tag.E8 L (chainRoot e8a4chain i j) (((e : ℤ) : L) * t), hmem⟩ =
      Matrix.SpecialLinearGroup.transvection hij t := by
    apply Subtype.ext
    rw [coe_e8a4Rep, h, CFSG.LinearGroups.coe_transvection]
    congr 1
    rw [← mul_assoc, hee, one_mul]
  have h2 := e8rhoJ4_e8a4Rep hmem
  rw [hrep] at h2
  rw [h2, he1, one_mul]

variable (L) in
@[expose] def rhoW (ω : List (Fin Tag.E8.rank)) : SL(5, L) →* ModGL Tag.E8 L :=
  (MulAut.conj (wr L ω)).toMonoidHom.comp (e8rhoJ4 L)

theorem rhoW_apply (ω : List (Fin Tag.E8.rank)) (A : SL(5, L)) :
    rhoW L ω A = wr L ω * e8rhoJ4 L A * (wr L ω)⁻¹ := by
  simp [rhoW, MulAut.conj_apply]

theorem rhoW_injective (ω : List (Fin Tag.E8.rank)) : Function.Injective (rhoW L ω) :=
  (MulAut.conj (wr L ω)).injective.comp e8rhoJ4_injective

theorem rhoW_transvection [CharP L 2] (ω : List (Fin Tag.E8.rank)) {i j : Fin 5} (hij : i ≠ j)
    (t : L) :
    rhoW L ω (Matrix.SpecialLinearGroup.transvection hij t) =
      pinnedX Tag.E8 L ((coxeterSystem Tag.E8).wordProd ω • chainRoot e8a4chain i j) t := by
  rw [rhoW_apply, e8rhoJ4_transvection_char2 hij, wr_conj_pinnedX ω
    (e8a4chainRoot_mem_parabolicRoots hij).1]

theorem conj_wr_rhoW (a b : List (Fin Tag.E8.rank)) (A : SL(5, L)) :
    wr L a * rhoW L b A * (wr L a)⁻¹ = rhoW L (a ++ b) A := by
  rw [rhoW_apply, rhoW_apply, wr_append]
  group

theorem map_transvection5 (σ : L →+* L) {i j : Fin 5} (hij : i ≠ j) (t : L) :
    Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij (σ t) := by
  apply Subtype.ext
  ext a b
  simp only [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply,
    CFSG.LinearGroups.coe_transvection, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply,
    map_add]
  split_ifs <;> simp

theorem map_e8rhoJ4 [CharP L 2] (σ : L →+* L) (A : SL(5, L)) :
    Units.map (entrywiseHom σ) (e8rhoJ4 L A) = e8rhoJ4 L (Matrix.SpecialLinearGroup.map σ A) := by
  have h : (Units.map (entrywiseHom σ)).comp (e8rhoJ4 L) =
      (e8rhoJ4 L).comp (Matrix.SpecialLinearGroup.map σ) := by
    refine MonoidHom.eq_of_eqOn_dense
      (CFSG.LinearGroups.special_linear_elementary_generation (n := 5) (K := L)) ?_
    rintro _ ⟨i, j, hij, t, rfl⟩
    simp only [MonoidHom.comp_apply]
    rw [e8rhoJ4_transvection_char2 hij, units_map_entrywiseHom_pinnedX, map_transvection5 σ hij,
      e8rhoJ4_transvection_char2 hij]
  exact DFunLike.congr_fun h A

theorem map_rhoW [CharP L 2] (σ : L →+* L) (ω : List (Fin Tag.E8.rank)) (A : SL(5, L)) :
    Units.map (entrywiseHom σ) (rhoW L ω A) =
      rhoW L ω (Matrix.SpecialLinearGroup.map σ A) := by
  rw [rhoW_apply, rhoW_apply, map_mul, map_mul, map_inv, wr_fixed, map_e8rhoJ4]

theorem tauSL_transvection [CharP L 2] {i j : Fin 5} (hij : i ≠ j) (t : L) :
    tauSL (Matrix.SpecialLinearGroup.transvection hij t) =
      Matrix.SpecialLinearGroup.transvection hij.symm t := by
  apply Subtype.ext
  rw [coe_tauSL, Matrix.SpecialLinearGroup.transvection_inv, CFSG.LinearGroups.coe_transvection,
    CFSG.LinearGroups.coe_transvection, Matrix.transpose_add, Matrix.transpose_one,
    Matrix.transpose_single, CharTwo.neg_eq]

theorem chainRoot_swap (i j : Fin 5) :
    chainRoot e8a4chain j i = -chainRoot e8a4chain i j := by
  rw [e8a4chainRoot_eq_sub, e8a4chainRoot_eq_sub, neg_sub]

theorem rhoW_double [CharP L 2] {ww : List (Fin Tag.E8.rank)}
    (hsq : ∀ γ : Fin Tag.E8.rank → ℤ, (coxeterSystem Tag.E8).wordProd ww •
      ((coxeterSystem Tag.E8).wordProd ww • γ) = -γ) (ω : List (Fin Tag.E8.rank)) :
    rhoW L (ww ++ (ww ++ ω)) = (rhoW L ω).comp tauSL := by
  refine MonoidHom.eq_of_eqOn_dense
    (CFSG.LinearGroups.special_linear_elementary_generation (n := 5) (K := L)) ?_
  rintro _ ⟨i, j, hij, t, rfl⟩
  simp only [MonoidHom.comp_apply]
  rw [rhoW_transvection, tauSL_transvection hij, rhoW_transvection]
  rw [CoxeterSystem.wordProd_append, CoxeterSystem.wordProd_append, mul_smul, mul_smul, hsq,
    chainRoot_swap, smul_neg, neg_neg]

end Rep

section Datum

variable {L : Type} [Field L]

@[expose] def aVec (j : Fin Tag.E8.rank) : ℤ :=
  Tag.E8.cartan (e8Index 0) j + 2 * Tag.E8.cartan (e8Index 2) j + 3 * Tag.E8.cartan (e8Index 3) j +
    4 * Tag.E8.cartan (e8Index 4) j

@[expose] def phiExp (γ : Fin Tag.E8.rank → ℤ) : ℤ := ∑ j, aVec j * γ j

structure PairDatum (ww : List (Fin Tag.E8.rank)) where
  ω : List (Fin Tag.E8.rank)
  w : List (Fin Tag.E8.rank)
  c : ℕ
  hsq : ∀ γ : Fin Tag.E8.rank → ℤ, (coxeterSystem Tag.E8).wordProd ww •
    ((coxeterSystem Tag.E8).wordProd ww • γ) = -γ
  horth : ∀ i j k l : Fin 5, i ≠ j → k ≠ l →
    ((coxeterSystem Tag.E8).wordProd ω • chainRoot e8a4chain i j) ⬝ᵥ
      (Tag.E8.symmetrizedCartan *ᵥ ((coxeterSystem Tag.E8).wordProd (ww ++ ω) •
        chainRoot e8a4chain k l)) = 0
  hback : (coxeterSystem Tag.E8).wordProd (ww ++ ω) • ((coxeterSystem Tag.E8).wordProd w •
      (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ)) =
    (coxeterSystem Tag.E8).wordProd ω • (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ)
  hexp : ¬ (5 : ℤ) ∣ phiExp (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ) +
    (c : ℤ) * phiExp ((coxeterSystem Tag.E8).wordProd w •
      (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ))

end Datum

section Pair

variable {L : Type} [Field L] [CharP L 2] {ww : List (Fin Tag.E8.rank)}

theorem forall_of_elementary {G : Type*} [Group G] (f : SL(5, L) →* G) (S : Subgroup G)
    (h : ∀ T ∈ CFSG.LinearGroups.elementarySet 5 L, f T ∈ S) (A : SL(5, L)) : f A ∈ S := by
  have h1 : Subgroup.closure (CFSG.LinearGroups.elementarySet 5 L) ≤ S.comap f :=
    (Subgroup.closure_le _).2 fun T hT => h T hT
  rw [CFSG.LinearGroups.special_linear_elementary_generation] at h1
  exact h1 (Subgroup.mem_top A)

theorem PairDatum.comm (D : PairDatum ww) (A B : SL(5, L)) :
    rhoW L D.ω A * rhoW L (ww ++ D.ω) B = rhoW L (ww ++ D.ω) B * rhoW L D.ω A := by
  have hcomm := (CFSG.LieType.Chevalley.simply_laced_orthogonal_root_commutation Tag.E8
    (Or.inr (Or.inr (Or.inr rfl)))).2 L
  have hT : ∀ (i j k l : Fin 5) (hij : i ≠ j) (hkl : k ≠ l) (t s : L),
      rhoW L D.ω (Matrix.SpecialLinearGroup.transvection hij t) *
        rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.transvection hkl s) =
      rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.transvection hkl s) *
        rhoW L D.ω (Matrix.SpecialLinearGroup.transvection hij t) := by
    intro i j k l hij hkl t s
    rw [rhoW_transvection, rhoW_transvection]
    exact hcomm _ _ (IsRoot.smul (e8a4chainRoot_mem_parabolicRoots hij).1 _)
      (IsRoot.smul (e8a4chainRoot_mem_parabolicRoots hkl).1 _) (D.horth i j k l hij hkl) _
      (Subgroup.subset_closure (Set.mem_range_self t)) _
      (Subgroup.subset_closure (Set.mem_range_self s))
  have h1 : ∀ T ∈ CFSG.LinearGroups.elementarySet 5 L, ∀ B : SL(5, L),
      rhoW L (ww ++ D.ω) B ∈ Subgroup.centralizer {rhoW L D.ω T} := by
    rintro T ⟨i, j, hij, t, rfl⟩ B
    refine forall_of_elementary (rhoW L (ww ++ D.ω)) _ ?_ B
    rintro _ ⟨k, l, hkl, s, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    intro g hg
    rw [Set.mem_singleton_iff.1 hg]
    exact hT i j k l hij hkl t s
  have h2 : ∀ A : SL(5, L),
      rhoW L D.ω A ∈ Subgroup.centralizer (Set.range (rhoW L (ww ++ D.ω))) := by
    refine forall_of_elementary (rhoW L D.ω) _ ?_
    intro T hT'
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨B, rfl⟩
    have := Subgroup.mem_centralizer_iff.1 (h1 T hT' B) (rhoW L D.ω T) rfl
    exact this.symm
  have := Subgroup.mem_centralizer_iff.1 (h2 A) (rhoW L (ww ++ D.ω) B) ⟨B, rfl⟩
  exact this.symm

theorem rhoW_mem_adjoint (ω : List (Fin Tag.E8.rank)) (A : SL(5, L)) :
    rhoW L ω A ∈ adjointGroup Tag.E8 L := by
  rw [rhoW_apply]
  have h1 : wr L ω ∈ adjointGroup Tag.E8 L :=
    monomialSubgroup_le_adjointGroup' (wr_mem_monomial ω)
  have h2 : e8rhoJ4 L A ∈ adjointGroup Tag.E8 L := by
    have := e8rhoJ4_mem A
    rw [subsystemGroup_eq_rootSpan] at this
    exact rootSpan_le_adjointGroup L _ this
  exact mul_mem (mul_mem h1 h2) (inv_mem h1)

theorem conj_mem_torusGroup {n : ModGL Tag.E8 L} (hn : n ∈ monomialSubgroup Tag.E8 L)
    {h : ModGL Tag.E8 L} (hh : h ∈ torusGroup Tag.E8 L) : n * h * n⁻¹ ∈ torusGroup Tag.E8 L := by
  have hTN : torusGroup Tag.E8 L ≤ monomialSubgroup Tag.E8 L := le_sup_left
  have := (torusGroup_subgroupOf_monomialSubgroup_normal Tag.E8 L).conj_mem ⟨h, hTN hh⟩
    (Subgroup.mem_subgroupOf.2 hh) ⟨n, hn⟩
  exact Subgroup.mem_subgroupOf.1 this

theorem e8rhoJ4_diagonal_mem (A : SL(5, L))
    (hA : ∀ i j : Fin 5, i ≠ j → (A : Matrix (Fin 5) (Fin 5) L) i j = 0) :
    e8rhoJ4 L A ∈ torusGroup Tag.E8 L := by
  have h := rhoSigmaE8A4_diagonal (v := 1) A hA
  rwa [rhoSigmaE8A4_apply, canonicalRep_one, inv_one, one_mul, mul_one] at h

theorem rhoW_diagonal_mem (ω : List (Fin Tag.E8.rank)) (A : SL(5, L))
    (hA : ∀ i j : Fin 5, i ≠ j → (A : Matrix (Fin 5) (Fin 5) L) i j = 0) :
    rhoW L ω A ∈ torusGroup Tag.E8 L := by
  rw [rhoW_apply]
  exact conj_mem_torusGroup (wr_mem_monomial ω) (e8rhoJ4_diagonal_mem A hA)

variable (σ : L →+* L)

@[expose] def eVal (D : PairDatum ww) (A : SL(5, L)) : ModGL Tag.E8 L :=
  rhoW L D.ω A * rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ A)

@[expose] def eHom (D : PairDatum ww) : SL(5, L) →* ModGL Tag.E8 L :=
  MonoidHom.mk' (eVal σ D) fun A B => by
    unfold eVal
    rw [map_mul, map_mul, map_mul]
    calc rhoW L D.ω A * rhoW L D.ω B *
          (rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ A) *
            rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ B))
        = rhoW L D.ω A * (rhoW L D.ω B *
          rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ A)) *
            rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ B) := by group
      _ = rhoW L D.ω A * (rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ A) *
          rhoW L D.ω B) * rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ B) := by
        rw [D.comm B]
      _ = _ := by group

theorem eHom_apply (D : PairDatum ww) (A : SL(5, L)) :
    eHom σ D A = rhoW L D.ω A * rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ A) := rfl

theorem eHom_mem_adjoint (D : PairDatum ww) (A : SL(5, L)) :
    eHom σ D A ∈ adjointGroup Tag.E8 L := by
  rw [eHom_apply]
  exact mul_mem (rhoW_mem_adjoint _ _) (rhoW_mem_adjoint _ _)

theorem eHom_diagonal_mem (D : PairDatum ww) (A : SL(5, L))
    (hA : ∀ i j : Fin 5, i ≠ j → (A : Matrix (Fin 5) (Fin 5) L) i j = 0) :
    eHom σ D A ∈ torusGroup Tag.E8 L := by
  rw [eHom_apply]
  refine mul_mem (rhoW_diagonal_mem _ A hA) (rhoW_diagonal_mem _ _ fun i j hij => ?_)
  simp [Matrix.SpecialLinearGroup.map_apply_coe, hA i j hij]

theorem eHom_fixed (D : PairDatum ww) {A : SL(5, L)} (hA : A ∈ U (σ.comp σ)) :
    wr L ww * Units.map (entrywiseHom σ) (eHom σ D A) * (wr L ww)⁻¹ = eHom σ D A := by
  rw [eHom_apply, map_mul, map_rhoW, map_rhoW]
  calc wr L ww * (rhoW L D.ω (Matrix.SpecialLinearGroup.map σ A) *
        rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map σ A))) *
        (wr L ww)⁻¹
      = (wr L ww * rhoW L D.ω (Matrix.SpecialLinearGroup.map σ A) * (wr L ww)⁻¹) *
        (wr L ww * rhoW L (ww ++ D.ω)
          (Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map σ A)) * (wr L ww)⁻¹) := by
        group
    _ = rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ A) *
        rhoW L (ww ++ (ww ++ D.ω))
          (Matrix.SpecialLinearGroup.map σ (Matrix.SpecialLinearGroup.map σ A)) := by
        rw [conj_wr_rhoW, conj_wr_rhoW]
    _ = rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ A) * rhoW L D.ω A := by
        rw [rhoW_double D.hsq, MonoidHom.comp_apply, map_map_SL]
        have h := (mem_U_iff' (Fr₂ := σ.comp σ)).1 hA
        rw [h]
    _ = rhoW L D.ω A * rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ A) :=
        (D.comm A _).symm

end Pair

section Kernel

variable {L : Type} [Field L] [CharP L 2] {ww : List (Fin Tag.E8.rank)}

theorem rootChar_aVec (r : Lˣ) (γ : Fin Tag.E8.rank → ℤ) :
    rootChar (fun j => r ^ aVec j) γ = r ^ phiExp γ := by
  rw [rootChar, phiExp, ← Finset.prod_zpow_eq_zpow_sum]
  exact Finset.prod_congr rfl fun j _ => (_root_.zpow_mul _ _ _).symm

theorem e8rhoJ4_scalar (r : Lˣ) (hr : r ^ 5 = 1) (A : SL(5, L))
    (hA : (A : Matrix (Fin 5) (Fin 5) L) = Matrix.scalar (Fin 5) (r : L)) :
    e8rhoJ4 L A = rootDiagUnit Tag.E8 (fun j => r ^ aVec j) := by
  have hinv4 : (r ^ 4)⁻¹ = r := by
    apply inv_eq_of_mul_eq_one_right
    rw [← pow_succ, hr]
  have hrep : e8a4Rep L ⟨e8a4TorusElt r (r ^ 2) (r ^ 3) (r ^ 4),
      e8a4TorusElt_mem _ _ _ _⟩ = A := by
    apply Subtype.ext
    rw [coe_e8a4Rep, e8a4Mat_e8a4TorusElt, hA, Matrix.scalar_apply]
    congr 1
    funext i
    fin_cases i
    · rfl
    · show ((r⁻¹ * r ^ 2 : Lˣ) : L) = r
      rw [show r⁻¹ * r ^ 2 = r by group]
    · show (((r ^ 2)⁻¹ * r ^ 3 : Lˣ) : L) = r
      rw [show (r ^ 2)⁻¹ * r ^ 3 = r by group]
    · show (((r ^ 3)⁻¹ * r ^ 4 : Lˣ) : L) = r
      rw [show (r ^ 3)⁻¹ * r ^ 4 = r by group]
    · show (((r ^ 4)⁻¹ : Lˣ) : L) = r
      rw [hinv4]
  have hJ : e8rhoJ4 L A = e8a4TorusElt r (r ^ 2) (r ^ 3) (r ^ 4) := by
    rw [← hrep]
    exact e8rhoJ4_e8a4Rep (e8a4TorusElt_mem _ _ _ _)
  rw [hJ, e8a4TorusElt, torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit,
    torusElt_eq_rootDiagUnit, torusElt_eq_rootDiagUnit, ← rootDiagUnit_mul, ← rootDiagUnit_mul,
    ← rootDiagUnit_mul]
  congr 1
  funext j
  simp only [Pi.mul_apply, aVec, _root_.zpow_add]
  rw [← zpow_natCast, ← zpow_natCast, ← zpow_natCast]
  simp only [← _root_.zpow_mul]
  congr 3

theorem rhoW_scalar_conj_pinnedX (ω : List (Fin Tag.E8.rank)) (r : Lˣ) (hr : r ^ 5 = 1)
    (A : SL(5, L)) (hA : (A : Matrix (Fin 5) (Fin 5) L) = Matrix.scalar (Fin 5) (r : L))
    {γ : Fin Tag.E8.rank → ℤ} (hγ : IsRoot Tag.E8 γ) (s : L) :
    rhoW L ω A * pinnedX Tag.E8 L ((coxeterSystem Tag.E8).wordProd ω • γ) s * (rhoW L ω A)⁻¹ =
      pinnedX Tag.E8 L ((coxeterSystem Tag.E8).wordProd ω • γ)
        (((r ^ phiExp γ : Lˣ) : L) * s) := by
  rw [rhoW_apply, e8rhoJ4_scalar r hr A hA, ← wr_conj_pinnedX ω hγ s,
    ← wr_conj_pinnedX ω hγ (((r ^ phiExp γ : Lˣ) : L) * s)]
  have h := rootDiagUnit_conj_pinnedX (K := L) (τ := Tag.E8) (fun j => r ^ aVec j) hγ s
  rw [rootChar_aVec] at h
  rw [← h]
  group

theorem eHom_ker_trivial (D : PairDatum ww) (σ : L →+* L) {q : ℕ} (hσ : ∀ x, σ x = x ^ q)
    (hq : q % 5 = D.c) {A : SL(5, L)} (hA : eHom σ D A = 1) : A = 1 := by
  have hcent : ∀ B : SL(5, L), B * A = A * B := by
    intro B
    apply rhoW_injective D.ω
    rw [map_mul, map_mul]
    have h1 : rhoW L D.ω A = (rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ A))⁻¹ := by
      rw [eHom_apply] at hA
      exact eq_inv_of_mul_eq_one_left hA
    rw [h1]
    exact (show Commute (rhoW L D.ω B) (rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ A))
      from D.comm B _).inv_right.eq
  have hAc : A ∈ Subgroup.center SL(5, L) := Subgroup.mem_center_iff.2 hcent
  obtain ⟨r, hr, hsc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hAc
  rw [Fintype.card_fin] at hr
  by_contra hne
  have hr1 : r ≠ 1 := by
    rintro rfl
    apply hne
    apply Subtype.ext
    rw [← hsc]
    simp
  have hr0 : r ≠ 0 := by
    rintro rfl
    rw [zero_pow (by norm_num)] at hr
    exact zero_ne_one hr
  set u : Lˣ := Units.mk0 r hr0 with hu
  have hu5 : u ^ 5 = 1 := Units.ext (by simpa [hu] using hr)
  have hu1 : u ≠ 1 := fun h => hr1 (by simpa [hu] using congrArg Units.val h)
  have hscalar : (A : Matrix (Fin 5) (Fin 5) L) = Matrix.scalar (Fin 5) (u : L) := hsc.symm
  have he₁ : IsRoot Tag.E8 (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ) := IsRoot.basis _
  have hγ₂ : IsRoot Tag.E8 ((coxeterSystem Tag.E8).wordProd D.w •
      (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ)) := IsRoot.smul he₁ _
  set β : Fin Tag.E8.rank → ℤ := (coxeterSystem Tag.E8).wordProd D.ω •
    (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ) with hβ
  have hσu : ((u ^ q : Lˣ) : L) = σ (u : L) := by
    rw [hσ]
    simp
  have hA' : ((Matrix.SpecialLinearGroup.map σ A : SL(5, L)) : Matrix (Fin 5) (Fin 5) L) =
      Matrix.scalar (Fin 5) (((u ^ q : Lˣ)) : L) := by
    rw [Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, hscalar, hσu]
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [Matrix.scalar_apply, Matrix.diagonal_apply_ne _ hij]
  have hu5' : (u ^ q) ^ 5 = 1 := by rw [← pow_mul, mul_comm, pow_mul, hu5, one_pow]
  have h2 := rhoW_scalar_conj_pinnedX (ww ++ D.ω) (u ^ q) hu5' _ hA' hγ₂ (1 : L)
  rw [D.hback] at h2
  have h1 := rhoW_scalar_conj_pinnedX D.ω u hu5 A hscalar he₁
    ((((u ^ q) ^ phiExp ((coxeterSystem Tag.E8).wordProd D.w •
      (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ)) : Lˣ) : L) * 1)
  have hA1 : rhoW L D.ω A * rhoW L (ww ++ D.ω) (Matrix.SpecialLinearGroup.map σ A) = 1 := by
    rw [eHom_apply] at hA
    exact hA
  have key : ∀ (a b x y z : ModGL Tag.E8 L), a * b = 1 → b * x * b⁻¹ = y → a * y * a⁻¹ = z →
      x = z := by
    intro a b x y z hab hy hz
    have hb : b = a⁻¹ := eq_inv_of_mul_eq_one_right hab
    rw [← hz, ← hy, hb]
    group
  have h3 := key _ _ _ _ _ hA1 h2 h1
  have h4 := pinnedX_injective Tag.E8 L β h3
  have h5 : u ^ phiExp (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ) *
      (u ^ q) ^ phiExp ((coxeterSystem Tag.E8).wordProd D.w •
        (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ)) = 1 := by
    apply Units.ext
    simpa using h4.symm
  rw [← zpow_natCast u q, ← _root_.zpow_mul, ← _root_.zpow_add] at h5
  have hord : orderOf u = 5 := by
    have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
    exact orderOf_eq_prime hu5 hu1
  have h7 := orderOf_dvd_iff_zpow_eq_one.2 h5
  rw [hord] at h7
  obtain ⟨k, hk⟩ := h7
  have hq' : (q : ℤ) = 5 * ((q / 5 : ℕ) : ℤ) + (D.c : ℤ) := by omega
  apply D.hexp
  refine ⟨k - ((q / 5 : ℕ) : ℤ) * phiExp ((coxeterSystem Tag.E8).wordProd D.w •
    (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ)), ?_⟩
  push_cast at hk
  linear_combination hk - phiExp ((coxeterSystem Tag.E8).wordProd D.w •
    (Pi.single (e8Index 1) 1 : Fin Tag.E8.rank → ℤ)) * hq'

end Kernel

end CFSG.RankThree.PartOne.KC1

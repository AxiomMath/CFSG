module

public import CFSG.HardMathSupport.Solomon.Coordinator.LieComp.LinearInner
public import CFSG.RankThree.PartTwo.Sec4.Ronan148SRows
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
public import CFSG.HardMathSupport.Solomon.Coordinator.LieSemisimple.D4Graph.Transfer
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3Orbit
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionLift

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148H

open Polynomial CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.HardMathSupport.Solomon.Coordinator
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartOne.KCPrimary (primaryFactors primaryMultiplicity primaryComponent)
open CFSG.Assembly.RankThreeEven (projSL projSU)

theorem center_specialLinearGroup_two_eq_bot (E : Type*) [Field E] [CharP E 2] {m : ℕ}
    (hm : m = 2) : Subgroup.center (Matrix.SpecialLinearGroup (Fin m) E) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin, hm] at hr
  have hr1 : r = 1 := by
    have h1 : (r - 1) ^ 2 = 0 := by
      have h2 : (2 : E) = 0 := CharTwo.two_eq_zero
      calc (r - 1) ^ 2 = r ^ 2 - 1 - 2 * (r - 1) := by ring
        _ = 0 := by rw [hr, h2]; ring
    exact sub_eq_zero.mp (pow_eq_zero_iff (by norm_num) |>.mp h1)
  rw [Subgroup.mem_bot]
  ext i j
  rw [← hrA, hr1]
  simp [Matrix.scalar_apply, Matrix.one_apply]

theorem exists_eq_smul_of_three_le {k : Type*} [Field k] {x : Module.End k (Fin 3 → k)}
    (hsq : Squarefree (minpoly k x)) {h : k[X]} (hh : h ∈ primaryFactors x)
    (hm : 3 ≤ primaryMultiplicity x h) : ∃ r : k, x = r • (1 : Module.End k (Fin 3 → k)) := by
  classical
  have hsum := CFSG.RankThree.PartOne.KCPrimary.finrank_eq_sum_degree_mul_multiplicity hsq
  rw [Module.finrank_fin_fun] at hsum
  rw [Finset.sum_coe_sort (primaryFactors x)
    (fun a : k[X] => a.natDegree * primaryMultiplicity x a)] at hsum
  have hpos : ∀ a ∈ primaryFactors x, 1 ≤ a.natDegree * primaryMultiplicity x a := by
    intro a ha
    have hd : 1 ≤ a.natDegree :=
      Irreducible.natDegree_pos (CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors ha)
    have : Fact (Irreducible a) :=
      ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors ha⟩
    have hne := CFSG.RankThree.PartOne.KCPrimary.primaryComponent_ne_bot hsq ha
    have hm1 : 1 ≤ primaryMultiplicity x a := by
      rw [Nat.one_le_iff_ne_zero]
      intro h0
      apply hne
      exact Submodule.finrank_eq_zero.mp
        (by
          have h1 := CFSG.RankThree.PartOne.KCPrimary.finrank_primaryComponent x a
          rw [h1]
          change a.natDegree * primaryMultiplicity x a = 0
          rw [h0, mul_zero])
    exact Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega))
  have hdh : 1 ≤ h.natDegree :=
    Irreducible.natDegree_pos (CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors hh)
  have hth : 3 ≤ h.natDegree * primaryMultiplicity x h :=
    le_trans hm (Nat.le_mul_of_pos_left _ hdh)
  have hsplit := Finset.add_sum_erase (primaryFactors x)
    (fun a : k[X] => a.natDegree * primaryMultiplicity x a) hh
  have hrest : (primaryFactors x).erase h = ∅ := by
    by_contra hne
    obtain ⟨b, hb⟩ := Finset.nonempty_iff_ne_empty.mpr hne
    have hb1 := hpos b (Finset.mem_of_mem_erase hb)
    have hle : b.natDegree * primaryMultiplicity x b ≤
        ∑ a ∈ (primaryFactors x).erase h, a.natDegree * primaryMultiplicity x a :=
      Finset.single_le_sum (f := fun a : k[X] => a.natDegree * primaryMultiplicity x a)
        (fun _ _ => Nat.zero_le _) hb
    omega
  have hset : primaryFactors x = {h} := by
    rw [← Finset.insert_erase hh, hrest]
    rfl
  have h3 : h.natDegree * primaryMultiplicity x h = 3 := by
    rw [hrest, Finset.sum_empty, add_zero] at hsplit
    omega
  have hd1 : h.natDegree = 1 := by
    rcases Nat.lt_or_ge h.natDegree 2 with hlt | hge
    · omega
    · have : 6 ≤ h.natDegree * primaryMultiplicity x h := Nat.mul_le_mul hge hm
      omega
  have hmin : minpoly k x = h := by
    rw [← CFSG.RankThree.PartOne.KCPrimary.prod_primaryFactors hsq, hset, Finset.prod_singleton]
  have hmon : (minpoly k x).Monic := minpoly.monic (Algebra.IsIntegral.isIntegral x)
  have hX := hmon.eq_X_add_C (by rw [hmin, hd1])
  refine ⟨-(minpoly k x).coeff 0, ?_⟩
  have haev := minpoly.aeval k x
  rw [hX, map_add, aeval_X, aeval_C, Algebra.algebraMap_eq_smul_one] at haev
  exact (eq_neg_of_add_eq_zero_left haev).trans (neg_smul _ _).symm

section L3

variable {k : Type} [Field k] [Finite k]

theorem exists_lift_conjAut {s : LinearFlag.projectiveSL 3 k} (hs3 : s ^ 3 = 1) :
    ∃ (A' : Matrix.SpecialLinearGroup (Fin 3) k) (c : kˣ), LinearFlag.proj 3 k A' = s ∧
      Matrix.SpecialLinearGroup.toGL A' ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c ∧
      fixSubgroup (LinearFlag.conjAut 3 k (Matrix.SpecialLinearGroup.toGL A')) =
        Subgroup.centralizer {s} := by
  obtain ⟨A', rfl⟩ := LinearFlag.proj_surjective 3 k s
  set A : GL (Fin 3) k := Matrix.SpecialLinearGroup.toGL A' with hAdef
  have hA'3 : A' ^ 3 ∈ LinearFlag.scalars 3 k :=
    LinearFlag.proj_eq_one_iff.mp (by rw [map_pow, hs3])
  obtain ⟨c, -, hc⟩ := hA'3
  have hA : A ^ 3 = Matrix.GeneralLinearGroup.scalar (Fin 3) c := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, hAdef, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    rw [← Matrix.SpecialLinearGroup.coe_pow, hc]
    rfl
  have hconj : LinearFlag.conjAut 3 k A = MulAut.conj (LinearFlag.proj 3 k A') := by
    ext x
    obtain ⟨g, rfl⟩ := LinearFlag.proj_surjective 3 k x
    rw [LinearFlag.conjAut_proj, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    apply Subtype.ext
    rw [LinearFlag.coe_slConjugation, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul]
    have hinv : ((A⁻¹ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) =
        ((A'⁻¹ : Matrix.SpecialLinearGroup (Fin 3) k) : Matrix (Fin 3) (Fin 3) k) := by
      rw [hAdef, ← map_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
    rw [hinv, hAdef, Matrix.SpecialLinearGroup.coe_GL_coe_matrix]
  refine ⟨A', c, rfl, hA, ?_⟩
  ext x
  rw [mem_fixSubgroup, hconj, MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro hx
    calc x * LinearFlag.proj 3 k A' =
        LinearFlag.proj 3 k A' * x * (LinearFlag.proj 3 k A')⁻¹ * LinearFlag.proj 3 k A' := by
          rw [hx]
      _ = LinearFlag.proj 3 k A' * x := by group
  · intro hx
    rw [← hx]
    group

theorem center_map_proj_eq_bot {n : ℕ} {F : Subgroup (Matrix.SpecialLinearGroup (Fin n) k)}
    (hF : Subgroup.center ↥F = ⊥) : Subgroup.center ↥(F.map (LinearFlag.proj n k)) = ⊥ := by
  rw [eq_bot_iff]
  rintro ⟨z, g, hgF, rfl⟩ hz
  rw [Subgroup.mem_bot]
  have hgc : (⟨g, hgF⟩ : ↥F) ∈ Subgroup.center ↥F := by
    rw [Subgroup.mem_center_iff]
    intro y
    apply Subtype.ext
    have hzy := congrArg Subtype.val ((Subgroup.mem_center_iff.mp hz)
      ⟨LinearFlag.proj n k y, y, y.2, rfl⟩)
    simp only [Subgroup.coe_mul] at hzy
    set w : Matrix.SpecialLinearGroup (Fin n) k := (y : Matrix.SpecialLinearGroup (Fin n) k) * g *
      (y : Matrix.SpecialLinearGroup (Fin n) k)⁻¹ * g⁻¹ with hw
    have hwproj : LinearFlag.proj n k w = 1 := by
      rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, hzy]
      group
    have hwZ : w ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) k) :=
      LinearFlag.scalars_le_center n k (LinearFlag.proj_eq_one_iff.mp hwproj)
    have hwF : w ∈ F := by
      rw [hw]
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ y.2 hgF)
        (Subgroup.inv_mem _ y.2)) (Subgroup.inv_mem _ hgF)
    have hwc : (⟨w, hwF⟩ : ↥F) ∈ Subgroup.center ↥F := by
      rw [Subgroup.mem_center_iff]
      intro z'
      exact Subtype.ext ((Subgroup.mem_center_iff.mp hwZ) z')
    rw [hF, Subgroup.mem_bot] at hwc
    have hw1 : w = 1 := congrArg Subtype.val hwc
    rw [hw] at hw1
    change (y : Matrix.SpecialLinearGroup (Fin n) k) * g = g * (y : Matrix.SpecialLinearGroup (Fin n) k)
    calc (y : Matrix.SpecialLinearGroup (Fin n) k) * g =
        (y : Matrix.SpecialLinearGroup (Fin n) k) * g *
          (y : Matrix.SpecialLinearGroup (Fin n) k)⁻¹ * g⁻¹ *
            (g * (y : Matrix.SpecialLinearGroup (Fin n) k)) := by group
      _ = g * (y : Matrix.SpecialLinearGroup (Fin n) k) := by rw [hw1, one_mul]
  rw [hF, Subgroup.mem_bot] at hgc
  apply Subtype.ext
  change LinearFlag.proj n k g = 1
  rw [show g = 1 from congrArg Subtype.val hgc, map_one]

variable [CharP k 2]

theorem center_eq_bot_of_isComponentOf {s : LinearFlag.projectiveSL 3 k} (hs : orderOf s = 3)
    {J : Subgroup (LinearFlag.projectiveSL 3 k)}
    (hJ : CFSG.Open.IsComponentOf J (Subgroup.centralizer {s})) : Subgroup.center ↥J = ⊥ := by
  have hs3 : s ^ 3 = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs] at h
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    norm_num at hs
  obtain ⟨A', c, rfl, hA, hfix⟩ := exists_lift_conjAut hs3
  have hpk : ((3 : ℕ) : k) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff k 2 3).mp h
    norm_num at this
  rw [← hfix] at hJ
  obtain ⟨h, hJeq⟩ := LieComp.linear_inner_components hpk hA J hJ
  have hsq := LieSemisimple.squarefree_minpoly_glA hpk hA
  have hm2 : primaryMultiplicity
      (LieSemisimple.glA (Matrix.SpecialLinearGroup.toGL A') : Module.End k (Fin 3 → k))
        h.1.1 = 2 := by
    have hnot3 : ¬ 3 ≤ primaryMultiplicity
        (LieSemisimple.glA (Matrix.SpecialLinearGroup.toGL A') : Module.End k (Fin 3 → k))
          h.1.1 := by
      intro h3
      obtain ⟨r, hr⟩ := exists_eq_smul_of_three_le hsq h.1.2 h3
      apply hs1
      rw [LinearFlag.proj_eq_one_iff]
      have hmat : (A' : Matrix (Fin 3) (Fin 3) k) = Matrix.scalar (Fin 3) r := by
        have h1 : ((LieSemisimple.glA (Matrix.SpecialLinearGroup.toGL A') :
            LinearMap.GeneralLinearGroup k (Fin 3 → k)) : Module.End k (Fin 3 → k)) =
              Matrix.toLin' (A' : Matrix (Fin 3) (Fin 3) k) := rfl
        rw [h1] at hr
        apply Matrix.toLin'.injective
        rw [hr, Matrix.scalar_apply, ← Matrix.smul_one_eq_diagonal, map_smul, Matrix.toLin'_one]
        rfl
      have hr0 : r ≠ 0 := by
        intro h0
        have hdet := A'.2
        rw [hmat, h0, map_zero, Matrix.det_zero] at hdet
        exact zero_ne_one hdet
      refine ⟨Units.mk0 r hr0, ?_, by rw [hmat]; rfl⟩
      have hdet := A'.2
      rw [hmat, Matrix.scalar_apply, Matrix.det_diagonal, Finset.prod_const, Finset.card_univ,
        Fintype.card_fin] at hdet
      ext
      rw [Units.val_pow_eq_pow_val, Units.val_mk0, hdet, Units.val_one]
    rcases h.2 with h3 | ⟨h2, -⟩
    · exact absurd h3 hnot3
    · omega
  have : Fact (Irreducible h.1.1) :=
    ⟨CFSG.RankThree.PartOne.KCPrimary.irreducible_of_mem_primaryFactors h.1.2⟩
  have : CharP (AdjoinRoot h.1.1) 2 :=
    charP_of_injective_algebraMap (algebraMap k (AdjoinRoot h.1.1)).injective 2
  obtain ⟨e⟩ := LieComp.nonempty_mulEquiv_specialFactor hsq h.1.2
  have hZF : Subgroup.center
      ↥(LieSemisimple.specialFactor (Matrix.SpecialLinearGroup.toGL A') h.1.1) = ⊥ := by
    rw [← Subgroup.map_center_eq e, center_specialLinearGroup_two_eq_bot _ hm2,
      Subgroup.map_bot]
  rw [hJeq]
  exact center_map_proj_eq_bot hZF

theorem noCC425_projectiveSL_three : Ronan148S.NoCC425 (LinearFlag.projectiveSL 3 k) := by
  intro s K hcc
  have hcomp : CFSG.Open.IsComponentOf K (Subgroup.centralizer {s}) :=
    ⟨hcc.le_centralizer,
      Ronan148L.open_isSubnormal_of_subgroupOf hcc.le_centralizer hcc.isSubnormal,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open _).1
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).2
          hcc.isQuasisimple)⟩
  have hZ := center_eq_bot_of_isComponentOf hcc.orderOf_eq hcomp
  have hsZ : (⟨s, hcc.mem⟩ : ↥K) ∈ Subgroup.center ↥K := by
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hcc.le_centralizer y.2))
  rw [hZ, Subgroup.mem_bot] at hsZ
  have := hcc.orderOf_eq
  rw [show s = 1 from congrArg Subtype.val hsZ, orderOf_one] at this
  norm_num at this

theorem false_of_quasisimple_le_centralizer {s : LinearFlag.projectiveSL 3 k} (hs : orderOf s = 3)
    {K : Subgroup (LinearFlag.projectiveSL 3 k)} (hK : CFSG.IsQuasisimple ↥K) (hsK : s ∈ K)
    (hKC : K ≤ Subgroup.centralizer {s}) : False := by
  have hs3 : s ^ 3 = 1 := by
    have h := pow_orderOf_eq_one s
    rwa [hs] at h
  have hs1 : s ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hs
    norm_num at hs
  obtain ⟨A', c, hA's, hA, hfix⟩ := exists_lift_conjAut hs3
  have hpk : ((3 : ℕ) : k) ≠ 0 := by
    intro h
    have := (CharP.cast_eq_zero_iff k 2 3).mp h
    norm_num at this
  have hperf : ⁅K, K⁆ = K := Subgroup.isPerfect_iff.mp hK.1
  have hlay := LieSemisimple.perfectInLayer_conjAut hpk hA K (hfix ▸ hKC) hperf
  rw [hfix] at hlay
  set C := Subgroup.centralizer ({s} : Set (LinearFlag.projectiveSL 3 k)) with hC
  have hsC : s ∈ C := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  obtain ⟨w, hw, hws⟩ := LieSemisimple.glaLayer_le_map_layer C (hlay hsK)
  have hw1 : w = 1 := by
    refine CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.Bal3.eq_one_of_central_in_layer
      (fun K' hK' => ?_) hw fun x _ => ?_
    · have hmap := CFSG.LocalAnalysis.RankThreeTheoremC.isComponentOf_map_subtype hK'
      have hZ := center_eq_bot_of_isComponentOf hs hmap
      rw [← Subgroup.map_center_eq (K'.equivMapOfInjective C.subtype C.subtype_injective).symm,
        hZ, Subgroup.map_bot]
    · apply Subtype.ext
      rw [Subgroup.coe_mul, Subgroup.coe_mul]
      have hws' : ((w : ↥C) : LinearFlag.projectiveSL 3 k) = s := hws
      rw [hws']
      exact Subgroup.mem_centralizer_singleton_iff.mp x.2
  apply hs1
  rw [← hws, hw1]
  rfl

omit [Field k] [Finite k] [CharP k 2] in
theorem projSU_le_projSL (n : ℕ) [Fact (Nat.Prime 2)] :
    projSU 3 2 n ≤ projSL 3 (GaloisField 2 (2 * n)) := by
  unfold CFSG.PGLModel.projSU CFSG.PGLModel.projSL CFSG.PGLModel.projImage
  apply Subgroup.map_mono
  rw [Subgroup.closure_le]
  rintro A ⟨hdet, -⟩
  exact hdet

section Row


omit [Field k] [Finite k] [CharP k 2] in
theorem rowOf425_projSL_three_two (n : ℕ) (hn : 1 ≤ n) :
    Ronan148S.RowOf425 (projSL 3 (GaloisField 2 n)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_projSL_mulEquiv 3 (GaloisField 2 n)
  refine Ronan148S.rowOf425_of_noCC fun S _ _ _ _ ⟨e⟩ => ?_
  exact Ronan148S.NoCC425.of_mulEquiv (e.trans τ) noCC425_projectiveSL_three

omit [Field k] [Finite k] [CharP k 2] in
theorem rowOf425_projSU_three_two (n : ℕ) (hn : 1 ≤ n) :
    Ronan148S.RowOf425 (projSU 3 2 n) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨τ⟩ := CFSG.RankThree.PartTwo.KFacts.nonempty_projSL_mulEquiv 3 (GaloisField 2 (2 * n))
  refine Ronan148S.rowOf425_of_noCC fun S _ _ _ _ ⟨e⟩ => ?_
  let f : S →* LinearFlag.projectiveSL 3 (GaloisField 2 (2 * n)) :=
    τ.toMonoidHom.comp ((Subgroup.inclusion (projSU_le_projSL n)).comp e.toMonoidHom)
  have hf : Function.Injective f :=
    τ.injective.comp ((Subgroup.inclusion_injective (projSU_le_projSL n)).comp e.injective)
  intro s K hcc
  have hfs : orderOf (f s) = 3 := by rw [orderOf_injective f hf s]; exact hcc.orderOf_eq
  refine false_of_quasisimple_le_centralizer hfs (K := K.map f) ?_ ⟨s, hcc.mem, rfl⟩ ?_
  · exact CFSG.LocalCores.isQuasisimple_of_mulEquiv (K.equivMapOfInjective f hf)
      hcc.isQuasisimple
  · rintro _ ⟨y, hy, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
      Subgroup.mem_centralizer_singleton_iff.mp (hcc.le_centralizer hy)]

end Row

end L3

end CFSG.RankThree.PartTwo.Sec4.Ronan148H

module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148TEvenL3
public import Certificates.Certificate43
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
public import CFSG.RankThree.FFModules.Transvections
import CFSG.StronglyEmbedded
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Borel
import CFSG.StronglyEmbedded.BenderBorelTransport
import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma114Models
import CFSG.Dihedral.DisconnectedInvolutionGraph.StrongEmbedding
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderAutOmega
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderInvBasic
import CFSG.LocalAnalysis.ShultStronglyClosedTI.RankOneModelTransport
import CFSG.Walter.PSL2Facts.Even
import CFSG.RankThree.PartTwo.Sec16.KL3SubProofMain
import CFSG.RankThree.PartOne.SolD3.SzSpecial
import CFSG.RankThree.PartTwo.KFacts.K72Centralizer
import CFSG.RankThree.SubgroupLists.LinearTwoFamily
import CFSG.Timmesfeld.Orders.Bang
import CFSG.CGT.PushingUp.BenderBridge
import CFSG.FeitThompson.OddOrderTheorem
public import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
import CFSG.ClassicalInvolution.WeakCT.StandardPair
import CFSG.LieType.CurtisTits.SpecialLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
import CFSG.RankThree.PartOne.CTP.SeitzLinear
import CFSG.RankThree.PartOne.KC.LinearCommutatorOdd
import CFSG.RankThree.PartOne.KC.LinearDegreeFive
import CFSG.RankThree.PartOne.KC.PlaneReductionGeneral
import CFSG.RankThree.PartOne.S11d.OutLinear
import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148T

open CFSG CFSG.RankThree Matrix Module
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSU)
open CFSG.RankThree.FFModules (transvectionGroup mem_transvectionGroup subOne subOne_eq_zero_iff
  range_subOne_le le_ker_subOne exists_le_transvectionGroup finrank_fin3 mulVec_mulVec_inv
  mulVec_inv_mulVec)
open scoped MatrixGroups

theorem card_center_dvd_three_of_scalar {F : Type} [Field F] [Finite F]
    {D : Subgroup (GL (Fin 3) F)} (hZ3 : ∀ z ∈ Subgroup.center D, z ^ 3 = 1)
    (hcomm : ∀ M : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) * M = M * g) → ∃ c : F, M = Matrix.scalar (Fin 3) c) :
    Nat.card (Subgroup.center D) ∣ 3 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hP : IsPGroup 3 (Subgroup.center D) := fun z => ⟨1, by
    rw [pow_one]
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hZ3 z z.2⟩
  obtain ⟨j, hj⟩ := hP.exists_card_eq
  have hscal : ∀ z : Subgroup.center D, (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.scalar (Fin 3) ((((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0) := by
    intro z
    obtain ⟨c, hc⟩ := hcomm (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) fun g hg => by
      have h1 := Subgroup.mem_center_iff.mp z.2 ⟨g, hg⟩
      have h2 := congrArg (fun x : D => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h1
      simpa using h2
    rw [hc]
    simp
  have hroot : ∀ z : Subgroup.center D, (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 ∈
      (Polynomial.nthRoots 3 (1 : F)).toFinset := by
    intro z
    rw [Multiset.mem_toFinset, Polynomial.mem_nthRoots (by norm_num)]
    have h3 : (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
      have h1 := hZ3 z z.2
      have h2 := congrArg (fun x : D => ((x : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) h1
      simpa using h2
    rw [hscal z, ← map_pow] at h3
    have h4 := congrFun (congrFun h3 0) 0
    simpa using h4
  let f : Subgroup.center D → (Polynomial.nthRoots 3 (1 : F)).toFinset := fun z => ⟨_, hroot z⟩
  have hf : Function.Injective f := by
    intro z z' h
    have h1 : (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 =
        (((z' : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) 0 0 := congrArg Subtype.val h
    have h2 : (((z : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = (((z' : D) : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [hscal z, hscal z', h1]
    exact Subtype.ext (Subtype.ext (Units.ext h2))
  have hle : Nat.card (Subgroup.center D) ≤ 3 := by
    calc Nat.card (Subgroup.center D)
        ≤ Nat.card (Polynomial.nthRoots 3 (1 : F)).toFinset := Nat.card_le_card_of_injective f hf
      _ = (Polynomial.nthRoots 3 (1 : F)).toFinset.card := by
          rw [Nat.card_eq_fintype_card, Fintype.card_coe]
      _ ≤ Multiset.card (Polynomial.nthRoots 3 (1 : F)) := Multiset.toFinset_card_le _
      _ ≤ 3 := Polynomial.card_nthRoots 3 1
  rw [hj] at hle ⊢
  have hj1 : j ≤ 1 := by
    by_contra h
    have : 3 ^ 2 ≤ 3 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  exact (pow_dvd_pow 3 hj1).trans (by norm_num)

theorem isCyclic_sylow_of_mulEquiv_degen {X Y : Type*} [Group X] [Group Y] [Finite X] {p : ℕ}
    [Fact p.Prime] (e : X ≃* Y) (hY : ∀ S : Sylow p Y, IsCyclic S) (S : Sylow p X) :
    IsCyclic S := by
  have h : IsCyclic ((S : Subgroup X).map e.toMonoidHom) :=
    hY (S.mapSurjective (f := e.toMonoidHom) e.surjective)
  exact isCyclic_of_surjective
    ((S : Subgroup X).equivMapOfInjective e.toMonoidHom e.injective).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem commute_trans_of_degenerate {G : Type*} [Group G]
    (hdeg : ∀ x y : G, x ^ 2 = 1 → y ^ 2 = 1 → x * y = y * x ∨ Odd (orderOf (x * y)))
    {s t u : G} (hs : s ^ 2 = 1) (ht : orderOf t = 2) (hu : u ^ 2 = 1)
    (hst : s * t = t * s) (htu : t * u = u * t) : s * u = u * s := by
  by_contra hsu
  have hodd : Odd (orderOf (s * u)) := (hdeg s u hs hu).resolve_left hsu
  have ht2 : t ^ 2 = 1 := by rw [← ht, pow_orderOf_eq_one]
  have hv : (s * t) ^ 2 = 1 := by
    rw [Commute.mul_pow hst 2, hs, ht2, one_mul]
  have hcomm : Commute t (s * u) := by
    show t * (s * u) = s * u * t
    rw [← mul_assoc, ← hst, mul_assoc, htu, ← mul_assoc]
  have hord : orderOf (t * (s * u)) = 2 * orderOf (s * u) := by
    rw [hcomm.orderOf_mul_eq_mul_orderOf_of_coprime (by rw [ht]; exact Nat.coprime_two_left.mpr hodd),
      ht]
  rcases hdeg (s * t) u hv hu with h | h
  · apply hsu
    have h1 : s * t * u = s * u * t := by rw [mul_assoc, htu, ← mul_assoc]
    have h2 : u * (s * t) = u * s * t := by rw [mul_assoc]
    exact mul_right_cancel (h1.symm.trans (h.trans h2))
  · have heq : s * t * u = t * (s * u) := by rw [hst, mul_assoc]
    rw [heq, hord] at h
    exact (Nat.not_even_iff_odd.mpr h) (even_two_mul _)

theorem exists_isStronglyEmbeddedOrder_of_degenerate {G : Type*} [Group G] [Finite G]
    (hs : IsSimpleGroup G) (hnab : ∃ a b : G, a * b ≠ b * a)
    (hdeg : ∀ x y : G, x ^ 2 = 1 → y ^ 2 = 1 → x * y = y * x ∨ Odd (orderOf (x * y))) :
    ∃ M : Subgroup G, CFSG.BenderSuzuki.IsStronglyEmbeddedOrder M := by
  classical
  have hsq : ∀ x : G, orderOf x = 2 → x ^ 2 = 1 := fun x hx => by rw [← hx, pow_orderOf_eq_one]
  have hdisc : ¬ (CFSG.Open.disconnectedInvolutionCommutingGraph G).Preconnected := by
    intro hconn
    have hwalk : ∀ (a b : {t : G // orderOf t = 2})
        (_ : (CFSG.Open.disconnectedInvolutionCommutingGraph G).Walk a b),
        (a : G) * b = b * a := by
      intro a b w
      induction w with
      | nil => rfl
      | @cons a c b hadj p ih =>
        obtain ⟨-, hc⟩ :=
          (CFSG.DisconnectedInvolutionGraph.Helpers.involutionGraph_adj_iff a c).mp hadj
        exact commute_trans_of_degenerate hdeg (hsq _ a.2) c.2 (hsq _ b.2) hc ih
    have hall : ∀ t u : G, orderOf t = 2 → orderOf u = 2 → t * u = u * t := by
      intro t u ht hu
      obtain ⟨w⟩ := hconn ⟨t, ht⟩ ⟨u, hu⟩
      exact hwalk _ _ w
    have h2 : 2 ∣ Nat.card G := by
      by_contra hodd
      have hoddG : Odd (Nat.card G) := Nat.odd_iff.mpr (by omega)
      exact not_isSolvable_of_simple hs hnab (CFSG.FeitThompson.isSolvable_of_odd_natCard _ hoddG)
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' 2 h2
    set C := Group.conjugatesOfSet ({t} : Set G) with hC
    have hgen : ∀ x ∈ C, orderOf x = 2 := by
      intro x hx
      obtain ⟨b, hb, hbx⟩ := Group.mem_conjugatesOfSet_iff.mp hx
      rw [Set.mem_singleton_iff] at hb
      subst hb
      obtain ⟨c, rfl⟩ := isConj_iff.mp hbx
      rw [← MulAut.conj_apply, MulEquiv.orderOf_eq]
      exact ht
    have h1 : Subgroup.normalClosure ({t} : Set G) ≤ Subgroup.centralizer C := by
      change Subgroup.closure C ≤ _
      rw [Subgroup.closure_le]
      intro x hx
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro y hy
      exact hall y x (hgen y hy) (hgen x hx)
    have hNcomm : ∀ x ∈ Subgroup.normalClosure ({t} : Set G),
        ∀ y ∈ Subgroup.normalClosure ({t} : Set G), x * y = y * x := by
      intro x hx y hy
      have h3 : Subgroup.normalClosure ({t} : Set G) ≤ Subgroup.centralizer {x} := by
        change Subgroup.closure C ≤ _
        rw [Subgroup.closure_le]
        intro z hz
        rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
        intro w hw
        rw [Set.mem_singleton_iff] at hw
        subst hw
        exact ((Subgroup.mem_centralizer_iff.mp (h1 hx)) z hz).symm
      exact Subgroup.mem_centralizer_iff.mp (h3 hy) x (Set.mem_singleton x)
    rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.normalClosure ({t} : Set G)) with h | h
    · have htN : t ∈ Subgroup.normalClosure ({t} : Set G) :=
        Subgroup.subset_normalClosure (Set.mem_singleton t)
      rw [h, Subgroup.mem_bot] at htN
      rw [htN, orderOf_one] at ht
      norm_num at ht
    · obtain ⟨a, b, hab⟩ := hnab
      exact hab (hNcomm a (h ▸ Subgroup.mem_top a) b (h ▸ Subgroup.mem_top b))
  obtain ⟨M, hM1, hM2, hM3⟩ :=
    CFSG.DisconnectedInvolutionGraph.Helpers.disconnected_exists_stronglyEmbedded hdisc
  refine ⟨M, hM1, hM2, fun g hg => ?_⟩
  have heq : M.map (MulAut.conj g).toMonoidHom =
      CFSG.DisconnectedInvolutionGraph.Helpers.conjugateSubgroup M g := by
    ext x
    simp only [Subgroup.mem_map, CFSG.DisconnectedInvolutionGraph.Helpers.conjugateSubgroup,
      Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨y, hy, rfl⟩
      have e : g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y := by group
      rw [e]
      exact hy
    · intro hx
      exact ⟨g⁻¹ * x * g⁻¹⁻¹, hx, by group⟩
  rw [heq]
  exact hM3 g hg

theorem degenerate_quotient {D : Type*} [Group D] (hZ3 : ∀ z ∈ Subgroup.center D, z ^ 3 = 1)
    (hdeg : ∀ s t : D, s ^ 2 = 1 → t ^ 2 = 1 → s * t = t * s ∨ Odd (orderOf (s * t))) :
    ∀ x y : D ⧸ Subgroup.center D, x ^ 2 = 1 → y ^ 2 = 1 →
      x * y = y * x ∨ Odd (orderOf (x * y)) := by
  have hlift : ∀ x : D ⧸ Subgroup.center D, x ^ 2 = 1 →
      ∃ s : D, s ^ 2 = 1 ∧ (s : D ⧸ Subgroup.center D) = x := by
    intro x hx
    induction x using QuotientGroup.induction_on with
    | H d =>
      refine ⟨d ^ 3, ?_, ?_⟩
      · have hd2 : d ^ 2 ∈ Subgroup.center D := by
          rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow]
          exact hx
        have h6 := hZ3 _ hd2
        rw [← pow_mul] at h6 ⊢
        rw [show 3 * 2 = 2 * 3 by norm_num]
        exact h6
      · rw [QuotientGroup.mk_pow, pow_succ, hx, one_mul]
  intro x y hx hy
  obtain ⟨s, hs, rfl⟩ := hlift x hx
  obtain ⟨t, ht, rfl⟩ := hlift y hy
  rcases hdeg s t hs ht with h | h
  · left
    rw [← QuotientGroup.mk_mul, h, QuotientGroup.mk_mul]
  · right
    rw [← QuotientGroup.mk_mul]
    exact h.of_dvd_nat (orderOf_map_dvd (QuotientGroup.mk' (Subgroup.center D)) (s * t))

section Transvection

variable {F : Type} [Field F]

theorem conj_mem_transvectionGroup {S : Submodule F (Fin 3 → F)} {t : SL(3, F)}
    (ht : t ∈ transvectionGroup S) (g : SL(3, F)) :
    g * t * g⁻¹ ∈ transvectionGroup (S.map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F))) := by
  rw [mem_transvectionGroup]
  refine ⟨?_, fun v => ?_⟩
  · rintro _ ⟨w, hw, rfl⟩
    rw [Matrix.toLin'_apply, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, mulVec_inv_mulVec, ht.1 w hw]
  · refine ⟨(t : Matrix (Fin 3) (Fin 3) F) *ᵥ (((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v) -
      ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ v, ht.2 _, ?_⟩
    rw [Matrix.toLin'_apply, Matrix.mulVec_sub, mulVec_mulVec_inv,
      Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]

theorem eq_of_mem_transvectionGroup {S S' : Submodule F (Fin 3 → F)} {g : SL(3, F)} (hg : g ≠ 1)
    (hS : g ∈ transvectionGroup S) (hS' : g ∈ transvectionGroup S')
    (hdim : finrank F S = 1 ∨ finrank F S = 2) (hdim' : finrank F S' = finrank F S) : S' = S := by
  have h0 : subOne g ≠ 0 := fun h => hg ((subOne_eq_zero_iff g).mp h)
  rcases hdim with h1 | h2
  · have key : ∀ T : Submodule F (Fin 3 → F), g ∈ transvectionGroup T → finrank F T = 1 →
        T = LinearMap.range (subOne g) := by
      intro T hT hT1
      symm
      apply Submodule.eq_of_le_of_finrank_le (range_subOne_le hT)
      rw [hT1]
      apply Nat.one_le_iff_ne_zero.mpr
      intro hr
      apply h0
      rw [Submodule.finrank_eq_zero, LinearMap.range_eq_bot] at hr
      exact hr
    rw [key S' hS' (hdim'.trans h1), key S hS h1]
  · have key : ∀ T : Submodule F (Fin 3 → F), g ∈ transvectionGroup T → finrank F T = 2 →
        T = LinearMap.ker (subOne g) := by
      intro T hT hT2
      apply Submodule.eq_of_le_of_finrank_le (le_ker_subOne hT)
      rw [hT2]
      have hlt := Submodule.finrank_lt (s := LinearMap.ker (subOne g))
        (fun h => h0 (LinearMap.ker_eq_top.mp h))
      rw [finrank_fin3] at hlt
      omega
    rw [key S' hS' (hdim'.trans h2), key S hS h2]

theorem finrank_map_toLin' (S : Submodule F (Fin 3 → F)) (g : SL(3, F)) :
    finrank F (S.map (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F))) = finrank F S := by
  have hinj : Function.Injective (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F)) := by
    intro v w h
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply] at h
    have h1 := congrArg (fun x => ((g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ x) h
    simpa only [mulVec_inv_mulVec] using h1
  exact (LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj S)).symm

theorem map_toLin'_mul (S : Submodule F (Fin 3 → F)) (g h : SL(3, F)) :
    S.map (Matrix.toLin' ((g * h : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) =
      (S.map (Matrix.toLin' (h : Matrix (Fin 3) (Fin 3) F))).map
        (Matrix.toLin' (g : Matrix (Fin 3) (Fin 3) F)) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.toLin'_mul, Submodule.map_comp]

end Transvection

theorem false_of_psl2 {F : Type} [Field F] [Finite F] [CharP F 2]
    {D : Subgroup (GL (Fin 3) F)} (hdet : ∀ x ∈ D, (x : Matrix (Fin 3) (Fin 3) F).det = 1)
    (hirr : SubgroupLists.IsIrreducibleOn D) {n : ℕ} (hn : 2 ≤ n)
    (χ : D ≃* PSL(2, GaloisField 2 n)) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite (PSL(2, GaloisField 2 n)) := Finite.of_equiv D χ.toEquiv
  have hB : CFSG.Open.fusionBenderBorel D (2 ^ n) 1 :=
    (CFSG.Open.bender_psl2_borel_full n hn).map_mulEquiv χ.symm
  obtain ⟨T⟩ : Nonempty (Sylow 2 D) := inferInstance
  obtain ⟨hSE, -, hZ2, hZq, hTq⟩ := hB T
  rw [pow_one] at hTq
  have hZT : Subgroup.center (T : Subgroup D) = ⊤ :=
    (Subgroup.card_eq_iff_eq_top _).mp (hZq.trans hTq.symm)
  have hT2 : ∀ x ∈ (T : Subgroup D), x ^ 2 = 1 := by
    intro x hx
    have h1 := hZ2 ⟨x, hx⟩ (hZT ▸ Subgroup.mem_top _)
    have h2 := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h2
  have hTc : ∀ x ∈ (T : Subgroup D), ∀ y ∈ (T : Subgroup D), x * y = y * x := by
    intro x hx y hy
    have h1 := Subgroup.mem_center_iff.mp
      (hZT ▸ Subgroup.mem_top (⟨y, hy⟩ : (T : Subgroup D))) ⟨x, hx⟩
    exact congrArg Subtype.val h1
  have hcard : Nat.card (Sylow 2 D) = Nat.card (T : Subgroup D) + 1 := by
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.card_sylow_eq_of_mulEquiv χ 2,
      CFSG.Walter.psl2_even_card_sylow (by omega), hTq]
  obtain ⟨T₁, hT₁⟩ : ∃ T₁ : Sylow 2 D, T₁ ≠ T := by
    by_contra h
    push Not at h
    have hsub : Subsingleton (Sylow 2 D) := ⟨fun a b => (h a).trans (h b).symm⟩
    have h1 := Finite.card_le_one_iff_subsingleton.mpr hsub
    have h2 : 0 < Nat.card (T : Subgroup D) := Nat.card_pos
    omega
  obtain ⟨g₁, hg₁⟩ := MulAction.exists_smul_eq D T T₁
  have htrans : ∀ x : D, x • T = T ∨ ∃ r ∈ (T : Subgroup D), x • T = (r * g₁) • T := by
    intro x
    by_cases hx : x • T = T
    · exact Or.inl hx
    · obtain ⟨r, hr, hrx⟩ :=
        CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.exists_smul_eq hSE hcard hT₁ hx
      exact Or.inr ⟨r, hr, by rw [mul_smul, hg₁, hrx]⟩
  let ι : D →* SL(3, F) :=
    { toFun := fun g => ⟨((g : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F), hdet g g.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hιinj : Function.Injective ι := by
    intro a b h
    have h1 := congrArg (fun x : SL(3, F) => (x : Matrix (Fin 3) (Fin 3) F)) h
    exact Subtype.ext (Units.ext h1)
  have hTbot : (T : Subgroup D) ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hTq
    have : 2 ^ 2 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    omega
  obtain ⟨t₀, ht₀, ht₀1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hTbot
  have hB2 : ∀ b ∈ (T : Subgroup D).map ι, b * b = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_mul, ← pow_two, hT2 x hx, map_one]
  have hBc : ∀ b ∈ (T : Subgroup D).map ι, ∀ c ∈ (T : Subgroup D).map ι, b * c = c * b := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hTc x hx y hy]
  have hB0 : (T : Subgroup D).map ι ≠ ⊥ := by
    intro h
    have h1 : ι t₀ ∈ (T : Subgroup D).map ι := ⟨t₀, ht₀, rfl⟩
    rw [h, Subgroup.mem_bot] at h1
    exact ht₀1 (hιinj (h1.trans (map_one ι).symm))
  obtain ⟨S, hSdim, hBS⟩ := exists_le_transvectionGroup hB2 hBc hB0
  have hTS : ∀ r ∈ (T : Subgroup D), ι r ∈ transvectionGroup S := fun r hr => hBS ⟨r, hr, rfl⟩
  let σ : D → Submodule F (Fin 3 → F) := fun x =>
    S.map (Matrix.toLin' ((ι x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F))
  have hσmul : ∀ x y : D, σ (x * y) =
      (σ y).map (Matrix.toLin' ((ι x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) := by
    intro x y
    change S.map (Matrix.toLin' ((ι (x * y) : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) = _
    rw [map_mul]
    exact map_toLin'_mul S (ι x) (ι y)
  have hσone : σ 1 = S := by
    change S.map (Matrix.toLin' ((ι 1 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) = S
    rw [map_one, Matrix.SpecialLinearGroup.coe_one, Matrix.toLin'_one, Submodule.map_id]
  have hσdim : ∀ x : D, finrank F (σ x) = finrank F S := fun x => finrank_map_toLin' S (ι x)
  have hσconj : ∀ x : D, ∀ t ∈ (T : Subgroup D), ι (x * t * x⁻¹) ∈ transvectionGroup (σ x) := by
    intro x t ht
    rw [map_mul, map_mul, map_inv]
    exact conj_mem_transvectionGroup (hTS t ht) (ι x)
  have hσwd : ∀ x y : D, x • T = y • T → σ x = σ y := by
    intro x y hxy
    have hmem : x * t₀ * x⁻¹ ∈ ((y • T : Sylow 2 D) : Subgroup D) := by
      rw [← hxy, CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff]
      have e : x⁻¹ * (x * t₀ * x⁻¹) * x = t₀ := by group
      rw [e]
      exact ht₀
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff] at hmem
    have he : y * (y⁻¹ * (x * t₀ * x⁻¹) * y) * y⁻¹ = x * t₀ * x⁻¹ := by group
    have h1 := hσconj x t₀ ht₀
    have h2 := hσconj y _ hmem
    rw [he] at h2
    have hne : ι (x * t₀ * x⁻¹) ≠ 1 := by
      intro h
      apply ht₀1
      have h3 := hιinj (h.trans (map_one ι).symm)
      calc t₀ = x⁻¹ * (x * t₀ * x⁻¹) * x := by group
        _ = 1 := by rw [h3]; group
    exact (eq_of_mem_transvectionGroup hne h1 h2 (hσdim x ▸ hSdim)
      ((hσdim y).trans (hσdim x).symm)).symm
  have hσT : ∀ x : D, σ x = S ∨ ∃ r ∈ (T : Subgroup D),
      σ x = (σ g₁).map (Matrix.toLin' ((ι r : SL(3, F)) : Matrix (Fin 3) (Fin 3) F)) := by
    intro x
    rcases htrans x with h | ⟨r, hr, h⟩
    · left
      rw [hσwd x 1 (h.trans (one_smul D T).symm), hσone]
    · right
      exact ⟨r, hr, by rw [hσwd x (r * g₁) h, hσmul]⟩
  rcases hSdim with h1 | h2
  ·
    set W := S ⊔ σ g₁ with hW
    have hσW : ∀ x : D, σ x ≤ W := by
      intro x
      rcases hσT x with h | ⟨r, hr, h⟩
      · rw [h]
        exact le_sup_left
      · rw [h]
        rintro _ ⟨w, hw, rfl⟩
        have hrw : Matrix.toLin' ((ι r : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) w =
            (((ι r : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) *ᵥ w - w) + w := by
          rw [Matrix.toLin'_apply]
          abel
        rw [hrw]
        exact W.add_mem (Submodule.mem_sup_left ((hTS r hr).2 w)) (Submodule.mem_sup_right hw)
    have hWinv : ∀ g ∈ D, ∀ w ∈ W, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w ∈ W := by
      intro g hg w hw
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hw
      rw [Matrix.mulVec_add]
      refine W.add_mem (hσW ⟨g, hg⟩ ⟨a, ha, Matrix.toLin'_apply _ _⟩) ?_
      have hb' : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ b ∈ σ (⟨g, hg⟩ * g₁) := by
        rw [hσmul]
        exact ⟨b, hb, Matrix.toLin'_apply _ _⟩
      exact hσW _ hb'
    rcases hirr W hWinv with h | h
    · have hS0 : S = ⊥ := le_bot_iff.mp (h ▸ le_sup_left)
      rw [hS0, finrank_bot] at h1
      omega
    · have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (σ g₁)
      rw [← hW, h, finrank_top, finrank_fin3, hσdim, h1] at hsum
      omega
  ·
    set L := S ⊓ σ g₁ with hL
    have hLσ : ∀ x : D, L ≤ σ x := by
      intro x
      rcases hσT x with h | ⟨r, hr, h⟩
      · rw [h]
        exact inf_le_left
      · rw [h]
        intro v hv
        refine ⟨v, hv.2, ?_⟩
        rw [Matrix.toLin'_apply]
        exact (hTS r hr).1 v hv.1
    have hLinv : ∀ g ∈ D, ∀ v ∈ L, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ L := by
      intro g hg v hv
      have hx : ∀ y : D, (g : Matrix (Fin 3) (Fin 3) F) *ᵥ v ∈ σ (⟨g, hg⟩ * y) := by
        intro y
        rw [hσmul]
        exact ⟨v, hLσ y hv, Matrix.toLin'_apply _ _⟩
      refine ⟨?_, ?_⟩
      · have h3 := hx (⟨g, hg⟩ : D)⁻¹
        rwa [mul_inv_cancel, hσone] at h3
      · have h3 := hx ((⟨g, hg⟩ : D)⁻¹ * g₁)
        rwa [← mul_assoc, mul_inv_cancel, one_mul] at h3
    rcases hirr L hLinv with h | h
    · have hsum := Submodule.finrank_sup_add_finrank_inf_eq S (σ g₁)
      rw [← hL, h, finrank_bot, hσdim, h2] at hsum
      have hle : finrank F ↥(S ⊔ σ g₁) ≤ 3 := by
        have h3 := Submodule.finrank_le (S ⊔ σ g₁)
        rwa [finrank_fin3] at h3
      omega
    · have hS : S = ⊤ := top_le_iff.mp (h ▸ inf_le_left)
      have h3 : finrank F ↥(⊤ : Submodule F (Fin 3 → F)) = 3 := by
        rw [finrank_top, finrank_fin3]
      rw [← hS, h2] at h3
      omega

theorem not_three_dvd_card_suzuki {n : ℕ} (hn : 1 ≤ n) :
    ¬ 3 ∣ Nat.card (CFSG.Theory.Comparator.SzModel n) := by
  rw [(show CFSG.Theory.Comparator.SzModel _ = _ from CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup _),
    CFSG.BenderSuzuki.lemma114_suzukiMatrixGroup_card_formula n (by omega)]
  have hq : 2 ^ (2 * n + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  generalize 2 ^ (2 * n + 1) = q at hq ⊢
  have h1 : (q ^ 2 + 1) % 3 = 2 := by
    rw [Nat.add_mod, Nat.pow_mod, hq]
  have h2 : q ^ 2 % 3 = 1 := by
    rw [Nat.pow_mod, hq]
  have h3 : (q - 1) % 3 = 1 := by omega
  intro h
  have h4 := (Nat.dvd_iff_mod_eq_zero ..).mp h
  rw [Nat.mul_mod, Nat.mul_mod (q ^ 2 + 1), h1, h2, h3] at h4
  norm_num at h4

theorem false_of_suzuki {F : Type} [Field F] [Finite F] [CharP F 2]
    {D : Subgroup (GL (Fin 3) F)} (hirr : SubgroupLists.IsIrreducibleOn D) (hs : IsSimpleGroup D)
    {n : ℕ} (hn : 1 ≤ n) (χ : D ≃* CFSG.Theory.Comparator.SzModel n) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let χ' : D ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n :=
    χ.trans (MulEquiv.subgroupCongr (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup n))
  have : Finite (CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup n) :=
    Finite.of_equiv D χ'.toEquiv
  have hSp : CFSG.RankThree.PartOne.SolD3.SylowSpecial D :=
    (CFSG.RankThree.PartOne.SolD3.sylowSpecial_suzukiMatrixGroup n (by omega)).map_mulEquiv χ'.symm
  have h2 : 2 ∣ Nat.card D := by
    rw [Nat.card_congr χ'.toEquiv,
      CFSG.BenderSuzuki.lemma114_suzukiMatrixGroup_card_formula n (by omega)]
    refine Dvd.dvd.mul_right (Dvd.dvd.mul_left ?_ _) _
    exact dvd_pow (dvd_pow_self 2 (by omega)) (by norm_num)
  obtain ⟨P⟩ : Nonempty (Sylow 2 D) := inferInstance
  have hP : ¬ IsMulCommutative (P : Subgroup D) := by
    intro hc
    have hPne : (P : Subgroup D) ≠ ⊥ := P.ne_bot_of_dvd_card h2
    obtain ⟨x, hx, hx1⟩ := (Subgroup.bot_or_exists_ne_one _).resolve_left hPne
    have hcen : (⟨x, hx⟩ : (P : Subgroup D)) ∈ Subgroup.center (P : Subgroup D) := by
      rw [Subgroup.mem_center_iff]
      intro y
      exact hc.is_comm.comm y _
    have hcomm' := hSp P hcen
    have hbot : commutator (P : Subgroup D) = ⊥ := by
      rw [eq_bot_iff, commutator_def, Subgroup.commutator_le]
      intro a _ b _
      rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
      exact hc.is_comm.comm a b
    rw [hbot, Subgroup.mem_bot] at hcomm'
    exact hx1 (congrArg Subtype.val hcomm')
  have h3 := CFSG.RankThree.PartTwo.Sec16.KL3SubProof.ksl3TwoIrrSimpleNonab F D hirr hs P hP
  apply not_three_dvd_card_suzuki hn
  rw [← Nat.card_congr χ.toEquiv]
  exact h3

theorem dvd_of_psu3 {F : Type} [Field F] [Finite F] {e : ℕ} (hF : Nat.card F = 2 ^ e)
    {D : Subgroup (GL (Fin 3) F)} {n : ℕ} (hn : 2 ≤ n)
    (χ : D ⧸ Subgroup.center D ≃* CFSG.Theory.Comparator.PSU3Model n) : n ∣ e := by
  have hmodel : CFSG.Theory.Comparator.PSU3Model n = CFSG.Open.PSU3 2 n :=
    CFSG.Models.benderPSU3Model_eq_psu3 n
  let eK : D ⧸ Subgroup.center D ≃* StatedProj (StatedSU 3 (2 ^ n) (GaloisField 2 (2 * n))) :=
    (χ.trans (MulEquiv.subgroupCongr hmodel)).trans
      (CFSG.ShultStronglyClosedTI.glaSUCanonicalEquivNative n).symm
  have hK3 := card_statedProj_statedSU_three_two_mul (m := n) (by omega)
  rw [← Nat.card_congr eK.toEquiv] at hK3
  have hk : 0 < 6 * n := by omega
  obtain ⟨r, hr⟩ := CFSG.Timmesfeld.exists_isPrimitivePrimeDivisor (k := 6 * n) (by omega)
    (by omega)
  have hrp := hr.prime
  have hr3 : r ≠ 3 := fun h3 => by
    have := hr.eq_two_of_dvd_three hk (by rw [h3])
    omega
  have hr2 := hr.ne_two hk
  have hrq : r ∣ 2 ^ (3 * n) + 1 := (hr.dvd_add_one_iff hk (3 * n)).mpr
    ⟨⟨1, by ring⟩, fun h => by
      have := Nat.le_of_dvd (by omega) h
      omega⟩
  have hrK : r ∣ Nat.card (D ⧸ Subgroup.center D) := by
    have h1 : r ∣ Nat.card (D ⧸ Subgroup.center D) * Nat.gcd 3 (2 ^ n + 1) := by
      rw [hK3, ← pow_mul, mul_comm n 3]
      exact Dvd.dvd.mul_left hrq _
    have hcop : Nat.Coprime r (Nat.gcd 3 (2 ^ n + 1)) :=
      Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_left 3 _)
        ((Nat.coprime_primes hrp Nat.prime_three).mpr hr3)
    exact hcop.dvd_of_dvd_mul_right h1
  have hrGL : r ∣ Nat.card (GL (Fin 3) F) :=
    hrK.trans ((Subgroup.card_quotient_dvd_card _).trans (Subgroup.card_subgroup_dvd_card D))
  have := Fintype.ofFinite F
  rw [Matrix.card_GL_field, Fin.prod_univ_three, ← Nat.card_eq_fintype_card, hF] at hrGL
  simp only [Fin.val_zero, Fin.val_one, Fin.val_two, pow_zero, pow_one] at hrGL
  set x := 2 ^ e with hx
  have hx1 : 1 ≤ x := Nat.one_le_two_pow
  have hr2x : ¬ r ∣ x := fun h => hr2 ((Nat.prime_dvd_prime_iff_eq hrp Nat.prime_two).mp
    (hrp.dvd_of_dvd_pow h))
  have e1 : x ^ 3 - x = x * (x ^ 2 - 1) := by
    rw [Nat.mul_sub_one, ← pow_succ']
  have e2 : x ^ 3 - x ^ 2 = x ^ 2 * (x - 1) := by
    rw [Nat.mul_sub_one, ← pow_succ]
  rw [e1, e2] at hrGL
  rcases (Nat.Prime.dvd_mul hrp).mp hrGL with h | h
  · rcases (Nat.Prime.dvd_mul hrp).mp h with h | h
    · rw [hx, ← pow_mul, mul_comm e 3] at h
      obtain ⟨c, hc⟩ := (hr.dvd_sub_one_iff hk (3 * e)).mp h
      exact ⟨2 * c, by linarith⟩
    · rcases (Nat.Prime.dvd_mul hrp).mp h with h | h
      · exact absurd h hr2x
      · rw [hx, ← pow_mul, mul_comm e 2] at h
        obtain ⟨c, hc⟩ := (hr.dvd_sub_one_iff hk (2 * e)).mp h
        exact ⟨3 * c, by linarith⟩
  · rcases (Nat.Prime.dvd_mul hrp).mp h with h | h
    · exact absurd (hrp.dvd_of_dvd_pow h) hr2x
    · rw [hx] at h
      obtain ⟨c, hc⟩ := (hr.dvd_sub_one_iff hk e).mp h
      exact ⟨6 * c, by linarith⟩

theorem evenSL3Irred_degenerate {F : Type} [Field F] [Finite F]
    {e : ℕ} (hF : Nat.card F = 2 ^ e) {D : Subgroup (GL (Fin 3) F)}
    (hdet : ∀ x ∈ D, (x : Matrix (Fin 3) (Fin 3) F).det = 1) (hDq : IsQuasisimple D)
    (hZ3 : ∀ z ∈ Subgroup.center D, z ^ 3 = 1) (hirr : SubgroupLists.IsIrreducibleOn D)
    (hcomm : ∀ M : Matrix (Fin 3) (Fin 3) F,
      (∀ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) * M = M * g) → ∃ c : F, M = Matrix.scalar (Fin 3) c)
    (hdeg : ∀ s t : D, s ^ 2 = 1 → t ^ 2 = 1 → s * t = t * s ∨ Odd (orderOf (s * t))) :
    ∃ f : ℕ, 1 ≤ f ∧ f ∣ e ∧ (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩;
      IsLThreeEpsAt (D ⧸ Subgroup.center D) 2 f) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype F := Fintype.ofFinite F
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  haveI : Group.IsPerfect D := hDq.1
  haveI hKs : IsSimpleGroup (D ⧸ Subgroup.center D) := hDq.2.1
  have hnab := hDq.2.2
  obtain ⟨M, hM⟩ := exists_isStronglyEmbeddedOrder_of_degenerate hKs hnab
    (degenerate_quotient hZ3 hdeg)
  have hZ : Nat.card (Subgroup.center D) ∣ 3 := card_center_dvd_three_of_scalar hZ3 hcomm
  have hiso : Subgroup.center D = ⊥ → D ≃* D ⧸ Subgroup.center D := fun hZ1 =>
    ((QuotientGroup.quotientMulEquivOfEq hZ1).trans QuotientGroup.quotientBot).symm
  rcases CFSG.BenderSuzuki.bender_suzuki M hM with ⟨n, hn, χ⟩ | ⟨n, hn, χ⟩ | ⟨n, hn, χ⟩
  ·
    exfalso
    have hZ1 : Subgroup.center D = ⊥ := by
      apply SubgroupLists.center_eq_bot_of_isCyclic_sylow hZ
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      apply isCyclic_sylow_of_mulEquiv_degen χ
      intro Q
      refine CFSG.RankThree.PartTwo.KFacts.isCyclic_sylow_three_psl2 ?_ ?_ Q
      · rw [ringChar.eq (GaloisField 2 n) 2]
        norm_num
      · rw [GaloisField.card 2 n (by omega)]
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    exact false_of_psl2 hdet hirr hn ((hiso hZ1).trans χ)
  ·
    exfalso
    have hZ1 : Subgroup.center D = ⊥ := by
      apply SubgroupLists.center_eq_bot_of_isCyclic_sylow hZ
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      intro Q
      have hQ : Nat.card (Q : Subgroup (D ⧸ Subgroup.center D)) = 1 := by
        obtain ⟨k, hk⟩ := Q.isPGroup'.exists_card_eq
        have hdvd : Nat.card (Q : Subgroup (D ⧸ Subgroup.center D)) ∣
            Nat.card (CFSG.Theory.Comparator.SzModel n) := by
          rw [← Nat.card_congr χ.toEquiv]
          exact Subgroup.card_subgroup_dvd_card _
        rcases k with _ | k
        · rw [hk, pow_zero]
        · exfalso
          rw [hk, pow_succ] at hdvd
          exact not_three_dvd_card_suzuki hn (dvd_trans (Dvd.intro_left _ rfl) hdvd)
      have : Subsingleton (Q : Subgroup (D ⧸ Subgroup.center D)) :=
        (Nat.card_eq_one_iff_unique.mp hQ).1
      infer_instance
    have hs : IsSimpleGroup D := MulEquiv.isSimpleGroup (hiso hZ1)
    exact false_of_suzuki hirr hs hn ((hiso hZ1).trans χ)
  ·
    refine ⟨n, by omega, dvd_of_psu3 hF hn χ, Or.inr ⟨?_, CFSG.CGT.PushingUp.benderBridge_psu hn χ⟩⟩
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn

@[expose] def EvenSL3IrredNondeg : Prop :=
  ∀ (F : Type) [Field F] [Finite F] (e : ℕ), 1 ≤ e → Nat.card F = 2 ^ e → 2 ^ e % 3 = 1 →
    ∀ D : Subgroup (GL (Fin 3) F), (∀ x ∈ D, (x : Matrix (Fin 3) (Fin 3) F).det = 1) →
      IsQuasisimple D → (∀ z ∈ Subgroup.center D, z ^ 3 = 1) →
      SubgroupLists.IsIrreducibleOn D →
      (∀ M : Matrix (Fin 3) (Fin 3) F, (∀ g ∈ D, (g : Matrix (Fin 3) (Fin 3) F) * M = M * g) →
        ∃ c : F, M = Matrix.scalar (Fin 3) c) →
      ¬ SubgroupLists.IsTransitiveMonomial D →
      (∃ s t : D, s ^ 2 = 1 ∧ t ^ 2 = 1 ∧ s * t ≠ t * s ∧ Even (orderOf (s * t))) →
      StatedClassicalModel (D ⧸ Subgroup.center D) .PSL 2 3 2 ∨
        ∃ f : ℕ, 1 ≤ f ∧ f ∣ e ∧ (haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩;
          IsLThreeEpsAt (D ⧸ Subgroup.center D) 2 f)

theorem evenSL3Irred_of_nondeg (hN : EvenSL3IrredNondeg) :
    EvenSL3Irred := by
  intro F _ _ e he hF hq D hdet hDq hZ3 hirr hcomm hprim
  by_cases hnd : ∃ s t : D, s ^ 2 = 1 ∧ t ^ 2 = 1 ∧ s * t ≠ t * s ∧ Even (orderOf (s * t))
  · exact hN F e he hF hq D hdet hDq hZ3 hirr hcomm hprim hnd
  · right
    refine evenSL3Irred_degenerate hF hdet hDq hZ3 hirr hcomm fun s t hs ht => ?_
    by_contra h
    push Not at h
    exact hnd ⟨s, t, hs, ht, h.1, Nat.not_odd_iff_even.mp h.2⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148T

module

public import CFSG.OddTranspositions.PartFour.ThirteenCompFactorModels
public import CFSG.LocalAnalysis.WeakClosure81.OddTranspCompFactorDerivedCases
import CFSG.OddTranspositions.PartFour.Thirteen
import CFSG.LocalAnalysis.WeakClosure81.W18KernBridge
import CFSG.LocalAnalysis.ComponentClassification.CatLeafProofX10LinOrthHigh
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOddQuadraticBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDerived
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalLowDimCoverageCases
public import CFSG.Quasithin.Vol2.Ch8Sec2L829LN0

public section

namespace CFSG.OddTranspositions.PartFour

open CFSG.LocalAnalysis.WeakClosure81 CFSG.Quasithin CFSG.Quasithin.H13.L829N
open CFSG.Blueprint (LieModel)
open CFSG.ComponentClassification.CatLeafProof.X10Lin (ModelIn orthTuples)
open scoped commutatorElement

namespace OddTranspFactors

theorem of_normal_subgroup {Y : Type} [Group Y] (N : Subgroup Y) [N.Normal]
    (h : OddTranspFactors Y) : OddTranspFactors ↥N :=
  fun T _ hT hnab => h T (kbr_isCompositionFactor_of_normal_subgroup N hT) hnab

theorem of_sup_eq_top {Y : Type} [Group Y] (A B : Subgroup Y) [A.Normal] [B.Normal]
    (hAB : A ⊔ B = ⊤) (hA : OddTranspFactors ↥A) (hB : OddTranspFactors ↥B) :
    OddTranspFactors Y :=
  fun T _ hT hnab => (isCompositionFactor_of_sup_eq_top A B hAB hT).elim (hA T · hnab)
    (hB T · hnab)

theorem of_isQuasisimple {Y : Type} [Group Y] (hY : CFSG.IsQuasisimple Y)
    (h : OddTranspFactor (Y ⧸ Subgroup.center Y)) : OddTranspFactors Y := by
  haveI := hY.2.1
  exact of_normal (Subgroup.center Y)
    (of_commute fun a b => Subtype.ext (Subgroup.mem_center_iff.mp b.2 a.1))
    (of_isSimpleGroup h)

theorem of_normal_commutator {G : Type} [Group G] (H : Subgroup G) [H.Normal]
    (h : OddTranspFactors ↥(commutator G)) : OddTranspFactors ↥H := by
  have hN : OddTranspFactors ↥(H ⊓ commutator G) :=
    (h.of_normal_subgroup ((H ⊓ commutator G).subgroupOf (commutator G))).of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe inf_le_right)
  refine of_normal ((H ⊓ commutator G).subgroupOf H)
    (hN.of_mulEquiv (Subgroup.subgroupOfEquivOfLe inf_le_left).symm) (of_commute fun a b => ?_)
  obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq, Subgroup.mem_subgroupOf,
    Subgroup.mem_inf]
  refine ⟨((x * y)⁻¹ * (y * x)).2, ?_⟩
  have hc : (((x * y)⁻¹ * (y * x) : ↥H) : G) = ⁅((y : G))⁻¹, ((x : G))⁻¹⁆ := by
    simp only [commutatorElement_def, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv, mul_inv_rev,
      mul_assoc]
  rw [hc, commutator_def]
  exact Subgroup.commutator_mem_commutator (Subgroup.mem_top _) (Subgroup.mem_top _)

theorem of_commutator_eq_sup {G : Type} [Group G]
    (hcomp : ∀ M : Subgroup G, CFSG.IsComponent M → OddTranspFactors ↥M) (L R : Subgroup G)
    (hsup : commutator G = L ⊔ R) (hqL : CFSG.IsQuasisimple ↥L) (hqR : CFSG.IsQuasisimple ↥R)
    (hnL : (L.subgroupOf (commutator G)).Normal) (hnR : (R.subgroupOf (commutator G)).Normal) :
    OddTranspFactors ↥(commutator G) := by
  have hLC : L ≤ commutator G := hsup ▸ le_sup_left
  have hRC : R ≤ commutator G := hsup ▸ le_sup_right
  have hC : (commutator G).IsSubnormal := (inferInstance : (commutator G).Normal).isSubnormal
  haveI := hnL
  haveI := hnR
  refine of_sup_eq_top (L.subgroupOf (commutator G)) (R.subgroupOf (commutator G)) ?_
    ((hcomp L ⟨hqL, Subgroup.IsSubnormal.step L _ hLC hC hnL⟩).of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hLC).symm)
    ((hcomp R ⟨hqR, Subgroup.IsSubnormal.step R _ hRC hC hnR⟩).of_mulEquiv
      (Subgroup.subgroupOfEquivOfLe hRC).symm)
  have h := sup_subgroupOf_sup_eq_top L R
  rw [← hsup] at h
  exact h

end OddTranspFactors

private theorem oddTranspFactor_of_modelIn_orthTuples_five {d : ℕ} {L : Type} [Group L]
    (h : ModelIn 5 (orthTuples d 1) L) : OddTranspFactor (L ⧸ Subgroup.center L) := by
  obtain ⟨t, m, f, hT, -, hL⟩ := h
  have q5 : (5 = 3 ∨ 5 = 5) := Or.inr rfl
  rcases hT with ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨-, h⟩ | ⟨-, h | h⟩ | ⟨-, -, h⟩ | ⟨-, -, h | h⟩ <;>
    simp only [Prod.mk.injEq] at h <;> obtain ⟨rfl, rfl, rfl⟩ := h
  · exact Or.inr (Or.inr (Or.inl ⟨5, 0, 1, q5, by norm_num, Or.inl hL⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨5, 0, 1, q5, by norm_num, Or.inl hL⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨5, 0, 2 * 1, q5, by norm_num, Or.inl hL⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨5, 0, 0, q5, by norm_num, Or.inr (Or.inl hL)⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨5, 0, 0, q5, by norm_num, Or.inr (Or.inr (Or.inl hL))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨5, 0, 0, q5, by norm_num,
      Or.inr (Or.inr (Or.inr (Or.inl hL)))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨5, d / 2, 0, q5, by norm_num,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL))))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨5, d / 2, 0, q5, by norm_num,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hL)))))⟩))
  · exact Or.inr (Or.inr (Or.inl ⟨5, d / 2, 0, q5, by norm_num,
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hL)))))⟩))

section Orthogonal

variable {K W : Type} [Field K] [Finite K] [AddCommGroup W] [Module K W] [FiniteDimensional K W]

theorem oddTranspFactors_of_isComponent_five (hK : Nat.card K = 5) (Q : QuadraticForm K W)
    (hQ : Q.polarBilin.Nondegenerate) (h3 : 3 ≤ Module.finrank K W)
    {M : Subgroup ↥(TauCeti.QuadraticMap.orthogonalGroup Q)} (hM : CFSG.IsComponent M) :
    OddTranspFactors ↥M :=
  OddTranspFactors.of_isQuasisimple hM.1 (oddTranspFactor_of_modelIn_orthTuples_five
    (CFSG.ComponentClassification.CatLeafProof.X10Lin.orthogonal_component_models
      Nat.prime_five (by norm_num) le_rfl (by rw [hK]; norm_num) Q hQ h3 hM))

theorem oddTranspFactors_commutator_orthogonalGroup_five (hK : Nat.card K = 5)
    (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) (h4 : 4 ≤ Module.finrank K W) :
    OddTranspFactors ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := by
  have hodd : Odd (Nat.card K) := by rw [hK]; decide
  have h2 : (2 : K) ≠ 0 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.two_ne_zero_of_odd_card hodd
  have hC : (commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)).Normal := inferInstance
  have hder : CFSG.IsQuasisimple ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) →
      OddTranspFactors ↥(commutator ↥(TauCeti.QuadraticMap.orthogonalGroup Q)) := fun hq =>
    oddTranspFactors_of_isComponent_five hK Q hQ (by omega) ⟨hq, hC.isSubnormal⟩
  by_cases hT : ∃ T : Submodule K W, Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0
  · obtain ⟨T, hT3, hTQ⟩ := hT
    exact hder (CFSG.ComponentClassification.CatalogueBOrthogonal.derived_quasisimple Q h2 hQ
      hT3.ge hTQ)
  have h6 :=
    CFSG.ComponentClassification.CatalogueBOddQuadratic.finrank_le_six_of_no_totallySingular_three
      hodd Q hQ hT
  rcases (show Module.finrank K W = 4 ∨ Module.finrank K W = 5 ∨ Module.finrank K W = 6 by
    omega) with h | h | h
  · by_cases hS : ∃ S : Submodule K W, Module.finrank K S = 2 ∧ ∀ x ∈ S, Q x = 0
    ·
      obtain ⟨-, e, -, -, hsup, hqL, hqR, hnL, hnR, -, -, -⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.orthogonal_split_four_derived (by omega) (by omega)
          Q hQ h hS
      exact OddTranspFactors.of_commutator_eq_sup
        (fun M hM => oddTranspFactors_of_isComponent_five hK Q hQ (by omega) hM) _ _ hsup hqL hqR
        hnL hnR
    · obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
        CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_four_derived hodd Q hQ h hS
      exact hder hq
  · obtain ⟨-, -, -, -, -, -, hq, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.orthogonal_five_derived hodd Q hQ h
    exact hder hq
  · obtain ⟨-, -, -, -, -, -, -, -, hq, -⟩ :=
      CFSG.LocalAnalysis.ComponentInitial.orthogonal_nonsplit_six_derived hodd Q hQ h hT
    exact hder hq

end Orthogonal

section Reflections

open CFSG.ClassicalGroups.Orthogonal

variable {n : ℕ} {b : LinearMap.BilinForm (ZMod 5) (Fin n → ZMod 5)}

private theorem fact_prime_five : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩

attribute [local instance] fact_prime_five

theorem bilin_map_of_mem_orthogonalGroup (hsym : ∀ x y, b x y = b y x)
    {g : (Fin n → ZMod 5) ≃ₗ[ZMod 5] (Fin n → ZMod 5)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b))
    (x y : Fin n → ZMod 5) : b (g x) (g y) = b x y := by
  have hQ := TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp hg
  have hp : QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap b) (g x) (g y) =
      QuadraticMap.polar (LinearMap.BilinMap.toQuadraticMap b) x y := by
    rw [QuadraticMap.polar, QuadraticMap.polar, ← map_add, hQ, hQ, hQ]
  rw [LinearMap.BilinMap.polar_toQuadraticMap, LinearMap.BilinMap.polar_toQuadraticMap,
    hsym (g y) (g x), hsym y x, ← two_mul, ← two_mul] at hp
  exact mul_left_cancel₀ (by decide : (2 : ZMod 5) ≠ 0) hp

theorem reflectionGroup_le_orthogonalGroup (hsym : ∀ x y, b x y = b y x) :
    (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => -2 * b x y)
        fun v => b v v = 1)).map (toLinEquiv (Fin n) (ZMod 5)).toMonoidHom ≤
      TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b) := by
  rw [MonoidHom.map_closure, Subgroup.closure_le]
  rintro _ ⟨m, ⟨v, hv, hmv⟩, rfl⟩
  refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun x => ?_
  rw [MulEquiv.coe_toMonoidHom, toLinEquiv_apply, hmv, LinearMap.BilinMap.toQuadraticMap_apply,
    LinearMap.BilinMap.toQuadraticMap_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hv,
    hsym v x]
  ring

theorem conj_mem_reflections (hsym : ∀ x y, b x y = b y x)
    {g : (Fin n → ZMod 5) ≃ₗ[ZMod 5] (Fin n → ZMod 5)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b))
    {m : GL (Fin n) (ZMod 5)}
    (hm : m ∈ CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1) :
    g * (toLinEquiv (Fin n) (ZMod 5)).toMonoidHom m * g⁻¹ ∈
      (toLinEquiv (Fin n) (ZMod 5)).toMonoidHom ''
        CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1 := by
  obtain ⟨v, hv, hmv⟩ := hm
  have key : ∀ x, b (g.symm x) v = b x (g v) := fun x => by
    have := bilin_map_of_mem_orthogonalGroup hsym hg (g.symm x) v
    rw [g.apply_symm_apply] at this
    exact this.symm
  refine ⟨(toLinEquiv (Fin n) (ZMod 5)).symm (g * (toLinEquiv (Fin n) (ZMod 5)).toMonoidHom m *
    g⁻¹), ⟨g v, ?_, fun x => ?_⟩, MulEquiv.apply_symm_apply _ _⟩
  · show b (g v) (g v) = 1
    rw [bilin_map_of_mem_orthogonalGroup hsym hg, hv]
  · rw [← toLinEquiv_apply, MulEquiv.apply_symm_apply]
    change g ((toLinEquiv (Fin n) (ZMod 5)) m (g.symm x)) = _
    rw [toLinEquiv_apply, hmv, map_add, map_smul, g.apply_symm_apply]
    simp only [key]

theorem conj_mem_reflectionGroup (hsym : ∀ x y, b x y = b y x)
    {g : (Fin n → ZMod 5) ≃ₗ[ZMod 5] (Fin n → ZMod 5)}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b))
    {h : (Fin n → ZMod 5) ≃ₗ[ZMod 5] (Fin n → ZMod 5)}
    (hh : h ∈ (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => -2 * b x y)
        fun v => b v v = 1)).map (toLinEquiv (Fin n) (ZMod 5)).toMonoidHom) :
    g * h * g⁻¹ ∈ (Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => -2 * b x y)
        fun v => b v v = 1)).map (toLinEquiv (Fin n) (ZMod 5)).toMonoidHom := by
  rw [MonoidHom.map_closure] at hh ⊢
  have hle : (Subgroup.closure ((toLinEquiv (Fin n) (ZMod 5)).toMonoidHom ''
      CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1)).map
        (MulAut.conj g).toMonoidHom ≤
      Subgroup.closure ((toLinEquiv (Fin n) (ZMod 5)).toMonoidHom ''
        CFSG.Open.fischerTransvections (fun x y => -2 * b x y) fun v => b v v = 1) := by
    rw [MonoidHom.map_closure]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨_, ⟨m, hm, rfl⟩, rfl⟩
    exact conj_mem_reflections hsym hg hm
  exact hle ⟨h, hh, rfl⟩

theorem oddTranspCompFactorOFive_of_models : OddTranspCompFactorOFive := by
  intro n hn b hsym hnd T _ hT hnab
  have h2 : (2 : ZMod 5) ≠ 0 := by decide
  have hQ : (LinearMap.BilinMap.toQuadraticMap b).polarBilin.Nondegenerate :=
    CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_of_forall fun v hv => hnd v fun w => by
      have := hv w
      rw [LinearMap.BilinMap.polar_toQuadraticMap, hsym w v, ← two_mul] at this
      exact (mul_eq_zero.mp this).resolve_left h2
  have hdim : 4 ≤ Module.finrank (ZMod 5) (Fin n → ZMod 5) := by
    rw [Module.finrank_fin_fun]
    exact hn
  have hO := oddTranspFactors_commutator_orthogonalGroup_five (K := ZMod 5)
    (by rw [Nat.card_eq_fintype_card, ZMod.card]) _ hQ hdim
  have hle := reflectionGroup_le_orthogonalGroup hsym
  haveI : (((Subgroup.closure (CFSG.Open.fischerTransvections (fun x y => -2 * b x y)
      fun v => b v v = 1)).map (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n)
        (ZMod 5)).toMonoidHom).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b))).Normal :=
    ⟨fun x hx g => by
      rw [Subgroup.mem_subgroupOf] at hx ⊢
      exact conj_mem_reflectionGroup hsym g.2 hx⟩
  have hHO : OddTranspFactors ↥(((Subgroup.closure (CFSG.Open.fischerTransvections
      (fun x y => -2 * b x y) fun v => b v v = 1)).map
        (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n) (ZMod 5)).toMonoidHom).subgroupOf
      (TauCeti.QuadraticMap.orthogonalGroup (LinearMap.BilinMap.toQuadraticMap b))) :=
    OddTranspFactors.of_normal_commutator _ hO
  have hH := (hHO.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hle)).of_mulEquiv
    ((Subgroup.closure _).equivMapOfInjective _
      (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin n) (ZMod 5)).injective).symm
  exact hH T hT hnab

end Reflections

end CFSG.OddTranspositions.PartFour

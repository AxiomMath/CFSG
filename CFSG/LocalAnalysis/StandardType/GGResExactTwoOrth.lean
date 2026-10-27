module

public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthDefs
public import CFSG.LocalAnalysis.StandardType.GGHdRo7DAssembly
import CFSG.LocalAnalysis.StandardType.GGHdRo7CFullWeyl
import CFSG.LocalAnalysis.StandardType.GGHdRo7CGen
import CFSG.LocalAnalysis.StandardType.GGHdRo7CNormalizer
import CFSG.LocalAnalysis.StandardType.GGHdRo7CRefl
import CFSG.LocalAnalysis.StandardType.GGHdRo7CSignX
import CFSG.LocalAnalysis.StandardType.GGHdRo7DAJ
import CFSG.LocalAnalysis.StandardType.GGHdRo7DClassLarge
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFixWeyl
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFrameOmega
import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModel
import CFSG.LocalAnalysis.StandardType.GGHdRo7DNormalizer
import CFSG.LocalAnalysis.StandardType.GGHdRo7DReduceU
import CFSG.LocalAnalysis.StandardType.GGHdRo7DReduceV
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSideCoord
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSmallFinal
import CFSG.LocalAnalysis.StandardType.GGHdRo7DStab
import CFSG.LocalAnalysis.StandardType.GGHdRo7NoTV
import CFSG.LocalAnalysis.StandardType.GGHdRo7SUGraph
import CFSG.LocalAnalysis.StandardType.GGHdRo7XDatum
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Datum

variable {G : Type} [Group G] [Finite G] {k p : ℕ} [Fact p.Prime] {Bs L J K : Subgroup G}
  {sel : Prop → Prop → Prop}
  {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}

theorem GGResLeviDatumCard.xDatum_left (hD : GGResLeviDatumCard k p Bs L J K sel typ) :
    GGResXDatum p Bs L := by
  obtain ⟨Λ, instΛ, decΛ, S, Λa, instΛa, decΛa, ML, CL, MK, CK, V, instV, instMod, ι, φ, h, α,
    -, -, -, hWL, hCL, -, -, -, hform, hrefl, hpL, -, -, ⟨fL, hfL⟩, -, hgenL, -, -, -⟩ := hD
  exact ⟨Λ, instΛ, decΛ, ML, CL, V, instV, instMod, ι, fun i => φ (Sum.inl i),
    fun i => h (Sum.inl i), fun i => α (Sum.inl i), hWL, hCL, fun i w => hform (Sum.inl i) w,
    fun i => hrefl (Sum.inl i), hpL, ⟨fL, hfL⟩, hgenL⟩

theorem GGResLeviDatumCard.xDatum_right (hD : GGResLeviDatumCard k p Bs L J K sel typ) :
    GGResXDatum p Bs K := by
  classical
  obtain ⟨Λ, instΛ, decΛ, S, Λa, instΛa, decΛa, ML, CL, MK, CK, V, instV, instMod, ι, φ, h, α,
    -, -, -, -, -, hWK, hCK, -, hform, hrefl, -, hpK, -, -, ⟨fK, hfK⟩, -, hgenK, -, -⟩ := hD
  refine ⟨{i : Λ // i ∉ S} ⊕ Λa, inferInstance, inferInstance, MK, CK, V, instV, instMod, ι,
    fun o => φ (o.map Subtype.val id), fun o => h (o.map Subtype.val id),
    fun o => α (o.map Subtype.val id), hWK, hCK, fun o w => hform _ w, fun o => hrefl _, hpK,
    ⟨fK, hfK⟩, ?_⟩
  rw [hgenK]
  congr 1
  ext ψ
  constructor
  · rintro (⟨j, rfl⟩ | ⟨a, rfl⟩)
    · exact ⟨Sum.inl j, rfl⟩
    · exact ⟨Sum.inr a, rfl⟩
  · rintro ⟨o, rfl⟩
    rcases o with j | a
    · exact Or.inl ⟨j, rfl⟩
    · exact Or.inr ⟨a, rfl⟩

theorem GGResLeviDatumCard.aj_nonabelian (hD : GGResLeviDatumCard k p Bs L J K sel typ)
    {n : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (ι : Additive ↥Bs ≃+ V) (hp3 : p = 3)
    (hn : k + 2 ≤ n)
    (hsub : ∀ g : V ≃ₗ[ZMod p] V, HdRo7D.DSP p b g →
      g ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι)) :
    ∃ u ∈ ggAutomizer J Bs, ∃ v ∈ ggAutomizer J Bs, u * v ≠ v * u := by
  classical
  obtain ⟨Λ, instΛ, decΛ, S, Λa, instΛa, decΛa, ML, CL, MK, CK, V', instV, instMod, ι', φ, h, α,
    hk, -, -, -, -, -, -, -, hform, -, -, -, -, ⟨fL, hfL⟩, -, hgenL, -, hconn, hgenJ⟩ := hD
  have hΛ : n ≤ Nat.card Λ :=
    HdRo7D.hdRo7DAJAux_model_card_le b ι hp3 (by omega) hsub ι' (fun i => φ (Sum.inl i))
      (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i)) (fun i w => hform (Sum.inl i) w) hgenL
  have hsplit : Nat.card Λ = Nat.card {j : Λ // j ∈ S} + Nat.card {j : Λ // j ∉ S} := by
    rw [← Nat.card_congr (Equiv.sumCompl (fun j : Λ => j ∈ S)), Nat.card_sum]
  have hSc : Nat.card {j : Λ // j ∈ S} = S.card := by
    rw [Nat.card_eq_fintype_card]
    exact Fintype.card_coe S
  have hrest : 1 < Nat.card {j : Λ // j ∉ S} := by omega
  obtain ⟨u, v, huv⟩ := (Finite.one_lt_card_iff_nontrivial.mp hrest).exists_pair_ne
  obtain ⟨w, ⟨huw, hMuw⟩, -⟩ := (Relation.ReflTransGen.cases_head (hconn u v)).resolve_left huv
  refine ⟨φ (Sum.inl u.val), ?_, φ (Sum.inl w.val), ?_, ?_⟩
  · rw [hgenJ]
    exact Subgroup.subset_closure ⟨u, rfl⟩
  · rw [hgenJ]
    exact Subgroup.subset_closure ⟨w, rfl⟩
  · intro hcomm
    have hsimple_comm :
        ML.simple u.val * ML.simple w.val = ML.simple w.val * ML.simple u.val := by
      apply fL.injective
      apply Subtype.ext
      simp only [map_mul, Subgroup.coe_mul, hfL]
      exact hcomm
    have hsq : (ML.simple u.val * ML.simple w.val) ^ 2 = 1 := by
      have hc : Commute (ML.simple u.val) (ML.simple w.val) := hsimple_comm
      rw [hc.mul_pow]
      rw [show ML.simple u.val ^ 2 = 1 from by
            rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
            exact CoxeterSystem.simple_mul_simple_self ML.toCoxeterSystem u.val,
          show ML.simple w.val ^ 2 = 1 from by
            rw [pow_two, ← CoxeterMatrix.toCoxeterSystem_simple]
            exact CoxeterSystem.simple_mul_simple_self ML.toCoxeterSystem w.val]
      simp
    have horder : orderOf (ML.simple u.val * ML.simple w.val) = ML.M u.val w.val := by
      rw [← CoxeterMatrix.toCoxeterSystem_simple]
      exact CoxeterSystem.orderOf_simple_mul_simple ML.toCoxeterSystem u.val w.val
    have hdvd : ML.M u.val w.val ∣ 2 := by
      rw [← horder]
      exact orderOf_dvd_iff_pow_eq_one.mpr hsq
    have h1 : ML.M u.val w.val ≠ 1 := ML.off_diagonal u.val w.val fun h => huw (Subtype.ext h)
    rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h' | h'
    · exact h1 h'
    · exact hMuw h'

end Datum

theorem ggResLeviDatumCard_join_orthQTwo_six (hRig : GGLabelRigidInput)
    (hKG : GGReflClassLargeInput') {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hlab : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
      lab.n = 1 ∧ 6 ≤ lab.rank) p Bs L)
    {k : ℕ} (hk : k ≤ 3) {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hdat : GGResLeviDatumCard k p Bs L J K sel typ) :
    GGWeylReflectionGroup p (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  obtain ⟨lab, hΛ2, hhas, R, _, I, F, θ, ⟨hp3, htag, hn, hr⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hlab
  have hr6 : 6 ≤ lab.rank := hr
  have hDLin : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (H A : Subgroup (V ≃ₗ[ZMod p] V)),
      HdRo7D.DLinData p n V b H A → ZS.LinWeyl p H :=
    fun _ _ _ _ _ _ _ hD => HdRo7D.d_lin_of_leaves HdRo7D.d_normalizer_holds
      HdRo7D.d_fixWeyl_holds HdRo7D.d_reduceU_holds HdRo7D.d_reduceV_holds
      HdRo7D.d_classLarge_holds HdRo7D.d_linSmall_holds hKG hD
  have hCLin : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module (ZMod p) V]
      (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (AL Q A : Subgroup (V ≃ₗ[ZMod p] V)),
      HdRo7C.C2LinData p n V b AL Q A → ZS.LinWeyl p (AL ⊔ Q) :=
    fun _ _ _ _ _ _ _ _ hD => HdRo7C.c2_lin_of_leaves HdRo7C.c2_normalizer_holds
      HdRo7C.c2_refl_holds HdRo7C.c2_join_of_leaves
      hD
  have hM : HdRo7D.DModelAt p Bs L x :=
    HdRo7D.d_lModel_of_label hRig (HdRo7D.d_sideCoord_of_frame HdRo7D.d_frameOmega_holds) hH hp3
      ⟨lab, hΛ2, hhas, htag, hn, hr6⟩
  have hAJ : (∃ a ∈ ggAutomizer J Bs, ∃ c ∈ ggAutomizer J Bs, a * c ≠ c * a) ∧
      ggAutomizer J Bs ≤ ggAutomizer L Bs ⊓ ggAutomizer K Bs := by
    refine ⟨?_, hdat.aj_le⟩
    obtain ⟨n, V, hV, hVp, ι, b, -, -, -, hcase⟩ := hM
    letI := hV
    letI := hVp
    refine hdat.aj_nonabelian b ι hp3 ?_ ?_
    · rcases hcase with ⟨h6, -⟩ | ⟨h5, -⟩ <;> omega
    · intro g hg
      rcases hcase with ⟨-, hP⟩ | ⟨-, hP⟩
      · exact (hP g).mpr hg
      · exact (hP g).mpr (HdRo7D.hdRo7DAJAux_dsp_c2sp b hg)
  exact HdRo7D.d_core hH.2.2.2.1 HdRo7C.noTV_holds HdRo7C.xDatumGraph_holds
    HdRo7SU.su_graph_holds hDLin hCLin hdat.xDatum_left hdat.xDatum_right hAJ hM
    fun hx ψ hψ hψx => HdRo7D.d_lstab_of_label hH hp3 htag hn (by omega) hhas hx hψ hψx

theorem ggResExactTwoOrthQTwoOn_six (hRig : GGLabelRigidInput) (hKG : GGReflClassLargeInput') :
    GGResExactTwoOrthQTwoOn (6 ≤ ·) := by
  rintro G _ _ p B Bs x L D J y K hH _ hF hS hE ⟨hlab, hdat, -⟩
  exact ggResLeviDatumCard_join_orthQTwo_six hRig hKG hH hlab (by norm_num) hdat

theorem ggResExactTwoOrthQTwoOn_of_small (hRig : GGLabelRigidInput)
    (hKG : GGReflClassLargeInput') (hsmall : GGResExactTwoOrthQTwoOn fun r => r = 4 ∨ r = 5) :
    GGResExactTwoOrthQTwoOn (4 ≤ ·) :=
  (ggResExactTwoOrthQTwoOn_or hsmall (ggResExactTwoOrthQTwoOn_six hRig hKG)).mono
    fun r (hr : 4 ≤ r) => show (r = 4 ∨ r = 5) ∨ 6 ≤ r by omega

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGResE6Coordinates
public import CFSG.LocalAnalysis.StandardType.GGTBE6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBE6
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallExcC3Bstar
public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreE6
public import CFSG.LocalAnalysis.StandardType.GGIOneFieldCFHolds
public import CFSG.LocalAnalysis.StandardType.GGResIBasic
public import CFSG.LocalAnalysis.StandardType.GGKOnlyE6Normalization
public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc11R
public import CFSG.LocalAnalysis.StandardType.GGResE6DependentDualClassification
import TauCeti.LinearAlgebra.Pi
import CFSG.LocalAnalysis.StandardType.GGQ2P3Hyp

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

end CFSG.StandardType

namespace CFSG.StandardType

open CFSG.Assembly

open CFSG.Assembly CFSG.StandardType.TableBExc CFSG.StandardType.TableBExc.E6Three

private theorem ggRes_bstar_eq_of_bound_norm_marking
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hM : LargeEvenMarking L fun _ R _ I _ θ =>
      (Bs ≤ Subgroup.normalizer (L : Set G) ∧
        ∀ b ∈ Bs, ∃ φ ∈ I,
          LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) ∧
      ((∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I)) :
    B = Bs := by
  obtain ⟨hL, lab, -, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, ⟨hBsN, h3Bs⟩, ⟨r₁, hlift₁, hbound⟩,
    r₂, hlift₂, hnorm⟩ := largeEvenRawDatum_exists hraw
  have hnc := ggLNoncyclicInput_holds G p B x L hH.1.1
  have hBBs : B ≤ Bs := hH.1.2.1.1
  exact bstar_eq_of_bound_norm hH.1.1 hH.1.2.1 hnc hL θ
    (hBBs.trans hBsN) (fun b hb => h3Bs b (hBBs hb)) hlift₁ hbound hlift₂ hnorm

theorem GGResHyp.bstar_eq_of_splitE6
    {G : Type} [Group G] [Finite G] {p : ℕ}
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGInnerDiagOnLabel
      (fun p lab => p = 3 ∧ lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    B = Bs := by
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => p = 3 ∧ lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1)
    (P' := fun R _ I _ =>
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I)
    (fun lab hlab hS => SmallExc.largeEvenLabelAll_bstarEq_e6Three hlab
      ⟨hS.2.1, hS.1, hS.2.2⟩) (fun _ _ _ _ _ _ hP => hP.1) hRig
  exact ggRes_bstar_eq_of_bound_norm_marking hH
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2, hP.2⟩) hMark)

theorem GGResHyp.bstar_eq_of_splitE6_coprime
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3 ∧ ¬ p ∣ lab.n) p Bs L) :
    B = Bs := by
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3 ∧ ¬ p ∣ lab.n)
    (P' := fun R _ I _ =>
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I)
    (fun lab hlab hS => (largeEvenLabelAll_bstarEq_e6Coprime hp hlab hS).mono
      (fun _ _ _ _ ⟨hb, r, hr, hrk⟩ =>
        ⟨hb, r, hr, ggINormAbove_of_iRankLe hp.one_lt hrk⟩))
    (fun _ _ _ _ _ _ hP => hP.1) hRig
  exact ggRes_bstar_eq_of_bound_norm_marking hH
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2, hP.2⟩) hMark)

theorem GGResHyp.bstar_eq_of_splitE6_field
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGInnerDiagOnLabel
      (fun p lab => lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3 ∧ p ∣ lab.n) p Bs L) :
    B = Bs := by
  have hMark := largeEvenMarking_and_labelAll
    (S := fun lab => lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3 ∧ p ∣ lab.n)
    (P' := fun R _ I _ =>
      (∃ r, GGTorusLift p r R ∧ GGInnerDiagBound p r R I) ∧
        ∃ r, GGTorusLift p r R ∧ GGINormAbove p r R I)
    (fun lab hlab hS =>
      largeEvenLabelAll_and
        (largeEvenLabelAll_innerDiagBound_field hp hlab (Or.inr (Or.inr (Or.inl hS))))
        (IOneMore.largeEvenLabelAll_normAbove_field hp hlab
          (Or.inr (Or.inr (Or.inl hS)))))
    (fun _ _ _ _ _ _ hP => hP.1) hRig
  exact ggRes_bstar_eq_of_bound_norm_marking hH
    (largeEvenMarking_mono (fun _ _ _ _ _ _ hP => ⟨hP.1.2, hP.2⟩) hMark)

theorem GGResHyp.bstar_eq_of_splitE6_all
    {G : Type} [Group G] [Finite G] {p : ℕ} (hp : p.Prime)
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hRig : GGInnerDiagOnLabel
      (fun _ lab => lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1) p Bs L) :
    B = Bs := by
  classical
  by_cases hp3 : p = 3
  · exact GGResHyp.bstar_eq_of_splitE6 hH
      (largeEvenMarking_mono
        (fun _ _ _ _ _ _ hP => ⟨⟨hp3, hP.1⟩, hP.2⟩) hRig)
  · have hSplit : GGInnerDiagOnLabel
        (fun _ lab =>
          (lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3 ∧ ¬ p ∣ lab.n) ∨
          (lab.tag = .E6 ∧ p ∣ 2 ^ lab.n - 1 ∧ p ≠ 3 ∧ p ∣ lab.n)) p Bs L :=
      largeEvenMarking_mono (fun lab _ _ _ _ _ hP => by
        refine ⟨?_, hP.2⟩
        by_cases hpn : p ∣ lab.n
        · exact Or.inr ⟨hP.1.1, hP.1.2, hp3, hpn⟩
        · exact Or.inl ⟨hP.1.1, hP.1.2, hp3, hpn⟩) hRig
    rcases GGInnerDiagOnLabel.elim_or hSplit with hCop | hField
    · exact GGResHyp.bstar_eq_of_splitE6_coprime hp hH hCop
    · exact GGResHyp.bstar_eq_of_splitE6_field hp hH hField

end CFSG.StandardType

namespace CFSG.StandardType

section OriginalLDatum

open CFSG.Assembly Module

theorem GGResHyp.card_Bs_six_or_seven_of_original_L_E6_datum
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    {sel : Prop → Prop → Prop}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K sel ggTypLE6) :
    Nat.card Bs = 3 ^ 6 ∨ Nat.card Bs = 3 ^ 7 := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK,
    hsel, hfL, hfK, hclosL, hclosK, hconn, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  obtain ⟨e, hML'⟩ := htyp
  let h' : Fin 6 → V := fun i => h (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let xV : V := ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs))
  have hxV : xV ≠ 0 := by
    intro h0
    have h0' : ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs)) = 0 := h0
    have h1 : (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs) = 1 := by
      have h2 : Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs) = 0 :=
        ι.injective (h0'.trans (map_zero ι).symm)
      simpa using (Additive.ofMul.injective h2)
    have hS : LargeEvenSStar 3 B x L := hH.1.1.2.2.2.2.2.2.1
    exact hS.2.2.1 (congrArg (fun z : ↥Bs => (z : G)) h1)
  have hpair' : ∀ i j, α' i (h' j) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpair (e i) (e j), e6Cartan_reindex e hCL hML']
  have hxα : ∀ i : Fin 6, α' i xV = 0 := by
    intro i
    have hφi : φ (Sum.inl (e i)) ∈ ggAutomizer L Bs := by
      rw [hclosL]
      exact Subgroup.subset_closure ⟨e i, rfl⟩
    have hfixb := ggResI_automizer_fix hH.1.tableB_facts.2.2.1
      hH.1.tableB_facts.2.2.2.1 (φ (Sum.inl (e i))) hφi
    have hfixV : ggLin (p := 3) ι (φ (Sum.inl (e i))) xV = xV := by
      change ggLin (p := 3) ι (φ (Sum.inl (e i)))
        (ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs))) = _
      rw [ggLin_apply_ofMul, hfixb]
    exact ggResI_alpha_eq_zero_of_refl ι (hlin (Sum.inl (e i)))
      (hrefl (Sum.inl (e i))) hfixV
  have hca : 0 < Fintype.card Λa := by
    rw [← Nat.card_eq_fintype_card]
    omega
  let a0 : Λa := Classical.choice (Fintype.card_pos_iff.mp hca)
  have hfix : ∀ v, (∀ i : Fin 6, α' i v = 0) ↔
      v ∈ Submodule.span (ZMod 3) ({xV} : Set V) := by
    intro v
    constructor
    · intro hv
      have hvΛ : ∀ i : Λ, α (Sum.inl i) v = 0 := by
        intro i
        simpa [α'] using hv (e.symm i)
      obtain ⟨c, hc⟩ := ggRes_raw_commonKernel_le_xline ggTBFixInput_holds hH
        a0 ι φ h α hlin hclosL v hvΛ
      rw [Submodule.mem_span_singleton]
      exact ⟨c, hc.symm⟩
    · intro hv
      rw [Submodule.mem_span_singleton] at hv
      obtain ⟨c, rfl⟩ := hv
      intro i
      rw [map_smul, hxα i, smul_zero]
  have hdim := E6QTwo.finrank_six_or_seven_of_common_kernel h' α' xV hxV hfix hpair'
  have hVpow : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V))
  have hcard : Nat.card Bs = 3 ^ Module.finrank (ZMod 3) V := by
    rw [← Nat.card_congr Additive.toMul, Nat.card_congr ι.toEquiv, hVpow]
  rcases hdim with h6 | h7
  · exact Or.inl (hcard.trans (by rw [h6]))
  · exact Or.inr (hcard.trans (by rw [h7]))

theorem GGResHyp.card_Bs_le_three_pow_seven_of_original_L_E6_datum
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    {sel : Prop → Prop → Prop}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K sel ggTypLE6) :
    Nat.card Bs ≤ 3 ^ 7 := by
  rcases GGResHyp.card_Bs_six_or_seven_of_original_L_E6_datum hH hD with h6 | h7
  · rw [h6]
    norm_num
  · rw [h7]

theorem e6_dependent_fixed_axis_coordinates_of_original_L
    {G : Type} [Group G] [Finite G]
    {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {Λ Λa : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λa] [DecidableEq Λa]
    (a0 : Λa)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (htyp : GGIsTypeE6 ML) (hCL : GGIntCartan ML CL)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpair : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hsel : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)))
    (hdim : Module.finrank (ZMod 3) V = 7) :
    ∃ (e : Fin 6 ≃ Λ) (c : V ≃ₗ[ZMod 3] ((Fin 6 → ZMod 3) × ZMod 3)),
      ML = CoxeterMatrix.E₆.reindex e ∧
      c (ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs))) = (0, 1) ∧
      (∀ i, c (h (Sum.inl (e i))) =
        ((fun j => (CartanMatrix.E 6 j i : ZMod 3)), 0)) ∧
      (∀ v, (c v).1 = fun i => α (Sum.inl (e i)) v) ∧
      (∀ i v, c (v - α (Sum.inl (e i)) v • h (Sum.inl (e i))) =
        ((c v).1 - (c v).1 i • (fun j => (CartanMatrix.E 6 j i : ZMod 3)), (c v).2)) := by
  classical
  obtain ⟨e, hML⟩ := htyp
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  let h' : Fin 6 → V := fun i => h (Sum.inl (e i))
  let α' : Fin 6 → Module.Dual (ZMod 3) V := fun i => α (Sum.inl (e i))
  let xV : V := ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs))
  have hxV : xV ≠ 0 := by
    intro h0
    have h0' : ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs)) = 0 := h0
    have h1 : (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs) = 1 := by
      have h2 : Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs) = 0 :=
        ι.injective (h0'.trans (map_zero ι).symm)
      simpa using (Additive.ofMul.injective h2)
    have hS : LargeEvenSStar 3 B x L := hH.1.1.2.2.2.2.2.2.1
    exact hS.2.2.1 (congrArg (fun z : ↥Bs => (z : G)) h1)
  have hpair' : ∀ i j, α' i (h' j) = (CartanMatrix.E 6 i j : ZMod 3) := by
    intro i j
    rw [hpair (e i) (e j), e6Cartan_reindex e hCL hML]
  have hxα : ∀ i : Fin 6, α' i xV = 0 := by
    intro i
    have hφi : φ (Sum.inl (e i)) ∈ ggAutomizer L Bs := by
      rw [hclosL]
      exact Subgroup.subset_closure ⟨e i, rfl⟩
    have hfixb := ggResI_automizer_fix hH.1.tableB_facts.2.2.1
      hH.1.tableB_facts.2.2.2.1 (φ (Sum.inl (e i))) hφi
    have hfixV : ggLin (p := 3) ι (φ (Sum.inl (e i))) xV = xV := by
      change ggLin (p := 3) ι (φ (Sum.inl (e i)))
        (ι (Additive.ofMul (⟨x, hH.1.tableB_facts.2.2.1⟩ : ↥Bs))) = _
      rw [ggLin_apply_ofMul, hfixb]
    have h2i : α (Sum.inl (e i)) (h (Sum.inl (e i))) = 2 := by
      rw [hpair (e i) (e i), e6Cartan_reindex e hCL hML]
      norm_num [CartanMatrix.E]
    have hrefli : GGIsReflection 3 (φ (Sum.inl (e i))) :=
      ggIsReflection_of_eq_reflection (p := 3) (by norm_num) ι h2i
        (ggLin_eq_reflection ι h2i (hlin (Sum.inl (e i))))
    exact ggResI_alpha_eq_zero_of_refl ι (hlin (Sum.inl (e i))) hrefli hfixV
  have hdep : ¬ LinearIndependent (ZMod 3) h' := by
    intro hLI
    apply hsel
    have hLI' : LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i)) :=
      (linearIndependent_equiv e (f := fun i : Λ => h (Sum.inl i))).mp
        (by simpa only [h', Function.comp_def] using hLI)
    exact hLI'
  have hfix : ∀ v, (∀ i : Fin 6, α' i v = 0) ↔
      v ∈ Submodule.span (ZMod 3) ({xV} : Set V) := by
    intro v
    constructor
    · intro hv
      have hvΛ : ∀ i : Λ, α (Sum.inl i) v = 0 := by
        intro i
        simpa [α'] using hv (e.symm i)
      obtain ⟨c, hc⟩ := ggRes_raw_commonKernel_le_xline ggTBFixInput_holds hH
        a0 ι φ h α hlin hclosL v hvΛ
      rw [Submodule.mem_span_singleton]
      exact ⟨c, hc.symm⟩
    · intro hv
      rw [Submodule.mem_span_singleton] at hv
      obtain ⟨c, rfl⟩ := hv
      intro i
      rw [map_smul, hxα i, smul_zero]
  obtain ⟨c, hcx, hch, hcα, hcact⟩ :=
    E6QTwo.exists_e6_dependent_fixed_axis_coordinates h' α' xV hdep hxV hdim hfix hpair'
  exact ⟨e, c, hML, hcx, hch, hcα, hcact⟩

private noncomputable def e6DualSevenProdCoordinates :
    ((Fin 6 → ZMod 3) × ZMod 3) ≃ₗ[ZMod 3] (Fin 7 → ZMod 3) :=
  (LinearEquiv.piFinSnoc (ZMod 3) (fun _ : Fin 7 => ZMod 3)).symm

private lemma e6DualSevenProdCoordinates_apply (p : (Fin 6 → ZMod 3) × ZMod 3) :
    e6DualSevenProdCoordinates p = Fin.snoc p.1 p.2 :=
  LinearEquiv.piFinSnoc_symm_apply (ZMod 3) (fun _ : Fin 7 => ZMod 3) p

private lemma e6DualSevenProdCoordinates_col (i : Fin 6) :
    e6DualSevenProdCoordinates ((fun j : Fin 6 => (CartanMatrix.E 6 j i : ZMod 3)), 0) =
      E6DependentDualSeven.e6Col i := by
  rw [e6DualSevenProdCoordinates_apply]
  rfl

private lemma e6DualSeven_simple_apply (i : Fin 6) (v : Fin 7 → ZMod 3) :
    E6DependentDualSeven.s i v =
      v - v i.castSucc • E6DependentDualSeven.e6Col i := by
  rw [E6DependentDualSeven.s, Module.reflection_apply, E6DependentDualSeven.e6F]
  rfl

theorem e6_dependent_dual_transport_of_raw
    {G : Type} [Group G] [Finite G] {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    {Λ Λa : Type} [Fintype Λ] [DecidableEq Λ] [Fintype Λa] [DecidableEq Λa]
    (a0 : Λa) (S : Finset Λ)
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (ι : Additive ↥Bs ≃+ V)
    (φ : Λ ⊕ Λa → MulAut ↥Bs) (h : Λ ⊕ Λa → V)
    (α : Λ ⊕ Λa → Module.Dual (ZMod 3) V)
    (hcard : Nat.card Bs = 3 ^ 7)
    (htyp : GGIsTypeE6 ML) (hCL : GGIntCartan ML CL)
    (hlin : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hpair : ∀ i j : Λ, α (Sum.inl i) (h (Sum.inl j)) = (CL i j : ZMod 3))
    (hclosL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (Sum.inl i)))
    (hclosK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ∉ S} => φ (Sum.inl j)) ∪
        Set.range fun a : Λa => φ (Sum.inr a)))
    (hsel : ¬ LinearIndependent (ZMod 3) (fun i : Λ => h (Sum.inl i))) :
    ∃ (e : Fin 6 ≃ Λ) (ι7 : Additive ↥Bs ≃+ (Fin 7 → ZMod 3))
      (H : Subgroup ((Fin 7 → ZMod 3) ≃ₗ[ZMod 3] (Fin 7 → ZMod 3))),
      (∀ i, ggLin (p := 3) ι7 (φ (Sum.inl (e i))) = E6DependentDualSeven.s i) ∧
      H = (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι7) ∧
      QTwoLin.TransvectionFree H ∧
      (∀ i, E6DependentDualSeven.s i ∈ H) ∧
      (∀ a : Λa, ggLin (p := 3) ι7 (φ (Sum.inr a)) ∈ H) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  haveI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have hcardV : Nat.card V = 3 ^ 7 := by
    rw [← Nat.card_congr ι.toEquiv]
    exact hcard
  have hVpow : Nat.card V = 3 ^ Module.finrank (ZMod 3) V := by
    simpa using (Module.natCard_eq_pow_finrank (K := ZMod 3) (V := V))
  have hdim : Module.finrank (ZMod 3) V = 7 :=
    Nat.pow_right_injective (by norm_num : 2 ≤ 3) (hVpow.symm.trans hcardV)
  obtain ⟨e, c, -, -, hch, hcα, -⟩ :=
    e6_dependent_fixed_axis_coordinates_of_original_L hH a0 ι φ h α
      htyp hCL hlin hpair hclosL hsel hdim
  let ι7 : Additive ↥Bs ≃+ (Fin 7 → ZMod 3) :=
    ι.trans (c.toAddEquiv.trans e6DualSevenProdCoordinates.toAddEquiv)
  let H := (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι7)
  have hι7_apply (b : ↥Bs) :
      ι7 (Additive.ofMul b) = e6DualSevenProdCoordinates (c (ι (Additive.ofMul b))) := rfl
  have hcoord (i : Fin 6) (v : V) :
      (e6DualSevenProdCoordinates (c v)) i.castSucc = (c v).1 i := by
    rw [e6DualSevenProdCoordinates_apply, Fin.snoc_castSucc]
  have hs (i : Fin 6) :
      ggLin (p := 3) ι7 (φ (Sum.inl (e i))) = E6DependentDualSeven.s i := by
    apply LinearEquiv.ext
    intro v
    obtain ⟨b, rfl⟩ := (Additive.ofMul.trans ι7.toEquiv).surjective v
    change ggLin (p := 3) ι7 (φ (Sum.inl (e i))) (ι7 (Additive.ofMul b)) =
      E6DependentDualSeven.s i (ι7 (Additive.ofMul b))
    rw [ggLin_apply_ofMul]
    rw [hι7_apply, hι7_apply]
    have hstep : ι (Additive.ofMul (φ (Sum.inl (e i)) b)) =
        ι (Additive.ofMul b) - α (Sum.inl (e i)) (ι (Additive.ofMul b)) •
          h (Sum.inl (e i)) := by
      rw [← ggLin_apply_ofMul (p := 3) ι (φ (Sum.inl (e i))) b]
      exact hlin (Sum.inl (e i)) (ι (Additive.ofMul b))
    rw [hstep, map_sub, map_smul, hch i]
    rw [show α (Sum.inl (e i)) (ι (Additive.ofMul b)) = (c (ι (Additive.ofMul b))).1 i by
      simpa using (congrFun (hcα (ι (Additive.ofMul b))) i).symm]
    rw [map_sub, map_smul, e6DualSevenProdCoordinates_col, e6DualSeven_simple_apply, hcoord]
  have hTF : QTwoLin.TransvectionFree H := by
    have htop := ggQ2P3P_transvectionFree (p := 3) ι7 hH.2.2.2.1
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨ψ, hψ, rfl⟩ := hg
    exact htop _ (Subgroup.mem_map.mpr
      ⟨ψ, Subgroup.subset_closure (ggResI_mem_ggInduced_top hψ), rfl⟩)
  have hsimple : ∀ i, E6DependentDualSeven.s i ∈ H := by
    intro i
    refine Subgroup.mem_map.mpr ⟨φ (Sum.inl (e i)), ?_, hs i⟩
    refine (show ggAutomizer L Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs from le_sup_left) ?_
    rw [hclosL]
    exact Subgroup.subset_closure ⟨e i, rfl⟩
  have haddmem : ∀ a : Λa, ggLin (p := 3) ι7 (φ (Sum.inr a)) ∈ H := by
    intro a
    refine Subgroup.mem_map.mpr ⟨φ (Sum.inr a), ?_, rfl⟩
    refine (show ggAutomizer K Bs ≤ ggAutomizer L Bs ⊔ ggAutomizer K Bs from le_sup_right) ?_
    rw [hclosK]
    exact Subgroup.subset_closure (Or.inr ⟨a, rfl⟩)
  exact ⟨e, ι7, H, hs, rfl, hTF, hsimple, haddmem⟩

theorem GGResHyp.weyl_join_of_original_L_E6_dep_card_seven
    {G : Type} [Group G] [Finite G] {B Bs L D J K : Subgroup G} {x y : G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelDep ggTypLE6)
    (hcard : Nat.card Bs = 3 ^ 7) :
    GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  obtain ⟨Λ, i1, i2, S, Λa, i3, i4, ML, CL, MK, CK, V, i5, i6, ι, φ, h, α,
    hS, hA1, hA3, hML, hCL, hMK, hCK, htyp, hlin, hrefl, hpair, hpairK,
    hsel, hfL, hfK, hclosL, hclosK, hconn, hclosJ⟩ := hD
  letI := i1
  letI := i2
  letI := i3
  letI := i4
  letI := i5
  letI := i6
  have hca : 0 < Fintype.card Λa := by
    rw [← Nat.card_eq_fintype_card]
    omega
  let a0 : Λa := Classical.choice (Fintype.card_pos_iff.mp hca)
  have htransport := e6_dependent_dual_transport_of_raw hH a0 S ι φ h α hcard
    (by simpa only [ggTypLE6] using htyp) hCL hlin hpair hclosL hclosK
    (by simpa only [ggSelDep] using hsel)
  exact ggWeylJoin_of_e6DualSeven_transport S hS hA1 hML hMK φ hrefl
    hfL.choose hfL.choose_spec hfK.choose hfK.choose_spec hclosL hclosK htransport

end OriginalLDatum

end CFSG.StandardType

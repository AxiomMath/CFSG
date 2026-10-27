module

public import CFSG.LocalAnalysis.StandardType.GGResExactTwoOrthSmallDefs
import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
import CFSG.LocalAnalysis.StandardType.GGPZWeylType
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSideCoord
import CFSG.LocalAnalysis.StandardType.GGHdRo7DFrameOmega
import CFSG.LocalAnalysis.StandardType.GGHdRo7DLModel
import CFSG.LocalAnalysis.StandardType.GGHdRo7CLin
import CFSG.LocalAnalysis.StandardType.GGHdRo7DAJ
import CFSG.LocalAnalysis.StandardType.GGHdRo7SULCoordSplit
import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBIrred
import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelTypeABridge
import CFSG.LocalAnalysis.StandardType.GGTWLowStmt
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSideData
import CFSG.LocalAnalysis.StandardType.GGHdRo7CoprimeSplit
import CFSG.LocalAnalysis.StandardType.GGTableBBstar
import CFSG.LocalAnalysis.StandardType.GGTableBNoncyclic
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperRestDefs
import CFSG.LocalAnalysis.StandardType.GGStdSubIOneProperMoreOrth

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem ggResX2Aux_card_le_of_c2sp {p : ℕ} [Fact p.Prime] (hp3 : p = 3) {E : Type} [Group E]
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] {n : ℕ}
    (b : Module.Basis (Fin (n + 1)) (ZMod p) V) (ι : Additive E ≃+ V)
    (A : Subgroup (MulAut E)) (hA : ∀ a ∈ A, HdRo7C.C2SP p b (ggLin (p := p) ι a)) :
    Nat.card A ≤ 2 ^ n * n.factorial := by
  classical
  have hdata : ∀ a : A, ∃ σc : Equiv.Perm (Fin (n + 1)) × (Fin (n + 1) → ZMod p),
      σc.1 0 = 0 ∧ σc.2 0 = 1 ∧ (∀ i, σc.2 i = 1 ∨ σc.2 i = -1) ∧
        ∀ i, ggLin (p := p) ι a (b i) = σc.2 i • b (σc.1 i) := by
    intro a
    obtain ⟨σ, c, hσ, hc0, hc, ha⟩ := hA a a.2
    exact ⟨(σ, c), hσ, hc0, hc, ha⟩
  choose d hd using hdata
  have hm1 : (-1 : ZMod p) ≠ 1 := by
    have : Fact (2 < p) := ⟨by omega⟩
    exact ZMod.neg_one_ne_one
  have hfst : ∀ σ : Equiv.Perm (Fin (n + 1)), (Equiv.Perm.decomposeFin σ).1 = σ 0 := by
    intro σ
    have h := Equiv.Perm.decomposeFin_symm_apply_zero (Equiv.Perm.decomposeFin σ).1
      (Equiv.Perm.decomposeFin σ).2
    rw [Prod.mk.eta, Equiv.symm_apply_apply] at h
    exact h.symm
  let F : A → Equiv.Perm (Fin n) × (Fin n → Bool) := fun a =>
    ((Equiv.Perm.decomposeFin (d a).1).2, fun i => decide ((d a).2 i.succ = 1))
  have hF : Function.Injective F := by
    intro a a' haa'
    simp only [F, Prod.mk.injEq] at haa'
    obtain ⟨h1, h2⟩ := haa'
    have hσ : (d a).1 = (d a').1 := by
      apply Equiv.Perm.decomposeFin.injective
      refine Prod.ext ?_ h1
      rw [hfst, hfst, (hd a).1, (hd a').1]
    have hc : (d a).2 = (d a').2 := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [(hd a).2.1, (hd a').2.1]
      · have hj := congrFun h2 j
        simp only [decide_eq_decide] at hj
        rcases (hd a).2.2.1 j.succ with h | h <;> rcases (hd a').2.2.1 j.succ with h' | h'
        · rw [h, h']
        · exact absurd (hj.mp h) (by rw [h']; exact hm1)
        · exact absurd (hj.mpr h') (by rw [h]; exact hm1)
        · rw [h, h']
    apply Subtype.ext
    apply ggLin_injective (p := p) ι
    refine b.ext' fun i => ?_
    rw [(hd a).2.2.2 i, (hd a').2.2.2 i, hσ, hc]
  calc Nat.card A ≤ Nat.card (Equiv.Perm (Fin n) × (Fin n → Bool)) :=
        Nat.card_le_card_of_injective F hF
    _ = 2 ^ n * n.factorial := by
      rw [Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_perm, Fintype.card_fun,
        Fintype.card_fin, Fintype.card_bool]
      ring

private theorem ggResX2Aux_rank_eq_of_weylTypeData {r N c n : ℕ} (hW : GGWeylTypeData r N c)
    (hnr : n ≤ r) (hN : N ≤ 2 ^ n * n.factorial) (hn3 : 3 ≤ n) (hn5 : n ≤ 5) : r = n := by
  have h5 : 2 ^ n * n.factorial ≤ 3840 :=
    calc 2 ^ n * n.factorial ≤ 2 ^ 5 * Nat.factorial 5 :=
          Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hn5) (Nat.factorial_le hn5)
      _ = 3840 := by decide
  rcases hW with ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨-, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ |
      ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩ | ⟨rfl, rfl, -⟩
  · have hr : r ≤ 5 := by
      by_contra h
      have h7 : Nat.factorial 7 ≤ Nat.factorial (r + 1) := Nat.factorial_le (by omega)
      have : Nat.factorial 7 = 5040 := by decide
      omega
    interval_cases n <;> interval_cases r <;> first | rfl | (exfalso; revert hN; decide)
  · have hr : r ≤ 5 := by
      by_contra h
      have h6 : 2 ^ 6 * Nat.factorial 6 ≤ 2 ^ r * Nat.factorial r :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.factorial_le (by omega))
      have : 2 ^ 6 * Nat.factorial 6 = 46080 := by decide
      omega
    interval_cases n <;> interval_cases r <;> first | rfl | (exfalso; revert hN; decide)
  · have hr : r ≤ 5 := by
      by_contra h
      have h6 : 2 ^ 5 * Nat.factorial 6 ≤ 2 ^ (r - 1) * Nat.factorial r :=
        Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) (by omega)) (Nat.factorial_le (by omega))
      have : 2 ^ 5 * Nat.factorial 6 = 23040 := by decide
      omega
    interval_cases n <;> interval_cases r <;> first | rfl | (exfalso; revert hN; decide)
  all_goals first | omega | (interval_cases n <;> (exfalso; revert hN; decide))

theorem ggResExactTwoOrth_fix_iff (hRig : GGLabelRigidInput) (hFix : GGResExactTwoOrthFixLeaf)
    {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hlab : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
      lab.n = 1 ∧ (lab.rank = 4 ∨ lab.rank = 5)) p Bs L) (b : ↥Bs) :
    (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔ (b : G) ∈ Subgroup.centralizer (J : Set G) := by
  refine ⟨hFix hRig G p B Bs x L D J hcfg (largeEvenMarking_mono
    (fun _ _ _ _ _ _ ⟨⟨h1, h2, h3, h4⟩, h5⟩ => ⟨⟨h1, h2, h3, by omega⟩, h5⟩) hlab) b,
    fun hb φ hφ => ggAutomizer_apply_eq_of_le_centralizer (fun g hg => ?_) hφ⟩
  exact Subgroup.mem_centralizer_singleton_iff.mpr (Subgroup.mem_centralizer_iff.mp hb g hg)

theorem ggResExactTwoOrth_card_bstar_inf_L (hRig : GGLabelRigidInput) {G : Type} [Group G]
    [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig p B Bs x L D J)
    (hlab : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
      lab.n = 1 ∧ 4 ≤ lab.rank) p Bs L) :
    p ^ 3 ≤ Nat.card ↥(Bs ⊓ L) ∧ ∃ S : Subgroup G, S ≤ L ∧ IsPGroup p S ∧ ¬ IsCyclic S := by
  obtain ⟨hp, hEA, hxBs, -, h4⟩ := hcfg.tableB_facts
  have hM : GGInnerDiagOn Bs L := largeEvenMarking_mono (fun _ _ _ _ _ _ hP => hP.2) hlab
  obtain ⟨lab, hΛ2, hhas, R, _, I, F, θ, ⟨hp3, htag, hn, hr⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hlab
  obtain ⟨hBsN, hinner, hcop, -⟩ :=
    HdRo7D.d_sideData hRig HdRo7D.d_frameOmega_holds hp3 hM hΛ2 hhas htag hn hr
  have hsplit := ggBstar_split_of_inner_coprime hp hcfg.2.1
    ((Nat.Prime.coprime_iff_not_dvd hp).mpr hcop) hBsN hinner
  have hS : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have hC : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    inf_centralizer_eq_zpowers_of_elemAbelian hp hBs.2.1 (hBs.1 hS.2.1) hS.2.2.1
      hS.2.2.2.1.1 hS.2.2.2.2
  have := Fact.mk hp
  have hxp : Nat.card ↥(Subgroup.zpowers x) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hEA.2 x hxBs) hS.2.2.1
  have hle : Nat.card Bs ≤ Nat.card ↥(Bs ⊓ L) * p := by
    let f : ↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) → ↥Bs :=
      fun q => ⟨(q.1 : G) * (q.2 : G), Bs.mul_mem q.1.2.1 q.2.2.1⟩
    have hf : Function.Surjective f := by
      rintro ⟨b, hb⟩
      obtain ⟨t, ht, c, hc, rfl⟩ := hsplit b hb
      exact ⟨(⟨t, ht⟩, ⟨c, hc⟩), rfl⟩
    calc Nat.card Bs ≤ Nat.card (↥(Bs ⊓ L) × ↥(Bs ⊓ Subgroup.centralizer (L : Set G))) :=
          Nat.card_le_card_of_surjective f hf
      _ = Nat.card ↥(Bs ⊓ L) * p := by rw [Nat.card_prod, hC, hxp]
  have h3 : p ^ 3 ≤ Nat.card ↥(Bs ⊓ L) := by
    have h' : p ^ 3 * p ≤ Nat.card ↥(Bs ⊓ L) * p := by
      rw [← pow_succ]
      exact h4.trans hle
    exact Nat.le_of_mul_le_mul_right h' hp.pos
  refine ⟨h3, Bs ⊓ L, inf_le_right, fun g => ⟨1, ?_⟩, fun hcyc => ?_⟩
  · rw [pow_one]
    exact Subtype.ext (hEA.2 (g : G) g.2.1)
  · obtain ⟨g, hg⟩ := hcyc.exists_generator
    have hord : orderOf g = Nat.card ↥(Bs ⊓ L) := orderOf_eq_card_of_forall_mem_zpowers hg
    have hdvd : orderOf g ∣ p := orderOf_dvd_of_pow_eq_one (Subtype.ext (hEA.2 (g : G) g.2.1))
    have hcle : Nat.card ↥(Bs ⊓ L) ≤ p := hord ▸ Nat.le_of_dvd hp.pos hdvd
    have hpp : p < p ^ 3 :=
      lt_of_eq_of_lt (pow_one p).symm (Nat.pow_lt_pow_right hp.one_lt (by norm_num))
    omega

section Certs


private theorem ggResX2Aux_finrank_eq_card_add_one (hRig : GGLabelRigidInput) {G : Type}
    [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    (hlab : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
      lab.n = 1 ∧ (lab.rank = 4 ∨ lab.rank = 5)) p Bs L)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {ML : CoxeterMatrix Λ} (hWL : GGIsWeylMatrix ML)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] (ι : Additive ↥Bs ≃+ V)
    (φL : Λ → MulAut ↥Bs) (hL : Λ → V) (αL : Λ → Module.Dual (ZMod p) V)
    (hform : ∀ i w, ggLin (p := p) ι (φL i) w = w - αL i w • hL i)
    (fL : ML.Group ≃* ↥(ggAutomizer L Bs))
    (hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range φL)) :
    Module.finrank (ZMod p) V = Fintype.card Λ + 1 := by
  classical
  obtain ⟨lab, hΛ2, hhas, R, _, I, F, θ, ⟨hp3, htag, hn, hr⟩, -⟩ :=
    largeEvenMarking_exists_hasLabel hlab
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨-, -, hxBs, -, h4⟩ := hcfg.tableB_facts
  have hSstar : LargeEvenSStar p B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSstar.2.2.1
  have hBs : GGBstar p B Bs := hcfg.2.1
  have hM : GGInnerDiagOn Bs L := hH.2.2.1.1
  have hC : Bs ⊓ Subgroup.centralizer (L : Set G) = Subgroup.zpowers x :=
    HdRo7SU.hdRo7SULCoordAux_centralizer hH hp3
  obtain ⟨n, τ, hτ, hmod⟩ := HdRo7D.d_sideCoord_exact HdRo7D.d_frameOmega_holds hRig hxBs hp3
    hBs hM hΛ2 hhas htag hn (by omega) hx1 hC h4
  have hn35 : 3 ≤ n ∧ n ≤ 5 := by rcases hmod with ⟨h, -⟩ | ⟨h, -⟩ <;> omega
  obtain ⟨V', hV', hVp', ι', b, hsub, hc2⟩ : ∃ (V' : Type) (_ : AddCommGroup V')
      (_ : Module (ZMod p) V') (ι' : Additive ↥Bs ≃+ V')
      (b : Module.Basis (Fin (n + 1)) (ZMod p) V'),
      (∀ g, HdRo7D.DSP p b g → g ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι')) ∧
        ∀ g ∈ (ggAutomizer L Bs).map (ggLin (p := p) ι'), HdRo7C.C2SP p b g := by
    rcases hmod with ⟨-, hcoord⟩ | ⟨-, hcoord⟩
    · obtain ⟨V', hV', hVp', ι', b, -, hAL⟩ :=
        HdRo7D.d_linearModel_of_dcoord p Bs L n x hxBs τ hτ hcoord
      exact ⟨V', hV', hVp', ι', b, fun g hg => (hAL g).mpr hg,
        fun g hg => HdRo7D.hdRo7DAJAux_dsp_c2sp b ((hAL g).mp hg)⟩
    · obtain ⟨V', hV', hVp', ι', b, -, hAL⟩ :=
        HdRo7C.c2_linearModel_of_coord p Bs L n x hxBs τ hτ hcoord
      exact ⟨V', hV', hVp', ι', b, fun g hg => (hAL g).mpr (HdRo7D.hdRo7DAJAux_dsp_c2sp b hg),
        fun g hg => (hAL g).mp hg⟩
  have hnΛ : n ≤ Nat.card Λ :=
    HdRo7D.hdRo7DAJAux_model_card_le b ι' hp3 (by omega) hsub ι φL hL αL hform hgenL
  have hAL : Nat.card ↥(ggAutomizer L Bs) ≤ 2 ^ n * n.factorial :=
    ggResX2Aux_card_le_of_c2sp hp3 b ι' (ggAutomizer L Bs) fun a ha => hc2 _ ⟨a, ha, rfl⟩
  have hW := ggWeylTypeData_of_isWeylMatrix hWL
  rw [Nat.card_congr fL.toEquiv] at hW
  have hΛn : Fintype.card Λ = n := ggResX2Aux_rank_eq_of_weylTypeData hW
    (by rwa [Nat.card_eq_fintype_card] at hnΛ) hAL hn35.1 hn35.2
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have : Finite V' := Finite.of_equiv _ ι'.toEquiv
  have : Module.Finite (ZMod p) V := Module.Finite.of_finite
  have : Module.Finite (ZMod p) V' := Module.Finite.of_finite
  have hp : p.Prime := Fact.out
  have hcardV : p ^ Module.finrank (ZMod p) V = p ^ (n + 1) := by
    have e1 : Nat.card V = Nat.card V' := Nat.card_congr (ι.symm.trans ι').toEquiv
    have e2 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V)
    have e3 := Module.natCard_eq_pow_finrank (K := ZMod p) (V := V')
    rw [Nat.card_zmod] at e2 e3
    rw [← e2, e1, e3, Module.finrank_eq_card_basis b, Fintype.card_fin]
  rw [hΛn]
  exact Nat.pow_right_injective hp.two_le hcardV

theorem ggResExactTwoOrth_centralizer_J (hRig : GGLabelRigidInput)
    (hFix : GGResExactTwoOrthFixLeaf) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hlab : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
      lab.n = 1 ∧ (lab.rank = 4 ∨ lab.rank = 5)) p Bs L)
    (hdat : GGResLeviDatumExact2 p Bs L J K ggSelAny ggTypAny) :
    D < Bs ⊓ Subgroup.centralizer (J : Set G) ∧
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) = p ^ 3 := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨-, -, -, -, -, -, -, -, ⟨hp3, -⟩, -⟩ := largeEvenMarking_exists_hasLabel hlab
  obtain ⟨Λ, instΛ, decΛ, S, Λa, instΛa, decΛa, ML, CL, MK, CK, V, instV, instMod, ι, φ, h, α,
    hk, -, -, hWL, hCL, -, -, -, hform, -, hpL, -, -, ⟨fL, -⟩, -, hgenL, -, -, hgenJ⟩ := hdat
  have hdim := ggResX2Aux_finrank_eq_card_add_one hRig hH hlab hWL ι (fun i => φ (Sum.inl i))
    (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i)) (fun i w => hform (Sum.inl i) w) fL hgenL
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hfixJ := ggResExactTwoOrth_fix_iff hRig hFix hcfg hlab
  have hp2 : p ≠ 2 := by omega
  have hfix3 := ggResExact2_fix_eq_three_of_finrank_eq_card_add_one hp2 ι hCL
    (fun i => φ (Sum.inl i)) (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i))
    (fun i w => hform (Sum.inl i) w) hpL hk hgenJ hdim (ggResExact2_fix_le_three hH hfixJ ι)
  have hcard := ggResExact2_centralizer_J_card_eq_pow_three_of_fix_eq_three hfixJ ι hfix3
  exact ⟨ggResExact2_D_lt_centralizer_J_of_card_eq_pow_three hH hcard, hcard⟩

theorem ggResExactTwoOrth_card_deleted_le_two (hRig : GGLabelRigidInput)
    (hFix : GGResExactTwoOrthFixLeaf) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K)
    (hlab : GGInnerDiagOnLabel (fun p lab => p = 3 ∧ (lab.tag = .D ∨ lab.tag = .twD) ∧
      lab.n = 1 ∧ (lab.rank = 4 ∨ lab.rank = 5)) p Bs L)
    {k : ℕ} {sel : Prop → Prop → Prop}
    {typ : ∀ {Λ Λ' : Type}, CoxeterMatrix Λ → CoxeterMatrix Λ' → Prop}
    (hdat : GGResLeviDatumCard k p Bs L J K sel typ) : k ≤ 2 := by
  classical
  have hcfg : GGConfig p B Bs x L D J := hH.1
  obtain ⟨-, -, -, -, -, -, -, -, ⟨hp3, -⟩, -⟩ := largeEvenMarking_exists_hasLabel hlab
  obtain ⟨Λ, instΛ, decΛ, S, Λa, instΛa, decΛa, ML, CL, MK, CK, V, instV, instMod, ι, φ, h, α,
    hk, -, -, hWL, hCL, -, -, -, hform, -, hpL, -, -, ⟨fL, -⟩, -, hgenL, -, -, hgenJ⟩ := hdat
  have hdim := ggResX2Aux_finrank_eq_card_add_one hRig hH hlab hWL ι (fun i => φ (Sum.inl i))
    (fun i => h (Sum.inl i)) (fun i => α (Sum.inl i)) (fun i w => hform (Sum.inl i) w) fL hgenL
  have : Finite V := Finite.of_equiv _ ι.toEquiv
  have hfix3 := ggResExact2_fix_le_three hH (ggResExactTwoOrth_fix_iff hRig hFix hcfg hlab) ι
  have hdiagJ : ∀ i : {i : Λ // i ∉ S}, α (Sum.inl i.1) (h (Sum.inl i.1)) = 2 := by
    intro i
    rw [hpL i.1 i.1, hCL.1 i.1]
    norm_num
  have hker := ggFixedSubmodule_pi_ker (p := p) (Λ := Λ) (S := S) ι
    (fun i : {i : Λ // i ∉ S} => φ (Sum.inl i.1)) (fun i => h (Sum.inl i.1))
    (fun i => α (Sum.inl i.1)) (fun i w => hform (Sum.inl i.1) w) hdiagJ (by omega)
    (ggAutomizer J Bs) hgenJ
  have hle := finrank_le_card_add_finrank_ker_pi (p := p) (Λ := Λ) (S := S) (V := V)
    (fun i : {i : Λ // i ∉ S} => α (Sum.inl i.1))
  rw [hker] at hle
  have hsub : Fintype.card {i : Λ // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]
    simp
  have hcomp : Fintype.card {i : Λ // i ∉ S} = Fintype.card Λ - S.card := by
    rw [Fintype.card_subtype_compl (fun i : Λ => i ∈ S), hsub]
  have hSle : S.card ≤ Fintype.card Λ := S.card_le_univ
  omega


theorem ggResExactTwoOrthQTwoOn_four_five (hRig : GGLabelRigidInput)
    (hFix : GGResExactTwoOrthFixLeaf) (hD4 : GGResExactTwoOrthDFourLeaf)
    (hTwD5 : GGResExactTwoOrthTwDFiveLeaf) (hSel : GGResExactTwoOrthSelLeaf) :
    GGResExactTwoOrthQTwoOn fun r => r = 4 ∨ r = 5 := by
  rintro G _ _ p B Bs x L D J y K hH _ hF hS hE ⟨hlab, hdat, -⟩
  exfalso
  obtain ⟨hlt, hcard⟩ := ggResExactTwoOrth_centralizer_J hRig hFix hH hlab hdat
  have hcfg : GGConfig p B Bs x L D J := hH.1
  have hp : p.Prime := Fact.out
  obtain ⟨-, -, -, -, -, -, -, -, ⟨hp3, -⟩, -⟩ := largeEvenMarking_exists_hasLabel hlab
  have hne : B ≠ Bs := fun heq => (ne_of_lt hlt) (by
    rw [← heq]
    exact hcfg.2.2.1.2.2.2.2.2.2)
  have hlab' : GGInnerDiagOnLabel (fun p lab =>
      ((p = 3 ∧ lab.tag = .D ∧ lab.n = 1 ∧ lab.rank = 4) ∨
        (p = 3 ∧ lab.tag = .twD ∧ lab.n = 1 ∧ lab.rank = 5)) ∨
      (p = 3 ∧ lab.n = 1 ∧ ((lab.tag = .twD ∧ lab.rank = 4) ∨ (lab.tag = .D ∧ lab.rank = 5))))
      p Bs L := by
    refine largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨⟨h1, h2, h3, h4⟩, h5⟩ => ⟨?_, h5⟩) hlab
    rcases h2 with h2 | h2 <;> rcases h4 with h4 | h4
    · exact Or.inl (Or.inl ⟨h1, h2, h3, h4⟩)
    · exact Or.inr ⟨h1, h3, Or.inr ⟨h2, h4⟩⟩
    · exact Or.inr ⟨h1, h3, Or.inl ⟨h2, h4⟩⟩
    · exact Or.inl (Or.inr ⟨h1, h2, h3, h4⟩)
  rcases hlab'.elim_or with hl | hl
  · rcases hl.elim_or with hl | hl
    · have h9 := hD4 hRig G p B Bs x L D J hcfg hl
      rw [hcard, hp3] at h9
      norm_num at h9
    · have hsm := hTwD5 hRig G p B Bs x L D J hcfg hl (by rw [hcard, hp3]; norm_num)
      obtain ⟨D₁, K₁, hpre, hns⟩ := hSel hRig G p B Bs x L D J hcfg hl hne
      exact hcfg.2.2.2 ⟨hp3, D₁, K₁, hpre, hns⟩ hsm
  · have hBs : GGBstar p B Bs := hcfg.2.1
    have hnc := (ggResExactTwoOrth_card_bstar_inf_L hRig hcfg (largeEvenMarking_mono
      (fun _ _ _ _ _ _ ⟨⟨h1, h2, h3, h4⟩, h5⟩ => ⟨⟨h1, by
        rcases h2 with h2 | h2 <;> rcases h4 with h4 | h4 <;> simp_all, h3, by omega⟩, h5⟩)
      hlab)).2
    have hMB : LargeEvenMarking L (fun lab _ _ I _ θ =>
        (p = 3 ∧ lab.n = 1 ∧ ((lab.tag = .twD ∧ lab.rank = 4) ∨ (lab.tag = .D ∧ lab.rank = 5))) ∧
          B ≤ Subgroup.normalizer (L : Set G) ∧
          ∀ b ∈ B, ∃ φ ∈ I, LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ) :=
      largeEvenMarking_mono (fun _ _ _ _ _ _ ⟨h1, hN, h3⟩ =>
        ⟨h1, le_trans hBs.1 hN, fun b hb => h3 b (hBs.1 hb)⟩) hl
    have hM' := largeEvenMarking_and_labelAll (S := fun lab => p = 3 ∧ lab.n = 1 ∧
        ((lab.tag = .twD ∧ lab.rank = 4) ∨ (lab.tag = .D ∧ lab.rank = 5)))
      (fun lab _ hs => largeEvenLabelAll_bstarEq_orthEq hp (by omega) (by
        obtain ⟨h1, h2, ⟨h3, h4⟩ | ⟨h3, h4⟩⟩ := hs
        · refine Or.inl ⟨h3, by omega, ?_, ?_, ?_⟩
          · rw [h4]
            exact ⟨2, rfl⟩
          · rw [h1, h2]
            norm_num
          · rw [h1, h2]
            norm_num
        · exact Or.inr ⟨h3, by omega, by rw [h4]; exact ⟨2, rfl⟩, h2, h1⟩))
      (fun _ _ _ _ _ _ hP => hP.1) hMB
    obtain ⟨hL, lab, -, hraw⟩ := hM'
    obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBN, h3⟩, ⟨r₁, hl₁, hb⟩, r₂, hl₂, hr⟩ :=
      largeEvenRawDatum_exists hraw
    exact hne (bstar_eq_of_bound_rank hcfg.1 hBs hnc hL θ hBN h3 hl₁ hb hl₂ hr)

end Certs

end CFSG.StandardType

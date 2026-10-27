module

public import CFSG.Monster.Existence.Census.FusionGens
public import CFSG.Monster.B.TwoA.Census.CosetEnum
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumCheck
public meta import CFSG.Monster.B.TwoA.Census.CosetEnumBits
public meta import CFSG.Monster.B.TwoA.Census.NatCert
public meta import CFSG.Monster.B.TwoA.Census.CosetCertData
public meta import CFSG.Monster.B.TwoA.Census.MonoCert
public meta import CFSG.Monster.B.TwoA.Census.CosetSquares
public meta import CFSG.Monster.B.Rep4371.GlueDefs
public meta import CFSG.Monster.B.Rep4371.Model
public meta import CFSG.Monster.Existence.Census.FusionGens
public meta import Certificates.Data.CFSGNative.MonsterB.CosetEnum
public meta import Certificates.Data.CFSGNative.MonsterAxis.Dense
public import CFSG.Monster.Existence.Census.CosetOneFusionInputs
public import Certificates.Certificate6021
public import Certificates.Certificate6022
public import Certificates.Certificate6023
public import Certificates.Certificate6007
public import Certificates.Certificate1020
public import Certificates.Certificate1022
public import Certificates.Certificate3015
public import Certificates.Certificate3016
public import Certificates.Certificate3017
public import Certificates.Certificate3018
public import Certificates.Certificate3019
public import Certificates.Certificate3020
public import Certificates.Certificate3021
public import Certificates.Certificate3022
public import Certificates.Certificate3023
public import CFSG.Sporadic.ThSchreier.Max3Action

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence.Census

open CFSG.Monster CFSG.Monster.B CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.ScalarKernel CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated
  CFSG.Monster.AxisCount CFSG.Monster.B.TwoA.Census Matrix
open CFSG.Monster.B.Rep4371 hiding interp interp_eq_sum

theorem conj_letter_rho (g : Native.Gen) (hg : g.validB = true) (hne : ¬ g = Native.Gen.tau)
    (y : Model.Pauli) :
    g.toLin * rhoEquiv (pauliQ y) * g.toLin⁻¹ = rhoEquiv (pauliQ (betaOf g y)) := by
  cases g with
  | rho q =>
    rw [Native.Gen.toLin_rho]
    exact (thetaEquiv_conj_rhoEquiv (rhoPair (pauliQ q)) (pauliQ y)).trans
      (congrArg rhoEquiv (conjQ_rhoPair_toQ q y))
  | perm arr =>
    rw [Native.Gen.toLin_perm]
    exact (thetaEquiv_conj_rhoEquiv (permPairOf (permOf arr)) (pauliQ y)).trans
      (congrArg rhoEquiv (conjQ_perm_toQ (permOf arr) (permOf_spec hg) y))
  | sign a =>
    rw [Native.Gen.toLin_sign]
    exact (thetaEquiv_conj_rhoEquiv (signPair a) (pauliQ y)).trans
      (congrArg rhoEquiv (conjQ_sign_toQ a y))
  | xi =>
    rw [Native.Gen.toLin_xi]
    exact (thetaEquiv_conj_rhoEquiv xiPair (pauliQ y)).trans
      (congrArg rhoEquiv (conjQ_xi_toQ y))
  | tau => exact absurd rfl hne

theorem coe_cosetElt (i n : ℕ) :
    ((cosetElt i n : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) =
      (cosetRep i : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv (qOfEnc n) := rfl

theorem conj_cosetElt_one
    (g : Native.Gen) (c : Model.Pauli) (hg : g.validB = true)
    (hne : ¬ g = Native.Gen.tau)
    (hcomm : g.toLin * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) =
      (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv (pauliQ c) * g.toLin) (n : ℕ) :
    g.toLin * ((cosetElt 1 n : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) * g.toLin⁻¹ =
      ((cosetElt 1 (fusF g c n) : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) := by
  have e1 : g.toLin * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * g.toLin⁻¹ =
      (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv (pauliQ c) := by
    rw [hcomm]
    group
  have e2 := conj_letter_rho g hg hne (pauliDec n)
  have e3 : qOfEnc n = pauliQ (pauliDec n) := rfl
  have e4 : qOfEnc (fusF g c n) = pauliQ (betaOf g (pauliDec n)) * pauliQ c := by
    rw [fusF, qOfEnc_enc, pauliQ_mul]
  rw [coe_cosetElt, coe_cosetElt, e4, rhoEquiv_mul, ← e2, e3]
  calc g.toLin * ((cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * rhoEquiv (pauliQ (pauliDec n))) *
        g.toLin⁻¹ = (g.toLin * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) * g.toLin⁻¹) *
          (g.toLin * rhoEquiv (pauliQ (pauliDec n)) * g.toLin⁻¹) := by group
    _ = _ := by rw [e1]; group

theorem fusGens_match_fusionData :
    fusionData.generators.length = 11 ∧
      ((List.range 11).all fun j => match fusionData.generators[j]? with
        | some r => genMatches (fusGen j) r && (ofTriple r.shift == fusShift j)
        | none => false) = true := by
  refine ⟨by decide +kernel, ?_⟩
  exact Certificates.certificate6021.1

@[expose] noncomputable def fusElt (j : ℕ) : Gvis :=
  ⟨(fusGen j).toLin, Native.Gen.toLin_mem_Gvis _ (fusGen_ne_tau j)⟩

theorem fusGen_valid : ∀ j < 11, (fusGen j).validB = true :=
  Certificates.certificate6021.2.1

theorem foldl_mem_orbit {G X : Type*} [Group G] [MulAction G X] {H : Subgroup G} {m : ℕ}
    {act : ℕ → ℕ → ℕ} {gens : ℕ → G} {dec : ℕ → X} (hgens : ∀ k < m, gens k ∈ H)
    (hact : ∀ k < m, ∀ a, dec (act k a) = gens k • dec a) (w : List ℕ)
    (hw : w.all (· < m) = true) (n : ℕ) :
    dec (w.foldl (fun x k => act k x) n) ∈ MulAction.orbit H (dec n) := by
  induction w generalizing n with
  | nil => exact MulAction.mem_orbit_self _
  | cons k w ih =>
    simp only [List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at hw
    obtain ⟨g, hg⟩ := ih hw.2 (act k n)
    refine ⟨g * ⟨gens k, hgens k hw.1⟩, ?_⟩
    rw [List.foldl_cons, ← hg, hact k hw.1]
    exact mul_smul g (⟨gens k, hgens k hw.1⟩ : H) (dec n)

theorem cosetElt_walkEnc_mem_qmatClass
    (w : List ℕ) (hw : w.all (· < 24) = true) (n : ℕ) :
    cosetElt 1 (walkEnc w n) ∈ qmatClass (cosetElt 1 n) := by
  have h1 : ∀ k < 24, ConjAct.toConjAct (rhoGvis (conjQ (cosetPair 1) (gQ k))) ∈
      Subgroup.closure ((fun k => ConjAct.toConjAct (rhoGvis (conjQ (cosetPair 1) (gQ k)))) ''
        {k | k < 24}) :=
    fun k hk => Subgroup.subset_closure (Set.mem_image_of_mem _ hk)
  have h2 := foldl_mem_orbit (act := Native.CosetEnum.act (imgs 1)) (dec := cosetElt 1) h1
    (fun k hk a => cosetElt_act 1 hk a) w hw n
  rw [← orbit_closure_conjAct (cosetPair 1), walkEnc]
  exact h2

theorem cosetElt_mem_qmatClass_of_walk
    {t n : ℕ} (h : ∃ w : List ℕ, w.all (· < 24) = true ∧ walkEnc w (classEnc t) = n) :
    cosetElt 1 n ∈ qmatClass (classRep t) := by
  obtain ⟨w, hw, rfl⟩ := h
  exact cosetElt_walkEnc_mem_qmatClass w hw (classEnc t)

theorem coe_fusElt_conj (j : ℕ) (f : Gvis) :
    ((fusElt j * f * (fusElt j)⁻¹ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) =
      (fusGen j).toLin * (f : SpaceB ≃ₗ[ℚ] SpaceB) * (fusGen j).toLin⁻¹ := rfl

theorem fusElt_conj_classRep
    {j k t : ℕ} (hj : j < 11)
    (h : ∃ w : List ℕ, w.all (· < 24) = true ∧
      walkEnc w (classEnc t) = fusF (fusGen j) (fusShift j) (classEnc k)) :
    fusElt j * classRep k * (fusElt j)⁻¹ ∈ qmatClass (classRep t) := by
  have h1 := conj_cosetElt_one (fusGen j) (fusShift j) (fusGen_valid j hj) (fusGen_ne_tau j)
    (fusGens_comm j hj) (classEnc k)
  have h2 := cosetElt_mem_qmatClass_of_walk h
  have e : fusElt j * classRep k * (fusElt j)⁻¹ =
      cosetElt 1 (fusF (fusGen j) (fusShift j) (classEnc k)) := Subtype.ext h1
  rw [e]
  exact h2

theorem fusGens_fix_zero_four_check :
    ∀ j < 11,
      (∃ w : List ℕ, w.all (· < 24) = true ∧
        walkEnc w (classEnc 0) = fusF (fusGen j) (fusShift j) (classEnc 0)) ∧
      (∃ w : List ℕ, w.all (· < 24) = true ∧
        walkEnc w (classEnc 4) = fusF (fusGen j) (fusShift j) (classEnc 4)) :=
  Certificates.certificate6021.2.2.1

theorem fusGens_fix_zero_four
    (j : ℕ) (hj : j < 11) :
    fusElt j * classRep 0 * (fusElt j)⁻¹ ∈ qmatClass (classRep 0) ∧
      fusElt j * classRep 4 * (fusElt j)⁻¹ ∈ qmatClass (classRep 4) := by
  have h := fusGens_fix_zero_four_check j hj
  exact ⟨fusElt_conj_classRep hj h.1, fusElt_conj_classRep hj h.2⟩

theorem fusTargets_check :
    ∀ j < 11, ∀ k < 137, fusTarget j k < 137 ∧
      ∃ w : List ℕ, w.all (· < 24) = true ∧
        walkEnc w (classEnc (fusTarget j k)) = fusF (fusGen j) (fusShift j) (classEnc k) :=
  Certificates.certificate6021.2.2.2.1

theorem fusElt_conj_classRep_recorded
    (j k : ℕ) (hj : j < 11) (hk : k < 137) :
    fusTarget j k < 137 ∧
      fusElt j * classRep k * (fusElt j)⁻¹ ∈ qmatClass (classRep (fusTarget j k)) := by
  have h := fusTargets_check j hj k hk
  exact ⟨h.1, fusElt_conj_classRep hj h.2⟩

theorem fusTreeOK_eq : fusTreeOK = true :=
  Certificates.certificate6021.2.2.2.2.1

theorem exists_conj_of_mem_qmatClass {f x : Gvis} (hx : x ∈ qmatClass f) :
    ∃ u ∈ rhoQ.subgroupOf Gvis, u * x * u⁻¹ = f := by
  obtain ⟨u, hu, rfl⟩ := hx
  exact ⟨u, hu, by group⟩

theorem fusion_to_seventeen_aux :
    ∀ d k, k < 137 → (fusTree.getD k (0, 0, 0)).2.2 = d →
    k ≠ 0 → k ≠ 4 → ∃ g : Gvis, g * classRep k * g⁻¹ ∈ qmatClass (classRep 17) := by
  intro d
  induction d using Nat.strong_induction_on with
  | _ d ih =>
    intro k hk hd h0 h4
    by_cases h17 : k = 17
    · subst h17
      exact ⟨1, by simpa using mem_qmatClass_self (classRep 17)⟩
    · have hok := List.all_eq_true.1 fusTreeOK_eq k (List.mem_range.2 hk)
      simp only [Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne,
        ne_eq, h0, h4, h17, false_or, or_false] at hok
      obtain ⟨⟨⟨⟨⟨hj, ht⟩, ht0⟩, ht4⟩, hlt⟩, htgt⟩ := hok
      set e := fusTree.getD k (0, 0, 0) with he
      have hstep := (fusElt_conj_classRep_recorded e.1 k hj hk).2
      rw [htgt] at hstep
      obtain ⟨u, hu, hux⟩ := exists_conj_of_mem_qmatClass hstep
      obtain ⟨g', hg'⟩ := ih (fusTree.getD e.2.1 (0, 0, 0)).2.2 (hd ▸ hlt) e.2.1 ht rfl ht0 ht4
      refine ⟨g' * u * fusElt e.1, ?_⟩
      have : g' * u * fusElt e.1 * classRep k * (g' * u * fusElt e.1)⁻¹ =
          g' * classRep e.2.1 * g'⁻¹ := by
        have h2 : u * (fusElt e.1 * classRep k * (fusElt e.1)⁻¹) * u⁻¹ = classRep e.2.1 := hux
        calc g' * u * fusElt e.1 * classRep k * (g' * u * fusElt e.1)⁻¹ =
            g' * (u * (fusElt e.1 * classRep k * (fusElt e.1)⁻¹) * u⁻¹) * g'⁻¹ := by group
          _ = _ := by rw [h2]
      rw [this]
      exact hg'

theorem fusion_to_seventeen
    (k : ℕ) (hk : k < 137) (h0 : k ≠ 0) (h4 : k ≠ 4) :
    ∃ g : Gvis, g * classRep k * g⁻¹ ∈ qmatClass (classRep 17) :=
  fusion_to_seventeen_aux _ k hk rfl h0 h4

theorem classRep_zero :
    classRep 0 = cosetElt 1 0 := by
  rw [classRep, classEnc_zero]

theorem classRep_four :
    classRep 4 = cosetElt 1 63 := by
  rw [classRep, classEnc_four]

theorem qOfEnc_zero : qOfEnc 0 = 1 := pauliQ_false_zero

theorem qOfEnc_sixtythree : qOfEnc 63 = qP 0 63 0 :=
  qOfEnc_eq_qP (by norm_num) (by norm_num) (by norm_num) (by norm_num [pauliEnc])

theorem qOfEnc_196668 : qOfEnc 196668 = qP 0 60 48 :=
  qOfEnc_eq_qP (by norm_num) (by norm_num) (by norm_num) (by norm_num [pauliEnc])

theorem cosetElt_zero :
    ((cosetElt 1 0 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = cosetRep 1 := by
  rw [coe_cosetElt, qOfEnc_zero, rhoEquiv_one', mul_one]

theorem cosetElt_sixtythree :
    ((cosetElt 1 63 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) =
    rhoEquiv (qP 0 63 0) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [coe_cosetElt, qOfEnc_sixtythree]
  exact cosetRep_comm_rho 1 (false, 63, 0) Certificates.certificate6021.2.2.2.2.2.1

theorem cosetElt_196668 :
    ((cosetElt 1 196668 : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) =
    rhoEquiv (qP 0 60 48) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) := by
  rw [coe_cosetElt, qOfEnc_196668]
  exact cosetRep_comm_rho 1 (false, 60, 48) Certificates.certificate6021.2.2.2.2.2.2

theorem exists_conj_cosetElt_of_mem_cosetInv_one
    {f : Gvis} (hf : f ∈ cosetInv 1) :
    ∃ g : Gvis, ∃ n ∈ ({0, 63, 196668} : Finset ℕ), g * f * g⁻¹ = cosetElt 1 n := by
  obtain ⟨k, hk, hfk⟩ := mem_qmatClass_of_mem_cosetInv_one hf
  obtain ⟨u, hu, hux⟩ := exists_conj_of_mem_qmatClass hfk
  by_cases h0 : k = 0
  · subst h0
    exact ⟨u, 0, by simp, by rw [hux, classRep_zero]⟩
  by_cases h4 : k = 4
  · subst h4
    exact ⟨u, 63, by simp, by rw [hux, classRep_four]⟩
  obtain ⟨g', hg'⟩ := fusion_to_seventeen k hk h0 h4
  have h17 := qmatClass_eq_of_mem mem_qmatClass_seventeen
  rw [← h17] at hg'
  obtain ⟨u', hu', hu'x⟩ := exists_conj_of_mem_qmatClass hg'
  refine ⟨u' * g' * u, 196668, by simp, ?_⟩
  calc u' * g' * u * f * (u' * g' * u)⁻¹ = u' * (g' * (u * f * u⁻¹) * g'⁻¹) * u'⁻¹ := by group
    _ = cosetElt 1 196668 := by rw [hux, hu'x]

theorem visible_involution_coset_one_fusion :
    (∀ f ∈ cosetInv 1, ∃ g : Gvis,
      ((g * f * g⁻¹ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) = cosetRep 1 ∨
      ((g * f * g⁻¹ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) =
        rhoEquiv (qP 0 63 0) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB) ∨
      ((g * f * g⁻¹ : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) =
        rhoEquiv (qP 0 60 48) * (cosetRep 1 : SpaceB ≃ₗ[ℚ] SpaceB)) ∧
    (∀ j < 11, ∀ n : ℕ, (fusGen j).toLin * ((cosetElt 1 n : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB) *
        (fusGen j).toLin⁻¹ =
      ((cosetElt 1 (fusF (fusGen j) (fusShift j) n) : Gvis) : SpaceB ≃ₗ[ℚ] SpaceB)) ∧
    (∀ k < 137, k ≠ 0 → k ≠ 4 →
      ∃ g : Gvis, g * classRep k * g⁻¹ ∈ qmatClass (classRep 17)) ∧
    (∀ j < 11, fusElt j * classRep 0 * (fusElt j)⁻¹ ∈ qmatClass (classRep 0) ∧
      fusElt j * classRep 4 * (fusElt j)⁻¹ ∈ qmatClass (classRep 4)) ∧
    (∀ j < 11, ∀ k < 137, fusTarget j k < 137 ∧
      fusElt j * classRep k * (fusElt j)⁻¹ ∈ qmatClass (classRep (fusTarget j k))) := by
  refine ⟨?_, fun j hj n => conj_cosetElt_one (fusGen j) (fusShift j) (fusGen_valid j hj)
    (fusGen_ne_tau j) (fusGens_comm j hj) n, fusion_to_seventeen, fusGens_fix_zero_four,
    fun j hj k hk => fusElt_conj_classRep_recorded j k hj hk⟩
  intro f hf
  obtain ⟨g, n, hn, hgf⟩ := exists_conj_cosetElt_of_mem_cosetInv_one hf
  refine ⟨g, ?_⟩
  rw [hgf]
  simp only [Finset.mem_insert, Finset.mem_singleton] at hn
  rcases hn with rfl | rfl | rfl
  · exact Or.inl cosetElt_zero
  · exact Or.inr (Or.inl cosetElt_sixtythree)
  · exact Or.inr (Or.inr cosetElt_196668)

end CFSG.Monster.Existence.Census

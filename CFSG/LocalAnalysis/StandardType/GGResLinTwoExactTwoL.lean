module

public import CFSG.LocalAnalysis.StandardType.GGResLinTwoRank78K3
public import CFSG.LocalAnalysis.StandardType.GGResJOneReflCell
import CFSG.LocalAnalysis.StandardType.GGResFixedWeylCentralizer
import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeBLinearNs
import CFSG.LocalAnalysis.StandardType.GGNbrU63StepTwo
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoTableBReduce

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Open

theorem GGResHyp.false_of_oneRefl_of_card_gamma_sq
    (hLift : GGTBTorLiftRows) {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hJ : GGInnerDiagOn Bs J) {τ : MulAut ↥Bs}
    (hτ : GGIsReflection p τ) (hA : ggAutomizer J Bs = Subgroup.zpowers τ)
    (h2 : Nat.card (ggGamma J hH.Bs_le_normalizer_J).range = p ^ 2) : False := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hH.1.tableB_facts.2.1
  rcases (hJ.label GGResJOneReflLabel p).elim_or with hJ1 | hJ2
  ·
    obtain ⟨hJperf, lab, -, hraw⟩ := largeEvenMarking_and_labelAll_simple
      (S := fun lab => GGResJOneReflLabel p lab)
      (P' := fun R _ I _ => ∀ E : Subgroup (MulAut R), (E : Set (MulAut R)) ⊆ I →
        IsElemAbelian p E → Nat.card E = p ^ 2 → ∃ F : Subgroup R, IsPGroup p F ∧ ¬ IsCyclic F)
      (fun lab hlab hS => ggResJOneReflLabelInput_holds p hp2 lab hlab hS)
      (fun _ _ _ _ _ _ hP => hP.1) hJ1
    obtain ⟨R, _, I, F, -, -, θ, ⟨-, hBN, h3⟩, hP'⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨F', hF', hnc⟩ := hP' (ggBeta J θ hBN).range
      (by rintro _ ⟨b, rfl⟩; exact ggBeta_mem J θ hBN h3 b)
      (isElemAbelian_range_ggBeta θ hBs hBN) ((NbrU63.card_range_ggBeta_eq hJperf θ hBN).trans h2)
    obtain ⟨S, hSJ, hSp, hSnc⟩ := exists_noncyclic_of_noncyclic_quot
      (θ.toMonoidHom.comp (QuotientGroup.mk' _))
      (θ.surjective.comp (QuotientGroup.mk'_surjective _)) hF' hnc
    exact hSnc (hH.isCyclic_of_le_J_of_oneRefl hτ hA hSp hSJ)
  ·
    obtain ⟨hJperf, lab, -, hraw⟩ := largeEvenMarking_and_labelAll
      (S := fun lab => ¬ GGResJOneReflLabel p lab)
      (P' := fun R _ _ _ => ∃ r, 2 ≤ r ∧ GGTorusLift p r R)
      (fun lab hΛ h => by
        simp only [GGResJOneReflLabel, not_forall, not_le, exists_prop] at h
        obtain ⟨r, m, N, C, M, hrow, hr⟩ := h
        exact (hLift p lab r m N C M hp hp2 hΛ hrow).mono fun _ _ _ _ hT => ⟨r, hr, hT⟩)
      (fun _ _ _ _ _ _ hP => hP.1) hJ2
    obtain ⟨R, _, I, F, -, -, θ, -, r, hr, hT⟩ := largeEvenRawDatum_exists hraw
    obtain ⟨-, E, -, -, -, hE, hEcard, -⟩ := hT J (ggQuotHom θ) (ggQuotHom_surjective θ)
      (by rw [ker_ggQuotHom]) hJperf
    have hEJ : IsCyclic ↥(E.map J.subtype) :=
      hH.isCyclic_of_le_J_of_oneRefl hτ hA
        ((CFSG.Open.IsElemAbelian.isPGroup hE).map J.subtype) (Subgroup.map_subtype_le E)
    have hcyc : IsCyclic ↥E :=
      (MulEquiv.isCyclic (E.equivMapOfInjective J.subtype J.subtype_injective)).mpr hEJ
    obtain ⟨g, hg⟩ := isCyclic_iff_exists_orderOf_eq_natCard.1 hcyc
    have hgp : g ^ p = 1 := Subtype.ext (hE.2 g g.2)
    have hdvd : p ^ r ∣ p := hEcard ▸ hg ▸ orderOf_dvd_of_pow_eq_one hgp
    have hle : p ^ r ≤ p := Nat.le_of_dvd hp.pos hdvd
    have hsq : p * p ≤ p ^ r := by
      rw [← sq]
      exact Nat.pow_le_pow_right hp.pos hr
    nlinarith [hp.two_le]

theorem GGResHyp.false_of_exact2_L_linTwo
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (lab : LargeEvenLabel) (hlab : GGLinTwoLabel 3 lab)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny) : False := by
  classical
  have hpq : 3 ∣ 2 ^ 1 + 1 := by norm_num
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) := hH.2.2.1.1.le_normalizer
  have hL : GGInnerDiagOnLabel (fun p lab' => p = 3 ∧ lab' = lab) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab' h => ⟨rfl, h⟩) hmark
  have hlabAeq : lab = (⟨.A, lab.rank, 1⟩ : LargeEvenLabel) := by
    rcases lab with ⟨tag, r, n⟩
    rcases hlab with ⟨htag, -, hn, -⟩
    subst htag
    subst hn
    rfl
  have hmarkA : GGInnerDiagOnLabel
      (fun _ lab' => lab' = (⟨.A, lab.rank, 1⟩ : LargeEvenLabel)) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab' h => h.trans hlabAeq) hmark
  have hB : Bs = B := hH.bstar_eq_of_linMinus_side (Or.inl rfl) hpq hmarkA
  obtain ⟨s, T, hTA, hZinj, hEq, hcardE, hsd, hcardBs⟩ :=
    GGResHyp.linTwo_stable_torus hH lab hlab hN hL
  have hs3 : 3 ≤ s := by have := hlab.2.1; rw [hsd]; omega
  have hcardAL : Nat.card ↥(ggAutomizer L Bs) = 2 ^ s * s.factorial := by
    have h := GGResHyp.linTwo_rank_ge_five_automizerL_card hH lab hlab hlab.2.1 hN hL
    simpa [hsd] using h
  have hiOne : Bs ⊓ Subgroup.centralizer (J : Set G) = D :=
    hH.iOne_of_linMinus_side (Or.inl rfl) hpq hmarkA
  have hDcard : Nat.card ↥D = 3 ^ 2 := hH.1.2.2.1.2.2.1
  have hsmall : ¬ S2MathAs51642Interfaces.SmallDerived 3 lab := by
    simp [S2MathAs51642Interfaces.SmallDerived, hlab.1]
  have hgcd : ¬ 3 ∣ Nat.gcd (lab.rank + 1) (2 ^ lab.n - 1) := by
    rw [hlab.2.2.1]
    norm_num
  have hcenter : S2MathAs51642Interfaces.CenterPrimeTo 3 lab ∧ lab.tag = .A := by
    refine ⟨?_, hlab.1⟩
    simp only [S2MathAs51642Interfaces.CenterPrimeTo, hlab.1]
    exact ⟨hsmall, hgcd⟩
  have hLsel : GGInnerDiagOnLabel
      (fun p lab' => S2MathAs51642Interfaces.CenterPrimeTo p lab' ∧ lab'.tag = .A) 3 Bs L :=
    GGInnerDiagOnLabel.mono_label (fun lab' h => by
      rw [h.2]
      exact hcenter) hL
  have hJ : GGInnerDiagOn Bs J :=
    q1CenterPrimeLinear_holds G 3 B Bs x L D J hH.1 hLsel
  rcases hD with ⟨Λ, hΛF, hΛD, Sdel, Λa, hΛaF, hΛaD, ML, CL, MK, CK, Vd, hVd, hVdM,
    ιd, φd, hd, αd, hSdel, -, -, hML, hCL, -, -, -, hlind, hreflD, hpairD,
    -, -, ⟨fL, -⟩, -, hclosL, -, -, hclosJ⟩
  letI : Fintype Λ := hΛF
  letI : DecidableEq Λ := hΛD
  letI : AddCommGroup Vd := hVd
  letI : Module (ZMod 3) Vd := hVdM
  letI : Finite Vd := Finite.of_equiv (Additive ↥Bs) ιd.toEquiv
  have hWML : GGWeylTypeData (Fintype.card Λ) (2 ^ s * s.factorial)
      (Nat.card ↥(Subgroup.center ML.Group)) := by
    rw [← hcardAL, ← Nat.card_congr fL.toEquiv]
    exact ggWeylTypeData_of_isWeylMatrix hML
  have hcardΛ : Fintype.card Λ = s :=
    ggWeylTypeData_rank_eq hWML (Or.inr (Or.inl ⟨by omega, rfl, rfl⟩))
  rcases Nat.lt_or_ge s 4 with hs4 | hs4
  ·
    have hs : s = 3 := by omega
    subst hs
    have hcardC : Fintype.card {i : Λ // i ∉ Sdel} = 1 := by
      rw [Fintype.card_subtype_compl, Fintype.card_coe, hcardΛ, hSdel]
    obtain ⟨j0, hj0⟩ := Fintype.card_eq_one_iff.mp hcardC
    have hA : ggAutomizer J Bs = Subgroup.zpowers (φd (Sum.inl j0.1)) := by
      rw [hclosJ, Subgroup.zpowers_eq_closure]
      congr 1
      ext ψ
      simp only [Set.mem_range, Set.mem_singleton_iff]
      constructor
      · rintro ⟨j, rfl⟩
        rw [hj0 j]
      · rintro rfl
        exact ⟨j0, rfl⟩
    have hγ : Nat.card (ggGamma J hH.Bs_le_normalizer_J).range = 3 ^ 2 := by
      have hprod := NbrU63.card_range_ggGamma_mul_card_inf hH.Bs_le_normalizer_J
      rw [hiOne, hDcard, hcardBs, show (3 : ℕ) ^ (3 + 1) = 3 ^ 2 * 3 ^ 2 by norm_num] at hprod
      exact Nat.mul_right_cancel (by norm_num : 0 < 3 ^ 2) hprod
    exact hH.false_of_oneRefl_of_card_gamma_sq ggTBTorLiftRows_holds hJ (hreflD _) hA hγ
  ·
    have hS : LargeEvenSStar 3 B x L := hH.1.1.2.2.2.2.2.2.1
    have hcardB : Nat.card B = 3 ^ (s + 1) := by rw [← hB, hcardBs]
    have hm : LargeEvenTwoLocalRank 3 G = s + 1 := by
      apply Nat.pow_right_injective (by norm_num : 2 ≤ 3)
      exact hS.1.2.1.symm.trans hcardB
    have hm5 : 5 ≤ LargeEvenTwoLocalRank 3 G := by omega
    have hJlab : GGInnerDiagOnLabel (fun _ _ => True) 3 Bs J :=
      (GGInnerDiagOn.label (fun _ _ => True) 3 hJ).mono_label (fun _ _ => trivial)
    have hJL : J ≤ L := hH.1.2.2.1.2.2.2.2.2.1.1.trans inf_le_left
    have hfwd : ∀ b : ↥Bs, (∀ a ∈ ggAutomizer J Bs, a b = b) →
        (b : G) ∈ Subgroup.centralizer (J : Set G) := by
      rcases hH.fix_mem_centralizer_J_or_low_of_tcj
        (ggTBTorAll_of_remaining trivial) ggTBTorLiftRows_holds
        TCJ.ggTCJKnown_holds ggLabelRigidInput_holds hm5 hJlab with
        hfwd | ⟨hm5eq, hA5⟩ | ⟨hm6eq, hE6⟩
      · exact hfwd
      ·
        exfalso
        have hJ5 : GGInnerDiagOnLabel GGTwA5PlusThreeLabel 3 Bs J :=
          hA5.mono_label (fun _ h => h.2)
        exact not_twA5_le_linTwo_rank_seven_eight hJL hlab (by omega) hL hJ5
      ·
        exfalso
        have hJ6 : GGInnerDiagOnLabel GGTableBTwE6ThreeLabel 3 Bs J :=
          hE6.mono_label (fun _ h => h.2)
        obtain ⟨labJ, hΛJ, hhasJ, _, _, _, _, _, ⟨htJ, -, -⟩, -⟩ :=
          largeEvenMarking_exists_hasLabel hJ6
        obtain ⟨labL, hΛL, hhasL, _, _, _, _, _, ⟨-, hlabEq⟩, -⟩ :=
          largeEvenMarking_exists_hasLabel hL
        have htL : labL.tag = .A := by rw [hlabEq]; exact hlab.1
        have hnL : labL.n = 1 := by rw [hlabEq]; exact hlab.2.2.1
        have hrL : labL.rank ≤ 10 := by rw [hlabEq]; omega
        exact ggTwE6_false_of_le_linTwo hJL hΛL hhasL htL hnL hrL hΛJ hhasJ htJ
    have hfixJ : ∀ b : ↥Bs,
        (∀ φ ∈ ggAutomizer J Bs, φ b = b) ↔
          (b : G) ∈ Subgroup.centralizer (J : Set G) := by
      intro b
      constructor
      · exact hfwd b
      · intro hb
        apply ggAutomizer_apply_eq_of_le_centralizer (H := J) (x := b)
        intro j hj
        rw [Subgroup.mem_centralizer_singleton_iff]
        rw [Subgroup.mem_centralizer_iff] at hb
        exact hb j hj
    have hdet : (CL.det : ZMod 3) ≠ 0 := by
      intro hdet0
      have hsing : ggSingularWeylOrder 3 (Nat.card ↥(ggAutomizer L Bs)) :=
        ggSingularWeylOrder_of_type fL
          (ggRC_singular_typeA_or_E6 Nat.prime_three (by norm_num) hML hCL hdet0)
      rw [hcardAL] at hsing
      exact not_ggSingularWeylOrder_two_pow_mul_factorial (by omega) hsing
    have hres := ggResExact2_nonI1_L_of_det hH ιd hCL
      (fun i => φd (Sum.inl i)) (fun i => hd (Sum.inl i)) (fun i => αd (Sum.inl i))
      (fun i w => hlind (Sum.inl i) w) hpairD hclosL hSdel hclosJ hfixJ hdet
    have hlt := hres.2.2.2
    rw [hiOne] at hlt
    exact lt_irrefl _ hlt


theorem GGResHyp.false_of_exact2_L_linTwo_of_marking
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hM : GGInnerDiagOnLabel GGLinTwoLabel 3 Bs L)
    (hD : GGResLeviDatumExact2 3 Bs L J K ggSelAny ggTypAny) : False := by
  obtain ⟨hperf, lab, hlab, hraw⟩ := hM
  obtain ⟨R, _, I, F, -, -, θ, hS, -⟩ := largeEvenRawDatum_exists hraw
  exact hH.false_of_exact2_L_linTwo lab hS ⟨hperf, lab, hlab, largeEvenRawDatum_mono
    (fun _ _ _ _ ⟨hs, hna, θ', _, hP⟩ => ⟨hs, hna, θ', rfl, hP⟩) hraw⟩ hD

end CFSG.StandardType

end

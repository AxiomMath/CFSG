module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2CensusDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2OmegaSelect
import CFSG.LocalAnalysis.StandardType.GGNbrLangQ2SpBlock

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly
open CFSG.Open (StatedOmega StatedSL)
open CFSG.StandardType.ClassicalPosition CFSG.StandardType.ClassicalBlocks
open CFSG.LocalAnalysis.GLTheoremA (canonLabel)
open CFSG.LocalAnalysis.GLTheoremA.Y10F


private theorem q2cON_false_of_orthogonal_label_iso_A {d n : ℕ} (hd : 3 ≤ d) (hd4 : d ≠ 4)
    (lab : LargeEvenLabel)
    (hdisj : ((((lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) ∨
        (lab.tag = .A ∧ lab.rank = 1)) ∨
        (lab.tag = .A ∧ lab.rank = 3) ∨
        (lab.tag = .twA ∧ lab.rank = 3)))
    (hiso : GGLabelIso (⟨.A, d - 1, n⟩ : LargeEvenLabel) lab) : False := by
  obtain ⟨tag, rank, nn⟩ := lab
  have hcanon :=
    CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.canonLabel_eq_of_ggLabelIso hiso
  dsimp only [LargeEvenLabel.tag, LargeEvenLabel.rank] at hcanon hdisj
  rcases hdisj with hD | hAtail
  · rcases hD with ⟨hD, hr⟩ | ⟨hA1, hr⟩
    · rcases hD with hD | hD
      · change tag = .D at hD
        cases hD
        change 4 ≤ rank at hr
        have hr3 : rank ≠ 3 := by omega
        have htag := congrArg LargeEvenLabel.tag hcanon
        simpa [canonLabel, hr3] using htag
      · change tag = .twD at hD
        cases hD
        change 4 ≤ rank at hr
        have hr3 : rank ≠ 3 := by omega
        have hr2 : rank ≠ 2 := by omega
        have htag := congrArg LargeEvenLabel.tag hcanon
        simpa [canonLabel, hr3, hr2] using htag
    · change tag = .A at hA1
      cases hA1
      change rank = 1 at hr
      have hrank := congrArg LargeEvenLabel.rank hcanon
      simp [canonLabel] at hrank
      omega
  · rcases hAtail with ⟨hA3, hr⟩ | ⟨hAtwA3, hr⟩
    · change tag = .A at hA3
      cases hA3
      change rank = 3 at hr
      have hrank := congrArg LargeEvenLabel.rank hcanon
      simp [canonLabel] at hrank
      omega
    · change tag = .twA at hAtwA3
      cases hAtwA3
      have htag := congrArg LargeEvenLabel.tag hcanon
      simp [canonLabel] at htag

private theorem q2cON_ggHasLabel_linear_of_supplied
    {C K : Type} [Group C] [Field K] [Finite K] {d n : ℕ} (hd1 : 1 ≤ d)
    (hK : Nat.card K = 2 ^ n)
    (θ : C ⧸ Subgroup.center C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    GGHasLabel (⟨.A, d - 1, n⟩ : LargeEvenLabel) (C ⧸ Subgroup.center C) := by
  refine ⟨K, inferInstance, inferInstance, hK, ?_⟩
  have hd1' : d - 1 + 1 = d := Nat.sub_add_cancel hd1
  refine ⟨?_⟩
  rw [hd1']
  exact θ

private theorem q2cON_false_of_fixed_orthogonal_block_label
    {G ι F K : Type} [Group G] [Fintype ι] [DecidableEq ι] [Field F] [Finite F] [CharP F 2]
    [Field K] [Finite K]
    {Fε : Subgroup G} (Φ : QuadraticForm F (ι → F))
    (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (e : ↥Fε ≃* ↥(StatedOmega ⇑Φ)) {C : Subgroup G} (hC : CFSG.Assembly.IsComponentOf C Fε)
    {d m : ℕ} (hd : 3 ≤ d) (hd4 : d ≠ 4)
    (hK : Nat.card K = 2 ^ m)
    (hlam : LargeEvenInLambda2 (⟨.A, d - 1, m⟩ : LargeEvenLabel))
    (θ : ↥C ⧸ Subgroup.center ↥C ≃*
      LargeEvenProj (LargeEvenSLGroup (Fin d) K)) : False := by
  obtain ⟨lab, hlab, hdisj⟩ := exists_label_of_isComponentOf_iso_statedOmega Φ hΦ e hC
  have hlabData := CFSG.LocalAnalysis.GLTheoremA.Y10GInnLin.ggHasLabel_of_hasLabel hlab
  have hhasLab : GGHasLabel lab (↥C ⧸ Subgroup.center ↥C) := hlabData.2.2
  have hhasA : GGHasLabel (⟨.A, d - 1, m⟩ : LargeEvenLabel)
      (↥C ⧸ Subgroup.center ↥C) := q2cON_ggHasLabel_linear_of_supplied (by omega) hK θ
  have hiso : GGLabelIso (⟨.A, d - 1, m⟩ : LargeEvenLabel) lab :=
    ggLabelRigidInput_holds _ _ _ hlam hlabData.1 hhasA hhasLab
  exact q2cON_false_of_orthogonal_label_iso_A hd hd4 lab hdisj hiso

private theorem q2cON_no_dual_pair
    {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [Fintype F] [CharP F 2]
    (Φ : QuadraticForm F (ι → F)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hpF : p ∣ Nat.card F + 1)
    (b : GL ι F) (hb : b ∈ StatedOmega ⇑Φ) (hordb : orderOf b = p)
    {ε e e' : Matrix ι ι F}
    (hε : IsPrimAdjIdemIn (RingHom.id F) (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin F (Units.val '' ({b} : Set (GL ι F)))) ε)
    (he : IsPrimIdemIn (Algebra.adjoin F (Units.val '' ({b} : Set (GL ι F)))) e)
    (he' : IsPrimIdemIn (Algebra.adjoin F (Units.val '' ({b} : Set (GL ι F)))) e')
    (hne : e ≠ e') (hεe : ε = e + e') : False := by
  classical
  have hodd : Odd (orderOf b) := by
    rw [hordb]
    exact hp.odd_of_ne_two hp2
  have hx : CFSG.RankThree.PartOne.KCOrthogonal.OddOrderIsometry Φ p (ggJSo2_ML b) := by
    rw [← hordb]
    exact ggJSo2_oddOrderIsometry Φ hΦ b hb hodd
  have hxeq : (ggJSo2_ML b).toLinearMap = Matrix.toLin' (b : Matrix ι ι F) :=
    ggOmegaBlk_toLinEquiv_toLinearMap b
  have hsq : Squarefree (minpoly F (Matrix.toLin' (b : Matrix ι ι F))) := by
    rw [← hxeq]
    exact hx.squarefree_minpoly
  obtain ⟨a, ha, hae⟩ := ggOmegaBlk_prim_idem_eq_primaryProjection b hsq he
  obtain ⟨a', ha', ha'e⟩ := ggOmegaBlk_prim_idem_eq_primaryProjection b hsq he'
  have hax : a ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors
      (ggJSo2_ML b).toLinearMap := by
    rw [hxeq]
    exact ha
  have ha'x : a' ∈ CFSG.RankThree.PartOne.KCPrimary.primaryFactors
      (ggJSo2_ML b).toLinearMap := by
    rw [hxeq]
    exact ha'
  have haex : Matrix.toLinAlgEquiv' e =
      CFSG.RankThree.PartOne.KCPrimary.primaryProjection (ggJSo2_ML b).toLinearMap a := by
    rw [hxeq]
    exact hae
  have ha'ex : Matrix.toLinAlgEquiv' e' =
      CFSG.RankThree.PartOne.KCPrimary.primaryProjection (ggJSo2_ML b).toLinearMap a' := by
    rw [hxeq]
    exact ha'e
  have hrec := paired_prim_idem_primary_reciprocal Φ hΦ b hx hax ha'x haex ha'ex hεe hne
    hε he he'
  have hself :=
    CFSG.RankThree.PartOne.K159.reciprocalPolynomial_eq_of_dvd_card_add_one hx hpF hax
  exact hrec.2 hself.symm

theorem q2cON_unitary_block_false {m Q : ℕ} {E : Type} [Field E] [Finite E] [CharP E 2]
    (hE : Nat.card E = Q ^ 2) {G : Type} [Group G] {Fε : Subgroup G}
    (e : ↥Fε ≃* ↥(GUFull m Q E)) {C : Subgroup G}
    (hC : CFSG.Assembly.IsComponentOf C Fε) {d n : ℕ} (hd : 3 ≤ d) (hn : 2 ≤ n)
    {K : Type} [Field K] [Finite K] (hK : Nat.card K = 2 ^ n)
    (θ : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) : False := by
  haveI : CharP K 2 := charP_two_of_card hK
  exact l02qq2spb_unitary_excl hd hE hC e θ

theorem q2cON_nonsplit {ι F K : Type} [Fintype ι] [DecidableEq ι] [Field F] [Finite F]
    [CharP F 2] [Field K] [Finite K]
    (Φ : QuadraticForm F (ι → F)) (hΦ : (QuadraticMap.polarBilin Φ).Nondegenerate)
    (h8 : 8 ≤ Fintype.card ι) {p d m : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpF : p ∣ Nat.card F + 1) (hd : 3 ≤ d) (hpd : p ∣ d)
    (hm : 2 ≤ m) (hK : Nat.card K = 2 ^ m)
    (s : ↥(StatedOmega ⇑Φ)) (hs : orderOf s = p)
    (C : Subgroup ↥(StatedOmega ⇑Φ))
    (hC : CFSG.Assembly.IsComponentOf C (Subgroup.centralizer {s}))
    (θ : ↥C ⧸ Subgroup.center ↥C ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) K)) :
    False := by
  classical
  letI : Fintype F := Fintype.ofFinite F
  let b : GL ι F := s
  have hb : b ∈ StatedOmega ⇑Φ := s.2
  have hordb : orderOf b = p := by simpa [b] using hs
  have hodd : Odd (orderOf b) := by
    rw [hordb]
    exact hp.odd_of_ne_two hp2
  have hd4 : d ≠ 4 := by
    intro h4
    subst h4
    have hpd4 : p ∣ 2 ^ 2 := by simpa using hpd
    have hp_dvd_two : p ∣ 2 := hp.dvd_of_dvd_pow hpd4
    exact hp2 (Nat.le_antisymm (Nat.le_of_dvd (by norm_num) hp_dvd_two) hp.two_le)
  have hlam : LargeEvenInLambda2 (⟨.A, d - 1, m⟩ : LargeEvenLabel) := by
    simp only [LargeEvenInLambda2]
    exact ⟨by omega, by omega, fun _ => hm⟩
  obtain ⟨P, hPprim, -, -, hPcomm, hPsup, -⟩ :=
    centralizer_block_decomp_Omega Φ hΦ h8 b hb hodd
  have hcent : Subgroup.centralizer ({s} : Set ↥(StatedOmega ⇑Φ)) =
      (Subgroup.centralizer ({b} : Set (GL ι F))).comap (StatedOmega ⇑Φ).subtype := by
    ext g
    dsimp only [b]
    simp only [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff, Subgroup.coe_subtype,
      Subtype.ext_iff, Subgroup.coe_mul]
  have hCsup : CFSG.Assembly.IsComponentOf C (⨆ ε ∈ P,
      glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι F)) ε) := by
    rw [hcent, ← hPsup] at hC
    exact hC
  obtain ⟨ε, hεP, hCε⟩ :=
    exists_isComponentOf_block P
      (fun ε => glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι F)) ε)
      (fun i hi j hj hij x hx y hy => hPcomm i hi j hj hij x hx y hy) hCsup
  have hεprim : IsPrimAdjIdemIn (RingHom.id F)
      (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Φ))
      (Algebra.adjoin F (Units.val '' ({b} : Set (GL ι F)))) ε := hPprim ε hεP
  let G : Matrix ι ι F := LinearMap.toMatrix₂' F (QuadraticMap.polarBilin Φ)
  have hG : IsUnit G.det := CFSG.StandardType.TableC.polarGram_isUnit_det Φ hΦ
  have hGt : Matrix.transpose G = G := CFSG.StandardType.TableC.polarGram_transpose Φ
  have hS : ∀ s' ∈ ({b} : Set (GL ι F)), ∀ s'' ∈ ({b} : Set (GL ι F)), Commute s' s'' := by
    intro s' hs' s'' hs''
    rw [Set.mem_singleton_iff] at hs' hs''
    rw [hs', hs'']
  have hSU : ∀ s' ∈ ({b} : Set (GL ι F)),
      Matrix.transpose (s' : Matrix ι ι F) * G * (s' : Matrix ι ι F) = G := by
    intro s' hs'
    rw [Set.mem_singleton_iff] at hs'
    subst hs'
    have hg : ∀ v : ι → F, Φ (Matrix.mulVec (b : Matrix ι ι F) v) = Φ v :=
      fun v => CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.isometry_of_mem_statedOmega
        (f := ⇑Φ) hb v
    have h := CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.gram_invariant (Q := Φ) hg
    simpa [G, Matrix.map_id,
      CFSG.RankThree.GF2n.Smith81.Smith23E1.KFLin.polarGram_eq_toMatrix₂'] using h
  have hSUmap : ∀ s' ∈ ({b} : Set (GL ι F)),
      Matrix.transpose ((s' : Matrix ι ι F).map (RingHom.id F)) * G *
        (s' : Matrix ι ι F) = G := by
    intro s' hs'
    simpa using hSU s' hs'
  obtain ⟨e, he, heε, -⟩ :=
    CFSG.StandardType.ClassicalPosition.exists_isPrimIdemIn_of_isPrimAdjIdemIn (RingHom.id F)
      (fun _ => rfl) (G := G) hG (by simpa [Matrix.map_id] using hGt) hS hSUmap hεprim
  rcases CFSG.StandardType.TableC.isPrimIdemIn_cases hG hGt hS hSU hεprim he heε with
    heq | ⟨-, e', he', hne, hεe⟩
  · have heprim : IsPrimIdemIn (Algebra.adjoin F (Units.val '' ({b} : Set (GL ι F)))) ε :=
      heq ▸ he
    by_cases h1 : (b : Matrix ι ι F) * ε = ε
    · obtain ⟨ι₁, hFintype₁, hDecEq₁, Q₁, -, hform₁, hcases₁⟩ :=
        blockGroup_iso_Omega_one Φ hΦ h8 b hb hodd hεprim h1
      letI : Fintype ι₁ := hFintype₁
      letI : DecidableEq ι₁ := hDecEq₁
      obtain ⟨Φ₁, hQ₁, hΦ₁⟩ := hform₁
      rcases hcases₁ with ⟨⟨eF⟩, -⟩ | ⟨-, -, hsol, -⟩
      · let eF' : ↥(glBlockCentralizer (StatedOmega ⇑Φ).subtype ({b} : Set (GL ι F)) ε) ≃*
            ↥(StatedOmega ⇑Φ₁) := hQ₁.symm ▸ eF
        exact (q2cON_false_of_fixed_orthogonal_block_label (K := K) Φ₁ hΦ₁ eF' hCε hd hd4
          hK hlam θ).elim
      · exact (ResU3Three.not_isComponentOf_of_isSolvable hsol hCε).elim
    · obtain ⟨dblk, mult, E, hEfld, hEfin, hdblk, hEcard, -, -, ⟨eU⟩⟩ :=
        blockGroup_iso_Omega_unitary Φ hΦ h8 b hb hodd hεprim heprim h1
      letI : Field E := hEfld
      letI : Fintype E := hEfin
      obtain ⟨nF, -, hFcard⟩ := FiniteField.card F 2
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have hEtwo : Fintype.card E = 2 ^ ((nF : ℕ) * dblk * 2) := by
        rw [hEcard, hFcard, ← pow_mul, ← pow_mul]
        ring_nf
      have hcharE : CharP E 2 :=
        charP_of_card_eq_prime_pow (p := 2) (f := (nF : ℕ) * dblk * 2) hEtwo
      letI : CharP E 2 := hcharE
      have hEcard' : Nat.card E = (Fintype.card F ^ dblk) ^ 2 := by
        rw [Nat.card_eq_fintype_card]
        exact hEcard
      exact q2cON_unitary_block_false (m := mult) (Q := Fintype.card F ^ dblk) (E := E)
        hEcard' eU hCε hd hm hK θ
  · exact q2cON_no_dual_pair Φ hΦ hp hp2 hpF b hb hordb hεprim he he' hne hεe

end CFSG.StandardType

module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGAutomizerGammaCard
public import CFSG.LocalAnalysis.StandardType.GGStdPosC13Unitary
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUElt
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUModel
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryEndNodeInner
public import CFSG.LocalAnalysis.StandardType.GGTableBUnitaryTorus
public import CFSG.LocalAnalysis.StandardType.GGNbrInnerWeylUnitaryCover
public import CFSG.LocalAnalysis.StandardType.GGResE6DepRank
public import CFSG.LocalAnalysis.StandardType.GGResE6DepExceptional
public import CFSG.LocalAnalysis.StandardType.GGTDModelU
public import CFSG.LocalAnalysis.StandardType.GGTDLabels
public import CFSG.LocalAnalysis.StandardType.GGRCWeylCard
public import CFSG.LocalAnalysis.StandardType.GGTBTorRelA5Holds
public import CFSG.LocalAnalysis.StandardType.GGForkJrPumpLattice
public import CFSG.LocalAnalysis.StandardType.GGPZWeylB
public import CFSG.LocalAnalysis.StandardType.GGTBTorDatum

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem GGResHyp.relativeA5_card_automizer
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hMark : GGInnerDiagOnLabel (fun p lab => lab.rank = 5 ∧
      ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1))) p Bs X) :
    Nat.card ↥(ggAutomizer X Bs) = 48 := by
  have hp : p.Prime := Fact.out
  have hp2 : p ≠ 2 := hH.1.1.2.2.2.2.2.1.2.1
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R₀, _, I₀, F₀, _, _, θ₀, ⟨hrank, hrow⟩, _, _⟩ :=
    largeEvenRawDatum_exists hraw
  have hTorW := ggTBTorRelA5_holds p hp hp2 lab hΛ hrank hrow
  let Qmark : LargeEvenRawCont := fun R _ I F =>
    IsSimpleGroup R ∧ (∃ a b : R, a * b ≠ b * a) ∧
      ∃ θ : X ⧸ Subgroup.center X ≃* R,
        (lab.rank = 5 ∧ ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨
          (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1))) ∧
          Bs ≤ Subgroup.normalizer (X : Set G) ∧
          ∀ b ∈ Bs, ∃ φ ∈ I,
            LargeEvenInduces θ (fun l l' => (l' : G) = b⁻¹ * l * b) φ
  have hraw' : LargeEvenRawDatum lab Qmark := hraw
  obtain ⟨R, _, I, F, ⟨hs, hna, θ, hpred, hN, hInd⟩, hTorGen⟩ :=
    largeEvenRawDatum_exists (hTorW Qmark hraw')
  have hBs : IsElemAbelian p Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hInd (b := b) hb
  have h3 : p ^ 3 ≤ Nat.card ↥(ggGamma X hN).range :=
    hH.pow_three_le_card_range hX hN
  have hTB : GGTorusTBGroup p 3 R I X (ggQuotHom θ) (ggGamma X hN).range :=
    ggTorusTBGroup_of_marking hp hBs hSC hperf θ hN hBsI h3 h3
  have hTor : GGTorusTorData (ggTorMpm p lab) 3 (CartanMatrix.C 3)
      (CoxeterMatrix.B 3) X (ggGamma X hN).range :=
    hTorGen X (ggQuotHom θ) (ggGamma X hN).range hTB
  have hm : Odd (ggTorMpm p lab) := by
    unfold ggTorMpm
    split_ifs
    · exact ggHLT_odd_two_pow_sub_one hΛ.1
    · exact ggHLT_odd_two_pow_add_one hΛ.1
  have hpm : p ∣ ggTorMpm p lab := by
    unfold ggTorMpm
    split_ifs with hsub
    · exact hsub
    · rcases hrow with hrow | hrow
      · exact hrow.2
      · exact (hsub hrow.2).elim
  obtain ⟨φ, e, hφ, he⟩ := ggTBWeyl_of_torW hp2 hm hpm hBs hSC hN hTor
  rw [← Nat.card_congr e.toEquiv, ggCoxeterB_card 3 (by norm_num)]
  norm_num

theorem GGResHyp.not_relativeA5_of_card_automizer_E6
    {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp p B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun p lab => lab.rank = 5 ∧
      ((lab.tag = .A ∧ p ∣ 2 ^ lab.n + 1) ∨
        (lab.tag = .twA ∧ p ∣ 2 ^ lab.n - 1))) p Bs X) : False := by
  rw [hH.relativeA5_card_automizer hX hMark] at hcard
  norm_num at hcard

theorem GGResHyp.not_splitUnitaryCoprime_of_card_automizer_E6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧
      ¬ 3 ∣ lab.rank + 1) 3 Bs X) : False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, ⟨ht, hdiv, hcop⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  let d := lab.rank + 1
  have hd : 3 ≤ d := by
    simp only [LargeEvenInLambda2, ht] at hΛ
    dsimp [d]
    omega
  have hdq : (d, 2 ^ lab.n) ≠ (3, 2) := by
    rintro h
    have heq : d = 3 := (Prod.mk.inj h).1
    have h : 3 ∣ lab.rank + 1 := by change 3 ∣ d; rw [heq]
    exact hcop h
  let P : LargeEvenRawCont := fun R _ I _ =>
    GGTorusAutCardSC 3 R I (d - 1) d.factorial ∧ GGCenterPrime 3 R
  have hAll : LargeEvenLabelAll lab P := by
    intro Q hQ
    obtain ⟨t, l, f⟩ := lab
    dsimp only at ht hdiv hcop
    subst ht
    obtain ⟨E, _, _, hE, hQ⟩ := hQ
    have hcp := StdSubRestU.ggCenterPrime_unitary hE hΛ.1 hd hdq Nat.prime_three
      (by norm_num) hcop
    have hOrder := ggTorusAutCardSC_of_permEltSC Nat.prime_three (by norm_num) (by omega : 1 ≤ d)
      (TableBUE.center_proj_eq_bot hE hd hdq)
      (fun φ hφ hφ3 => InndiagSU.ggOutdiagPrime_unitary hE hΛ.1 hd hdq Nat.prime_three
        hdiv hcop φ hφ hφ3) hcp
      (UModel.ggTorusPermEltSC_unitary hE hΛ.1 (by omega) Nat.prime_three
        (by norm_num) hdiv hcop)
    exact ⟨E, inferInstance, inferInstance, hE, hQ, hOrder, hcp⟩
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, hind⟩, hOrder, hCp⟩ :=
    largeEvenRawDatum_exists (hAll _ hraw)
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  have h3 := hH.pow_three_le_card_range hX hN
  have hTB := ggTorusTBGroup_of_marking (r := 3) Nat.prime_three hBs hSC hperf θ hN hBsI h3 h3
  obtain ⟨hRank, hInnerOrder⟩ := hOrder X (ggQuotHom θ) (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hperf (ggGamma X hN).range hTB.2.2.2.1 hTB.2.2.2.2.1 h3
    hTB.2.2.2.2.2.2.2
  have hcp : ¬ 3 ∣ Nat.card (Subgroup.center X) :=
    hCp X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
  have hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 := by
    rw [inf_center_eq_bot_of_isElemAbelian_of_not_dvd Nat.prime_three hBs hcp, Subgroup.card_bot]
    norm_num
  have hdvd := card_ggAutomizer_dvd_gamma Nat.prime_three hBs hH.2.2.2.1 hN hZ
  have hActualOrder : Nat.card (ggAutomizer X Bs) = 51840 := hcard
  rw [hActualOrder, hInnerOrder] at hdvd
  have hz : ∃ z : G, z ∈ Bs ∧ z ≠ 1 ∧ z ∈ Subgroup.centralizer (X : Set G) := by
    rcases hX with hX | hX
    · rw [hX]
      exact ⟨x, hH.1.tableB_facts.2.2.1, hH.1.data_L.2.1, hH.1.data_L.1⟩
    · rw [hX]
      exact ⟨y, hH.1.2.1.1 hH.2.2.2.2.1.1.2.1, hH.data_K.2.1, hH.data_K.1⟩
  obtain ⟨z, hzBs, hz1, hzC⟩ := hz
  have hmul := card_range_ggGamma_mul_prime_le Nat.prime_three hBs hN hzBs hz1 hzC
  rw [hcardBs] at hmul
  have hupper : Nat.card (ggGamma X hN).range ≤ 3 ^ 5 := by norm_num at hmul ⊢; omega
  have hd6 : d ≤ 6 := by
    have hpow := hRank.trans hupper
    have hle := (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).mp hpow
    omega
  have hfac := Nat.factorial_le hd6
  have hlarge := Nat.le_of_dvd (Nat.factorial_pos d) hdvd
  norm_num at hfac
  omega

theorem GGResHyp.not_splitUnitaryDvd_of_card_automizer_E6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (h5 : ∀ (hN : Bs ≤ Subgroup.normalizer (X : Set G)),
      3 ^ 5 ≤ Nat.card ↥(ggGamma X hN).range)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel (fun _ lab => lab.tag = .twA ∧ 3 ∣ 2 ^ lab.n + 1 ∧
      3 ∣ lab.rank + 1 ∧ 5 ≤ lab.rank ∧ ¬ (lab.rank = 5 ∧ lab.n = 1)) 3 Bs X) : False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, ⟨ht, hdiv, hdvd, hrank, hex⟩, -, -⟩ :=
    largeEvenRawDatum_exists hraw
  let d := lab.rank + 1
  have hd : 6 ≤ d := by dsimp [d]; omega
  have hdn : (d, lab.n) ≠ (6, 1) := by
    intro h
    exact hex ⟨by have := (Prod.mk.inj h).1; dsimp [d] at this; omega, (Prod.mk.inj h).2⟩
  have hAll : LargeEvenLabelAll lab (fun R _ I _ =>
      GGTorusLift 3 (ggUnitaryTorusRank 3 d) R ∧
      (∀ (L' : Type) [Group L'] [Finite L'] (ψ : L' →* R), Function.Surjective ψ →
        ψ.ker ≤ Subgroup.center L' → commutator L' = ⊤ →
        ∀ A : Subgroup (MulAut L'), IsElemAbelian 3 A →
          (∀ a ∈ A, ∃ φ ∈ I, ∀ l, φ (ψ l) = ψ (a l)) →
          3 ^ (d / 3 + 2) ≤ Nat.card A → GGTorusSelfCent 3 A →
          GGTorusTorData (2 ^ lab.n + 1) lab.rank (CartanMatrix.A lab.rank)
            (CoxeterMatrix.A lab.rank) L' A)) := by
    intro Q hQ
    obtain ⟨t, l, f⟩ := lab
    dsimp only at ht hdiv hdvd hrank hex
    subst ht
    obtain ⟨E, _, _, hE, hQ⟩ := hQ
    have hLift := ggTorusLift_unitary (n := f) (d := l + 1) hE hΛ.1 (by omega) (by
      rintro h; have := (Prod.mk.inj h).1; omega) Nat.prime_three hdiv
    refine ⟨E, inferInstance, inferInstance, hE, hQ, hLift, ?_⟩
    intro L' _ _ ψ hψ hker hperf A hA hAI hcard hsc
    obtain ⟨φ, hφs, hφker, hdiag⟩ := LineU.exists_diagModel hE hΛ.1 (by omega)
      Nat.prime_three hdiv hdvd (LineU.unitaryCoverAt hE (by omega) hdn) hψ hker hperf hA hAI hcard
    exact ggTorusTorData_of_model_U hE Nat.prime_three (by norm_num) hdiv
      (by omega : 3 ≤ l) (show UnitTB.Model φ from ⟨TableBU.unitaryFieldData_of_card hE hΛ.1,
        hφs, hφker⟩) hA hsc hdiag
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, hind⟩, hLift, hTor⟩ :=
    largeEvenRawDatum_exists (hAll _ hraw)
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  have h6 : d ≤ 8 := by
    by_contra h
    have h9 : 9 ≤ d := by omega
    have hU : 6 ≤ ggUnitaryTorusRank 3 d := by
      have h3d : 3 ∣ d := hdvd
      simp only [ggUnitaryTorusRank, if_pos h3d]
      omega
    exact GGResHyp.not_torusLift_six_of_card_bstar hH hX hperf θ hN hcardBs
      (ggTorusLift_mono Nat.prime_three hLift hU)
  have hd6 : d = 6 := by
    have h3d : 3 ∣ d := hdvd
    omega
  have h5' := h5 hN
  have hCard : 3 ^ (d / 3 + 2) ≤ Nat.card (ggGamma X hN).range := by
    rw [hd6]
    norm_num
    norm_num at h5'
    omega
  have h3 := hH.pow_three_le_card_range hX hN
  have hTB := ggTorusTBGroup_of_marking (r := 3) Nat.prime_three hBs hSC hperf θ hN hBsI h3 h3
  have hT := hTor X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
    (ggGamma X hN).range hTB.2.2.2.1 hTB.2.2.2.2.1 hCard hTB.2.2.2.2.2.2.2
  have hom : Odd (2 ^ lab.n + 1) := by
    have hf := hΛ.1
    obtain ⟨f, hf'⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : lab.n ≠ 0)
    rw [hf', pow_succ]
    exact ⟨2 ^ f, by omega⟩
  obtain ⟨φ, e, _, _⟩ := ggTBWeyl_of_torW (by norm_num : (3 : ℕ) ≠ 2) hom hdiv hBs hSC hN hT
  have horder : Nat.card (ggAutomizer X Bs) = 51840 := hcard
  have he : Nat.card (ggAutomizer X Bs) = d.factorial := by
    rw [← Nat.card_congr e.toEquiv, l05nK3a_card_coxeterA]
  rw [hd6] at he
  norm_num at he
  omega

end CFSG.StandardType

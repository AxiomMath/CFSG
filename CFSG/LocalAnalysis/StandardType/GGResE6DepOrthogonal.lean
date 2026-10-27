module

public import CFSG.LocalAnalysis.StandardType.GGResE6DepLabels
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.StandardType.GGSignedPermCount

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem seven_le_card_of_signed_automizer {L' : Type} [Group L'] {A : Subgroup (MulAut L')}
    {k : ℕ} (Θ : (Fin k → Multiplicative (ZMod 3)) ≃* ↥A)
    (hsp : ∀ (n : L') (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))),
      SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut A hn)))
    (hcard : 51840 ∣ Nat.card (ggAutomizer (MulAut.conj : L' →* MulAut L').range A)) :
    3 ^ 7 ≤ Nat.card A := by
  have hdvd := hcard.trans
    (SignedPermCount.card_dvd_signed_of_normalizer_model Nat.prime_three (by norm_num) Θ hsp)
  have hk7 : 7 ≤ k := by
    by_contra h
    have hk6 : k ≤ 6 := by omega
    have hle : 2 ^ k * k.factorial ≤ 2 ^ 6 * (6 : ℕ).factorial :=
      Nat.mul_le_mul (Nat.pow_le_pow_right (by norm_num) hk6) (Nat.factorial_le hk6)
    have hgt := Nat.le_of_dvd (by positivity : 0 < 2 ^ k * k.factorial) hdvd
    norm_num at hle
    omega
  have hcardA : Nat.card A = 3 ^ k := by
    rw [← Nat.card_congr Θ.toEquiv, Nat.card_fun, Nat.card_fin,
      Nat.card_congr Multiplicative.toAdd, Nat.card_zmod]
  rw [hcardA]
  exact Nat.pow_le_pow_right (by norm_num) hk7

theorem GGResHyp.not_signed_model_of_card_automizer_E6_upto_seven
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hN : Bs ≤ Subgroup.normalizer (X : Set G))
    (hcp : ¬ 3 ∣ Nat.card (Subgroup.center X))
    (hcardBs : Nat.card Bs ≤ 3 ^ 7)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840) :
    ¬ ∃ (k : ℕ) (Θ : (Fin k → Multiplicative (ZMod 3)) ≃* ↥(ggGamma X hN).range),
      ∀ (n : X) (hn : MulAut.conj n ∈
          Subgroup.normalizer ((ggGamma X hN).range : Set (MulAut X))),
        SpCoord.IsSignedPerm ⇑((MulAut.congr Θ).symm (ggConjAut (ggGamma X hN).range hn)) := by
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hZ : Nat.card ↥(Bs ⊓ X ⊓ Subgroup.centralizer (X : Set G)) ≤ 3 := by
    rw [inf_center_eq_bot_of_isElemAbelian_of_not_dvd Nat.prime_three hBs hcp, Subgroup.card_bot]
    norm_num
  have hdvd := card_ggAutomizer_dvd_gamma Nat.prime_three hBs hH.2.2.2.1 hN hZ
  have horder : Nat.card (ggAutomizer X Bs) = 51840 := hcard
  rw [horder] at hdvd
  rintro ⟨k, Θ, hsp⟩
  have h7 := seven_le_card_of_signed_automizer Θ hsp hdvd
  have hz : ∃ z : G, z ∈ Bs ∧ z ≠ 1 ∧ z ∈ Subgroup.centralizer (X : Set G) := by
    rcases hX with hX | hX
    · rw [hX]
      exact ⟨x, hH.1.tableB_facts.2.2.1, hH.1.data_L.2.1, hH.1.data_L.1⟩
    · rw [hX]
      exact ⟨y, hH.1.2.1.1 hH.2.2.2.2.1.1.2.1, hH.data_K.2.1, hH.data_K.1⟩
  obtain ⟨z, hzBs, hz1, hzC⟩ := hz
  have hmul := card_range_ggGamma_mul_prime_le Nat.prime_three hBs hN hzBs hz1 hzC
  norm_num at hmul h7 hcardBs
  omega

theorem GGResHyp.not_orthogonal_of_card_automizer_E6_upto_seven
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs ≤ 3 ^ 7)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) 3 Bs X) :
    False := by
  obtain ⟨hperf, lab, hΛ, hraw⟩ := hMark
  obtain ⟨R, _, I, F, -, -, θ, ⟨htag, hrank⟩, -, -⟩ := largeEvenRawDatum_exists hraw
  let P : LargeEvenRawCont := fun R _ I _ =>
    Subgroup.center R = ⊥ ∧ GGCenterPrime 3 R ∧
      (I ⊆ Set.range (MulAut.conj : R →* MulAut R)) ∧
      GGTorusEvenSignedPermEltSC 3 R (fun _ => True)
  have hModels : LargeEvenLabelAll lab P := by
    intro Q hQ
    obtain ⟨t, l, f⟩ := lab
    have hf : 1 ≤ f := hΛ.1
    dsimp only at htag hrank
    rcases htag with ht | ht
    · subst ht
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      rw [if_neg (by omega : l ≠ 3)] at hQ ⊢
      obtain ⟨E, _, _, hE, hQ⟩ := hQ
      have : CharP E 2 := charP_two_of_card hE
      obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := E) Nat.prime_three
        (by norm_num) (by omega : 3 ≤ l)
      have hT : GGTorusEvenSignedPermEltSC 3 (OrthRest.RPlus E l) fun _ => True := by
        rcases three_dvd_two_pow_pred_or_succ f with h | h
        · exact (ggOrthEvenTorusInput_holds.1 E l 3 hrank Nat.prime_three
            (Or.inl (by rw [hE]; exact h))).mono (fun _ _ => trivial)
        · by_cases hev : Even l
          · exact (ggOrthEvenTorusInput_holds.1 E l 3 hrank Nat.prime_three
              (Or.inr ⟨hev, by rw [hE]; exact h⟩)).mono (fun _ _ => trivial)
          · have hlo : Odd l := Nat.not_even_iff_odd.mp hev
            have h5 : 5 ≤ l := by obtain ⟨j, hj⟩ := hlo; omega
            exact ggTorusEvenSignedPermEltSC_of_signedEltSC
              (ggOrthSignedTorusInput_holds.1 E l 3 h5 hlo Nat.prime_three
                (by rw [hE]; exact h))
      exact ⟨E, inferInstance, inferInstance, hE, hQ, hZ, hcp,
        (fun _ h => h), hT⟩
    · subst ht
      dsimp only [LargeEvenRawDatum] at hQ ⊢
      rw [if_neg (by omega : l ≠ 2), if_neg (by omega : l ≠ 3)] at hQ ⊢
      obtain ⟨E, _, _, hE, b, c, hbc, hQ⟩ := hQ
      have : CharP E 2 := charP_two_of_card hE
      obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := E) Nat.prime_three
        (by norm_num) (by omega : 3 ≤ l - 1) hbc
      have hT : GGTorusEvenSignedPermEltSC 3 (OrthRest.RMinus E (l - 1) b c) fun _ => True := by
        rcases three_dvd_two_pow_pred_or_succ f with h | h
        · exact ggTorusEvenSignedPermEltSC_of_signedEltSC
            (ggOrthSignedTorusInput_holds.2 E (l - 1) 3 b c (by omega) hbc Nat.prime_three
              (Or.inl (by rw [hE]; exact h)))
        · by_cases hev : Even (l - 1)
          · have hm4 : 4 ≤ l - 1 := by obtain ⟨j, hj⟩ := hev; omega
            exact (ggOrthEvenTorusInput_holds.2 E (l - 1) 3 b c hm4 hev hbc Nat.prime_three
              (by rw [hE]; exact h)).mono (fun _ _ => trivial)
          · exact ggTorusEvenSignedPermEltSC_of_signedEltSC
              (ggOrthSignedTorusInput_holds.2 E (l - 1) 3 b c (by omega) hbc Nat.prime_three
                (Or.inr ⟨Nat.not_even_iff_odd.mp hev, by rw [hE]; exact h⟩))
      exact ⟨E, inferInstance, inferInstance, hE, b, c, hbc, hQ, hZ, hcp,
        (fun _ h => h), hT⟩
  obtain ⟨R, _, I, F, ⟨-, -, θ, -, hN, hind⟩, hZ, hcp, hI, hT⟩ :=
    largeEvenRawDatum_exists (hModels _ hraw)
  have hBs : IsElemAbelian 3 Bs := hH.1.2.1.2.1
  have hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs :=
    hH.1.2.1.2.2.2
  have hBsI : ∀ (b : G) (hb : b ∈ Bs), ggLAut X θ ⟨b, hN hb⟩ ∈ I :=
    fun b hb => ggLAut_mem_of_induces X θ hN hind hb
  have h3 := hH.pow_three_le_card_range hX hN
  have hTB := ggTorusTBGroup_of_marking (r := 3) Nat.prime_three hBs hSC hperf θ hN hBsI h3 h3
  have hCenter : ¬ 3 ∣ Nat.card (Subgroup.center X) :=
    hcp X (ggQuotHom θ) (ggQuotHom_surjective θ) (by rw [ker_ggQuotHom]) hperf
  obtain ⟨k, Θ, -, -, -, -, -, -, hsp⟩ := OrthExcEven.exists_evenSignedPermModelSC
    Nat.prime_three (by norm_num) hI hZ hcp hT (ggQuotHom_surjective θ)
    (by rw [ker_ggQuotHom]) hperf hTB.2.2.2.1 hTB.2.2.2.2.1 h3 hTB.2.2.2.2.2.2.2
  exact GGResHyp.not_signed_model_of_card_automizer_E6_upto_seven hH hX hN hCenter hcardBs hcard
    ⟨k, Θ, hsp⟩

theorem GGResHyp.not_orthogonal_of_card_automizer_E6
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K X : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K) (hX : X = L ∨ X = K)
    (hcardBs : Nat.card Bs = 3 ^ 6)
    (hcard : Nat.card ↥(ggAutomizer X Bs) = 51840)
    (hMark : GGInnerDiagOnLabel
      (fun _ lab => (lab.tag = .D ∨ lab.tag = .twD) ∧ 4 ≤ lab.rank) 3 Bs X) :
    False := by
  exact GGResHyp.not_orthogonal_of_card_automizer_E6_upto_seven
    hH hX (by rw [hcardBs]; norm_num) hcard hMark

end CFSG.StandardType

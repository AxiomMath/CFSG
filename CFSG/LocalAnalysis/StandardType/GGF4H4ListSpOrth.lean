module

public import CFSG.LocalAnalysis.StandardType.GGF4H4ListSpCore
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEven
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusCore
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorusForms
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExc
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthExcEvenLabels
import CFSG.LocalAnalysis.StandardType.GGCorFourTwoOrthNsLabels
import CFSG.LocalAnalysis.StandardType.GGSignedPermCount
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUSigned

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly SpCoord Multiplicative Module
open CFSG.RankThree.Classical2 (orthDerived)

namespace F4H4Sp

theorem finrank_le_of_selfCent {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpq : p ∣ Nat.card K - 1 ∨ p ∣ Nat.card K + 1) {Q : QuadraticForm K V}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ v ∈ T, Q v = 0)
    {R : Type} [Group R] (e : R ≃* ↥(orthDerived Q)) {E : Subgroup R} (hE : IsElemAbelian p E)
    (hsc : ∀ g : R, (∀ x ∈ E, g * x = x * g) → g ^ p = 1 → g ∈ E) (hne : ∃ x ∈ E, x ≠ 1)
    {r : ℕ} (hr : Nat.card E = p ^ r) : finrank K V ≤ 2 * r + 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  set E' : Subgroup ↥(orthDerived Q) := E.map e.toMonoidHom with hE'
  set A : Subgroup (V ≃ₗ[K] V) := E'.map (orthDerived Q).subtype with hA
  have hcardA : Nat.card A = Nat.card E := by
    rw [hA, Subgroup.card_map_of_injective (Subgroup.subtype_injective _), hE',
      Subgroup.card_map_of_injective e.injective]
  have hAΩ : A ≤ orthDerived Q := by
    rintro _ ⟨x, -, rfl⟩
    exact x.2
  have hApow : ∀ a ∈ A, a ^ p = 1 := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩
    rw [← map_pow, ← map_pow, hE.2 y hy, map_one, map_one]
  have hAcomm : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a := by
    rintro _ ⟨_, ⟨y, hy, rfl⟩, rfl⟩ _ ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, TableB.IsElemAbelian.comm hE hy hz]
  have hmax : ∀ g ∈ orthDerived Q, g ^ p = 1 → (∀ c ∈ A, g * c = c * g) → g ∈ A := by
    intro g hg hgp hgc
    have hg' : e.symm ⟨g, hg⟩ ∈ E := by
      refine hsc _ (fun x hx => e.injective ?_) ?_
      · rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
        exact Subtype.ext (hgc _ ⟨e x, ⟨x, hx, rfl⟩, rfl⟩)
      · have h1 : (⟨g, hg⟩ : ↥(orthDerived Q)) ^ p = 1 :=
          Subtype.ext (by rw [Subgroup.coe_pow]; exact hgp)
        rw [← map_pow, h1, map_one]
    exact ⟨⟨g, hg⟩, ⟨e.symm ⟨g, hg⟩, hg', by simp⟩, rfl⟩
  have hneA : ∃ b ∈ A, b ≠ 1 := by
    obtain ⟨x, hx, hx1⟩ := hne
    refine ⟨((e x : ↥(orthDerived Q)) : V ≃ₗ[K] V), ⟨e x, ⟨x, hx, rfl⟩, rfl⟩, fun h => hx1 ?_⟩
    have h2 : e x = 1 := Subtype.ext h
    rw [← map_one e] at h2
    exact e.injective h2
  obtain ⟨r', τ, F, -, -, hdimV, -, -⟩ :=
    OrthTorus.exists_torus_frame hp2 hpq hQ hT hAΩ hApow hAcomm hmax hneA
  have hcardF : Nat.card A = p ^ r' := by
    rw [← F.range, ← Nat.card_congr (MonoidHom.ofInjective F.inj).toEquiv]
    show Nat.card (Fin r' → ZMod p) = p ^ r'
    rw [Nat.card_fun, Nat.card_fin, Nat.card_zmod]
  have hrr : r' = r := Nat.pow_right_injective hp.two_le (show p ^ r' = p ^ r by
    rw [← hcardF, hcardA, hr])
  omega

section Models


theorem largeEvenLabelAll_orthEven {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : LargeEvenLieTag}
    {l n : ℕ}
    (h : (t = .D ∧ 4 ≤ l ∧ (p ∣ 2 ^ n - 1 ∨ (Even l ∧ p ∣ 2 ^ n + 1))) ∨
      (t = .twD ∧ 5 ≤ l ∧ Even (l - 1) ∧ p ∣ 2 ^ n + 1)) :
    LargeEvenLabelAll ⟨t, l, n⟩ fun R _ I _ => I ⊆ Set.range (MulAut.conj : R →* MulAut R) ∧
      Subgroup.center R = ⊥ ∧ GGCenterPrime p R ∧
      GGTorusEvenSignedPermEltSC p R fun k => k = l := by
  intro Q hQ
  rcases h with ⟨rfl, hl, hpq⟩ | ⟨rfl, hl, hev, hpq⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [show l ≠ 3 by omega, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, hq⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
    have hpK : p ∣ Nat.card K - 1 ∨ (Even l ∧ p ∣ Nat.card K + 1) := by rw [hK]; exact hpq
    exact ⟨K, inferInstance, inferInstance, hK, hq, fun _ h => h, hZ, hcp,
      ggOrthEvenTorusInput_holds.1 K l p hl hp hpK⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [show l ≠ 2 by omega, show l ≠ 3 by omega, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, b, c, hbc, hq⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 (by omega : 3 ≤ l - 1) hbc
    have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
    have hT := ggOrthEvenTorusInput_holds.2 K (l - 1) p b c (by omega) hev hbc hp hpK
    rw [Nat.sub_add_cancel (by omega : 1 ≤ l)] at hT
    exact ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hq, fun _ h => h, hZ, hcp, hT⟩

theorem largeEvenLabelAll_orthSigned {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {t : LargeEvenLieTag}
    {l n : ℕ}
    (h : (t = .D ∧ 5 ≤ l ∧ Odd l ∧ p ∣ 2 ^ n + 1) ∨
      (t = .twD ∧ 4 ≤ l ∧ (p ∣ 2 ^ n - 1 ∨ (Odd (l - 1) ∧ p ∣ 2 ^ n + 1)))) :
    LargeEvenLabelAll ⟨t, l, n⟩ fun R _ I _ => I ⊆ Set.range (MulAut.conj : R →* MulAut R) ∧
      Subgroup.center R = ⊥ ∧ GGCenterPrime p R ∧ GGTorusSignedEltSC p R ∧
      ∀ E : Subgroup R, IsElemAbelian p E →
        (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → (∃ x ∈ E, x ≠ 1) →
          ∀ r : ℕ, Nat.card E = p ^ r → l ≤ r + 1 := by
  intro Q hQ
  rcases h with ⟨rfl, hl, hodd, hpq⟩ | ⟨rfl, hl, hpq⟩
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [show l ≠ 3 by omega, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, hq⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    obtain ⟨hZ, hcp⟩ := OrthNs.center_data_omegaPlus (K := K) hp hp2 (by omega : 3 ≤ l)
    have hpK : p ∣ Nat.card K + 1 := by rw [hK]; exact hpq
    refine ⟨K, inferInstance, inferInstance, hK, hq, fun _ h => h, hZ, hcp,
      ggOrthSignedTorusInput_holds.1 K l p hl hodd hp hpK, ?_⟩
    intro E hE hsc hne r hr
    obtain ⟨m, rfl⟩ : ∃ m, l = m + 1 := ⟨l - 1, by omega⟩
    have hdim : finrank K (Fin (m + 1) ⊕ Fin (m + 1) → K) = 2 * (m + 1) := by
      rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_fin]
      ring
    have := finrank_le_of_selfCent hp hp2 (Or.inr hpK) (TableBOrth.nondegenerate_qPlusForm _)
      (OrthTorus.exists_totallySingular_qPlusForm (by omega)) (OrthTorus.rPlusEquiv K (by omega))
      hE hsc hne hr
    omega
  · dsimp only [LargeEvenRawDatum] at hQ ⊢
    simp only [show l ≠ 2 by omega, show l ≠ 3 by omega, ↓reduceIte] at hQ ⊢
    obtain ⟨K, _, _, hK, b, c, hbc, hq⟩ := hQ
    have : CharP K 2 := charP_two_of_card hK
    obtain ⟨hZ, hcp⟩ := OrthExc.center_data_omegaMinus (K := K) hp hp2 (by omega : 3 ≤ l - 1) hbc
    have hpK : p ∣ Nat.card K - 1 ∨ (Odd (l - 1) ∧ p ∣ Nat.card K + 1) := by rw [hK]; exact hpq
    refine ⟨K, inferInstance, inferInstance, hK, b, c, hbc, hq, fun _ h => h, hZ, hcp,
      ggOrthSignedTorusInput_holds.2 K (l - 1) p b c (by omega) hbc hp hpK, ?_⟩
    intro E hE hsc hne r hr
    have hdim : finrank K (LargeEvenMinusIdx (l - 1) → K) = 2 * (l - 1 + 1) := by
      rw [Module.finrank_fintype_fun_eq_card]
      simp only [LargeEvenMinusIdx, Fintype.card_sum, Fintype.card_fin]
      omega
    have := finrank_le_of_selfCent hp hp2 (hpK.imp id fun h => h.2)
      (TableBOrth.nondegenerate_qMinusForm (l - 1) hbc)
      ((OrthTorus.charSum_qMinusForm (l - 1) hbc).2 (by omega)) (OrthTorus.rMinusEquiv K (l - 1) b c)
      hE hsc hne hr
    omega

end Models

section Nbr


variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
  {ks : Finset (Subgroup G)}

theorem false_of_orthEven_at_nbr (hres : GGF4SmallRes p B Bs x L D J ks)
    (hB : ∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) {K : Subgroup G}
    (hK : K ∈ ks) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (K ⧸ Subgroup.center K)) {l : ℕ} (hl : 4 ≤ l)
    (hP : LargeEvenLabelAll lab fun R _ I _ => I ⊆ Set.range (MulAut.conj : R →* MulAut R) ∧
      Subgroup.center R = ⊥ ∧ GGCenterPrime p R ∧
      GGTorusEvenSignedPermEltSC p R fun k => k = l) : False := by
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨R, _, I, F, θ, hN, ⟨hI, hZ, hcp, hT⟩, hTB, -, -, hW48⟩ :=
    exists_model_at_nbr hres hB hK hΛ hlab hP fun _ _ _ _ h => h.2.2.1
  obtain ⟨hψ, hker, hperf, hA, hAI, -, h3, hsc⟩ := hTB
  obtain ⟨k, Θ, -, hkl, hW, hd, hPm, -, hNs⟩ :=
    OrthExcEven.exists_evenSignedPermModelSC hp hp2 hI hZ hcp hT hψ hker hperf hA hAI h3 hsc
  have hb := SignedPermCount.card_inner_even_signed_bounds hp2 Θ hd hPm hNs
  rw [hW48 hW] at hb
  exact not_two_pow_pred_mul_factorial_dvd (l := k) (by omega) hb.1

theorem rank_le_four_of_orthSigned_at_nbr (hres : GGF4SmallRes p B Bs x L D J ks)
    (hB : ∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) {K : Subgroup G}
    (hK : K ∈ ks) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (hlab : GGHasLabel lab (K ⧸ Subgroup.center K)) {l : ℕ}
    (hP : LargeEvenLabelAll lab fun R _ I _ => I ⊆ Set.range (MulAut.conj : R →* MulAut R) ∧
      Subgroup.center R = ⊥ ∧ GGCenterPrime p R ∧ GGTorusSignedEltSC p R ∧
      ∀ E : Subgroup R, IsElemAbelian p E →
        (∀ g : R, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) → (∃ x ∈ E, x ≠ 1) →
          ∀ r : ℕ, Nat.card E = p ^ r → l ≤ r + 1) : l ≤ 4 := by
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨R, _, I, F, θ, hN, ⟨hI, hZ, hcp, hT, hdim⟩, hTB, -, -, hW48⟩ :=
    exists_model_at_nbr hres hB hK hΛ hlab hP fun _ _ _ _ h => h.2.2.1
  obtain ⟨hψ, hker, hperf, hA, hAI, -, h3, hsc⟩ := hTB
  obtain ⟨k, Θ, -, hW, hsgn, hperm, hSigned⟩ :=
    exists_signedModelSC hp hp2 hI hZ hcp hT hψ hker hperf hA hAI h3 hsc
  have hAut := SignedPermCount.ggAutomizer_card_eq_signed_of_model hp hp2 Θ hSigned hsgn hperm
  rw [hW48 hW] at hAut
  have hk : k = 3 := eq_three_of_two_pow_mul_factorial hAut.symm
  have hcardA : Nat.card (ggGamma K hN).range = p ^ k := by
    rw [← Nat.card_congr Θ.toEquiv, Nat.card_fun, Nat.card_fin]
    congr 1
    exact Nat.card_zmod p
  obtain ⟨E, hEab, hEcard, hEsc⟩ :=
    exists_selfCent_preimage hp hI hZ hψ hker hperf (hcp _ _ hψ hker hperf) hA hAI hsc
  have hne : ∃ y ∈ E, y ≠ 1 := by
    by_contra hcon
    push Not at hcon
    have hE1 : E = ⊥ := (Subgroup.eq_bot_iff_forall E).mpr hcon
    rw [hE1, Subgroup.card_bot, hcardA, hk] at hEcard
    have := Nat.one_lt_pow (by norm_num : 3 ≠ 0) hp.one_lt
    omega
  have := hdim E hEab hEsc hne k (hEcard.trans hcardA)
  omega

theorem nbrList_of_orth
    (hres : GGF4SmallRes p B Bs x L D J ks)
    (hB : ∀ K ∈ ks, GGWeylOfType p (CoxeterMatrix.B 3) (ggAutomizer K Bs)) {K : Subgroup G}
    (hK : K ∈ ks) {lab : LargeEvenLabel} (hΛ : LargeEvenInLambda2 lab)
    (htD : lab.tag = .D ∨ lab.tag = .twD) (hl : 4 ≤ lab.rank)
    (hlab : GGHasLabel lab (K ⧸ Subgroup.center K)) : GGF4NbrList p K := by
  have hcfg : GGConfig p B Bs x L D J := hres.1.1.1
  have hp : p.Prime := hcfg.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hcfg.1.2.2.2.2.2.1.2.1
  have hpq := halfSplit_dvd_at_nbr hres hK hΛ
    (by rcases htD with h | h <;> simp [GGF4TagClassical, h]) (Or.inr (Or.inr hl)) hlab
  obtain ⟨t, l, n⟩ := lab
  dsimp only at htD hl hpq
  rcases htD with rfl | rfl
  ·
    by_cases hE : p ∣ 2 ^ n - 1 ∨ (Even l ∧ p ∣ 2 ^ n + 1)
    · exact (false_of_orthEven_at_nbr hres hB hK hΛ hlab hl
        (largeEvenLabelAll_orthEven hp hp2 (Or.inl ⟨rfl, hl, hE⟩))).elim
    · have hplus : p ∣ 2 ^ n + 1 := hpq.resolve_left fun h => hE (Or.inl h)
      have hodd : Odd l := Nat.not_even_iff_odd.mp fun he => hE (Or.inr ⟨he, hplus⟩)
      have h5 : 5 ≤ l := by
        obtain ⟨j, hj⟩ := hodd
        omega
      have := rank_le_four_of_orthSigned_at_nbr hres hB hK hΛ hlab
        (largeEvenLabelAll_orthSigned hp hp2 (Or.inl ⟨rfl, h5, hodd, hplus⟩))
      omega
  ·
    by_cases hE : Even (l - 1) ∧ p ∣ 2 ^ n + 1
    · have h5 : 5 ≤ l := by
        obtain ⟨⟨j, hj⟩, -⟩ := hE
        omega
      exact (false_of_orthEven_at_nbr hres hB hK hΛ hlab hl
        (largeEvenLabelAll_orthEven hp hp2 (Or.inr ⟨rfl, h5, hE.1, hE.2⟩))).elim
    · have hS : p ∣ 2 ^ n - 1 ∨ (Odd (l - 1) ∧ p ∣ 2 ^ n + 1) := by
        rcases hpq with h | h
        · exact Or.inl h
        · exact Or.inr ⟨Nat.not_even_iff_odd.mp fun he => hE ⟨he, h⟩, h⟩
      have hl4 := rank_le_four_of_orthSigned_at_nbr hres hB hK hΛ hlab
        (largeEvenLabelAll_orthSigned hp hp2 (Or.inr ⟨rfl, hl, hS⟩))
      obtain rfl : l = 4 := by omega
      exact Or.inl ⟨n, hΛ.1, hpq, Or.inr hlab⟩

end Nbr

end F4H4Sp

end CFSG.StandardType

end

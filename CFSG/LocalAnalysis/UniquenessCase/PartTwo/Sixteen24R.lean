module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveSevenA
public import CFSG.GH74.Uniqueness.SU.SU1Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

namespace Sixteen24

theorem eight_le_card_of_hyp125 (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) : 8 ≤ Nat.card V := by
  rcases h.1 with ⟨hW, -⟩ | ⟨h0, -, -⟩
  · exact hW.1.2.1
  · exact uc22p22n_eight_le_card D hx h61 h0.2.1 h0.2.2.2.2.1

private theorem card_inf_centralizer_modEq {p : ℕ} [Fact p.Prime] {E Y : Subgroup G}
    (hE : IsPGroup p E) (hEY : E ≤ Subgroup.normalizer (Y : Set G)) :
    Nat.card (Y ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) ≡ Nat.card Y [MOD p] := by
  let : MulDistribMulAction E Y := Subgroup.conjMulDistribMulActionOfLeNormalizer E Y hEY
  have hsmul : ∀ (e : E) (y : Y), ((e • y : Y) : G) = (e : G) * y * (e : G)⁻¹ := fun _ _ => rfl
  have h := hE.card_modEq_card_fixedPoints Y
  have heq : Nat.card (MulAction.fixedPoints E Y) =
      Nat.card (Y ⊓ Subgroup.centralizer (E : Set G) : Subgroup G) := by
    refine Nat.card_congr
      { toFun := fun y => ⟨(y : Y), (y : Y).2, Subgroup.mem_centralizer_iff.mpr fun e he => ?_⟩
        invFun := fun y => ⟨⟨y, y.2.1⟩, MulAction.mem_fixedPoints.mpr fun e => Subtype.ext ?_⟩
        left_inv := fun y => rfl
        right_inv := fun y => rfl }
    · have h1 := MulAction.mem_fixedPoints.mp y.2 ⟨e, he⟩
      have h2 := congrArg Subtype.val h1
      rw [hsmul] at h2
      calc e * (y : G) = (e * (y : G) * e⁻¹) * e := by group
        _ = (y : G) * e := by rw [h2]
    · rw [hsmul]
      have h1 := Subgroup.mem_centralizer_iff.mp y.2.2 e e.2
      calc (e : G) * y * (e : G)⁻¹ = (y : G) * e * (e : G)⁻¹ := by rw [h1]
        _ = y := by group
  rw [heq] at h
  exact h.symm

private theorem succ_le_two_pow_of_dvd_sub {p a b : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hba : b < a) (h : p ∣ 2 ^ a - 2 ^ b) : p + 1 ≤ 2 ^ a := by
  have hsplit : 2 ^ a - 2 ^ b = 2 ^ b * (2 ^ (a - b) - 1) := by
    have hab : a = b + (a - b) := (Nat.add_sub_cancel' (le_of_lt hba)).symm
    have h2a : 2 ^ a = 2 ^ b * 2 ^ (a - b) := by rw [← pow_add, ← hab]
    rw [h2a, Nat.mul_sub_left_distrib, mul_one]
  have hcop : Nat.Coprime p (2 ^ b) :=
    ((Nat.coprime_primes hp Nat.prime_two).2 hp2).pow_right b
  have hdiv : p ∣ 2 ^ (a - b) - 1 := by
    rw [hsplit] at h
    exact hcop.dvd_of_dvd_mul_left h
  have hpos : 0 < 2 ^ (a - b) - 1 := by
    have h1 : 1 ≤ a - b := Nat.sub_pos_of_lt hba
    have h2 : 2 ≤ 2 ^ (a - b) := by
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (a - b) := Nat.pow_le_pow_right (by norm_num) h1
    omega
  have hple : p ≤ 2 ^ (a - b) - 1 := Nat.le_of_dvd hpos hdiv
  have hone : 1 ≤ 2 ^ (a - b) := by omega
  have hsub : 2 ^ (a - b) ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) (Nat.sub_le a b)
  omega

theorem succ_le_two_pow_rk_of_not_le_centralizer {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {E W : Subgroup G} (hE : IsPGroup p E) (hEW : E ≤ normalizer (W : Set G))
    (hW : IsElemAbelian 2 W) (hne : ¬ W ≤ centralizer (E : Set G)) :
    p + 1 ≤ 2 ^ rk ↥W := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hW2 : IsPGroup 2 W := hW.isPGroup
  have hC2 : IsPGroup 2 ↥(W ⊓ centralizer (E : Set G)) := hW2.to_le inf_le_left
  have hcardW : Nat.card W = 2 ^ rk ↥W := card_eq_two_pow_of_isPGroup hW2
  have hcardC : Nat.card ↥(W ⊓ centralizer (E : Set G)) =
      2 ^ rk ↥(W ⊓ centralizer (E : Set G)) := card_eq_two_pow_of_isPGroup hC2
  have hmod := card_inf_centralizer_modEq (p := p) (E := E) (Y := W) hE hEW
  rw [hcardC, hcardW] at hmod
  have hlt : (W ⊓ centralizer (E : Set G)) < W := by
    refine lt_of_le_of_ne inf_le_left ?_
    intro heq
    exact hne (heq ▸ inf_le_right)
  have hcardlt : Nat.card ↥(W ⊓ centralizer (E : Set G)) < Nat.card W :=
    Subgroup.card_lt_of_lt hlt
  rw [hcardC, hcardW] at hcardlt
  have hlt' : rk ↥(W ⊓ centralizer (E : Set G)) < rk ↥W :=
    (Nat.pow_lt_pow_iff_right (by norm_num : 1 < 2)).mp hcardlt
  have hba : 2 ^ rk ↥(W ⊓ centralizer (E : Set G)) ≤ 2 ^ rk ↥W := le_of_lt hcardlt
  have hdiv : p ∣ 2 ^ rk ↥W - 2 ^ rk ↥(W ⊓ centralizer (E : Set G)) :=
    (Nat.modEq_iff_dvd' hba).mp hmod
  exact succ_le_two_pow_of_dvd_sub hp hp2 hlt' hdiv

theorem k_lt_of_succ_le_two_pow (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) {p : ℕ} (hp : p ∈ D.sig) {m : ℕ} (hm : p + 1 ≤ 2 ^ m) :
    D.k < m := by
  have hk : D.k ≤ 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split_ifs <;> norm_num
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  have hp3 : 3 ≤ p := by
    have := hpP.two_le
    omega
  by_contra hle
  rcases eq_or_ne p 3 with rfl | hp3'
  · have hk1 : D.k = 1 := Data.k_eq_one_of_three_mem D hSg h1219 hp
    have h2 : 2 ^ m ≤ 2 ^ 1 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega
  · have h4 : 2 ^ m ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) (by omega)
    omega

theorem exists_noncyclic_k_lt_rk (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (hx : DataExt D) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) :
    ∃ p ∈ D.sig, ∃ B : Subgroup G, B ≤ D.M ∧ IsPGroup p B ∧ ¬ IsCyclic B ∧
      D.k < rk ↥(V ⊓ centralizer (B : Set G)) := by
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpP⟩
  have hk : D.k ≤ 2 := by
    unfold Data.k CFSG.LocalAnalysis.RankThreeUC.kParam
    split_ifs <;> norm_num
  obtain ⟨E, hEM, hEel, hEcard⟩ :=
    CFSG.GH74.Uniqueness.SU.SU1.exists_isElemAbelian_of_le_pRank hpP (H := D.M) (k := 3)
      (hSg.three_le p hp)
  haveI hEEA : CFSG.IsElementaryAbelian p E := hEel.isElementaryAbelian
  have hV2 : IsPGroup 2 V := h.isElemAbelian.isPGroup
  have hVcard : Nat.card V = 2 ^ rk ↥V := card_eq_two_pow_of_isPGroup hV2
  have hVp : ¬ p ∣ Nat.card V := by
    rw [hVcard]
    intro hdvd
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hpP Nat.prime_two).mp (hpP.dvd_of_dvd_pow hdvd))
  have hEMnorm : E ≤ normalizer (V : Set G) := hEM.trans h.pairFacts.le_normalizer
  by_cases hVCE : V ≤ centralizer (E : Set G)
  · refine ⟨p, hp, E, hEM, hEel.isPGroup, ?_, ?_⟩
    · intro hcyc
      have hdvd : Nat.card ↥E ∣ p := by
        rw [← hcyc.exponent_eq_card]
        exact hEEA.exponent_dvd_p
      rw [hEcard] at hdvd
      have hle : p ^ 3 ≤ p ^ 1 := by simpa using Nat.le_of_dvd hpP.pos hdvd
      have h31 : 3 ≤ 1 := (Nat.pow_le_pow_iff_right hpP.one_lt).mp hle
      omega
    · rw [inf_eq_left.mpr hVCE]
      exact lt_of_le_of_lt hk
        (TwelveSeven.two_lt_rk_of_card h.isElemAbelian (eight_le_card_of_hyp125 D hx h61 h))
  · haveI : Nontrivial ↥E :=
      Finite.one_lt_card_iff_nontrivial.mp (by
        rw [hEcard]
        exact Nat.one_lt_pow (by norm_num) hpP.one_lt)
    have hsup := CFSG.RankThree.PartOne.KE8F.le_iSup_hyperplane_centralizers (p := p) (A := E)
      (V := V) hEMnorm hVp
    have hex : ∃ B : Subgroup E, B.index = p ∧
        ¬ (V ⊓ centralizer ((B.map E.subtype : Subgroup G) : Set G)) ≤
          centralizer (E : Set G) := by
      by_contra hcon
      have hcon' : ∀ (B : Subgroup E) (_ : B.index = p),
          V ⊓ centralizer ((B.map E.subtype : Subgroup G) : Set G) ≤
            centralizer (E : Set G) := by
        intro B hB
        by_contra hW
        exact hcon ⟨B, hB, hW⟩
      exact hVCE (hsup.trans (iSup₂_le hcon'))
    obtain ⟨B, hB, hneW⟩ := hex
    have hB'E : B.map E.subtype ≤ E := Subgroup.map_subtype_le B
    haveI : IsMulCommutative ↥E := hEel.1
    have hcommE : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
      congrArg Subtype.val (mul_comm' (⟨a, ha⟩ : E) (⟨b, hb⟩ : E))
    have hEcent : E ≤ centralizer ((B.map E.subtype : Subgroup G) : Set G) := by
      intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      exact (hcommE e he b (hB'E hb)).symm
    have hEnormC : E ≤ normalizer (centralizer ((B.map E.subtype : Subgroup G) : Set G)) :=
      hEcent.trans Subgroup.le_normalizer
    have hEnormW : E ≤ normalizer ((V ⊓ centralizer ((B.map E.subtype : Subgroup G) : Set G) :
        Subgroup G) : Set G) :=
      (le_inf hEMnorm hEnormC).trans inf_normalizer_le_normalizer_inf
    have hW_el : IsElemAbelian 2 (V ⊓ centralizer ((B.map E.subtype : Subgroup G) : Set G)) :=
      h.isElemAbelian.mono inf_le_left
    have hle := succ_le_two_pow_rk_of_not_le_centralizer (E := E)
      (W := V ⊓ centralizer ((B.map E.subtype : Subgroup G) : Set G))
      hpP hp2 hEel.isPGroup hEnormW hW_el hneW
    have hklt := k_lt_of_succ_le_two_pow D hSg h1219 hp hle
    refine ⟨p, hp, B.map E.subtype, hB'E.trans hEM, (hEel.mono hB'E).isPGroup, ?_, hklt⟩
    have hBcard : Nat.card B = p ^ 2 := by
      have hcard := Subgroup.card_mul_index B
      rw [hB, hEcard] at hcard
      have hp3 : p ^ 3 = p ^ 2 * p := by ring
      rw [hp3] at hcard
      exact Nat.mul_right_cancel hpP.pos hcard
    have hB'card : Nat.card (B.map E.subtype) = p ^ 2 := by
      rw [Subgroup.card_map_of_injective (K := B) E.subtype_injective, hBcard]
    haveI : CFSG.IsElementaryAbelian p ↥(B.map E.subtype) :=
      (hEel.mono hB'E).isElementaryAbelian
    exact CFSG.IsElementaryAbelian.not_isCyclic_of_card_eq_prime_sq hB'card

theorem k_lt_rMV_of_hyp125 (D : Data G) (hSg : UC6S846.SigmaStd D) (h1219 : D.sig = D.sig1)
    (hx : DataExt D) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G} (h : Hyp125 D V₀ V) :
    (D.k : ℕ∞) < rMV D.M V := by
  obtain ⟨p, hp, B, hBM, hBp, hBc, hk⟩ := exists_noncyclic_k_lt_rk D hSg h1219 hx h61 h
  exact lt_of_lt_of_le (by exact_mod_cast hk)
    (rk_inf_centralizer_le_rMV D h61 hp hBM hBp hBc h.isElemAbelian)

theorem k_lt_rParam_of_hyp125 (D : Data G) (hSg : UC6S846.SigmaStd D)
    (h1219 : D.sig = D.sig1) (hx : DataExt D) (h61 : UC6.R6_1 D) {V₀ V : Subgroup G}
    (h : Hyp125 D V₀ V) : (D.k : ℕ∞) < E3.rParam V := by
  rw [← rMV_eq_rParam_of_inCalV D h.inCalV]
  exact k_lt_rMV_of_hyp125 D hSg h1219 hx h61 h

end Sixteen24

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

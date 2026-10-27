module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yd
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yg
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22yc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped Pointwise

namespace P22y

theorem mem_normalizer_of_map_conj_eq {A : Type} [Group A] {H : Subgroup A} {g : A}
    (h : H.map (MulAut.conj g).toMonoidHom = H) : g ∈ normalizer (H : Set A) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    rw [← h]
    exact ⟨x, hx, rfl⟩
  · intro hx
    rw [← h] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    have : y = x := by
      have h1 : g * y * g⁻¹ = g * x * g⁻¹ := hyx
      simpa using h1
    rwa [← this]

theorem mulAut_smul_eq_map {A : Type} [Group A] (a : MulAut A) (H : Subgroup A) :
    a • H = H.map a.toMonoidHom := by
  ext x
  rw [Subgroup.mem_smul_pointwise_iff_exists]
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩
  · rintro ⟨y, hy, rfl⟩
    exact ⟨y, hy, rfl⟩

theorem one_le_of_isL2Ev {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) : 1 ≤ n := by
  obtain ⟨F, _, _, hF, -⟩ := h
  exact one_le_of_card hF

theorem six_lt_card_of_isL2Ev {X : Type} [Group X] {n : ℕ} (h : IsL2Ev X n) (hn : 2 ≤ n) :
    6 < Nat.card X := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := h
  rw [Nat.card_congr e.toEquiv, CFSG.Open.StatedAPI.card_statedSL_two, hF]
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h16 : 16 ≤ (2 ^ n) ^ 2 := by nlinarith
  have h15 : 15 ≤ (2 ^ n) ^ 2 - 1 := by omega
  nlinarith

end P22y

open P22y

variable {G : Type} [Group G] [Finite G]

theorem uc22p22yh_s22_6hat_of (D : Data G) (Ch : Choice2011 G) (h2 : S22_3_2 D Ch) (h3 : S22_3_3 D Ch)
    (h51 : S22_5_1 D Ch) (h61 : UC6.R6_1 D) (hX : DataExt D) (h119 : R119W D) (h1110 : R1110W D)
    (hW : InCalW D.M D.T D.U) (hsig3 : 3 < CFSG.Open.pRank 3 D.M → 3 ∈ D.sig) :
    H1930 D → ∀ _ : Ctx22c D Ch, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)),
      NbarSplit D Nb → Cl22_6Hat D Nb := by
  intro hH c m Nb hNb i
  classical
  set E : Subgroup G := proofEiHat D (preN D (Nb i)) with hE
  obtain ⟨hEne, hEU⟩ := uc22p22xg_proofEiHat_ne_bot D Ch h2 h3 h51 hH c m Nb hNb i
  have hE2 : IsPGroup 2 ↥E := ((uc22p22e_inCalV_U D).2.2.2.isPGroup).to_le hEU
  suffices hsuff : ∃ r ∈ D.sig, ∃ X : Subgroup G, X ≤ D.M ∧ X ≤ normalizer (E : Set G) ∧
      IsPGroup r ↥X ∧ ¬ IsCyclic ↥X by
    obtain ⟨r, hr, X, hXM, hXN, hXp, hXc⟩ := hsuff
    exact PartTwo.normalizer_le_of_noncyclic D h61 hr hXM hXp hXc hEne hE2 hXN
  have hcl := h51 hH c m Nb hNb
  obtain ⟨n, hn, -⟩ := hcl i
  obtain ⟨p, hp⟩ := hX.sig_nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpp⟩
  obtain ⟨P₀, hP₀M, hP₀el, hP₀card⟩ :=
    CFSG.SectionRank.exists_isElemAbelian_card_of_le_pRank (p := p) (hX.three_le p hp)
  set ρ : ↥P₀ →* MulAut (MBar D.M D.U) :=
    (MulAut.conj : MBar D.M D.U →* MulAut (MBar D.M D.U)).comp (toMbarOf D hP₀M) with hρ
  letI : MulAction ↥P₀ (Subgroup (MBar D.M D.U)) := MulAction.compHom _ ρ
  have hsmul : ∀ (x : ↥P₀) (H : Subgroup (MBar D.M D.U)),
      x • H = H.map (MulAut.conj (toMbarOf D hP₀M x)).toMonoidHom := fun x H => by
    rw [MulAction.compHom_smul_def, mulAut_smul_eq_map]
    rfl
  set Stab : Subgroup ↥P₀ := MulAction.stabilizer ↥P₀ (Nb i) with hStab
  have hStabN : ∀ x ∈ Stab, toMbarOf D hP₀M x ∈ normalizer (Nb i : Set (MBar D.M D.U)) := by
    intro x hx
    exact mem_normalizer_of_map_conj_eq ((hsmul x (Nb i)).symm.trans hx)
  have horb : ∀ H ∈ MulAction.orbit ↥P₀ (Nb i), ∃ j, H = Nb j ∧ Nat.card (Nb j) = Nat.card (Nb i) := by
    rintro H ⟨x, rfl⟩
    obtain ⟨τ, hτ⟩ := uc22p22ya_exists_perm D hNb hcl (toMbarOf D hP₀M x)
    refine ⟨τ i, ?_, ?_⟩
    · show x • Nb i = Nb (τ i)
      rw [hsmul, hτ]
    · rw [← hτ i, Subgroup.card_map_of_injective (MulAut.conj _).injective]
  set O : Finset (Fin m) := Finset.univ.filter fun j => Nb j ∈ MulAction.orbit ↥P₀ (Nb i) with hO
  have hNbinj : Function.Injective Nb := uc22p22yd_nb_injective D hNb fun j => by
    obtain ⟨n', hn', -⟩ := hcl j
    intro hbot
    have hcard := three_dvd_card_of_isL2Ev hn'
    rw [hbot, Subgroup.card_bot] at hcard
    omega
  have hOcard : Stab.index ≤ O.card := by
    rw [hStab, MulAction.index_stabilizer]
    have hsub : MulAction.orbit ↥P₀ (Nb i) ⊆ Nb '' (O : Set (Fin m)) := by
      intro H hH'
      obtain ⟨j, rfl, -⟩ := horb H hH'
      exact ⟨j, by simp [hO, hH'], rfl⟩
    calc (MulAction.orbit ↥P₀ (Nb i)).ncard ≤ (Nb '' (O : Set (Fin m))).ncard :=
          Set.ncard_le_ncard hsub (Set.toFinite _)
      _ = O.card := by rw [Set.ncard_image_of_injective _ hNbinj, Set.ncard_coe_finset]
  have hOmem : ∀ j ∈ O, Nat.card (Nb j) = Nat.card (Nb i) := by
    intro j hj
    have hj' : Nb j ∈ MulAction.orbit ↥P₀ (Nb i) := by simpa [hO] using hj
    obtain ⟨k, hk, hkc⟩ := horb _ hj'
    rw [hNbinj hk, hkc]
  have hiO : i ∈ O := by simp [hO, MulAction.mem_orbit_self]
  have hidx : Stab.index ∣ p ^ 3 := hP₀card ▸ Subgroup.index_dvd_card Stab
  obtain ⟨a, ha3, ha⟩ := (Nat.dvd_prime_pow hpp).1 hidx
  have htwo : 3 ≤ O.card → ∃ k l, k ∈ O ∧ l ∈ O ∧ k ≠ i ∧ l ≠ i ∧ k ≠ l := by
    intro h3O
    have h2 : 1 < (O.erase i).card := by
      rw [Finset.card_erase_of_mem hiO]
      omega
    obtain ⟨k, hk, l, hl, hkl⟩ := Finset.one_lt_card.1 h2
    exact ⟨k, l, Finset.mem_of_mem_erase hk, Finset.mem_of_mem_erase hl, Finset.ne_of_mem_erase hk,
      Finset.ne_of_mem_erase hl, hkl⟩
  have hp3 : 3 ≤ p := by
    have := hpp.two_le
    omega
  rcases Nat.eq_zero_or_pos a with ha0 | ha0
  ·
    have hStabtop : Stab = ⊤ := by
      rw [ha0, pow_zero] at ha
      exact Subgroup.index_eq_one.1 ha
    exact ⟨p, hp, uc22p22yc_caseA D Ch h2 h3 h51 hH c m Nb hNb i hpp hp2 hP₀M hP₀el hP₀card
      fun x => hStabN x (hStabtop ▸ Subgroup.mem_top x)⟩
  · have hpO : p ≤ O.card := by
      calc p = p ^ 1 := (pow_one p).symm
        _ ≤ p ^ a := Nat.pow_le_pow_right hpp.pos ha0
        _ = Stab.index := ha.symm
        _ ≤ O.card := hOcard
    obtain ⟨k, l, hkO, hlO, hki, hli, hkl⟩ := htwo (hp3.trans hpO)
    by_cases hpN : p ∣ Nat.card (Nb i)
    ·
      exact ⟨p, hp, uc22p22yd_two_factors D Ch h2 h3 h51 hH c m Nb hNb hki hli hkl hpp
        ((hOmem k hkO).symm ▸ hpN) ((hOmem l hlO).symm ▸ hpN)⟩
    · rcases Nat.lt_or_ge a 2 with ha1 | ha2
      ·
        have ha1' : a = 1 := by omega
        rw [ha1', pow_one] at ha
        set Pi : Subgroup G := Stab.map P₀.subtype with hPi
        have hPiM : Pi ≤ D.M := (Subgroup.map_subtype_le Stab).trans hP₀M
        have hPiel : IsElemAbelian p Pi := hP₀el.mono (Subgroup.map_subtype_le Stab)
        have hPicard : p ^ 2 ≤ Nat.card Pi := by
          rw [hPi, Subgroup.card_map_of_injective P₀.subtype_injective]
          have h1 := Subgroup.card_mul_index Stab
          rw [ha, hP₀card] at h1
          have h2 : Nat.card ↥Stab * p = p ^ 2 * p := by rw [h1]; ring
          exact (Nat.eq_of_mul_eq_mul_right hpp.pos h2).ge
        have hPiN : ∀ x : ↥Pi, toMbarOf D hPiM x ∈ normalizer (Nb i : Set (MBar D.M D.U)) := by
          rintro ⟨_, ⟨s, hs, rfl⟩⟩
          exact hStabN s hs
        exact ⟨p, hp, uc22p22yc_caseA2 D Ch h2 h3 h51 hH c m Nb hNb i hpp hp2 hPiM hPiel hPicard hpN hPiN⟩
      ·
        have hp2O : 9 ≤ O.card := by
          calc 9 = 3 ^ 2 := by norm_num
            _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
            _ ≤ p ^ a := Nat.pow_le_pow_right hpp.pos ha2
            _ = Stab.index := ha.symm
            _ ≤ O.card := hOcard
        have h3sig : 3 ∈ D.sig := by
          apply hsig3
          have hn1 := one_le_of_isL2Ev hn
          rcases Nat.lt_or_ge n 2 with hn2 | hn2
          ·
            have hn1' : n = 1 := by omega
            subst hn1'
            have h6i := card_of_isL2Ev_one hn
            refine uc22p22ye_three_lt_pRank D Ch h51 h1110 hW hH c m Nb hNb ?_
            refine le_trans (by omega) (Finset.card_le_card (s := O) fun j hj => ?_)
            simp only [Finset.mem_filter, Finset.mem_univ, true_and]
            rw [hOmem j hj, h6i]
          ·
            have h6i := six_lt_card_of_isL2Ev hn hn2
            exact uc22p22yg_three_lt_pRank D Ch h51 h119 hW hH c m Nb hNb O (by omega)
              fun j hj => (hOmem j hj).symm ▸ h6i
        have h3N : 3 ∣ Nat.card (Nb i) := three_dvd_card_of_isL2Ev hn
        exact ⟨3, h3sig, uc22p22yd_two_factors D Ch h2 h3 h51 hH c m Nb hNb hki hli hkl Nat.prime_three
          ((hOmem k hkO).symm ▸ h3N) ((hOmem l hlO).symm ▸ h3N)⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

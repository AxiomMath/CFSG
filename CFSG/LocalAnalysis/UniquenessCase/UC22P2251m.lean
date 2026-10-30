module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251n
import CFSG.LocalAnalysis.UniquenessCase.UC22R8107PairCore
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251K
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251c
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.Quasithin.H13.KG14726Alt

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

theorem BadShape22.not_dvd_card_mulAut_of_not_dvd {X : Type} [Group X] [Finite X] (h : BadShape22 X) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) (hpX : ¬ p ∣ Nat.card X) : ¬ p ∣ Nat.card (MulAut X) := by
  have h2 : Nat.card (MulAut X) ∣ 2 * Nat.card X := by
    rcases h with h | h
    · obtain ⟨e⟩ := BadShape22.nonempty_mulEquiv_alt_five_of_isL2Ev_two h
      rw [Nat.card_congr (MulAut.congr e).toEquiv, Nat.card_congr e.toEquiv,
        CFSG.Quasithin.H13.KG14726.card_mulAut_alternatingGroup (by norm_num) (by norm_num),
        Nat.card_eq_fintype_card, card_alternatingGroup]
      decide
    · rw [PartTwo.card_eq_of_isL3 h]
      exact PartTwo.card_mulAut_dvd_of_isL3 h
  intro hdvd
  rcases (Nat.Prime.dvd_mul hp).1 (hdvd.trans h2) with h' | h'
  · have := Nat.le_of_dvd (by norm_num) h'
    omega
  · exact hpX h'

variable {G : Type} [Group G] [Finite G]

theorem P2251m.exists_elemAbelian_of_pair_of_not_dvd {M K L : Subgroup G} (hK : K ∈ calC M)
    (hKn : (K.subgroupOf M).Normal) (hL : L ∈ calC M) (hKL : K ≠ L) (hKs : BadShape22 (Bar2 K))
    (hLs : LayerShape22 (Bar2 L)) (hM3 : CFSG.Open.pRank 3 M ≤ 3) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hM : 3 ≤ CFSG.Open.pRank p M) (hpK : ¬ p ∣ Nat.card (Bar2 K)) :
    ∃ R E A : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 3 R M ∧ E ≤ R ⊓ centralizer (R : Set G) ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ A ≤ M ⊓ centralizer (E : Set G) ∧ IsElemAbelian p A ∧
      Nat.card A = p ^ 2 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hMK : M ≤ normalizer (K : Set G) := (normal_subgroupOf_iff_le_normalizer hK.1.le).1 hKn
  have hK3 := hKs.layerShape.three_dvd_card
  have hKZ := hKs.layerShape.center_eq_bot
  have hLN : ∀ H : Subgroup G, H ≤ M → Odd (Nat.card H) → H ≤ normalizer (L : Set G) := fun _ hHM hH =>
    P2251c.le_normalizer_of_pRank_le hK hKn hL hKL hK3 hKZ hLs.three_dvd_card hLs.center_eq_bot hM3 hHM hH
  obtain ⟨A₀, hA₀M, hA₀, hA₀c⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hM
  have hA₀K := hA₀M.trans hMK
  have hA₀L := hLN A₀ hA₀M (hA₀c ▸ (hp.odd_of_ne_two hp2).pow)
  have hexp : ∀ w : ↥A₀, w ^ p = 1 := fun w =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hA₀.2 _ w.2)
  have hpA := hKs.not_dvd_card_mulAut_of_not_dvd hp hp5 hpK
  have hA₀C : ∀ w : ↥A₀, UC6S846.rhoL K (inclusion hA₀K w) = 1 := fun w => by
    have h1 : (UC6S846.rhoL K (inclusion hA₀K w)) ^ p = 1 := by rw [← map_pow, ← map_pow, hexp, map_one, map_one]
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one h1) with h | h
    · exact orderOf_eq_one_iff.1 h
    · exact absurd (h ▸ orderOf_dvd_natCard _) hpA
  obtain ⟨Q, hQA₀, hQc, b, hbL, hb3, hbQ⟩ : ∃ Q ≤ A₀, p ^ 2 ≤ Nat.card Q ∧ ∃ b ∈ L, orderOf b = 3 ∧
      ∀ u ∈ Q, b⁻¹ * (u * b * u⁻¹) ∈ pCoreOf 2 L := by
    obtain ⟨x, hx3, Q, hQc, hQx⟩ := P2251d.exists_orderOf_three_card_le_of_layerShape hLs hp hp2 hexp
      (fun x y => Subtype.ext (by rw [Subgroup.coe_mul, Subgroup.coe_mul]; exact hA₀.comm x.2 y.2))
      ((UC6S846.rhoL L).comp (inclusion hA₀L)) hA₀c.ge
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    have h3l : 3 ∣ orderOf l := by
      have h := orderOf_map_dvd (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) l
      rwa [QuotientGroup.mk'_apply, hx3] at h
    have hfix : ∀ v ∈ Q, UC6S846.rhoL L (inclusion hA₀L v) ((l ^ (orderOf l / 3) : ↥L) : Bar2 L) =
        ((l ^ (orderOf l / 3) : ↥L) : Bar2 L) := fun v hv => by
      rw [QuotientGroup.mk_pow, map_pow]
      exact congrArg (· ^ (orderOf l / 3)) (hQx v hv)
    refine ⟨Q.map A₀.subtype, map_subtype_le _, by rwa [card_map_of_injective A₀.subtype_injective], _,
      (l ^ (orderOf l / 3)).2, by rw [Subgroup.orderOf_coe]; exact orderOf_pow_orderOf_div (orderOf_pos l).ne' h3l, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    exact P2251d.inv_mul_conj_mem_of_rhoL (inclusion hA₀L v) (l ^ (orderOf l / 3)).2 (hfix v hv)
  obtain ⟨b₁, hb₁K, hb₁⟩ := P2251c.exists_orderOf_three_mem hK3
  refine R8107Pair.exists_elemAbelian_of_fixed_pair hK hL hKL (fun _ hHM _ => hHM.trans hMK) hLN hKZ
    (fun _ hBK hB => uc22p2251b_isCyclic_of_isPGroup hKs.layerShape Nat.prime_three (by norm_num) hBK hB)
    (fun _ hBL hB => uc22p2251b_isCyclic_of_isPGroup hLs Nat.prime_three (by norm_num) hBL hB)
    hp hp2 (hQA₀.trans hA₀M) (hA₀.mono hQA₀) hQc hb₁K hb₁ (fun u hu => ?_) hbL hb3 hbQ
  exact P2251d.inv_mul_conj_mem_of_rhoL (inclusion hA₀K ⟨u, hQA₀ hu⟩) hb₁K
    (by rw [hA₀C ⟨u, hQA₀ hu⟩, MulAut.one_apply])

theorem uc22p2251m_eq (D : Data G) (hx : DataExt D) (hSg : UC6S846.SigmaStd D) (hk : D.k = 2)
    (h76 : ∀ L ∈ calC D.M, ∀ p ∈ D.sig, Conclusion76 D.M p) (h614 : UC6.R6_14 D) {K L : Subgroup G}
    (hK : K ∈ calC D.M) (hKn : (K.subgroupOf D.M).Normal) (hKs : BadShape22 (Bar2 K)) (hL : L ∈ calC D.M)
    (hLs : LayerShape22 (Bar2 L)) {p : ℕ} (hp : p ∈ D.sig) (hpK : ¬ p ∣ Nat.card (Bar2 K)) : L = K := by
  by_contra hLK
  have hns := UC6S846.not_solvable_of_mem_calC hK
  have h3 := (Data.k_eq_two_iff D).1 hk
  have h3σ : 3 ∉ D.sig := fun h => h3 (UC6S846.sp_of_mem_sig hSg hns h)
  have hM3 : CFSG.Open.pRank 3 D.M ≤ 3 := by
    by_contra h
    exact h3σ (hSg.four_mem 3 Nat.prime_three (by norm_num) (by omega))
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp5 : 5 ≤ p := by
    have h2 := hpp.two_le
    have hp3 : p ≠ 3 := fun h => h3σ (h ▸ hp)
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hpp
    omega
  obtain ⟨R, E, A, hR, hEZ, hEel, hEc, hA, hAel, hAc⟩ := P2251m.exists_elemAbelian_of_pair_of_not_dvd hK hKn hL
    (Ne.symm hLK) hKs hLs hM3 hpp hp5 (hx.three_le p hp) hpK
  have hΓ := h76 K hK p hp 3 Nat.prime_three E (hEZ.trans (inf_le_left.trans hR.le)) hEel hEc
    (lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp hA hAel hAc))
    (fun X hXE _ => lt_of_lt_of_le (by norm_num) (UC6S846.le_pRank' hpp
      (hA.trans (inf_le_inf_left _ ((centralizer_le hXE).trans (centralizer_le_normalizer _)))) hAel hAc))
  exact h3 (h614 (UC6S846.sig_subset_sig1 hSg hns) 3 Nat.prime_three (by norm_num) h3σ R hR E hEZ hEel hEc hΓ)

theorem uc22p2251m_isL2Ev_one (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h119 : R119W D) (h17 : S21_17 D Ch) (hH : H1930 D) (c : Ctx22 D Ch) (hSg : UC6S846.SigmaStd D)
    (hk : D.k = 2) (h76 : ∀ L ∈ calC D.M, ∀ p ∈ D.sig, Conclusion76 D.M p) (h614 : UC6.R6_14 D) {m : ℕ}
    {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) {i : Fin m}
    (hbad : ¬ ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2) {p : ℕ} (hp : p ∈ D.sig) (hpi : ¬ p ∣ Nat.card ↥(Nb i)) :
    ∀ j, j ≠ i → IsL2Ev ↥(Nb j) 1 := by
  intro j hji
  by_contra hj
  obtain ⟨K, hK, hKb, ⟨eK⟩, hKs, hKn⟩ := uc22p2251b_exists_bad D hx h61 h119 h17 hH c hNb hbad
  have hpK : ¬ p ∣ Nat.card (Bar2 K) := fun h => hpi ((Nat.card_congr eK.toEquiv ▸ h).trans
    (Subgroup.card_dvd_of_le (Subgroup.commutator_le_self _)))
  obtain ⟨L, hL, hLb, -, hLs⟩ := uc22p2251b_exists_lift_nb D hx h61 h119 c hNb j hj
  exact uc22p2251b_ne D hNb (Ne.symm hji) (P2251b.not_isL2Ev_one_of_bad hbad) hKb hLb
    (uc22p2251m_eq D hx hSg hk h76 h614 hK hKn hKs hL hLs hp hpK).symm

theorem s22_5_1K2_of_not_dvd (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h119 : R119W D) (h17 : S21_17 D Ch) (h31 : S22_3_1 D Ch) (h33 : S22_3_3 D Ch)
    (hSg : UC6S846.SigmaStd D) (hk : D.k = 2) (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) (hH : H1930 D)
    (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb) (i : Fin m) {p : ℕ}
    (hp : p ∈ D.sig) (hpi : ¬ p ∣ Nat.card ↥(Nb i)) : ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2 := by
  by_contra hbad
  have h76' : ∀ L ∈ calC D.M, ∀ p ∈ D.sig, Conclusion76 D.M p := fun L hL p hp =>
    h76 p hp (D.sig_prime p hp).2 (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp)
  have hS3 := uc22p2251m_isL2Ev_one D Ch hx h61 h119 h17 hH c.toCtx22 hSg hk h76' h614 hNb hbad hp hpi
  have hbad' : IsL2Ev ↥(Nb i) 2 ∨ IsL3 ↥(Nb i) 1 ∨ IsS5 ↥(Nb i) := by
    rcases hNb.2 i with ⟨n, hn⟩ | h | h
    · obtain rfl : n = 2 := by
        by_contra hne
        exact hbad ⟨n, hn, hne⟩
      exact Or.inl hn
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨K, hK, -⟩ := uc22p2251b_exists_bad D hx h61 h119 h17 hH c.toCtx22 hNb hbad
  have h3σ : 3 ∉ D.sig := fun h =>
    (Data.k_eq_two_iff D).1 hk (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hK) h)
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp5 : 5 ≤ p := by
    have h2 := hpp.two_le
    have hp3 : p ≠ 3 := fun h => h3σ (h ▸ hp)
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hpp
    omega
  exact (h31 hH c).2 (uc22p2251n_calCGS_le D Ch hx h61 h33 hH c hNb hS3 hbad' hp hp5 hpi)

theorem s22_5_1_of_s22_5_1R3 {D : Data G} {Ch : Choice2011 G} (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h119 : R119W D) (h17 : S21_17 D Ch) (h31 : S22_3_1 D Ch) (h33 : S22_3_3 D Ch)
    (hSg : UC6S846.SigmaStd D) (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) (h : S22_5_1R3 D Ch) :
    S22_5_1 D Ch := by
  refine s22_5_1_of_branches (fun hk hH c m Nb hNb i => h hH c m Nb hNb i (Or.inl hk)) fun hk hH c m Nb hNb i => ?_
  by_cases hall : ∀ p ∈ D.sig, p ∣ Nat.card ↥(Nb i)
  · exact h hH c m Nb hNb i (Or.inr hall)
  · push Not at hall
    obtain ⟨p, hp, hpi⟩ := hall
    exact s22_5_1K2_of_not_dvd D Ch hx h61 h119 h17 h31 h33 hSg hk h76 h614 hH c hNb i hp hpi

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

module

public import CFSG.Quasithin.Background.KnownMultL2
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Case
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem25Small

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3

@[expose] def Lie625Elim : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V : Subgroup G) (n : ℕ) (l : G) (DL K : Subgroup G),
    In625 → Dat625 T M L V n l DL K → ¬ IsLieChar2Big (KBar K)

theorem exists_prime_dvd_two_pow_sub_one_ne_three {n : ℕ} (hn : 3 ≤ n) :
    ∃ r : ℕ, r.Prime ∧ r ∣ 2 ^ n - 1 ∧ r ≠ 3 := by
  by_contra hcon
  push Not at hcon
  have h8 : 8 ∣ 2 ^ n := by
    have e : 2 ^ n = 2 ^ 3 * 2 ^ (n - 3) := by rw [← pow_add]; congr 1; omega
    rw [e]
    exact Dvd.intro _ rfl
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hpos : 2 ^ n - 1 ≠ 0 := by omega
  have heq := Nat.eq_prime_pow_of_unique_prime_dvd hpos (fun {d} hd hdvd => hcon d hd hdvd)
  have h3 : ∀ a : ℕ, 3 ^ a % 8 = 1 ∨ 3 ^ a % 8 = 3 := by
    intro a
    induction a with
    | zero => left; rfl
    | succ k ih => rw [pow_succ, Nat.mul_mod]; rcases ih with h | h <;> rw [h] <;> norm_num
  have h7 : (2 ^ n - 1) % 8 = 7 := by omega
  rcases h3 (2 ^ n - 1).primeFactorsList.length with h | h <;> rw [← heq] at h <;> omega

theorem statedClassicalModel_psl_of_mulEquiv_ch625 {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    {n p f : ℕ} (h : CFSG.Assembly.LowTwoRank.StatedClassicalModel Y .PSL n p f) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL n p f :=
  CFSG.Open.StatedAPI.statedClassicalModel_of_mulEquiv e.symm h

variable {G : Type} [Group G] [Finite G]

namespace Dat625

variable {T M L V : Subgroup G} {n : ℕ} {l : G} {DL K : Subgroup G}
  (hI : In625) (d : Dat625 T M L V n l DL K)
include d

theorem exists_mem_DL_orderOf {r : ℕ} (hr : r.Prime) (hrd : r ∣ 2 ^ n - 1) :
    ∃ x ∈ DL, orderOf x = r := by
  have : Fact r.Prime := ⟨hr⟩
  obtain ⟨-, hc⟩ := d.hyp.card_DL d.hall
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥DL) r (hc ▸ hrd)
  exact ⟨x, x.2, by rw [← hx, Subgroup.orderOf_coe]⟩

include hI in
theorem n_eq_two (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact)
    (kf3 : SmallGroup625Fact) (h23 : A23SQTKListFact) (hLie : Lie625Elim) : n = 2 := by
  by_contra hn
  have hn3 : 3 ≤ n := by have := d.hyp.toHyp5_0_1.two_le; omega
  obtain ⟨r, hr, hrd, hr3⟩ := exists_prime_dvd_two_pow_sub_one_ne_three hn3
  have hr2 : r ≠ 2 := by
    rintro rfl
    have h2 : 2 ∣ 2 ^ n := dvd_pow_self 2 (by omega)
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
    omega
  obtain ⟨x, hx, hxr⟩ := d.exists_mem_DL_orderOf hr hrd
  rcases d.kf2_cases hI kf1 kf2 h23 hx hr hr2 hxr with hL | ⟨h7, hinn, hD⟩ | ⟨h3, -⟩ |
      ⟨h3, -⟩
  · exact hLie G T M L V n l DL K hI d hL
  · subst h7
    exact d.false_of_3D4 hI kf3 hx hxr hinn hD
  · exact hr3 h3
  · exact hr3 h3

include hI in
theorem exists_isPSL (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact)
    (kf3 : SmallGroup625Fact) (h23 : A23SQTKListFact) (hLie : Lie625Elim) (hn : n = 2) :
    ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧ IsPSL 2 p 1 (KBar K) := by
  obtain ⟨x, hx, hxr⟩ := d.exists_mem_DL_orderOf Nat.prime_three (by subst hn; norm_num)
  rcases d.kf2_cases hI kf1 kf2 h23 hx Nat.prime_three (by norm_num) hxr with hL |
      ⟨h7, -⟩ | ⟨-, hinn, hJ⟩ | ⟨-, -, hp⟩
  · exact absurd hL (hLie G T M L V n l DL K hI d)
  · norm_num at h7
  · exact (d.false_of_J2 hI kf3 hx hxr hinn hJ).elim
  · exact hp

include hI in
theorem centralizerMod_K_eq :
    centralizerMod (ch6ZS T L V) K (ch6U T L V) = pCoreOf 2 K := by
  have hCH := d.hyp.ch6CH_eq hI.h432 hI.h6111 hI.h6119
  apply le_antisymm
  · intro x hx
    have hxCH : x ∈ ch6CH T L V := ⟨d.K_le_H hx.1, hx.2.1, hx.2.2⟩
    rw [hCH] at hxCH
    exact d.inf_O2_le ⟨hx.1, hxCH⟩
  · intro x hx
    have hxK : x ∈ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K hx
    have hxO : x ∈ pCoreOf 2 (Subgroup.centralizer (ch6ZS T L V : Set G)) :=
      A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp d.comp) hx
    rw [← hCH] at hxO
    exact ⟨hxK, hxO.2.1, hxO.2.2⟩

include hI in
theorem nonempty_quot_mulEquiv (hZ : Subgroup.center (KQ K) = ⊥)
    [hN : ((centralizerMod (ch6ZS T L V) K (ch6U T L V)).subgroupOf K).Normal] :
    Nonempty ((↥K ⧸ (centralizerMod (ch6ZS T L V) K (ch6U T L V)).subgroupOf K) ≃* KBar K) := by
  have hNeq : (centralizerMod (ch6ZS T L V) K (ch6U T L V)).subgroupOf K = CFSG.pCore 2 ↥K := by
    rw [d.centralizerMod_K_eq hI, pCoreOf_two_eq_map_ch625]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hNeq).trans
    ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm⟩

include hI in
theorem lieModel_quot (kf1 : OutTwoNilpotentFact) (kf2 : OddSylowNormalizerFact)
    (kf3 : SmallGroup625Fact) (h23 : A23SQTKListFact) (hLie : Lie625Elim) (hn : n = 2) :
    ∃ p : ℕ, p.Prime ∧ 11 ≤ p ∧ (p % 8 = 3 ∨ p % 8 = 5) ∧
      ∀ _ : ((centralizerMod (ch6ZS T L V) K (ch6U T L V)).subgroupOf K).Normal,
        CFSG.Blueprint.LieModel
          (↥K ⧸ (centralizerMod (ch6ZS T L V) K (ch6U T L V)).subgroupOf K) .PSL 2 p 1 := by
  obtain ⟨p, hp, hp11, hp8, hK⟩ := d.exists_isPSL hI kf1 kf2 kf3 h23 hLie hn
  refine ⟨p, hp, hp11, hp8, fun hN => ?_⟩
  have hZ := d.center_KQ_of_L2 l2MultiplierFact hp (by omega) hK
  obtain ⟨e⟩ := d.nonempty_quot_mulEquiv hI hZ
  exact Or.inl ⟨by decide, statedClassicalModel_psl_of_mulEquiv_ch625 e hK⟩

end Dat625

end CFSG.Quasithin.H13

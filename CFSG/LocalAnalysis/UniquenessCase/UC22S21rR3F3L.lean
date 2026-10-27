module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3Res
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InducedQuotInfAut
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3A
import CFSG.LocalAnalysis.UniquenessCase.UC22P21b
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4XB
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour
import CFSG.Quasithin.H13.KGFactLieOutAbL

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

private theorem false_of_conj_eq_inv {X : Type} [Group X] (N : Subgroup (MulAut X))
    {θ μ : MulAut X} {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hθr : orderOf θ = r)
    (hμ : μ * θ * μ⁻¹ = θ⁻¹) (hN : μ * θ * μ⁻¹ * θ⁻¹ ∈ N) (hθN : θ ∉ N) : False := by
  rw [hμ] at hN
  obtain ⟨k, hk⟩ := hr.odd_of_ne_two hr2
  have hordg : orderOf (θ⁻¹) = r := by rw [orderOf_inv, hθr]
  have hpow : (θ⁻¹) = ((θ⁻¹) ^ 2) ^ (k + 1) := by
    have h1 : 2 * (k + 1) = orderOf (θ⁻¹) + 1 := by omega
    rw [← pow_mul, h1, pow_succ, pow_orderOf_eq_one, one_mul]
  have hmem : (θ⁻¹) ∈ N := by
    rw [hpow]
    exact N.pow_mem (by simpa [pow_two] using hN) (k + 1)
  exact hθN (by simpa using N.inv_mem hmem)

private theorem false_of_inverted {L : Subgroup G}
    (N : Subgroup (MulAut (BarInf L ⧸ Subgroup.center (BarInf L))))
    {b m : G} (hbN : b ∈ normalizer (L : Set G)) (hmN : m ∈ normalizer (L : Set G)) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r)
    (hθN : inducedQuotInfAut L b hbN ∉ N)
    (hcommN : ∀ α β : MulAut (BarInf L ⧸ Subgroup.center (BarInf L)),
      α * β * α⁻¹ * β⁻¹ ∈ N) (hmb : m * b * m⁻¹ = b⁻¹) : False := by
  have hθr : orderOf (inducedQuotInfAut L b hbN) = r := by
    have hdvd : orderOf (inducedQuotInfAut L b hbN) ∣ r := by
      have h := orderOf_inducedQuotInfAut_dvd L (x := b) hbN
      rwa [hbr] at h
    have hne : inducedQuotInfAut L b hbN ≠ 1 := fun h1 => hθN (h1 ▸ N.one_mem)
    have hne1 : orderOf (inducedQuotInfAut L b hbN) ≠ 1 := fun h1 =>
      hne (orderOf_eq_one_iff.mp h1)
    rcases (Nat.dvd_prime hr).mp hdvd with h | h
    · exact absurd h hne1
    · exact h
  have hμ : inducedQuotInfAut L m hmN * inducedQuotInfAut L b hbN *
      (inducedQuotInfAut L m hmN)⁻¹ = (inducedQuotInfAut L b hbN)⁻¹ := by
    have hEq : (⟨m, hmN⟩ : ↥(Subgroup.normalizer (L : Set G))) * ⟨b, hbN⟩ *
        ⟨m, hmN⟩⁻¹ = ⟨b⁻¹, (Subgroup.normalizer (L : Set G)).inv_mem hbN⟩ := by
      ext
      show m * b * m⁻¹ = b⁻¹
      exact hmb
    have h := congrArg (inducedQuotInfAutHom L) hEq
    rw [map_mul, map_mul, map_inv] at h
    rw [show (⟨b⁻¹, (Subgroup.normalizer (L : Set G)).inv_mem hbN⟩ :
        ↥(Subgroup.normalizer (L : Set G))) = (⟨b, hbN⟩)⁻¹ from rfl,
      map_inv (inducedQuotInfAutHom L) (⟨b, hbN⟩ : ↥(Subgroup.normalizer (L : Set G)))] at h
    simpa [inducedQuotInfAut] using h
  exact false_of_conj_eq_inv N hr hr2 hθr hμ (hcommN _ _) hθN

theorem uc22r3g_not_inner {M L : Subgroup G} (hL : L ∈ calC M) (hZ : center (Bar2 L) = ⊥)
    {b : G} (hbL : b ∈ normalizer (L : Set G))
    (hninn : ¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 M) :
    inducedQuotInfAut L b hbL ∉
      (MulAut.conj : _ →* MulAut (BarInf L ⧸ center (BarInf L))).range := by
  rintro ⟨x, hx⟩
  obtain ⟨y, rfl⟩ := piBarInf_surjective L x
  refine hninn ⟨y, y.2, fun l hl => ?_⟩
  have h1 := DFunLike.congr_fun hx (piBarInf L ⟨l, hl⟩)
  rw [MulAut.conj_apply, inducedQuotInfAut_piBarInf, ← map_inv, ← map_mul, ← map_mul] at h1
  have h2 : (⟨b * l * b⁻¹, (mem_normalizer_iff.1 hbL l).1 hl⟩ : ↥L) * (y * ⟨l, hl⟩ * y⁻¹)⁻¹ ∈
      CFSG.pCore 2 ↥L := by
    rw [← solvableRadical_eq_pCore_of_center_bar2_eq_bot hL.2.2 hZ, ← piBarInf_ker hL.2.2,
      MonoidHom.mem_ker, map_mul, map_inv, mul_inv_eq_one]
    exact h1.symm
  exact uc22ine229_pCoreOf_le_of_isSubnormal hL.1 (Subgroup.mem_map.2 ⟨_, h2, rfl⟩)

theorem uc22r3g_false_of_uniqueSet {D : Data G} {Ch : Choice2011 G} (h1930 : H1930 D)
    (c : Ctx21 D Ch) {L K : Subgroup G} (hne : K ≠ L) (hset : conjSetOf D.M L = {L, K})
    (hcomm : ∀ α β : MulAut (BarInf L ⧸ center (BarInf L)),
      α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : _ →* MulAut (BarInf L ⧸ center (BarInf L))).range)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {b : G} (hb : b ∈ c.B0) (hbo : orderOf b = q)
    (hbT : b ∈ normalizer (D.T : Set G)) (hbL : b ∈ normalizer (L : Set G))
    (hθ : inducedQuotInfAut L b hbL ∉
      (MulAut.conj : _ →* MulAut (BarInf L ⧸ center (BarInf L))).range)
    {X : Subgroup G} (hXne : X ≠ ⊥) (hXp : ∃ r : ℕ, r.Prime ∧ IsPGroup r ↥X)
    (hXc : X ≤ centralizer ({b} : Set G)) (hXU : X ∈ uniqueSet D.M) : False := by
  have hbM : b ∈ D.M := c.hBM hb
  have hKm : K ∈ conjSetOf D.M L := by rw [hset]; simp
  have hc2K : (conjSetOf D.M K).ncard = 2 := by
    rw [uc22p2214_conjSetOf_eq hKm, hset, Set.ncard_pair hne.symm]
  have hbK : b ∈ normalizer (K : Set G) :=
    uc22p2214_mem_normalizer_of_odd hc2K hbM (hbo ▸ hq.odd_of_ne_two hq2)
  let c' : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hAne : zpowers b ≠ ⊥ := by
    rw [Ne, zpowers_eq_bot]
    rintro rfl
    rw [orderOf_one] at hbo
    exact hq.ne_one hbo.symm
  have hXn : X ≤ normalizer (zpowers b : Set G) := by
    have h1 : centralizer ({b} : Set G) = centralizer (zpowers b : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    exact (h1 ▸ hXc).trans (centralizer_le_normalizer _)
  obtain ⟨m, hmM, hm⟩ :=
    s21_10 D Ch h1930 c' (zpowers b) hAne (zpowers_le.2 hb) X hXne hXp hXn hXU
  have hmb : m * b * m⁻¹ = b⁻¹ := hm b (mem_zpowers b)
  obtain ⟨m', hm'N, hm'b⟩ : ∃ m' ∈ normalizer (L : Set G), m' * b * m'⁻¹ = b⁻¹ := by
    by_cases hmL : m ∈ normalizer (L : Set G)
    · exact ⟨m, hmL, hmb⟩
    have hLm : L.map (MulAut.conj m).toMonoidHom = K := by
      have h : L.map (MulAut.conj m).toMonoidHom ∈ conjSetOf D.M L := ⟨m, hmM, rfl⟩
      rw [hset] at h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      exact h.resolve_left fun h' => hmL (mem_normalizer_iff_map_conj_eq.2 h')
    have hKm' : K.map (MulAut.conj m).toMonoidHom = L := by
      have h : K.map (MulAut.conj m).toMonoidHom ∈ conjSetOf D.M K := ⟨m, hmM, rfl⟩
      rw [uc22p2214_conjSetOf_eq hKm, hset] at h
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h
      refine h.resolve_right fun h' => hne ?_
      exact Subgroup.map_injective (f := (MulAut.conj m).toMonoidHom) (MulAut.conj m).injective
        (h'.trans hLm.symm)
    obtain ⟨t, -, htL, htb⟩ := uc22r3g_exists_swap_commute hne hset hq hq2 hbo hbT hbL hbK
    refine ⟨m * t, mem_normalizer_iff_map_conj_eq.2 ?_, ?_⟩
    · show L.map (MulAut.conj (m * t)).toMonoidHom = L
      rw [← uc22p22d_map_conj_map_conj, htL, hKm']
    · calc m * t * b * (m * t)⁻¹ = m * (t * b * t⁻¹) * m⁻¹ := by group
        _ = b⁻¹ := by rw [← htb, mul_inv_cancel_right, hmb]
  exact false_of_inverted _ hbL hm'N hq hq2 hbo hθ hcomm hm'b

theorem uc22r3g_false_of_isL2 {D : Data G} {Ch : Choice2011 G} (h8107 : F08.R8107 D)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hL2 : IsL2 (Bar2 L) n) {q m : ℕ} {b : G}
    (hq : q.Prime) (hqn : ¬ q ∣ 2 ^ n - 1) (hm : Odd m) (hqm : q ∣ 2 ^ m - 1)
    (hb : b ∈ c.B0) (hbo : orderOf b = q) (hbT : b ∈ normalizer (D.T : Set G))
    (hbL : b ∈ normalizer (L : Set G))
    (hninn : ¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨K, hne, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have hq7 := PartTwo.s13_seven_le_of_dvd hm hq hqm
  have hq2 : q ≠ 2 := by omega
  have hqL := uc22r3g_not_dvd_card (Or.inl hL2) hq hq2 hqn hm hqm
  obtain ⟨a, haL, hao, hba⟩ := uc22r3g_exists_commute Nat.prime_three hq hbo hbL hqL
    (PartTwo.S17.three_dvd_card_of_bar_isL2Even hL2)
    (PartTwo.S17.pRank_three_eq_one_of_isL2 hL2).le (by omega)
  obtain ⟨e⟩ := u4x_bar2_equiv (M := D.M) (L := L) (K := K) (by rw [hset]; simp)
  have hK2 : IsL2 (Bar2 K) n := CFSG.Blueprint.LieModel.of_mulEquiv e hL2
  obtain ⟨g, hg⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥K) 3 (PartTwo.S17.three_dvd_card_of_bar_isL2Even hK2)
  have hXU : zpowers a ∈ uniqueSet D.M :=
    (h8107 L hL K hK hne.symm (PartTwo.S17.pRank_three_eq_one_of_isL2 hL2)
      (PartTwo.S17.pRank_three_eq_one_of_isL2 hK2) (Or.inl (PartTwo.S17.thin8_of_isL2 hL2))
      (Or.inl (PartTwo.S17.thin8_of_isL2 hK2)) (zpowers a) (zpowers (g : G)) (zpowers_le.2 haL)
      (by rw [Nat.card_zpowers, hao]) (zpowers_le.2 g.2)
      (by rw [Nat.card_zpowers, Subgroup.orderOf_coe, hg])).1
  have hZ := center_eq_bot_of_isL2 hL.2.2 hL2
  have hX : IsL2 (BarInf L ⧸ center (BarInf L)) n := lieModel_xbar_of_lieModel_bar2 hL.2.2 hZ hL2
  have hcomm : ∀ α β : MulAut (BarInf L ⧸ center (BarInf L)),
      α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : _ →* MulAut (BarInf L ⧸ center (BarInf L))).range := by
    intro α β
    obtain ⟨x, hx⟩ := CFSG.Quasithin.H13.KGLieOut.inner_of_outer_comm (uc22p22g_outer_comm hX) α β
    exact ⟨x, hx.symm⟩
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hao
    omega
  exact uc22r3g_false_of_uniqueSet h1930 c hne hset hcomm hq hq2 hb hbo hbT hbL
    (uc22r3g_not_inner hL hZ hbL hninn) (zpowers_ne_bot.2 ha1)
    ⟨3, Nat.prime_three, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hao, pow_one])⟩
    (zpowers_le.2 (mem_centralizer_singleton_iff.2 hba.symm)) hXU

@[expose] def S21_22R3F3Sz (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ H₁ ∈ hSet D.T D.M, ∀ H₂ ∈ hSet D.T D.M, c.L0 ≤ H₁ ⊓ H₂ →
    (∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G)) →
    ⁅Hinf D.M, oTwoFOf D.M⁆ ≤ CFSG.Open.pCoreOf 2 D.M →
    (∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0) →
    D.sig = D.sig1 → CFSG.Open.evenRank G = 3 →
    ∀ L ∈ calC D.M, (conjSetOf D.M L).ncard = 2 → ∀ n : ℕ, 2 < n → IsSz (Bar2 L) n →
      ∀ (q : ℕ) (b : G), q.Prime → q ∣ n → ¬ q ∣ 2 ^ n - 1 →
        (∃ e m : ℕ, Odd m ∧ c.n = 2 ^ e * m ∧ q ∣ 2 ^ m - 1) →
        b ∈ c.B0 → orderOf b = q → b ∈ normalizer (D.T : Set G) →
        b ∈ normalizer (L : Set G) →
        (¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) → False

theorem s21_22R3F3_of_sz {D : Data G} {Ch : Choice2011 G} (h8107 : F08.R8107 D)
    (hSz : S21_22R3F3Sz D Ch) : S21_22R3F3 D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he L hL hc2 n hn hS q b hq hqd hqn hm hb hbo
    hbT hbL hninn
  rcases hS with hL2 | hSz'
  · obtain ⟨-, m, hmo, -, hqm⟩ := hm
    exact uc22r3g_false_of_isL2 h8107 h1930 c hL hc2 hL2 hq hqn hmo hqm hb hbo hbT hbL hninn
  · exact hSz h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 hs he L hL hc2 n hn hSz' q b hq hqd hqn hm
      hb hbo hbT hbL hninn

end CFSG.LocalAnalysis.UniquenessCase.UC22

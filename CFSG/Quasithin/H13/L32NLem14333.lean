module

public import CFSG.Quasithin.H13.L32NLem14333d
public import CFSG.Quasithin.H13.L32NItems143c

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint L14332 CFSG.LieType.BorelTits

theorem two_pow_eq_of_mul_odd {m n i j : ℕ} (hi : Odd i) (hj : Odd j)
    (h : 2 ^ m * i = 2 ^ n * j) : m = n := by
  have key : ∀ {m n i j : ℕ}, Odd i → 2 ^ m * i = 2 ^ n * j → m < n → False := by
    intro m n i j hi h hmn
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_lt hmn
    have h2 : i = 2 * (2 ^ k * j) := by
      have : 2 ^ m * i = 2 ^ m * (2 * (2 ^ k * j)) := by rw [h]; ring
      exact Nat.eq_of_mul_eq_mul_left (by positivity) this
    rw [h2] at hi
    exact Nat.not_even_iff_odd.mpr hi (even_two_mul _)
  rcases lt_trichotomy m n with hmn | hmn | hmn
  · exact (key hi h hmn).elim
  · exact hmn
  · exact (key hj h.symm hmn).elim

namespace L14333

variable {G : Type} [Group G] [Finite G]

namespace Ctx

variable {T L V V₂ K : Subgroup G} {g a z b d x : G} {D : HatModelU (fsuU T V)}
  (c : Ctx G T L V V₂ K g a z b d x D)
include c

theorem fsuU_eq_pCoreOf_of_le (hyp : AlmostSpecialL3Hyp 1 V (fsuV1 T V) L T (l32nH T V))
    (hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V)) (hTL : T ≤ L) :
    fsuU T V = pCoreOf 2 (l32nH T V) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨_, S⟩ := c.setting
  obtain ⟨-, hPcard⟩ := c.pCoreOf_eq hyp
  have hT2 := c.ctx.T2
  obtain ⟨m, hm⟩ := hT2.exists_card_eq
  have hTG := c.ctx.hyp.fsu.sylow
  have hoddL : Odd (T.relIndex L) := by
    have h := Subgroup.relIndex_mul_index hTL
    have hodd : Odd T.index := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hTG.2)
    rw [← h] at hodd
    exact Nat.Odd.of_mul_left hodd
  have hL := Subgroup.relIndex_mul_card T L
  rw [inf_eq_left.mpr hTL, S.card_L, hPcard, hm] at hL
  have hm9 : m = 9 := by
    have h' : 2 ^ m * T.relIndex L = 2 ^ 9 * 21 :=
      calc 2 ^ m * T.relIndex L = T.relIndex L * 2 ^ m := mul_comm _ _
        _ = 168 * 64 := hL
        _ = 2 ^ 9 * 21 := by norm_num
    exact two_pow_eq_of_mul_odd hoddL (by decide) h'
  obtain ⟨q, hq⟩ := (pCoreOf_isPGroup 2 (l32nH T V)).exists_card_eq
  have hH : Nat.card ↥(l32nH T V) = Nat.card ↥(pCoreOf 2 (l32nH T V)) * 120 := by
    have h := Subgroup.card_ker_mul_card_range (imgHom D)
    rw [imgHom_ker, ← c.q_eq, MonoidHom.range_eq_top.mpr (imgHom_surjective D), Subgroup.card_top,
      card_img_l32nH c.ii] at h
    rw [← h, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (pCoreOf_le 2 _)).toEquiv]
  have hoddH : Odd (T.relIndex (l32nH T V)) := Nat.odd_iff.mpr (Nat.two_dvd_ne_zero.mp hTS.2.2)
  have hHT := Subgroup.relIndex_mul_card T (l32nH T V)
  rw [inf_eq_left.mpr hTS.1, hm, hm9, hH, hq] at hHT
  have hq6 : q + 3 = 9 := by
    have h' : 2 ^ (q + 3) * 15 = 2 ^ 9 * T.relIndex (l32nH T V) :=
      calc 2 ^ (q + 3) * 15 = 2 ^ q * 120 := by rw [pow_add]; ring
        _ = T.relIndex (l32nH T V) * 2 ^ 9 := hHT.symm
        _ = 2 ^ 9 * T.relIndex (l32nH T V) := mul_comm _ _
    exact two_pow_eq_of_mul_odd (by decide) hoddH h'
  have hQ64 : Nat.card ↥(pCoreOf 2 (l32nH T V)) = 64 := by
    rw [hq, show q = 6 by omega]
    norm_num
  exact Subgroup.eq_of_le_of_card_ge (fsuU_le_pCoreOf c.ctx) (by rw [hQ64, c.card_U])

end Ctx

end L14333

open L14333 in
theorem lemma14333_of_inputs (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h1222 : Stmt12_2_2)
    (h12213 : Stmt12_2_13) (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h1288 : Lemma12_8_8_two) (h12884 : Lemma12_8_8_four) (h12810 : Lemma12_8_10)
    (h12811 : Lemma12_8_11) (h12811h : Lemma12_8_11_hat) (h12812 : Lemma12_8_12_two)
    (h12813 : Lemma12_8_13) (h14323 : Lemma14323Rest) (h14324 : Lemma14324One)
    (h14331 : Lemma14331One) (h14333 : Lemma14333MEqL) (hKG22 : KGG22PointStab)
    (hKGr : KGG22Rank) (hKGq : KGSp4Quad) (hKGl : KGSp4Line) (hKGL24 : KGL24Quad) :
    Lemma14333 := by
  intro G _ _ T L V h hlt
  obtain ⟨V₂, K, g, a, z, b, d, x, D, c⟩ := exists_ctx h1332 h1334 h1222 h12213 h37 h38 h39
    h1288 h12810 h12811 h12811h h12812 h12813 h14323 h14324 h14331 hKG22 hKGr hKGq
    hKGl hKGL24 h hlt
  have hyp := (h12884 G T L V 3 (fsuV1 T V) V₂ c.ctx.setting le_rfl).2
  have hK := c.eq_oTwoUpper
  have hTS : QuasithinUnique.IsSylowTwoOf T (l32nH T V) :=
    h.isSylowTwoOf_l32nH (stmtL32NModule_of_inputs h1332 h1334)
  have hM := h14333 G T L V h hlt
  have hTL : T ≤ L := hM ▸ c.T_le_normL
  exact ⟨(c.pCoreOf_eq hyp).1, c.isZ4Cube hyp, c.isXSectionIso₂ hyp,
    by rw [← hK, c.pCoreOf_K_eq hyp], hK ▸ c.isSylowTwoOf_PU hyp, hM,
    (C1Pack12.oTwoUpper_sup_eq_of_sylow hTS).symm, c.fsuU_eq_pCoreOf_of_le hyp hTS hTL⟩

end CFSG.Quasithin.H13

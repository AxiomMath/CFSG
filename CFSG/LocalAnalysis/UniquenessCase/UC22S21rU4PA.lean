module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3PA
import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem u4p_normalizer_le {D : Data G} (h869 : F08.R869NS5 D) {L : Subgroup G}
    (hL : L ∈ calC D.M)
    (hpX : ∃ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p (conjClosure D.M L) ∧
      (p = 5 → 2 ^ 12 ∣ Nat.card (Bar2 (conjClosure D.M L))))
    {w : G} (hwM : w ∈ D.M) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hwo : orderOf w = q)
    (hw : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨w, hwM⟩ ∈
      centralizer ((barImage D.M (conjClosure D.M L) : Subgroup (Bar2 D.M)) : Set (Bar2 D.M))) :
    normalizer (zpowers w : Set G) ≤ D.M := by
  obtain ⟨hXM, hMX, hprod⟩ := uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hL
  have hcard : Nat.card (zpowers w) = q := by rw [Nat.card_zpowers, hwo]
  refine h869 (conjClosure D.M L) hXM hMX hprod hpX q hq hq2 (zpowers w) (zpowers_le.2 hwM)
    hcard (uc22p21d_sup_pCore_eq hq hq2 hcard fun a ha => ?_)
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 ha
  refine u4x_centralizesBar hXM hMX (D.M.zpow_mem hwM k) ?_
  have he : (⟨w ^ k, D.M.zpow_mem hwM k⟩ : ↥D.M) = ⟨w, hwM⟩ ^ k := Subtype.ext (by simp)
  rw [he, map_zpow]
  exact Subgroup.zpow_mem _ hw k

theorem u4p_not_mem_centralizer {D : Data G} {Ch : Choice2011 G} (h869 : F08.R869NS5 D)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hpX : ∃ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p (conjClosure D.M L) ∧
      (p = 5 → 2 ^ 12 ∣ Nat.card (Bar2 (conjClosure D.M L))))
    {b : G} (hb : b ∈ c.B0) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) (hbo : orderOf b = q) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, c.hBM hb⟩ ∉
      centralizer ((barImage D.M (conjClosure D.M L) : Subgroup (Bar2 D.M)) : Set (Bar2 D.M)) :=
  fun hw => u4x_false_of_normalizer_le h1930 c hb
    (u4p_normalizer_le h869 hL hpX (c.hBM hb) hq hq2 hbo hw)

structure U4P (D : Data G) (L K : Subgroup G) (n p : ℕ) : Prop where
  hL : L ∈ calC D.M
  hK : K ∈ calC D.M
  hne : K ≠ L
  hset : conjSetOf D.M L = {L, K}
  hc2 : (conjSetOf D.M L).ncard = 2
  hL2 : IsL2 (Bar2 L) n
  hσ : p ∈ D.sig
  hk : ∃ k, 0 < k ∧ n = 2 ^ k * p
  hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]

namespace U4P

variable {D : Data G} {L K : Subgroup G} {n p : ℕ}

theorem toR3Pair (u : U4P D L K n p) : R3Pair D L K n p := by
  obtain ⟨k, hk, hn⟩ := u.hk
  exact R3Pair.of_two_pow_mul u.hL u.hK u.hne u.hset u.hc2 u.hL2 u.hσ hk hn u.hcong

theorem mem_K (u : U4P D L K n p) : K ∈ conjSetOf D.M L := by rw [u.hset]; simp

theorem shape (u : U4P D L K n p) : IsL2 (Bar2 L) n ∨ IsSz (Bar2 L) n := Or.inl u.hL2

theorem pX (u : U4P D L K n p) : ∃ q ∈ D.sig, 2 ≤ CFSG.Open.pRank q (conjClosure D.M L) ∧
    (q = 5 → 2 ^ 12 ∣ Nat.card (Bar2 (conjClosure D.M L))) :=
  u.toR3Pair.pX

theorem dvd_card_of_dvd (u : U4P D L K n p) {q : ℕ} (hq : q ∣ 2 ^ n - 1) : q ∣ Nat.card L :=
  u.toR3Pair.dvd_card_of_dvd hq

theorem symm (u : U4P D L K n p) : U4P D K L n p where
  hL := u.hK
  hK := u.hL
  hne := u.hne.symm
  hset := u.toR3Pair.symm.hset
  hc2 := u.toR3Pair.symm.hc2
  hL2 := by
    obtain ⟨e⟩ := u4x_bar2_equiv u.mem_K
    exact CFSG.Blueprint.LieModel.of_mulEquiv e u.hL2
  hσ := u.hσ
  hk := u.hk
  hcong := u.hcong

theorem conj_cases (u : U4P D L K n p) {t : G} (ht : t ∈ D.M) :
    (t ∈ normalizer (L : Set G) ∧ t ∈ normalizer (K : Set G)) ∨
      (L.map (MulAut.conj t).toMonoidHom = K ∧ K.map (MulAut.conj t).toMonoidHom = L) :=
  u.toR3Pair.conj_cases ht

end U4P

end CFSG.LocalAnalysis.UniquenessCase.UC22

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3L
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100U2
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3F3A
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4Exc
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Nb
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Facts13
import CFSG.Blueprint.LieModelAPI
import CFSG.GroupTheory.CoprimeFixedPointOrder
import CFSG.RankThree.PartOne.KE.SuzukiFinal
import CFSG.RankThree.PartTwo.KFacts.KS44OutSz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem uc22r3g_comm_of_isSz {M L : Subgroup G} (hL : L ∈ calC M)
    {n : ℕ} (hSz : IsSz (Bar2 L) n) (α β : MulAut (BarInf L ⧸ center (BarInf L))) :
    α * β * α⁻¹ * β⁻¹ ∈ (MulAut.conj : _ →* MulAut (BarInf L ⧸ center (BarInf L))).range := by
  have hX := lieModel_xbar_of_lieModel_bar2 hL.2.2 (center_eq_bot_of_isSz hL.2.2 hSz) hSz
  rw [← commutatorElement_def]
  exact CFSG.RankThree.PartTwo.KFacts.commutator_le_inner_of_suzukiModel
    (CFSG.Blueprint.LieModel.twistedB2_iff.1 hX).2
    (Subgroup.commutator_mem_commutator (Subgroup.mem_top α) (Subgroup.mem_top β))

theorem uc22r3g_exists_fixed_sz {M L : Subgroup G}
    (hL : L ∈ calC M) {n : ℕ} (hSz : IsSz (Bar2 L) n) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hqL : ¬ q ∣ Nat.card L) (hnq : n ≠ q) {b : G} (hbo : orderOf b = q)
    (hbL : b ∈ normalizer (L : Set G))
    (hθ : inducedQuotInfAut L b hbL ∉
      (MulAut.conj : _ →* MulAut (BarInf L ⧸ center (BarInf L))).range) :
    ∃ s r : ℕ, Odd s ∧ s ∣ n ∧ r.Prime ∧ r ∣ 2 ^ s - 1 ∧
      ∃ y ∈ L, orderOf y = r ∧ b * y = y * b := by
  classical
  have hq' : CFSG.Open.IsQuasisimple (Bar2 L) := hL.2.2
  obtain ⟨-, a, ha, K, _, _, hf, hKc, ⟨φ⟩⟩ := (CFSG.Blueprint.LieModel.twistedB2_iff.1
    (lieModel_xbar_of_lieModel_bar2 hq' (center_eq_bot_of_isSz hq' hSz) hSz)).2
  haveI : Finite (CFSG.Blueprint.suzukiGroup a K) := Finite.of_equiv _ φ.toEquiv
  have hθo : orderOf (inducedQuotInfAut L b hbL) = q := by
    have hd : orderOf (inducedQuotInfAut L b hbL) ∣ q := by
      rw [← hbo]
      exact orderOf_inducedQuotInfAut_dvd L hbL
    rcases (Nat.dvd_prime hq).1 hd with h | h
    · exact (hθ ⟨1, by rw [map_one, orderOf_eq_one_iff.1 h]⟩).elim
    · exact h
  obtain ⟨α, hα⟩ : ∃ α, α = MulAut.congr φ (inducedQuotInfAut L b hbL) := ⟨_, rfl⟩
  have hαo : orderOf α = q := by rw [hα, MulEquiv.orderOf_eq, hθo]
  have hαi : α ∉ CFSG.ComponentClassification.OuterAutomorphisms.inner
      (CFSG.Blueprint.suzukiGroup a K) := by
    rintro ⟨g, hg⟩
    refine hθ ⟨φ.symm g, (MulAut.congr φ).injective ?_⟩
    rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj, MulEquiv.apply_symm_apply,
      hg, hα]
  obtain ⟨σ, h, b', k, _, _, -, hb'q, hk, hconj, ⟨eF⟩⟩ :=
    CFSG.RankThree.PartOne.KE.suzukiPrimeFieldCosetDescent a ha K (by rw [← hf]; exact hKc) q
      hq hq2 α hαo hαi
  have hn : n = (2 * b' + 1) * q := hf.trans hb'q.symm
  have hb'1 : 1 ≤ b' := by
    refine Nat.one_le_iff_ne_zero.2 fun h0 => hnq ?_
    rw [hn, h0, mul_zero, zero_add, one_mul]
  have h4 : 4 ≤ 2 ^ (2 * b' + 1) :=
    le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num : 0 < 2) (by omega : 2 ≤ 2 * b' + 1))
  obtain ⟨r, hr, hrs⟩ := Nat.exists_prime_and_dvd (show 2 ^ (2 * b' + 1) - 1 ≠ 1 by omega)
  haveI : Fact r.Prime := ⟨hr⟩
  have hSzk : IsSz (CFSG.Blueprint.suzukiGroup b' k) (2 * b' + 1) :=
    CFSG.Blueprint.LieModel.twistedB2_iff.2
      ⟨rfl, rfl, b', hb'1, k, inferInstance, inferInstance, rfl, hk, ⟨MulEquiv.refl _⟩⟩
  haveI : Finite (CFSG.Blueprint.suzukiGroup b' k) := Finite.of_equiv _ eF.toEquiv
  obtain ⟨z₀, hz₀⟩ :=
    exists_prime_orderOf_dvd_card' r (hrs.trans (uc22ine229_dvd_card_of_isSz hSzk))
  obtain ⟨z, hzfix, hzo⟩ : ∃ z : CFSG.Blueprint.suzukiGroup a K,
      CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K σ z = z ∧ orderOf z = r :=
    ⟨eF.symm z₀, (eF.symm z₀).2, by rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hz₀]⟩
  obtain ⟨w, hw⟩ : ∃ w, w = (MulAut.conj h)⁻¹ z := ⟨_, rfl⟩
  have hwo : orderOf w = r := by rw [hw, MulEquiv.orderOf_eq, hzo]
  have hαw : α w = w := by
    have hα' : α = (MulAut.conj h)⁻¹ *
        (CFSG.SignalizerFunctorTheorem.NearModels.Suzuki.szFieldAut a K σ * MulAut.conj h) := by
      rw [← hconj]
      group
    rw [hw, hα', MulAut.mul_apply, MulAut.mul_apply, MulAut.apply_inv_self, hzfix]
  have hxfix : inducedQuotInfAut L b hbL (φ.symm w) = φ.symm w := by
    apply φ.injective
    calc φ (inducedQuotInfAut L b hbL (φ.symm w)) = α w := by subst hα; rfl
      _ = w := hαw
      _ = φ (φ.symm w) := (φ.apply_symm_apply w).symm
  have hxo : orderOf (φ.symm w) = r := by rw [MulEquiv.orderOf_eq, hwo]
  let ρ : MulAut ↥L := Subgroup.normalizerMonoidHom L ⟨b, hbL⟩
  have hρl : ∀ l : ↥L, ((ρ l : ↥L) : G) = b * (l : G) * b⁻¹ := fun l =>
    Subgroup.normalizerMonoidHom_apply_apply_coe L ⟨b, hbL⟩ l
  have hcomm : ∀ l : ↥L, piBarInf L (ρ l) = inducedQuotInfAut L b hbL (piBarInf L l) := by
    intro l
    rw [inducedQuotInfAut_piBarInf]
    exact congrArg (piBarInf L) (Subtype.ext (hρl l))
  have hρ : orderOf ρ ∣ q := by
    have h1 := orderOf_map_dvd (Subgroup.normalizerMonoidHom L) ⟨b, hbL⟩
    rwa [Subgroup.orderOf_mk, hbo] at h1
  have hcop : ¬ q ∣ Nat.card (piBarInf L).ker := by
    rw [piBarInf_ker hq']
    exact fun hd => hqL (hd.trans (Subgroup.card_subgroup_dvd_card _))
  obtain ⟨y, hyo, hyfix⟩ := CFSG.GroupTheory.exists_orderOf_eq_fixed_of_coprime_ker (piBarInf L)
    (piBarInf_surjective L) ρ (inducedQuotInfAut L b hbL) hcomm hq hρ hcop hxo hxfix
  have hby : b * (y : G) * b⁻¹ = y := (hρl y).symm.trans (congrArg Subtype.val hyfix)
  refine ⟨2 * b' + 1, r, ⟨b', rfl⟩, ⟨q, hn⟩, hr, hrs, (y : G), y.2,
    by rw [Subgroup.orderOf_coe, hyo], ?_⟩
  calc b * (y : G) = b * y * b⁻¹ * b := by group
    _ = y * b := by rw [hby]

theorem uc22r3g_false_of_ne {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h15 : S21_15C D Ch) (hU2 : R8100U2 D) (h1930 : H1930 D)
    (c : Ctx21 D Ch) (he : CFSG.Open.evenRank G = 3) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hSz : IsSz (Bar2 L) n) {q m : ℕ} {b : G}
    (hq : q.Prime) (hqn : ¬ q ∣ 2 ^ n - 1) (hm : Odd m) (hqm : q ∣ 2 ^ m - 1) (hnq : n ≠ q)
    (hb : b ∈ c.B0) (hbo : orderOf b = q) (hbT : b ∈ normalizer (D.T : Set G))
    (hbL : b ∈ normalizer (L : Set G))
    (hninn : ¬ ∃ y ∈ L, ∀ x ∈ L, b * x * b⁻¹ * (y * x * y⁻¹)⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M) :
    False := by
  obtain ⟨K, hne, hset, -⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have hq7 := PartTwo.s13_seven_le_of_dvd hm hq hqm
  have hq2 : q ≠ 2 := by omega
  have hθ := uc22r3g_not_inner hL (center_eq_bot_of_isSz hL.2.2 hSz) hbL hninn
  obtain ⟨s, r, hs, hsn, hr, hrs, y, hyL, hyo, hyb⟩ := uc22r3g_exists_fixed_sz hL hSz hq hq2
    (uc22r3g_not_dvd_card (Or.inr hSz) hq hq2 hqn hm hqm) hnq hbo hbL hθ
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hXU : zpowers y ∈ uniqueSet D.M :=
    hU2 he L n s r p hL hc2 (h15 h1930 c L hL hc2 n (Or.inl hSz) p hp) hs hsn hr hrs hp
      (zpowers y) (zpowers_le.2 hyL) (by rw [Nat.card_zpowers, hyo])
  have hy1 : y ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hyo
    exact hr.one_lt.ne hyo
  exact uc22r3g_false_of_uniqueSet h1930 c hne hset (uc22r3g_comm_of_isSz hL hSz) hq hq2 hb hbo
    hbT hbL hθ (zpowers_ne_bot.2 hy1)
    ⟨r, hr, IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])⟩
    (zpowers_le.2 (mem_centralizer_singleton_iff.2 hyb.symm)) hXU

end CFSG.LocalAnalysis.UniquenessCase.UC22

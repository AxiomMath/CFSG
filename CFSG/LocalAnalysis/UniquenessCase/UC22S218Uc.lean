module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218U
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213TDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section19.NineteenTwentyFive72
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Ua
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Ub
import CFSG.LocalAnalysis.UniquenessCase.UC22S218P
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC7R71Three
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SigmaRankThree13
import CFSG.LocalAnalysis.UniquenessCase.UC22S217Sp4
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.UniqueSetOfCentralizer
import CFSG.GH74.Uniqueness.SU.SU1Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL_fix_iff rhoL_inner)

variable {G : Type} [Group G] [Finite G]

theorem uc22s218u_seven_le {n r : ℕ} (hn : Odd n) (hr : r.Prime) (hrn : r ∣ 2 ^ n - 1) : 7 ≤ r := by
  obtain ⟨k, rfl⟩ := hn
  have e : 2 ^ (2 * k + 1) = 2 * 4 ^ k := by
    rw [pow_succ, pow_mul, mul_comm]
    norm_num
  have h3 : 4 ^ k % 3 = 1 := by
    rw [Nat.pow_mod]
    norm_num
  have h5 : 4 ^ k % 5 = 1 ∨ 4 ^ k % 5 = 4 := by
    rcases Nat.even_or_odd k with ⟨j, rfl⟩ | ⟨j, rfl⟩
    · left
      rw [← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    · right
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
  have hpos : 1 ≤ 4 ^ k := Nat.one_le_pow _ _ (by norm_num)
  rw [e] at hrn
  by_contra h
  have hr2 := hr.two_le
  interval_cases r
  · omega
  · omega
  · norm_num at hr
  · omega
  · norm_num at hr

theorem uc22s218u_mem_normalizer_inf {A B : Subgroup G} {g : G} (hA : g ∈ normalizer (A : Set G))
    (hB : g ∈ normalizer (B : Set G)) : g ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro h
  rw [mem_inf, mem_inf, hA h, hB h]

theorem s21_8U_of_r72 {D : Data G} {Ch : Choice2011 G} (he : CFSG.Open.evenRank G = 3)
    (hSg : UC6S846.SigmaStd D) (h211 : S21_1 D Ch) (hP : S21_8P D Ch) (h71 : F07.R71 D) (h72 : F07.R72 D)
    (hKf : PartTwo.S19.K_19_25_noL2SzSection)
    (hσ : ∀ r : ℕ, r.Prime → 7 ≤ r → 3 ≤ CFSG.Open.pRank r D.M → r ∈ D.sig) : S21_8U D Ch := by
  classical
  intro hH c L hL n hn hX
  have hLM : L ≤ D.M := hL.1.le
  have hML : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 (s21_normalSp4_of D Ch hSg h211 hH c L hL n hn hX)
  have hn3 : 3 ≤ n := uc22p218d_three_le_of_odd hX hn
  have hns := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  haveI : Fact p.Prime := ⟨hp⟩
  have hsp : IsStronglyPEmbedded p D.M := UC6S846.sp_of_mem_sig hSg hns hpσ
  have hpn : p ∣ 2 ^ n + 1 := by
    have h1 := (hP he hH c L hL n hn hX p hpσ).dvd
    have h2 : ((2 ^ n + 1 : ℕ) : ℤ) = -(-1 - 2 ^ n) := by
      push_cast
      ring
    exact Int.natCast_dvd_natCast.1 (by rw [h2]; exact dvd_neg.2 h1)
  have h8 : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn3
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd (show 2 ^ n - 1 ≠ 1 by omega)
  haveI : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := uc22p218c_ne_two_of_dvd (by omega) hrn
  have hrM : CFSG.Open.pRank r D.M ≤ 2 := by
    by_contra h
    exact uc22p218s_not_stronglyEmbedded D Ch h211 hH c hLM hML hX hn hr hr2 hrn
      (UC6S846.sp_of_mem_sig hSg hns (hσ r hr (uc22s218u_seven_le hn hr hrn) (by omega)))
  have hrL : CFSG.Open.pRank r L = 2 := uc22p218c_pRank_eq_two_of_bar2 hX hr hrn
  have hO : IsPGroup 2 (pCoreOf 2 L) := UC6S846.isPGroup_pCoreOf L
  have hOL : pCoreOf 2 L ≤ L := map_subtype_le _
  have hLO : L ≤ normalizer (pCoreOf 2 L : Set G) :=
    le_normalizer.trans (UC6S846.normalizer_le_normalizer_pCoreOf L)
  obtain ⟨y, hyM, hyo, hyL⟩ :=
    uc22s218u_exists_trivial_action D Ch h211 hH c hML hX hp hp2 hsp (hSg.three_le p hpσ)
  have hyp : IsPGroup p (zpowers y) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hyo, pow_one])
  obtain ⟨Q, hQ⟩ := D.sylowM.inf_of_le_normalizer hLM hML
  obtain ⟨x, hxL, hxS, hxo, hsec, hcard⟩ := uc22s218u_exists_lift hX (by omega) Q hr hrn
  rw [hQ] at hxS
  set X : Subgroup G := zpowers x with hXdef
  have hxp : IsPGroup r X := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hxo, pow_one])
  have hXM : X ≤ D.M := zpowers_le.2 (hLM hxL)
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [zpowers_eq_bot.1 h, orderOf_one] at hxo
    exact hr.one_lt.ne hxo
  obtain ⟨w, hwL, hwC⟩ :=
    uc22s218u_exists_conj_commute hp hp2 hr hr2 hO hOL hLO hxp (zpowers_le.2 hxL) hyp (hML hyM) hyL
  set y' : G := w⁻¹ * y * w with hy'
  have hy'M : y' ∈ D.M := mul_mem (mul_mem (inv_mem (hLM hwL)) hyM) (hLM hwL)
  have hy'o : orderOf y' = p := by
    have h1 : orderOf (MulAut.conj w⁻¹ y) = p := by rw [MulEquiv.orderOf_eq, hyo]
    rw [MulAut.conj_apply, inv_inv] at h1
    exact h1
  have hy'L : ∀ l ∈ L, y' * l * y'⁻¹ * l⁻¹ ∈ pCoreOf 2 L := by
    intro l hl
    have h1 := hyL _ (mul_mem (mul_mem hwL hl) (inv_mem hwL))
    have h2 := (mem_normalizer_iff.1 (hLO (inv_mem hwL)) _).1 h1
    have e : y' * l * y'⁻¹ * l⁻¹ =
        w⁻¹ * (y * (w * l * w⁻¹) * y⁻¹ * (w * l * w⁻¹)⁻¹) * w⁻¹⁻¹ := by
      rw [hy']
      group
    rw [e]
    exact h2
  have hy'nL : y' ∉ L := by
    intro hy'L0
    have hz : (QuotientGroup.mk (⟨y', hy'L0⟩ : ↥L) : Bar2 L) ∈ center (Bar2 L) := by
      rw [mem_center_iff]
      intro g
      obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective g
      have h1 := (rhoL_fix_iff L ⟨y', le_normalizer hy'L0⟩ l).2 (hy'L l l.2)
      rw [rhoL_inner L y' hy'L0, MulAut.conj_apply] at h1
      calc (QuotientGroup.mk l : Bar2 L) * QuotientGroup.mk ⟨y', hy'L0⟩
          = QuotientGroup.mk ⟨y', hy'L0⟩ * QuotientGroup.mk l * (QuotientGroup.mk ⟨y', hy'L0⟩)⁻¹ *
            QuotientGroup.mk ⟨y', hy'L0⟩ := by rw [h1]
        _ = QuotientGroup.mk ⟨y', hy'L0⟩ * QuotientGroup.mk l := by group
    rw [uc22p218d_center_eq_bot_sp4 hX, mem_bot, QuotientGroup.eq_one_iff] at hz
    obtain ⟨k, hk⟩ := CFSG.pCore_isPGroup (p := 2) (G := ↥L) ⟨_, hz⟩
    have h2 : y' ^ 2 ^ k = 1 := by
      have h := congrArg Subtype.val (congrArg Subtype.val hk)
      simpa using h
    have h3 : p ∣ 2 ^ k := by
      rw [← hy'o]
      exact orderOf_dvd_of_pow_eq_one h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3))
  have hpY : p ∣ 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    refine dvd_mul_of_dvd_right (hpn.trans ⟨2 ^ n - 1, ?_⟩) _
    obtain ⟨k, hk⟩ : ∃ k, 2 ^ n = k + 1 := ⟨2 ^ n - 1, by omega⟩
    rw [hk, Nat.add_sub_cancel]
    exact Nat.sub_eq_of_eq_add (by ring)
  obtain ⟨z, hzLC, hzo⟩ := hcard p hp hpY
  have hzp : IsPGroup p (zpowers z) := IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hzo, pow_one])
  obtain ⟨w', hw'L, hw'C⟩ := uc22s218u_exists_conj_commute (L := L ⊓ centralizer (X : Set G))
    (O := pCoreOf 2 L ⊓ centralizer (X : Set G)) hp hp2 hp hp2 (hO.to_le inf_le_left)
    (inf_le_inf_right _ hOL)
    (fun l hl => uc22s218u_mem_normalizer_inf (hLO (mem_inf.1 hl).1) (le_normalizer (mem_inf.1 hl).2))
    hzp (zpowers_le.2 hzLC) (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy'o, pow_one]))
    (uc22s218u_mem_normalizer_inf (hML hy'M) (le_normalizer hwC))
    (fun l hl => mem_inf.2 ⟨hy'L l (mem_inf.1 hl).1,
      mul_mem (mul_mem (mul_mem hwC (mem_inf.1 hl).2) (inv_mem hwC)) (inv_mem (mem_inf.1 hl).2)⟩)
  set z₁ : G := w' * z * w'⁻¹ with hz₁
  have hz₁LC : z₁ ∈ L ⊓ centralizer (X : Set G) := mul_mem (mul_mem hw'L hzLC) (inv_mem hw'L)
  have hz₁o : orderOf z₁ = p := by
    have h1 : orderOf (MulAut.conj w' z) = p := by rw [MulEquiv.orderOf_eq, hzo]
    rw [MulAut.conj_apply] at h1
    exact h1
  have hz₁y' : z₁ * y' = y' * z₁ := by
    have h1 := mem_centralizer_iff.1 hw'C z (mem_zpowers z)
    calc z₁ * y' = w' * (z * (w'⁻¹ * y' * w')) * w'⁻¹ := by rw [hz₁]; group
      _ = w' * ((w'⁻¹ * y' * w') * z) * w'⁻¹ := by rw [h1]
      _ = y' * z₁ := by rw [hz₁]; group
  have hz₁1 : z₁ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hz₁o
    exact hp.one_lt.ne hz₁o
  obtain ⟨hEel, hEc⟩ := CFSG.GH74.Uniqueness.SU.SU1.isElemAbelian_card_sup_zpowers hp
    (by rw [← hz₁o]; exact pow_orderOf_eq_one z₁) (by rw [← hy'o]; exact pow_orderOf_eq_one y') hz₁1
    (fun h => hy'nL (zpowers_le.2 (mem_inf.1 hz₁LC).1 h)) hz₁y'
  have hEN : zpowers z₁ ⊔ zpowers y' ≤ normalizer (X : Set G) ⊓ D.M :=
    sup_le (zpowers_le.2 (mem_inf.2 ⟨centralizer_le_normalizer _ (mem_inf.1 hz₁LC).2, hLM (mem_inf.1 hz₁LC).1⟩))
      (zpowers_le.2 (mem_inf.2 ⟨centralizer_le_normalizer _ hwC, hy'M⟩))
  have hrank : 1 < CFSG.Open.pRank p (normalizer (X : Set G) ⊓ D.M) := by
    have := UC6S846.le_pRank' hp hEN hEel hEc
    omega
  have hNX : normalizer (X : Set G) ≤ D.M :=
    uc22s218u_normalizer_le D hp hp2 hsp h71 h72 hKf hXM hX1 hrank hn3
      (PartTwo.S19.hasL2SzSection_of_le hsec
        (le_inf (inf_le_right.trans (centralizer_le_normalizer _)) (inf_le_left.trans hLM)))
  have hE : ∀ E : Subgroup G, E ≤ D.M → IsElemAbelian r E → Nat.card E = r ^ 2 →
      p ∣ Nat.card (D.M ⊓ centralizer (E : Set G) : Subgroup G) := by
    intro E hEM hEel hEc
    obtain ⟨R, hR, hER⟩ := UC6.exists_isSylowOf_ge hEM hEel.isPGroup
    obtain ⟨E₀, hE₀L, hE₀el, hE₀c⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hr hrL.ge
    obtain ⟨R₀, hR₀, hE₀R₀⟩ := UC6.exists_isSylowOf_ge (hE₀L.trans hLM) hE₀el.isPGroup
    obtain ⟨k, hkM, hk⟩ := hR₀.exists_mem_conj hR
    have hE₁R : E₀.map (MulAut.conj k).toMonoidHom ≤ R := by
      rintro _ ⟨e, he, rfl⟩
      rw [hk, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, show k⁻¹ * (k * e * k⁻¹) * k = e by group]
      exact hE₀R₀ he
    have hE₁L : E₀.map (MulAut.conj k).toMonoidHom ≤ L := by
      rintro _ ⟨e, he, rfl⟩
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact (mem_normalizer_iff.1 (hML hkM) e).1 (hE₀L he)
    have hE₁el : IsElemAbelian r (E₀.map (MulAut.conj k).toMonoidHom) := hE₀el.map _
    have hE₁c : Nat.card (E₀.map (MulAut.conj k).toMonoidHom) = r ^ 2 := by
      rw [card_map_of_injective (f := (MulAut.conj k).toMonoidHom) (MulAut.conj k).injective, hE₀c]
    have hE₁C := uc22p218s_le_centralizer hX hr hr2 hrn hML hR hE₁R hE₁L hE₁el.2
    have hsup : IsElemAbelian r (E ⊔ E₀.map (MulAut.conj k).toMonoidHom) :=
      hEel.sup_of_commute hE₁el fun a ha b hb => mem_centralizer_iff.1 (hE₁C hb) a (hER ha)
    obtain ⟨j, hj⟩ := hsup.isPGroup.exists_card_eq
    have hj2 : j ≤ 2 := (UC6S846.le_pRank' hr (sup_le hEM (hE₁L.trans hLM)) hsup hj).trans hrM
    have hle : Nat.card (E ⊔ E₀.map (MulAut.conj k).toMonoidHom : Subgroup G) ≤ r ^ 2 := by
      rw [hj]
      exact Nat.pow_le_pow_right hr.pos hj2
    have h1 := Subgroup.eq_of_le_of_card_ge le_sup_left (hle.trans hEc.ge)
    have h2 := Subgroup.eq_of_le_of_card_ge le_sup_right (hle.trans hE₁c.ge)
    have hEL : E ≤ L := (h1.trans h2.symm).le.trans hE₁L
    obtain ⟨w₂, hw₂L, hw₂C⟩ :=
      uc22s218u_exists_conj_commute hp hp2 hr hr2 hO hOL hLO hEel.isPGroup hEL hyp (hML hyM) hyL
    have hmem : w₂⁻¹ * y * w₂ ∈ D.M ⊓ centralizer (E : Set G) :=
      mem_inf.2 ⟨mul_mem (mul_mem (inv_mem (hLM hw₂L)) hyM) (hLM hw₂L), hw₂C⟩
    have ho : orderOf (w₂⁻¹ * y * w₂) = p := by
      have h3 : orderOf (MulAut.conj w₂⁻¹ y) = p := by rw [MulEquiv.orderOf_eq, hyo]
      rw [MulAut.conj_apply, inv_inv] at h3
      exact h3
    rw [← ho, ← Subgroup.orderOf_mk (w₂⁻¹ * y * w₂) hmem]
    exact orderOf_dvd_natCard _
  have hrankM : 2 ≤ CFSG.Open.pRank r D.M := by
    rw [← hrL]
    exact CFSG.SectionRank.pRank_mono hr.one_lt hLM
  have hXc : Nat.card X = r := by rw [hXdef, Nat.card_zpowers, hxo]
  refine ⟨X, by rw [hXc]; exact hr, by rw [hXc]; exact hrn, zpowers_le.2 (mem_inf.2 ⟨hxL, hxS⟩), ?_⟩
  exact PartTwo.mem_uniqueSet_of_centralizer hp hsp hr hXM hXc ((centralizer_le_normalizer _).trans hNX)
    hrankM hE

theorem s21_8U_dataOfSetup (hS : RankThreeUC.Standing G) (hUC : CFSG.Open.rankThreeUC G)
    (hC : RankThreeUC.AGL81TheoremC G) (S : RankThreeUC.Setup G) {Ch : Choice2011 G}
    (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) Ch) (h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S))
    (h76 : F07.R76Sig (PartTwo.Three.dataOfSetup hS S)) (h72 : F07.R72 (PartTwo.Three.dataOfSetup hS S))
    (hKf : PartTwo.S19.K_19_25_noL2SzSection) : S21_8U (PartTwo.Three.dataOfSetup hS S) Ch :=
  s21_8U_of_r72 hS.rank (UC6S846.sigmaStd_dataOfSetup hS S) h211
    (s21_8P_of_conclusion76 _ Ch h211 (UC6S846.sigmaStd_dataOfSetup hS S) h614 h76)
    (PartTwo.Three.r71_dataOfSetup hS S (PartTwo.Three.r6_3_dataOfSetup hS hUC hC S)) h72 hKf
    fun _ hr h7 h3 => PartTwo.Three.mem_sigmaOf_of_three_le_pRank hS hUC S.witness.maxLocal hr h7 h3

end CFSG.LocalAnalysis.UniquenessCase.UC22

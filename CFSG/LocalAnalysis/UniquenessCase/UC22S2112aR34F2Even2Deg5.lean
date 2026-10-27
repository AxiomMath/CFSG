module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.UC22S214U
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.OddLieFun
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Deg5Frame
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2Deg5Aut
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2Even2F1
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34F2
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34L3
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Inn
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Fun
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Odd
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Hall
import CFSG.LocalAnalysis.UniquenessCase.UC22S218GChain
import CFSG.LocalAnalysis.UniquenessCase.UC22S2113
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC22P20c
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.QuotInfBar2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsTwentyEight
import CFSG.LocalAnalysis.GLTheoremA.S4.FullCover.MultLie
import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3Odd
import CFSG.RankThree.PartTwo.Sec4.T444.Coprime
import CFSG.GroupTheory.PRankBound
import CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.Arith
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.Models.Transport
import CFSG.Timmesfeld.Bridge.RootSetsConn3

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Multiplier (genericOrders)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F14 (FunSet)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17 (IsL3EpsOdd17)

open scoped Pointwise
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719 (K_FunCommute)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r34_deg5_not_dvd_radical (hGA : GriessAllModelsStatement)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) (h5π : 5 ∈ piSet c.B0)
    {L : Subgroup G} (hL : L ∈ calC D.M) {t : StatedLieTag} {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ht : t = .PSL ∨ t = .PSU) (hX : LieModel (BarInf L) t 5 p f)
    (h5 : 5 ∣ (genericOrders t 5 p f).1) :
    ¬ 5 ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := by
  intro h5dvd
  have h5Z : 5 ∣ Nat.card ↥(center (Bar2 L)) := by
    by_contra h
    exact (not_dvd_card_solvableRadical hL.2.2 Nat.prime_five (by norm_num) h) h5dvd
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hL
  have hm : CFSG.Models.LieModel (Bar2 L ⧸ center (Bar2 L)) t 5 p f :=
    CFSG.Models.LieModel.of_mulEquiv e
      (CFSG.ComponentClassification.HarrisLit.T1.P58b3.models_lieModel_of_lieModel hTB hp
        (by omega) hX)
  have he : CFSG.Blueprint.Multiplier.exceptionalOrders t 5 p f = (1, 1) := by
    rcases ht with rfl | rfl <;> rfl
  have hne : (genericOrders t 5 p f).1 * (genericOrders t 5 p f).2 * (1 * 1) ≠ 0 := by
    have h1 := CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_fst_pos
      hX.admissible
    have h2 := (CFSG.HardMathSupport.Timmesfeld.Tables.Multiplier.genericOrders_snd_le
      t 5 p f).1
    exact Nat.mul_ne_zero (Nat.mul_ne_zero h1.ne' h2.ne') (by norm_num)
  have hdvd : Nat.card ↥(center (Bar2 L)) ∣
      (genericOrders t 5 p f).1 * (genericOrders t 5 p f).2 * (1 * 1) :=
    CFSG.LocalAnalysis.GLTheoremA.card_center_dvd_of_table hGA hL.2.2 hm rfl he hne
  have hg2 : (genericOrders t 5 p f).2 = 1 := by
    rcases ht with rfl | rfl <;> rfl
  have hg1 : (genericOrders t 5 p f).1 ∣ 5 := by
    rcases ht with rfl | rfl
    · exact (show (genericOrders .PSL 5 p f).1 = Nat.gcd 5 (p ^ f - 1) from rfl) ▸
        Nat.gcd_dvd_left 5 (p ^ f - 1)
    · exact (show (genericOrders .PSU 5 p f).1 = Nat.gcd 5 (p ^ f + 1) from rfl) ▸
        Nat.gcd_dvd_left 5 (p ^ f + 1)
  have hdvd5 : Nat.card ↥(center (Bar2 L)) ∣ 5 := by
    refine (hg2 ▸ hdvd).trans ?_
    simpa using hg1
  have hcardZ : Nat.card ↥(center (Bar2 L)) = 5 := Nat.dvd_antisymm hdvd5 h5Z
  let φ : Bar2 L →* BarInf L :=
    e.symm.toMonoidHom.comp (QuotientGroup.mk' (center (Bar2 L)))
  have hφker : φ.ker = center (Bar2 L) := by
    ext z
    show e.symm (QuotientGroup.mk z) = 1 ↔ z ∈ center (Bar2 L)
    rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
  have hsurj : Function.Surjective φ :=
    e.symm.surjective.comp (QuotientGroup.mk'_surjective (center (Bar2 L)))
  have hexp : ∀ z ∈ φ.ker, z ^ 5 = 1 := by
    intro z hz
    rw [hφker] at hz
    have hd : orderOf z ∣ Nat.card ↥(center (Bar2 L)) := Subgroup.orderOf_dvd_natCard _ hz
    rw [hcardZ] at hd
    exact orderOf_dvd_iff_pow_eq_one.1 hd
  have hnt : φ.ker ≠ ⊥ := by
    intro h
    have h1 : Nat.card φ.ker = 1 := by rw [h]; exact Subgroup.card_bot
    rw [hφker, hcardZ] at h1
    omega
  have h4 : 4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup (Bar2 L)) :=
    four_le_pRank_of_deg5Frame φ hsurj (by rw [hφker]) hexp hnt
      (deg5Frame_of_lieModel hp hp2 ht hX h5)
  rw [pRank_bar2_eq_of_odd Nat.prime_five (by norm_num)] at h4
  have h3 := (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 5) hL.1.le).trans
    (uc22s2112r34_pRank_le_three hσ hH c hL h5π (by norm_num))
  omega

private theorem uc22s2112r34_deg5_pow_five_sub_one_mod25 {x : ℕ} (hx : 1 ≤ x)
    (h : 5 ∣ x ^ 5 - 1) : 25 ∣ x ^ 5 - 1 := by
  have key : ∀ r < 25, r ^ 5 % 5 = 1 → r ^ 5 % 25 = 1 := by decide
  have hx5 : 1 ≤ x ^ 5 := Nat.one_le_pow 5 x hx
  have h5 : x ^ 5 % 5 = 1 := by
    have h1 : 1 ≡ x ^ 5 [MOD 5] := (Nat.modEq_iff_dvd' hx5).2 h
    simpa [Nat.ModEq] using h1.symm
  have hmod : (x % 25) ^ 5 % 5 = 1 := by
    rw [Nat.pow_mod, Nat.mod_mod_of_dvd x (by norm_num : 5 ∣ 25), ← Nat.pow_mod]
    exact h5
  have h25 : x ^ 5 % 25 = 1 := by
    rw [Nat.pow_mod]
    exact key (x % 25) (Nat.mod_lt _ (by norm_num)) hmod
  have h1 : 1 ≡ x ^ 5 [MOD 25] := by
    show 1 % 25 = x ^ 5 % 25
    rw [h25]
  exact (Nat.modEq_iff_dvd' hx5).1 h1

private theorem uc22s2112r34_deg5_pow_five_add_one_mod25 {x : ℕ}
    (h : 5 ∣ x ^ 5 + 1) : 25 ∣ x ^ 5 + 1 := by
  have key : ∀ r < 25, r ^ 5 % 5 = 4 → r ^ 5 % 25 = 24 := by decide
  have h5 : x ^ 5 % 5 = 4 := by
    have h0 : (x ^ 5 + 1) % 5 = 0 := Nat.dvd_iff_mod_eq_zero.1 h
    have h1 : (x ^ 5 % 5 + 1) % 5 = 0 := by
      rw [Nat.add_mod] at h0
      simpa using h0
    have hdiv : 5 ∣ x ^ 5 % 5 + 1 := Nat.dvd_iff_mod_eq_zero.2 h1
    have hle : 5 ≤ x ^ 5 % 5 + 1 := Nat.le_of_dvd (by norm_num) hdiv
    have hlt : x ^ 5 % 5 < 5 := Nat.mod_lt _ (by norm_num)
    omega
  have hmod : (x % 25) ^ 5 % 5 = 4 := by
    rw [Nat.pow_mod, Nat.mod_mod_of_dvd x (by norm_num : 5 ∣ 25), ← Nat.pow_mod]
    exact h5
  have h25 : x ^ 5 % 25 = 24 := by
    rw [Nat.pow_mod]
    exact key (x % 25) (Nat.mod_lt _ (by norm_num)) hmod
  have hx24 : 24 ≤ x ^ 5 := h25 ▸ Nat.mod_le (x ^ 5) 25
  have h1 : 24 ≡ x ^ 5 [MOD 25] := by
    show 24 % 25 = x ^ 5 % 25
    rw [h25]
  have hdvd : 25 ∣ x ^ 5 - 24 := (Nat.modEq_iff_dvd' hx24).1 h1
  have hx1 : x ^ 5 + 1 = (x ^ 5 - 24) + 25 := by omega
  rw [hx1]
  exact Nat.dvd_add hdvd (dvd_refl 25)

private theorem uc22s2112r34_deg5_not_dvd_twentyfive (hGA : GriessAllModelsStatement)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) (h5π : 5 ∈ piSet c.B0)
    {L : Subgroup G} (hL : L ∈ calC D.M) {t : StatedLieTag} {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ht : t = .PSL ∨ t = .PSU) (hX : LieModel (BarInf L) t 5 p f)
    (h5 : 5 ∣ (genericOrders t 5 p f).1) :
    ¬ ((t = .PSL ∧ 25 ∣ p ^ f - 1) ∨ (t = .PSU ∧ 25 ∣ p ^ f + 1)) := by
  have h5N := uc22s2112r34_deg5_not_dvd_radical hGA hTB hσ hH c h5π hL hp hp2 ht hX h5
  have h3 := (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 5) hL.1.le).trans
    (uc22s2112r34_pRank_le_three hσ hH c hL h5π (by norm_num))
  rintro (⟨rfl, h25⟩ | ⟨rfl, h25⟩)
  · have h4 := four_le_pRank_of_lieModel_deg5 (X := BarInf L) hp hp2 hX (Or.inl ⟨rfl, h25⟩)
    rw [← pRank_eq_pRank_barInf Nat.prime_five h5N] at h4
    omega
  · have h4 := four_le_pRank_of_lieModel_deg5 (X := BarInf L) hp hp2 hX (Or.inr ⟨rfl, h25⟩)
    rw [← pRank_eq_pRank_barInf Nat.prime_five h5N] at h4
    omega

theorem uc22s2112r34_deg5_not_five_dvd_f (hGA : GriessAllModelsStatement)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) (h5π : 5 ∈ piSet c.B0)
    {L : Subgroup G} (hL : L ∈ calC D.M) {t : StatedLieTag} {p f : ℕ} (hp : p.Prime)
    (hp2 : p ≠ 2) (ht : t = .PSL ∨ t = .PSU) (hX : LieModel (BarInf L) t 5 p f)
    (h5 : 5 ∣ (genericOrders t 5 p f).1) : ¬ 5 ∣ f := by
  have h25 := uc22s2112r34_deg5_not_dvd_twentyfive hGA hTB hσ hH c h5π hL hp hp2 ht hX h5
  intro h5f
  obtain ⟨k, hk⟩ := h5f
  have hpoweq : p ^ f = (p ^ k) ^ 5 := by rw [hk, pow_mul']
  rcases ht with rfl | rfl
  · have hgen : genericOrders .PSL 5 p f = (Nat.gcd 5 (p ^ f - 1), 1) := rfl
    rw [hgen] at h5
    have h5dvd : 5 ∣ p ^ f - 1 := h5.trans (Nat.gcd_dvd_right 5 _)
    have h25dvd : 25 ∣ p ^ f - 1 := by
      rw [hpoweq]
      exact uc22s2112r34_deg5_pow_five_sub_one_mod25 (x := p ^ k)
        (Nat.one_le_pow k p hp.pos) (by rwa [hpoweq] at h5dvd)
    exact h25 (Or.inl ⟨rfl, h25dvd⟩)
  · have hgen : genericOrders .PSU 5 p f = (Nat.gcd 5 (p ^ f + 1), 1) := rfl
    rw [hgen] at h5
    have h5dvd : 5 ∣ p ^ f + 1 := h5.trans (Nat.gcd_dvd_right 5 _)
    have h25dvd : 25 ∣ p ^ f + 1 := by
      rw [hpoweq]
      exact uc22s2112r34_deg5_pow_five_add_one_mod25 (by rwa [hpoweq] at h5dvd)
    exact h25 (Or.inr ⟨rfl, h25dvd⟩)

theorem uc22s2112r34_deg5_inner_of_pow_five {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) (h5π : 5 ∈ piSet c.B0)
    {L : Subgroup G} (hL : L ∈ calC D.M) {t : StatedLieTag} {p f : ℕ} (hp : p.Prime)
    (ht : t = .PSL ∨ t = .PSU) (hX : LieModel (BarInf L) t 5 p f)
    (h5 : 5 ∣ (genericOrders t 5 p f).1) (h5f : ¬ 5 ∣ f)
    (h5N : ¬ 5 ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) {b : G}
    (hbN : b ∈ normalizer (L : Set G)) (hbM : b ∈ D.M) (hb5 : b ^ 5 = 1) :
    inducedBarInfAutHom L ⟨b, hbN⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
  by_contra hout
  have hα5 : inducedBarInfAutHom L ⟨b, hbN⟩ ^ 5 = 1 := by
    rw [← map_pow,
      show (⟨b, hbN⟩ : ↥(normalizer (L : Set G))) ^ 5 = 1 from Subtype.ext (by simpa using hb5),
      map_one]
  have h4 := four_le_pRank_of_not_inner_deg5 hp ht hX h5 h5f hα5 hout
  set I : Subgroup (MulAut (BarInf L)) :=
    (MulAut.conj : BarInf L →* MulAut (BarInf L)).range with hIdef
  set α : MulAut (BarInf L) := inducedBarInfAutHom L ⟨b, hbN⟩ with hαdef
  have hout' : α ∉ I := hout
  have hα5' : α ^ 5 = 1 := hα5
  have h4' : 4 ≤ CFSG.Open.pRank 5 (I ⊔ Subgroup.zpowers α) := h4
  set H : Subgroup G := L ⊔ Subgroup.zpowers b with hHdef
  have hHN : H ≤ normalizer (L : Set G) :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hbN)
  have hHM : H ≤ D.M := sup_le hL.1.le (Subgroup.zpowers_le.mpr hbM)
  let φ : ↥H →* MulAut (BarInf L) :=
    (inducedBarInfAutHom L).comp (Subgroup.inclusion hHN)
  have hinclL : ∀ (x : ↥L) (hx : (x : G) ∈ H),
      φ ⟨x, hx⟩ = MulAut.conj ((x : ↥L) : BarInf L) := by
    intro x hx
    change inducedBarInfAutHom L (Subgroup.inclusion hHN ⟨x, hx⟩) =
      MulAut.conj ((x : ↥L) : BarInf L)
    rw [show (Subgroup.inclusion hHN ⟨x, hx⟩ : ↥(normalizer (L : Set G))) =
      ⟨x, le_normalizer x.2⟩ from Subtype.ext rfl]
    exact uc22s2113_inducedBarInfAutHom_of_mem x.2
  have hbφ : φ ⟨b, mem_sup_right (Subgroup.mem_zpowers b)⟩ = α := by
    change inducedBarInfAutHom L
      (Subgroup.inclusion hHN ⟨b, mem_sup_right (Subgroup.mem_zpowers b)⟩) =
        inducedBarInfAutHom L ⟨b, hbN⟩
    rw [show (Subgroup.inclusion hHN ⟨b, mem_sup_right (Subgroup.mem_zpowers b)⟩ :
      ↥(normalizer (L : Set G))) = ⟨b, hbN⟩ from Subtype.ext rfl]
  have hle : I ⊔ Subgroup.zpowers α ≤ φ.range := by
    refine sup_le ?_ ?_
    · rintro - ⟨x, rfl⟩
      obtain ⟨x₀, rfl⟩ := QuotientGroup.mk_surjective x
      exact ⟨⟨x₀, mem_sup_left x₀.2⟩, hinclL x₀ (mem_sup_left x₀.2)⟩
    · rw [Subgroup.zpowers_le]
      exact ⟨⟨b, mem_sup_right (Subgroup.mem_zpowers b)⟩, hbφ⟩
  have hker_le : φ.ker.map H.subtype ≤ (CFSG.solvableRadical ↥L).map L.subtype := by
    rintro g ⟨h, hh, rfl⟩
    have hφ1 : φ h = 1 := hh
    have hcoemul : (↑(L ⊔ Subgroup.zpowers b) : Set G) =
        (L : Set G) * (Subgroup.zpowers b : Set G) :=
      Subgroup.coe_mul_of_right_le_normalizer_left L (Subgroup.zpowers b)
        (Subgroup.zpowers_le.mpr hbN)
    have hmem : (h : G) ∈ (↑(L ⊔ Subgroup.zpowers b) : Set G) := h.2
    rw [hcoemul] at hmem
    obtain ⟨l₀, hl₀, c₀, hc₀, hlc₀⟩ := Set.mem_mul.mp hmem
    let l : ↥L := ⟨l₀, hl₀⟩
    let c' : ↥(Subgroup.zpowers b) := ⟨c₀, hc₀⟩
    have hlc : (l : G) * (c' : G) = (h : G) := hlc₀
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 c'.2
    have hdecomp : φ h =
        MulAut.conj (QuotientGroup.mk (s := CFSG.solvableRadical ↥L) l) * α ^ k := by
      have h1 : (⟨(h : G), h.2⟩ : ↥H) =
          ⟨(l : G), mem_sup_left l.2⟩ * ⟨(c' : G), mem_sup_right c'.2⟩ :=
        Subtype.ext hlc.symm
      have h2 : (⟨(c' : G), mem_sup_right c'.2⟩ : ↥H) =
          ⟨b, mem_sup_right (Subgroup.mem_zpowers b)⟩ ^ k := Subtype.ext hk.symm
      calc φ h = φ (⟨(l : G), mem_sup_left l.2⟩ * ⟨(c' : G), mem_sup_right c'.2⟩) :=
            congrArg φ h1
        _ = φ ⟨(l : G), mem_sup_left l.2⟩ * φ ⟨(c' : G), mem_sup_right c'.2⟩ :=
            map_mul _ _ _
        _ = MulAut.conj (QuotientGroup.mk (s := CFSG.solvableRadical ↥L) l) * α ^ k := by
              rw [hinclL l (mem_sup_left l.2), h2, map_zpow, hbφ]
    have hprod : MulAut.conj (QuotientGroup.mk (s := CFSG.solvableRadical ↥L) l) * α ^ k = 1 := by
      rw [← hdecomp]
      exact hφ1
    have hαkI : α ^ k ∈ I := by
      have h1 : α ^ k = (MulAut.conj (QuotientGroup.mk (s := CFSG.solvableRadical ↥L) l))⁻¹ :=
        eq_inv_of_mul_eq_one_right hprod
      rw [h1]
      exact I.inv_mem ⟨_, rfl⟩
    have key : ∀ k : ℤ, α ^ k ∈ I → ¬ (5 : ℤ) ∣ k → α ∈ I := by
      intro k hkI h5k
      have hgcd : Int.gcd k 5 = 1 := by
        have hdvd : Int.gcd k 5 ∣ 5 := by
          rw [Int.gcd_eq_natAbs_gcd_natAbs]
          exact Nat.gcd_dvd_right _ _
        rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h | h
        · exact h
        · exact absurd ((Int.dvd_gcd_iff (a := k) (b := (5 : ℤ)) (c := 5)).1
            (h ▸ dvd_rfl)).1 h5k
      have hbez := Int.gcd_eq_gcd_ab k 5
      rw [hgcd] at hbez
      have hα_eq : α = (α ^ k) ^ (Int.gcdA k 5) * (α ^ (5 : ℤ)) ^ (Int.gcdB k 5) := by
        rw [← zpow_mul, ← zpow_mul, ← zpow_add, ← hbez]
        simp
      rw [hα_eq]
      refine I.mul_mem (I.zpow_mem hkI _) (I.zpow_mem ?_ _)
      rw [show α ^ (5 : ℤ) = 1 from by simpa using hα5']
      exact I.one_mem
    by_cases h5k : (5 : ℤ) ∣ k
    · obtain ⟨j, hj⟩ := h5k
      have hαk1 : α ^ k = 1 := by
        rw [hj, zpow_mul, show α ^ (5 : ℤ) = 1 from by simpa using hα5', one_zpow]
      have hc1 : c' = 1 := by
        apply Subtype.ext
        rw [← hk, hj, zpow_mul, show b ^ (5 : ℤ) = 1 from by simpa using hb5, one_zpow]
        rfl
      have hl_eq : (h : G) = (l : G) := by
        simpa [hc1] using hlc.symm
      have hconj1 : MulAut.conj (QuotientGroup.mk (s := CFSG.solvableRadical ↥L) l) = 1 := by
        have h := hprod
        rwa [hαk1, mul_one] at h
      have hcenter : QuotientGroup.mk (s := CFSG.solvableRadical ↥L) l ∈
          Subgroup.center (BarInf L) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have h := congrArg (fun f : MulAut (BarInf L) => f y) hconj1
        simp only [MulAut.conj_apply, MulAut.one_apply] at h
        exact (mul_inv_eq_iff_eq_mul.1 h).symm
      rw [center_barInf_eq_bot hL.2.2, Subgroup.mem_bot] at hcenter
      have hrad : l ∈ CFSG.solvableRadical ↥L :=
        (QuotientGroup.eq_one_iff (N := CFSG.solvableRadical ↥L) l).1 hcenter
      exact ⟨l, hrad, hl_eq.symm⟩
    · exact (hout (key k hαkI h5k)).elim
  have hkerdvd : Nat.card φ.ker ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := by
    have h1 : Nat.card φ.ker = Nat.card (φ.ker.map H.subtype) :=
      (Subgroup.card_map_of_injective (f := H.subtype) H.subtype_injective).symm
    rw [h1, ← Subgroup.card_map_of_injective L.subtype_injective]
    exact Subgroup.card_dvd_of_le hker_le
  have h5ker : ¬ 5 ∣ Nat.card φ.ker := fun hd => h5N (hd.trans hkerdvd)
  have hmap := CFSG.RankThree.PartTwo.Sec4.pRank_map_le_of_not_dvd Nat.prime_five φ h5ker
    (⊤ : Subgroup ↥H)
  rw [Subgroup.map_top, ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H] at hmap
  have h4'' : 4 ≤ CFSG.Open.pRank 5 H :=
    h4'.trans ((CFSG.SectionRank.pRank_mono (by norm_num : 1 < 5) hle).trans hmap)
  have h3 := (CFSG.SectionRank.pRank_mono (by norm_num : 1 < 5) hHM).trans
    (uc22s2112r34_pRank_le_three hσ hH c hL h5π (by norm_num))
  omega

theorem uc22s2112r34_deg5_inner_f1 (hGA : GriessAllModelsStatement)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hBN : c.B0 ≤ normalizer (L : Set G))
    {t : StatedLieTag} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ht : t = .PSL ∨ t = .PSU)
    (hX : LieModel (BarInf L) t 5 p 1) (h5 : 5 ∣ (genericOrders t 5 p 1).1) :
    ∀ b (hb : b ∈ c.B0),
      inducedBarInfAutHom L ⟨b, hBN hb⟩ ∈ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range := by
  have houtdvd : Nat.card (CFSG.ComponentClassification.OuterAutomorphisms.Outer
      (BarInf L)) ∣ 10 := by
    obtain ⟨hb1, -⟩ :=
      CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound
        (T := BarInf L) ht (n := 5) (ℓ := p) (f := 1) (by norm_num) hp le_rfl
        (hX.statedClassicalModel_of_ne_zero (by norm_num))
    have hdet : CFSG.RankThree.OuterOrder.determinantParameter t 5 (p ^ 1) ∣ 5 := by
      rcases ht with rfl | rfl
      · exact Nat.gcd_dvd_left 5 _
      · exact Nat.gcd_dvd_left 5 _
    refine hb1.trans ?_
    simpa using Nat.mul_dvd_mul_left (2 * 1) hdet
  intro b hb
  by_contra hout
  have hout' : inducedBarInfAutHom L ⟨b, hBN hb⟩ ∉
      CFSG.ComponentClassification.OuterAutomorphisms.inner (BarInf L) := hout
  set α : MulAut (BarInf L) := inducedBarInfAutHom L ⟨b, hBN hb⟩ with hαdef
  have hoddm : Odd (orderOf b) :=
    Odd.of_dvd_nat (ch214_odd_card c.hpi) (Subgroup.orderOf_dvd_natCard c.B0 hb)
  have hsqm : Squarefree (orderOf b) := Ctx23L.orderOf_squarefree_of_mem_calB1 c.hB0 hb
  set π := QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner (BarInf L))
    with hπdef
  have hπne : π α ≠ 1 := fun h => hout' ((QuotientGroup.eq_one_iff α).1 h)
  have hdvdm : orderOf (π α) ∣ orderOf b := by
    refine (orderOf_map_dvd π α).trans ?_
    have h := orderOf_map_dvd (inducedBarInfAutHom L)
      (⟨b, hBN hb⟩ : ↥(normalizer (L : Set G)))
    simpa [Subgroup.orderOf_mk] using h
  have hdvd10 : orderOf (π α) ∣ 10 := (orderOf_dvd_natCard (π α)).trans houtdvd
  have h5ord : orderOf (π α) = 5 := by
    have hne1 : orderOf (π α) ≠ 1 := fun h => hπne (orderOf_eq_one_iff.1 h)
    have hodd := hoddm.of_dvd_nat hdvdm
    have h5dvd : orderOf (π α) ∣ 5 :=
      (Nat.Coprime.dvd_mul_right hodd.coprime_two_right).1 (by simpa using hdvd10)
    rcases (Nat.dvd_prime Nat.prime_five).1 h5dvd with h1 | h
    · exact absurd h1 hne1
    · exact h
  have h5m : 5 ∣ orderOf b := h5ord ▸ hdvdm
  have h5π : 5 ∈ piSet c.B0 :=
    ⟨Nat.prime_five, h5m.trans (Subgroup.orderOf_dvd_natCard c.B0 hb)⟩
  have h5N := uc22s2112r34_deg5_not_dvd_radical hGA hTB hσ hH c h5π hL hp hp2 ht hX h5
  obtain ⟨k, hk⟩ := h5m
  have hk5 : ¬ 5 ∣ k := by
    intro h
    obtain ⟨j, hj⟩ := h
    have h25 : 5 * 5 ∣ orderOf b := by
      rw [hk, hj]
      exact ⟨j, by ring⟩
    exact (Nat.squarefree_iff_prime_squarefree.1 hsqm 5 Nat.prime_five) h25
  have hb'B : b ^ k ∈ c.B0 := c.B0.pow_mem hb k
  have hb'N : b ^ k ∈ normalizer (L : Set G) := hBN hb'B
  have hb'M : b ^ k ∈ D.M := c.hBM hb'B
  have hb'5 : (b ^ k) ^ 5 = 1 := by
    rw [← pow_mul, show k * 5 = orderOf b by rw [hk]; ring, pow_orderOf_eq_one]
  have hinner := uc22s2112r34_deg5_inner_of_pow_five hσ hH c h5π hL hp ht hX h5 (by norm_num)
    h5N hb'N hb'M hb'5
  have hθ : inducedBarInfAutHom L ⟨b ^ k, hb'N⟩ = α ^ k := by
    rw [show (⟨b ^ k, hb'N⟩ : ↥(normalizer (L : Set G))) = ⟨b, hBN hb⟩ ^ k from
      Subtype.ext rfl, map_pow]
  have hαk_inner : α ^ k ∈
      CFSG.ComponentClassification.OuterAutomorphisms.inner (BarInf L) := by
    rw [← hθ]
    exact hinner
  have hq : π (α ^ k) = 1 := (QuotientGroup.eq_one_iff (α ^ k)).2 hαk_inner
  have hq2 : (π α) ^ k = 1 := by
    rw [← map_pow]
    exact hq
  have h5k : 5 ∣ k := by
    have h : orderOf (π α) ∣ k := (orderOf_dvd_iff_pow_eq_one).2 hq2
    rwa [h5ord] at h
  exact hk5 h5k

theorem uc22s2112r34_deg5_not_dvd_radical_all (hGA : GriessAllModelsStatement)
    (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) {t : StatedLieTag} {p f : ℕ} (hp : p.Prime)
    (hp5 : 5 ≤ p) (ht : t = .PSL ∨ t = .PSU) (hX : LieModel (BarInf L) t 5 p f)
    (h5 : 5 ∣ (genericOrders t 5 p f).1) :
    ∀ s : ℕ, s.Prime → s ∣ Nat.card c.B0 → ¬ s ∣ Nat.card ↥(CFSG.solvableRadical ↥L) := by
  intro s hs hsB
  have hs2 : s ≠ 2 := by
    intro h2
    subst h2
    exact (ch214_odd_card c.hpi).not_two_dvd_nat hsB
  by_cases hs5 : s = 5
  · subst hs5
    exact uc22s2112r34_deg5_not_dvd_radical hGA hTB hσ hH c ⟨Nat.prime_five, hsB⟩ hL hp
      (by omega) ht hX h5
  · have hsg : ¬ s ∣ (genericOrders t 5 p f).1 := by
      rcases ht with rfl | rfl
      · intro hdvd
        have hgen : genericOrders .PSL 5 p f = (Nat.gcd 5 (p ^ f - 1), 1) := rfl
        rw [hgen] at hdvd
        exact hs5 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_five).1
          (hdvd.trans (Nat.gcd_dvd_left 5 (p ^ f - 1))))
      · intro hdvd
        have hgen : genericOrders .PSU 5 p f = (Nat.gcd 5 (p ^ f + 1), 1) := rfl
        rw [hgen] at hdvd
        exact hs5 ((Nat.prime_dvd_prime_iff_eq hs Nat.prime_five).1
          (hdvd.trans (Nat.gcd_dvd_left 5 (p ^ f + 1))))
    exact not_dvd_card_solvableRadical hL.2.2 hs hs2
      (uc22s2112r34_not_dvd_center_of_five_le hGA hTB hL hp hp5 hX hs hs2 hsg)

section F2


theorem uc22s2112r34_false_deg5_f2 (hKS : KFunSplit) (hKC : KFunCount) (hFC : K_FunCommute)
    (hGA : GriessAllModelsStatement) (hTB : CFSG.TauCetiBridge.TypewiseBridges) {D : Data G}
    {Ch : Choice2011 G} (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D)
    (c : Ctx21 D Ch) (hn4 : c.n = 4) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hBN : c.B0 ≤ normalizer (L : Set G)) (hfaith : ∀ b ∈ c.B0, CentralizesBar b L → b = 1)
    {t : StatedLieTag} {p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (ht : t = .PSL ∨ t = .PSU)
    (hadm : StatedLieAdmissible t 5 p f) (hf2 : 2 ≤ f) (h5 : 5 ∣ (genericOrders t 5 p f).1)
    (hX : LieModel (BarInf L) t 5 p f) (hno : ∀ f : ℕ, ¬ LieModel (BarInf L) .PSL 2 p f)
    (hree : ∀ f : ℕ, ¬ LieModel (BarInf L) .twistedG2 0 3 f) (hpσ : p ∈ D.sig)
    (hpN : ¬ p ∣ Nat.card ↥(CFSG.solvableRadical ↥L)) : False := by
  have : IsSimpleGroup (BarInf L) := (uc22p20c_barInf_simple (uc22p20e_cComp_of_calC hL)).1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hZ : center (BarInf L) = ⊥ := center_barInf_eq_bot hL.2.2
  have h5π : 5 ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨Nat.prime_five, by rw [hn4]; norm_num⟩
  have hp5 : p ≠ 5 := fun h =>
    uc22s2112r34_not_mem_sig hσ hH c hL h5π (h ▸ hpσ)
  have h5N := uc22s2112r34_deg5_not_dvd_radical hGA hTB hσ hH c h5π hL hp hp2 ht hX h5
  have h5f := uc22s2112r34_deg5_not_five_dvd_f hGA hTB hσ hH c h5π hL hp hp2 ht hX h5
  have ht5 : FunTwoType t 5 := by rcases ht with rfl | rfl <;> exact Or.inr rfl
  obtain ⟨hA1, hA3, hRee⟩ := uc22s2112r34_funTwoType_ne ht5
  have hMs : IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hpσ
  have hp3 : 3 ≤ p := by have := hp.two_le; omega
  have hq9 : 9 ≤ p ^ f :=
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ f := Nat.pow_le_pow_right hp.pos hf2
  obtain ⟨-, h4⟩ := uc22s2112r34_pRank_of_lieModel hp hp2 hX hA1 (fun h => hA3 ⟨h.1, h.2.1⟩)
    hRee hpN
  have h4' : 4 ≤ CFSG.Open.pRank p L := by rcases h4 with ⟨-, h1⟩ | h4 <;> omega
  have hL3 : ¬ IsL3EpsOdd17 (BarInf L) p :=
    uc22s2112r34_not_isL3EpsOdd17 hp (by rwa [← pRank_eq_pRank_barInf hp hpN])
  obtain ⟨R, hRB, -, h5R, hRr2, hRT, hRr⟩ :=
    uc22s2112r34_exists_rSub_calB1 c.hB0 D.sylowM.isPGroup Nat.prime_five h5π.2
  have hRN : R ≤ normalizer (L : Set G) := hRB.trans hBN
  have hR5 : ∀ x ∈ R, x ^ 5 = 1 := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1, one_pow]
    · rw [← hRr x hx hx1, pow_orderOf_eq_one]
  obtain ⟨P, ψ, hψ, hperm⟩ := uc22s2112r34_exists_innerHom_permutes hZ hRN
    (fun x hx => uc22s2112r34_deg5_inner_of_pow_five hσ hH c h5π hL hp ht hX h5 h5f h5N
      (hRN hx) (c.hBM (hRB hx)) (hR5 x hx))
    (uc22p2214_isSylowOf_inf D.sylowM hL.1) D.sylowM.isPGroup hRT
  have hψinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro x hx
    have h1 : inducedBarInfAutHom L ⟨(x : G), hRN x.2⟩ = 1 := by rw [← hψ x, hx, map_one]
    exact Subtype.ext (hfaith x (hRB x.2)
      (uc22s2113_centralizesBar_of_inducedBarInfAutHom_eq_one hL.2.2 _ h1))
  have hcardB : Nat.card ψ.range = Nat.card R :=
    (Nat.card_congr (MonoidHom.ofInjective hψinj).toEquiv).symm
  have hne : ψ.range ≠ ⊥ := fun h => by
    rw [h, card_bot] at hcardB
    rw [← hcardB] at h5R
    exact Nat.prime_five.one_lt.ne' (Nat.dvd_one.1 h5R)
  have : IsMulCommutative ↥c.B0 := c.hB0.2.1
  have : IsMulCommutative ↥R := isMulCommutative_anti hRB
  have hoddB : Odd (Nat.card ψ.range) := by
    rw [hcardB]
    exact (Nat.prime_five.odd_of_ne_two (by omega)).pow.of_dvd_nat hRr2
  have h3B : ¬ 3 ∣ Nat.card ψ.range := fun h => by
    rw [hcardB] at h
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_five).1
      (Nat.prime_three.dvd_of_dvd_pow (h.trans hRr2))
    omega
  have hpB : ¬ p ∣ Nat.card ψ.range := fun h => by
    rw [hcardB] at h
    exact hp5 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1
      (hp.dvd_of_dvd_pow (h.trans hRr2)))
  have hrank : ∀ s : ℕ, s.Prime → s ∣ Nat.card ψ.range →
      CFSG.pRank s ψ.range ≤ 2 ∧ CFSG.pRank s (⊤ : Subgroup (BarInf L)) ≤ 3 := by
    intro s hs hsd
    rw [hcardB] at hsd
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hs Nat.prime_five).1
      (hs.dvd_of_dvd_pow (hsd.trans hRr2))
    refine ⟨?_, ?_⟩
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
      refine CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ hs fun h => ?_
      rw [hcardB] at h
      have := (Nat.pow_dvd_pow_iff_le_right hs.one_lt).1 (h.trans hRr2)
      omega
    · rw [CFSG.SectionRank.pRank_eq_open_pRank_top,
        ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup, ← pRank_eq_pRank_barInf hs h5N]
      exact (CFSG.SectionRank.pRank_mono hs.one_lt hL.1.le).trans
        (uc22s2112r34_pRank_le_three hσ hH c hL h5π (by omega))
  obtain ⟨K₁, K₂, hne12, hKeq⟩ :=
    Set.ncard_eq_two.1 ((hKC (BarInf L) t 5 p f hp hp2 hadm hX P).1 ht5)
  have h₁ : K₁ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) := by
    rw [hKeq]
    exact Set.mem_insert _ _
  have h₂ : K₂ ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)) := by
    rw [hKeq]
    exact Set.mem_insert_of_mem _ (Set.mem_singleton _)
  have hK12 : K₁ ≤ centralizer (K₂ : Set (BarInf L)) :=
    commutator_eq_bot_iff_le_centralizer.1
      (uc22s2112r34_funSet_commute_barInf hFC hL hp hp2 hX hno hL3 hree (by omega) P h₁ h₂ hne12)
  have key : ∀ K ∈ FunSet (fundPred (p ^ f)) (BarInf L) (P : Subgroup (BarInf L)),
      ∀ y ∈ ψ.range, y ∈ centralizer (K : Set (BarInf L)) → y ≠ 1 → False := by
    intro K hK y hy hyC hy1
    obtain ⟨x, rfl⟩ := MonoidHom.mem_range.1 hy
    have hx1 : (x : G) ≠ 1 := fun h => hy1 (by rw [show x = 1 from Subtype.ext h, map_one])
    have hxr := hRr x x.2 hx1
    refine uc22s2112r34_false_of_fund hKF7 hH c hL.1.le hp hp2 hf2 hpσ hMs (hRB x.2) (hRN x.2)
      (by rw [hxr]; exact Nat.prime_five) (by rw [hxr]; exact h5N) hpN hK.1 fun k hk => ?_
    change inducedBarInfAutHom L ⟨(x : G), hRN x.2⟩ k = k
    rw [← hψ x, MulAut.conj_apply, ← mem_centralizer_iff.1 hyC k hk, mul_inv_cancel_right]
  have hspl := hKS (BarInf L) t 5 p f hp hp2 hadm hX hA1 hRee P ψ.range hne inferInstance hoddB
    h3B hpB hperm hrank K₁ h₁
  rcases bot_or_exists_ne_one (ψ.range ⊓ centralizer (K₁ : Set (BarInf L))) with h0 | ⟨y, hy, hy1⟩
  ·
    rw [h0, sup_bot_eq] at hspl
    rcases bot_or_exists_ne_one ψ.range with h | ⟨y, hy, hy1⟩
    · exact hne h
    · exact key K₂ h₂ y hy (hK12 (mem_inf.1 (hspl.le hy)).2) hy1
  · exact key K₁ h₁ y (mem_inf.1 hy).1 (mem_inf.1 hy).2 hy1

end F2

end CFSG.LocalAnalysis.UniquenessCase.UC22

module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoNormalForm
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedRank
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.CaseTwoFixedEnd
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.CentralizingRank
import CFSG.GroupTheory.CoprimeCentralizerRank
import CFSG.GroupTheory.PGroup.CardCoprime
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.Quasithin.Background.A1cRank
import CFSG.RankThree.GroupTheory.SteinbergBYAschCoreConjugacy
import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.Fixed
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorSupLeOfCommutatorLeAndNormalize
public import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open Subgroup
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

namespace CaseTwoTransitive

section Neutral

variable {c : Ctx812E G} (t : CaseTwoTransitive c)

theorem pRank_Lf_eq (p : ℕ) [Fact p.Prime] (i : Fin 3) :
    CFSG.Open.pRank p (t.d.Lf i) = CFSG.Open.pRank p (t.d.Lf 0) := by
  have hstep : ∀ l : Fin 3, CFSG.Open.pRank p (t.d.Lf l) =
      CFSG.Open.pRank p (t.d.Lf (l + 1)) := by
    intro l
    rw [← t.hyL l]
    exact (CFSG.RankThree.GroupTheory.SteinbergBY.assembly_pRank_map_mulEquiv
      (Fact.out : p.Prime).one_lt (MulAut.conj t.y) (t.d.Lf l)).symm
  fin_cases i
  · rfl
  · exact (hstep 0).symm
  · exact hstep 2

private theorem map_conj_A_pow (s : Fin 3) (l : Fin 3) :
    (t.d.A l).map (MulAut.conj (t.y ^ ((s : ℕ)))).toMonoidHom = t.d.A (l + s) := by
  fin_cases s
  · show (t.d.A l).map (MulAut.conj (t.y ^ 0)).toMonoidHom = t.d.A (l + 0)
    rw [pow_zero]
    have h0 : l + 0 = l := by simp
    rw [h0]
    rw [show MulAut.conj (1 : G) = 1 from map_one (MulAut.conj : G →* MulAut G)]
    change (t.d.A l).map (MonoidHom.id G) = t.d.A l
    exact Subgroup.map_id (t.d.A l)
  · show (t.d.A l).map (MulAut.conj (t.y ^ 1)).toMonoidHom = t.d.A (l + 1)
    rw [pow_one]
    exact t.map_conj_A l
  · show (t.d.A l).map (MulAut.conj (t.y ^ 2)).toMonoidHom = t.d.A (l + 2)
    have hcomp : (MulAut.conj (t.y ^ 2)).toMonoidHom =
        (MulAut.conj t.y).toMonoidHom.comp (MulAut.conj t.y).toMonoidHom := by
      ext z
      simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      rw [show t.y ^ 2 * z * (t.y ^ 2)⁻¹ = t.y * (t.y * z * t.y⁻¹) * t.y⁻¹ by
        rw [pow_two]; group]
    rw [hcomp, ← Subgroup.map_map, t.map_conj_A l, t.map_conj_A (l + 1)]
    congr 1
    fin_cases l <;> rfl

private theorem two_le_of_map_conj {p : ℕ} [Fact p.Prime] {B B' : Subgroup G} {g : G}
    (hgM : g ∈ c.S.M) (hmap : B.map (MulAut.conj g).toMonoidHom = B')
    (h : 2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (B' : Set G))) :
    2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (B : Set G)) := by
  have hMeq : c.S.M.map (MulAut.conj g).toMonoidHom = c.S.M :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hgM)
  have hkey : (c.S.M ⊓ Subgroup.centralizer (B : Set G)).map
      (MulAut.conj g).toMonoidHom = c.S.M ⊓ Subgroup.centralizer (B' : Set G) := by
    rw [Subgroup.map_inf_eq _ _ _ (MulAut.conj g).injective, hMeq,
      CFSG.RankThree.GroupTheory.SteinbergBY.map_centralizer_mulEquiv, hmap]
  calc 2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (B' : Set G)) := h
    _ = CFSG.Open.pRank p ((c.S.M ⊓ Subgroup.centralizer (B : Set G)).map
        (MulAut.conj g).toMonoidHom) := by rw [hkey]
    _ = CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (B : Set G)) :=
        CFSG.RankThree.GroupTheory.SteinbergBY.assembly_pRank_map_mulEquiv
          (Fact.out : p.Prime).one_lt (MulAut.conj g) _

private theorem two_le_pRank_inf_centralizer_of_commutator_le {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {R B : Subgroup G}
    (hRM : R ≤ c.S.M) (hR : IsPGroup p R) (hrank : 2 ≤ CFSG.Open.pRank p R)
    (hB3 : IsPGroup 3 B) (hBM : B ≤ c.S.M)
    (hcomm : ⁅R, B⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M) :
    2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (B : Set G)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hO2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 c.S.M) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 c.S.M
  have hpO : ¬ p ∣ Nat.card ↥(CFSG.Open.pCoreOf 2 c.S.M) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hO2 (Fact.out : p.Prime) hp2
  have h3O : ¬ 3 ∣ Nat.card ↥(CFSG.Open.pCoreOf 2 c.S.M) :=
    CFSG.GroupTheory.not_dvd_card_of_isPGroup hO2 Nat.prime_three (by norm_num)
  have hbound := CFSG.GroupTheory.pRank_le_pRank_inf_centralizer_of_commutator_le
    (p := p) (q := 3) (M := c.S.M) (N := CFSG.Open.pCoreOf 2 c.S.M) (R := R) (B := B)
    hRM (CFSG.openPCoreOf_le 2 c.S.M)
    (hRM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M))
    (hBM.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M))
    hR hB3 hpO h3O hcomm
  omega

private theorem two_le_of_commuting_pElements {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {e u : G} (heM : e ∈ c.S.M) (he_ord : orderOf e = p) (huM : u ∈ c.S.M) (hu_ord : orderOf u = p)
    (hue : u * e = e * u) (hu_notmem : u ∉ Subgroup.zpowers e)
    {B : Subgroup G} (hB3 : IsPGroup 3 B) (hBM : B ≤ c.S.M)
    (hcomm : ⁅Subgroup.zpowers e ⊔ Subgroup.zpowers u, B⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M) :
    2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (B : Set G)) := by
  have hp1 : 1 < p := (Fact.out : p.Prime).one_lt
  have he_pow : e ^ p = 1 := by rw [← he_ord]; exact pow_orderOf_eq_one e
  have hu_pow : u ^ p = 1 := by rw [← hu_ord]; exact pow_orderOf_eq_one u
  have hcomm_ab : ∀ x ∈ Subgroup.zpowers e, ∀ y ∈ Subgroup.zpowers u, x * y = y * x := by
    intro x hx y hy
    obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    obtain ⟨b, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
    exact ((show Commute e u from hue.symm).zpow_zpow a b).eq
  have hR_elem : CFSG.Open.IsElemAbelian p (Subgroup.zpowers e ⊔ Subgroup.zpowers u) :=
    CFSG.Open.IsElemAbelian.sup_of_commute (CFSG.Open.isElemAbelian_zpowers he_pow)
      (CFSG.Open.isElemAbelian_zpowers hu_pow) hcomm_ab
  have hRcard : Nat.card ↥(Subgroup.zpowers e ⊔ Subgroup.zpowers u) = p ^ 2 := by
    obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute
      (Subgroup.zpowers e) (Subgroup.zpowers u) hcomm_ab
    have hinf : Subgroup.zpowers e ⊓ Subgroup.zpowers u = ⊥ := by
      rw [inf_comm]
      exact CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.Diag.zpowers_inf_eq_bot
        (Fact.out : p.Prime) hu_pow hu_notmem
    rw [hinf, Nat.card_zpowers, Nat.card_zpowers, he_ord, hu_ord, Subgroup.card_bot,
      mul_one] at hcard
    simpa [pow_two] using hcard
  have hRrank : 2 ≤ CFSG.Open.pRank p (Subgroup.zpowers e ⊔ Subgroup.zpowers u) :=
    CFSG.SectionRank.le_pRank hp1 le_rfl hR_elem hRcard
  have hRM : Subgroup.zpowers e ⊔ Subgroup.zpowers u ≤ c.S.M :=
    sup_le (Subgroup.zpowers_le.mpr heM) (Subgroup.zpowers_le.mpr huM)
  exact two_le_pRank_inf_centralizer_of_commutator_le hp2 hRM hR_elem.isPGroup hRrank
    hB3 hBM hcomm

theorem two_le_pRank_inf_centralizer_A_sup_A_of_exists {p : ℕ} (hp : p ∈ c.sig)
    (hm : 1 ≤ CFSG.Open.pRank p (t.d.Lf 0))
    (he : CFSG.Open.pRank p (t.d.Lf 0) ≤ 1 →
      ∃ e ∈ c.S.M ⊓ Subgroup.centralizer (t.d.AA : Set G), orderOf e = p)
    {i j : Fin 3} (hij : i ≠ j) :
    2 ≤ CFSG.Open.pRank p
      (c.S.M ⊓ Subgroup.centralizer ((t.d.A i ⊔ t.d.A j : Subgroup G) : Set G)) := by
  classical
  have hpp : p.Prime := (c.sig_prime p hp).1
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp1 : 1 < p := hpp.one_lt
  have hp2 : p ≠ 2 := (c.sig_prime p hp).2
  have hp5 : 5 ≤ p := c.five_le_of_mem_sigma hp
  have hAiLf : ∀ l, t.d.A l ≤ t.d.Lf l := fun l => (t.d.A_le_H l).trans (t.d.H_le_Lf l)
  have hAiM : ∀ l, t.d.A l ≤ c.S.M := fun l => (hAiLf l).trans (t.hdM ▸ t.d.hLM l)
  have hBM : (t.d.A i ⊔ t.d.A j) ≤ c.S.M := sup_le (hAiM i) (hAiM j)
  have hA_le_AA : ∀ l, t.d.A l ≤ t.d.AA := by
    intro l
    rw [t.d.AA_def]
    fin_cases l
    · exact le_sup_left.trans le_sup_left
    · exact le_sup_right.trans le_sup_left
    · exact le_sup_right
  have hpairAA : ∀ a b : Fin 3, (t.d.A a ⊔ t.d.A b) ≤ t.d.AA :=
    fun a b => sup_le (hA_le_AA a) (hA_le_AA b)
  have hBAA : (t.d.A i ⊔ t.d.A j) ≤ t.d.AA := hpairAA i j
  have hthird : ∀ a b : Fin 3, a ≠ b → ∃ k : Fin 3, a ≠ k ∧ b ≠ k := by decide
  have hadd : ∀ k m : Fin 3, ∃ s : Fin 3, k + s = m := by decide
  have hindex : ∀ (a b k s l : Fin 3), a ≠ b → a ≠ k → b ≠ k → k + s = l + 1 →
      (a + s = l + 2 ∧ b + s = l) ∨ (a + s = l ∧ b + s = l + 2) := by decide
  have hcomm_Lf : ∀ (l a b : Fin 3), a ≠ l → b ≠ l →
      ⁅t.d.Lf l, t.d.A a ⊔ t.d.A b⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M := by
    intro l a b hal hbl
    have h1 : ⁅t.d.A a ⊔ t.d.A b, t.d.Lf l⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M := by
      refine CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
        (t.d.A a) (t.d.A b) (t.d.Lf l) (CFSG.Open.pCoreOf 2 c.S.M) ?_ ?_ ?_ ?_
      · rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono le_rfl (hAiLf a)).trans (by
          have h := t.d.hcomm l a hal.symm
          rwa [t.hdM] at h)
      · rw [Subgroup.commutator_comm]
        exact (Subgroup.commutator_mono le_rfl (hAiLf b)).trans (by
          have h := t.d.hcomm l b hbl.symm
          rwa [t.hdM] at h)
      · exact (hAiM a).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M)
      · exact (hAiM b).trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M)
    rwa [Subgroup.commutator_comm] at h1
  have hnormLf : ∀ {x : G}, x ∈ c.S.M → IsPGroup p (Subgroup.zpowers x) →
      ∀ l, x ∈ Subgroup.normalizer (t.d.Lf l : Set G) := by
    intro x hxM hxp l
    exact t.d.le_normalizer_Lf_of_isPGroup hp5 t.hinj
      (fun m hm l' => t.hperm m (t.hdM ▸ hm) l') (t.hdM.symm ▸ hxM) hxp l
  have hu_fact : ∀ {x : G}, IsPGroup p (Subgroup.zpowers x) →
      (∀ l, x ∈ Subgroup.normalizer (t.d.Lf l : Set G)) → ∀ l : Fin 3,
      p ∣ Nat.card (t.d.Lf l) →
      ∃ u ∈ t.d.Lf l, orderOf u = p ∧ u * x = x * u := by
    intro x hxp hxN l hpdvd
    obtain ⟨u, huLf, huord, hucent⟩ :=
      CFSG.Quasithin.exists_orderOf_eq_of_isPGroup_normalizer hxp
        (Subgroup.zpowers_le.mpr (hxN l)) hpdvd
    exact ⟨u, huLf, huord,
      (Subgroup.mem_centralizer_iff.mp hucent x (Subgroup.mem_zpowers x)).symm⟩
  by_cases hm2 : 2 ≤ CFSG.Open.pRank p (t.d.Lf 0)
  ·
    obtain ⟨k, hik, hjk⟩ := hthird i j hij
    obtain ⟨R, hRL, hRab, hRcard⟩ := CFSG.SectionRank.exists_pRank hp1 (t.d.Lf k)
    have hRrank : 2 ≤ CFSG.Open.pRank p R := by
      have h1 : CFSG.Open.pRank p (t.d.Lf k) ≤ CFSG.Open.pRank p R :=
        (CFSG.SectionRank.le_pRank hp1 le_rfl hRab hRcard)
      have h2 : CFSG.Open.pRank p (t.d.Lf k) = CFSG.Open.pRank p (t.d.Lf 0) :=
        t.pRank_Lf_eq p k
      omega
    have hRM : R ≤ c.S.M := hRL.trans (t.hdM ▸ t.d.hLM k)
    have hcomm : ⁅R, t.d.A i ⊔ t.d.A j⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M :=
      (Subgroup.commutator_mono hRL le_rfl).trans (hcomm_Lf k i j hik hjk)
    exact two_le_pRank_inf_centralizer_of_commutator_le hp2 hRM hRab.isPGroup hRrank
      (t.d.isElemAbelian_A_sup_A i j).isPGroup hBM hcomm
  ·
    have hm1 : ∀ l, CFSG.Open.pRank p (t.d.Lf l) = 1 := by
      intro l
      rw [t.pRank_Lf_eq p l]
      omega
    have hpLf : ∀ l : Fin 3, p ∣ Nat.card (t.d.Lf l) := by
      intro l
      obtain ⟨E, hE, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank hp1 (t.d.Lf l)
      rw [hm1 l, pow_one] at hEcard
      exact hEcard ▸ Subgroup.card_dvd_of_le hE
    obtain ⟨e, ⟨heM, heC⟩, hee_ord⟩ := he (by omega)
    have he_pow : e ^ p = 1 := by
      rw [← hee_ord]
      exact pow_orderOf_eq_one _
    have hep : IsPGroup p (Subgroup.zpowers e) :=
      IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hee_ord, pow_one])
    have heN : ∀ l, e ∈ Subgroup.normalizer (t.d.Lf l : Set G) :=
      hnormLf heM hep
    by_cases hex : ∃ l : Fin 3, e ∈ t.d.Lf l
    ·
      obtain ⟨l, hel⟩ := hex
      obtain ⟨u, huLf, huord, hue⟩ := hu_fact hep heN (l + 1) (hpLf (l + 1))
      have huM : u ∈ c.S.M := (t.hdM ▸ t.d.hLM (l + 1)) huLf
      have hu_pow : u ^ p = 1 := by
        rw [← huord]
        exact pow_orderOf_eq_one u
      have hlu : (l + 1) ≠ l := by fin_cases l <;> decide
      have hu_notmem : u ∉ Subgroup.zpowers e := by
        intro hmem
        have huLfl : u ∈ t.d.Lf l := Subgroup.zpowers_le.mpr hel hmem
        have hup : IsPGroup p (Subgroup.zpowers u) :=
          (CFSG.Open.isElemAbelian_zpowers hu_pow).isPGroup
        have h1 : u = 1 :=
          eq_one_of_isPGroup_of_mem_inf_Lf t.d hp2 hlu huLf huLfl hup (hm1 (l + 1))
        rw [h1, orderOf_one] at huord
        omega
      have hcommR : ⁅Subgroup.zpowers e ⊔ Subgroup.zpowers u,
          t.d.A l ⊔ t.d.A (l + 2)⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M := by
        refine CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
          (Subgroup.zpowers e) (Subgroup.zpowers u)
          (t.d.A l ⊔ t.d.A (l + 2)) (CFSG.Open.pCoreOf 2 c.S.M) ?_ ?_ ?_ ?_
        · have hbot : ⁅Subgroup.zpowers e, t.d.A l ⊔ t.d.A (l + 2)⁆ = ⊥ := by
            rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
            exact (Subgroup.zpowers_le.mpr heC).trans
              (Subgroup.centralizer_le (hpairAA l (l + 2)))
          rw [hbot]
          exact bot_le
        · exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr huLf) le_rfl).trans
            (hcomm_Lf (l + 1) l (l + 2) (by fin_cases l <;> decide)
              (by fin_cases l <;> decide))
        · exact (Subgroup.zpowers_le.mpr heM).trans
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M)
        · exact (Subgroup.zpowers_le.mpr huM).trans
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M)
      have hbound := two_le_of_commuting_pElements (c := c) hp2 heM hee_ord huM huord hue
        hu_notmem (t.d.isElemAbelian_A_sup_A l (l + 2)).isPGroup
        (sup_le (hAiM l) (hAiM (l + 2))) hcommR
      obtain ⟨k, hik, hjk⟩ := hthird i j hij
      obtain ⟨s, hs⟩ := hadd k (l + 1)
      have hmapB : (t.d.A i ⊔ t.d.A j).map
          (MulAut.conj (t.y ^ ((s : ℕ)))).toMonoidHom = t.d.A l ⊔ t.d.A (l + 2) := by
        rw [Subgroup.map_sup, t.map_conj_A_pow s i, t.map_conj_A_pow s j]
        rcases hindex i j k s l hij hik hjk hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [h1, h2, sup_comm]
        · rw [h1, h2, sup_comm]
      exact two_le_of_map_conj (p := p) (c.S.M.pow_mem (t.hP.le t.hyP) (s : ℕ))
        hmapB hbound
    ·
      obtain ⟨k, hik, hjk⟩ := hthird i j hij
      obtain ⟨u, huLf, huord, hue⟩ := hu_fact hep heN k (hpLf k)
      have huM : u ∈ c.S.M := (t.hdM ▸ t.d.hLM k) huLf
      have hu_pow : u ^ p = 1 := by
        rw [← huord]
        exact pow_orderOf_eq_one u
      have hu_notmem : u ∉ Subgroup.zpowers e := by
        intro hmem
        have heLf : e ∈ t.d.Lf k := by
          have hEq : Subgroup.zpowers u = Subgroup.zpowers e := by
            refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hmem) ?_
            rw [Nat.card_zpowers, Nat.card_zpowers, huord, hee_ord]
          have he_in : e ∈ Subgroup.zpowers u := by
            rw [hEq]
            exact Subgroup.mem_zpowers _
          exact (Subgroup.zpowers_le.mpr huLf) he_in
        exact hex ⟨k, heLf⟩
      have hcommR : ⁅Subgroup.zpowers e ⊔ Subgroup.zpowers u,
          t.d.A i ⊔ t.d.A j⁆ ≤ CFSG.Open.pCoreOf 2 c.S.M := by
        refine CFSG.GorensteinWalter.commutator_sup_le_of_commutator_le_and_normalize
          (Subgroup.zpowers e) (Subgroup.zpowers u)
          (t.d.A i ⊔ t.d.A j) (CFSG.Open.pCoreOf 2 c.S.M) ?_ ?_ ?_ ?_
        · have hbot : ⁅Subgroup.zpowers e, t.d.A i ⊔ t.d.A j⁆ = ⊥ := by
            rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
            exact (Subgroup.zpowers_le.mpr heC).trans (Subgroup.centralizer_le hBAA)
          rw [hbot]
          exact bot_le
        · exact (Subgroup.commutator_mono (Subgroup.zpowers_le.mpr huLf) le_rfl).trans
            (hcomm_Lf k i j hik hjk)
        · exact (Subgroup.zpowers_le.mpr heM).trans
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M)
        · exact (Subgroup.zpowers_le.mpr huM).trans
            (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 c.S.M)
      exact two_le_of_commuting_pElements (c := c) hp2 heM hee_ord huM huord hue hu_notmem
        (t.d.isElemAbelian_A_sup_A i j).isPGroup hBM hcommR

theorem normalizer_le_of_le_A_sup_A_of_two_le {p : ℕ} (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p) {i j : Fin 3}
    (hij : i ≠ j)
    (h2 : 2 ≤ CFSG.Open.pRank p
      (c.S.M ⊓ Subgroup.centralizer ((t.d.A i ⊔ t.d.A j : Subgroup G) : Set G)))
    {Y : Subgroup G} (hY : Y ≤ t.d.A i ⊔ t.d.A j) (hY1 : Y ≠ ⊥) :
    Subgroup.normalizer (Y : Set G) ≤ c.S.M := by
  have hpp : p.Prime := (c.sig_prime p hp).1
  have : Fact p.Prime := ⟨hpp⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAiLf : ∀ l, t.d.A l ≤ t.d.Lf l := fun l => (t.d.A_le_H l).trans (t.d.H_le_Lf l)
  have hAiM : ∀ l, t.d.A l ≤ c.S.M := fun l => (hAiLf l).trans (t.hdM ▸ t.d.hLM l)
  have hBM : (t.d.A i ⊔ t.d.A j) ≤ c.S.M := sup_le (hAiM i) (hAiM j)
  have hB3 : IsPGroup 3 ↥(t.d.A i ⊔ t.d.A j) := (t.d.isElemAbelian_A_sup_A i j).isPGroup
  have hBr : 2 ≤ CFSG.Open.pRank 3 (t.d.A i ⊔ t.d.A j) := by
    have hcard : Nat.card ↥(t.d.A i ⊔ t.d.A j) = 3 ^ 2 := t.d.card_A_sup_A hij
    exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) le_rfl
      (t.d.isElemAbelian_A_sup_A i j) hcard
  exact
    CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.normalizer_le_of_two_le_pRank_inf_centralizer
      (p := p) (r := 3) (M := c.S.M) (B := t.d.A i ⊔ t.d.A j)
      (c.isStronglyPEmbedded_of_mem_sigma hp) h76 hBM hB3 hBr
      h2 Y hY hY1

structure PairNormalizerLe (p : ℕ) : Prop where
  normalizer_le : ∀ {i j : Fin 3}, i ≠ j → ∀ {Y : Subgroup G}, Y ≤ t.d.A i ⊔ t.d.A j → Y ≠ ⊥ →
    Subgroup.normalizer (Y : Set G) ≤ c.S.M
  dvd_card : ∀ {i j : Fin 3}, i ≠ j →
    p ∣ Nat.card ↥(c.S.M ⊓ Subgroup.centralizer ((t.d.A i ⊔ t.d.A j : Subgroup G) : Set G))

theorem pairNormalizerLe_of_two_le {p : ℕ} (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p)
    (h2 : ∀ {i j : Fin 3}, i ≠ j → 2 ≤ CFSG.Open.pRank p
      (c.S.M ⊓ Subgroup.centralizer ((t.d.A i ⊔ t.d.A j : Subgroup G) : Set G))) :
    t.PairNormalizerLe p where
  normalizer_le hij _ hY hY1 := t.normalizer_le_of_le_A_sup_A_of_two_le hp h76 hij (h2 hij) hY hY1
  dvd_card hij := CFSG.GroupTheory.dvd_card_of_one_le_pRank (c.sig_prime p hp).1 (by
    have h := h2 hij
    omega)

end Neutral

section Full

variable {c : Ctx812 G} (t : CaseTwoTransitive c.toCtx812E)

theorem two_le_pRank_inf_centralizer_A_sup_A {p : ℕ}
    (hp : p ∈ c.sig) {i j : Fin 3} (hij : i ≠ j) :
    2 ≤ CFSG.Open.pRank p
      (c.S.M ⊓ Subgroup.centralizer ((t.d.A i ⊔ t.d.A j : Subgroup G) : Set G)) := by
  classical
  have hpp : p.Prime := (c.sig_prime p hp).1
  have : Fact p.Prime := ⟨hpp⟩
  have h1 : CFSG.Open.pRank p (t.d.Lf 0) ≤ 1 → ∀ l, CFSG.Open.pRank p (t.d.Lf l) ≤ 1 := by
    intro h l
    rw [t.pRank_Lf_eq p l]
    exact h
  by_cases hm0 : CFSG.Open.pRank p (t.d.Lf 0) = 0
  ·
    obtain ⟨T, -, -, -, hTcond⟩ :=
      c.exists_isPGroup_le_centralizer_AA hp t.d t.hdM t.hdL t.hinj t.hperm (h1 (by omega))
    have hbig : 2 ≤ CFSG.Open.pRank p (c.S.M ⊓ Subgroup.centralizer (t.d.AA : Set G)) := by
      by_contra hle
      have hcontr := hTcond (by omega)
      have e1 := t.pRank_Lf_eq p 1
      have e2 := t.pRank_Lf_eq p 2
      have := c.three_le_k
      omega
    have hA_le_AA : ∀ l, t.d.A l ≤ t.d.AA := by
      intro l
      rw [t.d.AA_def]
      fin_cases l
      · exact le_sup_left.trans le_sup_left
      · exact le_sup_right.trans le_sup_left
      · exact le_sup_right
    have hBAA : (t.d.A i ⊔ t.d.A j) ≤ t.d.AA := sup_le (hA_le_AA i) (hA_le_AA j)
    exact hbig.trans (CFSG.SectionRank.pRank_mono hpp.one_lt
      (inf_le_inf_left c.S.M (Subgroup.centralizer_le (fun x hx => hBAA hx))))
  ·
    refine t.two_le_pRank_inf_centralizer_A_sup_A_of_exists hp (by omega) (fun hle => ?_) hij
    obtain ⟨T, hTp, hTne, hTC, -⟩ :=
      c.exists_isPGroup_le_centralizer_AA hp t.d t.hdM t.hdL t.hinj t.hperm (h1 hle)
    have hpdvdT : p ∣ Nat.card ↥T := by
      rcases hTp.card_eq_or_dvd with h | h
      · exact absurd (Subgroup.eq_bot_of_card_eq T h) hTne
      · exact h
    obtain ⟨e, heord⟩ := exists_prime_orderOf_dvd_card' (G := ↥T) p hpdvdT
    refine ⟨(e : G), hTC e.2, ?_⟩
    rw [← Subgroup.orderOf_mk (e : G) e.2]
    simpa using heord

theorem pairNormalizerLe {p : ℕ} (hp : p ∈ c.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 c.S.M p) :
    t.PairNormalizerLe p :=
  t.pairNormalizerLe_of_two_le hp h76 (fun hij => t.two_le_pRank_inf_centralizer_A_sup_A hp hij)

end Full

end CaseTwoTransitive

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

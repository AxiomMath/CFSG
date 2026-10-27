module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3UDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FInner
public import CFSG.LocalAnalysis.UniquenessCase.UCFront07Card
public import CFSG.LocalAnalysis.UniquenessCase.UC6Inst
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3FField
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Alpha
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251h
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.UCFront07CardFour
import CFSG.LocalAnalysis.UniquenessCase.UC22Sec7Three

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r3f_not_dvd_two_pow_add_one {n f r : ℕ} (hn : Odd n) (hr : r.Prime)
    (hr2 : r ≠ 2) (hrn : r ∣ 2 ^ n - 1) : ¬ r ∣ 2 ^ f + 1 := by
  intro hrf
  have h2f : r ∣ 2 ^ (f * 2) - 1 := by
    rw [pow_mul, show (2 ^ f) ^ 2 - 1 = (2 ^ f + 1) * (2 ^ f - 1) by
      rw [← Nat.sq_sub_sq (2 ^ f) 1, one_pow]]
    exact dvd_mul_of_dvd_left hrf _
  have hrq : r ∣ 2 ^ f - 1 :=
    (uc22s2114_dvd_two_pow_gcd_sub_one (d := f) (f := 2) hn ⟨1, rfl⟩ hrn h2f).trans
      (Nat.pow_sub_one_dvd_pow_sub_one 2 (Nat.gcd_dvd_right n f))
  have h2 : r ∣ (2 ^ f + 1) - (2 ^ f - 1) := Nat.dvd_sub hrf hrq
  rw [show (2 ^ f + 1) - (2 ^ f - 1) = 2 by have := Nat.one_le_two_pow (n := f); omega] at h2
  exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)


theorem uc22s2114r3f_false_of_outer (hGA : GriessAllModelsStatement) {D : Data G}
    {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D) (h74 : F07.R74Card D) (hH : H1930 D)
    (c : Ctx21 D Ch) {L : Subgroup G} (hL : L ∈ calC D.M) {m f : ℕ} (hm : m = 6 ∨ m = 7)
    (hX : LieModel (BarInf L) .PSU m 2 f) {b : G} (hbB : b ∈ c.B0)
    (hbL : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr7 : 7 ≤ r)
    (hbr : orderOf b = r) (hrn : r ∣ 2 ^ c.n - 1) (hodd : Odd c.n)
    (hin : inducedBarInfAutHom L ⟨b, hbL⟩ ∉
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) : False := by
  have : Fact r.Prime := ⟨hr⟩
  have hr2 : r ≠ 2 := by omega
  have hbr' : b ^ r = 1 := hbr ▸ pow_orderOf_eq_one b
  have hθr : inducedBarInfAutHom L ⟨b, hbL⟩ ^ r = 1 := by
    rw [← map_pow]
    have : (⟨b, hbL⟩ : ↥(normalizer (L : Set G))) ^ r = 1 := Subtype.ext (by simpa using hbr')
    rw [this, map_one]
  have hrq : ¬ r ∣ 2 ^ f + 1 := uc22s2114r3f_not_dvd_two_pow_add_one hodd hr hr2 hrn
  have hrK := uc22s2114r3f_not_dvd_card_solvableRadical hGA hL hm hX hr hr7
  have hN := uc22s2112r2_normalizer hH c hL.1.le hbB (by rw [hbr]; exact hr)
  obtain ⟨p, hp, hp2, hpf, X, hXp, hXc, hXfix⟩ :=
    uc22s2114r3f_exists_fixed_noncyclic hm hX hr hr2 hrq hθr hin
  have : Fact p.Prime := ⟨hp⟩
  have hbP : IsPGroup r ↥(zpowers b) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbr, pow_one])
  have hC := uc22s2114r3f_two_le_pRank_centralizer (zpowers_le.2 hbL) hbP hrK hp2 hXp hXc
    (uc22s2114r3f_fix_zpowers (X := (X : Set (BarInf L))) hbL hXfix)
  have hpN : 1 < CFSG.Open.pRank p (normalizer ((zpowers b : Subgroup G) : Set G) ⊓ D.M) := by
    have := hC.trans (CFSG.SectionRank.pRank_mono hp.one_lt ((inf_le_inf_left L
      (centralizer_le (Set.singleton_subset_iff.2 (mem_zpowers b)))).trans hN.2.2.2))
    omega
  have hpσ : p ∈ D.sig := hSg.four_mem p hp hp2
    ((uc22s2114r3u_four_le_pRank hGA hL (by omega) hX hp hp2 (fun h => absurd h (by omega))
      hpf).trans (CFSG.SectionRank.pRank_mono hp.one_lt hL.1.le))
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hpσ
  have h74b := h74 p _ ⟨hp, hp2, hsp, hN.1, hN.2.1, hpN⟩
  obtain ⟨q, hq, hq7, hqf, A, _, _, hAq, hAc, κ, hκ, ι, hι, hθι⟩ :=
    uc22s2114r3f_exists_fpf hm hX hr (by omega) hrq hθr hin
  have : Fact q.Prime := ⟨hq⟩
  have hqr : q ≠ r := fun h => hrq (h ▸ hqf)
  obtain ⟨ψ, hψ, hψL, hbψ⟩ := uc22s2114r3f_exists_lift hbL hr hbr hrK
    (uc22s2114r3f_not_dvd_card_solvableRadical hGA hL hm hX hq hq7) hAq ι hι κ hθι
  have h2 := uc22s2114r3f_two_lt_card (D := D) hq (by omega) hr hr2 hqr hAq hAc κ hκ ψ hψ
    (fun a => hL.1.le (hψL a)) (c.hBM hbB) hbr hbψ
  have hle := Subgroup.card_le_of_le (inf_le_inf_left (F07.Q7 D) hN.2.2.1)
  omega

theorem s21_14R3UF_of_inputs (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h76 : F07.R76Sig D) (h74 : F07.R74Card D) : S21_14R3UF D Ch := by
  rintro hH c L hL - - f hf hall - hodd hn3 hBT hBL hfaith
  exfalso
  obtain ⟨m, hm, hX⟩ : ∃ m, (m = 6 ∨ m = 7) ∧ LieModel (BarInf L) .PSU m 2 f :=
    hf.elim (fun h => ⟨6, Or.inl rfl, h⟩) fun h => ⟨7, Or.inr rfl, h⟩
  obtain ⟨r, hr, hrn⟩ := Nat.exists_prime_and_dvd (n := 2 ^ c.n - 1) (by
    have : 2 ^ 3 ≤ 2 ^ c.n := Nat.pow_le_pow_right (by norm_num) hn3
    omega)
  have : Fact r.Prime := ⟨hr⟩
  have hrf := hall r hr hrn
  have h3n : ¬ 3 ∣ 2 ^ c.n - 1 := fun h =>
    uc22s2114_not_dvd_of_odd (f := 2) hodd ⟨1, by norm_num⟩ Nat.prime_three h (by norm_num)
  have hr7 := P2251h.seven_le_of_dvd_two_pow_sub_one (by omega) h3n hr hrn
  have hrB : r ∣ Nat.card c.B0 := by
    have h : r ∈ piSet c.B0 := by
      rw [c.hpi]
      exact ⟨hr, hrn⟩
    exact h.2
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' r hrB
  have hbr : orderOf (b : G) = r := by rw [Subgroup.orderOf_coe, hb]
  have hb1 : inducedBarInfAutHom L ⟨b, hBL b.2⟩ ≠ 1 := fun h1 => by
    have h := uc22s2114_eq_one_of_inducedBarInfAutHom_eq_one hL hBL hfaith b.2 h1
    rw [← Subgroup.orderOf_coe, h, orderOf_one] at hb
    exact hr.ne_one hb.symm
  by_cases hin : inducedBarInfAutHom L ⟨b, hBL b.2⟩ ∈
      (MulAut.conj : BarInf L →* MulAut (BarInf L)).range
  · exact uc22s2114r3f_false_of_inner hGA hSg h76 hH c hL hm hX b.2 (hBL b.2) (hBT b.2) hr hr7
      hbr hrn hodd hrf hb1 hin
  · exact uc22s2114r3f_false_of_outer hGA hSg h74 hH c hL hm hX b.2 (hBL b.2) hr hr7 hbr hrn
      hodd hin

open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt) in
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedThree BadNoStrongThree c76Three_of_inputs) in
theorem s21_14R3UF_dataOfSetup4 (hGA : GriessAllModelsStatement) (hSE : StronglyEmbeddedFive)
    (hK3 : StronglyEmbeddedThree) (hB3 : BadNoStrongThree) (hS : Standing4 G)
    (hU : CFSG.Open.uniqueFourUnique G) (S : Setup4 G) (hMS : S.InMSigma) (hPart : PartIAt S.M)
    {Ch : Choice2011 G} : S21_14R3UF (UC6.dataOfSetup4 hS hU S) Ch := by
  have hC76 := c76Three_of_inputs hSE hK3 hB3 hS hU S
  have h76 : F07.R76Sig (UC6.dataOfSetup4 hS hU S) := fun p hp _ hsp => by
    by_cases h3 : 3 ∈ CFSG.Open.uniqueFourBeta G
    · exact hC76 hMS h3 p hp hsp
    · exact UC6.conclusion76_dataOfSetup4 hSE hS hU S h3 hp hsp
  exact s21_14R3UF_of_inputs hGA (UC6S846.sigmaStd_dataOfSetup4 hS hU S) h76
    (F07.r74Card_dataOfSetup4 hSE hK3 hB3 hS hU S hMS hPart.1)

end CFSG.LocalAnalysis.UniquenessCase.UC22

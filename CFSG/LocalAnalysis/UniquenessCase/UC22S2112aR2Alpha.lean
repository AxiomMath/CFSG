module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC6S9
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem uc22s2112r2_false_of_kf7 {D : Data G} (hKF7 : KF7Use D) {p : ℕ} (hpσ : p ∈ D.sig)
    (hM : IsStronglyPEmbedded p D.M) {H : Subgroup G} (hHne : H ≠ ⊤) (hHM : ¬ H ≤ D.M)
    (hrank : 2 ≤ Open.pRank p (H ⊓ D.M)) {D0 : Subgroup G} (hD0 : D0 ≤ H ⊓ D.M)
    (hD0perf : ⁅D0, D0⁆ = D0) {S : Type} [Group S] [IsSimpleGroup S]
    (hSns : ¬ Group.IsSolvable S) (f0 : ↥D0 →* S) (hf0 : Function.Surjective f0)
    (hpS : p ∣ Nat.card S) (h5 : p = 5 → ¬ IsAlt S 5) : False := by
  classical
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  haveI : Fact p.Prime := ⟨hp⟩
  have hD0H : D0 ≤ H := hD0.trans inf_le_left
  have hKF := hKF7 p hpσ H ⟨hp, hp2, hM, hHne, hHM, by omega⟩
  let ψ : ↥D0 →* F07.QuotK7 p H :=
    (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)).comp (Subgroup.inclusion hD0H)
  let J : Subgroup ↥D0 := (CFSG.pPrimeCore p ↥H).comap (Subgroup.inclusion hD0H)
  have hJn : J.Normal := CFSG.pPrimeCore_normal.comap _
  have hψJ : ψ.ker = J := by
    ext x
    show ψ x = 1 ↔ Subgroup.inclusion hD0H x ∈ CFSG.pPrimeCore p ↥H
    exact QuotientGroup.eq_one_iff (Subgroup.inclusion hD0H x)
  have hJcard : Nat.card J ∣ Nat.card (CFSG.pPrimeCore p ↥H) :=
    Subgroup.card_comap_dvd_of_injective _ (Subgroup.inclusion hD0H)
      (Subgroup.inclusion_injective hD0H)
  have hpI : ¬ p ∣ Nat.card (CFSG.pPrimeCore p ↥H) :=
    (hp.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := p))
  haveI : (J.map f0).Normal := hJn.map f0 hf0
  have hker : ψ.ker ≤ f0.ker := by
    rw [hψJ]
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (J.map f0) with hbot | htop
    · intro x hx
      have h := Subgroup.mem_map_of_mem f0 hx
      rw [hbot] at h
      exact MonoidHom.mem_ker.2 (Subgroup.mem_bot.1 h)
    · exfalso
      have hsurj : Function.Surjective (f0.comp J.subtype) := by
        intro s
        have hs : s ∈ J.map f0 := by
          rw [htop]
          exact Subgroup.mem_top s
        obtain ⟨j, hj, hjs⟩ := Subgroup.mem_map.1 hs
        exact ⟨⟨j, hj⟩, hjs⟩
      exact hpI (hpS.trans ((Subgroup.card_dvd_of_surjective hsurj).trans hJcard))
  have hYle : ψ.range ≤
      ((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H)) := by
    rintro _ ⟨x, rfl⟩
    have hx : Subgroup.inclusion hD0H x ∈ (H ⊓ D.M).subgroupOf H :=
      Subgroup.mem_subgroupOf.mpr (hD0 x.2)
    exact Subgroup.mem_map_of_mem _ hx
  haveI : Group.IsPerfect ↥D0 := Subgroup.isPerfect_iff.mpr hD0perf
  have hrs : Function.Surjective ψ.rangeRestrict := MonoidHom.rangeRestrict_surjective ψ
  have hYperf : ⁅ψ.range, ψ.range⁆ = ψ.range :=
    Subgroup.isPerfect_iff.mp (Group.IsPerfect.ofSurjective (f := ψ.rangeRestrict) hrs)
  have hker' : ψ.rangeRestrict.ker ≤ f0.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact hker
  let φY : ↥ψ.range →* S := ψ.rangeRestrict.liftOfRightInverse (Function.surjInv hrs)
    (Function.rightInverse_surjInv hrs) ⟨f0, hker'⟩
  have hφY : Function.Surjective φY := by
    intro s
    obtain ⟨x, rfl⟩ := hf0 s
    exact ⟨ψ.rangeRestrict x, MonoidHom.liftOfRightInverse_comp_apply ψ.rangeRestrict
      (Function.surjInv hrs) (Function.rightInverse_surjInv hrs) ⟨f0, hker'⟩ x⟩
  rcases hKF with hsolv | ⟨hp5, hquot⟩
  · haveI : Group.IsSolvable
        ↥(((H ⊓ D.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) := hsolv
    haveI : Group.IsSolvable ↥ψ.range :=
      Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hYle)
        (Subgroup.inclusion_injective hYle)
    exact hSns (Group.isSolvable_of_surjective hφY)
  · exact h5 hp5 (hquot ψ.range hYle hYperf S inferInstance φY hφY)

theorem uc22s2112r2_normalizer {D : Data G} {Ch : Choice2011 G} (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hLM : L ≤ D.M) {b : G} (hbB : b ∈ c.B0) (hb : (orderOf b).Prime) :
    normalizer ((zpowers b : Subgroup G) : Set G) ≠ ⊤ ∧
      ¬ normalizer ((zpowers b : Subgroup G) : Set G) ≤ D.M ∧
      centralizer ({b} : Set G) ≤ normalizer ((zpowers b : Subgroup G) : Set G) ∧
      L ⊓ centralizer ({b} : Set G) ≤ normalizer ((zpowers b : Subgroup G) : Set G) ⊓ D.M := by
  have hCN : centralizer ({b} : Set G) ≤ normalizer ((zpowers b : Subgroup G) : Set G) := by
    have h : centralizer ({b} : Set G) ≤ centralizer ((zpowers b : Subgroup G) : Set G) := by
      rw [zpowers_eq_closure, centralizer_closure]
    exact h.trans (centralizer_le_normalizer _)
  let c₀ : Ctx21 D Ch := { c with B := c.B0, hB := c.hB0, hle := le_rfl }
  exact ⟨UC6.normalizer_ne_top_of_card_prime_uc6 D.standing.simple D.standing.nonab hb
      (by rw [Nat.card_zpowers]), s21_2 D Ch hH c₀ (zpowers b) (zpowers_le.2 hbB), hCN,
    le_inf (inf_le_right.trans hCN) (inf_le_left.trans hLM)⟩

theorem uc22s2112r2_alpha (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hH : H1930 D) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hX : LieModel (BarInf L) .PSL 2 p f) {b : G} (hbB : b ∈ c.B0)
    (hb : b ∈ normalizer (L : Set G)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r)
    (hθ : inducedBarInfAutHom L ⟨b, hb⟩ ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range)
    (hfr : 2 ≤ f / r) : False := by
  have hp : p.Prime := Fact.out
  obtain ⟨hrf, hfL, hfC, hD0⟩ := uc22s2112r2_setup hGA hL hp2 hX hb hr hr2 hbr hθ
  have hr3 : 3 ≤ r := by
    have := hr.two_le
    omega
  have hf6 : 6 ≤ f := by
    obtain ⟨k, hk⟩ := hrf
    have hk2 : 2 ≤ k := by rwa [hk, Nat.mul_div_cancel_left _ hr.pos] at hfr
    rw [hk]
    nlinarith
  have hM4 : 4 ≤ Open.pRank p D.M := by
    obtain ⟨E, hEL, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hfL
    have := UC6S846.le_pRank' hp (hEL.trans hL.1.le) hEel hEc
    omega
  have hpσ : p ∈ D.sig := hσ.four_mem p hp hp2 hM4
  have hMs : IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hσ (UC6S846.not_solvable_of_mem_calC hL) hpσ
  obtain ⟨hHne, hHM, -, hCH⟩ := uc22s2112r2_normalizer hH c hL.1.le hbB (hbr ▸ hr)
  have hrank : 2 ≤ Open.pRank p (normalizer ((zpowers b : Subgroup G) : Set G) ⊓ D.M) := by
    obtain ⟨E, hEC, hEel, hEc⟩ :=
      UC6S846.exists_elemAbelian_card_of_le_pRank hp (hfr.trans hfC)
    exact UC6S846.le_pRank' hp (hEC.trans hCH) hEel hEc
  have hq9 : 9 ≤ p ^ (f / r) := by
    have hp3 : 3 ≤ p := by
      have := hp.two_le
      omega
    calc 9 = 3 ^ 2 := by norm_num
      _ ≤ p ^ 2 := Nat.pow_le_pow_left hp3 2
      _ ≤ p ^ (f / r) := Nat.pow_le_pow_right hp.pos hfr
  obtain ⟨D0, hD0C, hD0perf, f0, hf0⟩ := hD0 (by omega)
  obtain ⟨hS, hSns, -, hpS⟩ := uc22s2112r2_psl2_facts (k := f / r) hp2 (by omega) (by omega)
  haveI := hS
  refine uc22s2112r2_false_of_kf7 hKF7 hpσ hMs hHne hHM hrank (hD0C.trans hCH) hD0perf hSns
    f0 hf0 ((dvd_pow_self p (by omega)).trans hpS) ?_
  rintro rfl ⟨e⟩
  have h25 := (Nat.pow_dvd_pow 5 hfr).trans hpS
  have h60 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  rw [Nat.card_congr e.toEquiv, h60] at h25
  norm_num at h25

end CFSG.LocalAnalysis.UniquenessCase.UC22

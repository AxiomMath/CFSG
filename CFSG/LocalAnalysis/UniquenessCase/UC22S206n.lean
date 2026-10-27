module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S206h
import CFSG.LocalAnalysis.RankThreeUC.AGL81S15LiftA
import CFSG.LocalAnalysis.UniquenessCase.UC22S206i
import CFSG.LocalAnalysis.UniquenessCase.UC22S206j
import CFSG.LocalAnalysis.UniquenessCase.UC22S206l
import CFSG.LocalAnalysis.UniquenessCase.UC22S206m

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup CFSG.Open
open CFSG.Quasithin.H13.A7Blk (ptPre ptCore ptCore_le_ptPre ptHom)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G]

theorem uc22s206n_false [Finite G] (hU : uniqueFourUnique G) {M L : Subgroup G}
    (hM : uniqueFourIsMaxTwoLocal M)
    (hchar : M ⊓ centralizer (CFSG.Open.pCoreOf 2 M : Set G) ≤ CFSG.Open.pCoreOf 2 M)
    (α : ↥L →* alternatingGroup (Fin 9)) (hα : Function.Surjective α)
    (hker : α.ker = CFSG.pCore 2 ↥L) {i : Fin 9} (hLM : L ⊓ M = ptPre α i)
    (hN : ∃ J : Subgroup (Bar2 M), IsComponentOf J ⊤ ∧
      ¬ ((ptCore α i).subgroupOf M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥M)) ≤
        normalizer (J : Set (Bar2 M)))
    (h74 : ∀ p : ℕ, p ∈ uniqueFourSigma M → IsStronglyPEmbedded p M → 5 ≤ p →
      ∀ Y : Subgroup G, Y ≠ ⊥ → Y ≤ M →
        2 ≤ CFSG.Open.pRank p (M ⊓ normalizer (Y : Set G)) →
        CFSG.Open.pCoreOf 2 M ⊓ normalizer (Y : Set G) ≠ ⊥ → normalizer (Y : Set G) ≤ M) :
    False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKM : ptCore α i ≤ M := by
    refine (ptCore_le_ptPre α i).trans ?_
    rw [← hLM]
    exact inf_le_right
  set φ : ↥(ptCore α i) →* Bar2 M :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥M)).comp (Subgroup.inclusion hKM)
  obtain ⟨x, y, hx, hy, hx3, hy7, hxy, -⟩ := uc22s206g_lift α hα hker i φ (uc22s206l_ker_le hKM)
  have hy1 : ptHom α i y ≠ 1 := by
    rw [hy]
    intro h
    have h1 : uc22s206dY0 = 1 := uc22s206gEmb_injective i (h.trans (map_one _).symm)
    have h7 := uc22s206d_orderOf_Y0
    rw [h1, orderOf_one] at h7
    omega
  obtain ⟨J₀, hJ₀, hKJ₀⟩ := hN
  obtain ⟨J, hJ, hyJ⟩ := uc22s206l_exists_not_normalizer_bar α hα hker hKM hy1 hJ₀ hKJ₀
  obtain ⟨r, hr, hr2, hrJ⟩ :=
    CFSG.LocalAnalysis.RankThreeUC.S15.perfect_le_normalizer_component_aux1 hJ.2.2
  haveI : Fact r.Prime := ⟨hr⟩
  have hx3' : φ x ^ 3 = 1 := by rw [← map_pow, ← hx3, pow_orderOf_eq_one, map_one]
  have hy7' : φ y ^ 7 = 1 := by rw [← map_pow, ← hy7, pow_orderOf_eq_one, map_one]
  have hxy' : φ x * φ y * (φ x)⁻¹ = φ y ^ 2 := by
    rw [← map_inv, ← map_mul, ← map_mul, hxy, map_pow]
  obtain ⟨h7r, ⟨D, hD, hxD, hDx⟩, E', hE'C, hE', hE'card⟩ :=
    uc22s206m_diag hx3' hy7' hxy' hJ hyJ hr hr2 hrJ
  have hN2 : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥M) := by
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥M)).exists_card_eq
    rw [hk]
    intro hd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).mp (hr.dvd_of_dvd_pow hd))
  have h3r : 3 < CFSG.Open.pRank r M := by
    have h1 := CFSG.SectionRank.pRank_quotient_eq (p := r) (CFSG.pCore 2 ↥M) hN2
    have h2 := CFSG.SectionRank.pRank_le_map hr.one_lt M.subtype M.subtype_injective ⊤
    rw [← MonoidHom.range_eq_map, Subgroup.range_subtype] at h2
    exact lt_of_lt_of_le (lt_of_lt_of_le (by norm_num) (h7r.trans h1.le)) h2
  obtain ⟨hσ, hsp, hp3, -⟩ := uc22s206g_coprime hU hM α hα hLM hr hr2 h3r
  have hcharM : centralizer (CFSG.pCore 2 ↥M : Set ↥M) ≤ CFSG.pCore 2 ↥M := by
    intro m hm
    have hmG : (m : G) ∈ M ⊓ centralizer (CFSG.Open.pCoreOf 2 M : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨m.2, mem_centralizer_iff.mpr ?_⟩
      rintro _ ⟨q, hq, rfl⟩
      exact congrArg Subtype.val (mem_centralizer_iff.mp hm q hq)
    obtain ⟨q, hq, hqm⟩ := hchar hmG
    rwa [show q = m from Subtype.ext hqm] at hq
  have hxM3 : orderOf (Subgroup.inclusion hKM x) = 3 := by
    rw [orderOf_injective _ (Subgroup.inclusion_injective hKM) x, hx3]
  have hne := uc22s206j_inf_centralizer_ne_bot hcharM hr hr2 hp3 hxM3 hD hxD hDx
  have hQ : CFSG.Open.pCoreOf 2 M ⊓ centralizer (zpowers (x : G) : Set G) ≠ ⊥ := by
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨((z : ↥M) : G), Subgroup.mem_inf.mpr
      ⟨⟨z, (Subgroup.mem_inf.mp z.2).1, rfl⟩, mem_centralizer_iff.mpr fun s hs => ?_⟩⟩, ?_⟩
    · obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hs
      have hc := congrArg Subtype.val (mem_centralizer_iff.mp (Subgroup.mem_inf.mp z.2).2
        (Subgroup.inclusion hKM x ^ k) (zpow_mem_zpowers _ k))
      simpa using hc
    · intro h1
      have h2 : ((z : ↥M) : G) = 1 := congrArg Subtype.val h1
      exact hz1 (Subtype.ext (Subtype.ext h2))
  have hxM3' : Subgroup.inclusion hKM x ^ 3 = 1 := by
    rw [← hxM3]
    exact pow_orderOf_eq_one _
  obtain ⟨E, hEC, hE, hEcard⟩ := uc22s206i_lift hxM3' hr hr2 hE' hE'card hE'C
  have hrank : 2 ≤ CFSG.Open.pRank r (M ⊓ centralizer (zpowers (x : G) : Set G)) := by
    refine CFSG.SectionRank.le_pRank hr.one_lt (E := E.map M.subtype) ?_ (hE.map M.subtype) ?_
    · rintro _ ⟨m, hm, rfl⟩
      refine Subgroup.mem_inf.mpr ⟨m.2, mem_centralizer_iff.mpr ?_⟩
      intro s hs
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hs
      have hc := congrArg Subtype.val
        (mem_centralizer_iff.mp (hEC hm) (Subgroup.inclusion hKM x ^ k) (zpow_mem_zpowers _ k))
      simpa using hc
    · rw [Subgroup.card_map_of_injective M.subtype_injective, hEcard]
  have hCN : centralizer (zpowers (x : G) : Set G) ≤ normalizer (zpowers (x : G) : Set G) :=
    centralizer_le_normalizer _
  have hx1 : (x : G) ≠ 1 := by
    intro h
    rw [show x = 1 from Subtype.ext h, orderOf_one] at hx3
    omega
  have hNx := h74 r hσ hsp (Nat.Prime.five_le_of_ne_two_of_ne_three hr hr2 hp3)
    (zpowers (x : G)) (by rw [Ne, zpowers_eq_bot]; exact hx1) (zpowers_le.mpr (hKM x.2))
    (hrank.trans (CFSG.SectionRank.pRank_mono hr.one_lt (inf_le_inf_left _ hCN)))
    (fun hbot => hQ (eq_bot_iff.mpr ((inf_le_inf_left _ hCN).trans (eq_bot_iff.mp hbot))))
  exact uc22s206h_normalizer_not_le α hα hker hLM hx hx3 hNx

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

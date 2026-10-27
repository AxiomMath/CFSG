module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UseS5
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
import CFSG.LocalAnalysis.UniquenessCase.UCFront07Use
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.SectionRank.PRankIndex

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
  (StronglyEmbeddedFive StronglyEmbeddedSolvable Sec7Core4 five_le_of_mem_uniqueFourSigma)

variable {G : Type} [Group G] [Finite G]

namespace R869S

theorem perfect_of_isProdOfCalC {M L : Subgroup G} (h : F08.IsProdOfCalC M L) : ⁅L, L⁆ = L := by
  obtain ⟨k, S, hS, hL⟩ := h
  have hpair : ∀ A ∈ List.ofFn S, ∀ B ∈ List.ofFn S, A ≤ normalizer (B : Set G) := by
    intro A hA B hB
    obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
    obtain ⟨j, rfl⟩ := List.mem_ofFn.1 hB
    by_cases hij : S j = S i
    · rw [hij]
      exact Subgroup.le_normalizer
    · exact uc22p22u_calC_normalizes (hS j) (hS i) hij
  have hLeq : L = ⨆ A ∈ List.ofFn S, A := by
    apply SetLike.coe_injective
    rw [hL, ← uc22p22u_prod_list_eq_iSup _ hpair, List.map_ofFn]
    rfl
  have hle : ∀ A ∈ List.ofFn S, A ≤ L := fun A hA => by
    rw [hLeq]
    exact le_iSup₂ (f := fun A (_ : A ∈ List.ofFn S) => A) A hA
  refine le_antisymm (CFSG.Quasithin.A3.commutator_self_le L) ?_
  calc L = ⨆ A ∈ List.ofFn S, A := hLeq
    _ ≤ ⁅L, L⁆ := iSup₂_le fun A hA => by
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hA
      calc S i = ⁅S i, S i⁆ := (hS i).2.1.symm
        _ ≤ ⁅L, L⁆ := Subgroup.commutator_mono (hle _ hA) (hle _ hA)

theorem map_subgroupOf_eq_top {L Y : Subgroup G} (hYL : Y ≤ L) (hY : Y ⊔ pCoreOf 2 L = L) :
    (Y.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
  have h1 : Y.subgroupOf L ⊔ CFSG.pCore 2 ↥L = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_sup, Subgroup.subgroupOf_map_subtype, inf_of_le_left hYL,
      ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hY
  have h2 := congrArg (Subgroup.map (QuotientGroup.mk' (CFSG.pCore 2 ↥L))) h1
  rwa [Subgroup.map_sup, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _),
    (Subgroup.map_eq_bot_iff _).2 (QuotientGroup.ker_mk' _).ge, sup_bot_eq] at h2

theorem bar2_perfect {L : Subgroup G} (hL : ⁅L, L⁆ = L) :
    ⁅(⊤ : Subgroup (Bar2 L)), (⊤ : Subgroup (Bar2 L))⁆ = ⊤ := by
  have h1 : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := by
    apply Subgroup.map_injective L.subtype_injective
    rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype, hL]
  have h2 := Subgroup.map_commutator (⊤ : Subgroup ↥L) ⊤ (QuotientGroup.mk' (CFSG.pCore 2 ↥L))
  rw [h1, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
  exact h2.symm

theorem dvd_card_bar2 {L : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (h : 1 ≤ CFSG.Open.pRank p L) : p ∣ Nat.card (Bar2 L) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨E, hEL, -, hcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt L
  have h1 : p ∣ Nat.card L := by
    have hE : p ∣ Nat.card E := by
      rw [hcard]
      exact dvd_pow_self p (by omega)
    exact hE.trans (Subgroup.card_dvd_of_le hEL)
  obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L), ha] at h1
  rcases (Nat.Prime.dvd_mul hp).1 h1 with h3 | h3
  · exact h3
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h3)) hp2

theorem pRank_le_of_sup_pCore {L Y : Subgroup G} (hYL : Y ≤ L) (hY : Y ⊔ pCoreOf 2 L = L)
    {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) : CFSG.Open.pRank p L ≤ CFSG.Open.pRank p Y := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hnot : ¬ p ∣ (Y.subgroupOf L).index := by
    intro hd
    have h1 : Nat.card (Bar2 L) ∣ Nat.card (Y.subgroupOf L) := by
      rw [← Subgroup.card_top (G := Bar2 L), ← map_subgroupOf_eq_top hYL hY]
      exact Subgroup.card_map_dvd _ _
    obtain ⟨c, hc⟩ := h1
    obtain ⟨a, ha⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥L)).exists_card_eq
    have h2 := Subgroup.card_mul_index (Y.subgroupOf L)
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L), ha, hc] at h2
    have h3 : c * (Y.subgroupOf L).index = 2 ^ a := by
      refine Nat.eq_of_mul_eq_mul_left (Nat.card_pos (α := Bar2 L)) ?_
      rw [← mul_assoc]
      exact h2
    have h4 : p ∣ 2 ^ a := by
      rw [← h3]
      exact hd.mul_left c
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h4))
  have h1 := CFSG.SectionRank.pRank_top_le_of_not_dvd_index hp (Y.subgroupOf L) hnot
  rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L] at h1
  have h2 : CFSG.Open.pRank p (Y.subgroupOf L) = CFSG.Open.pRank p Y := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (Y.subgroupOf L),
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup Y]
    exact CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (Subgroup.subgroupOfEquivOfLe hYL)
  rwa [h2] at h1

theorem card_bar2_dvd {L Y H : Subgroup G} (hYL : Y ≤ L) (hYH : Y ≤ H)
    (hY : Y ⊔ pCoreOf 2 L = L) (hLperf : ⁅L, L⁆ = L) (N : Subgroup ↥H) [N.Normal] :
    Nat.card (Bar2 L) ∣
      Nat.card (CFSG.Quasithin.perfectCore ((Y.subgroupOf H).map (QuotientGroup.mk' N))) *
        Nat.card N := by
  have hL : Nat.card (Bar2 L) ∣ Nat.card (CFSG.Quasithin.perfectCore Y) := by
    have h1 : (CFSG.Quasithin.perfectCore (Y.subgroupOf L)).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = ⊤ := by
      rw [CFSG.Quasithin.map_perfectCore, map_subgroupOf_eq_top hYL hY,
        CFSG.Quasithin.perfectCore_eq_self_of_perfect (bar2_perfect hLperf)]
    have h2 : Nat.card (CFSG.Quasithin.perfectCore (Y.subgroupOf L)) =
        Nat.card (CFSG.Quasithin.perfectCore Y) := by
      rw [← Subgroup.card_map_of_injective L.subtype_injective, CFSG.Quasithin.map_perfectCore,
        Subgroup.subgroupOf_map_subtype, inf_of_le_left hYL]
    rw [← h2, ← Subgroup.card_top (G := Bar2 L), ← h1]
    exact Subgroup.card_map_dvd _ _
  have hQY : Nat.card (CFSG.Quasithin.perfectCore (Y.subgroupOf H)) =
      Nat.card (CFSG.Quasithin.perfectCore Y) := by
    rw [← Subgroup.card_map_of_injective H.subtype_injective, CFSG.Quasithin.map_perfectCore,
      Subgroup.subgroupOf_map_subtype, inf_of_le_left hYH]
  let f : ↥(CFSG.Quasithin.perfectCore (Y.subgroupOf H)) →* ↥H ⧸ N :=
    (QuotientGroup.mk' N).comp (CFSG.Quasithin.perfectCore (Y.subgroupOf H)).subtype
  have hrange : f.range =
      CFSG.Quasithin.perfectCore ((Y.subgroupOf H).map (QuotientGroup.mk' N)) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, CFSG.Quasithin.map_perfectCore]
  have hker : Nat.card f.ker ∣ Nat.card N := by
    have hle : f.ker.map (CFSG.Quasithin.perfectCore (Y.subgroupOf H)).subtype ≤ N := by
      rintro _ ⟨x, hx, rfl⟩
      have h1 : (QuotientGroup.mk' N) (x : ↥H) = 1 := hx
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    rw [← Subgroup.card_map_of_injective
      (CFSG.Quasithin.perfectCore (Y.subgroupOf H)).subtype_injective]
    exact Subgroup.card_dvd_of_le hle
  have hcard := Subgroup.card_ker_mul_card_range f
  rw [hrange, hQY] at hcard
  rw [← hcard] at hL
  exact hL.trans ((Nat.mul_dvd_mul hker (dvd_refl _)).trans (Nat.mul_comm _ _).dvd)

end R869S

theorem r869NS5_dataOfSetup4 (hSS : StronglyEmbeddedSolvable) (hSE : StronglyEmbeddedFive)
    (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) (h3 : 3 ∉ uniqueFourBeta G) :
    F08.R869NS5 (dataOfSetup4 hS hU S) := by
  rintro L hLM hML hprod ⟨p, hp, h2, h5⟩ r hr hr2 A hAM hAr hY
  have hpp : p.Prime := hp.1.1
  have hp2 : p ≠ 2 := hp.1.2.1
  haveI : Fact p.Prime := ⟨hpp⟩
  have hLperf := R869S.perfect_of_isProdOfCalC hprod
  have hL1 : L ≠ ⊥ := by
    rintro rfl
    obtain ⟨E, hE, -, hcard⟩ := CFSG.SectionRank.exists_pRank hpp.one_lt (⊥ : Subgroup G)
    rw [le_bot_iff.1 hE, Subgroup.card_bot] at hcard
    have := Nat.one_lt_pow (by omega : CFSG.Open.pRank p (⊥ : Subgroup G) ≠ 0) hpp.one_lt
    omega
  have hns : ¬ Group.IsSolvable ↥(dataOfSetup4 hS hU S).M := by
    intro hs
    have hsL : Group.IsSolvable ↥L :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hLM)
    rw [CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot,
      CFSG.Quasithin.perfectCore_eq_self_of_perfect hLperf] at hsL
    exact hL1 hsL
  have hsp := UC6S846.sp_of_mem_sig (UC6S846.sigmaStd_dataOfSetup4 hS hU S) hns hp
  let k : Sec7Core4 G := Sec7Core4.ofSetup4 hS hU S hp hsp h3
  by_contra hHM
  have hYL : L ⊓ centralizer (A : Set G) ≤ L := inf_le_left
  have hYH : L ⊓ centralizer (A : Set G) ≤ normalizer (A : Set G) :=
    inf_le_right.trans (Subgroup.centralizer_le_normalizer _)
  have hYM : L ⊓ centralizer (A : Set G) ≤ k.M := hYL.trans hLM
  have hrank : 2 ≤ CFSG.Open.pRank k.p (normalizer (A : Set G) ⊓ k.M) :=
    h2.trans ((R869S.pRank_le_of_sup_pCore hYL hY hpp hp2).trans
      (CFSG.SectionRank.pRank_mono hpp.one_lt (le_inf hYH hYM)))
  have htop : normalizer (A : Set G) ≠ ⊤ := by
    intro htop
    haveI : A.Normal := Subgroup.normalizer_eq_top_iff.1 htop
    haveI := hS.simple
    rcases (inferInstance : A.Normal).eq_bot_or_eq_top with h | h
    · rw [h, Subgroup.card_bot] at hAr
      exact hr.one_lt.ne hAr
    · exact hHM (le_top.trans (h ▸ hAM))
  have hConf : k.Config (normalizer (A : Set G)) := ⟨htop, hHM, hrank⟩
  have hdvd := R869S.card_bar2_dvd hYL hYH hY hLperf
    (CFSG.pPrimeCore k.p ↥(normalizer (A : Set G)))
  have hYN : ((L ⊓ centralizer (A : Set G)).subgroupOf (normalizer (A : Set G))).map
      (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥(normalizer (A : Set G)))) ≤
      ((normalizer (A : Set G) ⊓ k.M).subgroupOf (normalizer (A : Set G))).map
        (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥(normalizer (A : Set G)))) :=
    Subgroup.map_mono (Subgroup.comap_mono (le_inf hYH hYM))
  have h5k : 5 ≤ k.p := five_le_of_mem_uniqueFourSigma hp h3
  rcases k.solvable_or_of_stronglyEmbeddedSolvable h5k h3 hConf (k.step75 h5k hSE) hSS with
    hsol | ⟨hp5, -, hle⟩
  ·
    haveI : Group.IsSolvable ↥(((normalizer (A : Set G) ⊓ k.M).subgroupOf
        (normalizer (A : Set G))).map
          (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥(normalizer (A : Set G))))) := hsol
    have hsY : Group.IsSolvable ↥(((L ⊓ centralizer (A : Set G)).subgroupOf
        (normalizer (A : Set G))).map
          (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥(normalizer (A : Set G))))) :=
      Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective hYN)
    rw [CFSG.Quasithin.isSolvable_iff_perfectCore_eq_bot] at hsY
    rw [hsY, Subgroup.card_bot, one_mul] at hdvd
    exact (Nat.Prime.coprime_iff_not_dvd hpp).1
      (CFSG.pPrimeCore_coprime_card (p := p) (G := ↥(normalizer (A : Set G))))
      ((R869S.dvd_card_bar2 hpp hp2 (by omega)).trans hdvd)
  ·
    have hodd := k.odd_card_pPrimeCore_of_not_le hHM hrank
    have h12 := (Nat.Coprime.pow_left 12 hodd.coprime_two_left).dvd_of_dvd_mul_right
      ((h5 hp5).trans hdvd)
    have hle' := hle _ ((CFSG.Quasithin.perfectCore_le _).trans hYN)
      (CFSG.Quasithin.perfectCore_perfect _)
    have h4096 := Nat.le_of_dvd Nat.card_pos h12
    norm_num at h4096
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC6

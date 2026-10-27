module

public import CFSG.LocalAnalysis.UniquenessCase.UC6S898i
public import CFSG.LocalAnalysis.UniquenessCase.UCKP898G
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22S219R898
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229G898
import CFSG.LocalAnalysis.StronglyEmbedded.PSubgroups
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem r898GammaPrint_of_r76Sig (D : Data G) (hSg : UC6S846.SigmaStd D) (hCen : UCK.U3Center)
    (hTor : UCK.U3Fix3FieldTorus) (h76 : F07.R76Sig D) : UC6S898.R898GammaPrint D := by
  refine ⟨fun L hL hX X hXL hXc h7 E hEL hEel hEc =>
    uc22s219r_gamma_three D hSg hCen h76 hL hX hXL hXc h7 hEL hEel hEc, ?_⟩
  intro L hL hX X hXL hXc h7 y hy hy7 hαni
  classical
  have hLM : L ≤ D.M := hL.1.le
  have hα7 : (UC6S846.rhoL L ⟨y, hy⟩) ^ 7 = 1 := by
    rw [← map_pow]
    have : (⟨y, hy⟩ : ↥(normalizer (L : Set G))) ^ 7 = 1 :=
      Subtype.ext (by simpa using (hy7 ▸ pow_orderOf_eq_one y))
    rw [this, map_one]
  obtain ⟨Eb, hEbel, hEbc, hEbfix, hP⟩ := hTor (Bar2 L) hX _ hα7 hαni
  have hYN : Subgroup.zpowers y ≤ normalizer (L : Set G) := Subgroup.zpowers_le.2 hy
  have hYpg : IsPGroup 7 ↥(Subgroup.zpowers y) :=
    IsPGroup.of_card (n := 1) (by rw [pow_one, Nat.card_zpowers, hy7])
  have hYgen : ∀ b ∈ Subgroup.zpowers y, ∃ k : ℕ, y ^ k = b := fun b hb =>
    (Submonoid.mem_powers_iff _ _).1 (mem_powers_iff_mem_zpowers.2 hb)
  obtain ⟨E, hEL, hEcent, hEπ, hEcard, hEel⟩ := UC6S898.exists_lift_fixed (B := Subgroup.zpowers y)
    (ℓ := 7) (q := 3) (by norm_num) (by norm_num) Nat.prime_three (by norm_num) hYN hYpg Eb
    hEbel.isPGroup (UC6S898.rho_fix_of_generator hy hYN hYgen hEbfix)
  have hEel' : IsElemAbelian 3 E := hEel hEbel
  have hEc' : Nat.card E = 3 ^ 2 := hEcard.trans hEbc
  have hEy : E ≤ centralizer ({y} : Set G) :=
    hEcent.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.2 (Subgroup.mem_zpowers y)))
  refine ⟨E, hEL, hEy, hEel', hEc', ?_⟩
  have hEM : E ≤ D.M := hEL.trans hLM
  by_cases h3 : IsStronglyPEmbedded 3 D.M
  · exact h3.rankThreeGamma_one_le_of_le Nat.prime_three hEel'.isPGroup hEM
  have hns := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hsp := UC6S846.sp_of_mem_sig hSg hns hpσ
  have hp3 : p ≠ 3 := by
    rintro rfl
    exact h3 hsp
  have hp7 : p ≠ 7 := by
    rintro rfl
    exact h7 hsp
  have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) := by
    by_cases hpq : p ∣ 2 ^ 21 + 1
    ·
      obtain ⟨Pb, hPbel, hPbc, hPbcent⟩ := hP p hp hpq hp3
      obtain ⟨A, hAL, -, hAπ, hAcard, hAel⟩ := UC6S898.exists_lift_fixed (B := ⊥) (ℓ := 3) (q := p)
        Nat.prime_three (by norm_num) hp hp2 bot_le IsPGroup.of_bot Pb hPbel.isPGroup
        (fun b hb e _ => by
          obtain rfl := Subgroup.mem_bot.1 hb
          have h1 : ∀ h : (1 : G) ∈ normalizer (L : Set G),
              (⟨1, h⟩ : ↥(normalizer (L : Set G))) = 1 := fun _ => rfl
          rw [h1, map_one, MulAut.one_apply])
      have hAel' : IsElemAbelian p A := hAel hPbel
      have hAc : Nat.card A = p ^ 2 := hAcard.trans hPbc
      have hNO := UC6S846.normalizer_le_normalizer_pCoreOf L
      obtain ⟨A', hA'C, hA'le, ⟨eA⟩⟩ := UC6S846.exists_centralizing_copy Nat.prime_three
        (by norm_num) hp hp2 (pCoreOf 2 L) A E (UC6S846.isPGroup_pCoreOf L)
        ((hAL.trans Subgroup.le_normalizer).trans hNO) ((hEL.trans Subgroup.le_normalizer).trans hNO)
        hAel'.isPGroup hEel'.isPGroup (fun e he a ha => by
          have heb : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨e, hEL he⟩ : ↥L) : Bar2 L) ∈ Eb :=
            hEπ ⟨⟨e, hEL he⟩, he, rfl⟩
          have hab : (QuotientGroup.mk' (CFSG.pCore 2 ↥L) (⟨a, hAL ha⟩ : ↥L) : Bar2 L) ∈ Pb :=
            hAπ ⟨⟨a, hAL ha⟩, ha, rfl⟩
          have hcomm := Subgroup.mem_centralizer_iff.1 (hPbcent hab) _ heb
          have hk : (⟨e, hEL he⟩ : ↥L) * ⟨a, hAL ha⟩ * (⟨e, hEL he⟩ : ↥L)⁻¹ * (⟨a, hAL ha⟩ : ↥L)⁻¹ ∈
              CFSG.pCore 2 ↥L := by
            rw [← QuotientGroup.eq_one_iff]
            simp only [QuotientGroup.mk_mul, QuotientGroup.mk_inv]
            simp only [QuotientGroup.mk'_apply] at hcomm
            rw [hcomm]
            group
          exact ⟨_, hk, rfl⟩)
      have hA'M : A' ≤ D.M :=
        hA'le.trans (sup_le (hAL.trans hLM) ((Subgroup.map_subtype_le _).trans hLM))
      have hA'el : IsElemAbelian p A' := UC6S846.isElemAbelian_of_mulEquiv eA hAel'
      have hA'c : Nat.card A' = p ^ 2 := by rw [Nat.card_congr eA.toEquiv, hAc]
      exact UC6S846.le_pRank' hp (le_inf hA'M hA'C) hA'el hA'c
    ·
      have hp5 : 5 ≤ p := hp.five_le_of_ne_two_of_ne_three hp2 hp3
      obtain ⟨B, hBM, hBel, hBc⟩ :=
        UC6S846.exists_elemAbelian_card_of_le_pRank hp (hSg.three_le p hpσ)
      have h7r : CFSG.Open.pRank 7 D.M ≤ 3 := by
        by_contra h
        exact h7 (UC6S846.sp_of_mem_sig hSg hns (hSg.four_mem 7 (by norm_num) (by norm_num)
          (by omega)))
      have hZ7 : ¬ 7 ∣ Nat.card (center (Bar2 L)) := fun h => by
        have := Nat.le_of_dvd (by norm_num) (h.trans (hCen (Bar2 L) 21 hX))
        omega
      have hBN : B ≤ normalizer (L : Set G) := by
        intro b hb
        by_cases hb1 : b = 1
        · rw [hb1]
          exact one_mem _
        have : Fact p.Prime := ⟨hp⟩
        exact uc22ine229_normalizes_of_pRank_le_three hL (hBM hb) hp hp5
          (orderOf_eq_prime (hBel.2 b hb) hb1) (by norm_num) (by norm_num) hXL hXc hZ7 h7r
      exact uc22s219r_two_le_pRank_centralizer hLM hX hp hp2 hp3
        (uc22ine229_not_dvd_two_mul (Or.inr rfl) hp hp2 hp3 hp7) hpq hBM hBN hBel hBc
        Nat.prime_three (by norm_num) hEL hEel'.isPGroup
  refine h76 p hpσ hp2 hsp 3 Nat.prime_three E hEM hEel' hEc' (by omega) fun Z hZE _ => ?_
  refine lt_of_lt_of_le (by norm_num) (h2.trans (CFSG.SectionRank.pRank_mono hp.one_lt ?_))
  exact inf_le_inf_left _ ((Subgroup.centralizer_le hZE).trans
    (Subgroup.centralizer_le_normalizer _))

end CFSG.LocalAnalysis.UniquenessCase.UC22

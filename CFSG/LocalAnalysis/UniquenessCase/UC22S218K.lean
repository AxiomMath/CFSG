module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S218NThree
import CFSG.LocalAnalysis.UniquenessCase.UC22S218KLift
import CFSG.LocalAnalysis.UniquenessCase.UC22S218KEven
import CFSG.LocalAnalysis.UniquenessCase.UC22S218KOddAut
import CFSG.LocalAnalysis.UniquenessCase.UC22S218Ub
import CFSG.LocalAnalysis.UniquenessCase.UC6Syl
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (rhoL rhoL_mk rhoL_mk_coe rhoL_fix_iff)

variable {G : Type} [Group G] [Finite G]

theorem uc22s218k_odd {L M : Subgroup G} {n p : ℕ} (hLM : L ≤ M)
    (hML : M ≤ normalizer (L : Set G)) (hX : IsSp4 (Bar2 L) n) (hn : Odd n)
    (hpn : p ∣ 2 ^ n + 1) :
    ∃ E R : Subgroup G, E ≤ L ∧ IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ IsSylowOf 3 R M ∧
      E ≤ R ∧ E ≤ centralizer (R : Set G) ∧ ∀ e ∈ E, ∃ z ∈ L, Commute z e ∧ orderOf z = p := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Eb, Qb, hEbel, hEbc, hEQb, hQbp, hQbi, ⟨zb, hzbC, hzbo⟩, hfix⟩ :=
    uc22s218k_odd_sp4 hX hn hpn
  obtain ⟨E₀, Q₀, hEQ, hQp, hEmap, hQmap, hEel, hEc⟩ :=
    uc22s218k_exists_lift hEbel hEbc hQbp hEQb
  obtain ⟨R, hR, hQR⟩ :=
    UC6.exists_isSylowOf_ge ((map_subtype_le Q₀).trans hLM) (hQp.map L.subtype)
  have hER : E₀.map L.subtype ≤ R := (map_mono hEQ).trans hQR
  have hRb : (R.subgroupOf L).map (QuotientGroup.mk' (CFSG.pCore 2 ↥L)) = Qb := by
    have h := (hQbp.toSylow hQbi).is_maximal' (hR.isPGroup.comap_subtype.map _) (by
      rw [IsPGroup.toSylow_coe, ← hQmap]
      exact map_mono fun q hq => mem_subgroupOf.2 (hQR (mem_map_of_mem _ hq)))
    rwa [IsPGroup.toSylow_coe] at h
  refine ⟨E₀.map L.subtype, R, map_subtype_le _, hEel, hEc, hR, hER, ?_, ?_⟩
  · rintro _ ⟨e, he, rfl⟩
    rw [mem_centralizer_iff]
    intro x hx
    obtain ⟨m, rfl⟩ : ∃ m : ↥(normalizer (L : Set G)), (m : G) = x :=
      ⟨⟨x, hML (hR.le hx)⟩, rfl⟩
    obtain ⟨k, hk⟩ := hR.isPGroup ⟨m, hx⟩
    have hm : m ^ 3 ^ k = 1 := Subtype.ext (by simpa using congrArg Subtype.val hk)
    have hρ : rhoL L m ^ 3 ^ k = 1 := by rw [← map_pow, hm, map_one]
    have hρE : ∀ y ∈ Eb, rhoL L m y ∈ Qb := by
      intro y hy
      rw [← hEmap] at hy
      obtain ⟨e', he', rfl⟩ := hy
      rw [← hRb]
      refine ⟨Subgroup.normalizerMonoidHom L m e', ?_, (rhoL_mk L m e').symm⟩
      rw [SetLike.mem_coe, mem_subgroupOf, rhoL_mk_coe]
      exact mul_mem (mul_mem hx (hER (mem_map_of_mem _ he'))) (inv_mem hx)
    have h1 := hfix (rhoL L m) k hρ hρE _ (hEmap ▸ mem_map_of_mem _ he)
    have h2 := (rhoL_fix_iff L m e).1 h1
    have heR : (e : G) ∈ R := hER (mem_map_of_mem _ he)
    have h3 : (m : G) * e * (m : G)⁻¹ * (e : G)⁻¹ = 1 :=
      disjoint_def.1 (IsPGroup.disjoint_of_ne 3 2 (by norm_num) _ _ hR.isPGroup
        (UC6S846.isPGroup_pCoreOf L))
        (mul_mem (mul_mem (mul_mem hx heR) (inv_mem hx)) (inv_mem heR)) h2
    calc (m : G) * L.subtype e = ((m : G) * e * (m : G)⁻¹ * (e : G)⁻¹) * e * m := by
          rw [coe_subtype]
          group
      _ = L.subtype e * m := by rw [h3, one_mul, coe_subtype]
  · rintro _ ⟨e, he, rfl⟩
    obtain ⟨z, hzL, hzo, hzc⟩ := uc22s218k_exists_centralizer_lift (P := E₀) (zb := zb)
      (hQp.to_le hEQ) (by rw [hEmap]; exact hzbC) hzbo
    exact ⟨z, hzL, hzc e he, hzo⟩

theorem s21_8K_of_conclusion76 {D : Data G} {Ch : Choice2011 G} (hSg : UC6S846.SigmaStd D)
    (h614 : UC6.R6_14 D) (h211 : S21_1 D Ch) (h76 : F07.R76Sig D) : S21_8K D Ch := by
  intro hH c L hL n hX _ hN h3 hσ
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hLM : L ≤ D.M := hL.1.le
  have hML : D.M ≤ normalizer (L : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hLM).1 hN
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hsp : IsStronglyPEmbedded p D.M := UC6S846.sp_of_mem_sig hSg hns hpσ
  obtain ⟨y, hyM, hyo, hyL⟩ :=
    uc22s218u_exists_trivial_action D Ch h211 hH c hML hX hp hp2 hsp (hSg.three_le p hpσ)
  obtain ⟨E, R, hEL, hEel, hEc, hR, hER, hEC, hz⟩ : ∃ E R : Subgroup G, E ≤ L ∧
      IsElemAbelian 3 E ∧ Nat.card E = 3 ^ 2 ∧ IsSylowOf 3 R D.M ∧ E ≤ R ∧
      E ≤ centralizer (R : Set G) ∧ ∀ e ∈ E, ∃ z ∈ L, Commute z e ∧ orderOf z = p := by
    rcases Nat.even_or_odd n with hev | hodd
    · exact uc22s218k_even hLM hML hX
        (Nat.pow_sub_one_dvd_pow_sub_one 2 (even_iff_two_dvd.1 hev)) (hσ p hpσ)
    · exact uc22s218k_odd hLM hML hX hodd (hσ p hpσ)
  obtain ⟨hpos, hXN⟩ :=
    uc22s218k_conclusion76_hyps hLM hML hX hp hp2 hEel.isPGroup hEL hyM hyo hyL hz
  have hstr : IsStronglyPEmbedded 3 D.M :=
    h614 (UC6S846.sig_subset_sig1 hSg hns) 3 Nat.prime_three (by norm_num) h3 R hR E
      (le_inf hER hEC) hEel hEc
      (h76 p hpσ hp2 hsp 3 Nat.prime_three E (hEL.trans hLM) hEel hEc hpos hXN)
  unfold Data.k kParam
  rw [if_pos hstr]

theorem s21_8K_dataOfSetup (hS : RankThreeUC.Standing G) (S : RankThreeUC.Setup G)
    {Ch : Choice2011 G} (h211 : S21_1 (PartTwo.Three.dataOfSetup hS S) Ch)
    (h614 : UC6.R6_14 (PartTwo.Three.dataOfSetup hS S))
    (h76 : F07.R76Sig (PartTwo.Three.dataOfSetup hS S)) :
    S21_8K (PartTwo.Three.dataOfSetup hS S) Ch :=
  s21_8K_of_conclusion76 (UC6S846.sigmaStd_dataOfSetup hS S) h614 h211 h76

end CFSG.LocalAnalysis.UniquenessCase.UC22

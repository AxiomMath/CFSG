module

public import CFSG.RankThree.PartTwo.Sec17.Item17Res15ProofHJ
public import CFSG.RankThree.PartTwo.Sec14.Ronan148QDefs
import CFSG.RankThree.PartTwo.Sec14.Ronan149Holds
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
public import CFSG.RankThree.PartTwo.Sec17.Item17Res14ProofKb
public import CFSG.RankThree.PartTwo.Sec17.Item17Res15ProofSect

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan143Q

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS CFSG.RankThree.PartTwo.Sec17
  CFSG.RankThree.PartTwo.Sec17.HeadProof

open Proof17Res15 in
theorem step174KbOHJ_holdsQ
    (h45 : Sec4.Item4_5) (h143 : Ronan148Q.Item143QS14)
    (h146 : Item146S14) : Step174KbOHJ := by
  intro G _ _ A c L Y₀ h X hXΔ hX3 K hK hSz hθ hcen hAK _ b hb hb1 hbΩ _ _ hD3
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := hSz
  set C := Subgroup.centralizer ({b} : Set G) with hC
  set D := delta A (lB A) C with hD
  set O := pPrimeCoreOf 3 C with hO
  set OA := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hOA
  set J := inSubgroup perfectResidual (K ⊓ C) with hJ
  obtain ⟨-, hJD⟩ := Proof17Res14.perfectResidual_mem_scriptQ h (h146 G A c L h.toSec14Std) hXΔ
    hX3 hK hAK hb.1
  have hb3 : orderOf b = 3 := orderOf_eq_prime (pow_three_of_std h hb.1) hb1
  obtain ⟨eJ⟩ := Proof17Res12.nonempty_quotTheta_perfectResidual hcen hθ hn (h.le_y0 hb.2)
    (hAK hb.1) hb3
  have hJSz := Proof17Res12.suzukiModel_of_mulEquiv' eJ hn
  have : Group.IsPerfect ↥J := Item148HJ.residual_isPerfect K b
  have hJ3 : ¬ 3 ∣ Nat.card J := fun h3 => hX3 (h3.trans (Subgroup.card_dvd_of_le
    ((Subgroup.map_subtype_le _).trans (inf_le_left.trans (le_of_mem_thetaComponentsIn hK)))))
  obtain ⟨Qs, hQs⟩ := maxInvariantPiSubgroups_nonempty D A (piCompl 3)
  obtain ⟨-, halt⟩ := h143 G A c L h.toSec14Std b hb.1 hb1 hbΩ Qs hQs
  rcases halt with h1 | ⟨b', d, Lb, hb'Ω, -, -, -, -, -, -, X', hDX, hinv, hcase⟩
  · exact absurd (h1 ▸ hD3) (Proof17Res14.not_three_dvd_card_sup_pPrimeCoreOf hb.1)
  have hDC : D ≤ C := delta_le C
  have hOC : C ≤ Subgroup.normalizer (O : Set G) := le_normalizer_pPrimeCoreOf 3 C
  have hO3 : ¬ 3 ∣ Nat.card O :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 C)
  have hOA3 : ¬ 3 ∣ Nat.card OA :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hOAC : OA ≤ C := (pPrimeCoreOf_le 3 _).trans
    (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb.1))
  have hDle : D ≤ O ⊔ X' ⊔ OA := hDX.le.trans (sup_right_comm O OA X').le
  have hDN : D ≤ Subgroup.normalizer ((O ⊔ X' : Subgroup G) : Set G) := by
    rcases hinv with hfull | ⟨-, hXθ, -, hNA⟩
    · exact hDC.trans hfull
    · exact sSup_le fun Q hQ => Ronan149.le_normalizer_of_inv h45 h.toSec14Std.toTheoremFourHyp
        h.toSec14Std.isE27' hb.1 hb1 hXθ hNA ⟨hQ.2, hQ.1.1.2.1, hQ.1.1.2.2⟩
  have hOAN : OA ≤ Subgroup.normalizer ((O ⊔ X' : Subgroup G) : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (hinv.centralizer_le hb.1)
  rcases hcase with ⟨hXθ, hXeq, -⟩ | ⟨-, ⟨𝒳, h𝒳, -, hX𝒳⟩, htypes⟩
  ·
    have hB := Res7MemFix.isHyperplane_closure_of_omega h.toSec14Std hb.1 hb1 hbΩ hb'Ω
    set B := Subgroup.closure ({b, b'} : Set G) with hBdef
    obtain ⟨b₀, d₀, L₀, hc⟩ : ∃ (b₀ d₀ : G) (L₀ : Subgroup G), IsLBConfig A B b₀ d₀ L₀ := by
      by_contra hno
      push Not at hno
      rw [lB_eq_bot hno, bot_sup_eq] at hXeq
      have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hXθ
      have htop : aschbacherSolvableCore 3 ↥X' = ⊤ := by
        apply Subgroup.map_injective X'.subtype_injective
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
        exact hXeq.symm
      have hall : ∀ z : ↥X' ⧸ aschbacherSolvableCore 3 ↥X', z = 1 := by
        intro z
        obtain ⟨z', rfl⟩ := QuotientGroup.mk'_surjective _ z
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, htop]
        exact Subgroup.mem_top z'
      obtain ⟨x, y, hxy⟩ := hq.2.2
      obtain ⟨x', rfl⟩ := QuotientGroup.mk'_surjective _ x
      obtain ⟨y', rfl⟩ := QuotientGroup.mk'_surjective _ y
      exact hxy (by rw [hall x', hall y'])
    have hLBJ := Item148HJ.lB_eq_residual h.toSec14Std hB hc
    obtain ⟨-, -, hq, hZ, hperf, htc, -⟩ := Item148HJ.resProj_facts h.toSec14Std hB hc
    set J₀ := inSubgroup perfectResidual (L₀ ⊓ Subgroup.centralizer ({d₀} : Set G)) with hJ₀
    have hbB : b ∈ B := Subgroup.subset_closure (Set.mem_insert b _)
    have hJ₀C : J₀ ≤ C := (Item148HJ.residual_le_centralizer hc).trans
      (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hbB))
    have hθX := Res7MemFix.theta_le_of_mem hXθ
    have hNeq : O ⊔ X' = O ⊔ J₀ := by
      apply le_antisymm
      · refine sup_le le_sup_left ?_
        rw [hXeq, hLBJ]
        exact sup_le le_sup_right (hθX.trans le_sup_left)
      · refine sup_le le_sup_left (le_sup_of_le_right ?_)
        rw [← hLBJ]
        exact le_sup_left.trans hXeq.ge
    have : Group.IsPerfect ↥(Item148HJ.resProj L₀ d₀).range := hperf
    have hker₀ : ¬ 3 ∣ Nat.card (Item148HJ.resProj L₀ d₀).rangeRestrict.ker := by
      rw [MonoidHom.ker_rangeRestrict]
      intro h3
      have hle : (Item148HJ.resProj L₀ d₀).ker.map J₀.subtype ≤
          inSubgroup (aschbacherSolvableCore 3) L₀ := by
        rintro _ ⟨k, hk, rfl⟩
        exact (Item148HJ.mem_ker_resProj k).mp hk
      rw [← Subgroup.card_map_of_injective J₀.subtype_injective] at h3
      have h4 := h3.trans (Subgroup.card_dvd_of_le hle)
      rw [inSubgroup, Subgroup.card_map_of_injective L₀.subtype_injective] at h4
      exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1 h4
    refine le_pPrimeCoreOf_of_section (Y := J₀) (hNeq ▸ hDle) (hNeq ▸ hDN)
      (hJ₀C.trans hOC) hO3 (hNeq ▸ hOAN) hOA3 hJD hJ3 hJSz
      (Item148HJ.resProj L₀ d₀).rangeRestrict (MonoidHom.rangeRestrict_surjective _) hker₀
      (fun W hW hW3 => Item148HJ.eq_bot_of_normal_of_quasisimple hq hZ hW hW3) (Or.inr (Or.inl htc))
  ·
    subst hX𝒳
    have hXC : sSup 𝒳 ≤ C := sSup_le fun K' hK' =>
      Sec6.le_centralizer_of_mem_thetaComponentsAt (h𝒳 hK')
    have : Group.IsPerfect ↥(sSup 𝒳) := Proof171Steps.isPerfect_sSup fun K' hK' =>
      Sec6.isPerfect_of_mem_thetaComponentsAt (h𝒳 hK')
    have : Group.IsPerfect (↥(sSup 𝒳) ⧸ aschbacherSolvableCore 3 ↥(sSup 𝒳)) :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective _)
    have hker₀ : ¬ 3 ∣ Nat.card (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(sSup 𝒳))).ker := by
      rw [QuotientGroup.ker_mk']
      exact (solvable_prime_complement_core_characterization Nat.prime_three).2.2.1
    exact le_pPrimeCoreOf_of_section (Y := sSup 𝒳) hDle hDN (hXC.trans hOC) hO3
      hOAN hOA3 hJD hJ3 hJSz (QuotientGroup.mk' _) (QuotientGroup.mk'_surjective _)
      hker₀ (eq_bot_of_types htypes) htypes

end CFSG.RankThree.PartTwo.Sec14.Ronan143Q

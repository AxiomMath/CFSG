module

public import CFSG.RankThree.GF2n.Stroth80.Sec83Count
public import CFSG.RankThree.GF2n.Stroth80.Sec83Vec
public import CFSG.RankThree.GF2n.Stroth80.Sec83CommSect
public import CFSG.RankThree.GF2n.Stroth80.Sec83SpFixed
public import CFSG.RankThree.GF2n.Stroth80.Sec83SpA2
public import CFSG.RankThree.GF2n.Stroth80.Sec83SpRank

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open CFSG.ClassicalGroups.Symplectic CFSG.ClassicalGroups.F2Fixed
open scoped commutatorElement Matrix


theorem sec83Fixed_of_53 (h53 : Stroth53Statement) (hInv : Sec8InvStatement) :
    Sec83FixedStatement := by
  intro G _ _ M Q Z B hc n t r m K _ _ φ u u' hs hr hpts z hz hzL hzN hna
  classical
  haveI := hpts.charP
  have h8 : Sec8Hyp hc n t := ⟨hs, m, hpts.two_le, hpts.spMNat⟩
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hb := h53.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl
  have hcd := h53.2.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hinv := hInv G M Q Z B hc n t h8 r hr
  have hP : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8W1 M Q Z B t r, ρ * x * ρ⁻¹ ∈ Sec8W1 M Q Z B t r :=
    fun ρ hρ x hx => conj_mem_of_conjSubgroup_eq (hinv ρ hρ).2 hx
  have hI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8V1 M Q Z B t r, ρ * x * ρ⁻¹ ∈ Sec8V1 M Q Z B t r :=
    fun ρ hρ x hx => conj_mem_of_conjSubgroup_eq (hinv ρ hρ).1 hx
  have hLeR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hL'eR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs.mem hrR
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hpts.hL'
  have hsec : SecHyp (Rt M (LB M Q B) t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) :=
    SecHyp.of_isOppDecomp hcd hP hI
  obtain ⟨Mod, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hpts.ker hsec hb.2
  haveI : Finite Mod := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hP hκ hcd hLeR hL'eR
  have hzL' : φ ⟨z, hz⟩ ∈ LspGL m K u := by
    rw [← hpts.hL]
    exact ⟨⟨z, hz⟩, Subgroup.mem_subgroupOf.mpr hzL, rfl⟩
  obtain ⟨hrange, hcard⟩ := stroth_2_1_fixed_of_hom (X := ↥(Rt M (LB M Q B) t)) (M := Mod)
    φ hpts.range (by have := hpts.two_le; omega) hκ.two hker hpts.uu' hpts.hL hL2 hdec hzL' hna
  have hIP : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r := hcd.1.trans hcd.2.1
  have hcc : Nat.card ↥(CommSec (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) z) =
      Nat.card ↥(Sec8V1 M Q Z B t r) *
        Nat.card ↥(comm Mod (⟨z, hz⟩ : ↥(Rt M (LB M Q B) t))).range :=
    natCard_commutator_sup hκ hP hIP ⟨z, hz⟩
  have hWc : Nat.card ↥(Sec8W1 M Q Z B t r) = Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Mod :=
    natCard_eq_of_isSecMod hIP hκ
  rw [hcc, hWc, hrange, hcard]
  ring

theorem sec83Type_of_nat : Sec83TypeStatement := by
  intro G _ _ M Q Z B hc n t r m K _ _ φ u u' hs hr hpts z hz hzL hzN
  classical
  haveI := hpts.charP
  obtain ⟨κ, hκ⟩ := hpts.isSecMod
  letI : DistribMulAction ↥(Rt M (LB M Q B) t) (Fin m ⊕ Fin m → K) := hpts.vecAct
  have hVQ : Vt M (LB M Q B) B Z t ≤ Q := hc.Vt_le_Q t
  have hnorm : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Vt M (LB M Q B) B Z t,
      ρ * x * ρ⁻¹ ∈ Vt M (LB M Q B) B Z t := fun ρ hρ x hx =>
    (Subgroup.mem_normalizer_iff.mp (hpts.act.1 hρ) x).mp hx
  have hcc : Nat.card ↥(CommSec (Vt M (LB M Q B) B Z t) Z z) =
      Nat.card ↥Z * Nat.card ↥(comm (Fin m ⊕ Fin m → K)
        (⟨z, hz⟩ : ↥(Rt M (LB M Q B) t))).range :=
    natCard_commutator_sup hκ hnorm sec39_Z_le_Vt ⟨z, hz⟩
  have hrange : Nat.card ↥(comm (Fin m ⊕ Fin m → K) (⟨z, hz⟩ : ↥(Rt M (LB M Q B) t))).range =
      Nat.card ↥(LinearMap.range (Matrix.toLin'
        ((φ ⟨z, hz⟩ : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) - 1))) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun a => ?_)
    simp only [AddMonoidHom.mem_range, comm_apply, LinearMap.mem_range, Matrix.toLin'_apply,
      Matrix.sub_mulVec, Matrix.one_mulVec]
    exact Iff.rfl
  have hA : φ ⟨z, hz⟩ ∈ LspGL m K u := by
    rw [← hpts.hL]
    exact ⟨⟨z, hz⟩, Subgroup.mem_subgroupOf.mpr hzL, rfl⟩
  have hA1 : φ ⟨z, hz⟩ ≠ 1 := by
    intro h1
    apply hzN
    have : (⟨z, hz⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h1
    rw [hpts.ker] at this
    exact Subgroup.mem_subgroupOf.mp this
  obtain ⟨hlt, hnon⟩ := card_range_sub_one_of_mem_LspGL hpts.u_ne_zero hA hA1
  rw [hcc, hrange]
  refine ⟨fun _ => ?_, fun hna => ?_⟩
  · rcases hlt with h | h
    · left
      rw [h, hpts.card]
      ring
    · right
      rw [h, hpts.card]
      ring
  · rw [hnon hna, hpts.card]
    ring

theorem fixedNonA2Fact : FixedNonA2Fact := by
  unfold FixedNonA2Fact
  intro m K _ _ _ X _ M _ _ φ hφ hm h2 _ hker u u' huu' L₁ L₂ hL₁ hL₂ hdec x hx hn
  exact stroth_2_1_fixed_of_hom φ hφ hm h2 hker huu' hL₁ hL₂ hdec hx hn

theorem sec83A2_of_53 (h53 : Stroth53Statement) (hInv : Sec8InvStatement) :
    Sec83A2Statement := by
  intro G _ _ M Q Z B hc n t r m K _ _ φ u u' hs hr hpts z hz hzL hzN hna
  classical
  haveI := hpts.charP
  have h8 : Sec8Hyp hc n t := ⟨hs, m, hpts.two_le, hpts.spMNat⟩
  have hrR : r ∈ Rt M (LB M Q B) t := hr.mem
  have hrM : r ∈ M := hc.Rt_le_M t hrR
  have hb := h53.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (hc.CN t) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl
  have hcd := h53.2.2.1 G M Q Z B hc n t hs hpts.spNat r hrR hr.plane (conjSubgroup r B)
    (LB M Q B) (LB M Q (conjSubgroup r B)) (Vt M (LB M Q B) B Z t) (Sec8W1 M Q Z B t r)
    (Sec8V1 M Q Z B t r) rfl rfl rfl rfl rfl rfl
  have hinv := hInv G M Q Z B hc n t h8 r hr
  have hP : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8W1 M Q Z B t r, ρ * x * ρ⁻¹ ∈ Sec8W1 M Q Z B t r :=
    fun ρ hρ x hx => conj_mem_of_conjSubgroup_eq (hinv ρ hρ).2 hx
  have hI : ∀ ρ ∈ Rt M (LB M Q B) t, ∀ x ∈ Sec8V1 M Q Z B t r, ρ * x * ρ⁻¹ ∈ Sec8V1 M Q Z B t r :=
    fun ρ hρ x hx => conj_mem_of_conjSubgroup_eq (hinv ρ hρ).1 hx
  have hLeR : LB M Q B ≤ Rt M (LB M Q B) t := le_Rt (M := M) (LB M Q B) hs.mem
  have hL'eR : LB M Q (conjSubgroup r B) ≤ Rt M (LB M Q B) t :=
    hc.LB_conj_le_Rt_of_mem hs.mem hrR
  have hL2 : ((LB M Q (conjSubgroup r B)).subgroupOf (Rt M (LB M Q B) t)).map φ = LspGL m K u' := by
    rw [hc.LB_conj hrM]
    exact hpts.hL'
  have hsec : SecHyp (Rt M (LB M Q B) t) (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) :=
    SecHyp.of_isOppDecomp hcd hP hI
  obtain ⟨Mod, iM, iA, κ, hκ, hker⟩ := exists_sectionModule_ker hpts.ker hsec hb.2
  haveI : Finite Mod := hκ.finite
  have hdec := isCompl_fixedSub_of_isOppDecomp hP hκ hcd hLeR hL'eR
  have hzL' : φ ⟨z, hz⟩ ∈ LspGL m K u := by
    rw [← hpts.hL]
    exact ⟨⟨z, hz⟩, Subgroup.mem_subgroupOf.mpr hzL, rfl⟩
  have hx1 : φ ⟨z, hz⟩ ≠ 1 := by
    intro h1
    apply hzN
    have : (⟨z, hz⟩ : ↥(Rt M (LB M Q B) t)) ∈ φ.ker := h1
    rw [hpts.ker] at this
    exact Subgroup.mem_subgroupOf.mp this
  have hle := stroth_2_1_a2_of_fixed fixedNonA2Fact (X := ↥(Rt M (LB M Q B) t)) (M := Mod)
    φ hpts.range (by have := hpts.two_le; omega) hκ.two hker hpts.uu' hpts.hL hL2 hdec hzL' hx1 hna
  have hIP : Sec8V1 M Q Z B t r ≤ Sec8W1 M Q Z B t r := hcd.1.trans hcd.2.1
  have hcc : Nat.card ↥(CommSec (Sec8W1 M Q Z B t r) (Sec8V1 M Q Z B t r) z) =
      Nat.card ↥(Sec8V1 M Q Z B t r) *
        Nat.card ↥(comm Mod (⟨z, hz⟩ : ↥(Rt M (LB M Q B) t))).range :=
    natCard_commutator_sup hκ hP hIP ⟨z, hz⟩
  have hWc : Nat.card ↥(Sec8W1 M Q Z B t r) = Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Mod :=
    natCard_eq_of_isSecMod hIP hκ
  rw [hcc, hWc]
  calc Nat.card ↥(Sec8V1 M Q Z B t r) ^ 3 * (Nat.card ↥(Sec8V1 M Q Z B t r) * Nat.card Mod)
      ≤ Nat.card ↥(Sec8V1 M Q Z B t r) ^ 3 * (Nat.card ↥(Sec8V1 M Q Z B t r) *
        Nat.card ↥(comm Mod (⟨z, hz⟩ : ↥(Rt M (LB M Q B) t))).range ^ 4) := by gcongr
    _ = (Nat.card ↥(Sec8V1 M Q Z B t r) *
        Nat.card ↥(comm Mod (⟨z, hz⟩ : ↥(Rt M (LB M Q B) t))).range) ^ 4 := by ring

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.RankThree.PartTwo.Sec4.Item4443SL
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLSteps
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLTransfer
public import CFSG.RankThree.PartTwo.Sec4.T444.Gap452
public import CFSG.RankThree.PartTwo.KFacts.KS44Multiplier
import CFSG.RankThree.PartTwo.Sec4.T444.Step452Residual
import CFSG.RankThree.PartTwo.Sec4.Item413Setup
import CFSG.RankThree.PartTwo.Sec18.Item182
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLChoice
public import CFSG.RankThree.PartTwo.Sec4.T444.Item4443SLStar

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item4443SL

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.LocalCores
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open CFSG.Assembly.RankThreeEven (projSL)
open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem le_of_forall_pow_mem {I N : Subgroup G} (hIp : Group.IsPerfect I)
    (eI : I ⧸ CFSG.pCore 2 I ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (hNI : N ≤ I) (hIN : I ≤ normalizer (N : Set G))
    (hpow : ∀ x ∈ I, ∃ m : ℕ, ¬ 3 ∣ m ∧ x ^ m ∈ N) : I ≤ N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N' : Subgroup I := N.subgroupOf I with hN'
  have hN'n : N'.Normal := (normal_subgroupOf_iff_le_normalizer hNI).mpr hIN
  set φ := QuotientGroup.mk' (CFSG.pCore 2 I) with hφ
  have hIq : CFSG.IsQuasisimple (I ⧸ CFSG.pCore 2 I) :=
    LocalCores.isQuasisimple_of_mulEquiv eI.symm isQuasisimple_SL
  have hN'φ : (N'.map φ).Normal := hN'n.map φ (QuotientGroup.mk'_surjective _)
  rcases LocalCores.quasisimple_normal_subgroups hIq hN'φ with htop | hcen
  ·
    have hsurj : Function.Surjective ((QuotientGroup.mk' N').comp (CFSG.pCore 2 I).subtype) := by
      intro qq
      obtain ⟨i, rfl⟩ := QuotientGroup.mk'_surjective N' qq
      have hi : φ i ∈ N'.map φ := htop ▸ mem_top _
      obtain ⟨d, hd, hdi⟩ := hi
      rw [hφ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hdi
      refine ⟨⟨d⁻¹ * i, hdi⟩, ?_⟩
      rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
        QuotientGroup.eq]
      change (d⁻¹ * i)⁻¹ * i ∈ N'
      rw [show (d⁻¹ * i)⁻¹ * i = i⁻¹ * d * i by group]
      have := hN'n.conj_mem d hd i⁻¹
      simpa [mul_assoc] using this
    have hTs : Group.IsNilpotent (CFSG.pCore 2 I) := CFSG.pCore_isPGroup.isNilpotent
    have hsolv : Group.IsSolvable (I ⧸ N') := Group.isSolvable_of_surjective hsurj
    have hperf : Group.IsPerfect (I ⧸ N') :=
      Group.IsPerfect.ofSurjective (QuotientGroup.mk'_surjective N')
    have hsub : Subsingleton (I ⧸ N') := by
      by_contra hnt
      rw [not_subsingleton_iff_nontrivial] at hnt
      exact Group.IsPerfect.not_isSolvable _ hsolv
    intro x hx
    have h1 : (QuotientGroup.mk' N' ⟨x, hx⟩ : I ⧸ N') = 1 := Subsingleton.elim _ _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact mem_subgroupOf.mp h1
  ·
    exfalso
    have hZ3 : Nat.card (center (I ⧸ CFSG.pCore 2 I)) = 3 := by
      rw [← KFacts.L34.card_center_specialLinearGroup KFacts.L34.card_galoisField_two_two,
        ← map_center_eq eI, card_map_of_injective eI.injective]
    have h1 : Nat.card (N'.map φ) ∣ 3 := hZ3 ▸ card_dvd_of_le hcen
    have hQ : Nat.card (I ⧸ CFSG.pCore 2 I) = 60480 := by
      rw [Nat.card_congr eI.toEquiv, KFacts.KS14.card_SL_three_four]
    have h3 : 3 ∣ Nat.card ((I ⧸ CFSG.pCore 2 I) ⧸ N'.map φ) := by
      have hmul := card_eq_card_quotient_mul_card_subgroup (N'.map φ)
      rw [hQ] at hmul
      rcases (Nat.dvd_prime Nat.prime_three).mp h1 with h | h
      · rw [h, mul_one] at hmul
        rw [← hmul]
        norm_num
      · rw [h] at hmul
        exact ⟨6720, by omega⟩
    obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 3 h3
    obtain ⟨q, rfl⟩ := QuotientGroup.mk'_surjective (N'.map φ) z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 I) q
    obtain ⟨m, hm3, hxm⟩ := hpow x x.2
    have hm : (QuotientGroup.mk' (N'.map φ) (φ x)) ^ m = 1 := by
      rw [← map_pow, ← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact mem_map_of_mem φ (mem_subgroupOf.mpr (by simpa using hxm))
    exact hm3 (hz ▸ orderOf_dvd_of_pow_eq_one hm)

omit [Finite G] in
theorem mul_pow_mul_inv_mem {L : Subgroup G} {l p : G} (hl : l ∈ L)
    (hp : p ∈ normalizer (L : Set G)) (m : ℕ) : (l * p) ^ m * (p ^ m)⁻¹ ∈ L := by
  induction m with
  | zero => simp
  | succ m ih =>
    have h1 : (l * p) ^ (m + 1) * (p ^ (m + 1))⁻¹ =
        ((l * p) ^ m * (p ^ m)⁻¹) * (p ^ m * l * (p ^ m)⁻¹) := by
      rw [pow_succ, pow_succ]
      group
    rw [h1]
    exact L.mul_mem ih ((mem_normalizer_iff.mp (pow_mem hp m) l).mp hl)

theorem le_of_map_starQuot_le {I L : Subgroup G} (hIp : Group.IsPerfect I)
    (eI : I ⧸ CFSG.pCore 2 I ≃* Matrix.SpecialLinearGroup (Fin 3) (GaloisField 2 2))
    (hIL : I ≤ normalizer (L : Set G)) (hle : I.map (starQuot G) ≤ L.map (starQuot G)) :
    I ≤ L := by
  have hIN : I ≤ normalizer ((I ⊓ L : Subgroup G) : Set G) := fun x hx =>
    inf_normalizer_le_normalizer_inf ⟨le_normalizer hx, hIL hx⟩
  refine (le_of_forall_pow_mem hIp eI inf_le_left hIN fun x hx => ?_).trans inf_le_right
  obtain ⟨l, hl, hlx⟩ := hle (mem_map_of_mem _ hx)
  rw [starQuot, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hlx
  set p := l⁻¹ * x with hp
  have hpN : p ∈ normalizer (L : Set G) :=
    mul_mem (inv_mem (le_normalizer hl)) (hIL hx)
  refine ⟨orderOf p, not_three_dvd_orderOf_of_mem hlx not_three_dvd_card_pPrimeCore,
    pow_mem hx _, ?_⟩
  have h1 := mul_pow_mul_inv_mem hl hpN (orderOf p)
  rwa [pow_orderOf_eq_one, inv_one, mul_one, show l * p = x by rw [hp]; group] at h1

theorem item4_44_3SL_of_inputs
    (h434 : Item4_34Sec) (h45 : Item4_5) (h442 : Item4_44_2) (hSz : KFacts.KPSz)
    (hS : SchreierFor CFSG.Assembly.InCatalog) (hres : Item4_52Residual)
    (hmult : KFacts.L34CenterThreePrimeTwo) : Item4_44_3SL := by
  intro G _ _ A M h H hH hSL
  obtain ⟨eI⟩ := hSL
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨s, hs⟩ := exists_ctx4443 h442 h hH
  set I := inSubgroup perfectResidual H with hI
  set π := starQuot G with hπ
  obtain ⟨L, hL, h3, hLM, hIL, hIC, hIs, hsL, hss⟩ :=
    Ctx4443.exists_mem_thetaComponents_of_commutator_eq hSz hS h45 hs
      (Ctx4443.commutator_A_eq_general hs) (Ctx4443.isQuasisimple_quotient hs)
  have hIp : ⁅I, I⁆ = I := Sec18.commutator_inSubgroup_perfectResidual H
  have hAH : A ≤ H := Sec18.le_of_mem_scriptH₀ hH
  have hAI : A ≤ normalizer (I : Set G) :=
    hAH.trans (Sec18.le_normalizer_inSubgroup_perfectResidual H)
  have hAL := h.le_normalizer_of_mem_thetaComponents h45 hL
  have hZ : IsZ3L34OrHeisSL34 ((A ⊔ L).map π) :=
    Ctx4443.isZ3L34OrHeisSL34_map h434 h45 hs hL hLM hsL hss
  set T := (CFSG.Open.pCoreOf 2 I).map π with hT
  have hTn := map_pCoreOf_subgroupOf_normal (G := G) I
  obtain ⟨eIs⟩ := nonempty_quotient_map_equiv eI
  have hAT : A ≤ normalizer ((CFSG.Open.pCoreOf 2 I : Subgroup G) : Set G) := by
    have := CFSG.LieType.BorelTits.pCore_characteristic (G := I) 2
    exact hAI.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (CFSG.Open.pCore 2 I))
  have hLq := (isComponent_map_starQuot hL h3).1
  have hIsL : I.map π ≤ L.map π := by
    refine le_of_quotient (map_mono (CFSG.LieType.BorelTits.pCoreOf_le 2 I))
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 I).map π) eIs
      (isPerfect_iff.mpr (by rw [← map_commutator, hIp])) hLq
      ((map_mono hIL).trans (le_normalizer_map π)) hIC hIs (isE27_map_starQuot h.isE27)
      ((map_mono hAI).trans (le_normalizer_map π)) ((map_mono hAL).trans (le_normalizer_map π))
      ((map_mono hAT).trans (le_normalizer_map π)) (exists_inner_map hs)
      (fun _ hy hy3 => mem_map_of_mem_centralizer_map h hy hy3) ?_
    rw [← Subgroup.map_sup]
    exact hZ
  have hILe : I ≤ L := le_of_map_starQuot_le (isPerfect_iff.mpr hIp) eI hIL hIsL
  have hAL' : A.map π ≤ normalizer (L.map π : Set (G ⧸ CFSG.pPrimeCore 3 G)) :=
    (map_mono hAL).trans (le_normalizer_map π)
  obtain ⟨hshape, -, -⟩ := shape_sup (isE27_map_starQuot h.isE27) hAL' hLq.1
    (by rw [← Subgroup.map_sup]; exact hZ)
  obtain ⟨hLcard, hZL⟩ := card_of_shape hshape
  have hIs60 : 60480 ≤ Nat.card (I.map π) := by
    have hmul := card_eq_card_quotient_mul_card_subgroup (T.subgroupOf (I.map π))
    rw [Nat.card_congr eIs.toEquiv, KFacts.KS14.card_SL_three_four] at hmul
    rw [hmul]
    exact Nat.le_mul_of_pos_right _ Nat.card_pos
  have hIsEq : I.map π = L.map π := by
    refine eq_of_le_of_card_ge hIsL ?_
    rw [hLcard]
    have := Nat.le_of_dvd (by norm_num) hZL
    omega
  obtain ⟨K, _, hKs, h9, ⟨ψ⟩⟩ := exists_solvable_quotient_projSL h.isE27.isPGroup hL h3 hAL hZ
  have : Group.IsPerfect L := hL.1
  have hq := quasisimple_of_residual hres (sectionFourHyp_subgroup h.sectionFourHyp L) hKs h9 ψ
  have hθ2 := isPGroup_two_aschbacherSolvableCore hmult hq ψ
  have hθO : aschbacherSolvableCore 3 L ≤ CFSG.pCore 2 L := le_sSup ⟨inferInstance, hθ2⟩
  have hθL := inf_pPrimeCore_eq_of_mem_thetaComponents hL h3
  refine ⟨L, ⟨hL.1, hL.2.1, hq⟩, hLM,
    le_antisymm (fun l hl => ?_) (sup_le hILe (map_subtype_le _))⟩
  have hl' : π l ∈ I.map π := hIsEq ▸ mem_map_of_mem π hl
  obtain ⟨x, hx, hxl⟩ := hl'
  rw [hπ, starQuot, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hxl
  have hmem : x⁻¹ * l ∈ L ⊓ CFSG.pPrimeCore 3 G := ⟨L.mul_mem (L.inv_mem (hILe hx)) hl, hxl⟩
  rw [hθL] at hmem
  obtain ⟨t, ht, hte⟩ := hmem
  have h1 : l = x * (x⁻¹ * l) := by group
  rw [h1, ← hte]
  exact mul_mem (mem_sup_left hx) (mem_sup_right ⟨t, hθO ht, rfl⟩)

end CFSG.RankThree.PartTwo.Sec4.Item4443SL

module

public import CFSG.RankThree.PartTwo.Sec21.Item222ProofStatements
public import CFSG.RankThree.PartTwo.KFacts.KS222U4OddCent
import CFSG.RankThree.PartTwo.Sec21.Item222ProofCases
import CFSG.RankThree.PartTwo.Sec21.Item222ProofKZero

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Assembly.LowTwoRank (StatedProj StatedSU)

theorem ks222U4Odd : KS222U4Odd := by
  intro G _ _ L A c n hn1 hno ⟨eL⟩ hAe hA81 hcA hcL hLC hAL
  set K := GaloisField 2 (2 * n) with hKdef
  have hK : Nat.card K = (2 ^ n) ^ 2 := U4Lines.card_galoisField_two_mul n (by omega)
  have hU : UnitaryFieldData 2 n K :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have hpq : 3 ∣ 2 ^ n + 1 := by
    obtain ⟨k, rfl⟩ := hno
    have h : (2 : ℕ) ^ (2 * k + 1) % 3 = 2 := by
      rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
      norm_num
    rw [Nat.dvd_iff_mod_eq_zero, Nat.add_mod, h]
  have := isSimpleGroup_projSU (m := 4) (n := n) le_rfl (by omega)
  have : IsSimpleGroup L := eL.isSimpleGroup
  have h2L : 2 ∣ Nat.card L := by
    rw [Nat.card_congr eL.toEquiv]
    apply dvd_of_one_le_padicValNat
    rw [Item222Proof.padicValNat_card_projSU_four (by omega)]
    omega
  have h3L : 3 ∣ Nat.card L := by
    have h27 : Nat.card (A ⊓ L : Subgroup G) ∣ Nat.card L := Subgroup.card_dvd_of_le inf_le_right
    rw [hAL] at h27
    exact (dvd_pow_self 3 (by norm_num)).trans h27
  obtain ⟨x, y, hxy⟩ := Item222Proof.exists_not_commute_of_isSimpleGroup h2L h3L
  have hZ : Subgroup.center L = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center L) with h | h
    · exact h
    · exfalso
      exact hxy (Subgroup.mem_center_iff.mp (h ▸ Subgroup.mem_top y) x)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e₀ : projSU 4 2 n ≃* StatedProj (StatedSU 4 (2 ^ n) K) :=
    (MulEquiv.subgroupCongr (Census.projImage_statedSU 4 2 n).symm).trans
      (Census.statedProjEquivProjImage _).symm
  let e : ↥L ⧸ Subgroup.center ↥L ≃* StatedProj (StatedSU 4 (2 ^ n) K) :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans
      (QuotientGroup.quotientBot.trans (eL.trans e₀))
  set F : Subgroup L := (A ⊓ L).subgroupOf L with hFdef
  have hFexp : ∀ z ∈ F, z ^ 3 = 1 := by
    intro z hz
    apply Subtype.ext
    have hzA : (z : G) ∈ A := (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).1
    simpa using hAe.2 _ hzA
  have hFcomm : ∀ z ∈ F, ∀ w ∈ F, z * w = w * z := by
    intro z hz w hw
    apply Subtype.ext
    have h := congrArg (fun t : A => (t : G)) (hAe.1.is_comm.comm
      ⟨z, (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hz)).1⟩
      ⟨w, (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hw)).1⟩)
    exact h
  have hFcard : Nat.card F = 3 ^ 3 := by
    rw [hFdef, Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hAL]
  obtain ⟨ψ, hψ⟩ := CFSG.RankThree.PartOne.KFU.exists_diag_iso (by omega) hK Nat.prime_three hpq
    hZ e F hFexp hFcomm hFcard
  let C : U4OddLines.U4OddCtx G L A c n K :=
    { hU := hU
      hf2 := by omega
      hpq := hpq
      hAe := hAe
      hA81 := hA81
      hcA := hcA
      hcL := hcL
      hLc := hLC
      hAL := hAL
      ψ := ψ
      hψ := fun g => by
        rw [← hψ g, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
        exact ⟨fun h => ⟨h, (ψ g).2⟩, fun h => h.1⟩ }
  refine ⟨C.starOf_eq_closure, fun φ hφL hφR => ?_⟩
  rw [C.starOf_eq_range] at hφL
  obtain ⟨σ, rfl⟩ := hφL
  obtain ⟨a, b, hab, rfl⟩ := (C.isReflectionOn_actA_iff σ).mp hφR
  obtain ⟨e₁⟩ := C.nonempty_perfectResidual_fixed_swap hab
  have := hU.finite
  have := Fintype.ofFinite hU.fixedField
  have := Fintype.ofFinite (GaloisField 2 n)
  have hcard : Fintype.card hU.fixedField = Fintype.card (GaloisField 2 n) := by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hU.card_fixedField,
      GaloisField.card 2 n (by omega)]
  have hchar : CharP hU.fixedField 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq hU.card_fixedField
  exact ⟨e₁.trans ((CFSG.Adapters.RankTwoModelTransports.specialLinearGroupCongr (Fin 2)
    (FiniteField.ringEquivOfCardEq hcard)).trans (projSLTwoEquivSL _).symm)⟩

end CFSG.RankThree.PartTwo.Sec21

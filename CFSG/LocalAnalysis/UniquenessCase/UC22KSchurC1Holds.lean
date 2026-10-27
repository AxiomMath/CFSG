module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineKSchurC1
public import CFSG.GH74.Generic.Context
public import CFSG.HardMathSupport.U4FF.Omega2
public import CFSG.LocalAnalysis.ComponentClassification.RankTwoClassicalAS76aProofOMinusFacts
public import CFSG.LieType.Steinberg.CentralExt.PSpMultiplier

public section

open scoped MatrixGroups commutatorElement

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Assembly.LowTwoRank CFSG.LieType.Steinberg.CentralExt
open CFSG.LieType.Universal.Unitary CFSG.ComponentClassification.RankTwoClassical
open CFSG.RankThree.PerfectCover CFSG.HardMathSupport.U4FF
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

theorem ker_eq_bot_of_odd_of_hopfMultiplier_dvd_two {P H : Type} [Group P] [Finite P]
    [Group H] [Finite H] [Group.IsPerfect H] [Group.IsPerfect P] (η : P →* H)
    (hη : Function.Surjective η) (hK : η.ker ≤ Subgroup.center P)
    (hodd : Odd (Nat.card η.ker)) (hM : Nat.card (hopfMultiplier H) ∣ 2) :
    η.ker = ⊥ := by
  haveI : Finite (hopfMultiplier H) := finite_hopfMultiplier inferInstance
  have hdvd : Nat.card η.ker ∣ Nat.card (hopfMultiplier H) :=
    Subgroup.card_dvd_of_surjective (hopfMultiplierToKer_surjective η hη hK)
  have h2 : Nat.card η.ker ∣ 2 := hdvd.trans hM
  have hle : Nat.card η.ker ≤ 2 := Nat.le_of_dvd (by norm_num) h2
  obtain ⟨k, hk⟩ := hodd
  exact Subgroup.eq_bot_of_card_eq η.ker (by omega)

private theorem sp4_hopfMultiplier_dvd_two {F : Type} [Field F] [Finite F] {n : ℕ}
    (hF : Nat.card F = 2 ^ n) (hn : 3 ≤ n) :
    Group.IsPerfect (StatedProj (StatedSp 2 F)) ∧
      Nat.card (hopfMultiplier (StatedProj (StatedSp 2 F))) ∣ 2 := by
  have hK5 : 5 ≤ Nat.card F := by
    have h2n : 8 ≤ 2 ^ n := by
      calc 8 = 2 ^ 3 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
    rw [hF]
    omega
  obtain ⟨hcommH, ⟨eM⟩⟩ := SpClosed.psp_hopfMultiplier (n := 2) le_rfl hK5
  refine ⟨Group.isPerfect_def.2 hcommH, ?_⟩
  have e1 : hopfMultiplier (StatedProj (StatedSp 2 F)) ≃*
      Multiplicative (ZMod (Nat.gcd 2 (Nat.card F - 1))) :=
    (hopfMultiplierEquivGriess _).symm.trans eM
  rw [Nat.card_congr e1.toEquiv,
    Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod _) ≃ ZMod _), Nat.card_zmod]
  exact Nat.gcd_dvd_left 2 _

theorem kSchurC1_sp4 {X : Type} [Group X] [Finite X] (Z : Subgroup X) [Z.Normal]
    (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤) (hZc : Z ≤ Subgroup.center X)
    (hodd : Odd (Nat.card ↥Z)) (hsp : ∃ n : ℕ, 3 ≤ n ∧ IsSp4 (X ⧸ Z) n) : Z = ⊥ := by
  obtain ⟨n, hn, hSp⟩ := hsp
  obtain ⟨-, -, F, hField, hFinite, hF, ⟨e⟩⟩ := CFSG.GH74.Generic.lieModel_psp_data hSp
  letI := hField
  letI := hFinite
  haveI : Group.IsPerfect X := Group.isPerfect_def.2 (by rwa [_root_.commutator_def])
  obtain ⟨hperfH, hM⟩ := sp4_hopfMultiplier_dvd_two hF hn
  haveI : Group.IsPerfect (StatedProj (StatedSp 2 F)) := hperfH
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hkerπ : π.ker = Z := QuotientGroup.ker_mk' Z
  have hη : Function.Surjective (e.toMonoidHom.comp π) := e.surjective.comp hπ
  have hker_eq : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_eq_one_iff e e.injective
  have hker : (e.toMonoidHom.comp π).ker ≤ Subgroup.center X := by
    rw [hker_eq, hkerπ]
    exact hZc
  have hodd' : Odd (Nat.card (e.toMonoidHom.comp π).ker) := by
    rw [hker_eq, hkerπ]
    exact hodd
  have hbot := ker_eq_bot_of_odd_of_hopfMultiplier_dvd_two (e.toMonoidHom.comp π) hη hker
    hodd' hM
  rw [hker_eq, hkerπ] at hbot
  exact hbot

private theorem ker_eq_bot_of_statedSU
    {X : Type} [Group X] [Finite X]
    {Z : Subgroup X} [Z.Normal] (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hZc : Z ≤ Subgroup.center X) (hodd : Odd (Nat.card ↥Z)) {a : ℕ} (ha : 2 ≤ a)
    {F : Type} [Field F] [Finite F] [CharP F 2] (hF : Nat.card F = (2 ^ a) ^ 2)
    (e : X ⧸ Z ≃* StatedSU 4 (2 ^ a) F) : Z = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect X := Group.isPerfect_def.2 (by rwa [_root_.commutator_def])
  let π : X →* X ⧸ Z := QuotientGroup.mk' Z
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective Z
  have hkerπ : π.ker = Z := QuotientGroup.ker_mk' Z
  have hη : Function.Surjective (e.toMonoidHom.comp π) := e.surjective.comp hπ
  have hker_eq : (e.toMonoidHom.comp π).ker = π.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, MonoidHom.comp_apply]
    exact map_eq_one_iff e e.injective
  have hkerπc : π.ker ≤ Subgroup.center X := by
    rw [hkerπ]
    exact hZc
  have hker : (e.toMonoidHom.comp π).ker ≤ Subgroup.center X := by
    rw [hker_eq]
    exact hkerπc
  have hq : 4 ≤ 2 ^ a := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha
  obtain ⟨s, hs⟩ := SUClosed.statedSU_exists_section_of_central (n := 4) (p := 2) (f := a)
    (F := F) hF (by decide) le_rfl hq hη hker
  let σ : X ⧸ Z →* X := s.comp e.toMonoidHom
  have hσ : ∀ g, π (σ g) = g := by
    intro g
    apply e.injective
    calc e (π (σ g)) = (e.toMonoidHom.comp π) (s (e g)) := rfl
      _ = e g := hs (e g)
  have hbot := SL2Closed.ker_eq_bot_of_section π hkerπc σ hσ
  rw [← hkerπ]
  exact hbot

private theorem ker_eq_bot_of_omegaMinus
    {X : Type} [Group X] [Finite X]
    {Z : Subgroup X} [Z.Normal] (hX : ⁅(⊤ : Subgroup X), (⊤ : Subgroup X)⁆ = ⊤)
    (hZc : Z ≤ Subgroup.center X) (hodd : Odd (Nat.card ↥Z)) {n : ℕ} (hn : 3 ≤ n)
    (hΩ : IsOmegaMinus (X ⧸ Z) 6 n) : Z = ⊥ := by
  obtain ⟨-, E, hField, hFiniteE, b, c, hE, hirr, ⟨eΩ⟩⟩ := hΩ
  letI := hField
  letI := hFiniteE
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcharE : CharP E 2 := by
    have : Fintype E := Fintype.ofFinite E
    refine charP_of_card_eq_prime_pow (p := 2) (f := n) ?_
    rwa [Fintype.card_eq_nat_card]
  letI := hcharE
  have hinj : Function.Injective (oProj (StatedQuadMinus 3 E b c)) :=
    oProj_injective (v₀ := minusVec 3)
      (by rw [statedQuadMinus_minusVec]; exact one_ne_zero)
      (fun d => statedQuadMinus_smul 3 b c d (minusVec 3))
  let eProj : StatedProj (StatedOmega (StatedQuadMinus 3 E b c)) ≃*
      StatedOmega (StatedQuadMinus 3 E b c) :=
    (MulEquiv.ofBijective (oProj _) ⟨hinj, oProj_surjective _⟩).symm
  let K := GaloisField 2 (2 * n)
  have hKcard : Nat.card K = (2 ^ n) ^ 2 := by
    have hpow : (2 ^ n) ^ 2 = 2 ^ (2 * n) := by
      rw [← pow_mul, Nat.mul_comm]
    rw [GaloisField.card 2 (2 * n) (by omega), ← hpow]
  obtain ⟨eSU⟩ := exists_mulEquiv_su_statedOmega (E := E) (K := K) (n := n) hE hKcard hirr
  have e : X ⧸ Z ≃* StatedSU 4 (2 ^ n) K :=
    (eΩ.trans eProj).trans (eSU.symm.trans (equivStatedSU hKcard 4))
  exact ker_eq_bot_of_statedSU hX hZc hodd (by omega) hKcard e

theorem kSchurC1_holds :
    KSchurC1 := by
  intro X _ _ Z _ hX hZc hodd hshape
  rcases hshape with ⟨n, hn, hSp⟩ | ⟨a, ha, hSU⟩ | ⟨n, hn, hΩ⟩
  · exact kSchurC1_sp4 Z hX hZc hodd ⟨n, hn, hSp⟩
  · obtain ⟨F, hField, hFinite, hF, ⟨e⟩⟩ := hSU
    letI := hField
    letI := hFinite
    haveI hchar : CharP F 2 := by
      have : Fintype F := Fintype.ofFinite F
      haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      refine charP_of_card_eq_prime_pow (p := 2) (f := 2 * a) ?_
      have hpow : (2 ^ a) ^ 2 = 2 ^ (2 * a) := by
        rw [← pow_mul, Nat.mul_comm]
      rw [Fintype.card_eq_nat_card, hF, hpow]
    exact ker_eq_bot_of_statedSU hX hZc hodd ha hF e
  · exact ker_eq_bot_of_omegaMinus hX hZc hodd hn hΩ

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

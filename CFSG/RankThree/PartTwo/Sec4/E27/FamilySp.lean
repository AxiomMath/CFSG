module

public import CFSG.RankThree.PartTwo.Sec4.E27.InnerOuter
public import CFSG.RankThree.PartTwo.Sec4.E27.PairSpOdd
public import CFSG.RankThree.PartTwo.Sec4.E27.FieldAutSpOdd
public import CFSG.RankThree.PartTwo.Sec4.E27.FixSp
public import CFSG.RankThree.PartTwo.Sec19.Item19Res2ProofSplitSp4
public import CFSG.LieType.SeitzGeneration.SpHyperGen
public import CFSG.LieType.SeitzGeneration.OuterSpData

public section

open CFSG.LieType.Seitz CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.CTP CFSG.Open
  CFSG.Assembly.LowTwoRank
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open CFSG.RankThree.PartOne (proj_injective_sp)

namespace CFSG.RankThree.PartTwo.Sec4.E27


theorem hinner_sp4 {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 4 ≤ f)
    (hK : Nat.card K = 2 ^ f) :
    ∀ E : Subgroup (StatedProj (StatedSp 2 K)), IsElemAbelian 3 E → Nat.card E = 27 →
      HyperGen 3 (⊤ : Subgroup (StatedProj (StatedSp 2 K))) E := by
  intro E hE hc
  exfalso
  haveI : CharP K 2 := charP_two_of_card hK
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hinj : Function.Injective (proj 2 K) := proj_injective_sp hK (by omega) (by omega)
  have hker : ¬ 3 ∣ Nat.card (proj 2 K).ker := by
    have h1 : (proj 2 K).ker = ⊥ := (MonoidHom.ker_eq_bot_iff _).2 hinj
    rw [h1]
    simp
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  obtain ⟨A, hAE, hAdis, hAcomm, hAexp, hAcard⟩ :=
    exists_lift_elemAbelian (proj 2 K)
      (CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher.proj_surjective (r := 2) (K := K))
      hker hcomm hE.2
  have hAab : IsElemAbelian 3 A :=
    ⟨⟨⟨fun a b => Subtype.ext (hAcomm a a.2 b b.2)⟩⟩, fun x hx => hAexp x hx⟩
  have h9 := CFSG.RankThree.PartTwo.Sec19.Item19Res2Proof.card_le_nine_of_elemAbelian_sp4 hAab
  omega

theorem seitz27_sp4 {K : Type} [Field K] [Finite K] {f : ℕ} (hf : 4 ≤ f)
    (hK : Nat.card K = 2 ^ f) : Seitz27 (StatedProj (StatedSp 2 K)) := by
  haveI : CharP K 2 := charP_two_of_card hK
  have hZ : Subgroup.center (StatedProj (StatedSp 2 K)) = ⊥ :=
    center_statedProj_statedSp_eq_bot (by omega)
  have hF : FieldAutData (StatedProj (StatedSp 2 K)) 3 := by
    refine fieldAutData_projectiveSp_odd_e27 (le_refl 2) Nat.prime_three (by norm_num) (by omega) hK ?_
    intro k hkK A hne
    have hdvd : Nat.card k ∣ 2 ^ f := by
      rw [← hK, hkK]
      exact dvd_pow_self _ (by norm_num)
    obtain ⟨m, hm, hmk⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 hdvd
    rw [hK, hmk, ← pow_mul] at hkK
    have hfm : f = m * 3 := Nat.pow_right_injective (le_refl 2) hkK
    have hk4 : 4 ≤ Nat.card k := by
      rw [hmk]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact subfieldPairSp_of_four_le_odd k Nat.prime_three
      (by norm_num) (by rw [hK, hmk, ← pow_mul]; exact hkK ▸ rfl) hk4 A hne
  exact seitz27_of_inner_outer hZ (hinner_sp4 hf hK) hF (fixPlaneGen_sp4_three hf hK)

end CFSG.RankThree.PartTwo.Sec4.E27

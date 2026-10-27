module

public import CFSG.LocalAnalysis.StandardType.GGSUNonsplitTwoBlock
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContrary

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Multiplicative
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (primeFormUnitary)
open CFSG.RankThree.PartOne.KCUnitaryModel (idGram)

namespace CoordSU

@[expose] def negQ (p q : ℕ) : Subgroup (ZMod p)ˣ :=
  Subgroup.closure {u | (u : ZMod p) = -(q : ZMod p)}

theorem mem_negQ_of_eq {p q : ℕ} {u : (ZMod p)ˣ} (hu : (u : ZMod p) = -(q : ZMod p)) :
    u ∈ negQ p q :=
  Subgroup.subset_closure hu

theorem exists_ne_one_mem_negQ {p q : ℕ} (hcop : Nat.Coprime q p)
    (hpq : ¬ p ∣ q + 1) : ∃ u ∈ negQ p q, u ≠ 1 := by
  set u : (ZMod p)ˣ := -ZMod.unitOfCoprime q hcop with hudef
  have hu : (u : ZMod p) = -(q : ZMod p) := by
    simp [hudef]
  refine ⟨u, mem_negQ_of_eq hu, fun h1 => hpq ?_⟩
  have h3 : -(q : ZMod p) = 1 := by rw [← hu, h1, Units.val_one]
  have h2 : (q : ZMod p) + 1 = 0 := by linear_combination -h3
  exact (ZMod.natCast_eq_zero_iff (q + 1) p).mp (by exact_mod_cast h2)

theorem coprime_two_pow {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (f : ℕ) : Nat.Coprime (2 ^ f) p :=
  Nat.Coprime.pow_left f ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))

end CoordSU

@[expose] def GGSUNsCoordInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (f n : ℕ) (K : Type) [Field K], UnitaryFieldData 2 f K →
    ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 → ¬ p ∣ 2 ^ f + 1 →
    ∀ ψ₁ : ↥(unitarySU 2 f K n) →* G, SURep.GGFrameKer ψ₁ →
    ∀ Bs : Subgroup G, Bs ≤ ψ₁.range → IsElemAbelian p Bs → p ^ 4 ≤ Nat.card Bs →
      (∀ g ∈ ψ₁.range ⊓ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) →
      ∃ (r : ℕ) (ι : Multiplicative (Fin r → ZMod p) →* G),
        Function.Injective ι ∧ ι.range = Bs ∧
        (∀ (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ),
          (∀ i, η i ∈ CoordSU.negQ p (2 ^ f)) → ∏ i, η i = 1 →
          ∃ w ∈ ψ₁.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ s : Fin r → ZMod p,
            w⁻¹ * ι (ofAdd s) * w = ι (ofAdd fun i => (η i : ZMod p) * s (π i))) ∧
        (∀ (b : G) (L₁ : Subgroup G), b ∈ Bs → b ≠ 1 →
          IsComponentOf L₁ (ψ₁.range ⊓ Subgroup.centralizer {b}) →
          Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 →
          ∀ β : Fin r → ZMod p, ι (ofAdd β) = b →
            (∃ j j' : Fin r, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
              ∀ s : Fin r → ZMod p, s j = 0 → s j' = 0 → ι (ofAdd s) ∈ L₁) ∨
            (∃ (k : Fin r) (c : ZMod p) (ε : Fin r → (ZMod p)ˣ), c ≠ 0 ∧
              (∀ i, ε i ∈ CoordSU.negQ p (2 ^ f)) ∧
              (∀ i, i ≠ k → β i = (ε i : ZMod p) * c) ∧
              ∀ s : Fin r → ZMod p, s k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 →
                ι (ofAdd s) ∈ L₁)) ∧
        ∀ E J : Subgroup G, E ≤ Bs →
          IsComponentOf J (ψ₁.range ⊓ Subgroup.centralizer (E : Set G)) →
          Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ p ^ 3 →
          StepTwoToral.GGStepTwoCoordShape p r (CoordSU.negQ p (2 ^ f)) ι E

section Reduction

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem ggStepTwoCoordModelOn_PSU_of_coord (hcoord : GGSUNsCoordInput) :
    GGStepTwoCoordModelOn .PSU := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hlin
  have hns : ¬ p ∣ 2 ^ f + 1 := fun h' => hlin (Or.inr ⟨rfl, h'⟩)
  have hf1 : 1 ≤ f := hctx.2.2.2.1.1.2.1
  obtain ⟨f, rfl⟩ : ∃ f', f = f' + 1 := ⟨f - 1, by omega⟩
  classical
  have hF : Nat.card (GaloisField 2 (2 * (f + 1))) = (2 ^ (f + 1)) ^ 2 :=
    card_galoisField_two_mul 2 (f + 1) (Nat.le_add_left 1 f)
  have h : UnitaryFieldData 2 (f + 1) (GaloisField 2 (2 * (f + 1))) :=
    ⟨Nat.prime_two, by omega, by rw [hF, ← pow_mul, mul_comm]⟩
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hrank : 2 ≤ n / 2 := hctx.2.2.2.1.2
  have hn4 : 4 ≤ n := by omega
  obtain ⟨hrange, hker⟩ := hctx.2.2.2.2.1
  have hnq : (n, 2 ^ (f + 1)) ≠ (3, 2) := fun h' => by
    have : n = 3 := congrArg Prod.fst h'
    omega
  obtain ⟨P₀, hP₀⟩ := CFSG.LieType.Universal.Unitary.exists_wittMatrix hF n
  set ψ₁ := SURep.ggFrameU hF ψ P₀ hP₀ with hψ₁
  have hr₁ : ψ₁.range = ψ.range := SURep.range_ggFrameU hF ψ P₀ hP₀
  have hker₁ : ψ₁.ker ≤ Subgroup.center ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n) :=
    SURep.ker_ggFrameU_le hF ψ P₀ hP₀ hker
  have hFk₁ : SURep.GGFrameKer ψ₁ := SURep.ggFrameKer_of_ker_le_center hF (by omega) hnq hker₁
  have hC : Subgroup.centralizer (ψ₁.range : Set G) = ⊥ := by
    rw [hr₁, hrange]
    exact s1.1
  have hG₀ : ψ₁.range = ggG0 p B x L D J := hr₁.trans hrange
  have hBsel : IsElemAbelian p Bs := hctx.2.1.2.1
  have hEB : ∀ b ∈ Bs, ∃ B', B' ∈ primeFormUnitary h (idGram (GaloisField 2 (2 * (f + 1))) n) ∧
      (b, B') ∈ SUTorus.suPairs ψ₁ := by
    intro b hb
    obtain ⟨A, hA, hAc⟩ := InnerDiagSU.suInnerDiagConj hF hn4 G ψ hker b⁻¹
      (hctx.2.2.2.2.2.2.1.2 b⁻¹ (Bs.inv_mem hb))
    refine ⟨P₀ * A * P₀⁻¹,
      SUTorus.mem_primeFormUnitary_of_isIdUnitary h (InnerDiagSU.isIdUnitary_conj hP₀ hA),
      SUTorus.mem_suPairs_transfer P₀ hP₀ (CFSG.LieType.Universal.Unitary.SUid_eq_statedSU hF n)
        hA fun u => ?_⟩
    have := hAc u
    rwa [inv_inv] at this
  have hlift : ∀ b ∈ Bs, ∃ X : ↥(unitarySU 2 (f + 1) (GaloisField 2 (2 * (f + 1))) n),
      X ^ p = 1 ∧ ψ₁ X = b := fun b hb => by
    obtain ⟨B', hB'U, hB'⟩ := hEB b hb
    exact SUTB.exists_lift h (by omega) hnq hp hns hker₁ hC (hBsel.2 b hb) hB'U hB'
  have hBsle : Bs ≤ ψ₁.range := fun b hb => by
    obtain ⟨X, -, hX⟩ := hlift b hb
    exact ⟨X, hX⟩
  have hBs := hctx.bstar
  obtain ⟨r, ι, hιinj, hιrange, hmove, hcomp, hshape⟩ :=
    hcoord G (f + 1) n (GaloisField 2 (2 * (f + 1))) h p hp2 hns ψ₁ hFk₁ Bs hBsle hBsel
      hctx.pow_four_le_card_bstar (fun g hg hgp => hBs.2.2.2 g (Subgroup.mem_inf.mp hg).2 hgp)
  refine ⟨r, CoordSU.negQ p (2 ^ (f + 1)), ι,
    ⟨hιinj, hιrange, fun π η hη hprod => ?_, fun hr1 => ?_, fun b L₁ hpair β hβ => ?_⟩⟩
  ·
    obtain ⟨w, hw, hws⟩ := hmove π η hη hprod
    refine ⟨w, ?_, hws⟩
    rw [← hG₀]
    exact hw
  ·
    have hr4 : 4 ≤ r := hctx.four_le_of_range_eq hιrange
    have hrp : p + 1 ≤ r := StepTwoToral.succ_le_of_natCast_sub_one_eq_zero hr1 (by omega)
    have hDB : D ≤ ι.range := by
      rw [hιrange]
      exact hctx.d_le_bstar
    have hJ := hctx.j_isComponentOf_inf
    rw [← hG₀] at hJ
    obtain ⟨u, huO, hu1⟩ :=
      CoordSU.exists_ne_one_mem_negQ (CoordSU.coprime_two_pow hp hp2 (f + 1)) hns
    exact StepTwoToral.contrary_of_coordShape hDB hctx.card_d le_rfl huO hu1 hrp
      (hshape D J hctx.d_le_bstar hJ hctx.card_bstar_inf_centralizer_le)
  ·
    obtain ⟨hb, hb1, hcomp', hcard⟩ := hpair
    rw [← hG₀] at hcomp'
    exact hcomp b L₁ hb hb1 hcomp' hcard β hβ

theorem ggStepTwoToralWitnessOn_PSU_of_coord (hcoord : GGSUNsCoordInput) :
    GGStepTwoToralWitnessOn .PSU :=
  ggStepTwoToralWitnessOn_of_coordModel (ggStepTwoCoordModelOn_PSU_of_coord hcoord)

end Reduction

end CFSG.StandardType

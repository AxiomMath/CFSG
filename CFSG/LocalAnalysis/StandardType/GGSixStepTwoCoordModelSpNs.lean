module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContrary
public import CFSG.LocalAnalysis.StandardType.GGSpNonsplitFrame

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.LieType.Universal.Symplectic Multiplicative

namespace CoordSpNs

@[expose] def galSigns (p q : ℕ) : Subgroup (ZMod p)ˣ :=
  Subgroup.closure {u | (u : ZMod p) = q ∨ (u : ZMod p) = -1}

theorem neg_one_mem_galSigns (p q : ℕ) : (-1 : (ZMod p)ˣ) ∈ galSigns p q :=
  Subgroup.subset_closure (Or.inr (by simp))

theorem neg_one_ne_one {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) : (-1 : (ZMod p)ˣ) ≠ 1 := by
  have : Fact (2 < p) := ⟨by have := (Fact.out : p.Prime).two_le; omega⟩
  intro h
  have h' := congrArg Units.val h
  rw [Units.val_neg, Units.val_one] at h'
  exact ZMod.neg_one_ne_one h'

theorem le_range_of_innerDiag {G : Type} [Group G] {n f : ℕ} (hrk : 2 ≤ n)
    (ψ : StatedSp n (GaloisField 2 f) →* G)
    (hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)))
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hdiag : ∀ b ∈ Bs, GGPsiInnerDiag (Symplectic.rootDatum n (GaloisField 2 f)) ψ b) :
    Bs ≤ ψ.range := by
  intro b hb
  obtain ⟨g, hg, hcg⟩ := PsiDiag.Symp.exists_mem_centralizer (F := GaloisField 2 f) hrk ψ hker
    (hdiag b hb)
  rw [hC, Subgroup.mem_bot] at hcg
  rw [eq_inv_of_mul_eq_one_left hcg]
  exact ψ.range.inv_mem hg

end CoordSpNs

@[expose] def GGSpNsCoordInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Finite F] [CharP F 2] (n p : ℕ)
    [Fact p.Prime], p ≠ 2 → ¬ p ∣ Nat.card F - 1 →
    ∀ ψ : StatedSp n F →* G, Function.Injective ψ →
    ∀ Bs : Subgroup G, Bs ≤ ψ.range → IsElemAbelian p Bs → p ^ 4 ≤ Nat.card Bs →
      (∀ g ∈ ψ.range ⊓ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) →
      ∃ (r : ℕ) (ι : Multiplicative (Fin r → ZMod p) →* G),
        Function.Injective ι ∧ ι.range = Bs ∧
        (∀ (π : Equiv.Perm (Fin r)) (η : Fin r → (ZMod p)ˣ),
          (∀ i, η i ∈ CoordSpNs.galSigns p (Nat.card F)) → ∏ i, η i = 1 →
          ∃ w ∈ ψ.range ⊓ Subgroup.normalizer (Bs : Set G), ∀ s : Fin r → ZMod p,
            w⁻¹ * ι (ofAdd s) * w = ι (ofAdd fun i => (η i : ZMod p) * s (π i))) ∧
        (∀ (b : G) (L₁ : Subgroup G), b ∈ Bs → b ≠ 1 →
          IsComponentOf L₁ (ψ.range ⊓ Subgroup.centralizer {b}) →
          Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 →
          ∀ β : Fin r → ZMod p, ι (ofAdd β) = b →
            (∃ j j' : Fin r, (∀ i, i ≠ j → i ≠ j' → β i = 0) ∧
              ∀ s : Fin r → ZMod p, s j = 0 → s j' = 0 → ι (ofAdd s) ∈ L₁) ∨
            (∃ (k : Fin r) (c : ZMod p) (ε : Fin r → (ZMod p)ˣ), c ≠ 0 ∧
              (∀ i, ε i ∈ CoordSpNs.galSigns p (Nat.card F)) ∧
              (∀ i, i ≠ k → β i = (ε i : ZMod p) * c) ∧
              ∀ s : Fin r → ZMod p, s k = 0 → ∑ i, (↑(ε i)⁻¹ : ZMod p) * s i = 0 →
                ι (ofAdd s) ∈ L₁)) ∧
        ∀ E J : Subgroup G, E ≤ Bs →
          IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E : Set G)) →
          Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ p ^ 3 →
          StepTwoToral.GGStepTwoCoordShape p r (CoordSpNs.galSigns p (Nat.card F)) ι E

section Reduction

theorem ggSpCoordModelNonsplitInput_of_coord (h : GGSpNsCoordInput) :
    GGSpCoordModelNonsplitInput := by
  intro G _ _ p B Bs x L D J n f ψ hctx s1 hns
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have : Fact p.Prime := ⟨hp⟩
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hrk : 2 ≤ n := hctx.2.2.2.1.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)) := hctx.2.2.2.2.1.2
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz := hker ha
    rw [Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  have hG₀ : ψ.range = ggG0 p B x L D J := hctx.range_eq
  have hC : Subgroup.centralizer (ψ.range : Set G) = ⊥ := by
    rw [hG₀]
    exact s1.1
  have hmem : Bs ≤ ψ.range :=
    CoordSpNs.le_range_of_innerDiag hrk ψ hker hC (fun b hb => hctx.2.2.2.2.2.2.1.2 b hb)
  have hBs := hctx.bstar
  obtain ⟨r, ι, hιinj, hrange, hmove, hcomp, hshape⟩ :=
    h G (GaloisField 2 f) n p hp2 hpF ψ hinj Bs hmem hBs.2.1 hctx.pow_four_le_card_bstar
      (fun g hg hgp => hBs.2.2.2 g (Subgroup.mem_inf.mp hg).2 hgp)
  refine ⟨r, CoordSpNs.galSigns p (Nat.card (GaloisField 2 f)), ι,
    ⟨hιinj, hrange, fun π η hη hprod => ?_, fun hr1 => ?_, fun b L₁ hpair β hβ => ?_⟩⟩
  ·
    obtain ⟨w, hw, hws⟩ := hmove π η hη hprod
    exact ⟨w, hG₀ ▸ hw, hws⟩
  ·
    have hr4 : 4 ≤ r := hctx.four_le_of_range_eq hrange
    have hrp : p + 1 ≤ r := StepTwoToral.succ_le_of_natCast_sub_one_eq_zero hr1 (by omega)
    have hDB : D ≤ ι.range := by
      rw [hrange]
      exact hctx.d_le_bstar
    have hJ := hctx.j_isComponentOf_inf
    rw [← hG₀] at hJ
    exact StepTwoToral.contrary_of_coordShape hDB hctx.card_d le_rfl
      (CoordSpNs.neg_one_mem_galSigns _ _) (CoordSpNs.neg_one_ne_one hp2) hrp
      (hshape D J hctx.d_le_bstar hJ hctx.card_bstar_inf_centralizer_le)
  ·
    obtain ⟨hb, hb1, hcomp', hcard⟩ := hpair
    rw [← hG₀] at hcomp'
    exact hcomp b L₁ hb hb1 hcomp' hcard β hβ

end Reduction

end CFSG.StandardType

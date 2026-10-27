module

public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordContraryCore
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSLComp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSp
public import CFSG.LocalAnalysis.StandardType.GGSixStepOneCompDefs

public section

open Polynomial

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank Multiplicative

section Config

variable {G : Type} [Group G] [Finite G] {U : Type} [Group U] {p : ℕ} {B Bs : Subgroup G}
  {x : G} {L D J : Subgroup G} {Δ : UniversalRootDatum U} {t : StatedLieTag} {n f : ℕ}
  {ψ : U →* G}

theorem GGSixCtxV2.pow_four_le_card_bstar (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    p ^ 4 ≤ Nat.card Bs := by
  have hB : Nat.card B = p ^ LargeEvenTwoLocalRank p G := h.sstar.1.2.1
  have h4 : 4 ≤ LargeEvenTwoLocalRank p G := h.beta.2.2.2
  calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right h.prime.pos h4
    _ = Nat.card B := hB.symm
    _ ≤ Nat.card Bs := Subgroup.card_le_of_le h.bstar.1

theorem GGSixCtxV2.four_le_of_range_eq (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) {r : ℕ}
    {ι : Multiplicative (Fin r → ZMod p) →* G} (hι : ι.range = Bs) : 4 ≤ r := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hcard : Nat.card ι.range ≤ p ^ r := by
    calc Nat.card ι.range ≤ Nat.card (Multiplicative (Fin r → ZMod p)) :=
          Nat.card_le_card_of_surjective _ ι.rangeRestrict_surjective
      _ = p ^ r := by
          rw [Nat.card_congr Multiplicative.toAdd, Nat.card_fun, Nat.card_zmod,
            Nat.card_eq_fintype_card (α := Fin r), Fintype.card_fin]
  rw [hι] at hcard
  exact (pow_le_pow_iff_right₀ hp.one_lt).mp (h.pow_four_le_card_bstar.trans hcard)

theorem GGSixCtxV2.card_bstar_inf_centralizer_le (h : GGSixCtxV2 p B Bs x L D J Δ t n f ψ) :
    Nat.card (Bs ⊓ Subgroup.centralizer (J : Set G) : Subgroup G) ≤ p ^ 3 := by
  set H : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G) with hH
  have hD : D = B ⊓ Subgroup.centralizer (J : Set G) := h.stdSub.1.2.2.2.2.2.2
  have hBBs : B ≤ Bs := h.bstar.1
  have hBH : B ⊓ H = D := by rw [hH, hD, ← inf_assoc, inf_eq_left.mpr hBBs]
  have h1 := Subgroup.relIndex_mul_card B H
  have h2 := Subgroup.relIndex_mul_card B Bs
  rw [inf_eq_left.mpr hBBs] at h2
  have hpos : 0 < Nat.card B := Nat.card_pos
  have hBs : Nat.card Bs ≤ p * Nat.card B := h.bstar.2.2.1
  have hidx : B.relIndex Bs ≤ p := by
    rw [← h2] at hBs
    exact Nat.le_of_mul_le_mul_right hBs hpos
  have hne : B.relIndex Bs ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (Nat.card_pos (α := Bs)).ne' h2.symm
  have hle : B.relIndex H ≤ B.relIndex Bs := Subgroup.relIndex_le_of_le_right inf_le_left hne
  rw [hBH, h.card_d] at h1
  calc Nat.card H = B.relIndex H * p ^ 2 := h1.symm
    _ ≤ p * p ^ 2 := Nat.mul_le_mul_right _ (hle.trans hidx)
    _ = p ^ 3 := by ring

end Config

namespace CoordSL

theorem exists_ne_one_mem_galExp {K : Type} [Field K] [Finite K] {g : K[X]} [Fact (Irreducible g)]
    {p : ℕ} [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1) (hcop : Nat.Coprime (Nat.card K) p)
    (hK : ¬ p ∣ Nat.card K - 1) : ∃ u ∈ galExp g hζ, u ≠ 1 := by
  let := Fintype.ofFinite K
  have : Module.Finite K (AdjoinRoot g) := (rootPB g).finite
  have : Algebra.IsAlgebraic K (AdjoinRoot g) := Algebra.IsAlgebraic.of_finite K (AdjoinRoot g)
  have hq : Nat.card K = Fintype.card K := Nat.card_eq_fintype_card
  refine ⟨ZMod.unitOfCoprime (Nat.card K) hcop,
    ⟨FiniteField.frobeniusAlgEquivOfAlgebraic K (AdjoinRoot g), ?_⟩, ?_⟩
  · change AdjoinRoot.root g ^ Fintype.card K = _
    rw [ZMod.coe_unitOfCoprime, ZMod.val_natCast, ← hq]
    exact pow_eq_pow_mod _ hζ
  · intro h1
    apply hK
    have hval : ((Nat.card K : ℕ) : ZMod p) = 1 := by
      rw [← ZMod.coe_unitOfCoprime (Nat.card K) hcop, h1, Units.val_one]
    have hpos : 1 ≤ Nat.card K := Nat.card_pos
    rw [← ZMod.natCast_eq_zero_iff, Nat.cast_sub hpos, hval, Nat.cast_one, sub_self]

theorem root_eq_one_or_dvd_cyclotomic {K : Type} [Field K] {g : K[X]} [Fact (Irreducible g)]
    {p : ℕ} [Fact p.Prime] (hζ : AdjoinRoot.root g ^ p = 1) :
    AdjoinRoot.root g = 1 ∨ g ∣ cyclotomic p K := by
  have hdvd : g ∣ X ^ p - 1 := by
    rw [← AdjoinRoot.mk_eq_zero, map_sub, map_pow, AdjoinRoot.mk_X, map_one, hζ, sub_self]
  rw [← cyclotomic_prime_mul_X_sub_one K p] at hdvd
  rcases (Fact.out : Irreducible g).prime.dvd_or_dvd hdvd with h | h
  · exact Or.inr h
  · left
    have h0 : AdjoinRoot.mk g (X - 1) = 0 := AdjoinRoot.mk_eq_zero.mpr h
    rw [map_sub, AdjoinRoot.mk_X, map_one, sub_eq_zero] at h0
    exact h0

theorem range_frameHom_eq_bot_of_root_eq_one {G : Type} [Group G] {K : Type} [Field K]
    {g : K[X]} [Fact (Irreducible g)] {n s r p : ℕ} [NeZero p]
    (ψ : Matrix.SpecialLinearGroup (Fin n) K →* G) (A₀ : Matrix.SpecialLinearGroup (Fin n) K)
    (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r) (hC : (rootMat g).det = 1)
    (hCp : rootMat g ^ p = 1) (h1 : AdjoinRoot.root g = 1) :
    (frameHom ψ A₀ ε hC hCp).range = ⊥ := by
  have hC1 : rootMat g ^ 1 = 1 := by rw [pow_one, rootMat, h1, map_one]
  rw [eq_bot_iff]
  rintro _ ⟨a, rfl⟩
  rw [Subgroup.mem_bot]
  change SLRep.ggFrame ψ A₀ (SLNS.nsSL ε hC fun i => (toAdd a i).val) = 1
  rw [SLNS.nsSL_congr ε hC hC1 (k' := 0) (fun i => by simp only [Nat.mod_one]), SLNS.nsSL_zero,
    map_one]

end CoordSL

section Inputs

open CoordSL

@[expose] def GGSLCoordCompShapeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Finite F] [CharP F 2] (n p : ℕ)
    [Fact p.Prime], p ≠ 2 → ¬ p ∣ Nat.card F - 1 →
    ∀ ψ : Matrix.SpecialLinearGroup (Fin n) F →* G,
      ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin n) F) →
    ∀ (g : F[X]) [Fact (Irreducible g)], g ∣ cyclotomic p F →
    ∀ (s r : ℕ) (ε : Fin n ≃ (Fin (rootPB g).dim × Fin s) ⊕ Fin r)
      (A₀ : Matrix.SpecialLinearGroup (Fin n) F) (hC : (rootMat g).det = 1)
      (hCp : rootMat g ^ p = 1) (hζ : AdjoinRoot.root g ^ p = 1), 0 < s →
    ∀ E J : Subgroup G, E ≤ (frameHom ψ A₀ ε hC hCp).range →
      IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E : Set G)) →
      Nat.card ((frameHom ψ A₀ ε hC hCp).range ⊓ Subgroup.centralizer (J : Set G) :
        Subgroup G) ≤ p ^ 3 →
      StepTwoToral.GGStepTwoCoordShape p s (galExp g hζ) (frameHom ψ A₀ ε hC hCp) E

@[expose] def GGSpCoordCompShapeInput : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (F : Type) [Field F] [Finite F] [CharP F 2] (n p : ℕ)
    [Fact p.Prime], p ≠ 2 → p ∣ Nat.card F - 1 →
    ∀ ψ : StatedSp n F →* G, Function.Injective ψ →
    ∀ (A₀ : StatedSp n F) (ζ : Fˣ) (hζ : ζ ^ p = 1), orderOf ζ = p → 0 < n →
    ∀ E J : Subgroup G, E ≤ (CoordSp.frameHom ψ A₀ hζ).range →
      IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (E : Set G)) →
      Nat.card ((CoordSp.frameHom ψ A₀ hζ).range ⊓ Subgroup.centralizer (J : Set G) :
        Subgroup G) ≤ p ^ 3 →
      StepTwoToral.GGStepTwoCoordShape p n (CoordSp.signs p) (CoordSp.frameHom ψ A₀ hζ) E

end Inputs

section Reductions

open CoordSL

theorem ggSLCoordContraryInput_of_compShape (hshape : GGSLCoordCompShapeInput) :
    GGSLCoordContraryInput := by
  intro G _ _ p _ B Bs x L D J m f ψ hctx _ hns g _ s r ε A₀ hC hCp hζ hrange hs1
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : ¬ p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hcop : Nat.Coprime (Nat.card (GaloisField 2 f)) p := by
    rw [hcardF]
    exact Nat.Coprime.pow_left f ((Nat.coprime_primes Nat.prime_two hp).mpr (Ne.symm hp2))
  have hs4 : 4 ≤ s := hctx.four_le_of_range_eq hrange
  have hsp : p + 1 ≤ s := StepTwoToral.succ_le_of_natCast_sub_one_eq_zero hs1 (by omega)
  obtain ⟨u, huO, hu1⟩ := exists_ne_one_mem_galExp hζ hcop hpF
  have hDB : D ≤ (frameHom ψ A₀ ε hC hCp).range := by
    rw [hrange]
    exact hctx.d_le_bstar
  rcases root_eq_one_or_dvd_cyclotomic hζ with h1 | hgd
  · exfalso
    have hbot := range_frameHom_eq_bot_of_root_eq_one ψ A₀ ε hC hCp h1
    rw [hrange] at hbot
    have h4 := hctx.pow_four_le_card_bstar
    rw [hbot, Subgroup.card_bot] at h4
    have : 1 < p ^ 4 := Nat.one_lt_pow (by norm_num) hp.one_lt
    omega
  have hker : ψ.ker ≤
      Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) (GaloisField 2 f)) :=
    hctx.2.2.2.2.1.2
  have hJ := hctx.j_isComponentOf_inf
  rw [← hctx.range_eq] at hJ
  have hcard := hctx.card_bstar_inf_centralizer_le
  rw [← hrange] at hcard
  exact StepTwoToral.contrary_of_coordShape hDB hctx.card_d le_rfl huO hu1 hsp
    (hshape G (GaloisField 2 f) (m + 1) p hp2 hpF ψ hker g hgd s r ε A₀ hC hCp hζ (by omega) D J
      hDB hJ hcard)

theorem ggStepTwoCoordModelOn_PSL_of_compShape (hshape : GGSLCoordCompShapeInput) :
    GGStepTwoCoordModelOn .PSL :=
  ggStepTwoCoordModelOn_PSL_of_contrary (ggSLCoordContraryInput_of_compShape hshape)

open CFSG.LieType.Universal.Symplectic CoordSp in
theorem ggSpCoordContraryInput_of_compShape (hshape : GGSpCoordCompShapeInput) :
    GGSpCoordContraryInput := by
  intro G _ _ p _ B Bs x L D J n f ψ hctx _ hsplit A₀ ζ hζ hζo hrange hn1
  have hp : p.Prime := hctx.prime
  have hp2 : p ≠ 2 := hctx.ne_two
  have hf : 1 ≤ f := hctx.2.2.2.1.1.2.1
  have hrk : 2 ≤ n := hctx.2.2.2.1.2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardF : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hpF : p ∣ Nat.card (GaloisField 2 f) - 1 := by rwa [hcardF]
  have hker : ψ.ker ≤ Subgroup.center (StatedSp n (GaloisField 2 f)) := hctx.2.2.2.2.1.2
  have hinj : Function.Injective ψ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hz := hker ha
    rw [Symplectic.center_eq,
      CFSG.LieType.SteinbergBR.EvenSp.statedScalars_subgroupOf_statedSp (by omega)] at hz
    exact Subgroup.mem_bot.mp hz
  have hn4 : 4 ≤ n := hctx.four_le_of_range_eq hrange
  have hnp : p + 1 ≤ n := StepTwoToral.succ_le_of_natCast_sub_one_eq_zero hn1 (by omega)
  have : Fact (2 < p) := ⟨by have := hp.two_le; omega⟩
  have hu1 : (-1 : (ZMod p)ˣ) ≠ 1 := by
    intro h
    have h' := congrArg Units.val h
    rw [Units.val_neg, Units.val_one] at h'
    exact ZMod.neg_one_ne_one h'
  have hDB : D ≤ (frameHom ψ A₀ hζ).range := by
    rw [hrange]
    exact hctx.d_le_bstar
  have hJ := hctx.j_isComponentOf_inf
  rw [← hctx.range_eq] at hJ
  have hcard := hctx.card_bstar_inf_centralizer_le
  rw [← hrange] at hcard
  exact StepTwoToral.contrary_of_coordShape hDB hctx.card_d le_rfl
    (mem_signs.mpr (Or.inr rfl)) hu1 hnp
    (hshape G (GaloisField 2 f) n p hp2 hpF ψ hinj A₀ ζ hζ hζo (by omega) D J hDB hJ hcard)

theorem ggStepTwoCoordModelOn_PSp_of_compShape (hcomp : GGSpCoordCompInput)
    (hshape : GGSpCoordCompShapeInput) (hns : GGSpCoordModelNonsplitInput) :
    GGStepTwoCoordModelOn .PSp :=
  ggStepTwoCoordModelOn_PSp_of_inputs hcomp (ggSpCoordContraryInput_of_compShape hshape) hns

theorem ggStepTwoToralWitnessOn_PSL_of_compShape (hshape : GGSLCoordCompShapeInput) :
    GGStepTwoToralWitnessOn .PSL :=
  ggStepTwoToralWitnessOn_of_coordModel (ggStepTwoCoordModelOn_PSL_of_compShape hshape)

theorem ggStepTwoToralWitnessOn_PSp_of_compShape (hcomp : GGSpCoordCompInput)
    (hshape : GGSpCoordCompShapeInput) (hns : GGSpCoordModelNonsplitInput) :
    GGStepTwoToralWitnessOn .PSp :=
  ggStepTwoToralWitnessOn_of_coordModel
    (ggStepTwoCoordModelOn_PSp_of_compShape hcomp hshape hns)

end Reductions

end CFSG.StandardType

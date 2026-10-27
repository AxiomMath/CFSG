module

public import CFSG.RankThree.PartOne.AUTSL.KF1514S0
public import CFSG.RankThree.PartOne.AUTSL.OmegaModel
public import CFSG.RankThree.PartOne.S15K.OrthModel
public import CFSG.RankThree.PartOne.KF1514B.Row3
public import CFSG.RankThree.PartOne.KF1514B.Row4
import CFSG.Timmesfeld.Orders.Classical
public import CFSG.RankThree.PartOne.AUTSL.OmegaFamily

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.KF1514B

open CFSG CFSG.RankThree.PartOne.AUTSL CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.ComponentClassification
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.Assembly.LowTwoRank
  CFSG.ClassicalGroups.Orthogonal CFSG.Assembly.RankThreeEven Matrix
  CFSG.RankThree.PartOne.S15K

section Equiv

variable {f : ℕ} (hf : 1 ≤ f) {b c : GaloisField 2 f}

noncomputable def modelEquiv (hirr : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) :
    OmegaMinusModel f b c ≃* ↥(omegaG0 (GaloisField 2 f) b c) := by
  have h14 : (1 : ℕ) ≤ 4 := by norm_num
  have hreg := regular_coordinateQuadMinus 4 (GaloisField 2 f) b c (le_refl 4) hirr
  have hQ : ∃ v, coordinateQuadMinus 4 (GaloisField 2 f) h14 b c v ≠ 0 :=
    exists_ne_zero_of_polar_nondegenerate (by norm_num) _ hreg.1
  let e₀ : OmegaMinusModel f b c ≃* StatedProj (StatedOmega (StatedQuadMinus 4 (GaloisField 2 f) b c)) :=
    (statedProjEquivRefl (projImage_statedOmegaMinus_eq_projOmegaMinus 4 (GaloisField 2 f) b c)).symm
  let Ψ : OmegaMinusModel f b c ≃* matrixDerived (coordinateQuadMinus 4 (GaloisField 2 f) h14 b c) :=
    (coordinateMinusWitnessEquiv (GaloisField 2 f) h14 b c e₀).trans (derivedProjEquiv _ hQ).symm
  have hE := commutator_coordinateQuadMinus 4 (GaloisField 2 f) b c (le_refl 4) hirr
  let ψ : (quadTail (4 - 1) (minusTailForm (GaloisField 2 f) b c)).IsometryEquiv
      (coordinateQuadMinus 4 (GaloisField 2 f) (by norm_num) b c) :=
    (minusTailIsometry 4 (GaloisField 2 f) b c).trans
      (coordinateMinusIsometry 4 (GaloisField 2 f) (by norm_num) b c)
  let Φ : StatedOmega ⇑(coordinateQuadMinus 4 (GaloisField 2 f) (by norm_num) b c) ≃*
      omegaG0 (GaloisField 2 f) b c := tailOmegaEquiv ψ rfl hE
  exact (Ψ.trans (MulEquiv.subgroupCongr (matrixDerived_eq_statedOmega _))).trans Φ

end Equiv

section Sylow2

variable {f : ℕ} {b c : GaloisField 2 f}

theorem isSylowOf_U0 (hirr : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) :
    IsSylowOf 2 ((U0 b c).subgroupOf (G0 b c)) ⊤ := by
  have : AnisoPair b c := ⟨hirr⟩
  have hani := anisotropic_minusTailForm hirr
  have hreg := nondegenerate_minusTailForm hirr
  have hm : Module.finrank (GaloisField 2 f) (Fin 2 → GaloisField 2 f) = 1 ∨
      Module.finrank (GaloisField 2 f) (Fin 2 → GaloisField 2 f) = 2 := Or.inr finrank_fin_two_fun
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨S, hS⟩, -⟩ := orthogonal_geometry_tail_Sylow_flag_normalizer (p := 2)
    (by norm_num : 3 ≤ 3) hani hreg hm
  refine ⟨le_top, ?_, ?_⟩
  · rw [← hS]
    exact S.isPGroup'
  · rw [Subgroup.relIndex_top_right, ← hS]
    exact S.not_dvd_index

theorem exists_embedding (hirr : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0)
    {U : Subgroup (OmegaMinusModel f b c)} (hU : IsSylowOf 2 U ⊤) :
    ∃ ρ : ↥(⊤ : Subgroup (OmegaMinusModel f b c)) →*
      (Vt (GaloisField 2 f) ≃ₗ[GaloisField 2 f] Vt (GaloisField 2 f)),
      Function.Injective ρ ∧ ρ.range = G0 b c ∧ U5K.rm ⊤ ρ U = U0 b c := by
  have : AnisoPair b c := ⟨hirr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let Θ : OmegaMinusModel f b c ≃* ↥(G0 b c) := modelEquiv hirr
  have : Finite ↥(G0 b c) := inferInstance
  have hU' : IsSylowOf 2 (U.map Θ.toMonoidHom) ⊤ := by
    refine ⟨le_top, hU.2.1.map _, ?_⟩
    rw [Subgroup.relIndex_top_right]
    have hidx : (U.map Θ.toMonoidHom).index = U.index := Subgroup.index_map_equiv U Θ
    rw [hidx]
    have := hU.2.2
    rwa [Subgroup.relIndex_top_right] at this
  obtain ⟨x, -, hx⟩ := AUTSL.exists_conj_isSylowOf (isSylowOf_U0 hirr) hU'
  let Θ' : OmegaMinusModel f b c ≃* ↥(G0 b c) := Θ.trans (MulAut.conj x⁻¹)
  have hUΘ : U.map Θ'.toMonoidHom = (U0 b c).subgroupOf (G0 b c) := by
    have e : Θ'.toMonoidHom = (MulAut.conj x⁻¹).toMonoidHom.comp Θ.toMonoidHom := rfl
    rw [e, ← Subgroup.map_map, hx, Subgroup.map_map]
    have : (MulAut.conj x⁻¹).toMonoidHom.comp (MulAut.conj x).toMonoidHom = MonoidHom.id _ :=
      MonoidHom.ext fun y => by
        show x⁻¹ * (x * y * x⁻¹) * x⁻¹⁻¹ = y
        group
    rw [this, Subgroup.map_id]
  let ρ : ↥(⊤ : Subgroup (OmegaMinusModel f b c)) →*
      (Vt (GaloisField 2 f) ≃ₗ[GaloisField 2 f] Vt (GaloisField 2 f)) :=
    (G0 b c).subtype.comp (Θ'.toMonoidHom.comp (Subgroup.topEquiv).toMonoidHom)
  refine ⟨ρ, ?_, ?_, ?_⟩
  · exact Subtype.val_injective.comp (Θ'.injective.comp Subgroup.topEquiv.injective)
  · ext y
    constructor
    · rintro ⟨z, rfl⟩
      exact (Θ' z.1).2
    · intro hy
      obtain ⟨u, hu⟩ := Θ'.surjective ⟨y, hy⟩
      exact ⟨⟨u, trivial⟩, congrArg Subtype.val hu⟩
  · ext y
    rw [U5K.mem_rm]
    constructor
    · rintro ⟨u, hu1, hu2, rfl⟩
      have : Θ' u ∈ (U0 b c).subgroupOf (G0 b c) := by
        rw [← hUΘ]
        exact Subgroup.mem_map_of_mem _ hu2
      exact this
    · intro hy
      have hyG : y ∈ G0 b c := tailUnipotent_le hy
      have : (⟨y, hyG⟩ : ↥(G0 b c)) ∈ U.map Θ'.toMonoidHom := by
        rw [hUΘ]
        exact hy
      obtain ⟨u, hu, hu2⟩ := this
      exact ⟨u, trivial, hu, congrArg Subtype.val hu2⟩

theorem transport {p : ℕ} [Fact p.Prime] (hirr : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0)
    {U A₀ : Subgroup (OmegaMinusModel f b c)} (hU : IsSylowOf 2 U ⊤)
    (hexp : ∀ a ∈ A₀, a ^ p = 1)
    (H : ∀ A : Subgroup (Vt (GaloisField 2 f) ≃ₗ[GaloisField 2 f] Vt (GaloisField 2 f)),
      A ≤ G0 b c → (∀ a ∈ A, a ^ p = 1) →
        AUTSL.MCl1 p (G0 b c) A (U0 b c) ∧ AUTSL.MCl2 p (G0 b c) A (U0 b c)) :
    AUTSL.Cl1 p ⊤ ⊤ U A₀ ∧ AUTSL.Cl2 p ⊤ ⊤ U A₀ := by
  have : AnisoPair b c := ⟨hirr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hG0 : Finite ↥(G0 b c) := inferInstance
  have : Finite (OmegaMinusModel f b c) := Finite.of_equiv ↥(G0 b c) (modelEquiv hirr).symm.toEquiv
  obtain ⟨ρ, hρinj, hρrange, hρU⟩ := exists_embedding hirr hU
  have hA'G : U5K.rm ⊤ ρ A₀ ≤ G0 b c := by
    rw [← hρrange]
    exact U5K.rm_le_range _
  have hA'exp : ∀ a ∈ U5K.rm ⊤ ρ A₀, a ^ p = 1 := by
    intro a ha
    obtain ⟨x, hx, hxA, rfl⟩ := U5K.mem_rm.1 ha
    rw [← map_pow]
    have : (⟨x, hx⟩ : ↥(⊤ : Subgroup (OmegaMinusModel f b c))) ^ p = 1 :=
      Subtype.ext (hexp x hxA)
    rw [this, map_one]
  obtain ⟨h1, h2⟩ := H _ hA'G hA'exp
  refine AUTSL.clauses_of_model ρ (le_refl _) (fun x _ => by rw [Subgroup.mem_normalizer_iff]; intro h; simp) hU le_top hρinj ?_ ?_
  · rw [hρrange, hρU]
    exact h1
  · rw [hρrange, hρU]
    exact h2

theorem card_G0 (hf : 1 ≤ f) (hirr : ∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(G0 b c) = (2 ^ f) ^ 12 * ((2 ^ f) ^ 4 + 1) *
      (((2 ^ f) ^ 2 - 1) * ((2 ^ f) ^ 4 - 1) * ((2 ^ f) ^ 6 - 1)) := by
  have hC := statedClassicalModel_of_projOmegaMinus hf hirr
    (MulEquiv.refl (projOmegaMinus 3 (GaloisField 2 f) b c))
  have hcardΩ : Nat.card (OmegaMinusModel f b c) = CFSG.Open.ordTwistedD 4 (2 ^ f) :=
    (CFSG.Timmesfeld.card_statedClassicalModel_two hC).2.2.2.2 rfl
  have hodd : Odd ((2 ^ f) ^ 4 + 1) := by
    have h2 : Even ((2 ^ f) ^ 4) :=
      (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩)
    exact h2.add_one
  have hgcd : Nat.gcd 4 ((2 ^ f) ^ 4 + 1) = 1 := by
    have : Nat.Coprime (2 ^ 2) ((2 ^ f) ^ 4 + 1) :=
      Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hodd)
    simpa using this
  have hΘ : Nat.card ↥(G0 b c) = Nat.card (OmegaMinusModel f b c) :=
    Nat.card_congr (modelEquiv hirr).toEquiv.symm
  rw [hΘ, hcardΩ, CFSG.Open.ordTwistedD, hgcd, Nat.div_one]
  have hIcc : Finset.Icc 1 (4 - 1) = {1, 2, 3} := by decide
  rw [hIcc]
  simp [Finset.prod_insert, mul_assoc]

end Sylow2

section Final

theorem kf1514PModel_three : AUTSL.KF1514PModel 3 := by
  intro p f b c hp hp5 hf hcong hirr U A₀ hU hA _
  have : Fact p.Prime := ⟨hp⟩
  have : AnisoPair b c := ⟨hirr⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hcardG : Nat.card ↥(G0 b c) = (Nat.card (GaloisField 2 f)) ^ 12 *
      ((Nat.card (GaloisField 2 f)) ^ 4 + 1) * (((Nat.card (GaloisField 2 f)) ^ 2 - 1) *
        ((Nat.card (GaloisField 2 f)) ^ 4 - 1) * ((Nat.card (GaloisField 2 f)) ^ 6 - 1)) := by
    rw [hK]
    exact card_G0 hf hirr
  have hpq : p ∣ Nat.card (GaloisField 2 f) - 1 := by
    rw [hK]
    exact hcong
  have hexp : ∀ a ∈ A₀, a ^ p = 1 :=
    ((CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff).1 hA).2
  have hH : ∀ A : Subgroup (Vt (GaloisField 2 f) ≃ₗ[GaloisField 2 f] Vt (GaloisField 2 f)),
      A ≤ G0 b c → (∀ a ∈ A, a ^ p = 1) →
        AUTSL.MCl1 p (G0 b c) A (U0 b c) ∧ AUTSL.MCl2 p (G0 b c) A (U0 b c) := by
    intro A hAG hAexp
    refine ⟨?_, ?_⟩
    · obtain ⟨h, hh, hle⟩ := row3_clause_one hp5 hcardG hpq hAG hAexp
      exact ⟨h, hh, A, le_rfl, Nat.le_mul_of_pos_left _ hp.pos, hle⟩
    · obtain ⟨h, hh, B, hBA, hBc, hle⟩ := row3_clause_two hp5 hcardG hpq hAG hAexp
      exact ⟨x0 b c, x0_mem_omegaOneCenterIn, x0_ne_one, h, hh, B, hBA, hBc, hle⟩
  obtain ⟨hcl1, hcl2⟩ := transport hirr hU hexp hH
  obtain ⟨h, -, B, hB, hcard, hle⟩ := hcl1
  obtain ⟨x, hx, hx1, h', -, B', hB', hcard', hle'⟩ := hcl2
  exact ⟨⟨h, B, hB, hcard, hle.trans inf_le_right⟩,
    ⟨x, hx, hx1, h', B', hB', hcard', hle'.trans inf_le_right⟩⟩

theorem kf1514PModel_four : AUTSL.KF1514PModel 4 := by
  intro p f b c hp hp5 hf hcong hirr U A₀ hU hA _
  have : Fact p.Prime := ⟨hp⟩
  have : AnisoPair b c := ⟨hirr⟩
  have hK : Nat.card (GaloisField 2 f) = 2 ^ f := GaloisField.card 2 f (by omega)
  have hcardG : Nat.card ↥(G0 b c) = (Nat.card (GaloisField 2 f)) ^ 12 *
      ((Nat.card (GaloisField 2 f)) ^ 4 + 1) * (((Nat.card (GaloisField 2 f)) ^ 2 - 1) *
        ((Nat.card (GaloisField 2 f)) ^ 4 - 1) * ((Nat.card (GaloisField 2 f)) ^ 6 - 1)) := by
    rw [hK]
    exact card_G0 hf hirr
  have hpq : p ∣ Nat.card (GaloisField 2 f) + 1 := by
    rw [hK]
    exact hcong
  have hexp : ∀ a ∈ A₀, a ^ p = 1 :=
    ((CFSG.Quasithin.BlueprintB2.isElementaryAbelian_iff).1 hA).2
  have hH : ∀ A : Subgroup (Vt (GaloisField 2 f) ≃ₗ[GaloisField 2 f] Vt (GaloisField 2 f)),
      A ≤ G0 b c → (∀ a ∈ A, a ^ p = 1) →
        AUTSL.MCl1 p (G0 b c) A (U0 b c) ∧ AUTSL.MCl2 p (G0 b c) A (U0 b c) := by
    intro A hAG hAexp
    refine ⟨?_, ?_⟩
    · exact row4_clause_one hp5 hcardG hpq hAG hAexp
    · obtain ⟨h, hh, B, hBA, hBc, hle⟩ := row4_clause_two hp5 hcardG hpq hAG hAexp
      exact ⟨x0 b c, x0_mem_omegaOneCenterIn, x0_ne_one, h, hh, B, hBA, hBc, hle⟩
  obtain ⟨hcl1, hcl2⟩ := transport hirr hU hexp hH
  obtain ⟨h, -, B, hB, hcard, hle⟩ := hcl1
  obtain ⟨x, hx, hx1, h', -, B', hB', hcard', hle'⟩ := hcl2
  exact ⟨⟨h, B, hB, hcard, hle.trans inf_le_right⟩,
    ⟨x, hx, hx1, h', B', hB', hcard', hle'.trans inf_le_right⟩⟩

end Final

end CFSG.RankThree.PartOne.KF1514B

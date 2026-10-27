module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailureFieldPrimeCore
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.MinimalLocalFailurePrimeCentralizerScalar

public section

namespace CFSG.ShultStronglyClosedTI.CyclicSemiregular

open CFSG.Open CFSG.BenderSuzuki
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionInvariantNormalizer
open CFSG.ProperTwoGeneratedCore.LocalCriterionMaximalPrime
open CFSG.BenderSuzuki.PFAppendixIII CFSG.BenderSuzuki.PFchapter1section1
open CFSG.ShultStronglyClosedTI.PairInvolutionFixedField

universe u

variable {G : Type u} [Group G] [Finite G]

theorem eq_or_eq_of_pair {X : Type*} {α β lam mu ω : X} (hαβ : α ≠ β)
    (hα : α = lam ∨ α = mu) (hβ : β = lam ∨ β = mu) (hω : ω = lam ∨ ω = mu) :
    ω = α ∨ ω = β := by
  rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;> rcases hω with rfl | rfl
  all_goals first
    | exact Or.inl rfl
    | exact Or.inr rfl
    | exact absurd rfl hαβ

omit [Finite G] in
theorem translate_conj (H : Subgroup G) (omega : rightCosetSpace H) (g y : G) :
    rightCosetTranslate H omega (g * y * g⁻¹) =
      rightCosetTranslate H (rightCosetTranslate H (rightCosetTranslate H omega g) y) g⁻¹ := by
  rw [rightCosetTranslate_mul, rightCosetTranslate_mul, mul_assoc]

theorem prime_centralizer_field_case
    {H : Subgroup G} {z : G} (h : MinimalInvolutionPointLocalFailure H z)
    (hcomm : ProperStrongEmbeddingCommutingImages G)
    (hsmallerR1 : ∀ (F : Type u) [Group F] [Finite F], Nat.card F < Nat.card G →
      2 ≤ twoRank F → (∃ A : Subgroup F, fusionStronglyEmbedded A) → R1Full F)
    {beta : rightCosetSpace H} (hbeta : beta ≠ rightCosetMk H 1)
    {t : G} (ht : t ∈ rightPairFlipFiber H z beta)
    (hproper : minimalLocalFailureProperPairHull H z beta t < ⊤)
    {e : ℕ} (hQcard : Nat.card (minimalLocalFailurePairActionPointHull H z) = 2 ^ e)
    {p : ℕ} (hp : p.Prime) (hpq : p ∣ 2 ^ e - 1)
    (hdt : ∀ a b c d : rightCosetSpace H, a ≠ b → c ≠ d →
      ∃ g : G, rightCosetTranslate H a g = c ∧ rightCosetTranslate H b g = d)
    {y : G} (hyB : y ∈ pairPointStabilizer H beta) (hy : orderOf y = p)
    (hXy : ¬ rightInvolutionCommutatorSubgroup t (pairOddCore H beta) ≤
      Subgroup.centralizer ({y} : Set G))
    (P : Sylow p (pairPointStabilizer H beta ⊓ Subgroup.centralizer ({y} : Set G) :
      Subgroup G)) :
    let B := pairPointStabilizer H beta
    let C := Subgroup.centralizer ({y} : Set G)
    pointFixedSet H ((P : Subgroup (B ⊓ C : Subgroup G)).map (B ⊓ C).subtype) =
        {rightCosetMk H 1, beta} ∧
      ∃ S : Sylow p C, (S : Subgroup C).map C.subtype =
        (P : Subgroup (B ⊓ C : Subgroup G)).map (B ⊓ C).subtype := by
  intro B C
  let alpha := rightCosetMk H 1
  let X := rightInvolutionCommutatorSubgroup t (pairOddCore H beta)
  let Q := minimalLocalFailurePairActionPointHull H z
  let P' := (P : Subgroup (B ⊓ C : Subgroup G)).map (B ⊓ C).subtype
  let : Fact p.Prime := ⟨hp⟩
  obtain ⟨-, hq₀, -, hEcard, -, -, -, -, -, -, hαΔ, hβΔ, -, -, hsylow, hDY, hfixpair⟩ :=
    field_prime_core h hcomm hsmallerR1 hbeta ht hproper hQcard hp hpq hyB hy hXy
  obtain ⟨hQ, -, hQclass, hQH, -⟩ := proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
  obtain ⟨S, hS⟩ := hsylow P
  have hP'S : P' = (S : Subgroup C).map C.subtype := hS.symm
  refine ⟨?_, S, hS⟩
  have hP'BC : P' ≤ B ⊓ C := Subgroup.map_subtype_le _
  have hP'B : P' ≤ B := hP'BC.trans inf_le_left
  have hP'C : P' ≤ C := hP'BC.trans inf_le_right
  have hyP' : y ∈ P' := mem_sylow_map_of_central (K := B ⊓ C)
    ⟨hyB, Subgroup.mem_centralizer_singleton_iff.mpr rfl⟩
    (fun k hk => Subgroup.mem_centralizer_singleton_iff.mp hk.2) hy P
  have hαfix : alpha ∈ pointFixedSet H P' :=
    (mem_pointFixedSet_iff H P' alpha).mpr (hP'B.trans inf_le_left)
  have hβfix : beta ∈ pointFixedSet H P' :=
    (mem_pointFixedSet_iff H P' beta).mpr (hP'B.trans inf_le_right)
  have hfixT : ∀ ω ∈ pointFixedSet H P', ∀ g ∈ P', rightCosetTranslate H ω g = ω := by
    intro ω hω g hg
    rw [← pointRightCosetMul_eq_translate]
    exact hω g hg
  obtain ⟨lam, -, mu, -, -, hfixΔ⟩ := hfixpair S
  rw [hS] at hfixΔ
  have hinΔ : ∀ ω ∈ pointFixedSet H P', ω ∈ baseOrbit H C → ω = alpha ∨ ω = beta := by
    intro ω hω hωΔ
    have hmem : ∀ x ∈ pointFixedSet H P', x ∈ baseOrbit H C → x = lam ∨ x = mu := by
      intro x hx hxΔ
      have hx' : x ∈ pointFixedSet H P' ∩ baseOrbit H C := ⟨hx, hxΔ⟩
      rw [hfixΔ] at hx'
      exact hx'
    exact eq_or_eq_of_pair hbeta.symm (hmem alpha hαfix hαΔ) (hmem beta hβfix hβΔ)
      (hmem ω hω hωΔ)
  ext ω
  constructor
  swap
  · rintro (rfl | hω)
    · exact hαfix
    · rw [Set.mem_singleton_iff] at hω
      rw [hω]
      exact hβfix
  intro hω
  by_cases hωΔ : ω ∈ baseOrbit H C
  · exact hinΔ ω hω hωΔ
  exfalso
  have hωα : ω ≠ alpha := fun h' => hωΔ (h' ▸ hαΔ)
  obtain ⟨g, hgα, hgβ⟩ := hdt alpha beta ω alpha hbeta.symm hωα
  have hginvα : rightCosetTranslate H ω g⁻¹ = alpha := by
    rw [← hgα, rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  have hginvβ : rightCosetTranslate H alpha g⁻¹ = beta := by
    rw [← hgβ, rightCosetTranslate_mul, mul_inv_cancel, rightCosetTranslate_one]
  let y' := g * y * g⁻¹
  have hωy : rightCosetTranslate H ω y = ω := hfixT ω hω y hyP'
  have hαy : rightCosetTranslate H alpha y = alpha := hfixT alpha hαfix y hyP'
  have hy'B : y' ∈ B := by
    refine ⟨(mem_rightCosetStabilizer_iff H _ _).mpr ?_,
      (mem_rightCosetStabilizer_iff H _ _).mpr ?_⟩
    · change rightCosetTranslate H alpha (g * y * g⁻¹) = alpha
      rw [translate_conj, hgα, hωy, hginvα]
    · change rightCosetTranslate H beta (g * y * g⁻¹) = beta
      rw [translate_conj, hgβ, hαy, hginvβ]
  have hy' : orderOf y' = p := by
    have hconj := orderOf_conj_eq y g⁻¹
    rw [inv_inv, hy] at hconj
    exact hconj
  let P'' := P'.map (MulAut.conj g).toMonoidHom
  have hP''fix : ∀ ω', ω' ∈ pointFixedSet H P'' ↔
      rightCosetTranslate H ω' g ∈ pointFixedSet H P' :=
    fun ω' => mem_pointFixedSet_map_conj H P' g ω'
  by_cases hXy' : X ≤ Subgroup.centralizer ({y'} : Set G)
  ·
    let C' := Subgroup.centralizer ({y'} : Set G)
    have hC' : C' = C.map (MulAut.conj g).toMonoidHom := centralizer_conj_eq_map y g
    have hP''C' : P'' ≤ C' := by
      rw [hC']
      exact Subgroup.map_mono hP'C
    have hP''B : P'' ≤ B := by
      intro x hx
      refine ⟨?_, ?_⟩
      · have hαP'' : alpha ∈ pointFixedSet H P'' := by
          rw [hP''fix, hgα]
          exact hω
        exact (mem_pointFixedSet_iff H P'' alpha).mp hαP'' hx
      · have hβP'' : beta ∈ pointFixedSet H P'' := by
          rw [hP''fix, hgβ]
          exact hαfix
        exact (mem_pointFixedSet_iff H P'' beta).mp hβP'' hx
    have hcardP'' : Nat.card P'' = p ^ (Nat.card C').factorization p := by
      rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hP'S, card_sylow_map,
        hC', Subgroup.card_map_of_injective (MulAut.conj g).injective]
    have hcardP''' := card_eq_pow_factorization_of_le (le_inf hP''B hP''C') inf_le_right
      hcardP''
    obtain ⟨R, hR⟩ := exists_sylow_map_eq_of_card (le_inf hP''B hP''C') hcardP'''
    obtain ⟨hRfix, -⟩ := prime_centralizer_scalar_case h hcomm hsmallerR1 hbeta ht hproper hp
      (by
        obtain ⟨-, -, -, -, -, -, -, -, -, hXm, hXQ, -⟩ :=
          proper_pair_torus_setup h hcomm hsmallerR1 hbeta ht hproper
        rw [← hXm, hXQ, hQcard]
        exact hpq) hy'B hXy' R
    rw [hR] at hRfix
    have hδ : rightCosetTranslate H beta g⁻¹ ∈ pointFixedSet H P'' := by
      rw [hP''fix, rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one]
      exact hβfix
    rw [hRfix] at hδ
    rcases hδ with hδα | hδβ
    · apply hωΔ
      have hβω : beta = ω := by
        have h1 : beta = rightCosetTranslate H (rightCosetTranslate H beta g⁻¹) g := by
          rw [rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one]
        rw [h1, hδα]
        exact hgα
      rw [← hβω]
      exact hβΔ
    · rw [Set.mem_singleton_iff] at hδβ
      apply hbeta
      have h1 : rightCosetTranslate H beta g = beta := by
        conv_lhs => rw [← hδβ]
        rw [rightCosetTranslate_mul, inv_mul_cancel, rightCosetTranslate_one]
      exact h1.symm.trans hgβ
  ·
    obtain ⟨-, hq₀', -, hEcard', -⟩ :=
      field_prime_core h hcomm hsmallerR1 hbeta ht hproper hQcard hp hpq hy'B hy' hXy'
    obtain ⟨s', hs'E, hs'1⟩ := exists_mem_ne_one_of_one_lt_card
      (E := Q ⊓ Subgroup.centralizer ({y'} : Set G)) (by rw [hEcard']; omega)
    obtain ⟨r, hrE, hr1⟩ := exists_mem_ne_one_of_one_lt_card
      (E := Q ⊓ C) (by rw [hEcard]; omega)
    let s := g⁻¹ * s' * g
    have hsC : s ∈ C := by
      apply Subgroup.mem_centralizer_singleton_iff.mpr
      have hs'y' : s' * y' = y' * s' := Subgroup.mem_centralizer_singleton_iff.mp hs'E.2
      change g⁻¹ * s' * g * y = y * (g⁻¹ * s' * g)
      calc g⁻¹ * s' * g * y = g⁻¹ * (s' * (g * y * g⁻¹)) * g := by group
        _ = g⁻¹ * ((g * y * g⁻¹) * s') * g := by rw [hs'y']
        _ = y * (g⁻¹ * s' * g) := by group
    have hs'D : s' ∈ involutionPointClass z :=
      point_subgroup_class h.local_datum hQclass ⟨hs'E.1, hs'1⟩
    have hsD : s ∈ involutionPointClass z := conj_mem_pointClass hs'D g
    have hsω : rightCosetTranslate H ω s = ω := by
      change rightCosetTranslate H ω (g⁻¹ * s' * g) = ω
      rw [← hgα, rightCosetTranslate_mul, show g * (g⁻¹ * s' * g) = s' * g by group,
        ← rightCosetTranslate_mul, (translate_base_iff H s').mpr (hQH hs'E.1)]
    have hsrC : s ∈ conjugacyWithin C r := by
      rw [← hDY r hrE hr1]
      exact ⟨hsD, hsC⟩
    obtain ⟨a, ha⟩ := hsrC
    have hsa : rightCosetTranslate H (rightCosetTranslate H alpha a) s =
        rightCosetTranslate H alpha a := by
      rw [← ha, rightCosetTranslate_mul, show (a : G) * ((a : G)⁻¹ * r * a) = r * a by group,
        ← rightCosetTranslate_mul, (translate_base_iff H r).mpr (hQH hrE.1)]
    have heq := class_fixed_unique h.local_datum hsD hsω hsa
    exact hωΔ (heq ▸ ⟨a, a.2, rfl⟩)

end CFSG.ShultStronglyClosedTI.CyclicSemiregular

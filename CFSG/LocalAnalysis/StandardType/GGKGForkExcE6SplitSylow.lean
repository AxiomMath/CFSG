module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6SplitTor
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6SplitFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum

public section

namespace CFSG.StandardType

namespace ExcE6Split

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TwE6CorootCore CFSG.StandardType.TableBExcTwoFusion CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne.KE

private theorem ggKGSz_torus_commute
    {L : Type} [Field L] (n : ModGL .E6 L) (Φ : ModGL .E6 L →* ModGL .E6 L)
    {h h' : ModGL .E6 L} (hh : h ∈ twistedTorusOf n Φ) (hh' : h' ∈ twistedTorusOf n Φ) :
    Commute h h' := by
  have h1 : h ∈ torusGroup .E6 L := (mem_twistedTorusOf.1 hh).1
  have h2 : h' ∈ torusGroup .E6 L := (mem_twistedTorusOf.1 hh').1
  exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup h1)
    (torusGroup_le_diagonalGroup h2)

theorem exists_langConjugator_split
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (E : Subgroup (adjointGroup .E6 K)) (hE : IsElemAbelian p E) (hr : p ^ 6 ≤ Nat.card E)
    (hsc : ∀ g : adjointGroup .E6 K, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ g0' : ModGL .E6 (AlgebraicClosure K),
      g0' ∈ adjointGroup .E6 (AlgebraicClosure K) ∧
      Units.map (entrywiseHom Fr) g0' = g0' ∧
      ∀ x : adjointGroup .E6 K, x ∈ E ↔ x ^ p = 1 ∧
        g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) * g0' ∈
          twistedTorusOf (1 : ModGL .E6 (AlgebraicClosure K)) (Units.map (entrywiseHom Fr)) := by
  let L := AlgebraicClosure K
  let Φ : ModGL .E6 L →* ModGL .E6 L := Units.map (entrywiseHom Fr)
  let T : Subgroup (ModGL .E6 L) := twistedTorusOf 1 Φ
  obtain ⟨y, hy⟩ := exists_conj_into_splitTorus (K := K) (p := p) hp hp5 hpq Fr hFr E hE hr
  let g0' : ModGL .E6 L := baseChangeGL (algebraMap K L) (y : ModGL .E6 K)
  have hg0'C : g0' ∈ adjointGroup .E6 L := baseChangeGL_mem_adjointGroup _ y.2
  have hg0'Fix : Φ g0' = g0' := by
    simpa [Φ, g0', L] using
      units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr (y : ModGL .E6 K)
  have hET : ∀ x ∈ E, g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0' ∈ T := by
    intro x hx
    have h := hy x hx
    have hconj : g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0' =
        baseChangeGL (algebraMap K L)
          ((y⁻¹ * x * y : adjointGroup .E6 K) : ModGL .E6 K) := by
      dsimp only [g0']
      rw [show ((y⁻¹ * x * y : adjointGroup .E6 K) : ModGL .E6 K) =
          (y : ModGL .E6 K)⁻¹ * (x : ModGL .E6 K) * (y : ModGL .E6 K) by
        simp [Subgroup.coe_mul, Subgroup.coe_inv]]
      rw [map_mul, map_mul, map_inv]
    rw [hconj]
    exact h
  have hiff : ∀ x : adjointGroup .E6 K, x ∈ E ↔ x ^ p = 1 ∧
      g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0' ∈ T := by
    intro x
    constructor
    · intro hx
      exact ⟨hE.2 x hx, hET x hx⟩
    · rintro ⟨hxpow, hxT⟩
      refine hsc x ?_ hxpow
      intro e he
      have heT := hET e he
      have hcommT : (g0'⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL .E6 K) * g0') *
            (g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0') =
            (g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0') *
            (g0'⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL .E6 K) * g0') :=
        (ggKGSz_torus_commute (1 : ModGL .E6 L) Φ heT hxT).eq
      have hcommB : baseChangeGL (algebraMap K L) (e : ModGL .E6 K) *
          baseChangeGL (algebraMap K L) (x : ModGL .E6 K) =
          baseChangeGL (algebraMap K L) (x : ModGL .E6 K) *
          baseChangeGL (algebraMap K L) (e : ModGL .E6 K) := by
        have h := congrArg (fun t => g0' * t * g0'⁻¹) hcommT
        calc baseChangeGL (algebraMap K L) (e : ModGL .E6 K) *
              baseChangeGL (algebraMap K L) (x : ModGL .E6 K)
            = g0' * (g0'⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL .E6 K) * g0' *
                (g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0')) * g0'⁻¹ := by
                group
          _ = g0' * (g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL .E6 K) * g0' *
                (g0'⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL .E6 K) * g0')) * g0'⁻¹ := by
                rw [hcommT]
          _ = baseChangeGL (algebraMap K L) (x : ModGL .E6 K) *
              baseChangeGL (algebraMap K L) (e : ModGL .E6 K) := by group
      apply Subtype.ext
      apply baseChangeGL_injective (algebraMap K L)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hcommB.symm
  refine ⟨g0', hg0'C, ?_, ?_⟩
  · simpa [Φ] using hg0'Fix
  · intro x
    simpa [T, Φ] using hiff x

theorem excSCTorusInput_E6_split
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K - 1) :
    ExcSCTorusInput .E6 K p 6 := by
  intro E hE h3 h6 hsc
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, _, hcardK⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardK]
  let L := AlgebraicClosure K
  let Fr : L →+* L := iterateFrobenius L 2 (n : ℕ)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP L 2 := charP_of_injective_algebraMap (algebraMap K L).injective 2
  haveI : ExpChar L 2 := expChar_prime L 2
  have hFr : ∀ c, Fr c = c ^ Nat.card K := by
    intro c
    rw [hcard]
    exact iterateFrobenius_def 2 (n : ℕ) c
  obtain ⟨g0', hg0'C, hg0'Fix, hiff⟩ :=
    exists_langConjugator_split (K := K) (p := p) hp hp5 hpq Fr hFr E hE h6 hsc
  let D : LangDatum .E6 L :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr 1 hg0'C (by
      rw [canonicalRep_one, mul_one]; exact hg0'Fix)
  refine ⟨{ D := D
            w := 1
            q_eq := rfl
            frob := ⟨Fr, hFr, fun g => rfl⟩
            n_eq := rfl
            mem_iff := ?_ }, ?_, fun hpm1 => ?_⟩
  · intro x
    simpa [D, LangDatum.ofFrobenius, LangDatum.torus, canonicalRep_one] using hiff x
  · intro _
    rfl
  · exfalso
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
    have hdvd2 : p ∣ 2 := by
      have h := Nat.dvd_sub hpm1 hpq
      rwa [hsub] at h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega

end ExcE6Split

end CFSG.StandardType

end

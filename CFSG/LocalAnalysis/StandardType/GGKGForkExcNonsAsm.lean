module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcFrame
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.StandardType

namespace ExcNons

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

private theorem ggKGNa_torus_commute
    {τ : Tag} {L : Type} [Field L] (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L)
    {h h' : ModGL τ L} (hh : h ∈ twistedTorusOf n Φ) (hh' : h' ∈ twistedTorusOf n Φ) :
    Commute h h' := by
  have h1 : h ∈ torusGroup τ L := (mem_twistedTorusOf.1 hh).1
  have h2 : h' ∈ torusGroup τ L := (mem_twistedTorusOf.1 hh').1
  exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup h1)
    (torusGroup_le_diagonalGroup h2)

theorem excSCTorusInput_nons_of_toral {τ : Tag}
    {K : Type} [Field K] [Finite K] {p r₀ : ℕ} (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1)
    (htor : ∀ E : Subgroup (adjointGroup τ K), IsElemAbelian p E → p ^ r₀ ≤ Nat.card E →
      (∀ g : adjointGroup τ K, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) →
      ∃ (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (g0 : ModGL τ (AlgebraicClosure K))
        (w : WeylGroup τ) (y : adjointGroup τ K),
        (∀ c, Fr c = c ^ Nat.card K) ∧ g0 ∈ adjointGroup τ (AlgebraicClosure K) ∧ ExcIsLongest τ w ∧
        Units.map (entrywiseHom Fr) g0 = g0 * canonicalRep (coxeterSystem τ)
          (AlgebraicClosure K) w ∧
        ∀ x ∈ E,
          g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            ((y⁻¹ * x * y : adjointGroup τ K) : ModGL τ K) * g0 ∈
            twistedTorusOf (canonicalRep (coxeterSystem τ) (AlgebraicClosure K) w)
              (Units.map (entrywiseHom Fr))) :
    ExcSCTorusInput τ K p r₀ := by
  intro E hE _ hr hsc
  obtain ⟨Fr, g0, w, y, hFr, hg0C, hwlong, hlang, hy⟩ := htor E hE hr hsc
  let L := AlgebraicClosure K
  let nF : ModGL τ L := canonicalRep (coxeterSystem τ) L w
  let Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr)
  let T : Subgroup (ModGL τ L) := twistedTorusOf nF Φ
  let g0' : ModGL τ L := baseChangeGL (algebraMap K L) (y : ModGL τ K) * g0
  have hg0'C : g0' ∈ adjointGroup τ L := by
    dsimp only [g0']
    exact (adjointGroup τ L).mul_mem (baseChangeGL_mem_adjointGroup _ y.2) hg0C
  have hBfix : Φ (baseChangeGL (algebraMap K L) (y : ModGL τ K)) =
      baseChangeGL (algebraMap K L) (y : ModGL τ K) := by
    simpa [Φ] using units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr (y : ModGL τ K)
  have hg0'Lang : Φ g0' = g0' * nF := by
    have hL : Φ g0 = g0 * nF := by simpa [Φ, nF] using hlang
    calc Φ g0' = Φ (baseChangeGL (algebraMap K L) (y : ModGL τ K)) * Φ g0 := by
          dsimp only [g0']; rw [map_mul]
      _ = baseChangeGL (algebraMap K L) (y : ModGL τ K) * (g0 * nF) := by rw [hBfix, hL]
      _ = g0' * nF := by dsimp only [g0']; group
  have hET : ∀ x ∈ E,
      g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * g0' ∈ T := by
    intro x hx
    have h := hy x hx
    have hBz : baseChangeGL (algebraMap K L)
          ((y⁻¹ * x * y : adjointGroup τ K) : ModGL τ K) =
        (baseChangeGL (algebraMap K L) (y : ModGL τ K))⁻¹ *
          baseChangeGL (algebraMap K L) (x : ModGL τ K) *
          baseChangeGL (algebraMap K L) (y : ModGL τ K) := by
      rw [show ((y⁻¹ * x * y : adjointGroup τ K) : ModGL τ K) =
          (y : ModGL τ K)⁻¹ * (x : ModGL τ K) * (y : ModGL τ K) by
        simp [Subgroup.coe_mul, Subgroup.coe_inv]]
      rw [map_mul, map_mul, map_inv]
    have hconj : g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * g0' =
        g0⁻¹ * baseChangeGL (algebraMap K L)
          ((y⁻¹ * x * y : adjointGroup τ K) : ModGL τ K) * g0 := by
      dsimp only [g0']
      rw [hBz]
      group
    rw [hconj]
    simpa [T, nF, Φ] using h
  have hiff : ∀ x : adjointGroup τ K, x ∈ E ↔ x ^ p = 1 ∧
      g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * g0' ∈ T := by
    intro x
    constructor
    · intro hx
      exact ⟨hE.2 x hx, hET x hx⟩
    · rintro ⟨hxpow, hxT⟩
      refine hsc x ?_ hxpow
      intro e he
      have heT := hET e he
      have hcommT : (g0'⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * g0') *
            (g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * g0') =
            (g0'⁻¹ * baseChangeGL (algebraMap K L) (x : ModGL τ K) * g0') *
            (g0'⁻¹ * baseChangeGL (algebraMap K L) (e : ModGL τ K) * g0') :=
        (ggKGNa_torus_commute nF Φ heT hxT).eq
      have hcommB : baseChangeGL (algebraMap K L) (e : ModGL τ K) *
          baseChangeGL (algebraMap K L) (x : ModGL τ K) =
          baseChangeGL (algebraMap K L) (x : ModGL τ K) *
          baseChangeGL (algebraMap K L) (e : ModGL τ K) := by
        have h := congrArg (fun t => g0' * t * g0'⁻¹) hcommT
        calc baseChangeGL (algebraMap K L) (e : ModGL τ K) *
              baseChangeGL (algebraMap K L) (x : ModGL τ K)
            = g0' * (g0'⁻¹ * baseChangeGL (algebraMap K L)
                (e : ModGL τ K) * g0' *
                (g0'⁻¹ * baseChangeGL (algebraMap K L)
                  (x : ModGL τ K) * g0')) * g0'⁻¹ := by group
          _ = g0' * (g0'⁻¹ * baseChangeGL (algebraMap K L)
                (x : ModGL τ K) * g0' *
                (g0'⁻¹ * baseChangeGL (algebraMap K L)
                  (e : ModGL τ K) * g0')) * g0'⁻¹ := by rw [hcommT]
          _ = baseChangeGL (algebraMap K L) (x : ModGL τ K) *
              baseChangeGL (algebraMap K L) (e : ModGL τ K) := by group
      apply Subtype.ext
      apply baseChangeGL_injective (algebraMap K L)
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hcommB.symm
  let D : LangDatum τ L :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0'C hg0'Lang
  refine ⟨{
    D := D
    w := w
    q_eq := rfl
    frob := ⟨Fr, hFr, fun g => rfl⟩
    n_eq := rfl
    mem_iff := ?_ }, ?_, fun _ => hwlong⟩
  · intro x
    simpa [D, LangDatum.ofFrobenius, LangDatum.torus, T, nF, Φ, g0'] using hiff x
  · intro hpm1
    exfalso
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
    have hdvd2 : p ∣ 2 := by
      have h := Nat.dvd_sub hpq hpm1
      rwa [hsub] at h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega

end ExcNons

end CFSG.StandardType

end

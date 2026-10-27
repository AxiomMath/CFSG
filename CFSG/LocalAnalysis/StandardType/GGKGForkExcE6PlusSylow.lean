module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6PlusFrame
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6PlusTorus
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcE6PlusOrders
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtCore

public section

namespace CFSG.StandardType

namespace ExcE6Plus

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus
  CFSG.StandardType.TwE6CorootCore CFSG.StandardType.TableBExcTwoFusion
  CFSG.RankThree.PartOne.KE

private theorem ggKGE6d_torus_commute
    {L : Type} [Field L] (n : ModGL .E6 L) (Φ : ModGL .E6 L →* ModGL .E6 L)
    {h h' : ModGL .E6 L} (hh : h ∈ twistedTorusOf n Φ) (hh' : h' ∈ twistedTorusOf n Φ) :
    Commute h h' := by
  have h1 : h ∈ torusGroup .E6 L := (mem_twistedTorusOf.1 hh).1
  have h2 : h' ∈ torusGroup .E6 L := (mem_twistedTorusOf.1 hh').1
  exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup h1)
    (torusGroup_le_diagonalGroup h2)

theorem exists_langConjugator
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1)
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ Nat.card K)
    (g₀ : SL2 (AlgebraicClosure K))
    (hg₀ : Matrix.SpecialLinearGroup.map Fr g₀ = g₀ * nSL (1 : (AlgebraicClosure K)ˣ))
    (E : Subgroup (adjointGroup .E6 K)) (hE : IsElemAbelian p E)
    (hsc : ∀ g : adjointGroup .E6 K, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ g0' : ModGL .E6 (AlgebraicClosure K),
      g0' ∈ adjointGroup .E6 (AlgebraicClosure K) ∧
      Units.map (entrywiseHom Fr) g0' =
        g0' * (frameProd (AlgebraicClosure K) corootFrame
          (nSL (1 : (AlgebraicClosure K)ˣ)) : ModGL .E6 (AlgebraicClosure K)) ∧
      ∀ x : adjointGroup .E6 K, x ∈ E ↔ x ^ p = 1 ∧
        g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) * g0' ∈
          twistedTorusOf
            (frameProd (AlgebraicClosure K) corootFrame (nSL (1 : (AlgebraicClosure K)ˣ)) :
              ModGL .E6 (AlgebraicClosure K)) (Units.map (entrywiseHom Fr)) := by
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  let nF : ModGL .E6 (AlgebraicClosure K) :=
    frameProd (AlgebraicClosure K) corootFrame (nSL (1 : (AlgebraicClosure K)ˣ))
  let Φ : ModGL .E6 (AlgebraicClosure K) →* ModGL .E6 (AlgebraicClosure K) :=
    Units.map (entrywiseHom Fr)
  let T : Subgroup (ModGL .E6 (AlgebraicClosure K)) := twistedTorusOf nF Φ
  let g : ModGL .E6 (AlgebraicClosure K) :=
    frameProd (AlgebraicClosure K) corootFrame g₀
  have hgC : g ∈ adjointGroup .E6 (AlgebraicClosure K) :=
    (frameProd (AlgebraicClosure K) corootFrame g₀).2
  have hLangg : Φ g = g * nF := by
    have hBy : ∀ z : ModGL .E6 K,
        Φ (baseChangeGL (algebraMap K (AlgebraicClosure K)) z) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) z := fun z => by
      simpa [Φ] using
        units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr z
    have hbase : baseChangeGL Fr
        (frameProd (AlgebraicClosure K) corootFrame g₀ : ModGL .E6 (AlgebraicClosure K)) =
        frameProd (AlgebraicClosure K) corootFrame
          (Matrix.SpecialLinearGroup.map Fr g₀) := by
      have h := congrArg Subtype.val
        (adjointMap_frameProd (τ := .E6) (d := 3) Fr corootFrame g₀)
      rwa [CFSG.StandardType.TableBExcTwo.coe_adjointMap] at h
    have hmap : Matrix.SpecialLinearGroup.map Fr g₀ =
        g₀ * nSL (1 : (AlgebraicClosure K)ˣ) := hg₀
    dsimp only [g, nF]
    rw [show Φ (frameProd (AlgebraicClosure K) corootFrame g₀) =
        baseChangeGL Fr
          (frameProd (AlgebraicClosure K) corootFrame g₀ : ModGL .E6 (AlgebraicClosure K)) by
      simpa [Φ] using units_map_entrywiseHom_eq_baseChangeGL (τ := .E6) Fr
        (frameProd (AlgebraicClosure K) corootFrame g₀ : ModGL .E6 (AlgebraicClosure K))]
    rw [hbase, hmap, frameProd_mul, Subgroup.coe_mul]
  have hp2 : p ≠ 2 := by
    intro h
    rw [h] at hp5
    norm_num at hp5
  obtain ⟨P, hPpg, hPcard, hPT⟩ :=
    exists_sylow_conj_le_torus (K := K) (p := p) hp hp2 Fr hFr g₀ hg₀
  have hL15 := padicValNat_card_adjointGroup (K := K) (p := p) hp hp5 hpq
  haveI : Fact p.Prime := ⟨hp⟩
  have hcardSyl : Nat.card P = p ^ (Nat.card (adjointGroup .E6 K)).factorization p := by
    rw [Nat.factorization_def _ hp, hL15, hPcard]
  let P₀ : Sylow p (adjointGroup .E6 K) := Sylow.ofCard P hcardSyl
  have hP₀ : (P₀ : Subgroup (adjointGroup .E6 K)) = P := Sylow.coe_ofCard P hcardSyl
  obtain ⟨Q, hEQ⟩ := IsPGroup.exists_le_sylow hE.isPGroup
  haveI : MulAction.IsPretransitive (adjointGroup .E6 K) (Sylow p (adjointGroup .E6 K)) :=
    Sylow.isPretransitive_of_finite
  obtain ⟨y, hy⟩ :=
    MulAction.exists_smul_eq (adjointGroup .E6 K) P₀ Q
  have hQmap : (Q : Subgroup (adjointGroup .E6 K)) =
      P.map (MulAut.conj y).toMonoidHom := by
    rw [← hy, Sylow.coe_subgroup_smul, hP₀, Subgroup.pointwise_smul_def]
    rfl
  have hconjE : ∀ x ∈ E, y⁻¹ * x * y ∈ P := by
    intro x hx
    have hxQ : x ∈ (Q : Subgroup (adjointGroup .E6 K)) := hEQ hx
    rw [hQmap, Subgroup.mem_map] at hxQ
    obtain ⟨z, hzP, hzx⟩ := hxQ
    have hzx' : y * z * y⁻¹ = x := by simpa [MulAut.conj_apply] using hzx
    have hz : y⁻¹ * x * y = z := by rw [← hzx']; group
    rwa [hz]
  let g0' : ModGL .E6 (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E6 K) * g
  have hg0'C : g0' ∈ adjointGroup .E6 (AlgebraicClosure K) := by
    dsimp only [g0']
    exact (adjointGroup .E6 (AlgebraicClosure K)).mul_mem
      (baseChangeGL_mem_adjointGroup _ y.2) hgC
  have hg0'Lang : Φ g0' = g0' * nF := by
    have hBy : Φ (baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E6 K)) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E6 K) := by
      simpa [Φ] using
        units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr (y : ModGL .E6 K)
    calc Φ g0' = Φ (baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E6 K)) * Φ g := by
          dsimp only [g0']; rw [map_mul]
      _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E6 K) * (g * nF) := by
          rw [hBy, hLangg]
      _ = g0' * nF := by dsimp only [g0']; group
  have hET : ∀ x ∈ E,
      g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) * g0' ∈ T := by
    intro x hx
    have hzP : y⁻¹ * x * y ∈ P := hconjE x hx
    have hPT := hPT (y⁻¹ * x * y) hzP
    have hBz : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((y⁻¹ * x * y : adjointGroup .E6 K) : ModGL .E6 K) =
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E6 K))⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL .E6 K) := by
      rw [show ((y⁻¹ * x * y : adjointGroup .E6 K) : ModGL .E6 K) =
          (y : ModGL .E6 K)⁻¹ * (x : ModGL .E6 K) * (y : ModGL .E6 K) by
        simp [Subgroup.coe_mul, Subgroup.coe_inv]]
      rw [map_mul, map_mul, map_inv]
    have hconj : g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL .E6 K) * g0' =
        g⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((y⁻¹ * x * y : adjointGroup .E6 K) : ModGL .E6 K) * g := by
      dsimp only [g0']
      rw [hBz]
      group
    rw [hconj]
    exact hPT
  have hiff : ∀ x : adjointGroup .E6 K, x ∈ E ↔ x ^ p = 1 ∧
      g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) * g0' ∈ T := by
    intro x
    constructor
    · intro hx
      exact ⟨hE.2 x hx, hET x hx⟩
    · rintro ⟨hxpow, hxT⟩
      refine hsc x ?_ hxpow
      intro e he
      have heT := hET e he
      have hcommT : (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (e : ModGL .E6 K) * g0') *
          (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL .E6 K) * g0') =
          (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL .E6 K) * g0') *
          (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (e : ModGL .E6 K) * g0') :=
        (ggKGE6d_torus_commute nF Φ heT hxT).eq
      have hcommB : baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) := by
        have h := congrArg (fun t => g0' * t * g0'⁻¹) hcommT
        calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K)
            = g0' * (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                (e : ModGL .E6 K) * g0' *
                (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  (x : ModGL .E6 K) * g0')) * g0'⁻¹ := by group
          _ = g0' * (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                (x : ModGL .E6 K) * g0' *
                (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  (e : ModGL .E6 K) * g0')) * g0'⁻¹ := by rw [hcommT]
          _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL .E6 K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL .E6 K) := by group
      apply Subtype.ext
      apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hcommB.symm
  refine ⟨g0', hg0'C, hg0'Lang, ?_⟩
  intro x
  simpa [T, nF, Φ] using hiff x

theorem exists_excFrame_of_selfCentralizing
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup .E6 K))
    (hE : IsElemAbelian p E)
    (hsc : ∀ g : adjointGroup .E6 K, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E) :
    ∃ F : ExcFrame .E6 K p E, ExcIsLongest .E6 F.w := by
  haveI : Fintype K := Fintype.ofFinite K
  obtain ⟨n, _, hcardK⟩ := FiniteField.card K 2
  have hcard : Nat.card K = 2 ^ (n : ℕ) := by
    rw [Nat.card_eq_fintype_card, hcardK]
  let Fr : AlgebraicClosure K →+* AlgebraicClosure K :=
    iterateFrobenius (AlgebraicClosure K) 2 (n : ℕ)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP (AlgebraicClosure K) 2 :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective 2
  haveI : ExpChar (AlgebraicClosure K) 2 := expChar_prime (AlgebraicClosure K) 2
  have hFr : ∀ c, Fr c = c ^ Nat.card K := by
    intro c
    rw [hcard]
    exact iterateFrobenius_def 2 (n : ℕ) c
  obtain ⟨g₀, hg₀⟩ := exists_frameElt Fr hFr
  obtain ⟨w, hwlong, hwn⟩ := exists_longest_canonicalRep (L := AlgebraicClosure K)
  obtain ⟨g0', hg0'C, hg0'Lang, hiff⟩ :=
    exists_langConjugator (K := K) (p := p) hp hp5 hpq Fr hFr g₀ hg₀ E hE hsc
  have hg0w : Units.map (entrywiseHom Fr) g0' =
      g0' * canonicalRep (coxeterSystem .E6) (AlgebraicClosure K) w := by
    rw [← hwn]
    exact hg0'Lang
  let D : LangDatum .E6 (AlgebraicClosure K) :=
    LangDatum.ofFrobenius Fr (Nat.card K) hFr w hg0'C hg0w
  refine ⟨{
    D := D
    w := w
    q_eq := rfl
    frob := ⟨Fr, hFr, fun g => rfl⟩
    n_eq := by
      dsimp [D, LangDatum.ofFrobenius]
    mem_iff := ?_ }, hwlong⟩
  intro x
  simpa [D, LangDatum.ofFrobenius, LangDatum.torus, ← hwn] using hiff x


theorem excSCTorusInput_E6_plus
    {K : Type} [Field K] [Finite K] [CharP K 2] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hpq : p ∣ Nat.card K + 1) :
    ExcSCTorusInput .E6 K p 4 := by
  intro E hE _h3 _h4 hsc
  obtain ⟨F, hlong⟩ := exists_excFrame_of_selfCentralizing hp hp5 hpq E hE hsc
  refine ⟨F, ?_, fun _ => hlong⟩
  · intro hpm1
    exfalso
    have hKpos : 0 < Nat.card K := Nat.card_pos
    have hsub : Nat.card K + 1 - (Nat.card K - 1) = 2 := by omega
    have hdvd2 : p ∣ 2 := by
      have h := Nat.dvd_sub hpq hpm1
      rwa [hsub] at h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega

end ExcE6Plus

end CFSG.StandardType

end

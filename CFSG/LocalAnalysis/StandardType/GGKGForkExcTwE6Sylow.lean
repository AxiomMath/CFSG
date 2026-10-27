module

public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwE6Tor
public import CFSG.LocalAnalysis.StandardType.GGKGForkExcTwCent

public section

namespace CFSG.StandardType

namespace ExcTwE6Nons

open CFSG CFSG.Assembly CFSG.Open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.AlgebraicGroups CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.RankThree.PartOne.KE

private theorem ggKGTy_torus_commute
    {L : Type} [Field L] {τ : Tag} (n : ModGL τ L) (Φ : ModGL τ L →* ModGL τ L)
    {h h' : ModGL τ L} (hh : h ∈ twistedTorusOf n Φ) (hh' : h' ∈ twistedTorusOf n Φ) :
    Commute h h' := by
  have h1 : h ∈ torusGroup τ L := (mem_twistedTorusOf.1 hh).1
  have h2 : h' ∈ torusGroup τ L := (mem_twistedTorusOf.1 hh').1
  exact mul_comm_of_mem_diagonalGroup (torusGroup_le_diagonalGroup h1)
    (torusGroup_le_diagonalGroup h2)

private theorem ggKGTy_twistHom_baseChange_eq_self
    {K : Type} [Field K] {σ : K ≃+* K} {n : ℕ}
    (Fr : AlgebraicClosure K →+* AlgebraicClosure K) (hFr : ∀ c, Fr c = c ^ (2 ^ n))
    (hσ : ∀ c, σ c = c ^ (2 ^ n)) (y : twistedE6RootGroup K σ) :
    twistHom TwistTag.E6 (AlgebraicClosure K) Fr
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K)) =
      baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) := by
  have hcomm : (algebraMap K (AlgebraicClosure K)).comp σ.toRingHom =
      Fr.comp (algebraMap K (AlgebraicClosure K)) := by
    ext c
    change algebraMap K (AlgebraicClosure K) (σ c) =
      Fr (algebraMap K (AlgebraicClosure K) c)
    rw [hσ, hFr, map_pow]
  rw [twistHom_baseChangeGL (algebraMap K (AlgebraicClosure K)) hcomm,
    ((mem_twistedFixedGroup_iff_twistHom TwistTag.E6 K σ.toRingHom).1
      (graphFixedRootGroup_le TwistTag.E6 K σ.toRingHom y.2)).2]

theorem twE6SCTorusInput_nonsplit
    {K : Type} [Field K] [Finite K] (σ : K ≃+* K) {n p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hK : Nat.card K = (2 ^ n) ^ 2) (hσ : ∀ c, σ c = c ^ (2 ^ n)) (hpq : p ∣ 2 ^ n + 1) :
    TwE6SCTorusInput K σ n p 5 := by
  intro E hE _h3 h5 hsc
  obtain ⟨Fr, g0, w, y, hFr, hg0, hw, hlang, hy⟩ :=
    exists_twFrame_conj_into_torus (n := n) (p := p) σ hp hp5 hK hσ hpq E hE h5
  let g0' : ModGL TwistTag.E6.tag (AlgebraicClosure K) :=
    baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) * g0
  have hg0'C : g0' ∈ adjointGroup TwistTag.E6.tag (AlgebraicClosure K) := by
    dsimp only [g0']
    exact (adjointGroup TwistTag.E6.tag (AlgebraicClosure K)).mul_mem
      (baseChangeGL_mem_adjointGroup _ (ggKGTc_coe_mem_adjointGroup y)) hg0
  have hg0'Lang : twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0' =
      g0' * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w := by
    have hBy : twistHom TwistTag.E6 (AlgebraicClosure K) Fr
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K)) =
        baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) :=
      ggKGTy_twistHom_baseChange_eq_self (n := n) (σ := σ) Fr hFr hσ y
    calc twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0'
        = twistHom TwistTag.E6 (AlgebraicClosure K) Fr
            (baseChangeGL (algebraMap K (AlgebraicClosure K))
              (y : ModGL TwistTag.E6.tag K) * g0) := by
            rfl
      _ = twistHom TwistTag.E6 (AlgebraicClosure K) Fr
            (baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K)) *
          twistHom TwistTag.E6 (AlgebraicClosure K) Fr g0 := by rw [map_mul]
      _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) *
          (g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w) := by
            rw [hBy, hlang]
      _ = g0' * canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w := by
            dsimp only [g0']; group
  let T : Subgroup (ModGL TwistTag.E6.tag (AlgebraicClosure K)) :=
    twistedTorusOf (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
      (twistHom TwistTag.E6 (AlgebraicClosure K) Fr)
  have hET : ∀ x ∈ E,
      g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0' ∈ T := by
    intro x hx
    have hz := hy x hx
    have hBz : baseChangeGL (algebraMap K (AlgebraicClosure K))
        ((y⁻¹ * x * y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
        (baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K))⁻¹ *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (y : ModGL TwistTag.E6.tag K) := by
      rw [show ((y⁻¹ * x * y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) =
          (y : ModGL TwistTag.E6.tag K)⁻¹ * (x : ModGL TwistTag.E6.tag K) *
            (y : ModGL TwistTag.E6.tag K) by
        simp [Subgroup.coe_mul, Subgroup.coe_inv]]
      rw [map_mul, map_mul, map_inv]
    have hconj : g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          (x : ModGL TwistTag.E6.tag K) * g0' =
        g0⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
          ((y⁻¹ * x * y : twistedE6RootGroup K σ) : ModGL TwistTag.E6.tag K) * g0 := by
      dsimp only [g0']
      rw [hBz]
      group
    rw [hconj]
    exact hz
  have hiff : ∀ x : twistedE6RootGroup K σ, x ∈ E ↔ x ^ p = 1 ∧
      g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
        (x : ModGL TwistTag.E6.tag K) * g0' ∈ T := by
    intro x
    constructor
    · intro hx
      exact ⟨hE.2 x hx, hET x hx⟩
    · rintro ⟨hxpow, hxT⟩
      refine hsc x ?_ hxpow
      intro e he
      have heT := hET e he
      have hcommT : (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (e : ModGL TwistTag.E6.tag K) * g0') *
          (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL TwistTag.E6.tag K) * g0') =
          (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (x : ModGL TwistTag.E6.tag K) * g0') *
          (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
            (e : ModGL TwistTag.E6.tag K) * g0') :=
        (ggKGTy_torus_commute
          (canonicalRep (coxeterSystem TwistTag.E6.tag) (AlgebraicClosure K) w)
          (twistHom TwistTag.E6 (AlgebraicClosure K) Fr) heT hxT).eq
      have hcommB : baseChangeGL (algebraMap K (AlgebraicClosure K))
            (e : ModGL TwistTag.E6.tag K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) =
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
          baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL TwistTag.E6.tag K) := by
        have h := congrArg (fun t => g0' * t * g0'⁻¹) hcommT
        calc baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL TwistTag.E6.tag K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K)
            = g0' * (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                (e : ModGL TwistTag.E6.tag K) * g0' *
                (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  (x : ModGL TwistTag.E6.tag K) * g0')) * g0'⁻¹ := by group
          _ = g0' * (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                (x : ModGL TwistTag.E6.tag K) * g0' *
                (g0'⁻¹ * baseChangeGL (algebraMap K (AlgebraicClosure K))
                  (e : ModGL TwistTag.E6.tag K) * g0')) * g0'⁻¹ := by rw [hcommT]
          _ = baseChangeGL (algebraMap K (AlgebraicClosure K)) (x : ModGL TwistTag.E6.tag K) *
              baseChangeGL (algebraMap K (AlgebraicClosure K)) (e : ModGL TwistTag.E6.tag K) := by
                group
      apply Subtype.ext
      apply baseChangeGL_injective (algebraMap K (AlgebraicClosure K))
      rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
      exact hcommB.symm
  refine ⟨{
    Fr := Fr
    v := w
    g0 := g0'
    fr_eq := hFr
    g0_mem := hg0'C
    lang := hg0'Lang
    mem_iff := fun x => ?_ }, ?_, fun _ => hw⟩
  · simpa only [T] using hiff x
  · intro hpm1
    exfalso
    have h1 : 1 ≤ 2 ^ n := Nat.one_le_pow _ _ (by norm_num)
    have hsub : 2 ^ n + 1 - (2 ^ n - 1) = 2 := by omega
    have hdvd2 : p ∣ 2 := by
      have h := Nat.dvd_sub hpq hpm1
      rwa [hsub] at h
    have hle : p ≤ 2 := Nat.le_of_dvd (by norm_num) hdvd2
    omega

end ExcTwE6Nons

end CFSG.StandardType

end

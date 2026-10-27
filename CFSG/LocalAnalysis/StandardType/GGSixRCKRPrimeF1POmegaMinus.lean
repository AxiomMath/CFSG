module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPOmegaMinus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Position
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.Defs
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepACore
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.IDPOmegaMinus
public import CFSG.LieType.Universal.Spin.Twisted.Datum
public import CFSG.LieType.Universal.Spin.Action

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem spin_pow_eq_one_of_conj_POmegaMinus {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ}
    {bq cq : F} (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    {X : Type} [Group X] (ψ : spinGroup (Spin.quadMinus n F bq cq) →* X)
    (hψ : ψ.ker ≤ Subgroup.center (spinGroup (Spin.quadMinus n F bq cq)))
    {d : X} {p : ℕ} (hdp : d ^ p = 1) {s₀ : spinGroup (Spin.quadMinus n F bq cq)}
    (hconj : ∀ u, d⁻¹ * ψ u * d = ψ (s₀ * u * s₀⁻¹)) : s₀ ^ p = 1 := by
  have hinj : Function.Injective (Spin.spinMatrix (Spin.quadMinus n F bq cq)) :=
    (MonoidHom.ker_eq_bot_iff _).mp
      (Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero F 2))
  have hsl : IsGLLift (Spin.spinMatrix (Spin.quadMinus n F bq cq)) ψ
      (Spin.spinMatrix (Spin.quadMinus n F bq cq) s₀) d := by
    intro u
    exact ⟨s₀ * u * s₀⁻¹, by simp only [map_mul, map_inv], hconj u⟩
  have hslp : IsGLLift (Spin.spinMatrix (Spin.quadMinus n F bq cq)) ψ
      (Spin.spinMatrix (Spin.quadMinus n F bq cq) (s₀ ^ p)) 1 := by
    have h := hsl.pow p
    rw [hdp, ← map_pow] at h
    exact h
  apply conj_eq_unique_POmegaMinus n hirr hn ψ hψ (s' := 1)
  intro u
  obtain ⟨u', hu'j, hu'ψ⟩ := hslp u
  have h : u' = (s₀ ^ p) * u * (s₀ ^ p)⁻¹ :=
    hinj (by rw [hu'j]; simp only [map_mul, map_inv])
  rw [h] at hu'ψ
  simpa using hu'ψ.symm

theorem rckF1_POmegaMinus
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K J : Subgroup X}
    {d : X} (hdp : d ^ p = 1) {F : Type} [Field F] [Finite F] [CharP F 2] {n : ℕ} {bq cq : F}
    (hirr : ∀ s : F, s ^ 2 + bq * s + cq ≠ 0) (hn : 4 ≤ n)
    (φ : ↥(spinGroup (Spin.quadMinus n F bq cq)) →* X)
    (hφr : φ.range = K) (hφk : φ.ker ≤ Subgroup.center ↥(spinGroup (Spin.quadMinus n F bq cq)))
    (hdID : GGPsiInnerDiag (Spin.Twisted.minusDatum n hirr) φ d)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) :
    ∃ s : ↥(spinGroup (Spin.quadMinus n F bq cq)), (∀ u, d⁻¹ * φ u * d = φ (s * u * s⁻¹)) ∧
      Odd (orderOf (Spin.spinMatrix (Spin.quadMinus n F bq cq) s)) ∧
      ∃ ε : Matrix (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
        IsPrimAdjIdemIn (RingHom.id F)
          (LinearMap.toMatrix₂' F (QuadraticMap.polarBilin (Spin.quadMinus n F bq cq)))
          (Algebra.adjoin F
            (Units.val '' {Spin.spinMatrix (Spin.quadMinus n F bq cq) s})) ε ∧
        ∃ J' : Subgroup ↥(spinGroup (Spin.quadMinus n F bq cq)),
          IsComponentOf J'
            ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
                {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε :
                Subgroup ↥(spinGroup (Spin.quadMinus n F bq cq))),
              (glBlockCentralizer (Spin.spinMatrix (Spin.quadMinus n F bq cq))
                {Spin.spinMatrix (Spin.quadMinus n F bq cq) s} ε :
                Subgroup ↥(spinGroup (Spin.quadMinus n F bq cq)))⁆ ∧
          J'.map φ = J := by
  obtain ⟨s, hs⟩ := exists_conj_eq_POmegaMinus n hirr hn φ hφk hdID
  let s₀ : ↥(spinGroup (Spin.quadMinus n F bq cq)) := s
  have hs₀ : ∀ u, d⁻¹ * φ u * d = φ (s₀ * u * s₀⁻¹) := hs
  have hsp : s₀ ^ p = 1 := spin_pow_eq_one_of_conj_POmegaMinus hirr hn φ hφk hdp hs₀
  let j : ↥(spinGroup (Spin.quadMinus n F bq cq)) →*
      GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F :=
    Spin.spinMatrix (Spin.quadMinus n F bq cq)
  have hinj : Function.Injective j :=
    (MonoidHom.ker_eq_bot_iff j).mp
      (Spin.ker_spinMatrix_quadMinus_eq_bot hirr (CharP.cast_eq_zero F 2))
  have hdvd : orderOf (j s₀) ∣ p := by
    refine orderOf_dvd_iff_pow_eq_one.mpr ?_
    calc (j s₀) ^ p = j (s₀ ^ p) := (map_pow j s₀ p).symm
      _ = j 1 := by rw [hsp]
      _ = 1 := map_one j
  have hsodd : Odd (orderOf (j s₀)) := by
    rcases hp.eq_one_or_self_of_dvd (orderOf (j s₀)) hdvd with h | h
    · rw [h]
      exact odd_one
    · rw [h]
      exact hp.odd_of_ne_two hp2
  let D : Subgroup X := Subgroup.zpowers d
  let P : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F → Prop :=
    fun s' => s' ∈ Subgroup.zpowers (j s₀)
  have hDcent : Subgroup.centralizer (D : Set X) = Subgroup.centralizer ({d} : Set X) := by
    change Subgroup.centralizer ((Subgroup.zpowers d : Set X)) = _
    rw [Subgroup.zpowers_eq_closure d]
    exact Subgroup.centralizer_closure ({d} : Set X)
  have hJ' : IsComponentOf J (φ.range ⊓ Subgroup.centralizer (D : Set X)) := by
    rw [hφr, hDcent]
    exact hJ
  have hpowD : ∀ x ∈ Subgroup.closure ({d} : Set X), x ^ p = 1 := by
    intro x hx
    rw [← Subgroup.zpowers_eq_closure d] at hx
    rw [Subgroup.mem_zpowers_iff] at hx
    obtain ⟨q, rfl⟩ := hx
    calc (d ^ q) ^ p = (d ^ q) ^ (p : ℤ) := by rw [zpow_natCast]
      _ = d ^ (q * (p : ℤ)) := by rw [← zpow_mul]
      _ = d ^ ((p : ℤ) * q) := by rw [mul_comm]
      _ = (d ^ (p : ℤ)) ^ q := by rw [zpow_mul]
      _ = (d ^ p) ^ q := by rw [zpow_natCast]
      _ = 1 := by rw [hdp, one_zpow]
  have hlift_d : IsGLLift j φ (j s₀) d := by
    intro u
    exact ⟨s₀ * u * s₀⁻¹, by simp only [map_mul, map_inv], hs₀ u⟩
  have hlift : ∀ d' ∈ D, ∃ s' : GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F,
      P s' ∧ IsGLLift j φ s' d' := by
    intro d' hd'
    change d' ∈ Subgroup.zpowers d at hd'
    rw [Subgroup.zpowers_eq_closure d] at hd'
    induction hd' using Subgroup.closure_induction with
    | mem x hx =>
        rw [Set.mem_singleton_iff] at hx
        subst x
        exact ⟨j s₀, Subgroup.mem_zpowers (j s₀), hlift_d⟩
    | one => exact ⟨1, Subgroup.one_mem _, isGLLift_one⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨sx, hsxP, hsxL⟩ := ihx
        obtain ⟨sy, hsyP, hsyL⟩ := ihy
        exact ⟨sy * sx, Subgroup.mul_mem _ hsyP hsxP, hsxL.mul hsyL⟩
    | inv x hx ihx =>
        obtain ⟨sx, hsxP, hsxL⟩ := ihx
        refine ⟨sx ^ (p - 1), Subgroup.pow_mem _ hsxP (p - 1), ?_⟩
        have hxpow : x ^ p = 1 := hpowD x hx
        have hxinv : x ^ (p - 1) = x⁻¹ := by
          have hmul : x * x ^ (p - 1) = 1 := by
            have h1p : 1 ≤ p := Nat.succ_le_of_lt hp.pos
            rw [← pow_succ', Nat.sub_add_cancel h1p, hxpow]
          exact eq_inv_of_mul_eq_one_right hmul
        have h := hsxL.pow (p - 1)
        rwa [hxinv] at h
  obtain ⟨J', hJ'comp, hJ'map⟩ :=
    StepA.exists_isComponentOf_comap_lift_of_isGLLift (j := j) (hj := hinj) (ψ := φ)
      (hψ := hφk) (P := P) (D := D) (J := J) hJ' hlift
  let Sset : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F) :=
    {s' | P s' ∧ ∃ d' ∈ D, IsGLLift j φ s' d'}
  have hcl : Subgroup.closure Sset = Subgroup.zpowers (j s₀) := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      intro x hx
      exact hx.1
    · rw [Subgroup.zpowers_eq_closure, Subgroup.closure_le, Set.singleton_subset_iff]
      exact Subgroup.subset_closure
        ⟨Subgroup.mem_zpowers (j s₀), d, Subgroup.mem_zpowers d, hlift_d⟩
  have hcent : Subgroup.centralizer Sset =
      Subgroup.centralizer
        ({j s₀} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) := by
    rw [← Subgroup.centralizer_closure Sset, hcl, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
  have hJ'compS : IsComponentOf J' ((Subgroup.centralizer Sset).comap j) := hJ'comp
  have hJ'comp' : IsComponentOf J'
      ((Subgroup.centralizer
        ({j s₀} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F))).comap j) := by
    rwa [hcent] at hJ'compS
  have hS : ∀ a ∈ ({j s₀} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)),
      ∀ b ∈ ({j s₀} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)),
        Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl (j s₀)
  obtain ⟨ε, heprim, hcomp⟩ :=
    exists_isComponentOf_glBlockCentralizer_POmegaMinus n hirr hn
      ({j s₀} : Set (GL (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) F)) hS hJ'comp'
  exact ⟨s₀, hs₀, hsodd, ε, heprim, J', hcomp, hJ'map⟩

end CFSG.StandardType.RCKRP

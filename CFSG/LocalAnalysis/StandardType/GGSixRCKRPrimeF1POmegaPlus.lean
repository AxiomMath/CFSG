module

public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.CompPOmegaPlus
public import CFSG.LocalAnalysis.StandardType.ClassicalPosition.StepAPOmegaPlus
public import CFSG.LieType.Universal.Spin.Action

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckF1_POmegaPlus
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {K J : Subgroup X}
    {d : X} (hdp : d ^ p = 1) {k f : ℕ} (hf : 1 ≤ f) (φ : (ggU .POmegaPlus (k + 3) f).K →* X)
    (hφr : φ.range = K) (hφk : φ.ker ≤ Subgroup.center (ggU .POmegaPlus (k + 3) f).K)
    (hdID : GGPsiInnerDiag (ggU .POmegaPlus (k + 3) f).D φ d)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) :
    ∃ s : (ggU .POmegaPlus (k + 3) f).K, (∀ u, d⁻¹ * φ u * d = φ (s * u * s⁻¹)) ∧
      Odd (orderOf (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s)) ∧
      ∃ ε : Matrix (Fin (k + 3) ⊕ Fin (k + 3)) (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
        IsPrimAdjIdemIn (RingHom.id (GaloisField 2 f))
          (LinearMap.toMatrix₂' (GaloisField 2 f)
            (QuadraticMap.polarBilin (Spin.quadPlus (k + 3) (GaloisField 2 f))))
          (Algebra.adjoin (GaloisField 2 f)
            (Units.val '' {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s})) ε ∧
        ∃ J' : Subgroup (ggU .POmegaPlus (k + 3) f).K,
          IsComponentOf J'
            ⁅(glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
                {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε :
                Subgroup (ggU .POmegaPlus (k + 3) f).K),
              (glBlockCentralizer (Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)))
                {Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f)) s} ε :
                Subgroup (ggU .POmegaPlus (k + 3) f).K)⁆ ∧
          J'.map φ = J := by
  have hcard : Nat.card (GaloisField 2 f) = 2 ^ f :=
    GaloisField.card (p := 2) (n := f) (by omega)
  obtain ⟨s, hs⟩ :=
    exists_conj_eq_POmegaPlus (k + 3) (GaloisField 2 f) (by omega) φ hφk hdID
  let s₀ : (ggU .POmegaPlus (k + 3) f).K := s
  have hs₀ : ∀ u, d⁻¹ * φ u * d = φ (s₀ * u * s₀⁻¹) := hs
  have hsp : s₀ ^ p = 1 :=
    spin_pow_eq_one_of_conj_POmegaPlus (F := GaloisField 2 f) (n := k + 3) (by omega)
      φ hφk hdp hs₀
  let j : (ggU .POmegaPlus (k + 3) f).K →*
      GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f) :=
    Spin.spinMatrix (Spin.quadPlus (k + 3) (GaloisField 2 f))
  have hinj : Function.Injective j :=
    (MonoidHom.ker_eq_bot_iff j).mp
      (Spin.ker_spinMatrix_quadPlus_eq_bot (CharP.cast_eq_zero (GaloisField 2 f) 2))
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
  let P : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f) → Prop :=
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
  have hlift : ∀ d' ∈ D, ∃ s' : GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f),
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
  let Sset : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)) :=
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
        ({j s₀} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))) := by
    rw [← Subgroup.centralizer_closure Sset, hcl, Subgroup.zpowers_eq_closure,
      Subgroup.centralizer_closure]
  have hJ'compS : IsComponentOf J' ((Subgroup.centralizer Sset).comap j) := hJ'comp
  have hJ'comp' : IsComponentOf J'
      ((Subgroup.centralizer
        ({j s₀} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f)))).comap j) := by
    rwa [hcent] at hJ'compS
  have hS : ∀ a ∈ ({j s₀} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))),
      ∀ b ∈ ({j s₀} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))), Commute a b := by
    intro a ha b hb
    rw [Set.mem_singleton_iff] at ha hb
    subst a
    subst b
    exact Commute.refl (j s₀)
  obtain ⟨ε, heprim, hcomp⟩ :=
    exists_isComponentOf_glBlockCentralizer_POmegaPlus (k + 3) (GaloisField 2 f)
      (by omega) ({j s₀} : Set (GL (Fin (k + 3) ⊕ Fin (k + 3)) (GaloisField 2 f))) hS
      hJ'comp'
  exact ⟨s₀, hs₀, hsodd, ε, heprim, J', hcomp, hJ'map⟩

end CFSG.StandardType.RCKRP

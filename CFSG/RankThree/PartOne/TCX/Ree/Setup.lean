module

public import CFSG.RankThree.PartOne.TCX.Ree.Layer

public section

namespace CFSG.RankThree.PartOne.TCX.Ree

open Subgroup CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.RankThree.Chevalley CFSG.RankThree.PartOne.KLR CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.RF4
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

variable {K₀ K : Type} [Field K₀] [Finite K₀] [CharP K₀ ReeTag.F4.prime]
  [Field K] [Finite K] [CharP K ReeTag.F4.prime] {a₀ a : ℕ} {L : Type} [Field L]
  [Algebra K₀ L] [Algebra K L] [CharP L 2] [IsAlgClosed L] [IsAlgClosure K L]
  (D₀ : ReeFrameData K₀ L a₀) (D : ReeFrameData K L a)

omit [Finite K₀] [CharP K₀ ReeTag.F4.prime] [Finite K] [CharP K ReeTag.F4.prime] [CharP L 2]
  [IsAlgClosed L] [IsAlgClosure K L] [Algebra K L] in
theorem entrywise_baseChangeGL_comm (ι : K →+* L) (F : L →+* L) (σ : K →+* K)
    (h : ∀ b, F (ι b) = ι (σ b)) (g : ModGL ReeTag.F4.tag K) :
    Units.map (entrywiseHom F) (baseChangeGL ι g) =
      baseChangeGL ι (Units.map (entrywiseHom σ) g) := by
  have e : F.comp ι = ι.comp σ := RingHom.ext fun b => h b
  rw [units_map_entrywiseHom_eq_baseChangeGL_self, units_map_entrywiseHom_eq_baseChangeGL_self,
    baseChangeGL_baseChangeGL, baseChangeGL_baseChangeGL, e]

omit [CharP L 2] [IsAlgClosed L] [IsAlgClosure K L] in
theorem fext_sq_thetaGamma {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ Nat.card K₀)
    (z : ReeTag.F4.reeGamma K a) :
    Fext D₀.F (Fext D₀.F (thetaGamma L a z)) =
      thetaGamma L a (ReeTag.F4.reeGammaFieldAut K a σ z) := by
  have hςσ : ∀ c, D₀.Frq (algebraMap K L c) = algebraMap K L (σ c) := fun c => by
    rw [D₀.Frq_pow, hσ, map_pow]
  have hθ := thetaGamma_mem_adjointGroup L z
  rw [Fext_of_mem D₀.F hθ, Fext_of_mem D₀.F (D₀.F ⟨_, hθ⟩).2]
  have hsq := D₀.sq ⟨_, hθ⟩
  refine hsq.trans ?_
  show Units.map (entrywiseHom D₀.Frq) (thetaGamma L a z : ModGL ReeTag.F4.tag L) =
    thetaGamma L a (ReeTag.F4.reeGammaFieldAut K a σ z)
  rw [thetaGamma_apply, thetaGamma_apply,
    entrywise_baseChangeGL_comm (algebraMap K L) D₀.Frq σ.toRingHom hςσ,
    ReeTag.coe_reeGammaFieldAut]

omit [CharP L 2] [IsAlgClosed L] in
theorem reeShintani {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hFF : D.F = D₀.F ^ p)
    {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ Nat.card K₀) (hσord : orderOf σ = p) :
    IsReeShintani p (thetaGamma L a) D₀.F D.F
      ((ReeTag.F4.reeGammaFieldAut K a σ) ^ ((p + 1) / 2)) := by
  classical
  have hpodd : Odd p := hp.odd_of_ne_two hp2
  have h2p : 2 * ((p + 1) / 2) = p + 1 := by
    obtain ⟨k, rfl⟩ := hpodd
    omega
  set φ := ReeTag.F4.reeGammaFieldAut K a σ with hφ
  have hit : ∀ (m : ℕ) (y : ReeTag.F4.reeGamma K a),
      (Fext D₀.F)^[2 * m] (thetaGamma L a y) = thetaGamma L a ((φ ^ m) y) := by
    intro m
    induction m with
    | zero => intro y; simp
    | succ m ih =>
      intro y
      rw [show 2 * (m + 1) = 2 + 2 * m by ring, Function.iterate_add_apply, ih]
      show Fext D₀.F (Fext D₀.F _) = _
      rw [fext_sq_thetaGamma D₀ hσ, pow_succ', MulAut.mul_apply]
  refine ⟨hFF, thetaGamma_injective L, thetaGamma_mem_adjointGroup L, fun y => ?_, ?_,
    D.fext_theta, fun u hu hfix => ?_⟩
  ·
    have h1 : (Fext D₀.F)^[p + 1] (thetaGamma L a y) = Fext D₀.F (thetaGamma L a y) := by
      rw [Function.iterate_succ_apply']
      congr 1
      rw [← Fext_pow_eq_iterate D₀.F (thetaGamma_mem_adjointGroup L y) p, ← hFF]
      exact D.fext_theta y
    have h3 := hit ((p + 1) / 2) y
    rw [h2p] at h3
    rw [← h1, h3]
  ·
    have hφp : φ ^ p = 1 := by
      have : (ReeTag.F4.reeGammaFieldAutHom K a σ) ^ p = 1 := by
        rw [← map_pow, ← hσord, pow_orderOf_eq_one, map_one]
      exact this
    rw [← pow_mul, mul_comm, pow_mul, hφp, one_pow]
  · obtain ⟨γ, hγ⟩ := D.exists_theta_of_fixed hu hfix
    exact ⟨γ, hγ⟩

end CFSG.RankThree.PartOne.TCX.Ree

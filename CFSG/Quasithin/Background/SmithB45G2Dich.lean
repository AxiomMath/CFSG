module

public import CFSG.Quasithin.Background.SmithB42G2FNat
public import CFSG.Quasithin.Background.SmithB45G2Rank

public section

namespace CFSG.Quasithin.B45G2

open CFSG.Open CFSG.Quasithin.Explicit CFSG.Quasithin.JonesParshall CFSG.Quasithin.B42G2Ten
  CFSG.Quasithin.B42G2F
open CFSG.QuasithinUnique.Setup.X7
open CFSG.QuasithinUnique.Setup.X7a (frK)
open CFSG.QuasithinUnique.Setup.SL2Modules (EndRing repD repD_apply matRepE matRepE_apply
  finite_endRing equiv_apply)

variable {K : Type} [Field K] [CharP K 2] [Fintype K]
variable {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
  {ρ : Representation (ZMod 2) ↥(cayleyGroup K) M} [Fact ρ.IsIrreducible]

omit [CharP K 2] [Fintype K] in
theorem matRep_quad {m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M) {x y : ↥(cayleyGroup K)}
    (h : (ρ x - 1) * (ρ y - 1) = 0) :
    (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b x - 1) *
      (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b y - 1) = 0 := by
  have key : ∀ g w, (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).mulVec (b.equivFun w) =
      b.equivFun (ρ g w) := fun g w => by
    rw [equivFun_rep b g w, matRepE_apply]
    rfl
  have hsub : ∀ g u, (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g - 1).mulVec
      (b.equivFun u) = b.equivFun ((ρ g - 1) u) := fun g u => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, key, ← map_sub b.equivFun]
    rfl
  have hv : ∀ w : M,
      ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b x - 1) *
        (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b y - 1)).mulVec (b.equivFun w) = 0 := by
    intro w
    have hz : (ρ x - 1) ((ρ y - 1) w) = 0 := by
      rw [← Module.End.mul_apply, h]
      rfl
    exact (((Matrix.mulVec_mulVec (b.equivFun w) _ _).symm.trans
      (congrArg (fun c => (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b x - 1).mulVec c)
        (hsub y w))).trans (hsub x ((ρ y - 1) w))).trans
      ((congrArg b.equivFun hz).trans (map_zero _))
  refine Matrix.ext fun i j => ?_
  have h1 := hv (b.equivFun.symm (Pi.single j 1))
  rw [LinearEquiv.apply_symm_apply, Matrix.mulVec_single_one] at h1
  exact congrFun h1 i

omit [Fintype K] [Fact ρ.IsIrreducible] [Finite M] in
theorem rep_lie_quad (l : G2L) (hl : l = .lie) {x y : ↥(cayleyGroup K)}
    (h : (l.rep x - 1) * (l.rep y - 1) = 0) : (repLie x - 1) * (repLie y - 1) = 0 := by
  subst hl
  exact h

omit [Fintype K] in
theorem repLie_quad_of_rho {f m : ℕ} (b : Module.Basis (Fin m) (EndRing ρ) M) {E : Type}
    [Field E] [CharP E 2] (ιF : K →+* E) (ιD : EndRing ρ →+* E) (lab : Fin f → G2L)
    (Φ : (letI := ιF.toAlgebra
      (matRep (tRep K E lab)).Equiv (matRepE b ιD)))
    (j₀ : Fin f) (hlab : ∀ j ≠ j₀, lab j = .one) (hlie : lab j₀ = .lie)
    {x y : ↥(cayleyGroup K)} (h : (ρ x - 1) * (ρ y - 1) = 0) :
    (repLie x - 1) * (repLie y - 1) = 0 := by
  classical
  let _ : Algebra K E := ιF.toAlgebra
  set Mx := (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b x).map ιD with hMx
  set My := (CFSG.QuasithinUnique.Setup.SL2Modules.matRep b y).map ιD with hMy
  have hE : (Mx - 1) * (My - 1) = 0 := by
    have h1 := congrArg (Matrix.map · ιD) (matRep_quad b h)
    simp only [Matrix.map_mul, Matrix.map_sub _ (fun a b => map_sub ιD a b),
      Matrix.map_one _ (map_zero ιD) (map_one ιD), Matrix.map_zero _ (map_zero ιD)] at h1
    exact h1
  have hT : (tRep K E lab x - 1) * (tRep K E lab y - 1) = 0 := by
    have hv : ∀ v, ((tRep K E lab x - 1) * (tRep K E lab y - 1)).mulVec v = 0 := by
      intro v
      apply Φ.toLinearEquiv.injective
      rw [map_zero]
      have hΦ : ∀ g w, Φ.toLinearEquiv ((tRep K E lab g).mulVec w) =
          ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ιD).mulVec
            (Φ.toLinearEquiv w) := fun g w => by
        have := equiv_apply Φ g w
        rw [matRep_apply, matRepE_apply] at this
        exact this
      have hΦ' : ∀ g w, Φ.toLinearEquiv ((tRep K E lab g - 1).mulVec w) =
          ((CFSG.QuasithinUnique.Setup.SL2Modules.matRep b g).map ιD - 1).mulVec
            (Φ.toLinearEquiv w) := fun g w => by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, map_sub, hΦ, Matrix.sub_mulVec,
          Matrix.one_mulVec]
      rw [← Matrix.mulVec_mulVec, hΦ', hΦ', Matrix.mulVec_mulVec, ← hMx, ← hMy, hE,
        Matrix.zero_mulVec]
    exact Matrix.toLin'.injective (LinearMap.ext fun v => by
      rw [Matrix.toLin'_apply, hv v, map_zero, LinearMap.zero_apply])
  obtain ⟨P, Q, hPQ⟩ := tRep_single_iso (K := K) E lab j₀ hlab
  set φ := frK (F := K) E (j₀ : ℕ) with hφ
  have hR : ∀ g, ((lab j₀).rep g).map φ = P * tRep K E lab g * Q := fun g => by
    have h1 := hPQ.comm g
    rw [matMap_apply] at h1
    rw [h1, Matrix.mul_assoc, hPQ.mul_inv, Matrix.mul_one]
  have hlet : (((lab j₀).rep x - 1) * ((lab j₀).rep y - 1)).map φ = 0 := by
    rw [Matrix.map_mul, Matrix.map_sub _ (fun a b => map_sub φ a b),
      Matrix.map_sub _ (fun a b => map_sub φ a b), Matrix.map_one _ (map_zero φ) (map_one φ),
      hR, hR]
    have e1 : P * tRep K E lab x * Q - 1 = P * (tRep K E lab x - 1) * Q := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ.mul_inv]
    have e2 : P * tRep K E lab y * Q - 1 = P * (tRep K E lab y - 1) * Q := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hPQ.mul_inv]
    rw [e1, e2]
    calc P * (tRep K E lab x - 1) * Q * (P * (tRep K E lab y - 1) * Q)
        = P * (tRep K E lab x - 1) * (Q * P) * (tRep K E lab y - 1) * Q := by
          simp only [Matrix.mul_assoc]
      _ = 0 := by
        rw [hPQ.inv_mul, Matrix.mul_one, Matrix.mul_assoc P, hT, Matrix.mul_zero,
          Matrix.zero_mul]
  have hlet' : ((lab j₀).rep x - 1) * ((lab j₀).rep y - 1) = 0 :=
    Matrix.map_injective φ.injective (hlet.trans (Matrix.map_zero _ (map_zero φ)).symm)
  exact rep_lie_quad (lab j₀) hlie hlet'

omit [CharP K 2] [Fintype K] [Fact ρ.IsIrreducible] [Finite M] in
theorem letter_rank_bounds [Finite K] {z : ↥(cayleyGroup K)} [CharP K 2] (hz : z * z = 1)
    (hz1 : z ≠ 1) : 6 ≤ (G2L.lie.rep z - 1).rank ∧ 8 ≤ (G2L.st.rep z - 1).rank :=
  ⟨six_le_rank_repLie hz hz1, eight_le_rank_repSt hz hz1⟩

theorem natural_or_large_or_lie {f : ℕ} (hK : Fintype.card K = 2 ^ f) (hf : 1 ≤ f)
    (hnt : ∃ g, ρ g ≠ 1) :
    (∃ φ : M ≃+ (Ix3 → K), ∀ g w, φ (ρ g w) = g2Act g (φ w)) ∨
      (∀ z : ↥(cayleyGroup K), z * z = 1 → z ≠ 1 →
        6 * f + 1 ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1))) ∨
      ((∀ z : ↥(cayleyGroup K), z * z = 1 → z ≠ 1 →
        6 * f ≤ Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1))) ∧
        ∀ x y : ↥(cayleyGroup K), (ρ x - 1) * (ρ y - 1) = 0 →
          (repLie x - 1) * (repLie y - 1) = 0) := by
  classical
  obtain ⟨d, hd1, hDcard, hdesc⟩ := g2_descent hK hf hnt
  have : Finite (EndRing ρ) := finite_endRing ρ
  have : Module.Finite (EndRing ρ) M := Module.Finite.of_finite
  obtain ⟨E, _, _, _, ιF, ιD, lab, ⟨Φ⟩, hshift, hne, hdim⟩ :=
    hdesc (Module.finBasis (EndRing ρ) M)
  let _ : Algebra K E := ιF.toAlgebra
  set S := Finset.univ.filter fun j => lab j ≠ .one with hS
  have hfS : f ≤ S.card * d := le_card_support_mul lab hd1 hshift hne
  have hdisp : ∀ z : ↥(cayleyGroup K), Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) =
      d * (tRep K E lab z - 1).rank := fun z =>
    finrank_range_eq hDcard _ ιF ιD lab Φ hdim z
  by_cases hS2 : 2 ≤ S.card
  · right; left
    intro z hz hz1
    rw [hdisp]
    have h := eight_mul_le_rank_tRep E lab hz hz1 hS2
    nlinarith
  have hS1 : S.card = 1 := by
    obtain ⟨j, hj⟩ := hne
    have : 0 < S.card := Finset.card_pos.mpr ⟨j, by simpa [hS] using hj⟩
    omega
  obtain ⟨j₀, hj₀⟩ := Finset.card_eq_one.mp hS1
  have hother : ∀ j ≠ j₀, lab j = .one := fun j hj => by
    by_contra h
    have : j ∈ S := by simpa [hS] using h
    rw [hj₀] at this
    exact hj (Finset.mem_singleton.mp this)
  have hj₀S : lab j₀ ≠ .one := by
    have : j₀ ∈ S := by rw [hj₀]; exact Finset.mem_singleton_self j₀
    simpa [hS] using this
  have hfd : f ∣ d := dvd_of_single lab j₀ hshift hj₀S hother
  have hdf : f ≤ d := Nat.le_of_dvd (by omega) hfd
  have hsingle : ∀ z : ↥(cayleyGroup K), z * z = 1 →
      Module.finrank (ZMod 2) (LinearMap.range (ρ z - 1)) = d * ((lab j₀).rep z - 1).rank :=
    fun z hz => by rw [hdisp, rank_tRep_single E lab j₀ hother hz]
  rcases hl : lab j₀ with _ | _ | _ | _
  · exact absurd hl hj₀S
  · left
    have h6 : Module.finrank (EndRing ρ) M = 6 := by
      rw [hdim, prod_card_single lab j₀ hother, card_idx, hl]
    exact exists_natural_of_six hK hDcard hfd h6
  · right; right
    refine ⟨fun z hz hz1 => ?_, fun x y hxy => repLie_quad_of_rho _ ιF ιD lab Φ j₀ hother hl hxy⟩
    rw [hsingle z hz, hl]
    have h6 := (letter_rank_bounds (K := K) hz hz1).1
    nlinarith
  · right; left
    intro z hz hz1
    rw [hsingle z hz, hl]
    have h8 := (letter_rank_bounds (K := K) hz hz1).2
    nlinarith

end CFSG.Quasithin.B45G2

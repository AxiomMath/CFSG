module

public import CFSG.RankThree.GF2n.Smith81.S81YUOdd
public import CFSG.RankThree.GF2n.Smith81.S81YUWittC
public import CFSG.RankThree.GF2n.Smith81.S81RD8Pure
public import CFSG.RankThree.GF2n.Smith81.S81U6FE3
public import CFSG.RankThree.GF2n.Smith81.S81U6Transv

public section

namespace CFSG.RankThree.GF2n.Smith81.RootGenU

open CFSG.RankThree.GF2n.Smith81.U6Cube CFSG.RankThree.GF2n.Smith81.A5Cube
  CFSG.LieType.Universal.Unitary CFSG.ClassicalGroups.Unitary CFSG.LieType.BorelTits
  Matrix exteriorPower
  CFSG.RankThree.GF2n.Smith81 CFSG.RankThree.GF2n.Smith81.RootGen

variable {F : Type} [Field F] [Finite F] [CharP F 2] {σ : F ≃+* F} {K : Type} [Field K]


theorem u6_pure_rootPt {f : ℕ} (e : K ≃+* Fσ (unitaryInvolution F 2 f))
    {p : E3UWspace (unitaryInvolution F 2 f) e}
    (hp : IsPurePt (e3uGam (unitaryInvolution F 2 f) e) (e3uP0 (unitaryInvolution F 2 f) e) p) :
    e3uVal p ∈ RootPt (unitaryInvolution F 2 f) := by
  obtain ⟨g, hg, c, hc0, rfl⟩ := hp
  obtain ⟨h, rfl⟩ := MonoidHom.mem_range.mp hg
  have hfix : unitaryInvolution F 2 f ((e c : Fσ (unitaryInvolution F 2 f)) : F) =
      ((e c : Fσ (unitaryInvolution F 2 f)) : F) := mem_Fσ_iff.mp (e c).2
  have hne : ((e c : Fσ (unitaryInvolution F 2 f)) : F) ≠ 0 := fun h0 =>
    (map_ne_zero e).mpr hc0 (Subtype.ext h0)
  have key : e3uVal (c • e3uWact (unitaryInvolution F 2 f) e h
      (e3uP0 (unitaryInvolution F 2 f) e)) =
      ((e c : Fσ (unitaryInvolution F 2 f)) : F) • A5Cube.rho F (h : GL (Fin 6) F) (pt0 F) := rfl
  rw [key]
  exact smul_mem_RootPt hfix hne (rho_mem_RootPt h.2 pt0_mem_RootPt)

theorem u6_move {f : ℕ} (hF : Nat.card F = (2 ^ f) ^ 2) (e : K ≃+* Fσ (unitaryInvolution F 2 f))
    (r s : E3UWspace (unitaryInvolution F 2 f) e ≃ₗ[K] E3UWspace (unitaryInvolution F 2 f) e)
    (hr : IsRtU (unitaryInvolution F 2 f) e r) (hs : IsRtU (unitaryInvolution F 2 f) e s)
    (hB : ¬ (Odd (orderOf (r * s)) ∧ r * s ≠ 1))
    (p : E3UWspace (unitaryInvolution F 2 f) e)
    (hp : IsPurePt (e3uGam (unitaryInvolution F 2 f) e) (e3uP0 (unitaryInvolution F 2 f) e) p)
    (hpr : p ∈ LinearMap.range ((r : E3UWspace (unitaryInvolution F 2 f) e →ₗ[K]
      E3UWspace (unitaryInvolution F 2 f) e) - 1)) :
    ∃ c ∈ e3uGam (unitaryInvolution F 2 f) e, c * r = r * c ∧ s (c p) = c p := by
  obtain ⟨gx, hx, rfl⟩ := hr
  obtain ⟨gy, hy, rfl⟩ := hs
  have hσ : IsUnitaryInvolution (unitaryInvolution F 2 f) :=
    isUnitaryInvolution_unitaryInvolution hF
  obtain ⟨a, c, ha, hc, haa, -, hxa⟩ := U6Cube.exists_tv_of_isTransvec hσ.invol gx.2 hx
  obtain ⟨b, d, hb, hd, hbb, -, hyb⟩ := U6Cube.exists_tv_of_isTransvec hσ.invol gy.2 hy
  have hab : herm (unitaryInvolution F 2 f) a b = 0 :=
    u6_herm_eq_zero_of_not_odd hσ e hx hy ha hb hc hd haa hbb hxa hyb hB
  obtain ⟨hmemW, hne0, hpure⟩ := u6_pure_rootPt (f := f) e hp
  obtain ⟨v, hv⟩ := hpure
  have hvne : ιMulti F 3 v ≠ 0 := by
    rw [← hv]
    exact hne0
  have hθ : U6Cube.theta (unitaryInvolution F 2 f) (ιMulti F 3 v) = ιMulti F 3 v := by
    rw [← hv]
    exact mem_Wsub_iff.mp hmemW
  have hiso : ∀ i j, ∑ k, unitaryInvolution F 2 f (v i k) * v j k = 0 := fun i j =>
    U6Cube.hermF_eq_zero_of_theta_fixed_pure hσ.invol hvne hθ i j
  have hlin : LinearIndependent F v := A5Cube.linearIndependent_of_ιMulti_ne_zero hvne
  have hmemR : ιMulti F 3 v ∈ LinearMap.range (A5Cube.rho F (gx : GL (Fin 6) F) - 1) := by
    obtain ⟨y, hy'⟩ := hpr
    refine ⟨e3uVal y, ?_⟩
    rw [← hv, ← hy']
    rfl
  have hxa' : ((gx : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      1 + vecMulVec a (fun i => c * unitaryInvolution F 2 f (a i)) := by
    rw [hxa, tvMat]
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, vecMulVec_apply, smul_eq_mul]
    ring
  have hfa : (fun i => c * unitaryInvolution F 2 f (a i)) ⬝ᵥ a = 0 := by
    have h3 : (fun i => c * unitaryInvolution F 2 f (a i)) ⬝ᵥ a =
        c * herm (unitaryInvolution F 2 f) a a := by
      simp only [dotProduct, herm, Finset.mul_sum]
      exact Finset.sum_congr rfl fun i _ => by ring
    rw [h3, haa, mul_zero]
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact ha (funext hcon)
  have hfne : (fun i => c * unitaryInvolution F 2 f (a i)) ≠ 0 := by
    intro h0
    have h1 : c * unitaryInvolution F 2 f (a i0) = 0 := congrFun h0 i0
    rcases mul_eq_zero.mp h1 with h2 | h2
    · exact hc h2
    · exact hi0 (by simpa using h2)
  obtain ⟨hfv, hav⟩ := A5Cube.pure_range_support hxa' hfa ha hfne hlin hmemR
  obtain ⟨h, hha, hhb⟩ := u6_move_core hσ ha haa hbb hab hvne hiso hav
  have hMcomm : ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((gx : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) =
      ((gx : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
      ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) := by
    have hc1 := conj_tvMat hσ.invol h a c
    rw [hha, ← hxa] at hc1
    have hHi : ((((h : GL (Fin 6) F))⁻¹ : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) *
        ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    have hc2 := congrArg (fun x => x * ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F)) hc1
    simp only [mul_assoc, hHi, mul_one] at hc2
    exact hc2
  have hgcomm : h * gx = gx * h := by
    refine Subtype.ext (Units.ext ?_)
    simp only [Subgroup.coe_mul, Units.val_mul]
    exact hMcomm
  have hcomm_e : e3uWact (unitaryInvolution F 2 f) e h * e3uWact (unitaryInvolution F 2 f) e gx =
      e3uWact (unitaryInvolution F 2 f) e gx * e3uWact (unitaryInvolution F 2 f) e h := by
    rw [← map_mul, ← map_mul, hgcomm]
  have hfixv : ∀ i, ((gy : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec
      (((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (v i)) =
      ((h : GL (Fin 6) F) : Matrix (Fin 6) (Fin 6) F).mulVec (v i) := by
    intro i
    rw [hyb, tvMat_mulVec, hhb i, mul_zero, zero_smul, add_zero]
  have hW : e3uVal (e3uWact (unitaryInvolution F 2 f) e gy
      (e3uWact (unitaryInvolution F 2 f) e h p)) =
      e3uVal (e3uWact (unitaryInvolution F 2 f) e h p) := by
    rw [e3uWact_val, e3uWact_val, hv, rho_ιMulti, rho_ιMulti]
    congr 1
    funext i
    exact hfixv i
  exact ⟨e3uWact (unitaryInvolution F 2 f) e h, MonoidHom.mem_range.mpr ⟨h, rfl⟩, hcomm_e,
    Subtype.ext hW⟩

end CFSG.RankThree.GF2n.Smith81.RootGenU

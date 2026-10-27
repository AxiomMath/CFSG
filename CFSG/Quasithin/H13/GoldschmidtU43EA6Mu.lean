module

public import CFSG.Quasithin.H13.GoldschmidtU43EA6S1
public import CFSG.Quasithin.H13.GoldschmidtU43EMat4
public import CFSG.Quasithin.H13.GoldschmidtU43EMat6

public section

namespace CFSG.Quasithin.H13.U43

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H13.A5.Orth CFSG.Quasithin.H13.A6

variable {G : Type} [Group G]

namespace JWSetup

variable [Finite G] {z : G} (S : JWSetup z) (r : S.Rho)

@[expose] noncomputable def chiBarM : S.Nbar →* Mat3 where
  toFun := S.chiBar r
  map_one' := S.chiBar_one r
  map_mul' := S.chiBar_mul r

theorem chiBar_pow (g : S.Nbar) (n : ℕ) : S.chiBar r (g ^ n) = S.chiBar r g ^ n :=
  map_pow (S.chiBarM r) g n

theorem exists_mu_pair (e : S.Nbar ≃* alternatingGroup (Fin 6)) :
    ∃ m m' : S.Nbar, m ^ 3 = 1 ∧ m' ^ 3 = 1 ∧
      (S.chiBar r m = Amat1 ∨ S.chiBar r m = Amat2 ∨ S.chiBar r m = Amat3 ∨
        S.chiBar r m = Amat4) ∧
      (S.chiBar r m' = Bmat1 ∨ S.chiBar r m' = Bmat2 ∨ S.chiBar r m' = Bmat3 ∨
        S.chiBar r m' = Bmat4) := by
  have hu2 : (e S.ubar) ^ 2 = 1 := by
    rw [← map_pow, pow_two, S.ubar_sq, map_one]
  have hv4 : (e S.vbar) ^ 4 = 1 := by
    rw [← map_pow, S.vbar_pow_four, map_one]
  have hv2 : (e S.vbar) ^ 2 ≠ 1 := by
    rw [← map_pow]
    intro h
    exact S.vbar_sq_ne_one (e.injective (by rw [h, map_one]))
  have huv : e S.ubar * e S.vbar * (e S.ubar)⁻¹ = (e S.vbar)⁻¹ := by
    rw [← map_inv, ← map_mul, ← map_mul, S.ubar_vbar, map_inv]
  obtain ⟨⟨m, hm3, hm1, hm2⟩, ⟨m', hm3', hm1', hm2'⟩⟩ :=
    A6_dihedral_cyclic (e S.ubar) (e S.vbar) hu2 hv4 hv2 huv
  have hz : e S.zbar = (e S.vbar) ^ 2 := by
    rw [pow_two, ← map_mul, S.vbar_sq]
  refine ⟨e.symm m, e.symm m', ?_, ?_, ?_, ?_⟩
  · rw [← map_pow, hm3, map_one]
  · rw [← map_pow, hm3', map_one]
  ·
    have r1 : e.symm m * S.zbar = S.ubar * e.symm m := by
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hz, hm1]
    have r2 : e.symm m * S.ubar = (S.zbar * S.ubar) * e.symm m := by
      apply e.injective
      rw [map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply, hz, hm2]
    have c1 : S.chiBar r (e.symm m) * Zmat = Umat * S.chiBar r (e.symm m) := by
      have := congrArg (S.chiBar r) r1
      rwa [S.chiBar_mul, S.chiBar_mul, S.chiBar_zbar, S.chiBar_ubar] at this
    have c2 : S.chiBar r (e.symm m) * Umat = (Zmat * Umat) * S.chiBar r (e.symm m) := by
      have := congrArg (S.chiBar r) r2
      rwa [S.chiBar_mul, S.chiBar_mul, S.chiBar_mul, S.chiBar_zbar, S.chiBar_ubar] at this
    have c3 : S.chiBar r (e.symm m) ^ 3 = 1 := by
      rw [← S.chiBar_pow r, ← map_pow, hm3, map_one, S.chiBar_one]
    exact A_cases c1 c2 c3
  · have r1 : e.symm m' * S.zbar = (S.ubar * S.vbar) * e.symm m' := by
      apply e.injective
      rw [map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply, hz, hm1']
    have r2 : e.symm m' * (S.ubar * S.vbar) = (S.zbar * (S.ubar * S.vbar)) * e.symm m' := by
      apply e.injective
      rw [map_mul, map_mul, map_mul, map_mul, map_mul, MulEquiv.apply_symm_apply, hz, hm2']
    have c1 : S.chiBar r (e.symm m') * Zmat = Wmat * S.chiBar r (e.symm m') := by
      have := congrArg (S.chiBar r) r1
      simp only [S.chiBar_mul r, S.chiBar_zbar r, S.chiBar_ubar r, S.chiBar_vbar r] at this
      exact this
    have c2 : S.chiBar r (e.symm m') * Wmat = (Zmat * Wmat) * S.chiBar r (e.symm m') := by
      have := congrArg (S.chiBar r) r2
      simp only [S.chiBar_mul r, S.chiBar_zbar r, S.chiBar_ubar r, S.chiBar_vbar r] at this
      exact this
    have c3 : S.chiBar r (e.symm m') ^ 3 = 1 := by
      rw [← S.chiBar_pow r, ← map_pow, hm3', map_one, S.chiBar_one]
    exact B_cases c1 c2 c3

end JWSetup

end CFSG.Quasithin.H13.U43

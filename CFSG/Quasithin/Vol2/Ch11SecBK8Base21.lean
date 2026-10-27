module

public import CFSG.Quasithin.Vol2.Ch11SecBK8Base18
public import CFSG.Quasithin.Vol2.Ch11SecBK8Base8

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB.K8

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H CFSG.Assembly.LowTwoRank Matrix
open scoped Matrix

variable {K : Type} [Field K]

@[expose] def dotL (ψ : Fin 3 → K) : (Fin 3 → K) →ₗ[K] K where
  toFun v := ψ ⬝ᵥ v
  map_add' := dotProduct_add ψ
  map_smul' c v := by rw [dotProduct_smul, RingHom.id_apply]

theorem dotL_apply (ψ v : Fin 3 → K) : dotL ψ v = ψ ⬝ᵥ v := rfl

theorem dotL_ne_zero {ψ : Fin 3 → K} (hψ : ψ ≠ 0) : dotL ψ ≠ 0 := by
  intro h
  apply hψ
  funext j
  have := LinearMap.congr_fun h (Pi.single j 1)
  rwa [dotL_apply, dotProduct_single, mul_one] at this

theorem dg_eq_trvW {g : GL (Fin 3) K} {w ψ : Fin 3 → K}
    (hg : (g : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec w ψ) (v : I6 → K) :
    toAddMap (matAut (dgHom g)) v = trvW (dotL ψ) w v := by
  rw [toAddMap_matAut, dgHom_mulVec, hg, SL3Pair.one_add_vecMulVec_mulVec,
    SL3Pair.one_add_vecMulVec_mulVec]
  funext i
  rcases i with i | i <;> rfl

theorem trv_of_card_fix [Finite K] [CharP K 2] {y : MulAut (W6 K)} (hy : y ∈ normD K)
    (hsq : y ^ 2 = 1) (hfix : Nat.card (FixW y) = Nat.card K ^ 4) :
    ∃ (g : GL (Fin 3) K) (w ψ : Fin 3 → K), y = matAut (dgHom g) ∧
      (g : Matrix (Fin 3) (Fin 3) K) = 1 + vecMulVec w ψ ∧ ψ ⬝ᵥ w = 0 ∧ w ≠ 0 ∧ ψ ≠ 0 ∧
      Module.finrank K (fixSub g) = 2 := by
  have hq : 1 < Nat.card K := Finite.one_lt_card
  have h3 : Nat.card K ^ 3 < Nat.card (FixW y) := by
    rw [hfix]
    exact Nat.pow_lt_pow_right hq (by norm_num)
  obtain ⟨g, rfl⟩ := exists_dg_of_lt_card_fix hy h3
  have h2 : Module.finrank K (fixSub g) = 2 := by
    rw [card_fix_dg, card_fixSub, ← pow_mul, show 4 = 2 * 2 by rfl] at hfix
    have := Nat.pow_right_injective hq hfix
    omega
  obtain ⟨ψ, hψ, -, w, hg⟩ := exists_axis h2
  have hg1 : g ≠ 1 := by
    intro h1
    have := finrank_fixSub_lt (A := g)
    rw [h1] at h2
    have h4 : fixSub (1 : GL (Fin 3) K) = ⊤ :=
      eq_top_iff.mpr fun u _ => mem_fixSub.mpr (by rw [Units.val_one, Matrix.one_mulVec])
    rw [h4, finrank_top, Module.finrank_fin_fun] at h2
    omega
  have hw : w ≠ 0 := by
    rintro rfl
    apply hg1
    apply Units.ext
    rw [hg, Units.val_one]
    ext i j
    simp
  have hgsq : g * g = 1 := by
    apply matAut_dgHom_injective
    rw [matAut_dgHom_one, ← sq, matAut_dgHom_pow]
    exact hsq
  have hψw : ψ ⬝ᵥ w = 0 := by
    have h5 := congrArg (fun A : GL (Fin 3) K => (A : Matrix (Fin 3) (Fin 3) K) *ᵥ w) hgsq
    simp only [Units.val_mul, Units.val_one, Matrix.one_mulVec] at h5
    rw [← Matrix.mulVec_mulVec, hg, SL3Pair.one_add_vecMulVec_mulVec,
      SL3Pair.one_add_vecMulVec_mulVec, dotProduct_add, dotProduct_smul, smul_eq_mul, add_assoc,
      ← add_smul] at h5
    have h6 : (ψ ⬝ᵥ w + (ψ ⬝ᵥ w + ψ ⬝ᵥ w * ψ ⬝ᵥ w)) • w = 0 := by
      rw [add_eq_left] at h5
      exact h5
    have h7 := (smul_eq_zero.mp h6).resolve_right hw
    rw [← add_assoc, CharTwo.add_self_eq_zero, zero_add] at h7
    exact mul_self_eq_zero.mp h7
  exact ⟨g, w, ψ, rfl, hg, hψw, hw, hψ, h2⟩

theorem natSub_inf_sqSub {a b : K} (hab : a ≠ 0 ∨ b ≠ 0) (S : Submodule K (Fin 3 → K)) :
    natSub a b ⊓ sqSub S = natSubOf a b S := by
  apply le_antisymm
  · rintro _ ⟨⟨u, rfl⟩, hS⟩
    refine mem_natSubOf.mpr ⟨Multiplicative.toAdd u, ?_, rfl⟩
    have hS' : natEmb a b u ∈ sqSub S := hS
    rw [mem_sqSub, toAdd_natEmb, natVec_inl, natVec_inr] at hS'
    replace hS := hS'
    rcases hab with ha | hb
    · have := S.smul_mem a⁻¹ hS.1
      rwa [smul_smul, inv_mul_cancel₀ ha, one_smul] at this
    · have := S.smul_mem b⁻¹ hS.2
      rwa [smul_smul, inv_mul_cancel₀ hb, one_smul] at this
  · intro x hx
    obtain ⟨u, hu, rfl⟩ := mem_natSubOf.mp hx
    refine ⟨⟨_, rfl⟩, ?_⟩
    change natEmb a b (Multiplicative.ofAdd u) ∈ sqSub S
    rw [mem_sqSub, toAdd_natEmb, toAdd_ofAdd, natVec_inl, natVec_inr]
    exact ⟨S.smul_mem a hu, S.smul_mem b hu⟩

theorem natSubOf_le {a b : K} (S : Submodule K (Fin 3 → K)) : natSubOf a b S ≤ natSub a b := by
  intro x hx
  obtain ⟨u, -, rfl⟩ := mem_natSubOf.mp hx
  exact ⟨_, rfl⟩

end CFSG.Quasithin.Vol2.Ch11.SecB.K8

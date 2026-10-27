module

public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthIdentDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthNormIso
public import CFSG.LocalAnalysis.StandardType.GGQTwoDGNUnit
public import CFSG.ClassicalGroups.Unitary.Transitivity
public import CFSG.ClassicalInvolution.Phan.PhanDn.NormForm
public import CFSG.ClassicalInvolution.Phan.PhanDn.DiagTorus

public section

namespace CFSG.StandardType.QTwo

open CFSG.StandardType CFSG.StandardType.OrthTorus CFSG.ClassicalInvolution.PhanDn
open CFSG.ClassicalInvolution.Models.OrthogonalPairs CFSG.ClassicalGroups.Unitary
open CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits CFSG.LieType.Steinberg
open CFSG.ClassicalInvolution.Phan
open CFSG.RankThree.Classical2 (orthDerived)
open Multiplicative

local notation "𝔽₄" => GaloisField 2 2
local notation "σ₂" => unitaryInvolution (GaloisField 2 2) 2 1

variable {G : Type} [Group G] {p : ℕ} [Fact p.Prime] {Bs X : Subgroup G}

theorem qTwoD_card_gf4 : Nat.card (GaloisField 2 2) = (2 ^ 1) ^ 2 := by
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

structure OrthNormData (Φ : OrthFrameCore p Bs X) [Algebra Φ.F 𝔽₄] where
  E : QuadExt Φ.F 𝔽₄ σ₂
  χ : Φ.V ≃ₗ[Φ.F] (Fin Φ.r → 𝔽₄)
  ζ : normOne σ₂
  hζp : ζ ^ p = 1
  hχQ : ∀ v, Qn E Φ.r (χ v) = Φ.Q v
  hχτ : ∀ (g : Fin Φ.r → Multiplicative (ZMod p)) (v : Φ.V),
    χ (Φ.Δ.τ g v) = diagHom Φ.F σ₂ Φ.r (fun i => ζ ^ (toAdd (g i)).val) (χ v)

theorem qTwoD_exists_normData (Φ : OrthFrameCore p Bs X) (hF : Nat.card Φ.F = 2) :
    ∃ (_ : Algebra Φ.F 𝔽₄), Nonempty (OrthNormData Φ) := by
  obtain ⟨inst, E, χ, ζ, -, hζp, hχQ, hχτ⟩ := Φ.exists_normIso hF
  exact ⟨inst, ⟨⟨E, χ, ζ, hζp, hχQ, hχτ⟩⟩⟩

section Rep

variable {Φ : OrthFrameCore p Bs X} [Algebra Φ.F 𝔽₄] (N : OrthNormData Φ)

@[expose] noncomputable def OrthNormData.cχ :
    (Φ.V ≃ₗ[Φ.F] Φ.V) ≃* ((Fin Φ.r → 𝔽₄) ≃ₗ[Φ.F] (Fin Φ.r → 𝔽₄)) :=
  LinearEquiv.autCongr N.χ

theorem OrthNormData.cχ_apply (g : Φ.V ≃ₗ[Φ.F] Φ.V) (u : Fin Φ.r → 𝔽₄) :
    N.cχ g u = N.χ (g (N.χ.symm u)) := by
  simp [OrthNormData.cχ, LinearEquiv.autCongr_apply]

theorem OrthNormData.cχ_symm_apply (g : (Fin Φ.r → 𝔽₄) ≃ₗ[Φ.F] (Fin Φ.r → 𝔽₄)) (v : Φ.V) :
    N.cχ.symm g v = N.χ.symm (g (N.χ v)) :=
  LinearEquiv.autCongr_symm_apply_apply N.χ g v

theorem OrthNormData.cχ_mem_iff (g : Φ.V ≃ₗ[Φ.F] Φ.V) :
    N.cχ g ∈ TauCeti.QuadraticMap.orthogonalGroup (Qn N.E Φ.r) ↔
      g ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q := by
  rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff, TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
  constructor
  · intro h v
    have h1 := h (N.χ v)
    rw [N.cχ_apply, LinearEquiv.symm_apply_apply, N.hχQ, N.hχQ] at h1
    exact h1
  · intro h u
    rw [N.cχ_apply, N.hχQ, h, ← N.hχQ, LinearEquiv.apply_symm_apply]

theorem OrthNormData.cχ_tau (g : Fin Φ.r → Multiplicative (ZMod p)) :
    N.cχ (Φ.Δ.τ g) = diagHom Φ.F σ₂ Φ.r (fun i => N.ζ ^ (toAdd (g i)).val) := by
  apply LinearEquiv.ext
  intro u
  rw [N.cχ_apply, N.hχτ, LinearEquiv.apply_symm_apply]

@[expose] noncomputable def OrthNormData.rep : Su 𝔽₄ 2 1 Φ.r →* (Φ.V ≃ₗ[Φ.F] Φ.V) :=
  (N.cχ.symm : ((Fin Φ.r → 𝔽₄) ≃ₗ[Φ.F] (Fin Φ.r → 𝔽₄)) ≃* (Φ.V ≃ₗ[Φ.F] Φ.V)).toMonoidHom.comp
    (suEndN (F := Φ.F) σ₂ Φ.r)

theorem OrthNormData.cχ_rep (g : Su 𝔽₄ 2 1 Φ.r) :
    N.cχ (N.rep g) = suEndN (F := Φ.F) σ₂ Φ.r g := by
  simp [OrthNormData.rep]

theorem OrthNormData.rep_apply (g : Su 𝔽₄ 2 1 Φ.r) (v : Φ.V) :
    N.rep g v = N.χ.symm (g • N.χ v) := by
  rw [OrthNormData.rep, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, N.cχ_symm_apply,
    suEndN_apply]

theorem OrthNormData.rep_mem_orth (g : Su 𝔽₄ 2 1 Φ.r) :
    N.rep g ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q := by
  rw [← N.cχ_mem_iff, N.cχ_rep]
  exact suEndN_mem_orthogonalGroup N.E Φ.r g

theorem OrthNormData.rep_range_le (hr : 4 ≤ Φ.r) : N.rep.range ≤ orthDerived Φ.Q := by
  have hperf : commutator (Su 𝔽₄ 2 1 Φ.r) = ⊤ :=
    Group.isPerfect_def.mp (isPerfect_su_two (F := 𝔽₄) (by simpa using qTwoD_card_gf4) hr)
  have hO : (⊤ : Subgroup (Su 𝔽₄ 2 1 Φ.r)).map N.rep ≤
      TauCeti.QuadraticMap.orthogonalGroup Φ.Q := by
    rintro _ ⟨g, -, rfl⟩
    exact N.rep_mem_orth g
  calc N.rep.range = (⊤ : Subgroup (Su 𝔽₄ 2 1 Φ.r)).map N.rep := MonoidHom.range_eq_map _
    _ = (commutator (Su 𝔽₄ 2 1 Φ.r)).map N.rep := by rw [hperf]
    _ = ⁅(⊤ : Subgroup (Su 𝔽₄ 2 1 Φ.r)).map N.rep, (⊤ : Subgroup (Su 𝔽₄ 2 1 Φ.r)).map N.rep⁆ :=
        Subgroup.map_commutator _ _ _
    _ ≤ ⁅TauCeti.QuadraticMap.orthogonalGroup Φ.Q, TauCeti.QuadraticMap.orthogonalGroup Φ.Q⁆ :=
        Subgroup.commutator_mono hO hO

theorem OrthNormData.herm_eq_one {u : Fin Φ.r → 𝔽₄} (h : Qn N.E Φ.r u = 1) :
    herm σ₂ u u = 1 := by
  have h1 := algebraMap_Qn N.E Φ.r u
  rw [h, map_one] at h1
  calc herm σ₂ u u = ∑ i, σ₂ (u i) * u i := rfl
    _ = ∑ i, u i * σ₂ (u i) := Finset.sum_congr rfl fun i _ => mul_comm _ _
    _ = 1 := h1.symm

theorem OrthNormData.exists_su_smul_eq (hr : 4 ≤ Φ.r) {u u' : Fin Φ.r → 𝔽₄}
    (hu : Qn N.E Φ.r u = 1) (hu' : Qn N.E Φ.r u' = 1) :
    ∃ t : Su 𝔽₄ 2 1 Φ.r, t • u = u' := by
  obtain ⟨t, -, ht⟩ := exists_mem_T_smul_eq_of_norm_one
    (isUnitaryInvolution_unitaryInvolution (K := 𝔽₄) qTwoD_card_gf4) (Or.inl hr)
    (N.herm_eq_one hu) (N.herm_eq_one hu')
  exact ⟨t, ht⟩

end Rep

section Twist

variable {Φ : OrthFrameCore p Bs X} [Algebra Φ.F 𝔽₄] (N : OrthNormData Φ)

private theorem qtg_pow_val_neg {M : Type*} [Group M] {ζ : M} (hζ : ζ ^ p = 1) (a : ZMod p) :
    ζ ^ ((-a).val) = (ζ ^ a.val)⁻¹ := by
  haveI : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  rcases eq_or_ne a 0 with rfl | ha
  · simp
  · rw [ZMod.neg_val, if_neg ha]
    have hlt : a.val < p := ZMod.val_lt a
    have hsum : p - a.val + a.val = p := Nat.sub_add_cancel (Nat.le_of_lt hlt)
    have h1 : ζ ^ (p - a.val) * ζ ^ a.val = 1 := by
      rw [← pow_add, hsum, hζ]
    exact eq_inv_of_mul_eq_one_left h1

private theorem qtg_sigma_eq_inv {K : Type*} [Field K] {σ : K ≃+* K} (u : normOne σ) :
    σ (((u : Kˣ) : K)) = (((u⁻¹ : normOne σ) : Kˣ) : K) := by
  have hu : σ (((u : Kˣ) : K)) * (((u : Kˣ) : K)) = 1 := (mem_normOne σ).1 u.2
  rw [Subgroup.coe_inv, Units.val_inv_eq_inv_val]
  exact eq_inv_of_mul_eq_one_left hu

@[expose] noncomputable def OrthNormData.tauV (i : Fin Φ.r) : Φ.V ≃ₗ[Φ.F] Φ.V :=
  N.cχ.symm (tauAt N.E i)

theorem OrthNormData.cχ_tauV (i : Fin Φ.r) : N.cχ (N.tauV i) = tauAt N.E i :=
  N.cχ.apply_symm_apply _

theorem OrthNormData.tauV_mem_orth (i : Fin Φ.r) :
    N.tauV i ∈ TauCeti.QuadraticMap.orthogonalGroup Φ.Q := by
  rw [← N.cχ_mem_iff, N.cχ_tauV]
  exact tauAt_mem_orthogonalGroup N.E i

theorem OrthNormData.tauV_conj_tau (i : Fin Φ.r) (f : Fin Φ.r → Multiplicative (ZMod p)) :
    N.tauV i * Φ.Δ.τ f * (N.tauV i)⁻¹ = Φ.Δ.τ (SpCoord.sgnAut i f) := by
  apply N.cχ.injective
  have hinv : (tauAt N.E i)⁻¹ = tauAt N.E i :=
    inv_eq_of_mul_eq_one_right (tauAt_mul_self N.E i)
  rw [map_mul, map_mul, map_inv, N.cχ_tauV, N.cχ_tau, N.cχ_tau, hinv]
  have hupd : (fun j => N.ζ ^ (toAdd (SpCoord.sgnAut i f j)).val) =
      Function.update (fun j => N.ζ ^ (toAdd (f j)).val) i
        ((fun j => N.ζ ^ (toAdd (f j)).val) i)⁻¹ := by
    funext j
    by_cases hj : j = i
    · rw [hj, SpCoord.sgnAut_apply, Function.update_self, Function.update_self, toAdd_inv,
        qtg_pow_val_neg N.hζp (toAdd (f i))]
    · rw [SpCoord.sgnAut_apply, Function.update_of_ne hj, Function.update_of_ne hj]
  rw [hupd]
  apply LinearEquiv.ext
  intro x
  funext j
  by_cases hj : j = i
  · simp only [LinearEquiv.mul_apply, diagHom_apply, tauAt_apply, hj, Function.update_self,
      if_true, map_mul, N.E.isUnitary.invol, qtg_sigma_eq_inv]
  · simp only [LinearEquiv.mul_apply, diagHom_apply, tauAt_apply, Function.update_of_ne hj,
      if_false, if_neg hj]

end Twist

end CFSG.StandardType.QTwo

end

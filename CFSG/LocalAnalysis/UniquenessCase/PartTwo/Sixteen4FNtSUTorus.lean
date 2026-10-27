module

public import CFSG.ClassicalGroups.Unitary.SUnThreeLocalDefs
public import CFSG.ClassicalGroups.Unitary.Elements

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.ClassicalGroups.Unitary CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

open scoped Matrix

noncomputable abbrev s16ntSuSigma (K : Type) [Field K] [Finite K] [CharP K 2] : K ≃+* K :=
  unitaryInvolution K 2 1

@[expose] noncomputable def s16ntSuTorus (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    Subgroup ↥(SUid (s16ntSuSigma K) n) :=
  (CFSG.ClassicalGroups.SUnThreeLocal.diagGL K n).range.subgroupOf (SUid (s16ntSuSigma K) n)

noncomputable abbrev s16ntSuMono (K : Type) [Field K] [Finite K] [CharP K 2] (n : ℕ) :
    Subgroup ↥(SUid (s16ntSuSigma K) n) :=
  Subgroup.normalizer (s16ntSuTorus K n : Set ↥(SUid (s16ntSuSigma K) n))

@[expose] def s16ntSuV0 (n : ℕ) (K : Type) [Field K] : Fin n → K :=
  fun i => if i.val < 4 then 1 else 0

theorem s16nt_su_sigma_apply {K : Type} [Field K] [Finite K] [CharP K 2] (c : K) :
    s16ntSuSigma K c = c ^ 2 := by
  rw [s16ntSuSigma, unitaryInvolution_apply]; simp

theorem s16nt_su_pow_three {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) {c : K}
    (hc : c ≠ 0) : c ^ 3 = 1 := by
  haveI := Fintype.ofFinite K
  have := FiniteField.pow_card_sub_one_eq_one c hc
  rwa [← Nat.card_eq_fintype_card, hK] at this

theorem s16nt_su_norm_one {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {c : K} (hc : c ≠ 0) : s16ntSuSigma K c * c = 1 := by
  rw [s16nt_su_sigma_apply, ← s16nt_su_pow_three hK hc]; ring

theorem s16nt_su_exists_ne_zero_one {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 := by
  haveI : Nontrivial Kˣ :=
    Finite.one_lt_card_iff_nontrivial.mp (by rw [Nat.card_units, hK]; omega)
  obtain ⟨u, hu⟩ := exists_ne (1 : Kˣ)
  exact ⟨u, u.ne_zero, fun h => hu (Units.ext h)⟩

theorem s16nt_su_exists_omega {K : Type} [Field K] [Finite K] (hK : Nat.card K = 4) :
    ∃ ω : K, ω ≠ 0 ∧ ω ≠ 1 ∧ ω ^ 2 + ω + 1 = 0 := by
  obtain ⟨ω, h0, h1⟩ := s16nt_su_exists_ne_zero_one hK
  have : (ω - 1) * (ω ^ 2 + ω + 1) = 0 := by linear_combination s16nt_su_pow_three hK h0
  exact ⟨ω, h0, h1, (mul_eq_zero.mp this).resolve_left (sub_ne_zero.mpr h1)⟩

theorem s16nt_su_conj_smul {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    (g t : SUid (s16ntSuSigma K) n) {a b : Fin n → K} {l : K} (hl : s16ntSuSigma K l * l = 1)
    (ht : ∀ v : Fin n → K, t • v = v + herm (s16ntSuSigma K) a v • a) (hga : g • a = l • b)
    (v : Fin n → K) : (g * t * g⁻¹) • v = v + herm (s16ntSuSigma K) b v • b := by
  have h := conj_smul_of_tv g t (c := 1) (fun v => by rw [one_mul]; exact ht v) v
  rw [one_mul, hga, herm_smul_left, smul_smul] at h
  rw [h]
  congr 2
  linear_combination (herm (s16ntSuSigma K) b v) * hl

theorem s16nt_su_diag_mem {K : Type} [Field K] [Finite K] [CharP K 2] (hK : Nat.card K = 4)
    {n : ℕ} (u : Fin n → Kˣ) (hu : ∏ i, u i = 1) :
    ∃ d ∈ s16ntSuTorus K n, ∀ v : Fin n → K, d • v = fun i => (u i : K) * v i := by
  classical
  let D : Matrix (Fin n) (Fin n) K := Matrix.diagonal fun i => (u i : K)
  have hDdet : D.det = 1 := by
    change (Matrix.diagonal fun i => (u i : K)).det = 1
    rw [Matrix.det_diagonal, ← Units.coe_prod, hu, Units.val_one]
  have hDiso : ∀ x y, herm (s16ntSuSigma K) (D *ᵥ x) (D *ᵥ y) =
      herm (s16ntSuSigma K) x y := by
    intro x y
    simp only [D, herm, Matrix.mulVec_diagonal]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul,
      show s16ntSuSigma K (u i) * s16ntSuSigma K (x i) * ((u i : K) * y i) =
        (s16ntSuSigma K (u i) * (u i : K)) * (s16ntSuSigma K (x i) * y i) by ring,
      s16nt_su_norm_one hK (u i).ne_zero, one_mul]
  refine ⟨mkSU (s16ntSuSigma K) D hDdet hDiso, ?_, ?_⟩
  · change ((mkSU (s16ntSuSigma K) D hDdet hDiso : SUid (s16ntSuSigma K) n) :
      GL (Fin n) K) ∈ (CFSG.ClassicalGroups.SUnThreeLocal.diagGL K n).range
    rw [MonoidHom.mem_range]
    exact ⟨u, Units.ext (by rw [CFSG.ClassicalGroups.SUnThreeLocal.coe_diagGL]; rfl)⟩
  · intro v
    rw [mkSU_smul]
    funext i
    simp only [D, Matrix.mulVec_diagonal]

theorem s16nt_su_torus_odd_fix {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : Nat.card K = 4) {n : ℕ} (hn : 2 ≤ n) :
    Odd (Nat.card ↥(s16ntSuTorus K n)) ∧
      ∀ v : Fin n → K, (∀ t ∈ s16ntSuTorus K n, t • v = v) → v = 0 := by
  classical
  constructor
  · let f : ↥(s16ntSuTorus K n) →*
        ↥((CFSG.ClassicalGroups.SUnThreeLocal.diagGL K n).range) :=
      { toFun := fun t => ⟨(t : SUid (s16ntSuSigma K) n), t.2⟩
        map_one' := rfl
        map_mul' := fun _ _ => rfl }
    have hf : Function.Injective f := by
      intro t t' h
      have h' : ((t : SUid (s16ntSuSigma K) n) : GL (Fin n) K) =
          ((t' : SUid (s16ntSuSigma K) n) : GL (Fin n) K) :=
        congrArg (fun s : ↥((CFSG.ClassicalGroups.SUnThreeLocal.diagGL K n).range) =>
          (s : GL (Fin n) K)) h
      exact Subtype.ext (Subtype.ext h')
    have h3 : Nat.card (Fin n → Kˣ) = 3 ^ n := by
      rw [Nat.card_fun, Nat.card_units, hK, Nat.card_fin]
    have hodd : Odd (3 ^ n) := Odd.pow (show Odd 3 from ⟨1, by norm_num⟩)
    have hdvd : Nat.card ↥(s16ntSuTorus K n) ∣ 3 ^ n := by
      rw [← h3]
      exact (Subgroup.card_dvd_of_injective f hf).trans
        (Subgroup.card_range_dvd (CFSG.ClassicalGroups.SUnThreeLocal.diagGL K n))
    exact Odd.of_dvd_nat hodd hdvd
  · intro v hv
    funext i
    obtain ⟨ω, hω0, hω1, _⟩ := s16nt_su_exists_omega hK
    let ωu : Kˣ := Units.mk0 ω hω0
    let j : Fin n := ⟨if i.val = 0 then 1 else 0, by split_ifs <;> omega⟩
    have hji : j ≠ i := by
      intro h
      have h' := congrArg Fin.val h
      simp only [j] at h'
      split_ifs at h' <;> omega
    let u : Fin n → Kˣ := Pi.mulSingle i ωu * Pi.mulSingle j ωu⁻¹
    have hui : u i = ωu := by
      simp only [u, Pi.mul_apply, Pi.mulSingle_eq_same, Pi.mulSingle_eq_of_ne' hji, mul_one]
    have hu : ∏ k, u k = 1 := by
      simp only [u, Pi.mul_apply, Finset.prod_mul_distrib, Fintype.prod_pi_mulSingle',
        mul_inv_cancel]
    obtain ⟨d, hdT, hdv⟩ := s16nt_su_diag_mem hK u hu
    have hfix : v = fun k => (u k : K) * v k := (hv d hdT).symm.trans (hdv v)
    have hi : v i = (u i : K) * v i := congrFun hfix i
    have hiω : v i = ω * v i := by
      calc v i = (u i : K) * v i := hi
        _ = ω * v i := by simp only [hui, ωu, Units.val_mk0]
    have hzero : (ω - 1) * v i = 0 := by linear_combination -hiω
    exact (mul_eq_zero.mp hzero).resolve_left (sub_ne_zero.mpr hω1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

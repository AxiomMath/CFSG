module

public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Defs
public import CFSG.LocalAnalysis.StandardType.GGSporKOrd7Lift
public import CFSG.LieType.ChevTwo.OppCl.AutLifts
public import CFSG.LocalAnalysis.ComponentInitial.DiagonalSemilinear
public import CFSG.LieType.BorelTits.Classical

public section

namespace CFSG.StandardType.SporadicShape

open CFSG CFSG.StandardType CFSG.Assembly CFSG.Blueprint CFSG.Open

open CFSG.LieType.BorelTits CFSG.LieType.ChevTwo.OppCl Matrix in
theorem ord7Param_PSU {n f : ℕ} (h7 : ¬ 7 ∣ f) : Ord7Param .PSU n 2 f := by
  intro R _ _ hR hmodel
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hadm : StatedLieAdmissible .PSU n 2 f := LieModel.admissible hmodel
  rw [StatedLieAdmissible] at hadm
  obtain ⟨hp2, hf1, hn, hneq⟩ := hadm
  have hn0 : n ≠ 0 := by omega
  have hclass : StatedClassicalModel R .PSU n 2 f :=
    LieModel.statedClassicalModel_of_ne_zero hn0 hmodel
  rw [StatedClassicalModel] at hclass
  obtain ⟨_, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hclass
  letI : Field K := hKfield
  letI : Finite K := hKfin
  have hKcard' : Nat.card K = 2 ^ (2 * f) := by
    rw [hKcard, ← pow_mul, Nat.mul_comm]
  haveI : CharP K 2 := charP_of_natCard_eq (p := 2) (f := 2 * f) hKcard'
  have hq : 2 < 2 ^ f ∨ 4 ≤ n := by
    by_cases hn3 : n = 3
    · left
      have h2f : 2 ^ f ≠ 2 := by
        intro h2
        exact hneq (by rw [hn3, h2])
      have h2le : 2 ≤ 2 ^ f := by
        simpa using (pow_right_monotone (by norm_num : 1 ≤ (2 : ℕ)) hf1)
      omega
    · right; omega
  have h7q1 : ¬ 7 ∣ 2 ^ f + 1 := by
    have hmod : ∀ m : ℕ, 2 ^ m % 7 = 1 ∨ 2 ^ m % 7 = 2 ∨ 2 ^ m % 7 = 4 := by
      intro m
      induction m with
      | zero => left; norm_num
      | succ m ih =>
        rw [pow_succ, Nat.mul_mod]
        rcases ih with hc | hc | hc
        · right; left; rw [hc]
        · right; right; rw [hc]
        · left; rw [hc]
    intro h
    have hf : (2 ^ f + 1) % 7 = 0 := Nat.mod_eq_zero_of_dvd h
    rw [Nat.add_mod] at hf
    rcases hmod f with h1 | h1 | h1
    · rw [h1] at hf; norm_num at hf
    · rw [h1] at hf; norm_num at hf
    · rw [h1] at hf; norm_num at hf
  have hcardAut : Nat.card (K ≃+* K) = 2 * f :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      (p := 2) (n := 2 * f) Nat.prime_two K hKcard').1
  have h7F : ¬ 7 ∣ Nat.card (K ≃+* K) := by
    rw [hcardAut]
    intro hdvd
    rcases (Nat.Prime.dvd_mul (by norm_num : Nat.Prime 7)).mp hdvd with h72 | h7f
    · norm_num at h72
    · exact h7 h7f
  haveI : Nontrivial (Fin n → K) :=
    ⟨fun _ => 1, fun _ => 0, by
      intro h
      exact one_ne_zero (congr_fun h ⟨0, by omega⟩)⟩
  let Φ : ReflForm K (Fin n → K) := unitaryForm 2 f hKcard n
  have hexv : ∃ u v : Fin n → K, Φ.β u v ≠ 0 := by
    by_contra h
    simp only [not_exists, not_ne_iff] at h
    obtain ⟨u, hu⟩ := exists_ne (0 : Fin n → K)
    exact hu (Φ.nondeg u (fun v => h u v))
  let N : Subgroup (StatedSU n (2 ^ f) K) :=
    (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ f) K)
  have hind : ∀ R' : Subgroup (MulAut (StatedProj (StatedSU n (2 ^ f) K))),
      IsPGroup 7 R' → ∀ α ∈ R', ∃ r : Equiv.Perm (Fin n → K),
        r ∈ semilinGroup K (Fin n → K) ∧ SemiIso Φ r ∧
        Induces (QuotientGroup.mk' N) (natRep (StatedSU n (2 ^ f) K)) r α := by
    intro R' hR' α hα
    exact induced_PSU (F := K) (p := 7) (hp2 := by norm_num) (f := f) (hK := hKcard)
      (n := n) (hn := hn) (hq := hq) (R := R') (hR := hR') α hα
  have h7k : ¬ 7 ∣ Nat.card (QuotientGroup.mk' N).ker := by
    rw [QuotientGroup.ker_mk']
    intro hdvd
    obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' 7 hdvd
    have hxS : (((x : StatedSU n (2 ^ f) K)) : GL (Fin n) K) ∈
        StatedScalars (Fin n) K :=
      Subgroup.mem_subgroupOf.mp x.2
    obtain ⟨c, hc⟩ := MonoidHom.mem_range.mp hxS
    let d : K := c
    have hcpow : d ^ (2 ^ f + 1) = 1 := by
      obtain ⟨u, v, huv⟩ := hexv
      have hA : (((x : StatedSU n (2 ^ f) K)) : GL (Fin n) K) =
          Matrix.GeneralLinearGroup.scalar (Fin n) c := hc.symm
      have hvec : ∀ w, (((((x : N) : StatedSU n (2 ^ f) K)) : GL (Fin n) K) :
          Matrix (Fin n) (Fin n) K) *ᵥ w = d • w := by
        intro w
        rw [hA, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
          Matrix.diagonal_const_mulVec]
      have hform : Φ.β (d • u) (d • v) = Φ.β u v := by
        have h := statedSU_preserves (p := 2) (f := f) hKcard
          (x : StatedSU n (2 ^ f) K).2 u v
        rw [hvec u, hvec v] at h
        exact h
      have hσ : Φ.σ d = d ^ (2 ^ f) := by
        rw [show Φ.σ = unitaryInvolution K 2 f from rfl, unitaryInvolution_apply]
      have h1 : Φ.β (d • u) (d • v) = Φ.σ d * (d * Φ.β u v) := by
        rw [Φ.smul_left, Φ.smul_right]
      have h3 : d ^ (2 ^ f) * (d * Φ.β u v) = Φ.β u v := by
        rw [← hσ, ← h1, hform]
      have h2 : (d ^ (2 ^ f) * d) * Φ.β u v = 1 * Φ.β u v := by
        rw [one_mul, mul_assoc]
        exact h3
      have hone : d ^ (2 ^ f) * d = 1 := mul_right_cancel₀ huv h2
      rw [pow_succ]
      exact hone
    have hc7div : orderOf c ∣ 2 ^ f + 1 := by
      have h := orderOf_dvd_of_pow_eq_one hcpow
      simpa [d, orderOf_units] using h
    have hcne : c ≠ 1 := by
      intro hc1
      have hx1 : x = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        change ((((x : N) : StatedSU n (2 ^ f) K)) : GL (Fin n) K) = 1
        rw [← hc, hc1, map_one]
      rw [hx1, orderOf_one] at hxord
      norm_num at hxord
    have hx7 : x ^ 7 = 1 := by rw [← hxord, pow_orderOf_eq_one]
    have hA7 : ((((x : StatedSU n (2 ^ f) K)) : GL (Fin n) K)) ^ 7 = 1 := by
      have h := congrArg (fun z : N => (((z : StatedSU n (2 ^ f) K)) : GL (Fin n) K)) hx7
      simpa using h
    have hd7 : d ^ 7 = 1 := by
      have hmA :
          (Matrix.GeneralLinearGroup.scalar (Fin n) c : Matrix (Fin n) (Fin n) K) ^ 7 = 1 := by
        have h := congrArg (fun z : GL (Fin n) K => (z : Matrix (Fin n) (Fin n) K)) hA7
        rw [← hc] at h
        simpa using h
      have h := congrArg (fun M : Matrix (Fin n) (Fin n) K =>
        M ⟨0, by omega⟩ ⟨0, by omega⟩) hmA
      simpa [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.diagonal_pow, Matrix.diagonal_apply_eq, d] using h
    have hc7dvd : orderOf c ∣ 7 := by
      have h := orderOf_dvd_of_pow_eq_one hd7
      simpa [d, orderOf_units] using h
    have hordc : orderOf c = 7 := by
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 7)).mp hc7dvd with h1 | h7'
      · exact absurd (orderOf_eq_one_iff.mp h1) hcne
      · exact h7'
    rw [hordc] at hc7div
    exact h7q1 hc7div
  have hlin : ∀ r : Equiv.Perm (Fin n → K),
      r ∈ semilinGroup K (Fin n → K) → SemiIso Φ r →
      (∀ (c : K) (w : Fin n → K), r (c • w) = c • r w) →
      IsPGroup 7 (Subgroup.zpowers r) →
        ∃ h : StatedSU n (2 ^ f) K,
          ∀ w, r w = natRep (StatedSU n (2 ^ f) K) h w := by
    intro r hmem hsem hrlin hgrp
    have hadd : ∀ u v, r (u + v) = r u + r v := hmem.1
    obtain ⟨τ, hτ⟩ := hsem
    have hτid : τ = RingEquiv.refl K := by
      ext a
      obtain ⟨b, rfl⟩ := (unitaryInvolution K 2 f).surjective a
      obtain ⟨u, v, huv⟩ := hexv
      have h1 : Φ.σ b * τ (Φ.β u v) = Φ.β (r (b • u)) (r v) := by
        rw [hrlin, Φ.smul_left, hτ]
      have h2 : Φ.β (r (b • u)) (r v) = τ (Φ.σ b) * τ (Φ.β u v) := by
        rw [hτ, Φ.smul_left, map_mul]
      have key : Φ.σ b * τ (Φ.β u v) = τ (Φ.σ b) * τ (Φ.β u v) := h1.trans h2
      have hτne : τ (Φ.β u v) ≠ 0 := fun h0 =>
        huv (τ.injective (h0.trans (map_zero τ).symm))
      exact (mul_right_cancel₀ hτne key).symm
    have hpres : ∀ u v, Φ.β (r u) (r v) = Φ.β u v := by
      intro u v
      rw [hτ]
      exact congrArg (fun σ : K ≃+* K => σ (Φ.β u v)) hτid
    let g : (Fin n → K) →ₗ[K] (Fin n → K) :=
      { toFun := r, map_add' := hadd, map_smul' := hrlin }
    let M : Matrix (Fin n) (Fin n) K := LinearMap.toMatrixAlgEquiv' g
    have hMf : Matrix.toLinAlgEquiv' M = g := by
      dsimp [M]; exact Matrix.toLinAlgEquiv'_toMatrixAlgEquiv' g
    have hMvec : ∀ w, M *ᵥ w = r w := by
      intro w
      have h := congrArg (fun g' : (Fin n → K) →ₗ[K] (Fin n → K) => g' w) hMf
      simpa [Matrix.toLinAlgEquiv'_apply, g] using h
    have hMpres : ∀ u v, Φ.β (M *ᵥ u) (M *ᵥ v) = Φ.β u v := by
      intro u v
      rw [hMvec u, hMvec v]
      exact hpres u v
    have hmat : (M.map (unitaryInvolution K 2 f))ᵀ * M = 1 :=
      (unitaryForm_preserves_iff (p := 2) (f := f) hKcard M).mp hMpres
    have hdetpow : M.det ^ (2 ^ f + 1) = 1 := by
      have h := congrArg Matrix.det hmat
      rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_one] at h
      have hσdet : (M.map (unitaryInvolution K 2 f)).det = M.det ^ (2 ^ f) := by
        have hmap : M.map (unitaryInvolution K 2 f) =
            (unitaryInvolution K 2 f).mapMatrix M := by
          ext i j; rfl
        rw [hmap, ← RingEquiv.map_det (unitaryInvolution K 2 f) M, unitaryInvolution_apply]
      rw [hσdet] at h
      rw [← pow_succ] at h
      exact h
    obtain ⟨k, hk⟩ := IsPGroup.exists_orderOf_eq_pow (p := 7) hgrp
      ⟨r, Subgroup.mem_zpowers r⟩
    have hk' : orderOf r = 7 ^ k := by
      rw [← Subgroup.orderOf_mk r (Subgroup.mem_zpowers r)]
      exact hk
    have hrk : r ^ (7 ^ k) = 1 := by
      rw [← hk']; exact pow_orderOf_eq_one r
    have hfn : ∀ m w, (g ^ m) w = (r ^ m) w := by
      intro m
      induction m with
      | zero => intro w; simp
      | succ m ih =>
        intro w
        rw [pow_succ', pow_succ']
        change g ((g ^ m) w) = r ((r ^ m) w)
        rw [ih w]
        rfl
    have hfpow : g ^ (7 ^ k) = 1 := by
      apply LinearMap.ext
      intro w
      rw [hfn (7 ^ k) w, hrk]
      rfl
    have hMpow : M ^ (7 ^ k) = 1 := by
      apply Matrix.toLinAlgEquiv'.injective
      rw [map_pow, map_one, hMf]
      exact hfpow
    have hdet7 : M.det ^ (7 ^ k) = 1 := by
      have h := congrArg Matrix.det hMpow
      rw [Matrix.det_pow, Matrix.det_one] at h
      exact h
    have hcop : Nat.Coprime (2 ^ f + 1) (7 ^ k) :=
      Nat.Prime.coprime_pow_of_not_dvd (by norm_num : Nat.Prime 7) h7q1
    have horder : orderOf M.det = 1 :=
      Nat.eq_one_of_dvd_coprimes hcop (orderOf_dvd_of_pow_eq_one hdetpow)
        (orderOf_dvd_of_pow_eq_one hdet7)
    have hdet : M.det = 1 := orderOf_eq_one_iff.mp horder
    let A : GL (Fin n) K :=
      Matrix.GeneralLinearGroup.mkOfDetNeZero M (by rw [hdet]; exact one_ne_zero)
    have hA : A ∈ StatedSU n (2 ^ f) K :=
      mkOfDetNeZero_mem_statedSU (p := 2) (f := f) hKcard M hdet hMpres
    refine ⟨⟨A, hA⟩, fun w => ?_⟩
    rw [natRep_apply, Matrix.GeneralLinearGroup.val_mkOfDetNeZero]
    exact (hMvec w).symm
  have hbound : (Nat.card (MulAut (StatedProj (StatedSU n (2 ^ f) K)))).factorization 7 ≤
      (Nat.card (StatedProj (StatedSU n (2 ^ f) K))).factorization 7 :=
    ord7_factorization_le_of_lift (F := K) (V := Fin n → K)
      (H := StatedSU n (2 ^ f) K) (K := StatedProj (StatedSU n (2 ^ f) K))
      (π := QuotientGroup.mk' N) (hπ := QuotientGroup.mk'_surjective N)
      (ρ := natRep (StatedSU n (2 ^ f) K)) (hρ := natRep_injective _)
      (P := SemiIso Φ) (hP1 := semiIso_one Φ)
      (hPm := fun r s hr hs => semiIso_mul Φ hr hs)
      (hPi := fun r hr => semiIso_inv Φ hr)
      (h7F := h7F) (h7k := h7k) (hind := hind) (hlin := hlin)
  have hRcard : Nat.card R = Nat.card (StatedProj (StatedSU n (2 ^ f) K)) :=
    Nat.card_congr e.toEquiv
  have hRaut : Nat.card (MulAut R) =
      Nat.card (MulAut (StatedProj (StatedSU n (2 ^ f) K))) :=
    Nat.card_congr (MulAut.congr e).toEquiv
  rw [hRaut, hRcard]
  exact hbound

end CFSG.StandardType.SporadicShape

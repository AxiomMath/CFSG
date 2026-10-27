module

public import CFSG.RankThree.PartTwo.Sec21.Item223CensusResProofSeven
public import CFSG.LieType.Multipliers.G23Bridge
public import CFSG.LieType.Simplicity.Exceptional

public section

namespace CFSG.RankThree.PartTwo.Sec21

namespace Item223CensusResProof

open Polynomial Finset

section Seven

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem aeval_cyclotomic_seven (c : Module.End K V) : aeval c (cyclotomic 7 K) = cyc7 c := by
  have : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  rw [cyclotomic_prime, map_sum, cyc7]
  simp

theorem eq_zero_of_sum_pow_apply (hirr : Irreducible (cyclotomic 7 K)) {c : Module.End K V}
    {v : V} (hv : (cyc7 c) v = 0) (hv0 : v ≠ 0) {r : Fin 6 → K}
    (h : ∑ i, r i • (c ^ (i : ℕ)) v = 0) : r = 0 := by
  classical
  set P : K[X] := ∑ i : Fin 6, C (r i) * X ^ (i : ℕ) with hP
  have hPv : (aeval c P) v = 0 := by
    rw [hP, map_sum, LinearMap.sum_apply]
    simpa [Module.End.mul_apply, Module.algebraMap_end_apply] using h
  by_contra hr
  have hP0 : P ≠ 0 := by
    intro hP0
    apply hr
    funext i
    have := congrArg (fun p : K[X] => p.coeff (i : ℕ)) hP0
    simpa [hP, finsetSum_coeff, coeff_C_mul_X_pow, Fin.val_inj] using this
  have hdeg : P.natDegree ≤ 5 := by
    rw [hP]
    refine natDegree_sum_le_of_forall_le _ _ fun i _ => ?_
    exact (natDegree_C_mul_X_pow_le (r i) (i : ℕ)).trans (by have := i.isLt; omega)
  have hnd : ¬ cyclotomic 7 K ∣ P := by
    intro hd
    have h1 := natDegree_le_of_dvd hd hP0
    rw [natDegree_cyclotomic, Nat.totient_prime (by norm_num)] at h1
    omega
  obtain ⟨a, b, hab⟩ := hirr.coprime_iff_not_dvd.mpr hnd
  apply hv0
  have h1 := congrArg (fun p : K[X] => (aeval c p) v) hab
  simp only [map_add, map_mul, map_one, LinearMap.add_apply, Module.End.mul_apply,
    Module.End.one_apply] at h1
  rw [aeval_cyclotomic_seven, hv, hPv, map_zero, map_zero, add_zero] at h1
  exact h1.symm

variable [FiniteDimensional K V]

theorem apply_eq_zero_of_cyc7_seven (hV : Module.finrank K V ≤ 11)
    (hirr : Irreducible (cyclotomic 7 K)) {c N : Module.End K V} (hNc : N * c = c * N)
    (hN3 : N ^ 3 = 0) {y : V} (hy : (cyc7 c) y = 0) : N y = 0 := by
  by_contra hNy
  have hcomm : Commute N (cyc7 c) := commute_cyc7 hNc
  obtain ⟨y', hy', hz, hNz⟩ := exists_last_ne_zero hN3 hNy
  have hNcv : ∀ (k : ℕ) (w : V), N ((c ^ k) w) = (c ^ k) (N w) := fun k w => by
    rw [← Module.End.mul_apply, (Commute.pow_right (hNc : Commute N c) k).eq,
      Module.End.mul_apply]
  have hy'0 : (cyc7 c) y' = 0 := by
    rcases hy' with rfl | rfl
    · exact hy
    · rw [← Module.End.mul_apply, ← hcomm.eq, Module.End.mul_apply, hy, map_zero]
  set z := N y'
  have hz0 : (cyc7 c) z = 0 := by
    rw [← Module.End.mul_apply, ← hcomm.eq, Module.End.mul_apply, hy'0, map_zero]
  have hli : LinearIndependent K (Sum.elim (fun i : Fin 6 => (c ^ (i : ℕ)) y')
      (fun i : Fin 6 => (c ^ (i : ℕ)) z)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type] at hg
    simp only [Sum.elim_inl, Sum.elim_inr] at hg
    have hN := congrArg N hg
    simp only [map_add, map_sum, map_smul, hNcv, hNz, map_zero, smul_zero, sum_const_zero,
      add_zero] at hN
    have h1 := eq_zero_of_sum_pow_apply hirr hz0 hz hN
    have h1' : ∀ i, g (Sum.inl i) = 0 := fun i => by simpa using congrFun h1 i
    simp only [h1', zero_smul, sum_const_zero, zero_add] at hg
    have h2 := eq_zero_of_sum_pow_apply hirr hz0 hz hg
    rintro (i | i)
    · exact h1' i
    · simpa using congrFun h2 i
  have := hli.fintype_card_le_finrank
  simp only [Fintype.card_sum, Fintype.card_fin] at this
  omega

theorem apply_eq_zero_of_fixed_seven (hV : Module.finrank K V ≤ 7) (h7 : (7 : K) ≠ 0)
    (hirr : Irreducible (cyclotomic 7 K)) {c N : Module.End K V} (hNc : N * c = c * N)
    (hN3 : N ^ 3 = 0) {v₀ : V} (hv₀ : (cyc7 c) v₀ = 0) (hv₀0 : v₀ ≠ 0) {y : V}
    (hy : c y = y) : N y = 0 := by
  by_contra hNy
  obtain ⟨y', hy', hz, hNz⟩ := exists_last_ne_zero hN3 hNy
  have hNcv : ∀ w, N (c w) = c (N w) := fun w => by
    rw [← Module.End.mul_apply, hNc, Module.End.mul_apply]
  have hcy' : c y' = y' := by
    rcases hy' with rfl | rfl
    · exact hy
    · rw [← hNcv, hy]
  set z := N y'
  have hcz : c z = z := by rw [← hNcv, hcy']
  have hΦc : ∀ (k : ℕ) (w : V), (cyc7 c) ((c ^ k) w) = (c ^ k) ((cyc7 c) w) := fun k w => by
    rw [← Module.End.mul_apply, ← (commute_cyc7 ((Commute.refl c).pow_left k)).eq,
      Module.End.mul_apply]
  have hli : LinearIndependent K (Sum.elim ![y', z] (fun i : Fin 6 => (c ^ (i : ℕ)) v₀)) := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fintype.sum_sum_type, Fin.sum_univ_two] at hg
    simp only [Sum.elim_inl, Sum.elim_inr, Matrix.cons_val_zero, Matrix.cons_val_one] at hg
    have hΦ := congrArg (fun w => (cyc7 c : Module.End K V) w) hg
    simp only [map_add, map_sum, map_smul, hΦc, hv₀, map_zero, smul_zero, sum_const_zero,
      add_zero, cyc7_apply_of_fixed hcy', cyc7_apply_of_fixed hcz, smul_smul] at hΦ
    have hyz : g (Sum.inl 0) • y' + g (Sum.inl 1) • z = 0 := by
      have h1 : (7 : K) • (g (Sum.inl 0) • y' + g (Sum.inl 1) • z) = 0 := by
        rw [smul_add, smul_smul, smul_smul, mul_comm (7 : K), mul_comm (7 : K)]
        exact hΦ
      exact (smul_eq_zero.mp h1).resolve_left h7
    have hN := congrArg N hyz
    simp only [map_add, map_smul, hNz, smul_zero, add_zero, map_zero] at hN
    have hg0 : g (Sum.inl 0) = 0 := (smul_eq_zero.mp hN).resolve_right hz
    rw [hg0, zero_smul, zero_add] at hyz
    have hg1 : g (Sum.inl 1) = 0 := (smul_eq_zero.mp hyz).resolve_right hz
    rw [hg0, hg1, zero_smul, zero_smul, zero_add, zero_add] at hg
    have h2 := eq_zero_of_sum_pow_apply hirr hv₀ hv₀0 hg
    rintro (i | i)
    · fin_cases i
      · exact hg0
      · exact hg1
    · simpa using congrFun h2 i
  have := hli.fintype_card_le_finrank
  simp only [Fintype.card_sum, Fintype.card_fin] at this
  omega

theorem eq_zero_of_commute_cyc7_seven (hV : Module.finrank K V ≤ 7) (h7 : (7 : K) ≠ 0)
    (hirr : Irreducible (cyclotomic 7 K)) {c N : Module.End K V} (hc7 : c ^ 7 = 1)
    (hc1 : c ≠ 1) (hNc : N * c = c * N) (hN3 : N ^ 3 = 0) : N = 0 := by
  obtain ⟨x₀, hx₀⟩ : ∃ x₀, c x₀ ≠ x₀ := by
    by_contra h
    push Not at h
    exact hc1 (LinearMap.ext fun x => by rw [h x, Module.End.one_apply])
  set v₀ := c x₀ - x₀
  have hv₀0 : v₀ ≠ 0 := sub_ne_zero.mpr hx₀
  have hcyc : cyc7 c * (c - 1) = 0 := by rw [cyc7_mul_sub_one, hc7, sub_self]
  have hv₀ : (cyc7 c) v₀ = 0 := by
    have h1 : (cyc7 c * (c - 1)) x₀ = 0 := by rw [hcyc, LinearMap.zero_apply]
    rwa [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at h1
  have hfix : ∀ x, c ((cyc7 c) x) = (cyc7 c) x := by
    intro x
    have h1 : ((c - 1) * cyc7 c) x = 0 := by
      rw [sub_one_mul_cyc7, hc7, sub_self, LinearMap.zero_apply]
    rw [Module.End.mul_apply, LinearMap.sub_apply, Module.End.one_apply] at h1
    exact sub_eq_zero.mp h1
  refine LinearMap.ext fun x => ?_
  rw [LinearMap.zero_apply]
  have hdecomp : x = (7 : K)⁻¹ • (cyc7 c) x + (x - (7 : K)⁻¹ • (cyc7 c) x) := by abel
  have hker : (cyc7 c) (x - (7 : K)⁻¹ • (cyc7 c) x) = 0 := by
    rw [map_sub, map_smul, cyc7_apply_of_fixed (hfix x), smul_smul, inv_mul_cancel₀ h7, one_smul,
      sub_self]
  rw [hdecomp, map_add, map_smul,
    apply_eq_zero_of_fixed_seven hV h7 hirr hNc hN3 hv₀ hv₀0 (hfix x),
    apply_eq_zero_of_cyc7_seven (hV.trans (by norm_num)) hirr hNc hN3 hker, smul_zero, add_zero]

end Seven

theorem irreducible_cyclotomic_seven_zmod_three : Irreducible (cyclotomic 7 (ZMod 3)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  refine ZMod.irreducible_of_dvd_cyclotomic_of_natDegree (p := 3) (n := 7) (by norm_num) dvd_rfl
    ?_
  rw [natDegree_cyclotomic, Nat.totient_prime (by norm_num), ← orderOf_units,
    ZMod.coe_unitOfCoprime, eq_comm, orderOf_eq_iff (show 0 < 7 - 1 by norm_num)]
  exact ⟨by decide, by decide⟩

theorem pow_seven_or_pow_three_of_seven {K : Type*} [Field K] [CharP K 3]
    (hirr : Irreducible (cyclotomic 7 K)) {B : Matrix (Fin 7) (Fin 7) K} (h21 : B ^ 21 = 1) :
    B ^ 7 = 1 ∨ B ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have h7 : (7 : K) ≠ 0 := by
    intro h
    have h1 : ((7 : ℕ) : K) = 0 := by exact_mod_cast h
    rw [CharP.cast_eq_zero_iff K 3] at h1
    norm_num at h1
  by_contra hne
  push Not at hne
  obtain ⟨h7', h3'⟩ := hne
  have hc7 : (B ^ 3) ^ 7 = 1 := by rw [← pow_mul, h21]
  have hMc : B ^ 7 * B ^ 3 = B ^ 3 * B ^ 7 := by rw [← pow_add, ← pow_add, add_comm]
  have hN3 : (B ^ 7 - 1) ^ 3 = 0 := by
    rw [sub_pow_char_of_commute 3 (Commute.one_right (B ^ 7)), one_pow, ← pow_mul, h21,
      sub_self]
  have hNc : (B ^ 7 - 1) * B ^ 3 = B ^ 3 * (B ^ 7 - 1) := by
    rw [sub_mul, mul_sub, hMc, one_mul, mul_one]
  have h := eq_zero_of_commute_cyc7_seven (V := Fin 7 → K)
    (Module.finrank_fin_fun K).le h7 hirr
    (c := Matrix.toLinAlgEquiv' (B ^ 3)) (N := Matrix.toLinAlgEquiv' (B ^ 7 - 1))
    (by rw [← map_pow, hc7, map_one])
    (fun h => h3' (Matrix.toLinAlgEquiv'.injective (by rw [h, map_one])))
    (by rw [← map_mul, hNc, map_mul]) (by rw [← map_pow, hN3, map_zero])
  exact h7' (sub_eq_zero.mp (Matrix.toLinAlgEquiv'.injective (by rw [h, map_zero])))

open CFSG.LieType.Multipliers.G23 CFSG.Blueprint.Chevalley CFSG.Quasithin.G2U

def wIdx : Fin 7 → Fin 14 := ![2, 3, 4, 7, 9, 10, 11]

def inW : Fin 14 → Bool :=
  ![false, false, true, true, true, false, false, true, false, true, true, true, false, false]

theorem wIdx_injective : Function.Injective wIdx := by
  unfold wIdx
  decide

theorem inW_wIdx : ∀ l : Fin 7, inW (wIdx l) = true := by
  unfold wIdx inW
  decide

theorem mem_range_wIdx : ∀ k : Fin 14, inW k = true → ∃ l, wIdx l = k := by
  unfold wIdx inW
  decide

def PresW (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) : Prop :=
  ∀ a b, inW a = false → inW b = true → M a b = 0

def resW (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) : Matrix (Fin 7) (Fin 7) (ZMod 3) :=
  M.submatrix wIdx wIdx

theorem presW_one : PresW 1 := fun _ _ ha hb =>
  Matrix.one_apply_ne fun h => by
    subst h
    rw [ha] at hb
    exact Bool.false_ne_true hb

theorem PresW.mul {M N : Matrix (Fin 14) (Fin 14) (ZMod 3)} (hM : PresW M) (hN : PresW N) :
    PresW (M * N) := by
  intro a b ha hb
  rw [Matrix.mul_apply]
  refine Finset.sum_eq_zero fun k _ => ?_
  cases hk : inW k
  · rw [hN k b hk hb, mul_zero]
  · rw [hM a k ha hk, zero_mul]

theorem resW_mul (M : Matrix (Fin 14) (Fin 14) (ZMod 3)) {N : Matrix (Fin 14) (Fin 14) (ZMod 3)}
    (hN : PresW N) : resW (M * N) = resW M * resW N := by
  ext i j
  simp only [resW, Matrix.submatrix_apply, Matrix.mul_apply]
  symm
  refine Fintype.sum_of_injective wIdx wIdx_injective _ _ (fun k hk => ?_) fun l => rfl
  have hk' : inW k = false := by
    cases h : inW k
    · rfl
    · exact absurd (mem_range_wIdx k h) hk
  rw [hN k (wIdx j) hk' (inW_wIdx j), mul_zero]

theorem val_rootMat_eq_zero : ∀ (j : Fin 4) (a b : Fin 14), inW a = false → inW b = true →
    (rootMat j a b).val = 0 := by
  unfold inW
  decide +kernel

theorem presW_rootMat (j : Fin 4) : PresW (rootMat j) := fun a b ha hb =>
  (ZMod.val_eq_zero _).mp (val_rootMat_eq_zero j a b ha hb)

theorem resW_rootMat_zero_ne_one : resW (rootMat 0) ≠ 1 := by
  unfold resW wIdx
  decide +kernel

def stabW : Subgroup (GL (Fin 14) (ZMod 3)) where
  carrier := {A | PresW (A : Matrix (Fin 14) (Fin 14) (ZMod 3)) ∧
    PresW ((A⁻¹ : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3))}
  mul_mem' {A B} hA hB := by
    obtain ⟨hA1, hA2⟩ := hA
    obtain ⟨hB1, hB2⟩ := hB
    refine ⟨?_, ?_⟩
    · rw [Units.val_mul]
      exact hA1.mul hB1
    · rw [mul_inv_rev, Units.val_mul]
      exact hB2.mul hA2
  one_mem' := ⟨by rw [Units.val_one]; exact presW_one,
    by rw [inv_one, Units.val_one]; exact presW_one⟩
  inv_mem' {A} hA := by
    obtain ⟨hA1, hA2⟩ := hA
    exact ⟨hA2, by rw [inv_inv]; exact hA1⟩

theorem mem_stabW {A : GL (Fin 14) (ZMod 3)} :
    A ∈ stabW ↔ PresW (A : Matrix (Fin 14) (Fin 14) (ZMod 3)) ∧
      PresW ((A⁻¹ : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) :=
  Iff.rfl

theorem rootUnit_mem_stabW (j : Fin 4) : rootUnit j ∈ stabW :=
  mem_stabW.mpr ⟨presW_rootMat j, (presW_rootMat j).mul (presW_rootMat j)⟩

variable {K : Type} [Field K] (σ : K ≃+* ZMod 3)

theorem glHom_mem_stabW {g : ModGL .G2 K} (hg : g ∈ adjointGroup .G2 K) :
    glHom σ g ∈ stabW := by
  have hpow : ∀ (j : Fin 4) (n : ℕ) (g : ModGL .G2 K),
      ((glHom σ g : GL (Fin 14) (ZMod 3)) : Matrix (Fin 14) (Fin 14) (ZMod 3)) = rootMat j ^ n →
        glHom σ g ∈ stabW := fun j n g h => by
    have : glHom σ g = rootUnit j ^ n :=
      Units.ext (h.trans (Units.val_pow_eq_pow_val (rootUnit j) n).symm)
    rw [this]
    exact pow_mem (rootUnit_mem_stabW j) n
  refine (Subgroup.closure_le (K := stabW.comap (glHom σ))).mpr ?_ hg
  rintro g ⟨i, c, h | h⟩
  · exact hpow (xIdx i) (σ c).val g (by
      rw [glHom_apply, coe_glEquiv, h, endEquiv_xOp, (XMat_eq_rootMat_pow i (σ c)).1])
  · exact hpow (yIdx i) (σ c).val g (by
      rw [glHom_apply, coe_glEquiv, h, endEquiv_yOp, (XMat_eq_rootMat_pow i (σ c)).2])

theorem presW_glHom (g : adjointGroup .G2 K) :
    PresW ((glHom σ (g : ModGL .G2 K) : GL (Fin 14) (ZMod 3)) :
      Matrix (Fin 14) (Fin 14) (ZMod 3)) :=
  (mem_stabW.mp (glHom_mem_stabW σ g.2)).1

noncomputable def resHom : adjointGroup .G2 K →* Matrix (Fin 7) (Fin 7) (ZMod 3) where
  toFun g := resW ((glHom σ (g : ModGL .G2 K) : GL (Fin 14) (ZMod 3)) :
    Matrix (Fin 14) (Fin 14) (ZMod 3))
  map_one' := by
    change resW ((glHom σ (1 : ModGL .G2 K) : GL (Fin 14) (ZMod 3)) :
      Matrix (Fin 14) (Fin 14) (ZMod 3)) = 1
    rw [map_one, Units.val_one, resW, Matrix.submatrix_one _ wIdx_injective]
  map_mul' g h := by
    change resW ((glHom σ ((g : ModGL .G2 K) * h) : GL (Fin 14) (ZMod 3)) :
      Matrix (Fin 14) (Fin 14) (ZMod 3)) =
      resW ((glHom σ (g : ModGL .G2 K) : GL (Fin 14) (ZMod 3)) :
        Matrix (Fin 14) (Fin 14) (ZMod 3)) *
      resW ((glHom σ (h : ModGL .G2 K) : GL (Fin 14) (ZMod 3)) :
        Matrix (Fin 14) (Fin 14) (ZMod 3))
    rw [map_mul, Units.val_mul, resW_mul _ (presW_glHom σ h)]

noncomputable def xOne (σ : K ≃+* ZMod 3) : adjointGroup .G2 K :=
  ⟨(glEquiv σ).symm (rootUnit 0), glEquiv_symm_rootUnit_mem σ 0⟩

theorem resHom_xOne_ne_one : resHom σ (xOne σ) ≠ 1 := by
  change resW ((glHom σ ((glEquiv σ).symm (rootUnit 0)) : GL (Fin 14) (ZMod 3)) :
    Matrix (Fin 14) (Fin 14) (ZMod 3)) ≠ 1
  rw [glHom_apply, MulEquiv.apply_symm_apply]
  exact resW_rootMat_zero_ne_one

end Item223CensusResProof

open Item223CensusResProof CFSG.LieType.Multipliers.G23 CFSG.Blueprint.Chevalley

theorem orderOf_ne_twentyOne_of_G2_three
    {X : Type} [Group X] (hX : Blueprint.ChevalleyExceptionalModel X .G2 3 1) (x : X) :
    orderOf x ≠ 21 := by
  have : IsSimpleGroup X := (CFSG.LieType.Simplicity.fam_g2_simplicity X 3 1 hX).2
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hX
  have : Fintype K := Fintype.ofFinite K
  let σ : K ≃+* ZMod 3 := FiniteField.ringEquivOfCardEq (by
    rw [ZMod.card, ← Nat.card_eq_fintype_card, hK, pow_one])
  have hZ : Subgroup.center (adjointGroup .G2 K) = ⊥ :=
    CFSG.LieType.Chevalley.center_adjointGroup_eq_bot
  let E : X ≃* adjointGroup .G2 K :=
    e.trans ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot)
  let ψ : X →* Matrix (Fin 7) (Fin 7) (ZMod 3) := (resHom σ).comp E.toMonoidHom
  have hker : ψ.ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ψ.ker with h | h
    · exact h
    · exfalso
      have hmem : E.symm (xOne σ) ∈ ψ.ker := by
        rw [h]
        exact Subgroup.mem_top _
      apply resHom_xOne_ne_one σ
      have h1 := MonoidHom.mem_ker.mp hmem
      simpa [ψ] using h1
  have hinj : Function.Injective ψ := (MonoidHom.ker_eq_bot_iff ψ).mp hker
  intro h21
  have hx21 : ψ x ^ 21 = 1 := by rw [← map_pow, ← h21, pow_orderOf_eq_one, map_one]
  rcases pow_seven_or_pow_three_of_seven irreducible_cyclotomic_seven_zmod_three hx21 with h | h
  · have h7 : x ^ 7 = 1 := hinj (by rw [map_pow, h, map_one])
    have := orderOf_dvd_of_pow_eq_one h7
    rw [h21] at this
    norm_num at this
  · have h3 : x ^ 3 = 1 := hinj (by rw [map_pow, h, map_one])
    have := orderOf_dvd_of_pow_eq_one h3
    rw [h21] at this
    norm_num at this

end CFSG.RankThree.PartTwo.Sec21

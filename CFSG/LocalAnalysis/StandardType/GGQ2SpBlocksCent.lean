module

public import CFSG.LocalAnalysis.StandardType.GGQ2SpBlocksIdem
public import CFSG.LocalAnalysis.StandardType.GGTorCPlane

public section

namespace CFSG.StandardType.GGQ2Frame.SpBlocks

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.SpJoin
  CFSG.StandardType.ClassicalPosition CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl
  Matrix
open CFSG.Open (StatedSp)
open scoped commutatorElement

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K]

theorem coe_lam_eq_planeMat {m : ℕ} (i : Fin m) (a : SpecialLinearGroup (Fin 2) K) :
    (((lam i a : StatedSp m K) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) =
      WitSpNs.planeMat fun j => if j = i then (a : Matrix (Fin 2) (Fin 2) K) else 1 := by
  rw [coe_lam]
  ext x y
  rw [WitSpNs.planeMat_apply]
  rcases x with j | j <;> rcases y with k | k <;>
    by_cases hj : j = i <;> by_cases hk : k = i <;> by_cases hjk : j = k <;>
    simp_all [pairMat, Matrix.one_apply, WitSpNs.plane, WitSpNs.side]

theorem mem_levi_of_col {m : ℕ} {S : Finset (Fin m)} {g : ↥(StatedSp m K)}
    (h : ∀ x y : Fin m ⊕ Fin m, Sum.elim id id y ∉ S →
      ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y =
        (1 : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) x y) :
    g ∈ levi m S := by
  change ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) *
    (1 - planeIdem m S) = 1 - planeIdem m S
  rw [← planeIdem_compl]
  ext x y
  rw [planeIdem, Matrix.mul_diagonal, Matrix.diagonal_apply]
  by_cases hy : Sum.elim id id y ∈ Sᶜ
  · rw [if_pos hy, mul_one, h x y (Finset.mem_compl.mp hy), Matrix.one_apply]
    by_cases hxy : x = y
    · subst hxy
      simp [hy]
    · simp [hxy]
  · rw [if_neg hy, mul_zero]
    by_cases hxy : x = y
    · subst hxy
      simp [hy]
    · simp [hxy]

theorem lam_mem_levi {m : ℕ} {S : Finset (Fin m)} {i : Fin m} (hi : i ∈ S)
    (a : SpecialLinearGroup (Fin 2) K) : lam i a ∈ levi m S := by
  refine mem_levi_of_col fun x y hy => ?_
  have hyi : y ≠ Sum.inl i := by
    rintro rfl
    exact hy hi
  have hyi' : y ≠ Sum.inr i := by
    rintro rfl
    exact hy hi
  rw [coe_lam, pairMat_apply_of_ne' hyi hyi']

theorem rho_mem_levi {m : ℕ} {S : Finset (Fin m)} {i j : Fin m} (hi : i ∈ S) (hj : j ∈ S)
    (hij : i ≠ j) (a : SpecialLinearGroup (Fin 2) K) : rho i j hij a ∈ levi m S := by
  refine mem_levi_of_col fun x y hy => ?_
  rw [coe_rho]
  rcases y with k | k
  · have hki : k ≠ i := fun h => hy (h ▸ hi)
    have hkj : k ≠ j := fun h => hy (h ▸ hj)
    rcases x with l | l
    · rw [fromBlocks_apply₁₁, pairMat_apply_of_ne' hki hkj, Matrix.one_apply, Matrix.one_apply]
      simp
    · rw [fromBlocks_apply₂₁, Matrix.one_apply]
      simp
  · have hki : k ≠ i := fun h => hy (h ▸ hi)
    have hkj : k ≠ j := fun h => hy (h ▸ hj)
    rcases x with l | l
    · rw [fromBlocks_apply₁₂, Matrix.one_apply]
      simp
    · rw [fromBlocks_apply₂₂, Matrix.transpose_apply, pairMat_apply_of_ne hki hkj,
        Matrix.one_apply, Matrix.one_apply]
      simp [eq_comm]

theorem planeIdem_mul_J (m : ℕ) (S : Finset (Fin m)) :
    (planeIdem m S : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * Matrix.J (Fin m) K =
      Matrix.J (Fin m) K * planeIdem m S := by
  ext a b
  simp only [planeIdem, Matrix.diagonal_mul, Matrix.mul_diagonal]
  rcases a with i | i <;> rcases b with j | j <;> by_cases hij : i = j <;>
    simp [Matrix.J, hij] <;> rfl

theorem commute_planeIdem_of_mem_levi {m : ℕ} {S : Finset (Fin m)} {g : ↥(StatedSp m K)}
    (hg : g ∈ levi m S) :
    ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) * planeIdem m S =
      planeIdem m S * ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) := by
  set A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) with hA
  set P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := planeIdem m S with hP
  set J : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := Matrix.J (Fin m) K with hJ
  have hQ : A * (1 - P) = 1 - P := hg
  have hsp : A.transpose * J * A = J := by
    have hmem : (g : GL (Fin m ⊕ Fin m) K) ∈ TauCeti.GLSymplectic (Fin m) K := by
      rw [← CFSG.ClassicalGroups.Symplectic.statedSp_eq_GLSymplectic]
      exact g.2
    exact SymplecticGroup.mem_iff'.mp (TauCeti.GLSymplectic.mem_iff_mem_symplecticGroup.mp hmem)
  have hPt : P.transpose = P := Matrix.diagonal_transpose _
  have hPP : P * P = P := isIdempotentElem_planeIdem m S
  have hQt : (1 - P) * A.transpose = 1 - P := by
    have h := congrArg Matrix.transpose hQ
    rwa [Matrix.transpose_mul, Matrix.transpose_sub, Matrix.transpose_one, hPt] at h
  have hQJ : (1 - P) * J = J * (1 - P) := by
    rw [sub_mul, mul_sub, Matrix.one_mul, Matrix.mul_one, hP, hJ, planeIdem_mul_J]
  have hQP : (1 - P) * P = 0 := by rw [sub_mul, Matrix.one_mul, hPP, sub_self]
  have hPQ : P * (1 - P) = 0 := by rw [mul_sub, Matrix.mul_one, hPP, sub_self]
  have h1 : J * ((1 - P) * A * P) = 0 := by
    calc J * ((1 - P) * A * P) = (1 - P) * J * A * P := by
          rw [hQJ]; simp only [Matrix.mul_assoc]
      _ = (1 - P) * A.transpose * J * A * P := by rw [hQt]
      _ = (1 - P) * (A.transpose * J * A) * P := by simp only [Matrix.mul_assoc]
      _ = J * ((1 - P) * P) := by rw [hsp, hQJ, Matrix.mul_assoc]
      _ = 0 := by rw [hQP, Matrix.mul_zero]
  have h2 : (1 - P) * A * P = 0 := by
    have hJJ : J * J = -1 := Matrix.J_squared (Fin m) K
    calc (1 - P) * A * P = -(J * (J * ((1 - P) * A * P))) := by
          rw [← Matrix.mul_assoc, hJJ, neg_one_mul, neg_neg]
      _ = 0 := by rw [h1, Matrix.mul_zero, neg_zero]
  calc A * P = (P + (1 - P)) * A * P := by rw [add_sub_cancel, Matrix.one_mul]
    _ = P * A * P + (1 - P) * A * P := by rw [add_mul, add_mul]
    _ = P * A * P := by rw [h2, add_zero]
    _ = P * A * P + P * (A * (1 - P)) := by rw [hQ, hPQ, add_zero]
    _ = P * A * (P + (1 - P)) := by rw [mul_add, Matrix.mul_assoc P A (1 - P)]
    _ = P * A := by rw [add_sub_cancel, Matrix.mul_one]

theorem ycode_le_blockGroup {m : ℕ} (ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K)
    (c : PlaneRaw.Code m) : Ycode ζ m c ≤ blockGroup ζ m c := by
  refine Subgroup.commutator_le.mpr fun a ha b hb => ?_
  rw [commutatorElement_def]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ ha hb)
    (Subgroup.inv_mem _ ha)) (Subgroup.inv_mem _ hb)

theorem eq_zero_of_tau_mem_levi [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {S : Finset (Fin m)} {u : PlaneRaw.V m} (h : tau ζ m u ∈ levi m S) :
    ∀ i, i ∉ S → u i = 0 := by
  intro i hi
  by_contra hui
  set T : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    (((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) with hT
  have hTQ : T * (1 - planeIdem m S) = 1 - planeIdem m S := h
  have h2 : (T * T + T) * (1 - planeIdem m S) = 0 := by
    rw [add_mul, Matrix.mul_assoc, hTQ, hTQ, add_self_eq_zero_of_charTwo]
  rw [hT, tau_mul_self_add hK hζ u, ← planeIdem_compl, ← planeIdem_inter] at h2
  exact planeIdem_ne_zero ⟨i, Finset.mem_inter.mpr
    ⟨Finset.mem_filter.mpr ⟨Finset.mem_univ _, hui⟩, Finset.mem_compl.mpr hi⟩⟩ h2

theorem sl2W_conj_eq_inv [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {h : SpecialLinearGroup (Fin 2) K} (h3 : h ^ 3 = 1) (h1 : h ≠ 1) :
    sl2W * h * sl2W⁻¹ = h⁻¹ := by
  have hsq := mul_self_add_self_eq_one hK h3 h1
  set A : Matrix (Fin 2) (Fin 2) K := (h : Matrix (Fin 2) (Fin 2) K) with hA
  have hxx : ∀ x : K, x * x = x := fun x => by
    rcases eq_zero_or_eq_one hK x with hx | hx <;> rw [hx] <;> simp
  have h00 : A 0 0 * A 0 0 + A 0 1 * A 1 0 + A 0 0 = 1 := by
    have := congrFun (congrFun hsq 0) 0
    simpa [Matrix.mul_apply, Fin.sum_univ_two] using this
  have hbc : A 0 1 * A 1 0 = 1 := by
    rw [hxx, add_comm (A 0 0) _, add_assoc, CharTwo.add_self_eq_zero, add_zero] at h00
    exact h00
  have hb : A 0 1 = 1 := (eq_zero_or_eq_one hK _).resolve_left fun h0 => by
    rw [h0, zero_mul] at hbc
    exact zero_ne_one hbc
  have hc : A 1 0 = 1 := (eq_zero_or_eq_one hK _).resolve_left fun h0 => by
    rw [h0, mul_zero] at hbc
    exact zero_ne_one hbc
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_sl2W, coe_sl2W_inv,
    Matrix.SpecialLinearGroup.coe_inv, ← hA, Matrix.adjugate_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, hb, hc,
      CharTwo.neg_eq]

theorem zeta_pow_three {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (a : ZMod 3) : ζ (Multiplicative.ofAdd a) ^ 3 = 1 := by
  rw [← map_pow, ← ofAdd_nsmul]
  have h3 : (3 : ℕ) • a = 0 := by revert a; decide
  rw [h3, ofAdd_zero, map_one]

theorem zeta_ne_one {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    (hζ : Function.Injective ζ) {a : ZMod 3} (ha : a ≠ 0) : ζ (Multiplicative.ofAdd a) ≠ 1 := by
  intro h
  apply ha
  have := hζ (h.trans (map_one ζ).symm)
  simpa using this

theorem zeta_eq_commutator [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {a : ZMod 3} (ha : a ≠ 0) :
    ζ (Multiplicative.ofAdd a) =
      ⁅(sl2W : SpecialLinearGroup (Fin 2) K), ζ (Multiplicative.ofAdd a)⁆ := by
  have h3 := zeta_pow_three (ζ := ζ) a
  rw [commutatorElement_def, sl2W_conj_eq_inv hK h3 (zeta_ne_one hζ ha)]
  calc ζ (Multiplicative.ofAdd a)
      = (ζ (Multiplicative.ofAdd a))⁻¹ * (ζ (Multiplicative.ofAdd a))⁻¹ *
          ζ (Multiplicative.ofAdd a) ^ 3 := by group
    _ = (ζ (Multiplicative.ofAdd a))⁻¹ * (ζ (Multiplicative.ofAdd a))⁻¹ := by
        rw [h3, mul_one]

theorem lam_zeta_mem_ycode [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {S : Finset (Fin m)} {i : Fin m} (hi : i ∈ S) (a : ZMod 3) :
    lam i (ζ (Multiplicative.ofAdd a)) ∈ Ycode ζ m (.zero S) := by
  by_cases ha : a = 0
  · rw [ha, ofAdd_zero, map_one, map_one]
    exact Subgroup.one_mem _
  · rw [zeta_eq_commutator hK hζ ha, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (lam_mem_levi hi _) (lam_mem_levi hi _)

theorem tau_mem_ycode_zero [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {S : Finset (Fin m)} {u : PlaneRaw.V m} (hu : ∀ i, i ∉ S → u i = 0) :
    tau ζ m u ∈ Ycode ζ m (.zero S) := by
  have key : (fun i => Multiplicative.ofAdd (u i)) ∈
      (Ycode ζ m (.zero S)).comap (spPlaneTorus m ζ) := by
    rw [← Finset.univ_prod_mulSingle (fun i => Multiplicative.ofAdd (u i))]
    refine Subgroup.prod_mem _ fun i _ => ?_
    rw [Subgroup.mem_comap, spPlaneTorus_mulSingle]
    by_cases hi : i ∈ S
    · exact lam_zeta_mem_ycode hK hζ hi (u i)
    · rw [hu i hi, ofAdd_zero, map_one, map_one]
      exact Subgroup.one_mem _
  exact key

theorem tau_mem_ycode_zero_iff [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} (S : Finset (Fin m)) (u : PlaneRaw.V m) :
    tau ζ m u ∈ Ycode ζ m (.zero S) ↔ u ∈ PlaneRaw.inside .symplectic (.zero S) := by
  change _ ↔ u ∈ PlaneRaw.insideZero S
  rw [PlaneRaw.mem_insideZero']
  exact ⟨fun h => eq_zero_of_tau_mem_levi hK hζ (ycode_le_blockGroup ζ (.zero S) h),
    tau_mem_ycode_zero hK hζ⟩

theorem commute_tau_of_mem_levi {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K}
    {m : ℕ} {S : Finset (Fin m)} {u : PlaneRaw.V m} (hu : ∀ i ∈ S, u i = 0)
    {g : ↥(StatedSp m K)} (hg : g ∈ levi m S) : tau ζ m u * g = g * tau ζ m u := by
  set A : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    ((g : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) with hA
  set T : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K :=
    (((tau ζ m u : ↥(StatedSp m K)) : GL (Fin m ⊕ Fin m) K) :
      Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K) with hT
  set P : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K := planeIdem m S with hP
  have hAQ : A * (1 - P) = 1 - P := hg
  have hAP : A * P = P * A := commute_planeIdem_of_mem_levi hg
  have hTP : T * P = P := by
    rw [hT, hP, coe_tau, planeIdem_eq_planeMat, WitSpNs.planeMat_mul]
    congr 1
    funext j
    by_cases hj : j ∈ S
    · rw [if_pos hj, hu j hj, ofAdd_zero, map_one, Matrix.SpecialLinearGroup.coe_one,
        Matrix.mul_one]
    · rw [if_neg hj, Matrix.mul_zero]
  have hPT : P * T = P := by
    rw [hT, hP, coe_tau, planeIdem_eq_planeMat, WitSpNs.planeMat_mul]
    congr 1
    funext j
    by_cases hj : j ∈ S
    · rw [if_pos hj, hu j hj, ofAdd_zero, map_one, Matrix.SpecialLinearGroup.coe_one,
        Matrix.mul_one]
    · rw [if_neg hj, Matrix.zero_mul]
  have hTQ : T * (1 - P) = (1 - P) * T := by
    rw [mul_sub, sub_mul, Matrix.mul_one, Matrix.one_mul, hTP, hPT]
  have hAT : A * T = A * P + (1 - P) * T := by
    calc A * T = A * ((P + (1 - P)) * T) := by rw [add_sub_cancel, Matrix.one_mul]
      _ = A * (P * T) + A * (1 - P) * T := by rw [add_mul, mul_add, Matrix.mul_assoc]
      _ = A * P + (1 - P) * T := by rw [hPT, hAQ]
  have hTA : T * A = A * P + (1 - P) * T := by
    calc T * A = T * (A * (P + (1 - P))) := by rw [add_sub_cancel, Matrix.mul_one]
      _ = T * (A * P) + T * (A * (1 - P)) := by rw [mul_add, mul_add]
      _ = T * P * A + T * (1 - P) := by rw [hAP, hAQ, Matrix.mul_assoc]
      _ = A * P + (1 - P) * T := by rw [hTP, ← hAP, hTQ]
  exact statedSp_ext (by rw [coe_mul_statedSp, coe_mul_statedSp, ← hA, ← hT, hTA, hAT])

theorem exists_mem_ycode_not_commute [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {S : Finset (Fin m)} {i j : Fin m} (hi : i ∈ S) (hj : j ∈ S) (hij : i ≠ j)
    {u : PlaneRaw.V m} (hui : u i ≠ 0) :
    ∃ g ∈ Ycode ζ m (.zero S), tau ζ m u * g ≠ g * tau ζ m u := by
  have hw : ∃ w : SpecialLinearGroup (Fin 2) K, w = sl2W := ⟨_, rfl⟩
  obtain ⟨w, hw⟩ := hw
  refine ⟨⁅rho i j hij w, lam i w⁆, Subgroup.commutator_mem_commutator
    (rho_mem_levi hi hj hij _) (lam_mem_levi hi _), ?_⟩
  have hconj : rho i j hij w * lam i w * (rho i j hij w)⁻¹ = lam j w := by
    have h := congrArg (fun φ => φ w) (conj_rho_sl2W_comp_lam_fst (k := K) hij)
    rw [hw]
    simpa only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hw] using h
  rw [commutatorElement_def, hconj, ← map_inv]
  intro hcomm
  have hmat := congrArg (fun x : ↥(StatedSp m K) =>
    ((x : GL (Fin m ⊕ Fin m) K) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) K)) hcomm
  simp only [coe_mul_statedSp, coe_tau, coe_lam_eq_planeMat, WitSpNs.planeMat_mul] at hmat
  have hi' := congrFun (WitSpNs.planeMat_injective hmat) i
  simp only [if_neg hij, if_true, Matrix.one_mul] at hi'
  have hcomm' : w * ζ (Multiplicative.ofAdd (u i)) * w⁻¹ = ζ (Multiplicative.ofAdd (u i)) := by
    have hc : ζ (Multiplicative.ofAdd (u i)) * w⁻¹ = w⁻¹ * ζ (Multiplicative.ofAdd (u i)) :=
      Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul]
        exact hi')
    rw [mul_assoc, hc, ← mul_assoc, mul_inv_cancel, one_mul]
  rw [hw, sl2W_conj_eq_inv hK (zeta_pow_three (u i)) (zeta_ne_one hζ hui)] at hcomm'
  have h2 : ζ (Multiplicative.ofAdd (u i + u i)) = 1 := by
    rw [ofAdd_add, map_mul]
    nth_rewrite 1 [← hcomm']
    exact inv_mul_cancel _
  have hne : u i + u i ≠ 0 := by
    revert hui
    generalize u i = a
    revert a
    decide
  exact zeta_ne_one hζ hne h2

theorem tau_commute_ycode_zero_iff [Finite K] [CharP K 2] (hK : Nat.card K = 2)
    {ζ : Multiplicative (ZMod 3) →* SpecialLinearGroup (Fin 2) K} (hζ : Function.Injective ζ)
    {m : ℕ} {S : Finset (Fin m)} (hS : 2 ≤ S.card) (u : PlaneRaw.V m) :
    (∀ g ∈ Ycode ζ m (.zero S), tau ζ m u * g = g * tau ζ m u) ↔
      u ∈ PlaneRaw.cent .symplectic (.zero S) := by
  rw [PlaneRaw.mem_cent_zero]
  constructor
  · intro h i hi
    by_contra hui
    obtain ⟨j, hj, hji⟩ := Finset.exists_mem_ne (lt_of_lt_of_le one_lt_two hS) i
    obtain ⟨g, hg, hne⟩ := exists_mem_ycode_not_commute hK hζ hi hj (Ne.symm hji) hui
    exact hne (h g hg)
  · intro hu g hg
    exact commute_tau_of_mem_levi hu (ycode_le_blockGroup ζ (.zero S) hg)

end CFSG.StandardType.GGQ2Frame.SpBlocks

end

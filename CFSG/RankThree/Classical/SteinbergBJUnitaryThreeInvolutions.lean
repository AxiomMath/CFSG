module

public import CFSG.ClassicalGroups.UnitaryFlag.GroupData
public import CFSG.ClassicalGroups.Unitary.Finite
public import CFSG.LinearAlgebra.LinearGroups.UnitaryOrder
public import CFSG.LocalAnalysis.SectionRank.OddCover.CoverTools

public section

namespace CFSG.RankThree.Classical

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups
  CFSG.Assembly.LowTwoRank

variable {p f : ℕ} {K : Type} [Field K]

variable (K) in
@[expose] def negNegOneDiag : Matrix (Fin 3) (Fin 3) K :=
  diagonal ![-1, -1, 1]

theorem negNegOneDiag_mul_self : negNegOneDiag K * negNegOneDiag K = 1 := by
  rw [negNegOneDiag, diagonal_mul_diagonal, ← diagonal_one]
  congr 1
  funext i
  fin_cases i <;> simp

variable (K) in
@[expose] def negNegOneGL : GL (Fin 3) K :=
  ⟨negNegOneDiag K, negNegOneDiag K, negNegOneDiag_mul_self, negNegOneDiag_mul_self⟩

theorem coe_negNegOneGL : (negNegOneGL K : Matrix (Fin 3) (Fin 3) K) = negNegOneDiag K :=
  rfl

theorem negNegOneGL_mem_unitarySU (h : UnitaryFieldData p f K) :
    negNegOneGL K ∈ unitarySU p f K 3 := by
  rw [mem_unitarySU_iff h, coe_negNegOneGL, negNegOneDiag]
  refine ⟨?_, ?_⟩
  · rw [det_diagonal, Fin.prod_univ_three]
    simp
  · rw [diagonal_map (map_zero h.bar), diagonal_transpose, diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i <;> simp

@[expose] def unitaryInvT (h : UnitaryFieldData p f K) : unitarySU p f K 3 :=
  ⟨negNegOneGL K, negNegOneGL_mem_unitarySU h⟩

theorem coe_unitaryInvT (h : UnitaryFieldData p f K) :
    ((unitaryInvT h : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = negNegOneDiag K :=
  rfl

theorem unitaryInvT_sq (h : UnitaryFieldData p f K) : unitaryInvT h ^ 2 = 1 := by
  apply Subtype.ext
  apply Units.ext
  rw [SubmonoidClass.coe_pow, Units.val_pow_eq_pow_val, sq, coe_unitaryInvT,
    negNegOneDiag_mul_self, OneMemClass.coe_one, Units.val_one]

theorem isConj_unitaryInvT_of_orthonormal (h : UnitaryFieldData p f K) {g : unitarySU p f K 3}
    {v₀ v₁ w : Fin 3 → K}
    (hB : ∀ i j, stdHermForm h 3 (![v₀, v₁, w] i) (![v₀, v₁, w] j) = if i = j then 1 else 0)
    (hg : ∀ i, ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *ᵥ ![v₀, v₁, w] i =
      (![-1, -1, 1] : Fin 3 → K) i • ![v₀, v₁, w] i) :
    IsConj (unitaryInvT h) g := by
  set A : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hA
  set u : Matrix (Fin 3) (Fin 3) K := Matrix.of fun i j => ![v₀, v₁, w] j i with hu
  have hu1 : (u.map h.bar)ᵀ * u = 1 := by
    ext j k
    rw [Matrix.one_apply, ← hB j k, stdHermForm_apply, Matrix.mul_apply]
    rfl
  have hu2 : A * u = u * negNegOneDiag K := by
    ext i k
    rw [negNegOneDiag, mul_diagonal]
    change ∑ l, A i l * ![v₀, v₁, w] k l = ![v₀, v₁, w] k i * ![-1, -1, 1] k
    rw [mul_comm]
    exact congrFun (hg k) i
  set d := u.det with hd
  have hdd : h.bar d * d = 1 := by
    have := congrArg Matrix.det hu1
    rwa [det_mul, det_transpose, ← RingHom.mapMatrix_apply, ← RingHom.map_det, det_one] at this
  have hd0 : d ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hdd
    exact zero_ne_one hdd
  set D : Matrix (Fin 3) (Fin 3) K := diagonal ![d⁻¹, 1, 1] with hD
  set u' := u * D with hu'
  have hdet' : u'.det = 1 := by
    rw [hu', det_mul, hD, det_diagonal, Fin.prod_univ_three, ← hd]
    simp [hd0]
  have hu1' : (u'.map h.bar)ᵀ * u' = 1 := by
    rw [hu', Matrix.map_mul, transpose_mul, Matrix.mul_assoc, ← Matrix.mul_assoc _ u,
      hu1, Matrix.one_mul, hD, diagonal_map (map_zero h.bar), diagonal_transpose,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    fin_cases i
    · simp only [Fin.zero_eta, Matrix.cons_val_zero, map_inv₀]
      rw [← mul_inv, hdd, inv_one]
    · simp
    · simp
  have hu2' : A * u' = u' * negNegOneDiag K := by
    rw [hu', ← Matrix.mul_assoc, hu2, Matrix.mul_assoc, Matrix.mul_assoc]
    congr 1
    rw [hD, negNegOneDiag, diagonal_mul_diagonal, diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  set c : GL (Fin 3) K := GeneralLinearGroup.mkOfDetNeZero u' (by rw [hdet']; exact one_ne_zero)
    with hc
  have hcval : (c : Matrix (Fin 3) (Fin 3) K) = u' := rfl
  have hcmem : c ∈ unitarySU p f K 3 := by
    rw [mem_unitarySU_iff h, hcval]
    exact ⟨hdet', hu1'⟩
  rw [isConj_iff]
  refine ⟨⟨c, hcmem⟩, ?_⟩
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  apply Units.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul, Units.val_mul, coe_unitaryInvT]
  exact hu2'.symm

theorem isConj_unitaryInvT_of_orderOf (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    {g : unitarySU p f K 3} (hg : orderOf g = 2) : IsConj (unitaryInvT h) g := by
  classical
  have : CharP K p := h.charP
  have := h.finite
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp)
  have hneg1 : (-1 : K) ≠ 1 := fun h1 => h2 (by linear_combination -h1)
  set A : Matrix (Fin 3) (Fin 3) K := ((g : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hA
  set a := Matrix.toLin' A with ha
  set B := stdHermForm h 3 with hB
  have hg2 : g * g = 1 := by rw [← sq, ← hg, pow_orderOf_eq_one]
  have hAA : A * A = 1 := by
    have := congrArg (fun x : unitarySU p f K 3 => ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K))
      hg2
    simpa using this
  have haa : ∀ y, a (a y) = y := fun y => by
    rw [ha, Matrix.toLin'_apply, Matrix.toLin'_apply, Matrix.mulVec_mulVec, hAA,
      Matrix.one_mulVec]
  have hiso : ∀ x y, B (a x) (a y) = B x y := fun x y => by
    rw [ha, Matrix.toLin'_apply, Matrix.toLin'_apply]
    exact ((mem_unitarySU_iff_isometry h).mp g.2).2 x y
  have hdet : LinearMap.det a = 1 := by
    rw [ha, LinearMap.det_toLin']
    exact ((mem_unitarySU_iff h).mp g.2).1
  have hne : ∃ y, a y ≠ y := by
    by_contra hcon
    push Not at hcon
    have hg1 : g = 1 := by
      apply Subtype.ext
      apply Units.ext
      apply Matrix.toLin'.injective
      refine LinearMap.ext fun y => ?_
      change a y = _
      rw [hcon y, OneMemClass.coe_one, Units.val_one, Matrix.toLin'_one, LinearMap.id_apply]
    rw [hg1, orderOf_one] at hg
    exact absurd hg (by norm_num)
  set Vp : Submodule K (Fin 3 → K) := LinearMap.ker (a - LinearMap.id) with hVp
  set Vm : Submodule K (Fin 3 → K) := LinearMap.ker (a + LinearMap.id) with hVm
  have hmemVp : ∀ y, y ∈ Vp ↔ a y = y := fun y => by
    rw [hVp, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
  have hmemVm : ∀ y, y ∈ Vm ↔ a y = -y := fun y => by
    rw [hVm, LinearMap.mem_ker, LinearMap.add_apply, LinearMap.id_apply, add_eq_zero_iff_eq_neg]
  have hyp : ∀ y, (2 : K)⁻¹ • (y + a y) ∈ Vp := fun y => by
    rw [hmemVp, map_smul, map_add, haa, add_comm]
  have hym : ∀ y, (2 : K)⁻¹ • (y - a y) ∈ Vm := fun y => by
    rw [hmemVm, map_smul, map_sub, haa, ← smul_neg, neg_sub]
  have hsum : ∀ y, y = (2 : K)⁻¹ • (y + a y) + (2 : K)⁻¹ • (y - a y) := fun y => by
    rw [← smul_add, show y + a y + (y - a y) = (2 : K) • y by rw [two_smul]; abel, smul_smul,
      inv_mul_cancel₀ h2, one_smul]
  have horth : ∀ u ∈ Vp, ∀ w ∈ Vm, B u w = 0 := by
    intro u hu w hw
    have h1 := hiso u w
    rw [(hmemVp u).mp hu, (hmemVm w).mp hw, map_neg] at h1
    have h3 : (2 : K) * B u w = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  have horth' : ∀ u ∈ Vp, ∀ w ∈ Vm, B w u = 0 := by
    intro u hu w hw
    have h1 := hiso w u
    rw [(hmemVp u).mp hu, (hmemVm w).mp hw, map_neg, LinearMap.neg_apply] at h1
    have h3 : (2 : K) * B w u = 0 := by linear_combination -h1
    exact (mul_eq_zero.mp h3).resolve_left h2
  have hinf : Vp ⊓ Vm = ⊥ := by
    rw [eq_bot_iff]
    intro y hy
    have h1 := (hmemVp y).mp hy.1
    have h3 := (hmemVm y).mp hy.2
    rw [Submodule.mem_bot]
    have h4 : (2 : K) • y = 0 := by rw [two_smul]; nth_rewrite 1 [← h1]; rw [h3, neg_add_cancel]
    exact (smul_eq_zero.mp h4).resolve_left h2
  have hsup : Vp ⊔ Vm = ⊤ := by
    rw [eq_top_iff]
    intro y _
    rw [hsum y]
    exact Submodule.add_mem_sup (hyp y) (hym y)
  have hcompl : IsCompl Vp Vm := ⟨disjoint_iff.mpr hinf, codisjoint_iff.mpr hsup⟩
  have hdim : Module.finrank K Vp + Module.finrank K Vm = 3 := by
    rw [Submodule.finrank_add_eq_of_isCompl hcompl, Module.finrank_fin_fun]
  set e := Submodule.prodEquivOfIsCompl Vp Vm hcompl with he
  have hconj : a = (e : (Vp × Vm) →ₗ[K] (Fin 3 → K)) ∘ₗ
      LinearMap.prodMap LinearMap.id (-LinearMap.id) ∘ₗ
        (e.symm : (Fin 3 → K) →ₗ[K] (Vp × Vm)) := by
    refine LinearMap.ext fun x => ?_
    obtain ⟨y, rfl⟩ := e.surjective x
    rw [LinearMap.comp_apply, LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.coe_coe,
      LinearEquiv.symm_apply_apply, LinearMap.prodMap_apply, LinearMap.id_apply,
      LinearMap.neg_apply, LinearMap.id_apply, he, Submodule.coe_prodEquivOfIsCompl',
      Submodule.coe_prodEquivOfIsCompl', map_add, (hmemVp _).mp y.1.2, (hmemVm _).mp y.2.2]
    rfl
  have hdetm : LinearMap.det a = (-1) ^ Module.finrank K Vm := by
    rw [hconj, LinearMap.det_conj, LinearMap.det_prodMap, LinearMap.det_id, one_mul,
      ← neg_one_smul K (LinearMap.id : Vm →ₗ[K] Vm), LinearMap.det_smul, LinearMap.det_id,
      mul_one]
  have heven : Even (Module.finrank K Vm) := by
    rw [hdet] at hdetm
    exact (neg_one_pow_eq_one_iff_even hneg1).mp hdetm.symm
  have hVm0 : Module.finrank K Vm ≠ 0 := by
    intro h0
    obtain ⟨y, hy⟩ := hne
    have hm := hym y
    rw [Submodule.finrank_eq_zero.mp h0, Submodule.mem_bot] at hm
    have : y - a y = 0 := (smul_eq_zero.mp hm).resolve_left (inv_ne_zero h2)
    exact hy (sub_eq_zero.mp this).symm
  have hm2 : Module.finrank K Vm = 2 := by
    obtain ⟨k, hk⟩ := heven
    omega
  have hp1 : Module.finrank K Vp = 1 := by omega
  have hBs : B.IsSymm := stdHermForm_isSymm h 3
  have hBl : B.SeparatingLeft := stdHermForm_separatingLeft h 3
  have hsepP : (B.domRestrict₁₂ Vp Vp).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    rw [Submodule.coe_zero]
    refine hBl _ fun y => ?_
    rw [hsum y, map_add, horth _ x.2 _ (hym y), add_zero]
    exact hx ⟨_, hyp y⟩
  have hsepM : (B.domRestrict₁₂ Vm Vm).SeparatingLeft := by
    intro x hx
    apply Subtype.ext
    rw [Submodule.coe_zero]
    refine hBl _ fun y => ?_
    rw [hsum y, map_add, horth' _ (hyp y) _ x.2, zero_add]
    exact hx ⟨_, hym y⟩
  obtain ⟨ep, hep⟩ := h.exists_orthonormal_basis (hBs.domRestrict Vp) hsepP
  obtain ⟨em, hem⟩ := h.exists_orthonormal_basis (hBs.domRestrict Vm) hsepM
  set i₀ : Fin (Module.finrank K Vp) := ⟨0, by omega⟩ with hi₀
  set j₀ : Fin (Module.finrank K Vm) := ⟨0, by omega⟩ with hj₀
  set j₁ : Fin (Module.finrank K Vm) := ⟨1, by omega⟩ with hj₁
  have hj : j₀ ≠ j₁ := by
    rw [hj₀, hj₁, Ne, Fin.mk.injEq]
    exact zero_ne_one
  have hBp : B (ep i₀) (ep i₀) = 1 := by
    simpa [LinearMap.domRestrict₁₂_apply] using hep i₀ i₀
  have hBm : ∀ j j', B (em j) (em j') = if j = j' then 1 else 0 := hem
  refine isConj_unitaryInvT_of_orthonormal h (v₀ := em j₀) (v₁ := em j₁) (w := ep i₀)
    (fun i j => ?_) (fun i => ?_)
  · fin_cases i <;> fin_cases j
    · simpa using hBm j₀ j₀
    · simpa [hj] using hBm j₀ j₁
    · exact horth' _ (ep i₀).2 _ (em j₀).2
    · simpa [hj.symm] using hBm j₁ j₀
    · simpa using hBm j₁ j₁
    · exact horth' _ (ep i₀).2 _ (em j₁).2
    · exact horth _ (ep i₀).2 _ (em j₀).2
    · exact horth _ (ep i₀).2 _ (em j₁).2
    · simpa using hBp
  · rw [← Matrix.toLin'_apply, ← ha]
    fin_cases i
    · simpa using (hmemVm _).mp (em j₀).2
    · simpa using (hmemVm _).mp (em j₁).2
    · simpa using (hmemVp _).mp (ep i₀).2

theorem existsUnique_unitaryProj_lift (h : UnitaryFieldData p f K) {s : unitaryPSU h 3}
    (hs : orderOf s = 2) : ∃! g : unitarySU p f K 3, unitaryProj h 3 g = s ∧ orderOf g = 2 := by
  have := h.finite
  have hker : (unitaryProj h 3).ker = unitaryScalars h 3 := ker_unitaryProj h 3
  have hodd : Odd (Nat.card (unitaryProj h 3).ker) := by
    rw [hker, card_unitaryScalars h (by norm_num)]
    exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)
  have hC : (unitaryProj h 3).ker ≤ Subgroup.center _ := by
    rw [hker]
    exact unitaryScalars_le_center h 3
  have hs2 : s ^ 2 = 1 := by rw [← hs]; exact pow_orderOf_eq_one s
  have hs1 : s ≠ 1 := by
    rintro rfl
    rw [orderOf_one] at hs
    exact absurd hs (by norm_num)
  obtain ⟨g, ⟨hg2, hgs⟩, huniq⟩ := CFSG.SectionRank.OddCover.existsUnique_involution_lift
    (unitaryProj_surjective h 3) hC hodd hs2
  refine ⟨g, ⟨hgs, orderOf_eq_prime hg2 ?_⟩, fun g' hg' => huniq g' ⟨?_, hg'.1⟩⟩
  · rintro rfl
    rw [map_one] at hgs
    exact hs1 hgs.symm
  · rw [← hg'.2]
    exact pow_orderOf_eq_one g'

theorem orderOf_unitaryProj_unitaryInvT (h : UnitaryFieldData p f K) (hp : p ≠ 2) :
    orderOf (unitaryProj h 3 (unitaryInvT h)) = 2 := by
  have : CharP K p := h.charP
  have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [ringChar.eq K p]; exact hp)
  apply orderOf_eq_prime
  · rw [← map_pow, unitaryInvT_sq, map_one]
  · intro h1
    rw [← MonoidHom.mem_ker, ker_unitaryProj, mem_unitaryScalars] at h1
    obtain ⟨c, -, -, hc⟩ := h1
    have e0 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 0 0) hc
    have e2 := congrArg (fun M : GL (Fin 3) K => (M : Matrix (Fin 3) (Fin 3) K) 2 2) hc
    simp only [coe_unitaryInvT, negNegOneDiag, GeneralLinearGroup.coe_scalar, scalar_apply,
      diagonal_apply_eq] at e0 e2
    simp only [Matrix.cons_val_zero, Matrix.cons_val_two, Matrix.tail_cons,
      Matrix.head_cons] at e0 e2
    exact h2 (by linear_combination e2 - e0)

theorem isConj_unitaryProj_unitaryInvT (h : UnitaryFieldData p f K) (hp : p ≠ 2)
    {s : unitaryPSU h 3} (hs : orderOf s = 2) : IsConj s (unitaryProj h 3 (unitaryInvT h)) := by
  obtain ⟨g, ⟨rfl, hg⟩, -⟩ := existsUnique_unitaryProj_lift h hs
  exact MonoidHom.map_isConj (unitaryProj h 3) (isConj_unitaryInvT_of_orderOf h hp hg).symm

theorem unitary_three_five_model (B : Type) [Group B] (hB : StatedClassicalModel B .PSU 3 5 1) :
    Nat.card B = 126000 ∧ Group.IsPerfect B ∧ (∃ x : B, orderOf x = 2) ∧
      ∀ x y : B, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  obtain ⟨⟨hp, hf, -, -⟩, K, _, _, hK, ⟨e⟩⟩ := hB
  have hU : UnitaryFieldData 5 1 K := ⟨hp, hf, by rw [hK]; norm_num⟩
  have : Fact (Nat.Prime 5) := ⟨hp⟩
  have : CharP K 5 := hU.charP
  set φ : B ≃* unitaryPSU hU 3 := e.trans (unitaryPSUEquiv hU (by norm_num)).symm with hφ
  have hSint : (Nat.card (unitarySU 5 1 K 3) : ℤ) = ((5 ^ 1 : ℕ) : ℤ) ^ (3 * (3 - 1) / 2) *
      ∏ j ∈ Finset.Icc 2 3, (((5 ^ 1 : ℕ) : ℤ) ^ j - (-1) ^ j) := by
    have hBs := gramForm_isSymm hU (G := (1 : Matrix (Fin 3) (Fin 3) K)) (by
      rw [Matrix.map_one _ (map_zero hU.bar) (map_one hU.bar), transpose_one])
    have hBl := gramForm_separatingLeft hU (G := (1 : Matrix (Fin 3) (Fin 3) K)) (by simp)
    rw [unitarySU_eq_gramSU hU, card_gramSU]
    exact (unitary_full_group_order hU hBs hBl (Module.finrank_fin_fun K) (by norm_num)).2.1
  have hS : Nat.card (unitarySU 5 1 K 3) = 378000 := by
    have : (Nat.card (unitarySU 5 1 K 3) : ℤ) = 378000 := by
      rw [hSint]
      decide
    exact_mod_cast this
  have hZ : Nat.card (unitaryScalars hU 3) = 3 := by
    rw [card_unitaryScalars hU (by norm_num)]
    decide
  have hSZ : Nat.card (unitarySU 5 1 K 3) =
      Nat.card (unitaryPSU hU 3) * Nat.card (unitaryScalars hU 3) :=
    Subgroup.card_eq_card_quotient_mul_card_subgroup _
  rw [hS, hZ] at hSZ
  have hcard : Nat.card (unitaryPSU hU 3) = 126000 := by omega
  refine ⟨by rw [Nat.card_congr φ.toEquiv, hcard], ?_, ?_, ?_⟩
  ·
    have : Group.IsPerfect (StatedSU 3 (5 ^ 1) K) :=
      CFSG.ClassicalGroups.Unitary.isPerfect_statedSU hK (by norm_num) (by decide)
    exact Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  · refine ⟨φ.symm (unitaryProj hU 3 (unitaryInvT hU)), ?_⟩
    rw [MulEquiv.orderOf_eq, orderOf_unitaryProj_unitaryInvT hU (by norm_num)]
  · intro x y hx hy
    have hx' := isConj_unitaryProj_unitaryInvT hU (by norm_num)
      (show orderOf (φ x) = 2 by rw [MulEquiv.orderOf_eq, hx])
    have hy' := isConj_unitaryProj_unitaryInvT hU (by norm_num)
      (show orderOf (φ y) = 2 by rw [MulEquiv.orderOf_eq, hy])
    have hxy := MonoidHom.map_isConj φ.symm.toMonoidHom (hx'.trans hy'.symm)
    simpa using hxy

theorem odd_unitary_three_projective_involutions_single_class (h : UnitaryFieldData p f K)
    (hp : p ≠ 2) :
    unitaryScalars h 3 = (StatedScalars (Fin 3) K).subgroupOf (unitarySU p f K 3) ∧
    orderOf (unitaryProj h 3 (unitaryInvT h)) = 2 ∧
    (∀ s : unitaryPSU h 3, orderOf s = 2 → IsConj s (unitaryProj h 3 (unitaryInvT h))) ∧
    (∀ s : unitaryPSU h 3, orderOf s = 2 →
      ∃! g : unitarySU p f K 3, unitaryProj h 3 g = s ∧ orderOf g = 2) ∧
    (∀ g : unitarySU p f K 3, orderOf g = 2 → IsConj g (unitaryInvT h)) ∧
    Nat.card (unitaryScalars h 3) = Nat.gcd 3 (p ^ f + 1) ∧
    Odd (Nat.card (unitaryScalars h 3)) ∧
    ∀ (B : Type) [Group B], StatedClassicalModel B .PSU 3 5 1 →
      Nat.card B = 126000 ∧ Group.IsPerfect B ∧ (∃ x : B, orderOf x = 2) ∧
        ∀ x y : B, orderOf x = 2 → orderOf y = 2 → IsConj x y := by
  have hZ := card_unitaryScalars h (n := 3) (by norm_num)
  refine ⟨unitaryScalars_eq h (by norm_num), orderOf_unitaryProj_unitaryInvT h hp,
    fun s hs => isConj_unitaryProj_unitaryInvT h hp hs,
    fun s hs => existsUnique_unitaryProj_lift h hs,
    fun g hg => (isConj_unitaryInvT_of_orderOf h hp hg).symm, hZ, ?_,
    fun B _ hB => unitary_three_five_model B hB⟩
  rw [hZ]
  exact Odd.of_dvd_nat (by decide) (Nat.gcd_dvd_left 3 _)

end CFSG.RankThree.Classical

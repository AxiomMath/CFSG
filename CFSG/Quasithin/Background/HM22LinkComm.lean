module

public import CFSG.Quasithin.Background.HM22Link

public section

namespace CFSG.Quasithin.H.Mathieu.M22Link

open CFSG.Quasithin.H13 CFSG.Quasithin.H13.MatNCert Matrix

@[expose] def spanW : List (List ℕ) :=
  [[], [1], [0, 1], [1, 1], [1, 0, 1], [0, 1, 1], [0, 1, 0, 1], [1, 1, 0, 1], [1, 0, 1, 1],
    [1, 0, 1, 0, 1], [1, 1, 0, 1, 1], [1, 1, 0, 1, 0, 1]]

@[expose] def bC : List ℕ := [5, 80, 634, 1361, 3921, 1371, 3169, 1422, 1444, 2686, 2727, 1945]

@[expose] def bIC : List ℕ := [923, 1298, 922, 1338, 3093, 424, 3095, 163, 3179, 390, 4090, 414]

theorem basis_facts : validB 12 bC = true ∧ validB 12 bIC = true ∧ mulN bC bIC = oneN 12 ∧
    ∀ j < 12, mvN (H12Cert.tW (spanW.getD j [])) H12Cert.v0 = bC.getD j 0 := by
  decide +kernel

theorem validN_bC : ValidN 12 bC := validB_iff.mp basis_facts.1

theorem validN_bIC : ValidN 12 bIC := validB_iff.mp basis_facts.2.1

theorem eq_top_of_mul_eq_one {J : Submodule (ZMod 2) (Fin 12 → ZMod 2)}
    {B C : Matrix (Fin 12) (Fin 12) (ZMod 2)} (hBC : B * C = 1) (hB : ∀ j, (fun i => B i j) ∈ J) :
    J = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hv : v = B *ᵥ (C *ᵥ v) := by rw [mulVec_mulVec, hBC, one_mulVec]
  have hsum : B *ᵥ (C *ᵥ v) = ∑ j, (C *ᵥ v) j • (fun i => B i j) := by
    ext i
    simp only [mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, mul_comm]
  rw [hv, hsum]
  exact J.sum_mem fun j _ => J.smul_mem _ (hB j)

theorem eq_top_of_w0_mem {J : Submodule (ZMod 2) (Fin 12 → ZMod 2)}
    (hJ : ∀ g ∈ H12Cert.G, ∀ v ∈ J,
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v ∈ J)
    (h0 : H12Cert.w0 ∈ J) : J = ⊤ := by
  refine eq_top_of_mul_eq_one (B := decN 12 bC) (C := decN 12 bIC) ?_ fun j => ?_
  · rw [← decN_mulN validN_bC.1 validN_bIC.1, basis_facts.2.2.1, decN_oneN]
  · have h1 : (fun i => decN 12 bC i j) = vecN 12 (bC.getD j 0) := rfl
    rw [h1, ← basis_facts.2.2.2 j j.isLt, ← decN_mulVec (length_evalW _ _), ← H12Cert.tU_val]
    exact hJ _ (H12Cert.tU_mem _) _ h0

abbrev zM : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ((H12Cert.zU : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))

theorem eq_zero_of_mulVec_eq_zero {B : Matrix (Fin 12) (Fin 12) (ZMod 2)}
    (h : ∀ v, B *ᵥ v = 0) : B = 0 := by
  ext i j
  have h1 := congrFun (h (Pi.single j 1)) i
  simpa [mulVec_single] using h1

theorem eq_of_mulVec_w0 {A C : Matrix (Fin 12) (Fin 12) (ZMod 2)}
    (hA : ∀ g ∈ H12Cert.G, A * ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A)
    (hC : ∀ g ∈ H12Cert.G, C * ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * C)
    (h : A *ᵥ H12Cert.w0 = C *ᵥ H12Cert.w0) : A = C := by
  set B := A - C with hBdef
  have hB : ∀ g ∈ H12Cert.G, B * ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * B := fun g hg => by
    rw [hBdef, Matrix.sub_mul, Matrix.mul_sub, hA g hg, hC g hg]
  have hker := eq_top_of_w0_mem (J := LinearMap.ker (Matrix.mulVecLin B)) (fun g hg v hv => by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply] at hv ⊢
    rw [mulVec_mulVec, hB g hg, ← mulVec_mulVec, hv, mulVec_zero]) (by
    rw [LinearMap.mem_ker, Matrix.mulVecLin_apply, hBdef, sub_mulVec, h, sub_self])
  have hB0 : B = 0 := eq_zero_of_mulVec_eq_zero fun v => by
    have : v ∈ LinearMap.ker (Matrix.mulVecLin B) := by rw [hker]; exact Submodule.mem_top
    rwa [LinearMap.mem_ker, Matrix.mulVecLin_apply] at this
  exact sub_eq_zero.mp hB0

theorem zM_comm {g : GL (Fin 12) (ZMod 2)} (hg : g ∈ H12Cert.G) :
    zM * ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * zM := by
  rw [zM, ← Units.val_mul, ← Units.val_mul, H12Cert.zU_comm hg]

theorem commutant_G {A : Matrix (Fin 12) (Fin 12) (ZMod 2)}
    (hA : ∀ g ∈ H12Cert.G, A * ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A) :
    A = 0 ∨ A = 1 ∨ A = zM ∨ A = zM * zM := by
  have hfix : ∀ t ∈ H12Cert.T0,
      ((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ (A *ᵥ H12Cert.w0) =
        A *ᵥ H12Cert.w0 := fun t ht => by
    rw [mulVec_mulVec, ← hA t (H12Cert.T0_le_G ht), ← mulVec_mulVec,
      H12Cert.S0_fix (H12Cert.T0_le_S0 ht)]
  have hF := (H12Cert.fix_T0_iff _).mp hfix
  have h0 : ∀ g ∈ H12Cert.G, (0 : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * 0 := fun _ _ => by
    rw [Matrix.zero_mul, Matrix.mul_zero]
  have h1 : ∀ g ∈ H12Cert.G, (1 : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * 1 := fun _ _ => by
    rw [Matrix.one_mul, Matrix.mul_one]
  have hz2 : ∀ g ∈ H12Cert.G, zM * zM *
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * (zM * zM) :=
    fun g hg => by rw [Matrix.mul_assoc, zM_comm hg, ← Matrix.mul_assoc, zM_comm hg,
      Matrix.mul_assoc]
  rcases (H12Cert.mem_F0v_iff _).mp hF with h | h | h | h
  · exact Or.inl (eq_of_mulVec_w0 hA h0 (by rw [h, zero_mulVec]))
  · exact Or.inr (Or.inl (eq_of_mulVec_w0 hA h1 (by rw [h, one_mulVec])))
  · exact Or.inr (Or.inr (Or.inl (eq_of_mulVec_w0 hA (fun g hg => zM_comm hg) h)))
  · exact Or.inr (Or.inr (Or.inr (eq_of_mulVec_w0 hA hz2 (by rw [h, mulVec_mulVec]))))

theorem two_dvd_card {J : Submodule (ZMod 2) (Fin 12 → ZMod 2)} (hJ0 : J ≠ ⊥) :
    2 ∣ Nat.card ↥J := by
  have hdvd : Nat.card ↥J ∣ 2 ^ 12 := by
    have h := AddSubgroup.card_addSubgroup_dvd_card J.toAddSubgroup
    rw [Nat.card_fun, Nat.card_zmod, Nat.card_fin] at h
    exact h
  obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
  rcases k with _ | k
  · exfalso
    apply hJ0
    rw [pow_zero] at hk
    obtain ⟨hs, -⟩ := Nat.card_eq_one_iff_unique.mp hk
    rw [Submodule.eq_bot_iff]
    intro x hx
    have := hs.elim ⟨x, hx⟩ 0
    exact congrArg Subtype.val this
  · rw [hk, pow_succ]
    exact dvd_mul_left 2 _

theorem irreducible_G (J : Submodule (ZMod 2) (Fin 12 → ZMod 2))
    (hJ : ∀ g ∈ H12Cert.G, ∀ v ∈ J,
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v ∈ J) :
    J = ⊥ ∨ J = ⊤ := by
  by_cases hJ0 : J = ⊥
  · exact Or.inl hJ0
  right
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT : IsPGroup 2 ↥H12Cert.T0 := IsPGroup.of_card (n := 7) (by rw [H12Cert.card_T0]; norm_num)
  let act : MulAction ↥H12Cert.T0 ↥J :=
    { smul := fun t v => ⟨((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
          (v : Fin 12 → ZMod 2), hJ _ (H12Cert.T0_le_G t.2) _ v.2⟩
      one_smul := fun v => Subtype.ext (by
        show ((1 : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ (v : _) = v
        rw [Units.val_one, one_mulVec])
      mul_smul := fun s t v => Subtype.ext (by
        show (((s * t : ↥H12Cert.T0) : GL (Fin 12) (ZMod 2)) :
            Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ (v : Fin 12 → ZMod 2) =
          ((s : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ
            (((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v)
        rw [Subgroup.coe_mul, Units.val_mul, mulVec_mulVec]) }
  have hsmul : ∀ (t : ↥H12Cert.T0) (v : ↥J), ((t • v : ↥J) : Fin 12 → ZMod 2) =
      ((t : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ (v : Fin 12 → ZMod 2) :=
    fun _ _ => rfl
  have h0fix : (0 : ↥J) ∈ MulAction.fixedPoints ↥H12Cert.T0 ↥J := fun t =>
    Subtype.ext (by rw [hsmul, Submodule.coe_zero, mulVec_zero])
  obtain ⟨b, hb, hb0⟩ :=
    hT.exists_fixed_point_of_prime_dvd_card_of_fixed_point ↥J (two_dvd_card hJ0) h0fix
  have hbF : (b : Fin 12 → ZMod 2) ∈ H12Cert.F0v := (H12Cert.fix_T0_iff _).mp fun t ht => by
    have := congrArg Subtype.val (hb ⟨t, ht⟩)
    rwa [hsmul] at this
  have hb0' : (b : Fin 12 → ZMod 2) ≠ 0 := fun h => hb0 (Subtype.ext h.symm)
  have hzJ : ∀ v ∈ J, zM *ᵥ v ∈ J := fun v hv => hJ _ H12Cert.zU_mem v hv
  have hz3 : zM * (zM * zM) = 1 := by
    rw [zM, ← Units.val_mul, ← Units.val_mul, ← pow_three, H12Cert.zU_pow_three, Units.val_one]
  have hz3v : ∀ v, zM *ᵥ (zM *ᵥ (zM *ᵥ v)) = v := fun v => by
    rw [mulVec_mulVec, mulVec_mulVec, Matrix.mul_assoc, hz3, one_mulVec]
  have hw0 : H12Cert.w0 ∈ J := by
    rcases (H12Cert.mem_F0v_iff _).mp hbF with h | h | h | h
    · exact absurd h hb0'
    · rw [← h]; exact b.2
    · have hm : zM *ᵥ (zM *ᵥ (b : Fin 12 → ZMod 2)) ∈ J := hzJ _ (hzJ _ b.2)
      rwa [h, hz3v] at hm
    · have hm : zM *ᵥ (b : Fin 12 → ZMod 2) ∈ J := hzJ _ b.2
      rwa [h, hz3v] at hm
  exact eq_top_of_w0_mem hJ hw0

abbrev pM : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ((conjP : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))

abbrev qM : Matrix (Fin 12) (Fin 12) (ZMod 2) :=
  ((conjP⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))

theorem pM_mul_qM : pM * qM = 1 := Units.mul_inv conjP

theorem qM_mul_pM : qM * pM = 1 := Units.inv_mul conjP

theorem comm_of_comm_gens {A : Matrix (Fin 12) (Fin 12) (ZMod 2)}
    (ha : A * (L1442M.m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      (L1442M.m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A)
    (hb : A * (L1442M.m22b : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      (L1442M.m22b : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A)
    {x : GL (Fin 12) (ZMod 2)} (hx : x ∈ L1442M.m22) :
    A * (x : Matrix (Fin 12) (Fin 12) (ZMod 2)) = (x : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A := by
  induction hx using Subgroup.closure_induction with
  | mem y hy =>
    rcases hy with rfl | rfl
    · exact ha
    · exact hb
  | one => rw [Units.val_one, Matrix.mul_one, Matrix.one_mul]
  | mul y z _ _ hy hz =>
    rw [Units.val_mul, ← Matrix.mul_assoc, hy, Matrix.mul_assoc, hz, Matrix.mul_assoc]
  | inv y _ hy =>
    have h1 : ((y⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
        (y : Matrix (Fin 12) (Fin 12) (ZMod 2)) = 1 := Units.inv_mul y
    have h2 : (y : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
        ((y⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) = 1 := Units.mul_inv y
    calc A * ((y⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2))
        = ((y⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
            ((y : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A) *
            ((y⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
          rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
      _ = ((y⁻¹ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A := by
          rw [← hy, Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]

theorem zP_mul_four : zP * zP * (zP * zP) = zP := by
  have h : zP * zP * (zP * zP) = zP ^ 3 * zP := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  rw [h, zP_pow_three, one_mul]

theorem commutant_m22 {A : Matrix (Fin 12) (Fin 12) (ZMod 2)}
    (ha : A * (L1442M.m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      (L1442M.m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A)
    (hb : A * (L1442M.m22b : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
      (L1442M.m22b : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A) : A = 0 ∨ A = 1 := by
  set A' := qM * A * pM with hA'
  have hcomm : ∀ g ∈ H12Cert.G,
      A' * ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A' := by
    intro g hg
    have hm := comm_of_comm_gens ha hb (m22Zero_le_m22 (conj_mem_m22Zero hg))
    simp only [Units.val_mul] at hm
    have e1 : qM * (A * (pM * (g : Matrix (Fin 12) (Fin 12) (ZMod 2)) * qM)) * pM =
        A' * (g : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
      rw [hA']
      simp only [Matrix.mul_assoc]
      rw [qM_mul_pM, Matrix.mul_one]
    have e2 : qM * (pM * (g : Matrix (Fin 12) (Fin 12) (ZMod 2)) * qM * A) * pM =
        (g : Matrix (Fin 12) (Fin 12) (ZMod 2)) * A' := by
      rw [hA']
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc qM pM, qM_mul_pM, Matrix.one_mul]
    rw [← e1, hm, e2]
  have hA : A = pM * A' * qM := by
    rw [hA']
    simp only [Matrix.mul_assoc]
    rw [pM_mul_qM, Matrix.mul_one, ← Matrix.mul_assoc, pM_mul_qM, Matrix.one_mul]
  have hzP : pM * zM * qM = ((zP : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
    simp only [zP, Units.val_mul]
  have hnot : ∀ y : GL (Fin 12) (ZMod 2),
      (y : Matrix (Fin 12) (Fin 12) (ZMod 2)) * (L1442M.m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        (L1442M.m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) * y → y * L1442M.m22a = L1442M.m22a * y :=
    fun y hc => Units.ext (by rw [Units.val_mul, Units.val_mul, hc])
  rcases commutant_G hcomm with h | h | h | h
  · left
    rw [hA, h, Matrix.mul_zero, Matrix.zero_mul]
  · right
    rw [hA, h, Matrix.mul_one, pM_mul_qM]
  · exfalso
    have hc : (zP : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
        (L1442M.m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        (L1442M.m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) * zP := by
      rw [← hzP, ← h, ← hA]
      exact ha
    exact m22a_not_comm_zP (hnot zP hc).symm
  · exfalso
    have hzz : pM * (zM * zM) * qM =
        ((zP * zP : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) := by
      rw [Units.val_mul, ← hzP]
      simp only [Matrix.mul_assoc]
      rw [← Matrix.mul_assoc qM pM, qM_mul_pM, Matrix.one_mul]
    have hc : ((zP * zP : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *
        (L1442M.m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) =
        (L1442M.m22a : Matrix (Fin 12) (Fin 12) (ZMod 2)) * (zP * zP : GL (Fin 12) (ZMod 2)) := by
      rw [← hzz, ← h, ← hA]
      exact ha
    have hc' := hnot _ hc
    have hc2 : zP * zP * (zP * zP) * L1442M.m22a = L1442M.m22a * (zP * zP * (zP * zP)) := by
      rw [mul_assoc, hc', ← mul_assoc, hc', mul_assoc]
    rw [zP_mul_four] at hc2
    exact m22a_not_comm_zP hc2.symm

theorem irreducible_m22 (J : Submodule (ZMod 2) (Fin 12 → ZMod 2))
    (hJ : ∀ γ ∈ L1442M.m22, ∀ v ∈ J,
      ((γ : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v ∈ J) :
    J = ⊥ ∨ J = ⊤ := by
  set J' := J.comap (Matrix.mulVecLin pM) with hJ'
  have hmem : ∀ v, v ∈ J' ↔ pM *ᵥ v ∈ J := fun v => by
    rw [hJ', Submodule.mem_comap, Matrix.mulVecLin_apply]
  have hinv : ∀ g ∈ H12Cert.G, ∀ v ∈ J',
      ((g : GL (Fin 12) (ZMod 2)) : Matrix (Fin 12) (Fin 12) (ZMod 2)) *ᵥ v ∈ J' := by
    intro g hg v hv
    rw [hmem] at hv ⊢
    have h1 := hJ _ (m22Zero_le_m22 (conj_mem_m22Zero hg)) _ hv
    simp only [Units.val_mul] at h1
    rwa [mulVec_mulVec, Matrix.mul_assoc, Matrix.mul_assoc, qM_mul_pM, Matrix.mul_one,
      ← mulVec_mulVec] at h1
  have hback : ∀ v ∈ J, qM *ᵥ v ∈ J' := fun v hv => by
    rw [hmem, mulVec_mulVec, pM_mul_qM, one_mulVec]
    exact hv
  rcases irreducible_G J' hinv with h | h
  · left
    rw [Submodule.eq_bot_iff]
    intro v hv
    have h1 := hback v hv
    rw [h, Submodule.mem_bot] at h1
    calc v = pM *ᵥ (qM *ᵥ v) := by rw [mulVec_mulVec, pM_mul_qM, one_mulVec]
      _ = 0 := by rw [h1, mulVec_zero]
  · right
    rw [eq_top_iff]
    intro v _
    have h1 : qM *ᵥ v ∈ J' := by rw [h]; exact Submodule.mem_top
    rw [hmem, mulVec_mulVec, pM_mul_qM, one_mulVec] at h1
    exact h1

end CFSG.Quasithin.H.Mathieu.M22Link

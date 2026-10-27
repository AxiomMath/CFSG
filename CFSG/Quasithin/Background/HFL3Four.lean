module

public import CFSG.Quasithin.Background.FixVLattice
public import CFSG.Quasithin.Background.HFL3Q
public import CFSG.Quasithin.Background.HFL3Three

public section

namespace CFSG.Quasithin.H.L3Nine

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag SU3
  Tri

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

omit [Finite K] [CharP K 2] in
theorem transvection02_mem_Q2 (a : K) :
    SpecialLinearGroup.transvection (by decide : (0 : Fin 3) ≠ 2) a ∈ Q2 K := by
  refine ⟨mem_unitriangular.2 ⟨fun i k hik => ?_, fun i => ?_⟩, ?_⟩ <;>
    rw [Matrix.SpecialLinearGroup.transvection_coe]
  · fin_cases i <;> fin_cases k <;> simp_all [Matrix.transvection, Matrix.single_apply]
  · fin_cases i <;> simp [Matrix.transvection, Matrix.single_apply]
  · simp [Matrix.transvection, Matrix.single_apply]

theorem lt_card_rhoQ2 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    2 ^ n < Nat.card ↥((Q2 K).map (rho hK)) := by
  rw [card_map_rho_of_inj hK fun x (hx : x ∈ Q2 K) h => eq_one_of_rho_uni3 hK hx.1 h]
  let f : K → ↥(Q2 K) := fun a => ⟨_, transvection02_mem_Q2 a⟩
  have hf : Function.Injective f := by
    intro a b h
    have := congrArg (fun x : ↥(Q2 K) => ((x : SpecialLinearGroup (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 2) h
    simpa [f, Matrix.SpecialLinearGroup.transvection_coe, Matrix.transvection,
      Matrix.single_apply] using this
  have h1 := Nat.card_le_card_of_injective f hf
  rw [hK] at h1
  have h2 : 2 ^ n < (2 ^ n) ^ 2 := by
    rw [sq]
    exact lt_mul_self (Nat.one_lt_two_pow (by omega))
  omega

theorem fixV_rhoQ2 (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) :
    fixV ((Q2 K).map (rho hK)) = blkW n K := by
  have hle : blkW n K ≤ fixV ((Q2 K).map (rho hK)) := by
    rintro X hX _ ⟨x, hx, rfl⟩
    exact blkW_le_fixV hx hK hX
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  rw [card_blkW hn hK, hK, ← pow_mul, ← pow_mul]
  have h := card_fixV_le_of_card_gt hn hK (Subgroup.map_le_range _ _) ?_ (lt_card_rhoQ2 hn hK)
  · calc _ ≤ 2 ^ (4 * n) := h
      _ = 2 ^ (n * (2 * 2)) := by ring_nf
  · have hc : ∀ x ∈ Q2 K, ∀ y ∈ Q2 K, x * y = y * x := by
      intro x hx y hy
      apply uni3_ext (mul_mem hx.1 hy.1) (mul_mem hy.1 hx.1)
      · rw [uni3_mul_01 hx.1 hy.1, uni3_mul_01 hy.1 hx.1, add_comm]
      · rw [uni3_mul_02 hx.1 hy.1, uni3_mul_02 hy.1 hx.1, hx.2, hy.2]
        ring
      · rw [uni3_mul_12 hx.1 hy.1, uni3_mul_12 hy.1 hx.1, add_comm]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
      rw [← map_mul, ← map_mul, hc x hx y hy]
    · rintro _ ⟨x, hx, rfl⟩
      rw [← map_pow]
      have hxx : x ^ 2 = 1 := by
        rw [sq]
        apply uni3_ext (mul_mem hx.1 hx.1) (one_mem _)
        · rw [uni3_mul_01 hx.1 hx.1, hx.2]
          simp
        · rw [uni3_mul_02 hx.1 hx.1, hx.2, zero_mul, add_zero, CharTwo.add_self_eq_zero]
          simp
        · rw [uni3_mul_12 hx.1 hx.1, CharTwo.add_self_eq_zero]
          simp
      rw [hxx, map_one]

theorem card_inf_fixV_twist_sq_le (hK : Nat.card K = (2 ^ n) ^ 2) (A : GL (Fin 3) K)
    {σ : K ≃+* K} {c : K} (hc : bar n c = c) (hσc : σ c ≠ c) {U : Subgroup (HMod n K)}
    (hU : ∀ X ∈ U, smulH hc X ∈ U) :
    Nat.card ↥(U ⊓ fixV (Subgroup.zpowers (rhoT hK A * fldAut σ))) ^ 2 ≤ Nat.card U := by
  classical
  set C := U ⊓ fixV (Subgroup.zpowers (rhoT hK A * fldAut σ)) with hC
  have hfix : ∀ X : HMod n K, X ∈ C →
      tw n (A : Matrix (Fin 3) (Fin 3) K) ((mat X).map σ) = mat X := fun X hX => by
    have h := congrArg mat (mem_fixV_zpowers_iff.mp hX.2)
    rwa [MulAut.mul_apply, mat_rhoT, mat_fldAut] at h
  let G : ↥C × ↥C → ↥U := fun p =>
    ⟨(p.1 : HMod n K) * smulH hc (p.2 : HMod n K), U.mul_mem p.1.2.1 (hU _ p.2.2.1)⟩
  have hG : Function.Injective G := by
    rintro ⟨X, Y⟩ ⟨X', Y'⟩ h
    have h1 : mat (X : HMod n K) + c • mat (Y : HMod n K) =
        mat (X' : HMod n K) + c • mat (Y' : HMod n K) := by
      have := congrArg (fun p : ↥U => mat (p : HMod n K)) h
      simpa [G, mat_mul, mat_smulH] using this
    set D := mat (X : HMod n K) - mat (X' : HMod n K) with hD
    set E := mat (Y' : HMod n K) - mat (Y : HMod n K) with hE
    have hDE : D = c • E := by
      rw [hD, hE, smul_sub]
      linear_combination (norm := abel_nf) h1
    have hfD : tw n (A : Matrix (Fin 3) (Fin 3) K) (D.map σ) = D := by
      have e : D.map σ = (mat (X : HMod n K)).map σ + (-1 : K) • (mat (X' : HMod n K)).map σ := by
        ext i j
        simp [hD, sub_eq_add_neg]
      rw [e, tw_add, tw_smul, hfix _ X.2, hfix _ X'.2, hD]
      simp [sub_eq_add_neg]
    have hfE : tw n (A : Matrix (Fin 3) (Fin 3) K) (E.map σ) = E := by
      have e : E.map σ = (mat (Y' : HMod n K)).map σ + (-1 : K) • (mat (Y : HMod n K)).map σ := by
        ext i j
        simp [hE, sub_eq_add_neg]
      rw [e, tw_add, tw_smul, hfix _ Y'.2, hfix _ Y.2, hE]
      simp [sub_eq_add_neg]
    have hcE : (c • E).map σ = σ c • E.map σ := by
      ext i j
      simp
    have h2 : D = σ c • E := by
      rw [← hfD, hDE, hcE, tw_smul, hfE]
    have h3 : (σ c - c) • E = 0 := by rw [sub_smul, ← h2, ← hDE, sub_self]
    have hE0 : E = 0 := (smul_eq_zero.mp h3).resolve_left (sub_ne_zero.mpr hσc)
    have hD0 : D = 0 := by rw [hDE, hE0, smul_zero]
    exact Prod.ext (Subtype.ext (mat_injective (sub_eq_zero.mp hD0)))
      (Subtype.ext (mat_injective (sub_eq_zero.mp hE0).symm))
  have hle := Nat.card_le_card_of_injective G hG
  rw [Nat.card_prod] at hle
  rw [sq]
  exact hle

theorem fixV_sup_eq {W : Type*} [CommGroup W] (X Y : Subgroup (MulAut W)) :
    fixV (X ⊔ Y) = fixV X ⊓ fixV Y :=
  CFSG.Quasithin.FixVLat.fixV_sup_eq X Y

theorem smulH_mem_blkW {c : K} (hc : bar n c = c) {X : HMod n K} (hX : X ∈ blkW n K) :
    smulH hc X ∈ blkW n K := by
  obtain ⟨h1, h2, h3⟩ := hX
  refine ⟨?_, ?_, ?_⟩ <;> simp [mat_smulH, h1, h2, h3]

theorem card_blkW_fixV (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2) {x : MulAut (HMod n K)}
    (hx : x ∈ norm hK) (hodd : Odd (orderOf x))
    (hxN : x ∈ Subgroup.normalizer (((Q2 K).map (rho hK) : Subgroup (MulAut (HMod n K))) :
      Set (MulAut (HMod n K)))) :
    Nat.card ↥(blkW n K ⊓ fixV (Subgroup.zpowers x)) = 1 ∨
      Nat.card ↥(blkW n K ⊓ fixV (Subgroup.zpowers x)) = 2 ^ (4 * n) ∨
      Nat.card ↥(blkW n K ⊓ fixV (Subgroup.zpowers x)) ≤ 2 ^ (2 * n) := by
  classical
  have hpres : ∀ X ∈ blkW n K, x X ∈ blkW n K := by
    intro X hX
    rw [← fixV_rhoQ2 hn hK] at hX ⊢
    intro a ha
    have h1 : x⁻¹ * a * x ∈ (Q2 K).map (rho hK) := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) a).mp ha
      simpa [mul_assoc] using this
    have h2 := hX _ h1
    rw [MulAut.mul_apply, MulAut.mul_apply] at h2
    calc a (x X) = x (x⁻¹ (a (x X))) := by rw [MulAut.apply_inv_self]
      _ = x X := by rw [h2]
  have hcardB : Nat.card (blkW n K) = 2 ^ (4 * n) := by
    rw [card_blkW hn hK, hK, ← pow_mul, ← pow_mul]
    ring_nf
  obtain ⟨A, σ, rfl, hσ⟩ := exists_odd_decomp hn hK hx
  by_cases hσ1 : σ = 1
  · subst hσ1
    rw [fldAut_one, mul_one] at hpres ⊢
    have hrow : ∀ j : Fin 3, j ≠ 2 → (A : Matrix (Fin 3) (Fin 3) K) 2 j = 0 := by
      intro j hj
      have hmem : pt hK (Pi.single j 1) ∈ blkW n K := by
        refine ⟨?_, ?_, ?_⟩ <;> simp [mat_pt, rk1_apply, Pi.single_apply, hj.symm]
      have h1 := (hpres _ hmem).2.2
      rw [rhoT_pt, mat_pt, rk1_apply] at h1
      have h2 : ((A : Matrix (Fin 3) (Fin 3) K) *ᵥ Pi.single j 1) 2 =
          (A : Matrix (Fin 3) (Fin 3) K) 2 j := by
        simp [Matrix.mulVec_single]
      rw [h2] at h1
      rcases mul_eq_zero.mp h1 with h | h
      · exact h
      · exact (map_eq_zero_iff _ (bar n).injective).mp h
    have a20 := hrow 0 (by decide)
    have a21 := hrow 1 (by decide)
    set M := (A : Matrix (Fin 3) (Fin 3) K) with hM
    have hent : ∀ X ∈ blkW n K ⊓ fixV (Subgroup.zpowers (rhoT hK A)), ∀ i j : Fin 3,
        (M * mat X * (conjM n M)ᵀ) i j = mat X i j := by
      intro X hX i j
      have h := congrArg mat (mem_fixV_zpowers_iff.mp hX.2)
      rw [mat_rhoT] at h
      exact congrFun (congrFun h i) j
    by_cases hsc : M 0 1 = 0 ∧ M 1 0 = 0 ∧ M 1 1 = M 0 0
    ·
      obtain ⟨b0, c0, hd⟩ := hsc
      have hmul : ∀ X ∈ blkW n K, mat (rhoT hK A X) = (M 0 0 * bar n (M 0 0)) • mat X := by
        intro X hX
        obtain ⟨h02, h12, h22⟩ := hX
        have h20 : mat X 2 0 = 0 := by rw [← herm_apply, h02, map_zero]
        have h21 : mat X 2 1 = 0 := by rw [← herm_apply, h12, map_zero]
        rw [mat_rhoT]
        ext i j
        fin_cases i <;> fin_cases j <;>
          simp [tw, ← hM, Matrix.mul_apply, Fin.sum_univ_three, conjM, a20, a21, b0, c0, hd, h02,
            h12, h22, h20, h21] <;> ring
      by_cases hN : M 0 0 * bar n (M 0 0) = 1
      · right; left
        rw [← hcardB]
        have heq : blkW n K ⊓ fixV (Subgroup.zpowers (rhoT hK A)) = blkW n K := by
          refine inf_eq_left.mpr fun X hX => mem_fixV_zpowers_iff.mpr (mat_injective ?_)
          rw [hmul X hX, hN, one_smul]
        rw [heq]
      · left
        have hbot : blkW n K ⊓ fixV (Subgroup.zpowers (rhoT hK A)) = ⊥ := by
          refine (Subgroup.eq_bot_iff_forall _).2 fun X hX => ?_
          have h1 := hmul X hX.1
          rw [mem_fixV_zpowers_iff.mp hX.2] at h1
          apply mat_injective
          rw [mat_one]
          have h2 : (M 0 0 * bar n (M 0 0) - 1) • mat X = 0 := by
            rw [sub_smul, ← h1, one_smul, sub_self]
          exact (smul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hN)
        rw [hbot, Subgroup.card_bot]
    ·
      right; right
      obtain ⟨z, hz⟩ := exists_bar_ne hn hK
      set B' : Matrix (Fin 2) (Fin 2) K := !![M 0 0, M 0 1; M 1 0, M 1 1] with hB'
      set C' : Matrix (Fin 2) (Fin 2) K := (B'.map (bar n))ᵀ with hC'
      have hC'ns : ∀ e : K, C' ≠ e • 1 := by
        intro e he
        apply hsc
        have h1 : B'.map (bar n) = e • 1 := by
          have := congrArg Matrix.transpose he
          rwa [hC', transpose_transpose, Matrix.transpose_smul, Matrix.transpose_one] at this
        have h2 : ∀ i j, bar n (B' i j) = (e • (1 : Matrix (Fin 2) (Fin 2) K)) i j :=
          fun i j => congrFun (congrFun h1 i) j
        have e01 := h2 0 1
        have e10 := h2 1 0
        have e00 := h2 0 0
        have e11 := h2 1 1
        simp [hB'] at e01 e10 e00 e11
        refine ⟨e01, e10, (bar n).injective ?_⟩
        rw [e00, e11]
      set S := blkW n K ⊓ fixV (Subgroup.zpowers (rhoT hK A)) with hS
      let sub : HMod n K → Matrix (Fin 2) (Fin 2) K := fun X =>
        !![mat X 0 0, mat X 0 1; mat X 1 0, mat X 1 1]
      have hsub : ∀ X ∈ S, sub X ∈ fixSub B' C' := by
        intro X hX
        obtain ⟨h02, h12, h22⟩ := hX.1
        have h20 : mat X 2 0 = 0 := by rw [← herm_apply, h02, map_zero]
        have h21 : mat X 2 1 = 0 := by rw [← herm_apply, h12, map_zero]
        have e := hent X hX
        rw [mem_fixSub]
        ext i j
        have eij := e (Fin.castSucc i) (Fin.castSucc j)
        fin_cases i <;> fin_cases j <;>
          simp [Matrix.mul_apply, Fin.sum_univ_three, Fin.sum_univ_two, conjM, hB', hC', sub,
            h02, h12, h22, h20, h21] at eij ⊢ <;> linear_combination eij
      let G : ↥S × ↥S → ↥(fixSub B' C') := fun p =>
        ⟨sub p.1 + z • sub p.2, (fixSub B' C').add_mem (hsub _ p.1.2)
          ((fixSub B' C').smul_mem z (hsub _ p.2.2))⟩
      have hG : Function.Injective G := by
        rintro ⟨X, Y⟩ ⟨X', Y'⟩ h
        have h1 := congrArg Subtype.val h
        have hzero : ∀ P ∈ S, mat P 0 2 = 0 ∧ mat P 1 2 = 0 ∧ mat P 2 2 = 0 ∧ mat P 2 0 = 0 ∧
            mat P 2 1 = 0 := by
          intro P hP
          obtain ⟨h02, h12, h22⟩ := hP.1
          exact ⟨h02, h12, h22, by rw [← herm_apply, h02, map_zero],
            by rw [← herm_apply, h12, map_zero]⟩
        have h2 : mat (X : HMod n K) + z • mat (Y : HMod n K) =
            mat (X' : HMod n K) + z • mat (Y' : HMod n K) := by
          obtain ⟨x02, x12, x22, x20, x21⟩ := hzero _ X.2
          obtain ⟨y02, y12, y22, y20, y21⟩ := hzero _ Y.2
          obtain ⟨x02', x12', x22', x20', x21'⟩ := hzero _ X'.2
          obtain ⟨y02', y12', y22', y20', y21'⟩ := hzero _ Y'.2
          ext i j
          have e00 := congrFun (congrFun h1 0) 0
          have e01 := congrFun (congrFun h1 0) 1
          have e10 := congrFun (congrFun h1 1) 0
          have e11 := congrFun (congrFun h1 1) 1
          simp [G, sub] at e00 e01 e10 e11
          fin_cases i <;> fin_cases j <;>
            simp [x02, x12, x22, x20, x21, y02, y12, y22, y20, y21, x02', x12', x22', x20',
              x21', y02', y12', y22', y20', y21', e00, e01, e10, e11]
        obtain ⟨hX, hY⟩ := eq_of_add_smul_eq hz h2
        exact Prod.ext (Subtype.ext hX) (Subtype.ext hY)
      have hle := Nat.card_le_card_of_injective G hG
      have hS2 : Nat.card ↥(fixSub B' C') ≤ Nat.card K ^ 2 := by
        rw [Module.natCard_eq_pow_finrank (K := K)]
        exact Nat.pow_le_pow_right Nat.card_pos (finrank_fixSub_two_le hC'ns)
      rw [Nat.card_prod] at hle
      have h3 : Nat.card ↥S * Nat.card ↥S ≤ 2 ^ (2 * n) * 2 ^ (2 * n) := by
        calc _ ≤ Nat.card K ^ 2 := hle.trans hS2
          _ = 2 ^ (2 * n) * 2 ^ (2 * n) := by rw [hK, ← pow_mul, ← pow_mul, ← pow_add]; ring_nf
      exact Nat.mul_self_le_mul_self_iff.mp h3
  · right; right
    obtain ⟨c, hc, hσc⟩ := exists_fixed_moved hK hσ1 hodd hσ
    have h1 := card_inf_fixV_twist_sq_le hK A hc hσc (U := blkW n K)
      fun X hX => smulH_mem_blkW hc hX
    rw [hcardB, show 4 * n = 2 * n * 2 by ring, pow_mul] at h1
    exact (Nat.pow_le_pow_iff_left (by norm_num)).mp h1

theorem card_fixV_sup_ne (hn : 1 ≤ n) (hK : Nat.card K = (2 ^ n) ^ 2)
    {A : Subgroup (MulAut (HMod n K))} (hAL : A ≤ img hK) (hAe : IsElemAbelian2 A)
    (hcard : Nat.card A = Nat.card K ^ 2) {x : MulAut (HMod n K)} (hx : x ∈ norm hK)
    (hxN : x ∈ Subgroup.normalizer (A : Set (MulAut (HMod n K)))) (hodd : Odd (orderOf x)) :
    Nat.card ↥(fixV (A ⊔ Subgroup.zpowers x)) ≠ 2 ^ (3 * n) := by
  have hq3 : 2 ^ n < 2 ^ (3 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  by_cases hfix : 2 ^ n < Nat.card (fixV A)
  · have hAN : A ≤ norm hK := hAL.trans (Subgroup.le_normalizer)
    obtain ⟨g, hg⟩ := exists_conj_eq_Q2 hn hK hAN hAe hcard.ge hfix
    set c := MulAut.conj (rho hK g) with hcdef
    have hgN : rho hK g ∈ norm hK := Subgroup.le_normalizer ⟨g, rfl⟩
    set x' := rho hK g * x * (rho hK g)⁻¹ with hx'
    have hx'N : x' ∈ norm hK := (norm hK).mul_mem ((norm hK).mul_mem hgN hx)
      ((norm hK).inv_mem hgN)
    have hx'c : x' = c.toMonoidHom x := rfl
    have hx'o : Odd (orderOf x') := by
      rw [hx'c, orderOf_injective c.toMonoidHom c.injective x]
      exact hodd
    have hx'Q : x' ∈ Subgroup.normalizer (((Q2 K).map (rho hK) : Subgroup (MulAut (HMod n K))) :
        Set (MulAut (HMod n K))) := by
      rw [← hg, ← Subgroup.map_equiv_normalizer_eq, hx'c]
      exact ⟨x, hxN, rfl⟩
    have hmap : (A ⊔ Subgroup.zpowers x).map c.toMonoidHom =
        (Q2 K).map (rho hK) ⊔ Subgroup.zpowers x' := by
      rw [Subgroup.map_sup, hg, MonoidHom.map_zpowers]
      rfl
    have hcardeq : Nat.card ↥(fixV (A ⊔ Subgroup.zpowers x)) =
        Nat.card ↥(blkW n K ⊓ fixV (Subgroup.zpowers x')) := by
      rw [← card_fixV_map_conj (rho hK g), ← hcdef, hmap, fixV_sup_eq, fixV_rhoQ2 hn hK]
    rw [hcardeq]
    have hq4 : 2 ^ (3 * n) < 2 ^ (4 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    have hq2 : 2 ^ (2 * n) < 2 ^ (3 * n) := Nat.pow_lt_pow_right (by norm_num) (by omega)
    rcases card_blkW_fixV hn hK hx'N hx'o hx'Q with h | h | h
    · rw [h]
      exact (Nat.one_lt_two_pow (by omega)).ne
    · rw [h]
      exact hq4.ne'
    · exact (h.trans_lt hq2).ne
  · push Not at hfix
    have hle : Nat.card ↥(fixV (A ⊔ Subgroup.zpowers x)) ≤ Nat.card ↥(fixV A) :=
      Subgroup.card_le_of_le fun v hv a ha => hv a (le_sup_left (b := Subgroup.zpowers x) ha)
    exact (hle.trans hfix |>.trans_lt hq3).ne

end CFSG.Quasithin.H.L3Nine

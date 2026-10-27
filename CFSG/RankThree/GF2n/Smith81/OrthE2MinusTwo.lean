module

public import CFSG.RankThree.GF2n.Smith81.OrthE2Frame

public section

open scoped Matrix commutatorElement

namespace CFSG.RankThree.GF2n.Smith81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 QuadraticMap
open CFSG.LieType.Universal.Spin (quadPlus quadMinus)

section Arith

theorem orth_sl_exp_false_of_two_le {q : ℕ} (hq : Even q) (hq0 : q ≠ 0) {m k : ℕ} (hm : 2 ≤ m)
    (hk : 2 * m ≤ k + 1) {Y : ℕ} {X : ℤ} (hX : Odd X)
    (hY : (Y : ℤ) = (q : ℤ) ^ (m * (m - 1)) * X)
    (hdvd : q ^ (∑ i ∈ Finset.range k, i) ∣ Y) : False := by
  obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
  obtain ⟨a, rfl⟩ : ∃ a, m = a + 1 := ⟨m - 1, by omega⟩
  have hS := Finset.sum_range_id_mul_two (j + 1)
  simp only [Nat.add_sub_cancel] at hS
  set S := ∑ i ∈ Finset.range (j + 1), i with hSdef
  simp only [Nat.add_sub_cancel] at hY
  have h1 : (a + 1) * a + 1 ≤ S := by
    have h2 := Nat.mul_le_mul (show 2 * a + 1 ≤ j + 1 by omega) (show 2 * a ≤ j by omega)
    have ha : 1 ≤ a := by omega
    nlinarith [Nat.mul_le_mul ha ha]
  obtain ⟨d, hd⟩ : ∃ d, S = (a + 1) * a + 1 + d := ⟨S - ((a + 1) * a + 1), by omega⟩
  have h3 : ((q : ℤ) ^ S) ∣ (Y : ℤ) := by exact_mod_cast hdvd
  rw [hY, hd, pow_add, pow_add, pow_one] at h3
  have h4 : (q : ℤ) ^ ((a + 1) * a) * ((q : ℤ) * (q : ℤ) ^ d) ∣ (q : ℤ) ^ ((a + 1) * a) * X := by
    rw [← mul_assoc]
    exact h3
  have h5 := (mul_dvd_mul_iff_left (pow_ne_zero _ (by exact_mod_cast hq0))).mp h4
  have h6 : (q : ℤ) ∣ X := (dvd_mul_right _ _).trans h5
  have h7 : (2 : ℤ) ∣ X := by
    obtain ⟨r, hr⟩ := hq
    have h2q : (2 : ℤ) ∣ (q : ℤ) := ⟨(r : ℤ), by exact_mod_cast (by omega : q = 2 * r)⟩
    exact dvd_trans h2q h6
  exact (Int.not_even_iff_odd.mpr hX) (even_iff_two_dvd.mpr h7)

theorem card_statedOmega_plus_eq_of_two_le {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    (hq : 4 ≤ Nat.card K) (hm : 2 ≤ m) :
    (Nat.card ↥(StatedOmega (StatedQuadPlus m K)) : ℤ) =
      (Nat.card K : ℤ) ^ (m * (m - 1)) * ((Nat.card K : ℤ) ^ m - 1) *
        ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
  rcases (show m = 2 ∨ 3 ≤ m by omega) with rfl | h3
  · obtain ⟨e⟩ := statedOmega_plus_four_nonempty_equiv K hq
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, CFSG.Open.StatedAPI.card_statedSL_two]
    have : 1 ≤ Nat.card K ^ 2 := Nat.one_le_pow _ _ Nat.card_pos
    simp only [Nat.reduceSub, Finset.Icc_self, Finset.prod_singleton]
    push_cast [Nat.cast_sub this]
    ring
  · exact card_statedOmega_plus_eq h3

theorem orth_card_plus_ne_minus_of_two_le {K K' : Type} [Field K] [Finite K] [CharP K 2]
    [Field K'] [Finite K'] [CharP K' 2] (hKK : Nat.card K' = Nat.card K) (hq : 4 ≤ Nat.card K)
    {m : ℕ} (hm : 2 ≤ m) {b c : K'} (hirr : ∀ s : K', s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(StatedOmega (StatedQuadPlus m K)) ≠
      Nat.card ↥(StatedOmega (StatedQuadMinus m K' b c)) := by
  intro h
  have h1 := card_statedOmega_plus_eq_of_two_le (K := K) hq hm
  have h2 := card_statedOmega_minus_eq_of_two_le (K := K') (m := m) hm hirr
  rw [hKK] at h2
  have h3 : ((Nat.card ↥(StatedOmega (StatedQuadPlus m K)) : ℕ) : ℤ) =
      ((Nat.card ↥(StatedOmega (StatedQuadMinus m K' b c)) : ℕ) : ℤ) := by rw [h]
  rw [h1, h2] at h3
  have hq0 : (1 : ℤ) < (Nat.card K : ℤ) := by exact_mod_cast (show 1 < Nat.card K by omega)
  have hP : 0 < ∏ i ∈ Finset.Icc 1 (m - 1), ((Nat.card K : ℤ) ^ (2 * i) - 1) := by
    apply Finset.prod_pos
    intro i hi
    have hi1 : 1 ≤ i := (Finset.mem_Icc.mp hi).1
    have : (1 : ℤ) < (Nat.card K : ℤ) ^ (2 * i) := one_lt_pow₀ hq0 (by omega)
    omega
  have hpow : 0 < (Nat.card K : ℤ) ^ (m * (m - 1)) :=
    pow_pos (by omega : (0 : ℤ) < (Nat.card K : ℤ)) _
  have h4 := mul_right_cancel₀ hP.ne' h3
  have h5 := mul_left_cancel₀ hpow.ne' h4
  omega

end Arith

section Natural

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem orth_e2Natural_minus_of_two_le (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hc : Ctx M Q Z B) {t : G} {m : ℕ} (hs : Sec5Hyp hc (2 * m) t) (hm : 2 ≤ m)
    (hE : CaseE2Minus M Q Z B t m) :
    OmegaMinusNat hc t m := by
  classical
  obtain ⟨-, -, hNt, ⟨hNn, KE, hFE, hFinE, hKE, bE, cE, hirrE, ⟨e⟩⟩, -⟩ := hE
  haveI := hNn
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  haveI : CharP KE 2 := charP_two_of_card_eq_two_pow (hKE.trans hZ2)
  have hq4 : 4 ≤ Nat.card KE := by rw [hKE]; exact hc.hyp.q4
  obtain ⟨hsimple, -, hodd⟩ := endg_omegaMinus_facts hq4 hm hirrE
  haveI := hsimple
  have hqe : Even (Nat.card KE) := orth_even_card KE
  have hY2 : ¬ IsPGroup 2 ↥(StatedOmega (StatedQuadMinus m KE bE cE)) :=
    orth_not_pgroup_of_dvd hqe (by omega) hodd
  have hcore := orth_e2_core h34 h310 hc hs hNt hY2 e
  have hqZ : Even (Nat.card Z : ℤ) := by
    rw [← hKE]; exact orth_even_card_int KE
  have hq0 : (Nat.card Z : ℤ) ≠ 0 := by have := hc.hyp.q4; omega
  obtain ⟨XE, hXE, hYE⟩ := orth_card_omegaMinus_form (K := KE) hm hirrE
  rw [hKE] at hYE
  rcases hcore with ⟨K, fK, finK, k, hKq, hk, hdim, hcard⟩ | ⟨K, fK, finK, k, hKq, hk, hcard⟩ |
    ⟨K, fK, finK, k, hKq, hk, hnat, hcard⟩ | ⟨K, fK, finK, k, b, c, hKq, hk, hirr, hnat, hcard⟩
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    refine orth_sl_exp_false_of_two_le (q := Nat.card Z) ?_ (by have := hc.hyp.q4; omega) hm
      hdim (Y := Nat.card ↥(StatedOmega (StatedQuadMinus m KE bE cE))) hXE ?_ ?_
    · rw [← hKE]; exact orth_even_card KE
    · exact_mod_cast hYE
    · rw [← hcard, ← hKq]
      exact orth_dvd_card_statedSL (by omega)
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    obtain ⟨X', hX', hY'⟩ := orth_card_sp_form (K := K) k
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedSp k K) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadMinus m KE bE cE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    exact orth_sp_exp_ne hqZ hq0 hm hX' hXE h1
  · exfalso
    haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    have hq4K : 4 ≤ Nat.card K := by rw [hKq]; exact hc.hyp.q4
    obtain ⟨X', hX', hY'⟩ := orth_card_omegaPlus_form hq4K hk
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedOmega (StatedQuadPlus k K)) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadMinus m KE bE cE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    have hkm : k = m := orth_omega_exp_eq hqZ hq0 (by omega) (by omega) hX' hXE h1
    subst hkm
    exact orth_card_plus_ne_minus_of_two_le (K := K) (K' := KE) (hKE.trans hKq.symm) hq4K hm
      hirrE hcard
  · haveI : CharP K 2 := charP_two_of_card_eq_two_pow (hKq.trans hZ2)
    obtain ⟨X', hX', hY'⟩ := orth_card_omegaMinus_form (K := K) hk hirr
    rw [hKq] at hY'
    have h1 : (Nat.card ↥(StatedOmega (StatedQuadMinus k K b c)) : ℤ) =
        (Nat.card ↥(StatedOmega (StatedQuadMinus m KE bE cE)) : ℤ) := by rw [hcard]
    rw [hY', hYE] at h1
    have hkm : k = m := orth_omega_exp_eq hqZ hq0 (by omega) (by omega) hX' hXE h1
    subst hkm
    exact ⟨K, fK, finK, hKq, b, c, hirr, hnat⟩

end Natural

section Tensor

open CFSG.ClassicalGroups.Orthogonal (eichler)

theorem smith24E2Minus_tensorB_of_two_le (h34 : Stroth34Statement)
    {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G} {t : G} {m : ℕ}
    (hcfg : SmithOrthCfg M Q Z B) (ht : CtxD4 M Q Z B t) (hm : 2 ≤ m)
    (hE : CaseE2Minus M Q Z B t m) (hno : NoA2 Q Z (LB M Q B)) (hgen : GenByB M Q B)
    (hNat : OmegaMinusNat hcfg.ctx t m) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (qU : QuadraticForm K (ι → K))
        (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthPreFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)) ∧
          OrthBLine M₀ qU φ B := by
  have hc : Ctx M Q Z B := hcfg.ctx
  haveI : (Q.subgroupOf M).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hc.hyp.Q_normal.2
  have hw : Width Q Z (2 * m) := by
    unfold Width
    rw [hE.2.1]
    congr 1
    ring
  have hn : 2 < 2 * m := by omega
  have htLB : t ∈ LB M Q B := ht.2.1
  have htQ : t ∉ Q := ht.2.2.1
  obtain ⟨jj, kk, hZ2, -⟩ := hc.hyp.cp
  obtain ⟨K', hF', hFin', hK'card, b, c, hirr, hnat⟩ := hNat
  haveI : CharP K' 2 := charP_two_of_card_eq_two_pow (hK'card.trans hZ2)
  have hq4 : 4 ≤ Nat.card K' := by rw [hK'card]; exact hc.hyp.q4
  have hcoe : ⇑(quadMinus m K' b c) = StatedQuadMinus m K' b c :=
    CFSG.LieType.Universal.Spin.coe_quadMinus m K' b c
  haveI : Nonempty (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have hVU := (stroth310Chi_of_34 h34 G M Q Z B hc (2 * m) t ⟨hw, hn, hno, hgen, htLB, htQ⟩
    (Or.inr ⟨K', hF', hFin', hK'card, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩)).1
  have hnat' : NaturalRep (ι := Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2) K'
      (StatedOmega ⇑(quadMinus m K' b c))
      (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t) := by rw [hcoe]; exact hnat
  have hsing : Stroth310RootStatement →
      NatSingular hc t (quadMinus m K' b c) (StatedOmega ⇑(quadMinus m K' b c)) := by
    intro hRoot
    rw [hcoe]
    exact hc.natSingular_of h34 hRoot ⟨hw, hn, hno, hgen, htLB, htQ⟩
      (Or.inr ⟨K', hF', hFin', hK'card, Or.inr ⟨m, b, c, hm, hirr, hnat⟩⟩) hK'card
      (CFSG.ClassicalGroups.Orthogonal.ElemMatrixIso.minus hm hirr)
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K' hirr)
      (by
        rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
          Fintype.card_fin, Fintype.card_fin]
        omega)
      (addCommutantScalar_statedOmegaMinus hm hirr)
  have hres := orth_tensor_glue hc hw hn hno hgen h34 htLB htQ hVU
    (quadMinus m K' b c) hK'card (by simp [Fintype.card_sum]; omega)
    (fun u hu =>
      (CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus_of_finite m K' hirr).1 u
      (fun v => by simpa [QuadraticMap.polarBilin_apply_apply] using hu v))
    (fun A hA v => mem_statedOmega_preserves (Q := quadMinus m K' b c) rfl hA v)
    (by rw [hcoe]; exact addCommutantScalar_statedOmegaMinus hm hirr)
    (fun a' w' _ _ => by
      rw [hcoe, CFSG.ClassicalGroups.Orthogonal.statedOmega_quadMinus_eq_map_of_two_le hm hirr]
      exact Subgroup.mem_map.mpr ⟨eichler (quadMinus m K' b c) a' w',
        CFSG.ClassicalGroups.Orthogonal.eichler_mem_elementaryGroup _ a' w', rfl⟩)
    (by rw [hcoe]; exact (endg_omegaMinus_facts hq4 hm hirr).1)
    (by rw [hcoe, ← hK'card]; exact card_statedSL_two_lt_omega_minus_of_two_le hm hirr hq4)
    hnat' hsing
    (P₂ := IsOmegaMinus m (Nat.card Z))
    (fun X _ ⟨K'', hK''f, hK''fin, hK''card, b'', c'', hirr'', ⟨e⟩⟩ => by
      haveI : CharP K'' 2 := charP_two_of_card_eq_two_pow (hK''card.trans hZ2)
      have h1 := card_statedOmega_minus_eq_of_two_le (K := K'') hm hirr''
      have h2 := card_statedOmega_minus_eq_of_two_le (K := K') hm hirr
      rw [hK''card] at h1
      rw [hK'card] at h2
      have h3 : (Nat.card ↥(StatedOmega (StatedQuadMinus m K'' b'' c'')) : ℤ) =
          (Nat.card ↥(StatedOmega (StatedQuadMinus m K' b c)) : ℤ) := h1.trans h2.symm
      rw [Nat.card_congr e.toEquiv, hcoe]
      exact_mod_cast h3)
    hE.2.2.2.2
  obtain ⟨K, hK, hKfin, hKchar, γ, M₀, hM, θ, φ, hpre, hact, hsl, heich, u, hu0, hline, hsu⟩ := hres
  exact ⟨K, hK, hKfin, hKchar, γ, M₀, hM, Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2, inferInstance,
    inferInstance, qTransport θ (quadMinus m K' b c), φ, hpre, ⟨hact, hsl, heich⟩,
    OrthBLine.of_pure hu0 hline hsu⟩

end Tensor

section Two

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
  {t : G}

theorem orth_e2Natural_minus_two (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hc : Ctx M Q Z B) (hs : Sec5Hyp hc 4 t) (hE : CaseE2Minus M Q Z B t 2) :
    OmegaMinusNat hc t 2 :=
  orth_e2Natural_minus_of_two_le h34 h310 hc (m := 2) hs le_rfl hE

theorem smith24E2MinusTwo_tensorB (h34 : Stroth34Statement) (hcfg : SmithOrthCfg M Q Z B)
    (ht : CtxD4 M Q Z B t) (hE : CaseE2Minus M Q Z B t 2) (hno : NoA2 Q Z (LB M Q B))
    (hgen : GenByB M Q B) (hNat : OmegaMinusNat hcfg.ctx t 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (qU : QuadraticForm K (ι → K))
        (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthPreFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)) ∧
          OrthBLine M₀ qU φ B :=
  smith24E2Minus_tensorB_of_two_le h34 hcfg ht (m := 2) le_rfl hE hno hgen hNat

theorem smith24ActE2MinusTwo_of (h34 : Stroth34Statement) (h310 : Stroth310Statement)
    (hG : StrothGenByBStatement) (hc : SmithOrthCfg M Q Z B) (ht : CtxD4 M Q Z B t)
    (hE : CaseE2Minus M Q Z B t 2) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : CharP K 2) (γ : G → K)
      (M₀ : Tim79.QuadModel Q Z K γ), GlobalModelData M Q Z γ M₀ ∧
      ∃ (ι : Type) (_ : Fintype ι) (_ : DecidableEq ι) (qU : QuadraticForm K (ι → K))
        (φ : M₀.E ≃ₗ[K] (ι → K) × (ι → K)),
        OrthFrame Q Z M₀ qU φ ∧ OrthAct Q Z M₀ qU φ (Lgen M (LB M Q B)) := by
  have hE' : CaseE2 M Q Z B t 2 := (caseE2_iff M Q Z B t 2).mpr (Or.inr hE)
  have hT := orthTacit_of_caseE2 hc.toCfg hE' hG
  obtain ⟨hno, hgen⟩ := hT B hc.ctx
  have hs : Sec5Hyp hc.ctx 4 t := ⟨CaseE2.width hE', by omega, hno, hgen, ht.2.1, ht.2.2.1⟩
  obtain ⟨K, _, _, _, γ, M₀, hD, ι, _, _, qU, φ, hF, hAct, c, u, hc0, hu0, hBimg, -⟩ :=
    smith24E2MinusTwo_tensorB h34 hc ht hE hno hgen (orth_e2Natural_minus_two h34 h310 hc.ctx hs hE)
  refine ⟨K, inferInstance, inferInstance, inferInstance, γ, M₀, hD, ι, inferInstance,
    inferInstance, qU, φ, ?_, hAct⟩
  have hn : 4 ≤ Fintype.card ι := by
    obtain ⟨n, hw', -, h4⟩ := hc.orth.exists_width
    have hZ : 2 ≤ Nat.card Z := by have := hc.ctx.hyp.q4; omega
    rw [width_eq_of_width hZ (width_of_tensor hD φ) hw']
    exact h4
  exact orthFrame_of_tensor hc.ctx (fun C hC => exists_mem_M_eq_conj_of_tacit h34 hc hT hC)
    (fun C hC => (hT C hC).1) hD hF hAct (slPart_normal_minus hc.ctx hE hD hAct) hn hc0 hu0 hBimg

end Two




end CFSG.RankThree.GF2n.Smith81

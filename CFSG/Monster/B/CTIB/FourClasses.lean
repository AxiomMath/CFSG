module

public import CFSG.Monster.B.CTIB.Fusion
public import CFSG.Monster.B.Co2Catalog
public import CFSG.Monster.B.Cbar.SylowTwo
public import CFSG.Monster.B.Final.Assembly
public import CFSG.Sporadic.Co2Inv
public import Certificates.Certificate3011
public import Certificates.Certificate3012
public import Certificates.Certificate3014
public import Certificates.Certificate3017
public import Certificates.Certificate3019
public import Certificates.Certificate3025
public import Certificates.Certificate3026
public import Certificates.Certificate3028
public import Certificates.Certificate3045
public import Certificates.Certificate3048
public import Certificates.Certificate3049
public import Certificates.Certificate3050
public import Certificates.Certificate3051
public import Certificates.Certificate3098
public import Certificates.Certificate3099
public import Certificates.Certificate3100
public import Certificates.Certificate3101
public import Certificates.Certificate3102
public import Certificates.Certificate3103
public import Certificates.Certificate3106
public import Certificates.Certificate3107
public import Certificates.Certificate3108
public import Certificates.Certificate3109
public import Certificates.Certificate3110
public import Certificates.Certificate3111
public import Certificates.Certificate3114
public import Certificates.Certificate3115
public import Certificates.Certificate3116
public import Certificates.Certificate3117
public import Certificates.Certificate3118
public import Certificates.Certificate3027
public import CFSG.Certificates.InvariantMerge

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.CTIB

open MulOpposite CFSG.Blueprint CFSG.Monster.B CFSG.Monster.B.Bin Native Matrix
  CFSG.Monster.B.Short CFSG.Monster.SpinLattice CFSG.Monster.Griess CFSG.Monster.B.TwoA
  CFSG.Monster.B.Co2Catalog
open CFSG.Monster.B.Co2 (v0)
open CFSG.Sporadic.Co2Inv (Co2InvolutionInput co2_involution_input)

local notation "MatB" => Matrix (Fin 4370) (Fin 4370) (ZMod 2)
local notation "βr" s => ((betaRow Dyadic.betaS s : MatBˣ) : MatB)

theorem rank_conj_sub_one {m : ℕ} {A P B : Matrix (Fin m) (Fin m) (ZMod 2)} (hAB : A * B = 1) :
    (A * P * B - 1).rank = (P - 1).rank := by
  have e : A * P * B - 1 = A * (P - 1) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]
  rw [e, Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnit_det_of_left_inverse hAB),
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (Matrix.isUnit_det_of_right_inverse hAB)]

theorem rank_inv_transpose {m : ℕ} {N : Matrix (Fin m) (Fin m) (ZMod 2)} (hN : IsUnit N.det) :
    ((N⁻¹)ᵀ - 1).rank = (N - 1).rank := by
  have e1 : (N⁻¹)ᵀ - 1 = (N⁻¹ - 1)ᵀ := by rw [Matrix.transpose_sub, Matrix.transpose_one]
  have e2 : N⁻¹ - 1 = N⁻¹ * -(N - 1) := by
    rw [Matrix.mul_neg, Matrix.mul_sub, Matrix.mul_one, Matrix.nonsing_inv_mul _ hN, neg_sub]
  rw [e1, Matrix.rank_transpose, e2, Matrix.rank_mul_eq_right_of_isUnit_det _ _
    (Matrix.isUnit_det_of_right_inverse (Matrix.nonsing_inv_mul _ hN)), ZModModule.neg_eq_self]

theorem rank_kvMat_sub_one {v : L2} (B : Module.Basis (Fin 22) (ZMod 2) (Wv v)) (k : Kstab v) :
    (kvMat B k - 1).rank = Module.finrank (ZMod 2) (LinearMap.range (wAct v k - 1)) := by
  have e : kvMat B k - 1 = (LinearMap.toMatrix B B (wAct v k - 1))ᵀ := by
    ext i j
    rw [Matrix.transpose_apply, LinearMap.toMatrix_apply, LinearMap.sub_apply,
      Module.End.one_apply, map_sub, Finsupp.sub_apply, Module.Basis.repr_self, Matrix.sub_apply,
      kvMat_apply, Matrix.one_apply, Finsupp.single_apply]
  rw [e, Matrix.rank_transpose, Matrix.rank_eq_finrank_range_toLin _ B B, Matrix.toLin_toMatrix]

theorem finrank_wAct_congr {a b : L2} (h : a = b) (k : Kstab a) (k' : Kstab b)
    (hk : k.1 = k'.1) :
    Module.finrank (ZMod 2) (LinearMap.range (wAct b k' - 1)) =
      Module.finrank (ZMod 2) (LinearMap.range (wAct a k - 1)) := by
  subst h
  rw [show k' = k from Subtype.ext hk.symm]

abbrev KS : Type := Kstab (phi0 (coordOf rStar))

@[expose] noncomputable def rkW (k : KS) : ℕ :=
  Module.finrank (ZMod 2) (LinearMap.range (wAct _ k - 1))

@[expose] noncomputable def psiCo2 :
    KS ≃* NativeSporadic.Co2 :=
  (MulEquiv.subgroupCongr Kstab_rStar_eq).trans co2CatalogEquiv

theorem rank_co2
    (k : Kstab v0) :
    ((co2CatalogEquiv k).val.val - 1).rank = (kvM k - 1).rank := by
  rw [co2CatalogEquiv_val]
  have hC := (Matrix.isUnit_iff_isUnit_det _).1 isUnit_bridgeC
  have hM : IsUnit (kvM k).det := by
    have : IsUnit (kvM k) := by
      rw [kvM, ← coe_kvGL]
      exact Units.isUnit _
    exact (Matrix.isUnit_iff_isUnit_det _).1 this
  have hN : IsUnit (bridgeC⁻¹ * kvM k * bridgeC).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact ((Matrix.isUnit_det_of_right_inverse (Matrix.nonsing_inv_mul _ hC)).mul hM).mul hC
  rw [rank_inv_transpose hN, rank_conj_sub_one (Matrix.nonsing_inv_mul _ hC)]

theorem rank_psiCo2
    (k : KS) : ((psiCo2 k).val.val - 1).rank = rkW k := by
  rw [psiCo2, MulEquiv.trans_apply, rank_co2, kvM, rank_kvMat_sub_one, rkW]
  exact finrank_wAct_congr hv0 k _ rfl

theorem orderOf_two_iff {G : Type*} [Group G] {g : G} : orderOf g = 2 ↔ g * g = 1 ∧ g ≠ 1 := by
  rw [orderOf_eq_prime_iff, sq]

theorem rank_co2_conj {P Q : NativeSporadic.Co2} (h : IsConj P Q) :
    (P.val.val - 1).rank = (Q.val.val - 1).rank := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  have e : (c * P * c⁻¹).val.val = c.val.val * P.val.val * (c⁻¹).val.val := rfl
  rw [e, rank_conj_sub_one]
  show (c * c⁻¹).val.val = 1
  rw [mul_inv_cancel]
  rfl

theorem psiCo2_sq
    {k : KS} (hk : k * k = 1) : psiCo2 k * psiCo2 k = 1 := by
  rw [← map_mul, hk, map_one]

theorem psiCo2_ne_one
    {k : KS} (hk1 : k ≠ 1) : psiCo2 k ≠ 1 := by
  rw [Ne, MulEquiv.map_eq_one_iff]
  exact hk1

theorem isConj_of_psiCo2
    {k k' : KS} (h : IsConj (psiCo2 k) (psiCo2 k')) : IsConj k k' := by
  obtain ⟨c, hc⟩ := isConj_iff.1 h
  refine isConj_iff.2 ⟨psiCo2.symm c, ?_⟩
  apply psiCo2.injective
  rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, hc]

theorem kv_rank_cases
    (hCo2 : Co2InvolutionInput) {k : KS} (hk : k * k = 1) (hk1 : k ≠ 1) :
    rkW k = 6 ∨ rkW k = 8 ∨ rkW k = 10 := by
  obtain ⟨z, t, u, -, -, -, -, -, -, rz, rt, ru, hcov⟩ := hCo2
  rw [← rank_psiCo2]
  rcases hcov _ (psiCo2_sq hk) (psiCo2_ne_one hk1) with h | h | h
  · exact .inl (by rw [rank_co2_conj h, rz])
  · exact .inr (.inl (by rw [rank_co2_conj h, rt]))
  · exact .inr (.inr (by rw [rank_co2_conj h, ru]))

theorem kv_conj_of_rank
    (hCo2 : Co2InvolutionInput) {k k' : KS} (hk : k * k = 1) (hk1 : k ≠ 1)
    (hk' : k' * k' = 1) (hk1' : k' ≠ 1) (h : rkW k = rkW k') : IsConj k k' := by
  have hcases := kv_rank_cases hCo2 hk hk1
  obtain ⟨z, t, u, -, -, -, -, -, -, rz, rt, ru, hcov⟩ := hCo2
  have cls : ∀ P : NativeSporadic.Co2, P * P = 1 → P ≠ 1 →
      ((P.val.val - 1).rank = 6 → IsConj P z) ∧ ((P.val.val - 1).rank = 8 → IsConj P t) ∧
      ((P.val.val - 1).rank = 10 → IsConj P u) := by
    intro P hP hP1
    rcases hcov P hP hP1 with hc | hc | hc
    · refine ⟨fun _ => hc, fun hr => ?_, fun hr => ?_⟩ <;>
        rw [rank_co2_conj hc, rz] at hr <;> exact absurd hr (by decide)
    · refine ⟨fun hr => ?_, fun _ => hc, fun hr => ?_⟩ <;>
        rw [rank_co2_conj hc, rt] at hr <;> exact absurd hr (by decide)
    · refine ⟨fun hr => ?_, fun hr => ?_, fun _ => hc⟩ <;>
        rw [rank_co2_conj hc, ru] at hr <;> exact absurd hr (by decide)
  have c1 := cls _ (psiCo2_sq hk) (psiCo2_ne_one hk1)
  have c2 := cls _ (psiCo2_sq hk') (psiCo2_ne_one hk1')
  rw [rank_psiCo2] at c1 c2
  refine isConj_of_psiCo2 ?_
  rcases hcases with hr | hr | hr
  · exact (c1.1 hr).trans (c2.1 (h ▸ hr)).symm
  · exact (c1.2.1 hr).trans (c2.2.1 (h ▸ hr)).symm
  · exact (c1.2.2 hr).trans (c2.2.2 (h ▸ hr)).symm

@[expose] noncomputable def piH : Jbar.op →* KS :=
  MonoidHom.mk' (fun s => jbarToKv ⟨s.val.unop⁻¹, Jbar.inv_mem s.2⟩) fun s s' => by
    rw [← map_mul]
    exact congrArg jbarToKv (Subtype.ext (show (s.val * s'.val).unop⁻¹ = s.val.unop⁻¹ *
      s'.val.unop⁻¹ by rw [unop_mul, _root_.mul_inv_rev]))

theorem piH_apply (s : Jbar.op) : piH s = jbarToKv ⟨s.val.unop⁻¹, Jbar.inv_mem s.2⟩ := rfl

theorem piH_eq_one_iff (s : Jbar.op) : piH s = 1 ↔ s.val ∈ Qs := by
  rw [piH_apply, ← MonoidHom.mem_ker, ker_jbarToKv, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have := Ebar.inv_mem h
    rwa [inv_inv] at this
  · intro h
    exact Ebar.inv_mem h

theorem piH_surjective :
    Function.Surjective piH := by
  intro k
  obtain ⟨g, rfl⟩ := jbarToKv_surjective k
  refine ⟨⟨op g.val⁻¹, Jbar.inv_mem g.2⟩, ?_⟩
  rw [piH_apply]
  exact congrArg jbarToKv (Subtype.ext (inv_inv g.val))

theorem rkW_hs
    {k : ℕ} (hk : IsRank k) : rkW (piH ⟨hs k, hs_mem_Jbar hk⟩) = k := by
  have he : ∀ i, (fun i : Fin 22 => (eS gSeq i).unop) i ∈ Ebar :=
    fun i => eS_mem gSeq gSeq_zero_mem gSeq_mem_Jbar i
  have hM := kvMat_of_conj (fun i : Fin 22 => (eS gSeq i).unop) he
    (linearIndependent_eE betaS_explicit) (Jbar.inv_mem (hs_mem_Jbar hk)) (quotM k) (fun i => by
      have h := psiS_conj_hs hk i
      rw [psiS_of_mem (conj_mem_Qs (hs_mem_Jbar hk) (es_mem i))] at h
      simp only [psiS_es] at h
      have hA : ((hs k).unop⁻¹)⁻¹ * (eS gSeq i).unop * (hs k).unop⁻¹ =
          ((hs k)⁻¹ * es i * hs k).unop := by
        rw [inv_inv, unop_mul, unop_mul, unop_inv, mul_assoc]
        rfl
      refine (congrArg psiBar (Subtype.ext (a2 := ⟨((hs k)⁻¹ * es i * hs k).unop,
        conj_mem_Qs (hs_mem_Jbar hk) (es_mem i)⟩) hA)).trans ?_
      show psiBar _ = Multiplicative.ofAdd (∑ j, quotM k i j • Multiplicative.toAdd (psiBar (eE j)))
      rw [← h, ofAdd_toAdd])
  rw [rkW, ← rank_kvMat_sub_one (psiBasis _ he (linearIndependent_eE betaS_explicit)), piH_apply]
  rw [hM, rank_quotM hk]

theorem rkW_one : rkW 1 = 0 := by
  rw [rkW, wAct_one_eq, sub_self, LinearMap.range_zero, finrank_bot]

theorem piH_hs_sq
    {k : ℕ} (hk : IsRank k) :
    piH ⟨hs k, hs_mem_Jbar hk⟩ * piH ⟨hs k, hs_mem_Jbar hk⟩ = 1 := by
  rw [← map_mul, piH_eq_one_iff]
  show hs k * hs k ∈ Qs
  rw [hs_sq_code hk]
  exact qS_mem _

theorem piH_hs_ne_one
    {k : ℕ} (hk : IsRank k) : piH ⟨hs k, hs_mem_Jbar hk⟩ ≠ 1 := by
  intro h
  have := rkW_hs hk
  rw [h, rkW_one] at this
  rcases hk with rfl | rfl | rfl <;> simp at this

theorem isConj_of_mem_jClass {u t : Sbp} (h : u ∈ jClass t) : IsConj u t := by
  obtain ⟨g, -, rfl⟩ := h
  exact isConj_iff.2 ⟨g, by group⟩

theorem coset_cover
    {k : ℕ} (hk : IsRank k) {t : Sbp} (ht : t ∈ cosetInv k) :
    ∃ i < 14, IsConj t (rs i) := by
  have hc := native_three_coset_involution_cover
  have conv : ∀ {S : Finset ℕ}, (∀ i ∈ S, i < 14) → (∃ g ∈ Jbar.op, ∃ i ∈ S, g⁻¹ * t * g = rs i) →
      ∃ i < 14, IsConj t (rs i) := by
    rintro S hS ⟨g, -, i, hi, e⟩
    exact ⟨i, hS i hi, isConj_iff.2 ⟨g⁻¹, by rw [inv_inv, e]⟩⟩
  rcases hk with rfl | rfl | rfl
  · exact conv (by decide) (hc.1 t ht)
  · exact conv (by decide) (hc.2.1 t ht)
  · exact conv (by decide) (hc.2.2.1 t ht)

theorem noncore_cover
    (hCo2 : Co2InvolutionInput) {t : Sbp} (htJ : t.unop ∈ Jbar)
    (ht : t * t = 1) (hq : t ∉ Qs) : ∃ i < 14, IsConj t (rs i) := by
  set kt := piH ⟨t, htJ⟩ with hkt
  have hk2 : kt * kt = 1 := by
    rw [hkt, ← map_mul, ← map_one piH]
    congr 1
    exact Subtype.ext ht
  have hk1 : kt ≠ 1 := fun h => hq ((piH_eq_one_iff _).1 h)
  have main : ∀ r, IsRank r → rkW kt = r → ∃ i < 14, IsConj t (rs i) := by
    intro r hr hrk
    have hc := kv_conj_of_rank hCo2 hk2 hk1 (piH_hs_sq hr) (piH_hs_ne_one hr)
      (by rw [hrk, rkW_hs hr])
    obtain ⟨c, hc⟩ := isConj_iff.1 hc
    obtain ⟨g, rfl⟩ := piH_surjective c
    set u : Sbp := g.val * t * g.val⁻¹ with hu
    have huJ : u.unop ∈ Jbar := (Jbar.op.mul_mem (Jbar.op.mul_mem g.2 htJ) (Jbar.op.inv_mem g.2))
    have hpu : piH ⟨u, huJ⟩ = piH ⟨hs r, hs_mem_Jbar hr⟩ := by
      rw [← hc, hkt, ← map_inv, ← map_mul, ← map_mul]
      rfl
    have hq' : (hs r)⁻¹ * u ∈ Qs := by
      have h1 : piH (⟨hs r, hs_mem_Jbar hr⟩⁻¹ * ⟨u, huJ⟩) = 1 := by
        rw [map_mul, hpu, ← map_mul, inv_mul_cancel, map_one]
      exact (piH_eq_one_iff _).1 h1
    have hmem : u ∈ cosetInv r := by
      refine ⟨⟨(hs r)⁻¹ * u, hq', by group⟩, ?_⟩
      rw [hu]
      calc g.val * t * g.val⁻¹ * (g.val * t * g.val⁻¹) = g.val * (t * t) * g.val⁻¹ := by group
        _ = 1 := by rw [ht]; group
    obtain ⟨i, hi, hci⟩ := coset_cover hr hmem
    exact ⟨i, hi, (isConj_iff.2 ⟨g.val, rfl⟩).trans hci⟩
  rcases kv_rank_cases hCo2 hk2 hk1 with h | h | h
  · exact main 6 (.inl rfl) h
  · exact main 8 (.inr (.inl rfl)) h
  · exact main 10 (.inr (.inr rfl)) h

theorem cover_fourteen
    (hCo2 : Co2InvolutionInput) {t : Sbp} (ht : t * t = 1) (ht1 : t ≠ 1) :
    ∃ i < 14, IsConj t (rs i) := by
  obtain ⟨c, hc⟩ := short_centralizer_quotient_sylow_two.2.2.2.2.2.1 t.unop
    ⟨1, by rw [pow_one, sq, ← unop_mul, ht, unop_one]⟩
  set t' : Sbp := (op c)⁻¹ * t * op c with ht'
  have ht'J : t'.unop ∈ Jbar := by
    rw [ht', unop_mul, unop_mul, unop_inv, unop_op, ← mul_assoc]
    exact hc
  have hconj : IsConj t t' := isConj_iff.2 ⟨(op c)⁻¹, by rw [inv_inv]⟩
  have ht'sq : t' * t' = 1 := by
    rw [ht']
    calc (op c)⁻¹ * t * op c * ((op c)⁻¹ * t * op c) = (op c)⁻¹ * (t * t) * op c := by group
      _ = 1 := by rw [ht]; group
  have ht'1 : t' ≠ 1 := by
    intro h
    apply ht1
    calc t = op c * ((op c)⁻¹ * t * op c) * (op c)⁻¹ := by group
      _ = 1 := by rw [← ht', h]; group
  suffices h : ∃ i < 14, IsConj t' (rs i) by
    obtain ⟨i, hi, h⟩ := h
    exact ⟨i, hi, hconj.trans h⟩
  by_cases hq : t' ∈ Qs
  · have hmem : t' ∈ {t | t ∈ Qs ∧ t * t = 1 ∧ t ≠ 1} := ⟨hq, ht'sq, ht'1⟩
    rw [invs_eq] at hmem
    rcases hmem with ((h | h) | h) | h
    · exact ⟨0, by norm_num, isConj_of_mem_jClass h⟩
    · exact ⟨1, by norm_num, isConj_of_mem_jClass h⟩
    · exact ⟨2, by norm_num, isConj_of_mem_jClass h⟩
    · exact ⟨3, by norm_num, isConj_of_mem_jClass h⟩
  · exact noncore_cover hCo2 ht'J ht'sq hq

theorem fusion_conj_at
    (j : ℕ) (hj : j < 10) :
    IsConj (rs (globalFusion[j]'(by simpa [globalFusion] using hj)).1)
      (rs (globalFusion[j]'(by simpa [globalFusion] using hj)).2.1) :=
  fusion_conj (List.getElem_mem _)

theorem reduce_four
    {i : ℕ} (hi : i < 14) : ∃ j ∈ [1, 0, 5, 3], IsConj (rs i) (rs j) := by
  interval_cases i
  · exact ⟨0, by simp, IsConj.refl _⟩
  · exact ⟨1, by simp, IsConj.refl _⟩
  · exact ⟨0, by simp, fusion_conj_at 0 (by norm_num)⟩
  · exact ⟨3, by simp, IsConj.refl _⟩
  · exact ⟨3, by simp, fusion_conj_at 1 (by norm_num)⟩
  · exact ⟨5, by simp, IsConj.refl _⟩
  · exact ⟨1, by simp, fusion_conj_at 2 (by norm_num)⟩
  · exact ⟨0, by simp, fusion_conj_at 3 (by norm_num)⟩
  · exact ⟨3, by simp, fusion_conj_at 4 (by norm_num)⟩
  · exact ⟨3, by simp, fusion_conj_at 5 (by norm_num)⟩
  · exact ⟨3, by simp, fusion_conj_at 6 (by norm_num)⟩
  · exact ⟨0, by simp, fusion_conj_at 7 (by norm_num)⟩
  · exact ⟨3, by simp, fusion_conj_at 8 (by norm_num)⟩
  · exact ⟨5, by simp, fusion_conj_at 9 (by norm_num)⟩

theorem rank_beta_conj
    {a b : Sbp} (h : IsConj a b) : ((βr a) - 1).rank = ((βr b) - 1).rank := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 h
  rw [map_mul, map_mul, map_inv, Units.val_mul, Units.val_mul, rank_conj_sub_one]
  rw [← Units.val_mul, mul_inv_cancel, Units.val_one]

theorem rank_four :
    ((βr (rs 1)) - 1).rank = 1860 ∧ ((βr (rs 0)) - 1).rank = 2048 ∧
    ((βr (rs 5)) - 1).rank = 2158 ∧ ((βr (rs 3)) - 1).rank = 2168 :=
  ⟨rank_rs (i := 1) (by norm_num), rank_rs (i := 0) (by norm_num), rank_rs (i := 5) (by norm_num),
    rank_rs (i := 3) (by norm_num)⟩

theorem eq_of_conj_four
    {i j : ℕ} (hi : i ∈ [1, 0, 5, 3]) (hj : j ∈ [1, 0, 5, 3])
    (h : IsConj (rs i) (rs j)) : i = j := by
  have e := rank_beta_conj h
  obtain ⟨h1, h0, h5, h3⟩ := rank_four
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi hj
  rcases hi with rfl | rfl | rfl | rfl <;> rcases hj with rfl | rfl | rfl | rfl <;> omega

theorem four_classes
    (hCo2 : Co2InvolutionInput) {t : Sbp} (ht : orderOf t = 2) :
    ∃! i, i ∈ [1, 0, 5, 3] ∧ IsConj t (rs i) := by
  obtain ⟨hsq, h1⟩ := orderOf_two_iff.1 ht
  obtain ⟨i, hi, hti⟩ := cover_fourteen hCo2 hsq h1
  obtain ⟨j, hj, hij⟩ := reduce_four hi
  refine ⟨j, ⟨hj, hti.trans hij⟩, fun j' ⟨hj', hcj'⟩ => ?_⟩
  exact eq_of_conj_four hj' hj (hcj'.symm.trans (hti.trans hij))

theorem iotaS_surjective :
    Function.Surjective iotaS :=
  iota_surjective Dyadic.betaS betaS_explicit.injective gSeq betaS_explicit.gen gSeq_last
    gSeq_zero_mem gSeq_mem_Jbar iotaS iotaS_beta

@[expose] noncomputable def iotaEquiv :
    NativeSporadic.B ≃* Sbp :=
  MulEquiv.ofBijective iotaS ⟨iotaS_spec.1, iotaS_surjective⟩

theorem iotaEquiv_apply
    (X : NativeSporadic.B) : iotaEquiv X = iotaS X := rfl

theorem rank_iotaEquiv_symm
    (s : Sbp) :
    ((iotaEquiv.symm s).val.val - 1).rank = ((βr s) - 1).rank := by
  have e := iotaS_beta (iotaEquiv.symm s)
  rw [← iotaEquiv_apply, MulEquiv.apply_symm_apply] at e
  rw [e, rank_conj_sub_one Tmat_mul_inv]
  rfl

theorem four_classes_B
    (hCo2 : Co2InvolutionInput) {X : NativeSporadic.B} (hX : orderOf X = 2) :
    ∃! i, i ∈ [1, 0, 5, 3] ∧ IsConj X (iotaEquiv.symm (rs i)) := by
  obtain ⟨hX2, hX1⟩ := orderOf_two_iff.1 hX
  have hX' : orderOf (iotaEquiv X) = 2 := by
    refine orderOf_two_iff.2 ⟨by rw [← map_mul, hX2, map_one], ?_⟩
    rw [Ne, MulEquiv.map_eq_one_iff]
    exact hX1
  obtain ⟨i, ⟨hi, hc⟩, huniq⟩ := four_classes hCo2 hX'
  have back : ∀ j, IsConj X (iotaEquiv.symm (rs j)) ↔ IsConj (iotaEquiv X) (rs j) := by
    intro j
    constructor
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      refine isConj_iff.2 ⟨iotaEquiv c, ?_⟩
      rw [← map_inv, ← map_mul, ← map_mul, hc, MulEquiv.apply_symm_apply]
    · intro h
      obtain ⟨c, hc⟩ := isConj_iff.1 h
      refine isConj_iff.2 ⟨iotaEquiv.symm c, ?_⟩
      apply iotaEquiv.injective
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply, hc]
  refine ⟨i, ⟨hi, (back i).2 hc⟩, fun j ⟨hj, hcj⟩ => huniq j ⟨hj, (back j).1 hcj⟩⟩

theorem native_four_involution_classes :
    (∀ t : Sbp, orderOf t = 2 → ∃! i, i ∈ [1, 0, 5, 3] ∧ IsConj t (rs i)) ∧
    ((βr (rs 1)) - 1).rank = 1860 ∧ ((βr (rs 0)) - 1).rank = 2048 ∧
    ((βr (rs 5)) - 1).rank = 2158 ∧ ((βr (rs 3)) - 1).rank = 2168 ∧
    (List.range 14).map (fun i => ((βr (rs i)) - 1).rank) =
      [2048, 1860, 2048, 2168, 2168, 2158, 1860, 2048, 2168, 2168, 2168, 2048, 2168, 2158] ∧
    globalFusion.map (fun f => (f.1, f.2.1)) =
      [(2, 0), (4, 3), (6, 1), (7, 0), (8, 3), (9, 3), (10, 3), (11, 0), (12, 3), (13, 5)] ∧
    globalFusion.map (·.2.2.1) = [5, 35, 3, 5, 27, 39, 17, 5, 21, 35] ∧
    (∀ f ∈ globalFusion, Odd f.2.2.1 ∧
      (rs f.2.1 * (wordS' f.2.2.2)⁻¹ * rs f.1 * wordS' f.2.2.2) ^ f.2.2.1 = 1 ∧
      IsConj (rs f.1) (rs f.2.1)) ∧
    (∀ X : NativeSporadic.B, orderOf X = 2 →
      ∃! i, i ∈ [1, 0, 5, 3] ∧ IsConj X (iotaEquiv.symm (rs i))) ∧
    (∀ X : NativeSporadic.B, iotaEquiv X = iotaS X) ∧
    ((iotaEquiv.symm (rs 1)).val.val - 1).rank = 1860 ∧
    ((iotaEquiv.symm (rs 0)).val.val - 1).rank = 2048 ∧
    ((iotaEquiv.symm (rs 5)).val.val - 1).rank = 2158 ∧
    ((iotaEquiv.symm (rs 3)).val.val - 1).rank = 2168 := by
  have hCo2 : Co2InvolutionInput := co2_involution_input
  obtain ⟨r1, r0, r5, r3⟩ := rank_four
  refine ⟨fun t ht => four_classes hCo2 ht, r1, r0, r5, r3, ?_, globalFusion_pairs,
    globalFusion_exps, fun f hf => ⟨(globalFusion_ok f hf).2.2.1, fusion_eq hf, fusion_conj hf⟩,
    fun X hX => four_classes_B hCo2 hX, iotaEquiv_apply, ?_, ?_, ?_, ?_⟩
  · have : ∀ i ∈ List.range 14, ((βr (rs i)) - 1).rank = repRanks.getD i 0 :=
      fun i hi => rank_rs (List.mem_range.1 hi)
    rw [List.map_congr_left this]
    rfl
  · rw [rank_iotaEquiv_symm, r1]
  · rw [rank_iotaEquiv_symm, r0]
  · rw [rank_iotaEquiv_symm, r5]
  · rw [rank_iotaEquiv_symm, r3]

end CFSG.Monster.B.CTIB

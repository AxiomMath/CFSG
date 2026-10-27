module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflQuotient
public import CFSG.Fischer.Classification.Orthogonal3.Model
public import CFSG.Fischer.Classification.PartIII.Beta.Forms
import CFSG.LocalAnalysis.StandardType.ZS.DThreeTernaryChain

public section

namespace CFSG.StandardType.ZS

open CFSG.Fischer.Classification

variable {U : Type} [AddCommGroup U] [Module (ZMod 3) U] [Module.Finite (ZMod 3) U]
  {A : Subgroup (U ≃ₗ[ZMod 3] U)}

theorem diagF3_apply_single_castSucc (n : ℕ) (x : Fin (n + 1) → ZMod 3) (j : Fin n) :
    diagF3 (n + 1) 2 x (Pi.single j.castSucc 1) = x j.castSucc := by
  rw [diagF3_apply, Finset.sum_eq_single j.castSucc]
  · rw [Pi.single_eq_same, mul_one, diagF3Entry,
      if_neg (by rw [Fin.val_castSucc]; omega), one_mul]
  · intro k _ hk
    rw [Pi.single_eq_of_ne hk, mul_zero]
  · intro h
    exact absurd (Finset.mem_univ j.castSucc) h

theorem diagF3_single_castSucc (n : ℕ) (i j : Fin n) :
    diagF3 (n + 1) 2 (Pi.single i.castSucc 1) (Pi.single j.castSucc 1) =
      if i = j then 1 else 0 := by
  rw [diagF3_apply_single_castSucc]
  by_cases hij : i = j
  · subst hij
    rw [Pi.single_eq_same, if_pos rfl]
  · rw [Pi.single_eq_of_ne (fun h => hij (Fin.castSucc_injective n h.symm)), if_neg hij]

private theorem zzh_sum_castSucc_single {n : ℕ} (w : Fin (n + 1) → ZMod 3)
    (hwl : w (Fin.last n) = 0) :
    (∑ i : Fin n, Pi.single i.castSucc (w i.castSucc)) = w := by
  funext k
  induction k using Fin.lastCases with
  | last =>
    simp only [Finset.sum_apply, Pi.single_eq_of_ne (Fin.castSucc_lt_last _).ne', hwl,
      Finset.sum_const_zero]
  | cast j =>
    simp only [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro i _ hij
      rw [Pi.single_eq_of_ne (fun h => hij (Fin.castSucc_injective n h.symm))]
    · intro h
      exact absurd (Finset.mem_univ j) h

omit [Module.Finite (ZMod 3) U] in
private theorem zzh_prod_apply_ofFn {n : ℕ} {B : LinearMap.BilinForm (ZMod 3) U}
    {u : Fin n → U} (hu : ∀ i j, B (u i) (u j) = if i = j then 1 else 0)
    {q : Fin n → U ≃ₗ[ZMod 3] U} (hq : ∀ i x, q i x = x + B x (u i) • u i) (x : U) :
    (List.ofFn q).prod x = x + ∑ i, B x (u i) • u i := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.prod_cons, LinearEquiv.mul_apply]
    have htail := ih (u := fun i : Fin n => u i.succ) (q := fun i : Fin n => q i.succ)
      (fun i j => by simpa [Fin.succ_inj] using hu i.succ j.succ) (fun i y => hq i.succ y)
    rw [htail, hq 0]
    have hsum : B (∑ i : Fin n, B x (u i.succ) • u i.succ) (u 0) = 0 := by
      rw [LinearMap.BilinForm.sum_left]
      refine Finset.sum_eq_zero fun i _ => ?_
      rw [LinearMap.BilinForm.smul_left, hu i.succ 0, if_neg (Fin.succ_ne_zero i),
        mul_zero]
    rw [LinearMap.BilinForm.add_left, hsum, add_zero, Fin.sum_univ_succ]
    abel

omit [Module.Finite (ZMod 3) U] in
private theorem zzh_isRefl_of_add {B : LinearMap.BilinForm (ZMod 3) U} {u : U}
    (hu : B u u = 1) {q : U ≃ₗ[ZMod 3] U} (hq : ∀ x, q x = x + B x u • u) :
    IsRefl 3 q := by
  constructor
  · apply LinearEquiv.ext
    intro x
    rw [LinearEquiv.mul_apply, hq (q x), hq x]
    rw [LinearMap.BilinForm.add_left, LinearMap.BilinForm.smul_left, hu, mul_one, add_smul]
    have hcoef : B x u + (B x u + B x u) = 0 := by
      have h : ∀ c : ZMod 3, c + (c + c) = 0 := by decide
      exact h (B x u)
    calc
      (x + B x u • u) + (B x u • u + B x u • u)
          = x + (B x u + (B x u + B x u)) • u := by
            rw [add_smul, add_smul]
            abel
      _ = x + (0 : ZMod 3) • u := by rw [hcoef]
      _ = x := by rw [zero_smul, add_zero]
  · have hrange : LinearMap.range ((q : U →ₗ[ZMod 3] U) - (LinearMap.id : U →ₗ[ZMod 3] U)) =
        Submodule.span (ZMod 3) {u} := by
      apply le_antisymm
      · rintro _ ⟨y, rfl⟩
        have hy : ((q : U →ₗ[ZMod 3] U) - (LinearMap.id : U →ₗ[ZMod 3] U)) y = B y u • u := by
          simp [LinearMap.sub_apply, hq y]
        rw [hy]
        exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
      · rw [Submodule.span_singleton_le_iff_mem]
        refine ⟨u, ?_⟩
        have hqu : (q : U →ₗ[ZMod 3] U) u = u + u := by
          have h := hq u
          rw [hu, one_smul] at h
          simpa using h
        rw [LinearMap.sub_apply, LinearMap.id_apply, hqu]
        abel
    rw [hrange, finrank_span_singleton]
    intro h
    rw [h] at hu
    simp at hu

private theorem zzh_eq_zero_of_eq_neg {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {x : V} (h : x = -x) : x = 0 := by
  have h2 : (2 : ZMod 3) • x = 0 := by
    rw [two_smul]
    nth_rewrite 1 [h]
    rw [neg_add_cancel]
  calc x = ((2 : ZMod 3) * 2) • x := by
        rw [show (2 : ZMod 3) * 2 = 1 by decide, one_smul]
    _ = (2 : ZMod 3) • ((2 : ZMod 3) • x) := by rw [mul_smul]
    _ = 0 := by rw [h2, smul_zero]

private noncomputable def zzhF (n : ℕ) :
    LinearMap.BilinForm (ZMod 3) (Fin (n + 1) → ZMod 3) :=
  diagF3 (n + 1) 2

private noncomputable def zzhRho (n : ℕ) : F3.reflGroup (zzhF n) :=
  (List.ofFn fun i : Fin n => reflElt (zzhF n) (Pi.single i.castSucc 1)).prod

private theorem zzh_act_prod_rho {n : ℕ} {w : Fin (n + 1) → ZMod 3}
    (hwl : w (Fin.last n) = 0) :
    F3.act ((List.ofFn fun i : Fin n =>
      F3.refl (diagF3 (n + 1) 2) (Pi.single i.castSucc 1)).prod) w = -w := by
  have hunit : ∀ i : Fin n, diagF3 (n + 1) 2 (Pi.single i.castSucc 1)
      (Pi.single i.castSucc 1) = 1 := fun i => by
    rw [diagF3_single_castSucc, if_pos rfl]
  have horth : ∀ i j : Fin n, i ≠ j →
      diagF3 (n + 1) 2 (Pi.single i.castSucc 1) (Pi.single j.castSucc 1) = 0 :=
    fun i j hij => by rw [diagF3_single_castSucc, if_neg hij]
  rw [act_prod_ofFn_refl (n := n) (v := fun i : Fin n => Pi.single i.castSucc 1)
    hunit horth]
  have hsum : (∑ i : Fin n,
      diagF3 (n + 1) 2 w (Pi.single i.castSucc 1) • Pi.single i.castSucc 1) = w := by
    calc
      (∑ i : Fin n,
          diagF3 (n + 1) 2 w (Pi.single i.castSucc 1) • Pi.single i.castSucc 1)
          = ∑ i : Fin n, w i.castSucc • Pi.single i.castSucc 1 := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [diagF3_apply_single_castSucc]
      _ = ∑ i : Fin n, Pi.single i.castSucc (w i.castSucc) := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [← Pi.single_smul', smul_eq_mul, mul_one]
      _ = w := zzh_sum_castSucc_single w hwl
  rw [hsum]
  have h2 : ∀ y : Fin (n + 1) → ZMod 3, y + y = -y := by
    intro y
    funext k
    exact (show ∀ c : ZMod 3, c + c = -c by decide) (y k)
  exact h2 w

private theorem zzh_rho_comm {n : ℕ} {w : Fin (n + 1) → ZMod 3}
    (hwl : w (Fin.last n) = 0) :
    Commute (QuotientGroup.mk (zzhRho n) : R3 (zzhF n)) (reflBar (zzhF n) w) := by
  let f : LinearMap.BilinForm (ZMod 3) (Fin (n + 1) → ZMod 3) := diagF3 (n + 1) 2
  let ρ : F3.reflGroup f :=
    (List.ofFn fun i : Fin n => reflElt f (Pi.single i.castSucc 1)).prod
  change Commute (QuotientGroup.mk ρ : R3 f) (reflBar f w)
  have hf : IsF3Form f := isF3Form_diagF3 (by decide : (2 : ZMod 3) ≠ 0)
  have hρcoe : (ρ : GL (Fin (n + 1)) (ZMod 3)) =
      (List.ofFn fun i : Fin n => F3.refl f (Pi.single i.castSucc 1)).prod := by
    change (((List.ofFn fun i : Fin n => reflElt f (Pi.single i.castSucc 1)).prod :
      F3.reflGroup f) : GL (Fin (n + 1)) (ZMod 3)) = _
    rw [Subgroup.val_list_prod, List.map_ofFn]
    simp only [Function.comp_def, coe_reflElt]
  have hρact : F3.act (ρ : GL (Fin (n + 1)) (ZMod 3)) w = -w := by
    rw [hρcoe]
    exact zzh_act_prod_rho hwl
  have hρconj : (QuotientGroup.mk (s := Subgroup.center (F3.reflGroup f)) ρ : R3 f) *
      reflBar f w * (QuotientGroup.mk (s := Subgroup.center (F3.reflGroup f)) ρ)⁻¹ =
      reflBar f w := by
    rw [mk_conj_reflBar hf ρ w, hρact]
    exact reflBar_neg (f := f) w
  rw [commute_iff_eq]
  calc
    (QuotientGroup.mk (s := Subgroup.center (F3.reflGroup f)) ρ : R3 f) * reflBar f w
        = (QuotientGroup.mk ρ : R3 f) * reflBar f w *
            (QuotientGroup.mk ρ : R3 f)⁻¹ * (QuotientGroup.mk ρ : R3 f) := by group
    _ = reflBar f w * (QuotientGroup.mk ρ : R3 f) := by rw [hρconj]

private theorem zzh_commute_z_s {n : ℕ} (hn : 3 ≤ Module.finrank (ZMod 3) U)
    (hirr : AbsIrred 3 A)
    {φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 (n + 1) 2)}
    {t : Fin n → ↥A}
    {ht : ∀ i, φ (QuotientGroup.mk (t i)) =
      reflBar (diagF3 (n + 1) 2) (Pi.single i.castSucc 1)}
    {w : Fin (n + 1) → ZMod 3} (hwl : w (Fin.last n) = 0)
    {s : ↥A} (hs : IsRefl 3 (s : U ≃ₗ[ZMod 3] U))
    (hsw : φ (QuotientGroup.mk s) = reflBar (diagF3 (n + 1) 2) w) :
    Commute ((List.ofFn t).prod) s := by
  let f : LinearMap.BilinForm (ZMod 3) (Fin (n + 1) → ZMod 3) := diagF3 (n + 1) 2
  let ρ : F3.reflGroup f :=
    (List.ofFn fun i : Fin n => reflElt f (Pi.single i.castSucc 1)).prod
  let z : ↥A := (List.ofFn t).prod
  change Commute z s
  have hQcomm := zzh_rho_comm (n := n) hwl
  have hρbar : (QuotientGroup.mk (s := Subgroup.center (F3.reflGroup f)) ρ : R3 f) =
      (List.ofFn fun i : Fin n => reflBar f (Pi.single i.castSucc 1)).prod := by
    change (QuotientGroup.mk' (Subgroup.center (F3.reflGroup f)))
        ((List.ofFn fun i : Fin n => reflElt f (Pi.single i.castSucc 1)).prod) = _
    rw [← List.prod_hom (List.ofFn fun i : Fin n => reflElt f (Pi.single i.castSucc 1))
      (QuotientGroup.mk' (Subgroup.center (F3.reflGroup f))),
      ← List.ofFn_comp' (fun i : Fin n => reflElt f (Pi.single i.castSucc 1))
        (QuotientGroup.mk' (Subgroup.center (F3.reflGroup f)))]
    simp only [reflBar, QuotientGroup.coe_mk']
  have hφz : φ (QuotientGroup.mk (s := Subgroup.center ↥A) z) =
      (List.ofFn fun i : Fin n => reflBar f (Pi.single i.castSucc 1)).prod := by
    have hmk : QuotientGroup.mk (s := Subgroup.center ↥A) z =
        (List.ofFn fun i : Fin n =>
          QuotientGroup.mk (s := Subgroup.center ↥A) (t i)).prod := by
      change (QuotientGroup.mk' (Subgroup.center ↥A)) ((List.ofFn t).prod) = _
      rw [← List.prod_hom (List.ofFn t) (QuotientGroup.mk' (Subgroup.center ↥A)),
        ← List.ofFn_comp' t (QuotientGroup.mk' (Subgroup.center ↥A))]
      simp only [QuotientGroup.coe_mk']
    rw [hmk, map_list_prod, List.map_ofFn]
    simp only [Function.comp_def, ht]
    rfl
  have hφcomm : Commute (φ (QuotientGroup.mk (s := Subgroup.center ↥A) z))
      (φ (QuotientGroup.mk (s := Subgroup.center ↥A) s)) := by
    rw [hφz, hsw, ← hρbar]
    exact hQcomm
  have hcommQ : Commute (QuotientGroup.mk (s := Subgroup.center ↥A) z)
      (QuotientGroup.mk (s := Subgroup.center ↥A) s) := by
    rw [commute_iff_eq]
    apply φ.injective
    rw [map_mul, map_mul]
    exact hφcomm
  exact (hirr.commute_mk_iff (p := 3) hn (s := z) (t := s) hs).mp hcommQ

omit [Module.Finite (ZMod 3) U] in
private theorem zzh_step3 {z : ↥A} {B : LinearMap.BilinForm (ZMod 3) U}
    {s : ↥A} {a : U}
    (hsa : ∀ x, (s : U ≃ₗ[ZMod 3] U) x = x + B x a • a)
    (hzs : Commute z s) :
    ∀ x : U, B x a • (z : U ≃ₗ[ZMod 3] U) a =
      B ((z : U ≃ₗ[ZMod 3] U) x) a • a := by
  intro x
  have hzx : (z : U ≃ₗ[ZMod 3] U) ((s : U ≃ₗ[ZMod 3] U) x) =
      (s : U ≃ₗ[ZMod 3] U) ((z : U ≃ₗ[ZMod 3] U) x) := by
    have hcoe : ((z : U ≃ₗ[ZMod 3] U) * (s : U ≃ₗ[ZMod 3] U)) =
        ((s : U ≃ₗ[ZMod 3] U) * (z : U ≃ₗ[ZMod 3] U)) := by
      simpa only [Subgroup.coe_mul] using
        congrArg (fun e : ↥A => (e : U ≃ₗ[ZMod 3] U)) hzs.eq
    exact congrFun (congrArg (fun e : U ≃ₗ[ZMod 3] U => (e : U → U)) hcoe) x
  rw [hsa x] at hzx
  rw [map_add, map_smul] at hzx
  rw [hsa ((z : U ≃ₗ[ZMod 3] U) x)] at hzx
  exact add_left_cancel hzx

omit [Module.Finite (ZMod 3) U] in
private theorem zzh_c_actions {n : ℕ} {z : ↥A} {B : LinearMap.BilinForm (ZMod 3) U}
    {u : Fin n → U} (hu : ∀ i j, B (u i) (u j) = if i = j then 1 else 0)
    {t : Fin n → ↥A}
    (htu : ∀ i x, (t i : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i)
    {a : U} (ha : B a a = 1)
    (hstep3 : ∀ x : U, B x a • (z : U ≃ₗ[ZMod 3] U) a =
      B ((z : U ≃ₗ[ZMod 3] U) x) a • a)
    (hzcoe : (z : U ≃ₗ[ZMod 3] U) =
      (List.ofFn fun i : Fin n => (t i : U ≃ₗ[ZMod 3] U)).prod) :
    ∃ a' c : U, a' = ∑ i : Fin n, B a (u i) • u i ∧ a = a' + c ∧
      (∀ i : Fin n, B c (u i) = 0) ∧
      (z : U ≃ₗ[ZMod 3] U) c = c ∧
      (∀ j : Fin n, (z : U ≃ₗ[ZMod 3] U) (u j) = -u j) ∧
      (z : U ≃ₗ[ZMod 3] U) a = -a' + c ∧
      (z : U ≃ₗ[ZMod 3] U) a = B ((z : U ≃ₗ[ZMod 3] U) a) a • a := by
  have hBc : ∀ i : Fin n, B (a - ∑ j : Fin n, B a (u j) • u j) (u i) = 0 := by
    intro i
    rw [LinearMap.BilinForm.sub_left, LinearMap.BilinForm.sum_left,
      Finset.sum_eq_single i]
    · rw [LinearMap.BilinForm.smul_left, hu i i, if_pos rfl, mul_one, sub_self]
    · intro j _ hji
      rw [LinearMap.BilinForm.smul_left, hu j i, if_neg hji, mul_zero]
    · intro hh
      exact absurd (Finset.mem_univ i) hh
  have hz_c : (z : U ≃ₗ[ZMod 3] U) (a - ∑ i : Fin n, B a (u i) • u i) =
      a - ∑ i : Fin n, B a (u i) • u i := by
    rw [hzcoe, zzh_prod_apply_ofFn (B := B) (u := u) hu (fun i => htu i)
      (a - ∑ i : Fin n, B a (u i) • u i)]
    simp only [hBc, zero_smul, Finset.sum_const_zero, add_zero]
  have hz_u : ∀ j : Fin n, (z : U ≃ₗ[ZMod 3] U) (u j) = -u j := by
    intro j
    rw [hzcoe, zzh_prod_apply_ofFn (B := B) (u := u) hu (fun i => htu i) (u j)]
    have hsum : (∑ i : Fin n, B (u j) (u i) • u i) = u j := by
      rw [Finset.sum_eq_single j]
      · rw [hu j j, if_pos rfl, one_smul]
      · intro i _ hij
        rw [hu j i, if_neg (fun h : j = i => hij h.symm), zero_smul]
      · intro hh
        exact absurd (Finset.mem_univ j) hh
    rw [hsum]
    calc u j + u j = (2 : ZMod 3) • u j := by rw [two_smul]
      _ = (-1 : ZMod 3) • u j := by rw [show (2 : ZMod 3) = -1 by decide]
      _ = -u j := neg_one_smul (ZMod 3) (u j)
  have ha_split : a = (∑ i : Fin n, B a (u i) • u i) +
      (a - ∑ i : Fin n, B a (u i) • u i) := by abel
  have hz_a : (z : U ≃ₗ[ZMod 3] U) a =
      -(∑ i : Fin n, B a (u i) • u i) + (a - ∑ i : Fin n, B a (u i) • u i) := by
    conv_lhs => rw [ha_split]
    rw [map_add, map_sum]
    simp only [map_smul, hz_u, hz_c, smul_neg, Finset.sum_neg_distrib]
  have hza : (z : U ≃ₗ[ZMod 3] U) a = B ((z : U ≃ₗ[ZMod 3] U) a) a • a := by
    have h := hstep3 a
    rw [ha, one_smul] at h
    exact h
  exact ⟨∑ i : Fin n, B a (u i) • u i, a - ∑ i : Fin n, B a (u i) • u i,
    rfl, by abel, hBc, hz_c, hz_u, hz_a, hza⟩

omit [Module.Finite (ZMod 3) U] in
private theorem zzh_case_one_setup {n : ℕ} {z : ↥A} {a' c : U}
    {B : LinearMap.BilinForm (ZMod 3) U} {u : Fin n → U}
    (hu : ∀ i j, B (u i) (u j) = if i = j then 1 else 0)
    (hBs : ∀ x y, B x y = B y x) {t : Fin n → ↥A}
    (htu : ∀ i x, (t i : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i)
    {a : U} (hμ : B ((z : U ≃ₗ[ZMod 3] U) a) a = 1)
    (hBc : ∀ i : Fin n, B c (u i) = 0)
    (ha_eq : a = a' + c) (hz_a : (z : U ≃ₗ[ZMod 3] U) a = -a' + c)
    (hza : (z : U ≃ₗ[ZMod 3] U) a = B ((z : U ≃ₗ[ZMod 3] U) a) a • a) :
    a' = 0 ∧ (∀ i : Fin n, B a (u i) = 0) ∧
      (∀ i : Fin n, B (u i) a = 0) ∧
      (∀ i : Fin n, IsRefl 3 (t i : U ≃ₗ[ZMod 3] U)) := by
  have hza1 : (z : U ≃ₗ[ZMod 3] U) a = a := by rw [hza, hμ, one_smul]
  have ha'_zero : a' = 0 := by
    have h : -a' + c = a' + c := by
      calc -a' + c = (z : U ≃ₗ[ZMod 3] U) a := hz_a.symm
        _ = a := hza1
        _ = a' + c := ha_eq
    have h' : -a' = a' := add_right_cancel h
    exact zzh_eq_zero_of_eq_neg h'.symm
  have ha_c : a = c := by rw [ha_eq, ha'_zero, zero_add]
  have hBa_ui : ∀ i : Fin n, B a (u i) = 0 := by
    intro i
    rw [ha_c]
    exact hBc i
  have hBui_a : ∀ i : Fin n, B (u i) a = 0 := fun i => by rw [hBs, hBa_ui i]
  have ht_refl : ∀ i : Fin n, IsRefl 3 (t i : U ≃ₗ[ZMod 3] U) := by
    intro i
    exact zzh_isRefl_of_add (B := B) (u := u i) (q := (t i : U ≃ₗ[ZMod 3] U))
      (by simpa using hu i i) (htu i)
  exact ⟨ha'_zero, hBa_ui, hBui_a, ht_refl⟩

omit [Module.Finite (ZMod 3) U] in
private theorem zzh_case_one_hstcomm {n : ℕ} {B : LinearMap.BilinForm (ZMod 3) U}
    {u : Fin n → U} {t : Fin n → ↥A} {s : ↥A} {a : U}
    (htu : ∀ i x, (t i : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i)
    (hsa : ∀ x, (s : U ≃ₗ[ZMod 3] U) x = x + B x a • a)
    (hBa_ui : ∀ i : Fin n, B a (u i) = 0)
    (hBui_a : ∀ i : Fin n, B (u i) a = 0) :
    ∀ i : Fin n, Commute s (t i) := by
  intro i
  apply Subtype.ext
  apply LinearEquiv.ext
  intro x
  change (s : U ≃ₗ[ZMod 3] U) ((t i : U ≃ₗ[ZMod 3] U) x) =
    (t i : U ≃ₗ[ZMod 3] U) ((s : U ≃ₗ[ZMod 3] U) x)
  have hL : (s : U ≃ₗ[ZMod 3] U) ((t i : U ≃ₗ[ZMod 3] U) x) =
      x + B x (u i) • u i + B x a • a := by
    rw [hsa ((t i : U ≃ₗ[ZMod 3] U) x), htu i x, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, hBui_a i, mul_zero, add_zero]
  have hR : (t i : U ≃ₗ[ZMod 3] U) ((s : U ≃ₗ[ZMod 3] U) x) =
      x + B x a • a + B x (u i) • u i := by
    rw [htu i ((s : U ≃ₗ[ZMod 3] U) x), hsa x, LinearMap.BilinForm.add_left,
      LinearMap.BilinForm.smul_left, hBa_ui i, mul_zero, add_zero]
  rw [hL, hR]
  abel

omit [Module.Finite (ZMod 3) U] in
private theorem zzh_case_one_hR3comm {n : ℕ}
    {φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 (n + 1) 2)}
    {t : Fin n → ↥A} {w : Fin (n + 1) → ZMod 3} {s : ↥A}
    (ht : ∀ i, φ (QuotientGroup.mk (t i)) =
      reflBar (diagF3 (n + 1) 2) (Pi.single i.castSucc 1))
    (hsw : φ (QuotientGroup.mk s) = reflBar (diagF3 (n + 1) 2) w)
    (hstcomm : ∀ i : Fin n, Commute s (t i)) :
    ∀ i : Fin n, Commute (reflBar (diagF3 (n + 1) 2) w)
      (reflBar (diagF3 (n + 1) 2) (Pi.single i.castSucc 1)) := by
  intro i
  have hφst : φ (QuotientGroup.mk (s := Subgroup.center ↥A) s) *
      φ (QuotientGroup.mk (s := Subgroup.center ↥A) (t i)) =
      φ (QuotientGroup.mk (s := Subgroup.center ↥A) (t i)) *
      φ (QuotientGroup.mk (s := Subgroup.center ↥A) s) := by
    rw [← map_mul, ← map_mul]
    congr 1
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, (hstcomm i).eq]
  rw [hsw, ht i] at hφst
  exact hφst

private theorem zzh_case_one_contra {n : ℕ}
    (hn : 3 ≤ Module.finrank (ZMod 3) U) (hirr : AbsIrred 3 A)
    {φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 (n + 1) 2)}
    {t : Fin n → ↥A} {w : Fin (n + 1) → ZMod 3} {s : ↥A}
    (hs : IsRefl 3 (s : U ≃ₗ[ZMod 3] U))
    (ht : ∀ i, φ (QuotientGroup.mk (t i)) =
      reflBar (diagF3 (n + 1) 2) (Pi.single i.castSucc 1))
    (hsw : φ (QuotientGroup.mk s) = reflBar (diagF3 (n + 1) 2) w)
    {B : LinearMap.BilinForm (ZMod 3) U} {u : Fin n → U}
    (hu : ∀ i j, B (u i) (u j) = if i = j then 1 else 0)
    (htu : ∀ i x, (t i : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i)
    {a : U} (hsa : ∀ x, (s : U ≃ₗ[ZMod 3] U) x = x + B x a • a)
    (ht_refl : ∀ i : Fin n, IsRefl 3 (t i : U ≃ₗ[ZMod 3] U))
    (hBui_a : ∀ i : Fin n, B (u i) a = 0) :
    ∀ i : Fin n, reflBar (diagF3 (n + 1) 2) w =
      reflBar (diagF3 (n + 1) 2) (Pi.single i.castSucc 1) → False := by
  intro i hbar
  have hmk : QuotientGroup.mk (s := Subgroup.center ↥A) s =
      QuotientGroup.mk (s := Subgroup.center ↥A) (t i) := by
    apply φ.injective
    rw [hsw, ht i]
    exact hbar
  have hst_eq : s = t i := hirr.mk_injOn_refl hn hs (ht_refl i) hmk
  have happ : (s : U ≃ₗ[ZMod 3] U) (u i) = (t i : U ≃ₗ[ZMod 3] U) (u i) := by
    rw [hst_eq]
  rw [hsa (u i), hBui_a i, zero_smul, add_zero, htu i (u i), hu i i,
    if_pos rfl, one_smul] at happ
  have hui0 : u i = 0 := by
    have h' : u i + u i = u i := happ.symm
    have h'' : u i + u i = u i + 0 := by simpa using h'
    exact add_left_cancel h''
  have hui_ne : u i ≠ 0 := by
    intro h0
    have h1 : B (u i) (u i) = 1 := by rw [hu i i, if_pos rfl]
    rw [h0] at h1
    simp at h1
  exact hui_ne hui0

private theorem zzh_case_one_false {n : ℕ} (hn3 : 3 ≤ n)
    {w : Fin (n + 1) → ZMod 3} (hw : diagF3 (n + 1) 2 w w = 1)
    (hwl : w (Fin.last n) = 0)
    (hR3comm : ∀ i : Fin n, Commute (reflBar (diagF3 (n + 1) 2) w)
      (reflBar (diagF3 (n + 1) 2) (Pi.single i.castSucc 1)))
    (hcontra : ∀ i : Fin n, reflBar (diagF3 (n + 1) 2) w =
      reflBar (diagF3 (n + 1) 2) (Pi.single i.castSucc 1) → False) : False := by
  have hf : IsF3Form (diagF3 (n + 1) 2) :=
    isF3Form_diagF3 (by decide : (2 : ZMod 3) ≠ 0)
  have hm4 : 4 ≤ n + 1 := by omega
  have hunit : ∀ i : Fin n, diagF3 (n + 1) 2 (Pi.single i.castSucc 1)
      (Pi.single i.castSucc 1) = 1 := fun i => by
    rw [diagF3_single_castSucc, if_pos rfl]
  have hcases : ∀ i : Fin n, diagF3 (n + 1) 2 w (Pi.single i.castSucc 1) = 0 := by
    intro i
    have hc := (reflBar_commute_iff hf hm4 hw (hunit i)).1 (hR3comm i)
    rcases hc with h0 | hw_eq | hw_neg
    · exact h0
    · exfalso
      exact hcontra i (by rw [← hw_eq])
    · exfalso
      have hw_eq' : w = -(Pi.single i.castSucc 1) := by
        rw [hw_neg]
        exact (neg_neg w).symm
      exact hcontra i (by rw [hw_eq']; exact reflBar_neg _)
  have hw_i : ∀ i : Fin n, w i.castSucc = 0 := by
    intro i
    have h := hcases i
    rwa [diagF3_apply_single_castSucc] at h
  have hw0 : w = 0 := by
    rw [← zzh_sum_castSucc_single w hwl]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [hw_i i, Pi.single_zero]
  have h1 : (1 : ZMod 3) = 0 := by
    rw [hw0] at hw
    simpa using hw.symm
  exact one_ne_zero h1

omit [Module.Finite (ZMod 3) U] in
private theorem zzh_case_neg {n : ℕ} {z : ↥A} {a' c : U}
    {B : LinearMap.BilinForm (ZMod 3) U} {u : Fin n → U}
    {a : U} (hμ : B ((z : U ≃ₗ[ZMod 3] U) a) a = -1)
    (ha'_sum : a' = ∑ j : Fin n, B a (u j) • u j)
    (ha_eq : a = a' + c) (hz_a : (z : U ≃ₗ[ZMod 3] U) a = -a' + c)
    (hza : (z : U ≃ₗ[ZMod 3] U) a = B ((z : U ≃ₗ[ZMod 3] U) a) a • a) :
    a ∈ Submodule.span (ZMod 3) (Set.range u) := by
  have hza_neg : (z : U ≃ₗ[ZMod 3] U) a = -a := by
    rw [hza, hμ]
    exact neg_one_smul (ZMod 3) a
  have hc_neg : c = -c := by
    have h : -a' + c = -a' + (-c) := by
      calc -a' + c = (z : U ≃ₗ[ZMod 3] U) a := hz_a.symm
        _ = -a := hza_neg
        _ = -(a' + c) := by rw [ha_eq]
        _ = -a' + -c := by rw [neg_add]
    exact add_left_cancel h
  have hc0 : c = 0 := zzh_eq_zero_of_eq_neg hc_neg
  have ha_span : a = a' := by rw [ha_eq, hc0, add_zero]
  rw [ha_span, ha'_sum]
  exact Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem mem_span_of_last_eq_zero (hn : 3 ≤ Module.finrank (ZMod 3) U) (hirr : AbsIrred 3 A)
    {n : ℕ} (hn3 : 3 ≤ n) (φ : ↥A ⧸ Subgroup.center ↥A ≃* R3 (diagF3 (n + 1) 2))
    (hφ : ∀ g, g ∈ reflImage 3 A ↔ φ g ∈ D3 (diagF3 (n + 1) 2))
    {B : LinearMap.BilinForm (ZMod 3) U} (hBs : ∀ x y, B x y = B y x)
    {u : Fin n → U} (hu : ∀ i j, B (u i) (u j) = if i = j then 1 else 0) (t : Fin n → ↥A)
    (ht : ∀ i, φ (QuotientGroup.mk (t i)) =
      reflBar (diagF3 (n + 1) 2) (Pi.single i.castSucc 1))
    (htu : ∀ i x, (t i : U ≃ₗ[ZMod 3] U) x = x + B x (u i) • u i)
    {w : Fin (n + 1) → ZMod 3} (hw : diagF3 (n + 1) 2 w w = 1) (hwl : w (Fin.last n) = 0)
    {s : ↥A} (hs : IsRefl 3 (s : U ≃ₗ[ZMod 3] U))
    (hsw : φ (QuotientGroup.mk s) = reflBar (diagF3 (n + 1) 2) w)
    {a : U} (ha : B a a = 1) (hsa : ∀ x, (s : U ≃ₗ[ZMod 3] U) x = x + B x a • a) :
    a ∈ Submodule.span (ZMod 3) (Set.range u) := by
  have _ : φ (QuotientGroup.mk s) ∈ D3 (diagF3 (n + 1) 2) :=
    (hφ _).mp ⟨s, hs, rfl⟩
  let z : ↥A := (List.ofFn t).prod
  have hzcoe : (z : U ≃ₗ[ZMod 3] U) =
      (List.ofFn fun i : Fin n => (t i : U ≃ₗ[ZMod 3] U)).prod := by
    change (((List.ofFn t).prod : ↥A) : U ≃ₗ[ZMod 3] U) = _
    rw [Subgroup.val_list_prod, List.map_ofFn]
    rfl
  have hzs : Commute z s :=
    zzh_commute_z_s (n := n) hn hirr (φ := φ) (t := t) (ht := ht) (w := w) hwl
      (s := s) hs hsw
  have hstep3 := zzh_step3 (B := B) (s := s) (a := a) hsa hzs
  obtain ⟨a', c, ha'_sum, ha_eq, hBc, hz_c, hz_u, hz_a, hza⟩ :=
    zzh_c_actions (B := B) (u := u) hu (t := t) htu (a := a) ha hstep3 hzcoe
  have hane : a ≠ 0 := by
    intro h0
    simp [h0] at ha
  have hmu_ne : B ((z : U ≃ₗ[ZMod 3] U) a) a ≠ 0 := by
    intro h0
    apply hane
    have h : (z : U ≃ₗ[ZMod 3] U) a = 0 := by rw [hza, h0, zero_smul]
    apply (z : U ≃ₗ[ZMod 3] U).injective
    rw [h, map_zero]
  have hmu_cases : B ((z : U ≃ₗ[ZMod 3] U) a) a = 1 ∨
      B ((z : U ≃ₗ[ZMod 3] U) a) a = -1 :=
    (show ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 by decide) _ hmu_ne
  rcases hmu_cases with hμ | hμ
  · obtain ⟨ha'_zero, hBa_ui, hBui_a, ht_refl⟩ :=
      zzh_case_one_setup (z := z) (B := B) (u := u) hu hBs (t := t) htu
        (a := a) hμ hBc ha_eq hz_a hza
    have hstcomm := zzh_case_one_hstcomm (B := B) (u := u) (t := t) (s := s) (a := a)
      htu hsa hBa_ui hBui_a
    have hR3comm := zzh_case_one_hR3comm (φ := φ) (t := t) (w := w) (s := s)
      ht hsw hstcomm
    have hcontra := zzh_case_one_contra hn hirr (φ := φ) (t := t) (w := w) (s := s)
      hs ht hsw hu htu hsa ht_refl hBui_a
    exact False.elim (zzh_case_one_false hn3 hw hwl hR3comm hcontra)
  · exact zzh_case_neg (B := B) (u := u) (z := z) (a' := a')
      (c := c) hμ ha'_sum ha_eq hz_a hza


end CFSG.StandardType.ZS

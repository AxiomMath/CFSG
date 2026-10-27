module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs

public section

namespace CFSG.Quasithin.KGC31

open Matrix

variable {Γ : Type*} [Group Γ] {n : ℕ}

@[expose] def eElt (v : Fin n → Γ) (c : Fin n → ZMod 2) : Γ :=
  (List.ofFn fun i => v i ^ (c i).val).prod

theorem eElt_succ (v : Fin (n + 1) → Γ) (c : Fin (n + 1) → ZMod 2) :
    eElt v c = v 0 ^ (c 0).val * eElt (fun i => v i.succ) fun i => c i.succ := by
  simp [eElt, List.ofFn_succ]

theorem eElt_zero (v : Fin n → Γ) : eElt v 0 = 1 := by
  simp [eElt]

theorem commute_eElt {v : Fin n → Γ} {x : Γ} (hx : ∀ i, Commute x (v i))
    (c : Fin n → ZMod 2) : Commute x (eElt v c) := by
  refine Commute.list_prod_right _ _ fun y hy => ?_
  obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hy
  exact (hx i).pow_right _

theorem pow_val_add_of_sq {x : Γ} (hx : x * x = 1) (a b : ZMod 2) :
    x ^ (a + b).val = x ^ a.val * x ^ b.val := by
  have h2 : ∀ m : ℕ, x ^ (m % 2) = x ^ m := fun m => by
    conv_rhs => rw [← Nat.mod_add_div m 2, pow_add, pow_mul, sq, hx, one_pow, mul_one]
  rw [ZMod.val_add, h2, pow_add]

theorem eElt_add : ∀ {n : ℕ} {v : Fin n → Γ}, (∀ i, v i * v i = 1) →
    (∀ i j, Commute (v i) (v j)) → ∀ c d : Fin n → ZMod 2,
      eElt v (c + d) = eElt v c * eElt v d
  | 0, v, _, _, c, d => by simp [eElt]
  | n + 1, v, hs, hc, c, d => by
    rw [eElt_succ, eElt_succ, eElt_succ]
    have ih := eElt_add (v := fun i => v i.succ) (fun i => hs i.succ)
      (fun i j => hc i.succ j.succ) (fun i => c i.succ) (fun i => d i.succ)
    have e : ((fun i : Fin n => c i.succ) + fun i : Fin n => d i.succ) =
        fun i : Fin n => (c + d) i.succ := rfl
    rw [e] at ih
    rw [ih, Pi.add_apply, pow_val_add_of_sq (hs 0)]
    have hcomm : Commute (v 0 ^ (d 0).val) (eElt (fun i => v i.succ) fun i => c i.succ) :=
      commute_eElt (fun i => (hc 0 i.succ).pow_left _) _
    simp only [mul_assoc]
    rw [hcomm.left_comm]

structure EBasis (v : Fin n → Γ) : Prop where
  sq : ∀ i, v i * v i = 1
  comm : ∀ i j, Commute (v i) (v j)
  ne_one : ∀ c, eElt v c = 1 → c = 0

variable {v : Fin n → Γ}

theorem add_self_zmod2 (x : Fin n → ZMod 2) : x + x = 0 := by
  funext i
  simp only [Pi.add_apply, Pi.zero_apply]
  generalize x i = a
  revert a
  decide

theorem eElt_injective (h : EBasis v) : Function.Injective (eElt v) := by
  intro c d hcd
  have hcc : eElt v c * eElt v c = 1 := by
    rw [← eElt_add h.sq h.comm, add_self_zmod2, eElt_zero]
  have h1 : eElt v (c + d) = 1 := by rw [eElt_add h.sq h.comm, ← hcd, hcc]
  have h2 := h.ne_one _ h1
  funext i
  have h3 := congrFun h2 i
  simp only [Pi.add_apply, Pi.zero_apply] at h3
  revert h3
  generalize c i = a
  generalize d i = b
  revert a b
  decide

@[expose] def eHom (h : EBasis v) : Multiplicative (Fin n → ZMod 2) →* Γ where
  toFun c := eElt v c.toAdd
  map_one' := eElt_zero v
  map_mul' c d := eElt_add h.sq h.comm c.toAdd d.toAdd

theorem conj_eElt (g : Γ) (c : Fin n → ZMod 2) :
    g * eElt v c * g⁻¹ = eElt (fun i => g * v i * g⁻¹) c := by
  have h1 : g * eElt v c * g⁻¹ = MulAut.conj g (eElt v c) := rfl
  rw [h1, eElt, map_list_prod, List.map_ofFn]
  simp [eElt, Function.comp_def, MulAut.conj_apply]

theorem map_eElt {B : Type*} [Group B] (f : Γ →* B) (c : Fin n → ZMod 2) :
    f (eElt v c) = eElt (fun i => f (v i)) c := by
  rw [eElt, map_list_prod, List.map_ofFn]
  simp [eElt, Function.comp_def]

theorem eElt_pow_val (a : ZMod 2) (w : Fin n → ZMod 2) :
    eElt v w ^ a.val = eElt v (a • w) := by
  have ha : a = 0 ∨ a = 1 := by revert a; decide
  rcases ha with rfl | rfl
  · rw [zero_smul, eElt_zero, ZMod.val_zero, pow_zero]
  · rw [one_smul, show (1 : ZMod 2).val = 1 from rfl, pow_one]

theorem eElt_sum (h : EBasis v) : ∀ {m : ℕ} (w : Fin m → Fin n → ZMod 2),
    eElt v (∑ i, w i) = (List.ofFn fun i => eElt v (w i)).prod
  | 0, w => by simp [eElt_zero]
  | m + 1, w => by
    rw [Fin.sum_univ_succ, eElt_add h.sq h.comm, List.ofFn_succ, List.prod_cons,
      eElt_sum h (fun i => w i.succ)]

theorem eElt_mulVec (h : EBasis v) (M : Matrix (Fin n) (Fin n) (ZMod 2)) (c : Fin n → ZMod 2) :
    eElt (fun i => eElt v fun r => M r i) c = eElt v (M *ᵥ c) := by
  have hM : M *ᵥ c = ∑ i, c i • (fun r => M r i) := by
    funext r
    simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  rw [hM, eElt_sum h]
  unfold eElt
  congr 1
  refine List.ofFn_inj.mpr (funext fun i => ?_)
  exact eElt_pow_val _ _

theorem eElt_single : ∀ {n : ℕ} (v : Fin n → Γ) (i : Fin n), eElt v (Pi.single i 1) = v i
  | 0, _, i => i.elim0
  | n + 1, v, i => by
    rw [eElt_succ]
    refine Fin.cases ?_ (fun j => ?_) i
    · have h0 : (fun k : Fin n =>
          (Pi.single (0 : Fin (n + 1)) (1 : ZMod 2) : Fin (n + 1) → ZMod 2) k.succ) = 0 := by
        funext k
        simp [Fin.succ_ne_zero]
      rw [h0, eElt_zero, Pi.single_eq_same, show (1 : ZMod 2).val = 1 from rfl, pow_one,
        mul_one]
    · have h0 : (Pi.single j.succ (1 : ZMod 2) : Fin (n + 1) → ZMod 2) 0 = 0 := by
        simp [(Fin.succ_ne_zero j).symm]
      have h1 : (fun k : Fin n => (Pi.single j.succ (1 : ZMod 2) : Fin (n + 1) → ZMod 2) k.succ) =
          Pi.single j 1 := by
        funext k
        simp [Pi.single_apply, Fin.succ_inj]
      rw [h0, h1, eElt_single, ZMod.val_zero, pow_zero, one_mul]

theorem eElt_one_col (i : Fin n) :
    eElt v (fun r => (1 : Matrix (Fin n) (Fin n) (ZMod 2)) r i) = v i := by
  have : (fun r => (1 : Matrix (Fin n) (Fin n) (ZMod 2)) r i) = Pi.single i 1 := by
    funext r
    simp [Matrix.one_apply, Pi.single_apply, eq_comm]
  rw [this, eElt_single]

variable (h : EBasis v)

@[expose] def eSub : Subgroup Γ := (eHom h).range

theorem mem_eSub_iff (x : Γ) : x ∈ eSub h ↔ ∃ c, eElt v c = x :=
  ⟨fun ⟨c, hc⟩ => ⟨c.toAdd, hc⟩, fun ⟨c, hc⟩ => ⟨Multiplicative.ofAdd c, hc⟩⟩

theorem eElt_mem (c : Fin n → ZMod 2) : eElt v c ∈ eSub h := (mem_eSub_iff h _).mpr ⟨c, rfl⟩

theorem mem_eSub (i : Fin n) : v i ∈ eSub h := by
  rw [← eElt_single (v := v) i]
  exact eElt_mem h _

theorem card_eSub : Nat.card (eSub h) = 2 ^ n := by
  rw [eSub, MonoidHom.range_eq_map, Subgroup.card_map_of_injective
    (f := eHom h) (fun c d hcd => (eElt_injective h hcd : c.toAdd = d.toAdd)),
    Subgroup.card_top, Nat.card_eq_fintype_card]
  simp [ZMod.card]

theorem eSub_eq_closure : eSub h = Subgroup.closure (Set.range v) := by
  refine le_antisymm ?_ ((Subgroup.closure_le _).mpr ?_)
  · rintro _ ⟨c, rfl⟩
    change eElt v c.toAdd ∈ _
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := List.mem_ofFn.mp hx
    exact Subgroup.pow_mem _ (Subgroup.subset_closure (Set.mem_range_self i)) _
  · rintro _ ⟨i, rfl⟩
    exact mem_eSub h i

theorem eSub_comm (x y : Γ) (hx : x ∈ eSub h) (hy : y ∈ eSub h) : x * y = y * x := by
  obtain ⟨c, rfl⟩ := (mem_eSub_iff h x).mp hx
  obtain ⟨d, rfl⟩ := (mem_eSub_iff h y).mp hy
  rw [← eElt_add h.sq h.comm, ← eElt_add h.sq h.comm, add_comm]

theorem eSub_sq (x : Γ) (hx : x ∈ eSub h) : x * x = 1 := by
  obtain ⟨c, rfl⟩ := (mem_eSub_iff h x).mp hx
  rw [← eElt_add h.sq h.comm, add_self_zmod2, eElt_zero]

abbrev eNorm : Subgroup Γ := Subgroup.normalizer (eSub h : Set Γ)

theorem conj_mem_eSub (g : ↥(eNorm h)) (c : Fin n → ZMod 2) :
    (g : Γ) * eElt v c * (g : Γ)⁻¹ ∈ eSub h :=
  (Subgroup.mem_normalizer_iff.mp g.2 _).mp (eElt_mem h c)

@[expose] noncomputable def eCo (g : ↥(eNorm h)) (c : Fin n → ZMod 2) : Fin n → ZMod 2 :=
  ((mem_eSub_iff h _).mp (conj_mem_eSub h g c)).choose

theorem eElt_eCo (g : ↥(eNorm h)) (c : Fin n → ZMod 2) :
    eElt v (eCo h g c) = (g : Γ) * eElt v c * (g : Γ)⁻¹ :=
  ((mem_eSub_iff h _).mp (conj_mem_eSub h g c)).choose_spec

theorem eCo_eq {g : ↥(eNorm h)} {c d : Fin n → ZMod 2}
    (hd : eElt v d = (g : Γ) * eElt v c * (g : Γ)⁻¹) : eCo h g c = d :=
  eElt_injective h (by rw [eElt_eCo, hd])

theorem eCo_mul (g k : ↥(eNorm h)) (c : Fin n → ZMod 2) :
    eCo h (g * k) c = eCo h g (eCo h k c) := by
  apply eCo_eq
  rw [eElt_eCo, eElt_eCo, Subgroup.coe_mul]
  group

theorem eCo_one (c : Fin n → ZMod 2) : eCo h 1 c = c :=
  eCo_eq h (by rw [OneMemClass.coe_one, one_mul, inv_one, mul_one])

theorem eCo_add (g : ↥(eNorm h)) (c d : Fin n → ZMod 2) :
    eCo h g (c + d) = eCo h g c + eCo h g d := by
  apply eCo_eq
  rw [eElt_add h.sq h.comm, eElt_eCo, eElt_eCo, eElt_add h.sq h.comm]
  group

@[expose] noncomputable def eCoHom (g : ↥(eNorm h)) : (Fin n → ZMod 2) →+ (Fin n → ZMod 2) where
  toFun := eCo h g
  map_zero' := eCo_eq h (by rw [eElt_zero, mul_one, mul_inv_cancel])
  map_add' := eCo_add h g

theorem eCo_smul (g : ↥(eNorm h)) (a : ZMod 2) (x : Fin n → ZMod 2) :
    eCo h g (a • x) = a • eCo h g x := by
  have ha : a = 0 ∨ a = 1 := by revert a; decide
  rcases ha with rfl | rfl
  · rw [zero_smul, zero_smul]
    exact (eCoHom h g).map_zero
  · rw [one_smul, one_smul]

@[expose] noncomputable def eMat (g : ↥(eNorm h)) : Matrix (Fin n) (Fin n) (ZMod 2) :=
  Matrix.of fun r i => eCo h g (Pi.single i 1) r

theorem eMat_mulVec (g : ↥(eNorm h)) (c : Fin n → ZMod 2) : eMat h g *ᵥ c = eCo h g c := by
  have hc : c = ∑ i, c i • (Pi.single i 1 : Fin n → ZMod 2) := by
    funext r
    simp [Finset.sum_apply, Pi.single_apply]
  conv_rhs => rw [hc]
  change _ = eCoHom h g (∑ i, c i • (Pi.single i 1 : Fin n → ZMod 2))
  rw [map_sum]
  funext r
  simp only [eMat, Matrix.mulVec, dotProduct, Matrix.of_apply, Finset.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  change _ = (eCo h g (c i • Pi.single i 1)) r
  rw [eCo_smul, Pi.smul_apply, smul_eq_mul, mul_comm]

theorem matrix_ext_mulVec {M N : Matrix (Fin n) (Fin n) (ZMod 2)} (hMN : ∀ c, M *ᵥ c = N *ᵥ c) :
    M = N :=
  Matrix.toLin'.injective (LinearMap.ext fun c => by
    rw [Matrix.toLin'_apply, Matrix.toLin'_apply, hMN])

theorem eMat_mul (g k : ↥(eNorm h)) : eMat h (g * k) = eMat h g * eMat h k :=
  matrix_ext_mulVec fun c => by
    rw [eMat_mulVec, eCo_mul, ← Matrix.mulVec_mulVec, eMat_mulVec, eMat_mulVec]

theorem eMat_one : eMat h 1 = 1 :=
  matrix_ext_mulVec fun c => by rw [eMat_mulVec, eCo_one, Matrix.one_mulVec]

@[expose] noncomputable def eGL : ↥(eNorm h) →* Matrix.GeneralLinearGroup (Fin n) (ZMod 2) where
  toFun g := ⟨eMat h g, eMat h g⁻¹, by rw [← eMat_mul, mul_inv_cancel, eMat_one],
    by rw [← eMat_mul, inv_mul_cancel, eMat_one]⟩
  map_one' := Units.ext (eMat_one h)
  map_mul' g k := Units.ext (eMat_mul h g k)

theorem eGL_coe (g : ↥(eNorm h)) : ((eGL h g : Matrix.GeneralLinearGroup (Fin n) (ZMod 2)) :
    Matrix (Fin n) (Fin n) (ZMod 2)) = eMat h g := rfl

theorem conj_eq_eElt_mulVec (g : ↥(eNorm h)) (c : Fin n → ZMod 2) :
    (g : Γ) * eElt v c * (g : Γ)⁻¹ = eElt v (eMat h g *ᵥ c) := by
  rw [eMat_mulVec, eElt_eCo]

theorem eMat_eq (g : ↥(eNorm h)) (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hM : ∀ i, (g : Γ) * v i * (g : Γ)⁻¹ = eElt v fun r => M r i) : eMat h g = M := by
  apply matrix_ext_mulVec
  intro c
  rw [eMat_mulVec]
  apply eCo_eq
  rw [conj_eElt, ← eElt_mulVec h]
  congr 1
  funext i
  exact (hM i).symm

theorem eMat_eq_one_iff (g : ↥(eNorm h)) :
    eMat h g = 1 ↔ (g : Γ) ∈ Subgroup.centralizer (eSub h : Set Γ) := by
  constructor
  · intro h1
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨c, rfl⟩ := (mem_eSub_iff h x).mp hx
    have h2 := conj_eq_eElt_mulVec h g c
    rw [h1, Matrix.one_mulVec] at h2
    calc eElt v c * (g : Γ) = (g : Γ) * eElt v c * (g : Γ)⁻¹ * (g : Γ) := by rw [h2]
      _ = (g : Γ) * eElt v c := by group
  · intro hc
    refine eMat_eq h g 1 fun i => ?_
    rw [eElt_one_col]
    have := Subgroup.mem_centralizer_iff.mp hc (v i) (mem_eSub h i)
    rw [← this, mul_inv_cancel_right]

theorem mem_eNorm [Finite Γ] {g : Γ} (M : Matrix (Fin n) (Fin n) (ZMod 2))
    (hM : ∀ i, g * v i * g⁻¹ = eElt v fun r => M r i) : g ∈ eNorm h := by
  have hle : (eSub h).map (MulAut.conj g).toMonoidHom ≤ eSub h := by
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_eSub_iff h x).mp hx
    refine (mem_eSub_iff h _).mpr ⟨M *ᵥ c, ?_⟩
    rw [← eElt_mulVec h]
    change _ = g * eElt v c * g⁻¹
    rw [conj_eElt]
    congr 1
    funext i
    exact (hM i).symm
  have heq := Subgroup.eq_of_le_of_card_ge hle
    (by rw [Subgroup.card_map_of_injective (MulAut.conj g).injective])
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq

theorem EBasis.map {B : Type*} [Group B] (hv : EBasis v) {f : Γ →* B}
    (hf : Function.Injective f) : EBasis fun i => f (v i) where
  sq i := by rw [← map_mul, hv.sq i, map_one]
  comm i j := (hv.comm i j).map f
  ne_one c hc := hv.ne_one c (hf (by rw [map_eElt, hc, map_one]))

theorem eSub_map {B : Type*} [Group B] {f : Γ →* B} (hf : Function.Injective f) :
    (eSub h).map f = eSub (h.map hf) := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    obtain ⟨c, rfl⟩ := (mem_eSub_iff h y).mp hy
    exact (mem_eSub_iff (h.map hf) _).mpr ⟨c, (map_eElt f c).symm⟩
  · intro hx
    obtain ⟨c, rfl⟩ := (mem_eSub_iff (h.map hf) x).mp hx
    exact ⟨eElt v c, eElt_mem h c, map_eElt f c⟩

end CFSG.Quasithin.KGC31

end

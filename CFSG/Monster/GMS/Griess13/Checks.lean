module

public import CFSG.Monster.GMS.Griess13.DataPacked
public import CFSG.Monster.GMS.Griess13.ChecksInputs
public import Certificates.Certificate10032
public meta import CFSG.Monster.GMS.Griess13.DataPacked
public meta import Mathlib
public import Certificates.Kernel.SporSch.Co2M.ThirdBound

public section

namespace CFSG.Monster.GMS.Griess13.Co1Data

open scoped Matrix commutatorElement

section Generic

variable {M : Type} [Group M]

theorem getD_one_mem {H : Subgroup M} {gens : List M} (h : ∀ x ∈ gens, x ∈ H) (i : ℕ) :
    gens.getD i 1 ∈ H := by
  by_cases hi : i < gens.length
  · rw [List.getD_eq_getElem _ _ hi]
    exact h _ (List.getElem_mem hi)
  · rw [List.getD_eq_default _ _ (by omega)]
    exact one_mem H

theorem evalWord_mem {H : Subgroup M} {gens : List M} (h : ∀ x ∈ gens, x ∈ H) (w : List ℤ) :
    evalWord gens w ∈ H := by
  have hl : ∀ l, letterVal gens l ∈ H := by
    intro l
    unfold letterVal
    split_ifs
    · exact getD_one_mem h _
    · exact inv_mem (getD_one_mem h _)
  have key : ∀ (w : List ℤ) (acc : M), acc ∈ H →
      w.foldl (fun a l => a * letterVal gens l) acc ∈ H := by
    intro w
    induction w with
    | nil => intro acc hacc; exact hacc
    | cons l w ih =>
      intro acc hacc
      simp only [List.foldl_cons]
      exact ih _ (mul_mem hacc (hl l))
  exact key w 1 (one_mem H)

theorem prod_ofFn_mul {n : ℕ} (a b : Fin n → M) (hab : ∀ i j, Commute (a i) (b j)) :
    (List.ofFn fun i => a i * b i).prod = (List.ofFn a).prod * (List.ofFn b).prod := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [List.ofFn_succ, List.ofFn_succ, List.ofFn_succ, List.prod_cons, List.prod_cons,
      List.prod_cons, ih (fun i => a i.succ) (fun i => b i.succ) (fun i j => hab _ _)]
    have hc : Commute (b 0) (List.ofFn fun i => a i.succ).prod := by
      apply Commute.list_prod_right
      intro x hx
      obtain ⟨i, rfl⟩ := List.mem_ofFn.1 hx
      exact (hab _ _).symm
    simp only [mul_assoc]
    rw [← mul_assoc (b 0), hc.eq, mul_assoc]

variable (ε : Fin 6 → M)

theorem iotaOf_add (hc : ∀ i j, ε i * ε j = ε j * ε i) (h3 : ∀ i, ε i ^ 3 = 1)
    (v w : Fin 6 → ZMod 3) : iotaOf ε (v + w) = iotaOf ε v * iotaOf ε w := by
  unfold iotaOf
  have h : ∀ i, ε i ^ ((v + w) i).val = ε i ^ (v i).val * ε i ^ (w i).val := by
    intro i
    rw [Pi.add_apply, ZMod.val_add, ← pow_eq_pow_mod _ (h3 i), pow_add]
  simp only [h]
  exact prod_ofFn_mul _ _ fun i j => Commute.pow_pow (hc i j) _ _

theorem iotaOf_zero : iotaOf ε 0 = 1 := by simp [iotaOf]

theorem iotaOf_pow (hc : ∀ i j, ε i * ε j = ε j * ε i) (h3 : ∀ i, ε i ^ 3 = 1)
    (u : Fin 6 → ZMod 3) (n : ℕ) : iotaOf ε u ^ n = iotaOf ε (n • u) := by
  induction n with
  | zero => rw [pow_zero, zero_smul, iotaOf_zero]
  | succ n ih => rw [pow_succ, ih, succ_nsmul, iotaOf_add ε hc h3]

theorem iotaOf_ofFn_prod (hc : ∀ i j, ε i * ε j = ε j * ε i) (h3 : ∀ i, ε i ^ 3 = 1) {m : ℕ}
    (u : Fin m → Fin 6 → ZMod 3) :
    (List.ofFn fun i => iotaOf ε (u i)).prod = iotaOf ε (∑ i, u i) := by
  induction m with
  | zero => simp [iotaOf_zero]
  | succ m ih =>
    rw [List.ofFn_succ, List.prod_cons, ih (fun i => u i.succ), Fin.sum_univ_succ,
      iotaOf_add ε hc h3]

theorem conj_iotaOf (hc : ∀ i j, ε i * ε j = ε j * ε i) (h3 : ∀ i, ε i ^ 3 = 1) (g : M)
    (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) (h : ∀ i, g * ε i * g⁻¹ = iotaOf ε (A i))
    (v : Fin 6 → ZMod 3) : g * iotaOf ε v * g⁻¹ = iotaOf ε (v ᵥ* A) := by
  have h1 : g * iotaOf ε v * g⁻¹ = (List.ofFn fun i => (g * ε i * g⁻¹) ^ (v i).val).prod := by
    have := map_list_prod (MulAut.conj g) (List.ofFn fun i => ε i ^ (v i).val)
    simp_all [MulAut.conj_apply, map_pow, iotaOf]
  have h2 : (List.ofFn fun i => (g * ε i * g⁻¹) ^ (v i).val).prod =
      (List.ofFn fun i => iotaOf ε ((v i).val • A i)).prod := by
    congr 1
    congr 1
    funext i
    rw [h i, iotaOf_pow ε hc h3]
  rw [h1, h2, iotaOf_ofFn_prod ε hc h3]
  congr 1
  funext j
  rw [Finset.sum_apply]
  show ∑ i, ((v i).val • A i) j = ∑ i, v i * A i j
  refine Finset.sum_congr rfl fun i _ => ?_
  show (v i).val • A i j = v i * A i j
  rw [nsmul_eq_mul, ZMod.natCast_zmod_val]

end Generic

private theorem forall_fin_of_all {n : ℕ} {p : Fin n → Bool} (h : (List.finRange n).all p = true)
    (i : Fin n) : p i = true := by
  have := List.all_eq_true.1 h i (List.mem_finRange i)
  exact this

theorem wN_mem (s : String) : wN s ∈ N := by
  refine @evalWord_mem G _ N _ (fun x hx => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem n1_mem :
    n1 ∈ N := Subgroup.subset_closure (Set.mem_insert _ _)

theorem n2_mem :
    n2 ∈ N := Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem e_mem (i : Fin 6) : e i ∈ N := wN_mem _

theorem tau_mem : tau ∈ N := wN_mem _

theorem m_mem (i : Fin 2) : m i ∈ N := wN_mem _

theorem r_mem (k : Fin 12) : r k ∈ N := wN_mem _

theorem xGen_mem (k : Fin 3) : xGen k ∈ N := wN_mem _

theorem yGen_mem (k : Fin 3) : yGen k ∈ N := wN_mem _

theorem m_mem_P (i : Fin 2) : m i ∈ P := by
  fin_cases i
  · exact Subgroup.subset_closure (Set.mem_insert _ _)
  · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

theorem wM_mem (s : String) : wM s ∈ P := by
  refine @evalWord_mem G _ P _ (fun x hx => ?_) _
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · exact m_mem_P 0
  · exact m_mem_P 1

private theorem commCheck_true :
    commCheck = true :=
  Certificates.certificate10032.1

private theorem cubeCheck_true :
    cubeCheck = true :=
  Certificates.certificate10032.2.1

theorem e_comm
    (i j : Fin 6) : e i * e j = e j * e i :=
  ((is_prE i).mul (is_prE j)).eq_of ((is_prE j).mul (is_prE i))
    (forall_fin_of_all (forall_fin_of_all commCheck_true i) j)

theorem e_pow_three
    (i : Fin 6) : e i ^ 3 = 1 :=
  ((is_prE i).pow 3).eq_of PR.Is.one (forall_fin_of_all cubeCheck_true i)

private theorem iota_ne_one_aux :
    ∀ v : Fin 6 → ZMod 3, v ≠ 0 → PR.eq (prIota v) PR.one = false :=
  Certificates.certificate10032.2.2.1

theorem iota_ne_one
    {v : Fin 6 → ZMod 3} (hv : v ≠ 0) : iota v ≠ 1 :=
  (is_prIota v).ne_of PR.Is.one (iota_ne_one_aux v hv)

theorem iota_add
    (v w : Fin 6 → ZMod 3) : iota (v + w) = iota v * iota w := by
  have key := @iotaOf_add G _ e
  exact key e_comm e_pow_three v w

theorem iota_zero : iota 0 = 1 := @iotaOf_zero G _ e

theorem iota_neg
    (v : Fin 6 → ZMod 3) : iota (-v) = (iota v)⁻¹ := by
  apply eq_inv_of_mul_eq_one_left
  rw [← iota_add]
  have h : -v + v = 0 := funext fun i => neg_add_cancel (v i)
  rw [h, iota_zero]

theorem iota_sub
    (v w : Fin 6 → ZMod 3) : iota (v - w) = iota v * (iota w)⁻¹ := by
  have h : v - w = v + -w := funext fun i => sub_eq_add_neg (v i) (w i)
  rw [h, iota_add, iota_neg]

theorem iota_injective :
    Function.Injective iota := by
  intro v w h
  by_contra hne
  have h0 : v - w ≠ 0 := fun h0 => hne (funext fun i => sub_eq_zero.1 (congrFun h0 i))
  exact iota_ne_one h0 (by rw [iota_sub, h, mul_inv_cancel])

@[expose] noncomputable def iotaChar :
    AddChar (Fin 6 → ZMod 3) G where
  toFun := iota
  map_zero_eq_one' := iota_zero
  map_add_eq_mul' := iota_add

theorem iota_single (i : Fin 6) : iota (Pi.single i 1) = e i := by
  have h1 : ((1 : ZMod 3).val) = 1 := by decide
  fin_cases i <;> simp [iota, iotaOf, List.ofFn_succ, Pi.single_apply, h1]

theorem e_ne_one
    (i : Fin 6) : e i ≠ 1 := by
  rw [← iota_single]
  exact iota_ne_one fun h => by simpa using congrFun h i

@[expose] def ConjMat
    (g : G) (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) : Prop :=
  ∀ v, g * iota v * g⁻¹ = iota (v ᵥ* A)

theorem conjMat_of_rows
    {g : G} {A : Matrix (Fin 6) (Fin 6) (ZMod 3)}
    (h : ∀ i, g * e i * g⁻¹ = iota (A i)) : ConjMat g A := by
  have key := @conj_iotaOf G _ e
  exact key e_comm e_pow_three g A h

theorem hyp_conj (A : Matrix (Fin 6) (Fin 6) (ZMod 3)) (w v : Fin 6 → ZMod 3) :
    w ⬝ᵥ (v ᵥ* A) = (A *ᵥ w) ⬝ᵥ v := by
  rw [dotProduct_comm w (v ᵥ* A), ← Matrix.dotProduct_mulVec, dotProduct_comm]

theorem is_prNs (s : Fin 2) : PR.Is (prNs s) (nGen s) := by
  fin_cases s
  · exact is_prN1
  · exact is_prN2

private theorem nConjCheck_true :
    nConjCheck = true :=
  Certificates.certificate10032.2.2.2.1

theorem conj_e_n
    (s : Fin 2) (i : Fin 6) : nGen s * e i * (nGen s)⁻¹ = iota (actN s i) :=
  ((is_prNs s).conj (is_prE i)).eq_of (is_prIota _)
    (forall_fin_of_all (forall_fin_of_all nConjCheck_true s) i)

theorem conj_iota_n
    (s : Fin 2) (v : Fin 6 → ZMod 3) :
    nGen s * iota v * (nGen s)⁻¹ = iota (v ᵥ* actN s) :=
  conjMat_of_rows (conj_e_n s) v

private theorem tauCheck_true :
    tauCheck = true :=
  Certificates.certificate10032.2.2.2.2.1

theorem tau_sq : tau * tau = 1 :=
  (is_prTau.mul is_prTau).eq_of PR.Is.one (by
    have := tauCheck_true
    simp only [tauCheck, Bool.and_eq_true] at this
    exact this.1)

theorem tau_conj_e
    (i : Fin 6) : tau * e i * tau⁻¹ = e i ^ 2 :=
  (is_prTau.conj (is_prE i)).eq_of ((is_prE i).pow 2) (by
    have := tauCheck_true
    simp only [tauCheck, Bool.and_eq_true] at this
    have h := forall_fin_of_all this.2 i
    simp only [Bool.and_eq_true] at h
    exact h.1)

theorem conjMat_tau :
    ConjMat tau scal2 := by
  refine conjMat_of_rows fun i => ?_
  refine (is_prTau.conj (is_prE i)).eq_of (is_prIota _) ?_
  have := tauCheck_true
  simp only [tauCheck, Bool.and_eq_true] at this
  have h := forall_fin_of_all this.2 i
  simp only [Bool.and_eq_true] at h
  exact h.2

theorem tau_conj_iota
    (v : Fin 6 → ZMod 3) : tau * iota v * tau⁻¹ = (iota v)⁻¹ := by
  rw [conjMat_tau v]
  apply eq_inv_of_mul_eq_one_left
  rw [← iota_add]
  have h0 : v ᵥ* scal2 + v = 0 := by
    funext j
    have h2 : (v ᵥ* scal2) j = v j * 2 := by
      simp [Matrix.vecMul, dotProduct, scal2]
    show (v ᵥ* scal2) j + v j = 0
    rw [h2]
    exact (by decide : ∀ x : ZMod 3, x * 2 + x = 0) (v j)
  rw [h0, iota_zero]

theorem tau_normalizes_K0
    (v : Fin 6 → ZMod 3) (hv : w1 ⬝ᵥ v = 0) :
    ∃ u, tau * iota v * tau⁻¹ = iota u ∧ w1 ⬝ᵥ u = 0 := by
  refine ⟨v ᵥ* scal2, conjMat_tau v, ?_⟩
  rw [hyp_conj]
  have h : scal2 *ᵥ w1 = (2 : ZMod 3) • w1 := by
    funext i
    simp [Matrix.mulVec, dotProduct, scal2]
  rw [h, smul_dotProduct, hv, smul_zero]

private theorem conj_commutator_aux {M : Type} [Group M] (a b g : M) :
    g⁻¹ * (a⁻¹ * b⁻¹ * a * b) * g = ⁅g⁻¹ * a⁻¹ * g, g⁻¹ * b⁻¹ * g⁆ := by
  simp only [commutatorElement_def]
  group

set_option maxRecDepth 2000 in
private theorem cConj_eq_commutator (g : G) :
    cConj g = ⁅g⁻¹ * (m 0)⁻¹ * g, g⁻¹ * (m 1)⁻¹ * g⁆ := by
  have key := @conj_commutator_aux G _ (m 0) (m 1) g
  exact key

private theorem cConj_mem_commutator
    {g : G} (hg : g ∈ P) : cConj g ∈ ⁅P, P⁆ := by
  rw [cConj_eq_commutator]
  refine Subgroup.commutator_mem_commutator ?_ ?_
  · exact mul_mem (mul_mem (inv_mem hg) (inv_mem (m_mem_P 0))) hg
  · exact mul_mem (mul_mem (inv_mem hg) (inv_mem (m_mem_P 1))) hg

private theorem cm_eq_cConj_one : cm = cConj 1 := by simp [cConj]

theorem S_mem_commutator : ∀ x ∈ S, x ∈ ⁅P, P⁆ := by
  have h0 := m_mem_P 0
  have h1 := m_mem_P 1
  intro x hx
  simp only [S, List.mem_cons, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · rw [cm_eq_cConj_one]; exact cConj_mem_commutator (one_mem _)
  · exact cConj_mem_commutator h0
  · exact cConj_mem_commutator h1
  · exact cConj_mem_commutator (inv_mem h0)
  · exact cConj_mem_commutator (inv_mem h1)
  · exact cConj_mem_commutator (mul_mem h0 h1)
  · exact cConj_mem_commutator (mul_mem h1 h0)

private theorem mSCheck_true :
    mSCheck = true :=
  Certificates.certificate10032.2.2.2.2.2.1

theorem m_eq_S
    (i : Fin 2) : m i = evalWord S (mInS.getD i.val []) :=
  (is_prM i).eq_of (is_wordPR forall₂_S _) (forall_fin_of_all mSCheck_true i)

private theorem m_mem_commutator
    (i : Fin 2) : m i ∈ ⁅P, P⁆ := by
  rw [m_eq_S i]
  exact @evalWord_mem G _ ⁅P, P⁆ S S_mem_commutator _

theorem P_le_commutator :
    P ≤ ⁅P, P⁆ := by
  show Subgroup.closure {m 0, m 1} ≤ ⁅P, P⁆
  rw [Subgroup.closure_le]
  intro x hx
  rcases hx with rfl | hx
  · exact m_mem_commutator 0
  · rw [Set.mem_singleton_iff] at hx
    subst hx
    exact m_mem_commutator 1

theorem commutator_P :
    ⁅P, P⁆ = P := by
  refine le_antisymm (Subgroup.commutator_le.2 fun g₁ h₁ g₂ h₂ => ?_) P_le_commutator
  rw [commutatorElement_def]
  exact mul_mem (mul_mem (mul_mem h₁ h₂) (inv_mem h₁)) (inv_mem h₂)

private theorem mConjCheck_true :
    mConjCheck = true :=
  Certificates.certificate10032.2.2.2.2.2.2.1

theorem conj_e_m
    (i : Fin 2) (j : Fin 6) : m i * e j * (m i)⁻¹ = iota (actP i j) :=
  ((is_prM i).conj (is_prE j)).eq_of (is_prIota _)
    (forall_fin_of_all (forall_fin_of_all mConjCheck_true i) j)

theorem conj_iota_m
    (i : Fin 2) (v : Fin 6 → ZMod 3) :
    m i * iota v * (m i)⁻¹ = iota (v ᵥ* actP i) :=
  conjMat_of_rows (conj_e_m i) v

theorem actP_w1 : ∀ i : Fin 2, actP i *ᵥ w1 = w1 :=
  Certificates.certificate10032.2.2.2.2.2.2.2.1

private theorem w1_dotProduct_vecMul {A : Matrix (Fin 6) (Fin 6) (ZMod 3)} (h : A *ᵥ w1 = w1)
    (v : Fin 6 → ZMod 3) : w1 ⬝ᵥ (v ᵥ* A) = w1 ⬝ᵥ v := by
  rw [hyp_conj, h, dotProduct_comm]

private def Pres (g : G) : Prop :=
  ∀ v, ∃ u, g * iota v * g⁻¹ = iota u ∧ w1 ⬝ᵥ u = w1 ⬝ᵥ v

private theorem Pres.one : Pres 1 := fun v => ⟨v, by simp, rfl⟩

private theorem Pres.mul
    {g h : G} (hg : Pres g) (hh : Pres h) : Pres (g * h) := by
  intro v
  obtain ⟨u, hu1, hu2⟩ := hh v
  obtain ⟨u', hu1', hu2'⟩ := hg u
  refine ⟨u', ?_, hu2'.trans hu2⟩
  rw [show g * h * iota v * (g * h)⁻¹ = g * (h * iota v * h⁻¹) * g⁻¹ by group, hu1, hu1']

private theorem Pres.inv
    {g : G} (hg : Pres g) : Pres g⁻¹ := by
  classical
  choose φ hφ1 hφ2 using hg
  have hinj : Function.Injective φ := by
    intro v v' h
    apply iota_injective
    have h1 := hφ1 v
    rw [h] at h1
    have h2 := h1.trans (hφ1 v').symm
    exact mul_left_cancel (mul_right_cancel h2)
  have hsurj := Finite.injective_iff_surjective.1 hinj
  intro v
  obtain ⟨u, hu⟩ := hsurj v
  refine ⟨u, ?_, ?_⟩
  · have h1 := hφ1 u
    rw [hu] at h1
    rw [inv_inv, ← h1]
    group
  · rw [← hφ2 u, hu]

private theorem pres_m
    (i : Fin 2) : Pres (m i) := fun v =>
  ⟨v ᵥ* actP i, conj_iota_m i v, w1_dotProduct_vecMul (actP_w1 i) v⟩

private theorem pres_of_mem_closure
    {p : G}
    (hp : p ∈ Subgroup.closure ({m 0, m 1} : Set G)) : Pres p := by
  induction hp using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | hx
    · exact pres_m 0
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact pres_m 1
  | one => exact Pres.one
  | mul x y _ _ hx hy => exact hx.mul hy
  | inv x _ hx => exact hx.inv

theorem P_conj_iota
    {p : G} (hp : p ∈ P) (v : Fin 6 → ZMod 3) :
    ∃ u, p * iota v * p⁻¹ = iota u ∧ w1 ⬝ᵥ u = w1 ⬝ᵥ v :=
  pres_of_mem_closure hp v

private theorem rConjCheck_true :
    rConjCheck = true :=
  Certificates.certificate10032.2.2.2.2.2.2.2.2.1

theorem conj_e_r
    (k : Fin 12) (j : Fin 6) : r k * e j * (r k)⁻¹ = iota (actR k j) :=
  ((is_prR k).conj (is_prE j)).eq_of (is_prIota _)
    (forall_fin_of_all (forall_fin_of_all rConjCheck_true k) j)

theorem conj_iota_r
    (k : Fin 12) (v : Fin 6 → ZMod 3) :
    r k * iota v * (r k)⁻¹ = iota (v ᵥ* actR k) :=
  conjMat_of_rows (conj_e_r k) v

theorem actR_repw :
    ∀ k : Fin 12, ∃ c : ZMod 3, c ≠ 0 ∧ actR k *ᵥ repw k = c • w1 :=
  Certificates.certificate10032.2.2.2.2.2.2.2.2.2.1

theorem hyp_r (k : Fin 12) (v : Fin 6 → ZMod 3) :
    repw k ⬝ᵥ (v ᵥ* actR k) = 0 ↔ w1 ⬝ᵥ v = 0 := by
  obtain ⟨c, hc, h⟩ := actR_repw k
  rw [hyp_conj, h, dotProduct_comm, dotProduct_smul, smul_eq_mul, dotProduct_comm, mul_eq_zero]
  simp [hc]

theorem repw_zero : repw 0 = w1 :=
  Certificates.certificate10032.2.2.2.2.2.2.2.2.2.2.1

theorem r_zero : r 0 = 1 := by
  show wN (repStr 0) = 1
  have : repStr 0 = "" := rfl
  rw [this]
  rfl

theorem w1_dotProduct_v0 : w1 ⬝ᵥ v0 = 1 :=
  Certificates.certificate10032.2.2.2.2.2.2.2.2.2.2.2.1

private theorem decCheck_true :
    decCheck = true :=
  Certificates.certificate10032.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem dec_spec
    (s : Fin 2) (k : Fin 12) (j : Fin 2) :
    nGen s * r k * e0 ^ j.val =
      r (decSigma s k j) * iota (decU s k j) * tau ^ decEps s k j * decP s k j :=
  (((is_prNs s).mul (is_prR k)).mul (is_prE0.pow _)).eq_of
    ((((is_prR _).mul (is_prIota _)).mul (is_prTau.pow _)).mul (is_prWM _))
    (forall_fin_of_all (forall_fin_of_all (forall_fin_of_all decCheck_true s) k) j)

theorem decP_mem
    (s : Fin 2) (k : Fin 12) (j : Fin 2) : decP s k j ∈ P := wM_mem _

theorem decEps_le_one :
    ∀ (s : Fin 2) (k : Fin 12) (j : Fin 2), decEps s k j ≤ 1 :=
  Certificates.certificate10032.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Monster.GMS.Griess13.Co1Data

module

public import CFSG.Quasithin.H13.AS91Sec4EightModel
public import CFSG.Quasithin.H13.AS91Sec4SevenN

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.AS91

open Subgroup Module CFSG.Open CFSG.LargeExtraspecial CFSG.Quasithin CFSG.Quasithin.HatM22
open CFSG.GF2Type.Smith1979.GammaU CFSG.GF2Type.Smith1979.GammaU.StepA
open CFSG.GF2Type.Smith1979.GammaU.Viol CFSG.GF2Type.Smith1979.GammaU.Enum
open CFSG.GF2Type.Smith1979.IdxFour

@[expose] def mulFold {X : Type*} [Monoid X] (g : ℕ → X) (k n : ℕ) : X :=
  (List.range k).foldl (fun acc j => if n.testBit j then acc * g j else acc) 1

theorem mulFold_succ {X : Type*} [Monoid X] (g : ℕ → X) (k n : ℕ) :
    mulFold g (k + 1) n = mulFold g k n * (if n.testBit k then g k else 1) := by
  simp only [mulFold, List.range_succ, List.foldl_append, List.foldl_cons, List.foldl_nil]
  split_ifs <;> simp

theorem mulFold_zero_left {X : Type*} [Monoid X] (g : ℕ → X) (n : ℕ) : mulFold g 0 n = 1 := by
  simp [mulFold]

theorem mulFold_xor {X : Type*} [Group X] {g : ℕ → X} (hc : ∀ i j, g i * g j = g j * g i)
    (hs : ∀ i, g i * g i = 1) (k a b : ℕ) :
    mulFold g k (a ^^^ b) = mulFold g k a * mulFold g k b := by
  have hcomm : ∀ (m : ℕ) (n : ℕ) (j : ℕ), mulFold g m n * g j = g j * mulFold g m n := by
    intro m n j
    induction m with
    | zero => simp [mulFold_zero_left]
    | succ m ih =>
      rw [mulFold_succ]
      split_ifs
      · rw [mul_assoc, hc m j, ← mul_assoc, ih, mul_assoc]
      · simpa using ih
  induction k with
  | zero => simp [mulFold_zero_left]
  | succ k ih =>
    rw [mulFold_succ, mulFold_succ, mulFold_succ, ih, Nat.testBit_xor]
    cases a.testBit k <;> cases b.testBit k
    · simp
    · simp only [Bool.false_xor, if_true, Bool.false_eq_true, if_false, mul_one]
      rw [mul_assoc]
    · simp only [Bool.xor_false, if_true, Bool.false_eq_true, if_false, mul_one]
      rw [mul_assoc, mul_assoc, hcomm k b k]
    · simp only [Bool.xor_self, Bool.false_eq_true, if_false, if_true, mul_one]
      rw [hcomm k b k, mul_assoc, ← mul_assoc (g k) (g k), hs k, one_mul]

theorem mulFold_two_pow {X : Type*} [Monoid X] (g : ℕ → X) {k j : ℕ} (hj : j < k) :
    mulFold g k (2 ^ j) = g j := by
  have hle : ∀ m ≤ j, mulFold g m (2 ^ j) = 1 := by
    intro m hm
    induction m with
    | zero => exact mulFold_zero_left g _
    | succ m ihm =>
      rw [mulFold_succ, ihm (by omega)]
      have : (2 ^ j).testBit m = false := by
        rw [Nat.testBit_two_pow]
        simp only [decide_eq_false_iff_not]
        omega
      simp [this]
  induction k with
  | zero => omega
  | succ k ih =>
    rw [mulFold_succ]
    rcases Nat.lt_succ_iff_lt_or_eq.mp hj with h | h
    · have : (2 ^ j).testBit k = false := by
        rw [Nat.testBit_two_pow]
        simp only [decide_eq_false_iff_not]
        omega
      rw [ih h, this]
      simp
    · subst h
      have : (2 ^ j).testBit j = true := by simp [Nat.testBit_two_pow]
      rw [hle j le_rfl, this]
      simp

theorem map_mulFold_hom {X Y : Type*} [Monoid X] [Monoid Y] (f : X →* Y) (g : ℕ → X) (k n : ℕ) :
    f (mulFold g k n) = mulFold (fun j => f (g j)) k n := by
  induction k with
  | zero => rw [mulFold_zero_left, mulFold_zero_left, map_one]
  | succ k ih =>
    rw [mulFold_succ, mulFold_succ, map_mul, ih]
    split_ifs
    · rfl
    · rw [map_one]

theorem codeOf_add (u v : V12) : codeOf (u + v) = codeOf u ^^^ codeOf v := by
  have h1 : vecOf (codeOf u ^^^ codeOf v) = u + v := by
    rw [vecOf_xor, vecOf_codeOf, vecOf_codeOf]
  have hlt : codeOf u ^^^ codeOf v < 4096 :=
    Nat.xor_lt_two_pow (n := 12) (codeOf_lt u) (codeOf_lt v)
  rw [← h1]
  exact codeOf_vecOf hlt

namespace Data41

variable {G : Type} [Group G] [Finite G] {z : G} {h : HypJ4 G z} (D : Data41 h)

section Basic

@[expose] noncomputable def Mb : Subgroup (MulAut ↥D.E) := (conjNormalizer D.E).range

@[expose] noncomputable def toMb : ↥(normalizer (D.E : Set G)) →* ↥D.Mb :=
  (conjNormalizer D.E).rangeRestrict

theorem coe_toMb_apply (n : ↥(normalizer (D.E : Set G))) (e : ↥D.E) :
    (((D.toMb n : ↥D.Mb) : MulAut ↥D.E) e : G) = n * e * (n : G)⁻¹ := rfl

theorem toMb_surjective : Function.Surjective D.toMb :=
  (conjNormalizer D.E).rangeRestrict_surjective

theorem z_mem_E : z ∈ D.E := D.E1_le_E D.z_mem_E1

@[expose] noncomputable def zE : ↥D.E := ⟨z, D.z_mem_E⟩

@[expose] noncomputable def Mz : Subgroup ↥D.Mb :=
  (MulAction.stabilizer (MulAut ↥D.E) D.zE).comap D.Mb.subtype

theorem mem_Mz {φ : ↥D.Mb} : φ ∈ D.Mz ↔ (φ : MulAut ↥D.E) D.zE = D.zE := Iff.rfl

end Basic

section Bar

variable
  (hOut : KG82HatM22Out) (hTw : KG82HatM22Twelve)

include hOut hTw

theorem G13_le_normalizer : D.G13 ≤ normalizer (D.E : Set G) := fun _ hg =>
  (D.mem_normalizer_E_iff hOut hTw (pre_le_M _ hg)).mpr hg

theorem toMb_eq_one_iff (hHat : HatM22SmallModules) (n : ↥(normalizer (D.E : Set G))) :
    D.toMb n = 1 ↔ (n : G) ∈ D.E := by
  constructor
  · intro h1
    refine D.mem_E.mpr fun y hy => ?_
    have h2 := congrArg (fun φ : ↥D.Mb => (((φ : MulAut ↥D.E) ⟨y, D.E1_le_E hy⟩ : ↥D.E) : G)) h1
    simp only [coe_toMb_apply] at h2
    change (n : G) * y * (n : G)⁻¹ = y at h2
    calc y * n = (n * y * (n : G)⁻¹) * n := by rw [h2]
      _ = n * y := by group
  · intro hn
    apply Subtype.ext
    apply MulEquiv.ext
    intro e
    apply Subtype.ext
    change (n : G) * e * (n : G)⁻¹ = e
    rw [D.E_comm hOut hTw hHat hn e.2, mul_inv_cancel_right]

theorem mem_Mz_iff {φ : ↥D.Mb} :
    φ ∈ D.Mz ↔ ∃ (m : G) (hm : m ∈ D.G13), D.toMb ⟨m, D.G13_le_normalizer hOut hTw hm⟩ = φ := by
  constructor
  · intro hφ
    obtain ⟨⟨m, hmN⟩, rfl⟩ := D.toMb_surjective φ
    have hmz : m * z * m⁻¹ = z := congrArg Subtype.val (D.mem_Mz.mp hφ)
    have hmM : m ∈ h.setting.M := h.setting.mem_M_iff.mpr (by
      rw [h.setting_z]
      calc m * z = m * z * m⁻¹ * m := by group
        _ = z * m := by rw [hmz])
    exact ⟨m, (D.mem_normalizer_E_iff hOut hTw hmM).mp hmN, rfl⟩
  · rintro ⟨m, hm, rfl⟩
    refine D.mem_Mz.mpr (Subtype.ext ?_)
    change m * z * m⁻¹ = z
    have := h.setting.z_comm (pre_le_M _ hm)
    rw [h.setting_z] at this
    rw [this, mul_inv_cancel_right]

end Bar

section Coords

@[expose] noncomputable def bE (j : ℕ) : G :=
  if j = 0 then z else D.rep (Two.w1Basis.getD (j - 1) 0)

theorem bE_mem_E1 (j : ℕ) : D.bE j ∈ D.E1 := by
  unfold bE
  split_ifs
  · exact D.z_mem_E1
  · refine D.mem_E1.mpr ⟨D.rep_mem _, ?_⟩
    rw [D.ψV_cl_rep]
    have hm := Two.w1Basis_getD_mem (j - 1)
    exact (Two.vecOf_mem_W1 (Two.w1List_lt _ hm)).mpr hm

@[expose] noncomputable def elt7 (c : ℕ) : G := mulFold D.bE 7 c

theorem mulFold_mem_E1 {g : ℕ → G} (hg : ∀ j, g j ∈ D.E1) (k n : ℕ) : mulFold g k n ∈ D.E1 := by
  induction k with
  | zero => rw [mulFold_zero_left]; exact one_mem _
  | succ k ih =>
    rw [mulFold_succ]
    split_ifs
    · exact mul_mem ih (hg k)
    · rw [mul_one]; exact ih

theorem elt7_mem_E1 (c : ℕ) : D.elt7 c ∈ D.E1 := D.mulFold_mem_E1 D.bE_mem_E1 7 c

theorem elt7_xor (a b : ℕ) : D.elt7 (a ^^^ b) = D.elt7 a * D.elt7 b :=
  mulFold_xor (fun i j => D.E1_comm (D.bE_mem_E1 i) (D.bE_mem_E1 j))
    (fun i => D.E1_sq (D.bE_mem_E1 i)) 7 a b

theorem elt7_two_pow {j : ℕ} (hj : j < 7) : D.elt7 (2 ^ j) = D.bE j := mulFold_two_pow _ hj

theorem elt7_one : D.elt7 1 = z := by
  have := D.elt7_two_pow (j := 0) (by norm_num)
  rw [pow_zero] at this
  rw [this, bE, if_pos rfl]

@[expose] noncomputable def wc (x : G) : ℕ := codeOf (D.ψV (h.setting.cl x))

theorem wc_mul {x y : G} (hx : x ∈ h.setting.QG) (hy : y ∈ h.setting.QG) :
    D.wc (x * y) = D.wc x ^^^ D.wc y := by
  rw [wc, h.setting.cl_mul hx hy, map_add, codeOf_add]
  rfl

theorem wc_eq_zero_iff {x : G} (hx : x ∈ h.setting.QG) : D.wc x = 0 ↔ x = 1 ∨ x = z := by
  have h1 : D.wc x = 0 ↔ h.setting.cl x = 0 := by
    constructor
    · intro h0
      have h2 : D.ψV (h.setting.cl x) = 0 := by
        rw [← vecOf_codeOf (D.ψV (h.setting.cl x))]
        change vecOf (D.wc x) = 0
        rw [h0, vecOf_zero]
      exact (AddEquiv.map_eq_zero_iff D.ψV).mp h2
    · intro h0
      rw [wc, h0, map_zero]
      rfl
  exact h1.trans (h.setting.cl_eq_zero_iff hx)

theorem wc_bE (j : ℕ) : D.wc (D.bE j) = if j = 0 then 0 else Two.w1Basis.getD (j - 1) 0 := by
  unfold bE
  split_ifs
  · exact (D.wc_eq_zero_iff h.setting.z_mem_QG).mpr (Or.inr rfl)
  · rw [wc, D.ψV_cl_rep, codeOf_vecOf (Two.w1List_lt _ (Two.w1Basis_getD_mem _))]

theorem wc_mulFold {g : ℕ → G} (hg : ∀ j, g j ∈ D.E1) (k n : ℕ) :
    D.wc (mulFold g k n) = Two.xorFold (fun j => D.wc (g j)) k n := by
  induction k with
  | zero =>
    rw [mulFold_zero_left, Two.xorFold_zero_left]
    exact (D.wc_eq_zero_iff (one_mem _)).mpr (Or.inl rfl)
  | succ k ih =>
    rw [mulFold_succ, Two.xorFold_succ, D.wc_mul (D.E1_le_QG (D.mulFold_mem_E1 hg k n))
      (by split_ifs; exacts [D.E1_le_QG (hg k), one_mem _]), ih]
    split_ifs
    · rfl
    · rw [(D.wc_eq_zero_iff (one_mem _)).mpr (Or.inl rfl)]

theorem wc_elt7 (c : ℕ) : D.wc (D.elt7 c) = Two.wv7 c := by
  rw [elt7, D.wc_mulFold D.bE_mem_E1, Two.wv7]
  congr 1
  funext j
  rw [D.wc_bE]

theorem wc_mem {x : G} (hx : x ∈ D.E1) : D.wc x ∈ Two.w1List := Two.mem_W1_iff.mp hx.2

open scoped Classical in
@[expose] noncomputable def crd (x : G) : ℕ :=
  if D.elt7 (2 * Two.crd6 (D.wc x)) = x then 2 * Two.crd6 (D.wc x) else 2 * Two.crd6 (D.wc x) + 1

theorem crd_lt (x : G) (hx : x ∈ D.E1) : D.crd x < 128 := by
  have := Two.crd6_lt _ (D.wc_mem hx)
  unfold crd
  split_ifs <;> omega

theorem elt7_crd {x : G} (hx : x ∈ D.E1) : D.elt7 (D.crd x) = x := by
  set b := Two.crd6 (D.wc x) with hb
  have hb64 : b < 64 := Two.crd6_lt _ (D.wc_mem hx)
  have hw : D.wc (D.elt7 (2 * b)) = D.wc x := by
    rw [D.wc_elt7, Two.wv7_two_mul b hb64, hb, Two.vec6_crd6 _ (D.wc_mem hx)]
  have hcl : h.setting.cl (D.elt7 (2 * b)) = h.setting.cl x := by
    apply D.ψV.injective
    rw [← vecOf_codeOf (D.ψV (h.setting.cl (D.elt7 (2 * b)))), ← vecOf_codeOf (D.ψV (h.setting.cl x))]
    exact congrArg vecOf hw
  unfold crd
  split_ifs with h1
  · exact h1
  · rcases (h.setting.cl_eq_cl_iff (D.E1_le_QG hx) (D.E1_le_QG (D.elt7_mem_E1 _))).mp hcl.symm with
      h2 | h2
    · exact absurd h2 h1
    · rw [← Two.two_mul_xor_one b hb64, D.elt7_xor, D.elt7_one, h2, mul_assoc]
      have hz2 : h.setting.z * z = 1 := h.setting.z_mul_z
      rw [hz2, mul_one]

theorem elt7_eq_one {c : ℕ} (hc : c < 128) (h1 : D.elt7 c = 1) : c = 0 := by
  have hw := D.wc_elt7 c
  rw [h1, (D.wc_eq_zero_iff (one_mem _)).mpr (Or.inl rfl)] at hw
  have hc2 := Two.lt_two_of_wv7 c hc hw.symm
  interval_cases c
  · rfl
  · rw [D.elt7_one] at h1
    exact absurd h1 h.setting.z_ne_one

theorem elt7_injective {a b : ℕ} (ha : a < 128) (hb : b < 128) (h1 : D.elt7 a = D.elt7 b) :
    a = b := by
  have h2 : D.elt7 (a ^^^ b) = 1 := by
    rw [D.elt7_xor, h1, D.E1_sq (D.elt7_mem_E1 b)]
  have := D.elt7_eq_one (Nat.xor_lt_two_pow (n := 7) ha hb) h2
  calc a = (a ^^^ b) ^^^ b := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
    _ = b := by rw [this, Nat.zero_xor]

theorem crd_elt7 {c : ℕ} (hc : c < 128) : D.crd (D.elt7 c) = c :=
  D.elt7_injective (D.crd_lt _ (D.elt7_mem_E1 c)) hc (D.elt7_crd (D.elt7_mem_E1 c))

theorem crd_mul {x y : G} (hx : x ∈ D.E1) (hy : y ∈ D.E1) :
    D.crd (x * y) = D.crd x ^^^ D.crd y := by
  conv_lhs => rw [← D.elt7_crd hx, ← D.elt7_crd hy, ← D.elt7_xor]
  exact D.crd_elt7 (Nat.xor_lt_two_pow (n := 7) (D.crd_lt x hx) (D.crd_lt y hy))

theorem crd_injective {x y : G} (hx : x ∈ D.E1) (hy : y ∈ D.E1) (h1 : D.crd x = D.crd y) :
    x = y := by
  rw [← D.elt7_crd hx, ← D.elt7_crd hy, h1]

theorem crd_z : D.crd z = 1 := by
  have := D.crd_elt7 (c := 1) (by norm_num)
  rwa [D.elt7_one] at this

theorem crd_bE {j : ℕ} (hj : j < 7) : D.crd (D.bE j) = 2 ^ j := by
  rw [← D.elt7_two_pow hj]
  exact D.crd_elt7 (by interval_cases j <;> norm_num)

theorem crd_mulFold {g : ℕ → G} (hg : ∀ j, g j ∈ D.E1) (k n : ℕ) :
    D.crd (mulFold g k n) = Two.xorFold (fun j => D.crd (g j)) k n := by
  induction k with
  | zero =>
    rw [mulFold_zero_left, Two.xorFold_zero_left, ← D.elt7_eq_one (c := D.crd 1)
      (D.crd_lt _ (one_mem _)) (D.elt7_crd (one_mem _))]
  | succ k ih =>
    rw [mulFold_succ, Two.xorFold_succ]
    split_ifs
    · rw [D.crd_mul (D.mulFold_mem_E1 hg k n) (hg k), ih]
    · rw [mul_one, ih]
      simp

end Coords

section Kap

@[expose] noncomputable def bEE (j : ℕ) : ↥D.E := ⟨D.bE j, D.E1_le_E (D.bE_mem_E1 j)⟩

@[expose] noncomputable def kap (φ : MulAut ↥D.E) : Array ℕ :=
  ((List.range 7).map fun j => D.crd ((φ (D.bEE j) : ↥D.E) : G)).toArray

theorem kap_size (φ : MulAut ↥D.E) : (D.kap φ).size = 7 := by simp [kap]

theorem kap_getElem (φ : MulAut ↥D.E) {j : ℕ} (hj : j < 7) :
    (D.kap φ)[j]! = D.crd ((φ (D.bEE j) : ↥D.E) : G) := by
  rw [getElem!_pos _ j (by rw [kap_size]; exact hj)]
  simp [kap]

@[expose] def PresE1 (φ : MulAut ↥D.E) : Prop :=
  ∀ x : ↥D.E, (x : G) ∈ D.E1 → ((φ x : ↥D.E) : G) ∈ D.E1

theorem coe_mulFold_bEE (n : ℕ) : ((mulFold D.bEE 7 n : ↥D.E) : G) = D.elt7 n :=
  map_mulFold_hom D.E.subtype _ _ _

theorem crd_apply {φ : MulAut ↥D.E} (hφ : D.PresE1 φ) {x : ↥D.E} (hx : (x : G) ∈ D.E1) :
    D.crd ((φ x : ↥D.E) : G) = Two.app7 (D.kap φ) (D.crd x) := by
  set c := D.crd (x : G)
  have hx' : x = mulFold D.bEE 7 c := Subtype.ext (by rw [coe_mulFold_bEE, D.elt7_crd hx])
  have h1 : ((φ x : ↥D.E) : G) = mulFold (fun j => ((φ (D.bEE j) : ↥D.E) : G)) 7 c := by
    rw [hx', show φ (mulFold D.bEE 7 c) = mulFold (fun j => φ (D.bEE j)) 7 c from
      map_mulFold_hom φ.toMonoidHom _ _ _]
    exact map_mulFold_hom D.E.subtype _ _ _
  rw [h1, D.crd_mulFold (fun j => hφ _ (D.bE_mem_E1 j)), Two.app7_eq]
  exact Two.xorFold_congr (fun j hj => (D.kap_getElem φ hj).symm) c

theorem kap_mul {φ ψ : MulAut ↥D.E} (hφ : D.PresE1 φ) (hψ : D.PresE1 ψ) :
    D.kap (φ * ψ) = Two.mul7 (D.kap φ) (D.kap ψ) := by
  apply Array.ext
  · simp [Two.mul7, kap_size]
  · intro j h1 h2
    have hj : j < 7 := by rwa [kap_size] at h1
    have e1 := D.kap_getElem (φ * ψ) hj
    rw [getElem!_pos _ j h1] at e1
    rw [e1]
    simp only [Two.mul7, Array.getElem_map]
    rw [← getElem!_pos (D.kap ψ) j (by rw [kap_size]; exact hj), D.kap_getElem ψ hj,
      ← D.crd_apply hφ (hψ _ (D.bE_mem_E1 j))]
    rfl

theorem kap_one : D.kap 1 = Two.id7 := by
  apply Array.ext
  · simp [kap_size, Two.id7]
  · intro j h1 h2
    have hj : j < 7 := by rwa [kap_size] at h1
    have e1 := D.kap_getElem 1 hj
    rw [getElem!_pos _ j h1] at e1
    rw [e1]
    change D.crd (D.bE j) = _
    rw [D.crd_bE hj]
    interval_cases j <;> rfl

end Kap

end Data41

end CFSG.Quasithin.H13.AS91

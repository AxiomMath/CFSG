module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3Str

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3E

open GoldAmL3

open scoped commutatorElement

variable {D : Type*} [Group D]

theorem comm_mul_right (x y z : D) : ⁅x, y * z⁆ = ⁅x, y⁆ * (y * ⁅x, z⁆ * y⁻¹) := by
  simp only [commutatorElement_def]; group

theorem comm_mul_left (x y z : D) : ⁅x * y, z⁆ = x * ⁅y, z⁆ * x⁻¹ * ⁅x, z⁆ := by
  simp only [commutatorElement_def]; group

theorem conj_comm (g x y : D) : g * ⁅x, y⁆ * g⁻¹ = ⁅g * x * g⁻¹, g * y * g⁻¹⁆ := by
  simp only [commutatorElement_def]; group

theorem comm_eq_one_iff {x y : D} : ⁅x, y⁆ = 1 ↔ x * y = y * x := by
  rw [commutatorElement_eq_one_iff_mul_comm]

theorem comm_inv_right (x y : D) : ⁅x, y⁻¹⁆ = y⁻¹ * ⁅x, y⁆⁻¹ * y := by
  simp only [commutatorElement_def]; group

theorem comm_mul_right_of_comm {x y z : D} (h : y * ⁅x, z⁆ = ⁅x, z⁆ * y) :
    ⁅x, y * z⁆ = ⁅x, y⁆ * ⁅x, z⁆ := by
  rw [comm_mul_right]
  congr 1
  calc y * ⁅x, z⁆ * y⁻¹ = ⁅x, z⁆ * y * y⁻¹ := by rw [h]
    _ = ⁅x, z⁆ := by group

theorem conj_eq_of_comm {y c : D} (h : y * c = c * y) : y * c * y⁻¹ = c := by
  rw [h]; group

section Conj

variable {A B : Subgroup D}

theorem pCoreOf_conj_mem {g q : D} (hg : g ∈ A) (hq : q ∈ pCoreOf 2 A) :
    g * q * g⁻¹ ∈ pCoreOf 2 A :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 A hg) q).mp hq

theorem conjClosure_conj_mem {Z : Subgroup D} {g w : D} (hg : g ∈ A) (hw : w ∈ conjClosure Z A) :
    g * w * g⁻¹ ∈ conjClosure Z A :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure Z A hg) w).mp hw

theorem coreIn_conj_mem {K : Subgroup D} {g k : D} (hg : g ∈ B) (hk : k ∈ coreIn K B) :
    g * k * g⁻¹ ∈ coreIn K B :=
  (Subgroup.mem_normalizer_iff.mp (le_normalizer_coreIn _ _ hg) k).mp hk

end Conj

variable [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

structure Ctx (A B : Subgroup D) (z : D) (V : Subgroup D) : Prop where
  hyp : GoldHyp3 A B z V
  card_eq : Nat.card (conjClosure V B) = 8
  crit_eq : critDist (A ⊔ B) A B V = 3

@[expose] def Wsub (A B : Subgroup D) (V : Subgroup D) : Subgroup D :=
  conjClosure (conjClosure V B) A

@[expose] def Msub (A B : Subgroup D) (V : Subgroup D) : Subgroup D :=
  pCoreOf 2 A ⊓ Subgroup.centralizer (Wsub A B V : Set D)

namespace Ctx

theorem V_comm (c : Ctx A B z V) {v q : D} (hv : v ∈ V) (hq : q ∈ pCoreOf 2 A) :
    v * q = q * v :=
  Subgroup.mem_centralizer_iff.mp (c.hyp.pCoreOf_left_le_centralizer hq) v hv

theorem conj_V (c : Ctx A B z V) {v q : D} (hv : v ∈ V) (hq : q ∈ pCoreOf 2 A) :
    q * v * q⁻¹ = v :=
  conj_eq_of_comm (c.V_comm hv hq).symm

theorem comm_U_Q (c : Ctx A B z V) {u q : D} (hu : u ∈ conjClosure V B)
    (hq : q ∈ pCoreOf 2 A) : ⁅u, q⁆ ∈ V :=
  c.hyp.commutator_mem_V_of_pCoreOf_left c.card_eq hu hq

theorem U_le_Q (c : Ctx A B z V) : conjClosure V B ≤ pCoreOf 2 A :=
  c.hyp.conjClosure_le_pCoreOf_left

theorem U_le_P (c : Ctx A B z V) : conjClosure V B ≤ pCoreOf 2 B :=
  c.hyp.conjClosure_le_pCoreOf_right

omit [Finite D] in
theorem V_normal (c : Ctx A B z V) {g v : D} (hg : g ∈ A) (hv : v ∈ V) : g * v * g⁻¹ ∈ V :=
  (Subgroup.mem_normalizer_iff.mp (c.hyp.natural.reduced.2.1 hg) v).mp hv

omit [Finite D] in
theorem U_normal (_c : Ctx A B z V) {g u : D} (hg : g ∈ B) (hu : u ∈ conjClosure V B) :
    g * u * g⁻¹ ∈ conjClosure V B :=
  conjClosure_conj_mem hg hu

theorem Q_le_T (c : Ctx A B z V) : pCoreOf 2 A ≤ A ⊓ B := c.hyp.gold.pCoreOf_left_le

theorem P_le_T (c : Ctx A B z V) : pCoreOf 2 B ≤ A ⊓ B := c.hyp.gold.pCoreOf_right_le

theorem mem_K_iff (c : Ctx A B z V) {k : D} :
    k ∈ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B ↔
      k ∈ pCoreOf 2 A ∧ ∀ u ∈ conjClosure V B, u * k = k * u :=
  ⟨fun hk => ⟨coreIn_right_le_pCoreOf_left hk, c.hyp.comm_of_mem_coreIn hk⟩,
    fun hk => c.hyp.mem_coreIn_of_comm hk.1 hk.2⟩

theorem W_spec (c : Ctx A B z V) {w : D} (hw : w ∈ Wsub A B V) :
    w ∈ pCoreOf 2 A ∧ ∀ q ∈ pCoreOf 2 A, ⁅w, q⁆ ∈ V := by
  unfold Wsub conjClosure at hw
  induction hw using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨g, hg, u, hu, rfl⟩ := hx
    refine ⟨pCoreOf_conj_mem hg (c.U_le_Q hu), fun q hq => ?_⟩
    have h1 := c.comm_U_Q hu (pCoreOf_conj_mem (A.inv_mem hg) hq)
    have h2 := c.V_normal hg h1
    have e : ⁅g * u * g⁻¹, q⁆ = g * ⁅u, g⁻¹ * q * g⁻¹⁻¹⁆ * g⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e]; exact h2
  | one =>
    refine ⟨Subgroup.one_mem _, fun q _ => ?_⟩
    rw [show ⁅(1 : D), q⁆ = 1 by simp [commutatorElement_def]]
    exact V.one_mem
  | mul x y _ _ ihx ihy =>
    refine ⟨(pCoreOf 2 A).mul_mem ihx.1 ihy.1, fun q hq => ?_⟩
    rw [comm_mul_left, c.conj_V (ihy.2 q hq) ihx.1]
    exact V.mul_mem (ihy.2 q hq) (ihx.2 q hq)
  | inv x _ ih =>
    refine ⟨(pCoreOf 2 A).inv_mem ih.1, fun q hq => ?_⟩
    have e : ⁅x⁻¹, q⁆ = x⁻¹ * ⁅x, q⁆⁻¹ * x⁻¹⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [e, c.conj_V (V.inv_mem (ih.2 q hq)) ((pCoreOf 2 A).inv_mem ih.1)]
    exact V.inv_mem (ih.2 q hq)

theorem W_le_Q (c : Ctx A B z V) : Wsub A B V ≤ pCoreOf 2 A := fun _ hw => (c.W_spec hw).1

theorem comm_W_Q (c : Ctx A B z V) {w q : D} (hw : w ∈ Wsub A B V) (hq : q ∈ pCoreOf 2 A) :
    ⁅w, q⁆ ∈ V :=
  (c.W_spec hw).2 q hq

omit [Finite D] in
theorem U_le_W (_c : Ctx A B z V) : conjClosure V B ≤ Wsub A B V := le_conjClosure _ _

omit [Finite D] in
theorem V_le_U (_c : Ctx A B z V) : V ≤ conjClosure V B := le_conjClosure _ _

omit [Finite D] in
theorem W_normal (_c : Ctx A B z V) {g w : D} (hg : g ∈ A) (hw : w ∈ Wsub A B V) :
    g * w * g⁻¹ ∈ Wsub A B V :=
  conjClosure_conj_mem hg hw

omit [Finite D] in
theorem conj_mem_W (_c : Ctx A B z V) {g u : D} (hg : g ∈ A) (hu : u ∈ conjClosure V B) :
    g * u * g⁻¹ ∈ Wsub A B V :=
  mem_conjClosure hg hu

omit [Finite D] in
theorem mem_M_iff (_c : Ctx A B z V) {m : D} :
    m ∈ Msub A B V ↔ m ∈ pCoreOf 2 A ∧ ∀ w ∈ Wsub A B V, w * m = m * w := by
  unfold Msub
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  exact Iff.rfl

omit [Finite D] in
theorem M_normal (c : Ctx A B z V) {g m : D} (hg : g ∈ A) (hm : m ∈ Msub A B V) :
    g * m * g⁻¹ ∈ Msub A B V := by
  rw [c.mem_M_iff] at hm ⊢
  refine ⟨pCoreOf_conj_mem hg hm.1, fun w hw => ?_⟩
  have h := hm.2 (g⁻¹ * w * g⁻¹⁻¹) (by simpa using c.W_normal (A.inv_mem hg) hw)
  calc w * (g * m * g⁻¹) = g * ((g⁻¹ * w * g⁻¹⁻¹) * m) * g⁻¹ := by group
    _ = g * (m * (g⁻¹ * w * g⁻¹⁻¹)) * g⁻¹ := by rw [h]
    _ = (g * m * g⁻¹) * w := by group

theorem M_le_K (c : Ctx A B z V) : Msub A B V ≤ coreIn (pCoreOf 2 A ⊓ pCoreOf 2 B) B := by
  intro m hm
  rw [c.mem_M_iff] at hm
  exact (c.mem_K_iff).mpr ⟨hm.1, fun u hu => hm.2 u (c.U_le_W hu)⟩

theorem V_le_M (c : Ctx A B z V) : V ≤ Msub A B V := by
  intro v hv
  rw [c.mem_M_iff]
  exact ⟨c.U_le_Q (c.V_le_U hv), fun w hw => (c.V_comm hv (c.W_le_Q hw)).symm⟩

theorem not_normal_T_left (c : Ctx A B z V) :
    ¬ A ≤ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) := by
  intro hAN
  have hTQ : A ⊓ B ≤ pCoreOf 2 A :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hAN
      (c.hyp.gold.isSylowTwoOf_left.2.1.to_le le_rfl)
  have h1 : (pCoreOf 2 A).relIndex (A ⊓ B) = 1 := Subgroup.relIndex_eq_one.mpr hTQ
  have h2 := c.hyp.gold.relIndex_pCoreOf_T_left
  omega

theorem not_normal_T_right (c : Ctx A B z V) :
    ¬ B ≤ Subgroup.normalizer ((A ⊓ B : Subgroup D) : Set D) := by
  intro hBN
  have hTP : A ⊓ B ≤ pCoreOf 2 B :=
    le_pCoreOf_of_le_normalizer 2 inf_le_right hBN
      (c.hyp.gold.isSylowTwoOf_right.2.1.to_le le_rfl)
  have h1 : (pCoreOf 2 B).relIndex (A ⊓ B) = 1 := Subgroup.relIndex_eq_one.mpr hTP
  have h2 := c.hyp.gold.relIndex_pCoreOf_T_right
  omega

theorem eq_left_of_normal (c : Ctx A B z V) {C : Subgroup D} (hTC : A ⊓ B ≤ C) (hCA : C ≤ A)
    (hN : A ≤ Subgroup.normalizer (C : Set D)) : C = A := by
  have hmul := Subgroup.relIndex_mul_relIndex (A ⊓ B) C A hTC hCA
  rw [c.hyp.gold.relIndex_left] at hmul
  have hdvd : C.relIndex A ∣ 3 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact le_antisymm hCA (Subgroup.relIndex_eq_one.mp h1)
  · exfalso
    rw [h3] at hmul
    have h4 : (A ⊓ B).relIndex C = 1 := by omega
    have hCT : C = A ⊓ B := le_antisymm (Subgroup.relIndex_eq_one.mp h4) hTC
    apply c.not_normal_T_left
    rw [← hCT]; exact hN

theorem eq_right_of_normal (c : Ctx A B z V) {C : Subgroup D} (hTC : A ⊓ B ≤ C) (hCB : C ≤ B)
    (hN : B ≤ Subgroup.normalizer (C : Set D)) : C = B := by
  have hmul := Subgroup.relIndex_mul_relIndex (A ⊓ B) C B hTC hCB
  rw [c.hyp.gold.relIndex_right] at hmul
  have hdvd : C.relIndex B ∣ 3 := Dvd.intro_left _ hmul
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact le_antisymm hCB (Subgroup.relIndex_eq_one.mp h1)
  · exfalso
    rw [h3] at hmul
    have h4 : (A ⊓ B).relIndex C = 1 := by omega
    have hCT : C = A ⊓ B := le_antisymm (Subgroup.relIndex_eq_one.mp h4) hTC
    apply c.not_normal_T_right
    rw [← hCT]; exact hN

end Ctx

end GoldAmL3E

end F6

end CFSG.Quasithin

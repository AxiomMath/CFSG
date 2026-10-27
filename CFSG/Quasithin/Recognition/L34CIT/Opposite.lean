module

public import CFSG.Quasithin.Recognition.L34CIT.Parabolics
public import CFSG.GroupTheory.WielandtProductBasic
public import CFSG.GroupTheory.GL52.Basic

public section

namespace CFSG.Quasithin.L34CIT

open Subgroup CFSG.Open
open scoped Pointwise
open CFSG.GroupTheory.WielandtProduct (mem_conj_smul_iff)

variable {A : Type} [Group A]

private theorem smul_eq_map (a : A) (H : Subgroup A) :
    MulAut.conj a • H = H.map (MulAut.conj a).toMonoidHom :=
  rfl

private theorem smul_smul_conj (a b : A) (H : Subgroup A) :
    MulAut.conj a • (MulAut.conj b • H) = MulAut.conj (a * b) • H := by
  ext x
  rw [mem_conj_smul_iff (g := a) (H := MulAut.conj b • H),
    mem_conj_smul_iff (g := b) (H := H),
    mem_conj_smul_iff (g := a * b) (H := H)]
  constructor
  · intro h; simpa [mul_assoc] using h
  · intro h; simpa [mul_assoc] using h

@[simp] private theorem smul_inv_smul_conj (a : A) (H : Subgroup A) :
    MulAut.conj a • (MulAut.conj a⁻¹ • H) = H := by
  rw [smul_smul_conj, mul_inv_cancel, map_one, one_smul]

@[simp] private theorem inv_smul_smul_conj (a : A) (H : Subgroup A) :
    MulAut.conj a⁻¹ • (MulAut.conj a • H) = H := by
  rw [smul_smul_conj, inv_mul_cancel, map_one, one_smul]

private theorem centralizer_conj_smul (a x : A) :
    centralizer ({a * x * a⁻¹} : Set A) = MulAut.conj a • centralizer ({x} : Set A) := by
  rw [CFSG.GroupTheory.GL52.centralizer_conj, smul_eq_map]

namespace Config

variable (C : Config A)

theorem centralizer_Z_conj {a v : A} (hv : v ∈ MulAut.conj a • C.Z) (hv1 : v ≠ 1) :
    centralizer ({v} : Set A) = MulAut.conj a • (C.T : Subgroup A) := by
  have hy : a⁻¹ * v * a ∈ C.Z := (mem_conj_smul_iff (g := a) (H := C.Z) (x := v)).mp hv
  have hy1 : a⁻¹ * v * a ≠ 1 := by
    intro h
    exact hv1 (by rw [show v = a * (a⁻¹ * v * a) * a⁻¹ by group, h, mul_one, mul_inv_cancel])
  rw [show v = a * (a⁻¹ * v * a) * a⁻¹ by group, centralizer_conj_smul,
    C.centralizer_eq_T hy hy1]

theorem centralizer_point_conj {a x : A} (hx : x ∈ MulAut.conj a • C.L)
    (hxZ : x ∉ MulAut.conj a • C.Z) :
    centralizer ({x} : Set A) ⊓ (MulAut.conj a • (C.T : Subgroup A)) =
      MulAut.conj a • C.L := by
  have hy : a⁻¹ * x * a ∈ C.L := (mem_conj_smul_iff (g := a) (H := C.L) (x := x)).mp hx
  have hyZ : a⁻¹ * x * a ∉ C.Z := fun h =>
    hxZ ((mem_conj_smul_iff (g := a) (H := C.Z) (x := x)).mpr h)
  conv_lhs => rw [show x = a * (a⁻¹ * x * a) * a⁻¹ by group]
  rw [centralizer_conj_smul, ← Subgroup.smul_inf, C.centralizer_L _ hy hyZ]

theorem centralizer_line_conj {a y : A} (hy : y ∈ MulAut.conj a • C.M)
    (hyZ : y ∉ MulAut.conj a • C.Z) :
    centralizer ({y} : Set A) ⊓ (MulAut.conj a • (C.T : Subgroup A)) =
      MulAut.conj a • C.M := by
  have hy' : a⁻¹ * y * a ∈ C.M := (mem_conj_smul_iff (g := a) (H := C.M) (x := y)).mp hy
  have hyZ' : a⁻¹ * y * a ∉ C.Z := fun h =>
    hyZ ((mem_conj_smul_iff (g := a) (H := C.Z) (x := y)).mpr h)
  conv_lhs => rw [show y = a * (a⁻¹ * y * a) * a⁻¹ by group]
  rw [centralizer_conj_smul, ← Subgroup.smul_inf, C.centralizer_M _ hy' hyZ']

theorem eq_or_eq_conj {a : A} {E : Subgroup A} (hE : E ≤ MulAut.conj a • (C.T : Subgroup A))
    (hEea : IsElemAbelian 2 E) (hEcard : Nat.card E = 16) :
    E = MulAut.conj a • C.L ∨ E = MulAut.conj a • C.M := by
  have hle : MulAut.conj a⁻¹ • E ≤ (C.T : Subgroup A) := by
    rw [← inv_smul_smul_conj a (C.T : Subgroup A)]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr hE
  rcases C.eq_or_eq (MulAut.conj a⁻¹ • E) hle (isElemAbelian_conj hEea a⁻¹)
      (by rw [card_conj, hEcard]) with h | h
  · left
    rw [show E = MulAut.conj a • (MulAut.conj a⁻¹ • E) from by simp, h]
  · right
    rw [show E = MulAut.conj a • (MulAut.conj a⁻¹ • E) from by simp, h]

theorem card_inf_conj (a : A) :
    Nat.card ↥(MulAut.conj a • C.L ⊓ MulAut.conj a • C.M) = 4 := by
  rw [← Subgroup.smul_inf, card_conj, C.card_inf]

theorem inf_le_centralizer_conj (a : A) :
    MulAut.conj a • C.L ⊓ MulAut.conj a • C.M ≤
      centralizer (MulAut.conj a • (C.T : Subgroup A) : Set A) := by
  rw [← Subgroup.smul_inf]
  intro x hx
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have hx' : a⁻¹ * x * a ∈ C.Z := (mem_conj_smul_iff (g := a) (H := C.Z) (x := x)).mp hx
  have hy' : a⁻¹ * y * a ∈ C.T := (mem_conj_smul_iff (g := a) (H := C.T) (x := y)).mp hy
  have hcomm : (a⁻¹ * y * a) * (a⁻¹ * x * a) = (a⁻¹ * x * a) * (a⁻¹ * y * a) :=
    Subgroup.mem_centralizer_iff.mp (C.inf_le_centralizer hx') _ hy'
  calc y * x = a * ((a⁻¹ * y * a) * (a⁻¹ * x * a)) * a⁻¹ := by group
    _ = a * ((a⁻¹ * x * a) * (a⁻¹ * y * a)) * a⁻¹ := by rw [hcomm]
    _ = x * y := by group

theorem mem_point_or_line_conj [Finite A] {a x : A} (hx : x ∈ MulAut.conj a • (C.T : Subgroup A))
    (hx2 : x * x = 1) (hx1 : x ≠ 1) :
    x ∈ MulAut.conj a • C.L ∨ x ∈ MulAut.conj a • C.M :=
  C.mem_point_or_line_of_mem_sylow hx hx2 hx1

theorem sup_conj [Finite A] (a : A) :
    MulAut.conj a • C.L ⊔ MulAut.conj a • C.M = MulAut.conj a • (C.T : Subgroup A) := by
  rw [← Subgroup.smul_sup, C.sup_eq]

section PointLine

variable [Finite A]

theorem point_eq_of_smul_T_eq {a b : A}
    (h : MulAut.conj a • (C.T : Subgroup A) = MulAut.conj b • (C.T : Subgroup A)) :
    MulAut.conj a • C.L = MulAut.conj b • C.L :=
  C.conj_eq_of_le_L (by
    rw [← h]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr C.L_le)

theorem line_eq_of_smul_T_eq {a b : A}
    (h : MulAut.conj a • (C.T : Subgroup A) = MulAut.conj b • (C.T : Subgroup A)) :
    MulAut.conj a • C.M = MulAut.conj b • C.M :=
  C.conj_eq_of_le_M (by
    rw [← h]
    exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr C.M_le)

private theorem exists_point_of_sylow (P : Sylow 2 A) :
    ∃ E : Subgroup A, ∃ a : A,
      (P : Subgroup A) = MulAut.conj a • (C.T : Subgroup A) ∧ E = MulAut.conj a • C.L := by
  obtain ⟨a, ha⟩ := C.exists_conj_eq P
  exact ⟨_, a, ha, rfl⟩

private theorem exists_line_of_sylow (P : Sylow 2 A) :
    ∃ E : Subgroup A, ∃ a : A,
      (P : Subgroup A) = MulAut.conj a • (C.T : Subgroup A) ∧ E = MulAut.conj a • C.M := by
  obtain ⟨a, ha⟩ := C.exists_conj_eq P
  exact ⟨_, a, ha, rfl⟩

noncomputable def point (P : Sylow 2 A) : Subgroup A :=
  Classical.choose (C.exists_point_of_sylow P)

noncomputable def line (P : Sylow 2 A) : Subgroup A :=
  Classical.choose (C.exists_line_of_sylow P)

theorem point_spec (P : Sylow 2 A) :
    ∃ a : A, (P : Subgroup A) = MulAut.conj a • (C.T : Subgroup A) ∧
      C.point P = MulAut.conj a • C.L :=
  Classical.choose_spec (C.exists_point_of_sylow P)

theorem line_spec (P : Sylow 2 A) :
    ∃ a : A, (P : Subgroup A) = MulAut.conj a • (C.T : Subgroup A) ∧
      C.line P = MulAut.conj a • C.M :=
  Classical.choose_spec (C.exists_line_of_sylow P)

theorem exists_common (P : Sylow 2 A) :
    ∃ a : A, (P : Subgroup A) = MulAut.conj a • (C.T : Subgroup A) ∧
      C.point P = MulAut.conj a • C.L ∧ C.line P = MulAut.conj a • C.M := by
  obtain ⟨a, hPa, hpa⟩ := C.point_spec P
  obtain ⟨b, hPb, hpb⟩ := C.line_spec P
  have hsame : MulAut.conj a • (C.T : Subgroup A) = MulAut.conj b • (C.T : Subgroup A) := by
    rw [← hPa, ← hPb]
  refine ⟨a, hPa, hpa, ?_⟩
  rw [hpb, C.line_eq_of_smul_T_eq hsame]

theorem point_smul (a : A) : C.point (a • C.T) = MulAut.conj a • C.L := by
  obtain ⟨b, hPb, hpb⟩ := C.point_spec (a • C.T)
  rw [hpb]
  refine C.point_eq_of_smul_T_eq ?_
  rw [← hPb, Sylow.coe_subgroup_smul]

theorem line_smul (a : A) : C.line (a • C.T) = MulAut.conj a • C.M := by
  obtain ⟨b, hPb, hpb⟩ := C.line_spec (a • C.T)
  rw [hpb]
  refine C.line_eq_of_smul_T_eq ?_
  rw [← hPb, Sylow.coe_subgroup_smul]

theorem point_le (P : Sylow 2 A) : C.point P ≤ (P : Subgroup A) := by
  obtain ⟨a, hPa, hpa⟩ := C.point_spec P
  rw [hpa, hPa]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr C.L_le

theorem line_le (P : Sylow 2 A) : C.line P ≤ (P : Subgroup A) := by
  obtain ⟨a, hPa, hpa⟩ := C.line_spec P
  rw [hpa, hPa]
  exact Subgroup.pointwise_smul_le_pointwise_smul_iff.mpr C.M_le

theorem point_ea (P : Sylow 2 A) : IsElemAbelian 2 (C.point P) := by
  obtain ⟨a, -, hpa⟩ := C.point_spec P
  rw [hpa]
  exact isElemAbelian_conj C.isElemAbelian_L a

theorem line_ea (P : Sylow 2 A) : IsElemAbelian 2 (C.line P) := by
  obtain ⟨a, -, hpa⟩ := C.line_spec P
  rw [hpa]
  exact isElemAbelian_conj C.isElemAbelian_M a

theorem card_point (P : Sylow 2 A) : Nat.card ↥(C.point P) = 16 := by
  obtain ⟨a, -, hpa⟩ := C.point_spec P
  rw [hpa, card_conj, C.card_L]

theorem card_line (P : Sylow 2 A) : Nat.card ↥(C.line P) = 16 := by
  obtain ⟨a, -, hpa⟩ := C.line_spec P
  rw [hpa, card_conj, C.card_M]

theorem sup_point_line (P : Sylow 2 A) :
    C.point P ⊔ C.line P = (P : Subgroup A) := by
  obtain ⟨a, hPa, hpa, hpb⟩ := C.exists_common P
  rw [hpa, hpb, hPa, C.sup_conj]

theorem card_inf_point_line_sylow (P : Sylow 2 A) :
    Nat.card ↥(C.point P ⊓ C.line P) = 4 := by
  obtain ⟨a, -, hpa, hpb⟩ := C.exists_common P
  rw [hpa, hpb, C.card_inf_conj]

theorem inf_le_centralizer_point_line (P : Sylow 2 A) :
    C.point P ⊓ C.line P ≤ centralizer ((P : Subgroup A) : Set A) := by
  obtain ⟨a, hPa, hpa, hpb⟩ := C.exists_common P
  rw [hpa, hpb, hPa]
  exact C.inf_le_centralizer_conj a

theorem mem_point_or_line {P : Sylow 2 A} {x : A} (hx : x ∈ (P : Subgroup A))
    (hx2 : x * x = 1) (hx1 : x ≠ 1) : x ∈ C.point P ∨ x ∈ C.line P := by
  obtain ⟨a, hPa, hpa, hpb⟩ := C.exists_common P
  rw [hPa] at hx
  rw [hpa, hpb]
  exact C.mem_point_or_line_conj hx hx2 hx1

theorem eq_point_or_line {P : Sylow 2 A} {E : Subgroup A} (hE : E ≤ (P : Subgroup A))
    (hEea : IsElemAbelian 2 E) (hEcard : Nat.card E = 16) :
    E = C.point P ∨ E = C.line P := by
  obtain ⟨a, hPa, hpa, hpb⟩ := C.exists_common P
  rw [hPa] at hE
  rw [hpa, hpb]
  exact C.eq_or_eq_conj hE hEea hEcard

theorem centralizer_point {P : Sylow 2 A} {x : A} (hx : x ∈ C.point P)
    (hxZ : x ∉ C.point P ⊓ C.line P) :
    centralizer ({x} : Set A) ⊓ (P : Subgroup A) = C.point P := by
  obtain ⟨a, hPa, hpa, hpb⟩ := C.exists_common P
  have hx' : x ∈ MulAut.conj a • C.L := by rwa [hpa] at hx
  have hxZ' : x ∉ MulAut.conj a • C.Z := by
    rw [hpa, hpb, ← Subgroup.smul_inf] at hxZ
    exact hxZ
  rw [hpa, hPa]
  exact C.centralizer_point_conj hx' hxZ'

theorem centralizer_line {P : Sylow 2 A} {x : A} (hx : x ∈ C.line P)
    (hxZ : x ∉ C.point P ⊓ C.line P) :
    centralizer ({x} : Set A) ⊓ (P : Subgroup A) = C.line P := by
  obtain ⟨a, hPa, hpa, hpb⟩ := C.exists_common P
  have hx' : x ∈ MulAut.conj a • C.M := by rwa [hpb] at hx
  have hxZ' : x ∉ MulAut.conj a • C.Z := by
    rw [hpa, hpb, ← Subgroup.smul_inf] at hxZ
    exact hxZ
  rw [hpb, hPa]
  exact C.centralizer_line_conj hx' hxZ'

theorem centralizer_Z_sylow {P : Sylow 2 A} {v : A} (hv : v ∈ C.point P ⊓ C.line P)
    (hv1 : v ≠ 1) : centralizer ({v} : Set A) = (P : Subgroup A) := by
  obtain ⟨a, hPa, hpa, hpb⟩ := C.exists_common P
  rw [hpa, hpb, ← Subgroup.smul_inf] at hv
  exact (C.centralizer_Z_conj hv hv1).trans hPa.symm

theorem point_eq_L_of_le {P : Sylow 2 A} (h : C.L ≤ (P : Subgroup A)) : C.point P = C.L := by
  obtain ⟨a, hPa, hpa⟩ := C.point_spec P
  rw [hpa]
  have h' : C.L ≤ MulAut.conj a • (C.T : Subgroup A) := by rwa [hPa] at h
  have h1 := C.conj_eq_of_le_L (a := 1) (g := a) (by simpa using h')
  simpa using h1.symm

theorem line_eq_M_of_le {P : Sylow 2 A} (h : C.M ≤ (P : Subgroup A)) : C.line P = C.M := by
  obtain ⟨a, hPa, hpa⟩ := C.line_spec P
  rw [hpa]
  have h' : C.M ≤ MulAut.conj a • (C.T : Subgroup A) := by rwa [hPa] at h
  have h1 := C.conj_eq_of_le_M (a := 1) (g := a) (by simpa using h')
  simpa using h1.symm

end PointLine

@[simp] theorem swap_Z (C : Config A) : C.swap.Z = C.Z := by
  show C.M ⊓ C.L = C.L ⊓ C.M
  rw [inf_comm]

section Classification

variable [Finite A]

private theorem card_four_of_le_L {P : Sylow 2 A} (hne : P ≠ C.T)
    (hbot : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥)
    (hbotZ : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ⊓ C.Z = ⊥)
    (hsubL : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.L)
    (hsq : ∀ x ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A), x * x = 1)
    (hcomm : ∀ x ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A),
      ∀ y ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A), x * y = y * x) :
    Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4 := by
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hbot
  set v : A := (u : A) with hv_def
  have hvD : v ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A) := u.2
  have hv1 : v ≠ 1 := fun h => hu1 (Subtype.ext (by simpa [hv_def] using h))
  have hmemP : v ∈ (P : Subgroup A) := hvD.2
  have hvL : v ∈ C.L := hsubL hvD
  have hv2 : v * v = 1 := hsq v hvD
  have hvZ : v ∉ C.Z := by
    intro hZ
    have hmem : v ∈ ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ⊓ C.Z := ⟨hvD, hZ⟩
    rw [hbotZ] at hmem
    exact hv1 (by simpa using hmem)
  have hLcontra : (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L → False := by
    intro hDL
    have hcard : Nat.card ↥(((C.T : Subgroup A) ⊓ (P : Subgroup A)) ⊓ C.Z) = 4 := by
      rw [show ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ⊓ C.Z = C.Z from
        le_antisymm inf_le_right (by rw [hDL]; exact fun x hx => ⟨C.Z_le_L hx, hx⟩), C.card_Z]
    rw [hbotZ, Subgroup.card_bot] at hcard
    norm_num at hcard
  have hvZP : v ∉ C.point P ⊓ C.line P := by
    intro hmem
    have hP : centralizer ({v} : Set A) = (P : Subgroup A) := C.centralizer_Z_sylow hmem hv1
    have hD : (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L := by
      rw [show (C.T : Subgroup A) ⊓ (P : Subgroup A) =
        (C.T : Subgroup A) ⊓ centralizer ({v} : Set A) from by rw [hP], inf_comm]
      exact C.centralizer_L v hvL hvZ
    exact hLcontra hD
  obtain ⟨Q, hQ⟩ := C.exists_sylow_eq_centralizer hv2 hv1
  have hLQ : C.L ≤ (Q : Subgroup A) := by
    rw [← hQ, ← C.centralizer_L v hvL hvZ]
    exact inf_le_left
  have hPQP : (P : Subgroup A) ⊓ (Q : Subgroup A) = C.point P ∨
      (P : Subgroup A) ⊓ (Q : Subgroup A) = C.line P := by
    rcases C.mem_point_or_line hmemP hv2 hv1 with hp | hp
    · exact Or.inl (by rw [← hQ, inf_comm]; exact C.centralizer_point hp hvZP)
    · exact Or.inr (by rw [← hQ, inf_comm]; exact C.centralizer_line hp hvZP)
  have hPQea : IsElemAbelian 2 ((P : Subgroup A) ⊓ (Q : Subgroup A)) := by
    rcases hPQP with h | h
    · rw [h]; exact C.point_ea P
    · rw [h]; exact C.line_ea P
  have hPQcard : Nat.card ↥((P : Subgroup A) ⊓ (Q : Subgroup A)) = 16 := by
    rcases hPQP with h | h
    · rw [h]; exact C.card_point P
    · rw [h]; exact C.card_line P
  have hLpq : C.L = C.point Q ∨ C.L = C.line Q :=
    C.eq_point_or_line hLQ C.isElemAbelian_L C.card_L
  have hPQq : (P : Subgroup A) ⊓ (Q : Subgroup A) = C.point Q ∨
      (P : Subgroup A) ⊓ (Q : Subgroup A) = C.line Q :=
    C.eq_point_or_line inf_le_right hPQea hPQcard
  have hDsubQ : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ (Q : Subgroup A) := by
    intro x hx
    rw [← hQ, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    exact (hcomm x hx v hvD).symm
  have hLne : C.L ≠ (P : Subgroup A) ⊓ (Q : Subgroup A) := by
    intro heq
    exact hLcontra (le_antisymm hsubL (fun x hx => ⟨C.L_le hx, (heq ▸ hx).1⟩))
  have hZQ : C.point Q ⊓ C.line Q = (C.T : Subgroup A) ⊓ (P : Subgroup A) := by
    have hpair : (C.point Q = C.L ∧ C.line Q = (P : Subgroup A) ⊓ (Q : Subgroup A)) ∨
        (C.point Q = (P : Subgroup A) ⊓ (Q : Subgroup A) ∧ C.line Q = C.L) := by
      rcases hLpq with hLp | hLl
      · left
        refine ⟨hLp.symm, ?_⟩
        rcases hPQq with h | h
        · exact absurd (hLp.trans h.symm) hLne
        · exact h.symm
      · right
        refine ⟨?_, hLl.symm⟩
        rcases hPQq with h | h
        · exact h.symm
        · exact absurd (hLl.trans h.symm) hLne
    rcases hpair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1, h2]
      refine le_antisymm ?_ ?_
      · intro x hx
        exact ⟨C.L_le hx.1, hx.2.1⟩
      · intro x hx
        exact ⟨hsubL hx, hx.2, hDsubQ hx⟩
    · rw [h1, h2]
      refine le_antisymm ?_ ?_
      · intro x hx
        exact ⟨C.L_le hx.2, hx.1.1⟩
      · intro x hx
        exact ⟨⟨hx.2, hDsubQ hx⟩, hsubL hx⟩
  rw [← hZQ]
  exact C.card_inf_point_line_sylow Q

private theorem inf_eq_L_or_M_of_mem_Z {P : Sylow 2 A} (hne : P ≠ C.T) {v : A}
    (hvD : v ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A)) (hv1 : v ≠ 1) (hvZ : v ∈ C.Z) :
    ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = C.L ∨
      ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = C.M := by
  have hCT : centralizer ({v} : Set A) = (C.T : Subgroup A) := C.centralizer_eq_T hvZ hv1
  have hvP : v ∈ (P : Subgroup A) := hvD.2
  have hv2 : v * v = 1 := by
    have h := C.isElemAbelian_L.2 v (C.Z_le_L hvZ)
    simpa [pow_two] using h
  have hvZP : v ∉ C.point P ⊓ C.line P := by
    intro hmem
    have hPT : (P : Subgroup A) = (C.T : Subgroup A) := by
      rw [← C.centralizer_Z_sylow hmem hv1, hCT]
    exact hne (Sylow.ext hPT)
  have hDP : centralizer ({v} : Set A) ⊓ (P : Subgroup A) =
      (C.T : Subgroup A) ⊓ (P : Subgroup A) := by rw [hCT]
  rcases C.mem_point_or_line hvP hv2 hv1 with hvp | hvp
  · have hD : (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.point P := by
      rw [← hDP, C.centralizer_point hvp hvZP]
    have hle : C.point P ≤ (C.T : Subgroup A) := by rw [← hD]; exact inf_le_left
    rcases C.eq_or_eq (C.point P) hle (C.point_ea P) (C.card_point P) with h | h
    · exact Or.inl (by rw [hD, h])
    · exact Or.inr (by rw [hD, h])
  · have hD : (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.line P := by
      rw [← hDP, C.centralizer_line hvp hvZP]
    have hle : C.line P ≤ (C.T : Subgroup A) := by rw [← hD]; exact inf_le_left
    rcases C.eq_or_eq (C.line P) hle (C.line_ea P) (C.card_line P) with h | h
    · exact Or.inl (by rw [hD, h])
    · exact Or.inr (by rw [hD, h])

private theorem inf_eq_L_or_M_of_mem_ZP {P : Sylow 2 A} (hne : P ≠ C.T) {v : A}
    (hvD : v ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A)) (hv1 : v ≠ 1)
    (hvZP : v ∈ C.point P ⊓ C.line P) :
    ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = C.L ∨
      ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = C.M := by
  have hcent : centralizer ({v} : Set A) = (P : Subgroup A) := C.centralizer_Z_sylow hvZP hv1
  have hvT : v ∈ (C.T : Subgroup A) := hvD.1
  have hv2 : v * v = 1 := by
    have h := (C.point_ea P).2 v hvZP.1
    simpa [pow_two] using h
  have hvZ : v ∉ C.Z := by
    intro hZ
    have hPT : (P : Subgroup A) = (C.T : Subgroup A) := by
      rw [← hcent, C.centralizer_eq_T hZ hv1]
    exact hne (Sylow.ext hPT)
  rcases C.mem_or_mem v hvT hv2 with hvL | hvM
  · exact Or.inl (by
      rw [show (C.T : Subgroup A) ⊓ (P : Subgroup A) =
        (C.T : Subgroup A) ⊓ centralizer ({v} : Set A) from by rw [hcent], inf_comm]
      exact C.centralizer_L v hvL hvZ)
  · exact Or.inr (by
      rw [show (C.T : Subgroup A) ⊓ (P : Subgroup A) =
        (C.T : Subgroup A) ⊓ centralizer ({v} : Set A) from by rw [hcent], inf_comm]
      exact C.centralizer_M v hvM hvZ)

private theorem inf_eq_four_of_disjoint {P : Sylow 2 A} (hne : P ≠ C.T)
    (hbot : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥)
    (hnoZ : ∀ v ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A), v ≠ 1 → v ∉ C.Z)
    (hnoZP : ∀ v ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A), v ≠ 1 →
      v ∉ C.point P ⊓ C.line P) :
    (((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.L ∨
      ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.M) ∧
      Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4 := by
  have hmemT : ∀ x ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A), x ∈ (C.T : Subgroup A) :=
    fun x hx => hx.1
  have hbotZ : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ⊓ C.Z = ⊥ := by
    rw [eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact hnoZ x hx.1 hx1 hx.2
  have hsq : ∀ x ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A), x * x = 1 := by
    intro x hx
    have h1 : x * x ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A) :=
      Subgroup.mul_mem _ hx hx
    have h2 : x * x ∈ C.Z := C.mul_self_mem x (hmemT x hx)
    have hmem : x * x ∈ ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ⊓ C.Z := ⟨h1, h2⟩
    rw [hbotZ] at hmem
    simpa using hmem
  have hcomm : ∀ x ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A),
      ∀ y ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A), x * y = y * x := by
    intro x hx y hy
    have hxy : (x * y) * (x * y) = 1 :=
      hsq _ (Subgroup.mul_mem _ hx hy)
    have hx' : x⁻¹ = x := inv_eq_of_mul_eq_one_right (hsq x hx)
    have hy' : y⁻¹ = y := inv_eq_of_mul_eq_one_right (hsq y hy)
    have h := mul_eq_one_iff_eq_inv.mp hxy
    rwa [mul_inv_rev, hx', hy'] at h
  have hsub : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.L ∨
      ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.M := by
    by_contra hcon
    push Not at hcon
    obtain ⟨hconL, hconM⟩ := hcon
    obtain ⟨x, hxD, hxL⟩ := SetLike.not_le_iff_exists.mp hconL
    obtain ⟨y, hyD, hyM⟩ := SetLike.not_le_iff_exists.mp hconM
    have hx2 : x * x = 1 := hsq x hxD
    have hy2 : y * y = 1 := hsq y hyD
    have hx1 : x ≠ 1 := fun h => hxL (h ▸ C.L.one_mem)
    have hy1 : y ≠ 1 := fun h => hyM (h ▸ C.M.one_mem)
    have hxM : x ∈ C.M := by
      rcases C.mem_or_mem x (hmemT x hxD) hx2 with h | h
      · exact absurd h hxL
      · exact h
    have hyL : y ∈ C.L := by
      rcases C.mem_or_mem y (hmemT y hyD) hy2 with h | h
      · exact h
      · exact absurd h hyM
    have hxyD : x * y ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A) :=
      Subgroup.mul_mem _ hxD hyD
    have hxyT : x * y ∈ (C.T : Subgroup A) := hmemT _ hxyD
    have hxy2 : (x * y) * (x * y) = 1 := hsq _ hxyD
    have hxy1 : x * y ≠ 1 := by
      intro h
      apply hxL
      have hxeq : x = y := by
        have h' : x = y⁻¹ := mul_eq_one_iff_eq_inv.mp h
        rwa [inv_eq_of_mul_eq_one_right hy2] at h'
      rwa [hxeq]
    rcases C.mem_or_mem (x * y) hxyT hxy2 with hxyL | hxyM
    · exact hxL (by
        have h' : x = (x * y) * y⁻¹ := by group
        rw [h']
        exact C.L.mul_mem hxyL (C.L.inv_mem hyL))
    · exact hyM (by
        have h' : y = x⁻¹ * (x * y) := by group
        rw [h']
        exact C.M.mul_mem (C.M.inv_mem hxM) hxyM)
  refine ⟨hsub, ?_⟩
  rcases hsub with hsubL | hsubM
  · exact C.card_four_of_le_L hne hbot hbotZ hsubL hsq hcomm
  · exact C.swap.card_four_of_le_L hne hbot (by simpa [Config.swap_Z] using hbotZ)
      (by simpa using hsubM) hsq hcomm

theorem inf_eq_bot_or_L_or_M_or_four {P : Sylow 2 A} (hne : P ≠ C.T) :
    ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = ⊥ ∨
    ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = C.L ∨
    ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = C.M ∨
    ((((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.L ∨
      ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.M) ∧
      Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4) := by
  by_cases hbot : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = ⊥
  · exact Or.inl hbot
  · by_cases h1 : ∃ v ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A), v ≠ 1 ∧ v ∈ C.Z
    · obtain ⟨v, hvD, hv1, hvZ⟩ := h1
      rcases C.inf_eq_L_or_M_of_mem_Z hne hvD hv1 hvZ with h | h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr (Or.inl h))
    · by_cases h2 : ∃ v ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A), v ≠ 1 ∧
          v ∈ C.point P ⊓ C.line P
      · obtain ⟨v, hvD, hv1, hvZP⟩ := h2
        rcases C.inf_eq_L_or_M_of_mem_ZP hne hvD hv1 hvZP with h | h
        · exact Or.inr (Or.inl h)
        · exact Or.inr (Or.inr (Or.inl h))
      · push Not at h1 h2
        exact Or.inr (Or.inr (Or.inr (C.inf_eq_four_of_disjoint hne hbot h1 h2)))

end Classification

section Counting

variable [Finite A]

theorem ncard_sylow_ge_line (Q : Sylow 2 A) :
    {P : Sylow 2 A | C.line Q ≤ (P : Subgroup A)}.ncard = 5 := by
  obtain ⟨a, -, hline⟩ := C.line_spec Q
  have hiff : ∀ P : Sylow 2 A, (C.line Q ≤ (P : Subgroup A)) ↔
      C.M ≤ ((a⁻¹ • P : Sylow 2 A) : Subgroup A) := by
    intro P
    rw [Sylow.coe_subgroup_smul]
    constructor
    · intro hP
      rw [hline] at hP
      have := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj a⁻¹) |>.mpr hP
      simpa using this
    · intro hP
      rw [hline]
      have := Subgroup.pointwise_smul_le_pointwise_smul_iff (a := MulAut.conj a) |>.mpr hP
      simpa using this
  have himg : {P : Sylow 2 A | C.line Q ≤ (P : Subgroup A)} =
      (fun P : Sylow 2 A => a • P) '' {P : Sylow 2 A | C.M ≤ (P : Subgroup A)} := by
    ext P
    constructor
    · intro hP
      exact ⟨a⁻¹ • P, (hiff P).mp hP, by simp⟩
    · rintro ⟨P', hP', rfl⟩
      exact (hiff (a • P')).mpr (by simpa using hP')
  rw [himg, Set.ncard_image_of_injective _ (fun P P' h => by
    simpa using congrArg (fun Q : Sylow 2 A => a⁻¹ • Q) h), C.ncard_sylow_ge_M]

theorem card_sylow (Q : Sylow 2 A) :
    Nat.card ↥(Q : Subgroup A) = Nat.card ↥(C.T : Subgroup A) := by
  obtain ⟨a, ha⟩ := C.exists_conj_eq Q
  rw [ha, card_conj]

theorem line_le_of_inf_eq {Q P : Sylow 2 A} (hLQ : C.L ≤ (Q : Subgroup A)) (hQ : Q ≠ C.T)
    (h : (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q) :
    C.line Q ≤ (P : Subgroup A) := by
  have hpt : C.point Q = C.L := C.point_eq_L_of_le hLQ
  have hcard : Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4 := by
    rw [h, ← hpt]
    exact C.card_inf_point_line_sylow Q
  have hPne : P ≠ C.T := by
    intro hPT
    rw [hPT, inf_idem, C.card_T] at hcard
    norm_num at hcard
  have hne : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  set v : A := (u : A) with hv
  have hvD : v ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A) := u.2
  have hv1 : v ≠ 1 := fun hh => hu1 (Subtype.ext (by simpa [hv] using hh))
  have hvL : v ∈ C.L := by rw [h] at hvD; exact hvD.1
  have hvline : v ∈ C.line Q := by rw [h] at hvD; exact hvD.2
  have hv2 : v * v = 1 := by
    have := C.isElemAbelian_L.2 v hvL
    simpa [pow_two] using this
  have hvZQ : v ∈ C.point Q ⊓ C.line Q := by rw [hpt]; exact ⟨hvL, hvline⟩
  have hQcent : centralizer ({v} : Set A) = (Q : Subgroup A) := C.centralizer_Z_sylow hvZQ hv1
  have hvZ : v ∉ C.Z := by
    intro hZ
    have hQT : (Q : Subgroup A) = (C.T : Subgroup A) := by
      rw [← hQcent, C.centralizer_eq_T hZ hv1]
    exact hQ (Sylow.ext hQT)
  have hvZP : v ∉ C.point P ⊓ C.line P := by
    intro hmem
    have hTL : (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L := by
      rw [show (C.T : Subgroup A) ⊓ (P : Subgroup A) =
        centralizer ({v} : Set A) ⊓ (C.T : Subgroup A) from by
          rw [C.centralizer_Z_sylow hmem hv1, inf_comm]]
      exact C.centralizer_L v hvL hvZ
    rw [hTL, C.card_L] at hcard
    norm_num at hcard
  have hCP : (P : Subgroup A) ⊓ (Q : Subgroup A) = C.point P ∨
      (P : Subgroup A) ⊓ (Q : Subgroup A) = C.line P := by
    rcases C.mem_point_or_line hvD.2 hv2 hv1 with hp | hp
    · exact Or.inl (by rw [← hQcent, inf_comm]; exact C.centralizer_point hp hvZP)
    · exact Or.inr (by rw [← hQcent, inf_comm]; exact C.centralizer_line hp hvZP)
  have hCPea : IsElemAbelian 2 ((P : Subgroup A) ⊓ (Q : Subgroup A)) := by
    rcases hCP with h' | h'
    · rw [h']; exact C.point_ea P
    · rw [h']; exact C.line_ea P
  have hCPcard : Nat.card ↥((P : Subgroup A) ⊓ (Q : Subgroup A)) = 16 := by
    rcases hCP with h' | h'
    · rw [h']; exact C.card_point P
    · rw [h']; exact C.card_line P
  have hLpq : C.L = C.point Q ∨ C.L = C.line Q :=
    C.eq_point_or_line hLQ C.isElemAbelian_L C.card_L
  have hCPq : (P : Subgroup A) ⊓ (Q : Subgroup A) = C.point Q ∨
      (P : Subgroup A) ⊓ (Q : Subgroup A) = C.line Q :=
    C.eq_point_or_line inf_le_right hCPea hCPcard
  have hLneCP : C.L ≠ (P : Subgroup A) ⊓ (Q : Subgroup A) := by
    intro heq
    have hLP : C.L ≤ (P : Subgroup A) := heq ▸ inf_le_left
    have h16 : 16 ≤ Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) := by
      have hle : C.L ≤ (C.T : Subgroup A) ⊓ (P : Subgroup A) :=
        fun x hx => ⟨C.L_le hx, hLP hx⟩
      calc 16 = Nat.card ↥C.L := C.card_L.symm
        _ ≤ _ := Subgroup.card_le_of_le hle
    omega
  rcases hCPq with hCP' | hCP'
  · exfalso
    rcases hLpq with hLp | hLl
    · exact hLneCP (by rw [hLp, hCP'])
    · have h16 : Nat.card ↥(C.L ⊓ C.line Q) = 16 := by rw [hLl, inf_idem, C.card_line Q]
      rw [h, h16] at hcard
      norm_num at hcard
  · rw [← hCP']
    exact inf_le_left

theorem inf_eq_inf_line_of_line_le {Q P : Sylow 2 A} (hLQ : C.L ≤ (Q : Subgroup A))
    (hQ : Q ≠ C.T) (hP : C.line Q ≤ (P : Subgroup A)) (hPne : P ≠ Q) :
    (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q := by
  have hpt : C.point Q = C.L := C.point_eq_L_of_le hLQ
  have hcardQ : Nat.card ↥(C.L ⊓ C.line Q) = 4 := by
    rw [← hpt]; exact C.card_inf_point_line_sylow Q
  have hle : C.L ⊓ C.line Q ≤ (C.T : Subgroup A) ⊓ (P : Subgroup A) :=
    fun x hx => ⟨C.L_le hx.1, hP hx.2⟩
  have hPneT : P ≠ C.T := by
    intro hPT
    have hleT : C.line Q ≤ (C.T : Subgroup A) := by rw [← hPT]; exact hP
    rcases C.eq_or_eq (C.line Q) hleT (C.line_ea Q) (C.card_line Q) with h' | h'
    · rw [h'] at hcardQ
      rw [inf_idem, C.card_L] at hcardQ
      norm_num at hcardQ
    · have hM : C.M ≤ (Q : Subgroup A) := by rw [← h']; exact C.line_le Q
      have hsup : (C.T : Subgroup A) ≤ (Q : Subgroup A) := by
        rw [← C.sup_eq]
        exact sup_le hLQ hM
      exact hQ (Sylow.ext (Subgroup.eq_of_le_of_card_ge hsup
        (by rw [C.card_sylow Q])).symm)
  have hbot : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥(C.L ⊓ C.line Q) ≤ Nat.card ↥(⊥ : Subgroup A) :=
      Subgroup.card_le_of_le (hbot ▸ hle)
    rw [hcardQ, Subgroup.card_bot] at h1
    norm_num at h1
  rcases C.inf_eq_bot_or_L_or_M_or_four hPneT with h' | h' | h' | h'
  · exact absurd h' hbot
  · exfalso
    have hLP : C.L ≤ (P : Subgroup A) :=
      fun x hx => (h'.symm ▸ hx : x ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A)).2
    have hsup : (Q : Subgroup A) ≤ (P : Subgroup A) := by
      rw [← C.sup_point_line Q, hpt]
      exact sup_le hLP hP
    exact hPne (Sylow.ext (Subgroup.eq_of_le_of_card_ge hsup
      (by rw [C.card_sylow P, C.card_sylow Q])).symm)
  · exfalso
    have hZM : C.L ⊓ C.line Q ≤ C.M := h' ▸ hle
    have hZQle : C.L ⊓ C.line Q ≤ C.Z := fun x hx => ⟨hx.1, hZM hx⟩
    have hZQeq : C.L ⊓ C.line Q = C.Z :=
      Subgroup.eq_of_le_of_card_ge hZQle (by rw [hcardQ, C.card_Z])
    have hne2 : C.L ⊓ C.line Q ≠ ⊥ := by
      intro hbot
      have hc := hcardQ
      rw [hbot, Subgroup.card_bot] at hc
      norm_num at hc
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne2
    have huQ : ((u : A)) ∈ C.point Q ⊓ C.line Q := by rw [hpt]; exact u.2
    have huZ : ((u : A)) ∈ C.Z := by rw [← hZQeq]; exact u.2
    have hu1' : ((u : A)) ≠ 1 := fun hh => hu1 (Subtype.ext hh)
    have hQT : (Q : Subgroup A) = (C.T : Subgroup A) := by
      rw [← C.centralizer_Z_sylow huQ hu1', C.centralizer_eq_T huZ hu1']
    exact hQ (Sylow.ext hQT)
  · have hDcard : Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4 := h'.2
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcardQ, hDcard])).symm

theorem ne_conj_L_conj_M (a b : A) :
    MulAut.conj a • C.L ≠ MulAut.conj b • C.M := by
  intro h
  have h' : MulAut.conj (b⁻¹ * a) • C.L = C.M := by
    have := congrArg (fun H => MulAut.conj b⁻¹ • H) h
    rw [smul_smul_conj] at this
    simpa using this
  exact C.conj_L_ne_M (b⁻¹ * a) h'

theorem exists_centreSylow {P : Sylow 2 A}
    (hL : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.L)
    (hcard : Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4) :
    ∃ Q : Sylow 2 A, C.L ≤ (Q : Subgroup A) ∧ Q ≠ C.T ∧
      (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q := by
  have hne : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  set v : A := (u : A) with hv
  have hvD : v ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A) := u.2
  have hv1 : v ≠ 1 := fun hh => hu1 (Subtype.ext (by simpa [hv] using hh))
  have hvL : v ∈ C.L := hL hvD
  have hvP : v ∈ (P : Subgroup A) := hvD.2
  have hv2 : v * v = 1 := by
    have := C.isElemAbelian_L.2 v hvL
    simpa [pow_two] using this
  have hPneT : P ≠ C.T := by
    intro hPT
    rw [hPT, inf_idem, C.card_T] at hcard
    norm_num at hcard
  have hvZ : v ∉ C.Z := by
    intro hZ
    rcases C.inf_eq_L_or_M_of_mem_Z hPneT hvD hv1 hZ with h | h
    · rw [h, C.card_L] at hcard
      norm_num at hcard
    · rw [h, C.card_M] at hcard
      norm_num at hcard
  have hCT : centralizer ({v} : Set A) ⊓ (C.T : Subgroup A) = C.L :=
    C.centralizer_L v hvL hvZ
  obtain ⟨Q, hQ⟩ := C.exists_sylow_eq_centralizer hv2 hv1
  have hLQ : C.L ≤ (Q : Subgroup A) := by
    rw [← hQ, ← hCT]
    exact inf_le_left
  have hQT : Q ≠ C.T := by
    intro hQT
    have hTL : (C.T : Subgroup A) = C.L := by
      have h2 : (C.T : Subgroup A) ⊓ (C.T : Subgroup A) = C.L := by
        calc (C.T : Subgroup A) ⊓ (C.T : Subgroup A)
            = centralizer ({v} : Set A) ⊓ (C.T : Subgroup A) := by
              rw [show centralizer ({v} : Set A) = (C.T : Subgroup A) from
                hQ.trans (congrArg (fun P : Sylow 2 A => (P : Subgroup A)) hQT)]
          _ = C.L := hCT
      rwa [inf_idem] at h2
    have h64 := C.card_T
    rw [hTL, C.card_L] at h64
    norm_num at h64
  have hpt : C.point Q = C.L := C.point_eq_L_of_le hLQ
  have hDsubQ : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ (Q : Subgroup A) := by
    intro x hx
    have hxL : x ∈ C.L := hL hx
    rw [← hQ, Subgroup.mem_centralizer_iff]
    intro w hw
    rw [Set.mem_singleton_iff] at hw
    rw [hw]
    haveI := C.isElemAbelian_L.1
    exact congrArg Subtype.val (mul_comm' (⟨x, hxL⟩ : ↥C.L) ⟨v, hvL⟩).symm
  have hvZP : v ∉ C.point P ⊓ C.line P := by
    intro hmem
    have hPcent : centralizer ({v} : Set A) = (P : Subgroup A) := C.centralizer_Z_sylow hmem hv1
    have hD : (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L := by
      rw [show (C.T : Subgroup A) ⊓ (P : Subgroup A) =
        centralizer ({v} : Set A) ⊓ (C.T : Subgroup A) from by
          rw [hPcent, inf_comm]]
      exact C.centralizer_L v hvL hvZ
    rw [hD, C.card_L] at hcard
    norm_num at hcard
  have hCP : (P : Subgroup A) ⊓ (Q : Subgroup A) = C.point P ∨
      (P : Subgroup A) ⊓ (Q : Subgroup A) = C.line P := by
    rcases C.mem_point_or_line hvP hv2 hv1 with hp | hp
    · exact Or.inl (by rw [← hQ, inf_comm]; exact C.centralizer_point hp hvZP)
    · exact Or.inr (by rw [← hQ, inf_comm]; exact C.centralizer_line hp hvZP)
  have hCPea : IsElemAbelian 2 ((P : Subgroup A) ⊓ (Q : Subgroup A)) := by
    rcases hCP with h' | h'
    · rw [h']; exact C.point_ea P
    · rw [h']; exact C.line_ea P
  have hCPcard : Nat.card ↥((P : Subgroup A) ⊓ (Q : Subgroup A)) = 16 := by
    rcases hCP with h' | h'
    · rw [h']; exact C.card_point P
    · rw [h']; exact C.card_line P
  have hCPq : (P : Subgroup A) ⊓ (Q : Subgroup A) = C.point Q ∨
      (P : Subgroup A) ⊓ (Q : Subgroup A) = C.line Q :=
    C.eq_point_or_line inf_le_right hCPea hCPcard
  have hLpq : C.L = C.point Q ∨ C.L = C.line Q :=
    C.eq_point_or_line hLQ C.isElemAbelian_L C.card_L
  have hLline : C.L ≠ C.line Q := by
    obtain ⟨a, -, ha⟩ := C.line_spec Q
    intro h
    exact C.ne_conj_L_conj_M 1 a (by simpa [ha] using h)
  have hLneCP : C.L ≠ (P : Subgroup A) ⊓ (Q : Subgroup A) := by
    intro heq
    have hLP : C.L ≤ (P : Subgroup A) := heq ▸ inf_le_left
    have h16 : 16 ≤ Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) := by
      have hle : C.L ≤ (C.T : Subgroup A) ⊓ (P : Subgroup A) := fun x hx => ⟨C.L_le hx, hLP hx⟩
      calc 16 = Nat.card ↥C.L := C.card_L.symm
        _ ≤ _ := Subgroup.card_le_of_le hle
    omega
  have hPinfQ : (P : Subgroup A) ⊓ (Q : Subgroup A) = C.line Q := by
    rcases hCPq with h' | h'
    · exfalso
      rcases hLpq with hLp | hLl
      · exact hLneCP (by rw [hLp, h'])
      · exact hLline hLl
    · exact h'
  have hlineQP : C.line Q ≤ (P : Subgroup A) := by
    rcases hCPq with h' | h'
    · exfalso
      rcases hLpq with hLp | hLl
      · exact hLneCP (by rw [hLp, h'])
      · exact hLline hLl
    · rw [← h']
      exact inf_le_left
  refine ⟨Q, hLQ, hQT, le_antisymm ?_ ?_⟩
  · intro x hx
    exact ⟨hL hx, hPinfQ ▸ Subgroup.mem_inf.mpr ⟨hx.2, hDsubQ hx⟩⟩
  · intro x hx
    exact ⟨C.L_le hx.1, hlineQP hx.2⟩

theorem centreSylow_unique {P Q Q' : Sylow 2 A} (hLQ : C.L ≤ (Q : Subgroup A))
    (hLQ' : C.L ≤ (Q' : Subgroup A))
    (h : (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q)
    (h' : (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q') : Q = Q' := by
  have hpt : C.point Q = C.L := C.point_eq_L_of_le hLQ
  have hpt' : C.point Q' = C.L := C.point_eq_L_of_le hLQ'
  have hcard : Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4 := by
    rw [h, ← hpt]; exact C.card_inf_point_line_sylow Q
  have hne : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  set v : A := (u : A) with hv
  have hvD : v ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A) := u.2
  have hv1 : v ≠ 1 := fun hh => hu1 (Subtype.ext (by simpa [hv] using hh))
  have hZQ : v ∈ C.point Q ⊓ C.line Q := by
    rw [hpt]
    have := (h ▸ hvD : v ∈ C.L ⊓ C.line Q)
    exact ⟨this.1, this.2⟩
  have hZQ' : v ∈ C.point Q' ⊓ C.line Q' := by
    rw [hpt']
    have := (h' ▸ hvD : v ∈ C.L ⊓ C.line Q')
    exact ⟨this.1, this.2⟩
  have h1 : (Q : Subgroup A) = centralizer ({v} : Set A) :=
    (C.centralizer_Z_sylow hZQ hv1).symm
  have h2 : (Q' : Subgroup A) = centralizer ({v} : Set A) :=
    (C.centralizer_Z_sylow hZQ' hv1).symm
  exact Sylow.ext (h1.trans h2.symm)

@[expose] def sylowThroughL : Set (Sylow 2 A) := {Q | C.L ≤ (Q : Subgroup A) ∧ Q ≠ C.T}

@[expose] def zcaseL : Set (Sylow 2 A) :=
  {P | ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.L ∧
    Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4}

@[expose] def zcaseM : Set (Sylow 2 A) :=
  {P | ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.M ∧
    Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4}

noncomputable def centreSylowOf (P : Sylow 2 A)
    (hL : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.L)
    (hcard : Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4) : Sylow 2 A :=
  Classical.choose (C.exists_centreSylow hL hcard)

theorem centreSylowOf_spec (P : Sylow 2 A)
    (hL : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.L)
    (hcard : Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4) :
    C.L ≤ (C.centreSylowOf P hL hcard : Subgroup A) ∧
      C.centreSylowOf P hL hcard ≠ C.T ∧
      (C.T : Subgroup A) ⊓ (P : Subgroup A) =
        C.L ⊓ C.line (C.centreSylowOf P hL hcard) :=
  Classical.choose_spec (C.exists_centreSylow hL hcard)

theorem ncard_sylowThroughL : C.sylowThroughL.ncard = 4 := by
  have hset : C.sylowThroughL = {P : Sylow 2 A | C.L ≤ (P : Subgroup A)} \ {C.T} := by
    ext P
    constructor
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
    · rintro ⟨h1, h2⟩
      exact ⟨h1, h2⟩
  rw [hset, Set.ncard_diff_singleton_of_mem (show C.T ∈ {P : Sylow 2 A | C.L ≤ (P : Subgroup A)}
    from C.L_le), C.ncard_sylow_ge_L]

theorem ncard_line_fiber {Q : Sylow 2 A} (hLQ : C.L ≤ (Q : Subgroup A)) (hQ : Q ≠ C.T) :
    Nat.card {P : Sylow 2 A // (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q} = 4 := by
  have hset : {P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q} =
      {P : Sylow 2 A | C.line Q ≤ (P : Subgroup A)} \ {Q} := by
    ext P
    constructor
    · intro hP
      refine ⟨C.line_le_of_inf_eq hLQ hQ hP, ?_⟩
      intro hPQ
      rw [Set.mem_singleton_iff] at hPQ
      rw [Set.mem_setOf_eq] at hP
      rw [hPQ] at hP
      have h1 : (C.T : Subgroup A) ⊓ (Q : Subgroup A) = C.L :=
        C.inf_eq_L_of_ne C.L_le hLQ (Ne.symm hQ)
      rw [h1] at hP
      have h3 : Nat.card ↥(C.L ⊓ C.line Q) = 4 := by
        rw [← C.point_eq_L_of_le hLQ]; exact C.card_inf_point_line_sylow Q
      rw [← hP, C.card_L] at h3
      norm_num at h3
    · rintro ⟨hP, hPQ⟩
      exact C.inf_eq_inf_line_of_line_le hLQ hQ hP hPQ
  rw [show Nat.card {P : Sylow 2 A // (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q}
      = ({P : Sylow 2 A | (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q}).ncard from
    Nat.card_coe_set_eq _]
  rw [hset, Set.ncard_diff_singleton_of_mem
    (show Q ∈ {P : Sylow 2 A | C.line Q ≤ (P : Subgroup A)} from C.line_le Q),
    C.ncard_sylow_ge_line]

private noncomputable def zcaseLProj :
    (Σ Q : {Q : Sylow 2 A // Q ∈ C.sylowThroughL},
      {P : Sylow 2 A // (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q.1}) →
    {P : Sylow 2 A // P ∈ C.zcaseL} :=
  fun QP => ⟨QP.2.1, by
    refine ⟨?_, ?_⟩
    · rw [QP.2.2]
      exact inf_le_left
    · have hpt : C.point (QP.1 : Sylow 2 A) = C.L := C.point_eq_L_of_le QP.1.2.1
      rw [QP.2.2]
      have hc := C.card_inf_point_line_sylow QP.1.1
      rwa [hpt] at hc⟩

private theorem zcaseLProj_bijective : Function.Bijective C.zcaseLProj := by
  constructor
  · rintro ⟨Q, P, hP⟩ ⟨Q', P', hP'⟩ heq
    have hval : (P : Sylow 2 A) = P' := congrArg (fun z => z.1) heq
    have hQ : (Q : Sylow 2 A) = (Q' : Sylow 2 A) :=
      C.centreSylow_unique Q.2.1 Q'.2.1 hP (hval ▸ hP')
    subst hval
    have hQ' : Q = Q' := Subtype.ext hQ
    subst hQ'
    rfl
  · rintro ⟨P, hP⟩
    obtain ⟨Q, hLQ, hQT, hEq⟩ := C.exists_centreSylow hP.1 hP.2
    refine ⟨⟨⟨Q, hLQ, hQT⟩, ⟨P, hEq⟩⟩, ?_⟩
    apply Subtype.ext
    rfl

theorem ncard_zcaseL : C.zcaseL.ncard = 16 := by
  classical
  haveI : Fintype (Sylow 2 A) := Fintype.ofFinite _
  have hcard := Nat.card_congr (Equiv.ofBijective C.zcaseLProj C.zcaseLProj_bijective)
  have hsum : Nat.card (Σ Q : {Q : Sylow 2 A // Q ∈ C.sylowThroughL},
      {P : Sylow 2 A // (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q.1}) = 16 := by
    rw [Nat.card_sigma]
    have hcongr : (∑ Q : {Q : Sylow 2 A // Q ∈ C.sylowThroughL},
        Nat.card {P : Sylow 2 A // (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.L ⊓ C.line Q.1}) =
        ∑ _ : {Q : Sylow 2 A // Q ∈ C.sylowThroughL}, 4 :=
      Finset.sum_congr rfl (fun Q _ => C.ncard_line_fiber Q.2.1 Q.2.2)
    rw [hcongr, Finset.sum_const, Finset.card_univ]
    have hc : Nat.card {Q : Sylow 2 A // Q ∈ C.sylowThroughL} = 4 := by
      rw [Nat.card_coe_set_eq]
      exact C.ncard_sylowThroughL
    rw [← Nat.card_eq_fintype_card, hc]
    norm_num
  have hfinal : Nat.card {P : Sylow 2 A // P ∈ C.zcaseL} = C.zcaseL.ncard :=
    Nat.card_coe_set_eq _
  rw [← hfinal, ← hcard]
  exact hsum

theorem ncard_zcaseM : C.zcaseM.ncard = 16 := by
  have h := C.swap.ncard_zcaseL
  simpa [zcaseM, zcaseL, Config.swap_T, Config.swap_L, Config.swap_M] using h

@[expose] def sylowThroughM : Set (Sylow 2 A) := C.swap.sylowThroughL

theorem ncard_sylowThroughM : C.sylowThroughM.ncard = 4 :=
  C.swap.ncard_sylowThroughL

theorem ncard_meets :
    {P : Sylow 2 A | ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥}.ncard = 41 := by
  classical
  have hA1 : ({C.T} : Set (Sylow 2 A)).ncard = 1 := Set.ncard_singleton _
  have hA2 : C.sylowThroughL.ncard = 4 := C.ncard_sylowThroughL
  have hA3 : C.sylowThroughM.ncard = 4 := C.ncard_sylowThroughM
  have hZL : C.zcaseL.ncard = 16 := C.ncard_zcaseL
  have hZM : C.zcaseM.ncard = 16 := C.ncard_zcaseM
  have hzdisj : Disjoint C.zcaseL C.zcaseM := by
    rw [Set.disjoint_left]
    intro P hPL hPM
    have hD : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≤ C.Z := le_inf hPL.1 hPM.1
    have hcardD : Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) = 4 := hPL.2
    have hDZ : (C.T : Subgroup A) ⊓ (P : Subgroup A) = C.Z :=
      Subgroup.eq_of_le_of_card_ge hD (by rw [C.card_Z, hcardD])
    have hneZ : C.Z ≠ ⊥ := by
      intro hbot
      have hc := C.card_Z
      rw [hbot] at hc
      rw [Subgroup.card_bot] at hc
      norm_num at hc
    obtain ⟨u, hu1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hneZ
    have huD : ((u : A)) ∈ (C.T : Subgroup A) ⊓ (P : Subgroup A) := by
      rw [hDZ]; exact u.2
    have hu1' : ((u : A)) ≠ 1 := fun hh => hu1 (Subtype.ext hh)
    have hPT : P ≠ C.T := by
      intro hPT
      rw [hPT, inf_idem, C.card_T] at hcardD
      norm_num at hcardD
    rcases C.inf_eq_L_or_M_of_mem_Z hPT huD hu1' u.2 with h | h
    · rw [h, C.card_L] at hcardD
      norm_num at hcardD
    · rw [h, C.card_M] at hcardD
      norm_num at hcardD
  have hA4 : (C.zcaseL ∪ C.zcaseM).ncard = 32 := by
    rw [Set.ncard_union_eq hzdisj, hZL, hZM]
  have hpart : {P : Sylow 2 A | ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥} =
      ({C.T} : Set (Sylow 2 A)) ∪ C.sylowThroughL ∪ C.sylowThroughM ∪
        (C.zcaseL ∪ C.zcaseM) := by
    ext P
    constructor
    · intro hP
      by_cases hPT : P = C.T
      · exact Or.inl (Or.inl (Or.inl (by rw [hPT]; exact rfl)))
      · rcases C.inf_eq_bot_or_L_or_M_or_four hPT with h' | h' | h' | h'
        · exact absurd h' hP
        · refine Or.inl (Or.inl (Or.inr ⟨?_, hPT⟩))
          rw [← h']
          exact inf_le_right
        · refine Or.inl (Or.inr ⟨?_, hPT⟩)
          show C.M ≤ (P : Subgroup A)
          rw [← h']
          exact inf_le_right
        · rcases h'.1 with hL | hM
          · exact Or.inr (Or.inl ⟨hL, h'.2⟩)
          · exact Or.inr (Or.inr ⟨hM, h'.2⟩)
    · intro hP
      show ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥
      rcases hP with ((hPT | hL) | hM) | hZ
      · have hPT' : P = C.T := by simpa using hPT
        subst hPT'
        rw [inf_idem]
        intro h
        have hc := C.card_T
        rw [h] at hc
        rw [Subgroup.card_bot] at hc
        norm_num at hc
      · intro hbot
        have hLbot : C.L ≤ (⊥ : Subgroup A) := by
          calc C.L ≤ (C.T : Subgroup A) ⊓ (P : Subgroup A) :=
                fun x hx => ⟨C.L_le hx, hL.1 hx⟩
            _ = ⊥ := hbot
        have hc := C.card_L
        rw [show C.L = ⊥ from le_antisymm hLbot bot_le, Subgroup.card_bot] at hc
        norm_num at hc
      · intro hbot
        have hMbot : C.M ≤ (⊥ : Subgroup A) := by
          calc C.M ≤ (C.T : Subgroup A) ⊓ (P : Subgroup A) :=
                fun x hx => ⟨C.M_le hx, hM.1 hx⟩
            _ = ⊥ := hbot
        have hc := C.card_M
        rw [show C.M = ⊥ from le_antisymm hMbot bot_le, Subgroup.card_bot] at hc
        norm_num at hc
      · intro hbot
        rcases hZ with hZL | hZM
        · have hc := hZL.2
          rw [hbot, Subgroup.card_bot] at hc
          norm_num at hc
        · have hc := hZM.2
          rw [hbot, Subgroup.card_bot] at hc
          norm_num at hc
  rw [hpart]
  have h12 : Disjoint ({C.T} : Set (Sylow 2 A)) C.sylowThroughL := by
    rw [Set.disjoint_left]
    intro P hP hQ
    rw [Set.mem_singleton_iff] at hP
    exact hQ.2 hP
  have h13 : Disjoint ({C.T} : Set (Sylow 2 A)) C.sylowThroughM := by
    rw [Set.disjoint_left]
    intro P hP hQ
    rw [Set.mem_singleton_iff] at hP
    exact hQ.2 hP
  have h14 : Disjoint ({C.T} : Set (Sylow 2 A)) (C.zcaseL ∪ C.zcaseM) := by
    rw [Set.disjoint_left]
    intro P hP hQ
    rw [Set.mem_singleton_iff] at hP
    rw [hP] at hQ
    rcases hQ with hQ | hQ
    · have hQ' : ((C.T : Subgroup A) ⊓ (C.T : Subgroup A)) ≤ C.L ∧
          Nat.card ↥((C.T : Subgroup A) ⊓ (C.T : Subgroup A)) = 4 := hQ
      rw [inf_idem, C.card_T] at hQ'
      omega
    · have hQ' : ((C.T : Subgroup A) ⊓ (C.T : Subgroup A)) ≤ C.M ∧
          Nat.card ↥((C.T : Subgroup A) ⊓ (C.T : Subgroup A)) = 4 := hQ
      rw [inf_idem, C.card_T] at hQ'
      omega
  have h23 : Disjoint C.sylowThroughL C.sylowThroughM := by
    rw [Set.disjoint_left]
    intro P hL hM
    have hsup : (C.T : Subgroup A) ≤ (P : Subgroup A) := by
      rw [← C.sup_eq]
      exact sup_le hL.1 hM.1
    exact hL.2 (Sylow.ext (Subgroup.eq_of_le_of_card_ge hsup
      (by rw [C.card_sylow P])).symm)
  have h24 : Disjoint C.sylowThroughL (C.zcaseL ∪ C.zcaseM) := by
    rw [Set.disjoint_left]
    intro P hL hZ
    rcases hZ with hZ | hZ
    · have h16 : 16 ≤ Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) := by
        have hle : C.L ≤ (C.T : Subgroup A) ⊓ (P : Subgroup A) :=
          fun x hx => ⟨C.L_le hx, hL.1 hx⟩
        calc 16 = Nat.card ↥C.L := C.card_L.symm
          _ ≤ _ := Subgroup.card_le_of_le hle
      rw [hZ.2] at h16
      norm_num at h16
    · have h16 : 16 ≤ Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) := by
        have hle : C.L ≤ (C.T : Subgroup A) ⊓ (P : Subgroup A) :=
          fun x hx => ⟨C.L_le hx, hL.1 hx⟩
        calc 16 = Nat.card ↥C.L := C.card_L.symm
          _ ≤ _ := Subgroup.card_le_of_le hle
      rw [hZ.2] at h16
      norm_num at h16
  have h34 : Disjoint C.sylowThroughM (C.zcaseL ∪ C.zcaseM) := by
    rw [Set.disjoint_left]
    intro P hM hZ
    rcases hZ with hZ | hZ
    · have h16 : 16 ≤ Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) := by
        have hle : C.M ≤ (C.T : Subgroup A) ⊓ (P : Subgroup A) :=
          fun x hx => ⟨C.M_le hx, hM.1 hx⟩
        calc 16 = Nat.card ↥C.M := C.card_M.symm
          _ ≤ _ := Subgroup.card_le_of_le hle
      rw [hZ.2] at h16
      norm_num at h16
    · have h16 : 16 ≤ Nat.card ↥((C.T : Subgroup A) ⊓ (P : Subgroup A)) := by
        have hle : C.M ≤ (C.T : Subgroup A) ⊓ (P : Subgroup A) :=
          fun x hx => ⟨C.M_le hx, hM.1 hx⟩
        calc 16 = Nat.card ↥C.M := C.card_M.symm
          _ ≤ _ := Subgroup.card_le_of_le hle
      rw [hZ.2] at h16
      norm_num at h16
  have hunion : (({C.T} : Set (Sylow 2 A)) ∪ C.sylowThroughL ∪ C.sylowThroughM ∪
      (C.zcaseL ∪ C.zcaseM)) =
      {C.T} ∪ (C.sylowThroughL ∪ (C.sylowThroughM ∪ (C.zcaseL ∪ C.zcaseM))) := by
    rw [Set.union_assoc, Set.union_assoc]
  rw [hunion]
  have hd1 : Disjoint ({C.T} : Set (Sylow 2 A))
      (C.sylowThroughL ∪ (C.sylowThroughM ∪ (C.zcaseL ∪ C.zcaseM))) :=
    h12.union_right (h13.union_right h14)
  rw [Set.ncard_union_eq hd1]
  have hd2 : Disjoint C.sylowThroughL (C.sylowThroughM ∪ (C.zcaseL ∪ C.zcaseM)) :=
    h23.union_right h24
  rw [Set.ncard_union_eq hd2]
  rw [Set.ncard_union_eq h34]
  rw [hA1, hA2, hA3, hA4]

theorem ncard_opposite :
    {P : Sylow 2 A | ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = ⊥}.ncard =
      Nat.card (Sylow 2 A) - 41 := by
  classical
  have hunion : {P : Sylow 2 A | ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥} ∪
      {P : Sylow 2 A | ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = ⊥} = Set.univ := by
    ext P
    by_cases h : ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = ⊥
    · simp [h]
    · simp [h]
  have hdisj : Disjoint {P : Sylow 2 A | ((C.T : Subgroup A) ⊓ (P : Subgroup A)) ≠ ⊥}
      {P : Sylow 2 A | ((C.T : Subgroup A) ⊓ (P : Subgroup A)) = ⊥} := by
    rw [Set.disjoint_left]
    intro P h1 h2
    exact h1 h2
  have h := Set.ncard_union_eq hdisj
  rw [hunion, C.ncard_meets] at h
  have huniv : (Set.univ : Set (Sylow 2 A)).ncard = Nat.card (Sylow 2 A) := by
    rw [← Nat.card_coe_set_eq]
    simp
  rw [huniv] at h
  omega

end Counting

end Config

end CFSG.Quasithin.L34CIT

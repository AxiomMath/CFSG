module

public import CFSG.Sporadic.Co2Smith.GlNJDefs
public import Certificates.Certificate21166
public import Certificates.Certificate21167
public import CFSG.Sporadic.Co2Smith.GlC0Mark

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.CosetTable

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem glW_check : Native.glWOK = true :=
  Certificates.certificate21166

theorem glW_e1 :
    subsetCheckC (restrictWords (subsetOf 7 [0, 1, 2, 3, 4, 5]) Native.glWRels) [] 100000 1440 =
      true :=
  Certificates.certificate21167.1

theorem glW_e2 :
    subsetCheckC Native.glWRels [0, 1, 2, 3, 4, 5] 100000 36 = true :=
  Certificates.certificate21167.2

theorem glW_parts :
    Native.glWJcOK = true ∧ Native.glWTabsOK = true ∧ Native.glWE1OK = true ∧
      Native.glWhOK = true ∧ Native.glWbOK = true ∧ Native.glWFilterOK = true ∧
      Native.glWr0OK = true ∧ Native.glWInjOK = true ∧ Native.glWRelOK = true ∧
      Native.glWD0OK = true := by
  have h := glW_check
  simp only [Native.glWOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10⟩

theorem glWJc_spec : ∀ i < 10,
    mulRows 22 Native.glNJBR[i]! Native.glNJBR[i]! = idRows 22 ∧
      Native.commRows Native.glNJBR[i]! Native.glZ = true ∧
      ∀ j < 10, Native.commRows Native.glNJBR[i]! Native.glNJBR[j]! = true := by
  have h := glW_parts.1
  simp only [Native.glWJcOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range]
    at h
  intro i hi
  exact ⟨(h.2 i hi).1.1, (h.2 i hi).1.2, fun j hj => (h.2 i hi).2 j hj⟩

section Basis


theorem jcB_mul_self {i : ℕ} (hi : i < 10) : jcB i * jcB i = 1 :=
  eq_of_rows (val_mul_rows (jcB_val hi) (jcB_val hi)) val_one_rows (glWJc_spec i hi).1

theorem jcB_comm {i j : ℕ} (hi : i < 10) (hj : j < 10) : jcB i * jcB j = jcB j * jcB i :=
  comm_of_commRows (jcB_val hi) (jcB_val hj) ((glWJc_spec i hi).2.2 j hj)

theorem jcB_mem_Cz {i : ℕ} (hi : i < 10) : jcB i ∈ Cz :=
  mem_Cz_of_comm (comm_of_commRows (jcB_val hi) z0_val' (glWJc_spec i hi).2.1)

theorem Jc_le_Cz : Jc ≤ Cz := by
  rw [Jc, closure_le]
  rintro _ ⟨i, rfl⟩
  exact jcB_mem_Cz i.isLt

theorem Jc_comm {x y : K} (hx : x ∈ Jc) (hy : y ∈ Jc) : x * y = y * x := by
  have hS : Set.range (fun i : Fin 10 => jcB i) ⊆
      (centralizer (Set.range fun i : Fin 10 => jcB i) : Set K) := by
    rintro _ ⟨i, rfl⟩
    refine mem_centralizer_iff.2 ?_
    rintro _ ⟨j, rfl⟩
    exact jcB_comm j.isLt i.isLt
  have h1 : Jc ≤ centralizer (Set.range fun i : Fin 10 => jcB i) := (closure_le _).2 hS
  have h2 := closure_le_centralizer_centralizer (Set.range fun i : Fin 10 => jcB i)
  exact (mem_centralizer_iff.1 (h2 hx) y (h1 hy)).symm

end Basis

theorem glWTab_spec {R : Array ℕ} {tab : List ℕ} (h : Native.glWTabOK R tab = true) :
    ∀ i < 10, tab[i]! < 1024 ∧
      mulRows 22 R Native.glNJBR[i]! = mulRows 22 (Native.glJcR tab[i]!) R := by
  simp only [Native.glWTabOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, List.mem_range,
    decide_eq_true_eq] at h
  exact fun i hi => h.2 i hi

section Tab


theorem mem_normalizer_of_tab {g : K} {R : Array ℕ} (hg : g.val.val = rowsMatrix 22 R)
    {tab : List ℕ} (h : Native.glWTabOK R tab = true) : g ∈ normalizer (Jc : Set K) := by
  have hgen : ∀ i < 10, g * jcB i * g⁻¹ ∈ Jc := by
    intro i hi
    obtain ⟨-, he⟩ := glWTab_spec h i hi
    have e : g * jcB i = jcElt tab[i]! * g :=
      eq_of_rows (val_mul_rows hg (jcB_val hi)) (val_mul_rows (jcElt_val _) hg) he
    rw [e, mul_inv_cancel_right]
    exact jcElt_mem _
  have hle : Jc.map (MulAut.conj g).toMonoidHom ≤ Jc := by
    rw [Jc, MonoidHom.map_closure, closure_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact hgen i i.isLt
  have heq : Jc.map (MulAut.conj g).toMonoidHom = Jc :=
    eq_of_le_of_card_ge hle (by rw [card_map_of_injective (MulAut.conj g).injective])
  rw [mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hle ⟨x, hx, rfl⟩
  · intro hx
    rw [← heq] at hx
    obtain ⟨y, hy, e⟩ := hx
    have : y = x := by
      have e' : g * y * g⁻¹ = g * x * g⁻¹ := e
      simpa using e'
    rw [← this]
    exact hy

theorem glWTabs_spec :
    Native.glWTabOK Native.glD1h Native.glWTabs[0]! = true ∧
    Native.glWTabOK Native.glAl Native.glWTabs[1]! = true ∧
    Native.glWTabOK Native.glGa Native.glWTabs[2]! = true ∧
    Native.glWTabOK Native.glD0h Native.glWTabs[3]! = true := by
  have h := glW_parts.2.1
  simp only [Native.glWTabsOK, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩


theorem δ1hK_mem_N : δ1hK ∈ normalizer (Jc : Set K) :=
  mem_normalizer_of_tab δ1hK_val glWTabs_spec.1

theorem α3K_mem_N : α3K ∈ normalizer (Jc : Set K) :=
  mem_normalizer_of_tab α3K_val glWTabs_spec.2.1

theorem γ3K_mem_N : γ3K ∈ normalizer (Jc : Set K) :=
  mem_normalizer_of_tab γ3K_val glWTabs_spec.2.2.1

theorem δ0hK_mem_N : δ0hK ∈ normalizer (Jc : Set K) :=
  mem_normalizer_of_tab δ0hK_val glWTabs_spec.2.2.2

end Tab

theorem Jc_le_N : Jc ≤ normalizer (Jc : Set K) := le_normalizer

end CFSG.Sporadic.Co2Smith

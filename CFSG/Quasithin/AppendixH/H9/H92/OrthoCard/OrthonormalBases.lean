module

public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Data.ZMod.Defs

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

@[expose] def IsOrthonormalBasis5 (S : Finset (Fin 5 → ZMod 2)) : Prop :=
  S.card = 5 ∧ (∀ x ∈ S, x ⬝ᵥ x = 1) ∧ ∀ x ∈ S, ∀ y ∈ S, x ≠ y → x ⬝ᵥ y = 0

def oddVecs5 : Finset (Fin 5 → ZMod 2) := Finset.univ.filter fun x => x ⬝ᵥ x = 1

theorem mem_oddVecs5 {x : Fin 5 → ZMod 2} : x ∈ oddVecs5 ↔ x ⬝ᵥ x = 1 := by
  simp [oddVecs5]

def stdBasis5 : Finset (Fin 5 → ZMod 2) :=
  {![1, 0, 0, 0, 0], ![0, 1, 0, 0, 0], ![0, 0, 1, 0, 0], ![0, 0, 0, 1, 0], ![0, 0, 0, 0, 1]}

def otherBasis5 : Fin 5 → Finset (Fin 5 → ZMod 2)
  | 0 => {![1, 0, 0, 0, 0], ![0, 0, 1, 1, 1], ![0, 1, 0, 1, 1], ![0, 1, 1, 0, 1], ![0, 1, 1, 1, 0]}
  | 1 => {![0, 1, 0, 0, 0], ![0, 0, 1, 1, 1], ![1, 0, 0, 1, 1], ![1, 0, 1, 0, 1], ![1, 0, 1, 1, 0]}
  | 2 => {![0, 0, 1, 0, 0], ![0, 1, 0, 1, 1], ![1, 0, 0, 1, 1], ![1, 1, 0, 0, 1], ![1, 1, 0, 1, 0]}
  | 3 => {![0, 0, 0, 1, 0], ![0, 1, 1, 0, 1], ![1, 0, 1, 0, 1], ![1, 1, 0, 0, 1], ![1, 1, 1, 0, 0]}
  | 4 => {![0, 0, 0, 0, 1], ![0, 1, 1, 1, 0], ![1, 0, 1, 1, 0], ![1, 1, 0, 1, 0], ![1, 1, 1, 0, 0]}

def bases5 : Fin 6 → Finset (Fin 5 → ZMod 2) :=
  ![stdBasis5, otherBasis5 0, otherBasis5 1, otherBasis5 2, otherBasis5 3, otherBasis5 4]

theorem isOrthonormalBasis5_bases5 (i : Fin 6) : IsOrthonormalBasis5 (bases5 i) := by
  unfold IsOrthonormalBasis5
  revert i
  decide +kernel

theorem isOrthonormalBasis5_stdBasis5 : IsOrthonormalBasis5 stdBasis5 := by
  unfold IsOrthonormalBasis5
  decide +kernel

theorem isOrthonormalBasis5_otherBasis5 (i : Fin 5) : IsOrthonormalBasis5 (otherBasis5 i) := by
  unfold IsOrthonormalBasis5
  revert i
  decide +kernel

theorem stdBasis5_inter_otherBasis5 (i : Fin 5) {x : Fin 5 → ZMod 2} (hx : x ∈ stdBasis5)
    (hxi : x ∈ otherBasis5 i) : x = Pi.single i 1 := by
  revert x
  revert i
  decide +kernel

theorem single_mem_otherBasis5 (i : Fin 5) : (Pi.single i 1 : Fin 5 → ZMod 2) ∈ otherBasis5 i := by
  revert i
  decide +kernel

theorem single_mem_stdBasis5 (i : Fin 5) : (Pi.single i 1 : Fin 5 → ZMod 2) ∈ stdBasis5 := by
  revert i
  decide +kernel

private def ExtendsFour (a b c d : Fin 5 → ZMod 2) : Prop :=
  ∀ e ∈ oddVecs5, a ⬝ᵥ e = 0 → b ⬝ᵥ e = 0 → c ⬝ᵥ e = 0 → d ⬝ᵥ e = 0 →
    ∃ i : Fin 6, a ∈ bases5 i ∧ b ∈ bases5 i ∧ c ∈ bases5 i ∧ d ∈ bases5 i ∧ e ∈ bases5 i

private instance (a b c d : Fin 5 → ZMod 2) : Decidable (ExtendsFour a b c d) := by
  unfold ExtendsFour
  infer_instance

private def ExtendsThree (a b c : Fin 5 → ZMod 2) : Prop :=
  ∀ d ∈ oddVecs5, a ⬝ᵥ d = 0 → b ⬝ᵥ d = 0 → c ⬝ᵥ d = 0 → ExtendsFour a b c d

private instance (a b c : Fin 5 → ZMod 2) : Decidable (ExtendsThree a b c) := by
  unfold ExtendsThree
  infer_instance

private def ExtendsTwo (a b : Fin 5 → ZMod 2) : Prop :=
  ∀ c ∈ oddVecs5, a ⬝ᵥ c = 0 → b ⬝ᵥ c = 0 → ExtendsThree a b c

private instance (a b : Fin 5 → ZMod 2) : Decidable (ExtendsTwo a b) := by
  unfold ExtendsTwo
  infer_instance

private def ExtendsOne (a : Fin 5 → ZMod 2) : Prop :=
  ∀ b ∈ oddVecs5, a ⬝ᵥ b = 0 → ExtendsTwo a b

private instance (a : Fin 5 → ZMod 2) : Decidable (ExtendsOne a) := by
  unfold ExtendsOne
  infer_instance

private theorem enumerate_orthonormal5 : ∀ a ∈ oddVecs5, ExtendsOne a := by
  decide +kernel

theorem eq_basis_of_isOrthonormalBasis5 {S : Finset (Fin 5 → ZMod 2)}
    (h : IsOrthonormalBasis5 S) : ∃ i : Fin 6, S = bases5 i := by
  obtain ⟨hcard, hnorm, horth⟩ := h
  obtain ⟨a, t₁, ha, rfl, h₁⟩ := Finset.card_eq_succ.mp hcard
  obtain ⟨b, t₂, hb, rfl, h₂⟩ := Finset.card_eq_succ.mp h₁
  obtain ⟨c, t₃, hc, rfl, h₃⟩ := Finset.card_eq_succ.mp h₂
  obtain ⟨d, t₄, hd, rfl, h₄⟩ := Finset.card_eq_succ.mp h₃
  obtain ⟨e, rfl⟩ := Finset.card_eq_one.mp h₄
  simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at ha hb hc hd
  obtain ⟨hab, hac, had, hae⟩ := ha
  obtain ⟨hbc, hbd, hbe⟩ := hb
  obtain ⟨hcd, hce⟩ := hc
  have hna := hnorm a (by simp)
  have hnb := hnorm b (by simp)
  have hnc := hnorm c (by simp)
  have hnd := hnorm d (by simp)
  have hne := hnorm e (by simp)
  obtain ⟨i, hia, hib, hic, hid, hie⟩ := enumerate_orthonormal5 a (mem_oddVecs5.mpr hna)
    b (mem_oddVecs5.mpr hnb) (horth a (by simp) b (by simp) hab)
    c (mem_oddVecs5.mpr hnc) (horth a (by simp) c (by simp) hac) (horth b (by simp) c (by simp) hbc)
    d (mem_oddVecs5.mpr hnd) (horth a (by simp) d (by simp) had) (horth b (by simp) d (by simp) hbd)
      (horth c (by simp) d (by simp) hcd)
    e (mem_oddVecs5.mpr hne) (horth a (by simp) e (by simp) hae) (horth b (by simp) e (by simp) hbe)
      (horth c (by simp) e (by simp) hce) (horth d (by simp) e (by simp) hd)
  refine ⟨i, Finset.eq_of_subset_of_card_le ?_ ?_⟩
  · simp only [Finset.insert_subset_iff, Finset.singleton_subset_iff]
    exact ⟨hia, hib, hic, hid, hie⟩
  · rw [hcard, (isOrthonormalBasis5_bases5 i).1]

end CFSG.ASVolI.ChH

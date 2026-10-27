module

public import Certificates.Certificate21163
public import CFSG.Sporadic.Co2Smith.GlC0MarkB
public import CFSG.Sporadic.Co2Smith.Structure

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem glQt_check : Native.glQtOK = true :=
  Certificates.certificate21163

theorem glQtGens_size : Native.glQtGens.size = 7 := by simp [Native.glQtGens]

theorem glQtGens_get {k : ℕ} (hk : k < 7) :
    Native.glQtGens[k]! = if k < 6 then Native.glMkGens[k]! else Native.glMkR[16]! := by
  rw [Native.glQtGens, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

theorem glQt_parts :
    Native.commRows Native.glQtD0 Native.glZ = true ∧
    (∀ k < 36, Native.commRows Native.glQtD0 Native.glMkR[k]! = true ↔ k = 0 ∨ k = 16 ∨ k = 18) ∧
    mulRows 22 (mulRows 22 Native.glZ Native.glMkR[16]!) Native.glZ = Native.glMkR[18]! ∧
    (∀ e ∈ Native.glQtLetters, (∀ k ∈ e.2, k < 7) ∧
      Native.wRows Native.glQtGens e.2 = Native.glR [e.1]) ∧
    Native.glMkFixIs (mulRows 22 Native.glGa Native.glZ) 52 = true := by
  have h := glQt_check
  simp only [Native.glQtOK, Bool.and_eq_true, List.all_eq_true, List.mem_range, beq_iff_eq,
    decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, fun k hk => ?_, h3, h4, h5⟩
  rw [h2 k hk]
  simp only [Bool.or_eq_true, beq_iff_eq]
  omega

@[expose] noncomputable def qtLetters : Letters where
  elt k := if k < 6 then genLetters.elt k else if k = 6 then reflK 16 else 1
  rows := Native.glQtGens
  val_eq k hk := by
    rw [glQtGens_size] at hk
    rw [glQtGens_get hk]
    split_ifs with h6
    · exact genLetters.val_eq k (by
        show k < Native.glMkGens.size
        rw [glMkGens_size]
        exact h6)
    · exact reflK_val (by norm_num)
    · omega

section Closure

theorem C0c_le_closure :
    C0c ≤ Subgroup.closure ((C0c ⊓ Cz : Subgroup K) ∪ {reflK 16} : Set K) := by
  set S := Subgroup.closure ((C0c ⊓ Cz : Subgroup K) ∪ {reflK 16} : Set K)
  have hD : ∀ x ∈ C0c ⊓ Cz, x ∈ S := fun x hx => Subgroup.subset_closure (Or.inl hx)
  have hgen : ∀ k, qtLetters.elt k ∈ S := by
    intro k
    show (if k < 6 then genLetters.elt k else if k = 6 then reflK 16 else 1) ∈ S
    split_ifs with h6 h6'
    · show (if k = 0 then z0 else if k < 6 then tK (k - 1) else 1) ∈ S
      split_ifs with h0
      · exact hD _ (Subgroup.mem_inf.2 ⟨x16K_eq ▸ x16K_mem_C0c, z0_mem_Cz⟩)
      · exact hD _ (Subgroup.mem_inf.2 ⟨tK_mem_C0c (by omega),
          mem_Cz_of_comm (tK_comm_z0 (by omega))⟩)
    · exact Subgroup.subset_closure (Or.inr rfl)
    · exact S.one_mem
  have hlet : ∀ k ∈ Native.glC0Let, glElt k ∈ S := by
    intro k hk
    have hk' : k = 0 ∨ k = 11 ∨ k = 12 ∨ k = 13 := by simpa [Native.glC0Let] using hk
    rcases hk' with rfl | hk'
    · rw [show glElt 0 = z0 by rw [← x16K_eq]; exact (mul_one _).symm]
      exact hD _ (Subgroup.mem_inf.2 ⟨x16K_eq ▸ x16K_mem_C0c, z0_mem_Cz⟩)
    obtain ⟨e, he, rfl⟩ : ∃ e ∈ Native.glQtLetters, e.1 = k := by
      rcases hk' with rfl | rfl | rfl
      · exact ⟨(11, [0, 3]), by simp [Native.glQtLetters], rfl⟩
      · exact ⟨(12, [2, 3, 4, 3, 2, 1, 5, 4]), by simp [Native.glQtLetters], rfl⟩
      · exact ⟨(13, [0, 1, 3, 4, 6, 1, 5, 6]), by simp [Native.glQtLetters], rfl⟩
    obtain ⟨hlt, hrow⟩ := glQt_parts.2.2.2.1 e he
    have h1 : (lWord qtLetters e.2).val.val = rowsMatrix 22 (Native.glR [e.1]) := by
      rw [← hrow]
      exact lWord_val qtLetters e.2 fun j hj => by
        show j < Native.glQtGens.size
        rw [glQtGens_size]
        exact hlt j hj
    have h2 : (glElt e.1).val.val = rowsMatrix 22 (Native.glR [e.1]) := by
      rw [← glE_val (w := [e.1]) (by
        intro j hj
        rw [List.mem_singleton.1 hj]
        have : e.1 = 11 ∨ e.1 = 12 ∨ e.1 = 13 := by
          rcases hk' with h | h | h <;> omega
        omega)]
      exact congrArg (fun x : K => x.val.val) (mul_one (glElt e.1)).symm
    rw [eq_of_rows h2 h1 rfl]
    exact lWord_mem_closure qtLetters S hgen e.2
  have hw : ∀ w : List ℕ, (∀ k ∈ w, k ∈ Native.glC0Let) → glE w ∈ S :=
    fun w hw => glE_mem_of_letters hlet hw
  have hu : uK ∈ S := hw _ (by decide)
  have hx61 : x61K ∈ S := hw _ (by decide)
  have h0 : δ0hK ∈ S := hw _ (by decide)
  have h1 : δ1hK ∈ S := hw _ (by decide)
  have hz : x16K ∈ S := hw _ (by decide)
  have hw1 : w1K ∈ S := S.mul_mem (S.mul_mem hz hx61) hz
  have hw2 : w2K ∈ S := S.mul_mem (S.mul_mem h1 hw1) h1
  have hw3 : w3K ∈ S := S.mul_mem (S.mul_mem h0 hw2) h0
  have hv : vK ∈ S := S.mul_mem (S.mul_mem hu (S.mul_mem (S.mul_mem hw1 hw2) hw3)) hu
  have hform : ∀ t, glFormK t ∈ S := by
    intro t
    unfold glFormK
    split
    · exact hu
    · split
      · exact hv
      · exact S.one_mem
  intro g hg
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, rfl⟩ := exists_wit_C0c hg
  obtain ⟨-, hw₀, -⟩ := glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.1 e₀ he₀).1
  obtain ⟨-, hw₁, -⟩ := glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.1 e₁ he₁)
  obtain ⟨-, hw₂, -⟩ := glWitEntry_spec glC0Let_lt (by norm_num) (glWitC0_spec.2.2 e₂ he₂)
  exact S.mul_mem (S.mul_mem (S.mul_mem (hw _ hw₀) (hform _)) (hw _ hw₁)) (hw _ hw₂)

end Closure

end CFSG.Sporadic.Co2Smith

module

public import CFSG.Sporadic.Co2Smith.GlC0Mark

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native Matrix
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem glMkGens_size : Native.glMkGens.size = 6 := by
  simp [Native.glMkGens]

theorem glMkGens_get {k : ℕ} (hk : k < 6) :
    Native.glMkGens[k]! = if k = 0 then Native.glZ else Native.glMkT[k - 1]! := by
  rw [Native.glMkGens, getElem!_pos _ k (by simpa using hk), Array.getElem_ofFn]

@[expose] noncomputable def genLetters : Letters where
  elt k := if k = 0 then z0 else if k < 6 then tK (k - 1) else 1
  rows := Native.glMkGens
  val_eq k hk := by
    rw [glMkGens_size] at hk
    rw [glMkGens_get hk]
    split_ifs with h0
    · exact z0_val'
    · exact tK_val (by omega)

section Gen

theorem glMkGenList_spec {ws : Array (List ℕ)} {es : List (ℕ × List ℕ)}
    (h : Native.glMkGenListOK ws es = true) :
    ∀ e ∈ es, ∃ u : List ℕ, (∀ k ∈ u, k < 6) ∧ Native.wRows Native.glMkGens u = Native.glR e.2 := by
  simp only [Native.glMkGenListOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true,
    List.mem_range, decide_eq_true_eq] at h
  intro e he
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem he
  obtain ⟨h1, h2⟩ := h.2 i hi
  refine ⟨ws[i]!, h1, ?_⟩
  rw [h2, getElem!_pos es i hi]

theorem D_le_of_mem {S : Subgroup K} (hz : z0 ∈ S) (ht : ∀ j < 5, tK j ∈ S) :
    C0c ⊓ Cz ≤ S := by
  have hS : ∀ k, Letters.elt genLetters k ∈ S := by
    intro k
    show (if k = 0 then z0 else if k < 6 then tK (k - 1) else 1) ∈ S
    split_ifs with h0 h6
    · exact hz
    · exact ht _ (by omega)
    · exact S.one_mem
  have hgen := glMark_parts.2.2.2.2
  simp only [Native.glMkGenOK, Bool.and_eq_true] at hgen
  have key : ∀ s < 3, ∀ e ∈ glWitZ s, glE e.2 ∈ S := by
    intro s hs e he
    have hl : ∀ es : List (ℕ × List ℕ), ∀ ws, Native.glMkGenListOK ws es = true → e ∈ es →
        glE e.2 ∈ S := by
      intro es ws hok hes
      obtain ⟨u, hu, hrow⟩ := glMkGenList_spec hok e hes
      have h1 : (lWord genLetters u).val.val = rowsMatrix 22 (Native.glR e.2) := by
        rw [← hrow]
        exact lWord_val genLetters u fun k hk => by
          show k < Native.glMkGens.size
          rw [glMkGens_size]
          exact hu k hk
      rw [← eq_of_rows h1 (glE_val (glWitZ_spec hs he).1) rfl]
      exact lWord_mem_closure genLetters S hS u
    interval_cases s
    · exact hl _ _ hgen.1.1 he
    · exact hl _ _ hgen.1.2 he
    · exact hl _ _ hgen.2 he
  intro g hg
  obtain ⟨e₀, he₀, e₁, he₁, e₂, he₂, rfl⟩ := exists_wit_D hg
  exact S.mul_mem (S.mul_mem (key 0 (by norm_num) e₀ he₀) (key 1 (by norm_num) e₁ he₁))
    (key 2 (by norm_num) e₂ he₂)

end Gen

end CFSG.Sporadic.Co2Smith

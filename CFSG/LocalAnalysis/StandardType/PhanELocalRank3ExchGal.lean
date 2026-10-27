module

public import CFSG.LocalAnalysis.StandardType.PhanELocalRank3ExchDef
import CFSG.LocalAnalysis.StandardType.PhanELocalPlane

public section

namespace CFSG.ClassicalInvolution.Phan.PhanE.Exch

open CFSG.Monster.B.Geometry CFSG.Monster.B.Geometry.ChamberSystem

variable {K : Type} [Field K] [Finite K] {f : ℕ} [CharP K 2]

theorem P_b {e e' : ↥(setA2A1 K f)} (h : (X K f).adj (Sum.inl 1) e e') : P K f e = P K f e' := by
  have h' := (adj_b e e').mp h
  exact Subtype.ext h'.1

theorem P_c {e e' : ↥(setA2A1 K f)} (h : (X K f).adj (Sum.inr 0) e e') : P K f e = P K f e' := by
  have h' := (adj_c e e').mp h
  exact Subtype.ext h'.1

theorem inj_a {e e' : ↥(setA2A1 K f)} (h : (X K f).adj (Sum.inl 0) e e')
    (hP : P K f e = P K f e') : e = e' := by
  have h' := (adj_a e e').mp h
  have h1 : e.1.1.E 1 = e'.1.1.E 1 := by simpa [P] using congrArg Subtype.val hP
  exact Subtype.ext (Prod.ext (Plane.ext h1 h'.1) (flag_ext h'.2))

private theorem plxg_path {e e' : ↥(setA2A1 K f)} (h : P K f e = P K f e') :
    ∃ m : ↥(setA2A1 K f), (X K f).adj (Sum.inl 1) e m ∧ (X K f).adj (Sum.inr 0) m e' ∧
      m.1.1.E 1 = e.1.1.E 1 ∧ m.1.1.E 2 = e'.1.1.E 2 ∧ m.1.2.E 1 = e.1.2.E 1 := by
  have he := (mem_setA2A1_iff (K := K) (f := f) e.1).mp e.2
  have he' := (mem_setA2A1_iff (K := K) (f := f) e'.1).mp e'.2
  have hp : e.1.1.E 1 = e'.1.1.E 1 := by simpa [P] using congrArg Subtype.val h
  obtain ⟨c, hc, hc1, hc2, hc3⟩ := exists_mem_setA2A1 (K := K) (f := f)
    (p := e.1.1.E 1) (l := e'.1.1.E 2) (z := e.1.2.E 1)
    (Plane.finrank_E_one e.1.1) (Plane.finrank_E_two e'.1.1)
    (by rw [hp]; exact Plane.E_one_le_two e'.1.1)
    he.1 he'.2.1 (Exch.finrank_E_one e.1.2) he.2.2
  refine ⟨⟨c, hc⟩, ?_, ?_, hc1, hc2, hc3⟩
  · rw [adj_b]
    exact ⟨hc1.symm, hc3.symm⟩
  · rw [adj_c]
    exact ⟨hc1.trans hp, hc2⟩

theorem fib_exch (e e' : ↥(setA2A1 K f)) (h : P K f e = P K f e') :
    ∃ τ : List ((Fin 2 ⊕ Fin 1) × ↥(setA2A1 K f)),
      IsJGallery (X K f) {Sum.inl 1, Sum.inr 0} e τ ∧ galleryEnd e τ = e' := by
  obtain ⟨m, hb, hc, -, -, -⟩ := plxg_path h
  exact ⟨[(Sum.inl 1, m), (Sum.inr 0, e')],
    IsJGallery.cons (by simp) hb (IsJGallery.cons (by simp) hc IsJGallery.nil),
    by simp [galleryEnd]⟩

theorem edge_exch {e e' g g' : ↥(setA2A1 K f)} (h1 : (X K f).adj (Sum.inl 0) e g)
    (h2 : (X K f).adj (Sum.inl 0) e' g') (hee : P K f e = P K f e') (hgg : P K f g = P K f g')
    (hne : P K f e ≠ P K f g) :
    ∃ τ τ' : List ((Fin 2 ⊕ Fin 1) × ↥(setA2A1 K f)),
      IsJGallery (X K f) {Sum.inl 1, Sum.inr 0} e τ ∧ galleryEnd e τ = e' ∧
        IsJGallery (X K f) {Sum.inl 1, Sum.inr 0} g τ' ∧ galleryEnd g τ' = g' ∧
        (X K f).TwoHomotopic e (τ ++ [(Sum.inl 0, g')]) ((Sum.inl 0, g) :: τ') := by
  obtain ⟨m₁, hb₁, hc₁, hm₁p, hm₁l, hm₁z⟩ := plxg_path hee
  obtain ⟨m₂, hb₂, hc₂, hm₂p, hm₂l, hm₂z⟩ := plxg_path hgg
  have h1' := (adj_a e g).mp h1
  have h2' := (adj_a e' g').mp h2
  have ha : (X K f).adj (Sum.inl 0) m₁ m₂ := by
    rw [adj_a]
    exact ⟨hm₁l.trans (h2'.1.trans hm₂l.symm), hm₁z.trans (h1'.2.trans hm₂z.symm)⟩
  have hJab : ({Sum.inl 0, Sum.inl 1} : Set (Fin 2 ⊕ Fin 1)).encard ≤ 2 := by
    rw [Set.encard_pair (by decide)]
  have hJac : ({Sum.inl 0, Sum.inr 0} : Set (Fin 2 ⊕ Fin 1)).encard ≤ 2 := by
    rw [Set.encard_pair (by decide)]
  have hstep₁ : (X K f).TwoHomotopic e
      [(Sum.inl 0, g), (Sum.inl 1, m₂), (Sum.inr 0, g')]
      [(Sum.inl 1, m₁), (Sum.inl 0, m₂), (Sum.inr 0, g')] := by
    refine twoHomotopic_replace (X := X K f) (x := e) [] [(Sum.inl 0, g), (Sum.inl 1, m₂)]
      [(Sum.inl 1, m₁), (Sum.inl 0, m₂)] [(Sum.inr 0, g')] hJab ?_ ?_ ?_ ?_ rfl
    · exact ⟨h1, hb₂, trivial⟩
    · exact ⟨hb₁, ha, trivial⟩
    · intro i hi
      simp only [galleryType_cons, galleryType_nil, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
      tauto
    · intro i hi
      simp only [galleryType_cons, galleryType_nil, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
      tauto
  have hstep₂ : (X K f).TwoHomotopic e
      [(Sum.inl 1, m₁), (Sum.inl 0, m₂), (Sum.inr 0, g')]
      [(Sum.inl 1, m₁), (Sum.inr 0, e'), (Sum.inl 0, g')] := by
    refine twoHomotopic_replace (X := X K f) (x := e) [(Sum.inl 1, m₁)]
      [(Sum.inl 0, m₂), (Sum.inr 0, g')] [(Sum.inr 0, e'), (Sum.inl 0, g')] [] hJac ?_ ?_ ?_ ?_
      rfl
    · exact ⟨ha, hc₂, trivial⟩
    · exact ⟨hc₁, h2, trivial⟩
    · intro i hi
      simp only [galleryType_cons, galleryType_nil, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
      tauto
    · intro i hi
      simp only [galleryType_cons, galleryType_nil, List.mem_cons, List.not_mem_nil, or_false,
        Set.mem_insert_iff, Set.mem_singleton_iff] at hi ⊢
      tauto
  exact ⟨[(Sum.inl 1, m₁), (Sum.inr 0, e')], [(Sum.inl 1, m₂), (Sum.inr 0, g')],
    IsJGallery.cons (by simp) hb₁ (IsJGallery.cons (by simp) hc₁ IsJGallery.nil),
    by simp [galleryEnd],
    IsJGallery.cons (by simp) hb₂ (IsJGallery.cons (by simp) hc₂ IsJGallery.nil),
    by simp [galleryEnd],
    (hstep₁.trans hstep₂).symm⟩

end CFSG.ClassicalInvolution.Phan.PhanE.Exch

end

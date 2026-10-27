module

public import CFSG.Sporadic.Bridge.Common
public import CFSG.Sporadic.Th.TableSpec
public import Certificates.Data.CFSGNative.Bridge.SurjA

public section

namespace CFSG.Sporadic.Bridge.TwoGen

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Bridge.TwoGen.Native TauCeti

@[expose] def img2 {G : Type*} (x y : G) (i : ℕ) : G := if i = 0 then x else y

section Words

variable {G : Type*} [Group G] {n : ℕ} [MulAction G (Fin n)] {x y : G} {α αi β βi : Table}

theorem rep_letterTab (hx : Rep n α x) (hxi : Rep n αi x⁻¹) (hy : Rep n β y)
    (hyi : Rep n βi y⁻¹) (l : ℕ × Bool) :
    Rep n (letterTab α αi β βi l) (if l.2 then img2 x y l.1 else (img2 x y l.1)⁻¹) := by
  obtain ⟨i, s⟩ := l
  unfold letterTab img2
  by_cases hi : i = 0 <;> cases s <;> simp [hi] <;> assumption

theorem rep_wordTab (hn : n < 2 ^ 32) (hx : Rep n α x) (hxi : Rep n αi x⁻¹) (hy : Rep n β y)
    (hyi : Rep n βi y⁻¹) (v : List (ℕ × Bool)) :
    Rep n (wordTab n α αi β βi v) (wordProd (img2 x y) v) := by
  induction v with
  | nil => exact Rep.idT hn
  | cons l v ih =>
    have e : wordTab n α αi β βi (l :: v) =
        compT n (letterTab α αi β βi l) (wordTab n α αi β βi v) := rfl
    have hw : wordProd (img2 x y) (l :: v) =
        (if l.2 then img2 x y l.1 else (img2 x y l.1)⁻¹) * wordProd (img2 x y) v := by
      simp only [wordProd, List.map_cons, List.prod_cons]
    rw [e, hw]
    exact Rep.compT (rep_letterTab hx hxi hy hyi l) ih

theorem eq_one_of_rep_idT [FaithfulSMul G (Fin n)] (hn : n < 2 ^ 32) {g : G}
    (h : Rep n (idT n) g) : g = 1 := by
  refine FaithfulSMul.eq_of_smul_eq_smul (M := G) (α := Fin n) fun i => ?_
  rw [one_smul]
  apply Fin.ext
  have h1 := h i.val i.isLt
  have h2 := (Rep.idT (G := G) hn) i.val i.isLt
  rw [h1] at h2
  rw [idx_of_lt g i.isLt, idx_one] at h2
  simpa [idx_of_lt g i.isLt] using h2

theorem wordProd_eq_one_of_relCheck [FaithfulSMul G (Fin n)] (hn : n < 2 ^ 32)
    (hx : Rep n α x) (hxi : Rep n αi x⁻¹) (hy : Rep n β y) (hyi : Rep n βi y⁻¹)
    {rels : List (List (ℕ × Bool))} (h : relCheck n α αi β βi rels = true) :
    ∀ v ∈ rels, wordProd (img2 x y) v = 1 := by
  intro v hv
  unfold relCheck at h
  rw [List.all_eq_true] at h
  have hv' := h v hv
  rw [beq_iff_eq] at hv'
  apply eq_one_of_rep_idT hn
  rw [← hv']
  exact rep_wordTab hn hx hxi hy hyi v

end Words

theorem nonempty_mulEquiv_of_closure {G : Type*} [Group G] (P : GroupPresentation)
    (hP : P.generatorCount = 2) {x y : G} (hclosure : Subgroup.closure ({x, y} : Set G) = ⊤)
    (hrel : ∀ v ∈ P.relatorLetters, wordProd (img2 x y) v = 1) [Finite P.Group] {k : ℕ}
    (hcard : Nat.card P.Group ≤ k) (hk : k ≤ Nat.card G) : Nonempty (G ≃* P.Group) := by
  have hsurj : Function.Surjective (presHom P (img2 x y) hrel) := by
    rw [← MonoidHom.range_eq_top, eq_top_iff, ← hclosure, Subgroup.closure_le]
    rintro g (h | h)
    · exact ⟨presGen P 0, by
        rw [presHom_presGen P (img2 x y) hrel (by omega), h]
        simp [img2]⟩
    · rw [Set.mem_singleton_iff] at h
      exact ⟨presGen P 1, by
        rw [presHom_presGen P (img2 x y) hrel (by omega), h]
        simp [img2]⟩
  exact nonempty_mulEquiv_of_surjective _ hsurj hcard hk

end CFSG.Sporadic.Bridge.TwoGen

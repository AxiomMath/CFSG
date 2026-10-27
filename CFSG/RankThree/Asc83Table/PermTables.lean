module

public import CFSG.Sporadic.Schreier.CountSpec

public section

namespace CFSG.RankThree.Asc83Table

open CFSG.Sporadic.Th CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier
open CFSG.Sporadic.Schreier.Native CFSG.Certificates

variable {n : ℕ}

theorem size_compT (P Q : Table) : (compT n P Q).size = n := Array.size_ofFn

theorem beq_iff_of_rep {A B : Table} {g h : Equiv.Perm (Fin n)} (hA : Rep n A g)
    (hB : Rep n B h) (hsA : A.size = n) (hsB : B.size = n) : (A == B) = true ↔ g = h := by
  rw [beq_iff_eq]
  constructor
  · rintro rfl
    refine Equiv.ext fun i => Fin.ext ?_
    have h1 := hA i.val i.isLt
    have h2 := hB i.val i.isLt
    rw [idx_of_lt _ i.isLt] at h1 h2
    exact h1.symm.trans h2
  · rintro rfl
    refine Array.ext (hsA.trans hsB.symm) fun i hi₁ hi₂ => ?_
    have hin : i < n := hsA ▸ hi₁
    have h1 := hA i hin
    have h2 := hB i hin
    unfold ap at h1 h2
    rw [getElem!_pos A i hi₁] at h1
    rw [getElem!_pos B i hi₂] at h2
    exact UInt32.toNat_inj.1 (h1.trans h2.symm)

theorem compT_beq_iff {T X W : Table} {g x w : Equiv.Perm (Fin n)} (hT : Rep n T g)
    (hX : Rep n X x) (hW : Rep n W w) :
    (compT n T X == compT n W T) = true ↔ g * x = w * g :=
  beq_iff_of_rep (Rep.compT hT hX) (Rep.compT hW hT) (size_compT _ _) (size_compT _ _)

theorem not_of_countProducts_eq_zero (hn : n < 2 ^ 32) (Q : RawSchreierDatum n)
    (hQ : ValidSchreier Q) {f : Table → Bool} {P : Equiv.Perm (Fin n) → Prop}
    [DecidablePred P] (hfP : ∀ T g, Rep n T g → (f T = true ↔ P g))
    (h0 : countProducts n f (levelTables Q) (idT n) = 0) {g : Equiv.Perm (Fin n)}
    (hg : g ∈ Q.originalSubgroup) : ¬P g := by
  have hspec := countProducts_spec hfP (forall₂_levelTables hn Q) (Rep.idT hn)
  rw [h0] at hspec
  have hmem : g ∈ (products ((List.finRange Q.baseCount).map (levelTransversals Q))).map
      ((1 : Equiv.Perm (Fin n)) * ·) := by
    rw [List.mem_map]
    exact ⟨g, (mem_enumeration_iff Q hQ g).2 hg, one_mul g⟩
  intro hP
  have := (List.countP_pos_iff (p := fun h => decide (P h))).2 ⟨g, hmem, by simpa using hP⟩
  omega

end CFSG.RankThree.Asc83Table

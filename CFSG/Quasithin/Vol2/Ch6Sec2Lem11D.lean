module

public import CFSG.Quasithin.Vol2.Ch10SecDTL2

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.ASInputs CFSG.Quasithin.Vol2.Ch10.SecD

@[expose] def Ch6G31O2 : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (Gm : Subgroup (MulAut V)), pCoreOf 2 Gm = ⊥ → ∀ (Δ₀ : Set (Subgroup V)), Δ₀.Nonempty →
    (∀ X ∈ Δ₀, Nat.card X = 2) →
    (∀ X ∈ Δ₀, ∀ g ∈ Gm, X.map (g : MulAut V).toMonoidHom ∈ Δ₀) →
    (∀ X ∈ Δ₀, ∀ Y ∈ Δ₀, ∃ g ∈ Gm, X.map (g : MulAut V).toMonoidHom = Y) →
    (∀ X ∈ Δ₀, 4 ≤ (transvGroup Gm X ⊓ pCoreOf 2 Gm).relIndex (transvGroup Gm X)) →
    ∀ (s : ℕ) (hs : 0 < s) (Δ : Fin s → Set (Subgroup V)),
      (∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)) → (⋃ i, Δ i) = Δ₀ → (∀ i, (Δ i).Nonempty) →
      (∀ i, ∀ X ∈ Δ i, ∀ g ∈ g31G Gm Δ₀, X.map (g : MulAut V).toMonoidHom ∈ Δ i) →
      (∀ i, ∀ X ∈ Δ i, ∀ Y ∈ Δ i, ∃ g ∈ g31G Gm Δ₀, X.map (g : MulAut V).toMonoidHom = Y) →
        (iSupIndep (fun i => g31V (Δ i)) ∧ (⨆ i, g31V (Δ i)) = g31V Δ₀ ∧
          iSupIndep (fun i => g31G Gm (Δ i)) ∧ (⨆ i, g31G Gm (Δ i)) = g31G Gm Δ₀ ∧
          (∀ i j, i ≠ j → ∀ a ∈ g31G Gm (Δ i), ∀ b ∈ g31G Gm (Δ j), a * b = b * a) ∧
          (∀ i j, i ≠ j → ∀ a ∈ g31G Gm (Δ i), ∀ v ∈ g31V (Δ j), a v = v) ∧
          ∀ i j, ∃ g ∈ Gm, (g31V (Δ i)).map (g : MulAut V).toMonoidHom = g31V (Δ j) ∧
            (g31G Gm (Δ i)).map (MulAut.conj g).toMonoidHom = g31G Gm (Δ j)) ∧
        ((∀ φ : ↥(g31V (Δ ⟨0, hs⟩)) ≃* ↥(g31V (Δ ⟨0, hs⟩)), ∃ g ∈ g31G Gm (Δ ⟨0, hs⟩),
            ∀ v : ↥(g31V (Δ ⟨0, hs⟩)), g (v : V) = ((φ v : ↥(g31V (Δ ⟨0, hs⟩))) : V)) ∧
          Δ ⟨0, hs⟩ = {X | X ≤ g31V (Δ ⟨0, hs⟩) ∧ Nat.card X = 2} ∧
          IsElemAbelian2 (g31G Gm (Δ ⟨0, hs⟩) ⊓
            fixingSubgroup (MulAut V) (g31V (Δ ⟨0, hs⟩) : Set V)) ∧
          ∀ d : ℕ, Nat.card (g31V (Δ ⟨0, hs⟩)) = 2 ^ d → ∀ X ∈ Δ ⟨0, hs⟩,
            Nat.card (transvGroup Gm X) = 2 ^ (d - 1) * Nat.card ↥(transvGroup Gm X ⊓
              fixingSubgroup (MulAut V) (g31V (Δ ⟨0, hs⟩) : Set V))) ∧
        8 ≤ Nat.card (g31V (Δ ⟨0, hs⟩))

section Orbit

variable {V : Type} [CommGroup V]

@[expose] def orbitCh611 (Gm : Subgroup (MulAut V)) (X₀ : Subgroup V) : Set (Subgroup V) :=
  {X | ∃ g ∈ Gm, X₀.map (g : MulAut V).toMonoidHom = X}

theorem mem_orbitCh611_self (Gm : Subgroup (MulAut V)) (X₀ : Subgroup V) :
    X₀ ∈ orbitCh611 Gm X₀ :=
  ⟨1, Gm.one_mem, map_one_mulAut X₀⟩

theorem map_mem_orbitCh611 {Gm : Subgroup (MulAut V)} {X₀ X : Subgroup V}
    (hX : X ∈ orbitCh611 Gm X₀) {g : MulAut V} (hg : g ∈ Gm) :
    X.map g.toMonoidHom ∈ orbitCh611 Gm X₀ := by
  obtain ⟨h, hh, rfl⟩ := hX
  exact ⟨g * h, Gm.mul_mem hg hh, (map_mul_mulAut h g X₀).symm⟩

theorem g31G_le (Gm : Subgroup (MulAut V)) (Δ : Set (Subgroup V)) : g31G Gm Δ ≤ Gm :=
  iSup₂_le fun X _ => transvGroup_le Gm X

theorem transvGroup_le_g31G (Gm : Subgroup (MulAut V)) {Δ : Set (Subgroup V)} {X : Subgroup V}
    (hX : X ∈ Δ) : transvGroup Gm X ≤ g31G Gm Δ :=
  le_iSup₂_of_le X hX le_rfl

theorem le_g31V {Δ : Set (Subgroup V)} {X : Subgroup V} (hX : X ∈ Δ) : X ≤ g31V Δ :=
  le_iSup₂ (f := fun (Y : Subgroup V) (_ : Y ∈ Δ) => Y) X hX

end Orbit

structure G31Out {V : Type} [CommGroup V] (Gm : Subgroup (MulAut V)) (X₀ : Subgroup V) where
  s : ℕ
  hs : 0 < s
  Δ : Fin s → Set (Subgroup V)
  mem0 : X₀ ∈ Δ ⟨0, hs⟩
  disj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j)
  union : (⋃ i, Δ i) = orbitCh611 Gm X₀
  ne : ∀ i, (Δ i).Nonempty
  ginv : ∀ i, ∀ X ∈ Δ i, ∀ g ∈ g31G Gm (orbitCh611 Gm X₀), X.map g.toMonoidHom ∈ Δ i
  gtrans : ∀ i, ∀ X ∈ Δ i, ∀ Y ∈ Δ i, ∃ g ∈ g31G Gm (orbitCh611 Gm X₀),
    X.map g.toMonoidHom = Y
  indV : iSupIndep (fun i => g31V (Δ i))
  supV : (⨆ i, g31V (Δ i)) = g31V (orbitCh611 Gm X₀)
  supG : (⨆ i, g31G Gm (Δ i)) = g31G Gm (orbitCh611 Gm X₀)
  comm : ∀ i j, i ≠ j → ∀ a ∈ g31G Gm (Δ i), ∀ b ∈ g31G Gm (Δ j), a * b = b * a
  cent : ∀ i j, i ≠ j → ∀ a ∈ g31G Gm (Δ i), ∀ v ∈ g31V (Δ j), a v = v
  trans : ∀ i j, ∃ g ∈ Gm, (g31V (Δ i)).map g.toMonoidHom = g31V (Δ j) ∧
    (g31G Gm (Δ i)).map (MulAut.conj g).toMonoidHom = g31G Gm (Δ j)
  aut : ∀ φ : ↥(g31V (Δ ⟨0, hs⟩)) ≃* ↥(g31V (Δ ⟨0, hs⟩)), ∃ g ∈ g31G Gm (Δ ⟨0, hs⟩),
    ∀ v : ↥(g31V (Δ ⟨0, hs⟩)), g (v : V) = ((φ v : ↥(g31V (Δ ⟨0, hs⟩))) : V)
  pts : Δ ⟨0, hs⟩ = {X | X ≤ g31V (Δ ⟨0, hs⟩) ∧ Nat.card X = 2}
  card : ∀ d : ℕ, Nat.card (g31V (Δ ⟨0, hs⟩)) = 2 ^ d → ∀ X ∈ Δ ⟨0, hs⟩,
    Nat.card (transvGroup Gm X) = 2 ^ (d - 1) * Nat.card ↥(transvGroup Gm X ⊓
      fixingSubgroup (MulAut V) (g31V (Δ ⟨0, hs⟩) : Set V))
  eight : 8 ≤ Nat.card (g31V (Δ ⟨0, hs⟩))

theorem g31_apply_ch611 (hG31 : Ch6G31O2) {V : Type} [CommGroup V] [Finite V]
    (hV : ∀ v : V, v ^ 2 = 1) {Gm : Subgroup (MulAut V)} (hO2 : pCoreOf 2 Gm = ⊥)
    {X₀ : Subgroup V} (hX₀ : Nat.card X₀ = 2) (hA : 4 ≤ Nat.card (transvGroup Gm X₀)) :
    Nonempty (G31Out Gm X₀) := by
  classical
  set Δ₀ := orbitCh611 Gm X₀ with hΔ₀
  set G0 := g31G Gm Δ₀ with hG0
  have hG0le : G0 ≤ Gm := g31G_le Gm Δ₀
  have hX0Δ : X₀ ∈ Δ₀ := mem_orbitCh611_self Gm X₀
  have hcard : ∀ X ∈ Δ₀, Nat.card X = 2 := by
    rintro X ⟨g, hg, rfl⟩
    rw [← hX₀]
    exact Subgroup.card_map_of_injective (MulEquiv.injective g)
  have hinv : ∀ X ∈ Δ₀, ∀ g ∈ Gm, X.map g.toMonoidHom ∈ Δ₀ := fun X hX g hg =>
    map_mem_orbitCh611 hX hg
  have htrans : ∀ X ∈ Δ₀, ∀ Y ∈ Δ₀, ∃ g ∈ Gm, X.map g.toMonoidHom = Y := by
    rintro X ⟨h, hh, rfl⟩ Y ⟨k, hk, rfl⟩
    refine ⟨k * h⁻¹, Gm.mul_mem hk (Gm.inv_mem hh), ?_⟩
    rw [map_mul_mulAut, mul_assoc, inv_mul_cancel, mul_one]
  have hrel : ∀ X ∈ Δ₀, 4 ≤ (transvGroup Gm X ⊓ pCoreOf 2 Gm).relIndex (transvGroup Gm X) := by
    rintro X ⟨g, hg, rfl⟩
    rw [hO2, inf_bot_eq, Subgroup.relIndex_bot_left]
    exact hA.trans (card_transvGroup_le hg X₀)
  have : Finite (Subgroup V) :=
    Finite.of_injective (fun H : Subgroup V => (H : Set V)) SetLike.coe_injective
  set r := orbitSetoid G0 with hr
  set Q0 : Set (Quotient r) := (Quotient.mk r) '' Δ₀ with hQ0
  have hq0 : Quotient.mk r X₀ ∈ Q0 := ⟨X₀, hX0Δ, rfl⟩
  have : Nonempty ↥Q0 := ⟨⟨_, hq0⟩⟩
  have hs : 0 < Nat.card ↥Q0 := Nat.card_pos
  set e' : ↥Q0 ≃ Fin (Nat.card ↥Q0) := Finite.equivFin ↥Q0 with he'
  set e : ↥Q0 ≃ Fin (Nat.card ↥Q0) := e'.trans (Equiv.swap (e' ⟨_, hq0⟩) ⟨0, hs⟩) with he
  have he0 : e ⟨_, hq0⟩ = ⟨0, hs⟩ := by
    rw [he, Equiv.trans_apply, Equiv.swap_apply_left]
  set Δ : Fin (Nat.card ↥Q0) → Set (Subgroup V) :=
    fun i => {X | ∃ hX : X ∈ Δ₀, e ⟨Quotient.mk r X, X, hX, rfl⟩ = i} with hΔ
  have hdisj : ∀ i j, i ≠ j → Disjoint (Δ i) (Δ j) := by
    intro i j hij
    rw [Set.disjoint_left]
    rintro X ⟨hX, rfl⟩ ⟨hX', h'⟩
    exact hij h'
  have hunion : (⋃ i, Δ i) = Δ₀ := by
    ext X
    simp only [Set.mem_iUnion]
    constructor
    · rintro ⟨i, hX, -⟩
      exact hX
    · intro hX
      exact ⟨_, hX, rfl⟩
  have hne : ∀ i, (Δ i).Nonempty := by
    intro i
    obtain ⟨X, hX, hXq⟩ := (e.symm i).2
    refine ⟨X, hX, ?_⟩
    rw [show (⟨Quotient.mk r X, X, hX, rfl⟩ : ↥Q0) = e.symm i from Subtype.ext hXq,
      Equiv.apply_symm_apply]
  have hGinv : ∀ i, ∀ X ∈ Δ i, ∀ g ∈ G0, X.map g.toMonoidHom ∈ Δ i := by
    rintro i X ⟨hX, rfl⟩ g hg
    refine ⟨hinv X hX g (hG0le hg), ?_⟩
    congr 1
    exact Subtype.ext (Quotient.sound (show r.r X (X.map g.toMonoidHom) from ⟨g, hg, rfl⟩)).symm
  have hGtrans : ∀ i, ∀ X ∈ Δ i, ∀ Y ∈ Δ i, ∃ g ∈ G0, X.map g.toMonoidHom = Y := by
    rintro i X ⟨hX, hXi⟩ Y ⟨hY, hYi⟩
    exact Quotient.exact (congrArg Subtype.val (e.injective (hXi.trans hYi.symm)))
  have hX00 : X₀ ∈ Δ ⟨0, hs⟩ := ⟨hX0Δ, he0⟩
  obtain ⟨⟨hindV, hsupV, -, hsupG, hcomm, hcent, htr⟩, ⟨haut, hpts, -, hcd⟩, h8⟩ :=
    hG31 V hV Gm hO2 Δ₀ ⟨X₀, hX0Δ⟩ hcard hinv htrans hrel _ hs Δ hdisj hunion hne hGinv
      hGtrans
  exact ⟨⟨_, hs, Δ, hX00, hdisj, hunion, hne, hGinv, hGtrans, hindV, hsupV, hsupG, hcomm,
    hcent, htr, haut, hpts, hcd, h8⟩⟩

end CFSG.Quasithin.H13

module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Section 4, equation (11): the region inequality

The natural `(p₁ - 1) · q · k' · L ≤ |G : M|` inequality for the linear
equation-(11) region count, assembled from the generic count endpoints:
`hXs` (at least `(p₁ - 1) · q · k'` conjugates `X ≠ P` of `P` in the
region), `hYs` (at least `L` admissible conjugates per `X`), and `huniq`
(an admissible conjugate determines its line).  The injection
`(X, i) ↦ the i-th element of `Ys X`` from `Xs × Fin L` into the
conjugate class of `P` (explicit `Fintype.equivFin` + `Fin.castLE`
embeddings) yields the bound; `hNP` identifies `M` as the normalizer so
the conjugate class has cardinal `M.index`.  Source-specific hypotheses
(`hXs`, `hYs`, `huniq`) are inputs only — they are discharged by the
equation-(11) region producer / the `Equation11Aligned` and
`Equation11BadFiber` peers at the integration site.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-! ## The conjugate class of `P` -/

/-- The conjugacy class of `P` under the conjugation action has cardinal
equal to the index of its normalizer (orbit-stabilizer). -/
private theorem conjugate_family_card
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G) :
    Nat.card {X : Subgroup G // ∃ g : G,
      X = P.map (MulAut.conj g).toMonoidHom} =
      (Subgroup.normalizer (P : Set G)).index := by
  classical
  letI : MulAction G (Subgroup G) :=
    { smul := fun g H => H.map (MulAut.conj g).toMonoidHom
      one_smul := by
        intro H
        change H.map (MulAut.conj (1 : G)).toMonoidHom = H
        apply Subgroup.ext
        intro x
        rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
          ext x; simp]
        simp
      mul_smul := by
        intro g h H
        change H.map (MulAut.conj (g * h)).toMonoidHom =
          (H.map (MulAut.conj h).toMonoidHom).map (MulAut.conj g).toMonoidHom
        rw [Subgroup.map_map]
        congr 1
        ext x
        simp [MulAut.conj_apply, mul_assoc] }
  have horbit :
      MulAction.orbit G P =
        {X : Subgroup G | ∃ g : G,
          X = P.map (MulAut.conj g).toMonoidHom} := by
    ext X
    constructor
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, rfl⟩
  have hstab : MulAction.stabilizer G P =
      Subgroup.normalizer (P : Set G) := by
    ext g
    change g • P = P ↔ g ∈ Subgroup.normalizer (P : Set G)
    rw [eq_comm, SetLike.ext_iff,
      ← inv_mem_iff (G := G) (H := Subgroup.normalizer P),
      Subgroup.mem_normalizer_iff, inv_inv]
    exact forall_congr' fun h =>
      iff_congr Iff.rfl
        ⟨fun ⟨a, b, c⟩ => c ▸ by simpa [mul_assoc] using b,
          fun hh => ⟨(MulAut.conj g)⁻¹ h, hh,
            MulAut.apply_inv_self G (MulAut.conj g) h⟩⟩
  change Nat.card ↥{X : Subgroup G | ∃ g : G,
    X = P.map (MulAut.conj g).toMonoidHom} = _
  rw [← horbit, Nat.card_coe_set_eq,
    ← MulAction.index_stabilizer G P, hstab]

/-! ## The region inequality -/

/-- The `(p₁ - 1) · q · k' · L ≤ |G : M|` region inequality.

`Xs` is a family of at least `(p₁ - 1) · q · k'` conjugates `X ≠ P` of
`P` (one per line region), `Ys X` provides at least `L` admissible
conjugates per line, and `huniq` says an admissible conjugate lies in a
unique line.  The injection `(X, i) ↦ the i-th element of `Ys X`` from
`Xs × Fin L` into the conjugate class of `P` is injective (explicit
`Fintype.equivFin` + `Fin.castLE` embeddings), so
`|Xs| · L ≤ |{conjugates of P}| = (normalizer P).index = M.index`. -/
public theorem secondCase_linearEquation11_region_inequality
    {G : Type u} [Group G] [Finite G]
    (M P : Subgroup G) {p1 q k' L : ℕ}
    (hNP : Subgroup.normalizer (P : Set G) = M)
    (Region : Subgroup G → Prop) (Adm : Subgroup G → Subgroup G → Prop)
    (hXs : (p1 - 1) * q * k' ≤ Nat.card {X : Subgroup G //
      (∃ g : G, X = P.map (MulAut.conj g).toMonoidHom) ∧ X ≠ P ∧ Region X})
    (hYs : ∀ X : Subgroup G,
      L ≤ Nat.card {Y : Subgroup G //
        (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧ Adm X Y})
    (huniq : ∀ {X₁ X₂ Y : Subgroup G}, Adm X₁ Y → Adm X₂ Y → X₁ = X₂) :
    (p1 - 1) * q * k' * L ≤ M.index := by
  classical
  let Xs : Type u := {X : Subgroup G //
    (∃ g : G, X = P.map (MulAut.conj g).toMonoidHom) ∧ X ≠ P ∧ Region X}
  let Ys : Xs → Type u := fun X => {Y : Subgroup G //
    (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧ Adm X.1 Y}
  let ConjP : Type u := {Y : Subgroup G // ∃ g : G,
    Y = P.map (MulAut.conj g).toMonoidHom}
  letI : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  let Lle : ∀ X : Xs, L ≤ Fintype.card (Ys X) := fun X =>
    by
      have h1 : L ≤ Nat.card (Ys X) := by
        simpa [Ys] using hYs X.1
      simpa [Nat.card_eq_fintype_card] using h1
  -- the explicit Fin embedding of `Ys X` for each line `X`
  let embed : ∀ X : Xs, Fin L → Ys X := fun X i =>
    (Fintype.equivFin (Ys X)).symm (Fin.castLE (Lle X) i)
  -- the pair injection `(X, i) ↦ the i-th admissible conjugate of line X`
  let f : Xs × Fin L → ConjP := fun p =>
    ⟨(embed p.1 p.2).1, (embed p.1 p.2).2.1⟩
  have hembed_inj : ∀ X : Xs, Function.Injective (embed X) := by
    intro X i j hij
    apply Fin.ext
    change (Fintype.equivFin (Ys X)).symm (Fin.castLE (Lle X) i) =
      (Fintype.equivFin (Ys X)).symm (Fin.castLE (Lle X) j) at hij
    have h1 : Fin.castLE (Lle X) i = Fin.castLE (Lle X) j := by
      simpa only [Equiv.apply_symm_apply] using
        congrArg (Fintype.equivFin (Ys X)) hij
    simpa using congrArg Fin.val h1
  have hinj : Function.Injective f := by
    intro p q hpq
    rcases p with ⟨Xp, ip⟩
    rcases q with ⟨Xq, iq⟩
    have hY : (embed Xp ip).1 = (embed Xq iq).1 := congrArg Subtype.val hpq
    have hX : Xp = Xq := by
      apply Subtype.ext
      exact huniq (embed Xp ip).2.2 (by simpa [hY.symm] using (embed Xq iq).2.2)
    subst Xq
    have hY' : (embed Xp ip).1 = (embed Xp iq).1 := by
      simpa using hY
    have hEq : embed Xp ip = embed Xp iq := Subtype.ext hY'
    have hCast : Fin.castLE (Lle Xp) ip = Fin.castLE (Lle Xp) iq := by
      simpa [embed, Equiv.apply_symm_apply] using congrArg (Fintype.equivFin (Ys Xp)) hEq
    have hipq : ip = iq := by
      apply Fin.ext
      simpa using congrArg Fin.val hCast
    exact Prod.ext rfl hipq
  have hcard : Nat.card Xs * L ≤ Nat.card ConjP := by
    simpa using (Nat.card_mul_le_of_injective_pair f hinj)
  have hXs' : (p1 - 1) * q * k' ≤ Nat.card Xs := by
    simpa [Xs] using hXs
  have hConj : Nat.card ConjP = M.index := by
    calc
      Nat.card ConjP = (Subgroup.normalizer (P : Set G)).index := by
        simpa [ConjP] using conjugate_family_card P
      _ = M.index := by rw [hNP]
  calc
    (p1 - 1) * q * k' * L = ((p1 - 1) * q * k') * L := by ring
    _ ≤ Nat.card Xs * L := Nat.mul_le_mul_right L hXs'
    _ ≤ Nat.card ConjP := hcard
    _ = M.index := hConj

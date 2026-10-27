module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseEquationEleven
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Equation (11): indexed region inequality

The outer product family is naturally indexed by pairs `(line, torus)`.  The
underlying subgroup of a pair is a conjugate of `P`, but the pair also retains
the conjugator needed to transport the aligned rank-two geometry.  This
module isolates the counting argument from the particular representation of
the region index.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- An indexed family of regions, each carrying at least `L` admissible
conjugates, injects into the ambient conjugacy class when an admissible
conjugate determines its region index.  The map `X` need not be injective as a
function into subgroups; the uniqueness hypothesis is stated directly on
indices, which is the form used by the product-family construction. -/
public theorem secondCase_linearEquation11_indexed_region_inequality
    {G : Type u} [Group G] [Finite G]
    (M P : Subgroup G) {Xs : Type u} [Finite Xs]
    {p q k' L : ℕ}
    (hNP : Subgroup.normalizer (P : Set G) = M)
    (Adm : Xs → Subgroup G → Prop)
    (hYs' : ∀ x : Xs,
      L ≤ Nat.card {Y : Subgroup G //
        (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧ Adm x Y})
    (huniq : ∀ {x₁ x₂ : Xs} {Y : Subgroup G},
      Adm x₁ Y → Adm x₂ Y → x₁ = x₂)
    (hXs : (p - 1) * q * k' ≤ Nat.card Xs) :
    (p - 1) * q * k' * L ≤ M.index := by
  classical
  let Ys : Xs → Type u := fun x => {Y : Subgroup G //
    (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧ Adm x Y}
  let ConjP : Type u := {Y : Subgroup G // ∃ g : G,
    Y = P.map (MulAut.conj g).toMonoidHom}
  let : Fintype Xs := Fintype.ofFinite Xs
  let : Fintype (Subgroup G) := Fintype.ofFinite (Subgroup G)
  have hLle : ∀ x : Xs, L ≤ Fintype.card (Ys x) := by
    intro x
    change L ≤ Fintype.card {Y : Subgroup G //
      (∃ g : G, Y = P.map (MulAut.conj g).toMonoidHom) ∧ Adm x Y}
    rw [← Nat.card_eq_fintype_card]
    exact hYs' x
  let embed : ∀ x : Xs, Fin L → Ys x := fun x i =>
    (Fintype.equivFin (Ys x)).symm (Fin.castLE (hLle x) i)
  have hembed_inj : ∀ x : Xs, Function.Injective (embed x) := by
    intro x i j hij
    apply Fin.ext
    have hcast : Fin.castLE (hLle x) i = Fin.castLE (hLle x) j := by
      simpa [embed, Equiv.apply_symm_apply] using
        congrArg (Fintype.equivFin (Ys x)) hij
    simpa using congrArg Fin.val hcast
  let f : Xs × Fin L → ConjP := fun xi =>
    ⟨(embed xi.1 xi.2).1, (embed xi.1 xi.2).2.1⟩
  have hinj : Function.Injective f := by
    intro a b hab
    rcases a with ⟨a, i⟩
    rcases b with ⟨b, j⟩
    have hY : (embed a i).1 = (embed b j).1 :=
      congrArg Subtype.val hab
    have hX : a = b := huniq (embed a i).2.2
      (by simpa [hY.symm] using (embed b j).2.2)
    cases hX
    have hEq : embed a i = embed a j := by
      apply Subtype.ext
      simpa using hY
    have hcast : Fin.castLE (hLle a) i =
        Fin.castLE (hLle a) j := by
      simpa [embed, Equiv.apply_symm_apply] using
        congrArg (Fintype.equivFin (Ys a)) hEq
    have hij : i = j := by
      apply Fin.ext
      simpa using congrArg Fin.val hcast
    exact Prod.ext rfl hij
  have hcard : Nat.card Xs * L ≤ Nat.card ConjP := by
    simpa using (Nat.card_mul_le_of_injective_pair f hinj)
  have hConj : Nat.card ConjP = M.index := by
    classical
    let : MulAction G (Subgroup G) :=
      { smul := fun g H => H.map (MulAut.conj g).toMonoidHom
        one_smul := by
          intro H
          apply Subgroup.ext
          intro x
          change x ∈ H.map (MulAut.conj (1 : G)).toMonoidHom ↔ x ∈ H
          rw [show (MulAut.conj (1 : G)).toMonoidHom = MonoidHom.id G by
            ext z; simp]
          simp
        mul_smul := by
          intro g h H
          change H.map (MulAut.conj (g * h)).toMonoidHom =
            (H.map (MulAut.conj h).toMonoidHom).map
              (MulAut.conj g).toMonoidHom
          rw [Subgroup.map_map]
          congr 1
          ext z
          simp [MulAut.conj_apply, mul_assoc] }
    have horbit : MulAction.orbit G P = {Y : Subgroup G | ∃ g : G,
        Y = P.map (MulAut.conj g).toMonoidHom} := by
      ext Y
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
    change Nat.card ↥{Y : Subgroup G | ∃ g : G,
      Y = P.map (MulAut.conj g).toMonoidHom} = _
    rw [← horbit, Nat.card_coe_set_eq,
      ← MulAction.index_stabilizer G P, hstab, hNP]
  calc
    (p - 1) * q * k' * L = ((p - 1) * q * k') * L := by ring
    _ ≤ Nat.card Xs * L := Nat.mul_le_mul_right L hXs
    _ ≤ Nat.card ConjP := hcard
    _ = M.index := hConj

end CFSG.GorensteinWalter

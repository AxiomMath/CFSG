module

public import CFSG.RankThree.PartOne.NF7J.Model1

public section

namespace CFSG.RankThree.PartOne.NF7J

open CFSG CFSG.RankThree.PartOne CFSG.Assembly.LowTwoRank
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Trans

variable {G : Type} [Group G] [Finite G] {p : ℕ} [Fact p.Prime] {E : Subgroup G}
  (f : Multiplicative (Fin 3 → ZMod p) ≃* E)

@[expose] def invAut (hc : ∀ x y : E, x * y = y * x) : MulAut E where
  toFun x := x⁻¹
  invFun x := x⁻¹
  left_inv := inv_inv
  right_inv := inv_inv
  map_mul' x y := by rw [_root_.mul_inv_rev, hc]

omit [Finite G] in
theorem coordGL_invAut (hc : ∀ x y : E, x * y = y * x) :
    LinAlg.coordGL f (invAut hc) = -1 := by
  apply Units.ext
  apply Matrix.toLin'.injective
  apply LinearMap.ext
  intro v
  rw [Matrix.toLin'_apply, Matrix.toLin'_apply, LinAlg.coordGL_mulVec, LinAlg.coordLin_apply]
  have : (((-1 : GL (Fin 3) (ZMod p)) : Matrix (Fin 3) (Fin 3) (ZMod p)) *ᵥ v) = -v := by
    rw [Units.val_neg, Units.val_one, Matrix.neg_mulVec, Matrix.one_mulVec]
  rw [this]
  show Multiplicative.toAdd (f.symm ((f (Multiplicative.ofAdd v))⁻¹)) = -v
  rw [map_inv]
  simp

theorem exists_datum (hc : ∀ x y : E, x * y = y * x) (H : Subgroup (GL (Fin 3) (ZMod p)))
    (hHX : H ≤ (reflectionGroup p E).map (LinAlg.coordGL f))
    (e : ↥H ≃* GL (Fin 3) (ZMod 2))
    (hD : ∀ t ∈ LinAlg.coordGL f '' reflectionSet p E, ∃ a ∈ H, a * a = 1 ∧ a ≠ 1 ∧
      t = (-1 : GL (Fin 3) (ZMod p)) * a)
    (hD' : ∀ a ∈ H, a * a = 1 → a ≠ 1 →
      (-1 : GL (Fin 3) (ZMod p)) * a ∈ LinAlg.coordGL f '' reflectionSet p E) :
    Nonempty (Datum p E) := by
  classical
  have hinj := LinAlg.coordGL_injective f
  have hν1 : LinAlg.coordGL f (invAut hc) = -1 := coordGL_invAut f hc
  let H' : Subgroup (MulAut E) := H.comap (LinAlg.coordGL f) ⊓ reflectionGroup p E
  have hH' : H'.map (LinAlg.coordGL f) = H := by
    ext g
    constructor
    · rintro ⟨x, ⟨hx1, -⟩, rfl⟩
      exact hx1
    · intro hg
      obtain ⟨x, hx, hxg⟩ := hHX hg
      exact ⟨x, ⟨by simpa [hxg] using hg, hx⟩, hxg⟩
  let e' : ↥H' ≃* GL (Fin 3) (ZMod 2) :=
    ((Subgroup.equivMapOfInjective H' (LinAlg.coordGL f) hinj).trans
      (MulEquiv.subgroupCongr hH')).trans e
  refine ⟨{ H := H', e := e', ν := invAut hc, hν := fun x => rfl, hD := ?_, hD' := ?_, hHW := ?_ }⟩
  · intro t ht
    obtain ⟨a, haH, ha2, ha1, hta⟩ := hD (LinAlg.coordGL f t) ⟨t, ht, rfl⟩
    obtain ⟨x, hxX, hxa⟩ := hHX haH
    refine ⟨x, ⟨by simpa [hxa] using haH, hxX⟩, ?_, ?_, ?_⟩
    · apply hinj
      rw [map_mul, hxa, map_one, ha2]
    · intro h1
      apply ha1
      rw [← hxa, h1, map_one]
    · apply hinj
      rw [map_mul, hν1, hxa]
      exact hta
  · intro x hx hx2 hx1
    have hxH : LinAlg.coordGL f x ∈ H := hx.1
    obtain ⟨t, ht, hteq⟩ := hD' (LinAlg.coordGL f x) hxH (by rw [← map_mul, hx2, map_one])
      (fun h => hx1 (hinj (by rw [h, map_one])))
    have : invAut hc * x = t := hinj (by rw [map_mul, hν1, hteq])
    rw [this]
    exact ht
  · intro x hx
    exact Sec1322.reflectionGroup_le E hx.2

end Trans

end CFSG.RankThree.PartOne.NF7J

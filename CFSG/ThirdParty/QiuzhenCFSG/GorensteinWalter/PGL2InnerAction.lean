module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PGL2DerivedSubgroup
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Center

namespace CFSG
end CFSG
open CFSG

/-!
# The projective general linear action on `PSL₂`

For an odd finite field, the canonical image of `PSL₂(K)` has index two
and trivial centralizer in `PGL₂(K)`.  For `|K| > 3` this image is the
characteristic commutator subgroup, so conjugation restricts to a faithful
action

`PGL₂(K) → Aut(PSL₂(K))`.

This is the inner/projective-linear layer of the eventual projective
semilinear automorphism group.
-/

noncomputable section

namespace CFSG.GorensteinWalter

universe u

/-- The canonical equivalence between `PSL₂(K)` and its image in
`PGL₂(K)`. -/
public def psl2EquivToPGLRange (K : Type u) [Field K] :
    PSL2 K ≃*
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).range :=
  MulEquiv.ofBijective
    (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).rangeRestrict
    ⟨fun _a _b hab =>
        Matrix.ProjectiveSpecialLinearGroup.toPGL_injective
          (congrArg Subtype.val hab),
      (Matrix.ProjectiveSpecialLinearGroup.toPGL
        (n := Fin 2) (R := K)).rangeRestrict_surjective⟩

/-- An index-two subgroup is self-centralizing when both it and the ambient
group are centerless. -/
public theorem centralizer_eq_bot_of_index_eq_two_of_centers_eq_bot
    {G : Type u} [Group G] (H : Subgroup G)
    (hindex : H.index = 2)
    (hZH : Subgroup.center H = ⊥)
    (hZG : Subgroup.center G = ⊥) :
    Subgroup.centralizer (H : Set G) = ⊥ := by
  apply le_bot_iff.mp
  intro c hc
  by_cases hcH : c ∈ H
  · let cH : H := ⟨c, hcH⟩
    have hcZ : cH ∈ Subgroup.center H := by
      rw [Subgroup.mem_center_iff]
      intro h
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_iff.mp hc) h h.2
    rw [hZH] at hcZ
    have hcHone : cH = 1 := Subgroup.mem_bot.mp hcZ
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val hcHone)
  · have hcZ : c ∈ Subgroup.center G := by
      rw [Subgroup.mem_center_iff]
      intro g
      by_cases hgH : g ∈ H
      · exact (Subgroup.mem_centralizer_iff.mp hc) g hgH
      · have hcinv : c⁻¹ ∉ H := by simpa using hcH
        have hgc : g * c⁻¹ ∈ H :=
          (H.mul_mem_iff_of_index_two hindex).mpr
            (iff_of_false hgH hcinv)
        have hcomm :=
          (Subgroup.mem_centralizer_iff.mp hc) (g * c⁻¹) hgc
        calc
          g * c = ((g * c⁻¹) * c) * c := by group
          _ = (c * (g * c⁻¹)) * c := by rw [hcomm]
          _ = c * g := by group
    rw [hZG] at hcZ
    exact Subgroup.mem_bot.mp hcZ

/-- Over an odd finite field, the canonical `PSL₂(K)` image has index two
in `PGL₂(K)`. -/
public theorem pgl2_psl2Range_index_eq_two
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range.index = 2 := by
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  let H : Subgroup (PGL2 K) := toPGL.range
  let e : PSL2 K ≃* H := psl2EquivToPGLRange K
  have hHcard : Nat.card H = Nat.card (PSL2 K) :=
    (Nat.card_congr e.toEquiv).symm
  have hqOdd : Odd (Nat.card K) := by
    rcases hK with ⟨p, n, _hp, hpOdd, _hn, hcard⟩
    rw [hcard]
    exact hpOdd.pow
  have hfactorEven : Even (Nat.card K ^ 2 - 1) :=
    Nat.Odd.sub_odd hqOdd.pow (show Odd (1 : ℕ) from odd_one)
  have hdvd : 2 ∣ Nat.card K * (Nat.card K ^ 2 - 1) :=
    dvd_mul_of_dvd_right hfactorEven.two_dvd _
  have hdouble : 2 * Nat.card (PSL2 K) = Nat.card (PGL2 K) := by
    rw [psl2_card_formula K hK, pgl2_card_formula K]
    calc
      2 * (Nat.card K * (Nat.card K ^ 2 - 1) / 2) =
          (Nat.card K * (Nat.card K ^ 2 - 1) / 2) * 2 :=
        Nat.mul_comm _ _
      _ = Nat.card K * (Nat.card K ^ 2 - 1) := Nat.div_mul_cancel hdvd
  have hi := Subgroup.index_mul_card H
  rw [hHcard, ← hdouble] at hi
  change H.index = 2
  exact Nat.eq_of_mul_eq_mul_right Nat.card_pos hi

/-- The canonical `PSL₂(K)` image is self-centralizing in `PGL₂(K)`
for every odd finite field. -/
public theorem pgl2_psl2Range_centralizer_eq_bot
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) :
    Subgroup.centralizer
        ((Matrix.ProjectiveSpecialLinearGroup.toPGL
          (n := Fin 2) (R := K)).range : Set (PGL2 K)) = ⊥ := by
  let H : Subgroup (PGL2 K) :=
    (Matrix.ProjectiveSpecialLinearGroup.toPGL
      (n := Fin 2) (R := K)).range
  let e : PSL2 K ≃* H := psl2EquivToPGLRange K
  apply centralizer_eq_bot_of_index_eq_two_of_centers_eq_bot H
  · exact pgl2_psl2Range_index_eq_two K hK
  · exact center_eq_bot_of_mulEquiv e.symm (psl2_center_eq_bot K)
  · exact pgl2_center_eq_bot K

/-- For `|K| > 3`, conjugation on the characteristic `PSL₂(K)` range
gives the projective-linear action on `PSL₂(K)`. -/
public def pgl2InnerAutPSL2
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    PGL2 K →* MulAut (PSL2 K) := by
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  let H : Subgroup (PGL2 K) := toPGL.range
  letI : H.Normal := by
    dsimp [H, toPGL]
    rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    infer_instance
  let e : PSL2 K ≃* H := psl2EquivToPGLRange K
  exact (MulAut.congr e.symm).toMonoidHom.comp
    (MulAut.conjNormal (H := H))

/-- On the canonical `PSL₂` image, the projective-linear action is literal
conjugation inside `PGL₂`. -/
public theorem toPGL_pgl2InnerAutPSL2_apply
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (g : PGL2 K) (x : PSL2 K) :
    Matrix.ProjectiveSpecialLinearGroup.toPGL
        (pgl2InnerAutPSL2 K hK hcard g x) =
      g * Matrix.ProjectiveSpecialLinearGroup.toPGL x * g⁻¹ := by
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  let H : Subgroup (PGL2 K) := toPGL.range
  let : H.Normal := by
    dsimp [H, toPGL]
    rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    infer_instance
  let e : PSL2 K ≃* H := psl2EquivToPGLRange K
  change ((e (e.symm
    ((MulAut.conjNormal (H := H) g) (e x))) : H) : PGL2 K) = _
  rw [e.apply_symm_apply]
  rw [MulAut.conjNormal_apply]
  rfl

/-- The projective-linear action restricts on the canonical `PSL₂` image
to ordinary inner conjugation. -/
public theorem pgl2InnerAutPSL2_toPGL
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K)
    (y : PSL2 K) :
    pgl2InnerAutPSL2 K hK hcard
        (Matrix.ProjectiveSpecialLinearGroup.toPGL y) =
      MulAut.conj y := by
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  let H : Subgroup (PGL2 K) := toPGL.range
  let : H.Normal := by
    dsimp [H, toPGL]
    rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    infer_instance
  let e : PSL2 K ≃* H := psl2EquivToPGLRange K
  apply MulEquiv.ext
  intro x
  change e.symm
      ((MulAut.conjNormal (H := H)
        (Matrix.ProjectiveSpecialLinearGroup.toPGL y)) (e x)) =
    MulAut.conj y x
  apply e.injective
  apply Subtype.ext
  rw [e.apply_symm_apply]
  rw [MulAut.conjNormal_apply]
  change Matrix.ProjectiveSpecialLinearGroup.toPGL y *
      Matrix.ProjectiveSpecialLinearGroup.toPGL x *
        (Matrix.ProjectiveSpecialLinearGroup.toPGL y)⁻¹ =
    Matrix.ProjectiveSpecialLinearGroup.toPGL (MulAut.conj y x)
  simp [MulAut.conj_apply]

/-- The projective-linear action on `PSL₂(K)` is faithful. -/
public theorem pgl2InnerAutPSL2_injective
    (K : Type u) [Field K] [Finite K]
    (hK : IsOddPrimePower (Nat.card K)) (hcard : 3 < Nat.card K) :
    Function.Injective (pgl2InnerAutPSL2 K hK hcard) := by
  let toPGL : PSL2 K →* PGL2 K :=
    Matrix.ProjectiveSpecialLinearGroup.toPGL
  let H : Subgroup (PGL2 K) := toPGL.range
  let : H.Normal := by
    dsimp [H, toPGL]
    rw [← pgl2_commutator_eq_psl2_range_of_card_gt_three K hK hcard]
    infer_instance
  let e : PSL2 K ≃* H := psl2EquivToPGLRange K
  intro a b hab
  have hconj :
      MulAut.conjNormal (H := H) a = MulAut.conjNormal (H := H) b := by
    apply (MulAut.congr e.symm).injective
    exact hab
  have hc : b⁻¹ * a ∈ Subgroup.centralizer (H : Set (PGL2 K)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxEq := congrArg Subtype.val
      (DFunLike.congr_fun hconj ⟨x, hx⟩)
    rw [MulAut.conjNormal_apply, MulAut.conjNormal_apply] at hxEq
    calc
      x * (b⁻¹ * a) = b⁻¹ * (b * x * b⁻¹) * a := by group
      _ = b⁻¹ * (a * x * a⁻¹) * a := by rw [hxEq]
      _ = (b⁻¹ * a) * x := by group
  have hC : Subgroup.centralizer (H : Set (PGL2 K)) = ⊥ :=
    pgl2_psl2Range_centralizer_eq_bot K hK
  rw [hC] at hc
  have hc1 : b⁻¹ * a = 1 := Subgroup.mem_bot.mp hc
  have := congrArg (fun z => b * z) hc1
  simpa using this

end CFSG.GorensteinWalter

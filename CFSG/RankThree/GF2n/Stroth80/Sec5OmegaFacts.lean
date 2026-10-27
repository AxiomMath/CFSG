module

public import CFSG.RankThree.GF2n.Stroth80.Sec51Sp
public import CFSG.ClassicalGroups.Orthogonal.RootGroupSwap

public section

namespace CFSG.ClassicalGroups.Orthogonal

open CFSG.Open CFSG.ClassicalGroups.F2Fixed QuadraticMap
open scoped Matrix

section OrthMatrix

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
  {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}

theorem exists_perp_vector_map_ne_zero (hQ : (polarBilin Q').Nondegenerate)
    (h3 : 3 ≤ Module.finrank K (ι → K)) {u : ι → K} (hu0 : u ≠ 0) :
    ∃ w : ι → K, polar Q' u w = 0 ∧ Q' w ≠ 0 := by
  obtain ⟨s, w₀, hs, hw₀, hsw⟩ := exists_perp_pair_polar_ne_zero hQ h3 hu0
  by_cases hs0 : Q' s = 0
  · by_cases hw0 : Q' w₀ = 0
    · refine ⟨s + w₀, by rw [polar_add_right, hs, hw₀, add_zero], fun h => hsw ?_⟩
      have h1 := QuadraticMap.map_add Q' s w₀
      rw [h, hs0, hw0] at h1
      simpa using h1.symm
    · exact ⟨w₀, hw₀, hw0⟩
  · exact ⟨s, hs, hs0⟩

theorem ElemMatrixIso.card_LomGL [Finite K] (E : ElemMatrixIso Q' X)
    (hQ : (polarBilin Q').Nondegenerate) {u : ι → K} (hu : Q' u = 0) (hu0 : u ≠ 0) :
    Nat.card (E.LomGL u) = Nat.card K ^ (Module.finrank K (ι → K) - 2) := by
  have hL : Nat.card (E.LomGL u) = Nat.card (Lom Q' u) := by
    unfold ElemMatrixIso.LomGL matrixOf
    rw [Subgroup.card_subtype, Subgroup.comap_equiv_eq_map_symm']
    exact Subgroup.card_map_of_injective (f := E.equiv.symm.toMonoidHom) E.equiv.symm.injective
  have hle := rootGroup_le_elementaryGroup Q' u
  have h1 := Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv
  rw [card_rootGroup hQ hu hu0] at h1
  rw [hL]
  exact h1

theorem ElemMatrixIso.exists_eichler_LomGL (E : ElemMatrixIso Q' X)
    (hQ : (polarBilin Q').Nondegenerate) (h3 : 3 ≤ Module.finrank K (ι → K)) {u : ι → K}
    (hu : Q' u = 0) (hu0 : u ≠ 0) :
    ∃ A ∈ E.LomGL u, ∃ w : ι → K, polar Q' u w = 0 ∧ Q' w ≠ 0 ∧ ∀ x : ι → K,
      (A : Matrix ι ι K) *ᵥ x =
        x + polar Q' x u • w - (polar Q' x w + Q' w * polar Q' x u) • u := by
  obtain ⟨w, hw, hQw⟩ := exists_perp_vector_map_ne_zero hQ h3 hu0
  set g : Gom Q' := eichlerG Q' u w with hg
  set A : X := E.equiv.symm g with hA
  refine ⟨(A : GL ι K), ?_, w, hw, hQw, fun x => ?_⟩
  · unfold ElemMatrixIso.LomGL matrixOf
    refine ⟨A, ?_, rfl⟩
    show E.equiv A ∈ Lom Q' u
    rw [hA, MulEquiv.apply_symm_apply]
    exact mem_Lom.mpr (eichler_mem_rootGroup hw)
  · have h1 := E.app A x
    rw [hA, MulEquiv.apply_symm_apply, hg, eichlerG_app hu hw] at h1
    exact h1.symm

end OrthMatrix

section OrthFacts

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι]
  {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}

theorem ElemMatrixIso.quad_mulVec (E : ElemMatrixIso Q' X) {A : GL ι K} (hA : A ∈ X)
    (x : ι → K) : Q' ((A : Matrix ι ι K) *ᵥ x) = Q' x := by
  have h := Gom.map_of_mem (E.equiv ⟨A, hA⟩) x
  rwa [E.app ⟨A, hA⟩ x] at h

theorem ElemMatrixIso.polar_mulVec (E : ElemMatrixIso Q' X) {A : GL ι K} (hA : A ∈ X)
    (x y : ι → K) :
    polar Q' ((A : Matrix ι ι K) *ᵥ x) ((A : Matrix ι ι K) *ᵥ y) = polar Q' x y := by
  have h := Gom.polar_app (E.equiv ⟨A, hA⟩) x y
  rwa [E.app ⟨A, hA⟩ x, E.app ⟨A, hA⟩ y] at h

theorem ElemMatrixIso.polar_conj_mulVec (E : ElemMatrixIso Q' X) {g A : GL ι K} (hg : g ∈ X)
    (u : ι → K) :
    polar Q' u (((g⁻¹ * A * g : GL ι K) : Matrix ι ι K) *ᵥ u) =
      polar Q' ((g : Matrix ι ι K) *ᵥ u) ((A : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ u)) := by
  have hinv := E.polar_mulVec hg
  have hgg : (g : Matrix ι ι K) * ((g⁻¹ : GL ι K) : Matrix ι ι K) = 1 := by
    rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  set w := (A : Matrix ι ι K) *ᵥ ((g : Matrix ι ι K) *ᵥ u) with hw
  have e : ((g⁻¹ * A * g : GL ι K) : Matrix ι ι K) *ᵥ u =
      ((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w := by
    simp only [Units.val_mul, hw, Matrix.mulVec_mulVec, mul_assoc]
  have h1 : (g : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w) = w := by
    rw [Matrix.mulVec_mulVec, hgg, Matrix.one_mulVec]
  rw [e]
  calc polar Q' u (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w)
      = polar Q' ((g : Matrix ι ι K) *ᵥ u)
        ((g : Matrix ι ι K) *ᵥ (((g⁻¹ : GL ι K) : Matrix ι ι K) *ᵥ w)) := (hinv u _).symm
    _ = polar Q' ((g : Matrix ι ι K) *ᵥ u) w := by rw [h1]

theorem ElemMatrixIso.LomGL_mulVec_self (E : ElemMatrixIso Q' X)
    (hQ : (polarBilin Q').Nondegenerate) {u : ι → K} (hu : Q' u = 0) (hu0 : u ≠ 0)
    {A : GL ι K} (hA : A ∈ E.LomGL u) : (A : Matrix ι ι K) *ᵥ u = u :=
  ((E.mem_LomGL_iff_flag hQ hu hu0).mp hA).2.1

end OrthFacts

end CFSG.ClassicalGroups.Orthogonal

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.ClassicalGroups.F2Fixed
open QuadraticMap
open scoped commutatorElement Matrix



variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def NatSingular (hc : Ctx M Q Z B) (t : G) {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] (Q' : QuadraticForm K (ι → K)) (X : Subgroup (GL ι K)) : Prop :=
  ∀ (φ : ↥(Rt M (LB M Q B) t) →* GL ι K), φ.range = X →
    φ.ker = (hc.CN t).subgroupOf (Rt M (LB M Q B) t) →
    ∀ [(Z.subgroupOf (Vt M (LB M Q B) B Z t)).Normal]
      (ψ : ↥(Vt M (LB M Q B) B Z t) ⧸ Z.subgroupOf (Vt M (LB M Q B) B Z t) ≃*
        Multiplicative (ι → K)),
      (∀ (s : ↥(Rt M (LB M Q B) t)) (v w : ↥(Vt M (LB M Q B) B Z t)),
        (w : G) = (s : G) * v * (s : G)⁻¹ →
        Multiplicative.toAdd (ψ (QuotientGroup.mk w)) =
          (φ s : Matrix ι ι K) *ᵥ Multiplicative.toAdd (ψ (QuotientGroup.mk v))) →
      ∀ b : ↥(Vt M (LB M Q B) B Z t), (b : G) ∈ B → Q' (secVec ψ b) = 0


variable {K : Type} [Field K]

theorem not_slNat_of_orth (hc : Ctx M Q Z B) {t : G} (hsl : SLNat hc t) [Finite K]
    (hK : Nat.card K = Nat.card Z) {ι : Type} [Fintype ι] [DecidableEq ι]
    {Q' : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)} (E : ElemMatrixIso Q' X)
    (hQ : (polarBilin Q').Nondegenerate)
    (hnat : NaturalRep (ι := ι) K X (Rt M (LB M Q B) t) (Vt M (LB M Q B) B Z t) Z (hc.CN t))
    (hι : 3 ≤ Fintype.card ι) : False := by
  obtain ⟨i⟩ : Nonempty ι := Fintype.card_pos_iff.mp (by omega)
  have hu0 : (Pi.single i (1 : K) : ι → K) ≠ 0 := fun h => by
    have := congrFun h i
    simp at this
  obtain ⟨y, hy⟩ : ∃ y, polar Q' (Pi.single i (1 : K)) y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (hQ.1 _ fun y => by rw [polarBilin_apply_apply]; exact hcon y)
  refine not_slNat_of_form hc hsl hK hnat hι (bilinAddHom (polarBilin Q'))
    (fun g hg x y => ?_) ⟨Pi.single i (1 : K), y, ?_⟩
  · rw [bilinAddHom_apply, bilinAddHom_apply, polarBilin_apply_apply, polarBilin_apply_apply]
    exact E.polar_mulVec hg x y
  · rw [bilinAddHom_apply, polarBilin_apply_apply]
    exact hy

end CFSG.RankThree.GF2n.Stroth80

module

public import CFSG.Quasithin.Vol2.Ch11SecA11Concl
public import CFSG.Quasithin.Background.A3Structure312Iso
public import CFSG.CharacterTheory.Wreathed.TwoCommutingComponentCoverConjugation
import CFSG.GroupTheory.Fitting.MulEquiv

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecA

open scoped Matrix

variable {X Y : Type} [Group X] [Group Y]

theorem fittingSubgroup_map_mulEquiv' (e : X ≃* Y) :
    (CFSG.fittingSubgroup X).map (e : X →* Y) = CFSG.fittingSubgroup Y :=
  CFSG.WholeGroup.fittingSubgroup_map_mulEquiv e

theorem generalizedFitting_map_mulEquiv' (e : X ≃* Y) :
    (CFSG.generalizedFitting X).map (e : X →* Y) = CFSG.generalizedFitting Y :=
  CFSG.Wreathed.TwoCommutingComponentCover.generalizedFitting_map_equiv e

theorem pCore_map_mulEquiv' (p : ℕ) (e : X ≃* Y) :
    (CFSG.pCore p X).map (e : X →* Y) = CFSG.pCore p Y := by
  have := CFSG.LieType.BorelTits.map_pCore_mulEquiv p e
  assumption

@[expose] noncomputable def mapEquivOfEq (e : X ≃* Y) {A : Subgroup X} {B : Subgroup Y}
    (h : A.map (e : X →* Y) = B) : ↥A ≃* ↥B :=
  (e.subgroupMap A).trans (MulEquiv.subgroupCongr h)

theorem mapEquivOfEq_coe (e : X ≃* Y) {A : Subgroup X} {B : Subgroup Y}
    (h : A.map (e : X →* Y) = B) (a : ↥A) : ((mapEquivOfEq e h a : ↥B) : Y) = e a :=
  rfl

theorem mapEquivOfEq_symm_coe (e : X ≃* Y) {A : Subgroup X} {B : Subgroup Y}
    (h : A.map (e : X →* Y) = B) (b : ↥B) : (((mapEquivOfEq e h).symm b : ↥A) : X) = e.symm b := by
  apply e.injective
  rw [MulEquiv.apply_symm_apply, ← mapEquivOfEq_coe e h, MulEquiv.apply_symm_apply]

theorem isExtraspecial_of_mulEquiv {p : ℕ} (e : X ≃* Y) (h : CFSG.IsExtraspecial p X) :
    CFSG.IsExtraspecial p Y := by
  have hcen : (Subgroup.center X).map (e : X →* Y) = Subgroup.center Y := Subgroup.map_center_eq e
  let e' : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y := QuotientGroup.congr _ _ e hcen
  refine
    { center_order_p := ?_
      quotient_elementary_abelian := ?_
      quotient_nontrivial := ?_ }
  · rw [← hcen, Subgroup.card_map_of_injective e.injective]
    exact h.center_order_p
  · exact isElementaryAbelian_of_mulEquiv' e' h.quotient_elementary_abelian
  · have := h.quotient_nontrivial
    exact e'.toEquiv.symm.nontrivial

theorem IsPOnePlusTwo.of_mulEquiv {p : ℕ} (e : X ≃* Y) (h : IsPOnePlusTwo p X) :
    IsPOnePlusTwo p Y := by
  obtain ⟨hX, hc, hp⟩ := h
  refine ⟨isExtraspecial_of_mulEquiv e hX, by rw [← Nat.card_congr e.toEquiv, hc], fun y => ?_⟩
  obtain ⟨x, rfl⟩ := e.surjective y
  rw [← map_pow, hp x, map_one]

theorem NaturalSL2Action.of_mulEquiv {p : ℕ} (e : X ≃* Y) {F : Subgroup X} {F' : Subgroup Y}
    [F.Normal] [F'.Normal] (hF : F.map (e : X →* Y) = F') (h : NaturalSL2Action p X F) :
    NaturalSL2Action p Y F' := by
  obtain ⟨e₁, ψ, hψ, hker, hconj⟩ := h
  set eF := mapEquivOfEq e hF
  refine ⟨eF.symm.trans e₁, ψ.comp (e.symm : Y →* X), hψ.comp e.symm.surjective, ?_, ?_⟩
  · ext y
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hker, ← hF]
    constructor
    · intro hy
      exact ⟨e.symm y, hy, by simp⟩
    · rintro ⟨x, hx, rfl⟩
      simpa using hx
  · intro y f
    have h1 : eF.symm (MulAut.conjNormal y f) = MulAut.conjNormal (e.symm y) (eF.symm f) := by
      apply Subtype.ext
      rw [mapEquivOfEq_symm_coe, MulAut.conjNormal_apply, MulAut.conjNormal_apply,
        mapEquivOfEq_symm_coe, map_mul, map_mul, map_inv]
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, h1, hconj]
    rfl

theorem A36Case4.of_mulEquiv' (e : X ≃* Y) (h : A36Case4 X) : A36Case4 Y := by
  obtain ⟨hFF, hnil, hSL, hp⟩ := h
  have hF := fittingSubgroup_map_mulEquiv' e
  refine ⟨?_, (Group.isNilpotent_congr (mapEquivOfEq e hF)).mp hnil,
    IsSL2.of_mulEquiv (QuotientGroup.congr _ _ e hF) hSL, fun q hq hqd => ?_⟩
  · rw [← generalizedFitting_map_mulEquiv' e, hFF, hF]
  · rw [← Nat.card_congr (mapEquivOfEq e hF).toEquiv] at hqd
    obtain ⟨h5, h12⟩ := hp q hq hqd
    have eq : ↥(CFSG.pCore q X) ≃* ↥(CFSG.pCore q Y) := mapEquivOfEq e (pCore_map_mulEquiv' q e)
    exact ⟨h5, h12.imp (IsPOnePlusTwo.of_mulEquiv eq) (IsHomocyclicRank2.of_mulEquiv eq)⟩

theorem List11_1_1Two.of_mulEquiv {n : ℕ} (e : X ≃* Y) (h : List11_1_1Two X n) :
    List11_1_1Two Y n := by
  rcases h with h | h | h | h | h | h | ⟨h3, h⟩
  · exact Or.inl (IsSL3.of_mulEquiv e h)
  · exact Or.inr (Or.inl (IsPSL.of_mulEquiv e h))
  · exact Or.inr (Or.inr (Or.inl (IsPSp4.of_mulEquiv e h)))
  · exact Or.inr (Or.inr (Or.inr (Or.inl (IsG2.of_mulEquiv e h))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Is2F4.of_mulEquiv e h)))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (Is3D4.of_mulEquiv e h))))))
  · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr ⟨h3, Is3D4.of_mulEquiv e h⟩)))))

theorem List11_1_1Three.of_mulEquiv (e : X ≃* Y) (h : List11_1_1Three X) :
    List11_1_1Three Y := by
  rcases h with h | h | ⟨p, hp, h5, h8, h⟩ | h | ⟨s, h | h⟩ | h | h | h | h | h | h | h | h | h |
    ⟨p, hp, h5, h8, hFF, hE, hN⟩
  · exact three_alt7 (IsAlt.of_mulEquiv e h)
  · exact three_hat7 (IsHat.of_mulEquiv e h)
  · exact three_psl2p hp h5 h8 (IsPSL.of_mulEquiv e h)
  · exact three_psl225 (IsPSL.of_mulEquiv e h)
  · exact three_sl35 (s := s) (Or.inl (IsSLEps3.of_mulEquiv e h))
  · exact three_sl35 (s := s) (Or.inr (IsPSLEps3.of_mulEquiv e h))
  · exact three_M22 (IsSporadic.of_mulEquiv e h)
  · exact three_hatM22 (IsHat.of_mulEquiv e h)
  · exact three_M23 (IsSporadic.of_mulEquiv e h)
  · exact three_J1 (IsSporadic.of_mulEquiv e h)
  · exact three_J2 (IsSporadic.of_mulEquiv e h)
  · exact three_J4 (IsSporadic.of_mulEquiv e h)
  · exact three_HS (IsSporadic.of_mulEquiv e h)
  · exact three_Ru (IsSporadic.of_mulEquiv e h)
  · exact three_case4 (A36Case4.of_mulEquiv' e h)
  · have hF := fittingSubgroup_map_mulEquiv' e
    iterate 14 right
    refine ⟨p, hp, h5, h8, ?_, IsElemAbelianOfRank.of_mulEquiv (mapEquivOfEq e hF) hE,
      NaturalSL2Action.of_mulEquiv e hF hN⟩
    rw [← generalizedFitting_map_mulEquiv' e, hFF, hF]

theorem Concl1111.of_mulEquiv {n : ℕ} (e : X ≃* Y) (h : Concl1111 X n) : Concl1111 Y n :=
  h.imp (List11_1_1Two.of_mulEquiv e) (And.imp_right (List11_1_1Three.of_mulEquiv e))

end CFSG.Quasithin.Vol2.Ch11.SecA

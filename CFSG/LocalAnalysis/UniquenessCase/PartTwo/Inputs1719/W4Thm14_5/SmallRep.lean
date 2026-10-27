module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront05
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerBin
import CFSG.Quasithin.Background.SmithB42L2Sl2
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesTensor
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsModule
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 Subgroup
open CFSG.QuasithinUnique.Setup.Layer CFSG.RankThree.FFModules

variable {I : Type} [CommGroup I] {W : Type} [AddCommGroup W] [Module (ZMod 2) W]

@[expose] def subRep (θ : I ≃* Multiplicative W) (X : Subgroup (MulAut I)) :
    Representation (ZMod 2) ↥X W where
  toFun x := (binPsi θ (x : MulAut I)).toLinearMap
  map_one' := by
    apply LinearMap.ext
    intro w
    simp
  map_mul' x y := by
    apply LinearMap.ext
    intro w
    simp

theorem subRep_apply (θ : I ≃* Multiplicative W) (X : Subgroup (MulAut I)) (x : ↥X) (w : W) :
    subRep θ X x w = binPsi θ (x : MulAut I) w := rfl

theorem subRep_toAdd (θ : I ≃* Multiplicative W) (X : Subgroup (MulAut I)) (x : ↥X) (v : I) :
    subRep θ X x (Multiplicative.toAdd (θ v)) = Multiplicative.toAdd (θ ((x : MulAut I) v)) :=
  B42L2.toAdd_binPsi θ _ v

theorem subRep_injective (θ : I ≃* Multiplicative W) (X : Subgroup (MulAut I)) :
    Function.Injective (subRep θ X) := by
  intro x y hxy
  apply Subtype.ext
  apply (binPsi θ).injective
  apply LinearEquiv.ext
  intro w
  exact congrArg (fun f : Module.End (ZMod 2) W => f w) hxy

theorem subRep_isIrreducible (θ : I ≃* Multiplicative W) {X L : Subgroup (MulAut I)}
    (hLX : L ≤ X) (hirr : IsIrrOn L ⊤ ⊥) : (subRep θ X).IsIrreducible := by
  obtain ⟨hlt, -, -, hJ⟩ := hirr
  have hirrV : ∀ J : Subgroup I, (∀ l ∈ L, ∀ v ∈ J, l v ∈ J) → J = ⊥ ∨ J = ⊤ :=
    fun J hJL => hJ J hJL bot_le le_top
  have hntW : Nontrivial W := by
    obtain ⟨v, -, hv⟩ := SetLike.exists_of_lt hlt
    replace hv : v ≠ 1 := fun h => hv (h ▸ Subgroup.one_mem _)
    refine ⟨⟨Multiplicative.toAdd (θ v), 0, fun h => hv ?_⟩⟩
    have h1 : θ v = 1 := Multiplicative.toAdd.injective (by simpa using h)
    simpa using congrArg θ.symm h1
  rw [CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff]
  refine ⟨hntW, fun U hU => B42L2.irr_map θ hirrV U ?_⟩
  rintro _ ⟨l, hl, rfl⟩ u hu
  exact hU ⟨l, hLX hl⟩ u hu

theorem natCard_fixSub_subRep (θ : I ≃* Multiplicative W) (X : Subgroup (MulAut I))
    (A : Subgroup ↥X) :
    Nat.card (fixSub (subRep θ X) A) = Nat.card (fixV (A.map X.subtype)) := by
  refine (Nat.card_congr ?_).symm
  refine
    { toFun := fun v => ⟨Multiplicative.toAdd (θ v), fun a ha => ?_⟩
      invFun := fun w => ⟨θ.symm (Multiplicative.ofAdd w.1), fun b hb => ?_⟩
      left_inv := fun v => by
        apply Subtype.ext
        simp
      right_inv := fun w => by
        apply Subtype.ext
        simp }
  · rw [subRep_toAdd, v.2 (a : MulAut I) ⟨a, ha, rfl⟩]
  · obtain ⟨a, ha, rfl⟩ := hb
    have h := w.2 a ha
    rw [subRep_apply, binPsi_apply] at h
    apply θ.injective
    apply Multiplicative.toAdd.injective
    simpa using h

theorem finrank_quotient_fixSub_subRep [Finite I] (θ : I ≃* Multiplicative W)
    (X : Subgroup (MulAut I)) (A : Subgroup ↥X) :
    Module.finrank (ZMod 2) (W ⧸ fixSub (subRep θ X) A) = rkIdx (fixV (A.map X.subtype)) := by
  have : Finite W := Finite.of_equiv I (θ.toEquiv.trans Multiplicative.toAdd)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcardW : Nat.card W = Nat.card I :=
    Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd).symm
  set U := fixSub (subRep θ X) A
  have hU := natCard_fixSub_subRep θ X A
  have hq : Nat.card (W ⧸ U) * Nat.card U = Nat.card W := by
    rw [mul_comm, ← Submodule.card_eq_card_quotient_mul_card]
  have hi : Nat.card (fixV (A.map X.subtype)) * (fixV (A.map X.subtype)).index = Nat.card I :=
    Subgroup.card_mul_index _
  have hidx : (fixV (A.map X.subtype)).index = Nat.card (W ⧸ U) := by
    have hpos : 0 < Nat.card (fixV (A.map X.subtype)) := Nat.card_pos
    rw [← hU] at hi hpos
    exact Nat.eq_of_mul_eq_mul_left hpos (hi.trans (hcardW.symm.trans hq.symm |>.trans
      (mul_comm _ _)))
  have hpow : Nat.card (W ⧸ U) = 2 ^ Module.finrank (ZMod 2) (W ⧸ U) := by
    have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W ⧸ U)
    rwa [Nat.card_zmod] at this
  unfold rkIdx
  rw [hidx, hpow, padicValNat.prime_pow]

theorem mGV_subRep [Finite I] (θ : I ≃* Multiplicative W) (X : Subgroup (MulAut I)) :
    F05.mGV (subRep θ X) = E3.mParam X := by
  classical
  have : Finite W := Finite.of_equiv I (θ.toEquiv.trans Multiplicative.toAdd)
  unfold F05.mGV E3.mParam
  by_cases hev : Even (Nat.card ↥X)
  · rw [if_pos hev, if_pos hev]
    congr 1
    ext k
    constructor
    · rintro ⟨t, ht, rfl⟩
      refine ⟨(t : MulAut I), t.2, by rw [Subgroup.orderOf_coe]; exact ht, ?_⟩
      rw [finrank_quotient_fixSub_subRep, MonoidHom.map_zpowers]
      rfl
    · rintro ⟨t, htX, ht, rfl⟩
      refine ⟨⟨t, htX⟩, by rw [← Subgroup.orderOf_coe]; exact ht, ?_⟩
      rw [finrank_quotient_fixSub_subRep, MonoidHom.map_zpowers]
      rfl
  · rw [if_neg hev, if_neg hev]
    have hcardW : Nat.card W = Nat.card I :=
      Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd).symm
    have hpow : Nat.card W = 2 ^ Module.finrank (ZMod 2) W := by
      have := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := W)
      rwa [Nat.card_zmod] at this
    unfold rk
    rw [← hcardW, hpow, padicValNat.prime_pow]

theorem isComponentOf_subgroupOf {X L : Subgroup (MulAut I)} (hLX : L ≤ X)
    (hLn : (L.subgroupOf X).Normal) (hq : CFSG.Open.IsQuasisimple ↥L) :
    CFSG.Open.IsComponentOf (L.subgroupOf X) ⊤ := by
  refine ⟨le_top, CFSG.Open.IsSubnormal.step le_top
    ((Subgroup.normal_subgroupOf_iff le_top).mpr fun x k hx _ => hLn.conj_mem x hx k)
    (CFSG.Open.IsSubnormal.refl ⊤), ?_⟩
  exact CFSG.Open.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hLX) hq

theorem map_conj_subgroupOf_eq {X L : Subgroup (MulAut I)} (hLn : (L.subgroupOf X).Normal)
    (g : ↥X) : (L.subgroupOf X).map (MulAut.conj g).toMonoidHom = L.subgroupOf X := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact hLn.conj_mem z hz g
  · intro hy
    refine ⟨g⁻¹ * y * g, ?_, by group⟩
    have h := hLn.conj_mem y hy g⁻¹
    rwa [inv_inv] at h

theorem numConj_subgroupOf_eq_one {X L : Subgroup (MulAut I)} (hLn : (L.subgroupOf X).Normal) :
    F05.numConj (L.subgroupOf X) = 1 := by
  unfold F05.numConj
  have hset : {K : Subgroup ↥X | ∃ g : ↥X, K = (L.subgroupOf X).map (MulAut.conj g).toMonoidHom} =
      {L.subgroupOf X} := by
    ext K
    simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
    constructor
    · rintro ⟨g, rfl⟩
      exact map_conj_subgroupOf_eq hLn g
    · rintro rfl
      exact ⟨1, (map_conj_subgroupOf_eq hLn 1).symm⟩
  rw [hset, Set.ncard_singleton]

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

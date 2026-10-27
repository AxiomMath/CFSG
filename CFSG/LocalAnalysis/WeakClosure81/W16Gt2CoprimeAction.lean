module

public import CFSG.SignalizerFunctorTheorem.Quadratic.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
public import TauCeti.Algebra.GroupAction.TypeTags

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic

namespace NOne

theorem iSup_fixSub_zpowers_eq_top {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {O : Subgroup (LGL 2 W)} (hO : IsPGroup p O)
    (hab : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a) (hnc : ¬ IsCyclic ↥O) :
    (⨆ (a : LGL 2 W) (_ : a ∈ O ∧ a ≠ 1), fixSub (Subgroup.zpowers a)) = ⊤ := by
  classical
  letI : CommGroup ↥O :=
    { (inferInstance : Group ↥O) with
      mul_comm := fun a b => Subtype.ext (hab a a.2 b b.2) }
  letI : Fact (IsPGroup p ↥O) := ⟨hO⟩
  let ψ : ↥O →* MulAut (Multiplicative W) :=
    { toFun := fun a => AddEquiv.toMultiplicative (a : W ≃ₗ[ZMod 2] W).toAddEquiv
      map_one' := by
        ext w
        simp
      map_mul' := by
        intro a b
        ext w
        simp [LinearEquiv.mul_apply] }
  letI : MulDistribMulAction ↥O (Multiplicative W) :=
    MulDistribMulAction.compHom (Multiplicative W) ψ
  have hp2 : Nat.Coprime p 2 :=
    ((Fact.out : p.Prime).coprime_iff_not_dvd).2 fun h =>
      hp (le_antisymm (Nat.le_of_dvd (by norm_num) h) (Fact.out : p.Prime).two_le)
  have hcard : Nat.card (Multiplicative W) = 2 ^ Module.finrank (ZMod 2) W := by
    haveI : Fintype W := Fintype.ofFinite W
    have h1 : Nat.card (Multiplicative W) = Fintype.card W := by
      rw [Nat.card_eq_fintype_card, Fintype.card_multiplicative]
    rw [h1, Module.card_eq_pow_finrank (K := ZMod 2) (V := W), ZMod.card]
  have hG : Nat.Coprime p (Nat.card (Multiplicative W)) := by
    rw [hcard]
    exact hp2.pow_right _
  have hgen := CFSG.iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := Multiplicative W) (A := ↥O) p hG hnc
  let T : Submodule (ZMod 2) W :=
    ⨆ (a : LGL 2 W) (_ : a ∈ O ∧ a ≠ 1), fixSub (Subgroup.zpowers a)
  change T = ⊤
  rw [Submodule.eq_top_iff']
  intro w
  have hmem : (Multiplicative.ofAdd w) ∈
      (⨆ (b : ↥O) (_ : b ≠ 1),
        CFSG.fixedPointSubgroup (↥(Subgroup.zpowers b)) (Multiplicative W)) := by
    rw [hgen]
    exact Subgroup.mem_top _
  have hle : (⨆ (b : ↥O) (_ : b ≠ 1),
        CFSG.fixedPointSubgroup (↥(Subgroup.zpowers b)) (Multiplicative W)) ≤
      T.toAddSubgroup.toSubgroup := by
    refine iSup₂_le fun b hb => ?_
    intro x hx
    rw [FixedPoints.mem_subgroup] at hx
    rw [Multiplicative.mem_toSubgroup, Submodule.mem_toAddSubgroup]
    refine Submodule.mem_iSup_of_mem (b : LGL 2 W) ?_
    refine Submodule.mem_iSup_of_mem ⟨b.2, ?_⟩ ?_
    · intro h
      exact hb (Subtype.ext h)
    · intro c hc
      have hc' : c ∈ (Subgroup.zpowers b).map O.subtype := by
        rw [MonoidHom.map_zpowers]
        exact hc
      obtain ⟨z, hz, hzc⟩ := Subgroup.mem_map.mp hc'
      have hzx : z • x = x := hx ⟨z, hz⟩
      have hzx' : z • (Multiplicative.toAdd x) = Multiplicative.toAdd x := by
        have h := congrArg Multiplicative.toAdd hzx
        simpa using h
      rw [← hzc]
      exact hzx'
  have hwT : (Multiplicative.ofAdd w) ∈ T.toAddSubgroup.toSubgroup := hle hmem
  rw [Multiplicative.mem_toSubgroup, Submodule.mem_toAddSubgroup] at hwT
  simpa using hwT

theorem eq_one_of_noncyclic_inverted {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]
    {p : ℕ} [Fact p.Prime] (hp : p ≠ 2) {O : Subgroup (LGL 2 W)} (hO : IsPGroup p O)
    (hab : ∀ a ∈ O, ∀ b ∈ O, a * b = b * a) (hnc : ¬ IsCyclic ↥O) {t : LGL 2 W}
    (hinv : ∀ a ∈ O, t * a * t⁻¹ = a⁻¹) {X : Submodule (ZMod 2) W}
    (hX : ∀ w : W, t w - w ∈ X)
    (hfix : ∀ a ∈ O, a ≠ 1 → ∀ w ∈ X, a w = w → w = 0) : t = 1 := by
  have hker : (⨆ (a : LGL 2 W) (_ : a ∈ O ∧ a ≠ 1), fixSub (Subgroup.zpowers a)) ≤
      LinearMap.ker ((t : W →ₗ[ZMod 2] W) - LinearMap.id) := by
    refine iSup₂_le fun a ha => ?_
    intro v hv
    have haO : a ∈ O := ha.1
    have ha1 : a ≠ 1 := ha.2
    have hva : a v = v := hv a (Subgroup.mem_zpowers a)
    have hmul : t * a = a⁻¹ * t := by
      calc t * a = t * a * t⁻¹ * t := by group
        _ = a⁻¹ * t := by rw [hinv a haO]
    have h1 : t (a v) = a⁻¹ (t v) := by
      have h := congrArg (fun e : LGL 2 W => e v) hmul
      simpa [LinearEquiv.mul_apply] using h
    rw [hva] at h1
    have h2 : a (t v) = t v := by
      have h := congrArg (fun x : W => a x) h1
      simpa using h
    have haX : a (t v - v) = t v - v := by
      simpa [h2, hva] using LinearMap.map_sub (a : W →ₗ[ZMod 2] W) (t v) v
    have hzero : t v - v = 0 := hfix a haO ha1 (t v - v) (hX v) haX
    rw [LinearMap.mem_ker]
    simpa using hzero
  have hfix_all : ∀ v : W, t v = v := by
    intro v
    have hv : v ∈ (⨆ (a : LGL 2 W) (_ : a ∈ O ∧ a ≠ 1), fixSub (Subgroup.zpowers a)) := by
      rw [iSup_fixSub_zpowers_eq_top hp hO hab hnc]
      exact Submodule.mem_top
    have hkv := hker hv
    rw [LinearMap.mem_ker] at hkv
    have hv' : t v - v = 0 := by simpa using hkv
    simpa using sub_eq_zero.mp hv'
  ext v
  simpa using hfix_all v

end NOne

end CFSG.LocalAnalysis.WeakClosure81

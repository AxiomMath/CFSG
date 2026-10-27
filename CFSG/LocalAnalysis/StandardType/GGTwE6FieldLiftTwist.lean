module

public import CFSG.LieType.Chevalley.GraphFixedBruhatEquivariance
public import CFSG.RankThree.Chevalley.SteinbergCEF4EvenQPlusWeyl
public import CFSG.LieType.Chevalley.C2E6SubsystemBruhat
public import CFSG.LieType.Chevalley.SignKernelComponentBruhat
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.TwE6FieldCore

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {L : Type} [Field L]

theorem twistHom_comp_eq (σ τ : L →+* L) (g : ModGL TwistTag.E6.tag L) :
    twistHom TwistTag.E6 L (σ.comp τ) g =
      twistHom TwistTag.E6 L σ (Units.map (entrywiseHom τ) g) := by
  rw [twistHom_apply, twistHom_apply, units_map_entrywiseHom_comp]

theorem ringHom_pow_apply_eq_pow {Fr : L →+* L} {q : ℕ} (hFr : ∀ c, Fr c = c ^ q) (n : ℕ)
    (c : L) : (Fr ^ n) c = c ^ q ^ n := by
  induction n generalizing c with
  | zero => simp
  | succ n ih =>
    rw [pow_succ Fr n, RingHom.coe_mul, Function.comp_apply, ih, hFr, ← pow_mul, ← pow_succ']

section Certs


theorem twistHom_twistHom_eq_entrywise (σ τ : L →+* L) (g : ModGL TwistTag.E6.tag L) :
    twistHom TwistTag.E6 L σ (twistHom TwistTag.E6 L τ g) =
      Units.map (entrywiseHom (σ.comp τ)) g := by
  rw [twistHom_apply, twistHom_apply, map_mul, map_mul, map_inv,
    units_map_entrywiseHom_diagramMap, units_map_entrywiseHom_comp]
  have hP2 : diagramMap TwistTag.E6 L * diagramMap TwistTag.E6 L = 1 := by
    have h := diagramMap_pow_order TwistTag.E6 L
    rwa [show TwistTag.E6.order = 2 from rfl, pow_two] at h
  calc diagramMap TwistTag.E6 L * (diagramMap TwistTag.E6 L *
        Units.map (entrywiseHom (σ.comp τ)) g * (diagramMap TwistTag.E6 L)⁻¹) *
          (diagramMap TwistTag.E6 L)⁻¹ =
      (diagramMap TwistTag.E6 L * diagramMap TwistTag.E6 L) *
        Units.map (entrywiseHom (σ.comp τ)) g *
          (diagramMap TwistTag.E6 L * diagramMap TwistTag.E6 L)⁻¹ := by group
    _ = _ := by rw [hP2]; group

theorem exists_twistHom_pow_odd [CharP L 2] (Fr : L →+* L) {g0 : ModGL TwistTag.E6.tag L}
    {v : WeylGroup TwistTag.E6.tag}
    (hg0 : twistHom TwistTag.E6 L Fr g0 = g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L v)
    (k : ℕ) : ∃ w : WeylGroup TwistTag.E6.tag, twistHom TwistTag.E6 L (Fr ^ (2 * k + 1)) g0 =
      g0 * canonicalRep (coxeterSystem TwistTag.E6.tag) L w := by
  induction k with
  | zero => exact ⟨v, by rw [Nat.mul_zero, Nat.zero_add, pow_one, hg0]⟩
  | succ k ih =>
    obtain ⟨w, hw⟩ := ih
    refine ⟨w * weylTwist TwistTag.E6 v * weylTwist TwistTag.E6 (weylTwist TwistTag.E6 v), ?_⟩
    have hpow : Fr ^ (2 * (k + 1) + 1) = (Fr ^ (2 * k + 1)).comp (Fr.comp Fr) := by
      rw [show 2 * (k + 1) + 1 = 2 * k + 1 + 1 + 1 by ring, pow_succ, pow_succ, mul_assoc]
      rfl
    rw [hpow, twistHom_comp_eq, ← twistHom_twistHom_eq_entrywise, hg0, map_mul, hg0,
      twistHom_canonicalRep, map_mul, map_mul, hw, twistHom_canonicalRep, twistHom_canonicalRep,
      CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo,
      CFSG.RankThree.Chevalley.EvenF4QPlus.canonicalRep_mul_of_charTwo]
    simp only [mul_assoc]

end Certs

end CFSG.StandardType.TwE6FieldCore

end

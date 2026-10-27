module

public import CFSG.Quasithin.MS93.S36SpECrd
public import CFSG.Quasithin.MS93.S33LamQ

public section

namespace CFSG.Quasithin.MS93.S512N

open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open CFSG.Quasithin.MS93.S36E
open scoped Matrix

variable {S : Type} [CommGroup S]

theorem mem_fixSp_zpowers {F : Type} [Field F] {g : MSP.Sp4 F} {v : MSP.V4 F} :
    v ∈ MSP.fixSp (Subgroup.zpowers g) ↔ MSP.mat g *ᵥ v = v := by
  refine ⟨fun h => (MSP.mem_fixSp.1 h) g (Subgroup.mem_zpowers g), fun h => ?_⟩
  have hle : Subgroup.zpowers g ≤ MSP.fixer (F ∙ v) := by
    rw [Subgroup.zpowers_le, MSP.mem_fixer]
    intro w hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hw
    rw [Matrix.mulVec_smul, h]
  exact (MSP.le_fixer_iff.1 hle) (Submodule.mem_span_singleton_self v)

theorem mem_fixV_zpowers' {x : MulAut S} {s : S} : s ∈ fixV (Subgroup.zpowers x) ↔ x s = s :=
  CFSG.Quasithin.mem_fixV_zpowers_iff_apply

theorem card_fixV_zpowers_eq {F : Type} [Field F] (θ : S ≃* Multiplicative (MSP.V4 F))
    {x : MulAut S} {g : MSP.Sp4 F}
    (hθ : ∀ s : S, Multiplicative.toAdd (θ (x s)) = MSP.mat g *ᵥ Multiplicative.toAdd (θ s)) :
    Nat.card (fixV (Subgroup.zpowers x)) = Nat.card (MSP.fixSp (Subgroup.zpowers g)) := by
  have hiff : ∀ s : S, s ∈ fixV (Subgroup.zpowers x) ↔
      Multiplicative.toAdd (θ s) ∈ MSP.fixSp (Subgroup.zpowers g) := by
    intro s
    rw [mem_fixV_zpowers', mem_fixSp_zpowers, ← hθ]
    constructor
    · intro h
      rw [h]
    · intro h
      exact θ.injective (Multiplicative.toAdd.injective h)
  exact Nat.card_congr
    { toFun := fun s => ⟨Multiplicative.toAdd (θ s), (hiff s).1 s.2⟩
      invFun := fun v => ⟨θ.symm (Multiplicative.ofAdd v), (hiff _).2 (by simp)⟩
      left_inv := fun s => Subtype.ext (by simp)
      right_inv := fun v => Subtype.ext (by simp) }

theorem finrank_fixSp_le_two_of_mem_commutator {K : Type} [Field K] [Finite K]
    (c : ZMod 2 ≃+* K) {g : MSP.Sp4 K} (hg : g ∈ commutator (MSP.Sp4 K)) (hg1 : g ≠ 1) :
    Module.finrank K (MSP.fixSp (Subgroup.zpowers g)) ≤ 2 := by
  have : CharP K 2 := MSP.charP_of_ringEquiv c
  have hq : Nat.card K = 2 := by rw [← Nat.card_congr c.toEquiv, Nat.card_zmod]
  by_contra hlt
  push Not at hlt
  have hle4 : Module.finrank K (MSP.fixSp (Subgroup.zpowers g)) ≤ 4 := by
    have := Submodule.finrank_le (MSP.fixSp (Subgroup.zpowers g))
    simpa using this
  rcases (show Module.finrank K (MSP.fixSp (Subgroup.zpowers g)) = 3 ∨
      Module.finrank K (MSP.fixSp (Subgroup.zpowers g)) = 4 by omega) with h3 | h4
  · obtain ⟨p, hp, -, hEp⟩ := MSP.exists_point_of_finrank_fixSp_three h3
    obtain ⟨v, hv0, rfl⟩ := MSP.exists_eq_span_of_isPoint hp
    have hgx : g ∈ MSP.xPoint (K ∙ v) := hEp (Subgroup.mem_zpowers g)
    rcases S33.eq_one_or_eq_transv hq hv0 hgx with h1 | ht
    · exact hg1 h1
    · rw [ht] at hg
      exact MSP.transv_not_mem_commutator c hv0 hg
  · have htop : MSP.fixSp (Subgroup.zpowers g) = ⊤ :=
      Submodule.eq_top_of_finrank_eq (by rw [h4]; simp)
    have hbot := MSP.fixSp_eq_top_iff.1 htop
    exact hg1 (by
      have : g ∈ Subgroup.zpowers g := Subgroup.mem_zpowers g
      rw [hbot] at this
      exact this)

theorem four_mul_card_fixV_le_of_alt {K : Subgroup (MulAut S)}
    (hK : AlternatingNatural K ⊤ ⊥ 6) {x : MulAut S} (hxK : x ∈ K) (hx1 : x ≠ 1) :
    4 * Nat.card (fixV (Subgroup.zpowers x)) ≤ Nat.card S := by
  obtain ⟨π, hπ⟩ := hK
  obtain ⟨θ, hθ⟩ := exists_heartCoord hπ
  obtain ⟨σ₀, hσ⟩ := hπ.1 ⟨x, hxK⟩
  set σ : ↥(alternatingGroup (Fin 6)) := σ₀ with hσdef
  have hxσ : ((π σ : ↥K) : MulAut S) = x := congrArg Subtype.val hσ
  set g := S6B.thetaTwo (σ : Equiv.Perm (Fin 6)) with hg
  have hθx : ∀ s : S, Multiplicative.toAdd (θ (x s)) = MSP.mat g *ᵥ Multiplicative.toAdd (θ s) := by
    intro s
    rw [← hxσ]
    exact hθ σ s
  have hg1 : g ≠ 1 := by
    intro h1
    apply hx1
    have hσ1 : (σ : Equiv.Perm (Fin 6)) = 1 := by
      rw [← map_one S6B.thetaTwo] at h1
      exact S6B.thetaTwo.injective h1
    have hσ1' : σ = 1 := Subtype.ext hσ1
    have h0 : π σ₀ = 1 := by
      have : σ₀ = 1 := hσ1'
      rw [this, map_one]
    rw [← hxσ]
    exact congrArg Subtype.val h0
  have hgD : g ∈ commutator (MSP.Sp4 (ZMod 2)) := by
    rw [MSP.mem_commutator_iff_sign (RingEquiv.refl (ZMod 2)), hg]
    show Equiv.Perm.sign ((B5FinSp.theta (RingEquiv.refl (ZMod 2))).symm
      (B5FinSp.theta (RingEquiv.refl (ZMod 2)) (σ : Equiv.Perm (Fin 6)))) = 1
    rw [MulEquiv.symm_apply_apply]
    exact Equiv.Perm.mem_alternatingGroup.1 σ.2
  have hd := finrank_fixSp_le_two_of_mem_commutator (RingEquiv.refl (ZMod 2)) hgD hg1
  have hcardS : Nat.card S = Nat.card (MSP.V4 (ZMod 2)) :=
    Nat.card_congr (θ.toEquiv.trans Multiplicative.toAdd)
  rw [card_fixV_zpowers_eq θ hθx, hcardS, MSP.card_V4, MSP.card_fixSp, Nat.card_zmod]
  calc 4 * 2 ^ Module.finrank (ZMod 2) (MSP.fixSp (Subgroup.zpowers g)) ≤ 4 * 2 ^ 2 :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by norm_num) hd)
    _ = 2 ^ 4 := by norm_num

end CFSG.Quasithin.MS93.S512N

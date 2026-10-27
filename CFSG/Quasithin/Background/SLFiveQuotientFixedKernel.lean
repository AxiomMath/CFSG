module

public import CFSG.Quasithin.Vol2.Ch12Sec2GlueL52
public import CFSG.Quasithin.Background.F918D0
public import CFSG.Quasithin.Background.E3Defs
public import CFSG.Quasithin.Background.B1MoreIrr
public import CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQSL2RootCommutator

public section

noncomputable section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin

open CFSG.Quasithin.H13.L52
open CFSG.Quasithin.JonesParshall
open CFSG.Quasithin.JonesParshall.Curtis

theorem fixV_eq_bot_of_sl5_rank_ten
    {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1)
    (H : Subgroup (MulAut W))
    (e : ↥H ≃* Matrix.SpecialLinearGroup (Fin 5) (ZMod 2))
    (hcomm : commSub (⊤ : Subgroup W) H = ⊤)
    (hirr : ∀ J : Subgroup W, fixV H ≤ J →
      (∀ h ∈ H, ∀ w ∈ J, h w ∈ J) → J = fixV H ∨ J = ⊤)
    (hdim : E3.mQuot (⊤ : Subgroup W) (fixV H) = 10) :
    fixV H = ⊥ := by
  classical
  let Γ := Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)
  let θ : Γ ≃* ↥H := e.symm
  let Q := Additive (W ⧸ fixV H)
  have hq : ∀ q : W ⧸ fixV H, q ^ 2 = 1 := fun q => by
    obtain ⟨v, rfl⟩ := QuotientGroup.mk_surjective q
    rw [← QuotientGroup.mk_pow, hW, QuotientGroup.mk_one]
  let : Module (ZMod 2) Q := modTwo (V := W ⧸ fixV H) hq
  let ρQ : Representation (ZMod 2) Γ Q := repOfEnd (muQ H θ)
  have hnt : fixV H ≠ ⊤ := by
    intro htop
    have h0 : E3.mQuot (⊤ : Subgroup W) (fixV H) = 0 := by
      rw [htop, E3.mQuot_self]
    omega
  have hsimple : IsSimpleRep ρQ := isSimpleRep_quot H θ hnt hirr
  have hρ : ρQ.IsIrreducible :=
    (CFSG.QuasithinUnique.Setup.SL2Modules.isIrreducible_iff ρQ).mpr hsimple
  have htop : IsPGroup 2 (⊤ : Subgroup W) := fun w => ⟨1, by
    exact Subtype.ext (hW (w : W))⟩
  have hrel : (fixV H).relIndex ⊤ = 2 ^ 10 := by
    rw [E3.relIndex_eq_two_pow htop (fixV H), hdim]
  have hcardquot : Nat.card (W ⧸ fixV H) = 2 ^ 10 :=
    calc Nat.card (W ⧸ fixV H) = (fixV H).index := (Subgroup.index_eq_card (fixV H)).symm
      _ = (fixV H).relIndex ⊤ := (Subgroup.relIndex_top_right (fixV H)).symm
      _ = 2 ^ 10 := hrel
  have hfin : Module.finrank (ZMod 2) Q = 10 := by
    have hpow := FiniteField.pow_finrank_eq_natCard 2 Q
    have h2 : 2 ^ Module.finrank (ZMod 2) Q = 2 ^ 10 := by
      rw [hpow]
      exact hcardquot
    exact Nat.pow_right_injective (by norm_num : 2 ≤ 2) h2
  have hdimdual : Module.finrank (ZMod 2) (Module.Dual (ZMod 2) Q) = 10 := by
    rw [Subspace.dual_finrank_eq, hfin]
  have : FiniteDimensional (ZMod 2) Q := Module.Finite.of_finite
  have hdual : (Representation.dual ρQ).IsIrreducible :=
    CFSG.LocalAnalysis.GorensteinLyons.SteinbergBQ.isIrreducible_dual ρQ hρ
  have hH1 : Module.finrank (ZMod 2) (H1 (Representation.dual ρQ)) = 0 :=
    CFSG.Quasithin.JonesParshall.Curtis.finrank_H1_irreducible_ten
      (Γ := Γ) (W := Module.Dual (ZMod 2) Q) (ρ := Representation.dual ρQ)
      (MulEquiv.refl Γ) hdual hdimdual
  let β : ↥(⊤ : Subgroup W) →* Multiplicative Q :=
    { toFun := fun v => Multiplicative.ofAdd (Additive.ofMul
        (QuotientGroup.mk (v : W) : W ⧸ fixV H))
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  have hβs : Function.Surjective β := by
    intro m
    obtain ⟨x, hx⟩ := QuotientGroup.mk_surjective
      (Additive.toMul (Multiplicative.toAdd m))
    refine ⟨⟨x, Subgroup.mem_top x⟩, ?_⟩
    show Multiplicative.ofAdd (Additive.ofMul
      (QuotientGroup.mk x : W ⧸ fixV H)) = m
    rw [hx, ofMul_toMul, ofAdd_toAdd]
  have hβk : ∀ v : ↥(⊤ : Subgroup W), β v = 1 ↔ (v : W) ∈ fixV H := by
    intro v
    show (QuotientGroup.mk (v : W) : W ⧸ fixV H) = 1 ↔ (v : W) ∈ fixV H
    exact QuotientGroup.eq_one_iff (v : W)
  have hβe : ∀ (γ : Γ) (v : ↥(⊤ : Subgroup W))
      (hv : (θ.toMonoidHom γ : MulAut W) (v : W) ∈ (⊤ : Subgroup W)),
      β ⟨(θ.toMonoidHom γ : MulAut W) (v : W), hv⟩ =
        Multiplicative.ofAdd (ρQ γ (Multiplicative.toAdd (β v))) := by
    intro γ v hv
    have hρQ : ρQ γ (Additive.ofMul
        (QuotientGroup.mk (v : W) : W ⧸ fixV H)) =
        muQ H θ γ (Additive.ofMul
          (QuotientGroup.mk (v : W) : W ⧸ fixV H)) := rfl
    show Multiplicative.ofAdd (Additive.ofMul
        (QuotientGroup.mk (((θ γ : ↥H) : MulAut W) (v : W)) : W ⧸ fixV H)) =
      Multiplicative.ofAdd (ρQ γ (Additive.ofMul
        (QuotientGroup.mk (v : W) : W ⧸ fixV H)))
    rw [hρQ, muQ_mk]
  have hcard := card_le_pow_finrank_H1_dual (W := W) (Γ := Γ) hW H ⊤ (fixV H) le_top
    (fun z hz x hx => hz x hx)
    (fun x hx v hv => Subgroup.mem_top _)
    (by rw [commOf_eq_commSub, hcomm])
    θ.toMonoidHom θ.surjective ρQ β hβs hβk hβe
  have hcard1 : Nat.card ↥(fixV H) = 1 := by
    rw [hH1, pow_zero] at hcard
    exact le_antisymm hcard Nat.card_pos
  exact Subgroup.card_eq_one.mp hcard1

end CFSG.Quasithin

module

public import CFSG.LocalAnalysis.StandardType.GGTwE6ThreeRankFiveAmbient
public import CFSG.LocalAnalysis.StandardType.GGTwE6RecipeTransport
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.StandardType.NoOffTwE6Three

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.HardMathSupport.Lang.E6Descent
  CFSG.HardMathSupport.Timmesfeld.CrossChar CFSG.StandardType.TwE6RootKill CFSG.Open

theorem isPGroup_le_of_normal_of_relIndex_coprime {G : Type*} [Group G] {R C Q : Subgroup G}
    [Finite R] {p : ℕ} [Fact p.Prime] (hCR : C ≤ R) (hC : (C.subgroupOf R).Normal)
    (hQR : Q ≤ R) (hQ : IsPGroup p Q) (hcop : (C.relIndex R).Coprime p) : Q ≤ C := by
  intro x hxQ
  let C' : Subgroup R := C.subgroupOf R
  let Q' : Subgroup R := Q.subgroupOf R
  haveI : C'.Normal := hC
  have hxQ' : (⟨x, hQR hxQ⟩ : R) ∈ Q' := Subgroup.mem_subgroupOf.2 hxQ
  have hQ' : IsPGroup p Q' := hQ.comap_subtype
  let f : R →* R ⧸ C' := QuotientGroup.mk' C'
  let P : Subgroup (R ⧸ C') := Q'.map f
  have hP : IsPGroup p P := hQ'.map f
  have hdvd : Nat.card P ∣ C.relIndex R := by
    have h1 : Nat.card P ∣ Nat.card (R ⧸ C') := Subgroup.card_subgroup_dvd_card P
    have h2 : Nat.card (R ⧸ C') = C'.index := (Subgroup.index_eq_card C').symm
    have h3 : C'.index = C.relIndex R := rfl
    rwa [h2, h3] at h1
  have hcopP : p.Coprime (Nat.card P) :=
    Nat.Coprime.coprime_dvd_right hdvd hcop.symm
  have hcard : Nat.card P = 1 := by
    rcases hP.card_eq_or_dvd with h | h
    · exact h
    · exact absurd (hcopP.eq_one_of_dvd h) (Fact.out : p.Prime).ne_one
  have hbot : P = ⊥ := Subgroup.card_eq_one.1 hcard
  have hxP : f (⟨x, hQR hxQ⟩ : R) ∈ P :=
    Subgroup.mem_map.2 ⟨_, hxQ', rfl⟩
  have hf : f (⟨x, hQR hxQ⟩ : R) = 1 := by
    have := hxP
    rw [hbot] at this
    exact Subgroup.mem_bot.1 this
  have hyker : (⟨x, hQR hxQ⟩ : R) ∈ f.ker := MonoidHom.mem_ker.2 hf
  have hyC' : (⟨x, hQR hxQ⟩ : R) ∈ C' := by
    simpa [f] using hyker
  exact Subgroup.mem_subgroupOf.1 hyC'

theorem exists_twNormTwo_descent {f : ℕ} (hf : 1 ≤ f) (h3 : 3 ∣ 2 ^ f + 1) (Ω : Type) [Field Ω]
    [Algebra (GaloisField 2 (2 * f)) Ω] [IsAlgClosure (GaloisField 2 (2 * f)) Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ f)
    {X V : Subgroup (ModGL Tag.E6 Ω)} (hXR : X ≤ TwistedDiag.Rgrp Ω Fr)
    (hVR : V ≤ TwistedDiag.Rgrp Ω Fr) (hV1 : V ≠ ⊥) (hV2 : IsPGroup 2 V)
    (hXV : X ≤ Subgroup.normalizer (V : Set (ModGL Tag.E6 Ω))) :
    ∃ A : Subgroup (ModGL TwistTag.E6.tag (GaloisField 2 (2 * f))),
      A ≤ twistedE6InndiagGL (GaloisField 2 (2 * f)) (frobQEquiv hf) ∧
      A.map (baseChangeGL (algebraMap (GaloisField 2 (2 * f)) Ω)) = X ∧
      TwNormTwo (GaloisField 2 (2 * f)) (frobQEquiv hf) A := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let K := GaloisField 2 (2 * f)
  let R : Subgroup (ModGL Tag.E6 Ω) := TwistedDiag.Rgrp Ω Fr
  let C : Subgroup (ModGL Tag.E6 Ω) := TwistedDiag.Cgrp K (frobQEquiv hf).toRingHom Ω
  let C₀ : Subgroup (ModGL TwistTag.E6.tag K) :=
    graphFixedRootGroup TwistTag.E6 K (frobQEquiv hf).toRingHom
  let Γ : Subgroup (ModGL TwistTag.E6.tag K) :=
    RecipeExcLang.twInndiagGroup K (frobQEquiv hf)
  let b : ModGL TwistTag.E6.tag K →* ModGL Tag.E6 Ω :=
    baseChangeGL (algebraMap K Ω)
  have hb : Function.Injective b := baseChangeGL_injective (algebraMap K Ω)
  have hK : Nat.card K = (2 ^ f) ^ 2 :=
    CFSG.LieType.Universal.card_galoisField_two_mul 2 f hf
  have hσ : ∀ c : K, frobQEquiv hf c = c ^ 2 ^ f :=
    fun c => CFSG.LieType.Steinberg.Exceptional.frobQ_apply 2 f c
  let Φ : ↥Γ ≃* ↥R := twInndiagEquivRgrp hf hK (frobQEquiv hf) hσ Fr hFr
  obtain ⟨hfin, hCR, hCn, hC3, -⟩ :=
    TwistedDiag.cgrp_facts (ℓ := 2) hf K hK (frobQEquiv hf).toRingHom hσ h3 Ω Fr hFr
  haveI : Finite ↥R := hfin
  have hVC : V ≤ C := by
    refine isPGroup_le_of_normal_of_relIndex_coprime hCR hCn ?_ hV2 ?_
    · exact hVR
    · rw [hC3]; norm_num
  let ε : ↥C₀ ≃* ↥C := Subgroup.equivMapOfInjective C₀ b hb
  let A : Subgroup (ModGL TwistTag.E6.tag K) :=
    ((X.subgroupOf R).map Φ.symm.toMonoidHom).map Γ.subtype
  have hA_le : A ≤ twistedE6InndiagGL K (frobQEquiv hf) := by
    intro x hx
    obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.1 hx
    exact twInndiagGroup_le_twistedE6InndiagGL (frobQEquiv hf) w.2
  have hΦ_apply : ∀ w : ↥Γ, b (Γ.subtype w) = (Φ w : ModGL Tag.E6 Ω) := by
    intro w
    have h := twInndiagEquivRgrp_apply hf hK (frobQEquiv hf) hσ Fr hFr w
    dsimp only [b]
    exact h
  have hAb : A.map b = X := by
    ext y
    constructor
    · intro hy
      obtain ⟨x, hxA, rfl⟩ := Subgroup.mem_map.1 hy
      obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hxA
      obtain ⟨r, hr, hrw⟩ := Subgroup.mem_map.1 hw
      have hrX : (r : ModGL Tag.E6 Ω) ∈ X := Subgroup.mem_subgroupOf.1 hr
      have hwEq : w = Φ.symm r := by rw [← hrw]; rfl
      rw [hwEq, hΦ_apply, MulEquiv.apply_symm_apply]
      exact hrX
    · intro hy
      have hyR : y ∈ R := hXR hy
      have hwX : Φ.symm ⟨y, hyR⟩ ∈ (X.subgroupOf R).map Φ.symm.toMonoidHom :=
        Subgroup.mem_map.2 ⟨⟨y, hyR⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
      have hwA : ((Φ.symm ⟨y, hyR⟩ : ↥Γ) : ModGL TwistTag.E6.tag K) ∈ A :=
        Subgroup.mem_map.2 ⟨Φ.symm ⟨y, hyR⟩, hwX, rfl⟩
      refine Subgroup.mem_map.2 ⟨Φ.symm ⟨y, hyR⟩, hwA, ?_⟩
      rw [← Subgroup.subtype_apply, hΦ_apply, MulEquiv.apply_symm_apply]
  have hV' : V.subgroupOf C ≠ ⊥ := by
    intro hbot
    apply hV1
    refine le_antisymm ?_ bot_le
    intro v hv
    have hvC : (⟨v, hVC hv⟩ : ↥C) ∈ V.subgroupOf C := Subgroup.mem_subgroupOf.2 hv
    rw [hbot] at hvC
    have h1 : (⟨v, hVC hv⟩ : ↥C) = 1 := Subgroup.mem_bot.1 hvC
    exact congrArg Subtype.val h1
  have hV2' : IsPGroup 2 ↥(V.subgroupOf C) := hV2.comap_subtype
  have hconj : ∀ x ∈ A, ∀ v ∈ V.subgroupOf C,
      ∃ v' ∈ V.subgroupOf C, x * ↑(ε.symm v) * x⁻¹ = ↑(ε.symm v') := by
    intro x hxA v hvV
    obtain ⟨w, hw, hxw⟩ := Subgroup.mem_map.1 hxA
    obtain ⟨r, hr, hrw⟩ := Subgroup.mem_map.1 hw
    have hrX : (r : ModGL Tag.E6 Ω) ∈ X := Subgroup.mem_subgroupOf.1 hr
    have hxΓ : x ∈ Γ := hxw ▸ w.2
    have hbx : b x = (r : ModGL Tag.E6 Ω) := by
      have hwEq : w = Φ.symm r := by rw [← hrw]; rfl
      rw [← hxw, hwEq, hΦ_apply, MulEquiv.apply_symm_apply]
    let c : ↥C₀ := ε.symm v
    have hbc : b (c : ModGL TwistTag.E6.tag K) = (v : ModGL Tag.E6 Ω) := by
      have hεc : (Subgroup.equivMapOfInjective C₀ b hb) c = v := by
        change (Subgroup.equivMapOfInjective C₀ b hb)
          ((Subgroup.equivMapOfInjective C₀ b hb).symm v) = v
        exact MulEquiv.apply_symm_apply _ v
      have h1 := Subgroup.coe_equivMapOfInjective_apply C₀ b hb c
      rw [hεc] at h1
      exact h1.symm
    let x' : ↥Γ := ⟨x, hxΓ⟩
    let c' : ↥C₀ := RecipeExcLang.twConj K (frobQEquiv hf) x' c
    have hc' : (c' : ModGL TwistTag.E6.tag K) = x * (c : ModGL TwistTag.E6.tag K) * x⁻¹ :=
      RecipeExcLang.coe_twConj (frobQEquiv hf) x' c
    let v' : ↥C := ε c'
    have hv' : (v' : ModGL Tag.E6 Ω) =
        (r : ModGL Tag.E6 Ω) * (v : ModGL Tag.E6 Ω) * (r : ModGL Tag.E6 Ω)⁻¹ := by
      have h1 := Subgroup.coe_equivMapOfInjective_apply C₀ b hb c'
      calc
        (v' : ModGL Tag.E6 Ω) = b (c' : ModGL TwistTag.E6.tag K) := h1
        _ = b (x * (c : ModGL TwistTag.E6.tag K) * x⁻¹) := by rw [hc']
        _ = b x * b (c : ModGL TwistTag.E6.tag K) * (b x)⁻¹ := by
          rw [map_mul, map_mul, map_inv]
        _ = (r : ModGL Tag.E6 Ω) * (v : ModGL Tag.E6 Ω) * (r : ModGL Tag.E6 Ω)⁻¹ := by
          rw [hbx, hbc]
    have hv'V : (v' : ModGL Tag.E6 Ω) ∈ V := by
      have hyN : (r : ModGL Tag.E6 Ω) ∈
          Subgroup.normalizer (V : Set (ModGL Tag.E6 Ω)) := hXV hrX
      have hvV : (v : ModGL Tag.E6 Ω) ∈ V := Subgroup.mem_subgroupOf.1 hvV
      have h2 := (Subgroup.mem_normalizer_iff.1 hyN (v : ModGL Tag.E6 Ω)).1 hvV
      rwa [hv']
    have hv'sub : v' ∈ V.subgroupOf C := Subgroup.mem_subgroupOf.2 hv'V
    refine ⟨v', hv'sub, ?_⟩
    have hsym : ε.symm v' = c' := by
      change (Subgroup.equivMapOfInjective C₀ b hb).symm
        ((Subgroup.equivMapOfInjective C₀ b hb) c') = c'
      exact MulEquiv.symm_apply_apply _ c'
    rw [hsym, show ε.symm v = c from rfl]
    exact hc'.symm
  have htw : TwNormTwo K (frobQEquiv hf) A :=
    TwE6Transport.twNormTwo_of_conj (frobQEquiv hf) ε hV' hV2' hconj
  exact ⟨A, hA_le, hAb, htw⟩

end CFSG.StandardType.NoOffTwE6Three

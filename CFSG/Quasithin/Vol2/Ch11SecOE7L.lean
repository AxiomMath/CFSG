module

public import CFSG.Quasithin.Vol2.Ch11SecOE7K
public import CFSG.Quasithin.Vol2.Ch11SecBRootLiftSL2
public import CFSG.Quasithin.Vol2.Ch11SecU1Mem2

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ker_eq_pCore {F : Type} [Field F] [Finite F] [CharP F 2] {X : Type*} [Group X]
    [Finite X] (φ : X →* SL(2, F)) (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    (hF4 : 4 ≤ Nat.card F) : φ.ker = CFSG.Open.pCore 2 X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup SL(2, F) := E1.RootLift.isSimpleGroup_SL2 hF4
  refine le_antisymm (CFSG.LieType.BorelTits.le_pCore 2 inferInstance hker) ?_
  have h1 := CFSG.LieType.BorelTits.map_pCore_le 2 φ hφ
  have h2 : CFSG.Open.pCore 2 SL(2, F) = ⊥ := by
    have : (CFSG.Open.pCore 2 SL(2, F)).Normal := CFSG.LieType.BorelTits.pCore_normal 2
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (CFSG.Open.pCore 2 SL(2, F)) with h | h
    · exact h
    · exfalso
      have hp := CFSG.LieType.BorelTits.pCore_isPGroup (G := SL(2, F)) 2
      rw [h] at hp
      have := (hp.of_equiv Subgroup.topEquiv).isNilpotent
      exact E1.RootLift.not_isSolvable_SL2 hF4 inferInstance
  rw [h2, le_bot_iff, Subgroup.map_eq_bot_iff] at h1
  exact h1

theorem isE_sup_tauOf_of_quot_sl2 {n : ℕ} {F : Type} [Field F] [Finite F] [CharP F 2]
    {T A X : Subgroup G} (hT : IsSylowIn 2 T ⊤) (hAT : A ≤ T) (hA : IsElemAbelian 2 A)
    (φ : ↥X →* SL(2, F)) (hφ : Function.Surjective φ) (hker : IsPGroup 2 φ.ker)
    (hF : Nat.card F = 2 ^ n) (hF4 : 4 ≤ Nat.card F)
    (hτN : E1.tauOf ⊤ T A ≤ Subgroup.normalizer (X : Set G)) (hL : IsSylowIn 2 (T ⊓ X) X)
    (hAC : ¬ ∀ a ∈ A, ∀ x ∈ X, ⁅a, x⁆ ∈ φ.ker.map X.subtype) :
    E1.IsE n ⊤ T A (X ⊔ E1.tauOf ⊤ T A) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : IsSimpleGroup SL(2, F) := E1.RootLift.isSimpleGroup_SL2 hF4
  set τ := E1.tauOf ⊤ T A with hτdef
  have hτT : τ ≤ T := E1.tauOf_le _ _ _
  have hT2 : IsPGroup 2 T := hT.2.1
  set K := X ⊔ τ with hKdef
  have hXK : X ≤ K := le_sup_left
  have hKN : K ≤ Subgroup.normalizer (X : Set G) := sup_le Subgroup.le_normalizer hτN
  have hSyl : IsSylowIn 2 (T ⊓ K) K := SecU1.Comp.isSylowIn_sup hT2 hτT hτN hL
  set R : Subgroup G := φ.ker.map X.subtype with hRdef
  have hRX : R ≤ X := Subgroup.map_subtype_le _
  have hRc : R = (CFSG.Open.pCore 2 ↥X).map X.subtype := by
    rw [hRdef, ker_eq_pCore φ hφ hker hF4]
  have hKR : K ≤ Subgroup.normalizer (R : Set G) := by
    have : (CFSG.Open.pCore 2 ↥X).Characteristic := CFSG.LieType.BorelTits.pCore_characteristic 2
    rw [hRc]
    exact hKN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hR2 : IsPGroup 2 R := hker.map X.subtype
  set XK := X.subgroupOf K with hXKdef
  set RK := R.subgroupOf K with hRKdef
  have hXKn : XK.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hXK).mpr hKN
  have hRKn : RK.Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (hRX.trans hXK)).mpr hKR
  have hRK2 : IsPGroup 2 RK := hR2.comap_of_injective K.subtype K.subtype_injective
  have hτ' : IsPGroup 2 ↥(τ.subgroupOf K) :=
    (hT2.to_le hτT).comap_of_injective K.subtype K.subtype_injective
  have hsup : XK ⊔ τ.subgroupOf K = ⊤ := (Subgroup.codisjoint_subgroupOf_sup X τ).eq_top
  have htwoK : ∀ q : ↥K, ∃ k : ℕ, q ^ 2 ^ k ∈ XK := fun q => by
    have hq : q ∈ XK ⊔ τ.subgroupOf K := hsup ▸ Subgroup.mem_top q
    obtain ⟨y, hy, z, hz, rfl⟩ := Subgroup.mem_sup_of_normal_left.mp hq
    obtain ⟨k, hk⟩ := hτ' ⟨z, hz⟩
    refine ⟨k, ?_⟩
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, QuotientGroup.mk_mul,
      (QuotientGroup.eq_one_iff y).mpr hy, one_mul, ← QuotientGroup.mk_pow,
      show z ^ 2 ^ k = 1 by simpa using congrArg Subtype.val hk, QuotientGroup.mk_one]
  set π₁ := QuotientGroup.mk' RK with hπ₁
  have hπ₁s : Function.Surjective π₁ := QuotientGroup.mk'_surjective RK
  set Xt := XK.map π₁ with hXtdef
  have hXtn : Xt.Normal := hXKn.map π₁ hπ₁s
  set f₁ := π₁.subgroupMap XK with hf₁
  have hf₁s : Function.Surjective f₁ := π₁.subgroupMap_surjective XK
  set eX := Subgroup.subgroupOfEquivOfLe hXK with heX
  set f₂ : ↥XK →* SL(2, F) := φ.comp eX.toMonoidHom with hf₂
  have hf₂s : Function.Surjective f₂ := hφ.comp eX.surjective
  have hkereq : f₁.ker = f₂.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    constructor
    · intro hx
      have h1 : π₁ (x : ↥K) = 1 := congrArg Subtype.val hx
      rw [hπ₁, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hRKdef,
        Subgroup.mem_subgroupOf] at h1
      obtain ⟨y, hy, hyx⟩ := h1
      have hyx' : y = eX x := Subtype.ext hyx
      rw [hf₂, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, ← hyx']
      exact hy
    · intro hx
      apply Subtype.ext
      change π₁ (x : ↥K) = 1
      rw [hπ₁, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hRKdef,
        Subgroup.mem_subgroupOf]
      exact ⟨eX x, hx, rfl⟩
  let eXt : ↥Xt ≃* SL(2, F) :=
    (QuotientGroup.quotientKerEquivOfSurjective f₁ hf₁s).symm.trans
      ((QuotientGroup.quotientMulEquivOfEq hkereq).trans
        (QuotientGroup.quotientKerEquivOfSurjective f₂ hf₂s))
  have : IsSimpleGroup ↥Xt := eXt.isSimpleGroup
  have hnabXt : ∃ x y : ↥Xt, x * y ≠ y * x := by
    obtain ⟨x, y, hxy⟩ := SecE3.sl2_nonabelian (K := F)
    exact ⟨eXt.symm x, eXt.symm y, fun h => hxy (eXt.symm.injective (by
      rw [map_mul, map_mul, h]))⟩
  set Ct := Subgroup.centralizer (Xt : Set (↥K ⧸ RK)) with hCtdef
  have hZ := SecE3.center_eq_bot_of_simple hnabXt
  have hLC : Xt ⊓ Ct = ⊥ := by
    refine le_bot_iff.mp fun x hx => ?_
    obtain ⟨hxX, hxC⟩ := Subgroup.mem_inf.mp hx
    have hc : (⟨x, hxX⟩ : ↥Xt) ∈ Subgroup.center ↥Xt := Subgroup.mem_center_iff.mpr fun y =>
      Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC y y.2)
    rw [hZ, Subgroup.mem_bot] at hc
    exact Subgroup.mem_bot.mpr (by simpa using congrArg Subtype.val hc)
  have hcent : ∀ q : ↥K ⧸ RK, (∀ l ∈ Xt, l * q = q * l) → q ∈ Ct := fun q h =>
    Subgroup.mem_centralizer_iff.mpr fun l hl => h l hl
  have htwo : ∀ q : ↥K ⧸ RK, ∃ k : ℕ, q ^ 2 ^ k ∈ Xt := fun q => by
    obtain ⟨y, rfl⟩ := hπ₁s q
    obtain ⟨k, hk⟩ := htwoK y
    exact ⟨k, by rw [← map_pow]; exact Subgroup.mem_map_of_mem π₁ hk⟩
  have hAS := SecU1.Comp.almostSimple_map hnabXt hLC hcent htwo
  have hCt2 : IsPGroup 2 Ct := SecU1.Comp.isPGroup_two hLC htwo
  set ψ := (QuotientGroup.mk' Ct).comp π₁ with hψdef
  have hψs : Function.Surjective ψ := (QuotientGroup.mk'_surjective Ct).comp hπ₁s
  have hψker : IsPGroup 2 ψ.ker := by
    intro k
    have hk : π₁ (k : ↥K) ∈ Ct := by
      have h1 : QuotientGroup.mk' Ct (π₁ (k : ↥K)) = 1 := MonoidHom.mem_ker.mp k.2
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨a, ha⟩ := hCt2 ⟨_, hk⟩
    have ha' : (k : ↥K) ^ 2 ^ a ∈ RK := by
      rw [← QuotientGroup.eq_one_iff, ← QuotientGroup.mk'_apply, ← hπ₁, map_pow]
      simpa using congrArg Subtype.val ha
    obtain ⟨b, hb⟩ := hRK2 ⟨_, ha'⟩
    refine ⟨a + b, Subtype.ext ?_⟩
    have hb' : ((k : ↥K) ^ 2 ^ a) ^ 2 ^ b = 1 := by simpa using congrArg Subtype.val hb
    rw [← pow_mul, ← pow_add] at hb'
    simpa using hb'
  set χ := QuotientGroup.mk' Ct with hχ
  have hinj : Function.Injective (χ.comp Xt.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hχ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h : (x : ↥K ⧸ RK) ∈ Xt ⊓ Ct := ⟨x.2, hx⟩
    rw [hLC, Subgroup.mem_bot] at h
    exact Subgroup.mem_bot.mpr (Subtype.ext h)
  have hrange : (χ.comp Xt.subtype).range = Xt.map χ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  let eL : ↥(Xt.map χ) ≃* SL(2, F) :=
    ((MulEquiv.subgroupCongr hrange).symm.trans (MonoidHom.ofInjective hinj).symm).trans eXt
  have hB : (A.subgroupOf K).map ψ ≠ ⊥ := by
    intro h0
    apply hAC
    intro a ha x hx
    have hAτ : A ≤ τ := le_sup_left.trans (E1.le_tauOf hT hAT hA)
    have haK : a ∈ K := (le_sup_right : τ ≤ K) (hAτ ha)
    have hψa : ψ ⟨a, haK⟩ = 1 := by
      have : ψ ⟨a, haK⟩ ∈ (A.subgroupOf K).map ψ := ⟨⟨a, haK⟩, ha, rfl⟩
      rwa [h0, Subgroup.mem_bot] at this
    have haC : π₁ ⟨a, haK⟩ ∈ Ct := by
      have h1 : QuotientGroup.mk' Ct (π₁ ⟨a, haK⟩) = 1 := hψa
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hxt : π₁ ⟨x, hXK hx⟩ ∈ Xt := ⟨⟨x, hXK hx⟩, hx, rfl⟩
    have hcomm := Subgroup.mem_centralizer_iff.mp haC _ hxt
    have hc : π₁ ⁅(⟨a, haK⟩ : ↥K), ⟨x, hXK hx⟩⁆ = 1 := by
      rw [commutatorElement_def, map_mul, map_mul, map_mul, map_inv, map_inv, ← hcomm]
      group
    rw [hπ₁, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hRKdef,
      Subgroup.mem_subgroupOf] at hc
    simpa [commutatorElement_def] using hc
  exact isE_of_almostSimple_quot hT hAT hA le_sup_right hSyl ψ hψs hψker hAS eL hF hB

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

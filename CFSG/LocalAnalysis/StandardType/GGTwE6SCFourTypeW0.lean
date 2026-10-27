module

public import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourModel
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeAEndModel
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourInverter
import CFSG.LocalAnalysis.StandardType.GGTwE6SCFourCoroot
import CFSG.HardMathSupport.Malle.E27Lie.ExcCross.TwE6Core

public section

namespace CFSG.StandardType.SCFourCover

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.HardMathSupport.Lang.E6Descent
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three CFSG.RankThree.PartOne.KE


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)
  (ε : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) ≃* TwE6Delta.RecipeR K n)

include hn hK hσ hFr in
private theorem mem_Cgrp_of_mul_self (h3 : 3 ∣ 2 ^ n + 1) {x : ModGL Tag.E6 Ω}
    (hx : x ∈ TwistedDiag.Rgrp Ω Fr) (hx2 : x * x = 1) :
    x ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, hCn, hCi, -⟩ :=
    TwistedDiag.cgrp_facts (ℓ := 2) (f := n) hn K hK σ.toRingHom hσ h3 Ω Fr hFr
  haveI := hCn
  have h1 := Subgroup.pow_index_mem
    ((TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf (TwistedDiag.Rgrp Ω Fr)) ⟨x, hx⟩
  have hidx : ((TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf
      (TwistedDiag.Rgrp Ω Fr)).index = 3 := hCi
  rw [hidx] at h1
  have h : x ^ 3 ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := Subgroup.mem_subgroupOf.1 h1
  rwa [show x ^ 3 = x by rw [pow_succ, pow_two, hx2, one_mul]] at h

theorem conj_weylElt_mem_Rgrp {g0 : ModGL Tag.E6 Ω} (hg0 : g0 ∈ adjointGroup Tag.E6 Ω)
    (hgn : g0⁻¹ * twistE6 Ω Fr g0 = TwistedDiag.n0 Ω) (i : Fin Tag.E6.rank) :
    g0 * weylElt Tag.E6 Ω i 1 * g0⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
  refine (TwistedDiag.mem_thetaFixed_iff_conj Fr hg0 hgn _).1
    ⟨weylElt_mem_adjointGroup (τ := Tag.E6) i 1, ?_⟩
  change TwistedDiag.theta Fr (weylElt Tag.E6 Ω i 1) = weylElt Tag.E6 Ω i 1
  rw [TwistedDiag.theta_apply]
  exact CFSG.HardMathSupport.Malle.E27Lie.ExcCross.weylElt_twistFixed6 (L := Ω) Fr
    (fun u => twE6W0_smul u) i

include hFr in
theorem conj_torusElt_mem_Rgrp [IsAlgClosed Ω] (h3 : 3 ∣ 2 ^ n + 1)
    {g0 : ModGL Tag.E6 Ω} (hg0 : g0 ∈ adjointGroup Tag.E6 Ω)
    (hgn : g0⁻¹ * twistE6 Ω Fr g0 = TwistedDiag.n0 Ω) {ζ : Ωˣ} (hζ : ζ ^ 3 = 1)
    (i : Fin Tag.E6.rank) : g0 * torusElt Tag.E6 Ω i ζ * g0⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
  have hb : ∀ j, (fun j => ζ ^ Tag.E6.cartan i j) j ^ 3 = 1 := fun j => by
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζ, one_zpow]
  rw [torusElt_eq_rootDiagUnit]
  exact TwE6DD2.conj_cubeTorus_le_Rgrp Fr hFr h3 hg0 hgn
    ⟨_, TwE6DD2.rootDiagUnit_mem_cubeTorus hb, rfl⟩

private theorem rgrpRecipeAut_apply_eq (r : ↥(TwistedDiag.Rgrp Ω Fr))
    {c c' : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)}
    (h : (r : ModGL Tag.E6 Ω) * baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 *
      (r : ModGL Tag.E6 Ω)⁻¹ = baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c'.1) :
    rgrpRecipeAut hn hK σ hσ Fr hFr ε r (ε c) = ε c' := by
  rw [rgrpRecipeAut_apply]
  congr 1
  refine Subtype.ext (baseChangeGL_injective (τ := Tag.E6) (algebraMap K Ω) ?_)
  rw [← h]
  have key : ∀ a b : ModGL TwistTag.E6.tag K,
      baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) (a * b * a⁻¹) =
        baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) a *
          baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) b *
            (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω) a)⁻¹ := fun a b => by
    rw [map_mul, map_mul, map_inv]
  obtain ⟨w, rfl⟩ := (twInndiagEquivRgrp hn hK σ hσ Fr hFr).surjective r
  rw [rgrpConjAut_apply_baseChange, RecipeExcLang.coe_twConj]
  exact key w.1 c.1

include hn hK hσ hFr in
private theorem mem_rgrpModel_of_inverts
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (h3 : 3 ∣ 2 ^ n + 1) {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')}
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l))
    (hSC : GGTorusSelfCent 3 A) {u t : ModGL Tag.E6 Ω} (huR : u ∈ TwistedDiag.Rgrp Ω Fr)
    (htR : t ∈ TwistedDiag.Rgrp Ω Fr) (hu3 : u ^ 3 = 1) (ht2 : t * t = 1)
    (htu : t * u * t⁻¹ = u⁻¹)
    (hmodel : ∀ x ∈ rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A),
      x * u = u * x ∧ ∃ k : ℕ, x * t * x⁻¹ = t * u ^ k) :
    u ∈ rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) := by
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht2
  have htC := mem_Cgrp_of_mul_self hn hK σ hσ Fr hFr h3 htR ht2
  have htuC := mem_Cgrp_of_mul_self hn hK σ hσ Fr hFr h3 (mul_mem htR huR) (by
    rw [show t * u * (t * u) = t * u * t⁻¹ * u by rw [htinv, mul_assoc (t * u)], htu,
      inv_mul_cancel])
  have huC : u ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
    have h := mul_mem (inv_mem htC) htuC
    rwa [inv_mul_cancel_left] at h
  obtain ⟨cu, hcu, rfl⟩ := huC
  obtain ⟨ct, hct, rfl⟩ := htC
  set Cu : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := ⟨cu, hcu⟩
  set Ct : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) := ⟨ct, hct⟩
  have hι : ∀ {c c' : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)},
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 =
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c'.1 → ε c = ε c' := fun h =>
    congrArg ε (Subtype.ext (baseChangeGL_injective (τ := Tag.E6) (algebraMap K Ω) h))
  have hmul : ∀ c₁ c₂ : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (c₁ * c₂).1 =
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c₁.1 *
          baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c₂.1 := fun c₁ c₂ => by
    rw [Subgroup.coe_mul]
    exact map_mul (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω)) _ _
  have hinv : ∀ c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c⁻¹.1 =
        (baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1)⁻¹ := fun c => by
    rw [Subgroup.coe_inv]
    exact map_inv (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω)) _
  have hpow : ∀ (c : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)) (m : ℕ),
      baseChangeGL (τ := Tag.E6) (algebraMap K Ω) (c ^ m).1 =
        baseChangeGL (τ := Tag.E6) (algebraMap K Ω) c.1 ^ m := fun c m => by
    rw [Subgroup.coe_pow]
    exact map_pow (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω)) _ _
  have hU3 : ε Cu ^ 3 = 1 := by
    rw [← map_pow, ← map_one ε]
    refine hι ?_
    rw [hpow]
    refine hu3.trans ?_
    rw [Subgroup.coe_one]
    exact (map_one (baseChangeGL (τ := TwistTag.E6.tag) (algebraMap K Ω))).symm
  have hTU : ε Ct * ε Cu * (ε Ct)⁻¹ = (ε Cu)⁻¹ := by
    rw [← map_mul, ← map_inv, ← map_mul, ← map_inv]
    refine hι ?_
    rw [hmul, hmul, hinv, hinv]
    exact htu
  obtain ⟨a, ha, hconj⟩ := exists_induces_conj_of_inverts hψ hker hSC hU3 hTU fun a ha => by
    obtain ⟨φ, hφI, hφ⟩ := hAI a ha
    obtain ⟨r, rfl⟩ := (mem_range_rgrpRecipeAut hn hK σ hσ Fr hFr ε hε φ).2 hφI
    obtain ⟨hcomm, k, hk⟩ := hmodel r ((mem_rgrpModel hn hK σ hσ Fr hFr ε).2
      ⟨r.2, TypeA.mem_inducedSub.2 ⟨a, ha, hφ⟩⟩)
    refine ⟨_, hφ, rgrpRecipeAut_apply_eq hn hK σ hσ Fr hFr ε r ?_, k, ?_⟩
    · rw [mul_inv_eq_iff_eq_mul]
      exact hcomm
    · rw [zpow_natCast, ← map_pow, ← map_mul]
      refine rgrpRecipeAut_apply_eq hn hK σ hσ Fr hFr ε r ?_
      rw [hmul, hpow]
      exact hk
  refine (mem_rgrpModel hn hK σ hσ Fr hFr ε).2 ⟨huR, TypeA.mem_inducedSub.2 ⟨a, ha, fun l => ?_⟩⟩
  rw [← hconj l]
  obtain ⟨c, hc⟩ := ε.surjective (ψ l)
  rw [← hc, MulAut.conj_apply, ← map_mul, ← map_inv, ← map_mul]
  refine rgrpRecipeAut_apply_eq hn hK σ hσ Fr hFr ε _ ?_
  rw [hmul, hmul, hinv]

theorem conj_torusElt_mem_rgrpModel
    (hε : ∀ x : MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom),
      MulAut.congr ε x ∈ TwE6Delta.RecipeI K n ↔ x ∈ (RecipeExcLang.twConj K σ).range)
    (h3 : 3 ∣ 2 ^ n + 1) {L' : Type} [Group L'] {ψ : L' →* TwE6Delta.RecipeR K n}
    (hψ : Function.Surjective ψ) (hker : ψ.ker ≤ Subgroup.center L')
    {A : Subgroup (MulAut L')} (hA : ∀ a ∈ A, a ^ 3 = 1)
    (hAI : ∀ a ∈ A, ∃ φ ∈ TwE6Delta.RecipeI K n, ∀ l, φ (ψ l) = ψ (a l))
    (hSC : GGTorusSelfCent 3 A) {g0 : ModGL Tag.E6 Ω} (hg0 : g0 ∈ adjointGroup Tag.E6 Ω)
    (hgn : g0⁻¹ * twistE6 Ω Fr g0 = TwistedDiag.n0 Ω)
    (hX : ∀ x ∈ rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A),
      x ∈ (twistedTorusOf (TwistedDiag.n0 Ω) (twistE6 Ω Fr)).map (MulAut.conj g0).toMonoidHom)
    {ζ : Ωˣ} (hζ : orderOf ζ = 3) (i : Fin Tag.E6.rank) :
    g0 * torusElt Tag.E6 Ω i ζ * g0⁻¹ ∈ rgrpModel hn hK σ hσ Fr hFr ε (TypeA.inducedSub ψ A) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI := Fintype.ofFinite K
  haveI : CharP K 2 := charP_of_card_eq_prime_pow (f := n * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have hζ3 : ζ ^ 3 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  obtain ⟨hu3, ht2, htu⟩ := inverts_conj_torusElt (CharP.cast_eq_zero Ω 2) g0 hζ3 i
  refine mem_rgrpModel_of_inverts hn hK σ hσ Fr hFr ε hε h3 hψ hker hAI hSC
    (conj_torusElt_mem_Rgrp Fr hFr h3 hg0 hgn hζ3 i) (conj_weylElt_mem_Rgrp Fr hg0 hgn i) hu3
    ht2 htu fun x hx => ?_
  obtain ⟨hxR, hxA⟩ := (mem_rgrpModel hn hK σ hσ Fr hFr ε).1 hx
  obtain ⟨a, ha, hφ⟩ := TypeA.mem_inducedSub.1 hxA
  have h1 : (⟨x, hxR⟩ : ↥(TwistedDiag.Rgrp Ω Fr)) ^ 3 = 1 :=
    rgrpRecipeAut_injective hn hK σ hσ Fr hFr ε (by
      rw [map_pow, map_one]
      refine TypeA.induced_unique ψ hψ (TypeA.induced_pow ψ hφ 3) fun l => ?_
      rw [hA a ha]
      rfl)
  have hx3 : x ^ 3 = 1 := by
    have h := congrArg Subtype.val h1
    rwa [Subgroup.coe_pow, Subgroup.coe_one] at h
  obtain ⟨b, hb, rfl, -⟩ := exists_rootDiagUnit_of_mem_langTorus (v := twE6W0) (hX x hx) hx3
  exact conj_rootDiagUnit_conj_weylElt g0 hb hζ i

end CFSG.StandardType.SCFourCover

end

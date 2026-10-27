module

public import CFSG.LocalAnalysis.StandardType.GGTwE6DD2Torus
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLangTorus
public import CFSG.LocalAnalysis.StandardType.GGE6ThreeModelLiftT
import TauCeti.Algebra.Group.Coprime

public section

namespace CFSG.StandardType.TwE6R5

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LieType.Steinberg.Exceptional CFSG.LieType.Universal
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Lang.E6Descent CFSG.StandardType.TableBExc.E6Three
  CFSG.RankThree.Classical2 CFSG.StandardType.NoOffTwE6Three


variable {n : ℕ} (hn : 1 ≤ n) {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ n) ^ 2)
  (σ : K ≃+* K) (hσ : ∀ c, σ c = c ^ 2 ^ n) {Ω : Type} [Field Ω] [Algebra K Ω]
  [IsAlgClosure K Ω] (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ 2 ^ n)

include hn hK hσ hFr in
theorem exists_cube_not_mem_cgrp (h3 : 3 ∣ 2 ^ n + 1) (h9 : ¬ 9 ∣ 2 ^ n + 1)
    {g : ModGL Tag.E6 Ω} (hg : g ∈ adjointGroup Tag.E6 Ω)
    (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    ∃ b : Fin Tag.E6.rank → Ωˣ, (∀ i, b i ^ 3 = 1) ∧
      g * rootDiagUnit Tag.E6 b * g⁻¹ ∉ TwistedDiag.Cgrp K σ.toRingHom Ω := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 := charP_two_of_card (m := n * 2) (by rw [hK, pow_mul])
  haveI : CharP Ω 2 := charP_of_injective_algebraMap (algebraMap K Ω).injective 2
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  by_contra hcon
  have hall : ∀ b : Fin Tag.E6.rank → Ωˣ, (∀ i, b i ^ 3 = 1) →
      g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Cgrp K σ.toRingHom Ω :=
    fun b hb => Classical.byContradiction fun h => hcon ⟨b, hb, h⟩
  obtain ⟨-, -, hCnorm, hCidx, -⟩ :=
    TwistedDiag.cgrp_facts hn K hK σ.toRingHom hσ h3 Ω Fr hFr
  haveI : ((TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf (TwistedDiag.Rgrp Ω Fr)).Normal :=
    hCnorm
  obtain ⟨m, hm⟩ := id h3
  have hcop : Nat.Coprime 3 m := by
    rw [Nat.Prime.coprime_iff_not_dvd Nat.prime_three]
    rintro ⟨k, rfl⟩
    exact h9 ⟨k, by rw [hm]; ring⟩
  obtain ⟨i, j, hij⟩ := TauCeti.exists_zpow_mul_zpow_eq_of_coprime (G := ModGL Tag.E6 Ω) hcop
  obtain ⟨ζ, hζ, hζo⟩ := TwistedDiag.exists_cube_root (Ω := Ω)
    (three_ne_zero_of_dvd_card_add_one (ℓ := 2) hn h3)
  have hL : E6ThreeModel.IsLang Fr g := ⟨hg, hgn⟩
  obtain ⟨D, hD⟩ := E6ThreeModel.exists_tFrame hn hK σ hσ Fr hFr h3 hL hζ hζo
  refine E6ThreeModel.langTorus_not_le_cgrp hn hK σ hσ Fr hFr h3 hL hζ hζo hD fun x hx => ?_
  obtain ⟨b, hb, rfl⟩ := TwistedDiag.mem_thetaTorus.1 hx
  have hxR : g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr := by
    refine (TwistedDiag.mem_thetaFixed_iff_conj Fr hg hgn _).1 ?_
    rw [TwistedDiag.mem_thetaFixed]
    exact ⟨torusGroup_le_adjointGroup_E6 (rootDiagUnit_mem_torusGroup b),
      (TwistedDiag.theta_rootDiagUnit_eq_iff Fr hFr b).2 hb⟩
  have h3C : (g * rootDiagUnit Tag.E6 b * g⁻¹) ^ 3 ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
    have h := Subgroup.pow_index_mem ((TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf
      (TwistedDiag.Rgrp Ω Fr)) (⟨_, hxR⟩ : TwistedDiag.Rgrp Ω Fr)
    have hidx : ((TwistedDiag.Cgrp K σ.toRingHom Ω).subgroupOf
        (TwistedDiag.Rgrp Ω Fr)).index = 3 := hCidx
    rw [hidx] at h
    exact Subgroup.mem_subgroupOf.1 h
  have hmC : (g * rootDiagUnit Tag.E6 b * g⁻¹) ^ m ∈ TwistedDiag.Cgrp K σ.toRingHom Ω := by
    rw [conj_pow, rootDiagUnit_pow]
    refine hall (b ^ m) fun k => ?_
    rw [Pi.pow_apply, ← pow_mul, mul_comm m 3, ← hm]
    exact hb k
  have h := mul_mem (zpow_mem h3C i) (zpow_mem hmC j)
  rwa [hij] at h

theorem langCube_not_le_inn (h3 : 3 ∣ 2 ^ n + 1) (h9 : ¬ 9 ∣ 2 ^ n + 1) {g : ModGL Tag.E6 Ω}
    (hg : g ∈ adjointGroup Tag.E6 Ω) (hgn : g⁻¹ * twistE6 Ω Fr g = TwistedDiag.n0 Ω) :
    ¬ TwE6DD2.langCube hn hK σ hσ Fr hFr g ≤
      (MulAut.conj : ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom) →*
        MulAut ↥(graphFixedRootGroup TwistTag.E6 K σ.toRingHom)).range := by
  intro hle
  haveI : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  obtain ⟨b, hb, hbC⟩ := exists_cube_not_mem_cgrp hn hK σ hσ Fr hFr h3 h9 hg hgn
  have hx : g * rootDiagUnit Tag.E6 b * g⁻¹ ∈ TwistedDiag.Rgrp Ω Fr :=
    TwE6DD2.conj_cubeTorus_le_Rgrp Fr hFr h3 hg hgn
      ⟨_, TwE6DD2.rootDiagUnit_mem_cubeTorus hb, rfl⟩
  have hmem : rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hx⟩ ∈ TwE6DD2.langCube hn hK σ hσ Fr hFr g :=
    (TwE6DD2.mem_langCube hn hK σ hσ Fr hFr).2 ⟨b, hb, hx, rfl⟩
  obtain ⟨c, hc⟩ := hle hmem
  have h1 : rgrpConjAut hn hK σ hσ Fr hFr (twInndiagEquivRgrp hn hK σ hσ Fr hFr
      ⟨c, RecipeExcLang.graphFixedRootGroup_le_twInndiag σ c.2⟩) =
      rgrpConjAut hn hK σ hσ Fr hFr ⟨_, hx⟩ :=
    (rgrpConjAut_apply_baseChange hn hK σ hσ Fr hFr _).trans
      ((RecipeExcLang.twConj_of_mem_C0 σ c).trans hc)
  have h2 : baseChangeGL (algebraMap K Ω) (c : ModGL TwistTag.E6.tag K) =
      g * rootDiagUnit Tag.E6 b * g⁻¹ :=
    congrArg Subtype.val (rgrpConjAut_injective hn hK σ hσ Fr hFr h1)
  exact hbC ⟨c.1, c.2, h2⟩

end CFSG.StandardType.TwE6R5

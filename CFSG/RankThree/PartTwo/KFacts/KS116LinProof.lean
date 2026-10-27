module

public import CFSG.RankThree.PartTwo.KFacts.KS116Lin
public import Mathlib.Algebra.Module.ZMod
public import CFSG.RankThree.PartTwo.KFacts.KS116LinCore
public import Mathlib.Algebra.Field.ZMod

public section

namespace CFSG.RankThree.PartTwo.KFacts.NDC

open Representation
open scoped commutatorElement

theorem ndc_rep {F : Type} [Field F] [Finite F] (h2 : (2 : F) ≠ 0) {G : Type} [Group G] [Finite G]
    (T K : Subgroup G) (n : G) [T.Normal] [Group.IsSolvable T] (h3 : ¬ 3 ∣ Nat.card T)
    (hK : ⁅K, K⁆ = K) (hKT : ⁅K, K.map (MulAut.conj n).toMonoidHom⁆ ≤ T)
    (V : Type) [AddCommGroup V] [Module F V] [Module.Finite F V]
    (hd : Module.finrank F V ≤ 3) (ρ : Representation F G V) : ∀ k ∈ K, ρ k = 1 := by
  have key : ∀ d : ℕ, ∀ (W : Type) [AddCommGroup W] [Module F W] [Module.Finite F W],
      Module.finrank F W = d → d ≤ 3 → ∀ ρ' : Representation F G W, ∀ k ∈ K, ρ' k = 1 := by
    intro d
    induction d using Nat.strong_induction_on with
    | _ d ih =>
      intro W _ _ _ hdim hdle ρ'
      by_cases hex : ∃ U : Submodule F W, (∀ g, U ≤ U.comap (ρ' g)) ∧ U ≠ ⊥ ∧ U ≠ ⊤
      · obtain ⟨U, hU, hbot, htop⟩ := hex
        have hlt : Module.finrank F U < Module.finrank F W := Submodule.finrank_lt htop
        have hq : Module.finrank F (W ⧸ U) + Module.finrank F U = Module.finrank F W :=
          Submodule.finrank_quotient_add_finrank U
        have hpos : 1 ≤ Module.finrank F U := Submodule.one_le_finrank_iff.mpr hbot
        have hlt1 : Module.finrank F U < d := by omega
        have hlt2 : Module.finrank F (W ⧸ U) < d := by omega
        have h1 : ∀ k ∈ K, ρ'.subrepresentation U hU k = 1 :=
          ih (Module.finrank F U) hlt1 U rfl (by omega) (ρ'.subrepresentation U hU)
        have h2' : ∀ k ∈ K, ρ'.quotient U hU k = 1 :=
          ih (Module.finrank F (W ⧸ U)) hlt2 (W ⧸ U) rfl (by omega) (ρ'.quotient U hU)
        exact trivial_of_sub_quot ρ' U hU hK h1 h2'
      · have hirr : ∀ U : Submodule F W, (∀ g, U ≤ U.comap (ρ' g)) → U = ⊥ ∨ U = ⊤ := by
          intro U hU
          by_contra hc
          rw [not_or] at hc
          exact hex ⟨U, hU, hc.1, hc.2⟩
        exact core_irreducible h2 ρ' hirr (by omega) T K n h3 hK hKT
  exact key (Module.finrank F V) V rfl hd ρ

end CFSG.RankThree.PartTwo.KFacts.NDC

namespace CFSG.RankThree.PartTwo.KFacts

open scoped commutatorElement

private theorem noDoubleComponentGL_of_comm (r : ℕ) [Fact r.Prime] (hr5 : 5 ≤ r)
    (W : Type) [CommGroup W] [Finite W] (hexp : ∀ w : W, w ^ r = 1)
    (hgen : ∃ s : Finset W, s.card ≤ 3 ∧ Subgroup.closure (s : Set W) = ⊤)
    (Γ T K : Subgroup (MulAut W)) (n : MulAut W) (hn : n ∈ Γ) (hKΓ : K ≤ Γ) (hTΓ : T ≤ Γ)
    (hTn : ∀ g ∈ Γ, ∀ t ∈ T, g * t * g⁻¹ ∈ T) (hsolv : Group.IsSolvable T)
    (h3 : ¬ 3 ∣ Nat.card T) (hK : ⁅K, K⁆ = K)
    (hKT : ⁅K, K.map (MulAut.conj n).toMonoidHom⁆ ≤ T) : K = ⊥ := by
  have hpow : ∀ x : Additive W, r • x = 0 := by
    intro x
    obtain ⟨w, rfl⟩ : ∃ w : W, Additive.ofMul w = x := ⟨Additive.toMul x, rfl⟩
    rw [← ofMul_pow, hexp w]
    rfl
  have instMod : Module (ZMod r) (Additive W) := AddCommGroup.zmodModule hpow
  haveI : NeZero r := ⟨by omega⟩
  have h2 : (2 : ZMod r) ≠ 0 := by
    intro h
    have h' : ((2 : ℕ) : ZMod r) = 0 := by exact_mod_cast h
    have := Nat.le_of_dvd (by norm_num) ((ZMod.natCast_eq_zero_iff 2 r).1 h')
    omega
  have hfin : Module.finrank (ZMod r) (Additive W) ≤ 3 := by
    obtain ⟨s, hs3, hsT⟩ := hgen
    obtain ⟨S, hS3, hspan⟩ : ∃ S : Finset (Additive W), S.card ≤ 3 ∧
        Submodule.span (ZMod r) (S : Set (Additive W)) = (⊤ : Submodule (ZMod r) (Additive W)) := by
      refine ⟨s.map Additive.ofMul.toEmbedding, (Finset.card_map _).le.trans hs3, ?_⟩
      rw [eq_top_iff]
      rintro x -
      obtain ⟨w, rfl⟩ : ∃ w : W, Additive.ofMul w = x := ⟨Additive.toMul x, rfl⟩
      have hw : w ∈ Subgroup.closure (s : Set W) := by
        rw [hsT]
        exact Subgroup.mem_top w
      induction hw using Subgroup.closure_induction with
      | mem y hy =>
        exact Submodule.subset_span
          (Finset.mem_coe.2 (Finset.mem_map_of_mem _ (Finset.mem_coe.1 hy)))
      | one => exact zero_mem _
      | mul y z _ _ hy hz =>
        rw [ofMul_mul]
        exact add_mem hy hz
      | inv y _ hy =>
        rw [ofMul_inv]
        exact neg_mem hy
    have hc := finrank_span_finset_le_card (R := ZMod r) S
    rw [Set.finrank, hspan, finrank_top] at hc
    exact hc.trans hS3
  haveI : Finite (MulAut W) :=
    Finite.of_injective (fun f : MulAut W => (f : W → W)) DFunLike.coe_injective
  haveI : Module.Finite (ZMod r) (Additive W) := inferInstance
  obtain ⟨ρ, hρ⟩ : ∃ ρ : Representation (ZMod r) Γ (Additive W),
      ∀ (g : Γ) (w : W), ρ g (Additive.ofMul w) = Additive.ofMul ((g : MulAut W) w) := by
    let L : Γ → (Additive W →ₗ[ZMod r] Additive W) := fun g =>
      AddMonoidHom.toZModLinearMap r (MulEquiv.toAdditive (g : MulAut W)).toAddMonoidHom
    refine ⟨{ toFun := L, map_one' := LinearMap.ext fun w => rfl,
              map_mul' := fun g h => LinearMap.ext fun w => rfl }, fun _ _ => rfl⟩
  have hρ1 : ∀ g : Γ, ρ g = 1 → (g : MulAut W) = 1 := by
    intro g hg
    ext w
    have h1 := LinearMap.congr_fun hg (Additive.ofMul w)
    rw [hρ, Module.End.one_apply] at h1
    exact congrArg Additive.toMul h1
  haveI hTn' : (T.subgroupOf Γ).Normal :=
    (Subgroup.normal_subgroupOf_iff hTΓ).2 fun h k hh hk => hTn k hk h hh
  haveI hsolv' : Group.IsSolvable (T.subgroupOf Γ) :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe hTΓ).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hTΓ).injective
  have h3' : ¬ 3 ∣ Nat.card (T.subgroupOf Γ) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTΓ).toEquiv]
    exact h3
  have hmap : (K.subgroupOf Γ).map Γ.subtype = K := by
    rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hKΓ]
  have hK' : ⁅K.subgroupOf Γ, K.subgroupOf Γ⁆ = K.subgroupOf Γ := by
    apply Subgroup.map_injective (Subgroup.subtype_injective Γ)
    rw [Subgroup.map_commutator, hmap]
    exact hK
  have hcc : Γ.subtype.comp (MulAut.conj (⟨n, hn⟩ : Γ)).toMonoidHom =
      (MulAut.conj n).toMonoidHom.comp Γ.subtype := by
    ext x
    rfl
  have hKT' : ⁅K.subgroupOf Γ, (K.subgroupOf Γ).map (MulAut.conj (⟨n, hn⟩ : Γ)).toMonoidHom⁆ ≤
      T.subgroupOf Γ := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    refine hKT ?_
    have hx' : (x : MulAut W) ∈
        (⁅K.subgroupOf Γ, (K.subgroupOf Γ).map (MulAut.conj (⟨n, hn⟩ : Γ)).toMonoidHom⁆ :
          Subgroup Γ).map Γ.subtype :=
      Subgroup.mem_map.2 ⟨x, hx, rfl⟩
    have e : ((K.subgroupOf Γ).map (MulAut.conj (⟨n, hn⟩ : Γ)).toMonoidHom).map Γ.subtype =
        K.map (MulAut.conj n).toMonoidHom := by
      rw [Subgroup.map_map, hcc, ← Subgroup.map_map, hmap]
    rw [Subgroup.map_commutator, hmap, e] at hx'
    exact hx'
  have key := NDC.ndc_rep (F := ZMod r) h2 (T.subgroupOf Γ) (K.subgroupOf Γ) ⟨n, hn⟩ h3' hK' hKT'
    (Additive W) hfin ρ
  rw [eq_bot_iff]
  intro x hx
  have hxΓ : x ∈ Γ := hKΓ hx
  have hmem : (⟨x, hxΓ⟩ : Γ) ∈ K.subgroupOf Γ := Subgroup.mem_subgroupOf.2 hx
  exact Subgroup.mem_bot.2 (hρ1 _ (key _ hmem))

theorem noDoubleComponentGL_holds : NoDoubleComponentGL := by
  intro r hp hr5 W hgrp hfinW hcomm hexp hgen Γ T K n hn hKΓ hTΓ hTn hsolv h3 hK hKT
  exact @noDoubleComponentGL_of_comm r hp hr5 W { toGroup := hgrp, mul_comm := hcomm } hfinW hexp
    hgen Γ T K n hn hKΓ hTΓ hTn hsolv h3 hK hKT

end CFSG.RankThree.PartTwo.KFacts

end

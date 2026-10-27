module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.PermNormal
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.OffenderNilpotent
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModToolBase
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseDict

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.G7.K

open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs

variable {G : Type} [Group G]

theorem conj_mem {X S : Subgroup G} (h : X ≤ Subgroup.normalizer (S : Set G)) {g s : G}
    (hg : g ∈ X) (hs : s ∈ S) : g * s * g⁻¹ ∈ S :=
  (Subgroup.mem_normalizer_iff.mp (h hg) s).mp hs

@[expose] def cenSec (X L E : Subgroup G) (hX : X ≤ Subgroup.normalizer (L : Set G)) :
    Subgroup G where
  carrier := {g | g ∈ X ∧ ∀ e ∈ E, g * e * g⁻¹ * e⁻¹ ∈ L}
  one_mem' := ⟨one_mem _, fun e _ => by simp⟩
  mul_mem' := by
    rintro a b ⟨ha, hca⟩ ⟨hb, hcb⟩
    refine ⟨mul_mem ha hb, fun e he => ?_⟩
    have h1 := conj_mem hX ha (hcb e he)
    have h2 := mul_mem h1 (hca e he)
    have : a * b * e * (a * b)⁻¹ * e⁻¹ =
        a * (b * e * b⁻¹ * e⁻¹) * a⁻¹ * (a * e * a⁻¹ * e⁻¹) := by group
    rw [this]; exact h2
  inv_mem' := by
    rintro a ⟨ha, hca⟩
    refine ⟨inv_mem ha, fun e he => ?_⟩
    have h1 := conj_mem hX (inv_mem ha) (inv_mem (hca e he))
    have : a⁻¹ * e * a⁻¹⁻¹ * e⁻¹ =
        a⁻¹ * (a * e * a⁻¹ * e⁻¹)⁻¹ * a⁻¹⁻¹ := by group
    rw [this]; exact h1

theorem cenSec_conj {X L E : Subgroup G} (hX : X ≤ Subgroup.normalizer (L : Set G))
    (hE : X ≤ Subgroup.normalizer (E : Set G)) {g t : G} (hg : g ∈ X)
    (ht : t ∈ cenSec X L E hX) : g * t * g⁻¹ ∈ cenSec X L E hX := by
  obtain ⟨htX, ht⟩ := ht
  refine ⟨mul_mem (mul_mem hg htX) (inv_mem hg), fun e he => ?_⟩
  have he' : g⁻¹ * e * g⁻¹⁻¹ ∈ E := conj_mem hE (inv_mem hg) he
  have h1 := conj_mem hX hg (ht _ he')
  have : g * t * g⁻¹ * e * (g * t * g⁻¹)⁻¹ * e⁻¹ =
      g * (t * (g⁻¹ * e * g⁻¹⁻¹) * t⁻¹ * (g⁻¹ * e * g⁻¹⁻¹)⁻¹) * g⁻¹ := by group
  rw [this]; exact h1

theorem exists_mul_of_swap {X Q C : Subgroup G} (θ : ↥X →* Perm (Fin 5))
    (hθs : Function.Surjective θ) (hθk : θ.ker = Q.subgroupOf X) (hCX : C ≤ X)
    (hCn : ∀ g ∈ X, ∀ t ∈ C, g * t * g⁻¹ ∈ C) {y : G} (hy : y ∈ C)
    (hsw : (θ ⟨y, hCX hy⟩).IsSwap) :
    ∀ g ∈ X, ∃ q ∈ Q, ∃ c ∈ C, g = q * c := by
  have hnorm : (C.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact hCn g g.2 n hn
  have hN : ((C.subgroupOf X).map θ).Normal := hnorm.map θ hθs
  have hyN : θ ⟨y, hCX hy⟩ ∈ (C.subgroupOf X).map θ :=
    ⟨⟨y, hCX hy⟩, Subgroup.mem_subgroupOf.mpr hy, rfl⟩
  have hsign := hsw.sign_eq
  rcases normal_perm_five _ hN with h | h | h
  · rw [h, Subgroup.mem_bot] at hyN
    rw [hyN] at hsign
    simp at hsign
  · rw [h, Equiv.Perm.mem_alternatingGroup, hsign] at hyN
    exact absurd hyN (by decide)
  · intro g hg
    have : θ ⟨g, hg⟩ ∈ (C.subgroupOf X).map θ := by rw [h]; trivial
    obtain ⟨c, hc, hcg⟩ := this
    have hc : (c : G) ∈ C := hc
    have hk : (⟨g, hg⟩ : ↥X) * c⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hcg, mul_inv_cancel]
    rw [hθk, Subgroup.mem_subgroupOf] at hk
    exact ⟨g * (c : G)⁻¹, hk, c, hc, by group⟩

end S35.G7.K

end F53.Stellmacher

end CFSG.Quasithin

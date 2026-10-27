module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeExcOrbit

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
  CFSG.LieType.Steinberg.Adjoint CFSG.RankThree.PartOne.KE
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.GGFinModel
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.Open (StatedLieTag IsElemAbelian)

theorem rck_setoid_transfer {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (h : kernelRoots χ = kernelRoots χ') {α β : kernelRoots χ}
    (hαβ : (kernelRootSetoid χ).r α β) :
    (kernelRootSetoid χ').r ⟨α.1, h ▸ α.2⟩ ⟨β.1, h ▸ β.2⟩ := by
  unfold kernelRootSetoid at hαβ ⊢
  induction hαβ with
  | rel x y hxy => exact Relation.EqvGen.rel _ _ hxy
  | refl x => exact Relation.EqvGen.refl _
  | symm x y _ ih => exact Relation.EqvGen.symm _ _ ih
  | trans x y z _ _ ih1 ih2 => exact Relation.EqvGen.trans _ _ _ ih1 ih2

theorem rck_component_transfer {τ : Tag} {M M' : Type*} [CommGroup M] [CommGroup M']
    {χ : Multiplicative (Fin τ.rank → ℤ) →* M} {χ' : Multiplicative (Fin τ.rank → ℤ) →* M'}
    (h : kernelRoots χ = kernelRoots χ') (i : KernelComponent χ) :
    ∃ j : KernelComponent χ', componentRoots χ i = componentRoots χ' j := by
  induction i using Quotient.inductionOn with
  | h α =>
    refine ⟨⟦⟨α.1, h ▸ α.2⟩⟧, ?_⟩
    ext β
    constructor
    · rintro ⟨hβ, hβi⟩
      exact ⟨h ▸ hβ, Quotient.sound (rck_setoid_transfer h (Quotient.exact hβi))⟩
    · rintro ⟨hβ, hβj⟩
      refine ⟨h.symm ▸ hβ, Quotient.sound ?_⟩
      have := rck_setoid_transfer h.symm (Quotient.exact hβj)
      exact this

theorem rck_coord_zpow
    {τ : Tag} {L : Type} [Field L] {y : ModGL τ L} (hy : y ∈ torusGroup τ L) (k : ℤ) :
    rckTorusCoord (y ^ k) = rckTorusCoord y ^ k := by
  have hyk : y ^ k ∈ torusGroup τ L := zpow_mem hy k
  apply rootDiagUnit_injective
  rw [rck_rootDiagUnit_coord hyk]
  have h : rootDiagUnit τ (rckTorusCoord y ^ k) = rootDiagUnit τ (rckTorusCoord y) ^ k :=
    (rootDiagUnitHom τ L).map_zpow (rckTorusCoord y) k
  rw [h, rck_rootDiagUnit_coord hy]

theorem rck_rootChar_zpow {τ : Tag} {L : Type} [Field L] (a : Fin τ.rank → Lˣ) (k : ℤ)
    (v : Fin τ.rank → ℤ) : rootChar (a ^ k) v = rootChar a v ^ k := by
  simp only [rootChar, Pi.pow_apply, ← Finset.prod_zpow]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [← zpow_mul, ← zpow_mul, mul_comm]

theorem rck_cyclic_kernel
    {t : StatedLieTag} {Dl : LangDatum (langTag t) GGL} {p : ℕ} (hp : p.Prime)
    {S : Subgroup (ModGL (langTag t) GGL)} (hcard : Nat.card S = p)
    (hSt : ∀ x ∈ S, Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus) :
    ∃ a : Fin (langTag t).rank → GGLˣ, rootDiagUnit (langTag t) a ^ p = 1 ∧
      rootDiagUnit (langTag t) a ≠ 1 ∧
      kernelRoots (rckFamChar Dl.g0 (fun x : S => (x : ModGL (langTag t) GGL))) =
        kernelRoots (rootCharHom a) := by
  haveI := Fact.mk hp
  haveI : Finite S := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hp.ne_zero)
  haveI : IsCyclic S := isCyclic_of_prime_card hcard
  obtain ⟨s, hs⟩ := IsCyclic.exists_generator (α := S)
  set y : ModGL (langTag t) GGL := Dl.g0⁻¹ * (s : ModGL (langTag t) GGL) * Dl.g0 with hy
  have hyT : y ∈ torusGroup (langTag t) GGL := (mem_twistedTorusOf.1 (hSt s s.2)).1
  refine ⟨rckTorusCoord y, ?_, ?_, ?_⟩
  · have hsp : (s : ModGL (langTag t) GGL) ^ p = 1 := by
      have h := pow_card_eq_one' (G := S) (x := s)
      rw [hcard] at h
      exact congrArg Subtype.val h
    rw [rck_rootDiagUnit_coord hyT]
    exact rck_conj_pow Dl.g0 hsp
  · rw [rck_rootDiagUnit_coord hyT]
    intro h1
    have hs1' : (s : ModGL (langTag t) GGL) = 1 := by
      calc (s : ModGL (langTag t) GGL) = Dl.g0 * y * Dl.g0⁻¹ := by rw [hy]; group
        _ = 1 := by rw [h1]; group
    have hs1 : s = 1 := Subtype.ext hs1'
    have hS1 : ∀ x : S, x = 1 := fun x => by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hs x)
      rw [← hk, hs1, one_zpow]
    have h1card : Nat.card S = 1 :=
      Nat.card_eq_one_iff_unique.2 ⟨⟨fun a b => (hS1 a).trans (hS1 b).symm⟩, ⟨1⟩⟩
    rw [hcard] at h1card
    exact hp.ne_one h1card
  · ext γ
    constructor
    · rintro ⟨hγ, h1⟩
      refine ⟨hγ, ?_⟩
      have h2 := congrFun h1 s
      rw [rck_famChar_apply] at h2
      exact h2
    · rintro ⟨hγ, h1⟩
      refine ⟨hγ, ?_⟩
      funext x
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hs x)
      rw [rck_famChar_apply]
      have hxk : Dl.g0⁻¹ * (x : ModGL (langTag t) GGL) * Dl.g0 = y ^ k := by
        rw [← hk, hy]
        have hconj := conj_zpow (a := Dl.g0⁻¹) (b := (s : ModGL (langTag t) GGL)) (i := k)
        rw [inv_inv] at hconj
        rw [hconj]
        simp
      rw [hxk, rck_coord_zpow hyT, rck_rootChar_zpow]
      have h3 : rootChar (rckTorusCoord y) γ = 1 := h1
      rw [h3, one_zpow]
      rfl

@[expose] def RCKExcShapeFour : Prop :=
  ∀ (p : ℕ), p.Prime → p ≠ 2 → ∀ (a : Fin Tag.E8.rank → GGLˣ),
    rootDiagUnit Tag.E8 a ^ p = 1 → rootDiagUnit Tag.E8 a ≠ 1 →
    ∀ (ρ : Equiv.Perm (Fin Tag.E8.rank → ℤ)),
      (∀ γ, IsRoot Tag.E8 (ρ γ) ↔ IsRoot Tag.E8 γ) → (∀ γ, ρ (-γ) = -ρ γ) →
      (∀ γ δ, iform (ρ γ) (ρ δ) = iform γ δ) → (∀ γ, IsRoot Tag.E8 γ → ρ (ρ γ) = -γ) →
      (∀ γ ∈ kernelRoots (rootCharHom a), ρ γ ∈ kernelRoots (rootCharHom a)) →
      ∀ i : KernelComponent (rootCharHom a), ¬ RCKExcShape ρ (componentRoots (rootCharHom a) i)

theorem rckExcOrbitFour_of_shape
    (hV : RCKExcShapeFour) : RCKExcOrbitFour := by
  intro f p hf hp hp2 hd Dl ρ hΦ hρ hcl S₁ S₂ hS hel htor hc₁ hc₂ iJ iK hsub hshape
  exfalso
  have hSt₂ : ∀ x ∈ S₂, Dl.g0⁻¹ * x * Dl.g0 ∈ Dl.torus := fun x hx => htor x (hS hx)
  obtain ⟨a, hpa, ha1, hker⟩ := rck_cyclic_kernel hp hc₂ hSt₂
  obtain ⟨j, hj⟩ := rck_component_transfer hker iK
  have hsq : ∀ γ, IsRoot Tag.E8 γ → ρ (ρ γ) = -γ := by
    intro γ hγ
    have h := hcl.2.2.1 ⟨rfl, Or.inr (Or.inl rfl)⟩ γ hγ
    have hc : rckChebC 4 = 0 := by simp [rckChebC]
    rw [hc, zero_smul] at h
    exact eq_neg_of_add_eq_zero_left h
  have hstab : ∀ γ ∈ kernelRoots (rootCharHom a), ρ γ ∈ kernelRoots (rootCharHom a) := by
    intro γ hγ
    rw [← hker] at hγ ⊢
    exact rck_kernel_stable hρ (fun x : S₂ => (x : ModGL (langTag .E8) GGL))
      (fun x => hSt₂ x x.2) hγ
  rw [hj] at hshape
  exact hV p hp hp2 a hpa ha1 ρ hρ.isRoot_iff hρ.neg_eq hρ.iform_eq hsq hstab j hshape

end CFSG.StandardType.RCKRP

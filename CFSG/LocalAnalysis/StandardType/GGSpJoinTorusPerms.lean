module

public import CFSG.LocalAnalysis.StandardType.GGSpJoinPlaneTorusLift
public import CFSG.LocalAnalysis.StandardType.GGSpJoinSignedPermGen

public section

namespace CFSG.StandardType.SpJoin

open CFSG.Open CFSG.LieType.Universal.Symplectic
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl Matrix

variable {G : Type} [Group G]

@[expose] def torusPerms (X Bs : Subgroup G) {V : Type} [Group V] (tor : V →* G) :
    Subgroup (Equiv.Perm V) where
  carrier := {h | ∃ g ∈ X ⊓ Subgroup.normalizer (Bs : Set G), ∀ a, g * tor a * g⁻¹ = tor (h a)}
  one_mem' := ⟨1, one_mem _, fun a => by simp⟩
  mul_mem' := by
    rintro h₁ h₂ ⟨g₁, hg₁, e₁⟩ ⟨g₂, hg₂, e₂⟩
    refine ⟨g₁ * g₂, mul_mem hg₁ hg₂, fun a => ?_⟩
    calc g₁ * g₂ * tor a * (g₁ * g₂)⁻¹ = g₁ * (g₂ * tor a * g₂⁻¹) * g₁⁻¹ := by group
      _ = g₁ * tor (h₂ a) * g₁⁻¹ := by rw [e₂]
      _ = tor (h₁ (h₂ a)) := e₁ _
  inv_mem' := by
    rintro h ⟨g, hg, e⟩
    refine ⟨g⁻¹, inv_mem hg, fun a => ?_⟩
    have h1 : g * tor (h⁻¹ a) * g⁻¹ = tor a := by
      have := e (h⁻¹ a)
      have hh : h (h⁻¹ a) = a := by simp
      rwa [hh] at this
    calc g⁻¹ * tor a * g⁻¹⁻¹ = g⁻¹ * (g * tor (h⁻¹ a) * g⁻¹) * g := by rw [h1, inv_inv]
      _ = tor (h⁻¹ a) := by group

theorem mem_torusPerms_iff {X Bs : Subgroup G} {V : Type} [Group V] {tor : V →* G}
    {h : Equiv.Perm V} :
    h ∈ torusPerms X Bs tor ↔
      ∃ g ∈ X ⊓ Subgroup.normalizer (Bs : Set G), ∀ a, g * tor a * g⁻¹ = tor (h a) :=
  Iff.rfl

theorem spSignedGroup_le_torusPerms {F : Type} [Field F] {p n : ℕ} (h2 : (2 : F) = 0)
    {Bs X : Subgroup G} {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F}
    {φ : StatedSp n F →* G} (h : IsPlaneTorusLift p Bs X ζ φ) :
    spSignedGroup n p ≤ torusPerms X Bs (φ.comp (spPlaneTorus n ζ)) := by
  unfold spSignedGroup
  rw [Subgroup.closure_le]
  rintro _ ⟨k, rfl⟩
  refine ⟨φ (weylRep n F k), ⟨?_, h.weyl_mem k⟩, fun a => ?_⟩
  · rw [← h.range_eq]
    exact ⟨_, rfl⟩
  · show φ (weylRep n F k) * φ (spPlaneTorus n ζ a) * (φ (weylRep n F k))⁻¹ =
      φ (spPlaneTorus n ζ (spRefl n p k a))
    rw [← map_inv, ← map_mul, ← map_mul, weylRep_conj_spPlaneTorus h2 ζ h.zeta_inv k a]

theorem two_pow_mul_factorial_le_card_ggAutomizer [Finite G] {F : Type} [Field F] {p n : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (h2 : (2 : F) = 0) {Bs X : Subgroup G}
    {ζ : Multiplicative (ZMod p) →* SpecialLinearGroup (Fin 2) F} {φ : StatedSp n F →* G}
    (h : IsPlaneTorusLift p Bs X ζ φ) :
    2 ^ n * n.factorial ≤ Nat.card (ggAutomizer X Bs) := by
  classical
  haveI : Finite (MulAut ↥Bs) :=
    Finite.of_injective (fun f : MulAut ↥Bs => (f : ↥Bs → ↥Bs)) DFunLike.coe_injective
  have hle := spSignedGroup_le_torusPerms h2 h
  have hex : ∀ q : spSignedGroup n p, ∃ g ∈ X ⊓ Subgroup.normalizer (Bs : Set G),
      ∀ a, g * (φ.comp (spPlaneTorus n ζ)) a * g⁻¹ = (φ.comp (spPlaneTorus n ζ)) (q.1 a) :=
    fun q => hle q.2
  choose g hg hgconj using hex
  let ψ : spSignedGroup n p → MulAut ↥Bs := fun q =>
    (Subgroup.normalizerMonoidHom (H := Bs)) ⟨g q, (hg q).2⟩
  have hψ : ∀ q (b : ↥Bs), ((ψ q b : ↥Bs) : G) = g q * b * (g q)⁻¹ := fun q b => rfl
  have hψmem : ∀ q, ψ q ∈ ggAutomizer X Bs := fun q =>
    Subgroup.subset_closure ⟨g q, (hg q).1, (hg q).2, hψ q⟩
  have htorBs : ∀ a, (φ.comp (spPlaneTorus n ζ)) a ∈ Bs := by
    intro a
    have hmem : (φ.comp (spPlaneTorus n ζ)) a ∈ (φ.comp (spPlaneTorus n ζ)).range := ⟨a, rfl⟩
    rw [h.torus_range] at hmem
    exact hmem.1
  have hinj : Function.Injective
      (fun q : spSignedGroup n p => (⟨ψ q, hψmem q⟩ : ggAutomizer X Bs)) := by
    intro q q' hqq
    have hψeq : ψ q = ψ q' := congrArg Subtype.val hqq
    apply Subtype.ext
    apply Equiv.ext
    intro a
    have key := congrArg (fun f : MulAut ↥Bs => ((f ⟨_, htorBs a⟩ : ↥Bs) : G)) hψeq
    simp only [hψ] at key
    rw [hgconj q a, hgconj q' a] at key
    exact h.torus_injective key
  exact (two_pow_mul_factorial_le_card_spSignedGroup hp hp2).trans
    (Nat.card_le_card_of_injective _ hinj)

theorem two_pow_mul_factorial_le_card_ggAutomizer_of_lift [Finite G] {F : Type} [Field F] [Finite F]
    {p n : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (h2 : (2 : F) = 0) (φ' : StatedSp n F →* G)
    (hinj : Function.Injective φ') {B Bs X : Subgroup G} (hBs : GGBstar p B Bs)
    (hrange : φ'.range = X) (hNK : Bs ≤ Subgroup.normalizer (X : Set G))
    (hinner : ∀ b ∈ Bs, ∃ x ∈ X, ∀ y ∈ X, b * y * b⁻¹ = x * y * x⁻¹)
    (hcent : Nat.card ↥(Bs ⊓ Subgroup.centralizer (X : Set G)) ≤ p)
    (hrank : p ^ (n + 1) ≤ Nat.card Bs) :
    2 ^ n * n.factorial ≤ Nat.card (ggAutomizer X Bs) := by
  obtain ⟨ζ, φ, hl⟩ :=
    CFSG.StandardType.exists_plane_torus_lift_of_range hp hp2 h2 φ' hinj hBs hrange hNK hinner hcent
      hrank
  exact two_pow_mul_factorial_le_card_ggAutomizer hp hp2 h2 hl

end CFSG.StandardType.SpJoin

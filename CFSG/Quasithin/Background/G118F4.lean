module

public import CFSG.Quasithin.Background.G118F2
public import CFSG.Quasithin.Background.G118Inputs
public import CFSG.Quasithin.Background.E11Aux
public import CFSG.Quasithin.Background.G116IIIFStar
public import CFSG.Quasithin.Background.G118Alt

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Assembly.LowTwoRank

namespace G11

namespace G118

section F4Basic

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V} {X X₀ L : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

omit [Finite V] in
theorem finrank_eq_two_of_card_four {H : Subgroup (GLV V)} (D : E11Data H I)
    (hF : Nat.card D.F = 4) : Module.finrank (ZMod 2) D.F = 2 := by
  have h := Module.natCard_eq_pow_finrank (K := ZMod 2) (V := D.F)
  rw [hF, Nat.card_zmod] at h
  have h4 : (4 : ℕ) = 2 ^ 2 := by norm_num
  rw [h4] at h
  exact (Nat.pow_right_injective (le_refl 2) h).symm

omit [Finite V] in
theorem exists_semilinear_field_type {H : Subgroup (GLV V)} (D : E11Data H I)
    (hHI : Invariant H I) {g : GLV V} (hg : g ∈ Subgroup.normalizer (H : Set (GLV V)))
    (hgI : conjSub g I = I)
    (hnc : ¬ ∀ f : D.F, (g : Module.End (ZMod 2) V) * D.κ f =
      D.κ f * (g : Module.End (ZMod 2) V)) :
    ∃ (τ : D.F ≃+* D.F) (σ : D.U →ₛₗ[(τ : D.F →+* D.F)] D.U) (hσ : Function.Bijective σ),
      τ ≠ RingEquiv.refl D.F ∧ ActsOnPoints D.ψ g (Projectivization.map σ hσ.1) ∧
      ∀ c c' : Subgroup.centralizer (H : Set (GLV V)),
        (c' : GLV V) * g = g * c → ∀ u : D.U, D.θ c' (σ u) = σ (D.θ c u) := by
  obtain ⟨τ, σ, hσ, hact, hcompat⟩ := D.semilinear g hg
  refine ⟨τ, σ, hσ, ?_, hact, hcompat⟩
  intro hτ
  apply hnc
  refine (D.comm_kappa_iff hHI hg hgI).2
    ((D.tau_eq_one_iff hHI hg hgI τ σ hσ hcompat).1 fun f => ?_)
  rw [hτ]
  rfl

omit [Finite V] in
theorem map_semilinear_sq {H : Subgroup (GLV V)} (D : E11Data H I) {g : GLV V}
    (hg2 : g * g = 1) {τ : D.F ≃+* D.F} {σ : D.U →ₛₗ[(τ : D.F →+* D.F)] D.U}
    (hσ : Function.Bijective σ) (hact : ActsOnPoints D.ψ g (Projectivization.map σ hσ.1))
    (p : Projectivization D.F D.U) :
    Projectivization.map σ hσ.1 (Projectivization.map σ hσ.1 p) = p := by
  obtain ⟨⟨J, hJ⟩, rfl⟩ := D.ψ.surjective p
  obtain ⟨hJ', h1⟩ := hact J hJ
  obtain ⟨hJ'', h2⟩ := hact (conjSub g J) hJ'
  have hcc : conjSub g (conjSub g J) = J := by rw [← conjSub_mul, hg2, conjSub_one]
  rw [← h1, ← h2]
  congr 1
  exact Subtype.ext hcc

section Hat

variable {H : Subgroup (GLV V)}

omit [Finite V] in
theorem noNormalTwo_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : ∀ N : Subgroup B, N.Normal → IsPGroup 2 N → N = ⊥) :
    ∀ N : Subgroup A, N.Normal → IsPGroup 2 N → N = ⊥ := by
  intro N hN hp
  have hN' : (N.map e.toMonoidHom).Normal := Subgroup.Normal.map hN e.toMonoidHom e.surjective
  have hp' : IsPGroup 2 ↥(N.map e.toMonoidHom) :=
    hp.of_surjective (e.subgroupMap N).toMonoidHom (e.subgroupMap N).surjective
  have := h _ hN' hp'
  exact (Subgroup.map_eq_bot_iff_of_injective N e.injective).1 this

omit [Finite V] in
@[expose] noncomputable def centHat (D : E11Data H I) (Γ : Subgroup (GLV V)) :
    Subgroup (D.U ≃ₗ[D.F] D.U) :=
  ((centΓ Γ H).subgroupOf (Subgroup.centralizer (H : Set (GLV V)))).map D.θ.toMonoidHom

omit [Finite V] in
theorem mem_centHat_iff (D : E11Data H I) {Γ : Subgroup (GLV V)} {c : D.U ≃ₗ[D.F] D.U} :
    c ∈ centHat D Γ ↔ ∃ ĉ : ↥(Subgroup.centralizer (H : Set (GLV V))),
      (ĉ : GLV V) ∈ centΓ Γ H ∧ D.θ ĉ = c := by
  unfold centHat
  simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]

omit [Finite V] in
theorem centΓ_le_centralizer {Γ : Subgroup (GLV V)} :
    centΓ Γ H ≤ Subgroup.centralizer (H : Set (GLV V)) := inf_le_right

omit [Finite V] in
noncomputable def centHatEquiv (D : E11Data H I) (Γ : Subgroup (GLV V)) :
    ↥(centHat D Γ) ≃* ↥(centΓ Γ H) :=
  (MulEquiv.subgroupMap D.θ _).symm.trans (Subgroup.subgroupOfEquivOfLe centΓ_le_centralizer)

end Hat

section Scalar

theorem scalar_case {F U : Type} [Field F] [Finite F] [AddCommGroup U] [Module F U]
    (hF : Nat.card F = 4) [Nontrivial U] {ζ c : U ≃ₗ[F] U} (hζs : IsScalarAut ζ)
    (hc3 : c * c * c = 1) (hcs : ¬ IsScalarAut c) :
    ζ ^ 3 = 1 ∧ c ^ 3 = 1 ∧ c ≠ 1 ∧ c ≠ ζ ∧ c ≠ ζ ^ 2 ∧ ζ * c = c * ζ := by
  obtain ⟨a, ha⟩ := hζs
  have ha0 : a ≠ 0 := by
    intro h0
    obtain ⟨u, hu⟩ := exists_ne (0 : U)
    apply hu
    apply ζ.injective
    rw [ha, h0, zero_smul, map_zero]
  have ha3 : a ^ 3 = 1 := by
    let _ : Fintype F := Fintype.ofFinite F
    have h := FiniteField.pow_card_sub_one_eq_one a ha0
    rwa [← Nat.card_eq_fintype_card, hF] at h
  have hmul : ∀ (g h : U ≃ₗ[F] U) (u : U), (g * h) u = g (h u) := fun g h u => rfl
  have hsq : ∀ u : U, (ζ ^ 2) u = (a * a) • u := fun u => by
    rw [pow_two, hmul, ha, ha, smul_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · ext u
    have h3 : (ζ ^ 3) u = ζ ((ζ ^ 2) u) := by rw [pow_succ', hmul]
    have h3' : a * a * a = 1 := by rw [← pow_three']; exact ha3
    rw [h3, hsq, map_smul, ha, smul_smul, h3', one_smul]
    rfl
  · have : c ^ 3 = c * c * c := by simp [pow_succ]
    rw [this, hc3]
  · intro h
    exact hcs ⟨1, fun u => by rw [h]; simp⟩
  · intro h
    exact hcs ⟨a, fun u => by rw [h, ha]⟩
  · intro h
    exact hcs ⟨a * a, fun u => by rw [h, hsq]⟩
  · ext u
    rw [hmul, hmul, ha, ha u, map_smul]

end Scalar

section Dichotomy

omit [Finite V] in
theorem mem_normalizer_of_normal {Γ H : Subgroup (GLV V)}
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) {γ : GLV V} (hγ : γ ∈ Γ) :
    γ ∈ Subgroup.normalizer (H : Set (GLV V)) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  refine ⟨fun hh => hN γ hγ h hh, fun hh => ?_⟩
  have := hN γ⁻¹ (Γ.inv_mem hγ) _ hh
  simpa [mul_assoc] using this

end Dichotomy

section A5

variable {G : Type*} [Group G]

theorem center_eq_bot_of_mulEquiv_alt_five (e : G ≃* ↥(alternatingGroup (Fin 5))) :
    Subgroup.center G = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  have h1 : e x ∈ Subgroup.center ↥(alternatingGroup (Fin 5)) := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨z, rfl⟩ := e.surjective y
    rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.1 hx z]
  rw [g118_center_alt_five, Subgroup.mem_bot] at h1
  rw [Subgroup.mem_bot]
  exact e.injective (h1.trans (map_one e).symm)

theorem isQuasisimple_of_mulEquiv_alt_five (e : G ≃* ↥(alternatingGroup (Fin 5))) :
    CFSG.Open.IsQuasisimple G := by
  have hsimp : IsSimpleGroup ↥(alternatingGroup (Fin 5)) :=
    alternatingGroup.isSimpleGroup (by simp)
  have : IsSimpleGroup G := e.isSimpleGroup
  have hcenter := center_eq_bot_of_mulEquiv_alt_five e
  refine ⟨?_, ?_⟩
  · rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator G) with h | h
    · exfalso
      have h1 : Subgroup.center G = ⊤ := (commutator_eq_bot_iff_center_eq_top G).1 h
      rw [hcenter] at h1
      have : Nontrivial G := e.toEquiv.nontrivial
      exact bot_ne_top h1
    · exact h
  · let coord : (G ⧸ Subgroup.center G) ≃* G :=
      (QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot
    exact coord.isSimpleGroup

end A5

section FStar

omit [Finite V] in
theorem centralizer_comm_kappa {H : Subgroup (GLV V)} (D : E11Data H I) {c : GLV V}
    (hc : c ∈ Subgroup.centralizer (H : Set (GLV V))) (f : D.F) :
    (c : Module.End (ZMod 2) V) * D.κ f = D.κ f * (c : Module.End (ZMod 2) V) := by
  have hcN : c ∈ Subgroup.normalizer (H : Set (GLV V)) :=
    Subgroup.centralizer_le_normalizer _ hc
  have := D.κ_conj c hcN (RingEquiv.refl D.F) (D.θ ⟨c, hc⟩ : D.U →ₗ[D.F] D.U)
    (D.θ ⟨c, hc⟩).bijective (fun c₁ c₂ h u => ?_) f
  · simpa using this
  · have h' : c₂ * ⟨c, hc⟩ = ⟨c, hc⟩ * c₁ := Subtype.ext h
    have := congrArg (fun z => D.θ z u) h'
    rw [map_mul, map_mul] at this
    exact this

omit [Finite V] in
theorem isComponentOf_of_normal_alt_five {Γ K : Subgroup (GLV V)} (hKΓ : K ≤ Γ)
    (hN : ∀ γ ∈ Γ, ∀ k ∈ K, γ * k * γ⁻¹ ∈ K) (e : ↥K ≃* ↥(alternatingGroup (Fin 5))) :
    CFSG.Open.IsComponentOf K Γ := by
  refine ⟨hKΓ, CFSG.Open.IsSubnormal.step hKΓ ?_ (CFSG.Open.IsSubnormal.refl Γ),
    isQuasisimple_of_mulEquiv_alt_five e⟩
  refine ⟨fun n hn g => ?_⟩
  have hn' : (n : GLV V) ∈ K := hn
  exact hN g g.2 n hn'

theorem fstar_map_eq_of_alt_five {Γ H : Subgroup (GLV V)} (hHΓ : H ≤ Γ)
    (hN : ∀ γ ∈ Γ, ∀ h ∈ H, γ * h * γ⁻¹ ∈ H) (φ : ↥H ≃* ↥(alternatingGroup (Fin 5)))
    (e : ↥(centΓ Γ H) ≃* ↥(alternatingGroup (Fin 5))) :
    (CFSG.Open.genFittingFStar ↥Γ).map Γ.subtype = H ⊔ centΓ Γ H := by
  have hCΓ : centΓ Γ H ≤ Γ := inf_le_left
  have hHcomp := isComponentOf_of_normal_alt_five hHΓ hN φ
  have hCcomp := isComponentOf_of_normal_alt_five hCΓ (centΓ_conj hN) e
  have hA := (isComponentOf_iff_subgroupOf.1 hHcomp).2
  have hB := (isComponentOf_iff_subgroupOf.1 hCcomp).2
  have hC' : ∀ g : ↥Γ, (∀ a ∈ H.subgroupOf Γ, g * a = a * g) →
      (∀ b ∈ (centΓ Γ H).subgroupOf Γ, g * b = b * g) → g = 1 := by
    intro g hgA hgB
    have hgC : (g : GLV V) ∈ centΓ Γ H := mem_centΓ_iff.2 ⟨g.2, fun h hh => by
      have := hgA ⟨h, hHΓ hh⟩ (by simpa [Subgroup.mem_subgroupOf] using hh)
      exact (congrArg Subtype.val this).symm⟩
    have hz : (⟨(g : GLV V), hgC⟩ : ↥(centΓ Γ H)) ∈ Subgroup.center ↥(centΓ Γ H) := by
      rw [Subgroup.mem_center_iff]
      intro c
      have := hgB ⟨(c : GLV V), hCΓ c.2⟩ (by simp [Subgroup.mem_subgroupOf])
      exact Subtype.ext (congrArg Subtype.val this).symm
    rw [center_eq_bot_of_mulEquiv_alt_five e, Subgroup.mem_bot] at hz
    have h1 : ((⟨(g : GLV V), hgC⟩ : ↥(centΓ Γ H)) : GLV V) = 1 := congrArg Subtype.val hz
    exact Subtype.ext h1
  rw [genFittingFStar_eq_sup_of_components hA hB hC', Subgroup.map_sup,
    Subgroup.map_subgroupOf_eq_of_le hHΓ, Subgroup.map_subgroupOf_eq_of_le hCΓ]

end FStar

end F4Basic

end G118

end G11

end CFSG.Quasithin

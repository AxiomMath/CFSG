module

public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeKerMod
public import CFSG.LocalAnalysis.WeakClosure81.SevenSixThreeLiftTwo

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Subgroup
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]
variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem PInvol.map {G' : Type*} [Group G'] (f : G →* G') {p : ℕ} {Q : Subgroup G} {u : G}
    (h : PInvol p Q u) : PInvol p (Q.map f) (f u) := by
  refine ⟨h.prime, h.odd, ?_, ?_, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, h.exp x hx, map_one]
  · rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩ _ ⟨z, hz, rfl⟩
    rw [← map_commutatorElement f x y, ← map_commutatorElement f ⁅x, y⁆ z,
      h.class_two x hx y hy z hz, map_one]
  · rw [← map_mul, h.sq_eq_one, map_one]
  · rw [Subgroup.mem_normalizer_iff]
    intro g
    constructor
    · rintro ⟨x, hx, rfl⟩
      refine ⟨u * x * u⁻¹, ?_, ?_⟩
      · exact (Subgroup.mem_normalizer_iff.mp h.mem_normalizer x).mp hx
      · rw [map_mul, map_mul, map_inv]
    · rintro ⟨x, hx, hxeq⟩
      refine ⟨u⁻¹ * x * u, ?_, ?_⟩
      · have hm := (Subgroup.mem_normalizer_iff.mp h.mem_normalizer) (u⁻¹ * x * u)
        rw [show u * (u⁻¹ * x * u) * u⁻¹ = x by group] at hm
        exact hm.mpr hx
      · rw [map_mul, map_mul, map_inv, hxeq]
        group
  · intro y hy
    obtain ⟨x, hx, rfl⟩ := hy
    have hx' : f x ∈ (⁅Q, Subgroup.zpowers u⁆).map f := ⟨x, h.le_commutator hx, rfl⟩
    simpa only [Subgroup.map_commutator, MonoidHom.map_zpowers] using hx'

theorem PInvol.card_main_of_irreducible (ρ : Representation (ZMod 2) G W) {p : ℕ}
    {Q : Subgroup G} {u : G} (h : PInvol p Q u) (hQ : Q ≠ ⊥)
    (hirr : ∀ W' : Submodule (ZMod 2) W, (∀ x ∈ Q, ∀ w ∈ W', ρ x w ∈ W') →
      (∀ w ∈ W', ρ u w ∈ W') → W' = ⊥ ∨ W' = ⊤)
    (hW : Nontrivial W) (hne : traceSpace ρ u ≠ ⊥)
    (hTI : ∀ y ∈ Q, traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ y) ≠ ⊥ → y * u = u * y) :
    Nat.card Q = p ∨ (Nat.card Q = p ^ 3 ∧ ∃ x ∈ Q, ∃ y ∈ Q, ⁅x, y⁆ ≠ 1) := by
  haveI : Finite (W →ₗ[ZMod 2] W) :=
    Finite.of_injective (DFunLike.coe : (W →ₗ[ZMod 2] W) → W → W) DFunLike.coe_injective
  haveI : Finite (W →ₗ[ZMod 2] W)ˣ := Finite.of_injective _ Units.val_injective
  let γ : G →* (W →ₗ[ZMod 2] W)ˣ := ρ.asGroupHom
  let ρ' : Representation (ZMod 2) (W →ₗ[ZMod 2] W)ˣ W := Units.coeHom (W →ₗ[ZMod 2] W)
  have hγ : ∀ g : G, (γ g : W →ₗ[ZMod 2] W) = ρ g := fun g =>
    Representation.asGroupHom_apply ρ g
  have hMap : PInvol p (Q.map γ) (γ u) := PInvol.map γ h
  have htrace : ∀ x : G, traceSpace ρ' (γ x) = traceSpace ρ x := by
    intro x
    unfold traceSpace
    rw [show ρ' (γ x) = ρ x from by
      change (Units.coeHom (W →ₗ[ZMod 2] W)) (γ x) = ρ x
      rw [Units.coeHom_apply, hγ x]]
  have hmap : ∀ x : G,
      (traceSpace ρ' (γ u)).map (ρ' (γ x)) = (traceSpace ρ u).map (ρ x) := by
    intro x
    rw [htrace u]
    rw [show ρ' (γ x) = ρ x from by
      change (Units.coeHom (W →ₗ[ZMod 2] W)) (γ x) = ρ x
      rw [Units.coeHom_apply, hγ x]]
  have hQmap : Q.map γ ≠ ⊥ := by
    intro hbot
    have hγ1 : ∀ y ∈ Q, ρ.asGroupHom y = 1 := by
      intro y hy
      have hy' : γ y ∈ Q.map γ := ⟨y, hy, rfl⟩
      rw [hbot] at hy'
      simpa using hy'
    have hcomm : ∀ y ∈ Q, y * u = u * y := by
      intro y hy
      have hρy : ρ y = 1 := by
        have h1 := Representation.asGroupHom_apply ρ y
        rw [hγ1 y hy] at h1
        simpa using h1.symm
      refine hTI y hy ?_
      have htr : traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ y) = traceSpace ρ u := by
        rw [hρy, Module.End.one_eq_id, Submodule.map_id, inf_idem]
      rw [htr]
      exact hne
    have hbot' : ⁅Q, Subgroup.zpowers u⁆ = ⊥ := by
      rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
      intro y hy
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hv
      exact ((show Commute y u from hcomm y hy).zpow_right k).symm.eq
    have hle := h.le_commutator
    rw [hbot'] at hle
    exact hQ (le_bot_iff.mp hle)
  have hirr' : ∀ W' : Submodule (ZMod 2) W,
      (∀ x ∈ Q.map γ, ∀ w ∈ W', ρ' x w ∈ W') → (∀ w ∈ W', ρ' (γ u) w ∈ W') →
      W' = ⊥ ∨ W' = ⊤ := by
    intro W' hQ' hu'
    refine hirr W' ?_ ?_
    · intro x hx w hw
      have h' := hQ' (γ x) ⟨x, hx, rfl⟩ w hw
      change (Units.coeHom (W →ₗ[ZMod 2] W) (γ x)) w ∈ W' at h'
      rw [Units.coeHom_apply, hγ x] at h'
      exact h'
    · intro w hw
      have h' := hu' w hw
      change (Units.coeHom (W →ₗ[ZMod 2] W) (γ u)) w ∈ W' at h'
      rw [Units.coeHom_apply, hγ u] at h'
      exact h'
  have hTI' : ∀ y ∈ Q.map γ,
      traceSpace ρ' (γ u) ⊓ (traceSpace ρ' (γ u)).map (ρ' y) ≠ ⊥ → y * γ u = γ u * y := by
    rintro y ⟨z, hz, rfl⟩ hy
    have hy' : traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ z) ≠ ⊥ := by
      rw [← hmap z, ← htrace u]
      exact hy
    rw [← map_mul, ← map_mul, hTI z hz hy']
  have hinj : Function.Injective ρ' := fun a b hab => Units.ext hab
  have hmain : Nat.card (Q.map γ) = p ∨ (Nat.card (Q.map γ) = p ^ 3 ∧
      ∃ x ∈ Q.map γ, ∃ y ∈ Q.map γ, ⁅x, y⁆ ≠ 1) :=
    PInvol.card_main_of_faithful ρ' hinj hMap hQmap hirr' hW hTI'
  have hNcomm : ∀ n ∈ γ.ker ⊓ Q, u * n = n * u := by
    intro n hn
    obtain ⟨hnker, hnQ⟩ := Subgroup.mem_inf.mp hn
    have hγn : γ n = 1 := MonoidHom.mem_ker.mp hnker
    have hρn : ρ n = 1 := by
      have h1 := Representation.asGroupHom_apply ρ n
      have hγn' : ρ.asGroupHom n = 1 := hγn
      rw [hγn'] at h1
      simpa using h1.symm
    refine (hTI n hnQ ?_).symm
    have htr : traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ n) = traceSpace ρ u := by
      rw [hρn, Module.End.one_eq_id, Submodule.map_id, inf_idem]
    rw [htr]
    exact hne
  have hrel : (γ.ker ⊓ Q).relIndex Q = Nat.card (Q.map γ) := by
    rw [Subgroup.inf_relIndex_right, Subgroup.relIndex_ker]
  have hQN : (γ.ker ⊓ Q).relIndex Q = p ∨ ((γ.ker ⊓ Q).relIndex Q = p ^ 3 ∧
      ∃ x ∈ Q, ∃ y ∈ Q, ⁅x, y⁆ ∉ γ.ker ⊓ Q) := by
    rcases hmain with hcard | ⟨hcard, x, hx, y, hy, hxy⟩
    · left
      rw [hrel, hcard]
    · right
      refine ⟨by rw [hrel, hcard], ?_⟩
      rcases hx with ⟨x', hx'Q, rfl⟩
      rcases hy with ⟨y', hy'Q, rfl⟩
      refine ⟨x', hx'Q, y', hy'Q, ?_⟩
      intro hmem
      have hker : ⁅x', y'⁆ ∈ γ.ker := (Subgroup.mem_inf.mp hmem).1
      have h1 : γ ⁅x', y'⁆ = 1 := MonoidHom.mem_ker.mp hker
      rw [map_commutatorElement] at h1
      exact hxy h1
  have hNbot : γ.ker ⊓ Q = ⊥ := PInvol.eq_bot_of_relIndex h inf_le_right hNcomm hQN
  have hcardQ : Nat.card Q = Nat.card (Q.map γ) := by
    rw [← hrel, hNbot, Subgroup.relIndex_bot_left]
  rcases hmain with hcard | ⟨hcard, x, hx, y, hy, hxy⟩
  · left
    rw [hcardQ, hcard]
  · right
    refine ⟨by rw [hcardQ, hcard], ?_⟩
    rcases hx with ⟨x', hx'Q, rfl⟩
    rcases hy with ⟨y', hy'Q, rfl⟩
    refine ⟨x', hx'Q, y', hy'Q, ?_⟩
    intro hcomm1
    apply hxy
    rw [← map_commutatorElement γ x' y', hcomm1, map_one]

theorem PInvol.card_main_of_rep (ρ : Representation (ZMod 2) G W) {p : ℕ} {Q : Subgroup G}
    {u : G} (h : PInvol p Q u) (hgen : Q ⊔ Subgroup.zpowers u = ⊤) (hQ : Q ≠ ⊥)
    (hne : traceSpace ρ u ≠ ⊥)
    (hTI : ∀ y ∈ Q, traceSpace ρ u ⊓ (traceSpace ρ u).map (ρ y) ≠ ⊥ → y * u = u * y) :
    Nat.card Q = p ∨ (Nat.card Q = p ^ 3 ∧ ∃ x ∈ Q, ∃ y ∈ Q, ⁅x, y⁆ ≠ 1) := by
  obtain ⟨W₂, hW₂, hnt, hirr, hne', hTI'⟩ :=
    PInvol.exists_irreducible_restriction ρ h hgen hQ hne hTI
  exact PInvol.card_main_of_irreducible (restrictRep ρ W₂ hW₂) h hQ hirr hnt hne' hTI'

end CFSG.LocalAnalysis.WeakClosure81

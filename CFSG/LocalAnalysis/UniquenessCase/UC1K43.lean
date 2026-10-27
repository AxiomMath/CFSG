module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.TwoDimensionalOddOrder
public import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
public import CFSG.LocalAnalysis.UniquenessCase.UC1K462Basic
public import CFSG.LocalAnalysis.UniquenessCase.UC1S4Defs462
public import CFSG.LocalAnalysis.UniquenessCase.UCInspL2Abs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open Subgroup
open scoped MatrixGroups

@[expose] def K43 : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 2 < p → ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      (ρ : Representation (ZMod p) G V), Function.Injective ρ →
    ∀ D : Subgroup G, Nat.card D = 3 → fixV ρ D = ⊥ →
    ∀ T : Subgroup G, IsPGroup 2 T → T ≠ ⊥ → D ≤ normalizer (T : Set G) → ⁅D, T⁆ = T →
      IsCyclic ↥(Subgroup.center ↥T) →
      Nonempty (↥T ≃* QuaternionGroup 2) ∧ Nonempty (↥(T ⊔ D) ≃* SL(2, ZMod 3))

@[expose] def K43Gen : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 2 < p → ∀ (G : Type) [Group G] [Finite G], CFSG.Open.IsKGroup G →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Finite V]
      (ρ : Representation (ZMod p) G V), Function.Injective ρ →
    ∀ D : Subgroup G, Nat.card D = 3 → fixV ρ D = ⊥ →
    ∀ T : Subgroup G, IsPGroup 2 T → D ≤ normalizer (T : Set G) → ⁅D, T⁆ = T →
    ∀ W : Submodule (ZMod p) V, (∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) →
      (∀ W' : Submodule (ZMod p) V, W' ≤ W → (∀ g ∈ T ⊔ D, ∀ w ∈ W', ρ g w ∈ W') →
        W' = ⊥ ∨ W' = W) →
      (∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) →
      (∃ φ : ↥T →* QuaternionGroup 2, Function.Surjective φ ∧
        ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W, ρ t w = w) ∧
      (∃ ψ : ↥(T ⊔ D) →* SL(2, ZMod 3), Function.Surjective ψ ∧
        ∀ g : ↥(T ⊔ D), ψ g = 1 ↔ ∀ w ∈ W, ρ g w = w)

namespace K43.Gen

open scoped commutatorElement

variable {p : ℕ} [Fact p.Prime] {G : Type} [Group G] [Finite G]
  {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Finite V]
  {ρ : Representation (ZMod p) G V} {D T : Subgroup G} {W : Submodule (ZMod p) V}

instance finiteLinearEquiv [Finite W] : Finite (W ≃ₗ[ZMod p] W) :=
  Finite.of_injective (fun e : W ≃ₗ[ZMod p] W => (e : W → W))
    (fun a b h => LinearEquiv.ext fun w => congrFun h w)

@[expose] noncomputable def act (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    ↥(T ⊔ D) →* (W ≃ₗ[ZMod p] W) where
  toFun g := LinearEquiv.ofLinearMap
    ((ρ (g : G)).restrict fun x hx => hWin (g : G) g.2 x hx)
    ((ρ (((g⁻¹ : ↥(T ⊔ D)) : G))).restrict fun x hx => hWin _ (g⁻¹).2 x hx)
    (by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.restrict_apply, LinearMap.id_apply]
      rw [← Module.End.mul_apply, ← map_mul]
      simp)
    (by
      ext x
      simp only [LinearMap.comp_apply, LinearMap.restrict_apply, LinearMap.id_apply]
      rw [← Module.End.mul_apply, ← map_mul]
      simp)
  map_one' := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    simp
  map_mul' g h := by
    apply LinearEquiv.ext
    intro x
    apply Subtype.ext
    simp only [LinearEquiv.coe_ofLinearMap, LinearEquiv.mul_apply, LinearMap.restrict_apply,
      Subtype.coe_mk]
    change (ρ (↑g * ↑h)) ↑x = (ρ ↑g) ((ρ ↑h) ↑x)
    rw [map_mul, Module.End.mul_apply]

@[expose] noncomputable def rhoHat (act : ↥(T ⊔ D) →* (W ≃ₗ[ZMod p] W)) :
    Representation (ZMod p) ↥(act.range) W where
  toFun x := (x : W ≃ₗ[ZMod p] W).toLinearMap
  map_one' := by ext; rfl
  map_mul' := by intro x y; ext; rfl

@[simp] theorem act_apply (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) (g : ↥(T ⊔ D))
    (w : W) : ((act hWin g w : W) : V) = ρ (g : G) (w : V) := rfl

@[simp] theorem rhoHat_apply (act : ↥(T ⊔ D) →* (W ≃ₗ[ZMod p] W)) (x : ↥(act.range))
    (w : W) : rhoHat act x w = (x : W ≃ₗ[ZMod p] W) w := rfl

theorem rhoHat_injective (act : ↥(T ⊔ D) →* (W ≃ₗ[ZMod p] W)) :
    Function.Injective (rhoHat act) := by
  intro x y h
  apply Subtype.ext
  apply LinearEquiv.ext
  intro w
  have hw := congrArg (fun f : W →ₗ[ZMod p] W => f w) h
  simpa using hw

theorem nontrivial_subrepresentation_rhoHat (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (htw : ∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) :
    Nontrivial (Subrepresentation (rhoHat (act hWin))) := by
  obtain ⟨t, ht, w, hw, hne⟩ := htw
  refine ⟨⊥, ⊤, ?_⟩
  intro h
  have h2 : (⊥ : Submodule (ZMod p) W) = ⊤ :=
    congrArg Subrepresentation.toSubmodule h
  have hw0 : (⟨w, hw⟩ : W) = 0 := by
    have : (⟨w, hw⟩ : W) ∈ (⊥ : Submodule (ZMod p) W) := by rw [h2]; trivial
    simpa using this
  have hw0' : w = 0 := by simpa using congrArg (fun x : W => (x : V)) hw0
  exact hne (by rw [hw0']; simp)

theorem isIrreducible_rhoHat (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (hWirr : ∀ W' : Submodule (ZMod p) V, W' ≤ W →
      (∀ g ∈ T ⊔ D, ∀ w ∈ W', ρ g w ∈ W') → W' = ⊥ ∨ W' = W)
    (htw : ∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) :
    (rhoHat (act hWin)).IsIrreducible := by
  classical
  haveI : Nontrivial (Subrepresentation (rhoHat (act hWin))) :=
    nontrivial_subrepresentation_rhoHat hWin htw
  refine ⟨fun S => ?_⟩
  have hinv : ∀ g ∈ T ⊔ D, ∀ w ∈ S.toSubmodule.map W.subtype,
      ρ g w ∈ S.toSubmodule.map W.subtype := by
    rintro g hg w ⟨s, hs, rfl⟩
    refine ⟨rhoHat (act hWin) ((act hWin).rangeRestrict ⟨g, hg⟩) s,
      S.apply_mem_toSubmodule _ hs, ?_⟩
    simp
  have hle : S.toSubmodule.map W.subtype ≤ W := by
    rintro x ⟨s, hs, rfl⟩
    exact s.2
  rcases hWirr _ hle hinv with hbot | htop
  · left
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [hbot]
    exact (Submodule.map_bot W.subtype).symm
  · right
    apply Subrepresentation.toSubmodule_injective
    apply Submodule.map_injective_of_injective W.injective_subtype
    rw [htop]
    exact (Submodule.map_subtype_top W).symm

noncomputable abbrev Ghat (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    Subgroup (W ≃ₗ[ZMod p] W) :=
  (act hWin).range

noncomputable abbrev fT (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    ↥T →* ↥(Ghat hWin) :=
  (act hWin).rangeRestrict.comp (Subgroup.inclusion (le_sup_left : T ≤ T ⊔ D))

noncomputable abbrev fD (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    ↥D →* ↥(Ghat hWin) :=
  (act hWin).rangeRestrict.comp (Subgroup.inclusion (le_sup_right : D ≤ T ⊔ D))

noncomputable abbrev That (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    Subgroup ↥(Ghat hWin) :=
  (fT hWin).range

noncomputable abbrev Dhat (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    Subgroup ↥(Ghat hWin) :=
  (fD hWin).range

noncomputable abbrev Zmap (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    Subgroup ↥(Ghat hWin) :=
  (Subgroup.center ↥(That hWin)).map (That hWin).subtype

noncomputable abbrev A (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    Subgroup ↥(Ghat hWin) :=
  ⁅Zmap hWin, Dhat hWin⁆

theorem rangeRestrict_eq_one_iff (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (u : ↥(T ⊔ D)) :
    (act hWin).rangeRestrict u = 1 ↔ ∀ w ∈ W, ρ (u : G) w = w := by
  constructor
  · intro h w hw
    have h2 : act hWin u = 1 := by
      simpa using congrArg (fun x : ↥(Ghat hWin) => (x : W ≃ₗ[ZMod p] W)) h
    have h3 : act hWin u ⟨w, hw⟩ = ⟨w, hw⟩ := by
      simpa using congrArg (fun e : W ≃ₗ[ZMod p] W => e ⟨w, hw⟩) h2
    simpa using congrArg (fun x : W => (x : V)) h3
  · intro h
    apply Subtype.ext
    apply LinearEquiv.ext
    intro w
    apply Subtype.ext
    simpa using h w w.2

theorem that_eq_map (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    That hWin = (T.subgroupOf (T ⊔ D)).map (act hWin).rangeRestrict := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hx
    refine show fT hWin t ∈ (T.subgroupOf (T ⊔ D)).map (act hWin).rangeRestrict from
      Subgroup.mem_map.mpr ⟨Subgroup.inclusion (le_sup_left : T ≤ T ⊔ D) t, ?_, rfl⟩
    exact (Subgroup.mem_subgroupOf).mpr t.2
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    refine MonoidHom.mem_range.mpr ⟨⟨u.1, hu⟩, ?_⟩
    exact congrArg (act hWin).rangeRestrict
      (show Subgroup.inclusion le_sup_left ⟨u.1, hu⟩ = u from Subtype.ext rfl)

theorem dhat_eq_map (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    Dhat hWin = (D.subgroupOf (T ⊔ D)).map (act hWin).rangeRestrict := by
  ext x
  constructor
  · intro hx
    obtain ⟨t, rfl⟩ := MonoidHom.mem_range.mp hx
    refine show fD hWin t ∈ (D.subgroupOf (T ⊔ D)).map (act hWin).rangeRestrict from
      Subgroup.mem_map.mpr ⟨Subgroup.inclusion (le_sup_right : D ≤ T ⊔ D) t, ?_, rfl⟩
    exact (Subgroup.mem_subgroupOf).mpr t.2
  · intro hx
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hx
    refine MonoidHom.mem_range.mpr ⟨⟨u.1, hu⟩, ?_⟩
    exact congrArg (act hWin).rangeRestrict
      (show Subgroup.inclusion le_sup_right ⟨u.1, hu⟩ = u from Subtype.ext rfl)

theorem sup_eq_top (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    That hWin ⊔ Dhat hWin = ⊤ := by
  have hsup : T.subgroupOf (T ⊔ D) ⊔ D.subgroupOf (T ⊔ D) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right, Subgroup.subgroupOf_self]
  rw [that_eq_map hWin, dhat_eq_map hWin, ← Subgroup.map_sup, hsup, Subgroup.map_top,
    MonoidHom.range_eq_top_of_surjective (act hWin).rangeRestrict
      (MonoidHom.rangeRestrict_surjective (act hWin))]

theorem that_isPGroup (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) (hT2 : IsPGroup 2 T) :
    IsPGroup 2 (That hWin) := by
  change IsPGroup 2 (fT hWin).range
  exact hT2.of_surjective (fT hWin).rangeRestrict (fT hWin).rangeRestrict_surjective

theorem dhat_ker (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) (hD3 : Nat.card D = 3)
    (hDfix : fixV ρ D = ⊥) (hWne : W ≠ ⊥) :
    ∀ d : ↥D, fD hWin d = 1 → d = 1 := by
  intro d hd
  by_contra hne
  have hfix : ∀ w : W, ρ (d : G) (w : V) = (w : V) := fun w =>
    (rangeRestrict_eq_one_iff hWin (Subgroup.inclusion le_sup_right d)).mp
      (by simpa [fD] using hd) w w.2
  have hord : orderOf d = 3 := by
    have hdvd : orderOf d ∣ Nat.card D := by simpa using orderOf_dvd_natCard d
    rw [hD3] at hdvd
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hne
    · exact h
  have htop : Subgroup.zpowers d = ⊤ := by
    apply Subgroup.eq_top_of_card_eq
    rw [Nat.card_zpowers, hord, show Nat.card ↥D = 3 from hD3]
  have hfixall : ∀ w : W, (w : V) ∈ fixV ρ D := by
    intro w e he
    let K : Subgroup ↥D :=
      { carrier := {x | ρ (x : G) (w : V) = (w : V)}
        mul_mem' := fun {x y} hx hy => by
          change ρ ((x : G) * (y : G)) (w : V) = (w : V)
          rw [map_mul, Module.End.mul_apply, hy, hx]
        one_mem' := by simp
        inv_mem' := fun {x} hx => by
          change ρ ((x : G)⁻¹) (w : V) = (w : V)
          have h1 : ρ (x : G) (ρ (x : G)⁻¹ (w : V)) = ρ (x : G) (w : V) := by
            rw [Representation.self_inv_apply, hx]
          exact (Representation.apply_bijective ρ (x : G)).injective h1 }
    have hdK : d ∈ K := hfix w
    have hKtop : K = ⊤ := by
      rw [← htop]
      exact le_antisymm (by rw [htop]; exact le_top) (Subgroup.zpowers_le.mpr hdK)
    have heK : (⟨e, he⟩ : ↥D) ∈ K := by rw [hKtop]; trivial
    exact heK
  have hWbot : W = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    have := hfixall ⟨w, hw⟩
    rw [hDfix] at this
    simpa using this
  exact hWne hWbot

theorem dhat_card (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) (hD3 : Nat.card D = 3)
    (hDfix : fixV ρ D = ⊥) (hWne : W ≠ ⊥) : Nat.card (Dhat hWin) = 3 := by
  have hfD : Function.Injective (fD hWin) := by
    intro a b hab
    have h1 : fD hWin (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 := dhat_ker hWin hD3 hDfix hWne (a * b⁻¹) h1
    rwa [mul_inv_eq_one] at h2
  change Nat.card (fD hWin).range = 3
  rw [← hD3]
  exact (Nat.card_congr (Equiv.ofBijective (fD hWin).rangeRestrict
    ⟨MonoidHom.rangeRestrict_injective_iff.mpr hfD,
      MonoidHom.rangeRestrict_surjective (fD hWin)⟩)).symm

theorem fixV_dhat (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) (hDfix : fixV ρ D = ⊥) :
    fixV (rhoHat (act hWin)) (Dhat hWin) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro w hw
  apply Subtype.ext
  have hmem : (w : V) ∈ fixV ρ D := by
    intro d hd
    have hmemD : fD hWin ⟨d, hd⟩ ∈ Dhat hWin := MonoidHom.mem_range.mpr ⟨⟨d, hd⟩, rfl⟩
    have h1 : rhoHat (act hWin) (fD hWin ⟨d, hd⟩) w = w := hw (fD hWin ⟨d, hd⟩) hmemD
    have h1' : ((fD hWin ⟨d, hd⟩ : ↥(Ghat hWin)) : W ≃ₗ[ZMod p] W) w = w := by
      show (rhoHat (act hWin) (fD hWin ⟨d, hd⟩)) w = w
      exact h1
    have h2 : (((fD hWin ⟨d, hd⟩ : ↥(Ghat hWin)) : W ≃ₗ[ZMod p] W) w : V) = (w : V) :=
      congrArg (fun x : W => (x : V)) h1'
    simpa [fD] using h2
  rw [hDfix] at hmem
  simpa using hmem

theorem that_ne_bot (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (htw : ∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) : That hWin ≠ ⊥ := by
  obtain ⟨t, ht, w, hw, hne⟩ := htw
  intro hbot
  have hmem : fT hWin ⟨t, ht⟩ ∈ That hWin := MonoidHom.mem_range.mpr ⟨⟨t, ht⟩, rfl⟩
  rw [hbot] at hmem
  have h1 : fT hWin ⟨t, ht⟩ = 1 := by simpa using hmem
  have h2 : (act hWin).rangeRestrict (Subgroup.inclusion le_sup_left ⟨t, ht⟩) = 1 := by
    simpa [fT] using h1
  exact hne ((rangeRestrict_eq_one_iff hWin (Subgroup.inclusion le_sup_left ⟨t, ht⟩)).mp h2 w hw)

theorem dhat_le_normalizer (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (hDT : D ≤ normalizer (T : Set G)) :
    Dhat hWin ≤ Subgroup.normalizer (That hWin : Set ↥(Ghat hWin)) := by
  rw [Subgroup.le_normalizer_iff]
  rintro x ⟨d, rfl⟩ y ⟨t, rfl⟩
  rw [that_eq_map hWin]
  refine Subgroup.mem_map.mpr ⟨Subgroup.inclusion
    (le_sup_right : D ≤ T ⊔ D) d * Subgroup.inclusion (le_sup_left : T ≤ T ⊔ D) t *
    (Subgroup.inclusion (le_sup_right : D ≤ T ⊔ D) d)⁻¹, ?_, ?_⟩
  · rw [Subgroup.mem_subgroupOf]
    exact Subgroup.le_normalizer_iff.mp hDT d d.2 t t.2
  · simp only [fD, fT, MonoidHom.comp_apply, map_mul, map_inv]

theorem commutator_dhat_that (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (hDcomm : ⁅D, T⁆ = T) : ⁅Dhat hWin, That hWin⁆ = That hWin := by
  have hcomm_sub : ⁅D.subgroupOf (T ⊔ D), T.subgroupOf (T ⊔ D)⁆ = T.subgroupOf (T ⊔ D) := by
    apply Subgroup.map_injective (Subgroup.subtype_injective (T ⊔ D))
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le le_sup_right,
      Subgroup.map_subgroupOf_eq_of_le le_sup_left, hDcomm]
  rw [dhat_eq_map hWin, that_eq_map hWin, ← Subgroup.map_commutator, hcomm_sub]

theorem dhat_le_normalizer_center (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (hDT : D ≤ normalizer (T : Set G)) :
    Dhat hWin ≤ Subgroup.normalizer (Zmap hWin : Set ↥(Ghat hWin)) := by
  rw [Subgroup.le_normalizer_iff]
  rintro x ⟨d, rfl⟩ z ⟨w, hw, rfl⟩
  have hxT : fD hWin d ∈ Subgroup.normalizer (That hWin : Set ↥(Ghat hWin)) :=
    dhat_le_normalizer hWin hDT ⟨d, rfl⟩
  have hzT : fD hWin d * (That hWin).subtype w * (fD hWin d)⁻¹ ∈ That hWin :=
    (Subgroup.mem_normalizer_iff.mp hxT ((That hWin).subtype w)).mp w.2
  refine Subgroup.mem_map.mpr ⟨⟨_, hzT⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro v
  have hvT : (fD hWin d)⁻¹ * (That hWin).subtype v * (fD hWin d) ∈ That hWin :=
    (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxT) ((That hWin).subtype v)).mp v.2
  let v' : ↥(That hWin) := ⟨(fD hWin d)⁻¹ * (That hWin).subtype v * (fD hWin d), hvT⟩
  have hv'_eq : (That hWin).subtype v' =
      (fD hWin d)⁻¹ * (That hWin).subtype v * (fD hWin d) := rfl
  have hcomm : v' * w = w * v' := Subgroup.mem_center_iff.mp hw v'
  apply Subtype.ext
  change (That hWin).subtype v * (fD hWin d * (That hWin).subtype w * (fD hWin d)⁻¹) =
    (fD hWin d * (That hWin).subtype w * (fD hWin d)⁻¹) * (That hWin).subtype v
  have hv : (That hWin).subtype v = fD hWin d * (That hWin).subtype v' * (fD hWin d)⁻¹ := by
    rw [hv'_eq]; group
  calc (That hWin).subtype v * (fD hWin d * (That hWin).subtype w * (fD hWin d)⁻¹)
      = (fD hWin d * (That hWin).subtype v' * (fD hWin d)⁻¹) *
        (fD hWin d * (That hWin).subtype w * (fD hWin d)⁻¹) := by rw [hv]
    _ = fD hWin d * (That hWin).subtype (v' * w) * (fD hWin d)⁻¹ := by
          simp only [map_mul]; group
    _ = fD hWin d * (That hWin).subtype (w * v') * (fD hWin d)⁻¹ := by rw [hcomm]
    _ = (fD hWin d * (That hWin).subtype w * (fD hWin d)⁻¹) *
        (fD hWin d * (That hWin).subtype v' * (fD hWin d)⁻¹) := by
          simp only [map_mul]; group
    _ = (fD hWin d * (That hWin).subtype w * (fD hWin d)⁻¹) * (That hWin).subtype v := by
          rw [hv]

theorem zmap_le_that (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    Zmap hWin ≤ That hWin := by
  intro z hz
  obtain ⟨w, -, rfl⟩ := Subgroup.mem_map.mp hz
  exact w.2

theorem a_le_zmap (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (hDT : D ≤ normalizer (T : Set G)) : A hWin ≤ Zmap hWin := by
  change ⁅Zmap hWin, Dhat hWin⁆ ≤ Zmap hWin
  exact (Subgroup.le_normalizer_iff_commutator_le_left).mp (dhat_le_normalizer_center hWin hDT)

theorem a_commutative (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (hDT : D ≤ normalizer (T : Set G)) : IsMulCommutative ↥(A hWin) :=
  IsMulCommutative.of_comm fun x y =>
    Subtype.ext (congrArg (fun z : ↥(Zmap hWin) => (z : ↥(Ghat hWin)))
      (mul_comm' (M := ↥(Zmap hWin))
        (⟨x.1, a_le_zmap hWin hDT x.2⟩ : ↥(Zmap hWin))
        (⟨y.1, a_le_zmap hWin hDT y.2⟩ : ↥(Zmap hWin))))

theorem a_isPGroup (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (hDT : D ≤ normalizer (T : Set G)) (hT2 : IsPGroup 2 T) : IsPGroup 2 (A hWin) := by
  have hle : A hWin ≤ That hWin := (a_le_zmap hWin hDT).trans (zmap_le_that hWin)
  exact (that_isPGroup hWin hT2).of_injective (Subgroup.inclusion hle)
    (Subgroup.inclusion_injective hle)

theorem dhat_le_normalizer_A (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    Dhat hWin ≤ Subgroup.normalizer (A hWin : Set ↥(Ghat hWin)) := by
  change Dhat hWin ≤ Subgroup.normalizer
    ((⁅Zmap hWin, Dhat hWin⁆ : Subgroup ↥(Ghat hWin)) : Set ↥(Ghat hWin))
  exact Subgroup.normalizer_commutator_ge_right (Zmap hWin) (Dhat hWin)

theorem dhat_A (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (hDT : D ≤ normalizer (T : Set G)) (hT2 : IsPGroup 2 T)
    (hDhatcard : Nat.card (Dhat hWin) = 3) : ⁅Dhat hWin, A hWin⁆ = A hWin := by
  have hDhat3 : IsPGroup 3 (Dhat hWin) :=
    IsPGroup.of_card (n := 1) (by rw [hDhatcard]; norm_num)
  have hcop : ¬ 3 ∣ Nat.card (Zmap hWin) := by
    obtain ⟨n, hn⟩ := isPGroup_iff_card_dvd_pow.mp (that_isPGroup hWin hT2)
    intro h3
    have hdvd : 3 ∣ 2 ^ n :=
      h3.trans ((Subgroup.card_dvd_of_le (zmap_le_that hWin)).trans hn)
    exact absurd (Nat.prime_three.dvd_of_dvd_pow hdvd) (by norm_num)
  have hidem := CFSG.RankThreeEvenClassification.Helpers.coprime_commutator_idempotent 3
    Nat.prime_three (Dhat hWin) (Zmap hWin) hDhat3 hcop (dhat_le_normalizer_center hWin hDT)
  rw [Subgroup.commutator_comm (Dhat hWin) (A hWin)]
  exact hidem

theorem p_ne_three (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (htw : ∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w)
    (hDhatfix : fixV (rhoHat (act hWin)) (Dhat hWin) = ⊥)
    (hDhat3 : IsPGroup 3 (Dhat hWin)) : p ≠ 3 := by
  intro hp3eq
  haveI : Nontrivial W := by
    obtain ⟨t, ht, w, hw, hne⟩ := htw
    refine ⟨⟨w, hw⟩, 0, fun h => hne ?_⟩
    have hw0 : w = 0 := by simpa using congrArg (fun x : W => (x : V)) h
    rw [hw0]; simp
  have hDhat3p : IsPGroup p (Dhat hWin) := hp3eq.symm ▸ hDhat3
  exact (CFSG.LocalAnalysis.UniquenessCase.UCK.UC46.fixV_ne_bot_of_pGroup
    (ρ := rhoHat (act hWin)) hDhat3p) hDhatfix

theorem a_eq_bot (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) (hK42 : K42)
    (hKGGhat : CFSG.Open.IsKGroup ↥(Ghat hWin)) (hp2 : 2 < p) (hD3 : Nat.card D = 3)
    (hDfix : fixV ρ D = ⊥) (hT2 : IsPGroup 2 T) (hDT : D ≤ normalizer (T : Set G))
    (hWne : W ≠ ⊥) (htw : ∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) : A hWin = ⊥ := by
  have hDhatcard : Nat.card (Dhat hWin) = 3 := dhat_card hWin hD3 hDfix hWne
  have hDhatfix : fixV (rhoHat (act hWin)) (Dhat hWin) = ⊥ := fixV_dhat hWin hDfix
  have hDhat3 : IsPGroup 3 (Dhat hWin) :=
    IsPGroup.of_card (n := 1) (by rw [hDhatcard]; norm_num)
  have hp3 : p ≠ 3 := p_ne_three hWin htw hDhatfix hDhat3
  by_contra hAne
  have hres := hK42 p (Fact.out) ↥(Ghat hWin) hKGGhat W (rhoHat (act hWin))
    (rhoHat_injective (act hWin)) 2 3 Nat.prime_two Nat.prime_three (by omega) (Ne.symm hp3)
    (by norm_num) (Dhat hWin) hDhatcard hDhatfix (A hWin) (a_isPGroup hWin hDT hT2) hAne
    (dhat_le_normalizer_A hWin) (dhat_A hWin hDT hT2 hDhatcard)
  exact hres.1 (a_commutative hWin hDT)

theorem zmap_le_center (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (hDT : D ≤ normalizer (T : Set G)) (hA_bot : A hWin = ⊥) :
    Zmap hWin ≤ Subgroup.center ↥(Ghat hWin) := by
  have hZmap_cent_D : Zmap hWin ≤ Subgroup.centralizer (Dhat hWin : Set ↥(Ghat hWin)) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    change ⁅Zmap hWin, Dhat hWin⁆ = ⊥
    exact hA_bot
  have hZmap_cent_T : Zmap hWin ≤ Subgroup.centralizer (That hWin : Set ↥(Ghat hWin)) := by
    have h := Subgroup.map_centralizer_le_centralizer_image (Set.univ : Set ↥(That hWin))
      (That hWin).subtype
    rw [Subgroup.centralizer_univ] at h
    rwa [Set.image_univ, Subgroup.coe_subtype, Subtype.range_coe] at h
  rw [← Subgroup.centralizer_univ, ← Subgroup.coe_top, Subgroup.le_centralizer_iff,
    ← sup_eq_top hWin]
  refine sup_le ?_ ?_
  · rw [Subgroup.le_centralizer_iff]; exact hZmap_cent_T
  · rw [Subgroup.le_centralizer_iff]; exact hZmap_cent_D

theorem center_that_cyclic (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) (hK42 : K42)
    (hKGGhat : CFSG.Open.IsKGroup ↥(Ghat hWin)) (hp2 : 2 < p) (hD3 : Nat.card D = 3)
    (hDfix : fixV ρ D = ⊥) (hT2 : IsPGroup 2 T) (hDT : D ≤ normalizer (T : Set G))
    (hWne : W ≠ ⊥)
    (hWirr : ∀ W' : Submodule (ZMod p) V, W' ≤ W →
      (∀ g ∈ T ⊔ D, ∀ w ∈ W', ρ g w ∈ W') → W' = ⊥ ∨ W' = W)
    (htw : ∃ t ∈ T, ∃ w ∈ W, ρ t w ≠ w) :
    IsCyclic ↥(Subgroup.center ↥(That hWin)) := by
  have hA_bot : A hWin = ⊥ := a_eq_bot hWin hK42 hKGGhat hp2 hD3 hDfix hT2 hDT hWne htw
  have hZmap_center : Zmap hWin ≤ Subgroup.center ↥(Ghat hWin) :=
    zmap_le_center hWin hDT hA_bot
  haveI : (rhoHat (act hWin)).IsIrreducible := isIrreducible_rhoHat hWin hWirr htw
  haveI : FiniteDimensional (ZMod p) W := Module.Finite.of_finite
  haveI : IsCyclic ↥(Subgroup.center ↥(Ghat hWin)) :=
    CFSG.center_cyclic_of_representation_faithful_irreducible (rhoHat (act hWin))
      (rhoHat_injective (act hWin))
  refine isCyclic_of_injective (G := ↥(Subgroup.center ↥(That hWin)))
    (G' := ↥(Subgroup.center ↥(Ghat hWin)))
    { toFun := fun z => ⟨((z : ↥(That hWin)) : ↥(Ghat hWin)),
        hZmap_center (Subgroup.mem_map.mpr ⟨z.1, z.2, rfl⟩)⟩
      map_one' := rfl
      map_mul' := fun a b => rfl } ?_
  intro a b hab
  exact Subtype.ext ((That hWin).subtype_injective
    (congrArg (fun w : ↥(Subgroup.center ↥(Ghat hWin)) => (w : ↥(Ghat hWin))) hab))

noncomputable abbrev eTop (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W) :
    ↥(That hWin ⊔ Dhat hWin) ≃* ↥(Ghat hWin) :=
  { toFun := fun x => x.1
    invFun := fun y => ⟨y, by rw [sup_eq_top hWin]; trivial⟩
    left_inv := fun x => rfl
    right_inv := fun y => rfl
    map_mul' := fun x y => rfl }

theorem exists_phi (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (eQ : ↥(That hWin) ≃* QuaternionGroup 2) :
    ∃ φ : ↥T →* QuaternionGroup 2, Function.Surjective φ ∧
      ∀ t : ↥T, φ t = 1 ↔ ∀ w ∈ W, ρ t w = w := by
  refine ⟨eQ.toMonoidHom.comp (fT hWin).rangeRestrict, ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := eQ.surjective y
    obtain ⟨t, ht⟩ := (fT hWin).rangeRestrict_surjective x
    exact ⟨t, by rw [MonoidHom.comp_apply, ht]; simpa using hx⟩
  · intro t
    have h2 : (eQ.toMonoidHom.comp (fT hWin).rangeRestrict) t = 1 ↔
        (act hWin).rangeRestrict (Subgroup.inclusion le_sup_left t) = 1 := by
      rw [MonoidHom.comp_apply]
      change eQ ((fT hWin).rangeRestrict t) = 1 ↔
        (act hWin).rangeRestrict (Subgroup.inclusion le_sup_left t) = 1
      constructor
      · intro h
        have h3 : (fT hWin).rangeRestrict t = 1 := eQ.injective (by rw [h, map_one])
        exact Subtype.ext_iff.mp h3
      · intro h
        have h3 : (fT hWin).rangeRestrict t = 1 := Subtype.ext h
        rw [h3, map_one]
    simpa using (h2.trans (rangeRestrict_eq_one_iff hWin (Subgroup.inclusion le_sup_left t)))

theorem exists_psi (hWin : ∀ g ∈ T ⊔ D, ∀ w ∈ W, ρ g w ∈ W)
    (eSL : ↥(That hWin ⊔ Dhat hWin) ≃* SL(2, ZMod 3)) :
    ∃ ψ : ↥(T ⊔ D) →* SL(2, ZMod 3), Function.Surjective ψ ∧
      ∀ g : ↥(T ⊔ D), ψ g = 1 ↔ ∀ w ∈ W, ρ g w = w := by
  refine ⟨eSL.toMonoidHom.comp ((eTop hWin).symm.toMonoidHom.comp (act hWin).rangeRestrict),
    ?_, ?_⟩
  · intro y
    obtain ⟨x, hx⟩ := eSL.surjective y
    obtain ⟨z, hz⟩ := (eTop hWin).symm.surjective x
    obtain ⟨g, hg⟩ := MonoidHom.rangeRestrict_surjective (act hWin) z
    exact ⟨g, by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply, hg]
      change eSL ((eTop hWin).symm z) = y
      rw [hz]
      simpa using hx⟩
  · intro g
    have h2 : (eSL.toMonoidHom.comp ((eTop hWin).symm.toMonoidHom.comp
        (act hWin).rangeRestrict)) g = 1 ↔ (act hWin).rangeRestrict g = 1 := by
      rw [MonoidHom.comp_apply, MonoidHom.comp_apply]
      change eSL ((eTop hWin).symm ((act hWin).rangeRestrict g)) = 1 ↔
        (act hWin).rangeRestrict g = 1
      constructor
      · intro h
        have h3 : (eTop hWin).symm ((act hWin).rangeRestrict g) = 1 :=
          eSL.injective (by rw [h, map_one])
        exact (eTop hWin).symm.injective (by simpa using h3)
      · intro h
        rw [h, map_one, map_one]
    rw [h2, rangeRestrict_eq_one_iff hWin g]

theorem k43gen_of_k43 (hK42 : K42) (hK43 : K43) : K43Gen := by
  intro p hpFact hp2 G _ _ hKG V _ _ _ ρ hρ D hD3 hDfix T hT2 hDT hDcomm W hWin hWirr htw
  classical
  have hWne : W ≠ ⊥ := by
    obtain ⟨t, ht, w, hw, hne⟩ := htw
    intro h
    rw [h] at hw
    have hw0 : w = 0 := by simpa using hw
    exact hne (by rw [hw0]; simp)
  haveI : Finite (W ≃ₗ[ZMod p] W) :=
    Finite.of_injective (fun e : W ≃ₗ[ZMod p] W => (e : W → W))
      (fun a b h => LinearEquiv.ext fun w => congrFun h w)
  haveI : Finite ↥(Ghat hWin) := Subtype.finite
  have hKGGhat : CFSG.Open.IsKGroup ↥(Ghat hWin) :=
    (hKG.subgroup (T ⊔ D)).of_surjective (act hWin).rangeRestrict
      (act hWin).rangeRestrict_surjective
  have hDhatcard : Nat.card (Dhat hWin) = 3 := dhat_card hWin hD3 hDfix hWne
  have hDhatfix : fixV (rhoHat (act hWin)) (Dhat hWin) = ⊥ := fixV_dhat hWin hDfix
  have hThat2 : IsPGroup 2 (That hWin) := that_isPGroup hWin hT2
  have hThatne : That hWin ≠ ⊥ := that_ne_bot hWin htw
  have hDhatnorm : Dhat hWin ≤ Subgroup.normalizer (That hWin : Set ↥(Ghat hWin)) :=
    dhat_le_normalizer hWin hDT
  have hDhatcomm : ⁅Dhat hWin, That hWin⁆ = That hWin := commutator_dhat_that hWin hDcomm
  have hThatcyc : IsCyclic ↥(Subgroup.center ↥(That hWin)) :=
    center_that_cyclic hWin hK42 hKGGhat hp2 hD3 hDfix hT2 hDT hWne hWirr htw
  obtain ⟨hQ, hSL⟩ := @hK43 p hpFact hp2 ↥(Ghat hWin) _ _ hKGGhat W _ _ _ (rhoHat (act hWin))
    (rhoHat_injective (act hWin)) (Dhat hWin) hDhatcard hDhatfix (That hWin) hThat2 hThatne
    hDhatnorm hDhatcomm hThatcyc
  obtain ⟨eQ⟩ := hQ
  obtain ⟨eSL⟩ := hSL
  exact ⟨exists_phi hWin eQ, exists_psi hWin eSL⟩

end K43.Gen

end CFSG.LocalAnalysis.UniquenessCase.UCK

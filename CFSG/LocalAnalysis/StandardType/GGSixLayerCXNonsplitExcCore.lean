module

public import CFSG.LocalAnalysis.StandardType.GGSixLayerCXNonsplitKGOmTag
public import CFSG.LocalAnalysis.ComponentInitial.DerivedFixedLayer

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint LayerFacts
open CFSG.LocalAnalysis.ComponentInitial (isComponentOf_map_iff)

namespace ExcNonsplit

section Transport

variable {L G : Type} [Group L] [Group G]

theorem commutator_eq_top_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : commutator Y = ⊤) : commutator X = ⊤ := by
  have hsurj : Function.Surjective (e.symm : Y →* X) := e.symm.surjective
  have h1 := Subgroup.map_commutator (⊤ : Subgroup Y) ⊤ (e.symm : Y →* X)
  rw [Subgroup.map_top_of_surjective _ hsurj] at h1
  change ⁅(⊤ : Subgroup X), ⊤⁆ = ⊤
  rw [← h1]
  change (commutator Y).map (e.symm : Y →* X) = ⊤
  rw [h, Subgroup.map_top_of_surjective _ hsurj]

theorem ggNbrClauseFiveMarking_of_map {ψ : L →* G} (hinj : Function.Injective ψ) {p : ℕ}
    {x : G} {s : L} (hs : ∀ u, x⁻¹ * ψ u * x = ψ (s⁻¹ * u * s)) {X : Subgroup L}
    (h : GGNbrClauseFiveMarking p x (X.map ψ)) : GGNbrClauseFiveMarking p s X := by
  set e : ↥X ≃* ↥(X.map ψ) := X.equivMapOfInjective ψ hinj with he
  have hZ : (Subgroup.center ↥X).map (e : ↥X →* ↥(X.map ψ)) = Subgroup.center ↥(X.map ψ) :=
    Subgroup.map_center_eq e
  obtain ⟨hcomm, lab, hlab, hraw⟩ := h
  refine ⟨commutator_eq_top_of_mulEquiv e hcomm, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hsimp, hna, θ, hP⟩
  refine ⟨hsimp, hna, (QuotientGroup.congr _ _ e hZ).trans θ, ?_⟩
  rcases hP with hHS | ⟨h3, f, hf, u, hu, hord, hind⟩
  · left
    have hc : (Subgroup.center ↥(X.map ψ) = ⊥) = (Subgroup.center ↥X = ⊥) := by
      apply propext
      rw [← hZ, Subgroup.map_eq_bot_iff_of_injective _ e.injective]
    rw [← hc]
    exact hHS
  · right
    refine ⟨h3, f, hf, u, hu, hord, fun l l' hll' => ?_⟩
    have hrel : ((e l' : ↥(X.map ψ)) : G) = x⁻¹ * ((e l : ↥(X.map ψ)) : G) * x := by
      rw [he, Subgroup.coe_equivMapOfInjective_apply, Subgroup.coe_equivMapOfInjective_apply,
        hs, ← hll']
    have h1 := hind (e l) (e l') hrel
    simpa only [MulEquiv.trans_apply, QuotientGroup.congr_mk] using h1

end Transport

section Core

@[expose] def GGNonsplitCoreAt (C : Type) [Group C] (p : ℕ) : Prop :=
  ∀ a b : C, a ^ p = 1 → b ^ p = 1 → a * b = b * a →
    ∀ X : Subgroup C, IsComponentOf X (Subgroup.centralizer {a}) → ¬ p ∣ Nat.card X →
      ∃ X' : Subgroup C, IsComponentOf X' (Subgroup.centralizer {b}) ∧ X ≤ X' ∧
        ¬ GGNbrClauseFiveMarking p a X'

variable {L : Type} [Group L] {G : Type} [Group G]

theorem range_inf_centralizer_eq_map_centralizer {ψ : L →* G} (hinj : Function.Injective ψ)
    {x : G} {s : L} (hs : (x, s) ∈ ggConjPairs ψ) :
    ψ.range ⊓ Subgroup.centralizer {x} = (Subgroup.centralizer {s}).map ψ := by
  rw [ClNonsplit.range_inf_centralizer_eq hinj hs, Subgroup.zpowers_eq_closure,
    Subgroup.centralizer_closure]

theorem exists_component_of_pairs {ψ : L →* G} (hinj : Function.Injective ψ) {p : ℕ}
    (hcore : GGNonsplitCoreAt L p) {x y : G} {s t : L} (hsp : s ^ p = 1) (htp : t ^ p = 1)
    (hst : s * t = t * s) (hs : (x, s) ∈ ggConjPairs ψ) (ht : (y, t) ∈ ggConjPairs ψ)
    {K : Subgroup G} (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {x}))
    (hpK : ¬ p ∣ Nat.card K) :
    ∃ K' : Subgroup G, IsComponentOf K' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ K ≤ K' ∧
      ¬ GGNbrClauseFiveMarking p x K' := by
  rw [range_inf_centralizer_eq_map_centralizer hinj hs] at hK
  have hKr : K ≤ ψ.range := hK.1.trans (Subgroup.map_le_range ψ _)
  have hKeq : (K.comap ψ).map ψ = K := Subgroup.map_comap_eq_self hKr
  have hX : IsComponentOf (K.comap ψ) (Subgroup.centralizer {s}) := by
    rw [← isComponentOf_map_iff hinj, hKeq]
    exact hK
  have hpX : ¬ p ∣ Nat.card (K.comap ψ) := by
    rwa [← Subgroup.card_map_of_injective hinj, hKeq]
  obtain ⟨X', hX', hXX', hmark⟩ := hcore s t hsp htp hst _ hX hpX
  refine ⟨X'.map ψ, ?_, ?_, fun h => hmark (ggNbrClauseFiveMarking_of_map hinj (fun u => ?_) h)⟩
  · rw [range_inf_centralizer_eq_map_centralizer hinj ht]
    exact (isComponentOf_map_iff hinj).mpr hX'
  · rw [← hKeq]
    exact Subgroup.map_mono hXX'
  · have h4 := hs (s⁻¹ * u * s)
    rw [show s * (s⁻¹ * u * s) * s⁻¹ = u by group] at h4
    rw [h4]
    group

theorem exists_component_of_core (hZ : Subgroup.center L = ⊥) {ψ : L →* G}
    (hinj : Function.Injective ψ) {p : ℕ} (hcore : GGNonsplitCoreAt L p) {x y : G}
    (hx : x ^ p = 1) (hy : y ^ p = 1) (hxy : x * y = y * x) {s t : L}
    (hs : (x, s) ∈ ggConjPairs ψ) (ht : (y, t) ∈ ggConjPairs ψ) {K : Subgroup G}
    (hK : IsComponentOf K (ψ.range ⊓ Subgroup.centralizer {x})) (hpK : ¬ p ∣ Nat.card K) :
    ∃ K' : Subgroup G, IsComponentOf K' (ψ.range ⊓ Subgroup.centralizer {y}) ∧ K ≤ K' ∧
      ¬ GGNbrClauseFiveMarking p x K' := by
  have hZ1 : ∀ g : L, ((1 : G), g) ∈ ggConjPairs ψ → g = 1 := fun g hg => by
    have h := mem_center_of_mem_ggConjPairs_one hinj hg
    rwa [hZ, Subgroup.mem_bot] at h
  have hsp : s ^ p = 1 := hZ1 _ (by
    have h := (ggConjPairs ψ).pow_mem hs p
    rwa [Prod.pow_mk, hx] at h)
  have htp : t ^ p = 1 := hZ1 _ (by
    have h := (ggConjPairs ψ).pow_mem ht p
    rwa [Prod.pow_mk, hy] at h)
  have hst : s * t = t * s := by
    have h := (ggConjPairs ψ).mul_mem ((ggConjPairs ψ).mul_mem hs ht)
      ((ggConjPairs ψ).inv_mem ((ggConjPairs ψ).mul_mem ht hs))
    rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk, hxy, mul_inv_cancel] at h
    have h1 := hZ1 _ h
    calc s * t = s * t * (t * s)⁻¹ * (t * s) := by group
      _ = t * s := by rw [h1, one_mul]
  exact exists_component_of_pairs hinj hcore hsp htp hst hs ht hK hpK

theorem ggNonsplitCoreAt_of_mulEquiv {C C' : Type} [Group C] [Group C'] (e : C ≃* C')
    (hZ : Subgroup.center C' = ⊥) {p : ℕ} (h : GGNonsplitCoreAt C' p) : GGNonsplitCoreAt C p := by
  intro a b ha hb hab X hX hpX
  have hrange : (e.symm : C' →* C).range = ⊤ := MonoidHom.range_eq_top.mpr e.symm.surjective
  have hpair : ∀ c : C, (c, e c) ∈ ggConjPairs (e.symm : C' →* C) := fun c =>
    mem_ggConjPairs.mpr fun u => by
      change e.symm (e c * u * (e c)⁻¹) = c * e.symm u * c⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.symm_apply_apply]
  have hX' : IsComponentOf X ((e.symm : C' →* C).range ⊓ Subgroup.centralizer {a}) := by
    rwa [hrange, top_inf_eq]
  obtain ⟨K', hK', hXK', hm⟩ :=
    exists_component_of_core hZ e.symm.injective h ha hb hab (hpair a) (hpair b) hX' hpX
  rw [hrange, top_inf_eq] at hK'
  exact ⟨K', hK', hXK', hm⟩

end Core

end ExcNonsplit

end CFSG.StandardType

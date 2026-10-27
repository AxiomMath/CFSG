module

public import CFSG.LieType.Chevalley.GraphFixedOrbitCollection
public import CFSG.LieType.Chevalley.GraphFixedParameterFields

public noncomputable section

namespace CFSG.Timmesfeld.ExceptionalOrders

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {t : TwistTag} {K : Type} [Field K]

theorem card_orbitField {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (p ^ f) ^ t.order) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ (p ^ f))
    (a : Fin t.foldedTag.rank) :
    Nat.card (orbitField t K σ a) = (p ^ f) ^ (t.orbit a).card := by
  obtain ⟨σ', hσ', -, hcard, -⟩ := finite_graph_field_parameter_fields t hp hf K hK
  have e : σ = σ'.toRingHom := RingHom.ext fun c => by
    rw [hσ]
    exact (hσ' c).symm
  rw [e]
  exact hcard a

variable {σ : K →+* K} {q : ℕ}

theorem card_diagramOrbit_inf (hq : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card)
    {α : Fin t.tag.rank → ℤ} (hα : IsRoot t.tag α) :
    Nat.card ↥(rootSpan t.tag K (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)) ⊓
      twistedFixedGroup t K σ) = q ^ (t.diagramOrbit α).card := by
  obtain ⟨w, hw, a, heq, hcard, -⟩ := (diagram_root_orbit_reduction t).1 α hα
  have hset : (t.diagramOrbit α : Set (Fin t.tag.rank → ℤ)) =
      (fun i => w • (Pi.single i 1 : Fin t.tag.rank → ℤ)) '' ↑(t.orbit a) := by
    rw [heq, Finset.coe_image]
  rw [hset, ← Nat.card_congr (orbitConjEquiv t σ a hw).toEquiv, hcard]
  exact (Nat.card_congr Multiplicative.toAdd).trans (hq a)

theorem card_rootSpan_inf_twistedFixedGroup (hσ : Function.Surjective σ)
    (hq : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card)
    {S : Set (Fin t.tag.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot t.tag α ∧ 0 < height α)
    (hSρ : ∀ α ∈ S, permLattice t.perm α ∈ S)
    (hclosed : ∀ α ∈ S, ∀ β ∈ S, ∀ a b : ℕ, 1 ≤ a → 1 ≤ b → IsRoot t.tag (a • α + b • β) →
      a • α + b • β ∈ S) :
    Nat.card ↥(rootSpan t.tag K S ⊓ twistedFixedGroup t K σ) = q ^ S.ncard := by
  classical
  set 𝒪 : Set (Finset (Fin t.tag.rank → ℤ)) :=
    {O' | O' ∈ t.diagramRootOrbits ∧ (O' : Set (Fin t.tag.rank → ℤ)) ⊆ S}
  have hfin : 𝒪.Finite := by
    refine ((finite_setOf_isRoot t.tag).image fun α => t.diagramOrbit α).subset ?_
    rintro O ⟨⟨α, hα, rfl⟩, -⟩
    exact ⟨α, hα, rfl⟩
  set F := hfin.toFinset
  set O : Fin F.card → Finset (Fin t.tag.rank → ℤ) := fun j => (F.equivFin.symm j : _)
  have hO : Function.Injective O := fun i j h => F.equivFin.symm.injective (Subtype.ext h)
  have hrange : Set.range O = 𝒪 := by
    ext O'
    refine ⟨fun ⟨j, hj⟩ => hj ▸ hfin.mem_toFinset.1 (F.equivFin.symm j).2, fun h =>
      ⟨F.equivFin ⟨O', hfin.mem_toFinset.2 h⟩, by simp [O]⟩⟩
  have hbij := bijOn_prod_graphFixed hσ hS hSρ hclosed O hO hrange
  have hmemO : ∀ j, O j ∈ 𝒪 := fun j => hrange ▸ Set.mem_range_self j
  have hcardO : ∀ j, Nat.card ↥(rootSpan t.tag K (O j : Set (Fin t.tag.rank → ℤ)) ⊓
      twistedFixedGroup t K σ) = q ^ (O j).card := fun j => by
    obtain ⟨⟨α, hα, hαO⟩, -⟩ := hmemO j
    rw [← hαO]
    exact card_diagramOrbit_inf hq hα
  have hS_eq : S = ↑(F.biUnion id) := by
    ext α
    simp only [Finset.coe_biUnion, Finset.mem_coe, id, Set.mem_iUnion, exists_prop]
    refine ⟨fun hα => ⟨t.diagramOrbit α, hfin.mem_toFinset.2 ⟨⟨α, (hS α hα).1, rfl⟩,
      diagramOrbit_subset hSρ hα⟩, t.self_mem_diagramOrbit α⟩, fun ⟨O', hO', hαO'⟩ =>
        (hfin.mem_toFinset.1 hO').2 hαO'⟩
  have hdisj : (F : Set (Finset (Fin t.tag.rank → ℤ))).PairwiseDisjoint id := by
    intro O₁ h₁ O₂ h₂ hne
    obtain ⟨⟨α, -, rfl⟩, -⟩ := hfin.mem_toFinset.1 h₁
    obtain ⟨⟨β, -, rfl⟩, -⟩ := hfin.mem_toFinset.1 h₂
    exact t.disjoint_diagramOrbit hne
  have hncard : S.ncard = ∑ j, (O j).card := by
    rw [hS_eq, Set.ncard_coe_finset, Finset.card_biUnion hdisj, ← Finset.sum_coe_sort F]
    exact Fintype.sum_equiv F.equivFin _ _ fun u => by simp [O]
  calc Nat.card ↥(rootSpan t.tag K S ⊓ twistedFixedGroup t K σ)
      = Nat.card (Set.univ : Set ((j : Fin F.card) → ↥(rootSpan t.tag K
          (O j : Set (Fin t.tag.rank → ℤ)) ⊓ twistedFixedGroup t K σ))) :=
        (Nat.card_congr hbij.equiv).symm
    _ = ∏ j, Nat.card ↥(rootSpan t.tag K (O j : Set (Fin t.tag.rank → ℤ)) ⊓
          twistedFixedGroup t K σ) := by rw [Nat.card_univ, Nat.card_pi]
    _ = q ^ S.ncard := by
      rw [Finset.prod_congr rfl fun j _ => hcardO j, Finset.prod_pow_eq_pow_sum, hncard]

theorem card_graphFixedPosUnipotent (hσ : Function.Surjective σ)
    (hq : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card) :
    Nat.card (graphFixedPosUnipotent t K σ) =
      q ^ {α : Fin t.tag.rank → ℤ | IsRoot t.tag α ∧ 0 < height α}.ncard := by
  refine card_rootSpan_inf_twistedFixedGroup hσ hq (fun _ h => h)
    (fun α hα => ⟨hα.1.permLattice t.cartan_perm, by rw [height_permLattice]; exact hα.2⟩)
    fun α hα β hβ a b ha hb hr => ⟨hr, ?_⟩
  have ha' : (1 : ℤ) ≤ a := by exact_mod_cast ha
  have hb' : (1 : ℤ) ≤ b := by exact_mod_cast hb
  rw [height_nsmul_add_nsmul]
  nlinarith [hα.2, hβ.2]

theorem card_graphFixedInversionUnipotent (hσ : Function.Surjective σ)
    (hq : ∀ a, Nat.card (orbitField t K σ a) = q ^ (t.orbit a).card) {w : WeylGroup t.tag}
    (hw : w ∈ relWeylTwist t) :
    Nat.card (graphFixedInversionUnipotent t K σ w) = q ^ (coxeterSystem t.tag).length w := by
  rw [(weyl_inversion_length t.tag).1 w]
  refine card_rootSpan_inf_twistedFixedGroup hσ hq (fun _ h => inversionSet_pos h) ?_
    (inversionSet_closed w)
  rintro α ⟨hα, hpos, -, hneg⟩
  refine ⟨hα.permLattice t.cartan_perm, by rwa [height_permLattice],
    IsRoot.smul (hα.permLattice t.cartan_perm) w, ?_⟩
  rw [← (mem_relWeylTwist t).1 hw, weylTwist_smul_permLattice, height_permLattice]
  exact hneg

end CFSG.Timmesfeld.ExceptionalOrders

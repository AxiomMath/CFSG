module

public import CFSG.LieType.Chevalley.GraphFixedF4GroupDescent

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

theorem exists_cartan_mul_eq_one_of_G2_F4 {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4) :
    ∃ B : Matrix (Fin τ.rank) (Fin τ.rank) ℤ, τ.cartan * B = 1 := by
  rcases hτ with rfl | rfl
  · exact ⟨cartanInvG2, cartan_mul_cartanInv_G2⟩
  · exact ⟨cartanInvF4, cartan_mul_cartanInv_F4⟩

theorem exists_ringHom_pow_card (k M : Type) [Field k] [Finite k] [Field M] [Algebra k M] :
    ∃ Fr : M →+* M, ∀ c, Fr c = c ^ Nat.card k := by
  have : Fintype k := Fintype.ofFinite k
  exact ⟨(FiniteField.frobeniusAlgHom k M).toRingHom, fun c => by
    rw [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, FiniteField.frobeniusAlgHom_apply,
      Nat.card_eq_fintype_card]⟩

variable {k M : Type} [Field k] [Finite k] [Field M] [Algebra k M]

theorem mem_map_adjointGroup_of_frobenius_fixed {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4)
    (Fr : M →+* M) (hFr : ∀ c, Fr c = c ^ Nat.card k) (hbij : Function.Bijective Fr)
    {g : ModGL τ M} (hg : g ∈ adjointGroup τ M) (hfix : Units.map (entrywiseHom Fr) g = g) :
    g ∈ (adjointGroup τ k).map (baseChangeGL (algebraMap k M)) := by
  obtain ⟨B, hB⟩ := exists_cartan_mul_eq_one_of_G2_F4 hτ
  set σ : M ≃+* M := RingEquiv.ofBijective Fr hbij
  have hσ : σ.toRingHom = Fr := RingHom.ext fun _ => rfl
  have hσfix : ∀ c, σ c = c → c ∈ Set.range (algebraMap k M) := fun c hc =>
    mem_range_algebraMap_of_pow_card_eq (by rw [← hFr]; exact hc)
  have hg' : g ∈ entrywiseFixedGroup τ σ := ⟨hg, by
    change Units.map (entrywiseHom σ.toRingHom) g = g
    rw [hσ]
    exact hfix⟩
  obtain ⟨h, hh, j, hj, rfl⟩ := mem_mul_of_mem_entrywiseFixedGroup hg'
  refine mul_mem ?_ ?_
  ·
    obtain ⟨hhT, -, hhF⟩ := hh
    obtain ⟨t, ht⟩ := torusCoordHom_surjective (τ := τ) (R := M) ⟨h, hhT⟩
    have hval : h = (List.ofFn fun i => torusElt τ M i (t i)).prod := by
      have := congrArg Subtype.val ht
      rw [coe_torusCoordHom] at this
      exact this.symm
    have hσt : torusCoordHom τ M (fun i => Units.map σ.toRingHom.toMonoidHom (t i)) =
        torusCoordHom τ M t := by
      refine Subtype.ext ?_
      rw [coe_torusCoordHom, coe_torusCoordHom]
      have h1 : Units.map (entrywiseHom σ.toRingHom) h = h := hhF
      rw [hval, map_list_prod, List.map_ofFn] at h1
      simpa only [Function.comp_def, entrywise_torusElt] using h1
    have ht' := torusCoordHom_injective_of_mul_eq_one hB hσt
    rw [hval]
    refine Subgroup.list_prod_mem _ fun x hx => ?_
    obtain ⟨i, rfl⟩ := (List.mem_ofFn' _ _).1 hx
    have hfi : σ (t i : M) = t i := congrArg Units.val (congrFun ht' i)
    obtain ⟨s, hs⟩ := hσfix _ hfi
    have hs0 : s ≠ 0 := fun h0 => (t i).ne_zero (by rw [← hs, h0, map_zero])
    refine ⟨torusElt τ k i (Units.mk0 s hs0), torusElt_mem_adjointGroup i _, ?_⟩
    rw [baseChangeGL_torusElt]
    exact congrArg _ (Units.ext hs)
  ·
    rw [fixedFieldImage_eq_closure] at hj
    refine (Subgroup.closure_le _).2 ?_ hj
    rintro _ ⟨i, c, hc, rfl | rfl⟩
    · obtain ⟨c', rfl⟩ := hσfix c hc
      exact ⟨xUnit τ k i c', xUnit_mem_adjointGroup i c', baseChangeGL_xUnit _ i c'⟩
    · obtain ⟨c', rfl⟩ := hσfix c hc
      exact ⟨yUnit τ k i c', yUnit_mem_adjointGroup i c', baseChangeGL_yUnit _ i c'⟩

theorem frobenius_fixed_eq_map_of_bijective {τ : Tag} (hτ : τ = .G2 ∨ τ = .F4) (Fr : M →+* M)
    (hFr : ∀ c, Fr c = c ^ Nat.card k) (hbij : Function.Bijective Fr) :
    adjointGroup τ M ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _) =
      (adjointGroup τ k).map (baseChangeGL (algebraMap k M)) := by
  refine le_antisymm
    (fun g hg => mem_map_adjointGroup_of_frobenius_fixed hτ Fr hFr hbij hg.1 hg.2) ?_
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨baseChangeGL_mem_adjointGroup _ hg,
    units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr g⟩

theorem G2_F4_exact_finite_field_fixed_root_matrices (τ : Tag) (hτ : τ = .G2 ∨ τ = .F4)
    (K : Type) [Field K] [Finite K] (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (F : L →+* L) (hF : ∀ c, F c = c ^ Nat.card K) :
    adjointGroup τ L ⊓ (Units.map (entrywiseHom F)).eqLocus (MonoidHom.id _) =
        (adjointGroup τ K).map (baseChangeGL (algebraMap K L)) ∧
      ∀ (E : IntermediateField K L) [Finite E] (σ : E →+* E), (∀ c, σ c = c ^ Nat.card K) →
        adjointGroup τ E ⊓ (Units.map (entrywiseHom σ)).eqLocus (MonoidHom.id _) =
          (adjointGroup τ K).map (baseChangeGL (algebraMap K E)) := by
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  exact ⟨frobenius_fixed_eq_map_of_bijective hτ F hF (frobenius_bijective (k := K) F hF),
    fun E _ σ hσ => frobenius_fixed_eq_map_of_bijective hτ σ hσ
      (Finite.injective_iff_bijective.1 σ.injective)⟩

end CFSG.RankThree.Chevalley

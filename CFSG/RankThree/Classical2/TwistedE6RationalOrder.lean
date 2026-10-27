module

public import CFSG.LieType.Chevalley.AmbientTwistedFrobeniusFixedNormalizer
public import CFSG.ClassicalInvolution.Orders.Twisted
public import CFSG.LieType.Chevalley.RootDiagonalWeylTransporter
public import CFSG.RankThree.Classical2.MatrixFrobeniusLang

public noncomputable section

namespace CFSG.RankThree.Classical2

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.Timmesfeld.ExceptionalOrders CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Pointwise

section BaseChange

variable {τ : Tag} {K L : Type} [Field K] [Field L] (ι : K →+* L)

theorem baseChangeGL_mem_torusGroup {h : ModGL τ K} (hh : h ∈ torusGroup τ K) :
    baseChangeGL ι h ∈ torusGroup τ L := by
  have hle : torusGroup τ K ≤ (torusGroup τ L).comap (baseChangeGL ι) := by
    rw [torusGroup, Subgroup.closure_le]
    rintro _ ⟨⟨i, t⟩, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_torusElt]
    exact torusElt_mem_torusGroup i _
  exact hle hh

theorem baseChangeGL_mem_rootSpan {S : Set (Fin τ.rank → ℤ)} {g : ModGL τ K}
    (hg : g ∈ rootSpan τ K S) : baseChangeGL ι g ∈ rootSpan τ L S := by
  have hle : rootSpan τ K S ≤ (rootSpan τ L S).comap (baseChangeGL ι) := by
    refine iSup₂_le fun α hα => ?_
    show rootSubgroup τ K α ≤ (rootSpan τ L S).comap (baseChangeGL ι)
    rw [rootSubgroup, Subgroup.closure_le]
    rintro _ ⟨c, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, baseChangeGL_pinnedX]
    exact (le_iSup₂_of_le (f := fun β (_ : β ∈ S) => rootSubgroup τ L β) α hα le_rfl)
      (Subgroup.subset_closure ⟨ι c, rfl⟩)
  exact hle hg

theorem mem_torusGroup_of_baseChangeGL_mem {x : ModGL τ K} (hx : x ∈ adjointGroup τ K)
    (hxL : baseChangeGL ι x ∈ torusGroup τ L) : x ∈ torusGroup τ K := by
  obtain ⟨w, -, h, hh, u, hu, v, hv, rfl⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors τ K (1 : Fin τ.rank → Kˣ)).1 x
      (mem_toralCentralizer.2 ⟨hx, by rw [rootDiagUnit_one, one_mul, inv_one, mul_one]⟩)
  have hu' : u ∈ posUnipotent τ K := rootSpan_mono Set.inter_subset_right hu
  have hv' : v ∈ rootSpan τ K (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  have heq : baseChangeGL ι h * baseChangeGL ι u * canonicalRep (coxeterSystem τ) L w *
      baseChangeGL ι v = baseChangeGL ι (h * u * canonicalRep (coxeterSystem τ) K w * v) * 1 *
        canonicalRep (coxeterSystem τ) L 1 * 1 := by
    rw [canonicalRep_one, mul_one, mul_one, mul_one, map_mul, map_mul, map_mul,
      baseChangeGL_canonicalRep]
  obtain ⟨rfl, -, hu1, hv1⟩ :=
    (Chevalley_toral_centralizer_Bruhat_factors τ L (1 : Fin τ.rank → Lˣ)).2.1 w 1 _ _ _ 1 _ 1
      (baseChangeGL_mem_torusGroup ι hh) hxL (baseChangeGL_mem_rootSpan ι hu') (one_mem _)
      (baseChangeGL_mem_rootSpan ι hv') (one_mem _) heq
  have hu2 : u = 1 := baseChangeGL_injective ι (by rw [hu1, map_one])
  have hv2 : v = 1 := baseChangeGL_injective ι (by rw [hv1, map_one])
  rw [hu2, hv2, canonicalRep_one, mul_one, mul_one, mul_one]
  exact hh

end BaseChange

section Torus

variable {Ω : Type} [Field Ω]

theorem torusGroup_le_adjointGroup_of_field {τ : Tag} {K : Type} [Field K] :
    torusGroup τ K ≤ adjointGroup τ K := by
  refine (Subgroup.closure_le _).2 ?_
  rintro _ ⟨⟨i, t⟩, rfl⟩
  exact torusElt_mem_adjointGroup i t

theorem natCard_graphFixedTorus_eq_compatSubgroup [IsAlgClosed Ω] {t : TwistTag}
    (Fr : Ω →+* Ω) :
    Nat.card (graphFixedTorus t Ω Fr) = Nat.card (compatSubgroup (t := t) Fr) := by
  refine (Nat.card_congr (Equiv.ofBijective (fun b : compatSubgroup (t := t) Fr =>
    (⟨rootDiagUnit t.tag b.1, rootDiagUnit_mem_torusGroup b.1,
      torusGroup_le_adjointGroup_of_field (rootDiagUnit_mem_torusGroup b.1),
      twistHom_rootDiagUnit ((mem_compatSubgroup Fr).1 b.2)⟩ : graphFixedTorus t Ω Fr))
    ⟨fun b b' h => ?_, fun x => ?_⟩)).symm
  · exact Subtype.ext (rootDiagUnit_injective (congrArg Subtype.val h))
  · obtain ⟨hxT, hxR⟩ := Subgroup.mem_inf.1 x.2
    obtain ⟨l, hl⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hxT
    have hfix : twistHom t Ω Fr (rootDiagUnit t.tag l) = rootDiagUnit t.tag l := by
      rw [← hl]
      exact ((mem_twistedFixedGroup_iff_twistHom t Ω Fr).1 hxR).2
    exact ⟨⟨l, (mem_compatSubgroup Fr).2 fun i => compat_of_twistHom_rootDiagUnit hfix i⟩,
      Subtype.ext hl.symm⟩

theorem natCard_orbitField_of_isAlgClosed [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ]
    (hf : f ≠ 0) {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) (t : TwistTag)
    (a : Fin t.foldedTag.rank) :
    Nat.card (orbitField t Ω Fr a) = (ℓ ^ f) ^ (t.orbit a).card := by
  have hset : (orbitField t Ω Fr a : Set Ω) = {c : Ω | c ^ ℓ ^ (f * (t.orbit a).card) = c} := by
    ext c
    rw [SetLike.mem_coe, mem_orbitField, pow_apply_eq_pow hFr, ← pow_mul, Set.mem_ofPred_eq]
  rw [← SetLike.coe_sort_coe, hset, natCard_setOf_pow_eq_self (ℓ := ℓ)
    (mul_ne_zero hf (Finset.card_ne_zero.2 (t.orbit_nonempty a))), pow_mul]

theorem natCard_graphFixedTorus_E6 [IsAlgClosed Ω] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP Ω ℓ]
    (hf : f ≠ 0) {Fr : Ω →+* Ω} (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    Nat.card (graphFixedTorus TwistTag.E6 Ω Fr) = ((ℓ ^ f) ^ 2 - 1) ^ 2 * (ℓ ^ f - 1) ^ 2 := by
  rw [natCard_graphFixedTorus_eq_compatSubgroup, card_compatSubgroup]
  simp only [natCard_orbitField_of_isAlgClosed hf hFr]
  rw [prod_orbit_E6]
  ring

end Torus

theorem natCard_compatTorus_E6_mul {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {K : Type} [Field K]
    (hK : Nat.card K = (ℓ ^ f) ^ 2) {σ : K →+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    Nat.card (compatTorus (t := TwistTag.E6) σ) * Nat.gcd 3 (ℓ ^ f + 1) =
      ((ℓ ^ f) ^ 2 - 1) ^ 2 * (ℓ ^ f - 1) ^ 2 := by
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have hq := CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.E6) hℓ hf hK hσ
  have h := card_compatTorus_mul (t := TwistTag.E6) (K := K) σ
  rw [CFSG.ClassicalInvolution.card_compat_inf_ker_E6_of_card hK hσ, card_compatSubgroup] at h
  simp only [hq] at h
  rw [h, prod_orbit_E6]
  ring

theorem inf_graphFixedTorus_map_eq {t : TwistTag} {K Ω : Type} [Field K] [Field Ω]
    (ι : K →+* Ω) (σ : K →+* K) (Fr : Ω →+* Ω)
    (hle : (graphFixedRootGroup t K σ).map (baseChangeGL ι) ≤ twistedFixedGroup t Ω Fr) :
    graphFixedTorus t Ω Fr ⊓ (graphFixedRootGroup t K σ).map (baseChangeGL ι) =
      (graphFixedRootTorus t K σ).map (baseChangeGL ι) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨⟨hxT, -⟩, y, hy, rfl⟩
    have hyR := graphFixedRootGroup_le t K σ hy
    exact ⟨y, ⟨⟨mem_torusGroup_of_baseChangeGL_mem ι (Subgroup.mem_inf.1 hyR).1 hxT, hyR⟩, hy⟩,
      rfl⟩
  · rintro _ ⟨y, ⟨⟨hyT, -⟩, hy⟩, rfl⟩
    exact ⟨⟨baseChangeGL_mem_torusGroup ι hyT, hle ⟨y, hy, rfl⟩⟩, y, hy, rfl⟩

theorem twisted_E6_full_rational_fixed_group_order {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (K : Type) [Field K] (hK : Nat.card K = (ℓ ^ f) ^ 2) (σ : K →+* K)
    (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) (Ω : Type) [Field Ω] [Algebra K Ω] [IsAlgClosure K Ω]
    (Fr : Ω →+* Ω) (hFr : ∀ c, Fr c = c ^ (ℓ ^ f)) :
    Finite (twistedFixedGroup TwistTag.E6 Ω Fr) ∧
    (twistedFixedGroup TwistTag.E6 Ω Fr : Set (ModGL TwistTag.E6.tag Ω)) =
      (graphFixedTorus TwistTag.E6 Ω Fr : Set (ModGL TwistTag.E6.tag Ω)) *
        ((graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K Ω)) :
          Set (ModGL TwistTag.E6.tag Ω)) ∧
    ⁅twistedFixedGroup TwistTag.E6 Ω Fr, twistedFixedGroup TwistTag.E6 Ω Fr⁆ =
      (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K Ω)) ∧
    (∃ k : ℕ, (((graphFixedRootGroup TwistTag.E6 K σ).map
      (baseChangeGL (algebraMap K Ω))).subgroupOf (twistedFixedGroup TwistTag.E6 Ω Fr)).index =
        3 ^ k) ∧
    Nat.card (graphFixedTorus TwistTag.E6 Ω Fr) = ((ℓ ^ f) ^ 2 - 1) ^ 2 * (ℓ ^ f - 1) ^ 2 ∧
    Nat.card (twistedFixedGroup TwistTag.E6 Ω Fr) =
      (ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) * ((ℓ ^ f) ^ 8 - 1) *
        ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1) ∧
    ∀ p : ℕ, p.Prime → 3 < p →
      ordProj[p] (Nat.card ((graphFixedRootGroup TwistTag.E6 K σ).map
        (baseChangeGL (algebraMap K Ω)))) =
      ordProj[p] (Nat.card (twistedFixedGroup TwistTag.E6 Ω Fr)) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed K
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by
    rw [hK]
    exact pow_ne_zero _ (pow_ne_zero _ hℓ.ne_zero))
  have : Fintype K := Fintype.ofFinite K
  have : CharP K ℓ := charP_of_card_eq_prime_pow (f := f * 2)
    (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
  have : CharP Ω ℓ := charP_of_injective_algebraMap (algebraMap K Ω).injective ℓ
  have : Finite (Module.End K (RootModule TwistTag.E6.tag K)) := Module.finite_of_finite K
  have : Finite (ModGL TwistTag.E6.tag K) := inferInstance
  have : Fintype (WeylGroup TwistTag.E6.tag) := Fintype.ofFinite _
  have hσsurj : Function.Surjective σ := Finite.surjective_of_injective σ.injective
  have hq1 : 1 ≤ ℓ ^ f := Nat.one_le_pow _ _ hℓ.pos
  obtain ⟨hmul, hle, hnormal, -, hder, -⟩ :=
    exceptional_ambient_twisted_Frobenius_fixed_normalizer TwistTag.E6 hℓ hf K hK σ hσ Ω Fr hFr
  have hTC := inf_graphFixedTorus_map_eq (algebraMap K Ω) σ Fr hle
  have hTcard := natCard_graphFixedTorus_E6 (by omega : f ≠ 0) hFr
  have hcompat := natCard_compatTorus_E6_mul hℓ hf hK hσ
  have hC0 := card_graphFixedRootGroup hσsurj
    (CFSG.Timmesfeld.ExceptionalOrders.card_orbitField (t := TwistTag.E6) hℓ hf hK hσ)
  rw [sum_length_relWeylTwist_E6, ncard_posRoots_twistedE6] at hC0
  set R := twistedFixedGroup TwistTag.E6 Ω Fr
  set T := graphFixedTorus TwistTag.E6 Ω Fr
  set C := (graphFixedRootGroup TwistTag.E6 K σ).map (baseChangeGL (algebraMap K Ω))
  have hTCcard : Nat.card ↥(T ⊓ C) = Nat.card (compatTorus (t := TwistTag.E6) σ) := by
    rw [hTC, Subgroup.card_map_of_injective (baseChangeGL_injective _),
      graphFixedRootTorus_eq_compatTorus hσsurj]
  have hTR : T ≤ R := graphFixedTorus_le TwistTag.E6 Ω Fr
  have hsup : T.subgroupOf R ⊔ C.subgroupOf R = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨x, hx⟩ -
    have hx' : x ∈ (T : Set (ModGL TwistTag.E6.tag Ω)) *
        (C : Set (ModGL TwistTag.E6.tag Ω)) := by
      rw [← hmul]
      exact hx
    obtain ⟨a, ha, b, hb, rfl⟩ := hx'
    have e : (⟨a * b, hx⟩ : R) = ⟨a, hTR ha⟩ * ⟨b, hle hb⟩ := rfl
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.2 ha))
      (Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.2 hb))
  have hindex : (C.subgroupOf R).index * Nat.card ↥(T ⊓ C) = Nat.card T := by
    have := hnormal
    have h1 := Subgroup.relIndex_sup_right (H := T.subgroupOf R) (K := C.subgroupOf R)
    rw [hsup, Subgroup.relIndex_top_right] at h1
    have h2 := Subgroup.relIndex_mul_card (H := C.subgroupOf R) (K := T.subgroupOf R)
    rw [← h1] at h2
    have e : C.subgroupOf R ⊓ T.subgroupOf R = (T ⊓ C).subgroupOf R := by
      ext x
      rw [Subgroup.mem_inf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf,
        Subgroup.mem_subgroupOf, Subgroup.mem_inf]
      exact and_comm
    rw [e, Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left.trans hTR)).toEquiv,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTR).toEquiv] at h2
    exact h2
  have hidx : (C.subgroupOf R).index = Nat.gcd 3 (ℓ ^ f + 1) := by
    have hpos : 0 < Nat.card (compatTorus (t := TwistTag.E6) σ) := Nat.card_pos
    rw [hTCcard, hTcard, ← hcompat] at hindex
    exact Nat.eq_of_mul_eq_mul_right hpos (hindex.trans (mul_comm _ _))
  have hCcard : Nat.card C = Nat.card (graphFixedRootGroup TwistTag.E6 K σ) :=
    Subgroup.card_map_of_injective (baseChangeGL_injective _)
  have hRC : Nat.card R = Nat.gcd 3 (ℓ ^ f + 1) * Nat.card C := by
    have h := Subgroup.card_mul_index (H := C.subgroupOf R)
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv, hidx] at h
    rw [← h, mul_comm]
  have hg0 : Nat.gcd 3 (ℓ ^ f + 1) ≠ 0 := (Nat.gcd_pos_of_pos_left _ (by norm_num)).ne'
  have hCpos : Nat.card C ≠ 0 := by
    rw [hCcard]
    exact Nat.card_pos.ne'
  have hRcard : Nat.card R = (ℓ ^ f) ^ 36 * ((ℓ ^ f) ^ 12 - 1) * ((ℓ ^ f) ^ 9 + 1) *
      ((ℓ ^ f) ^ 8 - 1) * ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 5 + 1) * ((ℓ ^ f) ^ 2 - 1) := by
    rw [hRC, hCcard, hC0, ← ordTwistedE6_mul _ hq1]
    have e : ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 2 - 1) * (ℓ ^ f - 1) * (ℓ ^ f - 1) =
        Nat.card (compatTorus (t := TwistTag.E6) σ) * Nat.gcd 3 (ℓ ^ f + 1) := by
      rw [hcompat]
      ring
    rw [e]
    ring
  have hg : Nat.gcd 3 (ℓ ^ f + 1) = 1 ∨ Nat.gcd 3 (ℓ ^ f + 1) = 3 :=
    (Nat.dvd_prime Nat.prime_three).1 (Nat.gcd_dvd_left 3 (ℓ ^ f + 1))
  refine ⟨Nat.finite_of_card_ne_zero (by rw [hRC]; exact mul_ne_zero hg0 hCpos), hmul, hder,
    ?_, hTcard, hRcard, ?_⟩
  · rw [hidx]
    rcases hg with hg | hg
    · exact ⟨0, by rw [hg, pow_zero]⟩
    · exact ⟨1, by rw [hg, pow_one]⟩
  · intro p hp hp3
    have hndvd : ¬ p ∣ Nat.gcd 3 (ℓ ^ f + 1) := by
      intro hdvd
      rcases hg with hg | hg <;> rw [hg] at hdvd
      · exact hp.one_lt.ne' (Nat.dvd_one.1 hdvd)
      · exact (by omega : p ≠ 3) ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 hdvd)
    rw [hRC, Nat.factorization_mul hg0 hCpos, Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hndvd, zero_add]

end CFSG.RankThree.Classical2

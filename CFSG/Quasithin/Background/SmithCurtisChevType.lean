module

public import CFSG.Quasithin.Background.SmithCurtisChev
public import CFSG.LieType.Chevalley.SylowOpposition
public import CFSG.Quasithin.Background.SmithCurtisMain

public noncomputable section

namespace CFSG.Quasithin.SmithCurtis.Chev

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

variable {τ : Tag} {K : Type} [Field K]

theorem xC_injective
    (i : Fin τ.rank) : Function.Injective (xC τ K i) :=
  fun _ _ h => xUnit_injective i (congrArg Subtype.val h)

theorem xC_ne_one
    (i : Fin τ.rank) (c : Kˣ) : xC τ K i c ≠ 1 := by
  intro h
  have h1 : xUnit τ K i ((c : Kˣ) : K) = xUnit τ K i 0 := by
    rw [xUnit_zero]
    exact congrArg Subtype.val h
  exact c.ne_zero (xUnit_injective i h1)

theorem dC_mul
    (i : Fin τ.rank) (s t : Kˣ) :
    dC τ K i (s * t) = dC τ K i s * dC τ K i t :=
  Subtype.ext (torusElt_mul i s t)

theorem dC_one
    (i : Fin τ.rank) : dC τ K i 1 = 1 :=
  Subtype.ext (torusElt_one i)

variable [Finite K] {p : ℕ} [CharP K p]
  {hw : ∃ w₁ : WeylGroup τ, ∀ α : Fin τ.rank → ℤ, w₁ • α = -α}

theorem mem_X_chevDatum
    {i : Fin τ.rank} {x : adjointGroup τ K} :
    x ∈ (chevDatum τ K p hw).X i ↔ ∃ c : K, xC τ K i c = x := by
  change (x : ModGL τ K) ∈ rootSubgroup τ K (Pi.single i 1) ↔ _
  rw [mem_rootSubgroup_single]
  exact ⟨fun ⟨c, hc⟩ => ⟨c, Subtype.ext hc⟩, fun ⟨c, hc⟩ => ⟨c, congrArg Subtype.val hc⟩⟩

theorem xC_mem_X
    (i : Fin τ.rank) (c : K) : xC τ K i c ∈ (chevDatum τ K p hw).X i :=
  mem_X_chevDatum.mpr ⟨c, rfl⟩

theorem heckeT_chevDatum
    [Fintype K] {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] (ρ : Representation k (adjointGroup τ K) V) (i : Fin τ.rank) (v : V) :
    (chevDatum τ K p hw).heckeT ρ i v = ∑ c : K, ρ (xC τ K i c * nC τ K i) v := by
  have := Fintype.ofFinite ((chevDatum τ K p hw).X i)
  rw [CurtisDatum.heckeT_apply]
  symm
  refine Fintype.sum_bijective (fun c => ⟨xC τ K i c, xC_mem_X i c⟩) ⟨fun c d h =>
    xC_injective i (congrArg Subtype.val h), fun x => ?_⟩ _ _ fun c => rfl
  obtain ⟨c, hc⟩ := mem_X_chevDatum.mp x.2
  exact ⟨c, Subtype.ext hc⟩

theorem psi_chevDatum
    (i : Fin τ.rank) (c : Kˣ) :
    (chevDatum τ K p hw).psi i (xC τ K i c) = dC τ K i (-c) :=
  torusPart_eq rfl

theorem phi_chevDatum
    (i : Fin τ.rank) (c : Kˣ) :
    (chevDatum τ K p hw).phi i (xC τ K i c) = dC τ K i (-c) :=
  torusPart_eq rfl

theorem sum_X_erase_eq
    [Fintype Kˣ] {M : Type*} [AddCommMonoid M] (i : Fin τ.rank)
    {_ : Fintype ((chevDatum τ K p hw).X i)} {_ : DecidableEq ((chevDatum τ K p hw).X i)}
    (f : adjointGroup τ K → M) :
    ∑ x ∈ (Finset.univ : Finset ((chevDatum τ K p hw).X i)).erase 1, f x =
      ∑ t : Kˣ, f (xC τ K i (-(t : K))) := by
  symm
  refine Finset.sum_nbij (fun t => ⟨xC τ K i (-(t : K)), xC_mem_X i _⟩) (fun t _ => ?_)
    (fun t _ t' _ h => ?_) (fun x hx => ?_) fun t _ => rfl
  · refine Finset.mem_erase.mpr ⟨fun h => ?_, Finset.mem_univ _⟩
    have h1 := congrArg Subtype.val h
    exact xC_ne_one i (-t) h1
  · have h1 := xC_injective i (congrArg Subtype.val h)
    exact Units.ext (neg_inj.mp h1)
  · obtain ⟨c, hc⟩ := mem_X_chevDatum.mp x.2
    have hc0 : c ≠ 0 := by
      rintro rfl
      apply (Finset.mem_erase.mp hx).1
      refine Subtype.ext ?_
      rw [← hc]
      exact Subtype.ext (xUnit_zero i)
    refine ⟨-Units.mk0 c hc0, Finset.mem_coe.mpr (Finset.mem_univ _), Subtype.ext ?_⟩
    simp only [Units.val_neg, Units.val_mk0, neg_neg]
    exact hc

theorem d'Scalar_chevDatum
    [Fintype Kˣ] {k : Type*} [Field k]
    (χ : adjointGroup τ K → k) (i : Fin τ.rank) :
    (chevDatum τ K p hw).d'Scalar χ i = ∑ t : Kˣ, χ (dC τ K i t) := by
  classical
  unfold CurtisDatum.d'Scalar
  dsimp only
  rw [sum_X_erase_eq i (fun x => χ ((chevDatum τ K p hw).psi i x))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show (-(t : K)) = ((-t : Kˣ) : K) from (Units.val_neg t).symm, psi_chevDatum, neg_neg]

theorem dScalar_chevDatum
    [Fintype Kˣ] {k : Type*} [Field k]
    (χ : adjointGroup τ K → k) (i : Fin τ.rank) :
    (chevDatum τ K p hw).dScalar χ i = ∑ t : Kˣ, χ (dC τ K i t) := by
  classical
  unfold CurtisDatum.dScalar
  dsimp only
  rw [sum_X_erase_eq i (fun x => χ ((chevDatum τ K p hw).phi i x))]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [show (-(t : K)) = ((-t : Kˣ) : K) from (Units.val_neg t).symm, phi_chevDatum, neg_neg]

theorem dC_mem_H
    (i : Fin τ.rank) (t : Kˣ) : dC τ K i t ∈ (chevDatum τ K p hw).H :=
  torusElt_mem_torusGroup i t

theorem splitOver_torus
    (k : Type*) [Field k] [Algebra K k] :
    SplitOver k (chevDatum τ K p hw).H := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨g, hg⟩ := IsCyclic.exists_ofOrder_eq_natCard (α := Kˣ)
  have hq : 0 < Nat.card K - 1 := by
    have := Finite.one_lt_card_iff_nontrivial.mpr (inferInstance : Nontrivial K)
    omega
  have hprim : IsPrimitiveRoot (algebraMap K k (g : K)) (Nat.card K - 1) := by
    have h1 : IsPrimitiveRoot (g : K) (Nat.card K - 1) := by
      rw [← Nat.card_units K, ← hg, ← orderOf_units]
      exact IsPrimitiveRoot.orderOf _
    exact h1.map_of_injective (algebraMap K k).injective
  intro h hh
  refine ⟨Nat.card K - 1, ?_, (Polynomial.nthRootsFinset (Nat.card K - 1) (1 : k)).toList,
    ?_⟩
  · refine Subtype.ext ?_
    rw [SubgroupClass.coe_pow, OneMemClass.coe_one]
    exact pow_card_sub_one_eq_one_of_mem_diagonalGroup (torusGroup_le_diagonalGroup hh)
  · rw [Finset.prod_map_toList]
    exact Polynomial.X_pow_sub_one_eq_prod hq hprim

theorem sum_chi_torusElt
    [Fintype Kˣ] {k V : Type*} [Field k] [AddCommGroup V]
    [Module k V] {ρ : Representation k (adjointGroup τ K) V} {y : V}
    {χ : adjointGroup τ K → k} {μ : Fin τ.rank → k}
    (ht : (chevDatum τ K p hw).IsCurtisType ρ y χ μ) (i : Fin τ.rank)
    (hi : ¬ ∀ t : Kˣ, χ (dC τ K i t) = 1) : ∑ t : Kˣ, χ (dC τ K i t) = 0 := by
  let f : Kˣ →* k :=
    { toFun := fun t => χ (dC τ K i t)
      map_one' := by rw [dC_one, ht.chi_one]
      map_mul' := fun s t => by rw [dC_mul, ht.chi_mul (dC_mem_H i s) (dC_mem_H i t)] }
  refine sum_hom_units_eq_zero f fun hf => hi fun t => ?_
  exact DFunLike.congr_fun hf t

variable (τ K p hw) in
@[expose] def IsChevType
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    (ρ : Representation k (adjointGroup τ K) V) (y : V) (χ : adjointGroup τ K → k)
    (J : Finset (Fin τ.rank)) : Prop :=
  y ∈ (chevDatum τ K p hw).fixU ρ ∧ y ≠ 0 ∧ (∀ h ∈ (chevDatum τ K p hw).H, ρ h y = χ h • y) ∧
    ∀ i, i ∈ J ↔ (∀ t : Kˣ, χ (dC τ K i t) = 1) ∧ (chevDatum τ K p hw).heckeT ρ i y = 0

theorem IsChevType.subset
    {k V : Type*} [Field k] [AddCommGroup V] [Module k V]
    {ρ : Representation k (adjointGroup τ K) V} {y : V} {χ : adjointGroup τ K → k}
    {J : Finset (Fin τ.rank)} (ht : IsChevType τ K p hw ρ y χ J) {i : Fin τ.rank}
    (hi : i ∈ J) : ∀ t : Kˣ, χ (dC τ K i t) = 1 :=
  ((ht.2.2.2 i).mp hi).1

theorem IsChevType.exists_mu
    [Fact p.Prime] {k V : Type*} [Field k] [Algebra K k]
    [AddCommGroup V] [Module k V] [CharP k p]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) {y : V}
    {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)} (ht : IsChevType τ K p hw ρ y χ J) :
    ∃ μ : Fin τ.rank → k, (chevDatum τ K p hw).IsCurtisType ρ y χ μ := by
  have hU : ∀ i, (chevDatum τ K p hw).heckeT ρ i y ∈ (chevDatum τ K p hw).fixU ρ :=
    fun i => (chevDatum τ K p hw).heckeT_mem_fixU ρ i ht.1
  obtain ⟨y₀, χ₀, μ₀, ht₀⟩ := (chevDatum τ K p hw).exists_isCurtisType (splitOver_torus k) hρ
  have hsmul : ∀ x ∈ (chevDatum τ K p hw).fixU ρ, ∃ c : k, x = c • y := by
    intro x hx
    obtain ⟨c, hc⟩ := (chevDatum τ K p hw).fixU_eq_smul hρ ht₀ hx
    obtain ⟨d, hd⟩ := (chevDatum τ K p hw).fixU_eq_smul hρ ht₀ ht.1
    have hd0 : d ≠ 0 := by
      rintro rfl
      exact ht.2.1 (by rw [hd, zero_smul])
    refine ⟨c * d⁻¹, ?_⟩
    rw [hc, hd, smul_smul, mul_assoc, inv_mul_cancel₀ hd0, mul_one]
  exact ⟨fun i => (hsmul _ (hU i)).choose, ht.1, ht.2.1, ht.2.2.1,
    fun i => (hsmul _ (hU i)).choose_spec⟩

theorem exists_isChevType
    [Fact p.Prime] {k V : Type*} [Field k] [Algebra K k]
    [AddCommGroup V] [Module k V] [CharP k p]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) :
    ∃ y : V, ∃ χ : adjointGroup τ K → k, ∃ J : Finset (Fin τ.rank),
      IsChevType τ K p hw ρ y χ J := by
  classical
  obtain ⟨y, χ, μ, ht⟩ := (chevDatum τ K p hw).exists_isCurtisType (splitOver_torus k) hρ
  refine ⟨y, χ, Finset.univ.filter fun i => (∀ t : Kˣ, χ (dC τ K i t) = 1) ∧
    (chevDatum τ K p hw).heckeT ρ i y = 0, ht.1, ht.2.1, ht.2.2.1, fun i => ?_⟩
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem IsChevType.unique
    [Fact p.Prime] {k V : Type*} [Field k] [Algebra K k]
    [AddCommGroup V] [Module k V] [CharP k p]
    {ρ : Representation k (adjointGroup τ K) V} (hρ : IsSimpleRep ρ) {y y' : V}
    {χ χ' : adjointGroup τ K → k} {J J' : Finset (Fin τ.rank)}
    (ht : IsChevType τ K p hw ρ y χ J) (ht' : IsChevType τ K p hw ρ y' χ' J') :
    (∀ h ∈ (chevDatum τ K p hw).H, χ h = χ' h) ∧ J = J' := by
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  obtain ⟨μ', hμ'⟩ := ht'.exists_mu hρ
  obtain ⟨hχ, hμμ⟩ := hμ.unique hρ hμ'
  obtain ⟨c, hc⟩ := (chevDatum τ K p hw).fixU_eq_smul hρ hμ ht'.1
  have hc0 : c ≠ 0 := by
    rintro rfl
    exact ht'.2.1 (by rw [hc, zero_smul])
  refine ⟨hχ, Finset.ext fun i => ?_⟩
  rw [ht.2.2.2 i, ht'.2.2.2 i, hc, map_smul, smul_eq_zero, or_iff_right hc0]
  have e : ∀ t : Kˣ, χ (dC τ K i t) = χ' (dC τ K i t) := fun t => hχ _ (dC_mem_H i t)
  simp only [e]

open Classical in
theorem IsChevType.mu_eq
    [Fact p.Prime] [Fintype Kˣ] {k V : Type*} [Field k]
    [AddCommGroup V] [Module k V] [CharP k p] {ρ : Representation k (adjointGroup τ K) V}
    {y : V} {χ : adjointGroup τ K → k} {J : Finset (Fin τ.rank)}
    (ht : IsChevType τ K p hw ρ y χ J) {μ : Fin τ.rank → k}
    (hμ : (chevDatum τ K p hw).IsCurtisType ρ y χ μ) (i : Fin τ.rank) :
    μ i = if (∀ t : Kˣ, χ (dC τ K i t) = 1) ∧ i ∉ J then ∑ t : Kˣ, χ (dC τ K i t) else 0 := by
  have hmu := hμ.mu_eq i
  rw [d'Scalar_chevDatum] at hmu
  split_ifs with h
  · obtain ⟨hS, hJ⟩ := h
    rcases hmu with h0 | h1
    · exfalso
      apply hJ
      rw [ht.2.2.2 i]
      exact ⟨hS, by rw [hμ.2.2.2 i, h0, zero_smul]⟩
    · exact h1
  · rcases hmu with h0 | h1
    · exact h0
    · rw [h1]
      by_cases hS : ∀ t : Kˣ, χ (dC τ K i t) = 1
      · have hJ : i ∈ J := by
          by_contra hJ
          exact h ⟨hS, hJ⟩
        have hT := ((ht.2.2.2 i).mp hJ).2
        rw [hμ.2.2.2 i] at hT
        have hμ0 : μ i = 0 := (smul_eq_zero.mp hT).resolve_right ht.2.1
        rw [← h1, hμ0]
      · exact sum_chi_torusElt hμ i hS

theorem iso_of_isChevType
    [Fact p.Prime] {k V V' : Type*} [Field k] [Algebra K k]
    [AddCommGroup V] [Module k V] [AddCommGroup V'] [Module k V'] [CharP k p]
    {ρ : Representation k (adjointGroup τ K) V} {ρ' : Representation k (adjointGroup τ K) V'}
    (hρ : IsSimpleRep ρ) (hρ' : IsSimpleRep ρ') {y : V} {y' : V'} {χ : adjointGroup τ K → k}
    {J : Finset (Fin τ.rank)} (ht : IsChevType τ K p hw ρ y χ J)
    (ht' : IsChevType τ K p hw ρ' y' χ J) :
    ∃ β : V ≃ₗ[k] V', ∀ (g : adjointGroup τ K) (v : V), β (ρ g v) = ρ' g (β v) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨μ, hμ⟩ := ht.exists_mu hρ
  obtain ⟨μ', hμ'⟩ := ht'.exists_mu hρ'
  have hμμ : μ = μ' := funext fun i => by rw [ht.mu_eq hμ i, ht'.mu_eq hμ' i]
  rw [← hμμ] at hμ'
  exact (chevDatum τ K p hw).iso_of_isCurtisType hρ hρ' hμ hμ'

end CFSG.Quasithin.SmithCurtis.Chev

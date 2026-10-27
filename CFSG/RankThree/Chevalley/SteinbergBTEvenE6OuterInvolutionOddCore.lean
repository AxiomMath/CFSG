module

public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6FieldInvolutionOddCore
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6CanonicalGraphOddCore
public import CFSG.RankThree.Chevalley.SteinbergBTEvenE6SecondGraphTransfer
public import CFSG.RankThree.Chevalley.SteinbergBTTwistedE6ModelCover
public import CFSG.LieType.Chevalley.E6GraphFullDiagonalCoset
public import CFSG.LocalAnalysis.ComponentClassification.SteinbergBNEvenInnerInvolutionOddCore

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LieType.Chevalley.E6GraphFullCoset (IsOrdinaryDiagGraph)
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit)
open CFSG.ComponentClassification (OuterAutomorphisms.inner OuterAutomorphisms.inner_normal)
open CFSG.LieType.Chevalley.E6SecondGraphFull (secondGraphFullCentralizer_adjointGroup
  secondGraphFullCentralizer_graphFixedRootGroup)
open CFSG.ComponentClassification.UnbalancedCatalog (EvenCatalog.oddCore_eq_bot_of_mulEquiv)

theorem oddCore_eq_pPrimeCore_two' (X : Type*) [Group X] :
    CFSG.oddCore X = CFSG.pPrimeCore 2 X := by
  unfold CFSG.oddCore CFSG.pPrimeCore
  congr 1
  ext L
  simp only [Set.mem_ofPred_eq, Nat.coprime_two_left]

@[expose] def inf_centralizer_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (L : Subgroup (MulAut A)) (x : MulAut A) :
    ↥(L ⊓ Subgroup.centralizer {x}) ≃*
      ↥(L.map (MulAut.congr e).toMonoidHom ⊓ Subgroup.centralizer {MulAut.congr e x}) :=
  ((MulAut.congr e).subgroupMap (L ⊓ Subgroup.centralizer {x})).trans
    (MulEquiv.subgroupCongr (by
      ext y
      simp only [Subgroup.mem_inf, Subgroup.mem_map, Subgroup.mem_centralizer_singleton_iff]
      constructor
      · rintro ⟨z, ⟨hzL, hzx⟩, rfl⟩
        refine ⟨⟨z, hzL, rfl⟩, ?_⟩
        change MulAut.congr e z * MulAut.congr e x = MulAut.congr e x * MulAut.congr e z
        rw [← map_mul, ← map_mul, hzx]
      · rintro ⟨⟨z, hzL, rfl⟩, hzx⟩
        refine ⟨z, ⟨hzL, ?_⟩, rfl⟩
        apply (MulAut.congr e).injective
        change MulAut.congr e z * MulAut.congr e x = MulAut.congr e x * MulAut.congr e z at hzx
        rw [map_mul, map_mul, hzx]))

theorem oddCore_inf_centralizer_inner_of_F4 {G : Type*} [Group G] {J : Subgroup G} {f : ℕ}
    (hf : 1 ≤ f) (k : Type) [Field k] (hk : Nat.card k = 2 ^ f) (e : J ≃* adjointGroup Tag.F4 k)
    {t : G} (htJ : t ∈ J) (ht2 : t * t = 1) (ht1 : t ≠ 1) (τJ : MulAut J)
    (hτJ : ∀ x : J, (τJ x : G) = t * x * t⁻¹) (L : Subgroup (MulAut J))
    (hL : OuterAutomorphisms.inner J ≤ L) :
    CFSG.oddCore ↥(L ⊓ Subgroup.centralizer {τJ}) = ⊥ := by
  have hτ : τJ = MulAut.conj (⟨t, htJ⟩ : J) := MulEquiv.ext fun x => Subtype.ext (hτJ x)
  subst hτ
  set Φ := MulAut.congr e with hΦ
  have hΦconj : ∀ y : J, Φ (MulAut.conj y) = MulAut.conj (e y) := fun y =>
    MulEquiv.ext fun b => by
      change e (y * e.symm b * y⁻¹) = e y * b * (e y)⁻¹
      rw [map_mul, map_mul, map_inv, MulEquiv.apply_symm_apply]
  have hZJ : Subgroup.center J = ⊥ := center_eq_bot_of_mulEquiv_adjointGroup k e
  have htord : orderOf (⟨t, htJ⟩ : J) = 2 := by
    refine orderOf_eq_prime (Subtype.ext ?_) fun h => ht1 (congrArg Subtype.val h)
    rw [Subgroup.coe_pow, pow_two, ht2, Subgroup.coe_one]
  have hord : orderOf (Φ (MulAut.conj (⟨t, htJ⟩ : J))) = 2 := by
    rw [MulEquiv.orderOf_eq,
      orderOf_injective _ (mulAut_conj_injective_of_center_eq_bot hZJ), htord]
  have hinner : (MulAut.conj : adjointGroup Tag.F4 k →* MulAut (adjointGroup Tag.F4 k)).range ≤
      L.map Φ.toMonoidHom := by
    rintro _ ⟨y, rfl⟩
    refine ⟨MulAut.conj (e.symm y), hL ⟨e.symm y, rfl⟩, ?_⟩
    change Φ (MulAut.conj (e.symm y)) = MulAut.conj y
    rw [hΦconj, MulEquiv.apply_symm_apply]
  have hmem : Φ (MulAut.conj (⟨t, htJ⟩ : J)) ∈
      (MulAut.conj : adjointGroup Tag.F4 k →* MulAut (adjointGroup Tag.F4 k)).range :=
    ⟨e ⟨t, htJ⟩, (hΦconj _).symm⟩
  have h := (even_exceptional_inner_involution_full_centralizer_odd_core).1 Tag.F4 f k hf hk
    (Or.inl rfl) (L.map Φ.toMonoidHom) hinner _ hmem hord
  rw [← oddCore_eq_pPrimeCore_two'] at h
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv (inf_centralizer_congr e L _).symm h

theorem pinnedX_e6HighestRoot_one_sq {K : Type} [Field K] (h2 : (2 : K) = 0) :
    pinnedX TwistTag.E6.tag K e6HighestRoot 1 * pinnedX TwistTag.E6.tag K e6HighestRoot 1 = 1 ∧
      pinnedX TwistTag.E6.tag K e6HighestRoot 1 ≠ 1 := by
  refine ⟨?_, fun h => ?_⟩
  · rw [← pinnedX_add, show (1 : K) + 1 = 0 by rw [one_add_one_eq_two, h2], pinnedX_zero]
  · rw [← pinnedX_zero TwistTag.E6.tag K e6HighestRoot] at h
    exact one_ne_zero (pinnedX_injective TwistTag.E6.tag K e6HighestRoot h)

theorem even_E6_graph_classes_odd_core {f : ℕ} (hf : 1 ≤ f) (k : Type) [Field k]
    (hk : Nat.card k = 2 ^ f) (H : Subgroup (MulAut (adjointGroup TwistTag.E6.tag k)))
    (hIH : OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag k) ≤ H)
    (ht : pinnedX TwistTag.E6.tag k e6HighestRoot 1 ∈ adjointGroup TwistTag.E6.tag k)
    (η : MulAut (adjointGroup TwistTag.E6.tag k))
    (hη : ∀ h, (η h : ModGL TwistTag.E6.tag k) =
      diagramMap TwistTag.E6 k * h * (diagramMap TwistTag.E6 k)⁻¹)
    {α : MulAut (adjointGroup TwistTag.E6.tag k)} (hαH : α ∈ H)
    (hα : (∃ φ, φ * α * φ⁻¹ = η) ∨
      ∃ φ, φ * α * φ⁻¹ = MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag k) * η) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  rcases hα with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact even_E6_canonical_graph_class_odd_core hf k hk η hη H hIH hφ
  ·
    obtain ⟨htJ, -, -⟩ := secondGraphFullCentralizer_adjointGroup hf k hk
    obtain ⟨ht2, ht1⟩ := pinnedX_e6HighestRoot_one_sq h2
    have hF4 := fun τJ hτJ L hL => oddCore_inf_centralizer_inner_of_F4 hf k hk
      (graphFixedImageF4Equiv (RingHom.id k) h2) htJ ht2 ht1 τJ hτJ L hL
    have hξ : ∀ g, ((MulAut.conj (⟨_, ht⟩ : adjointGroup TwistTag.E6.tag k) * η) g :
        ModGL TwistTag.E6.tag k) =
        pinnedX TwistTag.E6.tag k e6HighestRoot 1 *
          (diagramMap TwistTag.E6 k * g * (diagramMap TwistTag.E6 k)⁻¹) *
            (pinnedX TwistTag.E6.tag k e6HighestRoot 1)⁻¹ := fun g => by
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hη]
    exact (even_E6_second_graph_transfer_from_F4 hf k hk _ hξ hF4 H hIH).2 α hαH ⟨φ, hφ⟩

theorem even_twisted_E6_graph_classes_odd_core {f : ℕ} (hf : 1 ≤ f) (k K : Type) [Field k]
    [Field K] [Algebra k K] (hk : Nat.card k = 2 ^ f) (hK : Nat.card K = (2 ^ f) ^ 2)
    (σ : K →+* K) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (H : Subgroup (MulAut (graphFixedRootGroup TwistTag.E6 K σ)))
    (hIH : OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.E6 K σ) ≤ H)
    (ht : pinnedX TwistTag.E6.tag K e6HighestRoot 1 ∈ graphFixedRootGroup TwistTag.E6 K σ)
    (η : MulAut (graphFixedRootGroup TwistTag.E6 K σ))
    (hη : ∀ h, (η h : ModGL TwistTag.E6.tag K) =
      diagramMap TwistTag.E6 K * h * (diagramMap TwistTag.E6 K)⁻¹)
    {α : MulAut (graphFixedRootGroup TwistTag.E6 K σ)} (hαH : α ∈ H)
    (hα : (∃ φ, φ * α * φ⁻¹ = η) ∨
      ∃ φ, φ * α * φ⁻¹ = MulAut.conj (⟨_, ht⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  have : Fintype k := Fintype.ofFinite k
  have hk2 : ringChar k = 2 := FiniteField.even_card_iff_char_two.2 (by
    rw [← Nat.card_eq_fintype_card, hk, ← Nat.sub_add_cancel hf, pow_succ, Nat.mul_mod_left])
  have h2 : (2 : k) = 0 := two_eq_zero_of_ringChar hk2
  have h2K : (2 : K) = 0 := by
    have := congrArg (algebraMap k K) h2
    rwa [map_ofNat, map_zero] at this
  rcases hα with ⟨φ, hφ⟩ | ⟨φ, hφ⟩
  · exact even_twisted_E6_canonical_graph_class_odd_core hf k K hk hK σ hσ η hη H hIH hφ
  · obtain ⟨htJ, -, -⟩ := secondGraphFullCentralizer_graphFixedRootGroup hf k K hk hK σ hσ
    obtain ⟨ht2, ht1⟩ := pinnedX_e6HighestRoot_one_sq h2K
    have hF4 := fun τJ hτJ L hL => oddCore_inf_centralizer_inner_of_F4 hf k hk
      (graphFixedImageF4Equiv (algebraMap k K) h2) htJ ht2 ht1 τJ hτJ L hL
    have hξ : ∀ g, ((MulAut.conj (⟨_, ht⟩ : graphFixedRootGroup TwistTag.E6 K σ) * η) g :
        ModGL TwistTag.E6.tag K) =
        pinnedX TwistTag.E6.tag K e6HighestRoot 1 *
          (diagramMap TwistTag.E6 K * g * (diagramMap TwistTag.E6 K)⁻¹) *
            (pinnedX TwistTag.E6.tag K e6HighestRoot 1)⁻¹ := fun g => by
      rw [MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul,
        Subgroup.coe_inv, hη]
    exact (even_twisted_E6_second_graph_transfer_from_F4 hf k K hk hK σ hσ _ hξ hF4 H hIH).2 α
      hαH ⟨φ, hφ⟩

theorem mem_inner_of_conj_mul_rootDiagAut {f : ℕ} (hf : 1 ≤ f) (k : Type) [Field k]
    (hk : Nat.card k = 2 ^ f) {α : MulAut (adjointGroup TwistTag.E6.tag k)}
    (hα2 : α ^ 2 = 1) (g : adjointGroup TwistTag.E6.tag k) (a : Fin TwistTag.E6.tag.rank → kˣ)
    (hga : α = MulAut.conj g * rootDiagAut TwistTag.E6.tag k a) :
    α ∈ OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag k) := by
  have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
  set n := Nat.card kˣ with hn
  have hnodd : Odd n := by
    rw [hn, Nat.card_units, hk]
    obtain ⟨m, hm⟩ : ∃ m, f = m + 1 := ⟨f - 1, by omega⟩
    refine ⟨2 ^ m - 1, ?_⟩
    rw [hm, pow_succ]
    have : 1 ≤ 2 ^ m := Nat.one_le_two_pow
    omega
  have : (OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag k)).Normal :=
    OuterAutomorphisms.inner_normal _
  set π := QuotientGroup.mk' (OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag k)) with hπ
  have hg1 : π (MulAut.conj g) = 1 := (QuotientGroup.eq_one_iff _).2 ⟨g, rfl⟩
  have hπα : π α = π (rootDiagAut TwistTag.E6.tag k a) := by rw [hga, map_mul, hg1, one_mul]
  have han : a ^ n = 1 := funext fun i => by
    rw [Pi.pow_apply, Pi.one_apply, hn]
    exact pow_card_eq_one'
  have hn1 : π α ^ n = 1 := by
    rw [hπα, ← map_pow, show rootDiagAut TwistTag.E6.tag k a = rootDiagAutHom TwistTag.E6.tag k a
      from rfl, ← map_pow, han, map_one, map_one]
  have h21 : π α ^ 2 = 1 := by rw [← map_pow, hα2, map_one]
  have hord : orderOf (π α) = 1 := by
    have hcop : Nat.Coprime 2 n := Nat.coprime_two_left.2 hnodd
    exact Nat.dvd_one.1 (hcop.gcd_eq_one ▸ Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h21)
      (orderOf_dvd_of_pow_eq_one hn1))
  exact (QuotientGroup.eq_one_iff α).1 (orderOf_eq_one_iff.1 hord)

theorem even_E6_twisted_E6_outer_involution_full_centralizer_odd_core {f : ℕ} (hf : 1 ≤ f) :
    (∀ (k : Type) [Field k], Nat.card k = 2 ^ f →
      ∀ H : Subgroup (MulAut (adjointGroup TwistTag.E6.tag k)),
        OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag k) ≤ H →
        ∀ α ∈ H, α ∉ OuterAutomorphisms.inner (adjointGroup TwistTag.E6.tag k) → orderOf α = 2 →
          CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥) ∧
    (∀ (K : Type) [Field K], Nat.card K = (2 ^ f) ^ 2 → ∀ σ : K →+* K, (∀ c, σ c = c ^ 2 ^ f) →
      ∀ H : Subgroup (MulAut (graphFixedRootGroup TwistTag.E6 K σ)),
        OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.E6 K σ) ≤ H →
        ∀ α ∈ H, α ∉ OuterAutomorphisms.inner (graphFixedRootGroup TwistTag.E6 K σ) →
          orderOf α = 2 →
          CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥) := by
  refine ⟨fun k _ hk H hIH α hαH hαI hα => ?_, fun K _ hK σ hσ H hIH α hαH hαI hα => ?_⟩
  ·
    classical
    have : Finite k := Nat.finite_of_card_ne_zero (by rw [hk]; positivity)
    have hα2 : α ^ 2 = 1 := by
      rw [← hα]
      exact pow_orderOf_eq_one α
    obtain ⟨Θ, -, hΘ, -, -, -⟩ :=
      ordinary_E_field_graph_quotient_and_involutions TwistTag.E6.tag (Or.inl rfl) k
    obtain ⟨-, -, hex⟩ := ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) k
    obtain ⟨g, a, σ, ε, hga⟩ := hex α
    have hΘα := hΘ α g a σ ε hga
    by_cases hσ1 : σ = 1
    · subst hσ1
      have hε2 : (ε : ℕ) = 0 ∨ (ε : ℕ) = 1 := by
        have := ε.isLt
        change (ε : ℕ) < 2 at this
        omega
      rcases hε2 with h0 | h1
      ·
        exfalso
        refine hαI (mem_inner_of_conj_mul_rootDiagAut hf k hk hα2 g a ?_)
        refine MulEquiv.ext fun h => Subtype.ext ?_
        have e1 : Units.map (entrywiseHom (1 : k ≃+* k).toRingHom)
            (h : ModGL TwistTag.E6.tag k) = h := Units.ext (entrywise_id _)
        rw [hga h, h0, exactQ_zero, e1, MulAut.mul_apply, MulAut.conj_apply, Subgroup.coe_mul,
          Subgroup.coe_mul, Subgroup.coe_inv, coe_rootDiagAut]
        group
      ·
        obtain ⟨ht, η, hη, hconj, hiff, -, -⟩ :=
          (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).1 k hk
        have hdiag : IsOrdinaryDiagGraph k α := by
          rw [hiff Θ hΘ, hΘα, h1, Nat.cast_one]
        exact even_E6_graph_classes_odd_core hf k hk H hIH ht η hη hαH (hconj α hdiag hα2)
    · exact even_E6_nontrivial_field_projection_involution_full_centralizer_odd_core hf k hk Θ hΘ
        H hIH hα (by rw [hΘα]; exact hσ1)
  ·
    have hk := card_eqLocusField_of_pow Nat.prime_two hf hK hσ
    have hα2 : α ^ 2 = 1 := by
      rw [← hα]
      exact pow_orderOf_eq_one α
    obtain ⟨ht, η, hη, -, -, hnoninner, -, -⟩ :=
      (even_E6_graph_full_inner_diagonal_coset_exhaustion f hf).2 K hK σ hσ
    have hnc : ∀ c, α ≠ MulAut.conj c := fun c h => hαI ⟨c, h.symm⟩
    exact even_twisted_E6_graph_classes_odd_core hf (RingHom.eqLocusField σ (RingHom.id K)) K hk
      hK σ hσ H hIH ht η hη hαH (hnoninner α hα2 hnc)

end CFSG.RankThree.Chevalley

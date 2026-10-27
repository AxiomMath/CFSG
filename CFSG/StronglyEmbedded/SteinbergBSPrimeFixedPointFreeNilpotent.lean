module

public import CFSG.GroupTheory.SteinbergBSFixedPointFree
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
public import CFSG.LocalAnalysis.SteinbergBVSolvableFrobeniusKernel
public import CFSG.RankThree.Coprime.ThompsonElementaryComplement
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerImageCompletion
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerPrimeCompatibility
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SignalizerRestrictionCompletion
public import CFSG.StronglyEmbedded.SteinbergBKSylowInheritance

public section

namespace CFSG.StronglyEmbedded

open Subgroup CFSG.GroupTheory.SteinbergBS

universe u

section Invariance

variable {G : Type*} [Group G]

theorem map_equiv_centralizer_eq {G' : Type*} [Group G'] (H : Subgroup G) (f : G ≃* G') :
    (centralizer (H : Set G)).map f.toMonoidHom = centralizer (H.map f.toMonoidHom : Set G') := by
  ext x
  rw [mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · rintro h _ ⟨y, hy, rfl⟩
    have := congrArg f (h y hy)
    simpa only [map_mul, MulEquiv.apply_symm_apply, MulEquiv.coe_toMonoidHom] using this
  · intro h y hy
    have := congrArg f.symm (h (f y) ⟨y, hy, rfl⟩)
    simpa only [map_mul, MulEquiv.symm_apply_apply] using this

theorem map_map_subtype_eq_of_characteristic (α : MulAut G) {P : Subgroup G}
    (hP : P.map α.toMonoidHom = P) (K : Subgroup P) [hK : K.Characteristic] :
    (K.map P.subtype).map α.toMonoidHom = K.map P.subtype := by
  have hcomp : α.toMonoidHom.comp P.subtype =
      P.subtype.comp (invariantRestrict α P hP).toMonoidHom :=
    MonoidHom.ext fun _ => rfl
  rw [Subgroup.map_map, hcomp, ← Subgroup.map_map,
    Subgroup.characteristic_iff_map_eq.1 hK (invariantRestrict α P hP)]

theorem fixedPointFree_invariantRestrict {α : MulAut G} (hα : MonoidHom.FixedPointFree α)
    (H : Subgroup G) (hH : H.map α.toMonoidHom = H) :
    MonoidHom.FixedPointFree (invariantRestrict α H hH) :=
  fun h hh => Subtype.ext (hα h (congrArg Subtype.val hh))

end Invariance

theorem hasNormalPComplement_of_isNilpotent {K : Type*} [Group K] [Finite K] [Group.IsNilpotent K]
    (p : ℕ) [Fact p.Prime] : HasNormalPComplement p K := by
  refine ⟨pPrimeCore p K, pPrimeCore_normal, pPrimeCore_coprime_card, ?_⟩
  have h := isPGroup_of_nilpotent_normal (G := K ⧸ pPrimeCore p K) ⊤ inferInstance
    inferInstance (pPrimeCore_quotient_pPrimeCore_eq_bot p)
  exact h.of_equiv Subgroup.topEquiv

theorem exists_isSolvable_quotient_of_forall {G : Type*} [Group G] {ι : Type*} (T : Finset ι)
    (N : ι → Subgroup G) (hN : ∀ i ∈ T, ∃ _ : (N i).Normal, Group.IsSolvable (G ⧸ N i)) :
    ∃ (K : Subgroup G) (_ : K.Normal), (∀ x, x ∈ K ↔ ∀ i ∈ T, x ∈ N i) ∧
      Group.IsSolvable (G ⧸ K) := by
  classical
  induction T using Finset.induction_on with
  | empty =>
    have : Subsingleton (G ⧸ (⊤ : Subgroup G)) := QuotientGroup.subsingleton_quotient_top
    exact ⟨⊤, inferInstance, fun x => by simp, inferInstance⟩
  | insert a T ha ih =>
    obtain ⟨K, hKn, hK, hKs⟩ := ih fun i hi => hN i (Finset.mem_insert_of_mem hi)
    obtain ⟨hNa, hNas⟩ := hN a (Finset.mem_insert_self a T)
    let φ : G →* (G ⧸ N a) × (G ⧸ K) := (QuotientGroup.mk' (N a)).prod (QuotientGroup.mk' K)
    refine ⟨φ.ker, inferInstance, fun x => ?_, ?_⟩
    · rw [MonoidHom.mem_ker, MonoidHom.prod_apply, Prod.mk_eq_one, QuotientGroup.mk'_apply,
        QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, QuotientGroup.eq_one_iff, hK,
        Finset.forall_mem_insert]
    · exact Group.isSolvable_of_isSolvable_injective (QuotientGroup.kerLift_injective φ)

theorem isSolvable_of_hasNormalPComplement {G : Type*} [Group G] [Finite G]
    (h : ∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ Nat.card G → HasNormalPComplement p G) :
    Group.IsSolvable G := by
  classical
  set S : Finset ℕ := (Nat.card G).primeFactors.filter (· ≠ 2) with hSdef
  have hS : ∀ p ∈ S, p.Prime ∧ p ≠ 2 ∧ p ∣ Nat.card G := fun p hp => by
    rw [hSdef, Finset.mem_filter, Nat.mem_primeFactors] at hp
    exact ⟨hp.1.1, hp.2, hp.1.2.1⟩
  have hc : ∀ p ∈ S, HasNormalPComplement p G := fun p hp =>
    h p (hS p hp).1 (hS p hp).2.1 (hS p hp).2.2
  choose! N hNn hNcop hNp using hc
  obtain ⟨K, hKn, hK, hKs⟩ := exists_isSolvable_quotient_of_forall S N fun p hp => by
    have : Fact p.Prime := ⟨(hS p hp).1⟩
    have := hNn p hp
    have := (hNp p hp).isNilpotent
    exact ⟨inferInstance, inferInstance⟩
  have h2 : ∀ {q : ℕ}, q.Prime → q ∣ Nat.card K → q = 2 := by
    intro q hq hqK
    by_contra hq2
    have hqS : q ∈ S := by
      rw [hSdef, Finset.mem_filter, Nat.mem_primeFactors]
      exact ⟨⟨hq, hqK.trans (Subgroup.card_subgroup_dvd_card K), Nat.card_pos.ne'⟩, hq2⟩
    have hle : K ≤ N q := fun x hx => (hK x).1 hx q hqS
    have hdvd : q ∣ Nat.card (N q) := hqK.trans (Subgroup.card_dvd_of_le hle)
    exact hq.one_lt.ne' (Nat.Coprime.eq_one_of_dvd (hNcop q hqS) hdvd)
  have hK2 : IsPGroup 2 K :=
    IsPGroup.of_card (Nat.eq_prime_pow_of_unique_prime_dvd Nat.card_pos.ne' h2)
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hK2.isNilpotent
  exact Group.isSolvable_of_ker_le_range K.subtype (QuotientGroup.mk' K)
    (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])

theorem isNilpotent_of_isSolvable_of_fixedPointFree {G : Type u} [Group G] [Finite G]
    [Group.IsSolvable G] (α : MulAut G) {r : ℕ} (hr : r.Prime) (hαr : orderOf α = r)
    (hα : MonoidHom.FixedPointFree α) : Group.IsNilpotent G := by
  let φ : zpowers α →* MulAut G := (zpowers α).subtype
  have : Finite (G ⋊[φ] zpowers α) := Finite.of_equiv _ SemidirectProduct.equivProd.symm
  have hsolv : Group.IsSolvable (G ⋊[φ] zpowers α) :=
    Group.isSolvable_of_ker_le_range SemidirectProduct.inl SemidirectProduct.rightHom
      SemidirectProduct.range_inl_eq_ker_rightHom.ge
  have hKn : (SemidirectProduct.inl : G →* G ⋊[φ] zpowers α).range.Normal := by
    rw [SemidirectProduct.range_inl_eq_ker_rightHom]
    infer_instance
  have hKR : (SemidirectProduct.inl : G →* G ⋊[φ] zpowers α).range.IsComplement'
      (SemidirectProduct.inr : zpowers α →* G ⋊[φ] zpowers α).range := by
    refine Subgroup.isComplement'_of_disjoint_and_mul_eq_univ ?_ ?_
    · rw [Subgroup.disjoint_def]
      rintro _ ⟨n, rfl⟩ ⟨g, hg⟩
      have h1 := congrArg SemidirectProduct.right hg
      have h2 := congrArg SemidirectProduct.left hg
      simp only [SemidirectProduct.right_inr, SemidirectProduct.right_inl,
        SemidirectProduct.left_inr, SemidirectProduct.left_inl] at h1 h2
      rw [← h2, map_one]
    · refine Set.eq_univ_of_forall fun x => ?_
      exact ⟨_, ⟨x.left, rfl⟩, _, ⟨x.right, rfl⟩, SemidirectProduct.inl_left_mul_inr_right x⟩
  have hR : (Nat.card (SemidirectProduct.inr : zpowers α →* G ⋊[φ] zpowers α).range).Prime := by
    rw [← Nat.card_congr (MonoidHom.ofInjective SemidirectProduct.inr_injective).toEquiv,
      Nat.card_zpowers, hαr]
    exact hr
  have hfix : ∀ k ∈ (SemidirectProduct.inl : G →* G ⋊[φ] zpowers α).range,
      (∀ x ∈ (SemidirectProduct.inr : zpowers α →* G ⋊[φ] zpowers α).range, x * k = k * x) →
        k = 1 := by
    rintro _ ⟨g, rfl⟩ hk
    have h := hk (SemidirectProduct.inr ⟨α, mem_zpowers α⟩) ⟨_, rfl⟩
    have h2 : (SemidirectProduct.inl (φ ⟨α, mem_zpowers α⟩ g) : G ⋊[φ] zpowers α) =
        SemidirectProduct.inl g := by
      rw [SemidirectProduct.inl_aut, h, map_inv, mul_inv_cancel_right]
    rw [hα g (SemidirectProduct.inl_injective h2), map_one]
  have hnil := CFSG.LocalAnalysis.SteinbergBV.solvable_prime_frobenius_kernel_nilpotent hsolv hKR
    hR hfix
  exact Group.nilpotent_of_surjective
    (MonoidHom.ofInjective (SemidirectProduct.inl_injective (φ := φ))).symm.toMonoidHom
    (MulEquiv.surjective _)

theorem prime_order_fixed_point_free_automorphism_nilpotent_aux {r : ℕ} (hr : r.Prime) (n : ℕ) :
    ∀ (G : Type u) [Group G] [Finite G], Nat.card G = n → ∀ α : MulAut G, orderOf α = r →
      MonoidHom.FixedPointFree α → Group.IsNilpotent G := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro G _ _ hn α hαr hα
  by_cases hsolv : Group.IsSolvable G
  · exact isNilpotent_of_isSolvable_of_fixedPointFree α hr hαr hα
  exfalso
  obtain ⟨-, -, hquot, hsyl, hprime⟩ := fixed_point_free_automorphism_quotients_and_sylows α hα
  obtain ⟨-, hsub, hquot'⟩ := hprime r hr hαr
  have hsubnil : ∀ H : Subgroup G, H.map α.toMonoidHom = H → H ≠ ⊥ → H ≠ ⊤ →
      Group.IsNilpotent H := by
    intro H hH hH1 hHtop
    have hlt : Nat.card H < n := by
      rw [← hn, ← Subgroup.card_top (G := G)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.2 hHtop)
    exact ih _ hlt H rfl (invariantRestrict α H hH) (hsub H hH hH1)
      (fixedPointFree_invariantRestrict hα H hH)
  have hnorm : ∀ (p : ℕ) [Fact p.Prime] (Q : Subgroup G), Q.Normal →
      Q.map α.toMonoidHom = Q → Q ≠ ⊥ → IsPGroup p Q → False := by
    intro p _ Q hQn hQα hQ1 hQp
    have := hQp.isNilpotent
    by_cases hQtop : Q = ⊤
    · subst hQtop
      exact hsolv (Group.isSolvable_of_surjective (f := (⊤ : Subgroup G).subtype)
        fun x => ⟨⟨x, mem_top x⟩, rfl⟩)
    have hlt : Nat.card (G ⧸ Q) < n := by
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup Q
      have h2 := (Subgroup.one_lt_card_iff_ne_bot Q).2 hQ1
      have h3 : 0 < Nat.card (G ⧸ Q) := Nat.card_pos
      rw [← hn, h1]
      exact lt_mul_of_one_lt_right h3 h2
    have hQα' : Q.map (α : G →* G) = Q := hQα
    have hnil := ih _ hlt (G ⧸ Q) rfl (QuotientGroup.congr Q Q α hQα')
      (hquot' Q hQα' hQtop) (hquot Q hQα')
    exact hsolv (Group.isSolvable_of_ker_le_range Q.subtype (QuotientGroup.mk' Q)
      (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype]))
  refine hsolv (isSolvable_of_hasNormalPComplement fun p hp hp2 hpG => ?_)
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPα, -⟩ := hsyl p
  have hP : (P : Subgroup G).map α.toMonoidHom = P := congrArg Sylow.toSubgroup hPα
  have hP1 : (P : Subgroup G) ≠ ⊥ := P.ne_bot_of_dvd_card hpG
  have : (elemThompson (P : Subgroup G) p).Characteristic :=
    CFSG.Quasithin.BlueprintB2.elemThompson_characteristic _ p
  set Z : Subgroup G := (center (P : Subgroup G)).map (P : Subgroup G).subtype with hZdef
  set J : Subgroup G := (elemThompson (P : Subgroup G) p).map (P : Subgroup G).subtype with hJdef
  have hZα : Z.map α.toMonoidHom = Z := map_map_subtype_eq_of_characteristic α hP _
  have hJα : J.map α.toMonoidHom = J := map_map_subtype_eq_of_characteristic α hP _
  have hZ1 : Z ≠ ⊥ := by
    have : Nontrivial (P : Subgroup G) := (Subgroup.nontrivial_iff_ne_bot _).2 hP1
    have := P.isPGroup'.center_nontrivial
    rw [hZdef, Ne, Subgroup.map_eq_bot_iff_of_injective _ (P : Subgroup G).subtype_injective]
    exact (Subgroup.nontrivial_iff_ne_bot _).1 this
  have hJ1 : J ≠ ⊥ := CFSG.RankThree.Coprime.map_elemThompson_ne_bot P.isPGroup' hP1
  have hZp : IsPGroup p Z := P.isPGroup'.to_le (map_subtype_le _)
  have hJp : IsPGroup p J := P.isPGroup'.to_le (map_subtype_le _)
  have hZC : Z ≤ centralizer (Z : Set G) := by
    rintro _ ⟨a, ha, rfl⟩
    rw [mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 ha b)
  have hCα : (centralizer (Z : Set G)).map α.toMonoidHom = centralizer (Z : Set G) := by
    rw [map_equiv_centralizer_eq, hZα]
  have hNα : (normalizer (J : Set G)).map α.toMonoidHom = normalizer (J : Set G) := by
    rw [Subgroup.map_equiv_normalizer_eq, hJα]
  have hCtop : centralizer (Z : Set G) ≠ ⊤ := by
    intro h
    exact hnorm p Z (Subgroup.normal_of_le_center (Subgroup.centralizer_eq_top_iff_subset.1 h))
      hZα hZ1 hZp
  have hNtop : normalizer (J : Set G) ≠ ⊤ := fun h =>
    hnorm p J (Subgroup.normalizer_eq_top_iff.1 h) hJα hJ1 hJp
  have hC1 : centralizer (Z : Set G) ≠ ⊥ := fun h => hZ1 (le_bot_iff.1 (h ▸ hZC))
  have hN1 : normalizer (J : Set G) ≠ ⊥ := fun h => hJ1 (le_bot_iff.1 (h ▸ le_normalizer))
  have hCnil := hsubnil _ hCα hC1 hCtop
  have hNnil := hsubnil _ hNα hN1 hNtop
  exact CFSG.RankThree.Coprime.thompson_elementary_normal_p_complement hp2 P
    (hasNormalPComplement_of_isNilpotent p) (hasNormalPComplement_of_isNilpotent p)

theorem prime_order_fixed_point_free_automorphism_nilpotent {G : Type u} [Group G] [Finite G]
    (α : MulAut G) {r : ℕ} (hr : r.Prime) (hαr : orderOf α = r)
    (hα : ∀ g : G, α g = g → g = 1) : Group.IsNilpotent G :=
  prime_order_fixed_point_free_automorphism_nilpotent_aux hr _ G rfl α hαr hα

end CFSG.StronglyEmbedded

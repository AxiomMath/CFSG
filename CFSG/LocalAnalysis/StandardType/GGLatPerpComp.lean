module

public import CFSG.LocalAnalysis.StandardType.GGLatPerpBase

public section

namespace CFSG.StandardType.LatPerp

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.StandardType.LatPerpChecks

open scoped Matrix

@[expose] def ggPerpComp (τ : Tag) (p : ℕ) (α : Fin τ.rank → ℤ) : Prop :=
  (∀ β ∈ ggPerp τ α, ∀ γ ∈ ggPerp τ α,
      latLinked (Tag.symmetrizedCartan τ) (ggPerp τ α) β γ) ∧
  Nat.card {f : Fin τ.rank → ZMod p // ∀ β ∈ ggPerp τ α, latChar p f β = 0} = p ∧
  7 ≤ (ggPerp τ α).ncard

theorem ggPerpComp_reflect (τ : Tag) (p : ℕ) (i : Fin τ.rank) {α : Fin τ.rank → ℤ}
    (h : ggPerpComp τ p α) : ggPerpComp τ p (reflect τ i α) := by
  obtain ⟨hconn, hcard, hnc⟩ := h
  have hperp : ggPerp τ (reflect τ i α) = reflect τ i '' ggPerp τ α := perp_reflect τ i
  refine ⟨?_, ?_, ?_⟩
  · intro β hβ γ hγ
    rw [hperp] at hβ hγ ⊢
    obtain ⟨β', hβ', rfl⟩ := hβ
    obtain ⟨γ', hγ', rfl⟩ := hγ
    exact (latLinked_image_iff _ (reflect τ i) (reflect_injective τ i) (reflect_invol τ i) rfl
      (latGram_reflect τ i)).mpr (hconn β' hβ' γ' hγ')
  · refine (Nat.card_congr ?_).trans hcard
    rw [hperp]
    refine Equiv.subtypeEquiv
      ⟨reflChar τ i p, reflChar τ i p, reflChar_invol τ i p, reflChar_invol τ i p⟩ ?_
    intro f
    constructor
    · intro hf β hβ
      change latChar p (reflChar τ i p f) β = 0
      rw [latChar_reflChar]
      exact hf _ ⟨β, hβ, rfl⟩
    · intro hf β' hβ'
      obtain ⟨β, hβ, rfl⟩ := hβ'
      have h1 := hf β hβ
      change latChar p (reflChar τ i p f) β = 0 at h1
      rwa [latChar_reflChar] at h1
  · rw [hperp, Set.ncard_image_of_injective _ (reflect_injective τ i)]
    exact hnc

theorem ggPerpComp_of_isRoot (τ : Tag) (p : ℕ) (hbase : ∀ j, ggPerpComp τ p (Pi.single j 1))
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : ggPerpComp τ p α := by
  induction hα with
  | basis j => exact hbase j
  | reflect i _ ih => exact ggPerpComp_reflect τ p i ih

theorem eq_smul_of_mulVec_supported {N : ℕ} {K : Type*} [Field K]
    (T : Matrix (Fin N) (Fin N) K) (hT : T.det ≠ 0) (j : Fin N)
    (g f : Fin N → K) (hg : g ≠ 0)
    (hgsupp : ∀ k, k ≠ j → (T *ᵥ g) k = 0)
    (hfsupp : ∀ k, k ≠ j → (T *ᵥ f) k = 0) : ∃ c : K, f = c • g := by
  have hcg : (T *ᵥ g) j ≠ 0 := by
    intro h0
    have hzero : T *ᵥ g = 0 := by
      funext k
      by_cases hk : k = j
      · rwa [hk]
      · exact hgsupp k hk
    exact hg (Matrix.eq_zero_of_mulVec_eq_zero hT hzero)
  refine ⟨(T *ᵥ f) j / (T *ᵥ g) j, ?_⟩
  have hsub : T *ᵥ (f - ((T *ᵥ f) j / (T *ᵥ g) j) • g) = 0 := by
    funext k
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
    by_cases hk : k = j
    · subst hk
      rw [div_mul_cancel₀ _ hcg, sub_self]
      simp
    · rw [hfsupp k hk, hgsupp k hk, mul_zero, sub_zero]
      simp
  exact sub_eq_zero.mp (Matrix.eq_zero_of_mulVec_eq_zero hT hsub)

theorem latGram_single_single {N : ℕ} (S : Matrix (Fin N) (Fin N) ℤ) (i j : Fin N) :
    latGram S (Pi.single i 1) (Pi.single j 1) = S i j := by
  simp [latGram, Pi.single_apply]

theorem ggSymmCartan_diag_ne_zero (τ : Tag) (j : Fin τ.rank) :
    Tag.symmetrizedCartan τ j j ≠ 0 := by
  cases τ <;> fin_cases j <;> decide +kernel

theorem ggCorootCoord_basis_apply (τ : Tag) (j : Fin τ.rank) (p : ℕ) :
    corootCoord p (Tag.symmetrizedCartan τ) (Pi.single j 1) j = (2 : ZMod p) := by
  simp only [corootCoord, latGram_single_single]
  rw [Int.mul_ediv_cancel 2 (ggSymmCartan_diag_ne_zero τ j)]
  norm_num

@[expose] def ggCertT (τ : Tag) (j : Fin τ.rank) (p : ℕ) :
    Matrix (Fin τ.rank) (Fin τ.rank) (ZMod p) :=
  (ggCertMat τ j).map (Int.cast : ℤ → ZMod p)

theorem ggTmat_mulVec_apply (τ : Tag) (j : Fin τ.rank) (p : ℕ)
    (f : Fin τ.rank → ZMod p) (k : Fin τ.rank) :
    (ggCertT τ j p *ᵥ f) k = latChar p f (ggCertMat τ j k) := by
  simp only [ggCertT, Matrix.mulVec, Matrix.map_apply, latChar, dotProduct]

theorem ggCertMat_det (τ : Tag) (j : Fin τ.rank) :
    (ggCertMat τ j).det = ggCertDet τ j := by
  rw [← CFSG.LieType.Chevalley.laplaceDet_eq_det]
  exact ggCertMat_laplace τ j

theorem ggCertDet_ne_zero {τ : Tag} {j : Fin τ.rank} {p : ℕ}
    (hval : ggCertDet τ j = 1 ∨ ggCertDet τ j = -1 ∨ ggCertDet τ j = 2 ∨
      ggCertDet τ j = -2) (hp : p.Prime) (hp2 : p ≠ 2) :
    (((ggCertMat τ j).det : ℤ) : ZMod p) ≠ 0 := by
  rw [ggCertMat_det]
  rcases hval with h | h | h | h <;> rw [h]
  · rw [Int.cast_one]; exact lat_zmod_one_ne_zero hp
  · rw [Int.cast_neg, Int.cast_one]; exact neg_ne_zero.mpr (lat_zmod_one_ne_zero hp)
  · rw [Int.cast_ofNat]; exact lat_zmod_two_ne_zero hp hp2
  · rw [Int.cast_neg, Int.cast_ofNat]; exact neg_ne_zero.mpr (lat_zmod_two_ne_zero hp hp2)

section Cert

theorem ggConnCheck_sound {τ : Tag} {α a₀ : Fin τ.rank → ℤ}
    (h : ggConnCheck τ α a₀ = true) (ha₀ : IsRoot τ a₀) :
    ∀ β ∈ ggPerp τ α, ∀ γ ∈ ggPerp τ α,
      latLinked (Tag.symmetrizedCartan τ) (ggPerp τ α) β γ := by
  unfold ggConnCheck at h
  dsimp only at h
  rw [Bool.and_eq_true] at h
  obtain ⟨ha₀perp, hall⟩ := h
  have ha₀gram : latGram (Tag.symmetrizedCartan τ) α a₀ = 0 := by
    rw [← ggGram_eq_latGram, ggGram_eq_pair]
    exact of_decide_eq_true ha₀perp
  have ha₀mem : a₀ ∈ ggPerp τ α := ⟨ha₀, ha₀gram⟩
  have hlink : ∀ β ∈ ggPerp τ α,
      latLinked (Tag.symmetrizedCartan τ) (ggPerp τ α) a₀ β := by
    intro β hβ
    have hb := List.all_eq_true.mp hall β (ggPerpList_mem.mpr hβ)
    rw [Bool.or_eq_true] at hb
    rcases hb with hdir | hind
    · refine Relation.EqvGen.rel _ _ ⟨ha₀mem, hβ, ?_⟩
      have h1 := of_decide_eq_true hdir
      rwa [← ggGram_eq_pair, ggGram_eq_latGram] at h1
    · obtain ⟨q, hq, hg2⟩ := List.any_eq_true.mp hind
      obtain ⟨γ, hγ, rfl⟩ := List.mem_map.mp hq
      rw [List.mem_filter] at hγ
      obtain ⟨hγplist, hγne⟩ := hγ
      have hγmem : γ ∈ ggPerp τ α := ggPerpList_mem.mp hγplist
      have hγne' : latGram (Tag.symmetrizedCartan τ) a₀ γ ≠ 0 := by
        have h1 := of_decide_eq_true hγne
        rwa [← ggGram_eq_pair, ggGram_eq_latGram] at h1
      have hg2' : latGram (Tag.symmetrizedCartan τ) γ β ≠ 0 := by
        have h1 := of_decide_eq_true hg2
        change ggPairVec (ggMulB τ γ) β ≠ 0 at h1
        rwa [← ggGram_eq_pair, ggGram_eq_latGram] at h1
      exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.rel _ _ ⟨ha₀mem, hγmem, hγne'⟩)
        (Relation.EqvGen.rel _ _ ⟨hγmem, hβ, hg2'⟩)
  intro β hβ γ hγ
  exact Relation.EqvGen.trans _ _ _ (Relation.EqvGen.symm _ _ (hlink β hβ)) (hlink γ hγ)

theorem ggBasisCheck_sound {τ : Tag} (h : ggBasisCheck τ = true) (j : Fin τ.rank) :
    ggConnCheck τ (Pi.single j 1) (ggCertA0 τ j) = true ∧
    ggCertA0 τ j ∈ ggRootList τ ∧
    7 ≤ (ggPerpFinset τ (Pi.single j 1)).card ∧
    (∀ k : Fin τ.rank, k ≠ j →
      ggCertMat τ j k ∈ ggRootList τ ∧
        ggGram τ (Pi.single j 1) (ggCertMat τ j k) = 0) ∧
    (ggCertDet τ j = 1 ∨ ggCertDet τ j = -1 ∨ ggCertDet τ j = 2 ∨ ggCertDet τ j = -2) := by
  have h1 := List.all_eq_true.mp h j (List.mem_finRange j)
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h1
  refine ⟨h1.1.1.1.1, h1.1.1.1.2, h1.1.1.2, ?_, h1.2⟩
  intro k hk
  have hk' := List.all_eq_true.mp h1.1.2 k (List.mem_finRange k)
  rw [Bool.or_eq_true] at hk'
  rcases hk' with h | h
  · exact absurd (decide_eq_true_eq.mp h) hk
  · rw [Bool.and_eq_true] at h
    exact ⟨decide_eq_true_eq.mp h.1, decide_eq_true_eq.mp h.2⟩

theorem ggPerpComp_basis {τ : Tag} (j : Fin τ.rank) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hcart : ggCartCheck τ = true) (hbasis : ggBasisCheck τ = true) :
    ggPerpComp τ p (Pi.single j 1) := by
  obtain ⟨hconn, ha₀root, hcount, hrows, hdetval⟩ := ggBasisCheck_sound hbasis j
  haveI : Fact p.Prime := ⟨hp⟩
  have ha₀ : IsRoot τ (ggCertA0 τ j) := ggRootList_mem.mp ha₀root
  have hrowsmem : ∀ k : Fin τ.rank, k ≠ j → ggCertMat τ j k ∈ ggPerp τ (Pi.single j 1) :=
    fun k hk => ⟨ggRootList_mem.mp (hrows k hk).1, by
      rw [← ggGram_eq_latGram]; exact (hrows k hk).2⟩
  set g : Fin τ.rank → ZMod p := corootCoord p (Tag.symmetrizedCartan τ) (Pi.single j 1) with hg
  have hgAnn : ∀ β ∈ ggPerp τ (Pi.single j 1), latChar p g β = 0 := by
    rintro β ⟨hβroot, hβgram⟩
    rw [hg, latChar_corootCoord, ((ggCartCheck_sound hcart j hβroot).2.2).mpr hβgram]
    simp
  have hgj : g j = 2 := ggCorootCoord_basis_apply τ j p
  have hgne : g j ≠ 0 := by rw [hgj]; exact lat_zmod_two_ne_zero hp hp2
  have hg0 : g ≠ 0 := fun h0 => hgne (by rw [h0]; rfl)
  have hTdet : (ggCertT τ j p).det ≠ 0 := by
    have hmap : (ggCertT τ j p).det = (((ggCertMat τ j).det : ℤ) : ZMod p) := by
      rw [ggCertT]
      exact (RingHom.map_det (Int.castRingHom (ZMod p)) (ggCertMat τ j)).symm
    rw [hmap]
    exact ggCertDet_ne_zero hdetval hp hp2
  have hAnn : ∀ f : Fin τ.rank → ZMod p,
      (∀ β ∈ ggPerp τ (Pi.single j 1), latChar p f β = 0) → ∃ c : ZMod p, f = c • g := by
    intro f hf
    exact eq_smul_of_mulVec_supported (ggCertT τ j p) hTdet j g f hg0
      (fun k hk => by rw [ggTmat_mulVec_apply]; exact hgAnn _ (hrowsmem k hk))
      (fun k hk => by rw [ggTmat_mulVec_apply]; exact hf _ (hrowsmem k hk))
  refine ⟨ggConnCheck_sound hconn ha₀, ?_, ?_⟩
  · let φ : ZMod p →
        {f : Fin τ.rank → ZMod p // ∀ β ∈ ggPerp τ (Pi.single j 1), latChar p f β = 0} :=
      fun c => ⟨c • g, fun β hβ => by rw [latChar_smul, hgAnn β hβ, mul_zero]⟩
    have hinj : Function.Injective φ := by
      intro c c' h
      have h1 : (c • g) j = (c' • g) j := congrFun (congrArg Subtype.val h) j
      simp only [Pi.smul_apply, smul_eq_mul] at h1
      exact mul_right_cancel₀ hgne h1
    have hsurj : Function.Surjective φ := by
      intro f
      obtain ⟨c, hc⟩ := hAnn f.1 f.2
      exact ⟨c, Subtype.ext hc.symm⟩
    exact (Nat.card_congr (Equiv.ofBijective φ ⟨hinj, hsurj⟩)).symm.trans (Nat.card_zmod p)
  · rw [ggPerp_eq_finset, Set.ncard_coe_finset]
    exact hcount

theorem ggPerpComp_of_checks {τ : Tag} (hcart : ggCartCheck τ = true)
    (hbasis : ggBasisCheck τ = true) (p : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : ggPerpComp τ p α :=
  ggPerpComp_of_isRoot τ p (fun j => ggPerpComp_basis j p hp hp2 hcart hbasis) hα

end Cert

end CFSG.StandardType.LatPerp

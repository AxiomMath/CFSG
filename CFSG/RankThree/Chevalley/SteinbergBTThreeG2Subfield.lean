module

public import CFSG.RankThree.Chevalley.SteinbergBTOddF4Subfield
public import CFSG.RankThree.Chevalley.G2F4FiniteFieldFixedMatrices
public import CFSG.LieType.Chevalley.G2ThreeAutomorphismNormalForm

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree SteinbergBT

section Inclusion

variable {τ : Tag} {K : Type} [Field K]

@[expose] def subfieldInclusion (k : Subfield K) : adjointGroup τ k →* adjointGroup τ K :=
  ((baseChangeGL k.subtype).comp (adjointGroup τ k).subtype).codRestrict (adjointGroup τ K)
    fun g => baseChangeGL_mem_adjointGroup k.subtype g.2

theorem coe_subfieldInclusion (k : Subfield K) (g : adjointGroup τ k) :
    (subfieldInclusion k g : ModGL τ K) = baseChangeGL k.subtype g :=
  rfl

theorem subfieldInclusion_injective (k : Subfield K) :
    Function.Injective (subfieldInclusion (τ := τ) k) := fun _ _ h =>
  Subtype.ext (baseChangeGL_injective _ (congrArg Subtype.val h))

theorem subfieldInclusion_xElement (k : Subfield K) (i : Fin τ.rank) (c : k) :
    subfieldInclusion k (xElement i c) = xElement i (c : K) :=
  Subtype.ext (baseChangeGL_xUnit _ i c)

theorem subfieldInclusion_yElement (k : Subfield K) (i : Fin τ.rank) (c : k) :
    subfieldInclusion k (yElement i c) = yElement i (c : K) :=
  Subtype.ext (baseChangeGL_yUnit _ i c)

theorem mem_subfieldImage_iff_exists (k : Subfield K) (g : adjointGroup τ K) :
    (g : ModGL τ K) ∈ subfieldImage τ k ↔ ∃ g', subfieldInclusion k g' = g := by
  constructor
  · rintro ⟨g', hg', hgg'⟩
    exact ⟨⟨g', hg'⟩, Subtype.ext hgg'⟩
  · rintro ⟨g', rfl⟩
    exact ⟨g', g'.2, rfl⟩

end Inclusion

section G2

variable {K : Type} [Field K] [Finite K] [CharP K ReeTag.G2.prime]

theorem finiteExceptionalAut_comp_subfieldInclusion_G2 (k : Subfield K)
    [CharP k ReeTag.G2.prime] :
    (ReeTag.G2.finiteExceptionalAut K).toMonoidHom.comp (subfieldInclusion k) =
      (subfieldInclusion k).comp (ReeTag.G2.finiteExceptionalAut k).toMonoidHom := by
  refine adjointGroup_hom_ext (fun i c => ?_) fun i c => ?_
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, subfieldInclusion_xElement,
      ReeTag.finiteExceptionalAut_xElement]
    rfl
  · simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, subfieldInclusion_yElement,
      ReeTag.finiteExceptionalAut_yElement]
    rfl

theorem finiteExceptionalAut_pow_subfieldInclusion_G2 (k : Subfield K)
    [CharP k ReeTag.G2.prime] (a : ℕ) (g : adjointGroup ReeTag.G2.tag k) :
    (ReeTag.G2.finiteExceptionalAut K ^ a) (subfieldInclusion k g) =
      subfieldInclusion k ((ReeTag.G2.finiteExceptionalAut k ^ a) g) := by
  induction a generalizing g with
  | zero => rfl
  | succ a ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply]
    have h := DFunLike.congr_fun (finiteExceptionalAut_comp_subfieldInclusion_G2 k) g
    simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom] at h
    rw [h, ih]

theorem three_G2_subfield_normalizer_and_pointwise_automorphism_centralizer {f d : ℕ}
    (hf : 1 ≤ f) (hd : 1 ≤ d) (hdf : d ∣ f) (hK : Nat.card K = 3 ^ f) (k : Subfield K)
    (hk : Nat.card k = 3 ^ d) :
    subfieldImage ReeTag.G2.tag k ≤ adjointGroup ReeTag.G2.tag K ∧
      adjointGroup ReeTag.G2.tag K ⊓
          Subgroup.normalizer (subfieldImage ReeTag.G2.tag k : Set (ModGL ReeTag.G2.tag K)) =
        subfieldImage ReeTag.G2.tag k ∧
      fixingSubgroup (MulAut (adjointGroup ReeTag.G2.tag K))
          (((subfieldImage ReeTag.G2.tag k).subgroupOf (adjointGroup ReeTag.G2.tag K) :
            Subgroup (adjointGroup ReeTag.G2.tag K)) : Set (adjointGroup ReeTag.G2.tag K)) =
        Subgroup.zpowers (ReeTag.G2.finiteFrobeniusAut K ^ d) ∧
      ReeTag.G2.finiteFrobeniusAut K ^ d = ReeTag.G2.finiteExceptionalAut K ^ (2 * d) ∧
      Nat.card (Subgroup.zpowers (ReeTag.G2.finiteFrobeniusAut K ^ d)) = f / d := by
  classical
  set C := adjointGroup ReeTag.G2.tag K
  set J := subfieldImage ReeTag.G2.tag k
  set φ := ReeTag.G2.finiteExceptionalAut K with hφ
  have : CharP k ReeTag.G2.prime := inferInstance
  have hJC : J ≤ C := subfieldImage_le k
  have hFrφ : ReeTag.G2.finiteFrobeniusAut K ^ d = φ ^ (2 * d) :=
    (finiteExceptionalAut_pow_two_mul ReeTag.G2 d).symm
  obtain ⟨fr, hfr, -⟩ :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_automorphism_fixed_field_cardinality
      Nat.prime_three hf hK
  have hfrd : ∀ c, (fr ^ d) c = c ^ 3 ^ d := ringAut_pow_apply_of_frobenius hfr d
  have hfrk : ∀ c ∈ k, (fr ^ d) c = c := fun c hc => by
    rw [hfrd]
    exact pow_card_eq_self_of_mem hk hc
  have hFr : ReeTag.G2.finiteFrobeniusAut K ^ d = entrywiseAdjointAut ReeTag.G2.tag (fr ^ d) := by
    rw [← exactNormalAut_one_eq_finiteFrobeniusAut_pow ReeTag.G2 (σ := fr ^ d) (j := d) hfrd,
      FieldGraphFieldPointwise.exactNormalAut_one_zero_eq]
  have hFrfix : ∀ x : C, (x : ModGL ReeTag.G2.tag K) ∈ J →
      (ReeTag.G2.finiteFrobeniusAut K ^ d) x = x := fun x hx => by
    rw [hFr]
    exact Subtype.ext (units_map_entrywiseHom_of_mem_subfieldImage hfrk hx)
  have hodd : Odd (Nat.card k) := by
    rw [hk]
    exact Odd.pow (by decide)
  have hfaith := (exceptional_Lang_finite_root_centralizer_faithfulness ReeTag.G2.tag k hodd K
    k.subtype).2.2.1
  have hfixed := frobenius_fixed_eq_map_of_bijective (τ := ReeTag.G2.tag) (k := k) (M := K)
    (Or.inl rfl) (fr ^ d : K ≃+* K).toRingHom (fun c => by rw [hk]; exact hfrd c)
    (fr ^ d).bijective
  have hnorm : C ⊓ Subgroup.normalizer (J : Set (ModGL ReeTag.G2.tag K)) = J := by
    refine le_antisymm (fun g hg => ?_) (le_inf hJC Subgroup.le_normalizer)
    obtain ⟨hgC, hgN⟩ := Subgroup.mem_inf.1 hg
    set F : ModGL ReeTag.G2.tag K →* ModGL ReeTag.G2.tag K :=
      Units.map (entrywiseHom (fr ^ d : K ≃+* K).toRingHom)
    have hFJ : ∀ x ∈ J, F x = x := fun x hx => units_map_entrywiseHom_of_mem_subfieldImage hfrk hx
    have hFC : F g ∈ C := by
      have h := map_exactEntrywiseAut (τ := ReeTag.G2.tag) (fr ^ d) (Or.inl rfl)
      have h' : F g ∈ (adjointGroup ReeTag.G2.tag K).map
          (exactEntrywiseAut ReeTag.G2.tag (fr ^ d)).toMonoidHom := ⟨g, hgC, rfl⟩
      rw [h] at h'
      exact h'
    have hcomm : ∀ x ∈ J, (g⁻¹ * F g) * x = x * (g⁻¹ * F g) := fun x hx => by
      have hgx : g * x * g⁻¹ ∈ J := (Subgroup.mem_normalizer_iff.1 hgN x).1 hx
      have h1 := hFJ _ hgx
      rw [map_mul, map_mul, map_inv, hFJ x hx] at h1
      calc g⁻¹ * F g * x = g⁻¹ * (F g * x * (F g)⁻¹) * F g := by group
        _ = g⁻¹ * (g * x * g⁻¹) * F g := by rw [h1]
        _ = x * (g⁻¹ * F g) := by group
    have hz := hfaith (g⁻¹ * F g) (mul_mem (inv_mem hgC) hFC) fun h hh => hcomm h hh
    have hFg : F g = g := (inv_mul_eq_one.1 hz).symm
    have hmem : g ∈ adjointGroup ReeTag.G2.tag K ⊓
        (Units.map (entrywiseHom (fr ^ d : K ≃+* K).toRingHom)).eqLocus (MonoidHom.id _) :=
      ⟨hgC, hFg⟩
    rw [hfixed] at hmem
    exact hmem
  have hφJ : ∀ (a : ℕ) (x : C), (x : ModGL ReeTag.G2.tag K) ∈ J →
      ((φ ^ a) x : ModGL ReeTag.G2.tag K) ∈ J := fun a x hx => by
    obtain ⟨x', rfl⟩ := (mem_subfieldImage_iff_exists k x).1 hx
    rw [finiteExceptionalAut_pow_subfieldInclusion_G2 k a x']
    exact ⟨_, ((ReeTag.G2.finiteExceptionalAut k ^ a) x').2, rfl⟩
  obtain ⟨hord, hNF, -⟩ := G2_three_exact_automorphism_normal_form hf K hK
  obtain ⟨hordk, hNFk, -⟩ := G2_three_exact_automorphism_normal_form hd k hk
  refine ⟨hJC, hnorm, le_antisymm (fun η hη => ?_) ?_, hFrφ, ?_⟩
  ·
    have hfix : ∀ x : C, (x : ModGL ReeTag.G2.tag K) ∈ J → η x = x := fun x hx => by
      have h := (mem_fixingSubgroup_iff _).1 hη x (Subgroup.mem_subgroupOf.2 hx)
      rwa [MulAut.smul_def] at h
    obtain ⟨⟨g, a⟩, hga, -⟩ := hNF η
    dsimp only at hga
    have hgJ : (g : ModGL ReeTag.G2.tag K) ∈ J := by
      rw [← hnorm]
      refine Subgroup.mem_inf.2 ⟨g.2, Subgroup.mem_normalizer_iff.2 fun y => ⟨fun hy => ?_,
        fun hy => ?_⟩⟩
      ·
        obtain ⟨y', hy'⟩ := (mem_subfieldImage_iff_exists k ⟨y, hJC hy⟩).1 hy
        have hyv : (subfieldInclusion k y' : ModGL ReeTag.G2.tag K) = y :=
          congrArg Subtype.val hy'
        set x' := (ReeTag.G2.finiteExceptionalAut k ^ (a : ℕ))⁻¹ y'
        have hx : (φ ^ (a : ℕ)) (subfieldInclusion k x') = subfieldInclusion k y' := by
          rw [finiteExceptionalAut_pow_subfieldInclusion_G2 k, MulAut.apply_inv_self]
        have h1 := hfix (subfieldInclusion k x') ⟨x', x'.2, rfl⟩
        rw [hga, MulAut.mul_apply, hx, MulAut.conj_apply] at h1
        have h2 := congrArg Subtype.val h1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hyv] at h2
        rw [h2]
        exact ⟨x', x'.2, rfl⟩
      ·
        obtain ⟨w', hw'⟩ := (mem_subfieldImage_iff_exists k ⟨_, hJC hy⟩).1 hy
        have hwv : (subfieldInclusion k w' : ModGL ReeTag.G2.tag K) =
            (g : ModGL ReeTag.G2.tag K) * y * (g : ModGL ReeTag.G2.tag K)⁻¹ :=
          congrArg Subtype.val hw'
        have h1 := hfix (subfieldInclusion k w') ⟨w', w'.2, rfl⟩
        rw [hga, MulAut.mul_apply, MulAut.conj_apply] at h1
        have h2 := congrArg Subtype.val h1
        simp only [Subgroup.coe_mul, Subgroup.coe_inv, hwv] at h2
        have h3 := mul_left_cancel (mul_right_cancel h2)
        rw [← h3]
        exact hφJ _ _ ⟨w', w'.2, rfl⟩
    obtain ⟨g', rfl⟩ := (mem_subfieldImage_iff_exists k g).1 hgJ
    set φk := ReeTag.G2.finiteExceptionalAut k
    have hidk : MulAut.conj g' * φk ^ (a : ℕ) = 1 := by
      refine MulEquiv.ext fun y => subfieldInclusion_injective k ?_
      have h1 := hfix (subfieldInclusion k y) ⟨y, y.2, rfl⟩
      rw [hga, MulAut.mul_apply, finiteExceptionalAut_pow_subfieldInclusion_G2 k (a : ℕ) y,
        MulAut.conj_apply] at h1
      rw [MulAut.one_apply, MulAut.mul_apply, MulAut.conj_apply, map_mul, map_mul, map_inv]
      exact h1
    have hmod : φk ^ ((a : ℕ) % (2 * d)) = φk ^ (a : ℕ) := by
      have h := pow_mod_orderOf φk (a : ℕ)
      rwa [hordk] at h
    obtain ⟨q, -, hq⟩ := hNFk 1
    have h1 := hq (1, ⟨0, by omega⟩) (by simp)
    have h2 := hq (g', ⟨(a : ℕ) % (2 * d), Nat.mod_lt _ (by omega)⟩) (by
      show 1 = MulAut.conj g' * φk ^ ((a : ℕ) % (2 * d))
      rw [hmod, hidk])
    have h3 := h2.trans h1.symm
    have hg'1 : g' = 1 := congrArg Prod.fst h3
    have ha0 : (a : ℕ) % (2 * d) = 0 := congrArg (fun x => (x.2 : ℕ)) h3
    obtain ⟨t, ht⟩ := Nat.dvd_of_mod_eq_zero ha0
    subst hg'1
    rw [hga, map_one, map_one, one_mul, ht, pow_mul, ← hFrφ]
    exact Subgroup.npow_mem_zpowers _ t
  ·
    refine Subgroup.zpowers_le.2 ((mem_fixingSubgroup_iff _).2 fun x hx => ?_)
    rw [MulAut.smul_def]
    exact hFrfix x (Subgroup.mem_subgroupOf.1 hx)
  ·
    have hdvd : 2 * d ∣ orderOf φ := by
      rw [hord]
      exact Nat.mul_dvd_mul_left 2 hdf
    rw [Nat.card_zpowers, hFrφ, orderOf_pow_of_dvd (by omega) hdvd, hord,
      Nat.mul_div_mul_left _ _ (by norm_num : 0 < 2)]

end G2

end CFSG.RankThree.Chevalley

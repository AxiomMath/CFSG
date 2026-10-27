module

public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex
public import CFSG.LieType.Chevalley.OddF4CosetDescent

public section

namespace CFSG.RankThree.OddE7Rational

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootDiag)
open CFSG.ComponentClassification.OuterAutomorphisms (inner)

theorem odd_E7_rational_inner_diagonal_field_automorphism_structure {ℓ f : ℕ} (hℓ : ℓ.Prime)
    (hℓ2 : ℓ ≠ 2) (_hf : 1 ≤ f) (K : Type) [Field K] [Finite K] (hK : Nat.card K = ℓ ^ f)
    (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L] (Fr : L →+* L)
    (hFr : ∀ c, Fr c = c ^ Nat.card K) (R H : Subgroup (ModGL Tag.E7 L))
    (hR : R = adjointGroup Tag.E7 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _))
    (hH : H = (adjointGroup Tag.E7 K).map (baseChangeGL (algebraMap K L))) :
    Finite R ∧ H ≤ R ∧ R ≤ Subgroup.normalizer (H : Set (ModGL Tag.E7 L)) ∧
    (∀ z ∈ R, ∃ y : ModGL Tag.E7 K, baseChangeGL (algebraMap K L) y = z) ∧
    ∃ ρ : R →* MulAut (adjointGroup Tag.E7 K),
      (∀ (z : R) (h : adjointGroup Tag.E7 K),
        baseChangeGL (algebraMap K L) (ρ z h : ModGL Tag.E7 K) =
          (z : ModGL Tag.E7 L) * baseChangeGL (algebraMap K L) (h : ModGL Tag.E7 K) *
            (z : ModGL Tag.E7 L)⁻¹) ∧
      Function.Injective ρ ∧
      (H.subgroupOf R).map ρ = inner (adjointGroup Tag.E7 K) ∧
      ρ.range.Normal ∧
      ((inner (adjointGroup Tag.E7 K)).subgroupOf ρ.range).index ∣ 2 ∧
      (∀ η : MulAut (adjointGroup Tag.E7 K),
        ∃! p : R × (K ≃+* K), η = ρ p.1 * entrywiseAdjointAut Tag.E7 p.2) ∧
      (∃ βR : (K ≃+* K) → MulAut R,
        (∀ (β : K ≃+* K) (z : R) (y : ModGL Tag.E7 K), baseChangeGL (algebraMap K L) y = z →
          ((βR β z : R) : ModGL Tag.E7 L) =
            baseChangeGL (algebraMap K L) (Units.map (entrywiseHom β.toRingHom) y)) ∧
        ∀ (β : K ≃+* K) (z : R), entrywiseAdjointAut Tag.E7 β * ρ z *
          (entrywiseAdjointAut Tag.E7 β)⁻¹ = ρ (βR β z)) ∧
      (∃ π : MulAut (adjointGroup Tag.E7 K) →* (K ≃+* K), Function.Surjective π ∧
        π.ker = ρ.range ∧
        ∀ (z : R) (β : K ≃+* K), π (ρ z * entrywiseAdjointAut Tag.E7 β) = β) ∧
      ∀ (k : Subfield K) (S : Subgroup (MulAut (adjointGroup Tag.E7 K))),
        S = fixingSubgroup (MulAut (adjointGroup Tag.E7 K))
          {j : adjointGroup Tag.E7 K | (j : ModGL Tag.E7 K) ∈
            (adjointGroup Tag.E7 k).map (baseChangeGL k.subtype)} →
        (S : Set (MulAut (adjointGroup Tag.E7 K))) =
            Set.range (fun σ : K ≃ₐ[k] K => entrywiseAdjointAut Tag.E7 σ.toRingEquiv) ∧
          IsCyclic S ∧ Nat.card S = Module.finrank k K := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hℓodd : Odd ℓ := hℓ.odd_of_ne_two hℓ2
  have hKodd : Odd (Nat.card K) := hK ▸ hℓodd.pow
  have : Fact ℓ.Prime := ⟨hℓ⟩
  have : NeZero ℓ := ⟨hℓ.ne_zero⟩
  have : CharP K ℓ := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hK])
  have : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have : Algebra.IsAlgebraic K L := IsAlgClosure.isAlgebraic
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ZMod ℓ →+* K, c₀ = ZMod.castHom (dvd_refl ℓ) K := ⟨_, rfl⟩
  have hZodd : Odd (Nat.card (ZMod ℓ)) := by
    rw [Nat.card_zmod]
    exact hℓodd
  obtain ⟨-, hHR, hRN, -⟩ :=
    exceptional_Lang_Frobenius_fixed_derived_root_group Tag.E7 K hKodd L Fr hFr
  obtain ⟨hfinR, -, hindex⟩ := odd_E7_rational_derived_index_at_most_two K hKodd L Fr hFr
  obtain ⟨hιinj, -, -, hconjinj⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness Tag.E7 K hKodd L (algebraMap K L)
  obtain ⟨-, -, hcent₀, -⟩ := exceptional_Lang_finite_root_centralizer_faithfulness Tag.E7
    (ZMod ℓ) hZodd L ((algebraMap K L).comp c₀)
  rw [← hR] at hHR hRN hfinR hindex
  rw [← hH] at hHR hRN hindex hconjinj
  set ι : K →+* L := algebraMap K L with hιdef
  set C := adjointGroup Tag.E7 K with hCdef
  set G₀ := adjointGroup Tag.E7 L with hG₀def
  have hFix : ∀ y : ModGL Tag.E7 K,
      Units.map (entrywiseHom Fr) (baseChangeGL ι y) = baseChangeGL ι y :=
    fun y => units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr y
  have hmemR : ∀ y : ModGL Tag.E7 K, baseChangeGL ι y ∈ G₀ → baseChangeGL ι y ∈ R := by
    intro y hy
    rw [hR]
    exact ⟨hy, hFix y⟩
  have hlift : ∀ a : Fin Tag.E7.rank → Kˣ, baseChangeGL ι (rootDiagUnit Tag.E7 a) ∈ G₀ := by
    intro a
    rw [baseChangeGL_rootDiagUnit]
    exact (exceptional_Lang_adjoint_diagonal_lift Tag.E7 L _).1
  have hCG : ∀ c ∈ C, baseChangeGL ι c ∈ G₀ := fun c hc => baseChangeGL_mem_adjointGroup ι hc
  have hdec : ∀ z ∈ R, ∃ a : Fin Tag.E7.rank → Kˣ, ∃ c ∈ C,
      z = baseChangeGL ι (rootDiagUnit Tag.E7 a * c) := by
    intro z hz
    rw [hR] at hz
    obtain ⟨a, u, hu, rfl⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed Tag.E7 Fr hFr hz.1 hz.2
    obtain ⟨c, hc, rfl⟩ := hu
    exact ⟨a, c, hc, by rw [map_mul]⟩
  have hentK : ∀ z ∈ R, ∃ y : ModGL Tag.E7 K, baseChangeGL ι y = z := by
    intro z hz
    obtain ⟨a, c, -, rfl⟩ := hdec z hz
    exact ⟨_, rfl⟩
  have hRle : R ≤ G₀ ⊓ Subgroup.normalizer (H : Set (ModGL Tag.E7 L)) := by
    intro z hz
    refine ⟨?_, hRN hz⟩
    rw [hR] at hz
    exact hz.1
  let e : C ≃* H :=
    (C.equivMapOfInjective (baseChangeGL ι) hιinj).trans (MulEquiv.subgroupCongr hH.symm)
  have he : ∀ c : C, (e c : ModGL Tag.E7 L) = baseChangeGL ι c := fun _ => rfl
  let ρ : R →* MulAut C := (MulAut.congr e.symm).toMonoidHom.comp
    ((conjNormalizerHom G₀ H).comp (Subgroup.inclusion hRle))
  have hρ : ∀ (z : R) (h : C), baseChangeGL ι (ρ z h : ModGL Tag.E7 K) =
      (z : ModGL Tag.E7 L) * baseChangeGL ι (h : ModGL Tag.E7 K) * (z : ModGL Tag.E7 L)⁻¹ := by
    intro z h
    rw [← he, ← he]
    change ((e (e.symm (conjNormalizerHom G₀ H (Subgroup.inclusion hRle z) (e h)))) :
      ModGL Tag.E7 L) = _
    rw [MulEquiv.apply_symm_apply, conjNormalizerHom_apply]
    rfl
  have hρinj : Function.Injective ρ :=
    (MulAut.congr e.symm).injective.comp (hconjinj.comp (Subgroup.inclusion_injective hRle))
  have hρH : ∀ (c : C) (hz : baseChangeGL ι (c : ModGL Tag.E7 K) ∈ R),
      ρ ⟨_, hz⟩ = MulAut.conj c := by
    intro c hz
    refine MulEquiv.ext fun h => Subtype.ext (hιinj ?_)
    rw [hρ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
      map_mul, map_inv]
  have hρmap : (H.subgroupOf R).map ρ = inner C := by
    apply le_antisymm
    · rintro _ ⟨z, hzH, rfl⟩
      have hzH' : (z : ModGL Tag.E7 L) ∈ H := Subgroup.mem_subgroupOf.mp hzH
      rw [hH] at hzH'
      obtain ⟨c, hc, hcz⟩ := hzH'
      have hz : baseChangeGL ι ((⟨c, hc⟩ : C) : ModGL Tag.E7 K) ∈ R := hcz ▸ z.2
      have hzeq : z = ⟨_, hz⟩ := Subtype.ext hcz.symm
      rw [hzeq, hρH ⟨c, hc⟩ hz]
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro _ ⟨c, rfl⟩
      have hcH : baseChangeGL ι (c : ModGL Tag.E7 K) ∈ H := by
        rw [hH]
        exact ⟨c, c.2, rfl⟩
      exact ⟨⟨_, hHR hcH⟩, Subgroup.mem_subgroupOf.mpr hcH, hρH c (hHR hcH)⟩
  have hcancel : ∀ (β : K ≃+* K) (x : C),
      entrywiseAdjointAut Tag.E7 β (entrywiseAdjointAut Tag.E7 β⁻¹ x) = x := by
    intro β x
    rw [← MulAut.mul_apply, ← entrywiseAdjointAut_mul, mul_inv_cancel, entrywiseAdjointAut_one,
      MulAut.one_apply]
  have hinv : ∀ β : K ≃+* K, (entrywiseAdjointAut Tag.E7 β)⁻¹ = entrywiseAdjointAut Tag.E7 β⁻¹ :=
    fun β => (map_inv (entrywiseAdjointAutHom (τ := Tag.E7) (K := K)) β).symm
  have hfieldone : ∀ γ : K ≃+* K, entrywiseAdjointAut Tag.E7 γ = 1 → γ = 1 := by
    intro γ hγ
    refine RingEquiv.ext fun c => ?_
    have h1 := congrArg (fun η : MulAut C => η (adjX Tag.E7 K ⟨0, Tag.E7.rank_pos⟩ c)) hγ
    have h2 : entrywiseAdjointAut Tag.E7 γ (adjX Tag.E7 K ⟨0, Tag.E7.rank_pos⟩ c) =
        adjX Tag.E7 K ⟨0, Tag.E7.rank_pos⟩ (γ c) :=
      Subtype.ext (units_map_entrywiseHom_xUnit γ.toRingHom _ c)
    simp only [MulAut.one_apply] at h1
    rw [h2] at h1
    rw [RingAut.one_apply]
    exact adjX_injective _ h1
  have hγfix : ∀ (γ : K ≃+* K) (y : ModGL Tag.E7 (ZMod ℓ)),
      Units.map (entrywiseHom γ.toRingHom) (baseChangeGL c₀ y) = baseChangeGL c₀ y := by
    intro γ y
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
      RingHom.ext_zmod (γ.toRingHom.comp c₀) c₀]
  have hJ₀C : ∀ y ∈ adjointGroup Tag.E7 (ZMod ℓ), baseChangeGL c₀ y ∈ C :=
    fun y hy => baseChangeGL_mem_adjointGroup c₀ hy
  have hkey : ∀ w : R, (∀ y (hy : y ∈ adjointGroup Tag.E7 (ZMod ℓ)),
      ρ w ⟨_, hJ₀C y hy⟩ = ⟨_, hJ₀C y hy⟩) → w = 1 := by
    intro w hw
    have hwG : (w : ModGL Tag.E7 L) ∈ G₀ := (hRle w.2).1
    refine Subtype.ext (hcent₀ (w : ModGL Tag.E7 L) hwG fun h hh => ?_)
    obtain ⟨y, hy, rfl⟩ := hh
    have h1 := congrArg (fun j : C => baseChangeGL ι (j : ModGL Tag.E7 K)) (hw y hy)
    simp only [hρ] at h1
    rw [← baseChangeGL_baseChangeGL]
    calc (w : ModGL Tag.E7 L) * baseChangeGL ι (baseChangeGL c₀ y) =
          ((w : ModGL Tag.E7 L) * baseChangeGL ι (baseChangeGL c₀ y) * (w : ModGL Tag.E7 L)⁻¹) *
            w := by group
      _ = baseChangeGL ι (baseChangeGL c₀ y) * w := by rw [h1]
  have hDF : ∀ (w : R) (γ : K ≃+* K), ρ w = entrywiseAdjointAut Tag.E7 γ → w = 1 ∧ γ = 1 := by
    intro w γ h
    have hw : w = 1 := hkey w fun y hy => by
      rw [h]
      exact Subtype.ext (hγfix γ y)
    refine ⟨hw, hfieldone γ ?_⟩
    rw [← h, hw, map_one]
  have hexist : ∀ η : MulAut C, ∃ (z : R) (γ : K ≃+* K),
      η = ρ z * entrywiseAdjointAut Tag.E7 γ := by
    intro η
    obtain ⟨g, a, σ, ε, hη⟩ :=
      (ordinary_E_exact_automorphism_normal_form Tag.E7 (Or.inr (Or.inl rfl)) K).2.2 η
    have hQ : exactQ Tag.E7 K ε = 1 := rfl
    have hyR : baseChangeGL ι ((g : ModGL Tag.E7 K) * rootDiagUnit Tag.E7 a) ∈ R :=
      hmemR _ (by rw [map_mul]; exact mul_mem (hCG g g.2) (hlift a))
    refine ⟨⟨_, hyR⟩, σ, MulEquiv.ext fun h => Subtype.ext (hιinj ?_)⟩
    rw [MulAut.mul_apply, hρ, hη h, hQ, coe_entrywiseAdjointAut]
    simp only [map_mul, map_inv, mul_one, inv_one, mul_inv_rev, mul_assoc]
  have huniq : ∀ (z z' : R) (γ γ' : K ≃+* K), ρ z * entrywiseAdjointAut Tag.E7 γ =
      ρ z' * entrywiseAdjointAut Tag.E7 γ' → z = z' ∧ γ = γ' := by
    intro z z' γ γ' h
    have h1 : ρ (z'⁻¹ * z) = entrywiseAdjointAut Tag.E7 (γ' * γ⁻¹) := by
      rw [map_mul, map_inv, entrywiseAdjointAut_mul, ← hinv, inv_mul_eq_iff_eq_mul, ← mul_assoc,
        eq_mul_inv_iff_mul_eq, h]
    obtain ⟨h2, h3⟩ := hDF _ _ h1
    exact ⟨(inv_mul_eq_one.mp h2).symm, (mul_inv_eq_one.mp h3).symm⟩
  have hEU : ∀ η : MulAut C,
      ∃! p : R × (K ≃+* K), η = ρ p.1 * entrywiseAdjointAut Tag.E7 p.2 := by
    intro η
    obtain ⟨z, γ, hzγ⟩ := hexist η
    refine ⟨(z, γ), hzγ, fun p hp => ?_⟩
    obtain ⟨h1, h2⟩ := huniq _ _ _ _ (hp.symm.trans hzγ)
    exact Prod.ext h1 h2
  set RK : Subgroup (ModGL Tag.E7 K) := R.comap (baseChangeGL ι) with hRKdef
  have hmapRK : RK.map (baseChangeGL ι) = R :=
    Subgroup.map_comap_eq_self fun z hz => hentK z hz
  let eR : RK ≃* R :=
    (RK.equivMapOfInjective (baseChangeGL ι) hιinj).trans (MulEquiv.subgroupCongr hmapRK)
  have heR : ∀ y : RK, (eR y : ModGL Tag.E7 L) = baseChangeGL ι y := fun _ => rfl
  have hβRK : ∀ (β : K ≃+* K) (y : ModGL Tag.E7 K), y ∈ RK →
      Units.map (entrywiseHom β.toRingHom) y ∈ RK := by
    intro β y hy
    obtain ⟨a, c, hc, hac⟩ := hdec _ hy
    have hyac : y = rootDiagUnit Tag.E7 a * c := hιinj hac
    subst hyac
    show baseChangeGL ι _ ∈ R
    apply hmemR
    have h1 : Units.map (entrywiseHom β.toRingHom) (rootDiagUnit Tag.E7 a) =
        rootDiagUnit Tag.E7 (fun i => Units.map β.toRingHom.toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag β.toRingHom a)
    rw [map_mul, map_mul, h1]
    exact mul_mem (hlift _) (hCG _ (entrywiseAdjointAut Tag.E7 β ⟨c, hc⟩).2)
  have hmapβ : ∀ β : K ≃+* K, RK.map (exactEntrywiseAut Tag.E7 β).toMonoidHom = RK := by
    intro β
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hβRK β y hy
    · intro y hy
      exact ⟨Units.map (entrywiseHom β.symm.toRingHom) y, hβRK β.symm y hy,
        exactEntrywiseAut_right_inv β y⟩
  let βR : (K ≃+* K) → MulAut R := fun β =>
    (eR.symm.trans (mulAutRestrict RK (exactEntrywiseAut Tag.E7 β) (hmapβ β))).trans eR
  have hβR : ∀ (β : K ≃+* K) (z : R) (y : ModGL Tag.E7 K), baseChangeGL ι y = z →
      ((βR β z : R) : ModGL Tag.E7 L) =
        baseChangeGL ι (Units.map (entrywiseHom β.toRingHom) y) := by
    intro β z y hyz
    have hyRK : y ∈ RK := by
      show baseChangeGL ι y ∈ R
      rw [hyz]
      exact z.2
    have h1 : eR.symm z = ⟨y, hyRK⟩ := by
      apply eR.injective
      rw [MulEquiv.apply_symm_apply]
      exact Subtype.ext hyz.symm
    change (eR (mulAutRestrict RK (exactEntrywiseAut Tag.E7 β) (hmapβ β) (eR.symm z)) :
      ModGL Tag.E7 L) = _
    rw [h1, heR, coe_mulAutRestrict]
    rfl
  have hconjβ : ∀ (β : K ≃+* K) (z : R), entrywiseAdjointAut Tag.E7 β * ρ z *
      (entrywiseAdjointAut Tag.E7 β)⁻¹ = ρ (βR β z) := by
    intro β z
    obtain ⟨y, hyz⟩ := hentK z z.2
    refine MulEquiv.ext fun h => Subtype.ext (hιinj ?_)
    rw [hρ, hβR β z y hyz, hinv, MulAut.mul_apply, MulAut.mul_apply]
    set h' := entrywiseAdjointAut Tag.E7 β⁻¹ h with hh'
    have hρh' : (ρ z h' : ModGL Tag.E7 K) = y * h' * y⁻¹ := by
      apply hιinj
      rw [hρ, ← hyz, map_mul, map_mul, map_inv]
    have hβh' : Units.map (entrywiseHom β.toRingHom) (h' : ModGL Tag.E7 K) = h := by
      rw [← coe_entrywiseAdjointAut, hh', hcancel]
    rw [coe_entrywiseAdjointAut, hρh']
    simp only [map_mul, map_inv, hβh']
  choose P hP using fun η => (hEU η).exists
  have hPeq : ∀ (z : R) (γ : K ≃+* K), P (ρ z * entrywiseAdjointAut Tag.E7 γ) = (z, γ) := by
    intro z γ
    obtain ⟨h1, h2⟩ := huniq _ _ _ _ (hP (ρ z * entrywiseAdjointAut Tag.E7 γ)).symm
    exact Prod.ext h1 h2
  have hone : (1 : MulAut C) = ρ 1 * entrywiseAdjointAut Tag.E7 1 := by
    rw [map_one, entrywiseAdjointAut_one, one_mul]
  let π : MulAut C →* (K ≃+* K) :=
    { toFun := fun η => (P η).2
      map_one' := by
        show (P 1).2 = 1
        rw [hone, hPeq]
      map_mul' := fun η₁ η₂ => by
        show (P (η₁ * η₂)).2 = (P η₁).2 * (P η₂).2
        have e : η₁ * η₂ = ρ ((P η₁).1 * βR (P η₁).2 (P η₂).1) *
            entrywiseAdjointAut Tag.E7 ((P η₁).2 * (P η₂).2) := by
          conv_lhs => rw [hP η₁, hP η₂]
          rw [map_mul ρ, ← hconjβ, entrywiseAdjointAut_mul]
          group
        rw [e, hPeq] }
  have hπ : ∀ (z : R) (γ : K ≃+* K), π (ρ z * entrywiseAdjointAut Tag.E7 γ) = γ := by
    intro z γ
    show (P _).2 = γ
    rw [hPeq]
  have hπsurj : Function.Surjective π := fun γ => ⟨ρ 1 * entrywiseAdjointAut Tag.E7 γ, hπ 1 γ⟩
  have hπker : π.ker = ρ.range := by
    ext η
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro h1
      refine ⟨(P η).1, ?_⟩
      have h2 := hP η
      rw [show (P η).2 = 1 from h1, entrywiseAdjointAut_one, mul_one] at h2
      exact h2.symm
    · rintro ⟨z, rfl⟩
      have h3 : ρ z = ρ z * entrywiseAdjointAut Tag.E7 1 := by
        rw [entrywiseAdjointAut_one, mul_one]
      rw [h3, hπ]
  have hD : ρ.range.Normal := hπker ▸ π.normal_ker
  have hidx : ((CFSG.ComponentClassification.OuterAutomorphisms.inner C).subgroupOf
      ρ.range).index ∣ 2 := by
    have : Finite R := hfinR
    have e1 : (CFSG.ComponentClassification.OuterAutomorphisms.inner C).subgroupOf ρ.range =
        (H.subgroupOf R).map ((MonoidHom.ofInjective hρinj : R ≃* ρ.range) : R →* ρ.range) := by
      ext x
      rw [Subgroup.mem_subgroupOf, ← hρmap, Subgroup.mem_map, Subgroup.mem_map]
      constructor
      · rintro ⟨z, hz, hzx⟩
        exact ⟨z, hz, Subtype.ext hzx⟩
      · rintro ⟨z, hz, hzx⟩
        exact ⟨z, hz, congrArg Subtype.val hzx⟩
    rw [e1, Subgroup.index_map_equiv]
    have h0 : (H.subgroupOf R).index ≠ 0 := Subgroup.index_ne_zero_of_finite
    obtain h | h : (H.subgroupOf R).index = 1 ∨ (H.subgroupOf R).index = 2 := by omega
    · rw [h]
      exact one_dvd 2
    · rw [h]
  refine ⟨hfinR, hHR, hRN, hentK, ρ, hρ, hρinj, hρmap, hD, hidx, hEU, ⟨βR, hβR, hconjβ⟩,
    ⟨π, hπsurj, hπker, hπ⟩, ?_⟩
  intro k S hS
  have : CharP k ℓ := RingHom.charP k.subtype k.subtype_injective ℓ
  obtain ⟨c₀k, hc₀kdef⟩ : ∃ c₀k : ZMod ℓ →+* k, c₀k = ZMod.castHom (dvd_refl ℓ) k := ⟨_, rfl⟩
  have hc₀k : k.subtype.comp c₀k = c₀ := RingHom.ext_zmod _ _
  set Jk : Set C := {j | (j : ModGL Tag.E7 K) ∈ (adjointGroup Tag.E7 k).map
    (baseChangeGL k.subtype)} with hJkdef
  have hJ₀k : ∀ y (hy : y ∈ adjointGroup Tag.E7 (ZMod ℓ)), (⟨_, hJ₀C y hy⟩ : C) ∈ Jk := by
    intro y hy
    refine ⟨baseChangeGL c₀k y, baseChangeGL_mem_adjointGroup c₀k hy, ?_⟩
    show baseChangeGL k.subtype (baseChangeGL c₀k y) = baseChangeGL c₀ y
    rw [baseChangeGL_baseChangeGL, hc₀k]
  have hfixJ : ∀ σ : K ≃ₐ[k] K, ∀ j ∈ Jk, entrywiseAdjointAut Tag.E7 σ.toRingEquiv j = j := by
    rintro σ j ⟨y, -, hyj⟩
    apply Subtype.ext
    rw [coe_entrywiseAdjointAut, ← hyj, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL]
    rw [show σ.toRingEquiv.toRingHom.comp k.subtype = k.subtype from
      RingHom.ext fun x => σ.commutes x]
  have hSset : (S : Set (MulAut C)) =
      Set.range (fun σ : K ≃ₐ[k] K => entrywiseAdjointAut Tag.E7 σ.toRingEquiv) := by
    rw [hS]
    ext η
    rw [SetLike.mem_coe, mem_fixingSubgroup_iff, Set.mem_range]
    constructor
    · intro hη
      obtain ⟨z, γ, rfl⟩ := hexist η
      have hz : z = 1 := hkey z fun y hy => by
        have h1 : (ρ z * entrywiseAdjointAut Tag.E7 γ) ⟨_, hJ₀C y hy⟩ = ⟨_, hJ₀C y hy⟩ :=
          hη _ (hJ₀k y hy)
        rw [MulAut.mul_apply] at h1
        have h2 : entrywiseAdjointAut Tag.E7 γ ⟨_, hJ₀C y hy⟩ = ⟨_, hJ₀C y hy⟩ :=
          Subtype.ext (hγfix γ y)
        rw [h2] at h1
        exact h1
      subst hz
      rw [map_one, one_mul] at hη ⊢
      have hγk : ∀ x : k, γ (x : K) = x := by
        intro x
        have hxJ : adjX Tag.E7 K ⟨0, Tag.E7.rank_pos⟩ (x : K) ∈ Jk :=
          ⟨xUnit Tag.E7 k ⟨0, Tag.E7.rank_pos⟩ x, xUnit_mem_adjointGroup _ _,
            baseChangeGL_xUnit k.subtype _ x⟩
        have h1 : entrywiseAdjointAut Tag.E7 γ (adjX Tag.E7 K ⟨0, Tag.E7.rank_pos⟩ (x : K)) =
            adjX Tag.E7 K ⟨0, Tag.E7.rank_pos⟩ (x : K) := hη _ hxJ
        have h2 : entrywiseAdjointAut Tag.E7 γ (adjX Tag.E7 K ⟨0, Tag.E7.rank_pos⟩ (x : K)) =
            adjX Tag.E7 K ⟨0, Tag.E7.rank_pos⟩ (γ x) :=
          Subtype.ext (units_map_entrywiseHom_xUnit γ.toRingHom _ _)
        rw [h2] at h1
        exact adjX_injective _ h1
      exact ⟨AlgEquiv.ofRingEquiv (f := γ) fun x => hγk x, rfl⟩
    · rintro ⟨σ, rfl⟩ j hj
      exact hfixJ σ j hj
  let φ : (K ≃ₐ[k] K) →* MulAut C :=
    { toFun := fun σ => entrywiseAdjointAut Tag.E7 σ.toRingEquiv
      map_one' := entrywiseAdjointAut_one
      map_mul' := fun σ τ => entrywiseAdjointAut_mul σ.toRingEquiv τ.toRingEquiv }
  have hEinj : Function.Injective (entrywiseAdjointAutHom (τ := Tag.E7) (K := K)) :=
    (injective_iff_map_eq_one _).mpr hfieldone
  have hφinj : Function.Injective φ := by
    intro σ τ h
    have h1 : σ.toRingEquiv = τ.toRingEquiv := hEinj h
    exact AlgEquiv.ext fun x => congrArg (fun g : K ≃+* K => g x) h1
  have hSφ : S = φ.range := by
    apply SetLike.ext'
    rw [hSset, MonoidHom.coe_range]
    rfl
  refine ⟨hSset, ?_, ?_⟩
  · rw [hSφ]
    exact isCyclic_of_surjective φ.rangeRestrict φ.rangeRestrict_surjective
  · rw [hSφ, ← Nat.card_congr (MonoidHom.ofInjective hφinj).toEquiv,
      IsGalois.card_aut_eq_finrank]

end CFSG.RankThree.OddE7Rational

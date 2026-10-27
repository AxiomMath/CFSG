module

public import CFSG.RankThree.PartOne.KE.OddE6RationalGraph
public import CFSG.RankThree.PartOne.KE.OddE6InnerGraph
public import CFSG.LieType.Chevalley.CLSOddE7RationalDerivedIndex

public section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley (rootDiagUnit rootDiag)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)

theorem conj_inv_conj_aux {G : Type*} [Group G] (w x q : G) (h : w * x * w⁻¹ = q * x * q⁻¹) :
    w⁻¹ * (q * x * q⁻¹) * w⁻¹⁻¹ = x := by
  rw [← h]
  group

theorem conj_graph_aux {G : Type*} [Group G] (P z x : G) (hP : P * P = 1) :
    P * (z * (P * x * P⁻¹) * z⁻¹) * P⁻¹ = (P * z * P⁻¹) * x * (P * z * P⁻¹)⁻¹ := by
  have hinv : P⁻¹ = P := inv_eq_of_mul_eq_one_right hP
  simp only [hinv, mul_inv_rev, mul_assoc]

theorem odd_E6_rational_inner_diagonal_graph_field_automorphism_structure {ℓ f : ℕ}
    (hℓ : ℓ.Prime) (hℓ2 : ℓ ≠ 2) (_hf : 1 ≤ f) (K : Type) [Field K] [Finite K]
    (hK : Nat.card K = ℓ ^ f) (L : Type) [Field L] [Algebra K L] [IsAlgClosure K L]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ Nat.card K) (R H : Subgroup (ModGL Tag.E6 L))
    (hR : R = adjointGroup Tag.E6 L ⊓ (Units.map (entrywiseHom Fr)).eqLocus (MonoidHom.id _))
    (hH : H = (adjointGroup Tag.E6 K).map (baseChangeGL (algebraMap K L))) :
    Finite R ∧ H ≤ R ∧ R ≤ Subgroup.normalizer (H : Set (ModGL Tag.E6 L)) ∧
    (∀ z ∈ R, ∃ y : ModGL Tag.E6 K, baseChangeGL (algebraMap K L) y = z) ∧
    ∃ ρ : R →* MulAut (adjointGroup Tag.E6 K),
      (∀ (z : R) (h : adjointGroup Tag.E6 K),
        baseChangeGL (algebraMap K L) (ρ z h : ModGL Tag.E6 K) =
          (z : ModGL Tag.E6 L) * baseChangeGL (algebraMap K L) (h : ModGL Tag.E6 K) *
            (z : ModGL Tag.E6 L)⁻¹) ∧
      Function.Injective ρ ∧
      (H.subgroupOf R).map ρ = inner (adjointGroup Tag.E6 K) ∧
      ρ.range.Normal ∧
      ((inner (adjointGroup Tag.E6 K)).subgroupOf ρ.range).index ∣ 3 ∧
      graphAut K 1 ^ 2 = 1 ∧
      (∀ β : K ≃+* K, graphAut K 1 * entrywiseAdjointAut Tag.E6 β =
        entrywiseAdjointAut Tag.E6 β * graphAut K 1) ∧
      Function.Injective (graphFieldHom (K := K)) ∧
      (∀ η : MulAut (adjointGroup Tag.E6 K),
        ∃! p : R × (Multiplicative (ZMod 2) × (K ≃+* K)), η = ρ p.1 * graphFieldHom p.2) ∧
      (∃ π : MulAut (adjointGroup Tag.E6 K) →* Multiplicative (ZMod 2) × (K ≃+* K),
        Function.Surjective π ∧ π.ker = ρ.range ∧
        ∀ (z : R) (x : Multiplicative (ZMod 2) × (K ≃+* K)), π (ρ z * graphFieldHom x) = x) ∧
      (∃ (βR : (K ≃+* K) → MulAut R) (γR : MulAut R),
        (∀ (β : K ≃+* K) (z : R) (y : ModGL Tag.E6 K), baseChangeGL (algebraMap K L) y = z →
          ((βR β z : R) : ModGL Tag.E6 L) =
            baseChangeGL (algebraMap K L) (Units.map (entrywiseHom β.toRingHom) y)) ∧
        (∀ (β : K ≃+* K) (z : R), entrywiseAdjointAut Tag.E6 β * ρ z *
          (entrywiseAdjointAut Tag.E6 β)⁻¹ = ρ (βR β z)) ∧
        (∀ z : R, ((γR z : R) : ModGL Tag.E6 L) =
          diagramE6 L * (z : ModGL Tag.E6 L) * (diagramE6 L)⁻¹) ∧
        (∀ z : R, graphAut K 1 * ρ z * (graphAut K 1)⁻¹ = ρ (γR z)) ∧
        ∀ (β : K ≃+* K) (z : R), βR β (γR z) = γR (βR β z)) ∧
      ∀ (k : Subfield K) (S : Subgroup (MulAut (adjointGroup Tag.E6 K))),
        S = fixingSubgroup (MulAut (adjointGroup Tag.E6 K))
          {j : adjointGroup Tag.E6 K | (j : ModGL Tag.E6 K) ∈
            (adjointGroup Tag.E6 k).map (baseChangeGL k.subtype)} →
        (S : Set (MulAut (adjointGroup Tag.E6 K))) =
            Set.range (fun σ : K ≃ₐ[k] K => entrywiseAdjointAut Tag.E6 σ.toRingEquiv) ∧
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
    exceptional_Lang_Frobenius_fixed_derived_root_group Tag.E6 K hKodd L Fr hFr
  obtain ⟨hιinj, -, -, hconjinj⟩ :=
    exceptional_Lang_finite_root_centralizer_faithfulness Tag.E6 K hKodd L (algebraMap K L)
  rw [← hR] at hHR hRN
  rw [← hH] at hHR hRN hconjinj
  set ι : K →+* L := algebraMap K L with hιdef
  set C := adjointGroup Tag.E6 K with hCdef
  set G₀ := adjointGroup Tag.E6 L with hG₀def
  have hFix : ∀ y : ModGL Tag.E6 K,
      Units.map (entrywiseHom Fr) (baseChangeGL ι y) = baseChangeGL ι y :=
    fun y => units_map_entrywiseHom_baseChangeGL_algebraMap Fr hFr y
  have hmemR : ∀ y : ModGL Tag.E6 K, baseChangeGL ι y ∈ G₀ → baseChangeGL ι y ∈ R := by
    intro y hy
    rw [hR]
    exact ⟨hy, hFix y⟩
  have hlift : ∀ a : Fin Tag.E6.rank → Kˣ, baseChangeGL ι (rootDiagUnit Tag.E6 a) ∈ G₀ := by
    intro a
    rw [baseChangeGL_rootDiagUnit]
    exact (exceptional_Lang_adjoint_diagonal_lift Tag.E6 L _).1
  have hCG : ∀ c ∈ C, baseChangeGL ι c ∈ G₀ := fun c hc => baseChangeGL_mem_adjointGroup ι hc
  have hdec : ∀ z ∈ R, ∃ a : Fin Tag.E6.rank → Kˣ, ∃ c ∈ C,
      z = baseChangeGL ι (rootDiagUnit Tag.E6 a * c) := by
    intro z hz
    rw [hR] at hz
    obtain ⟨a, u, hu, rfl⟩ := exists_rootDiagUnit_mul_of_frobenius_fixed Tag.E6 Fr hFr hz.1 hz.2
    obtain ⟨c, hc, rfl⟩ := hu
    exact ⟨a, c, hc, by rw [map_mul]⟩
  have hentK : ∀ z ∈ R, ∃ y : ModGL Tag.E6 K, baseChangeGL ι y = z := by
    intro z hz
    obtain ⟨a, c, -, rfl⟩ := hdec z hz
    exact ⟨_, rfl⟩
  have hfinR : Finite R := by
    have : Finite (ModGL Tag.E6 K) := finite_modGL
    have hle : R ≤ (baseChangeGL (τ := Tag.E6) ι).range := by
      intro z hz
      obtain ⟨y, rfl⟩ := hentK z hz
      exact ⟨y, rfl⟩
    have : Finite (baseChangeGL (τ := Tag.E6) ι).range :=
      Finite.of_surjective _ (baseChangeGL (τ := Tag.E6) ι).rangeRestrict_surjective
    exact Finite.of_injective _ (Subgroup.inclusion_injective hle)
  have hRle : R ≤ G₀ ⊓ Subgroup.normalizer (H : Set (ModGL Tag.E6 L)) := by
    intro z hz
    refine ⟨?_, hRN hz⟩
    rw [hR] at hz
    exact hz.1
  let e : C ≃* H :=
    (C.equivMapOfInjective (baseChangeGL ι) hιinj).trans (MulEquiv.subgroupCongr hH.symm)
  have he : ∀ c : C, (e c : ModGL Tag.E6 L) = baseChangeGL ι c := fun _ => rfl
  let ρ : R →* MulAut C := (MulAut.congr e.symm).toMonoidHom.comp
    ((conjNormalizerHom G₀ H).comp (Subgroup.inclusion hRle))
  have hρ : ∀ (z : R) (h : C), baseChangeGL ι (ρ z h : ModGL Tag.E6 K) =
      (z : ModGL Tag.E6 L) * baseChangeGL ι (h : ModGL Tag.E6 K) * (z : ModGL Tag.E6 L)⁻¹ := by
    intro z h
    rw [← he, ← he]
    change ((e (e.symm (conjNormalizerHom G₀ H (Subgroup.inclusion hRle z) (e h)))) :
      ModGL Tag.E6 L) = _
    rw [MulEquiv.apply_symm_apply, conjNormalizerHom_apply]
    rfl
  have hρinj : Function.Injective ρ :=
    (MulAut.congr e.symm).injective.comp (hconjinj.comp (Subgroup.inclusion_injective hRle))
  have hρH : ∀ (c : C) (hz : baseChangeGL ι (c : ModGL Tag.E6 K) ∈ R),
      ρ ⟨_, hz⟩ = MulAut.conj c := by
    intro c hz
    refine MulEquiv.ext fun h => Subtype.ext (hιinj ?_)
    rw [hρ, MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, map_mul,
      map_mul, map_inv]
  have hρK : ∀ (y : ModGL Tag.E6 K) (hy : baseChangeGL ι y ∈ R) (h : C),
      (ρ ⟨_, hy⟩ h : ModGL Tag.E6 K) = y * (h : ModGL Tag.E6 K) * y⁻¹ := by
    intro y hy h
    apply hιinj
    rw [hρ, map_mul, map_mul, map_inv]
  have hρmap : (H.subgroupOf R).map ρ = inner C := by
    apply le_antisymm
    · rintro _ ⟨z, hzH, rfl⟩
      have hzH' : (z : ModGL Tag.E6 L) ∈ H := Subgroup.mem_subgroupOf.mp hzH
      rw [hH] at hzH'
      obtain ⟨c, hc, hcz⟩ := hzH'
      have hz : baseChangeGL ι ((⟨c, hc⟩ : C) : ModGL Tag.E6 K) ∈ R := hcz ▸ z.2
      have hzeq : z = ⟨_, hz⟩ := Subtype.ext hcz.symm
      rw [hzeq, hρH ⟨c, hc⟩ hz]
      exact ⟨⟨c, hc⟩, rfl⟩
    · rintro _ ⟨c, rfl⟩
      have hcH : baseChangeGL ι (c : ModGL Tag.E6 K) ∈ H := by
        rw [hH]
        exact ⟨c, c.2, rfl⟩
      exact ⟨⟨_, hHR hcH⟩, Subgroup.mem_subgroupOf.mpr hcH, hρH c (hHR hcH)⟩
  have hcancel : ∀ (β : K ≃+* K) (x : C),
      entrywiseAdjointAut Tag.E6 β (entrywiseAdjointAut Tag.E6 β⁻¹ x) = x := by
    intro β x
    rw [← MulAut.mul_apply, ← entrywiseAdjointAut_mul, mul_inv_cancel, entrywiseAdjointAut_one,
      MulAut.one_apply]
  have hinv : ∀ β : K ≃+* K,
      (entrywiseAdjointAut Tag.E6 β)⁻¹ = entrywiseAdjointAut Tag.E6 β⁻¹ :=
    fun β => (map_inv (entrywiseAdjointAutHom (τ := Tag.E6) (K := K)) β).symm
  have hfieldone : ∀ γ : K ≃+* K, entrywiseAdjointAut Tag.E6 γ = 1 → γ = 1 := by
    intro γ hγ
    refine RingEquiv.ext fun c => ?_
    have h1 := congrArg (fun η : MulAut C => η (adjX Tag.E6 K ⟨0, Tag.E6.rank_pos⟩ c)) hγ
    have h2 : entrywiseAdjointAut Tag.E6 γ (adjX Tag.E6 K ⟨0, Tag.E6.rank_pos⟩ c) =
        adjX Tag.E6 K ⟨0, Tag.E6.rank_pos⟩ (γ c) :=
      Subtype.ext (units_map_entrywiseHom_xUnit γ.toRingHom _ c)
    simp only [MulAut.one_apply] at h1
    rw [h2] at h1
    rw [RingAut.one_apply]
    exact adjX_injective _ h1
  have hγfix : ∀ (γ : K ≃+* K) (y : ModGL Tag.E6 (ZMod ℓ)),
      Units.map (entrywiseHom γ.toRingHom) (baseChangeGL c₀ y) = baseChangeGL c₀ y := by
    intro γ y
    rw [units_map_entrywiseHom_eq_baseChangeGL, baseChangeGL_baseChangeGL,
      RingHom.ext_zmod (γ.toRingHom.comp c₀) c₀]
  have hJ₀C : ∀ y ∈ adjointGroup Tag.E6 (ZMod ℓ), baseChangeGL c₀ y ∈ C :=
    fun y hy => baseChangeGL_mem_adjointGroup c₀ hy
  have hkey : ∀ (w : R) (ε : ℕ), ε < 2 → (∀ y (hy : y ∈ adjointGroup Tag.E6 (ZMod ℓ)),
      ρ w ⟨_, hJ₀C y hy⟩ = graphAut K ε ⟨_, hJ₀C y hy⟩) → ε = 0 ∧ w = 1 := by
    intro w ε hε hw
    have hwG : (w : ModGL Tag.E6 L) ∈ G₀ := (hRle w.2).1
    have hN1 := odd_E6_finite_root_inner_graph_pointwise_faithfulness (ZMod ℓ) hZodd L
      (ι.comp c₀) (w : ModGL Tag.E6 L)⁻¹ (inv_mem hwG) ε hε (by
        rintro _ ⟨y, hy, rfl⟩
        have h1 := congrArg (fun j : C => baseChangeGL ι (j : ModGL Tag.E6 K)) (hw y hy)
        simp only [hρ, coe_graphAut, map_mul, map_inv] at h1
        have hQ : baseChangeGL ι (exactQ Tag.E6 K ε) = diagramMap TwistTag.E6 L ^ ε := by
          change baseChangeGL ι (diagramMap TwistTag.E6 K ^ ε) = _
          rw [map_pow, baseChangeGL_diagramMap]
        rw [hQ] at h1
        rw [← baseChangeGL_baseChangeGL]
        exact conj_inv_conj_aux _ _ _ h1)
    exact ⟨hN1.1, Subtype.ext (inv_eq_one.1 hN1.2)⟩
  have hDF : ∀ (w : R) (x : Multiplicative (ZMod 2) × (K ≃+* K)),
      ρ w = graphFieldHom x → w = 1 ∧ x = 1 := by
    intro w x h
    obtain ⟨a, β⟩ := x
    have hx : graphFieldHom (a, β) =
        graphAut K (Multiplicative.toAdd a).val * entrywiseAdjointAut Tag.E6 β := rfl
    have hε : (Multiplicative.toAdd a).val < 2 := ZMod.val_lt _
    obtain ⟨hε0, hw1⟩ := hkey w (Multiplicative.toAdd a).val hε (fun y hy => by
      rw [h, hx, MulAut.mul_apply]
      exact congrArg _ (Subtype.ext (hγfix β y)))
    have ha : a = 1 := by
      have h0 : Multiplicative.toAdd a = 0 := (ZMod.val_eq_zero _).1 hε0
      exact Multiplicative.toAdd.injective h0
    subst ha
    subst hw1
    rw [map_one] at h
    have h3 : graphFieldHom (1, β) = entrywiseAdjointAut Tag.E6 β := by
      rw [show graphFieldHom (1, β) = graphAut K (Multiplicative.toAdd
        (1 : Multiplicative (ZMod 2))).val * entrywiseAdjointAut Tag.E6 β from rfl]
      simp [graphAut_zero]
    exact ⟨rfl, Prod.ext rfl (hfieldone β (h3.symm.trans h.symm))⟩
  have hexist : ∀ η : MulAut C, ∃ (z : R) (x : Multiplicative (ZMod 2) × (K ≃+* K)),
      η = ρ z * graphFieldHom x := by
    intro η
    obtain ⟨g, a, σ, ε, hη⟩ :=
      (ordinary_E_exact_automorphism_normal_form Tag.E6 (Or.inl rfl) K).2.2 η
    have hyR : baseChangeGL ι ((g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a) ∈ R :=
      hmemR _ (by rw [map_mul]; exact mul_mem (hCG g g.2) (hlift a))
    have hεlt : (ε : ℕ) < 2 := ε.2
    refine ⟨⟨_, hyR⟩, (Multiplicative.ofAdd ((ε : ℕ) : ZMod 2), σ),
      MulEquiv.ext fun h => Subtype.ext ?_⟩
    rw [MulAut.mul_apply, hρK, hη h]
    change _ = ((g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a) * ((graphAut K
      (((ε : ℕ) : ZMod 2)).val (entrywiseAdjointAut Tag.E6 σ h) : C) : ModGL Tag.E6 K) *
        ((g : ModGL Tag.E6 K) * rootDiagUnit Tag.E6 a)⁻¹
    rw [coe_graphAut, coe_entrywiseAdjointAut, ZMod.val_natCast_of_lt hεlt]
    simp only [mul_inv_rev, mul_assoc]
  have huniq : ∀ (z z' : R) (x x' : Multiplicative (ZMod 2) × (K ≃+* K)),
      ρ z * graphFieldHom x = ρ z' * graphFieldHom x' → z = z' ∧ x = x' := by
    intro z z' x x' h
    have h1 : ρ (z'⁻¹ * z) = graphFieldHom (x' * x⁻¹) := by
      have e : graphFieldHom (x⁻¹) = (graphFieldHom x)⁻¹ :=
        eq_inv_of_mul_eq_one_right (by
          rw [← map_mul]
          exact (congrArg (graphFieldHom (K := K)) (mul_inv_cancel x)).trans (map_one _))
      rw [map_mul ρ, map_inv ρ, map_mul (graphFieldHom (K := K)), e,
        inv_mul_eq_iff_eq_mul, ← mul_assoc, eq_mul_inv_iff_mul_eq, h]
    obtain ⟨h2, h3⟩ := hDF _ _ h1
    exact ⟨(inv_mul_eq_one.mp h2).symm, (mul_inv_eq_one.mp h3).symm⟩
  have hEU : ∀ η : MulAut C,
      ∃! p : R × (Multiplicative (ZMod 2) × (K ≃+* K)), η = ρ p.1 * graphFieldHom p.2 := by
    intro η
    obtain ⟨z, x, hzx⟩ := hexist η
    refine ⟨(z, x), hzx, fun p hp => ?_⟩
    obtain ⟨h1, h2⟩ := huniq _ _ _ _ (hp.symm.trans hzx)
    exact Prod.ext h1 h2
  have hψinj : Function.Injective (graphFieldHom (K := K)) :=
    (injective_iff_map_eq_one _).2 fun x hx => (hDF 1 x (by rw [map_one, hx])).2
  set RK : Subgroup (ModGL Tag.E6 K) := R.comap (baseChangeGL ι) with hRKdef
  have hmapRK : RK.map (baseChangeGL ι) = R :=
    Subgroup.map_comap_eq_self fun z hz => hentK z hz
  let eR : RK ≃* R :=
    (RK.equivMapOfInjective (baseChangeGL ι) hιinj).trans (MulEquiv.subgroupCongr hmapRK)
  have heR : ∀ y : RK, (eR y : ModGL Tag.E6 L) = baseChangeGL ι y := fun _ => rfl
  have hβRK : ∀ (β : K ≃+* K) (y : ModGL Tag.E6 K), y ∈ RK →
      Units.map (entrywiseHom β.toRingHom) y ∈ RK := by
    intro β y hy
    obtain ⟨a, c, hc, hac⟩ := hdec _ hy
    have hyac : y = rootDiagUnit Tag.E6 a * c := hιinj hac
    subst hyac
    show baseChangeGL ι _ ∈ R
    apply hmemR
    have h1 : Units.map (entrywiseHom β.toRingHom) (rootDiagUnit Tag.E6 a) =
        rootDiagUnit Tag.E6 (fun i => Units.map β.toRingHom.toMonoidHom (a i)) :=
      Units.ext (entrywise_rootDiag β.toRingHom a)
    rw [map_mul, map_mul, h1]
    exact mul_mem (hlift _) (hCG _ (entrywiseAdjointAut Tag.E6 β ⟨c, hc⟩).2)
  have hmapβ : ∀ β : K ≃+* K, RK.map (exactEntrywiseAut Tag.E6 β).toMonoidHom = RK := by
    intro β
    apply le_antisymm
    · rintro _ ⟨y, hy, rfl⟩
      exact hβRK β y hy
    · intro y hy
      exact ⟨Units.map (entrywiseHom β.symm.toRingHom) y, hβRK β.symm y hy,
        exactEntrywiseAut_right_inv β y⟩
  let βR : (K ≃+* K) → MulAut R := fun β =>
    (eR.symm.trans (mulAutRestrict RK (exactEntrywiseAut Tag.E6 β) (hmapβ β))).trans eR
  have hβR : ∀ (β : K ≃+* K) (z : R) (y : ModGL Tag.E6 K), baseChangeGL ι y = z →
      ((βR β z : R) : ModGL Tag.E6 L) =
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
    change (eR (mulAutRestrict RK (exactEntrywiseAut Tag.E6 β) (hmapβ β) (eR.symm z)) :
      ModGL Tag.E6 L) = _
    rw [h1, heR, coe_mulAutRestrict]
    rfl
  have hconjβ : ∀ (β : K ≃+* K) (z : R), entrywiseAdjointAut Tag.E6 β * ρ z *
      (entrywiseAdjointAut Tag.E6 β)⁻¹ = ρ (βR β z) := by
    intro β z
    obtain ⟨y, hyz⟩ := hentK z z.2
    refine MulEquiv.ext fun h => Subtype.ext (hιinj ?_)
    rw [hρ, hβR β z y hyz, hinv, MulAut.mul_apply, MulAut.mul_apply]
    set h' := entrywiseAdjointAut Tag.E6 β⁻¹ h with hh'
    have hρh' : (ρ z h' : ModGL Tag.E6 K) = y * h' * y⁻¹ := by
      apply hιinj
      rw [hρ, ← hyz, map_mul, map_mul, map_inv]
    have hβh' : Units.map (entrywiseHom β.toRingHom) (h' : ModGL Tag.E6 K) = h := by
      rw [← coe_entrywiseAdjointAut, hh', hcancel]
    rw [coe_entrywiseAdjointAut, hρh']
    simp only [map_mul, map_inv, hβh']
  have hPP : diagramE6 L * diagramE6 L = 1 := diagramE6_mul_self
  have hPinv : (diagramE6 L)⁻¹ = diagramE6 L := inv_eq_of_mul_eq_one_right hPP
  have hPfix : Units.map (entrywiseHom Fr) (diagramE6 L) = diagramE6 L :=
    units_map_entrywiseHom_diagramE6 Fr
  have hγRle : ∀ z ∈ R, diagramE6 L * z * (diagramE6 L)⁻¹ ∈ R := by
    intro z hz
    rw [hR] at hz ⊢
    refine ⟨?_, ?_⟩
    · have h1 := map_conj_diagramMap TwistTag.E6 L (H := adjointGroup Tag.E6 L) (Or.inl rfl)
      have h2 : diagramE6 L * z * (diagramE6 L)⁻¹ ∈
          (adjointGroup Tag.E6 L).map (MulAut.conj (diagramMap TwistTag.E6 L)).toMonoidHom :=
        ⟨z, hz.1, rfl⟩
      exact h1.le h2
    · have h3 : Units.map (entrywiseHom Fr) z = z := hz.2
      show Units.map (entrywiseHom Fr) (diagramE6 L * z * (diagramE6 L)⁻¹) =
        diagramE6 L * z * (diagramE6 L)⁻¹
      rw [map_mul, map_mul, map_inv, hPfix, h3]
  have hmapγ : R.map (MulAut.conj (diagramE6 L)).toMonoidHom = R := by
    apply le_antisymm
    · rintro _ ⟨z, hz, rfl⟩
      exact hγRle z hz
    · intro y hy
      refine ⟨diagramE6 L * y * (diagramE6 L)⁻¹, hγRle y hy, ?_⟩
      change diagramE6 L * (diagramE6 L * y * (diagramE6 L)⁻¹) * (diagramE6 L)⁻¹ = y
      rw [hPinv]
      calc diagramE6 L * (diagramE6 L * y * diagramE6 L) * diagramE6 L =
          (diagramE6 L * diagramE6 L) * y * (diagramE6 L * diagramE6 L) := by simp only [mul_assoc]
        _ = y := by rw [hPP, one_mul, mul_one]
  let γR : MulAut R := mulAutRestrict R (MulAut.conj (diagramE6 L)) hmapγ
  have hγR : ∀ z : R, ((γR z : R) : ModGL Tag.E6 L) =
      diagramE6 L * (z : ModGL Tag.E6 L) * (diagramE6 L)⁻¹ := fun z => rfl
  have hgraph1 : graphAut K 1 * graphAut K 1 = 1 := by
    rw [← graphAut_add, show 1 + 1 = 2 from rfl, graphAut_two]
  have hgraphinv : (graphAut K 1)⁻¹ = graphAut K 1 := inv_eq_of_mul_eq_one_right hgraph1
  have hQ : baseChangeGL ι (exactQ Tag.E6 K 1) = diagramE6 L := by
    rw [exactQ_E6, pow_one, baseChangeGL_diagramE6]
  have hconjγ : ∀ z : R, graphAut K 1 * ρ z * (graphAut K 1)⁻¹ = ρ (γR z) := by
    intro z
    refine MulEquiv.ext fun h => Subtype.ext (hιinj ?_)
    rw [hgraphinv, MulAut.mul_apply, MulAut.mul_apply]
    simp only [coe_graphAut, hρ, map_mul, map_inv, hQ, hγR]
    exact conj_graph_aux _ _ _ hPP
  have hβγ : ∀ (β : K ≃+* K) (z : R), βR β (γR z) = γR (βR β z) := by
    intro β z
    obtain ⟨y, hyz⟩ := hentK z z.2
    have hy' : baseChangeGL ι (diagramE6 K * y * (diagramE6 K)⁻¹) = (γR z : ModGL Tag.E6 L) := by
      rw [hγR, ← hyz, map_mul, map_mul, map_inv, baseChangeGL_diagramE6]
    apply Subtype.ext
    rw [hβR β (γR z) _ hy', hγR, hβR β z y hyz]
    simp only [map_mul, map_inv, units_map_entrywiseHom_diagramE6, baseChangeGL_diagramE6]
  have hγn : ∀ (n : ℕ) (z : R), graphAut K n * ρ z * (graphAut K n)⁻¹ = ρ ((γR ^ n) z) := by
    intro n z
    induction n generalizing z with
    | zero =>
      rw [graphAut_zero, pow_zero]
      simp
    | succ n ih =>
      rw [graphAut_add, pow_succ, MulAut.mul_apply]
      have e : graphAut K n * graphAut K 1 * ρ z * (graphAut K n * graphAut K 1)⁻¹ =
          graphAut K n * (graphAut K 1 * ρ z * (graphAut K 1)⁻¹) * (graphAut K n)⁻¹ := by group
      rw [e, hconjγ, ih]
  let actR : Multiplicative (ZMod 2) × (K ≃+* K) → MulAut R := fun x =>
    γR ^ (Multiplicative.toAdd x.1).val * βR x.2
  have hact : ∀ (x : Multiplicative (ZMod 2) × (K ≃+* K)) (z : R),
      graphFieldHom x * ρ z * (graphFieldHom x)⁻¹ = ρ (actR x z) := by
    intro x z
    obtain ⟨a, β⟩ := x
    have hx : graphFieldHom (a, β) =
        graphAut K (Multiplicative.toAdd a).val * entrywiseAdjointAut Tag.E6 β := rfl
    show graphFieldHom (a, β) * ρ z * (graphFieldHom (a, β))⁻¹ =
      ρ ((γR ^ (Multiplicative.toAdd a).val * βR β) z)
    rw [hx, MulAut.mul_apply]
    have e : graphAut K (Multiplicative.toAdd a).val * entrywiseAdjointAut Tag.E6 β * ρ z *
        (graphAut K (Multiplicative.toAdd a).val * entrywiseAdjointAut Tag.E6 β)⁻¹ =
        graphAut K (Multiplicative.toAdd a).val * (entrywiseAdjointAut Tag.E6 β * ρ z *
          (entrywiseAdjointAut Tag.E6 β)⁻¹) * (graphAut K (Multiplicative.toAdd a).val)⁻¹ := by
      group
    rw [e, hconjβ, hγn]
  choose z₀ x₀ hzx using hexist
  have hPeq : ∀ (z : R) (x : Multiplicative (ZMod 2) × (K ≃+* K)),
      z₀ (ρ z * graphFieldHom x) = z ∧ x₀ (ρ z * graphFieldHom x) = x := fun z x =>
    huniq _ _ _ _ (hzx _).symm
  have hone : (1 : MulAut C) = ρ 1 * graphFieldHom 1 := by rw [map_one, map_one, one_mul]
  let π : MulAut C →* Multiplicative (ZMod 2) × (K ≃+* K) :=
    { toFun := x₀
      map_one' := by
        show x₀ 1 = 1
        have h1 := (hPeq 1 1).2
        rwa [← hone] at h1
      map_mul' := fun η₁ η₂ => by
        show x₀ (η₁ * η₂) = x₀ η₁ * x₀ η₂
        have e : η₁ * η₂ = ρ (z₀ η₁ * actR (x₀ η₁) (z₀ η₂)) *
            graphFieldHom (x₀ η₁ * x₀ η₂) := by
          conv_lhs => rw [hzx η₁, hzx η₂]
          rw [map_mul ρ, ← hact, map_mul (graphFieldHom (K := K))]
          group
        rw [e]
        exact (hPeq _ _).2 }
  have hπ : ∀ (z : R) (x : Multiplicative (ZMod 2) × (K ≃+* K)),
      π (ρ z * graphFieldHom x) = x := fun z x => (hPeq z x).2
  have hπsurj : Function.Surjective π := fun x => ⟨ρ 1 * graphFieldHom x, hπ 1 x⟩
  have hπker : π.ker = ρ.range := by
    ext η
    rw [MonoidHom.mem_ker, MonoidHom.mem_range]
    constructor
    · intro h1
      refine ⟨z₀ η, ?_⟩
      have h2 := hzx η
      rw [show x₀ η = 1 from h1, map_one, mul_one] at h2
      exact h2.symm
    · rintro ⟨z, rfl⟩
      have h3 : ρ z = ρ z * graphFieldHom 1 := by rw [map_one, mul_one]
      rw [h3, hπ]
  have hD : ρ.range.Normal := hπker ▸ π.normal_ker
  have hidx : ((inner C).subgroupOf ρ.range).index ∣ 3 := by
    have hle : inner C ≤ ρ.range := hρmap ▸ Subgroup.map_le_range _ _
    have h1 : (inner C).relIndex ρ.range * ρ.range.index = (inner C).index :=
      Subgroup.relIndex_mul_index hle
    obtain ⟨hn, -⟩ := CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic hℓ K hK
    have h2 : ρ.range.index = 2 * f := by
      rw [← hπker, Subgroup.index_ker, MonoidHom.range_eq_top.2 hπsurj, Subgroup.card_top,
        Nat.card_prod, Nat.card_congr Multiplicative.toAdd, Nat.card_zmod, hn]
    have hout := (ordinary_E_outer_order_Cartan_divisor Tag.E6 (Or.inl rfl) hℓ _hf K hK 3 2
      (Or.inl ⟨rfl, rfl, rfl⟩)).1
    have h3 : (inner C).index = Nat.card (Outer C) := Subgroup.index_eq_card _
    rw [h3] at h1
    rw [← h1, h2] at hout
    have hf0 : 0 < 2 * f := by omega
    have h4 : (inner C).relIndex ρ.range * (2 * f) ∣ 3 * (2 * f) := by
      have e : 3 * (2 * f) = 3 * 2 * f := by ring
      rw [e]
      exact hout
    exact Nat.dvd_of_mul_dvd_mul_right hf0 h4
  refine ⟨hfinR, hHR, hRN, hentK, ρ, hρ, hρinj, hρmap, hD, hidx, ?_, ?_, hψinj, hEU,
    ⟨π, hπsurj, hπker, hπ⟩, ⟨βR, γR, hβR, hconjβ, hγR, hconjγ, hβγ⟩, ?_⟩
  · rw [pow_two]
    exact hgraph1
  · intro β
    exact graphAut_comm_entrywise 1 β
  intro k S hS
  have : CharP k ℓ := RingHom.charP k.subtype k.subtype_injective ℓ
  obtain ⟨c₀k, hc₀kdef⟩ : ∃ c₀k : ZMod ℓ →+* k, c₀k = ZMod.castHom (dvd_refl ℓ) k := ⟨_, rfl⟩
  have hc₀k : k.subtype.comp c₀k = c₀ := RingHom.ext_zmod _ _
  set Jk : Set C := {j | (j : ModGL Tag.E6 K) ∈ (adjointGroup Tag.E6 k).map
    (baseChangeGL k.subtype)} with hJkdef
  have hJ₀k : ∀ y (hy : y ∈ adjointGroup Tag.E6 (ZMod ℓ)), (⟨_, hJ₀C y hy⟩ : C) ∈ Jk := by
    intro y hy
    refine ⟨baseChangeGL c₀k y, baseChangeGL_mem_adjointGroup c₀k hy, ?_⟩
    show baseChangeGL k.subtype (baseChangeGL c₀k y) = baseChangeGL c₀ y
    rw [baseChangeGL_baseChangeGL, hc₀k]
  have hfixJ : ∀ σ : K ≃ₐ[k] K, ∀ j ∈ Jk, entrywiseAdjointAut Tag.E6 σ.toRingEquiv j = j := by
    rintro σ j ⟨y, -, hyj⟩
    apply Subtype.ext
    rw [coe_entrywiseAdjointAut, ← hyj, units_map_entrywiseHom_eq_baseChangeGL,
      baseChangeGL_baseChangeGL]
    rw [show σ.toRingEquiv.toRingHom.comp k.subtype = k.subtype from
      RingHom.ext fun x => σ.commutes x]
  have hSset : (S : Set (MulAut C)) =
      Set.range (fun σ : K ≃ₐ[k] K => entrywiseAdjointAut Tag.E6 σ.toRingEquiv) := by
    rw [hS]
    ext η
    rw [SetLike.mem_coe, mem_fixingSubgroup_iff, Set.mem_range]
    constructor
    · intro hη
      obtain ⟨z, ⟨a, γ⟩, hηeq⟩ : ∃ (z : R) (x : Multiplicative (ZMod 2) × (K ≃+* K)),
          η = ρ z * graphFieldHom x := ⟨z₀ η, x₀ η, hzx η⟩
      subst hηeq
      have hx : graphFieldHom (a, γ) =
          graphAut K (Multiplicative.toAdd a).val * entrywiseAdjointAut Tag.E6 γ := rfl
      have hε : (Multiplicative.toAdd a).val < 2 := ZMod.val_lt _
      obtain ⟨hε0, hz1⟩ := hkey z⁻¹ (Multiplicative.toAdd a).val hε (fun y hy => by
        have h1 : (ρ z * graphFieldHom (a, γ)) ⟨_, hJ₀C y hy⟩ = ⟨_, hJ₀C y hy⟩ :=
          hη _ (hJ₀k y hy)
        rw [hx, MulAut.mul_apply, MulAut.mul_apply, show entrywiseAdjointAut Tag.E6 γ
          ⟨_, hJ₀C y hy⟩ = ⟨_, hJ₀C y hy⟩ from Subtype.ext (hγfix γ y)] at h1
        rw [map_inv]
        calc (ρ z)⁻¹ ⟨_, hJ₀C y hy⟩ =
            (ρ z)⁻¹ (ρ z (graphAut K (Multiplicative.toAdd a).val ⟨_, hJ₀C y hy⟩)) := by
              rw [h1]
          _ = graphAut K (Multiplicative.toAdd a).val ⟨_, hJ₀C y hy⟩ := MulAut.inv_apply_self _ _ _)
      have hz : z = 1 := inv_eq_one.1 hz1
      have ha : a = 1 := Multiplicative.toAdd.injective ((ZMod.val_eq_zero _).1 hε0)
      subst hz
      subst ha
      have h3 : (ρ 1 * graphFieldHom (1, γ) : MulAut C) = entrywiseAdjointAut Tag.E6 γ := by
        rw [map_one, one_mul, show graphFieldHom (1, γ) = graphAut K (Multiplicative.toAdd
          (1 : Multiplicative (ZMod 2))).val * entrywiseAdjointAut Tag.E6 γ from rfl]
        simp [graphAut_zero]
      rw [h3] at hη ⊢
      have hγk : ∀ x : k, γ (x : K) = x := by
        intro x
        have hxJ : adjX Tag.E6 K ⟨0, Tag.E6.rank_pos⟩ (x : K) ∈ Jk :=
          ⟨xUnit Tag.E6 k ⟨0, Tag.E6.rank_pos⟩ x, xUnit_mem_adjointGroup _ _,
            baseChangeGL_xUnit k.subtype _ x⟩
        have h1 : entrywiseAdjointAut Tag.E6 γ (adjX Tag.E6 K ⟨0, Tag.E6.rank_pos⟩ (x : K)) =
            adjX Tag.E6 K ⟨0, Tag.E6.rank_pos⟩ (x : K) := hη _ hxJ
        have h2 : entrywiseAdjointAut Tag.E6 γ (adjX Tag.E6 K ⟨0, Tag.E6.rank_pos⟩ (x : K)) =
            adjX Tag.E6 K ⟨0, Tag.E6.rank_pos⟩ (γ x) :=
          Subtype.ext (units_map_entrywiseHom_xUnit γ.toRingHom _ _)
        rw [h2] at h1
        exact adjX_injective _ h1
      exact ⟨AlgEquiv.ofRingEquiv (f := γ) fun x => hγk x, rfl⟩
    · rintro ⟨σ, rfl⟩ j hj
      exact hfixJ σ j hj
  let φ : (K ≃ₐ[k] K) →* MulAut C :=
    { toFun := fun σ => entrywiseAdjointAut Tag.E6 σ.toRingEquiv
      map_one' := entrywiseAdjointAut_one
      map_mul' := fun σ τ => entrywiseAdjointAut_mul σ.toRingEquiv τ.toRingEquiv }
  have hEinj : Function.Injective (entrywiseAdjointAutHom (τ := Tag.E6) (K := K)) :=
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

end CFSG.RankThree.PartOne.KE

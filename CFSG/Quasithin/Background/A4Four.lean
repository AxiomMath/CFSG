module

public import CFSG.Quasithin.Background.A4FourQuot
public import CFSG.Quasithin.Background.A4Local
public import CFSG.Quasithin.Background.B6Sections
public import CFSG.Quasithin.Background.A1aFStar

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.A4

variable {G : Type*} [Group G]

abbrev OTwoQuot (H : Subgroup G) : Type _ := ↥H ⧸ CFSG.Open.pCore 2 ↥H

@[expose] def imageOTwoQuot (H X : Subgroup G) : Subgroup (OTwoQuot H) :=
  (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H))

@[expose] def A44Hyp (H X : Subgroup G) : Prop :=
  IsTheta (OTwoQuot H) (imageOTwoQuot H X) ∨
    (IsSubnormal (imageOTwoQuot H X) (CFSG.generalizedFitting (OTwoQuot H)) ∧
      ∀ x ∈ Subgroup.centralizer (imageOTwoQuot H X : Set (OTwoQuot H)) ⊓
          CFSG.generalizedFitting (OTwoQuot H), (orderOf x).Prime → x ∈ imageOTwoQuot H X)

section Finite

variable [Finite G]

theorem pCore_two_quot_eq_bot (H : Subgroup G) : CFSG.pCore 2 (OTwoQuot H) = ⊥ := by
  rw [eq_bot_iff]
  set N := CFSG.Open.pCore 2 ↥H with hN
  set π := QuotientGroup.mk' N with hπ
  set M := CFSG.Open.pCore 2 (↥H ⧸ N) with hM
  have hMp : IsPGroup 2 M := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hMn : M.Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hNp : IsPGroup 2 N := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hcomp : IsPGroup 2 (M.comap π) := by
    intro y
    obtain ⟨k, hk⟩ := hMp ⟨π y, y.2⟩
    have h0 : (π (y : ↥H)) ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    have h1 : π ((y : ↥H) ^ 2 ^ k) = 1 := by rw [map_pow]; exact h0
    have hmem : (y : ↥H) ^ 2 ^ k ∈ N := by
      have hker : π.ker = N := QuotientGroup.ker_mk' N
      exact hker.le (MonoidHom.mem_ker.mpr h1)
    obtain ⟨j, hj⟩ := hNp ⟨(y : ↥H) ^ 2 ^ k, hmem⟩
    refine ⟨k + j, ?_⟩
    apply Subtype.ext
    have := congrArg Subtype.val hj
    simpa [pow_add, pow_mul] using this
  have hle : M.comap π ≤ N := CFSG.LieType.BorelTits.le_pCore 2 (hMn.comap π) hcomp
  intro m hm
  obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective m
  have hy : y ∈ N := hle hm
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff y).mpr hy

omit [Finite G] in
theorem A44Hyp.toAbstract {H X : Subgroup G} (h : A44Hyp H X) :
    IsTheta (OTwoQuot H) (imageOTwoQuot H X) ∨
      (IsSubnormal (imageOTwoQuot H X) (CFSG.generalizedFitting (OTwoQuot H)) ∧
        lambdaSubgroup (Subgroup.centralizer (imageOTwoQuot H X : Set (OTwoQuot H)) ⊓
          CFSG.generalizedFitting (OTwoQuot H)) ≤ imageOTwoQuot H X) := by
  rcases h with h | ⟨h1, h2⟩
  · exact Or.inl h
  · exact Or.inr ⟨h1, lambdaSubgroup_le_iff.mpr fun x hx hp => h2 x hx hp⟩

omit [Finite G] in
theorem imageOTwoQuot_comap {H X : Subgroup G} (hOX : pCoreOf 2 H ≤ X) :
    (imageOTwoQuot H X).comap (QuotientGroup.mk' (CFSG.Open.pCore 2 ↥H)) = X.subgroupOf H := by
  unfold imageOTwoQuot
  rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk']
  apply sup_eq_left.mpr
  intro n hn
  rw [Subgroup.mem_subgroupOf]
  exact hOX ⟨n, hn, rfl⟩

theorem a4_4_1 {H K X : Subgroup G} (hOX : pCoreOf 2 H ≤ X) (hXHK : X ≤ H ⊓ K)
    (h : A44Hyp H X) : pCoreOf 2 (H ⊓ K) = pCoreOf 2 H := by
  have hXH : X ≤ H := hXHK.trans inf_le_left
  obtain ⟨hsub, hO2X, hfaithQ⟩ := a44_abstract (pCore_two_quot_eq_bot H) h.toAbstract
  set N := CFSG.Open.pCore 2 ↥H with hN
  set π := QuotientGroup.mk' N with hπ
  have hcomap : (imageOTwoQuot H X).comap π = X.subgroupOf H := imageOTwoQuot_comap hOX
  have hPN : ∀ y : ↥H, (y : G) ∈ pCoreOf 2 H → y ∈ N := by
    rintro y ⟨n, hn, hny⟩
    have : n = y := Subtype.ext hny
    rwa [← this]
  have hXHsub : IsSubnormal X H := by
    have h1 := A4.subnormal_comap π hsub
    rw [hcomap, Subgroup.comap_top] at h1
    exact (isSubnormal_subgroupOf_top_iff hXH).mp h1
  have hX : X = oTwoUpper X ⊔ pCoreOf 2 H := by
    refine le_antisymm ?_ (sup_le (oTwoUpper_le X) hOX)
    set X₁ := X.subgroupOf H with hX₁
    have hmap : (oTwoUpper X₁).map π = X₁.map π := by
      rw [← oTwoUpper_map π X₁]; exact hO2X
    have h1 : X₁ ≤ oTwoUpper X₁ ⊔ π.ker := by
      have := Subgroup.le_comap_map π X₁
      rw [← hmap, Subgroup.comap_map_eq] at this
      exact this
    have hXmap : X₁.map H.subtype = X := Subgroup.map_subgroupOf_eq_of_le hXH
    have hOmap : (oTwoUpper X₁).map H.subtype = oTwoUpper X := by
      rw [← oTwoUpper_map H.subtype X₁, hXmap]
    have hker : (π.ker).map H.subtype = pCoreOf 2 H := by
      rw [hπ, QuotientGroup.ker_mk']; rfl
    calc X = X₁.map H.subtype := hXmap.symm
      _ ≤ (oTwoUpper X₁ ⊔ π.ker).map H.subtype := Subgroup.map_mono h1
      _ = oTwoUpper X ⊔ pCoreOf 2 H := by rw [Subgroup.map_sup, hOmap, hker]
  have hfaith : IsSylowTwoOf (pCoreOf 2 H) (centralizerSection H X (pCoreOf 2 H)) := by
    have hPnorm := le_normalizer_pCoreOf 2 H
    have hPC : pCoreOf 2 H ≤ centralizerSection H X (pCoreOf 2 H) := by
      rw [le_centralizerSection_iff hOX]
      refine ⟨pCoreOf_le 2 H, (Subgroup.commutator_le).mpr fun x hx p hp => ?_⟩
      have h1 := (Subgroup.mem_normalizer_iff.mp (hPnorm (hXH hx)) p).mp hp
      exact (pCoreOf 2 H).mul_mem h1 ((pCoreOf 2 H).inv_mem hp)
    refine isSylowTwoOf_iff_maximal.mpr ⟨hPC, pCoreOf_isPGroup 2 H, fun R hRC hR2 hPR => ?_⟩
    obtain ⟨hRH, hXR⟩ := (le_centralizerSection_iff hOX).mp hRC
    set R₁ := R.subgroupOf H with hR₁
    have hR₁2 : IsPGroup 2 R₁ := isPGroup_subgroupOf_of_le hRH hR2
    have hRbar2 : IsPGroup 2 (R₁.map π) := hR₁2.map π
    have hcent : R₁.map π ≤ Subgroup.centralizer (imageOTwoQuot H X : Set (OTwoQuot H)) := by
      rintro _ ⟨r, hr, rfl⟩
      rw [Subgroup.mem_centralizer_iff]
      rintro _ ⟨x, hx, rfl⟩
      have hc : ((x * r * x⁻¹ * r⁻¹ : ↥H) : G) ∈ pCoreOf 2 H := by
        apply hXR
        have := Subgroup.commutator_mem_commutator (H₁ := X) (H₂ := R) hx hr
        simpa [commutatorElement_def] using this
      have hcN : x * r * x⁻¹ * r⁻¹ ∈ N := hPN _ hc
      have h1 : π (x * r * x⁻¹ * r⁻¹) = 1 := (QuotientGroup.eq_one_iff _).mpr hcN
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
      have h2 : π x * π r * (π x)⁻¹ = π r := mul_inv_eq_one.mp h1
      calc π x * π r = π x * π r * (π x)⁻¹ * π x := by group
        _ = π r * π x := by rw [h2]
    have hbot := hfaithQ _ hRbar2 (hcent.trans (Subgroup.centralizer_le_normalizer _))
    rw [inf_eq_left.mpr hcent] at hbot
    intro r hr
    have h1 : π ⟨r, hRH hr⟩ ∈ R₁.map π := ⟨⟨r, hRH hr⟩, hr, rfl⟩
    rw [hbot, Subgroup.mem_bot] at h1
    have h2 : (⟨r, hRH hr⟩ : ↥H) ∈ N := (QuotientGroup.eq_one_iff _).mp h1
    exact ⟨⟨r, hRH hr⟩, h2, rfl⟩
  exact a4_4_1_of_faithful hOX hXHK hX hXHsub hfaith

theorem a4_4_2 {H K X : Subgroup G} (hOX : pCoreOf 2 H ≤ X) (hXHK : X ≤ H ⊓ K)
    (h : A44Hyp H X) (hH : quasithinIsMaxTwoLocal H) : CKQ K (pCoreOf 2 (H ⊓ K)) ≤ H ⊓ K :=
  a4_4_2_of_pCoreOf_eq hH (a4_4_1 hOX hXHK h)

omit [Finite G] in
theorem imageOTwoQuot_O2Fstar (K : Subgroup G) :
    imageOTwoQuot K ((O2Fstar ↥K).map K.subtype) =
      CFSG.generalizedFitting (OTwoQuot K) := by
  unfold imageOTwoQuot O2Fstar
  rw [A4.subgroupOf_map_subtype']
  exact Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _

theorem a4_4_3 {H K X : Subgroup G} (hOX : pCoreOf 2 H ≤ X) (hXHK : X ≤ H ⊓ K)
    (h : A44Hyp H X) (hH : quasithinIsMaxTwoLocal H) (hK : quasithinIsMaxTwoLocal K)
    (hFK : (O2Fstar ↥K).map K.subtype ≤ H) : H = K := by
  set X' : Subgroup G := (O2Fstar ↥K).map K.subtype with hX'
  have hX'K : X' ≤ K := Subgroup.map_subtype_le _
  have hOX' : pCoreOf 2 K ≤ X' := by
    rintro _ ⟨n, hn, rfl⟩
    refine ⟨n, ?_, rfl⟩
    show QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) n ∈ CFSG.generalizedFitting (OTwoQuot K)
    have : QuotientGroup.mk' (CFSG.Open.pCore 2 ↥K) n = 1 :=
      (QuotientGroup.eq_one_iff n).mpr hn
    rw [this]
    exact Subgroup.one_mem _
  have hh' : A44Hyp K X' := by
    right
    rw [imageOTwoQuot_O2Fstar]
    exact ⟨IsSubnormal.refl _, fun x hx _ => hx.2⟩
  have h1 := a4_4_1 hOX' (le_inf hX'K hFK) hh'
  have h2 := a4_4_1 hOX hXHK h
  rw [inf_comm] at h1
  exact a4_4_3_of_pCoreOf_eq hH hK (h1.symm.trans h2)

end Finite

end CFSG.Quasithin

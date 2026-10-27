module

public import CFSG.Quasithin.H13.NQBlockOriginalSupplements

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.ABGLocalTools (IsSylowOf)

section OTwo

variable {G : Type} [Group G] [Finite G]

theorem le_of_perfect_of_pow_mem {K O : Subgroup G} (hK : ⁅K, K⁆ = K) (hOK : O ≤ K)
    (hOn : (O.subgroupOf K).Normal) (h2 : ∀ x ∈ K, ∃ k : ℕ, x ^ 2 ^ k ∈ O) : K ≤ O := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hp : IsPGroup 2 (↥K ⧸ O.subgroupOf K) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ q
    obtain ⟨k, hk⟩ := h2 x x.2
    refine ⟨k, ?_⟩
    rw [← map_pow, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, mem_subgroupOf]
    simpa using hk
  have : Group.IsNilpotent (↥K ⧸ O.subgroupOf K) := hp.isNilpotent
  obtain ⟨n, hn⟩ := (Group.isSolvable_def _).mp
    (inferInstance : Group.IsSolvable (↥K ⧸ O.subgroupOf K))
  have h1 : (derivedSeries (↥K) n).map (QuotientGroup.mk' (O.subgroupOf K)) = ⊥ := by
    rw [map_derivedSeries_eq (QuotientGroup.mk'_surjective _) n, hn]
  have h3 : derivedSeries (↥K) n ≤ O.subgroupOf K := by
    rw [← QuotientGroup.ker_mk' (O.subgroupOf K), ← Subgroup.map_eq_bot_iff]
    exact h1
  have h4 := Subgroup.map_mono (f := K.subtype) h3
  rw [← derivedSeriesOf_eq_map_derivedSeries, Subgroup.map_subgroupOf_eq_of_le hOK] at h4
  calc K = perfectCore K := (perfectCore_eq_self_of_perfect hK).symm
    _ ≤ derivedSeriesOf K n := perfectCore_le_derivedSeriesOf K n
    _ ≤ O := h4

theorem oTwoUpper_sup_eq_of_perfect {K T : Subgroup G} (hK : ⁅K, K⁆ = K) (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) : oTwoUpper (K ⊔ T) = K := by
  have hKn : (K.subgroupOf (K ⊔ T)).Normal :=
    (normal_subgroupOf_iff_le_normalizer le_sup_left).mpr (sup_le le_normalizer hTK)
  refine le_antisymm (oTwoUpper_le_of_pow_mem fun x hx => ?_) ?_
  · have hx' : x ∈ ((K ⊔ T : Subgroup G) : Set G) := hx
    rw [coe_mul_of_right_le_normalizer_left K T hTK] at hx'
    obtain ⟨k, hk, t, ht, rfl⟩ := hx'
    obtain ⟨n, hn⟩ := hT ⟨t, ht⟩
    refine ⟨n, ?_⟩
    have hkB : k ∈ K ⊔ T := mem_sup_left hk
    have htB : t ∈ K ⊔ T := mem_sup_right ht
    have e1 : (⟨k * t, hx⟩ : ↥(K ⊔ T)) = ⟨k, hkB⟩ * ⟨t, htB⟩ := rfl
    have e2 : QuotientGroup.mk' (K.subgroupOf (K ⊔ T)) ⟨k, hkB⟩ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (mem_subgroupOf.mpr hk)
    have e3 : (⟨t, htB⟩ : ↥(K ⊔ T)) ^ 2 ^ n = 1 := Subtype.ext (by
      have := congrArg Subtype.val hn
      simpa using this)
    have hq : QuotientGroup.mk' (K.subgroupOf (K ⊔ T)) ((⟨k * t, hx⟩ : ↥(K ⊔ T)) ^ 2 ^ n) = 1 := by
      rw [map_pow, e1, map_mul, e2, one_mul, ← map_pow, e3, map_one]
    have hmem := (QuotientGroup.eq_one_iff _).mp hq
    rw [mem_subgroupOf] at hmem
    simpa using hmem
  · refine le_trans ?_ (oTwoUpper_mono le_sup_left)
    exact le_of_perfect_of_pow_mem hK (oTwoUpper_le K)
      ((normal_subgroupOf_iff_le_normalizer (oTwoUpper_le K)).mpr (le_normalizer_oTwoUpper K))
      fun x hx => exists_pow_mem_oTwoUpper K hx

end OTwo

section Sylow

variable {G : Type} [Group G] [Finite G] {T L M : Subgroup G}

omit [Finite G] in
theorem mem_normalizer_inf {A B : Subgroup G} {x : G} (hA : x ∈ normalizer (A : Set G))
    (hB : x ∈ normalizer (B : Set G)) : x ∈ normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  rw [mem_normalizer_iff] at hA hB ⊢
  intro y
  rw [mem_inf, mem_inf, hA y, hB y]

theorem mem_radical_of_central (h : QTNQ T L M) {b : ↥L}
    (hb : ∀ x : ↥L, x⁻¹ * (b * x * b⁻¹) ∈ CFSG.solvableRadical ↥L) :
    b ∈ CFSG.solvableRadical ↥L := by
  obtain ⟨hsimp, a, c, hac⟩ := NQBlock.simple_radical_quotient_of_isCComponent_top
    (NQSetup.isCComponent_top_of_qtnq h)
  have hcen : center (↥L ⧸ CFSG.solvableRadical ↥L) = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center (↥L ⧸ CFSG.solvableRadical ↥L))
      with h0 | h0
    · exact h0
    · exact absurd ((mem_center_iff.mp (h0 ▸ mem_top c)) a) hac
  have hc : (QuotientGroup.mk b : ↥L ⧸ CFSG.solvableRadical ↥L) ∈
      center (↥L ⧸ CFSG.solvableRadical ↥L) := by
    rw [mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : ((x⁻¹ * (b * x * b⁻¹) : ↥L) : ↥L ⧸ CFSG.solvableRadical ↥L) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hb x)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    have h2 := eq_of_inv_mul_eq_one h1
    calc (x : ↥L ⧸ CFSG.solvableRadical ↥L) * b
        = (b : ↥L ⧸ CFSG.solvableRadical ↥L) * x * (b : ↥L ⧸ CFSG.solvableRadical ↥L)⁻¹ * b := by
          rw [← h2]
      _ = b * x := by group
  rw [hcen, mem_bot, QuotientGroup.eq_one_iff] at hc
  exact hc

theorem originalCentralizer_inf_eq (h : QTNQ T L M) {R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) :
    R ⊓ L = T ⊓ (CFSG.solvableRadical L).map L.subtype := by
  have hRn := CFSG.ABGLocalTools.solvableRadical_normal (H := ↥L)
  ext x
  constructor
  · rintro ⟨hxR, hxL⟩
    have hx : x ∈ nqOriginalCentralizer T L := hR ▸ hxR
    rw [nqOriginalCentralizer, Set.mem_ofPred_eq] at hx
    refine ⟨hx.1, ⟨⟨x, hxL⟩, mem_radical_of_central h fun l => ?_, rfl⟩⟩
    obtain ⟨n, hn, hnx⟩ := hx.2 l l.2
    have e : l⁻¹ * ((⟨x, hxL⟩ : ↥L) * l * (⟨x, hxL⟩ : ↥L)⁻¹) = l⁻¹ * n * l := by
      apply Subtype.ext
      have hnx' : (n : G) = x * l * x⁻¹ * (l : G)⁻¹ := hnx
      simp only [coe_mul, coe_inv, hnx']
      group
    rw [e]
    have := hRn.conj_mem n hn l⁻¹
    simpa using this
  · rintro ⟨hxT, ⟨n, hn, rfl⟩⟩
    refine ⟨?_, n.2⟩
    show (n : G) ∈ (R : Set G)
    rw [hR, nqOriginalCentralizer, Set.mem_ofPred_eq]
    refine ⟨hxT, fun l hl => ?_⟩
    have hm : n * ((⟨l, hl⟩ : ↥L) * n⁻¹ * (⟨l, hl⟩ : ↥L)⁻¹) ∈ CFSG.solvableRadical ↥L :=
      mul_mem hn (hRn.conj_mem _ (inv_mem hn) _)
    refine ⟨_, hm, ?_⟩
    simp [mul_assoc]

theorem inf_normalizer_le_inf_normalizer_sylow (h : QTNQ T L M) {R : Subgroup G}
    (hR : (R : Set G) = nqOriginalCentralizer T L) :
    L ⊓ normalizer (R : Set G) ≤ L ⊓ normalizer
      ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G) := by
  rw [← originalCentralizer_inf_eq h hR]
  intro x hx
  obtain ⟨hxL, hxR⟩ := mem_inf.mp hx
  exact mem_inf.mpr ⟨hxL, mem_normalizer_inf hxR (le_normalizer hxL)⟩

theorem originalK_le_sylowResidual (h : QTNQ T L M) :
    nqOriginalK T L ≤ (CFSG.perfectResidual ↥(L ⊓ normalizer
      ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G))).map
      (L ⊓ normalizer
        ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G)).subtype := by
  obtain ⟨R, hR⟩ := NQBlock.exists_originalCentralizer (h.eq_normalizer ▸ h.t_le)
  unfold nqOriginalK
  rw [← hR, ← perfectCore_eq_map_perfectResidual, ← perfectCore_eq_map_perfectResidual]
  exact perfectCore_mono (inf_normalizer_le_inf_normalizer_sylow h hR)

theorem quotientCentralizer_self_eq (h : QTNQ T L M) {C : Subgroup ↥L}
    (hC : ∀ b : ↥L, b ∈ C ↔ ∀ x ∈ L.subgroupOf L, x⁻¹ * (b * x * b⁻¹) ∈
      (CFSG.solvableRadical (L.subgroupOf L)).map (L.subgroupOf L).subtype) :
    C = ((CFSG.solvableRadical L).map L.subtype).subgroupOf L := by
  have hN0 : (CFSG.solvableRadical (L.subgroupOf L)).map (L.subgroupOf L).subtype =
      CFSG.solvableRadical ↥L :=
    map_injective L.subtype_injective (NQBlock.map_radical_subgroupOf le_rfl)
  have hRn := CFSG.ABGLocalTools.solvableRadical_normal (H := ↥L)
  ext b
  rw [hC b, hN0, mem_subgroupOf]
  constructor
  · intro hb
    exact ⟨b, mem_radical_of_central h fun x => hb x (by rw [subgroupOf_self]; trivial), rfl⟩
  · rintro ⟨n, hn, hnb⟩
    have hb : b = n := Subtype.ext hnb.symm
    subst hb
    intro x _
    have h1 := hRn.conj_mem b hn x⁻¹
    have h2 : x⁻¹ * (b * x * b⁻¹) = (x⁻¹ * b * x⁻¹⁻¹) * b⁻¹ := by group
    rw [h2]
    exact mul_mem h1 (inv_mem hn)

theorem sylowResidual_le_originalK (h : QTNQ T L M) :
    (CFSG.perfectResidual ↥(L ⊓ normalizer
      ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G))).map
      (L ⊓ normalizer
        ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G)).subtype ≤
      nqOriginalK T L := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hKL, hTK, hLNK⟩ := NQBlock.original_K_supplement h
  have hLL : L ≤ L := le_rfl
  have hNL : (CFSG.solvableRadical L).map L.subtype ≤ L := map_subtype_le _
  have hL0n : (L.subgroupOf L).Normal := by
    rw [subgroupOf_self]
    infer_instance
  have hTM : IsSylowOf 2 T M := CFSG.ABGLocalTools.isSylowOf_iff.mpr
    ⟨h.t_le, h.sylow.1, fun h2 => h.sylow.2 (h2.trans (relIndex_dvd_index_of_le h.t_le))⟩
  obtain ⟨T0, hT0⟩ := hTM.inf_of_le_normalizer h.l_le h.eq_normalizer.le
  have hT0' : (T0 : Subgroup ↥L) = T.subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [hT0, subgroupOf_map_subtype]
  have hBLT : L.subgroupOf L ⊔ (T0 : Subgroup ↥L) = ⊤ := by
    rw [subgroupOf_self, top_sup_eq]
  let eL : L.subgroupOf L ≃* L := subgroupOfEquivOfLe hLL
  have hSQT : CFSG.IsStronglyQuasithin (L.subgroupOf L) := fun r hr hr2 => by
    rw [CFSG.QuasithinUnique.Setup.Campbell.pRank_eq_of_mulEquiv eL r]
    exact NQBlock.isStronglyQuasithin_L_of_qtnq h r hr hr2
  have hLC : CFSG.IsCComponent (⊤ : Subgroup (L.subgroupOf L)) := by
    have h1 := NQBlock.isCComponent_map_mulEquiv eL.symm (NQSetup.isCComponent_top_of_qtnq h)
    rwa [← MonoidHom.range_eq_map, MonoidHom.range_eq_top.mpr eL.symm.surjective] at h1
  let qO : (L.subgroupOf L ⧸ CFSG.pCore 2 (L.subgroupOf L)) ≃* (L ⧸ CFSG.pCore 2 L) :=
    QuotientGroup.congr _ _ eL (CFSG.LieType.SteinbergBR.pCore_map_equiv 2 eL)
  have hq : ¬ CFSG.IsQuasisimple (L.subgroupOf L ⧸ CFSG.pCore 2 (L.subgroupOf L)) :=
    fun hq' => h.not_quasisimple (CFSG.LocalCores.isQuasisimple_of_mulEquiv qO hq')
  obtain ⟨C', hC'⟩ := NQBlock.exists_quotientCentralizer (L.subgroupOf L)
    ((CFSG.solvableRadical (L.subgroupOf L)).map (L.subgroupOf L).subtype)
  obtain ⟨K', hK'⟩ : ∃ K' : Subgroup ↥L, K' = (CFSG.perfectResidual ↥(L.subgroupOf L ⊓
      normalizer (((T0 : Subgroup ↥L) ⊓ C' : Subgroup ↥L) : Set ↥L))).map
    (L.subgroupOf L ⊓ normalizer (((T0 : Subgroup ↥L) ⊓ C' : Subgroup ↥L) : Set ↥L)).subtype :=
    ⟨_, rfl⟩
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, -, hL1⟩ :=
    NQBlock.radical_Sylow_normalizer_residual_is_common_simple_two_core_supplement
      (L.subgroupOf L) T0 hBLT hSQT hLC hq _ C' _ _ K' rfl hC' rfl rfl hK'
  have hKL' : (nqOriginalK T L).subgroupOf L ≤ L.subgroupOf L := fun x _ => x.2
  have hTK' : (T0 : Subgroup ↥L) ≤
      normalizer (((nqOriginalK T L).subgroupOf L : Subgroup ↥L) : Set ↥L) := by
    rw [hT0', ← subgroupOf_normalizer_eq hKL]
    exact fun x hx => hTK hx
  have hLNK' : L.subgroupOf L = (CFSG.solvableRadical (L.subgroupOf L)).map
      (L.subgroupOf L).subtype ⊔ (nqOriginalK T L).subgroupOf L := by
    apply map_injective L.subtype_injective
    rw [Subgroup.map_sup, NQBlock.map_radical_subgroupOf hLL, map_subgroupOf_eq_of_le hLL,
      map_subgroupOf_eq_of_le hKL]
    exact hLNK
  obtain ⟨-, -, -, h4⟩ := hL1 _ hKL' hTK' hLNK'
  have hR0 : (((T0 : Subgroup ↥L) ⊓ C' : Subgroup ↥L)).map L.subtype =
      T ⊓ (CFSG.solvableRadical L).map L.subtype := by
    rw [map_inf_eq _ _ _ L.subtype_injective, hT0, quotientCentralizer_self_eq h hC',
      subgroupOf_map_subtype, inf_eq_left.mpr hNL, inf_assoc, inf_eq_right.mpr hNL]
  have hKmap : K'.map L.subtype = (CFSG.perfectResidual ↥(L ⊓ normalizer
      ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G))).map
      (L ⊓ normalizer
        ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G)).subtype := by
    rw [hK', ← perfectCore_eq_map_perfectResidual, map_perfectCore,
      NQBlock.map_inf_normalizer_subgroupOf hLL hR0, perfectCore_eq_map_perfectResidual]
  have h5 := map_mono (f := L.subtype) h4
  rwa [hKmap, map_subgroupOf_eq_of_le hKL] at h5

theorem originalK_eq_sylowResidual (h : QTNQ T L M) :
    nqOriginalK T L = (CFSG.perfectResidual ↥(L ⊓ normalizer
      ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G))).map
      (L ⊓ normalizer
        ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G)).subtype :=
  le_antisymm (originalK_le_sylowResidual h) (sylowResidual_le_originalK h)

theorem le_normalizer_originalK (h : QTNQ T L M) {I : Subgroup G}
    (hIL : I ≤ normalizer (L : Set G))
    (hIS : I ≤ normalizer ((T ⊓ (CFSG.solvableRadical L).map L.subtype : Subgroup G) : Set G)) :
    I ≤ normalizer (nqOriginalK T L : Set G) := by
  rw [originalK_eq_sylowResidual h, ← perfectCore_eq_map_perfectResidual]
  refine le_trans ?_ (normalizer_le_normalizer_perfectCore _)
  intro x hx
  exact mem_normalizer_inf (hIL hx) (le_normalizer (hIS hx))

theorem oTwoUpper_originalK_sup (h : QTNQ T L M) :
    oTwoUpper (nqOriginalK T L ⊔ T) = nqOriginalK T L := by
  obtain ⟨-, hTK, -⟩ := NQBlock.original_K_supplement h
  have hKp : ⁅nqOriginalK T L, nqOriginalK T L⁆ = nqOriginalK T L := by
    unfold nqOriginalK
    rw [← perfectCore_eq_map_perfectResidual]
    exact perfectCore_perfect _
  exact oTwoUpper_sup_eq_of_perfect hKp h.sylow.1 hTK

end Sylow

end CFSG.Quasithin.H13.NQRigid

module

public import CFSG.Quasithin.Background.GoldschmidtS146RQuot
public import CFSG.Quasithin.Background.GoldschmidtS146RPair
public import CFSG.Quasithin.EmptyFaithful.S146D1
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B113OverBender

public section

namespace CFSG.Quasithin.GoldS146R

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

section Bender

theorem fusionIsBenderGroup_congr {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : fusionIsBenderGroup X) : fusionIsBenderGroup Y := by
  rcases h with ⟨f, hf, ⟨e'⟩⟩ | ⟨f, hf, ⟨e'⟩⟩ | ⟨a, ha, ⟨e'⟩⟩
  · exact Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩
  · exact Or.inr (Or.inl ⟨f, hf, ⟨e.symm.trans e'⟩⟩)
  · exact Or.inr (Or.inr ⟨a, ha, ⟨e.symm.trans e'⟩⟩)

theorem fusionIsBenderGroup_of_shape {X : Type} [Group X]
    (h : (∃ n, IsPSL 2 2 n X) ∨ (∃ n, IsSz n X) ∨ IsAlt 5 X) : fusionIsBenderGroup X := by
  rcases h with ⟨n, hn⟩ | ⟨n, hn⟩ | h5
  · exact A5.C25.fusionIsBenderGroup_of_isPSL hn
  · exact A5.C25.fusionIsBenderGroup_of_isSz hn
  · exact A5.C25.fusionIsBenderGroup_of_isPSL
      (Ch1.statedClassicalModel_psl_two_four_of_alternating_five X h5)

variable {Q : Type} [Group Q] [Finite Q]

theorem bender_overgroup {A : Subgroup Q} (hB : fusionIsBenderGroup ↥A) {S R : Subgroup Q}
    (hS : IsSylowTwoOf S A) (hSR : S ≤ R) (hRA : R ≤ A) :
    R ≤ Subgroup.normalizer (S : Set Q) ∨ A ≤ R := by
  have hs : IsSimpleGroup ↥A := RankOneRecog.isSimpleGroup_of_fusionIsBenderGroup hB
  set SA : Sylow 2 ↥A := sylowOfIsSylowTwoOf hS with hSA
  by_cases hR : R.subgroupOf A = ⊤
  · right
    rwa [Subgroup.subgroupOf_eq_top] at hR
  · left
    have hSR' : (SA : Subgroup ↥A) ≤ R.subgroupOf A := by
      intro x hx
      rw [hSA, coe_sylowOfIsSylowTwoOf, Subgroup.mem_subgroupOf] at hx
      exact hSR hx
    have h1 := Bridge.Over.le_normalizer_of_bender hB SA hSR' hR
    intro r hr
    have hrA : r ∈ A := hRA hr
    have h2 := h1 (show (⟨r, hrA⟩ : ↥A) ∈ R.subgroupOf A from hr)
    rw [Subgroup.mem_normalizer_iff] at h2 ⊢
    intro x
    by_cases hxA : x ∈ A
    · have h3 := h2 ⟨x, hxA⟩
      rw [hSA, coe_sylowOfIsSylowTwoOf, Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf] at h3
      simpa using h3
    · constructor
      · intro hx
        exact absurd (hS.1 hx) hxA
      · intro hx
        have hx1 : r * x * r⁻¹ ∈ A := hS.1 hx
        have hx2 : x ∈ A := by
          have := A.mul_mem (A.mul_mem (A.inv_mem hrA) hx1) hrA
          simpa [mul_assoc] using this
        exact absurd hx2 hxA

theorem bender_sylow_ne_bot {A : Subgroup Q} (hB : fusionIsBenderGroup ↥A) {S : Subgroup Q}
    (hS : IsSylowTwoOf S A) : S ≠ ⊥ := by
  intro hbot
  obtain ⟨q, k, hq4, hBor⟩ := Unc25G2.BenderBorel.exists_borel_of_bender hB
  set SA : Sylow 2 ↥A := sylowOfIsSylowTwoOf hS with hSA
  obtain ⟨-, -, -, hZcard, -⟩ := hBor SA
  have hSAbot : (SA : Subgroup ↥A) = ⊥ := by
    rw [hSA, coe_sylowOfIsSylowTwoOf, hbot, Subgroup.bot_subgroupOf]
  have h1 : Nat.card (Subgroup.center (SA : Subgroup ↥A)) = 1 := by
    have : Subsingleton ↥(SA : Subgroup ↥A) := by
      rw [hSAbot]
      infer_instance
    have : Subsingleton (Subgroup.center (SA : Subgroup ↥A)) :=
      (Subgroup.center (SA : Subgroup ↥A)).subtype_injective.subsingleton
    exact Nat.card_unique
  omega

end Bender

section Dichotomy

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem inf_pCoreOf_eq_of_mem_cComp [Finite G] {H K : Subgroup G} (hK : K ∈ cComp H) :
    K ⊓ pCoreOf 2 H = pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply le_antisymm
  · have hKH : K ≤ H := le_of_mem_cComp hK
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
    intro x hx
    exact Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hx, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hx)⟩
  · exact le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K)
      (A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK))

omit [Finite G] in
theorem exists_noncomm_of_equiv {X : Type} [Group X] {A : Subgroup G} (e : X ≃* ↥A)
    (h : ¬ IsMulCommutative X) : ∃ x ∈ A, ∃ y ∈ A, x * y ≠ y * x := by
  by_contra hcon
  push Not at hcon
  apply h
  refine ⟨⟨fun a b => ?_⟩⟩
  have h1 := hcon (e a) (e a).2 (e b) (e b).2
  have h2 : e a * e b = e b * e a := Subtype.ext h1
  have h3 : e (a * b) = e (b * a) := by rw [map_mul, map_mul, h2]
  exact e.injective h3

theorem eq_of_imgJ_le {H J K K₂ : Subgroup G} [(J.subgroupOf H).Normal] (hK : K ∈ cComp H)
    (hK₂ : K₂ ∈ cComp H) (hJH : J ≤ H) (hJs : Group.IsSolvable ↥J)
    (hle : imgJ H J K ≤ imgJ H J K₂) : K = K₂ := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hK₂H : K₂ ≤ H := le_of_mem_cComp hK₂
  have hKle : K ≤ K₂ ⊔ J := by
    intro k hk
    have h1 : ((⟨k, hKH hk⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) ∈ imgJ H J K :=
      (mk_mem_imgJ hKH hJH _).mpr (Subgroup.mem_sup_left hk)
    exact (mk_mem_imgJ hK₂H hJH _).mp (hle h1)
  have hnorm : K₂ ≤ Subgroup.normalizer (J : Set G) :=
    hK₂H.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hJH).mp inferInstance)
  have hcore : perfectCore (K₂ ⊔ J) = K₂ :=
    (cComp_commutator_perfectCore hK₂ hJH hJs hnorm).2
  have hKK₂ : K ≤ K₂ := by
    calc K = perfectCore K := (perfectCore_eq_self_of_perfect (perfect_of_mem_cComp hK)).symm
      _ ≤ perfectCore (K₂ ⊔ J) := perfectCore_mono hKle
      _ = K₂ := hcore
  by_contra hne
  exact not_subnormal_of_mem_cComp hK₂ (lt_of_le_of_ne hKK₂ hne) (ne_bot_of_mem_cComp hK)
    (perfect_of_mem_cComp hK) (subnormal_of_mem_cComp hK)

theorem pair_facts {T K : Subgroup G} {t : G}
    (hsyl : IsSylowTwoOf T (conjClosure K T ⊔ T)) (hKc : K ∈ cComp (conjClosure K T ⊔ T))
    (htT : t ∈ T) (htK : t ∉ Subgroup.normalizer (K : Set G))
    (hK₀ : conjClosure K T = K ⊔ K.map (MulAut.conj t).toMonoidHom)
    (hcomm : ⁅K, K.map (MulAut.conj t).toMonoidHom⁆ ≤ pCoreOf 2 (conjClosure K T ⊔ T))
    (hsimp : IsSimpleGroup (KBar K)) (hBen : fusionIsBenderGroup (KBar K)) :
    (∀ Y : Subgroup G, T ≤ Y → Y ≤ conjClosure K T ⊔ T →
      conjClosure K T ≤ Y ∨
        Y ⊓ conjClosure K T ≤ Subgroup.normalizer ((T ⊓ conjClosure K T : Subgroup G) : Set G)) ∧
    ∀ K₂ ∈ cComp (conjClosure K T ⊔ T), K₂ = K ∨ K₂ = K.map (MulAut.conj t).toMonoidHom := by
  set K₀ : Subgroup G := conjClosure K T with hK₀def
  set H : Subgroup G := K₀ ⊔ T with hHdef
  set J : Subgroup G := pCoreOf 2 H with hJdef
  set Kt : Subgroup G := K.map (MulAut.conj t).toMonoidHom with hKtdef
  have hTH : T ≤ H := le_sup_right
  have htH : t ∈ H := hTH htT
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hK₀H : K₀ ≤ H := le_sup_left
  have hJH : J ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hJT : J ≤ T := pCoreOf_two_le_of_isSylowTwoOf hsyl
  have hKtc : Kt ∈ cComp H := map_conj_mem_cComp hKc htH
  have hKtH : Kt ≤ H := le_of_mem_cComp hKtc
  have hKJ : K ⊓ J = pCoreOf 2 K := inf_pCoreOf_eq_of_mem_cComp hKc
  have hnorm₀ : (K₀.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK₀H).mpr
      (sup_le Subgroup.le_normalizer (le_normalizer_conjClosure K T))
  set A₁ : Subgroup (↥H ⧸ J.subgroupOf H) := imgJ H J K with hA₁
  set A₂ : Subgroup (↥H ⧸ J.subgroupOf H) := imgJ H J Kt with hA₂
  set P : Subgroup (↥H ⧸ J.subgroupOf H) := imgJ H J T with hP
  set τ : ↥H ⧸ J.subgroupOf H := ((⟨t, htH⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) with hτ
  have hsup : A₁ ⊔ A₂ = imgJ H J K₀ := by
    rw [hA₁, hA₂, ← imgJ_sup hKH hKtH, ← hK₀]
  have hnormA : (A₁ ⊔ A₂).Normal := by
    rw [hsup]
    exact normal_imgJ hnorm₀
  have hc : ∀ a ∈ A₁, ∀ b ∈ A₂, a * b = b * a := by
    intro a ha b hb
    obtain ⟨x, hxK, rfl⟩ := mem_imgJ.mp ha
    obtain ⟨y, hyK, rfl⟩ := mem_imgJ.mp hb
    have hcom : ((x : G) * y * (x : G)⁻¹ * (y : G)⁻¹) ∈ J := by
      have := hcomm (Subgroup.commutator_mem_commutator hxK hyK)
      simpa [commutatorElement_def] using this
    have h1 : ((x * y * x⁻¹ * y⁻¹ : ↥H) : ↥H ⧸ J.subgroupOf H) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hcom)
    rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv,
      QuotientGroup.mk_inv] at h1
    calc (x : ↥H ⧸ J.subgroupOf H) * y =
        ((x : ↥H ⧸ J.subgroupOf H) * y * (x : ↥H ⧸ J.subgroupOf H)⁻¹ *
          (y : ↥H ⧸ J.subgroupOf H)⁻¹) * (y * x) := by group
      _ = y * x := by rw [h1, one_mul]
  obtain ⟨eK⟩ := nonempty_kbar_equiv_imgJ (J := J) hKH hKJ
  have hs₁ : IsSimpleGroup ↥A₁ := (MulEquiv.isSimpleGroup_congr eK).mp hsimp
  have hna₁ : ∃ x ∈ A₁, ∃ y ∈ A₁, x * y ≠ y * x :=
    exists_noncomm_of_equiv eK (not_isMulCommutative_kbar hKc)
  have hA₂eq : A₂ = A₁.map (MulAut.conj τ).toMonoidHom := (imgJ_map_conj hKH ⟨t, htH⟩)
  let eA : ↥A₁ ≃* ↥A₂ :=
    (Subgroup.equivMapOfInjective A₁ (MulAut.conj τ).toMonoidHom (MulAut.conj τ).injective).trans
      (MulEquiv.subgroupCongr hA₂eq.symm)
  have hs₂ : IsSimpleGroup ↥A₂ := (MulEquiv.isSimpleGroup_congr eA).mp hs₁
  have hna₂ : ∃ x ∈ A₂, ∃ y ∈ A₂, x * y ≠ y * x := by
    obtain ⟨x, hx, y, hy, hxy⟩ := hna₁
    refine ⟨τ * x * τ⁻¹, ?_, τ * y * τ⁻¹, ?_, ?_⟩
    · rw [hA₂eq]; exact ⟨x, hx, by simp [MulAut.conj_apply]⟩
    · rw [hA₂eq]; exact ⟨y, hy, by simp [MulAut.conj_apply]⟩
    · intro h
      apply hxy
      have h2 : τ * (x * y) * τ⁻¹ = τ * (y * x) * τ⁻¹ := by
        calc τ * (x * y) * τ⁻¹ = (τ * x * τ⁻¹) * (τ * y * τ⁻¹) := by group
          _ = (τ * y * τ⁻¹) * (τ * x * τ⁻¹) := h
          _ = τ * (y * x) * τ⁻¹ := by group
      have h3 := mul_left_cancel (mul_right_cancel h2)
      exact h3
  have hPsyl : IsSylowTwoOf P ⊤ := isSylowTwoOf_imgJ hsyl hJT
  have hBenA : fusionIsBenderGroup ↥A₁ := fusionIsBenderGroup_congr eK hBen
  have hA₁sub : IsSubnormal A₁ ⊤ := by
    have := hnormA
    exact IsSubnormal.step le_sup_left (normal_subgroupOf_sup_left hc)
      (IsSubnormal.step le_top inferInstance (IsSubnormal.refl ⊤))
  have hS₁ : IsSylowTwoOf (P ⊓ A₁) A₁ := A312.isSylowTwoOf_inf_of_subnormal hA₁sub hPsyl
  have hS₁ne : P ⊓ A₁ ≠ ⊥ := bender_sylow_ne_bot hBenA hS₁
  have hτP : τ ∈ P := (mk_mem_imgJ hTH hJH ⟨t, htH⟩).mpr (Subgroup.mem_sup_left htT)
  have hJs : Group.IsSolvable ↥J := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have : Group.IsNilpotent ↥J := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).isNilpotent
    infer_instance
  refine ⟨fun Y hTY hYH => ?_, fun K₂ hK₂ => ?_⟩
  · set Y' : Subgroup (↥H ⧸ J.subgroupOf H) := imgJ H J Y with hY'
    have hPY : P ≤ Y' := imgJ_mono hTY
    rcases pair_overgroup hna₁ hna₂ hc hnormA hA₂eq hPsyl.2.1 hS₁ hS₁ne hτP hPY
        (fun S R hS hSR hRA => bender_overgroup hBenA hS hSR hRA) with hfull | hnormal
    · left
      intro k hk
      have hkH : k ∈ H := hK₀H hk
      have h1 : ((⟨k, hkH⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) ∈ A₁ ⊔ A₂ := by
        rw [hsup]
        exact (mk_mem_imgJ hK₀H hJH ⟨k, hkH⟩).mpr (Subgroup.mem_sup_left hk)
      have h2 := (mk_mem_imgJ hYH hJH ⟨k, hkH⟩).mp (hfull h1)
      have h3 : Y ⊔ J = Y := sup_eq_left.mpr (hJT.trans hTY)
      rwa [h3] at h2
    · right
      have key : ∀ y ∈ Y ⊓ K₀, ∀ x ∈ T ⊓ K₀, y * x * y⁻¹ ∈ T ⊓ K₀ := by
        intro y hy x hx
        have hyH : y ∈ H := hK₀H hy.2
        have hxH : x ∈ H := hK₀H hx.2
        have hz : ((⟨y, hyH⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) ∈ Y' ⊓ (A₁ ⊔ A₂) := by
          refine ⟨(mk_mem_imgJ hYH hJH _).mpr (Subgroup.mem_sup_left hy.1), ?_⟩
          rw [hsup]
          exact (mk_mem_imgJ hK₀H hJH _).mpr (Subgroup.mem_sup_left hy.2)
        have hs : ((⟨x, hxH⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) ∈ P ⊓ (A₁ ⊔ A₂) := by
          refine ⟨(mk_mem_imgJ hTH hJH _).mpr (Subgroup.mem_sup_left hx.1), ?_⟩
          rw [hsup]
          exact (mk_mem_imgJ hK₀H hJH _).mpr (Subgroup.mem_sup_left hx.2)
        have h3 := hnormal _ hz _ hs
        have h4 : ((⟨y, hyH⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) *
            ((⟨x, hxH⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) *
            ((⟨y, hyH⟩ : ↥H) : ↥H ⧸ J.subgroupOf H)⁻¹ =
            (((⟨y, hyH⟩ * ⟨x, hxH⟩ * ⟨y, hyH⟩⁻¹ : ↥H)) : ↥H ⧸ J.subgroupOf H) := by
          rw [QuotientGroup.mk_mul, QuotientGroup.mk_mul, QuotientGroup.mk_inv]
        rw [h4] at h3
        have h5 := (mk_mem_imgJ hTH hJH _).mp h3
        rw [sup_eq_left.mpr hJT] at h5
        exact ⟨h5, K₀.mul_mem (K₀.mul_mem hy.2 hx.2) (K₀.inv_mem hy.2)⟩
      intro y hy
      refine B6.mem_normalizer_of_forall_mem (key y hy) (fun x hx => ?_)
      have := key y⁻¹ ⟨Y.inv_mem hy.1, K₀.inv_mem hy.2⟩ x hx
      simpa using this
  ·
    have hK₂H : K₂ ≤ H := le_of_mem_cComp hK₂
    have hnormKJ : ((K₀ ⊔ J).subgroupOf H).Normal := by
      rw [Subgroup.subgroupOf_sup hK₀H hJH]
      have := hnorm₀
      infer_instance
    have hTs : Group.IsSolvable ↥T := by
      have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
      have : Group.IsNilpotent ↥T := hsyl.2.1.isNilpotent
      infer_instance
    have hK₂le : K₂ ≤ K₀ ⊔ J := by
      have h1 : K₂ ≤ perfectCore H := le_perfectCore_of_perfect hK₂H (perfect_of_mem_cComp hK₂)
      have h2 : perfectCore H ≤ K₀ ⊔ J :=
        perfectCore_le_of_sup_solvable (A := K₀ ⊔ J) (B := T) (Y := H) (sup_le hK₀H hJH) hnormKJ
          (le_antisymm (sup_le_sup_right le_sup_left T) (sup_le (sup_le hK₀H hJH) hTH)) hTs
      exact h1.trans h2
    have hX₂le : imgJ H J K₂ ≤ A₁ ⊔ A₂ := by
      rw [hsup]
      intro q hq
      obtain ⟨h, hhK₂, rfl⟩ := mem_imgJ.mp hq
      exact (mk_mem_imgJ hK₀H hJH h).mpr (hK₂le hhK₂)
    have hX₂ne : imgJ H J K₂ ≠ ⊥ := by
      intro hbot
      have hK₂J : K₂ ≤ J := by
        intro k hk
        have h1 : ((⟨k, hK₂H hk⟩ : ↥H) : ↥H ⧸ J.subgroupOf H) ∈ imgJ H J K₂ :=
          mem_imgJ.mpr ⟨⟨k, hK₂H hk⟩, hk, rfl⟩
        rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at h1
        exact Subgroup.mem_subgroupOf.mp h1
      exact not_isSolvable_of_mem_cComp hK₂
        (Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hK₂J)
          (Subgroup.inclusion_injective hK₂J))
    have hX₂sub : IsSubnormal (imgJ H J K₂) (A₁ ⊔ A₂) := by
      have h1 : IsSubnormal (K₂.subgroupOf H) (H.subgroupOf H) :=
        A4.subnormal_subgroupOf H (subnormal_of_mem_cComp hK₂)
      rw [Subgroup.subgroupOf_self] at h1
      have h2 := A3.subnormal_map (QuotientGroup.mk' (J.subgroupOf H)) h1
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective _)] at h2
      exact A3.subnormal_of_le_of_le h2 hX₂le le_top
    rcases classify_subnormal hna₁ hna₂ hc hX₂sub hX₂ne with h | h | h
    · exact Or.inl (eq_of_imgJ_le hKc hK₂ hJH hJs (le_of_eq h.symm)).symm
    · exact Or.inr (eq_of_imgJ_le hKtc hK₂ hJH hJs (le_of_eq h.symm)).symm
    · exfalso
      have h1 : K = K₂ := eq_of_imgJ_le hKc hK₂ hJH hJs (h ▸ le_sup_left)
      have h2 : Kt = K₂ := eq_of_imgJ_le hKtc hK₂ hJH hJs (h ▸ le_sup_right)
      exact htK (A38.map_conj_eq_iff.mp (h2.trans h1.symm))

end Dichotomy

end CFSG.Quasithin.GoldS146R

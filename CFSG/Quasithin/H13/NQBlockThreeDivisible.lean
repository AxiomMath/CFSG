module

public import CFSG.Quasithin.H13.NQCatSuzukiComplementary
public import CFSG.Quasithin.H13.NQBlockSourceRank
public import CFSG.Quasithin.SteinbergBTCommutingFactorsPrimeRank

public section

namespace CFSG.Quasithin.H13.NQBlock

open Subgroup CFSG.Open

theorem card_dvd_center_quotient {X Γ : Type*} [Group X] [Group Γ] (ψ : X →* Γ)
    (N : Subgroup X) [N.Normal] (hker : ψ.ker ≤ N) (hsimple : IsSimpleGroup (X ⧸ N))
    (hnab : ∃ a b : X ⧸ N, a * b ≠ b * a) :
    Nat.card (X ⧸ N) ∣ Nat.card (↥ψ.range ⧸ center ↥ψ.range) := by
  classical
  have := hsimple
  have hZ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  set θ₀ : X ⧸ ψ.ker →* X ⧸ N := QuotientGroup.map ψ.ker N (MonoidHom.id X) hker with hθ₀def
  set θ : ↥ψ.range →* X ⧸ N := θ₀.comp (QuotientGroup.quotientKerEquivRange ψ).symm.toMonoidHom
    with hθdef
  have hθs : Function.Surjective θ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    refine ⟨⟨ψ x, x, rfl⟩, ?_⟩
    have h1 : (QuotientGroup.quotientKerEquivRange ψ).symm ⟨ψ x, x, rfl⟩ =
        (x : X ⧸ ψ.ker) := by
      apply (QuotientGroup.quotientKerEquivRange ψ).injective
      rw [MulEquiv.apply_symm_apply]
      rfl
    rw [hθdef, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, h1]
    rfl
  have hcen : center ↥ψ.range ≤ θ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have h1 : θ z ∈ center (X ⧸ N) := by
      rw [mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := hθs w
      rw [← map_mul, ← map_mul, (mem_center_iff.mp hz) w']
    rw [hZ, mem_bot] at h1
    exact h1
  have hs : Function.Surjective (QuotientGroup.lift (center ↥ψ.range) θ hcen) := by
    intro y
    obtain ⟨z, rfl⟩ := hθs y
    exact ⟨(z : ↥ψ.range ⧸ center ↥ψ.range), rfl⟩
  exact Subgroup.card_dvd_of_surjective hs

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_map_eq_bot_of_le_pCoreOf {H X Y : Subgroup G} (hXH : X ≤ H) (hYH : Y ≤ H)
    (hXY : ⁅X, Y⁆ ≤ pCoreOf 2 H) :
    ⁅(X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      (Y.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))⁆ = ⊥ := by
  rw [← map_commutator, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
  intro z hz
  rw [mem_pCore_iff_mem_pCoreOf]
  apply hXY
  have h1 := mem_map_of_mem H.subtype hz
  rwa [map_commutator, map_subgroupOf_eq_of_le hXH, map_subgroupOf_eq_of_le hYH] at h1

theorem mem_pCore_of_mem_pCoreOf {H X : Subgroup G} (hXH : X ≤ H) (x : ↥X)
    (hx : (x : G) ∈ pCoreOf 2 H) : x ∈ CFSG.pCore 2 ↥X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [mem_pCore_iff_mem_pCoreOf]
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left (fun g hg => ?_)
    ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right) (mem_inf.mpr ⟨x.2, hx⟩)
  exact Subgroup.inf_normalizer_le_normalizer_inf
    ⟨le_normalizer hg, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hXH hg)⟩

omit [Finite G] in
theorem three_dvd_image_center_quotient {H X : Subgroup G} (hXH : X ≤ H) (N : Subgroup ↥X)
    [N.Normal] (hker : ∀ x : ↥X, (x : G) ∈ pCoreOf 2 H → x ∈ N) (hs : IsSimpleGroup (↥X ⧸ N))
    (hnab : ∃ a b : ↥X ⧸ N, a * b ≠ b * a) (h3 : 3 ∣ Nat.card (↥X ⧸ N)) :
    3 ∣ Nat.card (↥((X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) ⧸
      center ↥((X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) := by
  set ψ : ↥X →* ↥H ⧸ CFSG.pCore 2 ↥H :=
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (Subgroup.inclusion hXH) with hψdef
  have hψr : ψ.range = (X.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) := by
    rw [hψdef, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hψk : ψ.ker ≤ N := by
    intro x hx
    apply hker
    rw [MonoidHom.mem_ker, hψdef, MonoidHom.comp_apply, ← MonoidHom.mem_ker,
      QuotientGroup.ker_mk', mem_pCore_iff_mem_pCoreOf] at hx
    exact hx
  have h1 := card_dvd_center_quotient ψ N hψk hs hnab
  rw [hψr] at h1
  exact h3.trans h1

omit [Finite G] in
theorem card_radical_quotient_map_conj (B : Subgroup G) (g : G) :
    Nat.card (↥(B.map (MulAut.conj g).toMonoidHom) ⧸
      CFSG.solvableRadical ↥(B.map (MulAut.conj g).toMonoidHom)) =
      Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) := by
  let e : ↥B ≃* ↥(B.map (MulAut.conj g).toMonoidHom) :=
    B.equivMapOfInjective _ (MulAut.conj g).injective
  exact (Nat.card_congr (QuotientGroup.congr _ _ e
    (CFSG.LieType.SteinbergBR.solvableRadical_map_equiv e)).toEquiv).symm

theorem complementary_three_divisible_unique
    {T L M : Subgroup G} (h : QTNQ T L M) {H : Subgroup G} (hH : quasithinIsMaxTwoLocal H)
    (hKTH : nqOriginalK T L ⊔ T ≤ H) {A : Subgroup G} (hA : A ∈ cComp H)
    (hKA : nqOriginalK T L ≤ A) {B₁ B₂ : Subgroup G} (hB₁ : B₁ ∈ cComp H) (hB₂ : B₂ ∈ cComp H)
    (hB₁A : B₁ ≠ A) (hB₂A : B₂ ≠ A)
    (h3₁ : 3 ∣ Nat.card (↥B₁ ⧸ CFSG.solvableRadical ↥B₁))
    (h3₂ : 3 ∣ Nat.card (↥B₂ ⧸ CFSG.solvableRadical ↥B₂)) : B₁ = B₂ := by
  classical
  by_contra hne
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hloc : QuasithinUnique.LocalSQTK G :=
    (QuasithinUnique.qtkeCore_of_cat h.nonabelian h.qtke).1
  have hO2 := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hH.1
  have hΓ := QuasithinUnique.Vol2Native.sqtkHypCat_quotient_of_pCoreOf_ne_bot hloc hO2
  have hr3 : CFSG.pRank 3 (↥H ⧸ CFSG.pCore 2 ↥H) ≤ 2 := hΓ.sqt 3 Nat.prime_three (by norm_num)
  have hKH : nqOriginalK T L ≤ H := le_sup_left.trans hKTH
  have hB₁H : B₁ ≤ H := le_of_mem_cComp hB₁
  have hB₂H : B₂ ≤ H := le_of_mem_cComp hB₂
  have hcommH : ∀ {X Y : Subgroup G}, X ∈ cComp H → Y ∈ cComp H → X ≠ Y →
      ⁅X, Y⁆ ≤ pCoreOf 2 H := fun hX hY hXY =>
    let h1 := QuasithinUnique.Vol2Native.lemma_1_2_1_two hloc
      QuasithinUnique.Vol2Native.a37ForSQTKCat_proved hO2 hX hY hXY
    h1.1.trans h1.2
  have hKB : ∀ {B : Subgroup G}, B ∈ cComp H → B ≠ A → ⁅nqOriginalK T L, B⁆ ≤ pCoreOf 2 H :=
    fun hB hBA => (commutator_mono hKA le_rfl).trans (hcommH hA hB (Ne.symm hBA))
  have hc01 := commutator_map_eq_bot_of_le_pCoreOf hKH hB₁H (hKB hB₁ hB₁A)
  have hc02 := commutator_map_eq_bot_of_le_pCoreOf hKH hB₂H (hKB hB₂ hB₂A)
  have hc12 := commutator_map_eq_bot_of_le_pCoreOf hB₁H hB₂H (hcommH hB₁ hB₂ hne)
  obtain ⟨-, -, -, hKs, hKnab, s, hs, hs5, -, hKcard⟩ := original_K_quotient_facts h
  have hd0 := three_dvd_image_center_quotient hKH (CFSG.pCore 2 ↥(nqOriginalK T L))
    (mem_pCore_of_mem_pCoreOf hKH) hKs hKnab (by rw [hKcard]; exact three_dvd_half_order hs hs5)
  have hdB : ∀ {B : Subgroup G}, B ∈ cComp H → 3 ∣ Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) →
      3 ∣ Nat.card (↥((B.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))) ⧸
        center ↥((B.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)))) := by
    intro B hB h3
    have hBc : CFSG.IsCComponent (⊤ : Subgroup ↥B) := by
      have h2 : B ∈ cComp B := cComp_mem_of_le hB le_rfl (le_of_mem_cComp hB)
      have h4 := mem_cComp_top_iff_isCComponent.mp (subgroupOf_mem_cComp h2)
      rwa [subgroupOf_self] at h4
    obtain ⟨hBs, hBnab⟩ := simple_radical_quotient_of_isCComponent_top hBc
    have hOR : CFSG.pCore 2 ↥B ≤ CFSG.solvableRadical ↥B := by
      have : Group.IsNilpotent (CFSG.pCore 2 ↥B) :=
        (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥B)).isNilpotent
      exact le_sSup ⟨CFSG.pCore_normal, inferInstance⟩
    exact three_dvd_image_center_quotient (le_of_mem_cComp hB) (CFSG.solvableRadical ↥B)
      (fun x hx => hOR (mem_pCore_of_mem_pCoreOf (le_of_mem_cComp hB) x hx)) hBs hBnab h3
  have hd1 := hdB hB₁ h3₁
  have hd2 := hdB hB₂ h3₂
  let Lf : Fin 3 → Subgroup (↥H ⧸ CFSG.pCore 2 ↥H) :=
    ![((nqOriginalK T L).subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      (B₁.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H)),
      (B₂.subgroupOf H).map (QuotientGroup.mk' (CFSG.pCore 2 ↥H))]
  have hcomm : ∀ i j, i ≠ j → ⁅Lf i, Lf j⁆ = ⊥ := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · exact absurd rfl hij
    · exact hc01
    · exact hc02
    · exact (commutator_comm _ _).trans hc01
    · exact absurd rfl hij
    · exact hc12
    · exact (commutator_comm _ _).trans hc02
    · exact (commutator_comm _ _).trans hc12
    · exact absurd rfl hij
  have h3 := SteinbergBT.commuting_central_quotient_factors_force_prime_rank Nat.prime_three 3 Lf
    hcomm fun i => by
      fin_cases i
      · exact hd0
      · exact hd1
      · exact hd2
  omega

theorem complementary_three_divisible_normal
    {T L M : Subgroup G} (h : QTNQ T L M) {H : Subgroup G} (hH : quasithinIsMaxTwoLocal H)
    (hKTH : nqOriginalK T L ⊔ T ≤ H) {A : Subgroup G} (hA : A ∈ cComp H)
    (hKA : nqOriginalK T L ≤ A) (hHA : H ≤ normalizer (A : Set G)) {B : Subgroup G}
    (hB : B ∈ cComp H) (hBA : B ≠ A) (h3 : 3 ∣ Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)) :
    H ≤ normalizer (B : Set G) := by
  intro g hg
  have hBg := CFSG.Quasithin.map_conj_mem_cComp hB hg
  have hBgA : B.map (MulAut.conj g).toMonoidHom ≠ A := by
    intro he
    have hAg : A.map (MulAut.conj g).toMonoidHom = A :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHA hg)
    exact hBA (Subgroup.map_injective (MulAut.conj g).injective (he.trans hAg.symm))
  have h3g : 3 ∣ Nat.card (↥(B.map (MulAut.conj g).toMonoidHom) ⧸
      CFSG.solvableRadical ↥(B.map (MulAut.conj g).toMonoidHom)) := by
    rw [card_radical_quotient_map_conj]
    exact h3
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (complementary_three_divisible_unique h hH hKTH hA hKA hBg hB hBgA hBA h3g h3)

theorem complementaryThreeDivisibleUniqueNormal_holds
    :
    ∀ (G : Type) [Group G] [Finite G] (T L M : Subgroup G), QTNQ T L M →
      ∀ H : Subgroup G, quasithinIsMaxTwoLocal H → nqOriginalK T L ⊔ T ≤ H → H ≠ M →
      ∀ A ∈ cComp H, nqOriginalK T L ≤ A → (∀ A' ∈ cComp H, nqOriginalK T L ≤ A' → A' = A) →
        (∀ B₁ ∈ cComp H, ∀ B₂ ∈ cComp H, B₁ ≠ A → B₂ ≠ A →
          3 ∣ Nat.card (↥B₁ ⧸ CFSG.solvableRadical ↥B₁) →
          3 ∣ Nat.card (↥B₂ ⧸ CFSG.solvableRadical ↥B₂) → B₁ = B₂) ∧
        (∀ B ∈ cComp H, B ≠ A → ¬ CFSG.IsQuasisimple (↥B ⧸ CFSG.pCore 2 ↥B) →
          3 ∣ Nat.card (↥B ⧸ CFSG.solvableRadical ↥B)) ∧
        ∀ B ∈ cComp H, B ≠ A → 3 ∣ Nat.card (↥B ⧸ CFSG.solvableRadical ↥B) →
          (B.subgroupOf H).Normal ∧ T ≤ normalizer (B : Set G) ∧
          (∀ D : Subgroup G, quasithinIsLocal T D → B ≤ D → T ≤ normalizer (D : Set G)) ∧
          (¬ B ≤ M →
            quasithinIsFaithfulLocal T B ∧
            (∀ D : Subgroup G, quasithinIsLocal T D → B ≤ D →
              quasithinIsFaithfulLocal T D ∧ ¬ D ≤ M) ∧
            (∃ B' : Subgroup G, (quasithinIsMaximalLocal T B' ∧ quasithinIsFaithfulLocal T B') ∧
              B ≤ B') ∧
            ∀ B' : Subgroup G, quasithinIsMaximalLocal T B' → B ≤ B' →
              quasithinIsFaithfulLocal T B' ∧ T ≤ normalizer (B' : Set G)) := by
  intro G _ _ T L M h H hH hKTH hHM A hA hKA hAu
  classical
  have := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hTH : T ≤ H := le_sup_right.trans hKTH
  have hTs := isSylowTwoOf_of_qtnq h hTH
  have hO2 := CFSG.Quasithin.pCoreOf_ne_bot_of_isTwoLocal hH.1
  obtain ⟨R, hR⟩ := exists_originalCentralizer (h.t_le.trans h.eq_normalizer.le)
  obtain ⟨A₀, hA₀, hKA₀, -, hA₀n, -⟩ := containing_component h hR hH hKTH
  have hAA : A₀ = A := hAu A₀ hA₀ hKA₀
  rw [hAA] at hA₀n
  have hHA : H ≤ normalizer (A : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (le_of_mem_cComp hA)).mp hA₀n
  refine ⟨fun B₁ hB₁ B₂ hB₂ hB₁A hB₂A h3₁ h3₂ =>
    complementary_three_divisible_unique h hH hKTH hA hKA hB₁ hB₂ hB₁A hB₂A h3₁ h3₂,
    fun B hB _ hq => ?_, fun B hB hBA h3 => ?_⟩
  ·
    have hBloc : quasithinIsLocal T B :=
      QuasithinUnique.Vol2Native.isLocal_of_mem_cComp hO2 hTs hB
    obtain ⟨hBc, hBsqt⟩ := NQCat.isCComponent_top_and_sqt_of_isLocal h hBloc
    obtain ⟨-, -, -, -, -, -, h3⟩ :=
      (NQCat.sqt_nonquasisimple_Ccomponent_prime_linear_radical_quotient_and_no_Suzuki_section
        hBsqt hBc).1 hq
    exact h3
  · have hBH : B ≤ H := le_of_mem_cComp hB
    have hHB := complementary_three_divisible_normal h hH hKTH hA hKA hHA hB hBA h3
    have hTB : T ≤ normalizer (B : Set G) := hTH.trans hHB
    have hBloc : quasithinIsLocal T B :=
      QuasithinUnique.Vol2Native.isLocal_of_mem_cComp hO2 hTs hB
    have hTD : ∀ D : Subgroup G, quasithinIsLocal T D → B ≤ D → T ≤ normalizer (D : Set G) :=
      fun D hD hBD t ht => (local_normalizer_chain_inclusion h.simple h.nonabelian h.qtke hBloc hD
        hBD ⟨ht, hTB ht⟩).2
    refine ⟨(normal_subgroupOf_iff_le_normalizer hBH).mpr hHB, hTB, hTD, fun hBM => ?_⟩
    obtain ⟨-, -, -, -, -, -, hcl, -⟩ := containing_sylow_closure (A := A) h hH hTH
    obtain ⟨-, -, hBf, B', hB', hBB', -⟩ := hcl B hB hBM
    have hup : ∀ D : Subgroup G, quasithinIsLocal T D → B ≤ D → quasithinIsFaithfulLocal T D :=
      fun D hD hBD => local_faithfulness_upward LocDbl.local_double_embedding_exclusion h.simple
        h.nonabelian h.qtke h.sylow hD hBD hBf
    exact ⟨hBf, fun D hD hBD => ⟨hup D hD hBD, fun hDM => hBM (hBD.trans hDM)⟩, ⟨B', hB', hBB'⟩,
      fun B'' hB'' hBB'' => ⟨hup B'' hB''.1 hBB'', hTD B'' hB''.1 hBB''⟩⟩

end CFSG.Quasithin.H13.NQBlock

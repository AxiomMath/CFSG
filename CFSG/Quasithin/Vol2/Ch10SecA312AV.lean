module

public import CFSG.Quasithin.Vol2.Ch10SecA312AQ
public import CFSG.Quasithin.Vol2.Ch10SecA312AW
public import CFSG.Quasithin.Vol2.Ch10SecA312AS

public section

namespace CFSG.Quasithin.Vol2.Ch10.A312A

open CFSG.Open CFSG.SectionRank CFSG.Quasithin CFSG.QuasithinUnique

variable {X : Type} [Group X] [Finite X]

omit [Finite X] in
theorem false_of_types_of_card {B : Subgroup X} (h : A312Types B)
    {m N : ℕ} (hM : Nat.card (ModO2 B) = m) (h3 : 3 ∣ m) (h60 : m ≠ 60) (h168 : m ≠ 168)
    (hN : ¬ 2 ^ (N + 1) ∣ m) (hq : ∀ n, 1 < n → n ≤ N → 2 ^ n * ((2 ^ n) ^ 2 - 1) ≠ m) :
    False := by
  rcases h with ⟨n, hn, F, _, _, hF, ⟨e⟩⟩ | he5 | he3 | ⟨n, hSz⟩
  · rw [Nat.card_congr e.toEquiv, CFSG.LieType.HighestRoot.card_SL2, hF] at hM
    refine hq n hn (not_lt.mp fun hc => hN ?_) hM
    exact (pow_dvd_pow 2 hc).trans ⟨_, hM.symm⟩
  · obtain ⟨e⟩ := he5
    rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup,
      Fintype.card_fin] at hM
    exact h60 (by rw [← hM]; decide)
  · obtain ⟨e⟩ := he3
    rw [Nat.card_congr e.toEquiv, Matrix.card_SL_field] at hM
    exact h168 (by rw [← hM]; simp [Fin.prod_univ_three])
  · exact CFSG.RankThree.ThinCatalog.not_three_dvd_card_of_suzukiModel hSz (by rw [hM]; exact h3)

omit [Finite X] in
theorem card_modO2_of_simple {B : Subgroup X} (W : Subgroup ↥B) [W.Normal] (hW : IsPGroup 2 W)
    (hs : IsSimpleGroup (↥B ⧸ W)) (hnp : ¬ IsPGroup 2 (↥B ⧸ W)) :
    Nat.card (ModO2 B) = Nat.card (↥B ⧸ W) :=
  Nat.card_congr (QuotientGroup.quotientMulEquivOfEq
    (pCore_eq_of_isSimpleGroup W hW hs hnp)).toEquiv

theorem false_of_isHat_types {B : Subgroup X} (W : Subgroup ↥B) [W.Normal] (hW : IsPGroup 2 W)
    {S : Type} [Group S] (hH : IsHat (↥B ⧸ W) S) (h : A312Types B) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hq, hZ3, -⟩ := hH
  have hWle : W ≤ CFSG.pCore 2 ↥B :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup inferInstance hW
  have hle : CFSG.pCore 2 ↥B ≤ W := by
    set N := (CFSG.pCore 2 ↥B).map (QuotientGroup.mk' W) with hN
    have hn : N.Normal :=
      (inferInstance : (CFSG.pCore 2 ↥B).Normal).map _ (QuotientGroup.mk'_surjective W)
    have hNp : IsPGroup 2 N := (CFSG.pCore_isPGroup (p := 2) (G := ↥B)).map _
    have hbot : N = ⊥ := by
      rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hq hn with h | h
      · exfalso
        apply not_isPGroup_two_of_quasisimple hq
        rw [h] at hNp
        exact hNp.of_equiv Subgroup.topEquiv
      · obtain ⟨k, hk⟩ := (IsPGroup.iff_card).mp hNp
        have hdvd : Nat.card N ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le h
        rw [hk] at hdvd
        have hk0 : k = 0 := by
          by_contra hk0
          have h2 : 2 ∣ 3 := (dvd_pow_self 2 hk0).trans hdvd
          omega
        rw [hk0, pow_zero] at hk
        exact Subgroup.eq_bot_of_card_eq N hk
    intro x hx
    have : (QuotientGroup.mk' W x) ∈ N := ⟨x, hx, rfl⟩
    rw [hbot, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at this
    exact this
  let e₀ : ModO2 B ≃* ↥B ⧸ W := QuotientGroup.quotientMulEquivOfEq (le_antisymm hle hWle)
  have hZB : Nat.card (Subgroup.center (ModO2 B)) = 3 := by
    rw [← Subgroup.map_center_eq e₀.symm, Subgroup.card_map_of_injective e₀.symm.injective, hZ3]
  rcases center_bot_or_top_of_types h with h0 | h0
  · rw [h0, Subgroup.card_bot] at hZB
    omega
  · have htop : Subgroup.center (↥B ⧸ W) = ⊤ := by
      rw [← Subgroup.map_center_eq e₀, h0, Subgroup.map_top_of_surjective _ e₀.surjective]
    obtain ⟨a, b, hab⟩ := hq.2.2
    apply hab
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective b
    have hx : x ∈ Subgroup.center (↥B ⧸ W) := htop ▸ Subgroup.mem_top x
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, Subgroup.mem_center_iff.mp hx y]

section M23

open CFSG.Blueprint CFSG.Certificates CFSG.Sporadic.Mathieu CFSG.Sporadic.Th
  CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native

theorem card_centralizerIn_m23 :
    ∀ u ∈ NativeSporadic.M23, orderOf u = 2 →
      Nat.card (centralizerIn NativeSporadic.M23 u) = 2688 := by
  have hn : (23 : ℕ) < 2 ^ 32 := by norm_num
  have hQ : ValidSchreier m23Certificate := m23Certificate_check
  obtain ⟨hok, hsz, -⟩ := m23_oddcore_cover
  obtain ⟨hr1, hro1, hK1, hKc1, -⟩ := m23_rep_data1
  have hA : m23PermA ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  have hB : m23PermB ∈ m23Certificate.originalSubgroup := m23_gens_mem _ (by simp)
  rw [m23InvReps_eq] at hok hsz
  simp only [repSizes, List.map_cons, List.map_nil, List.cons.injEq, and_true] at hsz
  rw [← m23Certificate_originalSubgroup]
  intro u hu ho
  obtain ⟨d, hd, hcard⟩ := CFSG.QuasithinUnique.Ch1.centralizer_card_of_reps hn m23Certificate
    hQ (pairTables_spec hn hA hB) 1 (fun h hh => by simpa using hh)
    [(m23Rep1, m23CentQ1.originalSubgroup)]
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      exact ⟨by simpa using hr1, hro1⟩)
    4000 hok
    (by
      intro d hd
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
      subst hd
      refine ⟨hK1, ?_⟩
      dsimp only
      rw [hsz, hKc1, m23Certificate_originalSubgroup, m23_card])
    u (by simpa using hu) ho
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hd
  subst hd
  exact hcard.trans hKc1

theorem false_of_m23_alt5
    {T B : Subgroup X} (hT : IsPGroup 2 ↥T)
    (hM23 : IsSporadic .M23 ↥(⊤ : Subgroup X))
    (hB : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y)) {z : X} (hzT : z ∈ T)
    (hz1 : z ≠ 1) (hzB : ∀ b ∈ B, z * b = b * z) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e⟩ := hM23
  let ψ : X ≃* ↥NativeSporadic.M23 :=
    (Subgroup.topEquiv.symm : X ≃* ↥(⊤ : Subgroup X)).trans e
  obtain ⟨k, hk1, hk2⟩ := exists_involution_pow hT hzT hz1
  have hord : orderOf (z ^ k) = 2 := orderOf_eq_prime (by rw [pow_two]; exact hk2) hk1
  have htord : orderOf ((ψ (z ^ k) : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) = 2 := by
    rw [Subgroup.orderOf_coe, MulEquiv.orderOf_eq, hord]
  have hcard := card_centralizerIn_m23 _ (ψ (z ^ k)).2 htord
  obtain ⟨b, hb⟩ := exists_prime_orderOf_dvd_card' (G := ↥B) 5
    (five_dvd_card_of_isExt hB fun Y _ _ hY => five_dvd_card_of_isAlt (Or.inl rfl) hY)
  have hmem : ((ψ b : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23)) ∈
      centralizerIn NativeSporadic.M23 ((ψ (z ^ k) : ↥NativeSporadic.M23) :
        Equiv.Perm (Fin 23)) := by
    rw [centralizerIn]
    refine Subgroup.mem_inf.mpr ⟨(ψ b).2, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
    have hbu : (b : X) * z ^ k = z ^ k * b := (Commute.pow_left (hzB b b.2) k).eq.symm
    rw [← Subgroup.coe_mul, ← Subgroup.coe_mul, ← map_mul, ← map_mul, hbu]
  have h := orderOf_dvd_natCard (⟨_, hmem⟩ : ↥(centralizerIn NativeSporadic.M23
    ((ψ (z ^ k) : ↥NativeSporadic.M23) : Equiv.Perm (Fin 23))))
  rw [Subgroup.orderOf_mk, Subgroup.orderOf_coe, MulEquiv.orderOf_eq, Subgroup.orderOf_coe, hb,
    hcard] at h
  norm_num at h

end M23

theorem a312ZCentM23_of
    (hM : A312ZCentRestM23) : A312ZCentM23 := by
  intro X _ _ T B hcase hc
  have hc' := hc
  obtain ⟨-, -, -, hT, hB, -, -, htypes, ⟨z, hzT, hz1, -, hzB⟩, V, hVB, hV, hBV, hcomm, hV1, hcV,
    -⟩ := hc'
  obtain ⟨hcase, hM23⟩ := hcase
  have hW2 : ∀ {W : Subgroup ↥B} {n : ℕ}, IsE2 n ↥W → IsPGroup 2 W := fun hW w =>
    ⟨1, by rw [pow_one]; exact pow_eq_one_of_elemAbelian hW w⟩
  rcases hcase with h22 | h2 | ⟨W, hWn, hW, hY⟩ | h4 | h5 | ⟨W, hWn, hW, hY⟩ | h7
  · obtain ⟨e⟩ := h22
    have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M22) :=
      CFSG.Sporadic.Mathieu.fam_m22_simplicity.2.2
    exact false_of_simple hB e.isSimpleGroup hVB hV hBV hcomm hV1 hcV
  · exact false_of_simple hB (isSimpleGroup_of_stated h2) hVB hV hBV hcomm hV1 hcV
  · obtain ⟨eA⟩ := hY
    have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
    have hM := card_modO2_of_simple W (hW2 hW) eA.isSimpleGroup
      (not_isPGroup_quotient hB W (hW2 hW))
    have hA : Nat.card (alternatingGroup (Fin 7)) = 2520 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    rw [Nat.card_congr eA.toEquiv, hA] at hM
    exact false_of_types_of_card (N := 3) htypes hM (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by intro n h1 h2; interval_cases n <;> norm_num)
  · exact hM X T B (Or.inl h4) hM23 hc
  · exact hM X T B (Or.inr h5) hM23 hc
  · obtain ⟨eA⟩ := hY
    have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
    have hM := card_modO2_of_simple W (hW2 hW) eA.isSimpleGroup
      (not_isPGroup_quotient hB W (hW2 hW))
    have hA : Nat.card (alternatingGroup (Fin 6)) = 360 := by
      rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]
      decide
    rw [Nat.card_congr eA.toEquiv, hA] at hM
    exact false_of_types_of_card (N := 3) htypes hM (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by intro n h1 h2; interval_cases n <;> norm_num)
  · exact false_of_m23_alt5 hT.isPGroup hM23 h7 hzT hz1 hzB

theorem a312ZCentJ4_of
    (hJ : A312ZCentRestJ4) : A312ZCentJ4 := by
  intro X _ _ T B hcase hc
  have hc' := hc
  obtain ⟨-, -, -, -, hB, -, -, htypes, -, -⟩ := hc'
  obtain ⟨hJ4, hcase⟩ := hcase
  rcases hcase with ⟨W, hWn, hW, hY⟩ | ⟨W, hWn, hW, hY⟩ | h5 | hH | h42 | h3
  · have : CFSG.IsExtraspecial 2 ↥W := hW.1
    exact false_of_isHat_types W (IsPGroup.of_card hW.2) hY htypes
  · have hW2 : IsPGroup 2 W := fun w =>
      ⟨1, by rw [pow_one]; exact pow_eq_one_of_elemAbelian hW w⟩
    obtain ⟨eM⟩ := hY
    have : IsSimpleGroup (CFSG.Blueprint.NativeSporadic.Carrier .M24) :=
      CFSG.Sporadic.Mathieu.fam_m24_simplicity.2.2
    have hM := card_modO2_of_simple W hW2 eM.isSimpleGroup (not_isPGroup_quotient hB W hW2)
    rw [Nat.card_congr eM.toEquiv] at hM
    have hM' : Nat.card (ModO2 B) = 244823040 := hM.trans CFSG.Sporadic.Mathieu.card_M24
    exact false_of_types_of_card (N := 10) htypes hM' (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by intro n h1 h2; interval_cases n <;> norm_num)
  · exact hJ.1 X T B h5 hJ4 hc
  · exact false_of_hat_types (CFSG.pCore 2 ↥B) (CFSG.pCore_isPGroup (p := 2) (G := ↥B)) hH
      htypes
  · exact false_of_psl42_types (CFSG.pCore 2 ↥B) (CFSG.pCore_isPGroup (p := 2) (G := ↥B)) h42
      htypes
  · exact hJ.2 X T B h3 hJ4 hc

end CFSG.Quasithin.Vol2.Ch10.A312A

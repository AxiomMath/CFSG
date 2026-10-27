module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23H
public import CFSG.Quasithin.Vol2.Ch5Sec2M23Alt7
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123Alt7B
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246C123CentralZero
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_19IdRank
public import CFSG.LieType.SteinbergBRLieModelRankOneClassifier
public import CFSG.Quasithin.Vol2.Ch5Sec2M23L34

public section

namespace CFSG.Quasithin.H13

open MulAction CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem lin2_arith {n a : ℕ} (hn : 2 ≤ n) (h : 2 ^ n * ((2 ^ n) ^ 2 - 1) * 2 ^ a ∣ 960) :
    n = 2 ∧ a ≤ 4 := by
  set c := (2 ^ n) ^ 2 - 1 with hc
  have h4 : 4 ≤ 2 ^ n := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h16 : 16 ≤ (2 ^ n) ^ 2 := by
    calc 16 = 4 ^ 2 := by norm_num
      _ ≤ (2 ^ n) ^ 2 := Nat.pow_le_pow_left h4 2
  have hc15 : 15 ≤ c := by omega
  have hcodd : Odd c := Nat.Even.sub_odd (by omega)
    (Nat.even_pow.mpr ⟨Nat.even_pow.mpr ⟨even_two, by omega⟩, by norm_num⟩) odd_one
  have hcd : c ∣ 64 * 15 := Dvd.dvd.trans ⟨2 ^ n * 2 ^ a, by ring⟩ h
  have hc64 : Nat.Coprime c 64 := Nat.Coprime.pow_right 6 (Nat.coprime_two_right.mpr hcodd)
  have hc' : c = 15 :=
    le_antisymm (Nat.le_of_dvd (by norm_num) (hc64.dvd_of_dvd_mul_left hcd)) hc15
  have hsq : (2 ^ n) ^ 2 = 4 ^ 2 := by
    rw [show (4 : ℕ) ^ 2 = 16 by norm_num]
    omega
  have h2n : 2 ^ n = 2 ^ 2 := by
    have := Nat.pow_left_injective (by norm_num : 2 ≠ 0) hsq
    rw [this]
    norm_num
  have hn2 : n = 2 := Nat.pow_right_injective (le_refl 2) h2n
  refine ⟨hn2, ?_⟩
  rw [hn2, hc'] at h
  have h' : 2 ^ a ∣ 2 ^ 4 := by
    have : 60 * 2 ^ a ∣ 60 * 16 := by
      have e : 2 ^ 2 * 15 * 2 ^ a = 60 * 2 ^ a := by ring
      rw [e] at h
      simpa using h
    exact Nat.dvd_of_mul_dvd_mul_left (by norm_num) this
  exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h'

theorem le_normalizer_of_isLocal_of_excA7 [Finite G]
    (hK : LocalSQTK G) (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    {T K' : Subgroup G} (hloc : quasithinIsLocal T K') (hexc : CFSG.Quasithin.IsExcA7Block K') :
    T ≤ Subgroup.normalizer (K' : Set G) := by
  obtain ⟨-, hcomp, -, hO2⟩ := hloc
  have hKX : K' ≤ K' ⊔ T := le_sup_left
  rcases Vol2Native.lemma_1_2_1_three hK h37 h38 hO2 hcomp with hn | ⟨-, hA⟩
  · exact le_sup_right.trans ((Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mp hn)
  · exfalso
    obtain ⟨-, ⟨α, hα, hαker⟩, -⟩ := hexc
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    let e : (↥K' ⧸ CFSG.pCore 2 ↥K') ≃* ↥(alternatingGroup (Fin 7)) :=
      (QuotientGroup.quotientMulEquivOfEq hαker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)
    have h1 := CFSG.QuasithinUnique.Id2519.lemma122Rank _ hA 3 Nat.prime_three (by norm_num)
    have h2 := C1GN.two_le_pRank_alt7
    rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at h1 h2
    rw [CFSG.LieType.SteinbergBR.RankOneClassifier.pRank_eq_of_mulEquiv e 3] at h1
    omega

theorem pCoreOf_le_of_card_eq [Finite G]
    {X U K : Subgroup G} {π : ↥X →* Equiv.Perm (Fin 7)}
    (hker : π.ker = U.subgroupOf X) (hrange : π.range = alternatingGroup (Fin 7))
    (hU2 : IsPGroup 2 U) (hKX : K ≤ X) (hUN : X ≤ Subgroup.normalizer (U : Set G)) {n : ℕ}
    (hn : 2 ≤ n)
    (hcardK : Nat.card K = 2 ^ n * ((2 ^ n) ^ 2 - 1) * Nat.card ↥(pCoreOf 2 K)) :
    n = 2 ∧ Nat.card ((K.subgroupOf X).map π) = 60 ∧ pCoreOf 2 K ≤ U := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 K with hQdef
  have hQK : Q ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hmapA : ∀ Y : Subgroup G, (Y.subgroupOf X).map π ≤ alternatingGroup (Fin 7) :=
    fun Y => hrange ▸ Subgroup.map_le_range π _
  set A := (K.subgroupOf X).map π with hAdef
  have hA := card_map_mul_card_inf hker hKX
  have hKN : ∀ k ∈ K, ∀ x ∈ K ⊓ U, k * x * k⁻¹ ∈ K ⊓ U := by
    intro k hk x hx
    obtain ⟨hxK, hxU⟩ := Subgroup.mem_inf.mp hx
    refine Subgroup.mem_inf.mpr ⟨K.mul_mem (K.mul_mem hk hxK) (K.inv_mem hk), ?_⟩
    exact (Subgroup.mem_normalizer_iff.mp (hUN (hKX hk)) x).mp hxU
  have hKUQ : K ⊓ U ≤ Q := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_ ?_
    · intro k hk
      rw [Subgroup.mem_normalizer_iff]
      intro x
      refine ⟨fun hx => hKN k hk x hx, fun hx => ?_⟩
      have := hKN k⁻¹ (K.inv_mem hk) _ hx
      simpa [mul_assoc] using this
    · exact hU2.to_le inf_le_right
  set j := (K ⊓ U).relIndex Q with hjdef
  have hjq : j * Nat.card ↥(K ⊓ U) = Nat.card Q := by
    have h2 := Subgroup.relIndex_mul_card (H := K ⊓ U) (K := Q)
    rwa [inf_of_le_left hKUQ] at h2
  obtain ⟨e, he⟩ := IsPGroup.iff_card.mp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  obtain ⟨i, hi⟩ : ∃ i, j = 2 ^ i := by
    have hjd : j ∣ 2 ^ e := he ▸ Dvd.intro _ hjq
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hjd
    exact ⟨i, hi⟩
  have hb0 : 0 < Nat.card ↥(K ⊓ U) := Nat.card_pos
  have haA : Nat.card A = 2 ^ n * ((2 ^ n) ^ 2 - 1) * 2 ^ i := by
    have h3 : Nat.card A * Nat.card ↥(K ⊓ U) =
        2 ^ n * ((2 ^ n) ^ 2 - 1) * 2 ^ i * Nat.card ↥(K ⊓ U) := by
      rw [hA, hcardK, ← hjq, hi]
      ring
    exact Nat.eq_of_mul_eq_mul_right hb0 h3
  have hAdvd : Nat.card A ∣ 2520 := by
    have := Subgroup.card_dvd_of_le (hmapA K)
    rwa [card_alternatingGroup_seven] at this
  rcases card_cases_of_dvd_card_A7 hn haA hAdvd with ⟨rfl, hi01⟩ | h504
  · rcases hi01 with rfl | rfl
    ·
      refine ⟨rfl, by rw [haA]; norm_num, ?_⟩
      have hj1 : j = 1 := by rw [hi]; norm_num
      have hKUeq : K ⊓ U = Q := Subgroup.eq_of_le_of_card_ge hKUQ
        (by rw [← hjq, hj1, one_mul])
      rw [← hKUeq]
      exact inf_le_right
    ·
      exfalso
      set Bq := (Q.subgroupOf X).map π with hBq
      have hB := card_map_mul_card_inf hker (hQK.trans hKX)
      have hQU : Q ⊓ U = K ⊓ U :=
        le_antisymm (inf_le_inf_right _ hQK) (le_inf hKUQ inf_le_right)
      rw [hQU, ← hjq, hi] at hB
      have hB2 : Nat.card Bq = 2 := Nat.eq_of_mul_eq_mul_right hb0 (by rw [hB]; norm_num)
      obtain ⟨y, hy1, hyu⟩ := (Nat.card_eq_two_iff' (1 : Bq)).mp hB2
      have hQnK : ∀ k ∈ K, ∀ x ∈ Q, k * x * k⁻¹ ∈ Q := fun k hk x hx =>
        (Subgroup.mem_normalizer_iff.mp
          ((Subgroup.le_normalizer.trans
            (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)) hk) x).mp hx
      have hconj : ∀ a ∈ A, ∀ b ∈ Bq, a * b * a⁻¹ ∈ Bq := by
        rintro _ ⟨k, hk, rfl⟩ _ ⟨x, hx, rfl⟩
        refine ⟨k * x * k⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
        simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        exact hQnK _ (Subgroup.mem_subgroupOf.mp hk) _ (Subgroup.mem_subgroupOf.mp hx)
      have hcomm : ∀ a ∈ A, (y : Equiv.Perm (Fin 7)) * a = a * y := by
        intro a ha
        have hmem : a * (y : Equiv.Perm (Fin 7)) * a⁻¹ ∈ Bq := hconj a ha y y.2
        have hne : (⟨_, hmem⟩ : Bq) ≠ 1 := by
          intro h1
          apply hy1
          have h2 := congrArg Subtype.val h1
          simp only [OneMemClass.coe_one] at h2
          apply Subtype.ext
          simp only [OneMemClass.coe_one]
          have h3 : a * (y : Equiv.Perm (Fin 7)) = a := by
            calc a * (y : Equiv.Perm (Fin 7)) = a * (y : Equiv.Perm (Fin 7)) * a⁻¹ * a := by
                  group
              _ = a := by rw [h2, one_mul]
          exact mul_eq_left.mp h3
        have h4 := hyu _ hne
        have h5 := congrArg Subtype.val h4
        simp only at h5
        calc (y : Equiv.Perm (Fin 7)) * a = a * (y : Equiv.Perm (Fin 7)) * a⁻¹ * a := by
              rw [h5]
          _ = a * y := by group
      have hyy : (y : Equiv.Perm (Fin 7)) * y = 1 := by
        by_contra hyy
        have hmem : (y : Equiv.Perm (Fin 7)) * y ∈ Bq := Bq.mul_mem y.2 y.2
        have hne : (⟨_, hmem⟩ : Bq) ≠ 1 := fun h1 => hyy (congrArg Subtype.val h1)
        have h4 := congrArg Subtype.val (hyu _ hne)
        simp only at h4
        apply hy1
        apply Subtype.ext
        simp only [OneMemClass.coe_one]
        exact mul_eq_right.mp h4
      have hyA : (y : Equiv.Perm (Fin 7)) ∈ alternatingGroup (Fin 7) := hmapA Q y.2
      have hy1' : (y : Equiv.Perm (Fin 7)) ≠ 1 := fun h1 => hy1 (Subtype.ext h1)
      have hle := card_le_of_le_centralizer (hmapA K) hyA hy1' hyy hcomm
      rw [haA] at hle
      norm_num at hle
  · exact absurd h504 (card_ne_504 (hmapA K))

theorem card_right_eq_960_of_isAmalgamOfGroup
    {G1 G2 : Subgroup G}
    (hα : IsAmalgamOfGroup (RankTwoAmalgam.ofSubgroups G1 G2) (IsLieOverTwo .PSL 3 2)) :
    Nat.card G2 = 960 := by
  rcases isParabolicIsoData_of_isAmalgamOfGroup hα with ⟨-, φ₂, -, -⟩ | ⟨φ₁, -, -, -⟩
  · rw [← Nat.card_congr φ₂.toEquiv, M22Witt.card_m22PtHexStab]
  · rw [← Nat.card_congr φ₁.toEquiv, Asc94.card_m22TwoStab]

theorem stmt5_2_8_Q_of
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) (h526 : Stmt5_2_6)
    (h1284 : Lemma128Four) (hSz : Stmt5_2_8_Sz) (hU4 : Stmt5_2_8_U4)
    (hsp : Stmt5_2_8_special) : Stmt5_2_8_Q := by
  intro G _ _ T M L V H B D L₂ n K' hyp hM23 hlt hmax hexc
  have h := hyp.toHyp5_0_1
  have : IsSimpleGroup G := h.simple
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set K := oTwoUpper H with hKdef
  set Q := pCoreOf 2 K with hQdef
  set W := pCoreOf 2 K' with hWdef
  have hKK' : K ≤ K' := hlt.le
  have hQ2 : IsPGroup 2 Q := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hW2 : IsPGroup 2 W := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K'
  have hK'N : K' ≤ Subgroup.normalizer (W : Set G) :=
    Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K')
  have hLin := isLin2Type_oTwoUpper_of h526 h1284 hSz hU4 hsp hyp hM23 hlt hmax
  have hcardK := card_eq_of_isLin2Type hLin
  have hG2 : Nat.card ↥(D ⊔ (sec52S M H ⊓ L) ⊔ K) = 960 :=
    card_right_eq_960_of_isAmalgamOfGroup hM23.1
  have hKdvd : Nat.card K ∣ 960 := hG2 ▸ Subgroup.card_dvd_of_le le_sup_right
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hQ2
  obtain ⟨hn2, ha4⟩ := lin2_arith h.two_le (by rw [← ha, ← hcardK]; exact hKdvd)
  have hUQ : blockU K ≤ Q := by
    show ⁅pCoreOf 2 K, K⁆ ≤ pCoreOf 2 K
    rw [Subgroup.commutator_le]
    intro q hq k hk
    have hKN : K ≤ Subgroup.normalizer (Q : Set G) :=
      Subgroup.le_normalizer.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K)
    have h1 : k * q⁻¹ * k⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hKN hk) _).mp (Q.inv_mem hq)
    rw [commutatorElement_def]
    have h2 := Q.mul_mem hq h1
    simpa [mul_assoc] using h2
  have hU16 : 16 ≤ Nat.card ↥(blockU K) := by
    obtain ⟨F, _, _, hF, -, -, -, β, hβ, -, -⟩ := hLin
    have h1 := Nat.card_le_card_of_surjective β hβ
    rw [Nat.card_eq_fintype_card (α := Multiplicative (Fin 2 → F)), Fintype.card_multiplicative,
      Fintype.card_fun, Fintype.card_fin, hF, hn2] at h1
    simpa using h1
  have hcardQ : Nat.card Q = 16 := by
    have h1 := (hU16.trans (Subgroup.card_le_of_le hUQ))
    have h2 : 2 ^ a ≤ 16 := by
      calc 2 ^ a ≤ 2 ^ 4 := Nat.pow_le_pow_right (by norm_num) ha4
        _ = 16 := by norm_num
    rw [ha] at h1 ⊢
    omega
  have hTN : T ≤ Subgroup.normalizer (K' : Set G) :=
    le_normalizer_of_isLocal_of_excA7 (CFSG.QuasithinUnique.qtkeCore_of_cat h.nonabelian h.qtke).1
      h37 h38 hmax.1 hexc
  obtain ⟨hsh, ⟨α, hα, hαker⟩, hidx⟩ := hexc
  set π : ↥K' →* Equiv.Perm (Fin 7) := (alternatingGroup (Fin 7)).subtype.comp α with hπ
  have hker : π.ker = W.subgroupOf K' := by
    rw [hπ, MonoidHom.ker_comp_of_injective _ _ (Subgroup.subtype_injective _), hαker, hWdef, pCoreOf, ← Subgroup.comap_subtype,
      Subgroup.comap_map_eq_self_of_injective (Subgroup.subtype_injective _)]
  have hrange : π.range = alternatingGroup (Fin 7) := by
    rw [hπ, MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hα, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  obtain ⟨-, -, hQW⟩ := pCoreOf_le_of_card_eq hker hrange hW2 hKK' hK'N h.two_le hcardK
  obtain ⟨-, -, -, -, -, -, hKT, hab⟩ := h526 G T M L V H B D L₂ n hyp
  have hKS : pCoreOf 2 (K ⊔ sec52S M H) = Q := by
    rcases hab with ⟨-, -, -, h1⟩ | ⟨m, -, h2n, -⟩
    · exact h1
    · omega
  have hXN : K' ⊔ T ≤ Subgroup.normalizer (K' : Set G) := sup_le Subgroup.le_normalizer hTN
  have hXW : K' ⊔ T ≤ Subgroup.normalizer (W : Set G) :=
    hXN.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K')
  have hTs : IsSylowTwoOf T (K' ⊔ T) := isSylowTwoOf_of_isSylowTwo hyp.sylow le_sup_right
  have hWX : W ≤ K' ⊔ T := (CFSG.LieType.BorelTits.pCoreOf_le 2 K').trans le_sup_left
  have hWT : W ≤ T := CFSG.Quasithin.IsSylowIn.le_of_normal ⟨hTs.1, hTs.2.1, hTs.2.2⟩ hWX
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hWX).mpr hXW) hW2
  have hKTN : K ⊔ T ≤ Subgroup.normalizer (W : Set G) :=
    sup_le (hKK'.trans hK'N) (le_sup_right.trans hXW)
  have hWKT : W ≤ pCoreOf 2 (K ⊔ T) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hWT.trans le_sup_right) hKTN hW2
  rw [hKT, hKS] at hWKT
  have hWQ : W = Q := le_antisymm hWKT hQW
  have hZ := CFSG.QuasithinUnique.L246.C123.blockZ_eq_bot_of_isExcA7Block
    ⟨hsh, ⟨α, hα, hαker⟩, hidx⟩
  have hcardU' : Nat.card ↥(blockU K') = 16 := by
    rw [hZ, Subgroup.bot_subgroupOf, Subgroup.index_bot] at hidx
    rw [hidx]
    norm_num
  have hcardW : Nat.card W = 16 := by rw [hWQ, hcardQ]
  have hUW : blockU K' = W :=
    Subgroup.eq_of_le_of_card_ge (CFSG.QuasithinUnique.C1.blockU_le_blockQ hsh)
      (by rw [hcardW, hcardU'])
  have hWab : IsElemAbelian 2 W := by
    refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩
    · have ha' : (a : G) ∈ blockU K' := by rw [hUW]; exact a.2
      have hb' : (b : G) ∈ blockU K' := by rw [hUW]; exact b.2
      exact CFSG.QuasithinUnique.C1.blockU_comm hsh a ha' b
        (CFSG.QuasithinUnique.C1.blockU_le_blockQ hsh hb')
    · have hx' : x ∈ blockU K' := by rw [hUW]; exact hx
      exact CFSG.QuasithinUnique.C1.blockU_sq hsh x hx'
  refine ⟨hWab, hcardW, ?_⟩
  set N := Subgroup.normalizer (W : Set G) with hNdef
  have hW1 : W ≠ ⊥ := by
    intro hb
    rw [hb, Subgroup.card_bot] at hcardW
    norm_num at hcardW
  have hWN : W ≤ pCoreOf 2 N :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hW2
  have hTNW : T ≤ N := le_sup_right.trans hXW
  have hInH : InH T N := ⟨hTNW, fun hb => hW1 (eq_bot_iff.mpr (hb ▸ hWN))⟩
  have hchar := charTwo_of_inH' h.qtke hyp.sylow hInH
  have hO2N : pCoreOf 2 N = W := by
    refine le_antisymm ?_ hWN
    have hTsN : IsSylowTwoOf T N := isSylowTwoOf_of_isSylowTwo hyp.sylow hTNW
    have hPN : pCoreOf 2 N ≤ N := CFSG.LieType.BorelTits.pCoreOf_le 2 N
    have hPT : pCoreOf 2 N ≤ T := CFSG.Quasithin.IsSylowIn.le_of_normal
      ⟨hTsN.1, hTsN.2.1, hTsN.2.2⟩ hPN
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hPN).mpr
        (Subgroup.le_normalizer.trans
          (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N)))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    have hKTN' : K ⊔ T ≤ Subgroup.normalizer (pCoreOf 2 N : Set G) :=
      hKTN.trans (Subgroup.le_normalizer.trans
        (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 N))
    have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hPT.trans le_sup_right) hKTN'
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 N)
    rw [hKT, hKS, ← hWQ] at h1
    exact h1
  unfold CharTwo at hchar
  rw [hO2N] at hchar
  have hcommW : ∀ a b : ↥W, a * b = b * a := fun a b => hWab.1.1.comm a b
  let _ : CommGroup ↥W := { (inferInstance : Group ↥W) with mul_comm := hcommW }
  have hW2' : ∀ w : ↥W, w ^ 2 = 1 := fun w =>
    Subtype.ext (by rw [Subgroup.coe_pow, Subgroup.coe_one]; exact hWab.2 w w.2)
  set X := K' ⊔ T with hXdef
  let φ : ↥X →* MulAut ↥W := (Subgroup.normalizerMonoidHom W).comp (Subgroup.inclusion hXW)
  have hφ : ∀ (g : ↥X) (w : ↥W), ((φ g w : ↥W) : G) = g * w * (g : G)⁻¹ := fun g w => rfl
  have hkerφ : ∀ g : ↥X, φ g = 1 → (g : G) ∈ W := by
    intro g hg
    have hc : (g : G) ∈ N ⊓ Subgroup.centralizer (W : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨hXW g.2, Subgroup.mem_centralizer_iff.mpr fun w hw => ?_⟩
      have h1 := congrArg (fun f : MulAut ↥W => ((f ⟨w, hw⟩ : ↥W) : G)) hg
      simp only [hφ, MulAut.one_apply] at h1
      calc w * (g : G) = (g : G) * w * (g : G)⁻¹ * g := by rw [h1]
        _ = g * w := by group
    exact hchar hc
  set Λ := (K'.subgroupOf X).map φ with hΛdef
  have hcardK' : Nat.card K' = 2520 * 16 := by
    have h1 := card_eq_card_modO2_mul K'
    have h2 : Nat.card (↥K' ⧸ CFSG.pCore 2 ↥K') = 2520 := by
      rw [← card_alternatingGroup_seven]
      exact Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hαker.symm).trans
        (QuotientGroup.quotientKerEquivOfSurjective α hα)).toEquiv
    have hW16 : Nat.card ↥(pCoreOf 2 K') = 16 := hcardW
    rw [h1, h2, hW16]
  have hcardΛ : Nat.card Λ = 2520 := by
    let ψ := φ.domRestrict (K'.subgroupOf X)
    have h1 : Nat.card ψ.range = ψ.ker.index := (Subgroup.index_ker ψ).symm
    rw [MonoidHom.domRestrict_range] at h1
    have h2 := Subgroup.card_mul_index ψ.ker
    have hmem : ∀ k : ↥(K'.subgroupOf X), k ∈ ψ.ker ↔ ((k : X) : G) ∈ W := by
      intro k
      rw [MonoidHom.mem_ker, MonoidHom.domRestrict_apply]
      constructor
      · exact hkerφ _
      · intro hk
        refine MulEquiv.ext fun w => Subtype.ext ?_
        rw [hφ, MulAut.one_apply]
        have h3 : ((k : X) : G) * w = w * ((k : X) : G) := congrArg Subtype.val (hcommW ⟨_, hk⟩ w)
        rw [h3, mul_inv_cancel_right]
    have h3 : Nat.card ψ.ker = 16 := by
      rw [← hcardW]
      refine Nat.card_congr
        { toFun := fun k => ⟨(((k : ↥(K'.subgroupOf X)) : X) : G), (hmem k).mp k.2⟩
          invFun := fun w => ⟨⟨⟨w, (CFSG.LieType.BorelTits.pCoreOf_le 2 K').trans le_sup_left w.2⟩,
            Subgroup.mem_subgroupOf.mpr ((CFSG.LieType.BorelTits.pCoreOf_le 2 K') w.2)⟩,
            (hmem _).mpr w.2⟩
          left_inv := fun k => rfl
          right_inv := fun w => rfl }
    have h4 : Nat.card ↥(K'.subgroupOf X) = 2520 * 16 := by
      rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv, hcardK']
    rw [hΛdef, h1]
    have h5 : ψ.ker.index * Nat.card ψ.ker = 2520 * 16 := by rw [mul_comm, h2, h4]
    rw [h3] at h5
    exact Nat.eq_of_mul_eq_mul_right (by norm_num) h5
  have hNΛ := CFSG.QuasithinUnique.L246.C123.normalizer_eq_of_card_2520 hW2'
    (by rw [hcardW]) hcardΛ
  intro t ht
  have htX : t ∈ X := Subgroup.mem_sup_right ht
  have hφt : φ ⟨t, htX⟩ ∈ Λ := by
    rw [← hNΛ, Subgroup.mem_normalizer_iff]
    intro f
    constructor
    · rintro ⟨k, hk, rfl⟩
      refine ⟨⟨t, htX⟩ * k * ⟨t, htX⟩⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp [map_mul, map_inv]⟩
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      exact (Subgroup.mem_normalizer_iff.mp (hTN ht) _).mp (Subgroup.mem_subgroupOf.mp hk)
    · rintro ⟨k, hk, hkf⟩
      refine ⟨⟨t, htX⟩⁻¹ * k * ⟨t, htX⟩, Subgroup.mem_subgroupOf.mpr ?_, ?_⟩
      · simp only [Subgroup.coe_mul, Subgroup.coe_inv]
        have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hTN ht)) _).mp
          (Subgroup.mem_subgroupOf.mp hk)
        simpa using h1
      · rw [map_mul, map_mul, hkf, map_inv]
        group
  obtain ⟨k, hk, hkt⟩ := hφt
  have hk' : ((k : X) : G) ∈ K' := Subgroup.mem_subgroupOf.mp hk
  have hd : φ (k⁻¹ * ⟨t, htX⟩) = 1 := by rw [map_mul, map_inv, hkt, inv_mul_cancel]
  have hdW := hkerφ _ hd
  have hdK' : ((k⁻¹ * ⟨t, htX⟩ : ↥X) : G) ∈ K' := (CFSG.LieType.BorelTits.pCoreOf_le 2 K') hdW
  have e : t = (k : G) * ((k⁻¹ * ⟨t, htX⟩ : ↥X) : G) := by
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    group
  rw [e]
  exact K'.mul_mem hk' hdK'

end CFSG.Quasithin.H13

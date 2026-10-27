module

public import CFSG.Quasithin.Vol2.Ch3Sec3Obs3324
public import CFSG.Quasithin.EmptyFaithful.LRed3Four

public section

namespace CFSG.Quasithin.H13

open CFSG.Open hiding StatedSL StatedSp StatedProj
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank

namespace L3316

theorem odd_two_pow_mul_sub_one {n k : ℕ} (hn : 1 ≤ n) (hk : 1 ≤ k) : Odd (2 ^ (n * k) - 1) :=
  SzN15.odd_two_pow_sub_one (Nat.one_le_iff_ne_zero.mpr (Nat.mul_ne_zero (by omega) (by omega)))

theorem exp_eq_of_mul {a b u w c : ℕ} (hc : c = 1 ∨ c = 3) (hu : Odd u) (hw : Odd w)
    (h : c * (2 ^ a * u) = 2 ^ b * w) : a = b :=
  SzN15.two_pow_mul_odd_inj (SzN15.odd_mul_c hc hu) hw (by rw [← h]; ring)

theorem sp4_ne_sl3 {n m c : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hc : c = 1 ∨ c = 3)
    (h : c * (2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1))) =
      2 ^ (m * 3) * ((2 ^ (m * 2) - 1) * (2 ^ (m * 3) - 1))) : False := by
  have he := exp_eq_of_mul hc
    ((odd_two_pow_mul_sub_one hn (by norm_num)).mul (odd_two_pow_mul_sub_one hn (by norm_num)))
    ((odd_two_pow_mul_sub_one hm (by norm_num)).mul (odd_two_pow_mul_sub_one hm (by norm_num))) h
  obtain ⟨j, rfl, rfl⟩ : ∃ j, n = 3 * j ∧ m = 4 * j := ⟨n / 3, by omega, by omega⟩
  have hj : 1 ≤ j := by omega
  have e1 : 2 ^ (3 * j * 4) = 2 ^ (4 * j * 3) := by rw [show 3 * j * 4 = 4 * j * 3 by ring]
  rw [e1] at h
  have hpos : 0 < 2 ^ (4 * j * 3) * (2 ^ (4 * j * 3) - 1) := by
    have h1 : 2 ≤ 2 ^ (4 * j * 3) :=
      calc 2 = 2 ^ 1 := by norm_num
        _ ≤ 2 ^ (4 * j * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
    exact Nat.mul_pos (by positivity) (by omega)
  have h2 : c * (2 ^ (3 * j * 2) - 1) = 2 ^ (4 * j * 2) - 1 := by
    apply Nat.eq_of_mul_eq_mul_left hpos
    calc 2 ^ (4 * j * 3) * (2 ^ (4 * j * 3) - 1) * (c * (2 ^ (3 * j * 2) - 1))
        = c * (2 ^ (4 * j * 3) * ((2 ^ (3 * j * 2) - 1) * (2 ^ (4 * j * 3) - 1))) := by ring
      _ = 2 ^ (4 * j * 3) * ((2 ^ (4 * j * 2) - 1) * (2 ^ (4 * j * 3) - 1)) := h
      _ = 2 ^ (4 * j * 3) * (2 ^ (4 * j * 3) - 1) * (2 ^ (4 * j * 2) - 1) := by ring
  have hx : 1 ≤ 2 ^ (3 * j * 2) := Nat.one_le_two_pow
  have hy : 4 * 2 ^ (3 * j * 2) ≤ 2 ^ (4 * j * 2) := by
    have e2 : 2 ^ (4 * j * 2) = 2 ^ (3 * j * 2) * 2 ^ (2 * j) := by
      rw [← pow_add]; congr 1; ring
    have h4 : 4 ≤ 2 ^ (2 * j) :=
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ (2 * j) := Nat.pow_le_pow_right (by norm_num) (by omega)
    rw [e2, mul_comm]
    exact Nat.mul_le_mul_left _ h4
  rcases hc with rfl | rfl <;> omega

theorem g2_ne_sl3 {n m c : ℕ} (hn : 1 ≤ n) (hm : 1 ≤ m) (hc : c = 1 ∨ c = 3)
    (h : c * (2 ^ (n * 6) * ((2 ^ (n * 6) - 1) * (2 ^ (n * 2) - 1))) =
      2 ^ (m * 3) * ((2 ^ (m * 2) - 1) * (2 ^ (m * 3) - 1))) : False := by
  have he := exp_eq_of_mul hc
    ((odd_two_pow_mul_sub_one hn (by norm_num)).mul (odd_two_pow_mul_sub_one hn (by norm_num)))
    ((odd_two_pow_mul_sub_one hm (by norm_num)).mul (odd_two_pow_mul_sub_one hm (by norm_num))) h
  obtain rfl : m = 2 * n := by omega
  have hr : 2 ≤ 2 ^ n :=
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  apply SzN15.key_g2 (2 ^ n) c hr hc
  have e6 : (2 ^ n) ^ 6 = 2 ^ (n * 6) := by rw [← pow_mul]
  have e4 : (2 ^ n) ^ 4 = 2 ^ (2 * n * 2) := by
    rw [← pow_mul, show n * 4 = 2 * n * 2 by ring]
  have e2 : (2 ^ n) ^ 2 = 2 ^ (n * 2) := by rw [← pow_mul]
  have e3 : 2 ^ (2 * n * 3) = 2 ^ (n * 6) := by rw [show 2 * n * 3 = n * 6 by ring]
  rw [e6, e4, e2]
  rw [e3] at h
  exact h

theorem sl3_ge {n : ℕ} (hn : 2 ≤ n) :
    60480 ≤ 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
  have h3 : 64 ≤ 2 ^ (n * 3) :=
    calc 64 = 2 ^ 6 := by norm_num
      _ ≤ 2 ^ (n * 3) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 16 ≤ 2 ^ (n * 2) :=
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (n * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 60480 = 64 * (15 * 63) := by norm_num
    _ ≤ 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) :=
      Nat.mul_le_mul h3 (Nat.mul_le_mul (by omega) (by omega))

theorem sp4_ge {n : ℕ} (hn : 2 ≤ n) :
    979200 ≤ 2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1)) := by
  have h4 : 256 ≤ 2 ^ (n * 4) :=
    calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ (n * 4) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 16 ≤ 2 ^ (n * 2) :=
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (n * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 979200 = 256 * (15 * 255) := by norm_num
    _ ≤ 2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1)) :=
      Nat.mul_le_mul h4 (Nat.mul_le_mul (by omega) (by omega))

theorem g2_ge {n : ℕ} (hn : 2 ≤ n) :
    979200 ≤ 2 ^ (n * 6) * ((2 ^ (n * 6) - 1) * (2 ^ (n * 2) - 1)) := by
  have h6 : 4096 ≤ 2 ^ (n * 6) :=
    calc 4096 = 2 ^ 12 := by norm_num
      _ ≤ 2 ^ (n * 6) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have h2 : 16 ≤ 2 ^ (n * 2) :=
    calc 16 = 2 ^ 4 := by norm_num
      _ ≤ 2 ^ (n * 2) := Nat.pow_le_pow_right (by norm_num) (by omega)
  calc 979200 ≤ 4096 * (4095 * 15) := by norm_num
    _ ≤ 2 ^ (n * 6) * ((2 ^ (n * 6) - 1) * (2 ^ (n * 2) - 1)) :=
      Nat.mul_le_mul h6 (Nat.mul_le_mul (by omega) (by omega))

theorem le_eight_of_dvd {k : ℕ} (h : 2 ^ k ∣ 979200) : k ≤ 8 := by
  by_contra hk
  have h9 : 2 ^ 9 ∣ 979200 := (pow_dvd_pow 2 (by omega)).trans h
  norm_num at h9

section Models

variable {X Y : Type} [Group X] [Group Y]

theorem isPSL3_of_equiv {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n)
    (hK : Nat.card K = 2 ^ n) (e : X ≃* StatedProj (StatedSL 3 K)) : IsPSL 3 2 n X :=
  ⟨⟨Nat.prime_two, hn, by norm_num, fun h => absurd (congrArg Prod.fst h) (by norm_num),
    fun h => absurd (congrArg Prod.fst h) (by norm_num)⟩, K, inferInstance, inferInstance, hK,
    ⟨e⟩⟩

theorem isPSL3_of_cover (hY : CFSG.IsQuasisimple Y)
    (cq : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) (e : Y ≃* StatedSL 3 K) :
    IsPSL 3 2 n (X ⧸ Subgroup.center X) := by
  obtain ⟨eY⟩ := lred3_cq_stated hY (StatedSL 3 K)
    (lred3_simple_statedProj_sl (by norm_num) (Or.inl le_rfl)) e.symm.toMonoidHom
    e.symm.surjective
  exact isPSL3_of_equiv hn hK (cq.trans eY)

theorem isPSp4_of_equiv {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) (e : X ≃* StatedProj (StatedSp 2 K)) : IsPSp4 2 n X := by
  have h4 : 4 ≤ 2 ^ n :=
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  refine ⟨⟨Nat.prime_two, by omega, le_rfl, ?_⟩, K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  intro h
  have h2 : 2 ^ n = 2 := congrArg Prod.snd h
  omega

theorem isPSp4_of_cover (hY : CFSG.IsQuasisimple Y)
    (cq : X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y) {K : Type} [Field K] [Finite K]
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (e : Y ≃* StatedSp 2 K) :
    IsPSp4 2 n (X ⧸ Subgroup.center X) := by
  have h4 : 4 ≤ Nat.card K := by
    rw [hK]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  obtain ⟨eY⟩ := lred3_cq_stated hY (StatedSp 2 K)
    (CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K 2 (by norm_num)
      (Or.inl (Or.inr h4))) e.symm.toMonoidHom e.symm.surjective
  exact isPSp4_of_equiv hn hK (cq.trans eY)

end Models

theorem card_sl3 {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(StatedSL 3 K) = 2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
  rw [CFSG.SectionRank.OddCover.card_statedSL_three, hK, ← pow_mul, ← pow_mul, mul_assoc]

theorem card_sp4 {K : Type} [Field K] [Finite K] {n : ℕ} (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(StatedSp 2 K) = 2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1)) := by
  rw [CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num), hK, ← pow_mul,
    ← pow_mul, ← pow_mul]
  norm_num

theorem card_g2 {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n) :
    Nat.card ↥(quasithinG2 K) = 2 ^ (n * 6) * ((2 ^ (n * 6) - 1) * (2 ^ (n * 2) - 1)) := by
  have : CharP K 2 := CFSG.Quasithin.Vol2.KGNat.charP_two_of_card (by omega) hK
  rw [CFSG.QuasithinUnique.Bridge.Alt57Model.quasithinG2_eq_cayleyGroup,
    CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup, hK, ← pow_mul, ← pow_mul]

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem card_quot_eq {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G)) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) =
      Nat.card ↥(autOn L W) * Nat.card (S153D.autOnQuot hLW hker).ker := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (S153D.autOnQuot hLW hker).ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective _
      (S153D.autOnQuot_surjective hLW hker)).toEquiv]

omit [Finite G] in
theorem card_dvd {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G)) :
    Nat.card ↥(autOn L W) ∣ Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) :=
  ⟨_, card_quot_eq hLW hker⟩

omit [Finite G] in
theorem exists_mul_card_sl3 {L W : Subgroup G} (hLW : L ≤ Subgroup.normalizer (W : Set G))
    (hker : pCoreOf 2 L ≤ Subgroup.centralizer (W : Set G))
    (hnt : ¬ L ≤ Subgroup.centralizer (W : Set G))
    (hq : CFSG.IsQuasisimple (↥L ⧸ CFSG.pCore 2 ↥L)) {F : Type} [Field F] [Finite F]
    (e : (↥L ⧸ CFSG.pCore 2 ↥L) ≃* ↥(StatedSL 3 F)) :
    ∃ c : ℕ, (c = 1 ∨ c = 3) ∧ c * Nat.card ↥(autOn L W) = Nat.card ↥(StatedSL 3 F) := by
  set ρ := S153D.autOnQuot hLW hker with hρ
  have hcent : ρ.ker ≤ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
    CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple hq
      (S153D.exists_autOnQuot_ne_one hLW hker hnt)
  have hdvd : Nat.card ρ.ker ∣ Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
    Subgroup.card_dvd_of_le hcent
  have hZ : Nat.card (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) = Nat.gcd (Nat.card F - 1) 3 := by
    rw [Nat.card_congr (Subgroup.centerCongr e).toEquiv,
      ← Nat.card_congr (Subgroup.centerCongr (specialLinearGroupEquivStatedSL 3 F)).toEquiv,
      CFSG.RankThree.SubgroupLists.card_center_sl3]
  have h3 : Nat.card ρ.ker ∣ 3 := hdvd.trans (hZ ▸ Nat.gcd_dvd_right _ _)
  refine ⟨Nat.card ρ.ker, (Nat.dvd_prime Nat.prime_three).mp h3, ?_⟩
  rw [mul_comm, ← card_quot_eq hLW hker, Nat.card_congr e.toEquiv]

theorem not_le_centralizer_of_one_lt {L W : Subgroup G}
    (hLW : L ≤ Subgroup.normalizer (W : Set G)) (h : 1 < Nat.card ↥(autOn L W)) :
    ¬ L ≤ Subgroup.centralizer (W : Set G) := by
  intro hL
  have : Nontrivial ↥(autOn L W) := Finite.one_lt_card_iff_nontrivial.mp h
  obtain ⟨a, b, hab⟩ := exists_pair_ne ↥(autOn L W)
  obtain ⟨x, rfl⟩ := S153D.autOnHom_surjective hLW a
  obtain ⟨y, rfl⟩ := S153D.autOnHom_surjective hLW b
  rw [(S153D.autOnHom_eq_one_iff hLW x).mpr (hL x.2),
    (S153D.autOnHom_eq_one_iff hLW y).mpr (hL y.2)] at hab
  exact hab rfl

omit [Finite G] in
theorem card_le_of_small_block {L : Subgroup G}
    (hb : CFSG.Quasithin.IsG2Block L ∨ IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≤ 6048 := by
  rcases hb with hb | hb | hb
  · rw [SBc11.card_of_isPSU_three_three hb.2.1]
  · obtain ⟨-, α, hαs, hαk, -⟩ := hb
    obtain ⟨e⟩ := Obs3324.nonempty_quot_equiv α hαs hαk
    rw [SBc11.card_of_isAlt_six ⟨e⟩]
    norm_num
  · obtain ⟨-, ⟨-, h3, ⟨e⟩⟩, -⟩ := hb
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin, h3] at h1
    rw [h1]
    decide

end L3316

@[expose] def Step3_3_16SL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∀ (n : ℕ) (K : Type) [Field K] [Finite K], 1 < n → Nat.card K = 2 ^ n →
      Nonempty (↥(autOn L (vPlus L T)) ≃* ↥(StatedSL 3 K)) →
      (∃ (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
        Fintype.card F = 2 ^ n ∧ IsModO2Surj L α) → False

@[expose] def Step3_3_16Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L D : Subgroup G), Hyp331 G T M L D →
    ∀ (K : Type) [Field K] [Finite K], Nat.card K = 4 →
      Nonempty (↥(autOn L (vPlus L T)) ≃* ↥(StatedSp 2 K)) → IsSp4Block L → False

theorem stmt3_3_16_of (h6 : Stmt3_3_6) (h14 : Stmt3_3_14) (hC32 : ASInputs.AS_C_1_32)
    (hG2 : FactG2Cayley) (hSL : Step3_3_16SL3) (hSp : Step3_3_16Sp4) : Stmt3_3_16 := by
  intro G _ _ T M L D h n K _ _ hn hK
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := h.TM.trans (h14 G T M L D h).2
  have hred := Hyp331.vPlus_reduced h.toSetup331
  have hLV : L ≤ Subgroup.normalizer (vPlus L T : Set G) := le_sup_left.trans hred.2.2.2.1
  have hOQ : pCoreOf 2 L ≤ qL L T :=
    CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_normal 2 L (L ⊔ T) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer hTL))
  have hQV : qL L T ≤ Subgroup.centralizer (vPlus L T : Set G) :=
    Subgroup.le_centralizer_iff.mp (hred.1.trans inf_le_right)
  have hker : pCoreOf 2 L ≤ Subgroup.centralizer (vPlus L T : Set G) := hOQ.trans hQV
  have hq := h.Lq
  have hc132 := fun (hr : IsRankTwoLie2Derived
      ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))) =>
    hC32 G (L ⊔ T) T L (((h6 G T M L D h).2.2.2 hr).2 hTL) h.toSetup331.mem_cComp
      (Subgroup.coe_mul_of_right_le_normalizer_left L T hTL)
  have hdvd := L3316.card_dvd hLV hker
  have hsp4 : IsSp4Block L → Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 979200 := fun hb => by
    obtain ⟨-, F, _, _, hF, α, hαs, hαk, -⟩ := hb
    obtain ⟨e'⟩ := Obs3324.nonempty_quot_equiv α hαs hαk
    have hF' : Nat.card F = 2 ^ 2 := by rw [Nat.card_eq_fintype_card, hF]; norm_num
    rw [Nat.card_congr e'.toEquiv, L3316.card_sp4 hF']
    norm_num
  have hsl3 : ∀ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F) (α : ↥L →* ↥(StatedSL 3 F)),
      Fintype.card F = 2 ^ m → IsModO2Surj L α → ¬ L ≤ Subgroup.centralizer (vPlus L T : Set G) →
      1 ≤ m ∧ ∃ c : ℕ, (c = 1 ∨ c = 3) ∧ c * Nat.card ↥(autOn L (vPlus L T)) =
        2 ^ (m * 3) * ((2 ^ (m * 2) - 1) * (2 ^ (m * 3) - 1)) := by
    intro m F _ _ α hF hmod hnt
    obtain ⟨e'⟩ := Obs3324.nonempty_quot_equiv α hmod.1 hmod.2
    have hF' : Nat.card F = 2 ^ m := by rw [Nat.card_eq_fintype_card, hF]
    have hm : 1 ≤ m := by
      by_contra hm0
      have h1 : 1 < Fintype.card F := Fintype.one_lt_card
      rw [hF, show m = 0 by omega] at h1
      norm_num at h1
    obtain ⟨c, hc, hcm⟩ := L3316.exists_mul_card_sl3 hLV hker hnt hq e'
    exact ⟨hm, c, hc, by rw [hcm, L3316.card_sl3 hF']⟩
  refine ⟨⟨fun e => ?_⟩, ⟨fun e => ?_⟩, ⟨fun e => ?_⟩⟩
  ·
    have hcard : Nat.card ↥(autOn L (vPlus L T)) =
        2 ^ (n * 3) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 3) - 1)) := by
      rw [Nat.card_congr e.toEquiv, L3316.card_sl3 hK]
    have hge := L3316.sl3_ge (n := n) (by omega)
    have hnt := L3316.not_le_centralizer_of_one_lt hLV (by omega)
    obtain ⟨⟨cq⟩, hle⟩ := Obs3324.quot_data hLV hker hnt hq
    have hr : IsRankTwoLie2Derived
        ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      Or.inl ⟨n, L3316.isPSL3_of_cover (SzN15.isQuasisimple_of_equiv_sl3 e) cq (by omega) hK e⟩
    rcases hc132 hr with hb | hb | hb | hb | ⟨m, F, _, _, α, hF, hmod⟩
    · have := L3316.card_le_of_small_block (L := L) (Or.inl hb); omega
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inl hb)); omega
    · rw [hcard, hsp4 hb] at hdvd
      have h3 := L3316.le_eight_of_dvd ((Dvd.intro _ rfl).trans hdvd)
      obtain rfl : n = 2 := by omega
      norm_num at hdvd
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inr hb)); omega
    · obtain ⟨hm, c, hc, hcm⟩ := hsl3 m F inferInstance inferInstance α hF hmod hnt
      rw [hcard] at hcm
      have he := L3316.exp_eq_of_mul hc
        ((L3316.odd_two_pow_mul_sub_one (by omega) (by norm_num)).mul
          (L3316.odd_two_pow_mul_sub_one (by omega) (by norm_num)))
        ((L3316.odd_two_pow_mul_sub_one hm (by norm_num)).mul
          (L3316.odd_two_pow_mul_sub_one hm (by norm_num))) hcm
      obtain rfl : m = n := by omega
      exact hSL G T M L D h m K hn hK ⟨e⟩ ⟨F, inferInstance, inferInstance, α, hF, hmod⟩
  ·
    have hcard : Nat.card ↥(autOn L (vPlus L T)) =
        2 ^ (n * 4) * ((2 ^ (n * 2) - 1) * (2 ^ (n * 4) - 1)) := by
      rw [Nat.card_congr e.toEquiv, L3316.card_sp4 hK]
    have hge := L3316.sp4_ge (n := n) (by omega)
    have hnt := L3316.not_le_centralizer_of_one_lt hLV (by omega)
    obtain ⟨⟨cq⟩, hle⟩ := Obs3324.quot_data hLV hker hnt hq
    have h4K : 4 ≤ Nat.card K := by
      rw [hK]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) (by omega)
    have hY : CFSG.IsQuasisimple ↥(autOn L (vPlus L T)) :=
      CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm
        (CFSG.LieType.Universal.Symplectic.isQuasisimple 2 K (by norm_num) (Or.inl (Or.inr h4K)))
    have hr : IsRankTwoLie2Derived
        ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      Or.inr (Or.inr (Or.inr (Or.inl ⟨n, L3316.isPSp4_of_cover hY cq (by omega) hK e⟩)))
    rcases hc132 hr with hb | hb | hb | hb | ⟨m, F, _, _, α, hF, hmod⟩
    · have := L3316.card_le_of_small_block (L := L) (Or.inl hb); omega
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inl hb)); omega
    · have hdvd' := hdvd
      rw [hcard, hsp4 hb] at hdvd'
      have h3 := L3316.le_eight_of_dvd ((Dvd.intro _ rfl).trans hdvd')
      obtain rfl : n = 2 := by omega
      exact hSp G T M L D h K (by rw [hK]; norm_num) ⟨e⟩ hb
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inr hb)); omega
    · obtain ⟨hm, c, hc, hcm⟩ := hsl3 m F inferInstance inferInstance α hF hmod hnt
      rw [hcard] at hcm
      exact L3316.sp4_ne_sl3 (by omega) hm hc hcm
  ·
    have hcard : Nat.card ↥(autOn L (vPlus L T)) =
        2 ^ (n * 6) * ((2 ^ (n * 6) - 1) * (2 ^ (n * 2) - 1)) := by
      rw [Nat.card_congr e.toEquiv, L3316.card_g2 (by omega) hK]
    have hge := L3316.g2_ge (n := n) (by omega)
    have hnt := L3316.not_le_centralizer_of_one_lt hLV (by omega)
    obtain ⟨⟨cq⟩, hle⟩ := Obs3324.quot_data hLV hker hnt hq
    have eZ : ↥(quasithinG2 K) ⧸ Subgroup.center ↥(quasithinG2 K) ≃*
        (↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L) :=
      (QuotientGroup.congr (Subgroup.center ↥(autOn L (vPlus L T)))
        (Subgroup.center ↥(quasithinG2 K)) e (Subgroup.map_center_eq e)).symm.trans cq.symm
    have hr : IsRankTwoLie2Derived
        ((↥L ⧸ CFSG.pCore 2 ↥L) ⧸ Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L)) :=
      Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
        ⟨n, IsG2.of_mulEquiv eZ (hG2 K n (by omega) hK)⟩)))))
    rcases hc132 hr with hb | hb | hb | hb | ⟨m, F, _, _, α, hF, hmod⟩
    · have := L3316.card_le_of_small_block (L := L) (Or.inl hb); omega
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inl hb)); omega
    · rw [hcard, hsp4 hb] at hdvd
      have h3 := L3316.le_eight_of_dvd ((Dvd.intro _ rfl).trans hdvd)
      omega
    · have := L3316.card_le_of_small_block (L := L) (Or.inr (Or.inr hb)); omega
    · obtain ⟨hm, c, hc, hcm⟩ := hsl3 m F inferInstance inferInstance α hF hmod hnt
      rw [hcard] at hcm
      exact L3316.g2_ne_sl3 (by omega) hm hc hcm

end CFSG.Quasithin.H13

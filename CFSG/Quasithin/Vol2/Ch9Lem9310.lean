module

public import CFSG.Quasithin.Vol2.Ch9Sec3MS
public import CFSG.Quasithin.Vol2.Ch9Sec3FactsLie
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3316Q
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.CommutatorNormalizer
public import CFSG.Quasithin.Vol2.Ch9Lem936
public import CFSG.Quasithin.Vol2.Ch9Sec3Cart
public import CFSG.Quasithin.Vol2.Ch9Sec3DSB
public import CFSG.Quasithin.Vol2.Ch9Sec3VU

public section

namespace CFSG.Quasithin.H13.Ch9

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.H Matrix

section Orders

variable {G : Type} [Group G]

theorem card_O2Q_of_surj {L : Subgroup G} {H : Type*} [Group H] (α : ↥L →* H)
    (hs : Function.Surjective α) (hk : α.ker = CFSG.pCore 2 ↥L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = Nat.card H :=
  Nat.card_congr ((QuotientGroup.quotientMulEquivOfEq hk.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective α hs)).toEquiv

theorem card_le_of_small_block' {L : Subgroup G}
    (hb : CFSG.Quasithin.IsG2Block L ∨ IsAltBlockType L 6 ∨ CFSG.Quasithin.IsHatA6Block L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) ≤ 6048 := by
  rcases hb with hb | hb | hb
  · rw [SBc11.card_of_isPSU_three_three hb.2.1]
  · obtain ⟨-, α, hαs, hαk, -⟩ := hb
    rw [card_O2Q_of_surj α hαs hαk, SBc11.card_of_isAlt_six ⟨MulEquiv.refl _⟩]
    norm_num
  · obtain ⟨-, ⟨-, h3, ⟨e⟩⟩, -⟩ := hb
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup
      (Subgroup.center (↥L ⧸ CFSG.pCore 2 ↥L))
    rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup,
      Nat.card_eq_fintype_card (α := Fin 6), Fintype.card_fin, h3] at h1
    rw [h1]
    decide

theorem card_O2Q_of_isSp4Block {L : Subgroup G} (hb : IsSp4Block L) :
    Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 979200 := by
  obtain ⟨-, F, _, _, hF, α, hαs, hαk, -⟩ := hb
  rw [card_O2Q_of_surj α hαs hαk, CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp,
    show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num),
    Nat.card_eq_fintype_card, hF]
  norm_num

theorem card_sl3_ne {F : Type} [Field F] [Fintype F] {m : ℕ} (hF : Fintype.card F = 2 ^ m) :
    Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) ≠ 979200 ∧
      Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) ≠ 251596800 := by
  rw [CFSG.SectionRank.OddCover.card_statedSL_three, Nat.card_eq_fintype_card, hF]
  rcases lt_or_ge m 4 with hm | hm
  · interval_cases m <;> norm_num
  · have hq : 16 ≤ 2 ^ m :=
      calc 16 = 2 ^ 4 := by norm_num
        _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) hm
    have h1 : 4096 ≤ (2 ^ m) ^ 3 :=
      calc 4096 = 16 ^ 3 := by norm_num
        _ ≤ (2 ^ m) ^ 3 := Nat.pow_le_pow_left hq 3
    have h2 : 256 ≤ (2 ^ m) ^ 2 :=
      calc 256 = 16 ^ 2 := by norm_num
        _ ≤ (2 ^ m) ^ 2 := Nat.pow_le_pow_left hq 2
    have h2' : 255 ≤ (2 ^ m) ^ 2 - 1 := by omega
    have h3' : 4095 ≤ (2 ^ m) ^ 3 - 1 := by omega
    have h4 : 4096 * 255 * 4095 ≤ (2 ^ m) ^ 3 * ((2 ^ m) ^ 2 - 1) * ((2 ^ m) ^ 3 - 1) :=
      Nat.mul_le_mul (Nat.mul_le_mul h1 h2') h3'
    constructor <;> omega

theorem center_eq_bot_of_simple_of_even {X : Type*} [Group X] [Finite X] [hs : IsSimpleGroup X]
    (h2 : 2 ∣ Nat.card X) (hgt : 2 < Nat.card X) : Subgroup.center X = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
  · exact h
  exfalso
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' 2 h2
  have hn : (Subgroup.zpowers g).Normal := ⟨fun x hx y => by
    have hy : y ∈ Subgroup.center X := h ▸ Subgroup.mem_top y
    have h1 := Subgroup.mem_center_iff.mp hy x
    rw [← h1, mul_inv_cancel_right]
    exact hx⟩
  rcases hs.eq_bot_or_eq_top_of_normal (Subgroup.zpowers g) with h1 | h1
  · rw [Subgroup.zpowers_eq_bot] at h1
    rw [h1, orderOf_one] at hg
    norm_num at hg
  · have h3 := congrArg (fun H : Subgroup X => Nat.card H) h1
    simp only [Nat.card_zpowers, Subgroup.card_top, hg] at h3
    omega

end Orders

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G} {n : ℕ}

namespace Setup

variable (S : Setup T L I n)
include S

theorem c132_K0' (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (hC32 : ASInputs.AS_C_1_32) (h3108 : Stmt3_2_10_eight) (h2 : n = 2)
    {K D K₀ : Subgroup G} (hKM : ¬ K ≤ fsuM T L) (hKns : ¬ Group.IsSolvable ↥K)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K)
    (h1 : zQ T I = fsuV T I)
    (hM₀O : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hK₀ : K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) (hLK₀ : L ≤ K₀)
    (hKK₀ : K ≤ K₀)
    (hK₀n : L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤
      Subgroup.normalizer (K₀ : Set G))
    (hr : IsRankTwoLie2Derived ((↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ⧸
      Subgroup.center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀))) :
    CFSG.Quasithin.IsG2Block K₀ ∨ IsAltBlockType K₀ 6 ∨ IsSp4Block K₀ ∨
      CFSG.Quasithin.IsHatA6Block K₀ ∨
      ∃ (m : ℕ) (F : Type) (_ : Field F) (_ : Fintype F)
        (α : ↥K₀ →* ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F)),
        Fintype.card F = 2 ^ m ∧ IsModO2Surj K₀ α := by
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  have hM₀M : ¬ M₀ ≤ fsuM T L := fun h => hKM (le_sup_right.trans h)
  obtain ⟨hM₀eq, -, hchar⟩ := S.lem936 h37 h38 h37c h38c h3108 h2 h1 hD hBK hM₀O hsyl hM₀M hK₀
    hLK₀ hKK₀
  have hMS := S.isMSPair_M0' h37 h38 hKM hKns hM₀O hsyl hchar hK₀ hK₀n hM₀eq hr
  have hT₁K₀ : T₁ ≤ Subgroup.normalizer (K₀ : Set G) := (le_sup_right.trans le_sup_left).trans hK₀n
  refine hC32 G M₀ T₁ K₀ hMS hK₀ ?_
  rw [show M₀ = K₀ ⊔ T₁ from hM₀eq]
  exact Subgroup.coe_mul_of_right_le_normalizer_left K₀ T₁ hT₁K₀

theorem lem939'
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hC32 : ASInputs.AS_C_1_32) (h3108 : Stmt3_2_10_eight)
    (h2 : n = 2) {K D K₀ : Subgroup G} (hKM : ¬ K ≤ fsuM T L) (hKns : ¬ Group.IsSolvable ↥K)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K)
    (h1 : zQ T I = fsuV T I)
    (hM₀O : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hK₀ : K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) (hLK₀ : L ≤ K₀)
    (hKK₀ : K ≤ K₀)
    (hK₀n : L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤
      Subgroup.normalizer (K₀ : Set G))
    (hG2 : IsG2 2 2 (O2Q K₀)) : False := by
  have hZ : Subgroup.center (O2Q K₀) = ⊥ :=
    (CFSG.QuasithinUnique.Setup.X6.even_G2_model_two_extensions hG2).1
  have hr : IsRankTwoLie2Derived ((↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ⧸
      Subgroup.center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) :=
    Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨2, IsG2.of_mulEquiv
      ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm hG2⟩)))))
  have hcard : Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) = 251596800 := by
    have h3 := CFSG.Timmesfeld.card_chevalleyExceptionalModel_two hG2
    rw [h3]
    show ordG2 (2 ^ 2) = 251596800
    norm_num [ordG2]
  rcases S.c132_K0' h37 h38 h37c h38c hC32 h3108 h2 hKM hKns hD hBK h1 hM₀O hsyl hK₀ hLK₀ hKK₀
      hK₀n hr with hb | hb | hb | hb | ⟨m, F, _, _, α, hF, hmod⟩
  · have := card_le_of_small_block' (Or.inl hb)
    omega
  · have := card_le_of_small_block' (Or.inr (Or.inl hb))
    omega
  · have := card_O2Q_of_isSp4Block hb
    omega
  · have := card_le_of_small_block' (Or.inr (Or.inr hb))
    omega
  · have h3 := card_O2Q_of_surj α hmod.1 hmod.2
    rw [hcard] at h3
    exact (card_sl3_ne hF).2 h3.symm

theorem lem939
    (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h37c : Vol2Native.A37ForSQTKCat)
    (h38c : Vol2Native.A38ForSQTKCat) (hC32 : ASInputs.AS_C_1_32) (h3108 : Stmt3_2_10_eight)
    (h2 : n = 2) {H K D K₀ : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T)
    (hKc : K ∈ cComp H)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K)
    (h1 : zQ T I = fsuV T I)
    (hM₀O : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hK₀ : K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) (hLK₀ : L ≤ K₀)
    (hKK₀ : K ≤ K₀)
    (hK₀n : L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤
      Subgroup.normalizer (K₀ : Set G))
    (hG2 : IsG2 2 2 (O2Q K₀)) : False :=
  S.lem939' h37 h38 h37c h38c hC32 h3108 h2
    (fun h => hH.2.1 (by rw [hHK]; exact sup_le h Setup.T_le_fsuM))
    (not_isSolvable_of_mem_cComp hKc) hD hBK h1 hM₀O hsyl hK₀ hLK₀ hKK₀ hK₀n hG2

theorem lem9310' (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (hC32 : ASInputs.AS_C_1_32) (hFH : Sp4BlockParabolicFact) (h3108 : Stmt3_2_10_eight)
    (h2 : n = 2) {K D K₀ : Subgroup G} (hKM : ¬ K ≤ fsuM T L) (hKns : ¬ Group.IsSolvable ↥K)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K)
    (h1 : zQ T I = fsuV T I)
    (hM₀O : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hK₀ : K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) (hLK₀ : L ≤ K₀)
    (hKK₀ : K ≤ K₀)
    (hK₀n : L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤
      Subgroup.normalizer (K₀ : Set G))
    (hP : IsPSp4 2 2 (O2Q K₀)) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hfsu := S.hyp.fsu
  obtain ⟨F, _, _, _, e, ψ, hc, hdiag⟩ := S.exists_isCoord_diag h37c h38c hD
  set T₁ := T ⊓ Subgroup.normalizer (L : Set G) with hT₁
  set M₀ := L ⊔ D ⊔ T₁ ⊔ K with hM₀
  set V₁ := fsuV T I ⊓ Subgroup.centralizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G) with hV₁
  have hLM₀ : L ≤ M₀ := le_sup_left.trans (le_sup_left.trans le_sup_left)
  have hT₁M₀ : T₁ ≤ M₀ := le_sup_right.trans le_sup_left
  have hK₀M₀ : K₀ ≤ M₀ := le_of_mem_cComp hK₀
  have hM₀M : ¬ M₀ ≤ fsuM T L := fun h => hKM (le_sup_right.trans h)
  obtain ⟨hM₀eq, hV₁O, hchar⟩ := S.lem936 h37 h38 h37c h38c h3108 h2 h1 hD hBK hM₀O hsyl hM₀M
    hK₀ hLK₀ hKK₀
  have hZM₀ := S.center_M0_eq_bot h37 h38 h37c h38c h2 h1 hD hsyl hchar
  have hcardP : Nat.card (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) = 979200 := by
    have h3 := (CFSG.Timmesfeld.card_statedClassicalModel_two hP).2.2.1 rfl
    rw [h3]
    decide
  have hcenter : Subgroup.center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) = ⊥ := by
    obtain ⟨-, F', _, _, hF', ⟨e'⟩⟩ := hP
    have h4 : 4 ≤ Nat.card F' := by rw [hF']; norm_num
    have : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSp 2 F')) :=
      CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp F' 2 (by norm_num)
        (Or.inl (Or.inr h4))
    have : IsSimpleGroup (↥K₀ ⧸ CFSG.pCore 2 ↥K₀) := e'.isSimpleGroup
    exact center_eq_bot_of_simple_of_even (by rw [hcardP]; norm_num) (by rw [hcardP]; norm_num)
  have hr : IsRankTwoLie2Derived ((↥K₀ ⧸ CFSG.pCore 2 ↥K₀) ⧸
      Subgroup.center (↥K₀ ⧸ CFSG.pCore 2 ↥K₀)) := by
    refine Or.inr (Or.inr (Or.inr (Or.inl ⟨2, ?_⟩)))
    obtain ⟨hadm, F', _, _, hF', ⟨e'⟩⟩ := hP
    exact ⟨hadm, F', inferInstance, inferInstance, hF',
      ⟨((QuotientGroup.quotientMulEquivOfEq hcenter).trans QuotientGroup.quotientBot).trans e'⟩⟩
  rcases S.c132_K0' h37 h38 h37c h38c hC32 h3108 h2 hKM hKns hD hBK h1 hM₀O hsyl hK₀ hLK₀ hKK₀
      hK₀n hr with hb | hb | hb | hb | ⟨m, F', _, _, α, hF', hmod⟩
  · have := card_le_of_small_block' (Or.inl hb)
    omega
  · have := card_le_of_small_block' (Or.inr (Or.inl hb))
    omega
  rotate_left
  · have := card_le_of_small_block' (Or.inr (Or.inr hb))
    omega
  · have h3 := card_O2Q_of_surj α hmod.1 hmod.2
    rw [hcardP] at h3
    exact (card_sl3_ne hF').1 h3.symm
  set U₀ := blockU K₀ with hU₀
  have hDK₀ : D ≤ K₀ := (hc.le_sup_L h37 h38 h37c h38c hD hdiag).trans
    (sup_le (hBK.trans hKK₀) hLK₀)
  have hT₁K₀ : T₁ ≤ Subgroup.normalizer (K₀ : Set G) := hT₁M₀.trans hK₀n
  have hT₁2 : IsPGroup 2 T₁ := hfsu.sylow.1.to_le inf_le_left
  have hOK₀ : pCoreOf 2 K₀ ≤ T₁ :=
    (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₀).trans hK₀M₀)
      (hK₀n.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₀))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₀)).trans (F7.isSylowTwoOf_pCoreOf_le hsyl)
  have hUQ : U₀ ≤ pCoreOf 2 K₀ := C1.blockU_le_blockQ hb.1
  have hZ0 : blockZ K₀ = ⊥ := by
    by_contra hne
    have hZT₁ : blockZ K₀ ≤ T₁ := inf_le_left.trans (hUQ.trans hOK₀)
    have hT₁Z : T₁ ≤ Subgroup.normalizer ((blockZ K₀ : Subgroup G) : Set G) := by
      intro x hx
      have hxK : x ∈ Subgroup.normalizer (K₀ : Set G) := hT₁K₀ hx
      have hxO : x ∈ Subgroup.normalizer ((pCoreOf 2 K₀ : Subgroup G) : Set G) :=
        CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₀ hxK
      have hxU : x ∈ Subgroup.normalizer ((U₀ : Subgroup G) : Set G) :=
        CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer (Subgroup.zpowers x)
          (pCoreOf 2 K₀) K₀ (Subgroup.zpowers_le.mpr hxO) (Subgroup.zpowers_le.mpr hxK)
          (Subgroup.mem_zpowers x)
      exact Subgroup.inf_normalizer_le_normalizer_inf ⟨hxU, mem_normalizer_centralizer hxK⟩
    have h3 := CFSG.QuasithinUnique.inf_centralizer_ne_bot_of_normalizes hT₁2 hZT₁ hT₁Z hne
    obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h3
    apply hz1
    have hzM : (z : G) ∈ M₀ ⊓ Subgroup.centralizer (M₀ : Set G) := by
      refine ⟨hT₁M₀ (hZT₁ z.2.1), ?_⟩
      have hle : K₀ ⊔ T₁ ≤ Subgroup.centralizer ({(z : G)} : Set G) := by
        refine sup_le (fun k hk => ?_) (fun t ht => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp z.2.1.2 k hk
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp z.2.2 t ht
      show (z : G) ∈ Subgroup.centralizer (M₀ : Set G)
      rw [Subgroup.mem_centralizer_iff]
      intro m hm
      have hm' : m ∈ K₀ ⊔ T₁ := by
        rw [← show M₀ = K₀ ⊔ T₁ from hM₀eq]
        exact hm
      have h4 := hle hm'
      rw [Subgroup.mem_centralizer_singleton_iff] at h4
      exact h4
    rw [hZM₀, Subgroup.mem_bot] at hzM
    exact Subtype.ext hzM
  have hU0card : Nat.card U₀ = 2 ^ 8 := by
    rw [hU₀, L3316.card_blockU hb, hZ0, Subgroup.card_bot, one_mul]
  obtain ⟨d, hdD, hdL, hfp⟩ := hc.exists_fpf h37 h38 h37c h38c h2 hD hdiag
  have hdK₀ : d ∈ K₀ := hDK₀ hdD
  have hdV : d ∈ Subgroup.normalizer (fsuV T I : Set G) := S.L0_le_normalizer_V (S.L_le_L0 hdL)
  have hQT₁ : T ⊓ Subgroup.centralizer (fsuV T I : Set G) ≤ T₁ :=
    le_inf inf_le_left (le_sup_right.trans (hc.r0_le_normalizer_L h37 h38 h37c h38c))
  have hVT₁ : fsuV T I ≤ T₁ := S.fsuV_le_Q.trans hQT₁
  have hVcomm := exists_eq_commutator_of_fpf hdV hfp
  have hVK₀ : fsuV T I ≤ K₀ := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hVcomm v hv
    have h3 : x * d * x⁻¹ ∈ K₀ := (Subgroup.mem_normalizer_iff.mp (hT₁K₀ (hVT₁ hx)) d).mp hdK₀
    exact K₀.mul_mem h3 (K₀.inv_mem hdK₀)
  set V₂ := conjClosure V₁ L with hV₂
  have hLV : L ≤ Subgroup.normalizer (fsuV T I : Set G) := S.L_le_L0.trans S.L0_le_normalizer_V
  have hV₂V : V₂ ≤ fsuV T I := conjClosure_le fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.mp (hLV hl) v).mp hv.1
  have hV₂O : V₂ ≤ pCoreOf 2 M₀ := conjClosure_le fun l hl v hv =>
    (Subgroup.mem_normalizer_iff.mp (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₀
      (hLM₀ hl)) v).mp (hV₁O hv)
  have hV₂OK₀ : V₂ ≤ pCoreOf 2 K₀ := by
    refine le_trans (le_inf (hV₂V.trans hVK₀) hV₂O)
      (CFSG.QuasithinUnique.le_pCoreOf_of_le_normalizer
      inf_le_left (fun k hk => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hk, CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M₀ (hK₀M₀ hk)⟩)
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M₀).to_le inf_le_right))
  have hV₂U : V₂ ≤ U₀ := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := exists_eq_commutator_of_fpf (le_normalizer_conjClosure V₁ L hdL)
      (fun w hw => hfp w (hV₂V hw)) v hv
    exact Subgroup.commutator_mem_commutator (hV₂OK₀ hx) hdK₀
  have hV₂card := hc.card_conjClosure_ge h37c h38c h2
  have hVcard : Nat.card ↥(fsuV T I) = 2 ^ 8 := by
    rw [Nat.card_congr e.toEquiv, card_vm, hc.card, h2]
    norm_num
  have hcardFH : Nat.card ↥(fsuV T I) ≤ 2 ^ 4 * Nat.card ↥(fsuV T I ⊓ blockU K₀) := by
    have h3 : Nat.card V₂ ≤ Nat.card ↥(fsuV T I ⊓ blockU K₀) :=
      Subgroup.card_le_of_le (le_inf hV₂V hV₂U)
    rw [hVcard]
    calc 2 ^ 8 = 2 ^ 4 * 2 ^ 4 := by norm_num
      _ ≤ 2 ^ 4 * Nat.card ↥(fsuV T I ⊓ blockU K₀) :=
        Nat.mul_le_mul_left _ (hV₂card.trans h3)
  have hFH' := hFH G K₀ (T₁ ⊓ K₀) L (fsuV T I) hb
    (A4.isSylowTwoOf_inf_normal hsyl hK₀M₀ hK₀n) hLK₀ (inf_le_left.trans inf_le_right)
    (perfect_of_mem_cComp hfsu.maximal.1.2.1) (S.oTwoQuot_L_facts h37c h38c h2) hVK₀
    S.isPGroup_fsuV hLV hcardFH
  have hVU : fsuV T I ≤ U₀ := by
    intro v hv
    obtain ⟨x, hx, rfl⟩ := hVcomm v hv
    exact hFH' (Subgroup.commutator_mem_commutator hx hdL)
  have hVeq : fsuV T I = U₀ := Subgroup.eq_of_le_of_card_ge hVU (by rw [hU0card, hVcard])
  have hK₀U : K₀ ≤ Subgroup.normalizer ((U₀ : Subgroup G) : Set G) :=
    CFSG.GorensteinWalter.le_normalizer_commutator_of_le_normalizer K₀ (pCoreOf 2 K₀) K₀
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K₀) Subgroup.le_normalizer
  rw [← hVeq] at hK₀U
  exact hKM (hKK₀.trans (hK₀U.trans S.hNM))

theorem lem9310 (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h37c : Vol2Native.A37ForSQTKCat) (h38c : Vol2Native.A38ForSQTKCat)
    (hC32 : ASInputs.AS_C_1_32) (hFH : Sp4BlockParabolicFact) (h3108 : Stmt3_2_10_eight)
    (h2 : n = 2) {H K D K₀ : Subgroup G} (hH : IsHStar T (fsuM T L) H) (hHK : H = K ⊔ T)
    (hKc : K ∈ cComp H)
    (hD : Lin2.IsHallTwoPrimeOf D
      (fsuL0 T L ⊓ Subgroup.normalizer ((T ⊓ fsuL0 T L : Subgroup G) : Set G)))
    (hBK : D ⊓ Subgroup.centralizer ((fsuV T I ⊓ Subgroup.centralizer
      ((T ⊓ fsuL0 T L : Subgroup G) : Set G) : Subgroup G) : Set G) ≤ K)
    (h1 : zQ T I = fsuV T I)
    (hM₀O : pCoreOf 2 (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K) ≠ ⊥)
    (hsyl : IsSylowTwoOf (T ⊓ Subgroup.normalizer (L : Set G))
      (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K))
    (hK₀ : K₀ ∈ cComp (L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K)) (hLK₀ : L ≤ K₀)
    (hKK₀ : K ≤ K₀)
    (hK₀n : L ⊔ D ⊔ (T ⊓ Subgroup.normalizer (L : Set G)) ⊔ K ≤
      Subgroup.normalizer (K₀ : Set G))
    (hP : IsPSp4 2 2 (O2Q K₀)) : False :=
  S.lem9310' h37 h38 h37c h38c hC32 hFH h3108 h2
    (fun h => hH.2.1 (by rw [hHK]; exact sup_le h Setup.T_le_fsuM))
    (not_isSolvable_of_mem_cComp hKc) hD hBK h1 hM₀O hsyl hK₀ hLK₀ hKK₀ hK₀n hP

end Setup

end CFSG.Quasithin.H13.Ch9

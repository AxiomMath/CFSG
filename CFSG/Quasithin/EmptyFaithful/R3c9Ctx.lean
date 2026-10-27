module

public import CFSG.Quasithin.EmptyFaithful.R3c9Lie
public import CFSG.Quasithin.EmptyFaithful.R3c8Main
public import CFSG.Quasithin.EmptyFaithful.S153D58
public import CFSG.Quasithin.Background.GoldschmidtS146RBend1

public section

namespace CFSG.Quasithin.R3c9

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.R3c2
  CFSG.Quasithin.R3c3 CFSG.LieType.BorelTits
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem three_dvd_of_padicValNat_eq_one {N : ℕ} (hN : N ≠ 0) (h : padicValNat 3 N = 1) :
    3 ∣ N ∧ ¬ 9 ∣ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  constructor
  · have := (padicValNat_dvd_iff_le (p := 3) (a := N) (n := 1) hN).mpr (by omega)
    simpa using this
  · intro h9
    have := (padicValNat_dvd_iff_le (p := 3) (a := N) (n := 2) hN).mp (by simpa using h9)
    omega

omit [Finite G] in
theorem le_normalizer_of_commute' {A B : Subgroup G} (hAB : ∀ a ∈ A, ∀ b ∈ B, a * b = b * a) :
    A ≤ Subgroup.normalizer (B : Set G) := fun a ha => by
  rw [Subgroup.mem_normalizer_iff]
  intro b
  have key : ∀ b' ∈ B, a * b' * a⁻¹ = b' := fun b' hb' => by rw [hAB a ha b' hb']; group
  constructor
  · intro hb
    rw [key b hb]
    exact hb
  · intro hb
    have h1 : a⁻¹ * (a * b * a⁻¹) = (a * b * a⁻¹) * a⁻¹ := hAB a⁻¹ (A.inv_mem ha) _ hb
    have h2 : b = a * b * a⁻¹ := by
      calc b = a⁻¹ * (a * b * a⁻¹) * a := by group
        _ = (a * b * a⁻¹) * a⁻¹ * a := by rw [h1]
        _ = a * b * a⁻¹ := by group
    rw [h2]
    exact hb


theorem noU34_core
    (c : CtxComp2 T Mc M V₁ V₂ Yp I L t) (hL0 : L = conjClosure L (Sgp153 T V₁))
    (hLs : IsSimpleGroup ↥L)
    (hY : Yp = oTwoUpper (Yp ⊓ L) ⊔ oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)))
    (h3L : padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ L))) = 1)
    (h3C : padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)))) = 1)
    (hE9 : IsElemAbelianOfRank 3 2 (OTwoQuot Yp))
    (h113 : StageLemma14113)
    (hnine : ∀ (G : Type) [Group G] [Finite G] (T Mc M : Subgroup G), Hyp153 G T Mc M →
      VZ T M < pCoreOf 2 (Y153 Mc M))
    (hfam' : (∃ n : ℕ, Even n ∧ IsPSL 2 2 n ↥L) ∨ (∃ n : ℕ, Even n ∧ n ≠ 2 ∧ IsPSU 3 2 n ↥L) ∨
      IsPSL 3 2 1 ↥L) : False := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  have hLc : L ∈ cComp I := c.c33.mem
  have hLI : L ≤ I := le_of_mem_cComp hLc
  have hSI : Sgp153 T V₁ ≤ I := le_sup_right.trans c.inH.1.1
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := by
    have := le_normalizer_conjClosure L (Sgp153 T V₁)
    rwa [← hL0] at this
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hVS : VZ T M ≤ Sgp153 T V₁ := by
    intro v hv
    refine ⟨hh.hyp.VZ_le_T hv, A4.mem_normalizer_of_conj_mem fun k hk => ?_⟩
    have hc := congrArg Subtype.val
      (hh.hyp.elemAbelian.1.is_comm.comm ⟨v, hv⟩ ⟨k, hh.decomp.le₁ hk⟩)
    have : v * k * v⁻¹ = k := by
      have h1 : v * k = k * v := hc
      rw [h1]
      group
    rw [this]
    exact hk
  have hperf : Group.IsPerfect ↥L := c.c33.quasisimple.1
  have hZ1 : centerOf L = ⊥ := by
    have h0 := CFSG.Quasithin.R3c3.center_eq_bot_of_simple_perfect hLs hperf
    rw [eq_bot_iff]
    intro x hx
    have hxL : x ∈ L := hx.1
    have : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L :=
      SBc2.mem_centerOf_iff_center.mp hx
    rw [h0] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val (Subgroup.mem_bot.mp this))
  set YL : Subgroup G := oTwoUpper (Yp ⊓ L) with hYLdef
  set YC : Subgroup G := oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)) with hYCdef
  have hYLL : YL ≤ L := (oTwoUpper_le _).trans inf_le_right
  have hYLY : YL ≤ Yp := (oTwoUpper_le _).trans inf_le_left
  have hYCC : YC ≤ Subgroup.centralizer (L : Set G) := (oTwoUpper_le _).trans inf_le_right
  have hYCY : YC ≤ Yp := (oTwoUpper_le _).trans inf_le_left
  have hcomm : ∀ a ∈ YL, ∀ b ∈ YC, a * b = b * a := fun a ha b hb =>
    Subgroup.mem_centralizer_iff.mp (hYCC hb) a (hYLL ha)
  have hdisj : YL ⊓ YC = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have : x ∈ centerOf L := ⟨hYLL hx.1, hYCC hx.2⟩
    rw [hZ1] at this
    exact this
  obtain ⟨e9⟩ := hE9
  have h9 : Nat.card (OTwoQuot Yp) = 9 := by
    rw [Nat.card_congr e9.toEquiv]
    simp
  obtain ⟨b, hb⟩ : ∃ b : ℕ, Nat.card ↥Yp = 2 ^ b * 9 := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.Open.pCore 2 ↥Yp)
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCore_isPGroup 2 :
      IsPGroup 2 ↥(CFSG.Open.pCore 2 ↥Yp)).exists_card_eq
    refine ⟨a, ?_⟩
    have h2 : Nat.card (↥Yp ⧸ CFSG.Open.pCore 2 ↥Yp) = 9 := h9
    rw [h1, ha, h2]
    ring
  have hodd3 : ∀ x ∈ Yp, Odd (orderOf x) → ∃ k : ℕ, orderOf x = 3 ^ k := by
    intro x hx hodd
    have hd : orderOf x ∣ 2 ^ b * 9 := hb ▸ Subgroup.orderOf_dvd_natCard Yp hx
    have hcop : Nat.Coprime (orderOf x) (2 ^ b) :=
      Nat.Coprime.pow_right b (Nat.coprime_two_right.mpr hodd)
    have h9' : orderOf x ∣ 3 ^ 2 := hcop.dvd_of_dvd_mul_left hd
    obtain ⟨k, -, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp h9'
    exact ⟨k, hk⟩
  have hYLgen : YL ≤ Subgroup.closure {x : G | x ∈ YL ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hodd3 x hx.1.1 hx.2⟩
  have hYCgen : YC ≤ Subgroup.closure {x : G | x ∈ YC ∧ ∃ k : ℕ, orderOf x = 3 ^ k} := by
    refine (Subgroup.closure_le _).mpr fun x hx => ?_
    exact Subgroup.subset_closure ⟨Subgroup.subset_closure hx, hodd3 x hx.1.1 hx.2⟩
  have hYLd : Nat.card ↥YL ∣ 2 ^ b * 9 := hb ▸ Subgroup.card_dvd_of_le hYLY
  have hYCd : Nat.card ↥YC ∣ 2 ^ b * 9 := hb ▸ Subgroup.card_dvd_of_le hYCY
  obtain ⟨hYL3, hYL9⟩ := three_dvd_of_padicValNat_eq_one Nat.card_pos.ne' h3L
  obtain ⟨hYC3, -⟩ := three_dvd_of_padicValNat_eq_one Nat.card_pos.ne' h3C
  have hSYp : Sgp153 T V₁ ≤ Subgroup.normalizer (Yp : Set G) := fun s hs => by
    have : s ∈ I ⊓ Subgroup.normalizer (Yp : Set G) := by
      rw [c.facts.norm_eq]
      exact ⟨hSM hs, hSI hs⟩
    exact this.2
  have hVcen : ∀ x : G, (∀ v ∈ V₁, x * v = v * x) → (∀ v ∈ V₂, x * v = v * x) →
      ∀ v ∈ VZ T M, x * v = v * x := by
    intro x h1 h2 v hv
    rw [← hh.decomp.sup] at hv
    have hle : V₁ ⊔ V₂ ≤ Subgroup.centralizer ({x} : Set G) :=
      sup_le (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (h1 u hu).symm)
        (fun u hu => Subgroup.mem_centralizer_singleton_iff.mpr (h2 u hu).symm)
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hv)).symm
  obtain ⟨a', hYLcard⟩ : ∃ a' : ℕ, Nat.card ↥YL = 3 * 2 ^ a' := by
    obtain ⟨y, z, hy, hz, hyz⟩ := (Nat.dvd_mul).mp hYLd
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hy
    obtain ⟨k, hk2, hk⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp (by simpa using hz : z ∣ 3 ^ 2)
    have hcard : Nat.card ↥YL = 2 ^ i * 3 ^ k := by rw [← hyz, hi, hk]
    interval_cases k
    · exfalso
      rw [hcard] at hYL3
      have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three (by simpa using hYL3 : 3 ∣ 2 ^ i))
      omega
    · exact ⟨i, by rw [hcard]; ring⟩
    · exfalso
      apply hYL9
      rw [hcard]
      exact Dvd.intro_left _ rfl
  have hYpM : Yp ≤ M := hh.Yp_le_Y153.trans (Y153_le Mc M)
  have hYpN : Yp ≤ Subgroup.normalizer (L : Set G) := by
    rw [hY]
    exact sup_le (hYLL.trans Subgroup.le_normalizer)
      (hYCC.trans (Subgroup.centralizer_le_normalizer _))
  rcases hh.cases with hYY | ⟨hU, hYp2⟩
  ·
    have hCV : Nat.card ↥(Yp ⊓ Subgroup.centralizer (VZ T M : Set G)) = 2 ^ b := by
      have h1 := hh.hyp.card_Y153 h113
      rw [← hYY, hb] at h1
      omega
    have hC2 : IsPGroup 2 ↥(Yp ⊓ Subgroup.centralizer (VZ T M : Set G)) := IsPGroup.of_card hCV
    have hnotC : ∀ X : Subgroup G, X ≤ Yp → 3 ∣ Nat.card ↥X →
        ¬ X ≤ Subgroup.centralizer (VZ T M : Set G) := by
      intro X hXY h3 hXC
      have h2 : IsPGroup 2 ↥X := hC2.to_le (le_inf hXY hXC)
      obtain ⟨n, hn⟩ := h2.exists_card_eq
      rw [hn] at h3
      have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
      omega
    have hSYL : Sgp153 T V₁ ≤ Subgroup.normalizer (YL : Set G) := by
      have h1 : Sgp153 T V₁ ≤ Subgroup.normalizer ((Yp ⊓ L : Subgroup G) : Set G) := fun s hs =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨hSYp hs, hSL hs⟩
      exact h1.trans (normalizer_le_normalizer_oTwoUpper _)
    obtain ⟨hY₁, hY₂⟩ := hh.hyp.Y153_le_normalizer_V h113 hh.decomp
    rw [← hYY] at hY₁ hY₂
    have hV₁YL : V₁ ≤ Subgroup.normalizer (YL : Set G) := fun v hv => hSYL (hVS (hh.decomp.le₁ hv))
    have hV₂YL : V₂ ≤ Subgroup.normalizer (YL : Set G) := fun v hv => hSYL (hVS (hh.decomp.le₂ hv))
    have d1 := centralizes_or_le_of_generated_by_threePow hYLgen hV₁YL (hYLY.trans hY₁)
      hh.decomp.card₁
    have d2 := centralizes_or_le_of_generated_by_threePow hYLgen hV₂YL (hYLY.trans hY₂)
      hh.decomp.card₂
    have hnotboth : ¬ ((∀ x ∈ YL, ∀ v ∈ V₁, x * v = v * x) ∧ (∀ x ∈ YL, ∀ v ∈ V₂, x * v = v * x)) := by
      rintro ⟨h1, h2⟩
      apply hnotC YL hYLY hYL3
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact (hVcen x (h1 x hx) (h2 x hx) v hv).symm
    have hnotVL : ¬ VZ T M ≤ L := by
      intro hVL
      apply hnotC YC hYCY hYC3
      intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      exact Subgroup.mem_centralizer_iff.mp (hYCC hx) v (hVL hv)
    have hcase : ((∀ x ∈ YL, ∀ v ∈ V₁, x * v = v * x) ∧ V₂ ≤ YL ∧
          ¬ ∀ x ∈ YL, ∀ v ∈ V₂, x * v = v * x) ∨
        ((∀ x ∈ YL, ∀ v ∈ V₂, x * v = v * x) ∧ V₁ ≤ YL ∧
          ¬ ∀ x ∈ YL, ∀ v ∈ V₁, x * v = v * x) := by
      rcases d1 with h1 | ⟨hV1, hn1⟩ <;> rcases d2 with h2 | ⟨hV2, hn2⟩
      · exact absurd ⟨h1, h2⟩ hnotboth
      · exact Or.inl ⟨h1, hV2, hn2⟩
      · exact Or.inr ⟨h2, hV1, hn1⟩
      · exfalso
        apply hnotVL
        rw [← hh.decomp.sup]
        exact sup_le (hV1.trans hYLL) (hV2.trans hYLL)
    obtain ⟨W, hWYL, hW4, hWV⟩ : ∃ W : Subgroup G, W ≤ YL ∧ Nat.card W = 4 ∧ W ≤ VZ T M := by
      rcases hcase with ⟨-, h2, -⟩ | ⟨-, h1, -⟩
      · exact ⟨V₂, h2, hh.decomp.card₂, hh.decomp.le₂⟩
      · exact ⟨V₁, h1, hh.decomp.card₁, hh.decomp.le₁⟩
    have hVcard : Nat.card ↥(VZ T M) = 16 := by
      have hc : ∀ a ∈ V₁, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb => by
        have := hh.hyp.elemAbelian.1.is_comm.comm ⟨a, hh.decomp.le₁ ha⟩ ⟨b, hh.decomp.le₂ hb⟩
        exact congrArg Subtype.val this
      have := S153D.card_sup_eq_mul hc hh.decomp.inf
      rw [hh.decomp.sup, hh.decomp.card₁, hh.decomp.card₂] at this
      simpa using this
    have hEcard : Nat.card ↥(VZ T M ⊓ L) ≤ 8 := by
      have hdvd : Nat.card ↥(VZ T M ⊓ L) ∣ 2 ^ 4 := by
        have := Subgroup.card_dvd_of_le (inf_le_left : VZ T M ⊓ L ≤ VZ T M)
        rw [hVcard] at this
        simpa using this
      obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hdvd
      have hne : Nat.card ↥(VZ T M ⊓ L) ≠ 16 := by
        intro h16
        apply hnotVL
        have : VZ T M ⊓ L = VZ T M :=
          Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h16, hVcard])
        rw [← this]
        exact inf_le_right
      rw [hjeq] at hne ⊢
      interval_cases j <;> first | (exfalso; apply hne; norm_num; done) | norm_num
    have hBor : ∀ n : ℕ, (IsPSL 2 2 n ↥L ∨ (2 ≤ n ∧ IsPSU 3 2 n ↥L)) → 2 ^ n ≤ 8 := by
      intro n hn
      have hBender : fusionIsBenderGroup ↥L := by
        rcases hn with h | ⟨h2, h⟩
        · exact A5.C25.fusionIsBenderGroup_of_isPSL h
        · exact K1.fusionIsBenderGroup_of_stated_psu_three h2 h
      set Q : Subgroup G := Sgp153 T V₁ ⊓ L with hQdef
      have hQL : Q ≤ L := inf_le_right
      have hYLM : YL ≤ M := hYLY.trans hYpM
      have hYLN : YL ≤ Subgroup.normalizer (Q : Set G) := by
        rcases GoldS146R.bender_overgroup hBender hQsyl (R := YL ⊔ Q) le_sup_right
          (sup_le hYLL hQL) with h | h
        · exact le_sup_left.trans h
        · exfalso
          exact c.c33.not_le (h.trans (sup_le hYLM (inf_le_left.trans hSM)))
      have hSQ : Sgp153 T V₁ ≤ Subgroup.normalizer (Q : Set G) := fun s hs =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hs, hSL hs⟩
      have hYCQ : YC ≤ Subgroup.normalizer (Q : Set G) :=
        (hYCC.trans (Subgroup.centralizer_le hQL)).trans (Subgroup.centralizer_le_normalizer _)
      have hXQ : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (Q : Set G) := by
        rw [hY]
        exact sup_le (sup_le hYLN hYCQ) hSQ
      have hXL : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := sup_le hYpN hSL
      have hBX : Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer ((L ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) :=
        SBc2.le_normalizer_borel hXL hXQ
      have hcentQ := bender_cent_le hBender hQsyl
      have hChar : CharTwo (L ⊓ Subgroup.normalizer (Q : Set G)) :=
        R3c8.charTwo_borel_of_cent hQsyl fun x hx hc => hcentQ x hx fun p hp => by
          have h1 := hc p hp
          rw [hZ1, Subgroup.mem_bot] at h1
          calc x * p = (x * p * x⁻¹ * p⁻¹) * (p * x) := by group
            _ = p * x := by rw [h1, one_mul]
      have hBMI : L ⊓ Subgroup.normalizer (Q : Set G) ≤ M ⊓ I :=
        c.c33.inv_le _ (inf_le_left.trans hL0.le) hBX hChar
      have hBV : L ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer (VZ T M : Set G) :=
        (hBMI.trans inf_le_left).trans hh.hyp.le_normalizer
      have hEQ : VZ T M ⊓ L ≤ Q := le_inf (inf_le_left.trans hVS) inf_le_right
      have hE1 : VZ T M ⊓ L ≠ ⊥ := by
        intro hb
        have hW1 : W ≤ VZ T M ⊓ L := le_inf hWV (hWYL.trans hYLL)
        rw [hb, le_bot_iff] at hW1
        rw [hW1, Subgroup.card_bot] at hW4
        omega
      have hN : L ⊓ Subgroup.normalizer (Q : Set G) ≤ Subgroup.normalizer ((VZ T M ⊓ L : Subgroup G) : Set G) :=
        fun b hb => Subgroup.inf_normalizer_le_normalizer_inf ⟨hBV hb, Subgroup.le_normalizer hb.1⟩
      obtain ⟨T', -, hcard⟩ := bender_center_card_le hBender hQsyl hEQ hE1 hN
      have hZ : Nat.card (CFSG.ComponentClassification.AschbacherToolkit.Bender.sylowCenter
          (T' : Subgroup ↥L)) = 2 ^ n := by
        rcases hn with h | ⟨h2, h⟩
        · exact card_sylowCenter_of_isPSL h T'
        · exact card_sylowCenter_of_isPSU h2 h T'
      rw [hZ] at hcard
      exact hcard.trans hEcard
    have hFour : FourSelfCentTwo ↥L := fourSelfCentTwo_of_family hfam' hBor
    have hVsq : ∀ v ∈ VZ T M, v ^ 2 = 1 := hh.hyp.elemAbelian.2
    have hVc : ∀ u ∈ VZ T M, ∀ v ∈ VZ T M, u * v = v * u := fun u hu v hv => by
      have := hh.hyp.elemAbelian.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩
      exact congrArg Subtype.val this
    have hYLgen' : YL = Subgroup.closure {x : G | x ∈ YL ∧ ∃ k : ℕ, orderOf x = 3 ^ k} :=
      le_antisymm hYLgen ((Subgroup.closure_le _).mpr fun x hx => hx.1)
    have hYLN : Yp ≤ Subgroup.normalizer (YL : Set G) := by
      have h1 : Yp ≤ Subgroup.normalizer ((Yp ⊓ L : Subgroup G) : Set G) := fun x hx =>
        Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hYpN hx⟩
      exact h1.trans (normalizer_le_normalizer_oTwoUpper _)
    have hfin : ∀ (V₁' V₂' : Subgroup G) (t' : G) (D : Decomp153 T M V₁' V₂' t'),
        (∀ x ∈ YL, ∀ v ∈ V₁', x * v = v * x) → V₂' ≤ YL →
        (¬ ∀ x ∈ YL, ∀ v ∈ V₂', x * v = v * x) → False := by
      intro V₁' V₂' t' D hP1 hV2 hnP2
      obtain ⟨hY₁', hY₂'⟩ := hh.hyp.Y153_le_normalizer_V h113 D
      rw [← hYY] at hY₁' hY₂'
      have hV2sq : ∀ v ∈ V₂', v ^ 2 = 1 := fun v hv => hVsq v (D.le₂ hv)
      have hVc2 : ∀ u ∈ V₂', ∀ v ∈ V₂', u * v = v * u := fun u hu v hv => hVc u (D.le₂ hu) v (D.le₂ hv)
      have hV2L : V₂' ≤ L := hV2.trans hYLL
      have hF : ∀ x ∈ YL, (∀ v ∈ V₂', x * v = v * x) → ¬ 3 ∣ orderOf x → x ∈ V₂' := by
        intro x hx hxc h3
        have hd : orderOf x ∣ 2 ^ b * 9 := (Subgroup.orderOf_dvd_natCard YL hx).trans hYLd
        have hd2 : orderOf x ∣ 2 ^ b := by
          have hcop : Nat.Coprime (orderOf x) 9 := by
            have : Nat.Coprime (orderOf x) 3 :=
              ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3).symm
            simpa using this.pow_right 2
          exact hcop.dvd_of_dvd_mul_right hd
        obtain ⟨m, -, hm⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hd2
        let V' : Subgroup ↥L := V₂'.subgroupOf L
        have hV'4 : Nat.card V' = 4 := by
          rw [← D.card₂]
          exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV2L).toEquiv
        have hV'2 : ∀ v ∈ V', v ^ 2 = 1 := by
          intro v hv
          have : (v : G) ^ 2 = 1 := hV2sq v hv
          exact Subtype.ext (by simpa using this)
        have hV'c : ∀ u ∈ V', ∀ v ∈ V', u * v = v * u := fun u hu v hv =>
          Subtype.ext (hVc2 u hu v hv)
        exact hFour V' hV'4 hV'2 hV'c ⟨x, hYLL hx⟩ (fun v hv => Subtype.ext (hxc v hv))
          ⟨m, (Subgroup.orderOf_coe (⟨x, hYLL hx⟩ : ↥L)).symm.trans hm⟩
      have hact : ¬ YL ≤ Subgroup.centralizer (V₂' : Set G) := by
        intro hle
        apply hnP2
        intro x hx v hv
        exact (Subgroup.mem_centralizer_iff.mp (hle hx) v hv).symm
      obtain ⟨e⟩ := isAlt4_of_selfCent (K := YL) (V := V₂') (Y := YL) hV2 (hYLY.trans hY₂')
        D.card₂ hV2sq hVc2 hYLgen' hV2 hYL9 hact hF
      set C₁ : Subgroup G := Yp ⊓ Subgroup.centralizer (V₁' : Set G) with hC₁
      have hYLC₁ : YL ≤ C₁ := le_inf hYLY (fun x hx => by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (hP1 x hx v hv).symm)
      have hC₁card : Nat.card ↥C₁ = 3 * 2 ^ b := by
        have h1 := hh.hyp.card_Yplus_base h113 D
        rw [← hYY, hCV] at h1
        exact h1
      have hYLn : (YL.subgroupOf C₁).Normal :=
        (Subgroup.normal_subgroupOf_iff_le_normalizer hYLC₁).mpr (inf_le_left.trans hYLN)
      obtain ⟨c', hc'⟩ : ∃ c' : ℕ, YL.relIndex C₁ = 2 ^ c' := by
        have h1 := Subgroup.relIndex_mul_card YL C₁
        rw [inf_eq_left.mpr hYLC₁, hYLcard, hC₁card] at h1
        have h3 : YL.relIndex C₁ * 2 ^ a' = 2 ^ b :=
          Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) (by rw [← h1]; ring)
        obtain ⟨c', -, hc'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro (2 ^ a') h3)
        exact ⟨c', hc'⟩
      have hAle : oTwoUpper C₁ ≤ YL := by
        refine oTwoUpper_le_of_pow_mem fun x hx => ⟨c', ?_⟩
        have h1 : (⟨x, hx⟩ : ↥C₁) ^ (YL.subgroupOf C₁).index ∈ YL.subgroupOf C₁ :=
          Subgroup.pow_index_mem _ _
        have hidx : (YL.subgroupOf C₁).index = 2 ^ c' := hc'
        rw [Subgroup.mem_subgroupOf, hidx] at h1
        simpa using h1
      have hYLA : YL ≤ oTwoUpper C₁ := by
        refine (Subgroup.closure_le _).mpr fun x hx => ?_
        have hxYL : x ∈ YL := Subgroup.subset_closure hx
        exact Subgroup.subset_closure ⟨hYLC₁ hxYL, hx.2⟩
      have hAeq : YL = oTwoUpper C₁ := le_antisymm hYLA hAle
      have hA' : IsAlt 4 ↥(oTwoUpper (Y153 Mc M ⊓ Subgroup.centralizer (V₁' : Set G))) := by
        rw [← hYY]
        change IsAlt 4 ↥(oTwoUpper C₁)
        rw [← hAeq]
        exact ⟨e⟩
      have hle := hh.hyp.pCoreOf_Y153_le_VZ_of_isAlt h113 D hA'
      exact lt_irrefl _ (lt_of_lt_of_le (hnine G T Mc M hh.hyp) hle)
    rcases hcase with ⟨hP1, hV2, hn2⟩ | ⟨hP2, hV1, hn1⟩
    · exact hfin V₁ V₂ t hh.decomp hP1 hV2 hn2
    · exact hfin V₂ V₁ t hh.decomp.swapPlanes hP2 hV1 hn1

  ·
    exfalso
    have hYM : Y153 Mc M ≤ M := Y153_le Mc M
    obtain ⟨-, hN₂⟩ := hh.hyp.normalizer_V_le h113 hh.decomp hU
    obtain ⟨hY₁, hY₂⟩ := hh.hyp.Y153_le_normalizer_V h113 hh.decomp
    set K₁ : Subgroup G := Y153 Mc M ⊓ Subgroup.centralizer (V₁ : Set G) with hK₁
    have hYpK : Yp ≤ K₁ := by
      rw [hYp2]
      exact oTwoUpper_le K₁
    have hYpC1 : Yp ≤ Subgroup.centralizer (V₁ : Set G) := hYpK.trans inf_le_right
    have hYpY : Yp ≤ Y153 Mc M := hYpK.trans inf_le_left
    have hSYC : Sgp153 T V₁ ≤ Subgroup.normalizer (YC : Set G) := by
      have h1 : Sgp153 T V₁ ≤
          Subgroup.normalizer ((Yp ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
        fun s hs => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hSYp hs, B2F.le_normalizer_centralizer hSL hs⟩
      exact h1.trans (normalizer_le_normalizer_oTwoUpper _)
    have hVYC₂ : V₂ ≤ Subgroup.normalizer (YC : Set G) := fun v hv =>
      hSYC (hVS (hh.decomp.le₂ hv))
    have hYCV₂ : ∀ x ∈ YC, ∀ v ∈ V₂, x * v = v * x := by
      rcases centralizes_or_le_of_generated_by_threePow hYCgen hVYC₂
        (hYCY.trans (hYpY.trans hY₂)) hh.decomp.card₂ with h | ⟨hV, -⟩
      · exact h
      · exfalso
        apply c.c33.not_le
        intro l hl
        apply hN₂
        apply Subgroup.centralizer_le_normalizer (V₂ : Set G)
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (Subgroup.mem_centralizer_iff.mp (hYCC (hV hv)) l hl).symm
    have hYCV₁ : ∀ x ∈ YC, ∀ v ∈ V₁, x * v = v * x := fun x hx v hv =>
      (Subgroup.mem_centralizer_iff.mp (hYpC1 (hYCY hx)) v hv).symm
    have hYCV : ∀ x ∈ YC, ∀ v ∈ VZ T M, x * v = v * x := fun x hx =>
      hVcen x (hYCV₁ x hx) (hYCV₂ x hx)
    have hcomm2 := hh.hyp.commutator_V₂_Yplus h113 hh.decomp
    rw [← hYp2] at hcomm2
    have hYLV : ¬ ∀ x ∈ YL, ∀ v ∈ VZ T M, x * v = v * x := by
      intro hall
      have hYpV : ∀ y ∈ Yp, ∀ v ∈ VZ T M, y * v = v * y := by
        intro y hy v hv
        have hy' : y ∈ ((YL ⊔ YC : Subgroup G) : Set G) := by
          rw [← hY]
          exact hy
        rw [Subgroup.coe_mul_of_left_le_normalizer_right YL YC (le_normalizer_of_commute' hcomm)]
          at hy'
        obtain ⟨a, ha, b, hb, rfl⟩ := hy'
        calc a * b * v = a * (b * v) := by group
          _ = a * (v * b) := by rw [hYCV b hb v hv]
          _ = (a * v) * b := by group
          _ = (v * a) * b := by rw [hall a ha v hv]
          _ = v * (a * b) := by group
      have h1 : ⁅V₂, Yp⁆ = ⊥ := by
        rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
        intro v hv
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        exact hYpV y hy v (hh.decomp.le₂ hv)
      rw [hcomm2] at h1
      have := hh.decomp.card₂
      rw [h1, Subgroup.card_bot] at this
      omega
    set K : Subgroup G := YL ⊓ Subgroup.centralizer (VZ T M : Set G) with hKdef
    have hKYL : K ≤ YL := inf_le_left
    have hYLVN : YL ≤ Subgroup.normalizer (VZ T M : Set G) :=
      (hYLY.trans hYpY).trans (hYM.trans hh.hyp.le_normalizer)
    have hKn : (K.subgroupOf YL).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hKYL).mpr fun x hx =>
        Subgroup.inf_normalizer_le_normalizer_inf
          ⟨Subgroup.le_normalizer hx, B2F.le_normalizer_centralizer hYLVN hx⟩
    have hK3 : ¬ 3 ∣ Nat.card ↥K := by
      intro h3
      apply hYLV
      obtain ⟨c', hc'⟩ : ∃ c' : ℕ, K.relIndex YL = 2 ^ c' := by
        have h1 := Subgroup.relIndex_mul_card K YL
        rw [inf_eq_left.mpr hKYL, hYLcard] at h1
        obtain ⟨k, hk⟩ := h3
        rw [hk] at h1
        have h2 : K.relIndex YL * k = 2 ^ a' :=
          Nat.eq_of_mul_eq_mul_left (by norm_num : 0 < 3) (by rw [← h1]; ring)
        obtain ⟨c', -, hc'⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp (Dvd.intro k h2)
        exact ⟨c', hc'⟩
      have hall3 : ∀ x ∈ YL, (∃ k : ℕ, orderOf x = 3 ^ k) → x ∈ K := by
        intro x hx hxk
        obtain ⟨k, hk⟩ := hxk
        exact @mem_of_odd_of_index_two_pow G _ K YL hKn c' hc' x hx
          (by rw [hk]; exact Odd.pow (by decide))
      have hYLK : YL ≤ K :=
        hYLgen.trans ((Subgroup.closure_le K).mpr fun x hx => hall3 x hx.1 hx.2)
      intro x hx v hv
      exact (Subgroup.mem_centralizer_iff.mp (hYLK hx).2 v hv).symm
    have hodd_b : ∀ x ∈ Yp ⊓ Subgroup.centralizer (VZ T M : Set G), Odd (orderOf x) → x ∈ YC := by
      rintro x ⟨hxYp, hxC⟩ hxodd
      have hxmem : x ∈ ((YL ⊔ YC : Subgroup G) : Set G) := by
        rw [← hY]
        exact hxYp
      rw [Subgroup.coe_mul_of_left_le_normalizer_right YL YC (le_normalizer_of_commute' hcomm)]
        at hxmem
      obtain ⟨a, ha, b, hb, rfl⟩ := hxmem
      have hbC : b ∈ Subgroup.centralizer (VZ T M : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (hYCV b hb v hv).symm
      have haC : a ∈ Subgroup.centralizer (VZ T M : Set G) := by
        have : a = (a * b) * b⁻¹ := by group
        rw [this]
        exact Subgroup.mul_mem _ hxC (Subgroup.inv_mem _ hbC)
      have haK : a ∈ K := ⟨ha, haC⟩
      set m := orderOf (a * b) with hm
      have hmpow : (a * b) ^ m = 1 := pow_orderOf_eq_one _
      have hcomm' : Commute a b := hcomm a ha b hb
      have h1 : a ^ m * b ^ m = 1 := by
        rw [← hcomm'.mul_pow]
        exact hmpow
      have h2 : a ^ m ∈ YL ⊓ YC := ⟨YL.pow_mem ha m, by
        have : a ^ m = (b ^ m)⁻¹ := eq_inv_of_mul_eq_one_left h1
        rw [this]
        exact YC.inv_mem (YC.pow_mem hb m)⟩
      rw [hdisj, Subgroup.mem_bot] at h2
      have haodd : Odd (orderOf a) := hxodd.of_dvd_nat (orderOf_dvd_of_pow_eq_one h2)
      obtain ⟨k, hk⟩ := hodd3 a (hYLY ha) haodd
      have hk0 : k = 0 := by
        by_contra hk0
        apply hK3
        have h3 : 3 ∣ orderOf a := by
          rw [hk]
          exact dvd_pow_self 3 hk0
        exact h3.trans (Subgroup.orderOf_dvd_natCard K haK)
      rw [hk0, pow_zero, orderOf_eq_one_iff] at hk
      have hab : a * b = b := by rw [hk, one_mul]
      show a * b ∈ YC
      rw [hab]
      exact hb
    have hWYC : oTwoUpper (Yp ⊓ Subgroup.centralizer (VZ T M : Set G)) ≤ YC :=
      (Subgroup.closure_le YC).mpr fun x hx => hodd_b x hx.1 hx.2
    have hYCW : YC ≤ oTwoUpper (Yp ⊓ Subgroup.centralizer (VZ T M : Set G)) := by
      have h1 : YC ≤ Yp ⊓ Subgroup.centralizer (VZ T M : Set G) :=
        le_inf hYCY fun x hx => by
          rw [Subgroup.mem_centralizer_iff]
          intro v hv
          exact (hYCV x hx v hv).symm
      exact (S153D.le_oTwoUpper_oTwoUpper _).trans (oTwoUpper_mono h1)
    set W : Subgroup G := oTwoUpper (Yp ⊓ Subgroup.centralizer (VZ T M : Set G)) with hWdef
    have hWeq : W = YC := le_antisymm hWYC hYCW
    have hYK : Y153 Mc M ≤ Subgroup.normalizer (K₁ : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf
        ⟨Subgroup.le_normalizer hg, B2F.le_normalizer_centralizer hY₁ hg⟩
    have hYYp : Y153 Mc M ≤ Subgroup.normalizer (Yp : Set G) := by
      rw [hYp2]
      exact hYK.trans (normalizer_le_normalizer_oTwoUpper K₁)
    have hYV : Y153 Mc M ≤ Subgroup.normalizer (VZ T M : Set G) := hYM.trans hh.hyp.le_normalizer
    have hYK₃ : Y153 Mc M ≤
        Subgroup.normalizer ((Yp ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) :=
      fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
        ⟨hYYp hg, B2F.le_normalizer_centralizer hYV hg⟩
    have hYW : Y153 Mc M ≤ Subgroup.normalizer (W : Set G) :=
      hYK₃.trans (normalizer_le_normalizer_oTwoUpper _)
    have hSW : Sgp153 T V₁ ≤ Subgroup.normalizer (W : Set G) := by
      have hSV : Sgp153 T V₁ ≤ Subgroup.normalizer (VZ T M : Set G) :=
        hSM.trans hh.hyp.le_normalizer
      have h1 : Sgp153 T V₁ ≤
          Subgroup.normalizer ((Yp ⊓ Subgroup.centralizer (VZ T M : Set G) : Subgroup G) : Set G) :=
        fun g hg => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hSYp hg, B2F.le_normalizer_centralizer hSV hg⟩
      exact h1.trans (normalizer_le_normalizer_oTwoUpper _)
    have hchar : CharTwo W := by
      obtain ⟨S', hS'⟩ := hh.hyp.qtfe.exists_sylow
      have hSM' : (S' : Subgroup G) ≤ M := hS' ▸ hh.hyp.T_le
      have c1 : CharTwo M := hh.hyp.qtfe.qtke.2.1 M hh.hyp.inM.1.1 ⟨S', hSM'⟩
      have c2 : CharTwo (Y153 Mc M) := A4.charTwo_of_normal hYM (le_normalizer_Y153 Mc M) c1
      have c3 : CharTwo (Yp ⊓ Subgroup.centralizer (VZ T M : Set G)) :=
        A4.charTwo_of_normal (inf_le_left.trans hYpY) hYK₃ c2
      exact A4.charTwo_of_normal (oTwoUpper_le _) (le_normalizer_oTwoUpper _) c3
    have hO : pCoreOf 2 W ≠ ⊥ := by
      intro hb
      have hWbot : W = ⊥ := by
        have h1 : W ⊓ Subgroup.centralizer (pCoreOf 2 W : Set G) ≤ pCoreOf 2 W := hchar
        rw [hb] at h1
        rw [eq_bot_iff]
        intro x hx
        exact h1 ⟨hx, Subgroup.mem_centralizer_iff.2 fun y hy => by
          rw [show (y : G) = 1 from by simpa using hy, mul_one, one_mul]⟩
      rw [hWeq] at hWbot
      have h1 : Nat.card ↥YC = 1 := by rw [hWbot, Subgroup.card_bot]
      rw [h1] at hYC3
      omega
    have hle : Y153 Mc M ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer (pCoreOf 2 W : Set G) :=
      sup_le (hYW.trans (normalizer_le_normalizer_pCoreOf 2 W))
        (hSW.trans (normalizer_le_normalizer_pCoreOf 2 W))
    have hCO : pCoreOf 2 W ≤ pCoreOf 2 (Subgroup.normalizer (pCoreOf 2 W : Set G)) :=
      le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl (pCoreOf_isPGroup 2 _)
    have hH : InH (Y153 Mc M ⊔ Sgp153 T V₁) (Subgroup.normalizer (pCoreOf 2 W : Set G)) :=
      ⟨hle, fun hb => hO (le_bot_iff.mp (hb ▸ hCO))⟩
    have hMle : Subgroup.normalizer (pCoreOf 2 W : Set G) ≤ M := le_of_isUniqueM hU hH
    apply c.c33.not_le
    intro l hl
    apply hMle
    apply normalizer_le_normalizer_pCoreOf 2 W
    apply Subgroup.centralizer_le_normalizer (W : Set G)
    rw [hWeq, Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp (hYCC hy) l hl).symm

end CFSG.Quasithin.R3c9

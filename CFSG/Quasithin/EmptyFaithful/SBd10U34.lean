module

public import CFSG.Quasithin.EmptyFaithful.R3c9Two
public import CFSG.Quasithin.EmptyFaithful.SBd9Sym

public section

namespace CFSG.Quasithin.SBd10

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.Quasithin CFSG.QuasithinUnique CFSG.Quasithin.R3c2
  CFSG.Quasithin.R3c3 CFSG.LieType.BorelTits CFSG.Quasithin.R3c9 CFSG.Quasithin.SBd9
open scoped MatrixGroups commutatorElement

variable {G : Type} [Group G] [Finite G] {T Mc M V₁ V₂ Yp I L : Subgroup G} {t : G}

theorem u34_structure (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hL0 : L = conjClosure L (Sgp153 T V₁)) (hLs : IsSimpleGroup ↥L)
    (hY : Yp = oTwoUpper (Yp ⊓ L) ⊔ oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)))
    (h3L : padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ L))) = 1)
    (h3C : padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)))) = 1)
    (hE9 : IsElemAbelianOfRank 3 2 (OTwoQuot Yp)) (h113 : StageLemma14113) :
    Yp = Y153 Mc M ∧
      ((V₁ ≤ oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)) ∧
          (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) ∧ V₂ ≤ oTwoUpper (Yp ⊓ L) ∧
          ¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) ∨
        (V₂ ≤ oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)) ∧
          (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) ∧ V₁ ≤ oTwoUpper (Yp ⊓ L) ∧
          ¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y)) := by
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
    have hSYC : Sgp153 T V₁ ≤ Subgroup.normalizer (YC : Set G) := by
      have h1 : Sgp153 T V₁ ≤
          Subgroup.normalizer ((Yp ⊓ Subgroup.centralizer (L : Set G) : Subgroup G) : Set G) :=
        fun s hs => Subgroup.inf_normalizer_le_normalizer_inf
          ⟨hSYp hs, B2F.le_normalizer_centralizer hSL hs⟩
      exact h1.trans (normalizer_le_normalizer_oTwoUpper _)
    have hV₁YC : V₁ ≤ Subgroup.normalizer (YC : Set G) := fun v hv => hSYC (hVS (hh.decomp.le₁ hv))
    have hV₂YC : V₂ ≤ Subgroup.normalizer (YC : Set G) := fun v hv => hSYC (hVS (hh.decomp.le₂ hv))
    refine ⟨hYY, ?_⟩
    rcases hcase with ⟨hP1, hV2, hn2⟩ | ⟨hP2, hV1, hn1⟩
    · left
      refine ⟨?_, hP1, hV2, hn2⟩
      have hYCV₂ : ∀ x ∈ YC, ∀ v ∈ V₂, x * v = v * x := fun x hx v hv =>
        (Subgroup.mem_centralizer_iff.mp (hYCC hx) v (hYLL (hV2 hv))).symm
      rcases centralizes_or_le_of_generated_by_threePow hYCgen hV₁YC (hYCY.trans hY₁)
        hh.decomp.card₁ with h | ⟨hV, -⟩
      · exfalso
        apply hnotC YC hYCY hYC3
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (hVcen x (h x hx) (hYCV₂ x hx) v hv).symm
      · exact hV
    · right
      refine ⟨?_, hP2, hV1, hn1⟩
      have hYCV₁ : ∀ x ∈ YC, ∀ v ∈ V₁, x * v = v * x := fun x hx v hv =>
        (Subgroup.mem_centralizer_iff.mp (hYCC hx) v (hYLL (hV1 hv))).symm
      rcases centralizes_or_le_of_generated_by_threePow hYCgen hV₂YC (hYCY.trans hY₂)
        hh.decomp.card₂ with h | ⟨hV, -⟩
      · exfalso
        apply hnotC YC hYCY hYC3
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        exact (hVcen x (hYCV₁ x hx) (h x hx) v hv).symm
      · exact hV

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

theorem u34_borel (c : CtxComp2 T Mc M V₁ V₂ Yp I L t)
    (hL0 : L = conjClosure L (Sgp153 T V₁)) (hLs : IsSimpleGroup ↥L)
    (hY : Yp = oTwoUpper (Yp ⊓ L) ⊔ oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)))
    (hBender : fusionIsBenderGroup ↥L) :
    Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ∧
      L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ M ⊓ I ∧
      Sgp153 T V₁ ⊓ L ≤ Subgroup.centralizer (VZ T M : Set G) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hLI : L ≤ I := le_of_mem_cComp c.c33.mem
  have hSL : Sgp153 T V₁ ≤ Subgroup.normalizer (L : Set G) := by
    have := le_normalizer_conjClosure L (Sgp153 T V₁)
    rwa [← hL0] at this
  have hSyl : IsSylowTwoOf (Sgp153 T V₁) I := c.facts.sylow
  have hQsyl : IsSylowTwoOf (Sgp153 T V₁ ⊓ L) L :=
    A4.isSylowTwoOf_inf_normal (A4.isSylowTwoOf_mono hSyl (le_inf hSyl.1 hSL) inf_le_left)
      (le_inf hLI Subgroup.le_normalizer) inf_le_right
  have hSM : Sgp153 T V₁ ≤ M := inf_le_left.trans hh.hyp.T_le
  have hYpM : Yp ≤ M := hh.Yp_le_Y153.trans (Y153_le Mc M)
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
  have hYpN : Yp ≤ Subgroup.normalizer (L : Set G) := by
    rw [hY]
    exact sup_le (hYLL.trans Subgroup.le_normalizer)
      (hYCC.trans (Subgroup.centralizer_le_normalizer _))
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
  have hBX : Yp ⊔ Sgp153 T V₁ ≤
      Subgroup.normalizer ((L ⊓ Subgroup.normalizer (Q : Set G) : Subgroup G) : Set G) :=
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
  refine ⟨hXQ, hBMI, ?_⟩
  have h1 : Q ≤ R153 T V₁ Yp :=
    le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) hXQ hQsyl.2.1
  rw [c.facts11.R_eq] at h1
  exact h1.trans inf_le_right

@[expose] def Input15340U34Rest : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M V₁ V₂ Yp I L : Subgroup G) (t : G),
    CtxComp2 T Mc M V₁ V₂ Yp I L t → L = conjClosure L (Sgp153 T V₁) →
      CFSG.Open.pRank 3 L = 1 → IsPSU 3 2 2 (↥L ⧸ Subgroup.center ↥L) → IsSimpleGroup ↥L →
      Yp = oTwoUpper (Yp ⊓ L) ⊔ oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)) →
      padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ L))) = 1 →
      padicValNat 3 (Nat.card ↥(oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)))) = 1 →
      IsElemAbelianOfRank 3 2 (OTwoQuot Yp) → ¬ Yp ≤ L →
      Yp = Y153 Mc M →
      Yp ⊔ Sgp153 T V₁ ≤ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) →
      L ⊓ Subgroup.normalizer ((Sgp153 T V₁ ⊓ L : Subgroup G) : Set G) ≤ M ⊓ I →
      Sgp153 T V₁ ⊓ L ≤ Subgroup.centralizer (VZ T M : Set G) →
      V₁ ≤ oTwoUpper (Yp ⊓ Subgroup.centralizer (L : Set G)) →
      (∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₁, y * v = v * y) → V₂ ≤ oTwoUpper (Yp ⊓ L) →
      (¬ ∀ y ∈ oTwoUpper (Yp ⊓ L), ∀ v ∈ V₂, y * v = v * y) → False

section Main

theorem input15340U34_of_rest (h113 : StageLemma14113) (hlist : Lemma115_3_List)
    (hA : R3c2.Input15333Two) (kRest : Input15340U34Rest) : Input15340U34 := by
  intro G _ _ T Mc M V₁ V₂ Yp I L t c hL0 hr hU hY h3L h3C hE9 hnot
  have hh : Hyp15310 G T Mc M V₁ V₂ Yp t := c.hyp
  have hq := hh.hyp.qtfe
  obtain ⟨z, hz⟩ := hA G T Mc M V₁ V₂ Yp I t c.toCtxComp
  have hcomp : IsComponentIn L I :=
    Id2519.isComponentIn_of_mem_cComp c.c33.mem c.c33.quasisimple
  have hsimpleG : IsSimpleGroup G := hq.simple
  have hcore : QTKECore G := qtkeCore_of_cat hq.nonabelian hq.qtke
  have hcases : Lemma115Cases L z :=
    (Lemma115_3_List.component_cases hlist hsimpleG hq.nonabelian hcore hz hcomp).2.2.2
  have hLs : IsSimpleGroup ↥L := isSimple_of_lemma115_rankOne hcases c.c33.center_eq hr
  have hperf : Group.IsPerfect ↥L := c.c33.quasisimple.1
  let eC := R3c3.quotCenterEquivOfSimple hLs hperf
  have hU' : IsPSU 3 2 2 ↥L := R3c3.isPSU_of_mulEquiv eC.symm hU
  have hBender : fusionIsBenderGroup ↥L :=
    K1.fusionIsBenderGroup_of_stated_psu_three (by norm_num) hU'
  obtain ⟨hYY, halt⟩ := u34_structure c hL0 hLs hY h3L h3C hE9 h113
  obtain ⟨hB, hBM, hQV⟩ := u34_borel c hL0 hLs hY hBender
  rcases halt with ⟨h1, h2, h3, h4⟩ | ⟨h1, h2, h3, h4⟩
  · exact kRest G T Mc M V₁ V₂ Yp I L t c hL0 hr hU hLs hY h3L h3C hE9 hnot hYY hB hBM hQV h1 h2 h3 h4
  ·
    have hS := sgp153_swap c.hyp.hyp c.hyp.decomp
    have c' := ctxComp2_swap c hYY
    have hL0' : L = conjClosure L (Sgp153 T V₂) := by rw [hS]; exact hL0
    rw [← hS] at hB hBM hQV
    exact kRest G T Mc M V₂ V₁ Yp I L t c' hL0' hr hU hLs hY h3L h3C hE9 hnot hYY hB hBM hQV
      h1 h2 h3 h4

end Main

end CFSG.Quasithin.SBd10

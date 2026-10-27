module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8KSet
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveTwentyTwo
import CFSG.GroupTheory.PCore.InfPCoreOf
import CFSG.Quasithin.Background.B1MoreTwelveA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {G : Type} [Group G] [Finite G]

theorem c8_c0_cent (D : Data G) {V₀ V L K : Subgroup G} (hMs : D.M ≤ stabTil V₀ V)
    (hLM : L ≤ D.M) (hGood : C8Good D V₀ V L) {d : ↥K} (hdL : (d : G) ∈ L) :
    ∀ R : Subgroup ↥K, R ≤ c8kC0 D V₀ V K → IsPGroup 7 R → (∀ x ∈ R, d * x * d⁻¹ ∈ R) →
      ∀ x ∈ R, d * x = x * d := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 7) := ⟨Nat.prime_seven⟩
  have hLN : D.M ≤ Subgroup.normalizer (L : Set G) := hGood.1
  have hL2 : IsPGroup 2 ↥(L ⊓ F11.CTilde D.M V₀ V) := hGood.2
  have hcT : F11.CTilde D.M V₀ V ≤ D.M :=
    (iInf₂_le 1 V.one_mem).trans fun _ hm => hm.1
  have hnorm : ∀ g ∈ D.M, ∀ y ∈ F11.CTilde D.M V₀ V,
      g * y * g⁻¹ ∈ F11.CTilde D.M V₀ V := by
    intro g hgM y hy
    have hgV : g ∈ Subgroup.normalizer (V : Set G) := stabTil_le_normalizer V₀ V (hMs hgM)
    have hgV0 : g ∈ Subgroup.normalizer (V₀ : Set G) :=
      stabTil_le_normalizer₀ V₀ V (hMs hgM)
    simp only [F11.CTilde, Subgroup.mem_iInf] at hy ⊢
    intro v hv
    have hv' : g⁻¹ * v * g ∈ V := (Subgroup.mem_normalizer_iff''.1 hgV v).1 hv
    obtain ⟨hyM, hyN, hyC⟩ := hy (g⁻¹ * v * g) hv'
    refine ⟨D.M.mul_mem (D.M.mul_mem hgM hyM) (D.M.inv_mem hgM),
      Subgroup.mul_mem _ (Subgroup.mul_mem _ hgV0 hyN) (Subgroup.inv_mem _ hgV0), ?_⟩
    have hconj : g * (y * (g⁻¹ * v * g) * y⁻¹ * (g⁻¹ * v * g)⁻¹) * g⁻¹ ∈ V₀ :=
      (Subgroup.mem_normalizer_iff.1 hgV0 _).1 hyC
    convert hconj using 1
    group
  intro R hR hR7 hRnorm x hxR
  have hxinf : (x : G) ∈ K ⊓ F11.CTilde D.M V₀ V := Subgroup.mem_subgroupOf.1 (hR hxR)
  have hxCT : (x : G) ∈ F11.CTilde D.M V₀ V := hxinf.2
  have hxM : (x : G) ∈ D.M := hcT hxCT
  have hdM : (d : G) ∈ D.M := hLM hdL
  have hcR : x * d * x⁻¹ * d⁻¹ ∈ R := by
    have h1 : d * x⁻¹ * d⁻¹ ∈ R := by
      have h := R.inv_mem (hRnorm x hxR)
      convert h using 1
      group
    have h2 := R.mul_mem hxR h1
    simpa only [mul_assoc] using h2
  have hcL : ((x * d * x⁻¹ * d⁻¹ : ↥K) : G) ∈ L := by
    have hxN : (x : G) ∈ Subgroup.normalizer (L : Set G) := hLN hxM
    have h1 : (x : G) * (d : G) * (x : G)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.1 hxN (d : G)).1 hdL
    have h2 : ((x * d * x⁻¹ * d⁻¹ : ↥K) : G) =
        (x : G) * (d : G) * (x : G)⁻¹ * (d : G)⁻¹ := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h2]
    exact L.mul_mem h1 (L.inv_mem hdL)
  have hcCT : ((x * d * x⁻¹ * d⁻¹ : ↥K) : G) ∈ F11.CTilde D.M V₀ V := by
    have hxinv : (x : G)⁻¹ ∈ F11.CTilde D.M V₀ V := (F11.CTilde D.M V₀ V).inv_mem hxCT
    have hz : (d : G) * (x : G)⁻¹ * (d : G)⁻¹ ∈ F11.CTilde D.M V₀ V :=
      hnorm (d : G) hdM ((x : G)⁻¹) hxinv
    have h1 : (x : G) * ((d : G) * (x : G)⁻¹ * (d : G)⁻¹) ∈ F11.CTilde D.M V₀ V :=
      (F11.CTilde D.M V₀ V).mul_mem hxCT hz
    have h2 : ((x * d * x⁻¹ * d⁻¹ : ↥K) : G) =
        (x : G) * ((d : G) * (x : G)⁻¹ * (d : G)⁻¹) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc]
    rw [h2]
    exact h1
  set w : ↥K := x * d * x⁻¹ * d⁻¹ with hw
  have hwR : w ∈ R := hcR
  have hwmem : (w : G) ∈ L ⊓ F11.CTilde D.M V₀ V := ⟨hcL, hcCT⟩
  obtain ⟨a, ha⟩ := hL2.exists_orderOf_eq_pow (⟨(w : G), hwmem⟩ : ↥(L ⊓ F11.CTilde D.M V₀ V))
  obtain ⟨b, hb⟩ := hR7.exists_orderOf_eq_pow (⟨w, hwR⟩ : ↥R)
  have ha' : orderOf w = 2 ^ a := by
    rw [← Subgroup.orderOf_coe w]
    exact (Subgroup.orderOf_coe (⟨(w : G), hwmem⟩ : ↥(L ⊓ F11.CTilde D.M V₀ V))).trans ha
  have hb' : orderOf w = 7 ^ b :=
    (Subgroup.orderOf_coe (⟨w, hwR⟩ : ↥R)).trans hb
  have hcop : Nat.Coprime (2 ^ a) (7 ^ b) :=
    Nat.Coprime.pow_right b (Nat.Coprime.pow_left a (by norm_num : Nat.Coprime 2 7))
  have h1 : orderOf w = 1 :=
    Nat.eq_one_of_dvd_coprimes hcop (by rw [ha']) (by rw [hb'])
  have hw1 : w = 1 := orderOf_eq_one_iff.1 h1
  rw [hw] at hw1
  have hconj : x * d * x⁻¹ = d := mul_inv_eq_one.1 hw1
  have hfinal : x * d = d * x := by
    calc x * d = (x * d * x⁻¹) * x := by group
      _ = d * x := by rw [hconj]
  exact hfinal.symm

private theorem c8k_map_subtype_top (K : Subgroup G) :
    (⊤ : Subgroup ↥K).map K.subtype = K := by
  ext x
  rw [Subgroup.mem_map]
  constructor
  · rintro ⟨y, -, rfl⟩
    exact y.2
  · rintro hx
    exact ⟨⟨x, hx⟩, trivial, rfl⟩

private theorem c8k_charTwo_of_le {K K₁ : Subgroup G} (hK₁K : K₁ ≤ K)
    (hQ : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 K₁)
    (hchar : CFSG.QuasithinUnique.CharTwo K) : CFSG.QuasithinUnique.CharTwo K₁ := by
  have hcent : Subgroup.centralizer (CFSG.Open.pCoreOf 2 K₁ : Set G) ≤
      Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    Subgroup.centralizer_le hQ
  have h1 : K₁ ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K₁ : Set G) ≤
      K ⊓ Subgroup.centralizer (CFSG.Open.pCoreOf 2 K : Set G) :=
    le_inf (inf_le_left.trans hK₁K) (inf_le_right.trans hcent)
  exact h1.trans (hchar.trans hQ)

theorem c8_minimal (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {v₀ : IntMod V hV} {T₀ K T' : Subgroup G} (hLM : L ≤ D.M) (hGood : C8Good D V₀ V L)
    (hU : C8SetUp D V₀ V L hV v₀ T₀ K T') (hQ : CFSG.pCore 2 ↥K ≤ c8kB D K) :
    ∀ O : Subgroup ↥K, O.Normal → ¬ O ≤ c8kB D K →
      ∃ Y : Subgroup ↥K, Y ≤ c8kB D K ∧ Y ⊔ O = ⊤ ∧
        ∀ y ∈ Y, y ∈ c8kC0 D V₀ V K → Odd (orderOf y) → y = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro O hOn hOB
  let C : Subgroup G := L ⊓ Subgroup.centralizer ({v₀.val} : Set G)
  let O' : Subgroup G := O.map K.subtype
  have hT₀M : T₀ ≤ D.M := hU.sylow.le.trans inf_le_left
  have hT₀_le : T₀ ≤ K ⊓ D.M := le_inf hU.mem.1 hT₀M
  obtain ⟨S₁, hS₁, hT₀S₁⟩ := exists_isSylowIn_ge 2 hT₀_le hU.sylow.isPGroup
  have hS₁K : S₁ ≤ K := hS₁.le.trans inf_le_left
  have hS₁M : S₁ ≤ D.M := hS₁.le.trans inf_le_right
  have hO'M : ¬ O' ≤ D.M := by
    intro h
    apply hOB
    intro o ho
    exact Subgroup.mem_subgroupOf.2 (show (o : G) ∈ K ⊓ D.M from
      ⟨o.2, h (Subgroup.mem_map_of_mem K.subtype ho)⟩)
  have hQ_le : CFSG.Open.pCoreOf 2 K ≤ K ⊓ D.M := by
    show (CFSG.pCore 2 ↥K).map K.subtype ≤ K ⊓ D.M
    have h1 : (CFSG.pCore 2 ↥K).map K.subtype ≤ ((K ⊓ D.M).subgroupOf K).map K.subtype :=
      Subgroup.map_mono hQ
    rw [Subgroup.subgroupOf_map_subtype] at h1
    rwa [inf_eq_left.2 (inf_le_left : K ⊓ D.M ≤ K)] at h1
  have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 K) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥K)).map K.subtype
  have hQn : ((CFSG.Open.pCoreOf 2 K).subgroupOf (K ⊓ D.M)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQ_le).2
      (inf_le_left.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (r := 2) K))
  have hQS₁ : CFSG.Open.pCoreOf 2 K ≤ S₁ := IsSylowIn.le_of_normal hS₁ hQ_le hQn hQ2
  let Y₀ : Subgroup G := C ⊔ S₁
  have hCK : C ≤ K := hU.mem.2.1
  have hY₀K : Y₀ ≤ K := sup_le hCK hS₁K
  have hY₀M : Y₀ ≤ D.M := sup_le (inf_le_left.trans hLM) hS₁M
  let K₁ : Subgroup G := Y₀ ⊔ O'
  have hO'K : O' ≤ K := Subgroup.map_subtype_le O
  have hK₁K : K₁ ≤ K := sup_le hY₀K hO'K
  have hS₁K₁ : S₁ ≤ K₁ := le_sup_right.trans le_sup_left
  have hQK₁ : CFSG.Open.pCoreOf 2 K ≤ K₁ := hQS₁.trans hS₁K₁
  have hQleK₁ : CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 K₁ := by
    have h1 : K₁ ⊓ CFSG.Open.pCoreOf 2 K ≤ CFSG.Open.pCoreOf 2 K₁ :=
      CFSG.GroupTheory.inf_pCoreOf_le_pCoreOf 2 hK₁K
    rwa [inf_eq_right.2 hQK₁] at h1
  have hcharK₁ : CFSG.QuasithinUnique.CharTwo K₁ :=
    c8k_charTwo_of_le hK₁K hQleK₁ hU.mem.2.2.2
  have hK₁notM : ¬ K₁ ≤ D.M := fun h => hO'M (le_sup_right.trans h)
  have hSp6K₁ : Sp6InL D L v₀.val T₀ K₁ :=
    ⟨hT₀S₁.trans (le_sup_right.trans le_sup_left),
      (le_sup_left.trans le_sup_left : C ≤ K₁), hK₁notM, hcharK₁⟩
  have hS₁inf : S₁ ≤ K₁ ⊓ D.M := le_inf hS₁K₁ hS₁M
  have hcardS₁ : Nat.card ↥S₁ = 2 ^ padicValNat 2 (Nat.card ↥(K ⊓ D.M)) := by
    rw [hS₁.card_eq, Nat.factorization_def _ Nat.prime_two]
  have hpad : padicValNat 2 (Nat.card ↥(K ⊓ D.M)) ≤
      padicValNat 2 (Nat.card ↥(K₁ ⊓ D.M)) := by
    refine (padicValNat_dvd_iff_le (p := 2) (a := Nat.card ↥(K₁ ⊓ D.M))
      (n := padicValNat 2 (Nat.card ↥(K ⊓ D.M))) Nat.card_pos.ne').1 ?_
    rw [← hcardS₁]
    exact Subgroup.card_dvd_of_le hS₁inf
  have heq : padicValNat 2 (Nat.card ↥(K₁ ⊓ D.M)) = padicValNat 2 (Nat.card ↥(K ⊓ D.M)) :=
    le_antisymm (hU.max K₁ hSp6K₁) hpad
  have hK₁eq : K₁ = K := hU.min K₁ hSp6K₁ heq hK₁K
  let Y : Subgroup ↥K := Y₀.subgroupOf K
  have hYle : Y ≤ c8kB D K := Subgroup.subgroupOf_mono K (le_inf hY₀K hY₀M)
  have hsup : Y ⊔ O = ⊤ := by
    change (Y₀.subgroupOf K) ⊔ O = ⊤
    refine Subgroup.map_injective K.subtype_injective ?_
    rw [Subgroup.map_sup, Subgroup.map_subgroupOf_eq_of_le hY₀K]
    show Y₀ ⊔ O.map K.subtype = (⊤ : Subgroup ↥K).map K.subtype
    rw [c8k_map_subtype_top K]
    exact hK₁eq
  refine ⟨Y, hYle, hsup, ?_⟩
  intro y hyY hyC0 hyodd
  have hyY₀ : (y : G) ∈ Y₀ := Subgroup.mem_subgroupOf.1 hyY
  have hyCT : (y : G) ∈ F11.CTilde D.M V₀ V := (Subgroup.mem_subgroupOf.1 hyC0).2
  have hY₀le : Y₀ ≤ L ⊔ S₁ := by
    change C ⊔ S₁ ≤ L ⊔ S₁
    exact sup_le (inf_le_left.trans le_sup_left) le_sup_right
  have hyL : (y : G) ∈ L :=
    B1Red.mem_of_odd_orderOf_of_mem_sup (N := L) (T := S₁) hS₁.isPGroup
      (hS₁M.trans hGood.1) (hY₀le hyY₀) (by rw [Subgroup.orderOf_coe]; exact hyodd)
  have hLCT : (y : G) ∈ L ⊓ F11.CTilde D.M V₀ V := ⟨hyL, hyCT⟩
  obtain ⟨a, ha⟩ := hGood.2.exists_orderOf_eq_pow
    (⟨(y : G), hLCT⟩ : ↥(L ⊓ F11.CTilde D.M V₀ V))
  have h2pow : orderOf y = 2 ^ a := by
    rw [← Subgroup.orderOf_coe y]
    exact (Subgroup.orderOf_coe (⟨(y : G), hLCT⟩ : ↥(L ⊓ F11.CTilde D.M V₀ V))).trans ha
  have hcop : Nat.Coprime (orderOf y) (2 ^ a) :=
    Nat.Coprime.pow_right a (Nat.coprime_two_right.2 hyodd)
  have hone : orderOf y = 1 := Nat.eq_one_of_dvd_coprimes hcop dvd_rfl (by rw [h2pow])
  exact orderOf_eq_one_iff.1 hone

theorem c8_exists_w (D : Data G) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {v₀ : IntMod V hV} {T₀ K T' : Subgroup G} (hS : Sect16 D V₀ V L hV) (hV₀ : V₀ ≠ ⊥)
    (hU : C8SetUp D V₀ V L hV v₀ T₀ K T') :
    ∃ w : ↥K, w ∈ c8kS K T' ∧ w ≠ 1 ∧ w ^ 2 = 1 ∧ (∀ s ∈ c8kS K T', w * s = s * w) ∧
      centralizer ({w} : Set ↥K) ≤ c8kB D K := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hyp125 : Hyp125 D V₀ V := hS.setting.hyp16.hyp125
  have hP : PairFacts D.M V₀ V := hyp125.pairFacts
  have hcu : CentralizersUnique D.M D.T :=
    TwelveTwentyTwo.centralizersUnique_of_hyp125 hyp125 hV₀
  have hV2 : IsPGroup 2 V := by
    intro x
    exact ⟨1, Subtype.ext (by simpa using hV.2 x x.2)⟩
  have hSylT' : IsSylowIn 2 T' D.M := CFSG.ABGLocalTools.isSylowOf_iff.1 hU.sylowM
  have hVT' : V ≤ T' := by
    refine IsSylowIn.le_of_normal hSylT' hP.le_M ?_ hV2
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hP.le_M]
    exact hP.le_normalizer
  have hVcent : V ≤ Subgroup.centralizer ({v₀.val} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact (congrArg Subtype.val
      ((isMulCommutative_iff.1 hV.1) ⟨x, hx⟩ ⟨v₀.val, v₀.val_mem⟩)).symm
  have hVinf : V ≤ D.M ⊓ Subgroup.centralizer ({v₀.val} : Set G) :=
    fun x hx => ⟨hP.le_M hx, hVcent hx⟩
  have hVT₀ : V ≤ T₀ := by
    refine IsSylowIn.le_of_normal hU.sylow hVinf ?_ hV2
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hVinf]
    exact inf_le_left.trans hP.le_normalizer
  have hVTK : V ≤ K := hVT₀.trans hU.mem.1
  obtain ⟨w, hwV, hwc, hw1⟩ := TwelveTwentyTwo.exists_ne_one_mem_inf_center
    (T := T') (W := V) hSylT'.isPGroup hVT' (hSylT'.le.trans hP.le_normalizer) hP.ne_bot
  have hwK : w ∈ K := hVTK hwV
  set w' : ↥K := ⟨w, hwK⟩ with hw'
  have hwS : w' ∈ c8kS K T' := by
    rw [c8kS, Subgroup.mem_subgroupOf]
    rw [hw']
    exact ⟨hVT' hwV, hwK⟩
  have hw'1 : w' ≠ 1 := by
    intro h
    exact hw1 (by simpa [hw'] using congrArg Subtype.val h)
  have hw'2 : w' ^ 2 = 1 := by
    apply Subtype.ext
    rw [hw']
    simpa using hV.2 w hwV
  have hcent : ∀ s ∈ c8kS K T', w' * s = s * w' := by
    intro s hs
    have hsT' : (s : G) ∈ T' := (Subgroup.mem_subgroupOf.1 hs).1
    apply Subtype.ext
    simpa using hwc (s : G) hsT'
  refine ⟨w', hwS, hw'1, hw'2, hcent, ?_⟩
  intro x hx
  have hxw : (x : G) * w = w * (x : G) := by
    have h1 := (Subgroup.mem_centralizer_iff.1 hx) w' (Set.mem_singleton w')
    exact (congrArg Subtype.val h1).symm
  obtain ⟨k, hkM, hk⟩ := CFSG.ABGLocalTools.IsSylowOf.exists_mem_conj D.sylowM hU.sylowM
  have hw''T : k⁻¹ * w * k ∈ D.T := (hk w).1 (hVT' hwV)
  have hw''c : ∀ t ∈ D.T, (k⁻¹ * w * k) * t = t * (k⁻¹ * w * k) := by
    intro t ht
    have ht' : k * t * k⁻¹ ∈ T' := by
      refine (hk (k * t * k⁻¹)).2 ?_
      convert ht using 1
      group
    have hcomm := hwc (k * t * k⁻¹) ht'
    have h2 := congrArg (fun z => k⁻¹ * z * k) hcomm
    rw [show k⁻¹ * (w * (k * t * k⁻¹)) * k = (k⁻¹ * w * k) * t by group,
      show k⁻¹ * ((k * t * k⁻¹) * w) * k = t * (k⁻¹ * w * k) by group] at h2
    exact h2
  have hw''1 : k⁻¹ * w * k ≠ 1 := by
    intro h
    apply hw1
    have h2 := congrArg (fun z => k * z * k⁻¹) h
    rw [show w = k * (k⁻¹ * w * k) * k⁻¹ by group, h2]
    group
  have hxD : k⁻¹ * (x : G) * k ∈ D.M := by
    have hy : k⁻¹ * (x : G) * k ∈ centralizer ({k⁻¹ * w * k} : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      subst hz
      have h2 := congrArg (fun u => k⁻¹ * u * k) hxw
      rw [show k⁻¹ * (x * w) * k = (k⁻¹ * x * k) * (k⁻¹ * w * k) by group,
        show k⁻¹ * (w * x) * k = (k⁻¹ * w * k) * (k⁻¹ * x * k) by group] at h2
      exact h2.symm
    exact (hcu (k⁻¹ * w * k) hw''T hw''c hw''1).1 hy
  exact Subgroup.mem_subgroupOf.2 (show (x : G) ∈ K ⊓ D.M from ⟨x.2, by
    have h1 : k * (k⁻¹ * (x : G) * k) * k⁻¹ = (x : G) := by group
    have hthis := D.M.mul_mem (D.M.mul_mem hkM hxD) (D.M.inv_mem hkM)
    rwa [h1] at hthis⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

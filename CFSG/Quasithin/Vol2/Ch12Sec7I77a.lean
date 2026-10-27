module

public import CFSG.Quasithin.Vol2.Ch12Sec7L5j
public import CFSG.Quasithin.Vol2.Ch12Sec7L5h
public import CFSG.Quasithin.EmptyFaithful.S1421QA12Aut

public section

namespace CFSG.Quasithin.H13.S127.I77

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique S127.L5

variable {G : Type} [Group G] [Finite G]

theorem eq_of_isComponentOf {H K₁ K₂ : Subgroup G} (hH : CFSG.Open.pRank 3 H ≤ 2)
    (h₁ : IsComponentOf K₁ H) (h₂ : IsComponentOf K₂ H)
    (hZ : IsPGroup 2 ↥(Subgroup.center ↥K₁)) (h3 : 2 ≤ CFSG.pRank 3 (↥K₁ ⧸ Subgroup.center ↥K₁))
    (h3' : 2 ≤ CFSG.pRank 3 ↥K₂) : K₁ = K₂ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set A : Subgroup ↥H := K₁.subgroupOf H with hA
  set B : Subgroup ↥H := K₂.subgroupOf H with hB
  have eA : ↥K₁ ≃* ↥A := (Subgroup.subgroupOfEquivOfLe h₁.1).symm
  have eB : ↥K₂ ≃* ↥B := (Subgroup.subgroupOfEquivOfLe h₂.1).symm
  have hAq : CFSG.IsQuasisimple ↥A := CFSG.LocalCores.isQuasisimple_of_mulEquiv eA
    (CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple h₁.2.2)
  have hBq : CFSG.IsQuasisimple ↥B := CFSG.LocalCores.isQuasisimple_of_mulEquiv eB
    (CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple h₂.2.2)
  have hAc : CFSG.IsComponent A :=
    ⟨hAq, CFSG.Fischer.Classification.Recognition.SpU.isSubnormal_subgroupOf h₁.2.1⟩
  have hBc : CFSG.IsComponent B :=
    ⟨hBq, CFSG.Fischer.Classification.Recognition.SpU.isSubnormal_subgroupOf h₂.2.1⟩
  have hcA : (Subgroup.center ↥K₁).map eA.toMonoidHom = Subgroup.center ↥A :=
    Subgroup.map_center_eq eA
  have hZA : IsPGroup 2 ↥(Subgroup.center ↥A) := by
    rw [← hcA]
    exact hZ.map _
  have hpc : CFSG.pCore 2 ↥A = Subgroup.center ↥A := pCore_eq_center hAq hZA
  let e1 : (↥A ⧸ CFSG.pCore 2 ↥A) ≃* (↥A ⧸ Subgroup.center ↥A) :=
    QuotientGroup.quotientMulEquivOfEq hpc
  let e2 : (↥K₁ ⧸ Subgroup.center ↥K₁) ≃* (↥A ⧸ Subgroup.center ↥A) :=
    QuotientGroup.congr _ _ eA hcA
  have hr1 : 2 ≤ CFSG.pRank 3 (↥A ⧸ CFSG.pCore 2 ↥A) := by
    rw [NQBlock.pRank_mulEquiv e1 3, ← NQBlock.pRank_mulEquiv e2 3]
    exact h3
  have hsimple : IsSimpleGroup (↥A ⧸ CFSG.pCore 2 ↥A) := by
    have := hAq.2.1
    exact e1.isSimpleGroup
  have hnab : ∃ a b : ↥A ⧸ CFSG.pCore 2 ↥A, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := hAq.2.2
    refine ⟨e1.symm a, e1.symm b, fun h => hab ?_⟩
    have := congrArg e1 h
    simpa using this
  have hr2 : 2 ≤ CFSG.pRank 3 ↥B := by
    rw [← NQBlock.pRank_mulEquiv eB 3]
    exact h3'
  rcases CFSG.LocalCores.distinct_components_commute hAc hBc with heq | hcomm
  · have := congrArg (fun X : Subgroup ↥H => X.map H.subtype) heq
    simpa [hA, hB, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr h₁.1,
      inf_eq_left.mpr h₂.1] using this
  · exfalso
    have hc1 : A ≤ Subgroup.centralizer (B : Set ↥H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hc2 : B ≤ Subgroup.centralizer (A : Set ↥H) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp
        (by rw [Subgroup.commutator_comm]; exact hcomm)
    have hN1 : A ≤ Subgroup.normalizer (B : Set ↥H) := fun a ha =>
      Subgroup.mem_normalizer_fintype fun x hx => by
        rw [← Subgroup.mem_centralizer_iff.mp (hc1 ha) x hx, mul_inv_cancel_right]
        exact hx
    have hN2 : B ≤ Subgroup.normalizer (A : Set ↥H) := fun a ha =>
      Subgroup.mem_normalizer_fintype fun x hx => by
        rw [← Subgroup.mem_centralizer_iff.mp (hc2 ha) x hx, mul_inv_cancel_right]
        exact hx
    have hsum := NQBlock.commuting_product_pRank hN1 hN2 (by rw [hcomm]; exact bot_le) hsimple
      hnab Nat.prime_three (by norm_num)
    have hle : CFSG.pRank 3 ↥(A ⊔ B) ≤ 2 := by
      rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
      refine (CFSG.SectionRank.pRank_mono (by norm_num) le_top).trans ?_
      rw [← CFSG.SectionRank.pRank_eq_open_pRank_top,
        CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank Nat.prime_three]
      exact hH
    omega

theorem isQuasisimple_of_mulEquiv' {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    (h : CFSG.Open.IsQuasisimple A) : CFSG.Open.IsQuasisimple B := by
  have h' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e
    (CFSG.Fischer.Classification.Recognition.localCores_isQuasisimple h)
  exact ⟨h'.1.1, h'.2.1⟩

abbrev Kt (L : Subgroup G) (t : G) : Subgroup G :=
  conjClosure (Lt L t) (Subgroup.centralizer ({t} : Set G))

structure Set77 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (t : G) : Prop where
  d : D127 G T L V t
  not_le : ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G)
  comp : IsComponentOf (Kt L t) (Subgroup.centralizer ({t} : Set G))
  center : (Subgroup.center ↥(Kt L t)).map (Kt L t).subtype = Vt L t
  psl : IsPSL 3 2 2 (↥(Kt L t) ⧸ Subgroup.center ↥(Kt L t))
  fpf : ∀ x ∈ XOf L, x ∉ Subgroup.centralizer (V : Set G) →
    V ⊓ Subgroup.centralizer ({x} : Set G) = ⊥
  exists_x : ∃ x ∈ XOf L, x ∉ Subgroup.centralizer (V : Set G)
  o2L : L ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 L

omit [Finite G] in
theorem lt_le_Kt (L : Subgroup G) (t : G) : Lt L t ≤ Kt L t := le_conjClosure _ _

theorem set77_of (h71 : Setup1271) (h74 : Lemma12_7_4) (h125 : Lemma12_7_5)
    {T L V : Subgroup G} {t : G} (h : Hyp1271 G T L V) (ht : t ∈ V)
    (h18 : (Subgroup.centralizer ({t} : Set G)).relIndex L = 18)
    (hnot : ¬ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (L : Set G)) :
    Set77 G T L V t := by
  obtain ⟨hc, hz, hp⟩ := (h125 G T L V h t ht h18).resolve_left hnot
  obtain ⟨-, -, hO2, h3, -, hfpf⟩ := h71 G T L V h
  refine ⟨d127_of h71 h74 h ht h18, hnot, hc, hz, hp, hfpf, ?_, hO2⟩
  by_contra hno
  push Not at hno
  have hbot : autOn (XOf L) V = ⊥ := by
    rw [autOn, Subgroup.map_eq_bot_iff]
    intro y hy
    rw [MonoidHom.mem_ker]
    exact A4.conjAct_eq_one_iff.mpr (hno _ (Subgroup.mem_subgroupOf.mp hy))
  rw [hbot, Subgroup.card_bot] at h3
  norm_num at h3

namespace Set77

variable {T L V : Subgroup G} {t : G} (s : Set77 G T L V t)
include s

theorem sq_t : t ^ 2 = 1 := sq_eq_one_of_mem s.d.hyp.hyp s.d.mem

theorem le_Gt : Kt L t ≤ Subgroup.centralizer ({t} : Set G) := s.comp.1

theorem vt_le : Vt L t ≤ Kt L t := by
  rw [← s.center]
  exact Subgroup.map_subtype_le _

theorem le_centralizer_vt : Kt L t ≤ Subgroup.centralizer (Vt L t : Set G) := by
  intro k hk
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  rw [← s.center] at hv
  obtain ⟨z, hz, rfl⟩ := hv
  exact (congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)).symm

theorem card_center : Nat.card ↥(Subgroup.center ↥(Kt L t)) = 4 := by
  rw [← Subgroup.card_map_of_injective (Kt L t).subtype_injective, s.center, s.d.card_Vt]

theorem isPGroup_center : IsPGroup 2 ↥(Subgroup.center ↥(Kt L t)) :=
  IsPGroup.of_card (n := 2) (by rw [s.card_center]; norm_num)

theorem two_le_pRank : 2 ≤ CFSG.pRank 3 (↥(Kt L t) ⧸ Subgroup.center ↥(Kt L t)) := by
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact QA12.two_le_pRank_psl34 s.psl

theorem normalizer_Gt :
    Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (Kt L t : Set G) :=
  le_normalizer_of_isComponentOf (s.d.pRank_le_two s.sq_t) s.comp s.isPGroup_center
    s.two_le_pRank

theorem card_quot : Nat.card (↥(Kt L t) ⧸ Subgroup.center ↥(Kt L t)) = 20160 := by
  obtain ⟨F, _, _, hF, ⟨e⟩⟩ := QA12.exists_equiv_projectiveSL s.psl
  rw [Nat.card_congr e.toEquiv, RankThree.PartTwo.KFacts.L34.card_projectiveSL hF]

theorem card_Kt : Nat.card ↥(Kt L t) = 80640 := by
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (Subgroup.center ↥(Kt L t)), s.card_quot,
    s.card_center]

theorem two_le_pRank_Kt : 2 ≤ CFSG.pRank 3 ↥(Kt L t) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcop : ¬ 3 ∣ Nat.card ↥(Subgroup.center ↥(Kt L t)) := by
    rw [s.card_center]
    norm_num
  rw [← CFSG.GroupTheory.PRankCoprimeQuotient.pRank_quotient_eq_of_not_dvd Nat.prime_three
    (Subgroup.center ↥(Kt L t)) hcop]
  exact s.two_le_pRank

theorem card_pCore_Lt : Nat.card ↥(CFSG.pCore 2 ↥(Lt L t)) = 64 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hdvd : Nat.card ↥(Lt L t) ∣ Nat.card ↥(Kt L t) := Subgroup.card_dvd_of_le (lt_le_Kt L t)
  rw [s.d.card_Lt, s.card_Kt] at hdvd
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥(Lt L t)))
  have hle := s.d.card_V_le
  rw [s.d.card_V, ha] at hle
  rw [ha] at hdvd ⊢
  have h2a : 2 ^ a ∣ 2 ^ 6 * 21 := by
    obtain ⟨c, hc⟩ := hdvd
    have hc' : (80640 : ℕ) = (2 ^ a * c) * 60 := by rw [hc]; ring
    exact ⟨c, by omega⟩
  have h64 : 2 ^ a ∣ 2 ^ 6 :=
    (Nat.Coprime.dvd_of_dvd_mul_right (Nat.Coprime.pow_left _ (by norm_num)) h2a)
  have ha6 : a ≤ 6 := (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h64
  have : 2 ^ a ≤ 2 ^ 6 := Nat.pow_le_pow_right (by norm_num) ha6
  omega

theorem pCore_Lt : CFSG.pCore 2 ↥(Lt L t) = V.subgroupOf (Lt L t) := by
  refine (Subgroup.eq_of_le_of_card_ge s.d.subgroupOf_le_pCore ?_).symm
  rw [s.card_pCore_Lt, Nat.card_congr (Subgroup.subgroupOfEquivOfLe s.d.v_le_lt).toEquiv,
    s.d.card_V]
  norm_num

theorem vt_ne_bot : Vt L t ≠ ⊥ := by
  intro h
  have := s.d.mem_vt
  rw [h, Subgroup.mem_bot] at this
  exact s.d.ne_one this

theorem isPGroup_vt : IsPGroup 2 ↥(Vt L t) :=
  IsPGroup.of_card (n := 2) (by rw [s.d.card_Vt]; norm_num)

theorem pRank_normalizer_vt :
    CFSG.Open.pRank 3 (Subgroup.normalizer (Vt L t : Set G)) ≤ 2 :=
  (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three (by norm_num) _
    ⟨Vt L t, s.vt_ne_bot, s.isPGroup_vt, rfl⟩).trans s.d.hyp.hyp.qtke.2.2

theorem centralizer_vt_le_Gt :
    Subgroup.centralizer (Vt L t : Set G) ≤ Subgroup.centralizer ({t} : Set G) :=
  Subgroup.centralizer_le (Set.singleton_subset_iff.mpr s.d.mem_vt)

theorem isComponentOf_normalizer_vt :
    IsComponentOf (Kt L t) (Subgroup.normalizer (Vt L t : Set G)) := by
  have hKC := s.le_centralizer_vt
  have hCN : Subgroup.centralizer (Vt L t : Set G) ≤ Subgroup.normalizer (Vt L t : Set G) :=
    Subgroup.centralizer_le_normalizer _
  refine ⟨hKC.trans hCN, ?_, s.comp.2.2⟩
  refine IsSubnormal.step hKC ?_ (IsSubnormal.step hCN ?_ (IsSubnormal.refl _))
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKC]
    exact s.centralizer_vt_le_Gt.trans s.normalizer_Gt
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hCN]
    intro n hn
    refine Subgroup.mem_normalizer_fintype fun c hc => ?_
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc ⊢
    intro v hv
    have hv' : n⁻¹ * v * n ∈ Vt L t := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) v).mp hv
      simpa using this
    have h1 := hc _ hv'
    calc v * (n * c * n⁻¹) = n * ((n⁻¹ * v * n) * c) * n⁻¹ := by group
      _ = n * (c * (n⁻¹ * v * n)) * n⁻¹ := by rw [h1]
      _ = n * c * n⁻¹ * v := by group

theorem normalizer_vt_le :
    Subgroup.normalizer (Vt L t : Set G) ≤ Subgroup.normalizer (Kt L t : Set G) :=
  le_normalizer_of_isComponentOf s.pRank_normalizer_vt s.isComponentOf_normalizer_vt
    s.isPGroup_center s.two_le_pRank

theorem mem_vt_iff {v : G} :
    v ∈ Vt L t ↔ v ∈ Kt L t ∧ v ∈ Subgroup.centralizer (Kt L t : Set G) := by
  rw [← s.center, map_center_eq_centerOf]
  rfl

theorem normalizer_le_vt :
    Subgroup.normalizer (Kt L t : Set G) ≤ Subgroup.normalizer (Vt L t : Set G) := by
  intro g hg
  refine Subgroup.mem_normalizer_fintype fun v hv => ?_
  rw [SetLike.mem_coe, s.mem_vt_iff] at hv ⊢
  refine ⟨(Subgroup.mem_normalizer_iff.mp hg v).mp hv.1, ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hk' : g⁻¹ * k * g ∈ Kt L t := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hg) k).mp hk
    simpa using this
  have h1 := Subgroup.mem_centralizer_iff.mp hv.2 _ hk'
  calc k * (g * v * g⁻¹) = g * ((g⁻¹ * k * g) * v) * g⁻¹ := by group
    _ = g * (v * (g⁻¹ * k * g)) * g⁻¹ := by rw [h1]
    _ = g * v * g⁻¹ * k := by group

theorem normalizer_vt_eq :
    Subgroup.normalizer (Vt L t : Set G) = Subgroup.normalizer (Kt L t : Set G) :=
  le_antisymm s.normalizer_vt_le s.normalizer_le_vt

omit [Finite G] s in
theorem xOf_le_normalizer_vt : XOf L ≤ Subgroup.normalizer (Vt L t : Set G) :=
  le_normalizer_conjClosure _ _

theorem mem_V_of_mem_vt {v : G} (hv : v ∈ Vt L t) : v ∈ V := s.d.vt_le hv

theorem conj_ne_self {a v : G} (haX : a ∈ XOf L) (haV : a ∉ Subgroup.centralizer (V : Set G))
    (hv : v ∈ V) (hv1 : v ≠ 1) : a * v * a⁻¹ ≠ v := by
  intro h
  have hc : a * v = v * a := by
    calc a * v = a * v * a⁻¹ * a := by group
      _ = v * a := by rw [h]
  have hmem : v ∈ V ⊓ Subgroup.centralizer ({a} : Set G) :=
    ⟨hv, Subgroup.mem_centralizer_singleton_iff.mpr hc.symm⟩
  rw [s.fpf a haX haV, Subgroup.mem_bot] at hmem
  exact hv1 hmem

theorem exists_conj_eq {v : G} (hv : v ∈ Vt L t) (hv1 : v ≠ 1) :
    ∃ x ∈ XOf L, x * t * x⁻¹ = v := by
  obtain ⟨a, haX, haV⟩ := s.exists_x
  have hN := xOf_le_normalizer_vt (L := L) (t := t)
  have hmemc : ∀ {x w : G}, x ∈ XOf L → w ∈ Vt L t → x * w * x⁻¹ ∈ Vt L t := fun hx hw =>
    (Subgroup.mem_normalizer_iff.mp (hN hx) _).mp hw
  set s₁ := a * t * a⁻¹ with hs₁
  set s₂ := a * s₁ * a⁻¹ with hs₂
  have ht := s.d.mem_vt
  have h1 : s₁ ∈ Vt L t := hmemc haX ht
  have h2 : s₂ ∈ Vt L t := hmemc haX h1
  have ht1 : t ≠ 1 := s.d.ne_one
  have hs₁1 : s₁ ≠ 1 := by
    intro h
    apply ht1
    have : t = a⁻¹ * s₁ * a := by rw [hs₁]; group
    rw [this, h]
    group
  have hs₂1 : s₂ ≠ 1 := by
    intro h
    apply hs₁1
    have : s₁ = a⁻¹ * s₂ * a := by rw [hs₂]; group
    rw [this, h]
    group
  have hts₁ : t ≠ s₁ := fun h => s.conj_ne_self haX haV s.d.mem ht1 h.symm
  have hs₁s₂ : s₁ ≠ s₂ := fun h => s.conj_ne_self haX haV (s.mem_V_of_mem_vt h1) hs₁1 h.symm
  have hts₂ : t ≠ s₂ := by
    intro h
    have hsw : a * s₁ * a⁻¹ = t := h.symm
    have hfix : a * (t * s₁) * a⁻¹ = t * s₁ := by
      calc a * (t * s₁) * a⁻¹ = (a * t * a⁻¹) * (a * s₁ * a⁻¹) := by group
        _ = s₁ * t := by rw [← hs₁, hsw]
        _ = t * s₁ := s.d.comm _ (s.mem_V_of_mem_vt h1) _ s.d.mem
    have hts : t * s₁ ∈ V := V.mul_mem s.d.mem (s.mem_V_of_mem_vt h1)
    by_cases h1' : t * s₁ = 1
    · apply hts₁
      have := s.sq_t
      have e : s₁ = t⁻¹ := eq_inv_of_mul_eq_one_right h1'
      rw [e, inv_eq_of_mul_eq_one_left (by rw [← pow_two, this])]
    · exact s.conj_ne_self haX haV hts h1' hfix
  by_contra hno
  push Not at hno
  have hvt : v ≠ t := fun h => hno 1 (XOf L).one_mem (by rw [h]; group)
  have hvs₁ : v ≠ s₁ := fun h => hno a haX h.symm
  have hvs₂ : v ≠ s₂ := fun h => hno (a * a) ((XOf L).mul_mem haX haX) (by rw [h, hs₂, hs₁]; group)
  have hsub : ({1, t, s₁, s₂, v} : Set G) ⊆ (Vt L t : Set G) := by
    intro x hx
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl
    · exact (Vt L t).one_mem
    · exact ht
    · exact h1
    · exact h2
    · exact hv
  have hcard : ({1, t, s₁, s₂, v} : Set G).ncard = 5 := by
    rw [Set.ncard_insert_of_notMem (by simp [ht1.symm, hs₁1.symm, hs₂1.symm, hv1.symm]),
      Set.ncard_insert_of_notMem (by simp [hts₁, hts₂, hvt.symm]),
      Set.ncard_insert_of_notMem (by simp [hs₁s₂, hvs₁.symm]), Set.ncard_pair hvs₂.symm]
  have hle := Set.ncard_le_ncard hsub (Set.toFinite _)
  have h4 : (Vt L t : Set G).ncard = 4 := by
    rw [← Nat.card_coe_set_eq]
    exact s.d.card_Vt
  omega

theorem sq_eq_one_of_mem_vt {v : G} (hv : v ∈ Vt L t) : v ^ 2 = 1 :=
  sq_eq_one_of_mem s.d.hyp.hyp (s.mem_V_of_mem_vt hv)

theorem centralizer_le_normalizer {v : G} (hv : v ∈ Vt L t) (hv1 : v ≠ 1) :
    Subgroup.centralizer ({v} : Set G) ≤ Subgroup.normalizer (Kt L t : Set G) := by
  obtain ⟨x, hxX, rfl⟩ := s.exists_conj_eq hv hv1
  have hxN : x ∈ Subgroup.normalizer (Kt L t : Set G) :=
    s.normalizer_vt_le (xOf_le_normalizer_vt hxX)
  intro c hc
  have hc' : x⁻¹ * c * x ∈ Subgroup.centralizer ({t} : Set G) := by
    rw [Subgroup.mem_centralizer_iff] at hc ⊢
    intro h hh
    rw [Set.mem_singleton_iff] at hh
    subst hh
    have h1 := hc _ (Set.mem_singleton _)
    calc h * (x⁻¹ * c * x) = x⁻¹ * ((x * h * x⁻¹) * c) * x := by group
      _ = x⁻¹ * (c * (x * h * x⁻¹)) * x := by rw [h1]
      _ = x⁻¹ * c * x * h := by group
  have h1 := s.normalizer_Gt hc'
  have e : c = x * (x⁻¹ * c * x) * x⁻¹ := by group
  rw [e]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ hxN h1) (Subgroup.inv_mem _ hxN)

theorem pRank_centralizer {v : G} (hv : v ∈ Vt L t) (hv1 : v ≠ 1) :
    CFSG.Open.pRank 3 (Subgroup.centralizer ({v} : Set G)) ≤ 2 :=
  (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three (by norm_num) _
    (CFSG.QuasithinUnique.Lin2.isTwoLocal_centralizer_of_sq_eq_one (s.sq_eq_one_of_mem_vt hv)
      hv1)).trans s.d.hyp.hyp.qtke.2.2

theorem inf_conj_eq_bot {g : G} (hg : g ∉ Subgroup.normalizer (Vt L t : Set G)) :
    Vt L t ⊓ (Vt L t).map (MulAut.conj g).toMonoidHom = ⊥ := by
  by_contra hne
  obtain ⟨⟨v, hvmem⟩, hv1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  have hv1' : v ≠ 1 := fun h => hv1 (Subtype.ext h)
  obtain ⟨hv, hvg⟩ := Subgroup.mem_inf.mp hvmem
  obtain ⟨w, hw, hwv⟩ := Subgroup.mem_map.mp hvg
  simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at hwv
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hv1'
    rw [← hwv]
    group
  set H := Subgroup.centralizer ({v} : Set G) with hH
  set K₂ := (Kt L t).map (MulAut.conj g).toMonoidHom with hK₂
  have e : ↥(Kt L t) ≃* ↥K₂ :=
    Subgroup.equivMapOfInjective _ _ (MulAut.conj g).injective
  have hKH : Kt L t ≤ H := fun k hk => by
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    exact (Subgroup.mem_centralizer_iff.mp (s.le_centralizer_vt hk) v hv).symm
  have h₁ : IsComponentOf (Kt L t) H := by
    refine ⟨hKH, IsSubnormal.step hKH ?_ (IsSubnormal.refl _), s.comp.2.2⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKH]
    exact s.centralizer_le_normalizer hv hv1'
  have hwC : ∀ k ∈ Kt L t, k * w = w * k := fun k hk =>
    (Subgroup.mem_centralizer_iff.mp (s.le_centralizer_vt hk) w hw).symm
  have hK₂H : K₂ ≤ H := by
    rintro _ ⟨k, hk, rfl⟩
    rw [hH, Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    rw [← hwv]
    calc g * k * g⁻¹ * (g * w * g⁻¹) = g * (k * w) * g⁻¹ := by group
      _ = g * (w * k) * g⁻¹ := by rw [hwC k hk]
      _ = g * w * g⁻¹ * (g * k * g⁻¹) := by group
  have hK₂N : H ≤ Subgroup.normalizer (K₂ : Set G) := by
    intro c hc
    have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({w} : Set G) := by
      rw [Subgroup.mem_centralizer_iff] at hc ⊢
      intro h hh
      rw [Set.mem_singleton_iff] at hh
      subst hh
      have h1 := hc _ (Set.mem_singleton _)
      rw [← hwv] at h1
      calc h * (g⁻¹ * c * g) = g⁻¹ * ((g * h * g⁻¹) * c) * g := by group
        _ = g⁻¹ * (c * (g * h * g⁻¹)) * g := by rw [h1]
        _ = g⁻¹ * c * g * h := by group
    have hN := s.centralizer_le_normalizer hw hw1 hc'
    refine Subgroup.mem_normalizer_fintype fun y hy => ?_
    obtain ⟨k, hk, rfl⟩ := hy
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine ⟨(g⁻¹ * c * g) * k * (g⁻¹ * c * g)⁻¹,
      (Subgroup.mem_normalizer_iff.mp hN k).mp hk, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group
  have h₂ : IsComponentOf K₂ H := by
    refine ⟨hK₂H, IsSubnormal.step hK₂H ?_ (IsSubnormal.refl _),
      isQuasisimple_of_mulEquiv' e s.comp.2.2⟩
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hK₂H]
    exact hK₂N
  have h3' : 2 ≤ CFSG.pRank 3 ↥K₂ := by
    rw [← NQBlock.pRank_mulEquiv e 3]
    exact s.two_le_pRank_Kt
  have heq := eq_of_isComponentOf (s.pRank_centralizer hv hv1') h₁ h₂ s.isPGroup_center
    s.two_le_pRank h3'
  apply hg
  apply s.normalizer_le_vt
  refine Subgroup.mem_normalizer_fintype fun k hk => ?_
  have : g * k * g⁻¹ ∈ K₂ := ⟨k, hk, by simp⟩
  rwa [← heq] at this

end Set77

end CFSG.Quasithin.H13.S127.I77

module

public import CFSG.Quasithin.EmptyFaithful.S151V8
public import CFSG.Quasithin.EmptyFaithful.S152He15A

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc CFSG.LieType.BorelTits
open scoped Pointwise commutatorElement

namespace He15

theorem center_slt_three : Subgroup.center (SLt 3) = ⊥ := by
  rw [eq_bot_iff]
  intro A hA
  obtain ⟨r, hr, hA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.1 hA
  rw [Subgroup.mem_bot]
  have h01 : ∀ s : ZMod 2, s = 0 ∨ s = 1 := by decide
  have hr1 : r = 1 := by
    rw [Fintype.card_fin] at hr
    rcases h01 r with h | h
    · rw [h, zero_pow (by omega : 3 ≠ 0)] at hr
      exact absurd hr zero_ne_one
    · exact h
  apply Subtype.ext
  rw [← hA, hr1, map_one, Matrix.SpecialLinearGroup.coe_one]

variable {G : Type} [Group G] [Finite G]

theorem eq_one_of_mem_inf_of_odd {L L' : Subgroup G} {e : ↥L →* SLt 3}
    {β : ↥(blockU L) →* Multiplicative (Vt 3)} (hs : LnStr L e β) (hc : ⁅L, L'⁆ ≤ pCoreOf 2 L)
    {y : G} (hyL : y ∈ L) (hyL' : y ∈ L') (hodd : Odd (orderOf y)) : y = 1 := by
  have hcen : e ⟨y, hyL⟩ ∈ Subgroup.center (SLt 3) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨l, rfl⟩ := hs.surj g
    have h1 : l * ⟨y, hyL⟩ * l⁻¹ * ⟨y, hyL⟩⁻¹ ∈ CFSG.pCore 2 ↥L := by
      rw [mem_pCore_iff]
      have := hc (Subgroup.commutator_mem_commutator l.2 hyL')
      simpa [commutatorElement_def] using this
    rw [← hs.ker, MonoidHom.mem_ker] at h1
    simp only [map_mul, map_inv] at h1
    have h2 : e l * e ⟨y, hyL⟩ * (e l)⁻¹ = e ⟨y, hyL⟩ := mul_inv_eq_one.mp h1
    calc e l * e ⟨y, hyL⟩ = (e l * e ⟨y, hyL⟩ * (e l)⁻¹) * e l := by group
      _ = e ⟨y, hyL⟩ * e l := by rw [h2]
  rw [center_slt_three, Subgroup.mem_bot] at hcen
  have hyO : y ∈ pCoreOf 2 L := by
    have : (⟨y, hyL⟩ : ↥L) ∈ CFSG.pCore 2 ↥L := by
      rw [← hs.ker]
      exact hcen
    exact (mem_pCore_iff _).mp this
  obtain ⟨j, hj⟩ := (pCoreOf_isPGroup 2 L) ⟨y, hyO⟩
  have hy2 : y ^ 2 ^ j = 1 := congrArg Subtype.val hj
  exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    ((Nat.coprime_two_right.mpr hodd).pow_right j) dvd_rfl (orderOf_dvd_of_pow_eq_one hy2))

theorem exists_three_element_moving_v1 (hK : KnownFacts15122Types)
    {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (h15 : Lemma1515Concl T Mc M)
    (hc : Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L) (hb : IsLnBlock L 3) (h4 : Ce15Four T Mc M) :
    ∃ x ∈ Subgroup.normalizer (V₁ : Set G), x ^ 3 = 1 ∧ x ∉ Subgroup.centralizer (V₁ : Set G) ∧
      3 ∣ Nat.card L := by
  classical
  have hp : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hS := hc.ctx.setting
  have h7n : ¬ Ce15Seven T Mc M := h4.not_seven
  obtain ⟨e, β, hs⟩ := exists_lnStr hb
  have h9 := s151v_not_nine_dvd_card hs
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  obtain ⟨hY₀L, hV2Y₀, hnorm, c, hcY, hfpf⟩ := v2_data hK h15 hc hb
  have hr := hS.ranks_four h4
  have hS2 : (s1516 T Z₁).relIndex T = 2 := hS.index_two hc.small h7n
  have hswap := hS.swap_small hc.small h7n
  obtain ⟨t₀, ht₀T, ht₀S⟩ : ∃ t ∈ T, t ∉ s1516 T Z₁ := by
    by_contra hall
    push Not at hall
    have : T ≤ s1516 T Z₁ := hall
    rw [Subgroup.relIndex_eq_one.mpr this] at hS2
    exact absurd hS2 (by norm_num)
  have hconj12 : ∀ x, x ∈ V₁ ↔ t₀⁻¹ * x * t₀ ∈ V₂ := by
    intro x
    rw [← hswap t₀ ht₀T ht₀S, mem_conjByElt]
  have hV2ne : V₂ ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot V₂).mp (by rw [hr.2.1]; norm_num)
  obtain ⟨⟨a, haV⟩, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hV2ne
  have ha1' : a ≠ 1 := fun h => ha1 (Subtype.ext h)
  have hca : c * a * c⁻¹ ≠ a := fun h => ha1' (hfpf a haV h)
  obtain ⟨y₀, hy₀ML, ⟨k, hk⟩, hy₀a⟩ : ∃ y₀ ∈ M ⊓ L, (∃ k : ℕ, orderOf y₀ = 3 ^ k) ∧
      y₀ * a * y₀⁻¹ ≠ a := by
    by_contra hall
    push Not at hall
    have hle : oPrimeResidualOf 3 (M ⊓ L) ≤ Subgroup.centralizer ({a} : Set G) := by
      unfold oPrimeResidualOf
      rw [Subgroup.closure_le]
      rintro y ⟨hyML, k, hk⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
      have := hall y hyML ⟨k, hk⟩
      calc y * a = (y * a * y⁻¹) * y := by group
        _ = a * y := by rw [this]
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp (hle hcY)
    apply hca
    calc c * a * c⁻¹ = (c * a) * c⁻¹ := rfl
      _ = a * c * c⁻¹ := by rw [h1]
      _ = a := by group
  have hy₀L : y₀ ∈ L := hy₀ML.2
  have hdvd : orderOf y₀ ∣ Nat.card ↥L := by
    have := orderOf_dvd_natCard (⟨y₀, hy₀L⟩ : ↥L)
    rwa [← Subgroup.orderOf_coe] at this
  have hy₀3 : y₀ ^ 3 = 1 := by
    rcases k with _ | _ | k
    · have : y₀ = 1 := orderOf_eq_one_iff.mp (by simpa using hk)
      rw [this]
      simp
    · have h3 : orderOf y₀ = 3 := by simpa using hk
      rw [← h3]
      exact pow_orderOf_eq_one y₀
    · exfalso
      apply h9
      have : 9 ∣ orderOf y₀ := by
        rw [hk]
        exact ⟨3 ^ k, by ring⟩
      exact this.trans hdvd
  have hy₀1 : y₀ ≠ 1 := fun h => hy₀a (by rw [h]; group)
  have hoy₀ : orderOf y₀ = 3 := orderOf_eq_prime hy₀3 hy₀1
  have h3L : 3 ∣ Nat.card L := hoy₀ ▸ hdvd
  have hYN : oPrimeResidualOf 3 (M ⊓ L) ≤ Subgroup.normalizer (V₂ : Set G) :=
    (oPrimeResidualOf_mono1516 3 (inf_le_inf_left M hLG)).trans (hS.y_facts hc.small).1.2.2.2
  have hy₀Y : y₀ ∈ oPrimeResidualOf 3 (M ⊓ L) := Subgroup.subset_closure ⟨hy₀ML, k, hk⟩
  have hy₀N : y₀ ∈ Subgroup.normalizer (V₂ : Set G) := hYN hy₀Y
  refine ⟨t₀ * y₀ * t₀⁻¹, ?_, ?_, ?_, h3L⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro v
    rw [hconj12 v, hconj12 ((t₀ * y₀ * t₀⁻¹) * v * (t₀ * y₀ * t₀⁻¹)⁻¹)]
    have : t₀⁻¹ * ((t₀ * y₀ * t₀⁻¹) * v * (t₀ * y₀ * t₀⁻¹)⁻¹) * t₀ = y₀ * (t₀⁻¹ * v * t₀) * y₀⁻¹ := by
      group
    rw [this]
    exact Subgroup.mem_normalizer_iff.mp hy₀N (t₀⁻¹ * v * t₀)
  · rw [conj_pow, hy₀3]
    group
  · intro hxC
    have hb : t₀ * a * t₀⁻¹ ∈ V₁ := by
      rw [hconj12]
      have : t₀⁻¹ * (t₀ * a * t₀⁻¹) * t₀ = a := by group
      rw [this]
      exact haV
    have h1 := Subgroup.mem_centralizer_iff.mp hxC _ hb
    apply hy₀a
    have h2 : y₀ * a = a * y₀ := by
      have e1 : t₀⁻¹ * ((t₀ * a * t₀⁻¹) * (t₀ * y₀ * t₀⁻¹)) * t₀ = a * y₀ := by group
      have e2 : t₀⁻¹ * ((t₀ * y₀ * t₀⁻¹) * (t₀ * a * t₀⁻¹)) * t₀ = y₀ * a := by group
      rw [← e1, ← e2, h1]
    calc y₀ * a * y₀⁻¹ = (a * y₀) * y₀⁻¹ := by rw [h2]
      _ = a := by group

theorem v1_normalizer_le_normalizer (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (hK : KnownFacts15122Types) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G} (h15 : Lemma1515Concl T Mc M)
    (hc : Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L) (hb : IsLnBlock L 3) (h4 : Ce15Four T Mc M)
    (hLV₁ : L ≤ Subgroup.centralizer (V₁ : Set G)) :
    ∀ y ∈ Subgroup.normalizer (V₁ : Set G), y ∈ Subgroup.normalizer (L : Set G) := by
  classical
  have hS := hc.ctx.setting
  have hq := hc.ctx.qtfe
  have h7n : ¬ Ce15Seven T Mc M := h4.not_seven
  have hr := hS.ranks_four h4
  obtain ⟨x, hxN, hx3, hxC, h3L⟩ := exists_three_element_moving_v1 hK h15 hc hb h4
  obtain ⟨e, β, hs⟩ := exists_lnStr hb
  have hV₁p : IsPGroup 2 ↥V₁ := IsPGroup.of_card (n := 2) (by rw [hr.1]; norm_num)
  have hV₁ne : V₁ ≠ ⊥ := (Subgroup.one_lt_card_iff_ne_bot V₁).mp (by rw [hr.1]; norm_num)
  have hpc : pCoreOf 2 (Subgroup.normalizer (V₁ : Set G)) ≠ ⊥ := by
    intro h
    have := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (Subgroup.le_normalizer : V₁ ≤ Subgroup.normalizer (V₁ : Set G)) le_rfl hV₁p
    rw [h] at this
    exact hV₁ne (le_bot_iff.mp this)
  have hZ₁V₁ : Z₁ ≤ V₁ := (hS.decomp_other h7n).2.1
  have hCG : Subgroup.centralizer (V₁ : Set G) ≤ g1_1516 Z₁ :=
    Subgroup.centralizer_le (fun z hz => hZ₁V₁ hz)
  have hLC : L ∈ cComp (Subgroup.centralizer (V₁ : Set G)) :=
    cComp_mem_of_le hc.hL.comp hLV₁ hCG
  have hCN : Subgroup.centralizer (V₁ : Set G) ≤ Subgroup.normalizer (V₁ : Set G) :=
    Subgroup.centralizer_le_normalizer _
  have hCnorm : ((Subgroup.centralizer (V₁ : Set G)).subgroupOf
      (Subgroup.normalizer (V₁ : Set G))).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCN).mpr fun n hn =>
      s151v_mem_normalizer_centralizer hn
  have hLN : L ∈ cComp (Subgroup.normalizer (V₁ : Set G)) :=
    cComp_mem_of_subnormal (A3.subnormal_of_normal hCN hCnorm) hLC
  have hLN' : L ≤ Subgroup.normalizer (V₁ : Set G) := hLV₁.trans hCN
  rcases lemma_1_2_1_three hq.qtke hq.simple hq.nonabelian h37 h38 hpc hLN with hn | ⟨h2, -⟩
  · exact fun y hy => (Subgroup.normal_subgroupOf_iff_le_normalizer hLN').mp hn hy
  · exfalso
    have hodd : ∀ y ∈ Subgroup.normalizer (V₁ : Set G), Odd (orderOf y) →
        y ∈ Subgroup.normalizer (L : Set G) := fun y hy ho =>
      mem_normalizer_of_odd hLN' hy ho (Or.inr h2)
    obtain ⟨a₁, b₁, hab, hs₂⟩ := Set.ncard_eq_two.mp h2
    have hLmem : L ∈ conjSubgroupsBy (Subgroup.normalizer (V₁ : Set G)) L :=
      S153D.mem_conjSubgroupsBy_self
    obtain ⟨L', hL'mem, hL'ne⟩ :
        ∃ L' ∈ conjSubgroupsBy (Subgroup.normalizer (V₁ : Set G)) L, L' ≠ L := by
      rw [hs₂] at hLmem ⊢
      rcases hLmem with h | h
      · exact ⟨b₁, Or.inr rfl, fun h' => hab (h.symm.trans h'.symm)⟩
      · exact ⟨a₁, Or.inl rfl, fun h' => hab (h'.trans h)⟩
    obtain ⟨n, hnN, hL'eq⟩ := hL'mem
    have hL'c : L' ∈ cComp (Subgroup.normalizer (V₁ : Set G)) := by
      rw [hL'eq]
      exact map_conj_mem_cComp hLN hnN
    have hne : L ≠ L' := fun h => hL'ne h.symm
    have hmemL' : ∀ g, g ∈ L' ↔ n⁻¹ * g * n ∈ L := by
      intro g
      rw [hL'eq]
      exact A38.mem_map_conj
    have hnV : ∀ v ∈ V₁, n⁻¹ * v * n ∈ V₁ := fun v hv => by
      have := (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (V₁ : Set G)).inv_mem hnN) v).mp hv
      simpa using this
    have hL'C : L' ≤ Subgroup.centralizer (V₁ : Set G) := by
      intro g hg
      have hgL : n⁻¹ * g * n ∈ L := (hmemL' g).mp hg
      rw [Subgroup.mem_centralizer_iff]
      intro v hv
      have h1 := Subgroup.mem_centralizer_iff.mp (hLV₁ hgL) _ (hnV v hv)
      calc v * g = n * ((n⁻¹ * v * n) * (n⁻¹ * g * n)) * n⁻¹ := by group
        _ = n * ((n⁻¹ * g * n) * (n⁻¹ * v * n)) * n⁻¹ := by rw [h1]
        _ = g * v := by group
    have h3L' : 3 ∣ Nat.card L' := by
      rw [hL'eq, Subgroup.card_map_of_injective (MulAut.conj n).injective]
      exact h3L
    have hx3odd : Odd (orderOf x) :=
      Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hx3)
    have hxL : x ∈ Subgroup.normalizer (L : Set G) := hodd x hxN hx3odd
    have hxL' : x ∈ Subgroup.normalizer (L' : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro g
      rw [hmemL' g, hmemL' (x * g * x⁻¹)]
      have hx'3 : (n⁻¹ * x * n) ^ 3 = 1 := by
        have h1 := conj_pow (a := n⁻¹) (b := x) (i := 3)
        rw [inv_inv, hx3] at h1
        rw [h1]
        group
      have hx' : n⁻¹ * x * n ∈ Subgroup.normalizer (L : Set G) := by
        refine hodd _ ?_ (Odd.of_dvd_nat (by decide : Odd 3) (orderOf_dvd_of_pow_eq_one hx'3))
        exact (Subgroup.normalizer _).mul_mem ((Subgroup.normalizer _).mul_mem
          ((Subgroup.normalizer _).inv_mem hnN) hxN) hnN
      have e1 : n⁻¹ * (x * g * x⁻¹) * n =
          (n⁻¹ * x * n) * (n⁻¹ * g * n) * (n⁻¹ * x * n)⁻¹ := by group
      rw [e1]
      exact Subgroup.mem_normalizer_iff.mp hx' (n⁻¹ * g * n)
    have hEp : IsPGroup 3 ↥(Subgroup.zpowers x) := fun g =>
      ⟨1, Subtype.ext (by simpa using (isElemAbelian_zpowers hx3).2 _ g.2)⟩
    obtain ⟨a, haL', hao, hxa⟩ := exists_central_order_three (X := L' ⊔ Subgroup.zpowers x)
      (L := L') (E := Subgroup.zpowers x) le_sup_left
      ((Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
        (sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.mpr hxL')))
      le_sup_right hEp h3L'
    have ha3 : a ^ 3 = 1 := by
      rw [← hao]
      exact pow_orderOf_eq_one a
    have haC : a ∈ Subgroup.centralizer (V₁ : Set G) := hL'C haL'
    have haN : a ∈ Subgroup.normalizer (V₁ : Set G) := hCN haC
    have haodd : Odd (orderOf a) := by
      rw [hao]
      decide
    have haLn : a ∈ Subgroup.normalizer (L : Set G) := hodd a haN haodd
    have hc' : ⁅L, L'⁆ ≤ pCoreOf 2 L :=
      ((lemma_1_2_1_two hq.qtke hq.simple hq.nonabelian h37 hpc hLN hL'c hne).1).trans inf_le_left
    have haL : a ∉ L := by
      intro haL
      have h1 := eq_one_of_mem_inf_of_odd hs hc' haL haL' haodd
      rw [h1, orderOf_one] at hao
      omega
    obtain ⟨E, hEel, hE9, -, -, hEL, hEle⟩ := exists_elemAbelian_nine
      (C := Subgroup.centralizer (V₁ : Set G)) (L := L) hx3 ha3 hxC haC haL hLV₁
      (hxa x (Subgroup.mem_zpowers x))
    have hEn : E ≤ Subgroup.normalizer (L : Set G) := hEle _ hxL haLn
    have hEN : E ≤ Subgroup.normalizer (V₁ : Set G) := hEle _ hxN haN
    have hXn : L ⊔ E ≤ Subgroup.normalizer (L : Set G) := sup_le Subgroup.le_normalizer hEn
    have hnX : (L.subgroupOf (L ⊔ E)).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr hXn
    have h3X : 3 ≤ CFSG.Open.pRank 3 (L ⊔ E) :=
      S153D.three_le_pRank_of_acts le_sup_left hnX le_sup_right hEel hE9 hEL h3L
    have hXN : L ⊔ E ≤ Subgroup.normalizer (V₁ : Set G) := sup_le hLN' hEN
    have h2' := pRank_le_two_of_pCoreOf_ne_bot hq.qtke hpc Nat.prime_three (by norm_num)
    have h4' := CFSG.SectionRank.pRank_mono (by norm_num : 1 < 3) hXN
    omega

end He15

theorem input15124NotBlock_of' (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hK : KnownFacts15122Types)
    (h15 : StageLemma1515CE) (h1416 : StageLemma1416) : Input15124NotBlock := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc h4 hb
  have hL15 : Lemma1515Concl T Mc M := h15 G T Mc M hc.ctx.qtfe hc.ctx.mf hc.ctx.ce
  have hS := hc.ctx.setting
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  obtain ⟨-, -, -, -, -, hCent⟩ := case15122Two_of_ln3 hK hb hc.h22
  have hV₁L : V₁ ≤ Subgroup.centralizer (L : Set G) :=
    v1_le_centralizer_of_centS
      (lemma_15_1_24_four hc.ctx.qtfe hc.ctx.mf hS hc.small (Or.inl h4)) hLG hCent
  have hLV₁ : L ≤ Subgroup.centralizer (V₁ : Set G) := fun ℓ hℓ =>
    Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (Subgroup.mem_centralizer_iff.mp (hV₁L hv) ℓ hℓ).symm
  exact notblock_core hK h1416 hL15 hc hb h4
    (He15.v1_normalizer_le_normalizer h37 h38 hK hL15 hc hb h4 hLV₁)

end CFSG.Quasithin

module

public import CFSG.RankThree.PartTwo.Sec17.PropUStepTwoB
public import CFSG.RankThree.OddKernel.FixedPlaneKernel

public section

namespace CFSG.RankThree.PartTwo.Sec17.PropU

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec17 CFSG.GH74.GLS
open scoped commutatorElement

theorem pu_conj_mem {G : Type} [Group G] {Q₁ : Subgroup G} {D₀ : Subgroup Q₁}
    (hchar : D₀.Characteristic) {x : G} (hx : x ∈ Subgroup.normalizer (Q₁ : Set G))
    {h : G} (hh : h ∈ D₀.map Q₁.subtype) : x * h * x⁻¹ ∈ D₀.map Q₁.subtype := by
  obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hh
  have hc := Subgroup.characteristic_iff_comap_eq.1 hchar (Q₁.normalizerMonoidHom ⟨x, hx⟩)
  have hd' : d ∈ D₀.comap (Q₁.normalizerMonoidHom ⟨x, hx⟩ : ↥Q₁ ≃* ↥Q₁).toMonoidHom := by
    rw [hc]
    exact hd
  have hαd : Q₁.normalizerMonoidHom ⟨x, hx⟩ d ∈ D₀ := Subgroup.mem_comap.1 hd'
  have hfin : Q₁.subtype (Q₁.normalizerMonoidHom ⟨x, hx⟩ d) ∈ D₀.map Q₁.subtype :=
    Subgroup.mem_map_of_mem Q₁.subtype hαd
  exact hfin

theorem critical_data {G : Type} [Group G] [Finite G] {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2)
    {Q₁ X : Subgroup G} (hQ₁ : IsPGroup q Q₁) (hXQ : X ≤ Subgroup.normalizer (Q₁ : Set G)) :
    ∃ D : Subgroup G, D ≤ Q₁ ∧ X ≤ Subgroup.normalizer (D : Set G) ∧ (∀ d ∈ D, d ^ q = 1) ∧
      ⁅D, D⁆ ≤ Subgroup.centralizer (D : Set G) ∧
      ∀ x ∈ X, Nat.Coprime (orderOf x) q → (∀ d ∈ D, x * d = d * x) →
        ∀ z ∈ Q₁, x * z = z * x := by
  by_cases hne : Q₁ = ⊥
  · subst hne
    refine ⟨⊥, le_rfl, ?_, ?_, ?_, ?_⟩
    · intro x _
      rw [Subgroup.mem_set_normalizer_iff]
      intro h
      simp
    · intro d hd
      rw [Subgroup.mem_bot] at hd
      simp [hd]
    · rw [Subgroup.commutator_le]
      intro a ha b _
      rw [Subgroup.mem_bot] at ha
      simp [ha]
    · intro x _ _ _ z hz
      rw [Subgroup.mem_bot] at hz
      simp [hz]
  · haveI : Nontrivial ↥Q₁ := (Subgroup.nontrivial_iff_ne_bot Q₁).mpr hne
    obtain ⟨D₀, hchar, -, hcomm, hexp, hfix⟩ :=
      CFSG.SectionRank.Ccomm.odd_critical_exponent_subgroup hq2 hQ₁
    refine ⟨D₀.map Q₁.subtype, Subgroup.map_subtype_le D₀, ?_, ?_, ?_, ?_⟩
    · intro x hx
      rw [Subgroup.mem_set_normalizer_iff]
      intro h
      simp only [SetLike.mem_coe]
      constructor
      · intro hh
        exact pu_conj_mem hchar (hXQ hx) hh
      · intro hh
        have h2 := pu_conj_mem hchar (inv_mem (hXQ hx)) hh
        have e : x⁻¹ * (x * h * x⁻¹) * x⁻¹⁻¹ = h := by group
        rwa [e] at h2
    · intro d hd
      obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.1 hd
      have h1 := congrArg Subtype.val (hexp d₀ hd₀)
      simpa using h1
    · rw [Subgroup.commutator_le]
      intro a ha b hb
      obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.1 ha
      obtain ⟨b₀, -, rfl⟩ := Subgroup.mem_map.1 hb
      rw [Subgroup.mem_centralizer_iff]
      intro c hc
      obtain ⟨c₀, hc₀, rfl⟩ := Subgroup.mem_map.1 (SetLike.mem_coe.1 hc)
      have hcen : ⁅a₀, b₀⁆ ∈ Subgroup.centralizer (D₀ : Set Q₁) :=
        (hcomm (Subgroup.commutator_mem_commutator ha₀ (Subgroup.mem_top b₀))).2
      have key := Subgroup.mem_centralizer_iff.1 hcen c₀ (SetLike.mem_coe.2 hc₀)
      have h2 := congrArg Subtype.val key
      simpa [commutatorElement_def] using h2
    · intro x hx hcop hcentD z hz
      have hxn : x ∈ Subgroup.normalizer (Q₁ : Set G) := hXQ hx
      obtain ⟨α, hαdef⟩ : ∃ α : MulAut Q₁, α = Q₁.normalizerMonoidHom ⟨x, hxn⟩ := ⟨_, rfl⟩
      have hαapp : ∀ w : Q₁, ((α w : Q₁) : G) = x * (w : G) * x⁻¹ := by
        intro w
        subst hαdef
        rfl
      have hαfix : α ∈ fixingSubgroup (MulAut Q₁) (D₀ : Set Q₁) := by
        rw [mem_fixingSubgroup_iff]
        intro w hw
        apply Subtype.ext
        show ((α w : Q₁) : G) = (w : G)
        rw [hαapp]
        have h1 : x * (w : G) = (w : G) * x :=
          hcentD _ (Subgroup.mem_map_of_mem Q₁.subtype (SetLike.mem_coe.1 hw))
        rw [h1, mul_inv_cancel_right]
      obtain ⟨k, hk⟩ := hfix ⟨α, hαfix⟩
      have hαpow : α ^ (q ^ k) = 1 := by
        have h1 := congrArg Subtype.val hk
        simpa using h1
      have hdvd_x : orderOf α ∣ orderOf x := by
        have h1 : orderOf α ∣ orderOf (⟨x, hxn⟩ : ↥(Subgroup.normalizer (Q₁ : Set G))) := by
          rw [hαdef]
          exact orderOf_map_dvd Q₁.normalizerMonoidHom _
        have h2 : orderOf (⟨x, hxn⟩ : ↥(Subgroup.normalizer (Q₁ : Set G))) = orderOf x :=
          (Subgroup.orderOf_coe (⟨x, hxn⟩ : ↥(Subgroup.normalizer (Q₁ : Set G)))).symm
        rw [h2] at h1
        exact h1
      have hco : Nat.Coprime (orderOf α) q := Nat.Coprime.coprime_dvd_left hdvd_x hcop
      have hα1 : orderOf α = 1 :=
        Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right k hco) (orderOf_dvd_of_pow_eq_one hαpow)
      have hαone : α = 1 := orderOf_eq_one_iff.1 hα1
      have hz1 : ((α ⟨z, hz⟩ : Q₁) : G) = z := by
        simp [hαone]
      rw [hαapp] at hz1
      exact mul_inv_eq_iff_eq_mul.1 hz1

theorem ker_le_pCore {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q)
    {Q₁ X D : Subgroup G} (hXD : X ≤ Subgroup.normalizer (D : Set G))
    (hcrit : ∀ x ∈ X, Nat.Coprime (orderOf x) q → (∀ d ∈ D, x * d = d * x) →
      ∀ z ∈ Q₁, x * z = z * x)
    (hX3 : oPrimeResidualOf 3 X = X)
    (hF5 : ∀ K : Subgroup ↥X, K.Normal → K ≤ CFSG.pCore 2 ↥X ∨ K = ⊤)
    (hnot : ¬ X ≤ Subgroup.centralizer (Q₁ : Set G)) :
    (D.normalizerMonoidHom.comp (Subgroup.inclusion hXD)).ker ≤ CFSG.pCore 2 ↥X := by
  classical
  set ρ := D.normalizerMonoidHom.comp (Subgroup.inclusion hXD) with hρ
  rcases hF5 ρ.ker (MonoidHom.normal_ker ρ) with h | h
  · exact h
  · exfalso
    apply hnot
    have hall : ∀ x : ↥X, ρ x = 1 := fun x => by
      have hx : x ∈ ρ.ker := by rw [h]; exact Subgroup.mem_top x
      exact hx
    have hcomm : ∀ x : ↥X, ∀ d ∈ D, (x : G) * d = d * (x : G) := by
      intro x d hd
      have h1 : ((ρ x ⟨d, hd⟩ : ↥D) : G) = ((1 : MulAut ↥D) ⟨d, hd⟩ : ↥D) :=
        congrArg (fun σ : MulAut ↥D => ((σ ⟨d, hd⟩ : ↥D) : G)) (hall x)
      have h2 : (x : G) * d * (x : G)⁻¹ = d := h1
      exact mul_inv_eq_iff_eq_mul.mp h2
    have h3 : ∀ x : ↥X, (∃ k : ℕ, x ^ (3 ^ k) = 1) →
        (x : G) ∈ Subgroup.centralizer (Q₁ : Set G) := by
      rintro x ⟨k, hk⟩
      have hk' : (x : G) ^ (3 ^ k) = 1 := by
        have := congrArg Subtype.val hk
        simpa using this
      have hdvd : orderOf (x : G) ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one hk'
      have hcop : Nat.Coprime (orderOf (x : G)) q := by
        have h3q : Nat.Coprime 3 q := (Nat.coprime_primes Nat.prime_three hq).mpr (by omega)
        exact Nat.Coprime.coprime_dvd_left hdvd (Nat.Coprime.pow_left k h3q)
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      exact (hcrit x x.2 hcop (hcomm x) z hz).symm
    intro g hg
    have hg' : g ∈ oPrimeResidualOf 3 X := by rw [hX3]; exact hg
    obtain ⟨c, hc, rfl⟩ := Subgroup.mem_map.mp hg'
    have hle : oPrimeResidual 3 ↥X ≤ (Subgroup.centralizer (Q₁ : Set G)).comap X.subtype := by
      unfold oPrimeResidual
      refine (Subgroup.closure_le _).mpr ?_
      intro x hx
      exact h3 x hx
    exact hle hc

theorem pu_pRank_mono {q : ℕ} (hq : q.Prime) {H : Type} [Group H] [Finite H] {A B : Subgroup H}
    (h : A ≤ B) : CFSG.pRank q ↥A ≤ CFSG.pRank q ↥B := by
  rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hq A,
    CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hq B]
  exact CFSG.SectionRank.pRank_mono hq.one_lt h

theorem pu_rank_chain {q : ℕ} (hq : q.Prime) {G : Type} [Group G] [Finite G] {D : Subgroup G}
    {F : Subgroup ↥D} {C : Subgroup G} (hFC : F.map D.subtype ≤ C) :
    CFSG.pRank q ↥F ≤ CFSG.pRank q ↥C := by
  rw [CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hq F,
    CFSG.Foundations.SteinbergCA.pRank_coe_eq_open_pRank hq C]
  exact (CFSG.SectionRank.pRank_le_map hq.one_lt D.subtype D.subtype_injective F).trans
    (CFSG.SectionRank.pRank_mono hq.one_lt hFC)

theorem pu_conj_val {G : Type} [Group G] {D X : Subgroup G}
    (hXD : X ≤ Subgroup.normalizer (D : Set G)) (x : ↥X) (d : ↥D) :
    ((((D.normalizerMonoidHom.comp (Subgroup.inclusion hXD)) x) d : ↥D) : G)
      = (x : G) * (d : G) * (x : G)⁻¹ :=
  rfl

theorem rank_bound {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2)
    (hloc : CFSG.Assembly.RankThreeEven.localRank q G < 3) {X D : Subgroup G}
    (hXD : X ≤ Subgroup.normalizer (D : Set G)) (hDq : IsPGroup q D) :
    ∀ x : ↥X, x ≠ 1 → IsPGroup 2 (Subgroup.zpowers x) →
      CFSG.pRank q ↥(fixedSubgroupOf ((D.normalizerMonoidHom.comp (Subgroup.inclusion hXD)) x))
        ≤ 2 := by
  intro x hx1 hx2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hx2) ⟨x, Subgroup.mem_zpowers x⟩
  rw [Subgroup.orderOf_mk] at hk
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact hx1 (orderOf_eq_one_iff.1 (by rw [hk, pow_zero]))
  obtain ⟨m, hm⟩ : ∃ m : ℕ, m = 2 ^ (k - 1) := ⟨_, rfl⟩
  have hm0 : m ≠ 0 := by
    rw [hm]
    exact pow_ne_zero _ (by norm_num)
  have hmdvd : m ∣ orderOf x := by
    rw [hk, hm]
    exact pow_dvd_pow 2 (Nat.sub_le k 1)
  have hord : orderOf (x ^ m) = 2 := by
    rw [orderOf_pow_of_dvd hm0 hmdvd, hk, hm,
      Nat.pow_div (Nat.sub_le k 1) (by norm_num : 0 < 2)]
    have h1 : k - (k - 1) = 1 := by omega
    rw [h1, pow_one]
  have hord2 : orderOf ((x ^ m : ↥X) : G) = 2 := by
    rw [Subgroup.orderOf_coe, hord]
  have hsub : fixedSubgroupOf ((D.normalizerMonoidHom.comp (Subgroup.inclusion hXD)) x)
      ≤ fixedSubgroupOf ((D.normalizerMonoidHom.comp (Subgroup.inclusion hXD)) (x ^ m)) := by
    intro d hd
    rw [mem_fixedSubgroupOf] at hd ⊢
    rw [map_pow]
    have h := zpow_apply_eq_self_of_apply_eq_self hd (m : ℤ)
    rw [zpow_natCast] at h
    exact h
  have hle : (fixedSubgroupOf ((D.normalizerMonoidHom.comp (Subgroup.inclusion hXD)) (x ^ m))).map
      D.subtype ≤ Subgroup.centralizer {((x ^ m : ↥X) : G)} := by
    intro y hy
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 hy
    rw [mem_fixedSubgroupOf] at hd
    have hconj : ((x ^ m : ↥X) : G) * (d : G) * ((x ^ m : ↥X) : G)⁻¹ = (d : G) :=
      (pu_conj_val hXD (x ^ m) d).symm.trans (congrArg Subtype.val hd)
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    rw [Set.mem_singleton_iff] at hz
    subst hz
    exact mul_inv_eq_iff_eq_mul.1 hconj
  refine le_trans (pu_pRank_mono hq hsub) ?_
  refine le_trans (pu_rank_chain hq hle) ?_
  have hC := CFSG.RankThree.OddKernel.pRank_centralizer_le_localRank hq.one_lt hord2
  omega

theorem pfCoreInj (hFT : J2NotSectionOfGLFourTwo)
    (hCover : J2CoverHasElemAbelianEight) {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {D Y : Type}
    [Group D] [Finite D] [Group Y] [Finite Y] (hD : IsPGroup q D) (hexp : ∀ x : D, x ^ q = 1)
    (hcl : commutator D ≤ Subgroup.center D) (ρ : Y →* MulAut D) (hρ : Function.Injective ρ)
    (S : Subgroup Y) [S.Normal] (hS : IsPGroup 2 S) (hYJ : Nonempty ((Y ⧸ S) ≃* J2))
    (hY3 : oPrimeResidual 3 Y = ⊤)
    (hrank : ∀ y : Y, y ≠ 1 → IsPGroup 2 (Subgroup.zpowers y) →
      CFSG.pRank q ↥(fixedSubgroupOf (ρ y)) ≤ 2) : False := by
  have hq2 : q ≠ 2 := by
    have := (Fact.out : q.Prime)
    omega
  obtain ⟨e⟩ := hYJ
  haveI : IsSimpleGroup J2 := Sporadic.J2.isSimpleGroup_J2
  haveI : IsSimpleGroup (Y ⧸ S) := e.isSimpleGroup
  have hF5 : ∀ K : Subgroup Y, K.Normal → K ≤ S ∨ K = ⊤ := fun K _ =>
    normal_le_or_eq_top S hS inferInstance hY3 K
  by_cases hE : ∃ E : Subgroup Y, CFSG.Assembly.IsElemAbelian 2 E ∧ Nat.card E = 8
  · obtain ⟨E, hE2, hE8⟩ := hE
    exact false_of_elemAbelianEight hFT hq5 hD hexp hcl ρ hρ S hS hF5 ⟨e⟩ hY3 hrank E hE2 hE8
  · by_cases hc : ∀ y : Y, orderOf y = 7 → ∀ s ∈ S, y * s = s * y
    · have h7 : 7 ∣ Nat.card Y := by
        have h1 : Nat.card (Y ⧸ S) ∣ Nat.card Y := Subgroup.card_quotient_dvd_card S
        have h2 : Nat.card (Y ⧸ S) = 604800 :=
          (Nat.card_congr e.toEquiv).trans Sporadic.J2.card_J2
        exact (show 7 ∣ 604800 by norm_num).trans (h2 ▸ h1)
      exact hE (exists_elemAbelianEight_of_central hCover S hS
        (center_of_order_seven S hS hF5 h7 hc) ⟨e⟩)
    · push Not at hc
      obtain ⟨y, hy, s, hs, hne⟩ := hc
      exact false_of_order_seven_acts hq2 hD ρ hρ S hS hrank hy (fun h => hne (h s hs))

theorem pu_zpow_pow_comm {G : Type*} [Group G] (g : G) (k : ℤ) (N : ℕ) :
    (g ^ k) ^ N = (g ^ N) ^ k := by
  rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast]

theorem pu_isPGroup_zpowers_of_pow {p : ℕ} {G : Type*} [Group G] (g : G) (n : ℕ)
    (hg : g ^ (p ^ n) = 1) : IsPGroup p (Subgroup.zpowers g) := by
  intro h
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp h.2
  refine ⟨n, Subtype.ext ?_⟩
  rw [Subgroup.coe_pow, Subgroup.coe_one, ← hk, pu_zpow_pow_comm, hg, one_zpow]

theorem pfCore (hFT : J2NotSectionOfGLFourTwo)
    (hCover : J2CoverHasElemAbelianEight) {q : ℕ} [Fact q.Prime] (hq5 : 5 ≤ q) {D X : Type}
    [Group D] [Finite D] [Group X] [Finite X] (hD : IsPGroup q D) (hexp : ∀ x : D, x ^ q = 1)
    (hcl : commutator D ≤ Subgroup.center D) (ρ : X →* MulAut D)
    (hX3 : oPrimeResidual 3 X = ⊤) (hXJ : Nonempty ((X ⧸ CFSG.pCore 2 X) ≃* J2))
    (hker : ρ.ker ≤ CFSG.pCore 2 X)
    (hrank : ∀ x : X, x ≠ 1 → IsPGroup 2 (Subgroup.zpowers x) →
      CFSG.pRank q ↥(fixedSubgroupOf (ρ x)) ≤ 2) : False := by
  haveI : Finite (X ⧸ ρ.ker) := Finite.of_surjective _ (QuotientGroup.mk'_surjective ρ.ker)
  have hS : IsPGroup 2 ((CFSG.pCore 2 X).map (QuotientGroup.mk' ρ.ker)) :=
    (CFSG.pCore_isPGroup (p := 2) (G := X)).map _
  have hYJ : Nonempty (((X ⧸ ρ.ker) ⧸ (CFSG.pCore 2 X).map (QuotientGroup.mk' ρ.ker)) ≃* J2) := by
    obtain ⟨e⟩ := hXJ
    exact ⟨(QuotientGroup.quotientQuotientEquivQuotient ρ.ker (CFSG.pCore 2 X) hker).trans e⟩
  have hY3 : oPrimeResidual 3 (X ⧸ ρ.ker) = ⊤ := by
    have hmap : (oPrimeResidual 3 X).map (QuotientGroup.mk' ρ.ker) ≤
        oPrimeResidual 3 (X ⧸ ρ.ker) := by
      unfold oPrimeResidual
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨x, hx, rfl⟩
      obtain ⟨k, hk⟩ := hx
      apply Subgroup.subset_closure
      exact ⟨k, by rw [← map_pow, hk, map_one]⟩
    rw [eq_top_iff]
    intro z _
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective ρ.ker z
    have hxmem : x ∈ oPrimeResidual 3 X := by
      rw [hX3]
      exact Subgroup.mem_top x
    exact hmap (Subgroup.mem_map_of_mem _ hxmem)
  have hrank' : ∀ y : X ⧸ ρ.ker, y ≠ 1 → IsPGroup 2 (Subgroup.zpowers y) →
      CFSG.pRank q ↥(fixedSubgroupOf (QuotientGroup.kerLift ρ y)) ≤ 2 := by
    intro y hy1 hy2
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    have hx1 : x ≠ 1 := by
      rintro rfl
      exact hy1 rfl
    obtain ⟨n, hn⟩ := hy2 ⟨(x : X ⧸ ρ.ker), Subgroup.mem_zpowers _⟩
    have hn' : (x ^ 2 ^ n : X) ∈ ρ.ker := by
      rw [← QuotientGroup.eq_one_iff]
      exact congrArg Subtype.val hn
    obtain ⟨m, hm⟩ := (CFSG.pCore_isPGroup (p := 2) (G := X)) ⟨x ^ 2 ^ n, hker hn'⟩
    have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
      refine pu_isPGroup_zpowers_of_pow (p := 2) x (n + m) ?_
      rw [pow_add, pow_mul]
      exact congrArg Subtype.val hm
    rw [QuotientGroup.kerLift_mk]
    exact hrank x hx1 hx2
  exact pfCoreInj hFT hCover hq5 hD hexp hcl (QuotientGroup.kerLift ρ)
    (QuotientGroup.kerLift_injective ρ) ((CFSG.pCore 2 X).map (QuotientGroup.mk' ρ.ker))
    hS hYJ hY3 hrank'

theorem pf (hFT : J2NotSectionOfGLFourTwo)
    (hCover : J2CoverHasElemAbelianEight) {G : Type} [Group G] [Finite G] {q : ℕ} (hq : q.Prime)
    (hq5 : 5 ≤ q) (hloc : CFSG.Assembly.RankThreeEven.localRank q G < 3)
    {X Q₁ : Subgroup G} (hQ₁ : IsPGroup q Q₁) (hXQ : X ≤ Subgroup.normalizer (Q₁ : Set G))
    (hX3 : oPrimeResidualOf 3 X = X) (hXJ : Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* J2)) :
    X ≤ Subgroup.centralizer (Q₁ : Set G) := by
  by_contra hnot
  haveI : Fact q.Prime := ⟨hq⟩
  have hq2 : q ≠ 2 := by omega
  obtain ⟨D, hDQ, hXD, hexp, hcl, hcrit⟩ := critical_data hq2 hQ₁ hXQ
  have hDq : IsPGroup q D := hQ₁.to_le hDQ
  have hX3' : oPrimeResidual 3 ↥X = ⊤ := by
    have h : (oPrimeResidual 3 ↥X).map X.subtype = (⊤ : Subgroup ↥X).map X.subtype := by
      rw [Subgroup.map_top, Subgroup.range_subtype]
      exact hX3
    exact Subgroup.map_injective X.subtype_injective h
  obtain ⟨e⟩ := hXJ
  haveI : IsSimpleGroup J2 := Sporadic.J2.isSimpleGroup_J2
  haveI : IsSimpleGroup (↥X ⧸ CFSG.pCore 2 ↥X) := e.isSimpleGroup
  have hF5 : ∀ K : Subgroup ↥X, K.Normal → K ≤ CFSG.pCore 2 ↥X ∨ K = ⊤ := fun K _ =>
    normal_le_or_eq_top (CFSG.pCore 2 ↥X) CFSG.pCore_isPGroup inferInstance hX3' K
  have hker := ker_le_pCore hq hq5 hXD hcrit hX3 hF5 hnot
  have hcl' : commutator ↥D ≤ Subgroup.center ↥D := by
    rw [commutator_def, Subgroup.commutator_le]
    intro x _ y _
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 : ((⁅x, y⁆ : ↥D) : G) ∈ ⁅D, D⁆ := by
      have := Subgroup.commutator_mem_commutator x.2 y.2
      simpa [commutatorElement_def] using this
    have h2 := Subgroup.mem_centralizer_iff.mp (hcl h1) (z : G) z.2
    exact Subtype.ext (by simpa using h2)
  exact pfCore hFT hCover hq5 hDq (fun x => by
      have := hexp (x : G) x.2
      exact Subtype.ext (by simpa using this)) hcl'
    (D.normalizerMonoidHom.comp (Subgroup.inclusion hXD)) hX3' ⟨e⟩ hker
    (rank_bound hq hq2 hloc hXD hDq)

end CFSG.RankThree.PartTwo.Sec17.PropU

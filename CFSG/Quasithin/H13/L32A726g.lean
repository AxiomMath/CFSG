module

public import CFSG.Quasithin.H13.L32A726f

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.ABGLocalTools

variable {G : Type} [Group G] [Finite G]

section General

variable {A A' : Type*} [Group A] [Group A'] [Finite A] [Finite A']

omit [Finite A] [Finite A'] in
theorem comap_pCore_eq_726 {p : ℕ} [Fact p.Prime] {f : A →* A'} (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) : (CFSG.pCore p A').comap f = CFSG.pCore p A := by
  apply le_antisymm
  · exact le_sSup ⟨(CFSG.pCore_normal (p := p) (G := A')).comap f,
      (CFSG.pCore_isPGroup (p := p) (G := A')).comap_of_ker_isPGroup f hker⟩
  · intro a ha
    have hle : (CFSG.pCore p A).map f ≤ CFSG.pCore p A' :=
      le_sSup ⟨(CFSG.pCore_normal (p := p) (G := A)).map f hf,
        (CFSG.pCore_isPGroup (p := p) (G := A)).map f⟩
    exact hle ⟨a, ha, rfl⟩

omit [Finite A] [Finite A'] in
theorem map_pCore_eq_726 {p : ℕ} [Fact p.Prime] {f : A →* A'} (hf : Function.Surjective f)
    (hker : IsPGroup p f.ker) : (CFSG.pCore p A).map f = CFSG.pCore p A' := by
  rw [← comap_pCore_eq_726 hf hker, Subgroup.map_comap_eq_self_of_surjective hf]

@[expose] noncomputable def quotPCoreEquiv_726 {p : ℕ} [Fact p.Prime] (f : A →* A')
    (hf : Function.Surjective f) (hker : IsPGroup p f.ker) :
    A ⧸ CFSG.pCore p A ≃* A' ⧸ CFSG.pCore p A' :=
  have hsurj : Function.Surjective ((QuotientGroup.mk' (CFSG.pCore p A')).comp f) :=
    (QuotientGroup.mk'_surjective _).comp hf
  have hk : CFSG.pCore p A = ((QuotientGroup.mk' (CFSG.pCore p A')).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', comap_pCore_eq_726 hf hker]
  (QuotientGroup.quotientMulEquivOfEq hk).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ hsurj)

omit [Finite A'] in
theorem isPOnePlusTwo_oTwoUpper_of_mulEquiv_726 (e : A ≃* A')
    (h : IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup A))) :
    IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup A')) := by
  have hmap : oTwoUpper (⊤ : Subgroup A') = (oTwoUpper (⊤ : Subgroup A)).map e.toMonoidHom := by
    rw [← oTwoUpper_map, Subgroup.map_top_of_surjective _ e.surjective]
  rw [hmap]
  exact isPOnePlusTwo_of_mulEquiv
    (Subgroup.equivMapOfInjective _ e.toMonoidHom e.injective) h

end General

section Ctx

variable {T L V H D : Subgroup G}

theorem oTwoUpper_hd_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) :
    oTwoUpper (H ⊓ Subgroup.centralizer ({d} : Set G)) = oTwoUpper H := by
  apply le_antisymm (oTwoUpper_mono inf_le_left)
  calc oTwoUpper H = oTwoUpper (oTwoUpper H) := (A4.oTwoUpper_oTwoUpper H).symm
    _ ≤ oTwoUpper (H ⊓ Subgroup.centralizer ({d} : Set G)) := oTwoUpper_mono (k_le_hd_726 hc hdD)

theorem isPOnePlusTwo_hd_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) :
    IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥(H ⊓ Subgroup.centralizer ({d} : Set G)) ⧸
      CFSG.pCore 2 ↥(H ⊓ Subgroup.centralizer ({d} : Set G))))) := by
  set Hd := H ⊓ Subgroup.centralizer ({d} : Set G) with hHd
  have hKHd : oTwoUpper H ≤ Hd := k_le_hd_726 hc hdD
  have hHdK : Hd ≤ Subgroup.normalizer (oTwoUpper H : Set G) :=
    inf_le_left.trans (le_normalizer_oTwoUpper H)
  have hmod : modO2Image Hd (oTwoUpper H) = oTwoUpper (⊤ : Subgroup (↥Hd ⧸ CFSG.pCore 2 ↥Hd)) := by
    rw [← oTwoUpper_hd_726 hc hdD]
    exact modO2Image_oTwoUpper Hd
  exact isPOnePlusTwo_of_mulEquiv ((quotEquivStar hKHd hHdK).trans (MulEquiv.subgroupCongr hmod))
    (isPOnePlusTwo_K hc.three)

theorem exists_card_h_726 (hc : Ctx726 G T L V H D) : ∃ a : ℕ, Nat.card H = 2 ^ a * 27 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_card_k_726 hc
  have hTK : T ≤ Subgroup.normalizer (oTwoUpper H : Set G) := t_le_normalizer_k_726 hc
  have e := card_sup_mul_726 hTK
  rw [sup_comm, ← hc.eq_kt, ha] at e
  obtain ⟨b, hb⟩ := hc.setting.hyp.hyp.h13.sylow.1.exists_card_eq
  obtain ⟨c, -, hcd⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp
    (hb ▸ Subgroup.card_dvd_of_le (inf_le_left : T ⊓ oTwoUpper H ≤ T))
  rw [hb, hcd] at e
  have hcle : c ≤ b + a := by
    have h1 : 2 ^ c ∣ 2 ^ (b + a) * 27 := ⟨Nat.card H, by rw [pow_add, mul_assoc, ← e]; ring⟩
    have h2 : Nat.Coprime (2 ^ c) 27 := Nat.Coprime.pow_left c (by norm_num)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (h2.dvd_of_dvd_mul_right h1)
  refine ⟨b + a - c, ?_⟩
  have hpos : 0 < 2 ^ c := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [e, show 2 ^ (b + a - c) * 27 * 2 ^ c = 2 ^ (b + a - c + c) * 27 by ring,
    Nat.sub_add_cancel hcle, pow_add]
  ring

theorem exists_card_hd_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) :
    ∃ a : ℕ, Nat.card (H ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) = 2 ^ a * 27 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_card_h_726 hc
  obtain ⟨b, hb⟩ := exists_card_k_726 hc
  have hKHd := k_le_hd_726 hc hdD
  have h1 : 2 ^ b * 27 ∣ Nat.card (H ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) :=
    hb ▸ Subgroup.card_dvd_of_le hKHd
  have h2 : Nat.card (H ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) ∣ 2 ^ a * 27 :=
    ha ▸ Subgroup.card_dvd_of_le inf_le_left
  obtain ⟨m, hm⟩ := h1
  have h27 : 27 ∣ Nat.card (H ⊓ Subgroup.centralizer ({d} : Set G) : Subgroup G) :=
    ⟨2 ^ b * m, by rw [hm]; ring⟩
  obtain ⟨n, hn⟩ := h27
  have hn2 : n ∣ 2 ^ a := by
    rw [hn, mul_comm] at h2
    exact Nat.dvd_of_mul_dvd_mul_right (by norm_num) h2
  obtain ⟨e, -, he⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp hn2
  exact ⟨e, by rw [hn, he, mul_comm]⟩

theorem zpowers_eq_of_mem_center_726 (hc : Ctx726 G T L V H D) {x : G} {Y E₁ E₂ : Subgroup G}
    (hX : XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂) {c : G} (hcY : c ∈ Y)
    (hcc : ∀ y ∈ Y, c * y = y * c) (hc3 : orderOf c = 3) :
    Subgroup.zpowers c = Subgroup.zpowers x := by
  have hr := pRank_three_le_726 hc (pCoreOf_h_ne_bot_726 hc)
  have hYH : Y ≤ H := hX.y_le.trans (oTwoUpper_le H)
  have h₁ := mem_of_commute_of_pRank_726 hr ((hX.e₁_le.trans hYH)) hX.e₁_elem hX.e₁_card
    (hYH hcY) hc3 fun e he => hcc e (hX.e₁_le he)
  have h₂ := mem_of_commute_of_pRank_726 hr ((hX.e₂_le.trans hYH)) hX.e₂_elem hX.e₂_card
    (hYH hcY) hc3 fun e he => hcc e (hX.e₂_le he)
  exact Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (hX.inf_le ⟨h₁, h₂⟩))
    (by rw [Nat.card_zpowers, Nat.card_zpowers, hc3, hX.x_order])

theorem mem_of_normal_y_726 (hc : Ctx726 G T L V H D) {x : G} {Y E₁ E₂ : Subgroup G}
    (hX : XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂) {N : Subgroup G} (hNY : N ≤ Y)
    (hYN : Y ≤ Subgroup.normalizer (N : Set G)) (hN : N ≠ ⊥) : x ∈ N := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨c', hc'N, hc'1, hc'c⟩ := exists_mem_inf_center_726 hX.y_pgroup hNY hYN hN
  obtain ⟨c, hcc', hc3⟩ := exists_pow_orderOf_three_726 hX.y_pgroup (hNY hc'N) hc'1
  have hcN : c ∈ N := (Subgroup.zpowers_le.mpr hc'N) hcc'
  have hcc : ∀ y ∈ Y, c * y = y * c := fun y hy =>
    (commute_zpowers_726 (hc'c y hy).symm hcc').symm
  have heq := zpowers_eq_of_mem_center_726 hc hX (hNY hcN) hcc hc3
  have hxc : x ∈ Subgroup.zpowers c := by rw [heq]; exact Subgroup.mem_zpowers x
  exact (Subgroup.zpowers_le.mpr hcN) hxc

omit [Finite G] in
theorem le_normalizer_map_726 {X : Subgroup G} {M : Subgroup ↥X} (hM : M.Normal) :
    X ≤ Subgroup.normalizer ((M.map X.subtype : Subgroup G) : Set G) := by
  have key : ∀ h ∈ X, ∀ g ∈ M.map X.subtype, h * g * h⁻¹ ∈ M.map X.subtype := by
    rintro h hh _ ⟨k, hk, rfl⟩
    exact ⟨⟨h, hh⟩ * k * ⟨h, hh⟩⁻¹, hM.conj_mem k hk ⟨h, hh⟩, rfl⟩
  intro h hh
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key h hh g, fun hg => ?_⟩
  have := key h⁻¹ (X.inv_mem hh) _ hg
  rwa [show h⁻¹ * (h * g * h⁻¹) * h⁻¹⁻¹ = g by group] at this

theorem isPGroup_ker_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) {x : G}
    {Y E₁ E₂ : Subgroup G} (hX : XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂)
    {Hd : Subgroup G} (hHd : H ⊓ Subgroup.centralizer ({d} : Set G) = Hd) {A₀ : Type*}
    [Group A₀] (ψ : ↥Hd →* A₀)
    (hx : ∀ hx : x ∈ Hd, ψ ⟨x, hx⟩ ≠ 1) :
    IsPGroup 2 ψ.ker := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hYHd : Y ≤ Hd := hHd ▸ hX.y_le.trans (k_le_hd_726 hc hdD)
  obtain ⟨a, ha⟩ := exists_card_hd_726 hc hdD
  rw [hHd] at ha
  have hv : (Nat.card Hd).factorization 3 = 3 := by
    rw [ha, Nat.factorization_mul (by positivity) (by norm_num), Finsupp.add_apply,
      Nat.factorization_pow, Finsupp.smul_apply,
      Nat.factorization_eq_zero_of_not_dvd (show ¬ 3 ∣ 2 by norm_num),
      show (27 : ℕ) = 3 ^ 3 by norm_num, Nat.factorization_pow]
    simp [Nat.Prime.factorization_self Nat.prime_three]
  have hYsyl : IsSylowOf 3 Y Hd := isSylowOf_of_card hYHd (by rw [hX.y_card, hv]; norm_num)
  set kerG : Subgroup G := ψ.ker.map Hd.subtype with hkerG
  have hHdk : Hd ≤ Subgroup.normalizer (kerG : Set G) := le_normalizer_map_726 ψ.normal_ker
  have h3 : ∀ m ∈ ψ.ker, m ^ 27 = 1 → m = 1 := by
    intro m hm hm27
    by_contra hm1
    have hzp : IsPGroup 3 (Subgroup.zpowers m) := by
      intro g
      obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp g.2
      refine ⟨3, Subtype.ext ?_⟩
      show ((g : ↥Hd)) ^ 3 ^ 3 = 1
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
        show (3 : ℕ) ^ 3 = 27 by norm_num, hm27, one_zpow]
    obtain ⟨S, hS⟩ := hzp.exists_le_sylow
    have hS' : IsSylowOf 3 ((S : Subgroup ↥Hd).map Hd.subtype) Hd := ⟨S, rfl⟩
    obtain ⟨i, hiHd, hi⟩ := exists_conj_of_isSylowOf_726 hYsyl hS'
    have hmS : (m : G) ∈ (S : Subgroup ↥Hd).map Hd.subtype :=
      ⟨m, hS (Subgroup.mem_zpowers m), rfl⟩
    have hmY : i⁻¹ * (m : G) * i ∈ Y := (hi _).mp hmS
    set m' : ↥Hd := (⟨i, hiHd⟩ : ↥Hd)⁻¹ * m * ⟨i, hiHd⟩ with hm'def
    have hm'ker : m' ∈ ψ.ker := by
      have := ψ.normal_ker.conj_mem m hm (⟨i, hiHd⟩ : ↥Hd)⁻¹
      simpa [hm'def] using this
    have hm'G : (m' : G) = i⁻¹ * m * i := by simp [hm'def]
    have hNY : Y ≤ Subgroup.normalizer ((Y ⊓ kerG : Subgroup G) : Set G) := by
      intro y hy
      rw [Subgroup.mem_normalizer_iff]
      intro n
      have h1 := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer hy) n
      have h2 := Subgroup.mem_normalizer_iff.mp (hHdk (hYHd hy)) n
      exact ⟨fun hn => ⟨h1.mp hn.1, h2.mp hn.2⟩, fun hn => ⟨h1.mpr hn.1, h2.mpr hn.2⟩⟩
    have hNne : Y ⊓ kerG ≠ ⊥ := by
      intro hbot
      have hmem : (m' : G) ∈ Y ⊓ kerG := ⟨hm'G ▸ hmY, ⟨m', hm'ker, rfl⟩⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      apply hm1
      have h1 : m' = 1 := Subtype.ext hmem
      rw [hm'def] at h1
      have h2 : m = (⟨i, hiHd⟩ : ↥Hd) * ((⟨i, hiHd⟩ : ↥Hd)⁻¹ * m * ⟨i, hiHd⟩) *
          (⟨i, hiHd⟩ : ↥Hd)⁻¹ := by group
      rw [h2, h1]
      group
    obtain ⟨-, y, hy, hyx⟩ := mem_of_normal_y_726 hc hX inf_le_left hNY hNne
    apply hx (hYHd hX.x_mem_y)
    have : y = ⟨x, hYHd hX.x_mem_y⟩ := Subtype.ext hyx
    rw [← this]
    exact hy
  intro n
  refine ⟨a, Subtype.ext ?_⟩
  have hn : (n : ↥Hd) ^ (2 ^ a * 27) = 1 := by rw [← ha]; exact pow_card_eq_one'
  have h := h3 ((n : ↥Hd) ^ 2 ^ a) (ψ.ker.pow_mem n.2 _) (by rw [← pow_mul]; exact hn)
  simpa using h

theorem card_range_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) {x : G}
    {Y E₁ E₂ : Subgroup G} (hX : XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂)
    {Hd : Subgroup G} (hHd : H ⊓ Subgroup.centralizer ({d} : Set G) = Hd) {A₀ : Type*}
    [Group A₀] (ψ : ↥Hd →* A₀)
    (hx : ∀ hx : x ∈ Hd, ψ ⟨x, hx⟩ ≠ 1) :
    ∃ a : ℕ, Nat.card ψ.range = 2 ^ a * 27 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨a, ha⟩ := exists_card_hd_726 hc hdD
  rw [hHd] at ha
  obtain ⟨c, hcard⟩ := (isPGroup_ker_726 hc hdD hX hHd ψ hx).exists_card_eq
  have e : Nat.card ψ.range * 2 ^ c = 2 ^ a * 27 := by
    rw [← hcard, ← ha, Nat.card_congr (QuotientGroup.quotientKerEquivRange ψ).toEquiv.symm,
      ← Subgroup.card_eq_card_quotient_mul_card_subgroup]
  have hcle : c ≤ a := by
    have h1 : 2 ^ c ∣ 2 ^ a * 27 := ⟨Nat.card ψ.range, by rw [← e]; ring⟩
    have h2 : Nat.Coprime (2 ^ c) 27 := Nat.Coprime.pow_left c (by norm_num)
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp (h2.dvd_of_dvd_mul_right h1)
  refine ⟨a - c, ?_⟩
  have hpos : 0 < 2 ^ c := by positivity
  apply Nat.eq_of_mul_eq_mul_right hpos
  rw [e, show 2 ^ (a - c) * 27 * 2 ^ c = 2 ^ (a - c + c) * 27 by ring, Nat.sub_add_cancel hcle]

theorem isPOnePlusTwo_range_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D) {x : G}
    {Y E₁ E₂ : Subgroup G} (hX : XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂)
    {Hd : Subgroup G} (hHd : H ⊓ Subgroup.centralizer ({d} : Set G) = Hd) {A₀ : Type*}
    [Group A₀] [Finite A₀] (ψ : ↥Hd →* A₀)
    (hx : ∀ hx : x ∈ Hd, ψ ⟨x, hx⟩ ≠ 1) :
    IsPOnePlusTwo 3 ↥(oTwoUpper (⊤ : Subgroup (↥ψ.range ⧸ CFSG.pCore 2 ↥ψ.range))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 ψ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact isPGroup_ker_726 hc hdD hX hHd ψ hx
  have hHdq := isPOnePlusTwo_hd_726 hc hdD
  rw [hHd] at hHdq
  exact isPOnePlusTwo_oTwoUpper_of_mulEquiv_726
    (quotPCoreEquiv_726 ψ.rangeRestrict ψ.rangeRestrict_surjective hker) hHdq

theorem pCoreOf_range_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) (hQ : pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G)) {x : G}
    {Y E₁ E₂ : Subgroup G} (hX : XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂)
    {Hd : Subgroup G} (hHd : H ⊓ Subgroup.centralizer ({d} : Set G) = Hd) {A₀ : Type*}
    [Group A₀] [Finite A₀] (ψ : ↥Hd →* A₀)
    (hx : ∀ hx : x ∈ Hd, ψ ⟨x, hx⟩ ≠ 1) :
    pCoreOf 2 ψ.range =
      ((pCoreOf 2 H).subgroupOf Hd).map ψ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hker : IsPGroup 2 ψ.rangeRestrict.ker := by
    rw [MonoidHom.ker_rangeRestrict]
    exact isPGroup_ker_726 hc hdD hX hHd ψ hx
  have h1 : CFSG.pCore 2 ↥ψ.range = (CFSG.pCore 2 ↥Hd).map ψ.rangeRestrict :=
    (map_pCore_eq_726 ψ.rangeRestrict_surjective hker).symm
  have hQeq := pCoreOf_hd_eq_726 hc hdD hdV hQ
  rw [hHd] at hQeq
  have h2 : (pCoreOf 2 H).subgroupOf Hd = CFSG.pCore 2 ↥Hd := by
    rw [← hQeq, pCoreOf, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective Hd.subtype_injective]
  rw [pCoreOf, h1, h2, Subgroup.map_map]
  rfl

omit [Finite G] in
theorem mem_normalizer_sup_726 {A B : Subgroup G} {g : G}
    (hA : g ∈ Subgroup.normalizer (A : Set G)) (hB : g ∈ Subgroup.normalizer (B : Set G)) :
    g ∈ Subgroup.normalizer ((A ⊔ B : Subgroup G) : Set G) := by
  have key : ∀ g : G, g ∈ Subgroup.normalizer (A : Set G) →
      g ∈ Subgroup.normalizer (B : Set G) → ∀ y ∈ A ⊔ B, g * y * g⁻¹ ∈ A ⊔ B := by
    intro g hA hB y hy
    have hle : A ⊔ B ≤ (A ⊔ B).comap (MulAut.conj g).toMonoidHom := sup_le
      (fun a ha => Subgroup.mem_sup_left ((Subgroup.mem_normalizer_iff.mp hA a).mp ha))
      (fun b hb => Subgroup.mem_sup_right ((Subgroup.mem_normalizer_iff.mp hB b).mp hb))
    exact hle hy
  rw [Subgroup.mem_normalizer_iff]
  intro y
  refine ⟨key g hA hB y, fun hy => ?_⟩
  have h := key g⁻¹ (inv_mem hA) (inv_mem hB) _ hy
  rwa [show g⁻¹ * (g * y * g⁻¹) * g⁻¹⁻¹ = y by group] at h

omit [Finite G] in
theorem range_le_normalizer_map_726 {X : Type*} [Group X] {A₀ : Type*} [Group A₀]
    (ψ : X →* A₀) {M : Subgroup X} (hM : M.Normal) :
    ψ.range ≤ Subgroup.normalizer ((M.map ψ : Subgroup A₀) : Set A₀) := by
  have key : ∀ h : X, ∀ b ∈ M.map ψ, ψ h * b * (ψ h)⁻¹ ∈ M.map ψ := by
    rintro h _ ⟨m, hm, rfl⟩
    exact ⟨h * m * h⁻¹, hM.conj_mem m hm h, by simp⟩
  rintro _ ⟨h, rfl⟩
  rw [Subgroup.mem_normalizer_iff]
  intro b
  refine ⟨key h b, fun hb => ?_⟩
  have h1 := key h⁻¹ _ hb
  rwa [map_inv, show (ψ h)⁻¹ * (ψ h * b * (ψ h)⁻¹) * (ψ h)⁻¹⁻¹ = b by group] at h1

theorem pCoreOf_l1_le_726 (hc : Ctx726 G T L V H D) :
    pCoreOf 2 (L32A.l1 T L V) ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  exact le_pCoreOf_of_le_normalizer 2
    ((pCoreOf_le 2 _).trans ((l1_le_k_726 hc).trans (oTwoUpper_le H)))
    (hc.l1_normal.trans (normalizer_le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)

theorem range_le_normalizer_726 (hc : Ctx726 G T L V H D) {d : G} (hdD : d ∈ D)
    (hdV : d ∉ fsuV1 T V) (hQ : pCoreOf 2 H ≤ T ⊓ Subgroup.centralizer ({d} : Set G)) {x : G}
    {Y E₁ E₂ : Subgroup G} (hX : XData726 (oTwoUpper H) (L32A.l1 T L V) x Y E₁ E₂)
    {Hd : Subgroup G} (hHd : H ⊓ Subgroup.centralizer ({d} : Set G) = Hd) {A₀ : Type*}
    [Group A₀] [Finite A₀] (ψ : ↥Hd →* A₀)
    (hx : ∀ hx : x ∈ Hd, ψ ⟨x, hx⟩ ≠ 1)
    (hxHd : x ∈ Hd) :
    ψ.range ≤ Subgroup.normalizer ((Subgroup.zpowers (ψ ⟨x, hxHd⟩) ⊔ pCoreOf 2 ψ.range :
      Subgroup A₀) : Set A₀) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q := pCoreOf 2 H with hQdef
  have hQHd : Q ≤ Hd := hHd ▸ hQ.trans (td_le_hd_726 hc d)
  have hHdH : Hd ≤ H := hHd ▸ inf_le_left
  set N1 : Subgroup ↥Hd := Subgroup.zpowers ⟨x, hxHd⟩ ⊔ Q.subgroupOf Hd with hN1
  have hN1G : N1.map Hd.subtype = L32A.l1 T L V ⊔ Q := by
    rw [hN1, Subgroup.map_sup, MonoidHom.map_zpowers, Subgroup.map_subgroupOf_eq_of_le hQHd]
    apply le_antisymm
    · exact sup_le_sup_right (Subgroup.zpowers_le.mpr hX.x_mem) Q
    · refine sup_le ?_ le_sup_right
      refine (l1_le_conjClosure_726 hc hX.x_mem hX.x_order).trans ?_
      refine (conjClosure_mono le_rfl (pCoreOf_l1_le_726 hc)).trans ?_
      exact A3.conjClosure_le_sup _ _
  have hHN : H ≤ Subgroup.normalizer ((L32A.l1 T L V ⊔ Q : Subgroup G) : Set G) :=
    fun h hh => mem_normalizer_sup_726 (hc.l1_normal hh) (le_normalizer_pCoreOf 2 H hh)
  have hN1n : N1.Normal := by
    refine ⟨fun n hn g => ?_⟩
    have hnG : (n : G) ∈ N1.map Hd.subtype := ⟨n, hn, rfl⟩
    rw [hN1G] at hnG
    have h1 : ((g * n * g⁻¹ : ↥Hd) : G) ∈ N1.map Hd.subtype := by
      rw [hN1G]
      exact (Subgroup.mem_normalizer_iff.mp (hHN (hHdH g.2)) _).mp hnG
    obtain ⟨m, hm, hmeq⟩ := h1
    have : m = g * n * g⁻¹ := Subtype.ext hmeq
    rwa [← this]
  have heq : Subgroup.zpowers (ψ ⟨x, hxHd⟩) ⊔ pCoreOf 2 ψ.range = N1.map ψ := by
    rw [pCoreOf_range_726 hc hdD hdV hQ hX hHd ψ hx, hN1, Subgroup.map_sup, MonoidHom.map_zpowers]
  rw [heq]
  exact range_le_normalizer_map_726 ψ hN1n

end Ctx

end CFSG.Quasithin.H13.L32A

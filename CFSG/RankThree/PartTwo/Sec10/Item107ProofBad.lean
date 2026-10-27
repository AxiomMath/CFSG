module

public import CFSG.RankThree.PartTwo.Sec10.Item107ProofBasic

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item107Proof

section Arith

theorem dvd_mul_sixtyfour_of_dvd {n k m : ℕ} (hn : n ≤ 81) (hn0 : 0 < n) (h : n ∣ m * 2 ^ k) :
    n ∣ m * 64 := by
  have hg : Nat.gcd n (2 ^ k) ∣ 64 := by
    have h1 : Nat.gcd n (2 ^ k) ∣ 2 ^ k := Nat.gcd_dvd_right _ _
    obtain ⟨j, hj, hjeq⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
    have h2 : 2 ^ j ≤ 81 := hjeq ▸ (Nat.le_of_dvd hn0 (Nat.gcd_dvd_left _ _)).trans hn
    have hj6 : j ≤ 6 := by
      by_contra hj6
      have : 2 ^ 7 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
      omega
    rw [hjeq]
    exact (Nat.pow_dvd_pow 2 hj6).trans (by norm_num)
  have h3 : n ∣ m * Nat.gcd n (2 ^ k) := by
    have : n ∣ Nat.gcd (m * n) (m * 2 ^ k) := Nat.dvd_gcd (dvd_mul_left n m) h
    rwa [Nat.gcd_mul_left] at this
  exact h3.trans (Nat.mul_dvd_mul_left m hg)

theorem twentyseven_dvd_of_bounds : ∀ n : ℕ, n < 82 → 14 ≤ n → n ∣ 11232 * 64 →
    n % 13 = 1 ∨ n % 13 = 2 → 27 ∣ n := by
  decide

theorem false_of_indices {n r₁ r₂ iE k : ℕ} (hn1 : 14 ≤ n) (hn2 : n ≤ 81)
    (hn13 : n % 13 = 1 ∨ n % 13 = 2) (hr₁ : 3 ∣ r₁) (hr₂ : r₂ = 2 ^ k) (hiE : iE ∣ 11232)
    (heq : r₁ * n = r₂ * iE) : False := by
  have hn : n ∣ 11232 * 2 ^ k := by
    have h1 : n ∣ r₂ * iE := heq ▸ dvd_mul_left n r₁
    rw [hr₂] at h1
    exact h1.trans (by rw [mul_comm]; exact Nat.mul_dvd_mul_right hiE _)
  have h27 := twentyseven_dvd_of_bounds n (by omega) hn1
    (dvd_mul_sixtyfour_of_dvd hn2 (by omega) hn) hn13
  have h81 : 81 ∣ iE * 2 ^ k := by
    rw [mul_comm, ← hr₂, ← heq]
    obtain ⟨u, hu⟩ := hr₁
    obtain ⟨v, hv⟩ := h27
    exact ⟨u * v, by rw [hu, hv]; ring⟩
  have hcop : Nat.Coprime 81 (2 ^ k) := Nat.Coprime.pow_right _ (by norm_num)
  have h3 := (hcop.dvd_of_dvd_mul_right h81).trans hiE
  norm_num at h3

end Arith

section Std


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem mem_normalizer_D_of (h : Sec10Std G A c L a R) {y : G} (hyc : y * c = c * y)
    (hyN : y ∈ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G)) :
    y ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G) := by
  apply Sec11.mem_normalizer_of_forall_conj_mem
  intro u hu
  obtain ⟨k, e, he, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers
    (fun z hz => h.commute_c_of_mem_inf hz) hu
  have hyck : y⁻¹ * c ^ k * y = c ^ k := by
    have := (Commute.zpow_right (show Commute y c from hyc) k)
    rw [mul_assoc, ← this.eq, inv_mul_cancel_left]
  have h1 : y⁻¹ * (c ^ k * e) * y = c ^ k * (y⁻¹ * e * y) := by
    calc y⁻¹ * (c ^ k * e) * y = (y⁻¹ * c ^ k * y) * (y⁻¹ * e * y) := by group
      _ = c ^ k * (y⁻¹ * e * y) := by rw [hyck]
  rw [h1]
  have h2 : y⁻¹ * e * y ∈ R ⊓ L := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hyN) e).mp he
    simpa using this
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (Subgroup.zpow_mem_zpowers c k))
    (Subgroup.mem_sup_right h2)

theorem mem_centralizer_D_of (h : Sec10Std G A c L a R) {y : G} (hyc : y * c = c * y)
    (hyE : ∀ e ∈ R ⊓ L, y * e * y⁻¹ = e) :
    y ∈ Subgroup.centralizer ((sec10D c R L : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro u hu
  obtain ⟨k, e, he, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers
    (fun z hz => h.commute_c_of_mem_inf hz) hu
  have hye : y * e = e * y := by
    have := hyE e he
    calc y * e = y * e * y⁻¹ * y := by group
      _ = e * y := by rw [this]
  have hyck : c ^ k * y = y * c ^ k := ((Commute.zpow_right (show Commute y c from hyc) k)).eq.symm
  calc c ^ k * e * y = c ^ k * (e * y) := by group
    _ = c ^ k * (y * e) := by rw [hye]
    _ = (c ^ k * y) * e := by group
    _ = y * (c ^ k * e) := by rw [hyck]; group

theorem mem_zpowers_c_of_fix (h : Sec10Std G A c L a R) {x : G}
    (hxfix : ∀ e ∈ R ⊓ L, x * e * x⁻¹ = e → e = 1) (hxc : x * c = c * x) {u : G}
    (hu : u ∈ sec10D c R L) (hfix : x * u * x⁻¹ = u) : u ∈ Subgroup.zpowers c := by
  obtain ⟨k, e, he, rfl⟩ := exists_zpow_mul_of_mem_sup_zpowers
    (fun y hy => h.commute_c_of_mem_inf hy) hu
  have hxck : x * c ^ k * x⁻¹ = c ^ k := by
    rw [← conj_zpow, hxc, mul_inv_cancel_right]
  have hefix : x * e * x⁻¹ = e := by
    have h2 : x * (c ^ k * e) * x⁻¹ = (x * c ^ k * x⁻¹) * (x * e * x⁻¹) := by group
    rw [h2, hxck] at hfix
    exact mul_left_cancel hfix
  rw [hxfix e he hefix, mul_one]
  exact Subgroup.zpow_mem_zpowers c k

theorem exists_not_commute_a (h97 : Sec9.Item97) (h : Sec10Std G A c L a R) :
    ∃ e ∈ R ⊓ L, a * e * a⁻¹ ≠ e := by
  obtain ⟨d, hdL, hd3, hA⟩ := exists_inf_eq_zpowers h97 h.toHyp91
  by_contra hcon
  push Not at hcon
  have hle : R ⊓ L ≤ R ⊓ L ⊓ Subgroup.centralizer ({a} : Set G) := fun e he =>
    ⟨he, Subgroup.mem_centralizer_singleton_iff.mpr (by
      have h1 := hcon e he
      calc e * a = a * e * a⁻¹ * a := by rw [h1]
        _ = a * e := by group)⟩
  rw [h.inf_centralizer_a hdL hA] at hle
  have h1 := Subgroup.card_le_of_le hle
  rw [h.card_inf, Nat.card_zpowers, hd3] at h1
  norm_num at h1

theorem card_mulAut_inf (h : Sec10Std G A c L a R) :
    Nat.card (MulAut (R ⊓ L : Subgroup G)) = 11232 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE := h.isElemAbelian_inf
  have hcomm : ∀ x y : (R ⊓ L : Subgroup G), x * y = y * x := fun x y => hE.1.is_comm.comm x y
  have hpow : ∀ x : (R ⊓ L : Subgroup G), x ^ 3 = 1 := fun x =>
    Subtype.ext (by simpa using hE.2 x x.2)
  obtain ⟨e⟩ := CFSG.SectionRank.Ccomm.nonempty_mulEquiv_of_elementary (p := 3) hcomm hpow
    (n := 3) (by rw [h.card_inf]; norm_num)
  rw [CFSG.SectionRank.Ccomm.card_mulAut_eq_card_GL e, CFSG.SectionRank.Ccomm.card_GL_zmod,
    Fin.prod_univ_three]
  norm_num

theorem sq_conj_c_eq (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h : Sec10Std G A c L a R)
    (hbad : ∀ m ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G),
      (∀ e' ∈ R ⊓ L, m * e' * m⁻¹ = e') → m * c * m⁻¹ * c⁻¹ ∈ R ⊓ L → m * c * m⁻¹ = c)
    {m : G} (hm : m ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G))
    (hmE : ∀ e ∈ R ⊓ L, m * e * m⁻¹ = e) : (m * m) * c * (m * m)⁻¹ = c := by
  have hc3 : c ^ 3 = 1 := h.pow_three h.mem_A
  obtain ⟨k, e, he, hke⟩ := exists_zpow_mul_of_mem_sup_zpowers
    (fun y hy => h.commute_c_of_mem_inf hy) (conj_c_mem_D h hm)
  have he3 : e ^ 3 = 1 := h.isElemAbelian_inf.2 e he
  have hce : e * c = c * e := h.commute_c_of_mem_inf he
  rcases zpow_cases_of_pow_three hc3 k with hk | hk | hk <;> rw [hk] at hke
  ·
    exfalso
    rw [one_mul] at hke
    have h1 : c ∈ R ⊓ L := by
      have hmN : m⁻¹ ∈ Subgroup.normalizer ((R ⊓ L : Subgroup G) : Set G) :=
        normalizer_D_le h45 h97 h (Subgroup.inv_mem _ hm)
      have h2 := (Subgroup.mem_normalizer_iff.mp hmN _).mp (hke ▸ he)
      simpa [mul_assoc] using h2
    exact h.c_not_mem_L h1.2
  ·
    have h1 : m * c * m⁻¹ * c⁻¹ ∈ R ⊓ L := by
      rw [hke, ← hce, mul_inv_cancel_right]
      exact he
    have h2 := hbad m hm hmE h1
    calc (m * m) * c * (m * m)⁻¹ = m * (m * c * m⁻¹) * m⁻¹ := by group
      _ = c := by rw [h2, h2]
  ·
    calc (m * m) * c * (m * m)⁻¹ = m * (m * c * m⁻¹) * m⁻¹ := by group
      _ = m * (c ^ 2 * e) * m⁻¹ := by rw [hke]
      _ = (m * c * m⁻¹) ^ 2 * (m * e * m⁻¹) := by simp only [sq]; group
      _ = (c ^ 2 * e) ^ 2 * e := by rw [hke, hmE e he]
      _ = c := by
          have hce' : Commute (c ^ 2) e := ((show Commute e c from hce).symm.pow_left 2)
          rw [hce'.mul_pow, mul_assoc, ← pow_succ, ← pow_mul,
            show 2 * 2 = 3 + 1 by norm_num, pow_succ, hc3, one_mul,
            show 2 + 1 = 3 by norm_num, he3, mul_one]

theorem false_of_bad (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h98 : Sec9.Item98)
    (h : Sec10Std G A c L a R)
    (hbad : ∀ m ∈ Subgroup.normalizer ((sec10D c R L : Subgroup G) : Set G),
      (∀ e' ∈ R ⊓ L, m * e' * m⁻¹ = e') → m * c * m⁻¹ * c⁻¹ ∈ R ⊓ L → m * c * m⁻¹ = c) :
    False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 13) := ⟨by norm_num⟩
  set D := sec10D c R L with hD
  set E := R ⊓ L with hE
  set M := Subgroup.normalizer ((D : Subgroup G) : Set G) with hM
  have hME : M ≤ Subgroup.normalizer (E : Set G) := normalizer_D_le h45 h97 h
  have hc1 : c ≠ 1 := h.ne_one
  obtain ⟨x, hxL, hxN, hxo, hxfix⟩ := exists_orderOf_thirteen h
  have hxc : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp (h.le_centralizer_c hxL)
  have hxM : x ∈ M := mem_normalizer_D_of h hxc hxN
  obtain ⟨g, hgM, hgne⟩ := exists_mem_normalizer_D h45 h97 h98 h
  have hac : a * c = c * a := h.comm h.a_mem h.mem_A
  have haM : a ∈ M := mem_normalizer_D_of h hac h.a_mem_normalizer_inf
  obtain ⟨e₁, he₁, hae₁⟩ := exists_not_commute_a h97 h
  set Mc : Subgroup M := (Subgroup.centralizer ({c} : Set G)).subgroupOf M with hMc
  set CD : Subgroup M := (Subgroup.centralizer (D : Set G)).subgroupOf M with hCD
  set ρ : M →* MulAut E := E.normalizerMonoidHom.comp (Subgroup.inclusion hME) with hρ
  have hρapp : ∀ (m : M) (e : E), ((ρ m e : E) : G) = (m : G) * e * (m : G)⁻¹ := fun _ _ => rfl
  set CE : Subgroup M := ρ.ker with hCE
  have hmemCE : ∀ m : M, m ∈ CE ↔ ∀ e ∈ E, (m : G) * e * (m : G)⁻¹ = e := by
    intro m
    rw [hCE, MonoidHom.mem_ker]
    constructor
    · intro h1 e he
      have := congrArg (fun σ : MulAut E => ((σ ⟨e, he⟩ : E) : G)) h1
      simpa [hρapp] using this
    · intro h1
      ext ⟨e, he⟩
      rw [hρapp]
      exact h1 e he
  have hmemCD : ∀ m : M, m ∈ CD ↔ (m : G) ∈ Subgroup.centralizer (D : Set G) := fun m =>
    Subgroup.mem_subgroupOf
  have hmemMc : ∀ m : M, m ∈ Mc ↔ (m : G) * c = c * m := fun m => by
    rw [hMc, Subgroup.mem_subgroupOf, Subgroup.mem_centralizer_singleton_iff]
  have hCDc : ∀ m : M, m ∈ CD → (m : G) * c = c * m := fun m hm =>
    ((Subgroup.mem_centralizer_iff.mp ((hmemCD m).mp hm)) c h.c_mem_D).symm
  have hCDE : ∀ m : M, m ∈ CD → ∀ e ∈ E, (m : G) * e * (m : G)⁻¹ = e := fun m hm e he => by
    have h1 := (Subgroup.mem_centralizer_iff.mp ((hmemCD m).mp hm)) e (h.inf_le_D he)
    rw [← h1, mul_inv_cancel_right]
  have hCDMc : CD ≤ Mc := fun m hm => (hmemMc m).mpr (hCDc m hm)
  have hCDCE : CD ≤ CE := fun m hm => (hmemCE m).mpr (hCDE m hm)
  have hCDn : CD.Normal := by
    constructor
    intro n hn m
    rw [hmemCD, Subgroup.mem_centralizer_iff]
    intro u hu
    have hu' : (m : G)⁻¹ * u * m ∈ D := by
      have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ m.2) u).mp hu
      simpa using this
    have h1 := (Subgroup.mem_centralizer_iff.mp ((hmemCD n).mp hn)) _ hu'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc u * ((m : G) * n * (m : G)⁻¹) = (m : G) * (((m : G)⁻¹ * u * m) * n) * (m : G)⁻¹ := by
          group
      _ = (m : G) * (n * ((m : G)⁻¹ * u * m)) * (m : G)⁻¹ := by rw [h1]
      _ = (m : G) * n * (m : G)⁻¹ * u := by group
  let F : M ⧸ Mc → G := Quotient.lift (fun m : M => (m : G) * c * (m : G)⁻¹) (by
    intro m₁ m₂ hm
    have hm' : m₁⁻¹ * m₂ ∈ Mc := QuotientGroup.leftRel_apply.mp hm
    rw [hmemMc] at hm'
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at hm'
    calc (m₁ : G) * c * (m₁ : G)⁻¹ =
          (m₁ : G) * (((m₁ : G)⁻¹ * m₂) * c) * ((m₁ : G)⁻¹ * m₂)⁻¹ * (m₁ : G)⁻¹ := by
            rw [hm']; group
      _ = (m₂ : G) * c * (m₂ : G)⁻¹ := by group)
  have hFmk : ∀ m : M, F (m : M ⧸ Mc) = (m : G) * c * (m : G)⁻¹ := fun _ => rfl
  have hFinj : Function.Injective F := by
    intro q₁ q₂ hq
    induction q₁ using QuotientGroup.induction_on with | H m₁ => ?_
    induction q₂ using QuotientGroup.induction_on with | H m₂ => ?_
    rw [hFmk, hFmk] at hq
    rw [QuotientGroup.eq, hmemMc]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    calc (m₁ : G)⁻¹ * m₂ * c = (m₁ : G)⁻¹ * ((m₂ : G) * c * (m₂ : G)⁻¹) * m₂ := by group
      _ = (m₁ : G)⁻¹ * ((m₁ : G) * c * (m₁ : G)⁻¹) * m₂ := by rw [hq]
      _ = c * ((m₁ : G)⁻¹ * m₂) := by group
  have hFD : ∀ q : M ⧸ Mc, F q ∈ D := by
    intro q
    induction q using QuotientGroup.induction_on with | H m => ?_
    rw [hFmk]
    exact conj_c_mem_D h m.2
  have hn81 : Nat.card (M ⧸ Mc) ≤ 81 := by
    have h1 := Nat.card_le_card_of_injective (fun q : M ⧸ Mc => (⟨F q, hFD q⟩ : D))
      (fun q₁ q₂ hq => hFinj (congrArg Subtype.val hq))
    rwa [h.card_D] at h1
  set x' : M := ⟨x, hxM⟩ with hx'
  set K : Subgroup M := Subgroup.zpowers x' with hK
  have hK13 : IsPGroup 13 K := IsPGroup.of_card (n := 1) (by
    rw [hK, Nat.card_zpowers, pow_one, hx', Subgroup.orderOf_mk, hxo])
  have hFsmul : ∀ q : M ⧸ Mc, F (x' • q) = x * F q * x⁻¹ := by
    intro q
    induction q using QuotientGroup.induction_on with | H m => ?_
    rw [MulAction.Quotient.smul_mk, smul_eq_mul, hFmk, hFmk, Subgroup.coe_mul, hx']
    group
  have hfixK : ∀ q : M ⧸ Mc, q ∈ MulAction.fixedPoints K (M ⧸ Mc) ↔ x * F q * x⁻¹ = F q := by
    intro q
    constructor
    · intro hq
      have h1 : (⟨x', Subgroup.mem_zpowers x'⟩ : K) • q = q := hq _
      rw [← hFsmul]
      exact congrArg F h1
    · intro hq k
      have h1 : x' ∈ MulAction.stabilizer M q := hFinj (by rw [hFsmul, hq])
      have h2 : (k : M) ∈ MulAction.stabilizer M q :=
        (Subgroup.zpowers_le.mpr h1) (show (k : M) ∈ Subgroup.zpowers x' from k.2)
      exact h2
  have hfix_mem : ∀ q ∈ MulAction.fixedPoints K (M ⧸ Mc),
      F q ∈ ({c, c ^ 2} : Set G) := by
    intro q hq
    have h1 := mem_zpowers_c_of_fix h hxfix hxc (hFD q) ((hfixK q).mp hq)
    have hF1 : F q ≠ 1 := by
      induction q using QuotientGroup.induction_on with | H m => ?_
      rw [hFmk]
      intro h2
      apply hc1
      calc c = (m : G)⁻¹ * ((m : G) * c * (m : G)⁻¹) * m := by group
        _ = 1 := by rw [h2]; group
    obtain ⟨i, hi⟩ := Subgroup.mem_zpowers_iff.mp h1
    rcases zpow_cases_of_pow_three (h.pow_three h.mem_A) i with h2 | h2 | h2 <;> rw [h2] at hi
    · exact absurd hi.symm hF1
    · exact Or.inl hi.symm
    · exact Or.inr hi.symm
  have hfix1 : ((1 : M) : M ⧸ Mc) ∈ MulAction.fixedPoints K (M ⧸ Mc) := by
    rw [hfixK, hFmk]
    simp only [OneMemClass.coe_one, one_mul, inv_one, mul_one]
    rw [hxc, mul_inv_cancel_right]
  have hfixg : ((⟨g, hgM⟩ : M) : M ⧸ Mc) ∉ MulAction.fixedPoints K (M ⧸ Mc) := by
    intro hq
    have h1 := hfix_mem _ hq
    rw [hFmk] at h1
    apply hgne
    have h2 : g * c * g⁻¹ ∈ Subgroup.zpowers c := by
      rcases h1 with h1 | h1
      · rw [h1]
        exact Subgroup.mem_zpowers c
      · rw [h1]
        exact Subgroup.pow_mem _ (Subgroup.mem_zpowers c) 2
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h2) ?_
    rw [Nat.card_zpowers, Nat.card_zpowers]
    have h3 := orderOf_injective (MulAut.conj g).toMonoidHom (MulAut.conj g).injective c
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h3
    rw [h3]
  have hfix2 : Nat.card (MulAction.fixedPoints K (M ⧸ Mc)) ≤ 2 := by
    have h1 := Nat.card_le_card_of_injective
      (fun q : MulAction.fixedPoints K (M ⧸ Mc) => (⟨F q, hfix_mem q q.2⟩ : ({c, c ^ 2} : Set G)))
      (fun q₁ q₂ hq => Subtype.ext (hFinj (congrArg Subtype.val hq)))
    refine h1.trans ?_
    rw [Nat.card_coe_set_eq]
    exact (Set.ncard_insert_le _ _).trans (by rw [Set.ncard_singleton])
  have hfixpos : 1 ≤ Nat.card (MulAction.fixedPoints K (M ⧸ Mc)) :=
    Nat.one_le_iff_ne_zero.mpr (Nat.card_ne_zero.mpr ⟨⟨_, hfix1⟩, inferInstance⟩)
  have hfixlt : Nat.card (MulAction.fixedPoints K (M ⧸ Mc)) < Nat.card (M ⧸ Mc) := by
    rw [Nat.card_coe_set_eq, ← Set.ncard_univ]
    exact Set.ncard_lt_ncard (Set.ssubset_univ_iff.mpr (fun h1 => hfixg (h1 ▸ Set.mem_univ _)))
  have hmod := hK13.card_modEq_card_fixedPoints (M ⧸ Mc)
  have hn13 : Nat.card (M ⧸ Mc) % 13 = Nat.card (MulAction.fixedPoints K (M ⧸ Mc)) := by
    rw [hmod]
    exact Nat.mod_eq_of_lt (by omega)
  have hiE : CE.index ∣ 11232 := by
    rw [hCE, Subgroup.index_ker, ← card_mulAut_inf h]
    exact Subgroup.card_subgroup_dvd_card _
  have : (CD.subgroupOf CE).Normal := Subgroup.Normal.subgroupOf hCDn CE
  have hr₂ : ∃ k : ℕ, CD.relIndex CE = 2 ^ k := by
    have h2grp : IsPGroup 2 (CE ⧸ CD.subgroupOf CE) := by
      intro q
      refine ⟨1, ?_⟩
      induction q using QuotientGroup.induction_on with | H m => ?_
      rw [pow_one, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf,
        hmemCD]
      have hmM : ((m : M) : G) ∈ M := (m : M).2
      have hmE := (hmemCE m).mp m.2
      have hsq := sq_conj_c_eq h45 h97 h hbad hmM hmE
      apply mem_centralizer_D_of h
      · simp only [sq, Subgroup.coe_mul]
        calc ((m : M) : G) * m * c = ((m : M) : G) * m * c * (((m : M) : G) * m)⁻¹ *
              (((m : M) : G) * m) := by group
          _ = c * (((m : M) : G) * m) := by rw [hsq]
      · intro e he
        simp only [sq, Subgroup.coe_mul]
        calc ((m : M) : G) * m * e * (((m : M) : G) * m)⁻¹ =
            ((m : M) : G) * (((m : M) : G) * e * ((m : M) : G)⁻¹) * ((m : M) : G)⁻¹ := by group
          _ = e := by rw [hmE e he, hmE e he]
    obtain ⟨k, hk⟩ := h2grp.exists_card_eq
    exact ⟨k, by rw [Subgroup.relIndex, Subgroup.index_eq_card, hk]⟩
  obtain ⟨k, hk⟩ := hr₂
  have : (CD.subgroupOf Mc).Normal := Subgroup.Normal.subgroupOf hCDn Mc
  have hr₁ : 3 ∣ CD.relIndex Mc := by
    set a' : M := ⟨a, haM⟩ with ha'
    have ha'Mc : a' ∈ Mc := (hmemMc a').mpr hac
    set q : Mc ⧸ CD.subgroupOf Mc := ((⟨a', ha'Mc⟩ : Mc) : Mc ⧸ CD.subgroupOf Mc) with hq
    have hq3 : orderOf q = 3 := by
      apply orderOf_eq_prime
      · rw [hq, ← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        have h1 : ((⟨a', ha'Mc⟩ : Mc) ^ 3 : Mc) = 1 := by
          apply Subtype.ext
          apply Subtype.ext
          simpa [ha'] using h.pow_three h.a_mem
        rw [h1]
        exact CD.one_mem
      · rw [hq, Ne, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
        intro h1
        exact hae₁ (hCDE a' h1 e₁ he₁)
    rw [Subgroup.relIndex, Subgroup.index_eq_card, ← hq3]
    exact orderOf_dvd_natCard q
  have heq : CD.relIndex Mc * Mc.index = CD.relIndex CE * CE.index := by
    rw [Subgroup.relIndex_mul_index hCDMc, Subgroup.relIndex_mul_index hCDCE]
  rw [← Subgroup.index_eq_card] at hn81 hn13 hfixlt
  exact false_of_indices (n := Mc.index) (by omega) hn81 (by omega) hr₁ hk hiE heq

end Std

end Item107Proof

end CFSG.RankThree.PartTwo.Sec10

module

public import CFSG.Timmesfeld.Bridge.RootStructR2OneTwoH
public import CFSG.Timmesfeld.Bridge.RootStructR2OneTwoDim
public import CFSG.Timmesfeld.Bridge.RootStructR2ManyIndex
public import CFSG.Timmesfeld.Bridge.RootStructWTIL2
public import CFSG.Timmesfeld.Bridge.RootSetsSyl
public import CFSG.Timmesfeld.Bridge.RootStructR2OneTwoW

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld
open scoped Matrix commutatorElement

namespace RootOne

variable {G : Type} [Group G] {D : Set G}

namespace ModConf

variable {a d x y : G} {C : LineConf D a d x y} {K : Type*} [Field K]
  {φ : ↥(rootGroup D x ⊔ rootGroup D y) ≃* Matrix.SpecialLinearGroup (Fin 2) K}
  {θ₀ θ₁ : (Fin 2 → K) → G} (M : ModConf C φ θ₀ θ₁)
include M

theorem false_of_trivial [Finite K] [CharP K 2] (hK2 : 2 < Nat.card K)
    (CT : ThinGateCounter G D) {h : G} (hp : (orderOf h).Prime) (hp2 : orderOf h ≠ 2)
    (hΩ : ¬ orderOf h ∣ (oneOmega D a).ncard)
    (hhX : ∀ g ∈ rootGroup D x ⊔ rootGroup D y, Commute h g) {lam : K} (hlam : lam ≠ 0)
    (hscal : ∀ v, h * θ₀ v * h⁻¹ = θ₀ (lam • v))
    (htriv : ∀ m ∈ lineN₀ D a d, h * m * h⁻¹ * m⁻¹ ∈ rootGroup D a ⊔ rootGroup D d) : False := by
  classical
  have := C.finite
  have hscal' : ∀ v, h⁻¹ * θ₀ v * h = θ₀ (lam⁻¹ • v) := by
    intro v
    have := hscal (lam⁻¹ • v)
    rw [smul_smul, mul_inv_cancel₀ hlam, one_smul] at this
    rw [← this]
    group
  have hhT : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, h * t * h⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
    intro t ht
    obtain ⟨v, rfl⟩ := (M.range₀ t).1 ht
    rw [hscal]
    exact M.θ₀_mem _
  have hhT' : ∀ t ∈ rootGroup D a ⊔ rootGroup D d,
      h⁻¹ * t * h ∈ rootGroup D a ⊔ rootGroup D d := by
    intro t ht
    obtain ⟨v, rfl⟩ := (M.range₀ t).1 ht
    rw [hscal']
    exact M.θ₀_mem _
  have hhN : ∀ n ∈ lineN D a d, h * n * h⁻¹ ∈ lineN D a d := fun n hn =>
    M.conj_mem_lineN hhT hhT' hn
  have hhN₀ : ∀ m ∈ lineN₀ D a d, h * m * h⁻¹ ∈ lineN₀ D a d := fun m hm =>
    C.conj_mem_lineN₀_of_commute hhX hhT hm
  have hhN₀' : ∀ m ∈ lineN₀ D a d, h⁻¹ * m * h ∈ lineN₀ D a d := by
    intro m hm
    have := C.conj_mem_lineN₀_of_commute (g := h⁻¹) (fun u hu => (hhX u hu).inv_left)
      (fun t ht => by rw [inv_inv]; exact hhT' t ht) hm
    rwa [inv_inv] at this
  obtain ⟨μ, hμ⟩ := natQuot_exists_smul M.nat₁ M.normal M.conj_N₀ hhN hhN₀ hhX
  have hθd : θ₁ ![0, 1] ∉ lineN₀ D a d := fun h0 => by
    have := congrFun (M.nat₁.eq_zero_of_mem _ h0) 1
    simp at this
  have hμ0 : μ ≠ 0 := by
    rintro rfl
    apply hθd
    have h1 := hμ ![0, 1]
    rw [zero_smul] at h1
    have h0 : θ₁ 0 ∈ lineN₀ D a d := by
      have := M.nat₁.map_add 0 0
      rw [add_zero, show (θ₁ 0 * θ₁ 0)⁻¹ * θ₁ 0 = (θ₁ 0)⁻¹ by group] at this
      exact inv_mem_iff.1 this
    have h2 : h * θ₁ ![0, 1] * h⁻¹ ∈ lineN₀ D a d := by
      have := Subgroup.mul_mem _ h0 h1
      rwa [mul_inv_cancel_left] at this
    have := hhN₀' _ h2
    rwa [show h⁻¹ * (h * θ₁ ![0, 1] * h⁻¹) * h = θ₁ ![0, 1] by group] at this
  by_cases hμ1 : μ = 1
  · subst hμ1
    by_cases hl : lam = 1
    ·
      have hhT1 : ∀ t ∈ rootGroup D a ⊔ rootGroup D d, Commute h t := by
        intro t ht
        obtain ⟨v, rfl⟩ := (M.range₀ t).1 ht
        have := hscal v
        rw [hl, one_smul] at this
        show h * θ₀ v = θ₀ v * h
        calc h * θ₀ v = h * θ₀ v * h⁻¹ * h := by group
          _ = θ₀ v * h := by rw [this]
      have h1 := M.eq_one_of_trivial CT hp hp2 hΩ hhX hhT1 hhN₀ (fun v => by
        simpa using hμ v)
      rw [h1, orderOf_one] at hp
      exact Nat.not_prime_one hp
    ·
      have hcoset : (θ₁ ![0, 1])⁻¹ * (h * θ₁ ![0, 1] * h⁻¹) ∈ lineN₀ D a d := by
        simpa using hμ ![0, 1]
      obtain ⟨c, hc, hhc⟩ := exists_fixed_mem_coset (isPGroup_lineN₀ a d) hp hp2 hhN₀ hcoset
      have hcN : c ∈ lineN D a d := by
        have := Subgroup.mul_mem _ (M.nat₁.mem ![0, 1]) (lineN₀_le_lineN D a d hc)
        rwa [mul_inv_cancel_left] at this
      have hcomm : Commute h c := by
        show h * c = c * h
        calc h * c = h * c * h⁻¹ * h := by group
          _ = c * h := by rw [hhc]
      have hc0 := M.mem_lineN₀_of_scalar hhX hl hscal hcN hcomm
      apply hθd
      have := Subgroup.mul_mem _ hc0 (Subgroup.inv_mem _ hc)
      rwa [show c * ((θ₁ ![0, 1])⁻¹ * c)⁻¹ = θ₁ ![0, 1] by group] at this
  · exact M.false_of_trivial_mod_T hK2 hhX hhN hhN₀ htriv hμ0 hμ1 hμ

end ModConf

theorem false_of_eq_two {q : ℕ} (C : ThinGateCounter G D) (K : ThinGateCount G D q 1 2) :
    False := by
  classical
  obtain ⟨a, d, x, y, L⟩ := exists_lineConf C
  have := L.finite
  have hD := L.root
  have hq : Nat.card (rootGroup D a) = q := K.card_rootGroup a L.ha
  have hq4 : 4 ≤ q := hq ▸ four_le_card_rootGroup L.isClass hD L.setting.closure C.nontrivial L.ha
  have hT := L.mem_rootLines_a
  have h3 : 3 ≤ (rootLines D a).ncard := by rw [K.ncard_rootLines a L.ha, pow_one]; omega
  have hsub : gatedPoints D a (rootGroup D a ⊔ rootGroup D d) ⊆ oneOmega D a := fun B hB => hB.1
  have hO := K.ncard_oneOmega a L.ha
  have hX1 : 1 ≤ q ^ 5 := Nat.one_le_pow _ _ (by omega)
  have hY : 4 * q ^ 5 ≤ q * q ^ 5 := Nat.mul_le_mul_right _ hq4
  rw [pow_one, show 2 * 1 + 3 = 5 by norm_num] at hO
  have hΩ : (oneOmega D a \ gatedPoints D a (rootGroup D a ⊔ rootGroup D d)).ncard =
      (oneOmega D a).ncard - q ^ 5 := by
    rw [Set.ncard_sdiff hsub, K.ncard_gatedPoints a L.ha _ hT]
  have hdvd := card_dvd_ncard_of_centralizes C L.ha L.hd L.had L.hadD L.hdT (lineN D a d)
    (fun g hg t ht => L.commute_of_mem_lineN hg ht)
  rw [hΩ] at hdvd
  have hNlt : Nat.card (lineN D a d) < Nat.card (rootGroup D a) ^ 6 := by
    rw [hq]
    have hpos : 0 < (oneOmega D a).ncard - q ^ 5 := by
      have : (q + 1) * q ^ 5 = q * q ^ 5 + q ^ 5 := by ring
      omega
    have hle := Nat.le_of_dvd hpos hdvd
    have : q ^ 6 = q * q ^ 5 := by ring
    have : (q + 1) * q ^ 5 = q * q ^ 5 + q ^ 5 := by ring
    omega
  obtain ⟨e, he0, he, φ, θ₀, θ₁, M⟩ := L.exists_modConf h3 hNlt
  have hKq : Nat.card (GaloisField 2 e) = q := M.card_K.trans hq
  have hK2 : 2 < Nat.card (GaloisField 2 e) := by omega
  have hTx : rootGroup D a ⊔ rootGroup D d ≠ rootGroup D a ⊔ rootGroup D x := fun h =>
    L.hxT (h ▸ right_mem_line L.hx)
  obtain ⟨h₀, hh₀R, hord, hh₀T, -, -⟩ := rootLinesTorusStep G D L.setting a L.ha d L.hd L.had
    L.hadD L.hdT h3 _ hT _ L.mem_rootLines_x hTx
  rw [K.ncard_rootLines a L.ha, pow_one] at hord
  have hord' : orderOf h₀ = q - 1 := by omega
  have hqeven : Even q := by
    rw [← hq, he]
    exact (Nat.even_pow.2 ⟨even_two, he0⟩)
  have hodd : Odd (q - 1) := by
    obtain ⟨j, hj⟩ := hqeven
    exact ⟨j - 1, by omega⟩
  have h₀a : ∀ t ∈ rootGroup D a, Commute h₀ t := fun t ht =>
    L.setting.commute_of_mem_lineGroup L.ha L.hd L.had L.hadD L.hdT hh₀R ht
  obtain ⟨h₁, hh₁, hh₁X, lam, hlam, hscal⟩ := M.exists_scalar_torus (hord' ▸ hodd) h₀a hh₀T
  rw [hord'] at hh₁
  have hpowscal : ∀ (k : ℕ) v, h₁ ^ k * θ₀ v * (h₁ ^ k)⁻¹ = θ₀ (lam ^ k • v) := by
    intro k
    induction k with
    | zero => intro v; simp
    | succ k ih =>
      intro v
      rw [pow_succ, mul_inv_rev, show h₁ ^ k * h₁ * θ₀ v * (h₁⁻¹ * (h₁ ^ k)⁻¹) =
        h₁ ^ k * (h₁ * θ₀ v * h₁⁻¹) * (h₁ ^ k)⁻¹ by group, hscal, ih, smul_smul, pow_succ]
  have hΩdiv : ∀ p : ℕ, p.Prime → p ∣ q - 1 → ¬ p ∣ (oneOmega D a).ncard := by
    intro p hp hpq hpO
    have h1 : p ∣ (q + 1) * q ^ 5 := by rw [← hO]; exact hpO.mul_right 2
    have hp2 : p ≠ 2 := fun h => by
      rw [h] at hpq
      exact Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 hpq)
    rcases (Nat.Prime.dvd_mul hp).1 h1 with h | h
    · have h2 : p ∣ (q + 1) - (q - 1) := Nat.dvd_sub h hpq
      rw [show q + 1 - (q - 1) = 2 by omega] at h2
      exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h2)
    · have h2 : p ∣ q := hp.dvd_of_dvd_pow h
      have h3 : p ∣ q - (q - 1) := Nat.dvd_sub h2 hpq
      rw [show q - (q - 1) = 1 by omega] at h3
      exact hp.one_lt.ne' (Nat.dvd_one.1 h3)
  have hpowX : ∀ (k : ℕ), ∀ g ∈ rootGroup D x ⊔ rootGroup D y, Commute (h₁ ^ k) g :=
    fun k g hg => (hh₁X g hg).pow_left k
  have hpowT : ∀ (k : ℕ), ∀ t ∈ rootGroup D a ⊔ rootGroup D d,
      h₁ ^ k * t * (h₁ ^ k)⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
    intro k t ht
    obtain ⟨v, rfl⟩ := (M.range₀ t).1 ht
    rw [hpowscal]
    exact M.θ₀_mem _
  have hpowN₀ : ∀ (k : ℕ), ∀ m ∈ lineN₀ D a d, h₁ ^ k * m * (h₁ ^ k)⁻¹ ∈ lineN₀ D a d :=
    fun k m hm => L.conj_mem_lineN₀_of_commute (hpowX k) (hpowT k) hm
  have htrivpow : ∀ (k : ℕ), (∀ m ∈ lineN₀ D a d,
      h₁ ^ k * m * (h₁ ^ k)⁻¹ * m⁻¹ ∈ rootGroup D a ⊔ rootGroup D d) → ∀ j : ℕ,
      ∀ m ∈ lineN₀ D a d, (h₁ ^ k) ^ j * m * ((h₁ ^ k) ^ j)⁻¹ * m⁻¹ ∈
        rootGroup D a ⊔ rootGroup D d := by
    intro k hk j
    induction j with
    | zero => intro m _; simp
    | succ j ih =>
      intro m hm
      have e : (h₁ ^ k) ^ (j + 1) * m * ((h₁ ^ k) ^ (j + 1))⁻¹ * m⁻¹ =
          (h₁ ^ k) ^ j * (h₁ ^ k * m * (h₁ ^ k)⁻¹ * m⁻¹) * ((h₁ ^ k) ^ j)⁻¹ *
            ((h₁ ^ k) ^ j * m * ((h₁ ^ k) ^ j)⁻¹ * m⁻¹) := by group
      rw [e]
      refine Subgroup.mul_mem _ ?_ (ih m hm)
      rw [← pow_mul]
      exact hpowT _ _ (hk m hm)
  have hfaith : ∀ k : ℕ, (∀ m ∈ lineN₀ D a d,
      h₁ ^ k * m * (h₁ ^ k)⁻¹ * m⁻¹ ∈ rootGroup D a ⊔ rootGroup D d) → h₁ ^ k = 1 := by
    intro k hk
    by_contra hne
    have hgpos : 0 < orderOf (h₁ ^ k) := orderOf_pos _
    have hg1 : orderOf (h₁ ^ k) ≠ 1 := fun h => hne (orderOf_eq_one_iff.1 h)
    obtain ⟨p, hp, hpd⟩ := Nat.exists_prime_and_dvd hg1
    have hgp : orderOf ((h₁ ^ k) ^ (orderOf (h₁ ^ k) / p)) = p :=
      orderOf_pow_orderOf_div hgpos.ne' hpd
    have hgj : (h₁ ^ k) ^ (orderOf (h₁ ^ k) / p) = h₁ ^ (k * (orderOf (h₁ ^ k) / p)) := by
      rw [← pow_mul]
    have hpq : p ∣ q - 1 := by
      rw [← hgp, hgj, ← hh₁]
      exact orderOf_pow_dvd _
    have hp2 : p ≠ 2 := fun h => by
      rw [h] at hpq
      exact Nat.not_even_iff_odd.2 hodd (even_iff_two_dvd.2 hpq)
    refine M.false_of_trivial hK2 C (h := (h₁ ^ k) ^ (orderOf (h₁ ^ k) / p)) (by rw [hgp]; exact hp)
      (by rw [hgp]; exact hp2) (by rw [hgp]; exact hΩdiv p hp hpq)
      (by rw [hgj]; exact hpowX _) (pow_ne_zero (k * (orderOf (h₁ ^ k) / p)) hlam)
      (by rw [hgj]; exact hpowscal _) (htrivpow k hk _)
  let instN₀ : CommGroup ↥(lineN₀ D a d) :=
    { (inferInstance : Group ↥(lineN₀ D a d)) with
      mul_comm := fun m m' => Subtype.ext (L.commute_of_mem_lineN₀ m.2 m'.2).eq }
  let T' : Subgroup ↥(lineN₀ D a d) := (rootGroup D a ⊔ rootGroup D d).subgroupOf (lineN₀ D a d)
  have hh₁N₀ : ∀ m ∈ lineN₀ D a d, h₁ * m * h₁⁻¹ ∈ lineN₀ D a d := fun m hm => by
    simpa using hpowN₀ 1 m hm
  let c₁ : ↥(lineN₀ D a d) →* ↥(lineN₀ D a d) :=
    { toFun := fun m => ⟨h₁ * m * h₁⁻¹, hh₁N₀ m m.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun m m' => Subtype.ext (by simp only [Subgroup.coe_mul]; group) }
  have hc₁T : T' ≤ T'.comap c₁ := by
    intro m hm
    rw [Subgroup.mem_comap, Subgroup.mem_subgroupOf]
    rw [Subgroup.mem_subgroupOf] at hm
    change h₁ * (m : G) * h₁⁻¹ ∈ _
    simpa using hpowT 1 _ hm
  let σ : AddMonoid.End (Additive (↥(lineN₀ D a d) ⧸ T')) :=
    (QuotientGroup.map T' T' c₁ hc₁T).toAdditive
  have hσpow : ∀ (k : ℕ) (m : ↥(lineN₀ D a d)),
      (σ ^ k) (Additive.ofMul (QuotientGroup.mk m)) =
        Additive.ofMul (QuotientGroup.mk ⟨h₁ ^ k * m * (h₁ ^ k)⁻¹, hpowN₀ k m m.2⟩) := by
    intro k
    induction k with
    | zero => intro m; simp
    | succ k ih =>
      intro m
      rw [pow_succ']
      change σ ((σ ^ k) (Additive.ofMul (QuotientGroup.mk m))) = _
      rw [ih]
      change Additive.ofMul (QuotientGroup.mk (c₁ _)) = _
      congr 2
      apply Subtype.ext
      simp only [c₁, MonoidHom.coe_mk, OneHom.coe_mk]
      group
  have hσone : ∀ k : ℕ, σ ^ k = 1 ↔ ∀ m ∈ lineN₀ D a d,
      h₁ ^ k * m * (h₁ ^ k)⁻¹ * m⁻¹ ∈ rootGroup D a ⊔ rootGroup D d := by
    intro k
    constructor
    · intro hk m hm
      have h1 := hσpow k ⟨m, hm⟩
      rw [hk] at h1
      change Additive.ofMul (QuotientGroup.mk ⟨m, hm⟩ : ↥(lineN₀ D a d) ⧸ T') = _ at h1
      have h2 := QuotientGroup.eq.1 (Additive.ofMul.injective h1)
      rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h2
      change m⁻¹ * (h₁ ^ k * m * (h₁ ^ k)⁻¹) ∈ _ at h2
      rw [(L.commute_of_mem_lineN₀ (Subgroup.inv_mem _ hm) (hpowN₀ k m hm)).eq] at h2
      exact h2
    · intro hk
      ext z
      induction z using QuotientGroup.induction_on with
      | H m =>
        change (σ ^ k) (Additive.ofMul (QuotientGroup.mk m)) = Additive.ofMul (QuotientGroup.mk m)
        rw [hσpow]
        congr 1
        refine QuotientGroup.eq.2 ?_
        rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv]
        change (h₁ ^ k * (m : G) * (h₁ ^ k)⁻¹)⁻¹ * m ∈ _
        have h1 := Subgroup.inv_mem _ (hk m m.2)
        rw [show (h₁ ^ k * (m : G) * (h₁ ^ k)⁻¹ * (m : G)⁻¹)⁻¹ =
          (m : G) * (h₁ ^ k * (m : G) * (h₁ ^ k)⁻¹)⁻¹ by group] at h1
        rwa [(L.commute_of_mem_lineN₀ m.2 (Subgroup.inv_mem _ (hpowN₀ k m m.2))).eq] at h1
  have hσord : orderOf σ = q - 1 := by
    rw [← hh₁, orderOf_eq_orderOf_iff]
    intro k
    rw [hσone]
    constructor
    · exact hfaith k
    · intro hk m _
      rw [hk, one_mul, inv_one, mul_one, mul_inv_cancel]
      exact Subgroup.one_mem _
  have h2 : ∀ z : Additive (↥(lineN₀ D a d) ⧸ T'), z + z = 0 := by
    intro z
    induction z using QuotientGroup.induction_on with
    | H m =>
      change Additive.ofMul (QuotientGroup.mk (m * m) : ↥(lineN₀ D a d) ⧸ T') = 0
      change (QuotientGroup.mk (m * m) : ↥(lineN₀ D a d) ⧸ T') = 1
      rw [QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf, Subgroup.coe_mul]
      exact Subgroup.mem_sup_left (mul_self_mem_rootGroup_of_mem_nCore L.setting.hyp
        L.setting.closure L.ha (Subgroup.mem_inf.1 m.2).1)
  have hnt : Nontrivial (Additive (↥(lineN₀ D a d) ⧸ T')) := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : σ = 1 := by
      ext z
      exact hnt.elim _ _
    rw [this, orderOf_one] at hσord
    omega
  have hlt := orderOf_lt_card h2 σ
  rw [hσord] at hlt
  have hcardQ : Nat.card ↥(lineN₀ D a d) =
      Nat.card (Additive (↥(lineN₀ D a d) ⧸ T')) * q ^ 2 := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup T']
    congr 1
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe L.T_le_lineN₀).toEquiv, L.card_T, hq]
  have hN₀ : q ^ 3 ≤ Nat.card ↥(lineN₀ D a d) := by
    rw [hcardQ, pow_succ' q 2]
    exact Nat.mul_le_mul_right _ (by omega)
  have hM := RootMany.le_card_nCore C K L.ha L.hd L.had L.hadD L.hdT
  refine RootMany.false_of_card_nCore C K le_rfl L.ha L.hd L.had L.hadD L.hdT ?_
  calc q ^ (1 + 4) = q ^ (1 + 1) * q ^ 3 := by ring
    _ ≤ q ^ (1 + 1) * Nat.card ↥(nCore D a ⊓ nCore D d) := Nat.mul_le_mul_left _ hN₀
    _ ≤ _ := hM

end RootOne

end CFSG.Timmesfeld.Bridge

module

public import CFSG.Quasithin.Background.SmithB45TorDisp
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneLines
public import Mathlib.Algebra.Module.Torsion.Prod
public import Mathlib.RingTheory.Etale.Weakly
public import Mathlib.RingTheory.TotallySplit

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.B45Tor

open scoped commutatorElement
open CFSG.QuasithinUnique.Setup.Family

section Action

variable {G : Type*} [Group G] (R : Subgroup G)

@[expose] def InvOn (c : G) : Prop := ∀ r ∈ R, c * r * c⁻¹ = r⁻¹

@[expose] def AgreeOn (a b : G) : Prop := ∀ r ∈ R, a * r * a⁻¹ = b * r * b⁻¹

abbrev conjSub (g : G) (K : Subgroup G) : Subgroup G := K.map (MulAut.conj g).toMonoidHom

variable {R}

theorem conj_mem_of_mem_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (R : Set G)) {r : G}
    (hr : r ∈ R) : g * r * g⁻¹ ∈ R :=
  (Subgroup.mem_normalizer_iff.1 hg r).1 hr

theorem conj_inv_mem_of_mem_normalizer {g : G} (hg : g ∈ Subgroup.normalizer (R : Set G))
    {r : G} (hr : r ∈ R) : g⁻¹ * r * g ∈ R := by
  have := conj_mem_of_mem_normalizer (inv_mem hg) hr
  rwa [inv_inv] at this

theorem AgreeOn.refl (a : G) : AgreeOn R a a := fun _ _ => rfl

theorem AgreeOn.symm {a b : G} (h : AgreeOn R a b) : AgreeOn R b a := fun r hr => (h r hr).symm

theorem AgreeOn.trans {a b c : G} (h : AgreeOn R a b) (h' : AgreeOn R b c) : AgreeOn R a c :=
  fun r hr => (h r hr).trans (h' r hr)

theorem AgreeOn.mul {a a' b b' : G} (ha : AgreeOn R a a') (hb : AgreeOn R b b')
    (hb' : b' ∈ Subgroup.normalizer (R : Set G)) : AgreeOn R (a * b) (a' * b') := by
  intro r hr
  have hm : b' * r * b'⁻¹ ∈ R := conj_mem_of_mem_normalizer hb' hr
  calc a * b * r * (a * b)⁻¹ = a * (b * r * b⁻¹) * a⁻¹ := by group
    _ = a * (b' * r * b'⁻¹) * a⁻¹ := by rw [hb r hr]
    _ = a' * (b' * r * b'⁻¹) * a'⁻¹ := ha _ hm
    _ = a' * b' * r * (a' * b')⁻¹ := by group

theorem AgreeOn.inv {a a' : G} (ha : AgreeOn R a a') (ha' : a' ∈ Subgroup.normalizer (R : Set G)) :
    AgreeOn R a⁻¹ a'⁻¹ := by
  intro r hr
  have hs : a'⁻¹ * r * a' ∈ R := conj_inv_mem_of_mem_normalizer ha' hr
  have h2 : a * (a'⁻¹ * r * a') * a⁻¹ = r := by rw [ha _ hs]; group
  calc a⁻¹ * r * a⁻¹⁻¹ = a⁻¹ * (a * (a'⁻¹ * r * a') * a⁻¹) * a⁻¹⁻¹ := by rw [h2]
    _ = a'⁻¹ * r * a'⁻¹⁻¹ := by group

theorem AgreeOn.commutator {a a' b b' : G} (ha : AgreeOn R a a') (hb : AgreeOn R b b')
    (ha' : a' ∈ Subgroup.normalizer (R : Set G)) (hb' : b' ∈ Subgroup.normalizer (R : Set G)) :
    AgreeOn R ⁅a, b⁆ ⁅a', b'⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  exact (((ha.mul hb hb').mul (ha.inv ha') (inv_mem ha')).mul (hb.inv hb') (inv_mem hb'))

theorem agreeOn_commutator_one {a b : G} {n : ℤ} (ha : a ∈ Subgroup.normalizer (R : Set G))
    (hb : AgreeOn R b (a ^ n)) : AgreeOn R ⁅a, b⁆ 1 := by
  have h := (AgreeOn.refl a).commutator hb ha (Subgroup.zpow_mem _ ha n)
  refine h.trans fun r _ => ?_
  rw [commutatorElement_def]
  group

theorem eq_one_of_invOn_of_agreeOn_one {p : ℕ} (hp : Odd p) (hRp : ∀ r ∈ R, r ^ p = 1) {c : G}
    (hc : InvOn R c) (h1 : AgreeOn R c 1) {r : G} (hr : r ∈ R) : r = 1 := by
  have h2 : r⁻¹ = r := by
    rw [← hc r hr, h1 r hr]
    group
  have hsq : r ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [← h2]; exact inv_mul_cancel r
  obtain ⟨k, rfl⟩ := hp
  have h3 := hRp r hr
  rw [pow_succ, pow_mul, hsq, one_pow, one_mul] at h3
  exact h3

theorem mem_conjSub {g : G} {K : Subgroup G} {x : G} :
    x ∈ conjSub g K ↔ g⁻¹ * x * g ∈ K := by
  constructor
  · rintro ⟨k, hk, rfl⟩
    have e : g⁻¹ * ((MulAut.conj g).toMonoidHom k) * g = k := by
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    rw [e]
    exact hk
  · intro h
    refine ⟨g⁻¹ * x * g, h, ?_⟩
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    group

theorem conjSub_one (K : Subgroup G) : conjSub 1 K = K := by
  ext x
  simp

theorem conjSub_mul (a b : G) (K : Subgroup G) : conjSub (a * b) K = conjSub a (conjSub b K) := by
  ext x
  simp only [mem_conjSub, mul_inv_rev]
  constructor <;> intro h <;> simpa [mul_assoc] using h

theorem conjSub_inv_conjSub (a : G) (K : Subgroup G) : conjSub a⁻¹ (conjSub a K) = K := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem conjSub_conjSub_inv (a : G) (K : Subgroup G) : conjSub a (conjSub a⁻¹ K) = K := by
  rw [← conjSub_mul, mul_inv_cancel, conjSub_one]

theorem conjSub_injective (a : G) {K K' : Subgroup G} (h : conjSub a K = conjSub a K') :
    K = K' := by
  rw [← conjSub_inv_conjSub a K, h, conjSub_inv_conjSub]

theorem card_conjSub (a : G) (K : Subgroup G) : Nat.card (conjSub a K) = Nat.card K :=
  Subgroup.card_map_of_injective (MulAut.conj a).injective

theorem conjSub_le {a : G} (ha : a ∈ Subgroup.normalizer (R : Set G)) {K : Subgroup G}
    (hK : K ≤ R) : conjSub a K ≤ R := by
  rintro _ ⟨k, hk, rfl⟩
  exact conj_mem_of_mem_normalizer ha (hK hk)

theorem conjSub_eq_of_agreeOn {a b : G} (h : AgreeOn R a b) {K : Subgroup G} (hK : K ≤ R) :
    conjSub a K = conjSub b K := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, (h k (hK hk)).symm⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨k, hk, h k (hK hk)⟩

theorem conjSub_eq_of_invOn {c : G} (hc : InvOn R c) {K : Subgroup G} (hK : K ≤ R) :
    conjSub c K = K := by
  ext x
  constructor
  · rintro ⟨k, hk, rfl⟩
    change c * k * c⁻¹ ∈ K
    rw [hc k (hK hk)]
    exact inv_mem hk
  · intro hx
    refine ⟨x⁻¹, inv_mem hx, ?_⟩
    change c * x⁻¹ * c⁻¹ = x
    rw [hc _ (hK (inv_mem hx)), inv_inv]

theorem exists_zpow_of_conjSub_le {K : Subgroup G} {k₀ : G} (hK : K = Subgroup.zpowers k₀) {a : G}
    (ha : conjSub a K ≤ K) : ∃ m : ℤ, ∀ k ∈ K, a * k * a⁻¹ = k ^ m := by
  have h0 : a * k₀ * a⁻¹ ∈ K := ha ⟨k₀, hK ▸ Subgroup.mem_zpowers k₀, rfl⟩
  rw [hK] at h0
  obtain ⟨m, hm⟩ := h0
  refine ⟨m, fun k hk => ?_⟩
  rw [hK] at hk
  obtain ⟨n, rfl⟩ := hk
  change a * k₀ ^ n * a⁻¹ = (k₀ ^ n) ^ m
  rw [← conj_zpow, ← hm, ← zpow_mul, ← zpow_mul, mul_comm]

theorem conj_commutator_eq_of_conjSub_eq {K : Subgroup G} {k₀ : G} (hK : K = Subgroup.zpowers k₀)
    {a b : G} (ha : conjSub a K = K) (hb : conjSub b K = K) {k : G} (hk : k ∈ K) :
    ⁅a, b⁆ * k * ⁅a, b⁆⁻¹ = k := by
  have ha' : conjSub a⁻¹ K = K := by
    conv_lhs => rw [← ha]
    exact conjSub_inv_conjSub a K
  have hb' : conjSub b⁻¹ K = K := by
    conv_lhs => rw [← hb]
    exact conjSub_inv_conjSub b K
  obtain ⟨m₁, h₁⟩ := exists_zpow_of_conjSub_le hK ha.le
  obtain ⟨m₂, h₂⟩ := exists_zpow_of_conjSub_le hK hb.le
  obtain ⟨m₃, h₃⟩ := exists_zpow_of_conjSub_le hK ha'.le
  obtain ⟨m₄, h₄⟩ := exists_zpow_of_conjSub_le hK hb'.le
  have hmem : ∀ (x : G) (n : ℤ), x ∈ K → x ^ n ∈ K := fun x n hx => Subgroup.zpow_mem _ hx n
  have e₁ : ∀ x ∈ K, x ^ (m₃ * m₁) = x := by
    intro x hx
    have h := h₁ _ (hmem x m₃ hx)
    rw [← zpow_mul, ← h₃ x hx] at h
    rw [← h]
    group
  have e₂ : ∀ x ∈ K, x ^ (m₄ * m₂) = x := by
    intro x hx
    have h := h₂ _ (hmem x m₄ hx)
    rw [← zpow_mul, ← h₄ x hx] at h
    rw [← h]
    group
  have hcomp : ⁅a, b⁆ * k * ⁅a, b⁆⁻¹ = a * (b * (a⁻¹ * (b⁻¹ * k * b⁻¹⁻¹) * a⁻¹⁻¹) * b⁻¹) * a⁻¹ := by
    rw [commutatorElement_def]
    group
  rw [hcomp, h₄ k hk, h₃ _ (hmem k m₄ hk), h₂ _ (hmem _ m₃ (hmem k m₄ hk)),
    h₁ _ (hmem _ m₂ (hmem _ m₃ (hmem k m₄ hk))), ← zpow_mul, ← zpow_mul, ← zpow_mul]
  have : m₄ * (m₃ * (m₂ * m₁)) = (m₃ * m₁) * (m₄ * m₂) := by ring
  rw [this, zpow_mul, e₁ k hk, e₂ k hk]

theorem eq_zpowers_of_card_eq_prime {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hK : Nat.card K = p) {k₀ : G} (hk₀ : k₀ ∈ K) (hk₁ : k₀ ≠ 1) : K = Subgroup.zpowers k₀ := by
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; exact (Fact.out : p.Prime).ne_zero)
  have hdvd : orderOf k₀ ∣ p := hK ▸ Subgroup.orderOf_dvd_natCard K hk₀
  have ho : orderOf k₀ = p :=
    ((Nat.dvd_prime Fact.out).1 hdvd).resolve_left fun h => hk₁ (orderOf_eq_one_iff.1 h)
  exact (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hk₀)
    (by rw [hK, Nat.card_zpowers, ho])).symm

theorem exists_ne_one_of_card_eq_prime {p : ℕ} [Fact p.Prime] {K : Subgroup G}
    (hK : Nat.card K = p) : ∃ k₀ ∈ K, k₀ ≠ 1 := by
  by_contra hcon
  push Not at hcon
  have hbot : K = ⊥ := (Subgroup.eq_bot_iff_forall K).2 hcon
  rw [hbot, Subgroup.card_bot] at hK
  exact (Fact.out : p.Prime).one_lt.ne hK

theorem not_fix_and_fix {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (hRp : ∀ r ∈ R, r ^ p = 1)
    {a b : G} (hab : InvOn R ⁅a, b⁆) {K : Subgroup G} (hKR : K ≤ R) (hK : Nat.card K = p)
    (ha : conjSub a K = K) (hb : conjSub b K = K) : False := by
  obtain ⟨k₀, hk₀, hk₁⟩ := exists_ne_one_of_card_eq_prime hK
  have hKz := eq_zpowers_of_card_eq_prime hK hk₀ hk₁
  have h1 := conj_commutator_eq_of_conjSub_eq hKz ha hb hk₀
  rw [hab k₀ (hKR hk₀)] at h1
  have hsq : k₀ ^ 2 = 1 := by rw [sq]; nth_rewrite 1 [← h1]; exact inv_mul_cancel k₀
  obtain ⟨m, hm⟩ := (Fact.out : p.Prime).odd_of_ne_two hp2
  have h3 := hRp k₀ (hKR hk₀)
  rw [hm, pow_succ, pow_mul, hsq, one_pow, one_mul] at h3
  exact hk₁ h3

end Action

section Unipotent

variable {G : Type*} [Group G] {p : ℕ} [hp : Fact p.Prime]

theorem zpow_param {φ : ZMod p × ZMod p → G} (hadd : ∀ x y, φ (x + y) = φ x * φ y)
    (hφp : ∀ x, φ x ^ p = 1) (u : ZMod p × ZMod p) (n : ℤ) :
    φ u ^ n = φ ((n : ZMod p) • u) := by
  rw [param_smul hadd, ← zpow_natCast, ZMod.val_intCast]
  exact zpow_eq_zpow_emod' n (hφp u)

theorem commutator_centralizes_of_fix {R : Subgroup G}
    (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a) (hRp : ∀ r ∈ R, r ^ p = 1)
    (hRcard : Nat.card R = p ^ 2) {a b : G} (ha : a ∈ Subgroup.normalizer (R : Set G))
    (hb : b ∈ Subgroup.normalizer (R : Set G)) {K : Subgroup G} (hKR : K ≤ R)
    (hK : Nat.card K = p) (haK : conjSub a K = K) (hbK : conjSub b K = K) {N : ℕ}
    (hN : N.Coprime p) (hc : ⁅a, b⁆ ^ N = 1) : ∀ r ∈ R, ⁅a, b⁆ * r * ⁅a, b⁆⁻¹ = r := by
  classical
  obtain ⟨φ, hadd, hinj, hmem, hsurj⟩ := exists_param R hRc hRp hRcard
  have hφp : ∀ x, φ x ^ p = 1 := fun x => hRp _ (hmem x)
  set c := ⁅a, b⁆ with hcdef
  have hcN : c ∈ Subgroup.normalizer (R : Set G) := by
    rw [hcdef, commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem ha hb) (inv_mem ha)) (inv_mem hb)
  obtain ⟨γa, hab, haadd, hak, hac⟩ :=
    exists_coord_conj hadd hinj hmem hsurj fun r hr => conj_mem_of_mem_normalizer ha hr
  obtain ⟨γb, hbb, hbadd, hbk, hbc⟩ :=
    exists_coord_conj hadd hinj hmem hsurj fun r hr => conj_mem_of_mem_normalizer hb hr
  obtain ⟨γc, hcb, hcadd, hck, hcc⟩ :=
    exists_coord_conj hadd hinj hmem hsurj fun r hr => conj_mem_of_mem_normalizer hcN hr
  have hcomp : ∀ x, γc (γb (γa x)) = γa (γb x) := by
    intro x
    apply hinj
    rw [← hcc, ← hbc, ← hac, ← hac, ← hbc]
    have : c * (b * a) = a * b := by rw [hcdef, commutatorElement_def]; group
    calc c * (b * (a * φ x * a⁻¹) * b⁻¹) * c⁻¹ = (c * (b * a)) * φ x * (c * (b * a))⁻¹ := by group
      _ = (a * b) * φ x * (a * b)⁻¹ := by rw [this]
      _ = a * (b * φ x * b⁻¹) * a⁻¹ := by group
  obtain ⟨k₀, hk₀, hk₁⟩ := exists_ne_one_of_card_eq_prime hK
  have hKz := eq_zpowers_of_card_eq_prime hK hk₀ hk₁
  obtain ⟨u, rfl⟩ := hsurj k₀ (hKR hk₀)
  have hu0 : u ≠ 0 := fun h => hk₁ (by rw [h, param_zero hadd])
  have hline : ∀ {g : G} {γ : ZMod p × ZMod p → ZMod p × ZMod p}, conjSub g K = K →
      (∀ x, g * φ x * g⁻¹ = φ (γ x)) → ∃ α : ZMod p, γ u = α • u := by
    intro g γ hgK hgc
    have hm : g * φ u * g⁻¹ ∈ K := by
      rw [← hgK]
      exact ⟨φ u, hk₀, rfl⟩
    rw [hKz] at hm
    obtain ⟨n, hn⟩ := hm
    beta_reduce at hn
    refine ⟨(n : ZMod p), hinj ?_⟩
    rw [← hgc, ← hn, zpow_param hadd hφp]
  obtain ⟨α, hα⟩ := hline haK hac
  obtain ⟨β, hβ⟩ := hline hbK hbc
  have hcu : γc u = u := by
    apply hinj
    rw [← hcc]
    exact conj_commutator_eq_of_conjSub_eq hKz haK hbK hk₀
  obtain ⟨w, hw⟩ := exists_det_ne u hu0
  have hbasis : ∀ x : ZMod p × ZMod p, ∃ s t : ZMod p, x = s • u + t • w := by
    intro x
    have hbij := Finite.injective_iff_bijective.1 (lineMap_injective hw)
    obtain ⟨⟨s, t⟩, hst⟩ := hbij.2 x
    exact ⟨s, t, hst.symm⟩
  have huniq : ∀ s t s' t' : ZMod p, s • u + t • w = s' • u + t' • w → s = s' ∧ t = t' := by
    intro s t s' t' h
    have := lineMap_injective hw (a₁ := (s, t)) (a₂ := (s', t')) h
    exact ⟨congrArg Prod.fst this, congrArg Prod.snd this⟩
  have hlin : ∀ {γ : ZMod p × ZMod p → ZMod p × ZMod p}, (∀ x y, γ (x + y) = γ x + γ y) →
      (∀ (c : ZMod p) x, γ (c • x) = c • γ x) → ∀ s t : ZMod p,
        γ (s • u + t • w) = s • γ u + t • γ w := by
    intro γ hγa hγk s t
    rw [hγa, hγk, hγk]
  obtain ⟨s₁, t₁, h₁⟩ := hbasis (γa w)
  obtain ⟨s₂, t₂, h₂⟩ := hbasis (γb w)
  obtain ⟨s₃, t₃, h₃⟩ := hbasis (γc w)
  have ht : ∀ {γ : ZMod p × ZMod p → ZMod p × ZMod p} {α s t : ZMod p}, Function.Bijective γ →
      (∀ (c : ZMod p) x, γ (c • x) = c • γ x) → γ u = α • u → γ w = s • u + t • w → t ≠ 0 := by
    intro γ α s t hγb hγk hγu hγw ht0
    rw [ht0, zero_smul, add_zero] at hγw
    have hγ0 : γ 0 = 0 :=
      calc γ 0 = γ ((0 : ZMod p) • (0 : ZMod p × ZMod p)) := by rw [zero_smul]
        _ = 0 := by rw [hγk, zero_smul]
    have hα0 : α ≠ 0 := by
      rintro rfl
      rw [zero_smul, ← hγ0] at hγu
      exact hu0 (hγb.1 hγu)
    have he : γ (α • w) = γ (s • u) := by rw [hγk, hγk, hγw, hγu, smul_smul, smul_smul, mul_comm]
    have he' := hγb.1 he
    have hd := congrArg (fun x => det2 u x) he'
    simp only [det2, Prod.smul_fst, Prod.smul_snd, smul_eq_mul] at hd
    apply hw
    refine (mul_eq_zero.1 ?_).resolve_left hα0
    unfold det2
    linear_combination hd
  have ht₁ := ht hab hak hα h₁
  have ht₂ := ht hbb hbk hβ h₂
  have eL : γc (γb (γa w)) = (s₁ * β + t₁ * s₂ + t₁ * t₂ * s₃) • u + (t₁ * t₂ * t₃) • w := by
    rw [h₁, hlin hbadd hbk, hβ, h₂]
    have e1 : s₁ • (β • u) + t₁ • (s₂ • u + t₂ • w) = (s₁ * β + t₁ * s₂) • u + (t₁ * t₂) • w := by
      module
    rw [e1, hlin hcadd hck, hcu, h₃]
    module
  have eR : γa (γb w) = (s₂ * α + t₂ * s₁) • u + (t₂ * t₁) • w := by
    rw [h₂, hlin haadd hak, hα, h₁]
    module
  have ht₃ : t₃ = 1 := by
    have := (huniq _ _ _ _ (eL.symm.trans ((hcomp w).trans eR))).2
    have h12 : t₁ * t₂ ≠ 0 := mul_ne_zero ht₁ ht₂
    apply mul_left_cancel₀ h12
    rw [mul_one]
    linear_combination this
  have hiter : ∀ n : ℕ, γc^[n] w = ((n : ZMod p) * s₃) • u + w := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ih, hcadd, hck, hcu, h₃, ht₃]
      push_cast
      module
  have hφiter : ∀ (n : ℕ) (x : ZMod p × ZMod p), φ (γc^[n] x) = c ^ n * φ x * (c ^ n)⁻¹ := by
    intro n x
    induction n with
    | zero => simp
    | succ n ih =>
      rw [Function.iterate_succ_apply', ← hcc, ih, pow_succ']
      group
  have hs₃ : s₃ = 0 := by
    have h1 : φ (γc^[N] w) = φ w := by rw [hφiter, hc]; group
    have h2 := hinj h1
    rw [hiter] at h2
    have h3 : ((N : ZMod p) * s₃) • u = 0 := by
      have := congrArg (· - w) h2
      simpa using this
    rcases smul_eq_zero.1 h3 with h4 | h4
    · rcases mul_eq_zero.1 h4 with h5 | h5
      · exfalso
        rw [ZMod.natCast_eq_zero_iff] at h5
        exact (Nat.Prime.coprime_iff_not_dvd hp.out).1 (Nat.coprime_comm.1 hN) h5
      · exact h5
    · exact absurd h4 hu0
  intro r hr
  obtain ⟨x, rfl⟩ := hsurj r hr
  obtain ⟨s, t, rfl⟩ := hbasis x
  rw [hcc, hlin hcadd hck, hcu, h₃, hs₃, ht₃, zero_smul, zero_add, one_smul]

end Unipotent

section Orbit

variable {G : Type*} [Group G] {R : Subgroup G} {p : ℕ} [hp : Fact p.Prime]

structure IsQ8Data (R : Subgroup G) (i j h : G) : Prop where
  mem_i : i ∈ Subgroup.normalizer (R : Set G)
  mem_j : j ∈ Subgroup.normalizer (R : Set G)
  mem_h : h ∈ Subgroup.normalizer (R : Set G)
  inv_comm : InvOn R ⁅i, j⁆
  inv_ii : InvOn R (i * i)
  inv_jj : InvOn R (j * j)
  conj_i : AgreeOn R (h * i * h⁻¹) j
  conj_j : AgreeOn R (h * j * h⁻¹) (i * j)

@[expose] def vImages (i j : G) (K : Subgroup G) : List (Subgroup G) :=
  [K, conjSub i K, conjSub j K, conjSub i (conjSub j K)]

theorem exists_finset_of_list {H : Subgroup G} {K : Subgroup G} (l : List G)
    (hl : ∀ g ∈ l, g ∈ H) (hnd : (l.map fun g => conjSub g K).Nodup) :
    ∃ S : Finset (Subgroup G), l.length ≤ S.card ∧ ∀ K' ∈ S, ∃ g ∈ H, K' = conjSub g K := by
  classical
  refine ⟨(l.map fun g => conjSub g K).toFinset, ?_, ?_⟩
  · rw [List.toFinset_card_of_nodup hnd, List.length_map]
  · intro K' hK'
    rw [List.mem_toFinset, List.mem_map] at hK'
    obtain ⟨g, hg, rfl⟩ := hK'
    exact ⟨g, hl g hg, rfl⟩

theorem orbit_of_conjSub {H : Subgroup G} {K : Subgroup G} {g : G} (hg : g ∈ H) {k : ℕ}
    (h : ∃ S : Finset (Subgroup G), k ≤ S.card ∧
      ∀ K' ∈ S, ∃ g' ∈ H, K' = conjSub g' (conjSub g K)) :
    ∃ S : Finset (Subgroup G), k ≤ S.card ∧ ∀ K' ∈ S, ∃ g' ∈ H, K' = conjSub g' K := by
  obtain ⟨S, hS, hS'⟩ := h
  refine ⟨S, hS, fun K' hK' => ?_⟩
  obtain ⟨g', hg', rfl⟩ := hS' K' hK'
  exact ⟨g' * g, mul_mem hg' hg, (conjSub_mul g' g K).symm⟩

namespace IsQ8Data

variable {i j h : G} (hd : IsQ8Data R i j h)
include hd

theorem ii (L : Subgroup G) (hL : L ≤ R) : conjSub i (conjSub i L) = L := by
  rw [← conjSub_mul, conjSub_eq_of_invOn hd.inv_ii hL]

theorem jj (L : Subgroup G) (hL : L ≤ R) : conjSub j (conjSub j L) = L := by
  rw [← conjSub_mul, conjSub_eq_of_invOn hd.inv_jj hL]

theorem ij_comm (L : Subgroup G) (hL : L ≤ R) :
    conjSub i (conjSub j L) = conjSub j (conjSub i L) := by
  have e : i * j = ⁅i, j⁆ * (j * i) := by rw [commutatorElement_def]; group
  rw [← conjSub_mul, ← conjSub_mul, e, conjSub_mul,
    conjSub_eq_of_invOn hd.inv_comm (conjSub_le (mul_mem hd.mem_j hd.mem_i) hL)]

theorem h_i (L : Subgroup G) (hL : L ≤ R) :
    conjSub h (conjSub i L) = conjSub j (conjSub h L) := by
  have e : h * i = (h * i * h⁻¹) * h := by group
  rw [← conjSub_mul, e, conjSub_mul, conjSub_eq_of_agreeOn hd.conj_i (conjSub_le hd.mem_h hL)]

theorem h_j (L : Subgroup G) (hL : L ≤ R) :
    conjSub h (conjSub j L) = conjSub i (conjSub j (conjSub h L)) := by
  have e : h * j = (h * j * h⁻¹) * h := by group
  rw [← conjSub_mul, e, conjSub_mul, conjSub_eq_of_agreeOn hd.conj_j (conjSub_le hd.mem_h hL),
    conjSub_mul]

theorem not_fix_i_j (hp2 : p ≠ 2) (hRp : ∀ r ∈ R, r ^ p = 1) {L : Subgroup G} (hL : L ≤ R)
    (hLp : Nat.card L = p) (hi : conjSub i L = L) (hj : conjSub j L = L) : False :=
  not_fix_and_fix hp2 hRp hd.inv_comm hL hLp hi hj

omit hd in
theorem fix_j_of_fix_i_ij {L : Subgroup G} (hi : conjSub i L = L)
    (hij : conjSub i (conjSub j L) = L) : conjSub j L = L := by
  apply conjSub_injective i
  rw [hij, hi]

omit hd in
theorem fix_i_of_fix_j_ij {L : Subgroup G} (hj : conjSub j L = L)
    (hij : conjSub i (conjSub j L) = L) : conjSub i L = L := by
  rwa [hj] at hij

theorem fix_i_of_fix_j {L : Subgroup G} (hL : L ≤ R) (hj : conjSub j L = L) :
    conjSub i (conjSub h⁻¹ L) = conjSub h⁻¹ L := by
  have h1 := hd.h_i (conjSub h⁻¹ L) (conjSub_le (inv_mem hd.mem_h) hL)
  rw [conjSub_conjSub_inv, hj] at h1
  calc conjSub i (conjSub h⁻¹ L) = conjSub h⁻¹ (conjSub h (conjSub i (conjSub h⁻¹ L))) :=
        (conjSub_inv_conjSub _ _).symm
    _ = conjSub h⁻¹ L := by rw [h1]

theorem fix_j_of_fix_ij {L : Subgroup G} (hL : L ≤ R) (hij : conjSub i (conjSub j L) = L) :
    conjSub j (conjSub h⁻¹ L) = conjSub h⁻¹ L := by
  have h1 := hd.h_j (conjSub h⁻¹ L) (conjSub_le (inv_mem hd.mem_h) hL)
  rw [conjSub_conjSub_inv, hij] at h1
  calc conjSub j (conjSub h⁻¹ L) = conjSub h⁻¹ (conjSub h (conjSub j (conjSub h⁻¹ L))) :=
        (conjSub_inv_conjSub _ _).symm
    _ = conjSub h⁻¹ L := by rw [h1]

end IsQ8Data

theorem nodup_four {α : Type*} {a b c d : α} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d) (h4 : b ≠ c)
    (h5 : b ≠ d) (h6 : c ≠ d) : [a, b, c, d].Nodup := by
  simp [h1, h2, h3, h4, h5, h6]

theorem nodup_six {α : Type*} {a b c d e f : α} (h1 : a ≠ b) (h2 : a ≠ c) (h3 : a ≠ d)
    (h4 : a ≠ e) (h5 : a ≠ f) (h6 : b ≠ c) (h7 : b ≠ d) (h8 : b ≠ e) (h9 : b ≠ f) (h10 : c ≠ d)
    (h11 : c ≠ e) (h12 : c ≠ f) (h13 : d ≠ e) (h14 : d ≠ f) (h15 : e ≠ f) :
    [a, b, c, d, e, f].Nodup := by
  simp [h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11, h12, h13, h14, h15]

theorem ne_of_excl {P Q : Subgroup G → Prop} (hPQ : ∀ L, P L → Q L → False) {X Y : Subgroup G}
    (hX : P X) (hY : Q Y) : X ≠ Y := fun h => hPQ X hX (h ▸ hY)

omit hp in
theorem line_conjSub {g : G} (hg : g ∈ Subgroup.normalizer (R : Set G)) {L : Subgroup G}
    (hL : L ≤ R) (hLp : Nat.card L = p) : conjSub g L ≤ R ∧ Nat.card (conjSub g L) = p :=
  ⟨conjSub_le hg hL, (card_conjSub g L).trans hLp⟩

namespace IsQ8Data

variable {i j h : G} (hd : IsQ8Data R i j h) (hp2 : p ≠ 2) (hRp : ∀ r ∈ R, r ^ p = 1)

include hd hp2 hRp in
theorem not_fix_i_ij {L : Subgroup G} (hL : L ≤ R) (hLp : Nat.card L = p)
    (hi : conjSub i L = L) (hij : conjSub i (conjSub j L) = L) : False :=
  hd.not_fix_i_j hp2 hRp hL hLp hi (fix_j_of_fix_i_ij hi hij)

include hd hp2 hRp in
theorem not_fix_j_ij {L : Subgroup G} (hL : L ≤ R) (hLp : Nat.card L = p)
    (hj : conjSub j L = L) (hij : conjSub i (conjSub j L) = L) : False :=
  hd.not_fix_i_j hp2 hRp hL hLp (fix_i_of_fix_j_ij hj hij) hj

include hd hp2 hRp in
theorem six_of_fix_i {L : Subgroup G} (hL : L ≤ R) (hLp : Nat.card L = p)
    (hi : conjSub i L = L) :
    ([1, j, h, i * h, h * h, i * (h * h)].map fun g => conjSub g L).Nodup := by
  have mj := hd.mem_j
  have mh := hd.mem_h
  have mi := hd.mem_i
  obtain ⟨hjL, hjLp⟩ := line_conjSub mj hL hLp
  obtain ⟨hhL, hhLp⟩ := line_conjSub mh hL hLp
  obtain ⟨hihL, hihLp⟩ := line_conjSub mi hhL hhLp
  obtain ⟨hhhL, hhhLp⟩ := line_conjSub mh hhL hhLp
  obtain ⟨hihhL, hihhLp⟩ := line_conjSub mi hhhL hhhLp
  have f1 : conjSub i (conjSub j L) = conjSub j L := by rw [hd.ij_comm L hL, hi]
  have f2 : conjSub j (conjSub h L) = conjSub h L := by rw [← hd.h_i L hL, hi]
  have f3 : conjSub j (conjSub i (conjSub h L)) = conjSub i (conjSub h L) := by
    rw [← hd.ij_comm _ hhL, f2]
  have f4 : conjSub i (conjSub j (conjSub h (conjSub h L))) = conjSub h (conjSub h L) := by
    rw [← hd.h_j _ hhL, f2]
  have f5 : conjSub i (conjSub j (conjSub i (conjSub h (conjSub h L)))) =
      conjSub i (conjSub h (conjSub h L)) := by
    have e : conjSub j (conjSub h (conjSub h L)) = conjSub i (conjSub h (conjSub h L)) := by
      conv_lhs => rw [← hd.ii _ (conjSub_le hd.mem_j hhhL), f4]
    rw [← hd.ij_comm _ hhhL, hd.ii _ (conjSub_le hd.mem_j hhhL), e]
  have xij : ∀ X, (X ≤ R ∧ Nat.card X = p ∧ conjSub i X = X) →
      (X ≤ R ∧ Nat.card X = p ∧ conjSub j X = X) → False :=
    fun X hX hX' => hd.not_fix_i_j hp2 hRp hX.1 hX.2.1 hX.2.2 hX'.2.2
  have xiij : ∀ X, (X ≤ R ∧ Nat.card X = p ∧ conjSub i X = X) →
      (X ≤ R ∧ Nat.card X = p ∧ conjSub i (conjSub j X) = X) → False :=
    fun X hX hX' => hd.not_fix_i_ij hp2 hRp hX.1 hX.2.1 hX.2.2 hX'.2.2
  have xjij : ∀ X, (X ≤ R ∧ Nat.card X = p ∧ conjSub j X = X) →
      (X ≤ R ∧ Nat.card X = p ∧ conjSub i (conjSub j X) = X) → False :=
    fun X hX hX' => hd.not_fix_j_ij hp2 hRp hX.1 hX.2.1 hX.2.2 hX'.2.2
  have t1 : L ≤ R ∧ Nat.card L = p ∧ conjSub i L = L := ⟨hL, hLp, hi⟩
  have t2 : conjSub j L ≤ R ∧ Nat.card (conjSub j L) = p ∧ conjSub i (conjSub j L) = conjSub j L :=
    ⟨hjL, hjLp, f1⟩
  have t3 : conjSub h L ≤ R ∧ Nat.card (conjSub h L) = p ∧
      conjSub j (conjSub h L) = conjSub h L := ⟨hhL, hhLp, f2⟩
  have t4 : conjSub i (conjSub h L) ≤ R ∧ Nat.card (conjSub i (conjSub h L)) = p ∧
      conjSub j (conjSub i (conjSub h L)) = conjSub i (conjSub h L) := ⟨hihL, hihLp, f3⟩
  have t5 : conjSub h (conjSub h L) ≤ R ∧ Nat.card (conjSub h (conjSub h L)) = p ∧
      conjSub i (conjSub j (conjSub h (conjSub h L))) = conjSub h (conjSub h L) :=
    ⟨hhhL, hhhLp, f4⟩
  have t6 : conjSub i (conjSub h (conjSub h L)) ≤ R ∧
      Nat.card (conjSub i (conjSub h (conjSub h L))) = p ∧
      conjSub i (conjSub j (conjSub i (conjSub h (conjSub h L)))) =
        conjSub i (conjSub h (conjSub h L)) := ⟨hihhL, hihhLp, f5⟩
  have w1 : L ≠ conjSub j L := fun e => xij L t1 ⟨hL, hLp, e.symm⟩
  have w2 : conjSub h L ≠ conjSub i (conjSub h L) := fun e =>
    xij _ ⟨hhL, hhLp, e.symm⟩ t3
  have w3 : conjSub h (conjSub h L) ≠ conjSub i (conjSub h (conjSub h L)) := fun e =>
    xiij _ ⟨hhhL, hhhLp, e.symm⟩ t5
  simp only [List.map_cons, List.map_nil, conjSub_one, conjSub_mul]
  exact nodup_six w1 (ne_of_excl xij t1 t3) (ne_of_excl xij t1 t4) (ne_of_excl xiij t1 t5)
    (ne_of_excl xiij t1 t6) (ne_of_excl xij t2 t3) (ne_of_excl xij t2 t4) (ne_of_excl xiij t2 t5)
    (ne_of_excl xiij t2 t6) w2 (ne_of_excl xjij t3 t5) (ne_of_excl xjij t3 t6)
    (ne_of_excl xjij t4 t5) (ne_of_excl xjij t4 t6) w3

include hd in
theorem ne_vImages {L : Subgroup G} (hL : L ≤ R) (hi : conjSub i L ≠ L)
    (hj : conjSub j L ≠ L) (hij : conjSub i (conjSub j L) ≠ L) :
    L ≠ conjSub i L ∧ L ≠ conjSub j L ∧ L ≠ conjSub i (conjSub j L) ∧
      conjSub i L ≠ conjSub j L ∧ conjSub i L ≠ conjSub i (conjSub j L) ∧
      conjSub j L ≠ conjSub i (conjSub j L) := by
  refine ⟨Ne.symm hi, Ne.symm hj, Ne.symm hij, fun e => hij ?_, fun e => hj ?_, fun e => hi ?_⟩
  · rw [← e, hd.ii L hL]
  · exact (conjSub_injective i e).symm
  · rw [hd.ij_comm L hL] at e
    exact (conjSub_injective j e).symm

include hd in
theorem nodup_vImages {L : Subgroup G} (hL : L ≤ R) (hi : conjSub i L ≠ L)
    (hj : conjSub j L ≠ L) (hij : conjSub i (conjSub j L) ≠ L) : (vImages i j L).Nodup := by
  obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hd.ne_vImages hL hi hj hij
  exact nodup_four n1 n2 n3 n4 n5 n6

include hd in
theorem conjSub_i_mem_vImages {L X : Subgroup G} (hL : L ≤ R) (hX : X ∈ vImages i j L) :
    conjSub i X ∈ vImages i j L := by
  simp only [vImages, List.mem_cons, List.mem_nil_iff, or_false] at hX ⊢
  rcases hX with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inl rfl)
  · exact Or.inl (hd.ii L hL)
  · exact Or.inr (Or.inr (Or.inr rfl))
  · exact Or.inr (Or.inr (Or.inl (hd.ii _ (conjSub_le hd.mem_j hL))))

include hd in
theorem conjSub_j_mem_vImages {L X : Subgroup G} (hL : L ≤ R) (hX : X ∈ vImages i j L) :
    conjSub j X ∈ vImages i j L := by
  simp only [vImages, List.mem_cons, List.mem_nil_iff, or_false] at hX ⊢
  rcases hX with rfl | rfl | rfl | rfl
  · exact Or.inr (Or.inr (Or.inl rfl))
  · exact Or.inr (Or.inr (Or.inr (hd.ij_comm L hL).symm))
  · exact Or.inl (hd.jj L hL)
  · refine Or.inr (Or.inl ?_)
    rw [← hd.ij_comm _ (conjSub_le hd.mem_j hL), hd.jj L hL]

include hd in
theorem conjSub_not_mem_vImages {L X : Subgroup G} (hL : L ≤ R) (hXR : X ≤ R)
    (hX : X ∉ vImages i j L) {x : G} (hx : x = i ∨ x = j) : conjSub x X ∉ vImages i j L := by
  intro hm
  apply hX
  rcases hx with rfl | rfl
  · rw [← hd.ii X hXR]
    exact hd.conjSub_i_mem_vImages hL hm
  · rw [← hd.jj X hXR]
    exact hd.conjSub_j_mem_vImages hL hm

theorem exists_of_mem_vImages {L X : Subgroup G} (hX : X ∈ vImages i j L) :
    ∃ a ∈ [1, i, j, i * j], X = conjSub a L := by
  simp only [vImages, List.mem_cons, List.mem_nil_iff, or_false] at hX
  rcases hX with rfl | rfl | rfl | rfl
  · exact ⟨1, by simp, (conjSub_one _).symm⟩
  · exact ⟨i, by simp, rfl⟩
  · exact ⟨j, by simp, rfl⟩
  · exact ⟨i * j, by simp, (conjSub_mul i j L).symm⟩

end IsQ8Data

theorem four_le_orbit (hp2 : p ≠ 2) (hRp : ∀ r ∈ R, r ^ p = 1) {i j h : G}
    (hd : IsQ8Data R i j h) {K : Subgroup G} (hKR : K ≤ R) (hK : Nat.card K = p) :
    ∃ S : Finset (Subgroup G), 4 ≤ S.card ∧
      ∀ K' ∈ S, ∃ g ∈ Subgroup.closure ({i, j, h} : Set G), K' = conjSub g K := by
  set H := Subgroup.closure ({i, j, h} : Set G) with hH
  have hiH : i ∈ H := Subgroup.subset_closure (by simp)
  have hjH : j ∈ H := Subgroup.subset_closure (by simp)
  have hhH : h ∈ H := Subgroup.subset_closure (by simp)
  have caseB : ∀ L : Subgroup G, L ≤ R → Nat.card L = p → conjSub i L = L →
      ∃ S : Finset (Subgroup G), 4 ≤ S.card ∧ ∀ K' ∈ S, ∃ g ∈ H, K' = conjSub g L := by
    intro L hL hLp hi
    have h6 := hd.six_of_fix_i hp2 hRp hL hLp hi
    have h4 : ([1, j, h, i * h].map fun g => conjSub g L).Nodup := by
      simp only [List.map_cons, List.map_nil] at h6 ⊢
      exact (List.Nodup.sublist (by simp) h6)
    exact exists_finset_of_list _ (by simp [hjH, hhH, mul_mem hiH hhH, one_mem]) h4
  by_cases hi : conjSub i K = K
  · exact caseB K hKR hK hi
  by_cases hj : conjSub j K = K
  · refine orbit_of_conjSub (inv_mem hhH) (caseB _ ?_ ?_ (hd.fix_i_of_fix_j hKR hj))
    · exact conjSub_le (inv_mem hd.mem_h) hKR
    · exact (card_conjSub _ _).trans hK
  by_cases hij : conjSub i (conjSub j K) = K
  · have h1 := hd.fix_j_of_fix_ij hKR hij
    have hR1 : conjSub h⁻¹ K ≤ R := conjSub_le (inv_mem hd.mem_h) hKR
    have h2 := hd.fix_i_of_fix_j hR1 h1
    refine orbit_of_conjSub (inv_mem hhH) (orbit_of_conjSub (inv_mem hhH) (caseB _ ?_ ?_ h2))
    · exact conjSub_le (inv_mem hd.mem_h) hR1
    · rw [card_conjSub, card_conjSub, hK]
  have hnd := hd.nodup_vImages hKR hi hj hij
  have e : vImages i j K = [1, i, j, i * j].map fun g => conjSub g K := by
    simp [vImages, conjSub_one, conjSub_mul]
  rw [e] at hnd
  exact exists_finset_of_list _ (by simp [hiH, hjH, mul_mem hiH hjH, one_mem]) hnd

structure IsGL23Data (R : Subgroup G) (i j h t : G) : Prop extends IsQ8Data R i j h where
  mem_t : t ∈ Subgroup.normalizer (R : Set G)
  comm : ∀ a ∈ [1, i, j, i * j], ∀ b ∈ [1, i, j, i * j],
    ⁅a⁻¹ * h, b⁻¹ * t⁆ ^ 12 = 1 ∧
      ∃ m : ℤ, AgreeOn R (⁅a⁻¹ * h, b⁻¹ * t⁆ * i * ⁅a⁻¹ * h, b⁻¹ * t⁆⁻¹) (i ^ m * j)

theorem six_le_orbit (hp2 : p ≠ 2) (hp3 : p ≠ 3) (hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a)
    (hRp : ∀ r ∈ R, r ^ p = 1) (hRcard : Nat.card R = p ^ 2) {i j h t : G}
    (hd : IsGL23Data R i j h t) {K : Subgroup G} (hKR : K ≤ R) (hK : Nat.card K = p) :
    ∃ S : Finset (Subgroup G), 6 ≤ S.card ∧
      ∀ K' ∈ S, ∃ g ∈ Subgroup.closure ({i, j, h, t} : Set G), K' = conjSub g K := by
  set H := Subgroup.closure ({i, j, h, t} : Set G) with hH
  have hq := hd.toIsQ8Data
  have hiH : i ∈ H := Subgroup.subset_closure (by simp)
  have hjH : j ∈ H := Subgroup.subset_closure (by simp)
  have hhH : h ∈ H := Subgroup.subset_closure (by simp)
  have htH : t ∈ H := Subgroup.subset_closure (by simp)
  have caseB : ∀ L : Subgroup G, L ≤ R → Nat.card L = p → conjSub i L = L →
      ∃ S : Finset (Subgroup G), 6 ≤ S.card ∧ ∀ K' ∈ S, ∃ g ∈ H, K' = conjSub g L := by
    intro L hL hLp hi
    exact exists_finset_of_list _ (by
      simp [hjH, hhH, mul_mem hiH hhH, mul_mem hhH hhH, mul_mem hiH (mul_mem hhH hhH), one_mem])
      (hq.six_of_fix_i hp2 hRp hL hLp hi)
  by_cases hi : conjSub i K = K
  · exact caseB K hKR hK hi
  by_cases hj : conjSub j K = K
  · refine orbit_of_conjSub (inv_mem hhH) (caseB _ ?_ ?_ (hq.fix_i_of_fix_j hKR hj))
    · exact conjSub_le (inv_mem hq.mem_h) hKR
    · exact (card_conjSub _ _).trans hK
  by_cases hij : conjSub i (conjSub j K) = K
  · have h1 := hq.fix_j_of_fix_ij hKR hij
    have hR1 : conjSub h⁻¹ K ≤ R := conjSub_le (inv_mem hq.mem_h) hKR
    have h2 := hq.fix_i_of_fix_j hR1 h1
    refine orbit_of_conjSub (inv_mem hhH) (orbit_of_conjSub (inv_mem hhH) (caseB _ ?_ ?_ h2))
    · exact conjSub_le (inv_mem hq.mem_h) hR1
    · rw [card_conjSub, card_conjSub, hK]
  have hout : ∀ g ∈ H, g ∈ Subgroup.normalizer (R : Set G) → conjSub g K ∉ vImages i j K →
      ∃ S : Finset (Subgroup G), 6 ≤ S.card ∧ ∀ K' ∈ S, ∃ g' ∈ H, K' = conjSub g' K := by
    intro g hgH hgN hX
    obtain ⟨hXR, hXp⟩ := line_conjSub hgN hKR hK
    obtain ⟨x, hx, hxX⟩ : ∃ x, (x = i ∨ x = j) ∧ conjSub x (conjSub g K) ≠ conjSub g K := by
      by_contra hcon
      push Not at hcon
      exact hq.not_fix_i_j hp2 hRp hXR hXp (hcon i (Or.inl rfl)) (hcon j (Or.inr rfl))
    have hxH : x ∈ H := by rcases hx with rfl | rfl <;> assumption
    have hxX' := hq.conjSub_not_mem_vImages hKR hXR hX hx
    refine exists_finset_of_list [1, i, j, i * j, g, x * g]
      (by simp [hiH, hjH, mul_mem hiH hjH, hgH, mul_mem hxH hgH, one_mem]) ?_
    obtain ⟨n1, n2, n3, n4, n5, n6⟩ := hq.ne_vImages hKR hi hj hij
    simp only [vImages, List.mem_cons, List.mem_nil_iff, or_false, not_or] at hX hxX'
    obtain ⟨m1, m2, m3, m4⟩ := hX
    obtain ⟨k1, k2, k3, k4⟩ := hxX'
    simp only [List.map_cons, List.map_nil, conjSub_one, conjSub_mul]
    exact nodup_six n1 n2 n3 (Ne.symm m1) (Ne.symm k1) n4 n5 (Ne.symm m2) (Ne.symm k2) n6
      (Ne.symm m3) (Ne.symm k3) (Ne.symm m4) (Ne.symm k4) (Ne.symm hxX)
  by_cases hhK : conjSub h K ∈ vImages i j K
  · by_cases htK : conjSub t K ∈ vImages i j K
    ·
      exfalso
      obtain ⟨a, ha, hae⟩ := IsQ8Data.exists_of_mem_vImages hhK
      obtain ⟨b, hb, hbe⟩ := IsQ8Data.exists_of_mem_vImages htK
      have haN : a ∈ Subgroup.normalizer (R : Set G) := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at ha
        rcases ha with rfl | rfl | rfl | rfl
        exacts [one_mem _, hq.mem_i, hq.mem_j, mul_mem hq.mem_i hq.mem_j]
      have hbN : b ∈ Subgroup.normalizer (R : Set G) := by
        simp only [List.mem_cons, List.mem_nil_iff, or_false] at hb
        rcases hb with rfl | rfl | rfl | rfl
        exacts [one_mem _, hq.mem_i, hq.mem_j, mul_mem hq.mem_i hq.mem_j]
      have hfa : conjSub (a⁻¹ * h) K = K := by rw [conjSub_mul, hae, conjSub_inv_conjSub]
      have hfb : conjSub (b⁻¹ * t) K = K := by rw [conjSub_mul, hbe, conjSub_inv_conjSub]
      obtain ⟨hc12, m, hm⟩ := hd.comm a ha b hb
      have hcop : Nat.Coprime 12 p := by
        refine Nat.Coprime.symm ((Nat.Prime.coprime_iff_not_dvd hp.out).2 fun h12 => ?_)
        have h12' : p ∣ 2 * 2 * 3 := h12
        rcases (Nat.Prime.dvd_mul hp.out).1 h12' with h4 | h3
        · rcases (Nat.Prime.dvd_mul hp.out).1 h4 with h2 | h2 <;>
            exact hp2 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_two).1 h2)
        · exact hp3 ((Nat.prime_dvd_prime_iff_eq hp.out Nat.prime_three).1 h3)
      have hcR := commutator_centralizes_of_fix hRc hRp hRcard
        (mul_mem (inv_mem haN) hq.mem_h) (mul_mem (inv_mem hbN) hd.mem_t) hKR hK hfa hfb hcop hc12
      set c := ⁅a⁻¹ * h, b⁻¹ * t⁆ with hcdef
      have hc1 : AgreeOn R c 1 := fun r hr => by rw [hcR r hr]; group
      have hci : AgreeOn R (c * i * c⁻¹) i := by
        have := (hc1.mul (AgreeOn.refl i) hq.mem_i).mul (hc1.inv (one_mem _)) (inv_mem (one_mem _))
        simpa using this
      have him : AgreeOn R i (i ^ m * j) := hci.symm.trans hm
      have hmN : i ^ m * j ∈ Subgroup.normalizer (R : Set G) :=
        mul_mem (Subgroup.zpow_mem _ hq.mem_i m) hq.mem_j
      have hj' : AgreeOn R j (i ^ (1 - m)) := by
        have := (AgreeOn.refl (i ^ (-m))).mul him hmN
        have e1 : i ^ (-m) * (i ^ m * j) = j := by group
        have e2 : i ^ (-m) * i = i ^ (1 - m) := by group
        rw [e1, e2] at this
        exact this.symm
      have hcomm1 := agreeOn_commutator_one hq.mem_i hj'
      obtain ⟨k₀, hk₀, hk₁⟩ := exists_ne_one_of_card_eq_prime hK
      exact hk₁ (eq_one_of_invOn_of_agreeOn_one (hp.out.odd_of_ne_two hp2) hRp hq.inv_comm
        hcomm1 (hKR hk₀))
    · exact hout t htH hd.mem_t htK
  · exact hout h hhH hq.mem_h hhK

theorem ncard_lines_of_plane {P : Subgroup G} (hcard : Nat.card P = p ^ 2)
    (hpow : ∀ x ∈ P, x ^ p = 1) : {M : Subgroup G | M ≤ P ∧ Nat.card M = p}.ncard = p + 1 := by
  classical
  have : Finite P := Nat.finite_of_card_ne_zero (by rw [hcard]; exact pow_ne_zero _ hp.out.ne_zero)
  have : Fintype P := Fintype.ofFinite P
  have hP : CFSG.RankThree.PartOne.KCUnitaryPlane.IsPlane p P :=
    ⟨hp.out, hcard, fun x => Subtype.ext (hpow x x.2)⟩
  have hlines := hP.card_lines
  have himage : {M : Subgroup G | M ≤ P ∧ Nat.card M = p} =
      (fun X : Subgroup P => X.map P.subtype) ''
        ((CFSG.RankThree.PartOne.KCUnitaryPlane.lines p P : Finset (Subgroup P)) : Set _) := by
    ext M
    simp only [Set.mem_ofPred_eq, Set.mem_image, Finset.mem_coe,
      CFSG.RankThree.PartOne.KCUnitaryPlane.mem_lines]
    constructor
    · rintro ⟨hMP, hM⟩
      refine ⟨M.subgroupOf P, ?_, ?_⟩
      · rw [← hM, ← Subgroup.card_map_of_injective P.subtype_injective,
          Subgroup.subgroupOf_map_subtype, inf_of_le_left hMP]
      · rw [Subgroup.subgroupOf_map_subtype, inf_of_le_left hMP]
    · rintro ⟨X, hX, rfl⟩
      exact ⟨Subgroup.map_subtype_le X,
        by rw [Subgroup.card_map_of_injective P.subtype_injective, hX]⟩
  rw [himage, Set.ncard_image_of_injective _ (Subgroup.map_injective P.subtype_injective),
    Set.ncard_coe_finset, hlines]

theorem six_le_orbit_of_eq_five (hp5 : p = 5) (hRp : ∀ r ∈ R, r ^ p = 1)
    (hRcard : Nat.card R = p ^ 2) {i j h : G} (hd : IsQ8Data R i j h) {K : Subgroup G}
    (hKR : K ≤ R) (hK : Nat.card K = p) :
    ∃ S : Finset (Subgroup G), 6 ≤ S.card ∧
      ∀ K' ∈ S, ∃ g ∈ Subgroup.closure ({i, j, h} : Set G), K' = conjSub g K := by
  classical
  have hp2 : p ≠ 2 := by omega
  set H := Subgroup.closure ({i, j, h} : Set G) with hH
  set Ω := {M : Subgroup G | M ≤ R ∧ Nat.card M = p} with hΩ
  have hΩc : Ω.ncard = p + 1 := ncard_lines_of_plane hRcard hRp
  have hΩf : Ω.Finite := Set.finite_of_ncard_pos (by rw [hΩc]; omega)
  have hHN : ∀ g ∈ H, g ∈ Subgroup.normalizer (R : Set G) := by
    intro g hg
    have hle : H ≤ Subgroup.normalizer (R : Set G) := by
      rw [hH, Subgroup.closure_le]
      intro x hx
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hx
      rcases hx with rfl | rfl | rfl
      exacts [hd.mem_i, hd.mem_j, hd.mem_h]
    exact hle hg
  set Orb : Subgroup G → Set (Subgroup G) := fun L => {L' | ∃ g ∈ H, L' = conjSub g L} with hOrb
  have hOrbΩ : ∀ L ∈ Ω, Orb L ⊆ Ω := by
    rintro L ⟨hL, hLp⟩ _ ⟨g, hg, rfl⟩
    exact ⟨conjSub_le (hHN g hg) hL, (card_conjSub _ _).trans hLp⟩
  have hOrb4 : ∀ L ∈ Ω, 4 ≤ (Orb L).ncard := by
    rintro L ⟨hL, hLp⟩
    obtain ⟨S, hS, hS'⟩ := four_le_orbit hp2 hRp hd hL hLp
    have hsub : (S : Set (Subgroup G)) ⊆ Orb L := fun K' hK' => hS' K' hK'
    calc 4 ≤ S.card := hS
      _ = (S : Set (Subgroup G)).ncard := (Set.ncard_coe_finset S).symm
      _ ≤ (Orb L).ncard := Set.ncard_le_ncard hsub (hΩf.subset (hOrbΩ L ⟨hL, hLp⟩))
  have hKΩ : K ∈ Ω := ⟨hKR, hK⟩
  have hall : Ω ⊆ Orb K := by
    intro L hLΩ
    by_contra hLK
    have hdisj : Disjoint (Orb K) (Orb L) := by
      rw [Set.disjoint_left]
      rintro M ⟨g, hg, rfl⟩ ⟨g', hg', hg'e⟩
      apply hLK
      refine ⟨g'⁻¹ * g, mul_mem (inv_mem hg') hg, ?_⟩
      rw [conjSub_mul, hg'e, conjSub_inv_conjSub]
    have hun := Set.ncard_union_eq hdisj (hΩf.subset (hOrbΩ K hKΩ)) (hΩf.subset (hOrbΩ L hLΩ))
    have hle : (Orb K ∪ Orb L).ncard ≤ Ω.ncard :=
      Set.ncard_le_ncard (Set.union_subset (hOrbΩ K hKΩ) (hOrbΩ L hLΩ)) hΩf
    have h1 := hOrb4 K hKΩ
    have h2 := hOrb4 L hLΩ
    omega
  refine ⟨hΩf.toFinset, ?_, fun K' hK' => hall ((Set.Finite.mem_toFinset hΩf).1 hK')⟩
  rw [← Set.ncard_eq_toFinset_card Ω hΩf, hΩc, hp5]

end Orbit

end CFSG.Quasithin.B45Tor

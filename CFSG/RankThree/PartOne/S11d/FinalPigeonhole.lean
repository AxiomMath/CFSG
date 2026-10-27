module

public import CFSG.RankThree.PartOne.S11d.Transvection
public import CFSG.RankThree.PartOne.S11d.FinalAlgebra
public import CFSG.RankThree.PartOne.S11d.FinalLemmas
public import CFSG.RankThree.PGroups.PrimaryFactorization

public section

namespace CFSG.RankThree.PartOne

open Subgroup CFSG.RankThree.PartOne.Transv

variable {G : Type*} [Group G]

@[expose] def transvCent (A : Subgroup G) (d ζ : G) : Subgroup G :=
  transvGroup A d ⊓ centralizer ({ζ} : Set G)

theorem mem_transvCent {A : Subgroup G} {d ζ g : G} :
    g ∈ transvCent A d ζ ↔ IsTransv A d g ∧ g * ζ = ζ * g := by
  rw [transvCent, mem_inf, mem_transvGroup, mem_centralizer_singleton_iff]

theorem mem_centralizer_of_lam_gens {A : Subgroup G} {d a₁ c₁ g : G}
    (hA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hdA : d ∈ A) (ha₁ : a₁ ∈ A) (hc₁ : c₁ ∈ A)
    (hAgen : ∀ e ∈ A, ∃ i j k : ℤ, e = a₁ ^ i * c₁ ^ j * d ^ k) (hg : IsTransv A d g)
    (h1 : lam g a₁ = 1) (h2 : lam g c₁ = 1) : g ∈ centralizer (A : Set G) := by
  rw [mem_centralizer_iff_lam_eq_one]
  intro e he
  obtain ⟨i, j, k, rfl⟩ := hAgen e he
  have hxA : a₁ ^ i ∈ A := zpow_mem ha₁ i
  have hyA : c₁ ^ j ∈ A := zpow_mem hc₁ j
  have hzA : d ^ k ∈ A := zpow_mem hdA k
  have hdl : lam g d = 1 := by
    have := hg.cent
    simp only [lam]
    rw [this]
    group
  rw [lam_mul_right hA hdA hg (A.mul_mem hxA hyA) hzA, lam_mul_right hA hdA hg hxA hyA,
    lam_zpow_right hA hdA hg ha₁ i, lam_zpow_right hA hdA hg hc₁ j,
    lam_zpow_right hA hdA hg hdA k, h1, h2, hdl]
  simp

theorem zpow_eq_one_iff_dvd {p : ℕ} (hp : p.Prime) {d : G} (hdp : d ^ p = 1) (hd1 : d ≠ 1)
    (k : ℤ) : d ^ k = 1 ↔ (p : ℤ) ∣ k := by
  have : Fact p.Prime := ⟨hp⟩
  have := orderOf_eq_prime hdp hd1
  rw [← orderOf_dvd_iff_zpow_eq_one, this]

theorem exists_mul_sub_dvd {p : ℕ} (hp : p.Prime) (x y : ℤ) (hx : ¬ (p : ℤ) ∣ x)
    (hy : ¬ (p : ℤ) ∣ y) : ∃ m : ℤ, ¬ (p : ℤ) ∣ m ∧ (p : ℤ) ∣ m * x - y := by
  have : Fact p.Prime := ⟨hp⟩
  have hx0 : (x : ZMod p) ≠ 0 := fun h => hx ((ZMod.intCast_zmod_eq_zero_iff_dvd x p).mp h)
  have hy0 : (y : ZMod p) ≠ 0 := fun h => hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp h)
  refine ⟨(((y : ZMod p) / (x : ZMod p)).val : ℤ), ?_, ?_⟩
  · intro h
    have h' := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).mpr h
    push_cast at h'
    rw [ZMod.natCast_zmod_val] at h'
    exact (div_ne_zero hy0 hx0) h'
  · rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
    push_cast
    rw [ZMod.natCast_zmod_val]
    field_simp
    ring

theorem exists_add_mul_dvd {p : ℕ} (hp : p.Prime) (x y : ℤ) (hy : ¬ (p : ℤ) ∣ y) :
    ∃ j : ℤ, (p : ℤ) ∣ x + j * y := by
  have : Fact p.Prime := ⟨hp⟩
  have hy0 : (y : ZMod p) ≠ 0 := fun h => hy ((ZMod.intCast_zmod_eq_zero_iff_dvd y p).mp h)
  refine ⟨-(((x : ZMod p) / (y : ZMod p)).val : ℤ), ?_⟩
  rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
  push_cast
  rw [ZMod.natCast_zmod_val]
  field_simp
  ring

theorem false_of_transvection_types [Finite G] {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    {A : Subgroup G} (hAc : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) (hAp : ∀ x ∈ A, x ^ p = 1)
    {d a₁ c₁ ζ : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (ha₁ : a₁ ∈ A) (hc₁ : c₁ ∈ A)
    (hAgen : ∀ e ∈ A, ∃ i j k : ℤ, e = a₁ ^ i * c₁ ^ j * d ^ k)
    {m : ℕ} (hm : 1 ≤ m) (hζord : orderOf ζ = p ^ m) (hdζ : d ∈ zpowers ζ)
    (hAζ : ∀ x ∈ A, x * ζ = ζ * x)
    (hQ : ∀ w : G, (∀ x ∈ A, w * x = x * w) → w * ζ = ζ * w → (∃ k : ℕ, orderOf w = p ^ k) →
      ∃ α ∈ A, ∃ e : ℤ, w = α * ζ ^ e)
    (gc : G) (hgc : IsTransv A d gc) (hgcζ : gc * ζ = ζ * gc)
    (hgcord : orderOf gc = p ^ (m + 1)) (hgcp : gc ^ p ∈ zpowers ζ)
    (hgc1 : lam gc c₁ = 1) (hgc2 : lam gc a₁ ≠ 1)
    (gj : ℤ → G) (hgj : ∀ j, IsTransv A d (gj j)) (hgjζ : ∀ j, gj j * ζ = ζ * gj j)
    (hgjord : ∀ j, orderOf (gj j) = p ^ (m + 1)) (hgjp : ∀ j, gj j ^ p ∈ zpowers ζ)
    (hgj1 : ∀ j, lam (gj j) (a₁ * c₁ ^ j) = 1) (hgj2 : ∀ j, lam (gj j) c₁ ≠ 1) : False := by
  have : Fact p.Prime := ⟨hp⟩
  have hdp : d ^ p = 1 := hAp d hdA
  have hdz := zpow_eq_one_iff_dvd hp hdp hd1
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hZp : IsPGroup p (zpowers ζ) :=
    IsPGroup.of_card (n := m) (by rw [Nat.card_zpowers, hζord])
  have hζT : IsTransv A d ζ := by
    refine ⟨?_, (hAζ d hdA).symm, fun e he => ?_⟩
    · exact centralizer_le_normalizer _ (mem_centralizer_iff.mpr hAζ)
    · have := hAζ e he
      have h1 : lam ζ e = 1 := by
        simp only [lam]
        rw [← this]
        group
      rw [h1]
      exact one_mem _
  set GZ := transvCent A d ζ with hGZdef
  have hζGZ : ζ ∈ GZ := mem_transvCent.mpr ⟨hζT, rfl⟩
  have hGZζ : ∀ g ∈ GZ, g * ζ = ζ * g := fun g hg => (mem_transvCent.mp hg).2
  have hGZζz : ∀ g ∈ GZ, ∀ k : ℤ, g * ζ ^ k = ζ ^ k * g := fun g hg k =>
    (Commute.zpow_right (show Commute g ζ from hGZζ g hg) k).eq
  obtain ⟨T, hT⟩ := CFSG.ABGLocalTools.exists_isSylowOf p GZ
  have hTGZ : T ≤ GZ := hT.le
  have hTp : IsPGroup p T := hT.isPGroup
  have hTN : T ≤ normalizer (zpowers ζ : Set G) := fun t ht => by
    refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun h hh => ?_) 
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hh
    exact (hGZζz t (hTGZ ht) k).symm
  have hζT' : ζ ∈ T := by
    have hpg : IsPGroup p (T ⊔ zpowers ζ : Subgroup G) := hTp.to_sup_of_normal_right' hZp hTN
    have hle : T ⊔ zpowers ζ ≤ GZ := sup_le hTGZ (zpowers_le.mpr hζGZ)
    have heq : T ⊔ zpowers ζ = T := hT.eq_of_le le_sup_left hle hpg
    rw [← heq]
    exact mem_sup_right (mem_zpowers ζ)
  set Q : Subgroup G := T ⊓ centralizer (A : Set G) with hQdef
  have hQT : Q ≤ T := inf_le_left
  have hζQ : ζ ∈ Q := ⟨hζT', mem_centralizer_iff.mpr hAζ⟩
  have hQstruct : ∀ q ∈ Q, ∃ α ∈ A, ∃ e : ℤ, q = α * ζ ^ e := by
    intro q hq
    obtain ⟨hqT, hqC⟩ := hq
    refine hQ q (fun x hx => (mem_centralizer_iff.mp hqC x hx).symm) (hGZζ q (hTGZ hqT)) ?_
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hTp) ⟨q, hqT⟩
    exact ⟨k, by simpa using hk⟩
  have hAzc : ∀ α ∈ A, ∀ e : ℤ, α * ζ ^ e = ζ ^ e * α := fun α hα e =>
    (Commute.zpow_right (show Commute α ζ from hAζ α hα) e).eq
  have hQc : ∀ q ∈ Q, ∀ q' ∈ Q, q * q' = q' * q := by
    intro q hq q' hq'
    obtain ⟨α, hα, e, rfl⟩ := hQstruct q hq
    obtain ⟨α', hα', e', rfl⟩ := hQstruct q' hq'
    have h1 : Commute α α' := hAc α hα α' hα'
    have h2 : Commute α (ζ ^ e') := (hAzc α hα e')
    have h3 : Commute (ζ ^ e) α' := (hAzc α' hα' e).symm
    have h4 : Commute (ζ ^ e) (ζ ^ e') := Commute.zpow_zpow_self ζ e e'
    exact ((h1.mul_right h2).mul_left (h3.mul_right h4)).eq
  have hζz : ∀ t ∈ T, t * ζ = ζ * t := fun t ht => hGZζ t (hTGZ ht)
  have hTTq : ∀ s ∈ T, ∀ t ∈ T, s⁻¹ * t⁻¹ * s * t ∈ Q := by
    intro s hs t ht
    have hsT := (mem_transvCent.mp (hTGZ hs)).1
    have htT := (mem_transvCent.mp (hTGZ ht)).1
    have h := commutator_mem_centralizer hsT.inv htT.inv
    simp only [inv_inv] at h
    refine ⟨?_, h⟩
    exact T.mul_mem (T.mul_mem (T.mul_mem (T.inv_mem hs) (T.inv_mem ht)) hs) ht
  have hQT' : ∀ q ∈ Q, ∀ t ∈ T, q⁻¹ * t⁻¹ * q * t ∈ zpowers ζ := by
    intro q hq t ht
    obtain ⟨α, hα, e, rfl⟩ := hQstruct q hq
    have htT := (mem_transvCent.mp (hTGZ ht)).1
    have h1 := commutator_inv_mem_zpowers hAc hdA htT hα
    have h2 : (α * ζ ^ e)⁻¹ * t⁻¹ * (α * ζ ^ e) * t = α⁻¹ * t⁻¹ * α * t := by
      have c3 : Commute (ζ ^ e) α := (hAzc α hα e).symm
      have c1 : Commute (ζ ^ e) α⁻¹ := c3.inv_right
      have c2 : Commute (ζ ^ e) t⁻¹ := (hGZζz t⁻¹ (GZ.inv_mem (hTGZ ht)) e).symm
      have hX : Commute (ζ ^ e) (α⁻¹ * t⁻¹ * α) := (c1.mul_right c2).mul_right c3
      have hX' : α⁻¹ * t⁻¹ * α * ζ ^ e = ζ ^ e * (α⁻¹ * t⁻¹ * α) := hX.symm.eq
      calc (α * ζ ^ e)⁻¹ * t⁻¹ * (α * ζ ^ e) * t
          = (ζ ^ e)⁻¹ * ((α⁻¹ * t⁻¹ * α) * ζ ^ e) * t := by group
        _ = (ζ ^ e)⁻¹ * (ζ ^ e * (α⁻¹ * t⁻¹ * α)) * t := by rw [hX']
        _ = α⁻¹ * t⁻¹ * α * t := by rw [inv_mul_cancel_left]
    rw [h2]
    exact (zpowers_le.mpr hdζ) h1
  have hpζ : p ∣ orderOf ζ := by
    rw [hζord]
    exact dvd_pow_self p (by omega)
  have hexp : orderOf ζ = Monoid.exponent Q := by
    have h1 : orderOf ζ ∣ Monoid.exponent Q := by
      have := Monoid.order_dvd_exponent (⟨ζ, hζQ⟩ : Q)
      rwa [Subgroup.orderOf_mk] at this
    have h2 : Monoid.exponent Q ∣ orderOf ζ := by
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun q => ?_
      obtain ⟨α, hα, e, hq⟩ := hQstruct q q.2
      apply Subtype.ext
      show (q : G) ^ orderOf ζ = 1
      rw [hq, hζord]
      have hcomm : Commute α (ζ ^ e) := hAzc α hα e
      rw [hcomm.mul_pow]
      have h3 : α ^ (p ^ m) = 1 := by
        obtain ⟨m', rfl⟩ : ∃ m', m = m' + 1 := ⟨m - 1, by omega⟩
        rw [pow_succ', pow_mul, hAp α hα, one_pow]
      have h4 : (ζ ^ e) ^ (p ^ m) = 1 := by
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, ← hζord,
          pow_orderOf_eq_one, one_zpow]
      rw [h3, h4, one_mul]
    exact Nat.dvd_antisymm h1 h2
  have hconj : ∀ g : G, IsTransv A d g → g * ζ = ζ * g → g ^ p ∈ zpowers ζ →
      (∃ k : ℕ, orderOf g = p ^ k) → ∃ g' ∈ T, IsTransv A d g' ∧
        (∀ e ∈ A, lam g' e = lam g e) ∧ orderOf g' = orderOf g ∧ g' ^ p = g ^ p := by
    intro g hg hgζ hgp hgo
    have hgGZ : g ∈ GZ := mem_transvCent.mpr ⟨hg, hgζ⟩
    obtain ⟨h, hh, hhg⟩ := exists_conj_mem_of_isSylowOf hT hgGZ hgo
    have hhT : IsTransv A d h := (mem_transvCent.mp hh).1
    refine ⟨h * g * h⁻¹, hhg, (hhT.mul hg).mul hhT.inv, fun e he => lam_conj hg hhT he, ?_, ?_⟩
    · have := CFSG.RankThree.PGroups.orderOf_inv_mul_mul h⁻¹ g
      simpa using this
    · obtain ⟨e, he⟩ := mem_zpowers_iff.mp hgp
      rw [conj_pow, ← he]
      have := hGZζz h hh e
      rw [this]
      group
  obtain ⟨g₁, hg₁T, hg₁, hg₁lam, hg₁ord, hg₁p⟩ :=
    hconj (gj 0) (hgj 0) (hgjζ 0) (hgjp 0) ⟨m + 1, hgjord 0⟩
  obtain ⟨g₂, hg₂T, hg₂, hg₂lam, hg₂ord, hg₂p⟩ :=
    hconj gc hgc hgcζ hgcp ⟨m + 1, hgcord⟩
  have hcoord : ∀ g : G, IsTransv A d g → ∀ e ∈ A, ∃ k : ℤ, lam g e = d ^ k := fun g hg e he => by
    obtain ⟨k, hk⟩ := mem_zpowers_iff.mp (hg.comm e he)
    exact ⟨k, hk.symm⟩
  have hnd : ∀ k : ℤ, ¬ (p : ℤ) ∣ k → d ^ k ≠ 1 := fun k hk h => hk ((hdz k).mp h)
  obtain ⟨α₂, hα₂⟩ := hcoord gc hgc a₁ ha₁
  have hα₂' : ¬ (p : ℤ) ∣ α₂ := fun h => hgc2 (by rw [hα₂, (hdz α₂).mpr h])
  obtain ⟨γ₁, hγ₁⟩ := hcoord (gj 0) (hgj 0) c₁ hc₁
  have hγ₁' : ¬ (p : ℤ) ∣ γ₁ := fun h => hgj2 0 (by rw [hγ₁, (hdz γ₁).mpr h])
  have hg₁a : lam g₁ a₁ = 1 := by
    rw [hg₁lam a₁ ha₁]
    have := hgj1 0
    simpa using this
  have hg₁c : lam g₁ c₁ = d ^ γ₁ := by rw [hg₁lam c₁ hc₁, hγ₁]
  have hg₂c : lam g₂ c₁ = 1 := by rw [hg₂lam c₁ hc₁, hgc1]
  have hg₂a : lam g₂ a₁ = d ^ α₂ := by rw [hg₂lam a₁ ha₁, hα₂]
  have hind : ∀ k₁ k₂ : ℤ, g₁ ^ k₁ * g₂ ^ k₂ ∈ Q → (p : ℤ) ∣ k₁ ∧ (p : ℤ) ∣ k₂ := by
    intro k₁ k₂ hk
    have hC := (mem_centralizer_iff_lam_eq_one.mp hk.2)
    have hg₁z : IsTransv A d (g₁ ^ k₁) := mem_transvGroup.mp ((transvGroup A d).zpow_mem
      (mem_transvGroup.mpr hg₁) k₁)
    have hg₂z : IsTransv A d (g₂ ^ k₂) := mem_transvGroup.mp ((transvGroup A d).zpow_mem
      (mem_transvGroup.mpr hg₂) k₂)
    have hl : ∀ e ∈ A, (lam g₂ e) ^ k₂ * (lam g₁ e) ^ k₁ = 1 := by
      intro e he
      have := hC e he
      rwa [lam_mul_eq hg₁z hg₂z he, lam_zpow hg₂ he, lam_zpow hg₁ he] at this
    have h1 := hl a₁ ha₁
    rw [hg₂a, hg₁a, one_zpow, mul_one, ← zpow_mul, hdz] at h1
    have h2 := hl c₁ hc₁
    rw [hg₂c, hg₁c, one_zpow, one_mul, ← zpow_mul, hdz] at h2
    refine ⟨?_, ?_⟩
    · rcases hpz.dvd_or_dvd h2 with h | h
      · exact absurd h hγ₁'
      · exact h
    · rcases hpz.dvd_or_dvd h1 with h | h
      · exact absurd h hα₂'
      · exact h
  have hexpQ : Monoid.exponent Q = p ^ m := by rw [← hexp, hζord]
  have hfull : ∀ t ∈ T, t ∉ Q → ∃ m' : ℤ, ¬ (p : ℤ) ∣ m' ∧ ∃ z ∈ Q,
      orderOf (t ^ m' * z) = p * Monoid.exponent Q := by
    intro t htT htQ
    have htT' := (mem_transvCent.mp (hTGZ htT)).1
    obtain ⟨α, hα⟩ := hcoord t htT' a₁ ha₁
    obtain ⟨γ, hγ⟩ := hcoord t htT' c₁ hc₁
    have hαγ : ¬ ((p : ℤ) ∣ α ∧ (p : ℤ) ∣ γ) := by
      rintro ⟨h1, h2⟩
      apply htQ
      refine ⟨htT, mem_centralizer_of_lam_gens hAc hdA ha₁ hc₁ hAgen htT' ?_ ?_⟩
      · rw [hα]
        exact (hdz α).mpr h1
      · rw [hγ]
        exact (hdz γ).mpr h2
    have key : ∀ g ∈ T, IsTransv A d g → ∀ α' γ' : ℤ, lam g a₁ = d ^ α' → lam g c₁ = d ^ γ' →
        orderOf g = p ^ (m + 1) → ∀ m' : ℤ, (p : ℤ) ∣ m' * α - α' → (p : ℤ) ∣ m' * γ - γ' →
        ¬ (p : ℤ) ∣ m' → ∃ m'' : ℤ, ¬ (p : ℤ) ∣ m'' ∧ ∃ z ∈ Q,
          orderOf (t ^ m'' * z) = p * Monoid.exponent Q := by
      intro g hgT hg α' γ' hα' hγ' hgo m' h1 h2 hm'
      have htz : t ^ m' ∈ transvGroup A d :=
        (transvGroup A d).zpow_mem (mem_transvGroup.mpr htT') m'
      have htz' : IsTransv A d (t ^ m') := mem_transvGroup.mp htz
      have hzT : IsTransv A d ((t ^ m')⁻¹ * g) :=
        mem_transvGroup.mp (mul_mem (inv_mem htz) (mem_transvGroup.mpr hg))
      refine ⟨m', hm', (t ^ m')⁻¹ * g, ⟨T.mul_mem (T.inv_mem (T.zpow_mem htT m')) hgT, ?_⟩, ?_⟩
      · refine mem_centralizer_of_lam_gens hAc hdA ha₁ hc₁ hAgen hzT ?_ ?_
        · rw [lam_mul_eq (htz'.inv) hg ha₁, lam_inv_eq htz' ha₁, lam_zpow htT' ha₁, hα', hα,
            ← zpow_mul, ← zpow_neg, ← zpow_add, hdz]
          have : α' + -(α * m') = -(m' * α - α') := by ring
          rw [this]
          exact (dvd_neg).mpr h1
        · rw [lam_mul_eq (htz'.inv) hg hc₁, lam_inv_eq htz' hc₁, lam_zpow htT' hc₁, hγ', hγ,
            ← zpow_mul, ← zpow_neg, ← zpow_add, hdz]
          have : γ' + -(γ * m') = -(m' * γ - γ') := by ring
          rw [this]
          exact (dvd_neg).mpr h2
      · have : t ^ m' * ((t ^ m')⁻¹ * g) = g := by group
        rw [this, hgo, hexpQ, pow_succ']
    by_cases hγp : (p : ℤ) ∣ γ
    ·
      have hαp : ¬ (p : ℤ) ∣ α := fun h => hαγ ⟨h, hγp⟩
      obtain ⟨m', hm', hdiv⟩ := exists_mul_sub_dvd hp α α₂ hαp hα₂'
      refine key g₂ hg₂T hg₂ α₂ 0 ?_ ?_ (by rw [hg₂ord, hgcord]) m' hdiv ?_ hm'
      · rw [hg₂lam a₁ ha₁, hα₂]
      · rw [hg₂lam c₁ hc₁, hgc1, zpow_zero]
      · simpa using hγp.mul_left m'
    · obtain ⟨j, hj⟩ := exists_add_mul_dvd hp α γ hγp
      obtain ⟨g', hg'T, hg', hg'lam, hg'ord, -⟩ :=
        hconj (gj j) (hgj j) (hgjζ j) (hgjp j) ⟨m + 1, hgjord j⟩
      obtain ⟨α', hα'⟩ := hcoord (gj j) (hgj j) a₁ ha₁
      obtain ⟨γ', hγ'⟩ := hcoord (gj j) (hgj j) c₁ hc₁
      have hγ'p : ¬ (p : ℤ) ∣ γ' := fun h => hgj2 j (by rw [hγ', (hdz γ').mpr h])
      have hrel : (p : ℤ) ∣ α' + j * γ' := by
        have h1 := hgj1 j
        rw [lam_mul_right hAc hdA (hgj j) ha₁ (zpow_mem hc₁ j),
          lam_zpow_right hAc hdA (hgj j) hc₁ j,
          hα', hγ', ← zpow_mul, ← zpow_add, hdz] at h1
        have : α' + γ' * j = α' + j * γ' := by ring
        rw [this] at h1
        exact h1
      obtain ⟨m', hm', hdiv⟩ := exists_mul_sub_dvd hp γ γ' hγp hγ'p
      refine key g' hg'T hg' α' γ' ?_ ?_ (by rw [hg'ord, hgjord j]) m' ?_ hdiv hm'
      · rw [hg'lam a₁ ha₁, hα']
      · rw [hg'lam c₁ hc₁, hγ']
      ·
        have e : m' * α - α' = m' * (α + j * γ) - j * (m' * γ - γ') - (α' + j * γ') := by ring
        rw [e]
        exact dvd_sub (dvd_sub (dvd_mul_of_dvd_right hj _) (dvd_mul_of_dvd_right hdiv _)) hrel
  have hge₁ : ∃ e₁ : ℤ, g₁ ^ p = ζ ^ e₁ := by
    obtain ⟨e, he⟩ := mem_zpowers_iff.mp (hg₁p ▸ hgjp 0)
    exact ⟨e, he.symm⟩
  have hge₂ : ∃ e₂ : ℤ, g₂ ^ p = ζ ^ e₂ := by
    obtain ⟨e, he⟩ := mem_zpowers_iff.mp (hg₂p ▸ hgcp)
    exact ⟨e, he.symm⟩
  obtain ⟨e₁, he₁⟩ := hge₁
  obtain ⟨e₂, he₂⟩ := hge₂
  exact false_of_symmetric_types hp hp5 T Q ζ hQT hζQ hQc hζz hTTq hQT' g₁ g₂ hg₁T hg₂T hind
    e₁ e₂ he₁ he₂ hpζ hexp hfull

end CFSG.RankThree.PartOne

module

public import CFSG.Walter.W67.Section5.P56AbHall

public section

namespace CFSG.Walter.W67

open P56Ab

namespace P56AbData

variable {G : Type} [Group G] [Finite G] (d : P56AbData G)

theorem mem_of_isPGroup_of_le_normalizer {A : Type} [Group A] [Finite A] {p : ℕ} [Fact p.Prime]
    {N Q : Subgroup A} (hQN : Q ≤ N) (hQp : IsPGroup p Q)
    (hQcard : (Nat.card Q).factorization p = (Nat.card N).factorization p) {g : A} (hgN : g ∈ N)
    (hgQ : g ∈ Subgroup.normalizer (Q : Set A)) (hg : ∃ k : ℕ, g ^ (p ^ k) = 1) : g ∈ Q := by
  have hZ : IsPGroup p (Subgroup.zpowers g) := by
    obtain ⟨k, hk⟩ := hg
    exact IsPGroup.of_card_dvd_pow (n := k) (by
      rw [Nat.card_zpowers]
      exact orderOf_dvd_of_pow_eq_one hk)
  have hQZ : IsPGroup p (Q ⊔ Subgroup.zpowers g : Subgroup A) :=
    hQp.to_sup_of_normal_left' hZ (Subgroup.zpowers_le.mpr hgQ)
  have hle : Q ⊔ Subgroup.zpowers g ≤ N := sup_le hQN (Subgroup.zpowers_le.mpr hgN)
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hQZ
  have hdvd : Nat.card (Q ⊔ Subgroup.zpowers g : Subgroup A) ∣ Nat.card N :=
    Subgroup.card_dvd_of_le hle
  rw [hk] at hdvd
  have hk' := (Nat.Prime.pow_dvd_iff_le_factorization Fact.out Nat.card_pos.ne').mp hdvd
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQp
  have hQeq : Q = Q ⊔ Subgroup.zpowers g := by
    apply Subgroup.eq_of_le_of_card_ge le_sup_left
    rw [hk, hj]
    rw [hj, Nat.Prime.factorization_pow Fact.out, Finsupp.single_eq_same] at hQcard
    exact Nat.pow_le_pow_right (Fact.out : p.Prime).pos (by omega)
  rw [hQeq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers g)

section complement

variable {Q : Subgroup (MulAut d.V)} (hQK : Q ≤ d.Kbar) (hQp : IsPGroup 3 Q)
  (hQcard : (Nat.card Q).factorization 3 = (Nat.card d.Nbar).factorization 3)
  (hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
  (hQsmall : ∀ E : Subgroup (MulAut d.V), E ≤ Q → (∀ x ∈ E, x ^ 3 = 1) → Nat.card E ≤ 3 ^ 2)
include hQK hQp hQcard hQcomm hQsmall

theorem comm_of_mem_normalizer {g : MulAut d.V} (hgK : g ∈ d.Kbar)
    (hgQ : g ∈ Subgroup.normalizer (Q : Set (MulAut d.V))) : ∀ q ∈ Q, g * q = q * g := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hgodd : Odd (orderOf g) := by
    have h1 : orderOf g ∣ Nat.card d.Kbar := by
      rw [← Subgroup.orderOf_mk g hgK]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat d.odd_card_Kbar h1
  obtain ⟨k, m', hm', hm⟩ := Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos g).ne' 3 (by norm_num)
  set C := Subgroup.centralizer (Q : Set (MulAut d.V)) with hC
  have h3 : g ^ m' ∈ C := by
    have hmem : g ^ m' ∈ Q := mem_of_isPGroup_of_le_normalizer (hQK.trans d.Kbar_le_Nbar) hQp
      hQcard (d.Kbar_le_Nbar (d.Kbar.pow_mem hgK m')) (Subgroup.pow_mem _ hgQ m')
      ⟨k, by rw [← pow_mul, mul_comm, ← hm, pow_orderOf_eq_one]⟩
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact hQcomm q hq _ hmem
  have h3' : g ^ (3 ^ k) ∈ C := by
    set g' := g ^ (3 ^ k) with hg'
    have hg'Q : g' ∈ Subgroup.normalizer (Q : Set (MulAut d.V)) := Subgroup.pow_mem _ hgQ _
    have hog' : orderOf g' ∣ m' := by
      apply orderOf_dvd_of_pow_eq_one
      rw [hg', ← pow_mul, ← hm, pow_orderOf_eq_one]
    have hcop6 : Nat.Coprime (orderOf g') 6 := by
      have hm'odd : Odd m' := Odd.of_dvd_nat hgodd (Dvd.intro_left _ hm.symm)
      have h2 : Nat.Coprime m' 2 := (Nat.coprime_two_right).mpr hm'odd
      have h3 : Nat.Coprime m' 3 := (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm' |>.symm
      exact Nat.Coprime.coprime_dvd_left hog' (Nat.Coprime.mul_right h2 h3)
    let W : Subgroup (MulAut d.V) :=
      { carrier := {w | w ∈ Q ∧ w ^ 3 = 1}
        one_mem' := ⟨Q.one_mem, one_pow _⟩
        mul_mem' := by
          rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
          exact ⟨Q.mul_mem ha hb, by
            rw [(Commute.mul_pow (hQcomm a ha b hb) 3), ha', hb', one_mul]⟩
        inv_mem' := by
          rintro a ⟨ha, ha'⟩
          exact ⟨Q.inv_mem ha, by rw [inv_pow, ha', inv_one]⟩ }
    have hWQ : W ≤ Q := fun _ hw => hw.1
    have hg'W : g' ∈ Subgroup.normalizer (W : Set (MulAut d.V)) := by
      apply Sec53.mem_normalizer_of_conj_le
      rintro w ⟨hw, hw'⟩
      exact ⟨(Subgroup.mem_normalizer_iff.mp hg'Q w).mp hw, by
        rw [conj_pow, hw', mul_one, mul_inv_cancel]⟩
    have hordconj : ∀ {Y : Subgroup (MulAut d.V)} (hY : g' ∈ Subgroup.normalizer (Y : Set _)),
        orderOf (conjOf hY) ∣ orderOf g' := by
      intro Y hY
      have := orderOf_map_dvd (conjAut (Subgroup.zpowers g') Y (Subgroup.zpowers_le.mpr hY))
        ⟨g', Subgroup.mem_zpowers _⟩
      rwa [Subgroup.orderOf_mk] at this
    have hβ : conjOf hg'W = 1 := eq_one_of_coprime_six
      (fun a b => Subtype.ext (hQcomm a (hWQ a.2) b (hWQ b.2)))
      (fun w => Subtype.ext (by simpa using w.2.2))
      (hQsmall W hWQ (fun x hx => hx.2)) _
      (Nat.Coprime.coprime_dvd_left (hordconj hg'W) hcop6)
    have hα : conjOf hg'Q = 1 := by
      apply eq_one_of_forall_pow_eq_one (p := 3) hQp
        (fun a b => Subtype.ext (hQcomm a a.2 b b.2))
      · exact Nat.Coprime.coprime_dvd_left (hordconj hg'Q)
          (Nat.Coprime.coprime_dvd_right (by norm_num : 3 ∣ 6) hcop6)
      · intro x hx
        have hxW : (x : MulAut d.V) ∈ W := ⟨x.2, by simpa using congrArg Subtype.val hx⟩
        have := congrArg (fun β : MulAut W => ((β ⟨_, hxW⟩ : W) : MulAut d.V)) hβ
        exact Subtype.ext this
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have h1 := congrArg (fun β : MulAut Q => ((β ⟨q, hq⟩ : Q) : MulAut d.V)) hα
    have h2 : g' * q * g'⁻¹ = q := h1
    calc q * g' = g' * q * g'⁻¹ * g' := by rw [h2]
      _ = g' * q := by group
  have hcop : Nat.Coprime m' (3 ^ k) :=
    Nat.Coprime.pow_right k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hm').symm
  have hgC : g ∈ C := by
    have hgcd := Nat.gcd_eq_gcd_ab m' (3 ^ k)
    rw [hcop] at hgcd
    have : g = (g ^ m') ^ (Nat.gcdA m' (3 ^ k)) * (g ^ (3 ^ k)) ^ (Nat.gcdB m' (3 ^ k)) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_mul, ← zpow_add, ← hgcd]
      simp
    rw [this]
    exact C.mul_mem (C.zpow_mem h3 _) (C.zpow_mem h3' _)
  intro q hq
  exact (Subgroup.mem_centralizer_iff.mp hgC q hq).symm

theorem exists_complement :
    ∃ R : Subgroup (MulAut d.V), R ≤ d.Kbar ∧
      (∀ x ∈ d.Kbar, Nat.Coprime 3 (orderOf x) → x ∈ R) ∧
      (∀ k ∈ d.Kbar, ∃ r ∈ R, ∃ q ∈ Q, r * q = k) ∧ R ⊓ Q = ⊥ ∧
      d.Jbar ∈ Subgroup.normalizer (R : Set (MulAut d.V)) ∧
      d.Kbar ≤ Subgroup.normalizer (R : Set (MulAut d.V)) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hQp
  have hcardS : Nat.card (Q.subgroupOf d.Kbar) = 3 ^ (Nat.card d.Kbar).factorization 3 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hQK).toEquiv, d.factorization_three_Kbar,
      ← hQcard]
    rw [hj, Nat.Prime.factorization_pow Nat.prime_three, Finsupp.single_eq_same]
  set S : Sylow 3 d.Kbar := Sylow.ofCard _ hcardS with hSdef
  have hP : Subgroup.normalizer ((S : Subgroup d.Kbar) : Set d.Kbar) ≤
      Subgroup.centralizer ((S : Subgroup d.Kbar) : Set d.Kbar) := by
    intro g hg
    have hgQ : (g : MulAut d.V) ∈ Subgroup.normalizer (Q : Set (MulAut d.V)) := by
      apply Sec53.mem_normalizer_of_conj_le
      intro x hx
      have hxS : (⟨x, hQK hx⟩ : d.Kbar) ∈ (S : Subgroup d.Kbar) := hx
      have := (Subgroup.mem_normalizer_iff.mp hg _).mp hxS
      exact this
    have hcomm := d.comm_of_mem_normalizer hQK hQp hQcard hQcomm hQsmall g.2 hgQ
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    exact Subtype.ext (hcomm _ hh).symm
  obtain ⟨K₀, hK₀n, hK₀3, hK₀idx, -, hK₀char, hcomp, hsup, hinf, -, -⟩ :=
    GroupTheory.burnside_normal_complement S hP
  refine ⟨K₀.map d.Kbar.subtype, Subgroup.map_subtype_le _, ?_, ?_, ?_, ?_, ?_⟩
  ·
    intro x hx hcop
    have hq : ((⟨x, hx⟩ : d.Kbar) : d.Kbar ⧸ K₀) = 1 := by
      have h1 : orderOf ((⟨x, hx⟩ : d.Kbar) : d.Kbar ⧸ K₀) ∣ orderOf x := by
        rw [← Subgroup.orderOf_mk x hx]
        exact orderOf_map_dvd (QuotientGroup.mk' K₀) _
      have h2 : orderOf ((⟨x, hx⟩ : d.Kbar) : d.Kbar ⧸ K₀) ∣ Nat.card (d.Kbar ⧸ K₀) :=
        orderOf_dvd_natCard _
      rw [← Subgroup.index, hK₀idx, Sylow.card_eq_multiplicity] at h2
      have h3 : Nat.Coprime (3 ^ (Nat.card d.Kbar).factorization 3) (orderOf x) :=
        Nat.Coprime.pow_left _ hcop
      exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes h3 h2 h1)
    rw [QuotientGroup.eq_one_iff] at hq
    exact ⟨_, hq, rfl⟩
  ·
    intro k hk
    have hkt : (⟨k, hk⟩ : d.Kbar) ∈ K₀ ⊔ (S : Subgroup d.Kbar) := by rw [hsup]; trivial
    obtain ⟨r, hr, q, hq, hrq⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := K₀) (t := (S : Subgroup d.Kbar))).mp hkt
    exact ⟨r, ⟨r, hr, rfl⟩, q, hq, congrArg Subtype.val hrq⟩
  ·
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨⟨r, hr, rfl⟩, hxQ⟩ := Subgroup.mem_inf.mp hx
    have : r ∈ K₀ ⊓ (S : Subgroup d.Kbar) := Subgroup.mem_inf.mpr ⟨hr, hxQ⟩
    rw [hinf, Subgroup.mem_bot] at this
    rw [this]
    exact Subgroup.one_mem _
  · exact mem_normalizer_map_of_characteristic hK₀char
      (d.Nbar_le_normalizer_Kbar d.Jbar_mem_Nbar)
  · exact le_normalizer_map_of_normal hK₀n

end complement

theorem eq_of_ne_one_of_card_le_two {A : Type*} [Group A] [Finite A] (hA : Nat.card A ≤ 2)
    {a b : A} (ha : a ≠ 1) (hb : b ≠ 1) : a = b := by
  by_contra hab
  classical
  have : Fintype A := Fintype.ofFinite A
  have h3 : ({1, a, b} : Finset A).card = 3 := by
    rw [Finset.card_insert_of_notMem (by simp [Ne.symm ha, Ne.symm hb]),
      Finset.card_pair hab]
  have := Finset.card_le_univ ({1, a, b} : Finset A)
  rw [h3, ← Nat.card_eq_fintype_card] at this
  omega

theorem mem_Kbar_or_mul_Jbar_mem {h : MulAut d.V} (hh : h ∈ d.Nbar) :
    h ∈ d.Kbar ∨ h * d.Jbar ∈ d.Kbar := by
  obtain ⟨S, hS, hS2⟩ := d.exists_sylow_two_Nbar
  have hcs := cyclic_sylow_normal_odd_complement S hS
  set K := pPrimeCore 2 d.Nbar
  have hKn : K.Normal := hcs.2.2.2.1.1
  have hidx : K.index = Nat.card S := hcs.2.2.2.1.2.2.1
  have hcard : Nat.card (d.Nbar ⧸ K) ≤ 2 := by rw [← Subgroup.index, hidx]; exact hS2
  by_cases h1 : h ∈ d.Kbar
  · exact Or.inl h1
  · right
    have hJ : ((⟨d.Jbar, d.Jbar_mem_Nbar⟩ : d.Nbar) : d.Nbar ⧸ K)⁻¹ ≠ 1 := by
      rw [inv_ne_one, Ne, QuotientGroup.eq_one_iff]
      intro hJK
      exact d.Jbar_not_mem_Kbar ⟨_, hJK, rfl⟩
    have hh' : ((⟨h, hh⟩ : d.Nbar) : d.Nbar ⧸ K) ≠ 1 := by
      rw [Ne, QuotientGroup.eq_one_iff]
      intro hK
      exact h1 ⟨_, hK, rfl⟩
    have heq := eq_of_ne_one_of_card_le_two hcard hh' hJ
    have : ((⟨h, hh⟩ * ⟨d.Jbar, d.Jbar_mem_Nbar⟩ : d.Nbar) : d.Nbar ⧸ K) = 1 := by
      rw [QuotientGroup.mk_mul, heq, inv_mul_cancel]
    rw [QuotientGroup.eq_one_iff] at this
    exact ⟨_, this, rfl⟩

theorem exists_conj_Jbar {g : MulAut d.V} (hg : g ∈ d.Nbar) (hog : orderOf g = 2) :
    ∃ h ∈ d.Nbar, h * d.Jbar * h⁻¹ = g := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set J₁ : d.Nbar := ⟨d.Jbar, d.Jbar_mem_Nbar⟩
  set J₂ : d.Nbar := ⟨g, hg⟩
  have hoJ₁ : orderOf J₁ = 2 := by rw [Subgroup.orderOf_mk, d.orderOf_Jbar]
  have hoJ₂ : orderOf J₂ = 2 := by rw [Subgroup.orderOf_mk, hog]
  have hS : ∀ y : d.Nbar, orderOf y = 2 →
      ∃ S : Sylow 2 d.Nbar, (S : Subgroup d.Nbar) = Subgroup.zpowers y := by
    intro y hy
    have hp : IsPGroup 2 (Subgroup.zpowers y) := by
      apply IsPGroup.of_card (n := 1)
      rw [Nat.card_zpowers, hy, pow_one]
    obtain ⟨S, hSle⟩ := hp.exists_le_sylow
    refine ⟨S, ?_⟩
    symm
    apply Subgroup.eq_of_le_of_card_ge hSle
    rw [Nat.card_zpowers, hy]
    have := d.card_le_two_of_le_Nbar (Subgroup.map_subtype_le (S : Subgroup d.Nbar))
      (S.isPGroup'.map _)
    rwa [Subgroup.card_map_of_injective d.Nbar.subtype_injective] at this
  obtain ⟨S₁, hS₁⟩ := hS J₁ hoJ₁
  obtain ⟨S₂, hS₂⟩ := hS J₂ hoJ₂
  obtain ⟨x, hx⟩ := MulAction.exists_smul_eq d.Nbar S₁ S₂
  have hmem : x * J₁ * x⁻¹ ∈ Subgroup.zpowers J₂ := by
    rw [← hS₂, ← hx, Sylow.coe_subgroup_smul, hS₁]
    exact ⟨J₁, Subgroup.mem_zpowers J₁, rfl⟩
  rcases eq_one_or_eq_of_mem_zpowers hoJ₂ hmem with h1 | h1
  · exfalso
    have : J₁ = 1 := by
      have := congrArg (fun z => x⁻¹ * z * x) h1
      simpa [mul_assoc] using this
    rw [this, orderOf_one] at hoJ₁
    exact absurd hoJ₁ (by norm_num)
  · exact ⟨x, x.2, by simpa using congrArg Subtype.val h1⟩

@[expose] def Dbar (Q : Subgroup (MulAut d.V)) (hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) :
    Subgroup (MulAut d.V) where
  carrier := {q | q ∈ Q ∧ d.Jbar * q * d.Jbar⁻¹ = q⁻¹}
  one_mem' := ⟨Q.one_mem, by group⟩
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨Q.mul_mem ha hb, ?_⟩
    calc d.Jbar * (a * b) * d.Jbar⁻¹ = (d.Jbar * a * d.Jbar⁻¹) * (d.Jbar * b * d.Jbar⁻¹) := by
          group
      _ = a⁻¹ * b⁻¹ := by rw [ha', hb']
      _ = (a * b)⁻¹ := by rw [mul_inv_rev, hQcomm _ (Q.inv_mem hb) _ (Q.inv_mem ha)]
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨Q.inv_mem ha, ?_⟩
    calc d.Jbar * a⁻¹ * d.Jbar⁻¹ = (d.Jbar * a * d.Jbar⁻¹)⁻¹ := by group
      _ = a⁻¹⁻¹ := by rw [ha']

section X

variable {Q R : Subgroup (MulAut d.V)} (hQK : Q ≤ d.Kbar) (hQp : IsPGroup 3 Q)
  (hJQ : Subgroup.zpowers d.Jbar ≤ Subgroup.normalizer (Q : Set (MulAut d.V)))
  (hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a)
  (hRK : R ≤ d.Kbar) (hR3 : ∀ x ∈ d.Kbar, Nat.Coprime 3 (orderOf x) → x ∈ R)
  (hKRQ : ∀ k ∈ d.Kbar, ∃ r ∈ R, ∃ q ∈ Q, r * q = k) (hRQ : R ⊓ Q = ⊥)
  (hJR : d.Jbar ∈ Subgroup.normalizer (R : Set (MulAut d.V)))
  (hKR : d.Kbar ≤ Subgroup.normalizer (R : Set (MulAut d.V)))

noncomputable abbrev Xbar (Q R : Subgroup (MulAut d.V))
    (hQcomm : ∀ a ∈ Q, ∀ b ∈ Q, a * b = b * a) : Subgroup (MulAut d.V) :=
  (R ⊔ d.Dbar Q hQcomm) ⊔ Subgroup.zpowers d.Jbar

include hJQ hKRQ in
theorem mem_X_of_orderOf_two {g : MulAut d.V} (hg : g ∈ d.Nbar) (hog : orderOf g = 2) :
    g ∈ d.Xbar Q R hQcomm := by
  obtain ⟨h, hh, rfl⟩ := d.exists_conj_Jbar hg hog
  obtain ⟨k, hk, hkeq⟩ : ∃ k ∈ d.Kbar, k * d.Jbar * k⁻¹ = h * d.Jbar * h⁻¹ := by
    rcases d.mem_Kbar_or_mul_Jbar_mem hh with h1 | h1
    · exact ⟨h, h1, rfl⟩
    · refine ⟨h * d.Jbar, h1, ?_⟩
      have := d.Jbar_mul_Jbar
      calc h * d.Jbar * d.Jbar * (h * d.Jbar)⁻¹ = h * (d.Jbar * d.Jbar) * d.Jbar⁻¹ * h⁻¹ := by
            group
        _ = h * d.Jbar * h⁻¹ := by rw [this, mul_one, d.Jbar_inv]
  rw [← hkeq]
  obtain ⟨r, hr, q, hq, rfl⟩ := hKRQ k hk
  have hJq : d.Jbar * q⁻¹ * d.Jbar⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hJQ (Subgroup.mem_zpowers _)) _).mp (Q.inv_mem hq)
  have hδ : q * (d.Jbar * q⁻¹ * d.Jbar⁻¹) ∈ d.Dbar Q hQcomm := by
    refine ⟨Q.mul_mem hq hJq, ?_⟩
    have hJJ : d.Jbar⁻¹ * d.Jbar⁻¹ = 1 := by rw [d.Jbar_inv, d.Jbar_mul_Jbar]
    calc d.Jbar * (q * (d.Jbar * q⁻¹ * d.Jbar⁻¹)) * d.Jbar⁻¹ =
          (d.Jbar * q * d.Jbar⁻¹) * (d.Jbar * d.Jbar) * q⁻¹ * (d.Jbar⁻¹ * d.Jbar⁻¹) := by group
      _ = (d.Jbar * q * d.Jbar⁻¹) * q⁻¹ := by rw [d.Jbar_mul_Jbar, hJJ]; group
      _ = (q * (d.Jbar * q⁻¹ * d.Jbar⁻¹))⁻¹ := by group
  have : r * q * d.Jbar * (r * q)⁻¹ =
      r * (q * (d.Jbar * q⁻¹ * d.Jbar⁻¹)) * d.Jbar * r⁻¹ := by group
  rw [this]
  have hrX : r ∈ d.Xbar Q R hQcomm := Subgroup.mem_sup_left (Subgroup.mem_sup_left hr)
  exact (d.Xbar Q R hQcomm).mul_mem ((d.Xbar Q R hQcomm).mul_mem
    ((d.Xbar Q R hQcomm).mul_mem hrX (Subgroup.mem_sup_left (Subgroup.mem_sup_right hδ)))
    (Subgroup.mem_sup_right (Subgroup.mem_zpowers _))) ((d.Xbar Q R hQcomm).inv_mem hrX)

include hJQ hKRQ hR3 in
theorem mem_X_of_coprime {g : MulAut d.V} (hg : g ∈ d.Nbar) (hcop : Nat.Coprime 3 (orderOf g)) :
    g ∈ d.Xbar Q R hQcomm := by
  rcases Nat.even_or_odd (orderOf g) with heven | hodd
  ·
    have hdvd : orderOf g ∣ Nat.card d.Nbar := by
      rw [← Subgroup.orderOf_mk g hg]
      exact orderOf_dvd_natCard _
    obtain ⟨m', hm'⟩ := heven
    have hm'odd : Odd m' := by
      by_contra hev
      rw [Nat.not_odd_iff_even] at hev
      obtain ⟨t, ht⟩ := hev
      have h4 : 2 ^ 2 ∣ Nat.card d.Nbar := by
        refine Dvd.dvd.trans ⟨t, ?_⟩ hdvd
        rw [hm', ht]
        ring
      have := (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_two Nat.card_pos.ne').mp h4
      have := d.factorization_two_Nbar
      omega
    have hm : orderOf g = 2 * m' := by rw [hm']; ring
    have hg2 : orderOf (g ^ m') = 2 := by
      rw [orderOf_pow' g hm'odd.pos.ne', hm, Nat.gcd_mul_left_left]
      have hpos : 0 < m' := hm'odd.pos
      rw [Nat.mul_div_cancel _ hpos]
    have hX1 := d.mem_X_of_orderOf_two (hJQ := hJQ) (hKRQ := hKRQ) (hQcomm := hQcomm)
      (d.Nbar.pow_mem hg m') hg2
    have hgsq : g ^ 2 ∈ R := by
      have hosq : orderOf (g ^ 2) ∣ m' := by
        apply orderOf_dvd_of_pow_eq_one
        rw [← pow_mul, ← hm, pow_orderOf_eq_one]
      apply hR3 _ (d.mem_Kbar_of_odd (d.Nbar.pow_mem hg 2) (Odd.of_dvd_nat hm'odd hosq))
      exact Nat.Coprime.coprime_dvd_right (hosq.trans (Dvd.intro_left 2 hm.symm)) hcop
    obtain ⟨t, ht⟩ := hm'odd
    have : g = g ^ m' * (g ^ 2) ^ (-(t : ℤ)) := by
      rw [← zpow_natCast, ← zpow_natCast, ← zpow_mul, ← zpow_add, ht]
      push_cast
      ring_nf
      rw [zpow_one]
    rw [this]
    exact (d.Xbar Q R hQcomm).mul_mem hX1
      ((d.Xbar Q R hQcomm).zpow_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left hgsq)) _)
  · exact Subgroup.mem_sup_left (Subgroup.mem_sup_left (hR3 g (d.mem_Kbar_of_odd hg hodd) hcop))

include hQK hQp hJQ hRK hRQ hJR hKR in
theorem eq_one_of_mem_X {y : MulAut d.V} (hyX : y ∈ d.Xbar Q R hQcomm) (hyQ : y ∈ Q)
    (hyJ : y * d.Jbar = d.Jbar * y) : y = 1 := by
  have hJQ' := hJQ (Subgroup.mem_zpowers d.Jbar)
  have hDR : d.Dbar Q hQcomm ≤ Subgroup.normalizer (R : Set (MulAut d.V)) :=
    fun x hx => hKR (hQK hx.1)
  have hJD : d.Jbar ∈ Subgroup.normalizer (d.Dbar Q hQcomm : Set (MulAut d.V)) := by
    apply Sec53.mem_normalizer_of_conj_le
    rintro x ⟨hx, hx'⟩
    refine ⟨(Subgroup.mem_normalizer_iff.mp hJQ' x).mp hx, ?_⟩
    rw [hx', show d.Jbar * x⁻¹ * d.Jbar⁻¹ = (d.Jbar * x * d.Jbar⁻¹)⁻¹ by group, hx']
  have hJRD : Subgroup.zpowers d.Jbar ≤
      Subgroup.normalizer ((R ⊔ d.Dbar Q hQcomm : Subgroup _) : Set (MulAut d.V)) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_sup' hJR hJD)
  obtain ⟨rd, hrd, e, he, rfl⟩ := (mem_sup_iff_of_le_normalizer hJRD).mp hyX
  obtain ⟨r, hr, δ, hδ, rfl⟩ := (mem_sup_iff_of_le_normalizer hDR).mp hrd
  rcases eq_one_or_eq_of_mem_zpowers d.orderOf_Jbar he with rfl | rfl
  · rw [mul_one] at hyQ hyJ ⊢
    have hrQ : r ∈ Q := by
      have := Q.mul_mem hyQ (Q.inv_mem hδ.1)
      rwa [mul_inv_cancel_right] at this
    have hr1 : r = 1 := by
      have := Subgroup.mem_inf.mpr ⟨hr, hrQ⟩
      rwa [hRQ, Subgroup.mem_bot] at this
    rw [hr1, one_mul] at hyJ hyQ ⊢
    have h1 := hδ.2
    have h2 : d.Jbar * δ * d.Jbar⁻¹ = δ := by rw [← hyJ, mul_inv_cancel_right]
    rw [h2] at h1
    have hδ2 : δ ^ 2 = 1 := by
      rw [sq]
      nth_rw 2 [h1]
      exact mul_inv_cancel δ
    obtain ⟨k, hk⟩ := hQp ⟨δ, hyQ⟩
    have h3 : δ ^ (3 ^ k) = 1 := congrArg Subtype.val hk
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
      (Nat.Coprime.pow_right k (by norm_num : Nat.Coprime 2 3))
      (orderOf_dvd_of_pow_eq_one hδ2) (orderOf_dvd_of_pow_eq_one h3))
  · exfalso
    apply d.Jbar_not_mem_Kbar
    have : d.Jbar = (r * δ)⁻¹ * (r * δ * d.Jbar) := by group
    rw [this]
    exact d.Kbar.mul_mem (d.Kbar.inv_mem (d.Kbar.mul_mem (hRK hr) (hQK hδ.1))) (hQK hyQ)

end X

theorem false_of_hallPResidual_eq_top
    (hres : BenderSuzuki.External.hallPResidual 3 d.NV = ⊤) : False := by
  obtain ⟨v, hvp, hvn⟩ := d.exists_zsigmondy
  have : Fact v.Prime := ⟨hvp⟩
  obtain ⟨Q, hQK, hQp, hQcard, hJQ, hPQ, hQcomm, hQsmall⟩ := d.exists_Qbar hvn
  obtain ⟨R, hRK, hR3, hKRQ, hRQ, hJR, hKR⟩ :=
    d.exists_complement hQK hQp hQcard hQcomm hQsmall
  have himg : (BenderSuzuki.External.hallPResidual 3 d.NV).map d.φ ≤ d.Xbar Q R hQcomm := by
    rw [Subgroup.map_le_iff_le_comap, BenderSuzuki.External.hallPResidual, Subgroup.closure_le]
    intro g hg
    have hcop : Nat.Coprime 3 (orderOf (d.φ g)) :=
      Nat.Coprime.coprime_dvd_right (orderOf_map_dvd d.φ g) hg
    exact d.mem_X_of_coprime (hJQ := hJQ) (hKRQ := hKRQ) (hR3 := hR3) (hQcomm := hQcomm)
      ⟨g, rfl⟩ hcop
  obtain ⟨y, hyP, hy1⟩ : ∃ y ∈ d.P₀, y ≠ 1 := by
    by_contra h
    push Not at h
    apply d.P₀_ne_bot
    rw [eq_bot_iff]
    intro y hy
    exact Subgroup.mem_bot.mpr (h y hy)
  have hyN := d.P₀_le_NV hyP
  have hyX : d.φ ⟨y, hyN⟩ ∈ d.Xbar Q R hQcomm :=
    himg ⟨⟨y, hyN⟩, by rw [hres]; trivial, rfl⟩
  have hyQ : d.φ ⟨y, hyN⟩ ∈ Q := hPQ (d.φ_mem_bar hyP)
  have hyJ : d.φ ⟨y, hyN⟩ * d.Jbar = d.Jbar * d.φ ⟨y, hyN⟩ :=
    d.phi_comm_Jbar_of_comm hyN (Subgroup.mem_centralizer_singleton_iff.mp (d.E_le (d.P₀_le hyP)))
  have h1 := d.eq_one_of_mem_X (hQK := hQK) (hQp := hQp) (hJQ := hJQ) (hRK := hRK) (hRQ := hRQ)
    (hJR := hJR) (hKR := hKR) (hQcomm := hQcomm) hyX hyQ hyJ
  rw [d.φ_eq_one_iff] at h1
  exact hy1 (d.eq_one_of_mem_P₀_of_mem_CV hyP h1)


end P56AbData

end CFSG.Walter.W67

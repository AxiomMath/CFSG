module

public import CFSG.Quasithin.Background.C1PackS15205A
public import CFSG.Quasithin.EmptyFaithful.S152Y03
public import CFSG.Quasithin.EmptyFaithful.S152Y14

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack5

section Abstract

variable {A : Type*} [Group A] [Finite A]

theorem inf_eq_bot_of_not_le {K X : Subgroup A} {n : ℕ} (hn : n.Prime) (hK : Nat.card K = n)
    (hX : ¬ K ≤ X) : K ⊓ X = ⊥ := by
  have hd : Nat.card (K ⊓ X : Subgroup A) ∣ n := hK ▸ Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime hn).mp hd with h1 | h1
  · exact Subgroup.card_eq_one.mp h1
  · exfalso
    apply hX
    have : K ⊓ X = K := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h1, hK])
    rw [← this]
    exact inf_le_right

theorem isPGroup_of_inf_oTwoUpper_eq_bot {M₀ W : Subgroup A} (hW : W ≤ M₀)
    (h : oTwoUpper M₀ ⊓ W = ⊥) : IsPGroup 2 W := by
  intro w
  obtain ⟨k, hk⟩ := exists_pow_mem_oTwoUpper M₀ (hW w.2)
  have h1 : (w : A) ^ 2 ^ k ∈ oTwoUpper M₀ ⊓ W := ⟨hk, W.pow_mem w.2 _⟩
  rw [h, Subgroup.mem_bot] at h1
  exact ⟨k, Subtype.ext (by simpa using h1)⟩

theorem card_le_two_of_isPGroup {X W : Subgroup A} {n : ℕ} (hn : Odd n) (hX : Nat.card X = 2 * n)
    (hW : W ≤ X) (hp : IsPGroup 2 W) : Nat.card W ≤ 2 := by
  obtain ⟨a, ha⟩ := hp.exists_card_eq
  have hd : Nat.card W ∣ 2 * n := hX ▸ Subgroup.card_dvd_of_le hW
  rw [ha] at hd ⊢
  by_contra hlt
  have ha2 : 2 ≤ a := by
    by_contra h; push Not at h
    interval_cases a <;> simp at hlt
  obtain ⟨b, rfl⟩ : ∃ b, a = b + 2 := ⟨a - 2, by omega⟩
  have h4 : 4 ∣ 2 * n := (Dvd.intro_left (2 ^ b) (by ring : 2 ^ b * 4 = 2 ^ (b + 2))).trans hd
  obtain ⟨m, hm⟩ := hn
  omega

theorem card_eq_two_of_isSylowTwoOf {X S : Subgroup A} {n : ℕ} (hn : Odd n)
    (hX : Nat.card X = 2 * n) (hS : IsSylowTwoOf S X) : Nat.card S = 2 := by
  have hle := card_le_two_of_isPGroup hn hX hS.1 hS.2.1
  have h1 : (S.subgroupOf X).index * Nat.card (S.subgroupOf X) = Nat.card X := by
    rw [mul_comm]; exact Subgroup.card_mul_index _
  have h2 : Nat.card (S.subgroupOf X) = Nat.card S :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hS.1).toEquiv
  have hodd : ¬ 2 ∣ (S.subgroupOf X).index := hS.2.2
  have hpos : 0 < Nat.card S := Nat.card_pos
  rw [h2, hX] at h1
  by_contra hne
  have h1' : Nat.card S = 1 := by omega
  rw [h1'] at h1
  apply hodd
  exact ⟨n, by omega⟩

theorem abstract_dihedral_exclusion {Mb Tb Hb Mcb M0 : Subgroup A} {n : ℕ} [NeZero n]
    (hn : Odd n) (hnp : n.Prime) (e : ↥M0 ≃* DihedralGroup n) (hSyl : IsSylowTwoOf Tb Mb)
    (hM0 : M0 ≤ Mb) (hM0n : ∀ g ∈ Mb, ∀ y ∈ M0, g * y * g⁻¹ ∈ M0) (hHb : Hb ≤ Mb)
    (hMcb : Mcb ≤ Mb) (hTH : Tb ≤ Hb) (hTMc : Tb ≤ Mcb)
    (hfr : ∀ g ∈ Mb, ∃ a ∈ Mcb, ∃ b ∈ oTwoUpper M0, g = a * b) (hM0Hb : ¬ M0 ≤ Hb) :
    Hb ≤ Mcb := by
  classical
  obtain ⟨hKcard, hM0card, hinv⟩ := dihedral_shape hn e
  set K : Subgroup A := oTwoUpper M0 with hKdef
  have hKM0 : K ≤ M0 := oTwoUpper_le M0
  by_cases hKMc : K ≤ Mcb
  ·
    intro h hh
    obtain ⟨a, ha, b, hb, rfl⟩ := hfr h (hHb hh)
    exact Mcb.mul_mem ha (hKMc hb)
  have hMn : Mb ≤ Subgroup.normalizer (M0 : Set A) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro x
    exact ⟨fun hx => hM0n g hg x hx, fun hx => by
      have := hM0n g⁻¹ (Mb.inv_mem hg) _ hx
      simpa [mul_assoc] using this⟩
  have hT0 : IsSylowTwoOf (Tb ⊓ M0) M0 := A4.isSylowTwoOf_inf_normal hSyl hM0 hMn
  have hT0card : Nat.card (Tb ⊓ M0 : Subgroup A) = 2 := card_eq_two_of_isSylowTwoOf hn hM0card hT0
  set T0 : Subgroup A := Tb ⊓ M0 with hT0def
  have hT0M0 : T0 ≤ M0 := inf_le_right
  have hKHb : ¬ K ≤ Hb := by
    intro hKH
    apply hM0Hb
    have hle : K ⊔ T0 ≤ M0 := sup_le hKM0 hT0M0
    have hge : Nat.card M0 ≤ Nat.card (K ⊔ T0 : Subgroup A) := by
      have hd1 : n ∣ Nat.card (K ⊔ T0 : Subgroup A) := hKcard ▸ Subgroup.card_dvd_of_le le_sup_left
      have hd2 : 2 ∣ Nat.card (K ⊔ T0 : Subgroup A) := hT0card ▸ Subgroup.card_dvd_of_le le_sup_right
      have hcop : Nat.Coprime n 2 := Nat.coprime_two_right.mpr hn
      have hd := hcop.mul_dvd_of_dvd_of_dvd hd1 hd2
      rw [hM0card, mul_comm]
      exact Nat.le_of_dvd Nat.card_pos hd
    have heq : K ⊔ T0 = M0 := Subgroup.eq_of_le_of_card_ge hle hge
    rw [← heq]
    exact sup_le hKH (inf_le_left.trans hTH)
  have key : ∀ X : Subgroup A, ¬ K ≤ X → T0 ≤ X → X ⊓ M0 = T0 := by
    intro X hKX hT0X
    have hKbot : K ⊓ (X ⊓ M0) = ⊥ := by
      have := inf_eq_bot_of_not_le hnp hKcard hKX
      refine eq_bot_iff.mpr fun x hx => ?_
      have hx' : x ∈ K ⊓ X := ⟨hx.1, hx.2.1⟩
      rw [this] at hx'
      exact hx'
    have hp := isPGroup_of_inf_oTwoUpper_eq_bot (M₀ := M0) (W := X ⊓ M0) inf_le_right hKbot
    have hle := card_le_two_of_isPGroup hn hM0card inf_le_right hp
    have hge : T0 ≤ X ⊓ M0 := le_inf hT0X hT0M0
    exact (Subgroup.eq_of_le_of_card_ge hge (by rw [hT0card]; exact hle)).symm
  have hT0Hb : T0 ≤ Hb := inf_le_left.trans hTH
  have hT0Mc : T0 ≤ Mcb := inf_le_left.trans hTMc
  have hHM0 : Hb ⊓ M0 = T0 := key Hb hKHb hT0Hb
  have hMcM0 : Mcb ⊓ M0 = T0 := key Mcb hKMc hT0Mc
  have hnormH : ∀ h ∈ Hb, ∀ x ∈ T0, h * x * h⁻¹ ∈ T0 := by
    intro h hh x hx
    have h1 : h * x * h⁻¹ ∈ Hb :=
      Hb.mul_mem (Hb.mul_mem hh (hT0Hb hx)) (Hb.inv_mem hh)
    have h2 : h * x * h⁻¹ ∈ M0 := hM0n h (hHb hh) x (hT0M0 hx)
    rw [← hHM0]
    exact ⟨h1, h2⟩
  have hnormM : ∀ h ∈ Mcb, ∀ x ∈ T0, h * x * h⁻¹ ∈ T0 := by
    intro h hh x hx
    have h1 : h * x * h⁻¹ ∈ Mcb :=
      Mcb.mul_mem (Mcb.mul_mem hh (hT0Mc hx)) (Mcb.inv_mem hh)
    have h2 : h * x * h⁻¹ ∈ M0 := hM0n h (hMcb hh) x (hT0M0 hx)
    rw [← hMcM0]
    exact ⟨h1, h2⟩
  have hnK : ∀ b ∈ K, (∀ x ∈ T0, b * x * b⁻¹ ∈ T0) → b = 1 := by
    intro b hb hbn
    have hex : ∃ t : T0, t ≠ 1 := by
      by_contra hcon
      push Not at hcon
      have : Nat.card T0 = 1 := by
        rw [Nat.card_eq_one_iff_unique]
        exact ⟨⟨fun x y => by rw [hcon x, hcon y]⟩, ⟨1⟩⟩
      omega
    obtain ⟨t, ht1⟩ := hex
    have huniq := (Nat.card_eq_two_iff' (1 : T0)).mp hT0card
    obtain ⟨u, hu1, huu⟩ := huniq
    have ht : (t : A) ^ 2 = 1 := by
      have : orderOf t ∣ 2 := hT0card ▸ orderOf_dvd_natCard t
      rcases (Nat.dvd_prime Nat.prime_two).mp this with h1 | h1
      · exact absurd (orderOf_eq_one_iff.mp h1) ht1
      · have := pow_orderOf_eq_one t
        rw [h1] at this
        exact congrArg Subtype.val this
    have hto : orderOf (t : A) = 2 := by
      refine orderOf_eq_prime ht ?_
      intro h1
      exact ht1 (Subtype.ext h1)
    have hbt : b * t * b⁻¹ = t := by
      have hmem : b * (t : A) * b⁻¹ ∈ T0 := hbn t t.2
      have hne : (⟨b * (t : A) * b⁻¹, hmem⟩ : T0) ≠ 1 := by
        intro h1
        have : b * (t : A) * b⁻¹ = 1 := congrArg Subtype.val h1
        apply ht1
        apply Subtype.ext
        simpa using this
      have h1 := huu _ hne
      have h2 := huu t ht1
      exact congrArg Subtype.val (h1.trans h2.symm)
    have hinvb : (t : A) * b * (t : A)⁻¹ = b⁻¹ := hinv t (hT0M0 t.2) hto b hb
    have hcomm : (t : A) * b * (t : A)⁻¹ = b := by
      have : b * (t : A) = (t : A) * b := by
        calc b * (t : A) = b * t * b⁻¹ * b := by group
          _ = t * b := by rw [hbt]
      calc (t : A) * b * (t : A)⁻¹ = b * (t : A) * (t : A)⁻¹ := by rw [this]
        _ = b := by group
    have hb2 : b ^ 2 = 1 := by
      have : b = b⁻¹ := hcomm.symm.trans hinvb
      calc b ^ 2 = b * b := sq b
        _ = b * b⁻¹ := by rw [← this]
        _ = 1 := mul_inv_cancel b
    have hbn' : b ^ n = 1 := by
      have : orderOf (⟨b, hb⟩ : K) ∣ n := hKcard ▸ orderOf_dvd_natCard _
      have h1 := pow_orderOf_eq_one (⟨b, hb⟩ : K)
      have h2 : (⟨b, hb⟩ : K) ^ n = 1 := by
        obtain ⟨k, hk⟩ := this
        rw [hk, pow_mul, h1, one_pow]
      exact congrArg Subtype.val h2
    have hbo : orderOf b ∣ Nat.gcd 2 n :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hb2) (orderOf_dvd_of_pow_eq_one hbn')
    rw [(Nat.coprime_two_left.mpr hn).gcd_eq_one] at hbo
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp hbo)
  intro h hh
  obtain ⟨a, ha, b, hb, hab⟩ := hfr h (hHb hh)
  have hb1 : b = 1 := by
    refine hnK b hb fun x hx => ?_
    have hbx : b = a⁻¹ * h := by rw [hab]; group
    have h1 := hnormH h hh x hx
    have h2 := hnormM a⁻¹ (Mcb.inv_mem ha) _ h1
    rw [hbx]
    simpa [mul_assoc] using h2
  rw [hab, hb1, mul_one]
  exact ha

end Abstract

section Concrete

variable {G : Type} [Group G] [Finite G] {T Mc M M₁ : Subgroup G}

theorem Ctr5.frattini_bar (c : Ctr5 T Mc M M₁) {g : MulAut (V154 T Mc M)}
    (hg : g ∈ autOn M (V154 T Mc M)) :
    ∃ a ∈ autOn (M ⊓ Mc) (V154 T Mc M), ∃ b ∈ oTwoUpper (mBar0 T Mc M), g = a * b := by
  obtain ⟨x, hxN, hxM, rfl⟩ := mem_autOn_iff_exists.mp hg
  have hx : x ∈ ((M ⊓ Mc : Subgroup G) : Set G) * (oTwoUpper (m0Of T Mc M) : Set G) := by
    rw [← c.std.c1523.frattini]
    exact hxM
  obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.mp hx
  have haN : a ∈ Subgroup.normalizer (V154 T Mc M : Set G) := c.std.data.hMV ha.1
  have hbM : b ∈ M := ((oTwoUpper_le _).trans (S152Y.m0Of_le T Mc M)) hb
  have hbN : b ∈ Subgroup.normalizer (V154 T Mc M : Set G) := c.std.data.hMV hbM
  refine ⟨conjAct _ ⟨a, haN⟩, mem_autOn_iff_exists.mpr ⟨a, haN, ha, rfl⟩, conjAct _ ⟨b, hbN⟩, ?_, ?_⟩
  · have h1 : conjAct _ ⟨b, hbN⟩ ∈ autOn (oTwoUpper (m0Of T Mc M)) (V154 T Mc M) :=
      mem_autOn_iff_exists.mpr ⟨b, hbN, hb, rfl⟩
    rwa [show autOn (oTwoUpper (m0Of T Mc M)) (V154 T Mc M) = oTwoUpper (mBar0 T Mc M) from
      c.std.data.autOn_y0Of] at h1
  · rw [← map_mul]
    rfl

theorem Ctr5.not_mBar0_le (c : Ctr5 T Mc M M₁) :
    ¬ mBar0 T Mc M ≤ autOn (M₁ ⊓ M) (V154 T Mc M) := by
  intro h
  apply c.not_m0_subset
  intro m hm
  have hm' : m ∈ preOn M (V154 T Mc M) (mBar0 T Mc M) := hm
  obtain ⟨hmM, hmN, hmL⟩ := mem_preOn.mp hm'
  obtain ⟨a, ha, k, hk, rfl⟩ := exists_mul_of_conjAct_mem c.std.data.hMV inf_le_right hmM (h hmL)
  refine Set.mem_mul.mpr ⟨a, ha, k, ⟨hk.1, ?_⟩, rfl⟩
  exact Subgroup.centralizer_le_normalizer _ (Subgroup.centralizer_le inf_le_right hk.2)

theorem false_of_dihedral (c : Ctr5 T Mc M M₁) {n : ℕ} [NeZero n] (hn : Odd n) (hnp : n.Prime)
    (e : ↥(mBar0 T Mc M) ≃* DihedralGroup n) : False := by
  have hd := c.std.data
  have hHc : autOn (M₁ ⊓ M) (V154 T Mc M) ≤ autOn (M ⊓ Mc) (V154 T Mc M) :=
    abstract_dihedral_exclusion hn hnp e (S152Y.isSylowTwoOf_Tb hd) (S152Y.mBar0_le T Mc M)
      (S152Y.mBar0_normalized T Mc M) (A4.autOn_mono inf_le_right) (A4.autOn_mono inf_le_left)
      (A4.autOn_mono c.T_le_H) (A4.autOn_mono (le_inf c.T_le_M c.qtfe.t_le_mc))
      (fun g hg => c.frattini_bar hg) c.not_mBar0_le
  exact c.not_forall_mul_Mc
    (exists_mul_of_autOn_le hd.hMV inf_le_right inf_le_left hHc)

theorem Ctr5.case_three (c : Ctr5 T Mc M M₁) :
    Case1517Three M (V154 T Mc M) (mBar0 T Mc M) := by
  rcases c.std.c1521.cases with h | h | h | h
  · obtain ⟨-, -, ⟨e⟩⟩ := h
    exact (false_of_dihedral c (n := 3) (by decide) Nat.prime_three e).elim
  · obtain ⟨-, ⟨e⟩, -⟩ := h
    exact (false_of_dihedral c (n := 3) (by decide) Nat.prime_three e).elim
  · exact h
  · obtain ⟨-, ⟨e⟩, -⟩ := h
    exact (false_of_dihedral c (n := 5) (by decide) (by norm_num) e).elim

end Concrete

end C1Pack5

end CFSG.Quasithin

module

public import CFSG.RankThree.PartTwo.Sec12.SylowIndependence

public section

namespace CFSG.RankThree.PartTwo.Sec12

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)

variable {G : Type*} [Group G]

theorem commute_of_conj_mem_zpowers {c g : G} (hc : orderOf c = 3)
    (hgc : g * c * g⁻¹ ∈ Subgroup.zpowers c) {k : ℕ} (hg : g ^ 3 ^ k = 1) : g * c = c * g := by
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgc
  rw [← zpow_mod_orderOf, hc] at hn
  have h0 : 0 ≤ n % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h3 : n % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  have hc1 : c ≠ 1 := fun h => by rw [h, orderOf_one] at hc; norm_num at hc
  have hc3 : c ^ 3 = 1 := by rw [← hc]; exact pow_orderOf_eq_one c
  have hsq : ∀ m : ℤ, c ^ m = g * c * g⁻¹ → m = 1 ∨ m = 2 →
      (g ^ 2) * c * (g ^ 2)⁻¹ = c := by
    intro m hm hm12
    have e : (g ^ 2) * c * (g ^ 2)⁻¹ = g * (g * c * g⁻¹) * g⁻¹ := by
      rw [pow_two, mul_inv_rev]
      group
    rw [e, ← hm]
    rcases hm12 with rfl | rfl
    · rw [zpow_one] at hm ⊢
      exact hm.symm
    · have : g * c ^ (2 : ℤ) * g⁻¹ = (g * c * g⁻¹) ^ (2 : ℤ) := by
        rw [conj_zpow]
      rw [this, ← hm, ← zpow_mul]
      have : c ^ ((2 : ℤ) * 2) = c := by
        rw [show (2 : ℤ) * 2 = 3 + 1 by norm_num, zpow_add, zpow_one,
          show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hc3, one_mul]
      exact this
  have hgpow : g = (g ^ 2) ^ ((3 ^ k + 1) / 2) := by
    have hodd : Odd (3 ^ k) := Odd.pow (by decide)
    have heven : Even (3 ^ k + 1) := hodd.add_one
    rw [← pow_mul, Nat.two_mul_div_two_of_even heven, pow_succ, hg, one_mul]
  have key : ∀ m : ℤ, c ^ m = g * c * g⁻¹ → m = 1 ∨ m = 2 → g * c = c * g := by
    intro m hm hm12
    have h2 := hsq m hm hm12
    have hcomm : Commute (g ^ 2) c := by
      change g ^ 2 * c = c * g ^ 2
      calc g ^ 2 * c = (g ^ 2 * c * (g ^ 2)⁻¹) * g ^ 2 := by group
        _ = c * g ^ 2 := by rw [h2]
    rw [hgpow]
    exact (hcomm.pow_left _).eq
  interval_cases h : n % ((3 : ℕ) : ℤ)
  · rw [zpow_zero] at hn
    exact absurd (by
      have := congrArg (fun x => g⁻¹ * x * g) hn
      simpa [mul_assoc] using this.symm) hc1
  · exact key 1 hn (Or.inl rfl)
  · exact key 2 hn (Or.inr rfl)

theorem eq_pow_sq_pow_of_pow_three_pow_eq_one {g : G} {k : ℕ} (hg : g ^ 3 ^ k = 1) :
    g = (g ^ 2) ^ ((3 ^ k + 1) / 2) := by
  have hodd : Odd (3 ^ k) := Odd.pow (by decide)
  rw [← pow_mul, Nat.two_mul_div_two_of_even hodd.add_one, pow_succ, hg, one_mul]

theorem exists_zpow_mul_zpow_of_mem_closure_pair {c y : G} (hcy : c * y = y * c) {z : G}
    (hz : z ∈ Subgroup.closure ({c, y} : Set G)) : ∃ m n : ℤ, z = c ^ m * y ^ n := by
  have hcomm : Commute c y := hcy
  induction hz using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact ⟨1, 0, by simp⟩
    · exact ⟨0, 1, by simp⟩
  | one => exact ⟨0, 0, by simp⟩
  | mul x w _ _ hx hw =>
    obtain ⟨m, n, rfl⟩ := hx
    obtain ⟨m', n', rfl⟩ := hw
    refine ⟨m + m', n + n', ?_⟩
    have hc : y ^ n * c ^ m' = c ^ m' * y ^ n := ((hcomm.zpow_zpow m' n).eq).symm
    rw [zpow_add, zpow_add]
    calc c ^ m * y ^ n * (c ^ m' * y ^ n') = c ^ m * (y ^ n * c ^ m') * y ^ n' := by group
      _ = c ^ m * (c ^ m' * y ^ n) * y ^ n' := by rw [hc]
      _ = c ^ m * c ^ m' * (y ^ n * y ^ n') := by group
  | inv x _ hx =>
    obtain ⟨m, n, rfl⟩ := hx
    refine ⟨-m, -n, ?_⟩
    rw [mul_inv_rev, zpow_neg, zpow_neg]
    exact ((hcomm.zpow_zpow m n).inv_inv).eq.symm

theorem closure_pair_eq_of_card_nine [Finite G] {D : Subgroup G} {c y : G}
    (hexp : ∀ x ∈ D, x ^ 3 = 1) (hD9 : Nat.card D = 9) (hcD : c ∈ D) (hc1 : c ≠ 1)
    (hy : y ∈ D) (hyc : y ∉ Subgroup.zpowers c) : Subgroup.closure ({c, y} : Set G) = D := by
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexp c hcD) hc1
  have hKD : Subgroup.closure ({c, y} : Set G) ≤ D := by
    rw [Subgroup.closure_le]
    rintro x (rfl | rfl)
    exacts [hcD, hy]
  have hcK : Subgroup.zpowers c ≤ Subgroup.closure ({c, y} : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert c {y}))
  have hyK : y ∈ Subgroup.closure ({c, y} : Set G) :=
    Subgroup.subset_closure (Set.mem_insert_of_mem c rfl)
  have h3K : 3 ∣ Nat.card (Subgroup.closure ({c, y} : Set G)) := by
    rw [← hc3, ← Nat.card_zpowers]
    exact Subgroup.card_dvd_of_le hcK
  have hK9 : Nat.card (Subgroup.closure ({c, y} : Set G)) ∣ 9 :=
    hD9 ▸ Subgroup.card_dvd_of_le hKD
  have hne : Nat.card (Subgroup.closure ({c, y} : Set G)) ≠ 3 := by
    intro h3
    apply hyc
    have : Subgroup.zpowers c = Subgroup.closure ({c, y} : Set G) :=
      Subgroup.eq_of_le_of_card_ge hcK (by rw [h3, Nat.card_zpowers, hc3])
    exact this ▸ hyK
  have h9 : Nat.card (Subgroup.closure ({c, y} : Set G)) = 9 := by
    have hdiv : Nat.card (Subgroup.closure ({c, y} : Set G)) ∈ Nat.divisors 9 :=
      Nat.mem_divisors.mpr ⟨hK9, by norm_num⟩
    have : Nat.divisors 9 = {1, 3, 9} := by decide
    rw [this] at hdiv
    rcases Finset.mem_insert.mp hdiv with h1 | hdiv
    · rw [h1] at h3K; norm_num at h3K
    rcases Finset.mem_insert.mp hdiv with h3 | h9
    · exact absurd h3 hne
    · exact Finset.mem_singleton.mp h9
  exact Subgroup.eq_of_le_of_card_ge hKD (by rw [h9, hD9])

theorem conj_mul_inv_mem_zpowers_of_mem_closure {c g y : G} (hcy : c * y = y * c)
    (hc3 : c ^ 3 = 1) (hy3 : y ^ 3 = 1) (hyc : y ∉ Subgroup.zpowers c) (hgc : g * c = c * g)
    {k : ℕ} (hg : g ^ 3 ^ k = 1) (hz : g * y * g⁻¹ ∈ Subgroup.closure ({c, y} : Set G)) :
    g * y * g⁻¹ * y⁻¹ ∈ Subgroup.zpowers c := by
  have hgc' : Commute g c := hgc
  have hcy' : Commute c y := hcy
  have hy1 : y ≠ 1 := fun h => hyc (h ▸ Subgroup.one_mem _)
  have hy3' : orderOf y = 3 := orderOf_eq_prime hy3 hy1
  have hfix : ∀ n : ℤ, g * c ^ n * g⁻¹ = c ^ n := fun n => by
    rw [(hgc'.zpow_right n).eq, mul_inv_cancel_right]
  obtain ⟨m, n, hmn⟩ := exists_zpow_mul_zpow_of_mem_closure_pair hcy hz
  rw [← zpow_mod_orderOf y n, hy3'] at hmn
  have h0 : 0 ≤ n % ((3 : ℕ) : ℤ) := Int.emod_nonneg _ (by norm_num)
  have h3 : n % ((3 : ℕ) : ℤ) < 3 := Int.emod_lt_of_pos _ (by norm_num)
  interval_cases h : n % ((3 : ℕ) : ℤ)
  ·
    exfalso
    apply hyc
    rw [zpow_zero, mul_one] at hmn
    have : y = g⁻¹ * c ^ m * g := by rw [← hmn]; group
    rw [this, show g⁻¹ * c ^ m * g = c ^ m by
      rw [(hgc'.inv_left.zpow_right m).eq, inv_mul_cancel_right]]
    exact Subgroup.zpow_mem_zpowers c m
  · rw [zpow_one] at hmn
    rw [hmn, mul_inv_cancel_right]
    exact Subgroup.zpow_mem_zpowers c m
  ·
    exfalso
    apply hyc
    set z := g * y * g⁻¹ with hzdef
    have hsq : (g ^ 2) * y * (g ^ 2)⁻¹ = y := by
      have e1 : (g ^ 2) * y * (g ^ 2)⁻¹ = g * z * g⁻¹ := by
        rw [hzdef, pow_two, mul_inv_rev]; group
      have e2 : g * z * g⁻¹ = c ^ m * z ^ (2 : ℤ) := by
        rw [hmn, show g * (c ^ m * y ^ (2 : ℤ)) * g⁻¹ = (g * c ^ m * g⁻¹) * (g * y * g⁻¹) ^ (2 : ℤ)
          by rw [conj_zpow]; group, hfix, ← hzdef, hmn]
      rw [e1, e2, hmn]
      have hcy2 : (c ^ m) * y ^ (2 : ℤ) = y ^ (2 : ℤ) * c ^ m := (hcy'.zpow_zpow m 2).eq
      have hc3' : c ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hc3]
      have hy3'' : y ^ (3 : ℤ) = 1 := by
        rw [show (3 : ℤ) = ((3 : ℕ) : ℤ) by norm_num, zpow_natCast, hy3]
      calc c ^ m * (c ^ m * y ^ (2 : ℤ)) ^ (2 : ℤ)
          = c ^ m * ((c ^ m * y ^ (2 : ℤ)) * (c ^ m * y ^ (2 : ℤ))) := by rw [zpow_two]
        _ = c ^ m * (c ^ m * (y ^ (2 : ℤ) * c ^ m) * y ^ (2 : ℤ)) := by group
        _ = c ^ m * (c ^ m * (c ^ m * y ^ (2 : ℤ)) * y ^ (2 : ℤ)) := by rw [hcy2]
        _ = (c ^ (3 : ℤ)) ^ m * (y ^ (3 : ℤ)) * y := by group
        _ = y := by rw [hc3', hy3'', one_zpow, one_mul, one_mul]
    have hcomm2 : Commute (g ^ 2) y := by
      change g ^ 2 * y = y * g ^ 2
      calc g ^ 2 * y = (g ^ 2 * y * (g ^ 2)⁻¹) * g ^ 2 := by group
        _ = y * g ^ 2 := by rw [hsq]
    have hgy : g * y = y * g := by
      rw [eq_pow_sq_pow_of_pow_three_pow_eq_one hg]
      exact (hcomm2.pow_left _).eq
    have hzy : z = y := by rw [hzdef, hgy, mul_inv_cancel_right]
    rw [hzy] at hmn
    have : y⁻¹ = c ^ m := by
      have h' := congrArg (fun t => t * (y ^ (2 : ℤ))⁻¹) hmn
      simp only [mul_inv_cancel_right] at h'
      rw [← h']
      group
    have : y = (c ^ m)⁻¹ := by rw [← this, inv_inv]
    rw [this]
    exact Subgroup.inv_mem _ (Subgroup.zpow_mem_zpowers c m)

theorem conj_mul_inv_mem_zpowers [Finite G] {D : Subgroup G} {c g : G}
    (hcomm : ∀ x ∈ D, ∀ y ∈ D, x * y = y * x) (hexp : ∀ x ∈ D, x ^ 3 = 1)
    (hD9 : Nat.card D = 9) (hcD : c ∈ D) (hc1 : c ≠ 1)
    (hgD : g ∈ Subgroup.normalizer (D : Set G)) (hgc : g * c = c * g) {k : ℕ}
    (hg : g ^ 3 ^ k = 1) :
    ∀ y ∈ D, g * y * g⁻¹ * y⁻¹ ∈ Subgroup.zpowers c := by
  have hgc' : Commute g c := hgc
  intro y hy
  by_cases hyc : y ∈ Subgroup.zpowers c
  · obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hyc
    rw [(hgc'.zpow_right n).eq, mul_inv_cancel_right, mul_inv_cancel]
    exact Subgroup.one_mem _
  have hz : g * y * g⁻¹ ∈ D := (Subgroup.mem_normalizer_iff.mp hgD y).mp hy
  rw [← closure_pair_eq_of_card_nine hexp hD9 hcD hc1 hy hyc] at hz
  exact conj_mul_inv_mem_zpowers_of_mem_closure (hcomm c hcD y hy) (hexp c hcD) (hexp y hy) hyc
    hgc hg hz

theorem mem_zpowers_subtype_iff {A : Subgroup G} {c x : A} :
    x ∈ Subgroup.zpowers c ↔ (x : G) ∈ Subgroup.zpowers (c : G) := by
  rw [show Subgroup.zpowers (c : G) = (Subgroup.zpowers c).map A.subtype from
    (MonoidHom.map_zpowers A.subtype c).symm]
  exact (Subgroup.mem_map_iff_mem A.subtype_injective).symm

theorem card_transvectionGroup_le [Finite G] {A : Subgroup G} {c b y : G} (hcA : c ∈ A)
    (hbA : b ∈ A) (hyA : y ∈ A) (hgen : Subgroup.closure ({c, b, y} : Set G) = A)
    (hc : orderOf c = 3) :
    Nat.card (transvectionGroup A ⟨c, hcA⟩) ≤ 9 := by
  set c' : A := ⟨c, hcA⟩
  set b' : A := ⟨b, hbA⟩
  set y' : A := ⟨y, hyA⟩
  let F : transvectionGroup A c' → Subgroup.zpowers c' × Subgroup.zpowers c' := fun σ =>
    (⟨(σ : MulAut A) b' * b'⁻¹, σ.2.2 b'⟩, ⟨(σ : MulAut A) y' * y'⁻¹, σ.2.2 y'⟩)
  have hF : Function.Injective F := by
    rintro ⟨σ, hσ⟩ ⟨τ, hτ⟩ hστ
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq, mul_left_inj] at hστ
    obtain ⟨hb, hy⟩ := hστ
    apply Subtype.ext
    have hle : Subgroup.closure ({c, b, y} : Set G) ≤
        (MonoidHom.eqLocus (σ : A →* A) (τ : A →* A)).map A.subtype := by
      rw [Subgroup.closure_le]
      rintro x (rfl | rfl | rfl)
      · exact ⟨c', (show (σ : A →* A) c' = (τ : A →* A) c' from hσ.1.trans hτ.1.symm), rfl⟩
      · exact ⟨b', (show (σ : A →* A) b' = (τ : A →* A) b' from hb), rfl⟩
      · exact ⟨y', (show (σ : A →* A) y' = (τ : A →* A) y' from hy), rfl⟩
    ext x
    have hx : (x : G) ∈ Subgroup.closure ({c, b, y} : Set G) := by
      rw [hgen]
      exact x.2
    obtain ⟨x', hx', hxx⟩ := hle hx
    have hx'' : x' = x := Subtype.ext hxx
    rw [← hx'']
    exact congrArg Subtype.val (hx' : (σ : A →* A) x' = (τ : A →* A) x')
  have hc' : orderOf c' = 3 := by rw [← Subgroup.orderOf_coe]; exact hc
  calc Nat.card (transvectionGroup A c')
      ≤ Nat.card (Subgroup.zpowers c' × Subgroup.zpowers c') :=
        Nat.card_le_card_of_injective F hF
    _ = 9 := by rw [Nat.card_prod, Nat.card_zpowers, hc']

theorem exists_mem_not_mem_zpowers [Finite G] {D : Subgroup G} {c : G} (hD9 : Nat.card D = 9)
    (hc3 : orderOf c = 3) : ∃ y ∈ D, y ∉ Subgroup.zpowers c := by
  by_contra hcon
  push Not at hcon
  have hle : D ≤ Subgroup.zpowers c := hcon
  have := Subgroup.card_le_of_le hle
  rw [hD9, Nat.card_zpowers, hc3] at this
  omega

theorem mem_normalizer_of_map_conj_eq {B : Subgroup G} {g : G}
    (h1 : B.map (MulAut.conj g).toMonoidHom = B) (h2 : B.map (MulAut.conj g⁻¹).toMonoidHom = B) :
    g ∈ Subgroup.normalizer (B : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    rw [← h1]
    exact ⟨y, hy, rfl⟩
  · intro hy
    rw [← h2]
    exact ⟨_, hy, by simp [mul_assoc]⟩

theorem autIn_le_transvectionGroup {G' : Type} [Group G'] [Finite G'] {A : Subgroup G'}
    {c : G'} {L : Subgroup G'} (h : Sec12Std G' A c L) {P : Subgroup G'}
    (hPH : P ≤ Subgroup.normalizer (A : Set G') ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G'))
    (hP3 : IsPGroup 3 P) (hPL : P ≤ Subgroup.normalizer (L : Set G'))
    (hAL : Nat.card (A ⊓ L : Subgroup G') = 9) :
    Sec4.autIn P A ≤ transvectionGroup A ⟨c, h.mem_A⟩ := by
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexpA : ∀ x ∈ A, x ^ 3 = 1 := h.isE27.1.2
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexpA c h.mem_A) h.ne_one
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G') := by
    obtain ⟨L', -, hL'⟩ := h.mem_thetaComponentsAt
    rw [← hL']
    exact Subgroup.map_subtype_le L'
  have hcB : c ∈ A ⊓ Subgroup.centralizer (L : Set G') := by
    refine ⟨h.mem_A, Subgroup.mem_centralizer_iff.mpr fun l hl => ?_⟩
    exact (Subgroup.mem_centralizer_singleton_iff.mp (hLc hl))
  have hcAL : c ∈ A ⊓ L := ⟨h.mem_A, h.mem_L⟩
  intro σ hσ
  obtain ⟨g, hN, hgP, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
  obtain ⟨k, hk⟩ := hP3 ⟨g, hgP⟩
  have hg : g ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have hgc : g * c * g⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.mp (hPH hgP).2 c).mp (Subgroup.mem_zpowers c)
  have hgc' := commute_of_conj_mem_zpowers hc3 hgc hg
  have hgA := (hPH hgP).1
  have hgL := hPL hgP
  have hgB : g ∈ Subgroup.normalizer ((A ⊓ Subgroup.centralizer (L : Set G') : Subgroup G') :
      Set G') :=
    mem_normalizer_of_map_conj_eq (map_conj_inf_centralizer hgA hgL)
      (map_conj_inf_centralizer (inv_mem hgA) (inv_mem hgL))
  have hgAL : g ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G') : Set G') := by
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp hgA y,
      Subgroup.mem_normalizer_iff.mp hgL y]
  have hB := conj_mul_inv_mem_zpowers (D := A ⊓ Subgroup.centralizer (L : Set G'))
    (fun x hx y hy => hcommA x hx.1 y hy.1) (fun x hx => hexpA x hx.1) h.card_B hcB h.ne_one
    hgB hgc' hg
  have hAL' := conj_mul_inv_mem_zpowers (D := A ⊓ L) (fun x hx y hy => hcommA x hx.1 y hy.1)
    (fun x hx => hexpA x hx.1) hAL hcAL h.ne_one hgAL hgc' hg
  refine ⟨Subtype.ext ?_, fun x => ?_⟩
  · rw [Sec4.normalizerMonoidHom_apply_coe]
    change g * c * g⁻¹ = c
    rw [hgc', mul_inv_cancel_right]
  · rw [mem_zpowers_subtype_iff, Subgroup.coe_mul, Sec4.normalizerMonoidHom_apply_coe,
      Subgroup.coe_inv]
    have hBN : A ⊓ Subgroup.centralizer (L : Set G') ≤
        Subgroup.normalizer ((A ⊓ L : Subgroup G') : Set G') := fun b hb => by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · intro hy
        rw [hcommA b hb.1 y hy.1, mul_inv_cancel_right]
        exact hy
      · intro hy
        have hyA : y ∈ A := by
          have := A.mul_mem (A.mul_mem (A.inv_mem hb.1) hy.1) hb.1
          simpa [mul_assoc] using this
        rwa [hcommA b hb.1 y hyA, mul_inv_cancel_right] at hy
    have hx : (x : G') ∈ ((A ⊓ Subgroup.centralizer (L : Set G') ⊔ A ⊓ L : Subgroup G') :
        Set G') := by
      rw [h.sup_eq]
      exact x.2
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hBN] at hx
    obtain ⟨b, hb, y, hy, hxy⟩ := hx
    rw [← hxy]
    have hgy : g * y * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hgA y).mp hy.1
    have h1 : b⁻¹ * (g * y * g⁻¹) = (g * y * g⁻¹) * b⁻¹ :=
      hcommA _ (A.inv_mem hb.1) _ hgy
    have h2 : b⁻¹ * y⁻¹ = y⁻¹ * b⁻¹ := hcommA _ (A.inv_mem hb.1) _ (A.inv_mem hy.1)
    have e : g * (b * y) * g⁻¹ * (b * y)⁻¹ =
        (g * b * g⁻¹) * ((g * y * g⁻¹) * (y⁻¹ * b⁻¹)) := by group
    have e' : (g * y * g⁻¹) * (y⁻¹ * b⁻¹) = b⁻¹ * ((g * y * g⁻¹) * y⁻¹) := by
      rw [← h2, ← mul_assoc, ← h1, mul_assoc]
    rw [e, e', ← mul_assoc]
    exact Subgroup.mul_mem _ (hB b hb) (hAL' y hy)

theorem nine_le_card_autIn {G' : Type} [Group G'] [Finite G'] {A : Subgroup G'} {c : G'}
    {L : Subgroup G'} (h : Sec12Std G' A c L) {P : Subgroup G'}
    (hP : IsSylowOf 3 P (Subgroup.normalizer (A : Set G') ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G')))
    (hPB : ¬ A ⊓ Subgroup.centralizer (L : Set G') ≤ (Subgroup.center P).map P.subtype)
    (hPAL : ∃ g ∈ P ⊓ L, ∃ y ∈ A ⊓ L, g * y * g⁻¹ ≠ y) :
    9 ≤ Nat.card (Sec4.autIn P A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcommA : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hexpA : ∀ x ∈ A, x ^ 3 = 1 := h.isE27.1.2
  have hA3 : IsPGroup 3 A := fun x => ⟨1, Subtype.ext (by simpa using hexpA x x.2)⟩
  have hPW : P ≤ Subgroup.normalizer (A : Set G') := hP.le.trans inf_le_left
  have hAWH : A ≤ Subgroup.normalizer (A : Set G') ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G') := by
    refine fun x hx => Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hx, ?_⟩
    have hcx : Commute x c := hcommA x hx c h.mem_A
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      rw [(hcx.zpow_right n).eq, mul_inv_cancel_right]
      exact hy
    · intro hy
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hy
      have : y = c ^ n := by
        rw [show y = x⁻¹ * (x * y * x⁻¹) * x by group, ← hn, (hcx.inv_left.zpow_right n).eq,
          inv_mul_cancel_right]
      rw [this]
      exact Subgroup.zpow_mem_zpowers c n
  have hPA : P ⊔ A = P := hP.eq_of_le le_sup_left (sup_le hP.le hAWH)
    (hP.isPGroup.to_sup_of_normal_right' hA3 hPW)
  have hAP : A ≤ P := hPA ▸ le_sup_right
  obtain ⟨b, hb₀, hbZ⟩ := Set.not_subset.mp hPB
  have hb := Subgroup.mem_inf.mp hb₀
  have hbP : b ∈ P := hAP hb.1
  have hbZ' : (⟨b, hbP⟩ : P) ∉ Subgroup.center P := fun hc => hbZ ⟨_, hc, rfl⟩
  rw [Subgroup.mem_center_iff] at hbZ'
  push Not at hbZ'
  obtain ⟨g₂, hg₂⟩ := hbZ'
  have hg₂b : (g₂ : G') * b * (g₂ : G')⁻¹ ≠ b := by
    intro he
    apply hg₂
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    calc (g₂ : G') * b = ((g₂ : G') * b * (g₂ : G')⁻¹) * g₂ := by group
      _ = b * g₂ := by rw [he]
  obtain ⟨g₁, ⟨hg₁P, hg₁L⟩, y, hy, hg₁y⟩ := hPAL
  set τ₁ := A.normalizerMonoidHom ⟨g₁, hPW hg₁P⟩ with hτ₁
  set τ₂ := A.normalizerMonoidHom ⟨g₂, hPW g₂.2⟩ with hτ₂
  have hτ₁S : τ₁ ∈ Sec4.autIn P A := Sec4.mem_autIn_iff.mpr ⟨g₁, _, hg₁P, rfl⟩
  have hτ₂S : τ₂ ∈ Sec4.autIn P A := Sec4.mem_autIn_iff.mpr ⟨g₂, _, g₂.2, rfl⟩
  have hτ₁1 : τ₁ ≠ 1 := by
    intro h1
    apply hg₁y
    have := congrArg (fun σ : MulAut A => ((σ ⟨y, hy.1⟩ : A) : G')) h1
    simpa [hτ₁, Sec4.normalizerMonoidHom_apply_coe] using this
  have hτ₁B : ∀ n : ℤ, (τ₁ ^ n) ⟨b, hb.1⟩ = ⟨b, hb.1⟩ := by
    have hfix : τ₁ ⟨b, hb.1⟩ = ⟨b, hb.1⟩ := by
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe]
      have hcomm : g₁ * b = b * g₁ := Subgroup.mem_centralizer_iff.mp hb.2 g₁ hg₁L
      rw [hcomm, mul_inv_cancel_right]
    intro n
    induction n using Int.induction_on with
    | zero => simp
    | succ n ih => rw [zpow_add_one, MulAut.mul_apply, hfix, ih]
    | pred n ih =>
      rw [zpow_sub_one, MulAut.mul_apply]
      have : τ₁⁻¹ ⟨b, hb.1⟩ = ⟨b, hb.1⟩ := by
        conv_lhs => rw [← hfix]
        exact MulEquiv.symm_apply_apply _ _
      rw [this, ih]
  have hτ₂B : τ₂ ⟨b, hb.1⟩ ≠ ⟨b, hb.1⟩ := by
    intro he
    apply hg₂b
    have := congrArg Subtype.val he
    simpa [hτ₂, Sec4.normalizerMonoidHom_apply_coe] using this
  have hS3 : IsPGroup 3 (Sec4.autIn P A) := by
    have h1 : IsPGroup 3 ((P ⊓ Subgroup.normalizer (A : Set G')).subgroupOf
        (Subgroup.normalizer (A : Set G'))) :=
      (hP.isPGroup.to_le inf_le_left).comap_subtype
    exact h1.map _
  set S := Sec4.autIn P A
  set K := (Subgroup.zpowers τ₁).subgroupOf S
  have hKS : Subgroup.zpowers τ₁ ≤ S := Subgroup.zpowers_le.mpr hτ₁S
  have hKne : K ≠ ⊤ := by
    intro htop
    have : (⟨τ₂, hτ₂S⟩ : S) ∈ K := htop ▸ Subgroup.mem_top _
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp this)
    have hn' : τ₁ ^ n = τ₂ := hn
    apply hτ₂B
    rw [← hn']
    exact hτ₁B n
  have hcardK : Nat.card K = orderOf τ₁ := by
    rw [← Nat.card_zpowers]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKS).toEquiv
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hS3
  have hord3 : 3 ≤ orderOf τ₁ := by
    obtain ⟨j, hj⟩ := (hS3 ⟨τ₁, hτ₁S⟩)
    have hdvd : orderOf τ₁ ∣ 3 ^ j := by
      rw [← Subgroup.orderOf_mk τ₁ hτ₁S]
      exact orderOf_dvd_of_pow_eq_one hj
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rcases i with _ | i
    · exact absurd (orderOf_eq_one_iff.mp (by simpa using hi)) hτ₁1
    · rw [hi, pow_succ]
      exact Nat.le_mul_of_pos_left 3 (by positivity)
  have hidx : 3 ≤ K.index := by
    have hdvd : K.index ∣ 3 ^ a := ha ▸ K.index_dvd_card
    obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rcases i with _ | i
    · exact absurd (Subgroup.index_eq_one.mp (by simpa using hi)) hKne
    · rw [hi, pow_succ]
      exact Nat.le_mul_of_pos_left 3 (by positivity)
  calc 9 = 3 * 3 := by norm_num
    _ ≤ Nat.card K * K.index := Nat.mul_le_mul (hcardK ▸ hord3) hidx
    _ = Nat.card S := K.card_mul_index

theorem autIn_eq_transvectionGroup {G' : Type} [Group G'] [Finite G'] {A : Subgroup G'} {c : G'}
    {L : Subgroup G'} (h : Sec12Std G' A c L) {P : Subgroup G'}
    (hP : IsSylowOf 3 P (Subgroup.normalizer (A : Set G') ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G')))
    (hPB : ¬ A ⊓ Subgroup.centralizer (L : Set G') ≤ (Subgroup.center P).map P.subtype)
    (hPL : P ≤ Subgroup.normalizer (L : Set G')) (hAL : Nat.card (A ⊓ L : Subgroup G') = 9)
    (hPAL : ∃ g ∈ P ⊓ L, ∃ y ∈ A ⊓ L, g * y * g⁻¹ ≠ y) :
    Sec4.autIn P A = transvectionGroup A ⟨c, h.mem_A⟩ ∧ Nat.card (Sec4.autIn P A) = 9 := by
  have hexpA : ∀ x ∈ A, x ^ 3 = 1 := h.isE27.1.2
  have hc3 : orderOf c = 3 := orderOf_eq_prime (hexpA c h.mem_A) h.ne_one
  have hLc : L ≤ Subgroup.centralizer ({c} : Set G') := by
    obtain ⟨L', -, hL'⟩ := h.mem_thetaComponentsAt
    rw [← hL']
    exact Subgroup.map_subtype_le L'
  have hcB : c ∈ A ⊓ Subgroup.centralizer (L : Set G') :=
    ⟨h.mem_A, Subgroup.mem_centralizer_iff.mpr fun l hl =>
      Subgroup.mem_centralizer_singleton_iff.mp (hLc hl)⟩
  obtain ⟨b₀, hb₀, hb₀c⟩ := exists_mem_not_mem_zpowers h.card_B hc3
  obtain ⟨y₀, hy₀, hy₀c⟩ := exists_mem_not_mem_zpowers hAL hc3
  have hB := closure_pair_eq_of_card_nine (fun x hx => hexpA x (Subgroup.mem_inf.mp hx).1)
    h.card_B hcB h.ne_one hb₀ hb₀c
  have hAL' := closure_pair_eq_of_card_nine (fun x hx => hexpA x (Subgroup.mem_inf.mp hx).1) hAL
    ⟨h.mem_A, h.mem_L⟩ h.ne_one hy₀ hy₀c
  have hgen : Subgroup.closure ({c, b₀, y₀} : Set G') = A := by
    rw [← h.sup_eq, ← hB, ← hAL', ← Subgroup.closure_union]
    congr 1
    ext x
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_union]
    tauto
  have hle := autIn_le_transvectionGroup h hP.le hP.isPGroup hPL hAL
  have hT := card_transvectionGroup_le h.mem_A hb₀.1 hy₀.1 hgen hc3
  have h9 := nine_le_card_autIn h hP hPB hPAL
  exact ⟨Subgroup.eq_of_le_of_card_ge hle (hT.trans h9),
    le_antisymm ((Subgroup.card_le_of_le hle).trans hT) h9⟩

theorem item123_of
    (h45 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec12Std G A c L → ∀ P : Subgroup G, IsSylowOf 3 P
        (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
          P ≤ Subgroup.normalizer (L : Set G))
    (hAL : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec12Std G A c L → Nat.card (A ⊓ L : Subgroup G) = 9)
    (hPAL : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec12Std G A c L → ∀ P : Subgroup G, IsSylowOf 3 P
        (Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G)) →
          ∃ g ∈ P ⊓ L, ∃ y ∈ A ⊓ L, g * y * g⁻¹ ≠ y) :
    Item123 := by
  intro G _ _ A c L h P hP hPB
  exact autIn_eq_transvectionGroup h hP hPB (h45 G A c L h P hP) (hAL G A c L h)
    (hPAL G A c L h P hP)

end CFSG.RankThree.PartTwo.Sec12

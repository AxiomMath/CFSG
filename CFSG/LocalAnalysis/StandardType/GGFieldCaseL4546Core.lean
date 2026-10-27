module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Homocyclic
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseXL48Homocyclic

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type} [Group G]

theorem mul_pow_mul_inv_pow_mem {H : Subgroup G} {w x : G} (hw : w ∈ H)
    (hx : x ∈ Subgroup.normalizer (H : Set G)) : ∀ j : ℕ, (w * x) ^ j * (x ^ j)⁻¹ ∈ H := by
  intro j
  induction j with
  | zero => simp
  | succ j ih =>
    have hc : x ^ j * w * (x ^ j)⁻¹ ∈ H :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ hx j) w).mp hw
    have e : (w * x) ^ (j + 1) * (x ^ (j + 1))⁻¹ =
        ((w * x) ^ j * (x ^ j)⁻¹) * (x ^ j * w * (x ^ j)⁻¹) := by
      rw [pow_succ, pow_succ, mul_inv_rev]
      simp only [mul_assoc, inv_mul_cancel_left, mul_inv_cancel_left]
    rw [e]
    exact H.mul_mem ih hc

end General

section Core

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGL45Config.exists_moving_ct (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁) :
    ∃ c ∈ Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G),
      ∃ t ∈ L ⊓ Subgroup.normalizer (Bs : Set G),
        c * t ∈ Subgroup.normalizer (U : Set G) ⊓
          Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) ∧
        c * t ∉ Subgroup.normalizer (Subgroup.zpowers d : Set G) := by
  obtain ⟨t, ht, htd⟩ := ggL45_exists_not_normalizer_zpowers hcfg.1 hcfg.2.1 hcfg.2.2.1
    hcfg.2.2.2.2.2.1
  have : Fact p.Prime := ⟨hcfg.prime⟩
  have hXN := hcfg.1.2.2.1
  have hXn := hcfg.1.2.2.2.2.1
  have hconj : ∀ n ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, n * g * n⁻¹ ∈ X := by
    intro n hn g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨n, hn⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have htX : t ∈ Subgroup.normalizer (X : Set G) :=
    Subgroup.le_normalizer_iff.mpr hconj ht.2
  have htB₁ : t ∈ Subgroup.normalizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨ht.2, ggNormalizer_le_normalizer_centralizer X htX⟩
  have htC := ggNormalizer_le_normalizer_centralizer _ htB₁
  have hsetup := hcfg.2.2.2.2.2.2.1
  obtain ⟨c, hc, hcU⟩ :=
    exists_mul_mem_normalizer_of_maxPSubgroup htC hsetup.2.1 hsetup.1 hsetup.2.2.1
  have hcd : c ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    le_normalizer_zpowers_of_le hcfg.d_mem le_rfl hc
  refine ⟨c, hc, t, ht, ⟨hcU, mul_mem (Subgroup.centralizer_le_normalizer _ hc) htB₁⟩,
    fun h => htd ?_⟩
  have := mul_mem (inv_mem hcd) h
  rwa [inv_mul_cancel_left] at this

theorem ggL46_torus (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hiso : GGRawInndiagIsoInput) (hcent : GGL45CentInput) (htorus : GGL45TorusInput)
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) :
    (∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a) ∧ ∃ s : ℕ, 2 ≤ s ∧ (∀ u ∈ U₁, u ^ p ^ s = 1) ∧
      (∃ u ∈ U₁, orderOf u = p ^ s) ∧
      ∃ x' : G, Subgroup.zpowers x' = Subgroup.zpowers x ∧
        ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1)) := by
  have hcfg := ggL45Config_of_setup hS
  have : Fact p.Prime := ⟨hcfg.prime⟩
  obtain ⟨c, hc, t, ht, hr, hrd⟩ := hcfg.exists_moving_ct
  have hii := ggL45_inf_conj_eq_one hraw hiso hcent hcfg hr hrd
  have hrU₁ : c * t ∈ Subgroup.normalizer (U₁ : Set G) := hS.2.2.2.2.2.2.2.2 hr
  have hconj : ∀ a ∈ U₁, (c * t) * a * (c * t)⁻¹ ∈ U₁ := fun a ha =>
    (Subgroup.mem_normalizer_iff.mp hrU₁ a).mp ha
  obtain ⟨s, hs, hcommV, hexpV, ⟨u₀, hu₀, hu₀V⟩, x', hx'x, hx'V⟩ :=
    htorus G p B Bs x L D J X B₂ d y K U U₁ hcfg
  have hab : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a := by
    intro a ha b hb
    have h2 : (c * t) * (a * b * a⁻¹ * b⁻¹) * (c * t)⁻¹ ∈
        U ⊓ Subgroup.centralizer (K : Set G) := by
      have := hcommV _ (hconj a ha) _ (hconj b hb)
      have e : (c * t) * (a * b * a⁻¹ * b⁻¹) * (c * t)⁻¹ =
          ((c * t) * a * (c * t)⁻¹) * ((c * t) * b * (c * t)⁻¹) *
            ((c * t) * a * (c * t)⁻¹)⁻¹ * ((c * t) * b * (c * t)⁻¹)⁻¹ := by group
      rw [e]
      exact this
    have h3 := hii _ (hcommV a ha b hb) h2
    calc a * b = (a * b * a⁻¹ * b⁻¹) * (b * a) := by group
      _ = b * a := by rw [h3, one_mul]
  have hexp : ∀ u ∈ U₁, u ^ p ^ s = 1 := by
    intro u hu
    refine hii _ (hexpV u hu) ?_
    rw [← conj_pow]
    exact hexpV _ (hconj u hu)
  have hs1 : 1 ≤ s := by omega
  have hord : ∃ u ∈ U₁, orderOf u = p ^ s := by
    refine ⟨u₀, hu₀, ?_⟩
    have hne : ¬ u₀ ^ p ^ (s - 1) = 1 := fun h => hu₀V (h ▸ one_mem _)
    have h := orderOf_eq_prime_pow hne (by rw [Nat.sub_add_cancel hs1]; exact hexp u₀ hu₀)
    rwa [Nat.sub_add_cancel hs1] at h
  have hxU : x ∈ U := hcfg.bs_le hcfg.x_mem
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) :=
    hcfg.1.1.1.2.2.2.2.2.2.1.2.2.2.1.1
  have htx : t * x * t⁻¹ = x := by
    have h1 := Subgroup.mem_centralizer_iff.mp (hLx ht.1) x rfl
    rw [← h1, mul_inv_cancel_right]
  have hrx : (c * t) * x * (c * t)⁻¹ = c * x * c⁻¹ := by
    rw [show (c * t) * x * (c * t)⁻¹ = c * (t * x * t⁻¹) * c⁻¹ by group, htx]
  have hcB₁ : c ∈ Subgroup.normalizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hc
  have hcd : c ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) :=
    le_normalizer_zpowers_of_le hcfg.d_mem le_rfl hc
  have hcK := ggL45_normalizer_le_of_canonical hcfg.1 hcfg.2.2.2.2.2.1 ⟨hcB₁, hcd⟩
  have hcxU : c * x * c⁻¹ ∈ U := by
    rw [← hrx]
    exact (Subgroup.mem_normalizer_iff.mp hr.1 x).mp hxU
  have hw₀ : (c * t) * x * (c * t)⁻¹ * x⁻¹ ∈ U₁ := by
    rw [hrx]
    exact ggL4546_comm_mem hraw hcen hiso hcfg hcK hcxU
  obtain ⟨j, rfl⟩ : ∃ j : ℕ, x ^ j = x' := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_iff_mem_zpowers.mpr (hx'x ▸ Subgroup.mem_zpowers x'))
  have hxN : x ∈ Subgroup.normalizer (U₁ : Set G) := hcfg.le_normalizer_part hxU
  have hw' : (c * t) * x ^ j * (c * t)⁻¹ * (x ^ j)⁻¹ ∈ U₁ := by
    have h := mul_pow_mul_inv_pow_mem hw₀ hxN j
    rw [show (c * t) * x * (c * t)⁻¹ * x⁻¹ * x = (c * t) * x * (c * t)⁻¹ by group,
      conj_pow] at h
    exact h
  set w' := (c * t) * x ^ j * (c * t)⁻¹ * (x ^ j)⁻¹ with hw'def
  have hy : (c * t) * x ^ j * (c * t)⁻¹ = w' * x ^ j := by rw [hw'def]; group
  refine ⟨hab, s, hs, hexp, hord, x ^ j, hx'x, fun u hu => ?_⟩
  set e := 1 + p ^ (s - 1) with he
  have hu' : (c * t) * u * (c * t)⁻¹ ∈ U₁ := hconj u hu
  have hw'u : w'⁻¹ * ((c * t) * u * (c * t)⁻¹) * w' = (c * t) * u * (c * t)⁻¹ := by
    rw [mul_assoc, hab _ hu' _ hw', inv_mul_cancel_left]
  have key : (c * t) * ((u ^ e)⁻¹ * ((x ^ j)⁻¹ * u * x ^ j)) * (c * t)⁻¹ =
      (((c * t) * u * (c * t)⁻¹) ^ e)⁻¹ *
        ((x ^ j)⁻¹ * ((c * t) * u * (c * t)⁻¹) * x ^ j) := by
    have h1 : ((c * t) * u * (c * t)⁻¹) ^ e = (c * t) * u ^ e * (c * t)⁻¹ := conj_pow
    calc (c * t) * ((u ^ e)⁻¹ * ((x ^ j)⁻¹ * u * x ^ j)) * (c * t)⁻¹
        = ((c * t) * u ^ e * (c * t)⁻¹)⁻¹ * (((c * t) * x ^ j * (c * t)⁻¹)⁻¹ *
            ((c * t) * u * (c * t)⁻¹) * ((c * t) * x ^ j * (c * t)⁻¹)) := by group
      _ = (((c * t) * u * (c * t)⁻¹) ^ e)⁻¹ * ((w' * x ^ j)⁻¹ *
            ((c * t) * u * (c * t)⁻¹) * (w' * x ^ j)) := by rw [h1, hy]
      _ = (((c * t) * u * (c * t)⁻¹) ^ e)⁻¹ * ((x ^ j)⁻¹ *
            (w'⁻¹ * ((c * t) * u * (c * t)⁻¹) * w') * x ^ j) := by group
      _ = _ := by rw [hw'u]
  have h1 := hii _ (hx'V u hu) (by rw [key]; exact hx'V _ hu')
  have h2 := congrArg (fun g => u ^ e * g) h1
  simp only [mul_one, mul_inv_cancel_left] at h2
  exact h2

theorem ggL46_omega (hraw : GGRawInnFieldInput) (hiso : GGRawInndiagIsoInput)
    (homega : GGL45OmegaInput) (hcfg : GGL45Config p B Bs x L D J X B₂ d y K U U₁)
    (hab : ∀ a ∈ U₁, ∀ b ∈ U₁, a * b = b * a) {s : ℕ} (hs : 2 ≤ s)
    (hexp : ∀ u ∈ U₁, u ^ p ^ s = 1) {x' : G} (hx'x : Subgroup.zpowers x' = Subgroup.zpowers x)
    (hact : ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1))) :
    (∀ u ∈ U, u ^ p = 1 → u ∈ Bs) ∧
      ∀ u : G, u ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ↔ u ∈ U₁ ∧ u ^ p = 1 := by
  have : Fact p.Prime := ⟨hcfg.prime⟩
  have hp := hcfg.prime
  obtain ⟨hB₁U₁, hxU₁, hVU₁⟩ := ggL4546_basic hraw hiso hcfg
  have hps : p ^ (s - 1) = p * p ^ (s - 2) := by
    rw [← pow_succ']
    congr 1
    omega
  have hgen : ∀ a : G, a ^ p = 1 → a ^ p ^ (s - 1) = 1 := fun a ha => by
    rw [hps, pow_mul, ha, one_pow]
  have hΩU : ∀ u ∈ U, u ^ p = 1 → u ∈ Bs := by
    intro u hu hup
    have hV1 : (1 : G) ∈ U ⊓ Subgroup.centralizer (K : Set G) := one_mem _
    have hu' := homega G p B Bs x L D J X B₂ d y K U U₁ hcfg u hu (hup ▸ hV1)
    have hN : Bs ≤ Subgroup.normalizer ((U ⊓ Subgroup.centralizer (K : Set G) : Subgroup G) :
        Set G) := fun b hb => by
      apply mem_normalizer_of_forall_conj_mem
      intro v hv
      have := hcfg.conj_mem_V (U.inv_mem (hcfg.bs_le hb)) hv
      rwa [inv_inv] at this
    rw [← SetLike.mem_coe, Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hu'
    obtain ⟨b, hb, v, hv, rfl⟩ := hu'
    have hN' : Bs ⊓ Subgroup.centralizer (X : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers x : Set G) := fun b hb =>
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
        exact (Commute.zpow_left (mul_comm_of_isElemAbelian hcfg.isElemAbelian hcfg.x_mem hb.1)
          k).eq)
    have hb' : b ∈ ((Bs ⊓ Subgroup.centralizer (X : Set G) ⊔ Subgroup.zpowers x : Subgroup G) :
        Set G) := by
      rw [← hcfg.2.2.1.2]
      exact hb
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN'] at hb'
    obtain ⟨b₁, hb₁, z, hz, rfl⟩ := hb'
    have hzBs : z ∈ Bs := (Subgroup.zpowers_le.mpr hcfg.x_mem) hz
    have hz' : z ∈ Subgroup.zpowers x' := hx'x ▸ hz
    obtain ⟨m, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz')
    have hvU₁ : v ∈ U₁ := hVU₁ hv
    have haU₁ : (v ^ p ^ (s - 1)) ^ m ∈ U₁ := U₁.pow_mem (U₁.pow_mem hvU₁ _) _
    have hap : ((v ^ p ^ (s - 1)) ^ m) ^ p = 1 := by
      have h1 : (v ^ p ^ (s - 1)) ^ p = 1 := by
        rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega), hexp v hvU₁]
      rw [← pow_mul, mul_comm, pow_mul, h1, one_pow]
    have hxu : (x' ^ m)⁻¹ * v * x' ^ m = v * (v ^ p ^ (s - 1)) ^ m :=
      conj_pow_eq_mul_pow_pow hs hexp hact m v hvU₁
    have hxa : (x' ^ m)⁻¹ * (v ^ p ^ (s - 1)) ^ m * x' ^ m = (v ^ p ^ (s - 1)) ^ m := by
      rw [conj_pow_eq_mul_pow_pow hs hexp hact m _ haU₁, hgen _ hap, one_pow, mul_one]
    have hua : Commute v ((v ^ p ^ (s - 1)) ^ m) := hab v hvU₁ _ haU₁
    have hx'p : (x' ^ m) ^ p = 1 := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
      rw [← hk, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hcfg.x_pow,
        one_zpow]
    have hpow := GGL48.mul_pow_prime_eq hp hcfg.odd hxu hxa hua hx'p hap
    have hxvU : x' ^ m * v ∈ U := U.mul_mem (hcfg.bs_le hzBs) hv.1
    have hcommb : Commute b₁ (x' ^ m * v) :=
      (Subgroup.mem_centralizer_iff.mp (hcfg.le_centralizer hxvU)) b₁ hb₁
    have hb₁p : b₁ ^ p = 1 := hcfg.isElemAbelian.2 b₁ hb₁.1
    have hvp : v ^ p = 1 := by
      beta_reduce at hup
      rw [mul_assoc, hcommb.mul_pow, hb₁p, one_mul, hpow] at hup
      exact hup
    have hvx' : Commute v x' := by
      have h1 := hact v hvU₁
      rw [pow_add, pow_one, hgen v hvp, mul_one] at h1
      calc v * x' = x' * (x'⁻¹ * v * x') := by group
        _ = x' * v := by rw [h1]
    have hvx : v * x = x * v := by
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hx'x ▸ Subgroup.mem_zpowers x :
        x ∈ Subgroup.zpowers x')
      rw [← hk]
      exact (Commute.zpow_right hvx' k).eq
    have hvBs := hcfg.mem_of_commute hv.1 hvx hvp
    exact Bs.mul_mem (Bs.mul_mem hb₁.1 hzBs) hvBs
  refine ⟨hΩU, fun u => ⟨fun hu => ⟨hB₁U₁ hu, hcfg.isElemAbelian.2 u hu.1⟩, ?_⟩⟩
  rintro ⟨hu, hup⟩
  exact hcfg.inf_part_le hB₁U₁ hxU₁ ⟨hΩU u (hcfg.part_le hu) hup, hu⟩

theorem ggL46_card_le (hcover : GGL46CoverInput)
    (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) (habU : IsMulCommutative U₁)
    {s : ℕ} (hs : 2 ≤ s) (hexp : ∀ u ∈ U₁, u ^ p ^ s = 1) {x' : G}
    (hx'x : Subgroup.zpowers x' = Subgroup.zpowers x)
    (hact : ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1))) :
    Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤
      p * Nat.card (ggPowSubgroup U₁ habU (p ^ (s - 1))) := by
  have hcfg := ggL45Config_of_setup hS
  have hp := hcfg.prime
  obtain ⟨j, hj⟩ : ∃ j : ℕ, x' ^ j = x := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_iff_mem_zpowers.mpr (hx'x ▸ Subgroup.mem_zpowers x : x ∈ Subgroup.zpowers x'))
  have hxinv : x' ^ (j * (p - 1)) = x⁻¹ := by
    rw [pow_mul, hj]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hcfg.x_pow]
  have hcomm : ∀ g ∈ X, g * x * g⁻¹ * x⁻¹ ∈ ggPowSubgroup U₁ habU (p ^ (s - 1)) := by
    intro g hg
    obtain ⟨u, hu, hug⟩ := hcover G p B Bs x L D J X B₂ d y K U U₁ hS g hg
    have hc : x * (u⁻¹ * g) = (u⁻¹ * g) * x :=
      (Subgroup.mem_centralizer_iff.mp hug) x hcfg.x_mem
    have hgx : g * x * g⁻¹ = u * x * u⁻¹ := by
      calc g * x * g⁻¹ = u * ((u⁻¹ * g) * x * (u⁻¹ * g)⁻¹) * u⁻¹ := by group
        _ = u * x * u⁻¹ := by rw [← hc, mul_inv_cancel_right]
    have h1 := conj_pow_eq_mul_pow_pow hs hexp hact (j * (p - 1)) u⁻¹ (U₁.inv_mem hu)
    rw [hxinv, inv_inv] at h1
    refine ⟨u⁻¹ ^ (j * (p - 1)), U₁.pow_mem (U₁.inv_mem hu) _, ?_⟩
    rw [hgx]
    calc (u⁻¹ ^ (j * (p - 1))) ^ p ^ (s - 1) = (u⁻¹ ^ p ^ (s - 1)) ^ (j * (p - 1)) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ = u * (x * u⁻¹ * x⁻¹) := by rw [h1]; group
      _ = u * x * u⁻¹ * x⁻¹ := by group
  rcases hS.2.2.2.2.1 with h1 | ⟨-, h2⟩
  · have hle : Bs ⊓ Subgroup.centralizer (X : Set G) ≤ ggPowSubgroup U₁ habU (p ^ (s - 1)) :=
      fun b hb => by
        obtain ⟨g, hg, rfl⟩ := (h1 b).mp hb
        exact hcomm g hg
    calc Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)
        ≤ Nat.card (ggPowSubgroup U₁ habU (p ^ (s - 1))) := Subgroup.card_le_of_le hle
      _ ≤ p * Nat.card (ggPowSubgroup U₁ habU (p ^ (s - 1))) :=
          Nat.le_mul_of_pos_left _ hp.pos
  · have hle : B₂ ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) ≤
        ggPowSubgroup U₁ habU (p ^ (s - 1)) := fun b hb => by
      obtain ⟨g, hg, rfl⟩ := (h2 b).mp ⟨hb.2, hb.1⟩
      exact hcomm g hg
    have hTBM := hS.2.1
    calc Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G)
        ≤ p * Nat.card (B₂ ⊓ (Bs ⊓ Subgroup.centralizer (X : Set G)) : Subgroup G) :=
          card_le_mul_card_inf inf_le_left hTBM.2.1 hTBM.2.2.1
      _ ≤ p * Nat.card (ggPowSubgroup U₁ habU (p ^ (s - 1))) :=
          Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle)

end Core

theorem ggL46CoreInput_of_inputs (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hiso : GGRawInndiagIsoInput) (hcent : GGL45CentInput) (homega : GGL45OmegaInput)
    (htorus : GGL45TorusInput) (hcover : GGL46CoverInput) : GGL46CoreInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS
  have hcfg := ggL45Config_of_setup hS
  have : Fact p.Prime := ⟨hcfg.prime⟩
  have hp := hcfg.prime
  obtain ⟨hab, s, hs, hexp, hord, x', hx'x, hact⟩ := ggL46_torus hraw hcen hiso hcent htorus hS
  have habU : IsMulCommutative U₁ := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  obtain ⟨hΩU, hΩ₁⟩ := ggL46_omega hraw hiso homega hcfg hab hs hexp hx'x hact
  have hcard := ggL46_card_le hcover hS habU hs hexp hx'x hact
  have hOU₁ : ggPowSubgroup U₁ habU (p ^ (s - 1)) ≤ U₁ := by
    rintro _ ⟨u, hu, rfl⟩
    exact U₁.pow_mem hu _
  obtain ⟨r, hr⟩ := IsPGroup.iff_card.mp ((hcfg.isPGroup.to_le hcfg.part_le).to_le hOU₁)
  obtain ⟨H, hHU₁, hHcard, hHB₁⟩ := exists_ggHomocyclic hp (by omega) habU hexp hΩ₁ hr
  refine ⟨habU, ⟨s, hs, hexp, hord, ⟨x', hx'x, hact⟩, H, r, hHU₁, fun h hh => hexp h (hHU₁ hh),
    hHcard, hHB₁, ?_⟩, hΩ₁, hΩU⟩
  rw [hr] at hcard
  rw [pow_succ, mul_comm]
  exact hcard

theorem ggL46Input_of_inputs (h43 : GGL43Input) (hraw : GGRawInnFieldInput)
    (hcen : GGRawFieldCentralInput) (hiso : GGRawInndiagIsoInput) (hcent : GGL45CentInput)
    (homega : GGL45OmegaInput) (htorus : GGL45TorusInput) (hcover : GGL46CoverInput)
    (hcyc : GGL46CyclicInput) : GGL46Input :=
  ggL46Input_of_core h43 (ggL46CoreInput_of_inputs hraw hcen hiso hcent homega htorus hcover)
    hcyc

end CFSG.StandardType

end

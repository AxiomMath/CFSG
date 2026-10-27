module

public import CFSG.LocalAnalysis.StandardType.GGFieldCaseL4546Core

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section General

variable {G : Type} [Group G]

theorem exists_inv_mul_mem_of_maxPSubgroup [Finite G] {p : ℕ} [Fact p.Prime]
    {C U X Z : Subgroup G} (hUp : IsPGroup p U) (hUC : U ≤ C)
    (hmax : ∀ Q : Subgroup G, Q ≤ C → IsPGroup p Q → U ≤ Q → Q = U) (hXC : X ≤ C)
    (hUX : U ≤ Subgroup.normalizer (X : Set G)) (hUZ : U ≤ Subgroup.normalizer (Z : Set G))
    (hXZ : X ≤ Subgroup.normalizer (Z : Set G)) (hXp : ∀ g ∈ X, ∃ k : ℕ, g ^ p ^ k ∈ Z) :
    ∀ g ∈ X, ∃ u ∈ U, u⁻¹ * g ∈ Z := by
  intro g hg
  set H : Subgroup G := U ⊔ X with hH
  have hUH : U ≤ H := le_sup_left
  have hXH : X ≤ H := le_sup_right
  have hHC : H ≤ C := sup_le hUC hXC
  have hHZ : H ≤ Subgroup.normalizer (Z : Set G) := sup_le hUZ hXZ
  have hHX : H ≤ Subgroup.normalizer (X : Set G) := sup_le hUX Subgroup.le_normalizer
  have hZn : (Z.subgroupOf H).Normal := by
    refine ⟨fun n hn h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHZ h.2) n).mp hn
  have hXn : (X.subgroupOf H).Normal := by
    refine ⟨fun n hn h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    exact (Subgroup.mem_normalizer_iff.mp (hHX h.2) n).mp hn
  obtain ⟨S, hS⟩ := (hUp.comap_subtype (K := H)).exists_le_sylow
  have hSU : (S : Subgroup H).map H.subtype = U :=
    hmax _ ((Subgroup.map_subtype_le _).trans hHC) (S.isPGroup'.map _)
      (fun u hu => ⟨⟨u, hUH hu⟩, hS (Subgroup.mem_subgroupOf.mpr hu), rfl⟩)
  set π : H →* H ⧸ Z.subgroupOf H := QuotientGroup.mk' (Z.subgroupOf H) with hπ
  have hπs : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hXp' : IsPGroup p ((X.subgroupOf H).map π) := by
    rintro ⟨_, ⟨h, hhX, rfl⟩⟩
    obtain ⟨k, hk⟩ := hXp h (Subgroup.mem_subgroupOf.mp hhX)
    refine ⟨k, Subtype.ext ?_⟩
    change π h ^ p ^ k = 1
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      Subgroup.mem_subgroupOf]
    simpa using hk
  have : ((X.subgroupOf H).map π).Normal := Subgroup.Normal.map hXn π hπs
  have hle := hXp'.le_sylow_of_normal (S.mapSurjective hπs)
  have hgmem : π ⟨g, hXH hg⟩ ∈ ((S.mapSurjective hπs : Sylow p _) : Subgroup _) :=
    hle ⟨⟨g, hXH hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
  rw [Sylow.coe_mapSurjective] at hgmem
  obtain ⟨u, huS, hu⟩ := hgmem
  have huU : (u : G) ∈ U := hSU ▸ ⟨u, huS, rfl⟩
  refine ⟨u, huU, ?_⟩
  have h1 : u⁻¹ * ⟨g, hXH hg⟩ ∈ Z.subgroupOf H := by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hu
    exact hu
  rw [Subgroup.mem_subgroupOf] at h1
  simpa using h1

theorem eq_one_of_mem_of_mem_zpowers [Finite G] {p : ℕ} [Fact p.Prime] {B₁ : Subgroup G}
    {x z : G}
    (hxp : x ^ p = 1) (hxB₁ : x ∉ B₁) (hz : z ∈ B₁) (hzx : z ∈ Subgroup.zpowers x) : z = 1 := by
  by_contra hz1
  apply hxB₁
  have h := zpowers_eq_of_mem_of_ne_one hxp hzx hz1
  exact (Subgroup.zpowers_le.mpr hz) (h ▸ Subgroup.mem_zpowers x)

theorem comm_mem_of_pow_prime_pow_eq_one [Finite G] {p : ℕ} [Fact p.Prime] {B₁ Bs : Subgroup G}
    {x w : G} (hBs : IsElemAbelian p Bs) (hsplit : Bs = B₁ ⊔ Subgroup.zpowers x)
    (hxB₁ : x ∉ B₁) (hwN : ∀ b ∈ Bs, w * b * w⁻¹ ∈ Bs) (hwC : ∀ b ∈ B₁, w * b = b * w)
    {n : ℕ} (hwn : w ^ p ^ n = 1) : w * x * w⁻¹ * x⁻¹ ∈ B₁ := by
  have hp : p.Prime := Fact.out
  have hB₁Bs : B₁ ≤ Bs := hsplit ▸ le_sup_left
  have hx : x ∈ Bs := hsplit ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  have hxp : x ^ p = 1 := hBs.2 x hx
  have hx1 : x ≠ 1 := fun h => hxB₁ (h ▸ B₁.one_mem)
  have hox : orderOf x = p := orderOf_eq_prime hxp hx1
  have hN : B₁ ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := fun b hb =>
    Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (Commute.zpow_left (mul_comm_of_isElemAbelian hBs hx (hB₁Bs hb)) k).eq)
  have hwx : w * x * w⁻¹ ∈ ((B₁ ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
    rw [← hsplit]
    exact hwN x hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hwx
  obtain ⟨b, hb, z, hz, hbz⟩ := hwx
  obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
  have hbx : Commute b (x ^ k) :=
    mul_comm_of_isElemAbelian hBs (hB₁Bs hb) (Bs.pow_mem hx k)
  have hiter : ∀ j : ℕ, ∃ b' ∈ B₁, w ^ j * x * (w ^ j)⁻¹ = b' * x ^ (k ^ j) := by
    intro j
    induction j with
    | zero => exact ⟨1, B₁.one_mem, by simp⟩
    | succ j ih =>
      obtain ⟨b', hb', hj⟩ := ih
      refine ⟨b' * b ^ (k ^ j), B₁.mul_mem hb' (B₁.pow_mem hb _), ?_⟩
      have e1 : w ^ (j + 1) * x * (w ^ (j + 1))⁻¹ = w * (w ^ j * x * (w ^ j)⁻¹) * w⁻¹ := by
        rw [pow_succ']
        group
      have hwb' : w * b' * w⁻¹ = b' := by rw [hwC b' hb', mul_inv_cancel_right]
      have e2 : w * (b' * x ^ (k ^ j)) * w⁻¹ = (w * b' * w⁻¹) * (w * x * w⁻¹) ^ (k ^ j) := by
        rw [conj_pow]
        group
      rw [e1, hj, e2, hwb', ← hbz, hbx.mul_pow, ← pow_mul, mul_assoc, pow_succ, mul_comm k]
  obtain ⟨b', hb', hj⟩ := hiter (p ^ n)
  rw [hwn, one_mul, inv_one, mul_one] at hj
  have hb'1 : b' = 1 := by
    have hb'x : b' ∈ Subgroup.zpowers x := by
      have e : b' = x * (x ^ (k ^ p ^ n))⁻¹ := by
        rw [eq_mul_inv_iff_mul_eq]
        exact hj.symm
      rw [e]
      exact Subgroup.mul_mem _ (Subgroup.mem_zpowers x)
        (Subgroup.inv_mem _ (Subgroup.pow_mem _ (Subgroup.mem_zpowers x) _))
    exact eq_one_of_mem_of_mem_zpowers hxp hxB₁ hb' hb'x
  rw [hb'1, one_mul] at hj
  have hK : k ^ p ^ n ≡ 1 [MOD p] := by
    have h := (pow_eq_pow_iff_modEq (x := x) (n := k ^ p ^ n) (m := 1)).mp (by rw [pow_one, ← hj])
    rwa [hox] at h
  have hk1 : k ≡ 1 [MOD p] := by
    have h1 := (ZMod.natCast_eq_natCast_iff _ _ _).mpr hK
    push_cast at h1
    rw [ZMod.pow_card_pow] at h1
    exact (ZMod.natCast_eq_natCast_iff _ _ _).mp (by simpa using h1)
  have hxk : x ^ k = x := by
    have h := (pow_eq_pow_iff_modEq (x := x) (n := k) (m := 1)).mpr (by rw [hox]; exact hk1)
    rwa [pow_one] at h
  rw [← hbz, hxk, mul_inv_cancel_right]
  exact hb

theorem pow_conj_eq_pow_mul {w x c : G} (h : w * x * w⁻¹ = c * x) (hwc : w * c = c * w) :
    ∀ k : ℕ, w ^ k * x * (w ^ k)⁻¹ = c ^ k * x := by
  intro k
  induction k with
  | zero => simp
  | succ k ih =>
    have hwck : w * c ^ k * w⁻¹ = c ^ k := by
      rw [(Commute.pow_right hwc k).eq, mul_inv_cancel_right]
    calc w ^ (k + 1) * x * (w ^ (k + 1))⁻¹ = w * (w ^ k * x * (w ^ k)⁻¹) * w⁻¹ := by
          rw [pow_succ']
          group
      _ = (w * c ^ k * w⁻¹) * (w * x * w⁻¹) := by rw [ih]; group
      _ = c ^ (k + 1) * x := by rw [hwck, h, pow_succ, mul_assoc]

end General

section Core

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J X B₂ : Subgroup G} {d y : G} {K U U₁ : Subgroup G}

theorem GGFieldCaseSetup.le_centralizer_x (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁) :
    L ≤ Subgroup.centralizer ({x} : Set G) :=
  hS.1.1.1.2.2.2.2.2.2.1.2.2.2.1.1

theorem ggL46_conj_mem_pow (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (habU : IsMulCommutative U₁) {N : ℕ}
    (hΩB₁ : ggPowSubgroup U₁ habU N ≤ Bs ⊓ Subgroup.centralizer (X : Set G))
    {n : G} (hn : n ∈ Subgroup.normalizer (Bs : Set G)) {t : G}
    (ht : t ∈ ggPowSubgroup U₁ habU N) : n * t * n⁻¹ ∈ ggPowSubgroup U₁ habU N := by
  have hcfg := ggL45Config_of_setup hS
  have : Fact p.Prime := ⟨hcfg.prime⟩
  have hXN := hcfg.1.2.2.1
  have hXn := hcfg.1.2.2.2.2.1
  have hconj : ∀ m ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, m * g * m⁻¹ ∈ X := by
    intro m hm g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨m, hm⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hnX : n ∈ Subgroup.normalizer (X : Set G) := Subgroup.le_normalizer_iff.mpr hconj hn
  have hnB₁ : n ∈ Subgroup.normalizer
      ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hn, ggNormalizer_le_normalizer_centralizer X hnX⟩
  have hnC := ggNormalizer_le_normalizer_centralizer _ hnB₁
  have hsetup := hS.2.2.2.2.2.2.1
  obtain ⟨c, hc, hcU⟩ :=
    exists_mul_mem_normalizer_of_maxPSubgroup hnC hsetup.2.1 hsetup.1 hsetup.2.2.1
  have hm : c * n ∈ Subgroup.normalizer (U : Set G) ⊓
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) : Set G) :=
    ⟨hcU, mul_mem (Subgroup.centralizer_le_normalizer _ hc) hnB₁⟩
  have hmU₁ : c * n ∈ Subgroup.normalizer (U₁ : Set G) := hS.2.2.2.2.2.2.2.2 hm
  obtain ⟨u, hu, rfl⟩ := ht
  have h1 : (c * n) * u ^ N * (c * n)⁻¹ ∈ ggPowSubgroup U₁ habU N :=
    ⟨(c * n) * u * (c * n)⁻¹, (Subgroup.mem_normalizer_iff.mp hmU₁ u).mp hu, conj_pow⟩
  have hcomm : (c * n) * u ^ N * (c * n)⁻¹ * c = c * ((c * n) * u ^ N * (c * n)⁻¹) :=
    (Subgroup.mem_centralizer_iff.mp hc) _ (hΩB₁ h1)
  have e : n * u ^ N * n⁻¹ = c⁻¹ * ((c * n) * u ^ N * (c * n)⁻¹) * c := by group
  rw [e, mul_assoc, hcomm, inv_mul_cancel_left]
  exact h1

theorem ggL46_card_le_of_cyclic (hS : GGFieldCaseSetup p B Bs x L D J X B₂ d y K U U₁)
    (habU : IsMulCommutative U₁) {s : ℕ} (hs : 2 ≤ s) (hexp : ∀ u ∈ U₁, u ^ p ^ s = 1)
    {x' : G} (hx'x : Subgroup.zpowers x' = Subgroup.zpowers x)
    (hact : ∀ u ∈ U₁, x'⁻¹ * u * x' = u ^ (1 + p ^ (s - 1)))
    (hΩU : ∀ u ∈ U, u ^ p = 1 → u ∈ Bs)
    (hΩ₁ : ∀ u : G, u ∈ Bs ⊓ Subgroup.centralizer (X : Set G) ↔ u ∈ U₁ ∧ u ^ p = 1)
    {g₀ : G} (hg₀ : g₀ ∈ U) (hcyc : U ≤ Subgroup.zpowers g₀ ⊔ U₁) :
    Nat.card (Bs ⊓ Subgroup.centralizer (X : Set G) : Subgroup G) ≤
      p * Nat.card (ggPowSubgroup U₁ habU (p ^ (s - 1))) := by
  have hcfg := ggL45Config_of_setup hS
  have hp := hcfg.prime
  have : Fact p.Prime := ⟨hp⟩
  have hconf := hS.1.1
  have hBs := hcfg.isElemAbelian
  have hxBs := hcfg.x_mem
  have hxp := hcfg.x_pow
  have hL43 : GGL43 Bs x X := hS.2.2.1
  set B₁ : Subgroup G := Bs ⊓ Subgroup.centralizer (X : Set G) with hB₁
  set Ω : Subgroup G := ggPowSubgroup U₁ habU (p ^ (s - 1)) with hΩ
  have hsplit : Bs = B₁ ⊔ Subgroup.zpowers x := hL43.2
  have hxB₁ : x ∉ B₁ := hL43.1
  have hΩB₁ : Ω ≤ B₁ := by
    rintro _ ⟨u, hu, rfl⟩
    refine (hΩ₁ _).mpr ⟨U₁.pow_mem hu _, ?_⟩
    rw [← pow_mul, ← pow_succ, Nat.sub_add_cancel (by omega), hexp u hu]
  have hUN : ∀ w ∈ U, ∀ b ∈ Bs, w * b * w⁻¹ ∈ Bs := by
    intro w hw b hb
    refine hΩU _ (U.mul_mem (U.mul_mem hw (hcfg.bs_le hb)) (U.inv_mem hw)) ?_
    rw [conj_pow, hBs.2 b hb, mul_one, mul_inv_cancel]
  have hUC : ∀ w ∈ U, ∀ b ∈ B₁, w * b = b * w := fun w hw b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hcfg.le_centralizer hw)) b hb).symm
  obtain ⟨j, hj⟩ : ∃ j : ℕ, x' ^ j = x := (Submonoid.mem_powers_iff _ _).mp
    (mem_powers_iff_mem_zpowers.mpr (hx'x ▸ Subgroup.mem_zpowers x : x ∈ Subgroup.zpowers x'))
  have hxinv : x' ^ (j * (p - 1)) = x⁻¹ := by
    rw [pow_mul, hj]
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel hp.one_lt.le, hxp]
  have hcommU₁ : ∀ u ∈ U₁, u * x * u⁻¹ * x⁻¹ ∈ Ω := by
    intro u hu
    have h1 := conj_pow_eq_mul_pow_pow hs hexp hact (j * (p - 1)) u⁻¹ (U₁.inv_mem hu)
    rw [hxinv, inv_inv] at h1
    refine ⟨u⁻¹ ^ (j * (p - 1)), U₁.pow_mem (U₁.inv_mem hu) _, ?_⟩
    calc (u⁻¹ ^ (j * (p - 1))) ^ p ^ (s - 1) = (u⁻¹ ^ p ^ (s - 1)) ^ (j * (p - 1)) := by
          rw [← pow_mul, ← pow_mul, mul_comm]
      _ = u * (x * u⁻¹ * x⁻¹) := by rw [h1]; group
      _ = u * x * u⁻¹ * x⁻¹ := by group
  obtain ⟨n₀, hn₀⟩ := hcfg.isPGroup ⟨g₀, hg₀⟩
  have hg₀n : g₀ ^ p ^ n₀ = 1 := by simpa using congrArg Subtype.val hn₀
  have hc : g₀ * x * g₀⁻¹ * x⁻¹ ∈ B₁ :=
    comm_mem_of_pow_prime_pow_eq_one hBs hsplit hxB₁ (hUN g₀ hg₀) (hUC g₀ hg₀) hg₀n
  set c := g₀ * x * g₀⁻¹ * x⁻¹ with hcdef
  have hcx : g₀ * x * g₀⁻¹ = c * x := by rw [hcdef]; group
  have hiter := pow_conj_eq_pow_mul hcx (hUC g₀ hg₀ c hc)
  have hcN : c ∈ Subgroup.normalizer (Ω : Set G) := by
    apply mem_normalizer_of_forall_conj_mem
    intro t ht
    have htc : t * c = c * t := mul_comm_of_isElemAbelian hBs (hΩB₁ ht).1 hc.1
    rw [mul_assoc, htc, inv_mul_cancel_left]
    exact ht
  have hzN : Subgroup.zpowers g₀ ≤ Subgroup.normalizer (U₁ : Set G) :=
    Subgroup.zpowers_le.mpr (hcfg.le_normalizer_part hg₀)
  have hφU : ∀ w ∈ U, w * x * w⁻¹ * x⁻¹ ∈ Subgroup.zpowers c ⊔ Ω := by
    intro w hw
    have hw' : w ∈ ((Subgroup.zpowers g₀ ⊔ U₁ : Subgroup G) : Set G) := hcyc hw
    rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hzN] at hw'
    obtain ⟨z, hz, u, hu, rfl⟩ := hw'
    obtain ⟨k, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp (mem_powers_iff_mem_zpowers.mpr hz)
    set a := u * x * u⁻¹ * x⁻¹ with ha
    have haΩ : a ∈ Ω := hcommU₁ u hu
    have hux : u * x * u⁻¹ = a * x := by rw [ha]; group
    have hza : g₀ ^ k * a * (g₀ ^ k)⁻¹ = a := by
      rw [hUC (g₀ ^ k) (U.pow_mem hg₀ k) a (hΩB₁ haΩ), mul_inv_cancel_right]
    have e : g₀ ^ k * u * x * (g₀ ^ k * u)⁻¹ * x⁻¹ =
        (g₀ ^ k * (u * x * u⁻¹) * (g₀ ^ k)⁻¹) * x⁻¹ := by group
    have e2 : g₀ ^ k * (a * x) * (g₀ ^ k)⁻¹ =
        (g₀ ^ k * a * (g₀ ^ k)⁻¹) * (g₀ ^ k * x * (g₀ ^ k)⁻¹) := by group
    rw [e, hux, e2, hza, hiter k, show a * (c ^ k * x) * x⁻¹ = a * c ^ k by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right haΩ)
      (Subgroup.mem_sup_left (Subgroup.pow_mem _ (Subgroup.mem_zpowers c) k))
  have hXN := hcfg.1.2.2.1
  have hXn := hcfg.1.2.2.2.2.1
  have hXp := hcfg.1.2.2.2.2.2.1
  have hXC : X ≤ Subgroup.centralizer (B₁ : Set G) := by
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact ((Subgroup.mem_centralizer_iff.mp hb.2) g hg).symm
  have hUNs : U ≤ Subgroup.normalizer (Bs : Set G) := fun w hw =>
    mem_normalizer_of_forall_conj_mem fun b hb => by
      have := hUN w⁻¹ (U.inv_mem hw) b hb
      rwa [inv_inv] at this
  have hconjX : ∀ m ∈ Subgroup.normalizer (Bs : Set G), ∀ g ∈ X, m * g * m⁻¹ ∈ X := by
    intro m hm g hg
    have := hXn.conj_mem ⟨g, hXN hg⟩ (Subgroup.mem_subgroupOf.mpr hg) ⟨m, hm⟩
    simpa [Subgroup.mem_subgroupOf] using this
  have hUX : U ≤ Subgroup.normalizer (X : Set G) :=
    hUNs.trans (Subgroup.le_normalizer_iff.mpr hconjX)
  have hUZ : U ≤ Subgroup.normalizer (Subgroup.centralizer (Bs : Set G) : Set G) :=
    fun w hw => ggNormalizer_le_normalizer_centralizer Bs (hUNs hw)
  have hXZ : X ≤ Subgroup.normalizer (Subgroup.centralizer (Bs : Set G) : Set G) :=
    fun g hg => ggNormalizer_le_normalizer_centralizer Bs (hXN hg)
  have hsetup := hS.2.2.2.2.2.2.1
  have hcover := exists_inv_mul_mem_of_maxPSubgroup hsetup.2.1 hsetup.1 hsetup.2.2.1 hXC
    hUX hUZ hXZ hXp
  have hφX : ∀ g ∈ X, g * x * g⁻¹ * x⁻¹ ∈ Subgroup.zpowers c ⊔ Ω := by
    intro g hg
    obtain ⟨w, hw, hwg⟩ := hcover g hg
    have hc' : x * (w⁻¹ * g) = (w⁻¹ * g) * x := (Subgroup.mem_centralizer_iff.mp hwg) x hxBs
    have hgx : g * x * g⁻¹ = w * x * w⁻¹ := by
      calc g * x * g⁻¹ = w * ((w⁻¹ * g) * x * (w⁻¹ * g)⁻¹) * w⁻¹ := by group
        _ = w * x * w⁻¹ := by rw [← hc', mul_inv_cancel_right]
    rw [hgx]
    exact hφU w hw
  set Y : Subgroup G := Subgroup.zpowers c ⊔ Ω with hY
  have hcp : c ^ p = 1 := hBs.2 c hc.1
  have hYcard : Nat.card Y ≤ p * Nat.card Ω := by
    have h := card_le_card_inf_mul_of_le_sup (A := Y) (U₁ := Ω) (a := c)
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers c)) hcN le_rfl hp.pos
      (by rw [hcp]; exact Ω.one_mem)
    calc Nat.card Y ≤ Nat.card (Y ⊓ Ω : Subgroup G) * p := h
      _ ≤ Nat.card Ω * p := Nat.mul_le_mul_right p (Subgroup.card_le_of_le inf_le_right)
      _ = p * Nat.card Ω := mul_comm _ _
  have hBsB₁ : Nat.card Bs ≤ Nat.card B₁ * p := by
    have hxN : x ∈ Subgroup.normalizer (B₁ : Set G) :=
      Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun b hb =>
        mul_comm_of_isElemAbelian hBs hb.1 hxBs)
    have h := card_le_card_inf_mul_of_le_sup hxBs hxN
      (by rw [hL43.2, sup_comm]) hp.pos (by rw [hxp]; exact B₁.one_mem)
    rwa [inf_eq_right.mpr (inf_le_left : B₁ ≤ Bs)] at h
  have hB4 : p ^ 4 ≤ Nat.card Bs := by
    have hBc : Nat.card B = p ^ LargeEvenTwoLocalRank p G := hconf.1.2.2.2.2.2.2.1.1.2.1
    have h4 : 4 ≤ LargeEvenTwoLocalRank p G := hconf.1.2.2.2.2.2.1.2.2.2
    calc p ^ 4 ≤ p ^ LargeEvenTwoLocalRank p G := Nat.pow_le_pow_right hp.pos h4
      _ = Nat.card B := hBc.symm
      _ ≤ Nat.card Bs := Subgroup.card_le_of_le hconf.2.1.1
  rcases hS.2.2.2.2.1 with h1 | ⟨-, h2⟩
  ·
    have hle : B₁ ≤ Y := fun b hb => by
      obtain ⟨g, hg, rfl⟩ := (h1 b).mp hb
      exact hφX g hg
    exact (Subgroup.card_le_of_le hle).trans hYcard
  ·
    obtain ⟨hxB₂, hB₂Bs, hcardB₂, hB₂inv, hirr, -⟩ := hS.2.1
    set T : Subgroup G := Ω ⊓ B₂ with hT
    have hLx := hS.le_centralizer_x
    have hTx_inv : ∀ n ∈ L ⊓ Subgroup.normalizer (Bs : Set G), ∀ s' ∈ T ⊔ Subgroup.zpowers x,
        n * s' * n⁻¹ ∈ T ⊔ Subgroup.zpowers x := by
      intro n hn s' hs'
      have hle : T ⊔ Subgroup.zpowers x ≤
          (T ⊔ Subgroup.zpowers x).comap (MulAut.conj n).toMonoidHom := by
        refine sup_le (fun t ht => ?_) (Subgroup.zpowers_le.mpr ?_)
        · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          exact Subgroup.mem_sup_left
            ⟨ggL46_conj_mem_pow hS habU hΩB₁ hn.2 ht.1, hB₂inv n hn t ht.2⟩
        · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          have hnx : n * x * n⁻¹ = x := by
            have h := (Subgroup.mem_centralizer_iff.mp (hLx hn.1)) x rfl
            rw [← h, mul_inv_cancel_right]
          rw [hnx]
          exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
      have := hle hs'
      rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
    have hTxle : T ⊔ Subgroup.zpowers x ≤ B₂ :=
      sup_le inf_le_right (Subgroup.zpowers_le.mpr hxB₂)
    have hB₁B₂ : Nat.card B₁ ≤ p * Nat.card (B₂ ⊓ B₁ : Subgroup G) :=
      card_le_mul_card_inf inf_le_left hB₂Bs hcardB₂
    rcases hirr _ le_sup_right hTxle hTx_inv with hTx | hTx
    ·
      exfalso
      have hT1 : ∀ t ∈ T, t = 1 := fun t ht =>
        eq_one_of_mem_of_mem_zpowers hxp hxB₁ (hΩB₁ ht.1)
          (by rw [← hTx]; exact Subgroup.mem_sup_left ht)
      set A : Subgroup G := B₁ ⊓ B₂ with hA
      have hAY : A ≤ Y := fun b hb => by
        obtain ⟨g, hg, rfl⟩ := (h2 b).mp hb
        exact hφX g hg
      have hAΩ : A ⊓ Ω = ⊥ := by
        rw [eq_bot_iff]
        intro t ht
        exact (Subgroup.mem_bot).mpr (hT1 t ⟨ht.2, ht.1.2⟩)
      have hAN : A ≤ Subgroup.normalizer (Ω : Set G) := fun b hb =>
        mem_normalizer_of_forall_conj_mem fun t ht => by
          have h := mul_comm_of_isElemAbelian hBs (hΩB₁ ht).1 hb.1.1
          rw [mul_assoc, h, inv_mul_cancel_left]
          exact ht
      have hcardAΩ := card_sup_eq_mul_of_inf_eq_bot hAN hAΩ
      have hAcard : Nat.card A ≤ p := by
        have h1 : Nat.card A * Nat.card Ω ≤ p * Nat.card Ω := by
          rw [← hcardAΩ]
          exact (Subgroup.card_le_of_le (sup_le hAY le_sup_right)).trans hYcard
        exact Nat.le_of_mul_le_mul_right h1 Nat.card_pos
      have hBA : Nat.card (B₂ ⊓ B₁ : Subgroup G) = Nat.card A := by rw [hA, inf_comm]
      have hB₁p : Nat.card B₁ ≤ p * p := by
        rw [hBA] at hB₁B₂
        exact hB₁B₂.trans (Nat.mul_le_mul_left p hAcard)
      have hlt : p ^ 4 ≤ p ^ 3 := by
        calc p ^ 4 ≤ Nat.card Bs := hB4
          _ ≤ Nat.card B₁ * p := hBsB₁
          _ ≤ p * p * p := Nat.mul_le_mul_right p hB₁p
          _ = p ^ 3 := by ring
      exact absurd hlt (not_le.mpr (Nat.pow_lt_pow_right hp.one_lt (by norm_num)))
    ·
      have hTN : T ≤ Subgroup.normalizer (Subgroup.zpowers x : Set G) := fun t ht =>
        Subgroup.centralizer_le_normalizer _ (Subgroup.mem_centralizer_iff.mpr fun z hz => by
          obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
          exact (Commute.zpow_left
            (mul_comm_of_isElemAbelian hBs hxBs (hΩB₁ ht.1).1) k).eq)
      have hle : B₂ ⊓ B₁ ≤ Ω := by
        intro b hb
        have hb' : b ∈ ((T ⊔ Subgroup.zpowers x : Subgroup G) : Set G) := by
          rw [hTx]
          exact hb.1
        rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hTN] at hb'
        obtain ⟨t, ht, z, hz, rfl⟩ := hb'
        have hzB₁ : z ∈ B₁ := by
          have := B₁.mul_mem (B₁.inv_mem (hΩB₁ ht.1)) hb.2
          rwa [inv_mul_cancel_left] at this
        have hz1 := eq_one_of_mem_of_mem_zpowers hxp hxB₁ hzB₁ hz
        subst hz1
        simpa using ht.1
      exact hB₁B₂.trans (Nat.mul_le_mul_left _ (Subgroup.card_le_of_le hle))

end Core

theorem ggL46CoreInput_of_cyclic (hraw : GGRawInnFieldInput) (hcen : GGRawFieldCentralInput)
    (hiso : GGRawInndiagIsoInput) (hcent : GGL45CentInput) (homega : GGL45OmegaInput)
    (htorus : GGL45TorusInput) (hcyc : GGL46CyclicInput) : GGL46CoreInput := by
  intro G _ _ p B Bs x L D J X B₂ d y K U U₁ hS
  have hcfg := ggL45Config_of_setup hS
  have : Fact p.Prime := ⟨hcfg.prime⟩
  have hp := hcfg.prime
  obtain ⟨hab, s, hs, hexp, hord, x', hx'x, hact⟩ := ggL46_torus hraw hcen hiso hcent htorus hS
  have habU : IsMulCommutative U₁ := ⟨⟨fun a b => Subtype.ext (hab a a.2 b b.2)⟩⟩
  obtain ⟨hΩU, hΩ₁⟩ := ggL46_omega hraw hiso homega hcfg hab hs hexp hx'x hact
  obtain ⟨g₀, hg₀, hcycU⟩ := hcyc G p B Bs x L D J X B₂ d y K U U₁ hS
  have hcard := ggL46_card_le_of_cyclic hS habU hs hexp hx'x hact hΩU hΩ₁ hg₀ hcycU
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

theorem ggL46Input_of_cyclic (h43 : GGL43Input) (hraw : GGRawInnFieldInput)
    (hcen : GGRawFieldCentralInput) (hiso : GGRawInndiagIsoInput) (hcent : GGL45CentInput)
    (homega : GGL45OmegaInput) (htorus : GGL45TorusInput) (hcyc : GGL46CyclicInput) :
    GGL46Input :=
  ggL46Input_of_core h43 (ggL46CoreInput_of_cyclic hraw hcen hiso hcent homega htorus hcyc) hcyc

end CFSG.StandardType

end

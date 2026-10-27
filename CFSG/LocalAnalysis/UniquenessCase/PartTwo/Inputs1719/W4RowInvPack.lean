module

public import CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit.InvertedAbelian
import CFSG.GroupTheory.ZpowersSupExponent
import CFSG.GroupTheory.TwoReflections
import CFSG.LocalAnalysis.EvenBN.Tits.I21Excl2

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

open CFSG.Quasithin CFSG.HardMathSupport.Meierfrankenfeld.FFToolkit Subgroup

structure InvPack {G : Type*} [Group G] (p m : ℕ) (τ x₁ x₂ h : G) : Prop where
  pow_left : x₁ ^ p = 1
  pow_right : x₂ ^ p = 1
  comm : x₁ * x₂ = x₂ * x₁
  ne_one : x₁ ≠ 1
  not_mem : x₂ ∉ zpowers x₁
  inv_left : τ * x₁ * τ⁻¹ = x₁⁻¹
  inv_right : τ * x₂ * τ⁻¹ = x₂⁻¹
  conj_left : ∃ a b : ℕ, h * x₁ * h⁻¹ = x₁ ^ a * x₂ ^ b
  conj_right : ∃ a b : ℕ, h * x₂ * h⁻¹ = x₁ ^ a * x₂ ^ b
  conj_inv_left : ∃ a b : ℕ, h⁻¹ * x₁ * h = x₁ ^ a * x₂ ^ b
  conj_inv_right : ∃ a b : ℕ, h⁻¹ * x₂ * h = x₁ ^ a * x₂ ^ b
  lines : ∀ a < p, ∀ b < p, x₁ ^ a * x₂ ^ b ≠ 1 → ∀ k : ℕ, 0 < k → k < m → ∀ j < p,
    h ^ k * (x₁ ^ a * x₂ ^ b) * (h ^ k)⁻¹ ≠ (x₁ ^ a * x₂ ^ b) ^ j

private theorem InvPack.map {G H : Type*} [Group G] [Group H] {p m : ℕ} {τ x₁ x₂ h : G}
    {f : G →* H} (hf : Function.Injective f) (P : InvPack p m τ x₁ x₂ h) :
    InvPack p m (f τ) (f x₁) (f x₂) (f h) where
  pow_left := by rw [← map_pow, P.pow_left, map_one]
  pow_right := by rw [← map_pow, P.pow_right, map_one]
  comm := by rw [← map_mul, ← map_mul, P.comm]
  ne_one := fun hh => P.ne_one (hf (by rw [hh, map_one]))
  not_mem := by
    intro hh
    rw [Subgroup.mem_zpowers_iff] at hh
    obtain ⟨k, hk⟩ := hh
    exact P.not_mem (Subgroup.mem_zpowers_iff.2 ⟨k, hf (by rw [map_zpow]; exact hk)⟩)
  inv_left := by
    simpa only [map_mul, map_inv] using congrArg f P.inv_left
  inv_right := by
    simpa only [map_mul, map_inv] using congrArg f P.inv_right
  conj_left := by
    obtain ⟨a, b, hab⟩ := P.conj_left
    exact ⟨a, b, by simpa only [map_mul, map_pow, map_inv] using congrArg f hab⟩
  conj_right := by
    obtain ⟨a, b, hab⟩ := P.conj_right
    exact ⟨a, b, by simpa only [map_mul, map_pow, map_inv] using congrArg f hab⟩
  conj_inv_left := by
    obtain ⟨a, b, hab⟩ := P.conj_inv_left
    exact ⟨a, b, by simpa only [map_mul, map_pow, map_inv] using congrArg f hab⟩
  conj_inv_right := by
    obtain ⟨a, b, hab⟩ := P.conj_inv_right
    exact ⟨a, b, by simpa only [map_mul, map_pow, map_inv] using congrArg f hab⟩
  lines := by
    intro a ha b hb hne k hk hkm j hj heq
    refine P.lines a ha b hb ?_ k hk hkm j hj
      (hf (by simpa only [map_mul, map_pow, map_inv] using heq))
    intro h1
    exact hne (by simpa only [map_mul, map_pow, map_one] using congrArg f h1)

private theorem InvPack.of_map {G H : Type*} [Group G] [Group H] {p m : ℕ} {τ x₁ x₂ h : G}
    {f : G →* H} (hf : Function.Injective f) (P : InvPack p m (f τ) (f x₁) (f x₂) (f h)) :
    InvPack p m τ x₁ x₂ h where
  pow_left := hf (by rw [map_pow, P.pow_left, map_one])
  pow_right := hf (by rw [map_pow, P.pow_right, map_one])
  comm := hf (by rw [map_mul, map_mul, P.comm])
  ne_one := fun hh => P.ne_one (by rw [hh, map_one])
  not_mem := by
    intro hh
    apply P.not_mem
    rw [Subgroup.mem_zpowers_iff] at hh ⊢
    obtain ⟨k, hk⟩ := hh
    exact ⟨k, by rw [← map_zpow, hk]⟩
  inv_left := hf (by rw [map_mul, map_mul, map_inv, map_inv, P.inv_left])
  inv_right := hf (by rw [map_mul, map_mul, map_inv, map_inv, P.inv_right])
  conj_left := by
    obtain ⟨a, b, hab⟩ := P.conj_left
    exact ⟨a, b, hf (show f (h * x₁ * h⁻¹) = f (x₁ ^ a * x₂ ^ b) by
      simpa only [map_mul, map_pow, map_inv] using hab)⟩
  conj_right := by
    obtain ⟨a, b, hab⟩ := P.conj_right
    exact ⟨a, b, hf (show f (h * x₂ * h⁻¹) = f (x₁ ^ a * x₂ ^ b) by
      simpa only [map_mul, map_pow, map_inv] using hab)⟩
  conj_inv_left := by
    obtain ⟨a, b, hab⟩ := P.conj_inv_left
    exact ⟨a, b, hf (show f (h⁻¹ * x₁ * h) = f (x₁ ^ a * x₂ ^ b) by
      simpa only [map_mul, map_pow, map_inv] using hab)⟩
  conj_inv_right := by
    obtain ⟨a, b, hab⟩ := P.conj_inv_right
    exact ⟨a, b, hf (show f (h⁻¹ * x₂ * h) = f (x₁ ^ a * x₂ ^ b) by
      simpa only [map_mul, map_pow, map_inv] using hab)⟩
  lines := by
    intro a ha b hb hne k hk hkm j hj heq
    refine P.lines a ha b hb ?_ k hk hkm j hj
      (by simpa only [map_mul, map_pow, map_inv] using congrArg f heq)
    intro h1
    exact hne (hf (by simpa only [map_mul, map_pow, map_one] using h1))

theorem InvPack.map_iff {G H : Type*} [Group G] [Group H] {p m : ℕ} {τ x₁ x₂ h : G}
    {f : G →* H} (hf : Function.Injective f) :
    InvPack p m (f τ) (f x₁) (f x₂) (f h) ↔ InvPack p m τ x₁ x₂ h :=
  ⟨InvPack.of_map hf, InvPack.map hf⟩

private theorem mem_sup_zpowers_iff_exists_zpow {G : Type*} [Group G] {a b z : G}
    (hc : Commute a b) :
    z ∈ Subgroup.zpowers a ⊔ Subgroup.zpowers b ↔ ∃ i j : ℤ, z = a ^ i * b ^ j := by
  rw [Subgroup.zpowers_eq_closure a, Subgroup.zpowers_eq_closure b,
    ← Subgroup.closure_union]
  have hpair : ({a} ∪ {b} : Set G) = {a, b} := by
    ext x
    simp only [Set.mem_union, Set.mem_singleton_iff, Set.mem_insert_iff]
  rw [hpair]
  constructor
  · intro hz
    exact CFSG.LocalAnalysis.EvenBN.Tits.I21.Excl.exists_zpow_mul_zpow_of_mem_closure hc hz
  · rintro ⟨i, j, rfl⟩
    exact Subgroup.mul_mem _
      (Subgroup.zpow_mem (Subgroup.closure {a, b}) (Subgroup.subset_closure (by simp)) i)
      (Subgroup.zpow_mem (Subgroup.closure {a, b}) (Subgroup.subset_closure (by simp)) j)

private theorem inf_zpowers_eq_bot_of_invPack {W : Type} [CommGroup W] [Finite W] {p m : ℕ}
    [Fact p.Prime] {τ x₁ x₂ h : MulAut W} (P : InvPack p m τ x₁ x₂ h) :
    Subgroup.zpowers x₁ ⊓ Subgroup.zpowers x₂ = ⊥ := by
  have hx1o : orderOf x₁ = p := orderOf_eq_prime P.pow_left P.ne_one
  have hx2ne : x₂ ≠ 1 := fun hh => P.not_mem (by rw [hh]; exact Subgroup.one_mem _)
  have hx2o : orderOf x₂ = p := orderOf_eq_prime P.pow_right hx2ne
  rw [eq_bot_iff]
  intro z hz
  obtain ⟨hz1, hz2⟩ := Subgroup.mem_inf.1 hz
  by_contra hz1'
  have hzp : z ^ p = 1 :=
    orderOf_dvd_iff_pow_eq_one.1 (by simpa [hx1o] using orderOf_dvd_of_mem_zpowers hz1)
  have hzo : orderOf z = p := orderOf_eq_prime hzp hz1'
  have hcardz : Nat.card ↥(Subgroup.zpowers z) = p := by rw [Nat.card_zpowers, hzo]
  have heq1 : Subgroup.zpowers z = Subgroup.zpowers x₁ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz1)
      (by rw [hcardz, Nat.card_zpowers, hx1o])
  have heq2 : Subgroup.zpowers z = Subgroup.zpowers x₂ :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz2)
      (by rw [hcardz, Nat.card_zpowers, hx2o])
  apply P.not_mem
  rw [← heq1, heq2]
  exact Subgroup.mem_zpowers x₂

private theorem card_sup_zpowers_of_invPack {W : Type} [CommGroup W] [Finite W] {p m : ℕ}
    [Fact p.Prime] {τ x₁ x₂ h : MulAut W} (P : InvPack p m τ x₁ x₂ h) :
    Nat.card ↥(Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) = p ^ 2 :=
  (CFSG.GroupTheory.card_zpowers_sup_zpowers P.comm
    (orderOf_eq_prime P.pow_left P.ne_one)
    (orderOf_eq_prime P.pow_right fun hh => P.not_mem (by rw [hh]; exact Subgroup.one_mem _))
    (inf_zpowers_eq_bot_of_invPack P)).1

private theorem comm_of_mem_sup_zpowers_of_invPack {W : Type} [CommGroup W] [Finite W]
    {p m : ℕ} [Fact p.Prime] {τ x₁ x₂ h : MulAut W} (P : InvPack p m τ x₁ x₂ h) :
    ∀ a ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂,
      ∀ b ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, a * b = b * a :=
  (CFSG.GroupTheory.card_zpowers_sup_zpowers P.comm
    (orderOf_eq_prime P.pow_left P.ne_one)
    (orderOf_eq_prime P.pow_right fun hh => P.not_mem (by rw [hh]; exact Subgroup.one_mem _))
    (inf_zpowers_eq_bot_of_invPack P)).2

private theorem exists_pow_pow_of_mem_sup_zpowers {W : Type} [CommGroup W] {p : ℕ}
    (hp : p.Prime) {x₁ x₂ : MulAut W} (h1 : x₁ ^ p = 1) (h2 : x₂ ^ p = 1)
    (hc : Commute x₁ x₂) {z : MulAut W}
    (hz : z ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :
    ∃ a < p, ∃ b < p, z = x₁ ^ a * x₂ ^ b := by
  obtain ⟨i, j, rfl⟩ := (mem_sup_zpowers_iff_exists_zpow hc).1 hz
  have hp0 : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h0i : 0 ≤ i % (p : ℤ) := Int.emod_nonneg i hpne
  have h0j : 0 ≤ j % (p : ℤ) := Int.emod_nonneg j hpne
  have hlti : (i % (p : ℤ)).toNat < p := by
    have h := Int.emod_lt_of_pos i hp0
    rw [← Int.toNat_of_nonneg h0i] at h
    exact_mod_cast h
  have hltj : (j % (p : ℤ)).toNat < p := by
    have h := Int.emod_lt_of_pos j hp0
    rw [← Int.toNat_of_nonneg h0j] at h
    exact_mod_cast h
  refine ⟨(i % (p : ℤ)).toNat, hlti, (j % (p : ℤ)).toNat, hltj, ?_⟩
  rw [zpow_eq_zpow_emod' i h1, zpow_eq_zpow_emod' j h2, ← zpow_natCast, ← zpow_natCast,
    Int.toNat_of_nonneg h0i, Int.toNat_of_nonneg h0j]

private theorem conj_mem_of_invPack {W : Type} [CommGroup W] {p m : ℕ}
    {τ x₁ x₂ h : MulAut W} (P : InvPack p m τ x₁ x₂ h) {z : MulAut W}
    (hz : z ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :
    h * z * h⁻¹ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := by
  obtain ⟨i, j, rfl⟩ := (mem_sup_zpowers_iff_exists_zpow P.comm).1 hz
  obtain ⟨a, b, hab⟩ := P.conj_left
  obtain ⟨c, d, hcd⟩ := P.conj_right
  have h1 : h * x₁ ^ i * h⁻¹ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := by
    rw [← conj_zpow, hab]
    exact Subgroup.zpow_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)) a)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)) b)) i
  have h2 : h * x₂ ^ j * h⁻¹ ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := by
    rw [← conj_zpow, hcd]
    exact Subgroup.zpow_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)) c)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)) d)) j
  have hcalc : h * (x₁ ^ i * x₂ ^ j) * h⁻¹
      = (h * x₁ ^ i * h⁻¹) * (h * x₂ ^ j * h⁻¹) := by group
  rw [hcalc]
  exact Subgroup.mul_mem _ h1 h2

private theorem conj_inv_mem_of_invPack {W : Type} [CommGroup W] {p m : ℕ}
    {τ x₁ x₂ h : MulAut W} (P : InvPack p m τ x₁ x₂ h) {z : MulAut W}
    (hz : z ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) :
    h⁻¹ * z * h ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := by
  obtain ⟨i, j, rfl⟩ := (mem_sup_zpowers_iff_exists_zpow P.comm).1 hz
  obtain ⟨a, b, hab⟩ := P.conj_inv_left
  obtain ⟨c, d, hcd⟩ := P.conj_inv_right
  have e1 : h⁻¹ * x₁ ^ i * h = (h⁻¹ * x₁ * h) ^ i := by
    have hc := conj_zpow (a := h⁻¹) (b := x₁) (i := i)
    rw [inv_inv] at hc
    exact hc.symm
  have e2 : h⁻¹ * x₂ ^ j * h = (h⁻¹ * x₂ * h) ^ j := by
    have hc := conj_zpow (a := h⁻¹) (b := x₂) (i := j)
    rw [inv_inv] at hc
    exact hc.symm
  have h1 : h⁻¹ * x₁ ^ i * h ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := by
    rw [e1, hab]
    exact Subgroup.zpow_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)) a)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)) b)) i
  have h2 : h⁻¹ * x₂ ^ j * h ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂ := by
    rw [e2, hcd]
    exact Subgroup.zpow_mem _ (Subgroup.mul_mem _
      (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)) c)
      (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)) d)) j
  have hcalc : h⁻¹ * (x₁ ^ i * x₂ ^ j) * h
      = (h⁻¹ * x₁ ^ i * h) * (h⁻¹ * x₂ ^ j * h) := by group
  rw [hcalc]
  exact Subgroup.mul_mem _ h1 h2

private theorem card_of_relIndex_eq_prime {W : Type} [CommGroup W] [Finite W]
    {p m : ℕ} [Fact p.Prime] {τ x₁ x₂ h : MulAut W} (P : InvPack p m τ x₁ x₂ h)
    {D : Subgroup (MulAut W)} (hDX : D ≤ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂)
    (hD : D.relIndex (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) = p) :
    Nat.card ↥D = p := by
  have hp : Nat.Prime p := Fact.out
  have h := Subgroup.relIndex_mul_card (H := D)
    (K := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂)
  rw [inf_eq_left.2 hDX, hD] at h
  rw [card_sup_zpowers_of_invPack P, pow_two] at h
  exact Nat.mul_left_cancel hp.pos h

private theorem exists_generator_of_relIndex_eq_prime {W : Type} [CommGroup W] [Finite W]
    {p m : ℕ} [Fact p.Prime] {τ x₁ x₂ h : MulAut W} (P : InvPack p m τ x₁ x₂ h)
    {D : Subgroup (MulAut W)} (hDX : D ≤ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂)
    (hD : D.relIndex (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) = p) :
    ∃ a < p, ∃ b < p, D = Subgroup.zpowers (x₁ ^ a * x₂ ^ b) ∧ x₁ ^ a * x₂ ^ b ≠ 1 := by
  have hp : Nat.Prime p := Fact.out
  have hp1 : 1 < p := hp.one_lt
  have hDcard : Nat.card ↥D = p := card_of_relIndex_eq_prime P hDX hD
  have hXp : ∀ z ∈ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂, z ^ p = 1 := fun z hz =>
    CFSG.GroupTheory.pow_eq_one_of_mem_zpowers_sup P.comm
      (orderOf_dvd_of_pow_eq_one P.pow_left) (orderOf_dvd_of_pow_eq_one P.pow_right) hz
  have hDne : D ≠ ⊥ := by
    intro hbot
    have h1 : Nat.card ↥D = 1 := by rw [hbot]; exact Subgroup.card_bot
    omega
  obtain ⟨d, hdne⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hDne
  set d₀ : MulAut W := (d : MulAut W) with hd₀
  have hdD : d₀ ∈ D := by rw [hd₀]; exact d.2
  have hd1 : d₀ ≠ 1 := by rw [hd₀]; exact fun hh => hdne (Subtype.ext hh)
  have hdo : orderOf d₀ = p := orderOf_eq_prime (hXp _ (hDX hdD)) hd1
  have hDeq : D = Subgroup.zpowers d₀ := by
    have hle : Subgroup.zpowers d₀ ≤ D := Subgroup.zpowers_le.2 hdD
    have hcard : Nat.card ↥(Subgroup.zpowers d₀) = p := by rw [Nat.card_zpowers, hdo]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hDcard])).symm
  obtain ⟨a, ha, b, hb, hdab⟩ :=
    exists_pow_pow_of_mem_sup_zpowers hp P.pow_left P.pow_right P.comm (hDX hdD)
  exact ⟨a, ha, b, hb, by rw [hdab] at hDeq; exact hDeq, by rw [← hdab]; exact hd1⟩

private theorem pow_not_mem_normalizer_of_invPack {W : Type} [CommGroup W] {p m : ℕ}
    [Fact p.Prime] {τ x₁ x₂ h : MulAut W} (P : InvPack p m τ x₁ x₂ h) {a b : ℕ}
    (ha : a < p) (hb : b < p) (hne : x₁ ^ a * x₂ ^ b ≠ 1) :
    ∀ k : ℕ, 0 < k → k < m →
      h ^ k ∉ Subgroup.normalizer
        (Subgroup.zpowers (x₁ ^ a * x₂ ^ b) : Set (MulAut W)) := by
  have hp : Nat.Prime p := Fact.out
  set z : MulAut W := x₁ ^ a * x₂ ^ b with hz
  intro k hk0 hkm hkN
  have hdp : z ^ p = 1 := by
    rw [hz]
    exact CFSG.GroupTheory.pow_eq_one_of_mem_zpowers_sup P.comm
      (orderOf_dvd_of_pow_eq_one P.pow_left) (orderOf_dvd_of_pow_eq_one P.pow_right)
      (Subgroup.mul_mem _
        (Subgroup.pow_mem _ (Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)) a)
        (Subgroup.pow_mem _ (Subgroup.mem_sup_right (Subgroup.mem_zpowers x₂)) b))
  have hmem : h ^ k * z * (h ^ k)⁻¹ ∈ Subgroup.zpowers z :=
    (Subgroup.mem_normalizer_iff.1 (hz ▸ hkN) z).1 (Subgroup.mem_zpowers z)
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 hmem
  have hp0 : (0 : ℤ) < (p : ℤ) := by exact_mod_cast hp.pos
  have hpne : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
  have h0j : 0 ≤ j % (p : ℤ) := Int.emod_nonneg j hpne
  have hltj : (j % (p : ℤ)).toNat < p := by
    have hlt := Int.emod_lt_of_pos j hp0
    rw [← Int.toNat_of_nonneg h0j] at hlt
    exact_mod_cast hlt
  have hjeq : z ^ j = z ^ ((j % (p : ℤ)).toNat) := by
    rw [zpow_eq_zpow_emod' j hdp]
    conv_rhs => rw [← zpow_natCast]
    exact congrArg (fun e : ℤ => z ^ e) (Int.toNat_of_nonneg h0j).symm
  exact P.lines a ha b hb hne k hk0 hkm _ hltj (by
    calc h ^ k * (x₁ ^ a * x₂ ^ b) * (h ^ k)⁻¹ = h ^ k * z * (h ^ k)⁻¹ := by rw [hz]
      _ = z ^ j := hj.symm
      _ = z ^ ((j % (p : ℤ)).toNat) := hjeq
      _ = (x₁ ^ a * x₂ ^ b) ^ ((j % (p : ℤ)).toNat) := by rw [hz])

private theorem card_le_relIndex_of_forall_not_mem {G : Type*} [Group G] [Finite G] {m : ℕ} {h : G}
    {N : Subgroup G} (hN : ∀ k : ℕ, 0 < k → k < m → h ^ k ∉ N) :
    m ≤ (Subgroup.zpowers h ⊓ N).relIndex (Subgroup.zpowers h) := by
  let T : Subgroup G := Subgroup.zpowers h
  let H : Subgroup ↥T := (T ⊓ N).subgroupOf T
  have hTcomm : IsMulCommutative ↥T := Subgroup.zpowers_isMulCommutative h
  have hHnormal : H.Normal := Subgroup.normal_of_comm H
  let φ : Fin m → ↥T ⧸ H := fun k =>
    QuotientGroup.mk
      ⟨h ^ (k : ℕ), Subgroup.pow_mem (Subgroup.zpowers h) (Subgroup.mem_zpowers h) k⟩
  have hφ : Function.Injective φ := by
    have key : ∀ i j : Fin m, (i : ℕ) ≤ (j : ℕ) → φ i = φ j → i = j := by
      intro i j hle hij
      by_contra hne
      have hlt : (i : ℕ) < (j : ℕ) := lt_of_le_of_ne hle fun hh => hne (Fin.ext hh)
      have hk0 : 0 < (j : ℕ) - (i : ℕ) := Nat.sub_pos_of_lt hlt
      have hkm : (j : ℕ) - (i : ℕ) < m := by
        have hj : (j : ℕ) < m := j.isLt
        omega
      have hpow : ∀ n : ℕ, h ^ n ∈ Subgroup.zpowers h := fun n =>
        Subgroup.pow_mem (Subgroup.zpowers h) (Subgroup.mem_zpowers h) n
      have hmemH : (⟨h ^ (i : ℕ), hpow i⟩ : ↥T)⁻¹ *
          ⟨h ^ (j : ℕ), hpow j⟩ ∈ H := QuotientGroup.eq.1 hij
      have hval : (((⟨h ^ (i : ℕ), hpow i⟩ : ↥T)⁻¹ *
          ⟨h ^ (j : ℕ), hpow j⟩ : ↥T) : G) =
          (h ^ (i : ℕ))⁻¹ * h ^ (j : ℕ) := by simp
      have hsplit : (h ^ (i : ℕ))⁻¹ * h ^ (j : ℕ) = h ^ ((j : ℕ) - (i : ℕ)) := by
        have h1 : h ^ (j : ℕ) = h ^ (i : ℕ) * h ^ ((j : ℕ) - (i : ℕ)) := by
          rw [← pow_add, Nat.add_sub_of_le hle]
        rw [h1, ← mul_assoc, inv_mul_cancel, one_mul]
      exact hN _ hk0 hkm (by
        have h2 := (Subgroup.mem_subgroupOf.1 hmemH).2
        rwa [hval, hsplit] at h2)
    intro i j hij
    rcases le_total (i : ℕ) (j : ℕ) with hle | hle
    · exact key i j hle hij
    · exact (key j i hle hij.symm).symm
  have hcard := Nat.card_le_card_of_injective φ hφ
  rw [Nat.card_fin] at hcard
  have hidx : Nat.card (↥T ⧸ H) = (T ⊓ N).relIndex T := rfl
  rwa [hidx] at hcard

private theorem le_relIndex_normalizer_of_invPack {W : Type} [CommGroup W] [Finite W]
    {p m : ℕ} [Fact p.Prime] {τ x₁ x₂ h : MulAut W} (P : InvPack p m τ x₁ x₂ h)
    {D : Subgroup (MulAut W)} (hDX : D ≤ Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂)
    (hD : D.relIndex (Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂) = p) :
    m ≤ (Subgroup.zpowers h ⊓ Subgroup.normalizer (D : Set (MulAut W))).relIndex
      (Subgroup.zpowers h) := by
  obtain ⟨a, ha, b, hb, hDeq, hne⟩ := exists_generator_of_relIndex_eq_prime P hDX hD
  rw [hDeq]
  exact card_le_relIndex_of_forall_not_mem (pow_not_mem_normalizer_of_invPack P ha hb hne)

theorem two_pow_le_index_sq_of_invPack {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w * w = 1) {p m : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {τ x₁ x₂ h : MulAut W}
    (hτ : τ * τ = 1) (P : InvPack p m τ x₁ x₂ h) :
    2 ^ (m * orderOf (2 : ZMod p)) ≤ (fixV (zpowers τ)).index ^ 2 := by
  let X : Subgroup (MulAut W) := Subgroup.zpowers x₁ ⊔ Subgroup.zpowers x₂
  have hcomm : Commute x₁ x₂ := P.comm
  have hXc : ∀ a ∈ X, ∀ b ∈ X, a * b = b * a := comm_of_mem_sup_zpowers_of_invPack P
  have hXp : ∀ a ∈ X, a ^ p = 1 := fun a ha =>
    CFSG.GroupTheory.pow_eq_one_of_mem_zpowers_sup P.comm
      (orderOf_dvd_of_pow_eq_one P.pow_left) (orderOf_dvd_of_pow_eq_one P.pow_right) ha
  have hX : X ≠ ⊥ := by
    intro hbot
    have hx1 : x₁ ∈ (⊥ : Subgroup (MulAut W)) := by
      rw [← hbot]
      exact Subgroup.mem_sup_left (Subgroup.mem_zpowers x₁)
    exact P.ne_one (Subgroup.mem_bot.1 hx1)
  have hTX : Subgroup.zpowers h ≤ Subgroup.normalizer (X : Set (MulAut W)) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact conj_mem_of_invPack P
    · intro hz
      have hh := conj_inv_mem_of_invPack P hz
      have hconj : h⁻¹ * (h * z * h⁻¹) * h = z := by group
      rwa [hconj] at hh
  have htX : ∀ z ∈ X, τ * z * τ⁻¹ = z⁻¹ := by
    intro z hz
    obtain ⟨i, j, rfl⟩ := (mem_sup_zpowers_iff_exists_zpow P.comm).1 hz
    have h1 : τ * x₁ ^ i * τ⁻¹ = (x₁ ^ i)⁻¹ := by
      have hc := conj_zpow (a := τ) (b := x₁) (i := i)
      rw [P.inv_left] at hc
      rw [← hc, inv_zpow]
    have h2 : τ * x₂ ^ j * τ⁻¹ = (x₂ ^ j)⁻¹ := by
      have hc := conj_zpow (a := τ) (b := x₂) (i := j)
      rw [P.inv_right] at hc
      rw [← hc, inv_zpow]
    have hcalc : τ * (x₁ ^ i * x₂ ^ j) * τ⁻¹
        = (τ * x₁ ^ i * τ⁻¹) * (τ * x₂ ^ j * τ⁻¹) := by group
    rw [hcalc, h1, h2, mul_inv_rev]
    exact ((hcomm.zpow_zpow i j).inv_inv).eq
  exact two_pow_le_index_sq_of_inverts_abelian hW hp2 hXc hXp hX hTX hτ htX
    fun D hDX hD => le_relIndex_normalizer_of_invPack P hDX hD

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.W4Row

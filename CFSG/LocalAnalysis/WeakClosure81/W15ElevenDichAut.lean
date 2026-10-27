module

public import CFSG.LocalAnalysis.WeakClosure81.W15ElevenBarAut
public import Mathlib.RingTheory.ZMod.UnitsCyclic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open scoped commutatorElement

variable {N : Type*} [Group N]

section Extraspecial

variable {p : ℕ} [Fact p.Prime] [hN : CFSG.IsExtraspecial p N]

include hN

private theorem b15_W15ElevenDichAut_map_center_mem (σ : MulAut N)
    (hσσ : ∀ x, σ (σ x) = x) {z : N} (hz : z ∈ Subgroup.center N) :
    σ z ∈ Subgroup.center N := by
  rw [Subgroup.mem_center_iff] at hz
  rw [Subgroup.mem_center_iff]
  intro g
  calc g * σ z = σ (σ g) * σ z := by rw [hσσ g]
    _ = σ (σ g * z) := by rw [map_mul]
    _ = σ (z * σ g) := by rw [(hz (σ g)).symm]
    _ = σ z * σ (σ g) := by rw [map_mul]
    _ = σ z * g := by rw [hσσ g]

theorem mulAut_fix_or_inv_center (σ : MulAut N) (hσσ : ∀ x, σ (σ x) = x) :
    (∀ z ∈ Subgroup.center N, σ z = z) ∨ (∀ z ∈ Subgroup.center N, σ z = z⁻¹) := by
  have hZcard : Nat.card (Subgroup.center N) = p := CFSG.IsExtraspecial.center_order_p p N
  haveI hZfin : Finite ↥(Subgroup.center N) :=
    Nat.finite_of_card_ne_zero (by rw [hZcard]; exact (Fact.out : p.Prime).ne_zero)
  have hZnt : Nontrivial ↥(Subgroup.center N) := by
    rw [← Finite.one_lt_card_iff_nontrivial]
    rw [hZcard]
    exact (Fact.out : p.Prime).one_lt
  obtain ⟨z, hz_ne⟩ := exists_ne (1 : ↥(Subgroup.center N))
  set z₀ : N := (z : N) with hz₀def
  have hz₀mem : z₀ ∈ Subgroup.center N := by rw [hz₀def]; exact z.2
  have hz₀ne : z₀ ≠ 1 := by
    rw [hz₀def]
    intro h
    exact hz_ne (Subtype.ext h)
  have hzord : orderOf z₀ = p := by
    have hdvd : orderOf z₀ ∣ p := by
      have h := Subgroup.orderOf_dvd_natCard (Subgroup.center N) hz₀mem
      rwa [hZcard] at h
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).1 hdvd with h1 | hp
    · exact absurd (orderOf_eq_one_iff.1 h1) hz₀ne
    · exact hp
  have hzp : Subgroup.zpowers z₀ = Subgroup.center N := by
    apply Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.2 hz₀mem)
    rw [Nat.card_zpowers, hzord, hZcard]
  have hσz₀mem : σ z₀ ∈ Subgroup.center N :=
    b15_W15ElevenDichAut_map_center_mem (p := p) σ hσσ hz₀mem
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (by rw [hzp]; exact hσz₀mem)
  have hsq : m * m ≡ 1 [ZMOD p] := by
    have h1 : z₀ ^ (m * m) = z₀ ^ (1 : ℤ) := by
      calc z₀ ^ (m * m) = (z₀ ^ m) ^ m := by rw [zpow_mul]
        _ = (σ z₀) ^ m := by rw [hm]
        _ = σ (z₀ ^ m) := by rw [map_zpow]
        _ = σ (σ z₀) := by rw [hm]
        _ = z₀ := hσσ z₀
        _ = z₀ ^ (1 : ℤ) := by rw [zpow_one]
    rw [zpow_eq_zpow_iff_modEq, hzord] at h1
    exact h1
  have hzmod : (m : ZMod p) * (m : ZMod p) = 1 := by
    have hcast : ((m * m : ℤ) : ZMod p) = ((1 : ℤ) : ZMod p) :=
      (ZMod.intCast_eq_intCast_iff (m * m) 1 p).2 hsq
    simpa using hcast
  rcases mul_self_eq_one_iff.1 hzmod with hm1 | hmneg
  · left
    have hm1' : m ≡ 1 [ZMOD p] :=
      (ZMod.intCast_eq_intCast_iff m 1 p).1 (by simpa using hm1)
    have hσz₀ : σ z₀ = z₀ := by
      rw [← hm]
      exact (zpow_eq_zpow_iff_modEq.2 (by rw [hzord]; exact hm1')).trans (zpow_one z₀)
    intro z hz
    rw [← hzp] at hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← hk, map_zpow, hσz₀]
  · right
    have hmneg' : m ≡ -1 [ZMOD p] :=
      (ZMod.intCast_eq_intCast_iff m (-1) p).1 (by simpa using hmneg)
    have hσz₀ : σ z₀ = z₀⁻¹ := by
      rw [← hm]
      exact (zpow_eq_zpow_iff_modEq.2 (by rw [hzord]; exact hmneg')).trans (zpow_neg_one z₀)
    intro z hz
    rw [← hzp] at hz
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hz
    rw [← hk, map_zpow, hσz₀, inv_zpow]

theorem mulAut_eq_one_of_two_power_order (hp2 : p ≠ 2) (σ : MulAut N) {e : ℕ}
    (he : σ ^ (2 ^ e) = 1) (hσZ : ∀ z ∈ Subgroup.center N, σ z = z)
    (h : ∀ x, σ x * x⁻¹ ∈ Subgroup.center N) : σ = 1 := by
  have hZcard : Nat.card (Subgroup.center N) = p := CFSG.IsExtraspecial.center_order_p p N
  refine MulEquiv.ext fun x => ?_
  obtain ⟨z, hzdef⟩ : ∃ z : N, z = σ x * x⁻¹ := ⟨_, rfl⟩
  have hz : z ∈ Subgroup.center N := by rw [hzdef]; exact h x
  have hzx : σ x = z * x := by rw [hzdef]; group
  have hfixz : σ z = z := hσZ z hz
  have hpow : ∀ j : ℕ, (σ ^ j) x = z ^ j * x := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      rw [pow_succ', MulAut.mul_apply, ih, map_mul, map_pow, hfixz, hzx, pow_succ]
      group
  have h1 : z ^ (2 ^ e) = 1 := by
    have hx' : x = z ^ (2 ^ e) * x := by
      have h2 := hpow (2 ^ e)
      rwa [he, MulAut.one_apply] at h2
    exact mul_right_cancel (by rw [← hx', one_mul])
  have hzp : z ^ p = 1 := by
    have hmem : (⟨z, hz⟩ : ↥(Subgroup.center N)) ^ Nat.card ↥(Subgroup.center N) = 1 :=
      pow_card_eq_one'
    rw [hZcard] at hmem
    simpa using congrArg Subtype.val hmem
  have hcop : Nat.Coprime (2 ^ e) p :=
    ((Nat.coprime_primes Nat.prime_two (Fact.out : p.Prime)).2 (Ne.symm hp2)).pow_left e
  have hd : orderOf z ∣ 1 := by
    have hgcd := Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one h1) (orderOf_dvd_of_pow_eq_one hzp)
    rwa [Nat.Coprime.gcd_eq_one hcop] at hgcd
  have hz1 : z = 1 := orderOf_eq_one_iff.1 (Nat.dvd_one.1 hd)
  rw [hzx, hz1, one_mul, MulAut.one_apply]

theorem mulAut_mul_eq_one_of_neg_neg (hp2 : p ≠ 2) (σ τ : MulAut N) {e : ℕ}
    (he : (σ * τ) ^ (2 ^ e) = 1) (hσZ : ∀ z ∈ Subgroup.center N, σ z = z)
    (hτZ : ∀ z ∈ Subgroup.center N, τ z = z) (hσ : ∀ x, σ x * x ∈ Subgroup.center N)
    (hτ : ∀ x, τ x * x ∈ Subgroup.center N) : σ * τ = 1 := by
  refine mulAut_eq_one_of_two_power_order hp2 (σ * τ) he ?_ ?_
  · intro z hz
    show σ (τ z) = z
    rw [hτZ z hz, hσZ z hz]
  · intro y
    show σ (τ y) * y⁻¹ ∈ Subgroup.center N
    have h1 := hτ y
    have h2 := hσ y
    obtain ⟨z1, hz1⟩ : ∃ z1 : N, z1 = τ y * y := ⟨_, rfl⟩
    obtain ⟨w, hw⟩ : ∃ w : N, w = σ y * y := ⟨_, rfl⟩
    rw [← hz1] at h1
    rw [← hw] at h2
    have e1 : τ y = z1 * y⁻¹ := by rw [hz1]; group
    have e2 : σ y = w * y⁻¹ := by rw [hw]; group
    have hc : y * w⁻¹ = w⁻¹ * y :=
      Subgroup.mem_center_iff.1 ((Subgroup.center N).inv_mem h2) y
    have h : σ (τ y) * y⁻¹ = z1 * w⁻¹ := by
      rw [e1, map_mul, hσZ z1 h1, map_inv, e2]
      calc z1 * (w * y⁻¹)⁻¹ * y⁻¹ = z1 * (y * w⁻¹ * y⁻¹) := by group
        _ = z1 * w⁻¹ := by rw [hc]; group
    rw [h]
    exact (Subgroup.center N).mul_mem h1 ((Subgroup.center N).inv_mem h2)

theorem index_ker_le_four_of_isExtraspecial [Finite N] (hp2 : p ≠ 2)
    (hcard : Nat.card N = p ^ 3) {A : Type*} [Group A] (ρ : A →* MulAut N)
    (hcomm : ∀ a a' : A, a * a' = a' * a) (hsq : ∀ a : A, a * a = 1) : ρ.ker.index ≤ 4 := by
  let F : Subgroup A :=
    { carrier := {a | ∀ z ∈ Subgroup.center N, ρ a z = z}
      one_mem' := by intro z hz; rw [map_one, MulAut.one_apply]
      mul_mem' := by
        intro a b ha hb z hz
        rw [map_mul, MulAut.mul_apply, hb z hz, ha z hz]
      inv_mem' := by
        intro a ha z hz
        have h : ρ a (ρ a⁻¹ z) = ρ a z := by
          rw [← MulAut.mul_apply, ← map_mul, mul_inv_cancel, map_one, MulAut.one_apply,
            ha z hz]
        exact (ρ a).injective h }
  have hfix_or_inv : ∀ a : A, a ∈ F ∨ ∀ z ∈ Subgroup.center N, ρ a z = z⁻¹ := by
    intro a
    have hsqA : ∀ x, ρ a (ρ a x) = x := by
      intro x
      rw [← MulAut.mul_apply, ← map_mul, hsq a, map_one, MulAut.one_apply]
    rcases mulAut_fix_or_inv_center (p := p) (ρ a) hsqA with h | h
    · left
      change ∀ z ∈ Subgroup.center N, ρ a z = z
      exact h
    · right
      exact h
  have hFdvd : F.index ∣ 2 := by
    rw [Subgroup.index_dvd_two_iff]
    by_cases hex : ∃ a : A, a ∉ F
    · obtain ⟨a₀, ha₀⟩ := hex
      refine ⟨a₀, fun b => ?_⟩
      by_cases hb : b ∈ F
      · exact Or.inr hb
      · left
        have hb' : ∀ z ∈ Subgroup.center N, ρ b z = z⁻¹ := (hfix_or_inv b).resolve_left hb
        have ha' : ∀ z ∈ Subgroup.center N, ρ a₀ z = z⁻¹ :=
          (hfix_or_inv a₀).resolve_left ha₀
        change ∀ z ∈ Subgroup.center N, ρ (b * a₀) z = z
        intro z hz
        rw [map_mul, MulAut.mul_apply, ha' z hz, map_inv, hb' z hz]
        simp
    · have hall : ∀ a : A, a ∈ F := fun a => by
        by_contra ha
        exact hex ⟨a, ha⟩
      exact ⟨1, fun b => Or.inr (hall b)⟩
  have hFindex : F.index ≤ 2 := Nat.le_of_dvd (by norm_num) hFdvd
  have hFF : (ρ.comp F.subtype).ker.index ≤ 2 :=
    index_ker_le_two_of_isExtraspecial hp2 hcard (ρ.comp F.subtype)
      (fun a a' => Subtype.ext (hcomm a a'))
      (fun a => Subtype.ext (hsq a))
      (fun a z hz => a.2 z hz)
  have hker_le_F : ρ.ker ≤ F := by
    intro a ha
    change ∀ z ∈ Subgroup.center N, ρ a z = z
    intro z hz
    rw [MonoidHom.mem_ker.1 ha, MulAut.one_apply]
  have hker_eq : (ρ.comp F.subtype).ker = ρ.ker.subgroupOf F := rfl
  calc ρ.ker.index = ρ.ker.relIndex F * F.index := (Subgroup.relIndex_mul_index hker_le_F).symm
    _ = (ρ.ker.subgroupOf F).index * F.index := rfl
    _ = (ρ.comp F.subtype).ker.index * F.index := by rw [hker_eq]
    _ ≤ 2 * 2 := Nat.mul_le_mul hFF hFindex
    _ = 4 := by norm_num

end Extraspecial

section Prime

variable {p : ℕ} [Fact p.Prime]

private theorem b15_W15ElevenDichAut_finite_mulAut [Finite N] : Finite (MulAut N) :=
  Finite.of_injective (fun f : MulAut N => (f : N → N)) DFunLike.coe_injective

private theorem b15_W15ElevenDichAut_isCyclic_mulAut [Finite N] (hcard : Nat.card N = p) :
    IsCyclic (MulAut N) := by
  haveI : IsCyclic N := isCyclic_of_prime_card hcard
  have h2 : IsCyclic (ZMod (Nat.card N))ˣ := by
    rw [hcard]
    exact ZMod.isCyclic_units_prime (Fact.out : p.Prime)
  exact (MulEquiv.isCyclic (IsCyclic.mulAutMulEquiv N)).mpr h2

theorem index_ker_le_two_of_card_prime [Finite N] (hcard : Nat.card N = p)
    {A : Type*} [Group A] (ρ : A →* MulAut N) (hsq : ∀ a : A, a * a = 1) : ρ.ker.index ≤ 2 := by
  classical
  haveI : IsCyclic (MulAut N) := b15_W15ElevenDichAut_isCyclic_mulAut hcard
  haveI : Finite (MulAut N) := b15_W15ElevenDichAut_finite_mulAut
  haveI : Fintype (MulAut N) := Fintype.ofFinite _
  have hcard_range : Nat.card ρ.range ≤ 2 := by
    let f : ρ.range → {x : MulAut N // x ^ 2 = 1} := fun g =>
      ⟨(g : MulAut N), by
        obtain ⟨a, ha⟩ := MonoidHom.mem_range.1 g.2
        show (g : MulAut N) ^ 2 = 1
        rw [← ha, pow_two, ← map_mul, hsq a, map_one]⟩
    have hinj : Function.Injective f := by
      intro g h hgh
      have hval : (g : MulAut N) = (h : MulAut N) := by
        simpa only [f, Subtype.mk.injEq] using hgh
      exact Subtype.ext hval
    calc Nat.card ρ.range = Fintype.card ρ.range := Nat.card_eq_fintype_card
      _ ≤ Fintype.card {x : MulAut N // x ^ 2 = 1} := Fintype.card_le_of_injective f hinj
      _ = (Finset.univ.filter (fun x : MulAut N => x ^ 2 = 1)).card := Fintype.card_subtype _
      _ ≤ 2 := IsCyclic.card_pow_eq_one_le (n := 2) (by norm_num)
  calc ρ.ker.index = Nat.card ρ.range := Subgroup.index_ker ρ
    _ ≤ 2 := hcard_range

theorem mulAut_eq_of_card_prime [Finite N] (hcard : Nat.card N = p) (σ τ : MulAut N)
    (hσσ : σ * σ = 1) (hττ : τ * τ = 1) (hσ : σ ≠ 1) (hτ : τ ≠ 1) : σ = τ := by
  classical
  haveI : IsCyclic (MulAut N) := b15_W15ElevenDichAut_isCyclic_mulAut hcard
  haveI : Finite (MulAut N) := b15_W15ElevenDichAut_finite_mulAut
  haveI : Fintype (MulAut N) := Fintype.ofFinite _
  by_contra hne
  have hsub : ({1, σ, τ} : Finset (MulAut N)) ⊆
      Finset.univ.filter (fun g : MulAut N => g ^ 2 = 1) := by
    intro g hg
    simp only [Finset.mem_insert, Finset.mem_singleton] at hg
    rw [Finset.mem_filter]
    refine ⟨Finset.mem_univ _, ?_⟩
    rcases hg with rfl | rfl | rfl
    · simp
    · simpa [pow_two] using hσσ
    · simpa [pow_two] using hττ
  have hcard3 : ({1, σ, τ} : Finset (MulAut N)).card = 3 := by
    have h1 : (1 : MulAut N) ∉ ({σ, τ} : Finset (MulAut N)) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      exact ⟨fun h => hσ h.symm, fun h => hτ h.symm⟩
    have h2 : (σ : MulAut N) ∉ ({τ} : Finset (MulAut N)) := by
      simpa using hne
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_singleton]
  have hle := Finset.card_le_card hsub
  rw [hcard3] at hle
  have h2 : (Finset.univ.filter (fun g : MulAut N => g ^ 2 = 1)).card ≤ 2 :=
    IsCyclic.card_pow_eq_one_le (n := 2) (by norm_num)
  exact absurd (le_trans hle h2) (by norm_num)

end Prime

theorem mulAut_sq_eq_one_of_card_three [Finite N] (hcard : Nat.card N = 3) (σ : MulAut N) :
    σ * σ = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  haveI : IsCyclic N := isCyclic_of_prime_card (p := 3) hcard
  have hcardAut : Nat.card (MulAut N) = 2 := by
    rw [IsCyclic.card_mulAut N, hcard, Nat.totient_prime Nat.prime_three]
  have h := pow_card_eq_one' (x := σ)
  rwa [hcardAut, pow_two] at h

theorem mulAut_eq_of_card_three [Finite N] (hcard : Nat.card N = 3) (σ τ : MulAut N)
    (hσ : σ ≠ 1) (hτ : τ ≠ 1) : σ = τ := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  exact mulAut_eq_of_card_prime (p := 3) hcard σ τ
    (mulAut_sq_eq_one_of_card_three hcard σ)
    (mulAut_sq_eq_one_of_card_three hcard τ) hσ hτ

theorem card_le_mul_card_inf_of_index_ker_le {G : Type} [Group G] [Finite G] {A Q : Subgroup G}
    {L : Type*} [Group L] (ρ : ↥A →* L) (hker : ∀ a : ↥A, ρ a = 1 → (a : G) ∈ Q) {n : ℕ}
    (hn : ρ.ker.index ≤ n) : Nat.card ↥A ≤ n * Nat.card ↥(A ⊓ Q) := by
  have hle : ρ.ker ≤ (A ⊓ Q).subgroupOf A := by
    intro a ha
    rw [MonoidHom.mem_ker] at ha
    exact Subgroup.mem_subgroupOf.2 ⟨a.2, hker a ha⟩
  have hcard : Nat.card ↥(ρ.ker) ≤ Nat.card ↥(A ⊓ Q) := by
    calc Nat.card ↥(ρ.ker) ≤ Nat.card ↥((A ⊓ Q).subgroupOf A) := Subgroup.card_le_of_le hle
      _ = Nat.card ↥(A ⊓ Q) :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  calc Nat.card ↥A = ρ.ker.index * Nat.card ↥(ρ.ker) := (Subgroup.index_mul_card ρ.ker).symm
    _ ≤ n * Nat.card ↥(A ⊓ Q) := Nat.mul_le_mul hn hcard

end CFSG.LocalAnalysis.WeakClosure81

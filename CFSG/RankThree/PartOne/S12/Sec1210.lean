module

public import CFSG.RankThree.PartOne.S12.Skeleton
public import CFSG.RankThree.PartOne.S12.BaseNodes
import CFSG.RankThree.PartOne.S12.Sec126a
import CFSG.RankThree.PartOne.S12.Sec127
import CFSG.RankThree.PartOne.S12.Sec12Three
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon
import CFSG.RankThree.PartOne.S9.Planes.Basic

public section

namespace CFSG.RankThree.PartOne

open CFSG.RankThree.PartOne.Torsion37 CFSG.RankThree.PartOne.Planes
open scoped commutatorElement

variable {G : Type} [Group G]

@[expose] def pCoreFixed (p : ℕ) (E : Subgroup G) : Subgroup G :=
  ⨅ φ ∈ CFSG.pCore p ↥(torusWeyl E), autFixedInG E (φ : MulAut E)

@[expose] def Node1210 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ Outcome152Five p E A (lieGenerated p E) → torusWeylHasPCore p E →
      pCoreFixed p E = E ⊓ L ∧ Nat.card E = p * Nat.card ↥(E ⊓ L) ∧
        ¬ p ∣ Nat.card (Subgroup.center L)

@[expose] def Node1211 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Sec12Hyp G p A c L E → ¬ Outcome152Five p E A (lieGenerated p E) → torusWeylHasPCore p E →
      Nonempty (↥(CFSG.pCore p ↥(torusWeyl E)) ≃* ↥(E ⊓ L)) ∧
      (∀ e e' : E, (e : G) ∉ L → (e' : G) ∉ L →
        ∃! φ : ↥(CFSG.pCore p ↥(torusWeyl E)),
          ∃ k : ℤ, ((φ : ↥(torusWeyl E)) : MulAut E) e = e' ^ k) ∧
      (CFSG.pCore p ↥(torusWeyl E)).map (torusWeyl E).subtype ⊔ torusImage E (cNormalizer c) =
        torusWeyl E ∧
      (CFSG.pCore p ↥(torusWeyl E)).map (torusWeyl E).subtype ⊓ torusImage E (cNormalizer c) = ⊥

theorem mem_autFixedInG_iff {E : Subgroup G} {φ : MulAut E} {g : G} :
    g ∈ autFixedInG E φ ↔ ∃ hg : g ∈ E, φ ⟨g, hg⟩ = ⟨g, hg⟩ := by
  constructor
  · rintro ⟨e, he, rfl⟩
    exact ⟨e.2, he⟩
  · rintro ⟨hg, h⟩
    exact ⟨⟨g, hg⟩, h, rfl⟩

theorem mem_pCoreFixed {p : ℕ} {E : Subgroup G} {g : G} :
    g ∈ pCoreFixed p E ↔ ∃ hg : g ∈ E, ∀ φ ∈ CFSG.pCore p ↥(torusWeyl E),
      ((φ : MulAut E) ⟨g, hg⟩ : E) = ⟨g, hg⟩ := by
  unfold pCoreFixed
  simp only [Subgroup.mem_iInf, mem_autFixedInG_iff]
  constructor
  · intro h
    obtain ⟨hg, -⟩ := h 1 (Subgroup.one_mem _)
    exact ⟨hg, fun φ hφ => (h φ hφ).choose_spec⟩
  · rintro ⟨hg, h⟩ φ hφ
    exact ⟨hg, h φ hφ⟩

theorem pCoreFixed_le (p : ℕ) (E : Subgroup G) : pCoreFixed p E ≤ E := fun _ hg =>
  (mem_pCoreFixed.1 hg).1

theorem mem_pCoreFixed_of_fixed {p : ℕ} {E : Subgroup G} (e : E)
    (h : ∀ φ ∈ CFSG.pCore p ↥(torusWeyl E), (φ : MulAut E) e = e) : (e : G) ∈ pCoreFixed p E :=
  mem_pCoreFixed.2 ⟨e.2, fun φ hφ => h φ hφ⟩

theorem torusInvariant_pCoreFixed (p : ℕ) (E : Subgroup G) :
    torusInvariant E ⊤ (pCoreFixed p E) := by
  rw [LinAlg.torusInvariant_top_iff_forall_torusWeyl (pCoreFixed_le p E)]
  intro φ hφ b hb
  obtain ⟨w, rfl⟩ : ∃ w : ↥(torusWeyl E), (w : MulAut E) = φ := ⟨⟨φ, hφ⟩, rfl⟩
  obtain ⟨hbE, hfix⟩ := mem_pCoreFixed.1 hb
  refine mem_pCoreFixed_of_fixed ((w : MulAut E) ⟨b, pCoreFixed_le p E hb⟩) fun x hx => ?_
  have hx' : w⁻¹ * x * w ∈ CFSG.pCore p ↥(torusWeyl E) := by
    simpa using (CFSG.pCore_normal (p := p) (G := ↥(torusWeyl E))).conj_mem x hx w⁻¹
  have h1 : (w : MulAut E)⁻¹ ((x : MulAut E) ((w : MulAut E) ⟨b, hbE⟩)) = ⟨b, hbE⟩ :=
    hfix (w⁻¹ * x * w) hx'
  calc (x : MulAut E) ((w : MulAut E) ⟨b, hbE⟩)
      = (w : MulAut E) ((w : MulAut E)⁻¹ ((x : MulAut E) ((w : MulAut E) ⟨b, hbE⟩))) := by simp
    _ = (w : MulAut E) ⟨b, hbE⟩ := by rw [h1]

theorem pCoreFixed_ne_bot [Finite G] {p : ℕ} [Fact p.Prime] {E : Subgroup G}
    (hdvd : p ∣ Nat.card E) : pCoreFixed p E ≠ ⊥ := by
  have hX : IsPGroup p ↥(CFSG.pCore p ↥(torusWeyl E)) := CFSG.pCore_isPGroup
  have h1 : (1 : E) ∈ MulAction.fixedPoints ↥(CFSG.pCore p ↥(torusWeyl E)) E :=
    fun x => map_one (x : MulAut E)
  obtain ⟨b, hb, hb1⟩ := hX.exists_fixed_point_of_prime_dvd_card_of_fixed_point E hdvd h1
  have hbmem : (b : G) ∈ pCoreFixed p E :=
    mem_pCoreFixed_of_fixed b fun φ hφ => MulAction.mem_fixedPoints.1 hb ⟨φ, hφ⟩
  intro hbot
  rw [hbot, Subgroup.mem_bot] at hbmem
  exact hb1 (Subtype.ext hbmem.symm)

theorem pCoreFixed_ne_top {p : ℕ} {E : Subgroup G} (hX : torusWeylHasPCore p E) :
    pCoreFixed p E ≠ E := by
  intro heq
  apply hX
  rw [eq_bot_iff]
  intro φ hφ
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  ext e
  have he : (e : G) ∈ pCoreFixed p E := heq.ge e.2
  exact congrArg Subtype.val ((mem_pCoreFixed.1 he).2 φ hφ)

namespace Sec1211

variable {Q Γ : Type} [Group Q] [Group Γ]

structure Data (p : ℕ) (α : Γ →* MulAut Q) (B : Subgroup Q) (X : Subgroup Γ) : Prop where
  prime : p.Prime
  comm : ∀ a b : Q, a * b = b * a
  pow_eq_one : ∀ a : Q, a ^ p = 1
  card_eq : Nat.card Q = p * Nat.card B
  α_inj : Function.Injective α
  X_normal : ∀ w : Γ, ∀ x ∈ X, w * x * w⁻¹ ∈ X
  X_pgroup : IsPGroup p X
  X_fixes : ∀ x ∈ X, ∀ b ∈ B, α x b = b
  B_inv : ∀ (w : Γ), ∀ b ∈ B, α w b ∈ B
  B_irr : ∀ S ≤ B, (∀ (w : Γ), ∀ s ∈ S, α w s ∈ S) → S = ⊥ ∨ S = B
  X_ne_bot : X ≠ ⊥

namespace Data

variable {p : ℕ} {α : Γ →* MulAut Q} {B : Subgroup Q} {X : Subgroup Γ} [Finite Q]
  (h : Data p α B X)

omit [Finite Q] in
include h in
theorem orderOf_eq {e : Q} (he : e ∉ B) : orderOf e = p := by
  have : Fact p.Prime := ⟨h.prime⟩
  refine orderOf_eq_prime (h.pow_eq_one e) ?_
  rintro rfl
  exact he B.one_mem

include h in
theorem zpow_mem_iff_dvd {e : Q} (he : e ∉ B) (j : ℤ) : e ^ j ∈ B ↔ (p : ℤ) ∣ j := by
  have hord := h.orderOf_eq he
  constructor
  · intro hj
    have hbot := Sec12Three.zpowers_inf_eq_bot h.prime hord he
    have h1 : e ^ j = 1 := by
      have hmem : e ^ j ∈ Subgroup.zpowers e ⊓ B :=
        ⟨Subgroup.zpow_mem _ (Subgroup.mem_zpowers e) j, hj⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    rw [← hord]
    exact orderOf_dvd_iff_zpow_eq_one.2 h1
  · intro hj
    have h1 : e ^ j = 1 := orderOf_dvd_iff_zpow_eq_one.1 (by rw [hord]; exact hj)
    rw [h1]
    exact B.one_mem

omit [Finite Q] in
include h in
theorem zpow_congr (a : Q) {m n : ℤ} (hmn : (p : ℤ) ∣ m - n) : a ^ m = a ^ n := by
  obtain ⟨t, ht⟩ := hmn
  have hm : m = n + p * t := by linarith
  rw [hm, zpow_add, zpow_mul, zpow_natCast, h.pow_eq_one, one_zpow, mul_one]

include h in
theorem sup_zpowers_eq_top {e : Q} (he : e ∉ B) : B ⊔ Subgroup.zpowers e = ⊤ := by
  have hcard := card_sup_zpowers h.prime B (h.pow_eq_one e) he (fun b _ => h.comm b e)
  rw [← Subgroup.card_eq_iff_eq_top, hcard, h.card_eq, mul_comm]

include h in
theorem exists_decomp {e : Q} (he : e ∉ B) (q : Q) : ∃ b ∈ B, ∃ a : ℤ, q = b * e ^ a := by
  have hq : q ∈ B ⊔ Subgroup.zpowers e := by
    rw [h.sup_zpowers_eq_top he]
    trivial
  obtain ⟨b, hb, z, hz, rfl⟩ := exists_mul_of_mem_sup_of_commute (fun k _ l _ => h.comm k l) hq
  obtain ⟨a, rfl⟩ := Subgroup.mem_zpowers_iff.1 hz
  exact ⟨b, hb, a, rfl⟩

include h in
theorem mul_inv_mem {x : Γ} (hx : x ∈ X) (e : Q) : α x e * e⁻¹ ∈ B := by
  have : Fact p.Prime := ⟨h.prime⟩
  by_cases he : e ∈ B
  · rw [h.X_fixes x hx e he, mul_inv_cancel]
    exact B.one_mem
  · obtain ⟨k, hk⟩ := h.X_pgroup ⟨x, hx⟩
    have hxk : x ^ p ^ k = 1 := by simpa using congrArg Subtype.val hk
    obtain ⟨b, hb, a, hbe⟩ := h.exists_decomp he (α x e)
    have hm : ∀ m : ℕ, ∃ b' ∈ B, α (x ^ m) e = b' * e ^ (a ^ m) := by
      intro m
      induction m with
      | zero => exact ⟨1, B.one_mem, by simp⟩
      | succ m ih =>
        obtain ⟨b', hb', hm⟩ := ih
        refine ⟨b' * b ^ (a ^ m), B.mul_mem hb' (B.zpow_mem hb _), ?_⟩
        rw [pow_succ', map_mul, MulAut.mul_apply, hm, map_mul, map_zpow, h.X_fixes x hx b' hb',
          hbe, Commute.mul_zpow (h.comm b (e ^ a)), ← zpow_mul, ← pow_succ', mul_assoc]
    obtain ⟨b', hb', hm'⟩ := hm (p ^ k)
    rw [hxk, map_one, MulAut.one_apply] at hm'
    have h1 : e ^ (a ^ p ^ k - 1) ∈ B := by
      obtain ⟨c, hc⟩ : ∃ c, c = e ^ (a ^ p ^ k) := ⟨_, rfl⟩
      rw [← hc] at hm'
      have h1' : e ^ (a ^ p ^ k - 1) = b'⁻¹ := by
        rw [zpow_sub_one, ← hc, eq_inv_iff_mul_eq_one]
        calc c * e⁻¹ * b' = c * (b' * c)⁻¹ * b' := by rw [← hm']
          _ = 1 := by group
      rw [h1']
      exact B.inv_mem hb'
    have h2 : (p : ℤ) ∣ a ^ p ^ k - 1 := (h.zpow_mem_iff_dvd he _).1 h1
    have h3 : ((a : ZMod p) ^ p ^ k) - 1 = 0 := by
      have := (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).2 h2
      simpa using this
    rw [ZMod.pow_card_pow, sub_eq_zero] at h3
    have h4 : (p : ℤ) ∣ a - 1 := by
      apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
      push_cast
      rw [h3, sub_self]
    have h5 : e ^ a = e := by
      have := h.zpow_congr e h4
      simpa using this
    rw [hbe, h5, mul_inv_cancel_right]
    exact hb

@[expose] def xiHom (e : Q) : ↥X →* ↥B where
  toFun x := ⟨α x e * e⁻¹, h.mul_inv_mem x.2 e⟩
  map_one' := by
    apply Subtype.ext
    simp
  map_mul' x y := by
    apply Subtype.ext
    show α ((x : Γ) * (y : Γ)) e * e⁻¹ = (α x e * e⁻¹) * (α y e * e⁻¹)
    obtain ⟨u, hu⟩ : ∃ u, u = α (y : Γ) e * e⁻¹ := ⟨_, rfl⟩
    have hy : α (y : Γ) e = u * e := by rw [hu, inv_mul_cancel_right]
    have hfix : α (x : Γ) u = u := h.X_fixes x x.2 u (hu ▸ h.mul_inv_mem y.2 e)
    rw [← hu]
    calc α ((x : Γ) * (y : Γ)) e * e⁻¹ = α x (α y e) * e⁻¹ := by rw [map_mul, MulAut.mul_apply]
      _ = α x (u * e) * e⁻¹ := by rw [hy]
      _ = u * (α x e * e⁻¹) := by rw [map_mul, hfix, mul_assoc]
      _ = (α x e * e⁻¹) * u := h.comm _ _

include h in
theorem coe_xiHom (e : Q) (x : ↥X) : ((h.xiHom e x : ↥B) : Q) = α x e * e⁻¹ := rfl

omit [Finite Q] in
include h in
theorem mul_mul_inv_comm (b u v : Q) : b * u * (b * v)⁻¹ = u * v⁻¹ := by
  calc b * u * (b * v)⁻¹ = b * (u * v⁻¹) * b⁻¹ := by group
    _ = u * v⁻¹ := by rw [h.comm b (u * v⁻¹)]; group

include h in
theorem xiHom_injective {e : Q} (he : e ∉ B) : Function.Injective (h.xiHom e) := by
  refine (injective_iff_map_eq_one _).2 fun x hx => ?_
  have hxe : α (x : Γ) e = e := by
    have h1 := congrArg Subtype.val hx
    rw [coe_xiHom] at h1
    simpa [mul_inv_eq_one] using h1
  have hx1 : (x : Γ) = 1 := by
    apply h.α_inj
    ext q
    obtain ⟨b, hb, a, rfl⟩ := h.exists_decomp he q
    rw [map_one, MulAut.one_apply, map_mul, map_zpow, hxe, h.X_fixes x x.2 b hb]
  exact Subtype.ext hx1

include h in
theorem xiHom_surjective {e : Q} (he : e ∉ B) : Function.Surjective (h.xiHom e) := by
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : ↥X →* Q, ψ = B.subtype.comp (h.xiHom e) := ⟨_, rfl⟩
  have hψ : ∀ x : ↥X, ψ x = α x e * e⁻¹ := fun x => by rw [hψdef]; rfl
  have hle : ψ.range ≤ B := by
    rintro _ ⟨x, rfl⟩
    rw [hψ]
    exact h.mul_inv_mem x.2 e
  have hinv : ∀ w : Γ, ∀ s ∈ ψ.range, α w s ∈ ψ.range := by
    intro w s hs
    obtain ⟨x, rfl⟩ := hs
    have hy : w * (x : Γ) * w⁻¹ ∈ X := h.X_normal w x x.2
    obtain ⟨b', hb', a, hwe⟩ := h.exists_decomp he (α w e)
    refine ⟨(⟨w * (x : Γ) * w⁻¹, hy⟩ : ↥X) ^ a, ?_⟩
    rw [map_zpow]
    have h1 : α w (α (x : Γ) e) = α (w * (x : Γ) * w⁻¹) (α w e) := by
      calc α w (α (x : Γ) e) = α (w * (x : Γ)) e := by rw [map_mul, MulAut.mul_apply]
        _ = α (w * (x : Γ) * w⁻¹ * w) e := by rw [inv_mul_cancel_right]
        _ = α (w * (x : Γ) * w⁻¹) (α w e) := by rw [map_mul, MulAut.mul_apply]
    have h2 : α w (ψ x) = α (w * (x : Γ) * w⁻¹) (α w e) * (α w e)⁻¹ := by
      rw [hψ, map_mul, map_inv, h1]
    rw [h2, hψ]
    generalize w * (x : Γ) * w⁻¹ = y at hy ⊢
    rw [hwe, map_mul, map_zpow, h.X_fixes _ hy b' hb', h.mul_mul_inv_comm,
      Commute.mul_zpow (h.comm _ _), inv_zpow]
  rcases h.B_irr ψ.range hle hinv with hbot | htop
  · exfalso
    apply h.X_ne_bot
    rw [eq_bot_iff]
    intro x hx
    rw [Subgroup.mem_bot]
    have hψx : ψ ⟨x, hx⟩ = 1 := by
      have hmem : ψ ⟨x, hx⟩ ∈ ψ.range := ⟨_, rfl⟩
      rw [hbot, Subgroup.mem_bot] at hmem
      exact hmem
    have hxi : h.xiHom e ⟨x, hx⟩ = 1 := Subtype.ext (by rw [coe_xiHom]; rw [hψ] at hψx; exact hψx)
    exact congrArg Subtype.val (h.xiHom_injective he (hxi.trans (map_one _).symm))
  · intro b
    have hb : (b : Q) ∈ ψ.range := htop ▸ b.2
    obtain ⟨x, hx⟩ := hb
    exact ⟨x, Subtype.ext (by rw [coe_xiHom, ← hψ]; exact hx)⟩

include h in
theorem exists_unique_regular {e e' : Q} (he : e ∉ B) (he' : e' ∉ B) :
    ∃! x : ↥X, ∃ k : ℤ, α x e = e' ^ k := by
  have : Fact p.Prime := ⟨h.prime⟩
  obtain ⟨b₀, hb₀, a, hea⟩ := h.exists_decomp he e'
  have hpa : ¬ (p : ℤ) ∣ a := by
    intro hdvd
    apply he'
    have h1 : e ^ a = 1 :=
      orderOf_dvd_iff_zpow_eq_one.1 (by rw [h.orderOf_eq he]; exact hdvd)
    rw [hea, h1, mul_one]
    exact hb₀
  obtain ⟨k₀, hk₀⟩ : ∃ k₀ : ℤ, (p : ℤ) ∣ a * k₀ - 1 := by
    have ha0 : (a : ZMod p) ≠ 0 := fun h0 => hpa ((ZMod.intCast_zmod_eq_zero_iff_dvd a p).1 h0)
    refine ⟨(((a : ZMod p)⁻¹).val : ℤ), ?_⟩
    apply (ZMod.intCast_zmod_eq_zero_iff_dvd _ p).1
    push_cast
    rw [ZMod.natCast_zmod_val, mul_inv_cancel₀ ha0, sub_self]
  have key : ∀ (x : ↥X) (k : ℤ), α x e = e' ^ k →
      (p : ℤ) ∣ a * k - 1 ∧ ((h.xiHom e x : ↥B) : Q) = b₀ ^ k := by
    intro x k hk
    have hxi : ((h.xiHom e x : ↥B) : Q) = b₀ ^ k * e ^ (a * k - 1) := by
      rw [coe_xiHom, hk, hea, Commute.mul_zpow (h.comm _ _), ← zpow_mul, zpow_sub_one, mul_assoc]
    have hmem : e ^ (a * k - 1) ∈ B := by
      have h1 : e ^ (a * k - 1) = (b₀ ^ k)⁻¹ * ((h.xiHom e x : ↥B) : Q) := by
        rw [hxi, ← mul_assoc, inv_mul_cancel, one_mul]
      rw [h1]
      exact B.mul_mem (B.inv_mem (B.zpow_mem hb₀ k)) (h.xiHom e x).2
    have hdvd := (h.zpow_mem_iff_dvd he _).1 hmem
    have h1 : e ^ (a * k - 1) = 1 :=
      orderOf_dvd_iff_zpow_eq_one.1 (by rw [h.orderOf_eq he]; exact hdvd)
    exact ⟨hdvd, by rw [hxi, h1, mul_one]⟩
  obtain ⟨x₀, hx₀⟩ := h.xiHom_surjective he ⟨b₀ ^ k₀, B.zpow_mem hb₀ k₀⟩
  have hx₀' : α (x₀ : Γ) e * e⁻¹ = b₀ ^ k₀ := by
    have := congrArg Subtype.val hx₀
    rwa [coe_xiHom] at this
  refine ⟨x₀, ⟨k₀, ?_⟩, ?_⟩
  · have h1 : α (x₀ : Γ) e = b₀ ^ k₀ * e := by
      rw [← hx₀', inv_mul_cancel_right]
    rw [h1, hea, Commute.mul_zpow (h.comm _ _), ← zpow_mul,
      h.zpow_congr e (m := a * k₀) (n := 1) (by simpa using hk₀), zpow_one]
  · rintro y ⟨l, hl⟩
    obtain ⟨hl1, hl2⟩ := key y l hl
    have hlk : (p : ℤ) ∣ l - k₀ := by
      have hprime : Prime (p : ℤ) := Nat.prime_iff_prime_int.1 h.prime
      have hmul : (p : ℤ) ∣ a * (l - k₀) := by
        have := dvd_sub hl1 hk₀
        rwa [show a * l - 1 - (a * k₀ - 1) = a * (l - k₀) by ring] at this
      exact (hprime.dvd_or_dvd hmul).resolve_left hpa
    have : h.xiHom e y = h.xiHom e x₀ := by
      apply Subtype.ext
      rw [hl2, coe_xiHom, hx₀', h.zpow_congr b₀ hlk]
    exact h.xiHom_injective he this

include h in
theorem nonempty_mulEquiv {e : Q} (he : e ∉ B) : Nonempty (↥X ≃* ↥B) :=
  ⟨MulEquiv.ofBijective (h.xiHom e) ⟨h.xiHom_injective he, h.xiHom_surjective he⟩⟩

include h in
theorem exists_mul_stabilizes {c : Q} (hc : c ∉ B) (φ : Γ) :
    ∃ x ∈ X, ∃ k : ℤ, α (x * φ) c = c ^ k := by
  have hφc : α φ c ∉ B := fun hmem => hc (by simpa using h.B_inv φ⁻¹ _ hmem)
  obtain ⟨x, ⟨k, hk⟩, -⟩ := h.exists_unique_regular hφc hc
  exact ⟨x, x.2, k, by rw [map_mul, MulAut.mul_apply]; exact hk⟩

include h in
theorem eq_one_of_stabilizes {c : Q} (hc : c ∉ B) {x : Γ} (hx : x ∈ X)
    (hk : ∃ k : ℤ, α x c = c ^ k) : x = 1 := by
  obtain ⟨y, -, huniq⟩ := h.exists_unique_regular hc hc
  have h1 : (⟨x, hx⟩ : ↥X) = y := huniq _ hk
  have h2 : (1 : ↥X) = y := huniq _ ⟨1, by simp⟩
  exact congrArg Subtype.val (h1.trans h2.symm)

end Data

end Sec1211

section Hypotheses

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem E_le_cNormalizer (h : Sec12Hyp G p A c L E) : E ≤ cNormalizer c := by
  intro e he
  refine Subgroup.centralizer_le_normalizer _ ?_
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hc : c * e = e * c :=
    congrArg Subtype.val (h.E_elem.is_comm.comm ⟨c, h.A_le_E h.c_mem⟩ ⟨e, he⟩)
  exact (Commute.zpow_left (hc : Commute c e) j).eq

theorem E_le_normalizer_L (h122b : Node122b) (h : Sec12Hyp G p A c L E) :
    E ≤ Subgroup.normalizer (L : Set G) := fun _ he =>
  h122b G p A c L E h ⟨E_le_cNormalizer h he, Subgroup.le_normalizer he⟩

theorem commutator_le_L (h122b : Node122b) (h : Sec12Hyp G p A c L E) :
    ⁅E, L ⊓ torusNormalizer E⁆ ≤ L := by
  rw [Subgroup.commutator_le]
  intro e he l hl
  have h1 : e * l * e⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.1 (E_le_normalizer_L h122b h he) l).1
    (Subgroup.mem_inf.1 hl).1
  rw [commutatorElement_def]
  exact L.mul_mem h1 (L.inv_mem (Subgroup.mem_inf.1 hl).1)

theorem pCoreFixed_eq_commutator (h124 : Node124) (h125 : Node125) (h : Sec12Hyp G p A c L E)
    (hX : torusWeylHasPCore p E) : pCoreFixed p E = ⁅E, L ⊓ torusNormalizer E⁆ := by
  have hp := h.prime
  have : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card E :=
    dvd_trans (dvd_pow_self p (by norm_num)) h.pow_three_dvd_card_E
  have hinvW := torusInvariant_pCoreFixed p E
  have hinvL : torusInvariant E L (pCoreFixed p E) := fun w hw =>
    hinvW w ⟨Subgroup.mem_top w, hw.2⟩
  rcases (h124 G p A c L E h).1 (pCoreFixed p E) (pCoreFixed_le p E) hinvL
      (pCoreFixed_ne_bot hdvd) (pCoreFixed_ne_top hX) with hc | hc
  · exact absurd (torusNormalizer_le_cNormalizer_of_invariant (hc ▸ hinvW)) (h125 G p A c L E h)
  · exact hc

theorem zpowers_comm_E (h : Sec12Hyp G p A c L E) :
    ∀ k ∈ Subgroup.zpowers c, ∀ e ∈ E, k * e = e * k := by
  intro k hk e he
  obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hk
  have hc : c * e = e * c :=
    congrArg Subtype.val (h.E_elem.is_comm.comm ⟨c, h.A_le_E h.c_mem⟩ ⟨e, he⟩)
  exact (Commute.zpow_left (hc : Commute c e) j).eq

end Hypotheses

theorem node1210_of_inputs (h122b : Node122b) (h124 : Node124) (h124b : Node124b)
    (h125 : Node125) : Node1210 := by
  intro G _ _ p A c L E h _ hX
  have hp := h.prime
  have hB0 := pCoreFixed_eq_commutator h124 h125 h hX
  have hB0top := pCoreFixed_ne_top hX
  have hZ : ¬ p ∣ Nat.card (Subgroup.center L) := fun hZ =>
    hB0top (hB0.trans (h124b G p A c L E h hZ))
  have hsplit : E = Subgroup.zpowers c ⊔ pCoreFixed p E ∧
      Subgroup.zpowers c ⊓ pCoreFixed p E = ⊥ := by
    rcases (h124 G p A c L E h).2 with ⟨hsup, hinf⟩ | ⟨-, hEE⟩
    · rw [hB0]
      exact ⟨hsup, hinf⟩
    · exact absurd (hB0.trans hEE) hB0top
  have hcL : c ∉ L := Sec12Three.c_not_mem_L h hZ
  have hLB : pCoreFixed p E ≤ L := hB0 ▸ commutator_le_L h122b h
  have hcomm : ∀ k ∈ Subgroup.zpowers c, ∀ l ∈ pCoreFixed p E, k * l = l * k := fun k hk l hl =>
    zpowers_comm_E h k hk l (pCoreFixed_le p E hl)
  have heq : pCoreFixed p E = E ⊓ L := by
    refine le_antisymm (le_inf (pCoreFixed_le p E) hLB) (fun x hx => ?_)
    obtain ⟨z, hz, b, hb, rfl⟩ := exists_mul_of_mem_sup_of_commute hcomm
      (hsplit.1 ▸ (Subgroup.mem_inf.1 hx).1)
    have hzL : z ∈ L := by
      have := L.mul_mem (Subgroup.mem_inf.1 hx).2 (L.inv_mem (hLB hb))
      rwa [mul_inv_cancel_right] at this
    have hz1 : z ∈ Subgroup.zpowers c ⊓ L := ⟨hz, hzL⟩
    rw [Sec12Three.zpowers_inf_eq_bot hp (Sec12Three.orderOf_c h) hcL, Subgroup.mem_bot] at hz1
    rw [hz1, one_mul]
    exact hb
  refine ⟨heq, ?_, hZ⟩
  have hcard := card_sup_of_commute_disjoint hcomm (disjoint_iff.2 hsplit.2)
  rw [← hsplit.1, Nat.card_zpowers, Sec12Three.orderOf_c h, heq] at hcard
  exact hcard

section Eleven

variable [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem data_of_inputs (h124 : Node124) (h125 : Node125) (h : Sec12Hyp G p A c L E)
    (hX : torusWeylHasPCore p E) (hfix : pCoreFixed p E = E ⊓ L)
    (hcard : Nat.card E = p * Nat.card ↥(E ⊓ L)) (hZ : ¬ p ∣ Nat.card (Subgroup.center L)) :
    Sec1211.Data p (torusWeyl E).subtype ((E ⊓ L).subgroupOf E) (CFSG.pCore p ↥(torusWeyl E)) := by
  have hp := h.prime
  have hcL : c ∉ L := Sec12Three.c_not_mem_L h hZ
  have hBle : E ⊓ L ≤ E := inf_le_left
  have hmemB : ∀ b : ↥E, b ∈ (E ⊓ L).subgroupOf E ↔ (b : G) ∈ E ⊓ L := fun b =>
    Subgroup.mem_subgroupOf
  refine
    { prime := hp
      comm := fun a b => h.E_elem.is_comm.comm a b
      pow_eq_one := fun a => Subtype.ext (by simpa using Sec12Three.pow_eq_one_of_mem_E h a.2)
      card_eq := ?_
      α_inj := Subtype.val_injective
      X_normal := fun w x hx =>
        (CFSG.pCore_normal (p := p) (G := ↥(torusWeyl E))).conj_mem x hx w
      X_pgroup := CFSG.pCore_isPGroup
      X_fixes := ?_
      B_inv := ?_
      B_irr := ?_
      X_ne_bot := hX }
  · exact hcard.trans (congrArg (p * ·)
      (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBle).toEquiv.symm))
  · intro x hx b hb
    exact (mem_pCoreFixed.1 (hfix.ge ((hmemB b).1 hb))).2 x hx
  · intro w b hb
    have hinv := (LinAlg.torusInvariant_top_iff_forall_torusWeyl (pCoreFixed_le p E)).1
      (torusInvariant_pCoreFixed p E) (w : MulAut E) w.2 b (hfix.ge ((hmemB b).1 hb))
    exact (hmemB _).2 (hfix.le hinv)
  · intro S hS hSinv
    have hS'E : S.map E.subtype ≤ E := Subgroup.map_subtype_le S
    have hS'B : S.map E.subtype ≤ E ⊓ L := by
      intro x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hx
      exact (hmemB s).1 (hS hs)
    have hinvW : torusInvariant E ⊤ (S.map E.subtype) := by
      rw [LinAlg.torusInvariant_top_iff_forall_torusWeyl hS'E]
      intro φ hφ b hb
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hb
      exact Subgroup.mem_map.2 ⟨(torusWeyl E).subtype ⟨φ, hφ⟩ s, hSinv ⟨φ, hφ⟩ s hs, rfl⟩
    have hinvL : torusInvariant E L (S.map E.subtype) := fun w hw =>
      hinvW w ⟨Subgroup.mem_top w, hw.2⟩
    by_cases hS0 : S.map E.subtype = ⊥
    · left
      exact (Subgroup.map_eq_bot_iff_of_injective S E.subtype_injective).1 hS0
    · right
      have hS'ne : S.map E.subtype ≠ E := fun heq =>
        pCoreFixed_ne_top hX (le_antisymm (pCoreFixed_le p E)
          (heq.symm.le.trans (hS'B.trans hfix.ge)))
      rcases (h124 G p A c L E h).1 _ hS'E hinvL hS0 hS'ne with hc | hc
      · exfalso
        have hcS : c ∈ S.map E.subtype := hc ▸ Subgroup.mem_zpowers c
        exact hcL (Subgroup.mem_inf.1 (hS'B hcS)).2
      · apply Subgroup.map_injective E.subtype_injective
        calc S.map E.subtype = ⁅E, L ⊓ torusNormalizer E⁆ := hc
          _ = pCoreFixed p E := (pCoreFixed_eq_commutator h124 h125 h hX).symm
          _ = E ⊓ L := hfix
          _ = ((E ⊓ L).subgroupOf E).map E.subtype :=
            (Subgroup.map_subgroupOf_eq_of_le hBle).symm

omit [Finite G] in
theorem exists_zpow_of_mem_torusImage (hcE : c ∈ E) {φ : MulAut E}
    (hφ : φ ∈ torusImage E (cNormalizer c)) : ∃ k : ℤ, φ ⟨c, hcE⟩ = (⟨c, hcE⟩ : E) ^ k := by
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hφ
  have hwc : (w : G) ∈ cNormalizer c := hw
  have h1 : (w : G) * c * (w : G)⁻¹ ∈ Subgroup.zpowers c :=
    (Subgroup.mem_normalizer_iff.1 hwc c).1 (Subgroup.mem_zpowers c)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 h1
  refine ⟨k, Subtype.ext ?_⟩
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_zpow]
  exact hk.symm

theorem mem_torusImage_of_zpow (hcE : c ∈ E) {φ : MulAut E}
    (hφ : φ ∈ torusWeyl E) (k : ℤ) (hk : φ ⟨c, hcE⟩ = (⟨c, hcE⟩ : E) ^ k) :
    φ ∈ torusImage E (cNormalizer c) := by
  obtain ⟨w, rfl⟩ := hφ
  refine Subgroup.mem_map.2 ⟨w, ?_, rfl⟩
  show (w : G) ∈ cNormalizer c
  apply Sec127.mem_cNormalizer_of_conj_mem
  have h1 := congrArg Subtype.val hk
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_zpow] at h1
  rw [h1]
  exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers c) k

theorem node1211_of_inputs (h124 : Node124) (h125 : Node125) (h1210 : Node1210) : Node1211 := by
  intro G _ _ p A c L E h hT hX
  obtain ⟨hfix, hcard, hZ⟩ := h1210 G p A c L E h hT hX
  have hD := data_of_inputs h124 h125 h hX hfix hcard hZ
  have hcL : c ∉ L := Sec12Three.c_not_mem_L h hZ
  have hcE : c ∈ E := h.A_le_E h.c_mem
  have hnot : ∀ e : ↥E, (e : G) ∉ L → e ∉ (E ⊓ L).subgroupOf E := fun e he hmem =>
    he (Subgroup.mem_inf.1 (Subgroup.mem_subgroupOf.1 hmem)).2
  have hcB : (⟨c, hcE⟩ : ↥E) ∉ (E ⊓ L).subgroupOf E := hnot _ hcL
  refine ⟨?_, fun e e' he he' => hD.exists_unique_regular (hnot e he) (hnot e' he'), ?_, ?_⟩
  · obtain ⟨e1⟩ := hD.nonempty_mulEquiv hcB
    exact ⟨e1.trans (Subgroup.subgroupOfEquivOfLe inf_le_left)⟩
  · apply le_antisymm
    · exact sup_le (Subgroup.map_subtype_le _) (Sec127.torusImage_le_torusWeyl E _)
    · intro φ hφ
      obtain ⟨x, hx, k, hk⟩ := hD.exists_mul_stabilizes hcB ⟨φ, hφ⟩
      have hψ : (x : MulAut E) * φ ∈ torusImage E (cNormalizer c) :=
        mem_torusImage_of_zpow hcE (mul_mem x.2 hφ) k hk
      have hφeq : φ = (x : MulAut E)⁻¹ * ((x : MulAut E) * φ) := by simp
      rw [hφeq]
      exact Subgroup.mul_mem_sup (inv_mem (Subgroup.mem_map_of_mem _ hx)) hψ
  · rw [eq_bot_iff]
    rintro φ ⟨hφX, hφH⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hφX
    obtain ⟨k, hk⟩ := exists_zpow_of_mem_torusImage hcE hφH
    have hx1 := hD.eq_one_of_stabilizes hcB hx ⟨k, hk⟩
    rw [Subgroup.mem_bot]
    simp [hx1]

end Eleven

end CFSG.RankThree.PartOne

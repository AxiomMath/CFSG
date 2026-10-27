module

public import CFSG.Quasithin.Background.E6TorusCover
public import CFSG.Quasithin.Vol2.Ch12Sec2E22BorelLiftBasic

public section

namespace CFSG.Quasithin.H13.KG4413

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open scoped Pointwise commutatorElement

theorem pow_index_mem_commutator {X : Type*} [Group X] [Finite X] (hperf : commutator X = ⊤)
    {ζ : X} (hζ : ζ ∈ Subgroup.center X) (L : Subgroup X) :
    ζ ^ L.index ∈ ⁅L, L⁆ := by
  classical
  have hkey : ∀ (k : ℕ) (g₀ : X), g₀⁻¹ * ζ ^ k * g₀ ∈ L → g₀⁻¹ * ζ ^ k * g₀ = ζ ^ k := by
    intro k g₀ _
    have h := Subgroup.mem_center_iff.mp ((Subgroup.center X).pow_mem hζ k) g₀
    calc g₀⁻¹ * ζ ^ k * g₀ = g₀⁻¹ * (ζ ^ k * g₀) := mul_assoc _ _ _
      _ = g₀⁻¹ * (g₀ * ζ ^ k) := by rw [h]
      _ = ζ ^ k := by group
  have htr := MonoidHom.transfer_eq_pow (Abelianization.of : ↥L →* Abelianization ↥L) ζ hkey
  have h1 : MonoidHom.transfer (Abelianization.of : ↥L →* Abelianization ↥L) ζ = 1 := by
    have hx : ζ ∈ commutator X := by
      rw [hperf]
      trivial
    exact Abelianization.commutator_subset_ker _ hx
  rw [htr] at h1
  have h2 : (⟨ζ ^ L.index, MonoidHom.transfer_eq_pow_aux ζ hkey⟩ : ↥L) ∈ commutator ↥L := by
    rw [← Abelianization.ker_of]
    exact h1
  rw [← Subgroup.map_subtype_commutator]
  exact ⟨_, h2, rfl⟩

variable {X X' : Type} [Group X] [Group X']

theorem commutator_normalizer_le {S D : Subgroup X}
    (hDN : D ≤ Subgroup.normalizer (S : Set X)) (hND : Subgroup.normalizer (S : Set X) ≤ D ⊔ S)
    (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) :
    ⁅Subgroup.normalizer (S : Set X), Subgroup.normalizer (S : Set X)⁆ ≤ S := by
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hDS : ((D ⊔ S : Subgroup X) : Set X) = (D : Set X) * (S : Set X) :=
    Subgroup.coe_mul_of_left_le_normalizer_right D S hDN
  have hx' : x ∈ ((D ⊔ S : Subgroup X) : Set X) := hND hx
  have hy' : y ∈ ((D ⊔ S : Subgroup X) : Set X) := hND hy
  rw [hDS] at hx' hy'
  obtain ⟨d₁, hd₁, s₁, hs₁, rfl⟩ := hx'
  obtain ⟨d₂, hd₂, s₂, hs₂, rfl⟩ := hy'
  have key : ⁅d₁ * s₁, d₂ * s₂⁆ = (d₁ * s₁ * d₁⁻¹) * ((d₁ * d₂) * (s₂ * s₁⁻¹) * (d₁ * d₂)⁻¹) *
      ((d₁ * d₂ * d₁⁻¹) * s₂⁻¹ * (d₁ * d₂ * d₁⁻¹)⁻¹) * (d₁ * d₂ * d₁⁻¹ * d₂⁻¹) := by
    rw [commutatorElement_def]
    group
  have hc : d₁ * d₂ * d₁⁻¹ * d₂⁻¹ = 1 := by
    rw [hDab d₁ hd₁ d₂ hd₂]
    group
  rw [key, hc, mul_one]
  have hN : ∀ g ∈ Subgroup.normalizer (S : Set X), ∀ t ∈ S, g * t * g⁻¹ ∈ S :=
    fun g hg t ht => (Subgroup.mem_normalizer_iff.1 hg t).1 ht
  refine S.mul_mem (S.mul_mem (hN d₁ (hDN hd₁) s₁ hs₁) (hN _ ?_ _ (S.mul_mem hs₂ (S.inv_mem hs₁))))
    (hN _ ?_ _ (S.inv_mem hs₂))
  · exact Subgroup.mul_mem _ (hDN hd₁) (hDN hd₂)
  · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hDN hd₁) (hDN hd₂)) (Subgroup.inv_mem _ (hDN hd₁))

theorem eq_one_of_odd_of_pow_two_pow {x : X} (hx : Odd (orderOf x)) {m : ℕ}
    (h : x ^ 2 ^ m = 1) : x = 1 := by
  have hdvd : orderOf x ∣ 2 ^ m := orderOf_dvd_of_pow_eq_one h
  have hcop : Nat.Coprime (orderOf x) (2 ^ m) :=
    Nat.Coprime.pow_right m (Nat.coprime_two_right.2 hx)
  exact orderOf_eq_one_iff.1 (Nat.Coprime.eq_one_of_dvd hcop hdvd)

variable [Finite X]

theorem mem_of_mem_normalizer_of_pow {S : Subgroup X} (hS : IsSylowTwoOf S ⊤) {x : X}
    (hx : x ∈ Subgroup.normalizer (S : Set X)) {e : ℕ} (hxe : x ^ 2 ^ e = 1) : x ∈ S := by
  have hx2 : IsPGroup 2 (Subgroup.zpowers x) := by
    rintro ⟨_, k, rfl⟩
    refine ⟨e, Subtype.ext ?_⟩
    show (x ^ k) ^ 2 ^ e = 1
    rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hxe, one_zpow]
  have hsup := IsPGroup.to_sup_of_normal_right' hx2 hS.2.1 (Subgroup.zpowers_le.2 hx)
  have hle := (A4.isSylowTwoOf_iff_maximal.1 hS).2.2 _ le_top hsup le_sup_right
  exact hle (Subgroup.mem_sup_left (Subgroup.mem_zpowers x))

theorem odd_orderOf_of_complement {S D : Subgroup X} (hS : IsSylowTwoOf S ⊤)
    (hDN : D ≤ Subgroup.normalizer (S : Set X)) (hDS : D ⊓ S = ⊥) {d : X} (hd : d ∈ D) :
    Odd (orderOf d) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨k, hk⟩ := hev
  have hpos : 0 < orderOf d := orderOf_pos d
  have hk0 : 0 < k := by omega
  have he : (d ^ k) ^ 2 ^ 1 = 1 := by
    rw [pow_one, ← pow_mul, mul_two, ← hk, pow_orderOf_eq_one]
  have hmem : d ^ k ∈ D ⊓ S :=
    ⟨D.pow_mem hd k, mem_of_mem_normalizer_of_pow hS (hDN (D.pow_mem hd k)) he⟩
  rw [hDS, Subgroup.mem_bot] at hmem
  exact pow_ne_one_of_lt_orderOf hk0.ne' (by omega) hmem

omit [Finite X] in
theorem isSylowTwoOf_map {φ : X →* X'} (hφ : Function.Surjective φ) {S : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) : IsSylowTwoOf (S.map φ) ⊤ := by
  refine ⟨le_top, hS.2.1.map φ, ?_⟩
  have h1 : ¬ 2 ∣ S.index := by
    have := hS.2.2
    rwa [← Subgroup.relIndex, Subgroup.relIndex_top_right] at this
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  exact fun h2 => h1 (h2.trans (Subgroup.index_map_dvd S hφ))

theorem isSylowTwoOf_of_sylow (P : Sylow 2 X) :
    IsSylowTwoOf (P : Subgroup X) ⊤ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine ⟨le_top, P.isPGroup', ?_⟩
  rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
  exact P.not_dvd_index

theorem natCast_eq_one_of_dvd_sub_one {p q : ℕ} (hq : 1 ≤ q) (h : p ∣ q - 1) :
    ((q : ℕ) : ZMod p) = 1 := by
  have h1 : ((q - 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  rw [Nat.cast_sub hq] at h1
  simpa [sub_eq_zero] using h1

theorem eq_two_of_dvd_two_pow {p k : ℕ} (hp : p.Prime) (h : p ∣ 2 ^ k) : p = 2 :=
  (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h)

theorem not_dvd_pow_add_one {p q : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hq : 1 ≤ q)
    (hpq : p ∣ q - 1) (k : ℕ) : ¬ p ∣ q ^ k + 1 := by
  intro h
  have h1 := natCast_eq_one_of_dvd_sub_one hq hpq
  have h2 : ((q ^ k + 1 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff _ _).2 h
  push_cast at h2
  rw [h1, one_pow] at h2
  have h3 : ((2 ^ 1 : ℕ) : ZMod p) = 0 := by
    push_cast
    linear_combination h2
  exact hp2 (eq_two_of_dvd_two_pow hp ((ZMod.natCast_eq_zero_iff _ _).1 h3))

@[expose] def WeylOut {Y : Type*} [Group Y] (S D : Subgroup Y) (n : ℕ) : Prop :=
  (∀ p : ℕ, p.Prime → p ≠ 2 → p ∣ 2 ^ n - 1 →
    ¬ p ∣ (Subgroup.normalizer (S : Set Y)).index) ∧
  (∀ d ∈ D, d ^ ((2 ^ n - 1) * (2 ^ n + 1)) = 1) ∧
  ∃ w : Y, w ∉ Subgroup.normalizer (S : Set Y) ∧ w * w = 1 ∧
    ∀ d ∈ D, (d ^ (2 ^ n - 1) = 1 → w * d * w⁻¹ = d⁻¹) ∧
      (d ^ (2 ^ n + 1) = 1 → w * d * w⁻¹ = d)

@[expose] def CartanWeyl (Y : Type*) [Group Y] (n : ℕ) : Prop :=
  ∀ S D : Subgroup Y, IsSylowTwoOf S ⊤ → D ≤ Subgroup.normalizer (S : Set Y) →
    Subgroup.normalizer (S : Set Y) ≤ D ⊔ S → D ⊓ S = ⊥ → WeylOut S D n

omit [Finite X] in
theorem WeylOut.map {S D : Subgroup X} {n : ℕ} (h : WeylOut S D n) (e : X ≃* X') :
    WeylOut (S.map e.toMonoidHom) (D.map e.toMonoidHom) n := by
  obtain ⟨hidx, hexp, w, hwS, hww, hact⟩ := h
  have hN : Subgroup.normalizer ((S.map e.toMonoidHom : Subgroup X') : Set X') =
      (Subgroup.normalizer (S : Set X)).map e.toMonoidHom :=
    (Subgroup.map_equiv_normalizer_eq S e).symm
  refine ⟨fun p hp hp2 hpq => ?_, ?_, e w, ?_, ?_, ?_⟩
  · rw [hN, Subgroup.index_map_of_bijective (f := e.toMonoidHom) e.bijective]
    exact hidx p hp hp2 hpq
  · rintro _ ⟨d, hd, rfl⟩
    rw [MulEquiv.coe_toMonoidHom, ← map_pow, hexp d hd, map_one]
  · intro hw
    rw [hN] at hw
    obtain ⟨w', hw', hww'⟩ := hw
    rw [MulEquiv.coe_toMonoidHom] at hww'
    exact hwS (e.injective hww' ▸ hw')
  · rw [← map_mul, hww, map_one]
  · rintro _ ⟨d, hd, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    refine ⟨fun h1 => ?_, fun h1 => ?_⟩
    · rw [← map_pow, MulEquiv.map_eq_one_iff] at h1
      rw [← map_inv, ← map_mul, ← map_mul, (hact d hd).1 h1, map_inv]
    · rw [← map_pow, MulEquiv.map_eq_one_iff] at h1
      rw [← map_inv, ← map_mul, ← map_mul, (hact d hd).2 h1]

theorem odd_card_of_complement {S D : Subgroup X} (hS : IsSylowTwoOf S ⊤)
    (hDN : D ≤ Subgroup.normalizer (S : Set X)) (hDS : D ⊓ S = ⊥) : Odd (Nat.card D) := by
  by_contra hev
  rw [Nat.not_odd_iff_even] at hev
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := D) 2 (even_iff_two_dvd.mp hev)
  have h1 := odd_orderOf_of_complement hS hDN hDS d.2
  rw [Subgroup.orderOf_coe, hd] at h1
  exact absurd h1 (by decide)

omit [Finite X] in
theorem card_normalizer_of_complement {S D : Subgroup X}
    (hDN : D ≤ Subgroup.normalizer (S : Set X)) (hND : Subgroup.normalizer (S : Set X) ≤ D ⊔ S)
    (hDS : D ⊓ S = ⊥) :
    Nat.card (Subgroup.normalizer (S : Set X)) = Nat.card D * Nat.card S := by
  have heq : D ⊔ S = Subgroup.normalizer (S : Set X) :=
    le_antisymm (sup_le hDN Subgroup.le_normalizer) hND
  have h := E2.BorelLift.card_sup_mul_card_inf hDN
  rw [hDS, Subgroup.card_bot, mul_one, heq] at h
  exact h

theorem WeylOut.of_complement {S D₀ D : Subgroup X} {n : ℕ} (hS : IsSylowTwoOf S ⊤)
    (hD₀N : D₀ ≤ Subgroup.normalizer (S : Set X))
    (hND₀ : Subgroup.normalizer (S : Set X) ≤ D₀ ⊔ S) (hD₀S : D₀ ⊓ S = ⊥)
    (hDN : D ≤ Subgroup.normalizer (S : Set X))
    (hND : Subgroup.normalizer (S : Set X) ≤ D ⊔ S) (hDS : D ⊓ S = ⊥) (h : WeylOut S D₀ n) :
    WeylOut S D n := by
  have hcard : Nat.card D = Nat.card D₀ := by
    have h1 := card_normalizer_of_complement hDN hND hDS
    have h2 := card_normalizer_of_complement hD₀N hND₀ hD₀S
    rw [h1] at h2
    exact Nat.eq_of_mul_eq_mul_right Nat.card_pos h2
  obtain ⟨s, hs, hDeq⟩ := E2.BorelLift.exists_conj_of_card_eq hS.2.1
    (odd_card_of_complement hS hD₀N hD₀S) hD₀N (hDN.trans hND₀) hcard
  have hSs : S.map (MulAut.conj s⁻¹).toMonoidHom = S := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact S.mul_mem (S.mul_mem (S.inv_mem hs) hy) (by simpa using hs)
    · intro hx
      refine ⟨s * x * s⁻¹, S.mul_mem (S.mul_mem hs hx) (S.inv_mem hs), ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
  have h1 := h.map (MulAut.conj s⁻¹)
  rwa [hSs, ← hDeq] at h1

theorem cartanWeyl_of_exists {n : ℕ} {S₀ D₀ : Subgroup X} (hS₀ : IsSylowTwoOf S₀ ⊤)
    (hD₀N : D₀ ≤ Subgroup.normalizer (S₀ : Set X))
    (hND₀ : Subgroup.normalizer (S₀ : Set X) ≤ D₀ ⊔ S₀) (hD₀S : D₀ ⊓ S₀ = ⊥)
    (h : WeylOut S₀ D₀ n) : CartanWeyl X n := by
  intro S D hS hDN hND hDS
  obtain ⟨g, -, hg⟩ := A4.exists_conj_of_isSylowTwoOf hS₀ hS
  set c := MulAut.conj g with hc
  have hSg : S₀.map c.toMonoidHom = S := by
    ext x
    rw [hg x]
    constructor
    · rintro ⟨y, hy, rfl⟩
      simpa [hc, MulAut.conj_apply, mul_assoc] using hy
    · intro hx
      exact ⟨g⁻¹ * x * g, hx, by simp only [hc, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]; group⟩
  have hN : Subgroup.normalizer (S : Set X) =
      (Subgroup.normalizer (S₀ : Set X)).map c.toMonoidHom := by
    rw [← hSg, Subgroup.map_equiv_normalizer_eq]
  have h1 := h.map c
  rw [hSg] at h1
  refine WeylOut.of_complement hS ?_ ?_ ?_ hDN hND hDS h1
  · rw [hN]
    exact Subgroup.map_mono hD₀N
  · rw [hN, ← hSg, ← Subgroup.map_sup]
    exact Subgroup.map_mono hND₀
  · rw [← hSg, ← Subgroup.map_inf_eq _ _ _ c.injective, hD₀S, Subgroup.map_bot]

theorem exists_mem_normalizer_of_cartanWeyl {n : ℕ} (hW : CartanWeyl X' n)
    (hperf : commutator X = ⊤) (φ : X →* X') (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center X) (hodd : Odd (Nat.card φ.ker)) {S D A : Subgroup X}
    (hS : IsSylowTwoOf S ⊤) (hDN : D ≤ Subgroup.normalizer (S : Set X))
    (hND : Subgroup.normalizer (S : Set X) ≤ D ⊔ S) (hDS : D ⊓ S = ⊥)
    (hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hAD : A ≤ D) (hA : ∀ a ∈ A, a ^ p = 1) :
    ∃ x : X, x ∉ Subgroup.normalizer (S : Set X) ∧ x ∈ Subgroup.normalizer (A : Set X) := by
  classical
  have hS2 : IsPGroup 2 S := hS.2.1
  set S' := S.map φ with hS'def
  have hNmap : ∀ x : X, φ x ∈ Subgroup.normalizer (S' : Set X') ↔
      x ∈ Subgroup.normalizer (S : Set X) := fun x =>
    ⟨fun h => E2.TorusCover.mem_normalizer_of_map hker hodd hS2 h,
      fun h => Subgroup.le_normalizer_map φ (Subgroup.mem_map_of_mem φ h)⟩
  have hidx : (Subgroup.normalizer (S : Set X)).index =
      (Subgroup.normalizer (S' : Set X')).index := by
    have he : Subgroup.normalizer (S : Set X) = (Subgroup.normalizer (S' : Set X')).comap φ := by
      ext x
      exact (hNmap x).symm
    rw [he, Subgroup.index_comap_of_surjective _ hφ]
  set D' := D.map φ with hD'def
  have hD'N : D' ≤ Subgroup.normalizer (S' : Set X') := by
    rintro _ ⟨d, hd, rfl⟩
    exact (hNmap d).mpr (hDN hd)
  have hND' : Subgroup.normalizer (S' : Set X') ≤ D' ⊔ S' := by
    intro y hy
    obtain ⟨x, rfl⟩ := hφ y
    have h1 : φ x ∈ (D ⊔ S).map φ := Subgroup.mem_map_of_mem φ (hND ((hNmap x).mp hy))
    rwa [Subgroup.map_sup] at h1
  have hD'S' : D' ⊓ S' = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨⟨d, hd, rfl⟩, ⟨s, hs, hsd⟩⟩
    obtain ⟨m, hm⟩ := hS2 ⟨s, hs⟩
    have hm' : s ^ 2 ^ m = 1 := congrArg Subtype.val hm
    have h2 : (φ d) ^ 2 ^ m = 1 := by rw [← hsd, ← map_pow, hm', map_one]
    have ho : Odd (orderOf (φ d)) :=
      (odd_orderOf_of_complement hS hDN hDS hd).of_dvd_nat (orderOf_map_dvd φ d)
    exact Subgroup.mem_bot.mpr (eq_one_of_odd_of_pow_two_pow ho h2)
  obtain ⟨hidx', hexp, w', hwS, hww, hact⟩ :=
    hW S' D' (isSylowTwoOf_map hφ hS) hD'N hND' hD'S'
  obtain ⟨w₀, hw₀⟩ := hφ w'
  have hz : w₀ * w₀ ∈ φ.ker := by rw [MonoidHom.mem_ker, map_mul, hw₀, hww]
  obtain ⟨r, hr⟩ := hodd
  set c : X := (w₀ * w₀) ^ (r + 1) with hcdef
  have hc : c ∈ φ.ker := Subgroup.pow_mem _ hz _
  have hcc : c * c = w₀ * w₀ := by
    have h1 : (w₀ * w₀) ^ Nat.card φ.ker = 1 := by
      have := pow_card_eq_one' (G := φ.ker) (x := ⟨w₀ * w₀, hz⟩)
      exact congrArg Subtype.val this
    rw [hr] at h1
    rw [hcdef, ← pow_add, show r + 1 + (r + 1) = (2 * r + 1) + 1 by ring, pow_succ, h1, one_mul]
  have hccen : ∀ g : X, g * c = c * g := Subgroup.mem_center_iff.1 (hker hc)
  set w : X := w₀ * c⁻¹ with hwdef
  have hww1 : w * w = 1 := by
    have hci : ∀ g : X, g * c⁻¹ = c⁻¹ * g :=
      Subgroup.mem_center_iff.1 (hker (Subgroup.inv_mem _ hc))
    calc w * w = w₀ * (c⁻¹ * w₀) * c⁻¹ := by rw [hwdef]; group
      _ = w₀ * (w₀ * c⁻¹) * c⁻¹ := by rw [hci w₀]
      _ = (w₀ * w₀) * (c * c)⁻¹ := by group
      _ = 1 := by rw [hcc, mul_inv_cancel]
  have hφw : φ w = w' := by
    rw [hwdef, map_mul, map_inv, hw₀, (MonoidHom.mem_ker).1 hc, inv_one, mul_one]
  have hwinv : w⁻¹ = w := inv_eq_of_mul_eq_one_right hww1
  have hwN : w ∉ Subgroup.normalizer (S : Set X) := fun h => hwS (hφw ▸ (hNmap w).mpr h)
  refine ⟨w, hwN, A4.mem_normalizer_of_conj_mem fun a ha => ?_⟩
  have haD := hAD ha
  have hap := hA a ha
  have ha'D : φ a ∈ D' := Subgroup.mem_map_of_mem φ haD
  have ha'p : (φ a) ^ p = 1 := by rw [← map_pow, hap, map_one]
  by_cases h1 : p ∣ 2 ^ n - 1
  ·
    have hZp : ∀ z ∈ φ.ker, z ^ p = 1 → z = 1 := by
      intro z hzk hzp
      have hzc := hker hzk
      have h2 := commutator_normalizer_le hDN hND hDab
        (pow_index_mem_commutator hperf hzc (Subgroup.normalizer (S : Set X)))
      have hzo : Odd (orderOf z) := by
        have := orderOf_dvd_natCard (⟨z, hzk⟩ : φ.ker)
        rw [Subgroup.orderOf_mk] at this
        exact Odd.of_dvd_nat ⟨r, hr⟩ this
      obtain ⟨m, hm⟩ := hS2 ⟨_, h2⟩
      have hm' : (z ^ (Subgroup.normalizer (S : Set X)).index) ^ 2 ^ m = 1 :=
        congrArg Subtype.val hm
      have h3 : z ^ (Subgroup.normalizer (S : Set X)).index = 1 :=
        eq_one_of_odd_of_pow_two_pow (hzo.of_dvd_nat (orderOf_pow_dvd _)) hm'
      have hcop : Nat.Coprime p (Subgroup.normalizer (S : Set X)).index := by
        rw [Nat.Prime.coprime_iff_not_dvd hp, hidx]
        exact hidx' p hp hp2 h1
      have h4 : orderOf z ∣ Nat.gcd p (Subgroup.normalizer (S : Set X)).index :=
        Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hzp) (orderOf_dvd_of_pow_eq_one h3)
      rw [hcop, Nat.dvd_one] at h4
      exact orderOf_eq_one_iff.1 h4
    have ha'q : (φ a) ^ (2 ^ n - 1) = 1 := by
      obtain ⟨m, hm⟩ := h1
      rw [hm, pow_mul, ha'p, one_pow]
    have hinv := (hact (φ a) ha'D).1 ha'q
    set z := w * a * w⁻¹ * a with hzdef
    have hzk : z ∈ φ.ker := by
      rw [MonoidHom.mem_ker, hzdef, map_mul, map_mul, map_mul, map_inv, hφw, hinv,
        inv_mul_cancel]
    have hzcen : ∀ g : X, g * z = z * g := Subgroup.mem_center_iff.1 (hker hzk)
    have hwa : w * a * w⁻¹ = z * a⁻¹ := by rw [hzdef]; group
    have hzp : z ^ p = 1 := by
      have e1 : (w * a * w⁻¹) ^ p = 1 := by rw [conj_pow, hap, mul_one, mul_inv_cancel]
      have hcomm : Commute z a⁻¹ := (hzcen a⁻¹).symm
      rw [hwa, hcomm.mul_pow, inv_pow, hap, inv_one, mul_one] at e1
      exact e1
    have hz1 := hZp z hzk hzp
    rw [hwa, hz1, one_mul]
    exact A.inv_mem ha
  · by_cases h2 : p ∣ 2 ^ n + 1
    · have ha'q : (φ a) ^ (2 ^ n + 1) = 1 := by
        obtain ⟨m, hm⟩ := h2
        rw [hm, pow_mul, ha'p, one_pow]
      have hcen := (hact (φ a) ha'D).2 ha'q
      set d := w * a * w⁻¹ * a⁻¹ with hddef
      have hdk : d ∈ φ.ker := by
        rw [MonoidHom.mem_ker, hddef, map_mul, map_mul, map_mul, map_inv, map_inv, hφw, hcen,
          mul_inv_cancel]
      have hdcen : ∀ g : X, g * d = d * g := Subgroup.mem_center_iff.1 (hker hdk)
      have hwa : w * a * w⁻¹ = d * a := by rw [hddef]; group
      have hd2 : d ^ 2 ^ 1 = 1 := by
        have e1 : a = w * (w * a * w⁻¹) * w⁻¹ := by
          calc a = (w * w) * a * (w * w)⁻¹ := by rw [hww1]; group
            _ = w * (w * a * w⁻¹) * w⁻¹ := by group
        rw [hwa] at e1
        have e2 : w * (d * a) * w⁻¹ = d * (d * a) := by
          calc w * (d * a) * w⁻¹ = d * (w * a * w⁻¹) := by rw [← mul_assoc, hdcen w]; group
            _ = d * (d * a) := by rw [hwa]
        rw [e2] at e1
        have e3 : d * d = 1 := by
          calc d * d = d * (d * a) * a⁻¹ := by group
            _ = 1 := by rw [← e1, mul_inv_cancel]
        rw [pow_one, sq, e3]
      have hdo : Odd (orderOf d) := by
        have := orderOf_dvd_natCard (⟨d, hdk⟩ : φ.ker)
        rw [Subgroup.orderOf_mk] at this
        exact Odd.of_dvd_nat ⟨r, hr⟩ this
      rw [hwa, eq_one_of_odd_of_pow_two_pow hdo hd2, one_mul]
      exact ha
    ·
      have ha'1 : φ a = 1 := by
        have hcop1 : Nat.Coprime p (2 ^ n - 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 h1
        have hcop2 : Nat.Coprime p (2 ^ n + 1) := (Nat.Prime.coprime_iff_not_dvd hp).2 h2
        have hcop : Nat.Coprime p ((2 ^ n - 1) * (2 ^ n + 1)) := Nat.Coprime.mul_right hcop1 hcop2
        have h4 : orderOf (φ a) ∣ Nat.gcd p ((2 ^ n - 1) * (2 ^ n + 1)) :=
          Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ha'p)
            (orderOf_dvd_of_pow_eq_one (hexp (φ a) ha'D))
        rw [hcop, Nat.dvd_one] at h4
        exact orderOf_eq_one_iff.1 h4
      have hak : a ∈ φ.ker := ha'1
      rw [E2.TorusCover.conj_of_central (hker hak) w]
      exact ha

end CFSG.Quasithin.H13.KG4413

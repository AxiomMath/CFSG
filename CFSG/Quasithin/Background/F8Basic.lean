module

public import CFSG.Quasithin.Background.F7
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
open CFSG.Quasithin.CosetGeom
open scoped Pointwise

variable {G : Type*} [Group G]

@[expose] def centralizerMod (V₁ X U : Subgroup G) : Subgroup G where
  carrier := {x | x ∈ X ∧ x ∈ Subgroup.normalizer (V₁ : Set G) ∧
    ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ V₁}
  one_mem' := ⟨X.one_mem, Subgroup.one_mem _, fun u _ => by simp⟩
  mul_mem' := by
    rintro x y ⟨hxX, hxN, hx⟩ ⟨hyX, hyN, hy⟩
    refine ⟨X.mul_mem hxX hyX, Subgroup.mul_mem _ hxN hyN, fun u hu => ?_⟩
    have h1 : x * (y * u * y⁻¹ * u⁻¹) * x⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp hxN _).mp (hy u hu)
    have h2 := V₁.mul_mem h1 (hx u hu)
    have e : x * y * u * (x * y)⁻¹ * u⁻¹ =
        x * (y * u * y⁻¹ * u⁻¹) * x⁻¹ * (x * u * x⁻¹ * u⁻¹) := by group
    rw [e]; exact h2
  inv_mem' := by
    rintro x ⟨hxX, hxN, hx⟩
    refine ⟨X.inv_mem hxX, Subgroup.inv_mem _ hxN, fun u hu => ?_⟩
    have h1 : x⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ * x⁻¹⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hxN) _).mp (V₁.inv_mem (hx u hu))
    have e : x⁻¹ * u * x⁻¹⁻¹ * u⁻¹ = x⁻¹ * (x * u * x⁻¹ * u⁻¹)⁻¹ * x⁻¹⁻¹ := by group
    rw [e]; exact h1

theorem mem_centralizerMod {V₁ X U : Subgroup G} {x : G} :
    x ∈ centralizerMod V₁ X U ↔ x ∈ X ∧ x ∈ Subgroup.normalizer (V₁ : Set G) ∧
      ∀ u ∈ U, x * u * x⁻¹ * u⁻¹ ∈ V₁ := Iff.rfl

theorem centralizerMod_le_left (V₁ X U : Subgroup G) : centralizerMod V₁ X U ≤ X :=
  fun _ hx => hx.1

theorem centralizerMod_le_normalizer (V₁ X U : Subgroup G) :
    centralizerMod V₁ X U ≤ Subgroup.normalizer (V₁ : Set G) := fun _ hx => hx.2.1

theorem centralizerMod_mono_left {V₁ X X' : Subgroup G} (U : Subgroup G) (h : X ≤ X') :
    centralizerMod V₁ X U ≤ centralizerMod V₁ X' U :=
  fun _ hx => ⟨h hx.1, hx.2⟩

theorem centralizerMod_anti_right {V₁ U U' : Subgroup G} (X : Subgroup G) (h : U ≤ U') :
    centralizerMod V₁ X U' ≤ centralizerMod V₁ X U :=
  fun _ hx => ⟨hx.1, hx.2.1, fun u hu => hx.2.2 u (h hu)⟩

theorem conjSub_centralizerMod (g : G) (V₁ X U : Subgroup G) :
    conjSub g (centralizerMod V₁ X U) =
      centralizerMod (conjSub g V₁) (conjSub g X) (conjSub g U) := by
  ext x
  rw [mem_conjSub, mem_centralizerMod, mem_centralizerMod, mem_conjSub, conjSub_normalizer,
    mem_conjSub]
  constructor
  · rintro ⟨hX, hN, h⟩
    refine ⟨hX, hN, fun u hu => ?_⟩
    rw [mem_conjSub] at hu ⊢
    have := h _ hu
    have e : g⁻¹ * (x * u * x⁻¹ * u⁻¹) * g =
        (g⁻¹ * x * g) * (g⁻¹ * u * g) * (g⁻¹ * x * g)⁻¹ * (g⁻¹ * u * g)⁻¹ := by group
    rw [e]; exact this
  · rintro ⟨hX, hN, h⟩
    refine ⟨hX, hN, fun u hu => ?_⟩
    have := h (g * u * g⁻¹) (mul_mem_conjSub hu)
    rw [mem_conjSub] at this
    have e : g⁻¹ * (x * (g * u * g⁻¹) * x⁻¹ * (g * u * g⁻¹)⁻¹) * g =
        (g⁻¹ * x * g) * u * (g⁻¹ * x * g)⁻¹ * u⁻¹ := by group
    rw [e] at this; exact this

theorem le_normalizer_centralizerMod {H V₁ X U : Subgroup G}
    (hV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) (hX : H ≤ Subgroup.normalizer (X : Set G))
    (hU : H ≤ Subgroup.normalizer (U : Set G)) :
    H ≤ Subgroup.normalizer (centralizerMod V₁ X U : Set G) := by
  intro h hh
  apply mem_normalizer_of_conjSub_eq
  rw [conjSub_centralizerMod, conjSub_eq_of_mem_normalizer (hV₁ hh),
    conjSub_eq_of_mem_normalizer (hX hh), conjSub_eq_of_mem_normalizer (hU hh)]

section Aux

variable [Finite G]

theorem exists_fixed_mod {T V V₁ : Subgroup G} (hT : IsPGroup 2 T) (hVT : V ≤ T)
    (hlt : V₁ < V) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hTV₁ : T ≤ Subgroup.normalizer (V₁ : Set G)) :
    ∃ z ∈ V, z ∉ V₁ ∧ ∀ t ∈ T, t * z * t⁻¹ * z⁻¹ ∈ V₁ := by
  have hN₁ : (V₁.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTV₁
  have hNV : (V.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTV
  have : Group.IsNilpotent (↥T ⧸ V₁.subgroupOf T) :=
    (hT.to_quotient (V₁.subgroupOf T)).isNilpotent
  let q : ↥T →* ↥T ⧸ V₁.subgroupOf T := QuotientGroup.mk' (V₁.subgroupOf T)
  let V' : Subgroup (↥T ⧸ V₁.subgroupOf T) := (V.subgroupOf T).map q
  have : V'.Normal := Subgroup.Normal.map hNV q (QuotientGroup.mk'_surjective _)
  obtain ⟨v, hvV, hvV₁⟩ : ∃ v ∈ V, v ∉ V₁ := by
    by_contra hcon
    push Not at hcon
    exact hlt.not_ge fun v hv => hcon v hv
  have hV'ne : V' ≠ ⊥ := by
    intro hbot
    have hmem : q ⟨v, hVT hvV⟩ ∈ V' :=
      Subgroup.mem_map_of_mem q (by simpa [Subgroup.mem_subgroupOf] using hvV)
    rw [hbot, Subgroup.mem_bot] at hmem
    have : (⟨v, hVT hvV⟩ : ↥T) ∈ V₁.subgroupOf T := (QuotientGroup.eq_one_iff _).mp hmem
    exact hvV₁ (by simpa [Subgroup.mem_subgroupOf] using this)
  have hc := Group.IsNilpotent.inf_center_ne_bot_of_normal hV'ne
  obtain ⟨⟨x, hxmem⟩, hxne⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hc
  obtain ⟨hxV', hxZ⟩ := hxmem
  obtain ⟨y, hyV, rfl⟩ := hxV'
  have hyV' : (y : G) ∈ V := by simpa [Subgroup.mem_subgroupOf] using hyV
  have hyV₁ : (y : G) ∉ V₁ := by
    intro h
    apply hxne
    have : q y = 1 := (QuotientGroup.eq_one_iff y).mpr (by simpa [Subgroup.mem_subgroupOf] using h)
    exact Subtype.ext this
  refine ⟨y, hyV', hyV₁, fun t ht => ?_⟩
  have hcen := Subgroup.mem_center_iff.mp hxZ (q ⟨t, ht⟩⁻¹)
  rw [← map_mul, ← map_mul] at hcen
  have h1 := QuotientGroup.eq.mp hcen
  rw [Subgroup.mem_subgroupOf] at h1
  have h2 : (y : G)⁻¹ * t * y * t⁻¹ ∈ V₁ := by
    have e : (y : G)⁻¹ * t * y * t⁻¹ =
        ((⟨t, ht⟩⁻¹ * y : ↥T) : G)⁻¹ * ((y * ⟨t, ht⟩⁻¹ : ↥T) : G) := by
      simp [mul_assoc]
    rw [e]; exact h1
  have h3 : (y : G) * ((y : G)⁻¹ * t * y * t⁻¹) * (y : G)⁻¹ ∈ V₁ :=
    (Subgroup.mem_normalizer_iff.mp (hTV₁ y.2) _).mp h2
  have e : t * (y : G) * t⁻¹ * (y : G)⁻¹ = (y : G) * ((y : G)⁻¹ * t * y * t⁻¹) * (y : G)⁻¹ := by
    group
  rw [e]; exact h3

theorem exists_pow_two_pow_eq_one_of_stability {H V₁ : Subgroup G} (hHV₁ : H ≤ Subgroup.normalizer
    (V₁ : Set G)) (hV₁ : IsPGroup 2 V₁) (hchar : CharTwo H) {d : G} (hdH : d ∈ H)
    (hdC : d ∈ Subgroup.centralizer (V₁ : Set G))
    (hd : ∀ q ∈ pCoreOf 2 H, d * q * d⁻¹ * q⁻¹ ∈ V₁) : ∃ n : ℕ, d ^ 2 ^ n = 1 := by
  obtain ⟨a, ha⟩ := IsPGroup.iff_card.mp hV₁
  have key : ∀ q ∈ pCoreOf 2 H, d ^ 2 ^ a * q = q * d ^ 2 ^ a := by
    intro q hq
    have hqH : q ∈ H := pCoreOf_le 2 H hq
    set z : G := q⁻¹ * (d * q * d⁻¹ * q⁻¹) * q with hz
    have hzV₁ : z ∈ V₁ := by
      have := (Subgroup.mem_normalizer_iff.mp (hHV₁ (H.inv_mem hqH)) _).mp (hd q hq)
      simpa [hz] using this
    have hdz : d * z * d⁻¹ = z := by
      have := Subgroup.mem_centralizer_iff.mp hdC z hzV₁
      calc d * z * d⁻¹ = z * d * d⁻¹ := by rw [this]
        _ = z := by group
    have hdq : d * q * d⁻¹ = q * z := by simp only [hz]; group
    have hpow : ∀ n : ℕ, d ^ n * q * (d ^ n)⁻¹ = q * z ^ n := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
        have e : d ^ (n + 1) * q * (d ^ (n + 1))⁻¹ = d * (d ^ n * q * (d ^ n)⁻¹) * d⁻¹ := by
          rw [pow_succ']; group
        rw [e, ih]
        have e2 : d * (q * z ^ n) * d⁻¹ = (d * q * d⁻¹) * (d * z ^ n * d⁻¹) := by group
        rw [e2, hdq]
        have e3 : d * z ^ n * d⁻¹ = z ^ n := by
          have := conj_pow (a := d) (b := z) (i := n)
          rw [hdz] at this
          exact this.symm
        rw [e3, pow_succ']
        group
    have hz1 : z ^ 2 ^ a = 1 := by
      have := pow_card_eq_one' (G := V₁) (x := ⟨z, hzV₁⟩)
      rw [ha] at this
      simpa using congrArg Subtype.val this
    have := hpow (2 ^ a)
    rw [hz1, mul_one] at this
    calc d ^ 2 ^ a * q = (d ^ 2 ^ a * q * (d ^ 2 ^ a)⁻¹) * d ^ 2 ^ a := by group
      _ = q * d ^ 2 ^ a := by rw [this]
  have hmem : d ^ 2 ^ a ∈ Subgroup.centralizer (pCoreOf 2 H : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    exact (key q hq).symm
  have hQ := hchar ⟨H.pow_mem hdH _, hmem⟩
  obtain ⟨m, hm⟩ := pCoreOf_isPGroup 2 H ⟨_, hQ⟩
  refine ⟨a + m, ?_⟩
  rw [pow_add, pow_mul]
  simpa using congrArg Subtype.val hm

theorem commutator_le_of_irreducible {X W W₁ P : Subgroup G} (hP : IsPGroup 2 P) (hPX : P ≤ X)
    (hXW : X ≤ Subgroup.normalizer (W : Set G)) (hXW₁ : X ≤ Subgroup.normalizer (W₁ : Set G))
    (hXP : X ≤ Subgroup.normalizer (P : Set G)) (hW₁W : W₁ ≤ W) (hW : IsPGroup 2 W)
    (hWN : W ≤ Subgroup.normalizer (W₁ : Set G))
    (hirr : ∀ U : Subgroup G, W₁ ≤ U → U ≤ W → X ≤ Subgroup.normalizer (U : Set G) →
      U = W₁ ∨ U = W) :
    ∀ p ∈ P, ∀ w ∈ W, p * w * p⁻¹ * w⁻¹ ∈ W₁ := by
  by_cases hEq : W₁ = W
  · intro p hp w hw
    have : p * w * p⁻¹ ∈ W := (Subgroup.mem_normalizer_iff.mp (hXW (hPX hp)) w).mp hw
    rw [hEq]
    exact W.mul_mem this (W.inv_mem hw)
  · have hlt : W₁ < W := lt_of_le_of_ne hW₁W hEq
    have hPW : P ≤ Subgroup.normalizer (W : Set G) := hPX.trans hXW
    have hT : IsPGroup 2 (P ⊔ W : Subgroup G) := hP.to_sup_of_normal_right' hW hPW
    obtain ⟨z, hzW, hzW₁, hz⟩ := exists_fixed_mod (T := P ⊔ W) (V := W) (V₁ := W₁) hT
      le_sup_right hlt (sup_le hPW Subgroup.le_normalizer) (sup_le (hPX.trans hXW₁) hWN)
    have hzC : ∀ u ∈ P, z * u * z⁻¹ * u⁻¹ ∈ W₁ := by
      intro u hu
      have := W₁.inv_mem (hz u (Subgroup.mem_sup_left hu))
      have e : (u * z * u⁻¹ * z⁻¹)⁻¹ = z * u * z⁻¹ * u⁻¹ := by group
      rwa [e] at this
    have hUN : X ≤ Subgroup.normalizer ((W ⊓ centralizerMod W₁ ⊤ P : Subgroup G) : Set G) :=
      le_normalizer_inf hXW (le_normalizer_centralizerMod hXW₁ (fun x _ => by
        rw [Subgroup.mem_normalizer_iff]; intro y; simp) hXP)
    have hW₁U : W₁ ≤ W ⊓ centralizerMod W₁ ⊤ P := by
      intro x hx
      refine ⟨hW₁W hx, Subgroup.mem_top _, Subgroup.le_normalizer hx, fun u hu => ?_⟩
      have h1 : u * x⁻¹ * u⁻¹ ∈ W₁ :=
        (Subgroup.mem_normalizer_iff.mp (hPX.trans hXW₁ hu) x⁻¹).mp (W₁.inv_mem hx)
      have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
      rw [e]; exact W₁.mul_mem hx h1
    rcases hirr _ hW₁U inf_le_left hUN with h | h
    · exfalso
      apply hzW₁
      rw [← h]
      exact ⟨hzW, Subgroup.mem_top _, hWN hzW, hzC⟩
    · intro p hp w hw
      have hwU : w ∈ W ⊓ centralizerMod W₁ ⊤ P := by rw [h]; exact hw
      have := W₁.inv_mem (hwU.2.2.2 p hp)
      have e : (w * p * w⁻¹ * p⁻¹)⁻¹ = p * w * p⁻¹ * w⁻¹ := by group
      rwa [e] at this

theorem V_le_pCoreOf_and_commutator_le {H T V V₁ X : Subgroup G} (hT : IsSylowTwoOf T H)
    (hVT : V ≤ T) (hVel : IsElemAbelian 2 V) (hV₁V : V₁ ≤ V)
    (hTV₁ : T ≤ Subgroup.normalizer (V₁ : Set G)) (hTV : T ≤ Subgroup.normalizer (V : Set G))
    (hHV₁ : H ≤ Subgroup.normalizer (V₁ : Set G)) (hchar : CharTwo H) (hXH : X ≤ H)
    (hXV : X ≤ Subgroup.normalizer (V : Set G))
    (hirr : ∀ W : Subgroup G, V₁ ≤ W → W ≤ V → X ≤ Subgroup.normalizer (W : Set G) →
      W = V₁ ∨ W = V) :
    V ≤ pCoreOf 2 H ∧ ∀ v ∈ V, ∀ q ∈ pCoreOf 2 H, v * q * v⁻¹ * q⁻¹ ∈ V₁ := by
  have hV2 : IsPGroup 2 V := isPGroup_of_isElemAbelian hVel
  have hVH : V ≤ H := hVT.trans hT.1
  have hQT : pCoreOf 2 H ≤ T := isSylowTwoOf_pCoreOf_le hT
  have hQN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  have hV₁Q : V₁ ≤ pCoreOf 2 H :=
    le_pCoreOf_of_le_normalizer 2 (hV₁V.trans hVH) hHV₁ (hV2.to_le hV₁V)
  have htop : ∀ K : Subgroup G, K ≤ Subgroup.normalizer ((⊤ : Subgroup G) : Set G) :=
    fun K x _ => by rw [Subgroup.mem_normalizer_iff]; intro y; simp
  by_cases hEq : V₁ = V
  · refine ⟨hEq ▸ hV₁Q, fun v hv q hq => ?_⟩
    have hvV₁ : v ∈ V₁ := hEq ▸ hv
    have h1 : q * v⁻¹ * q⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (hHV₁ (pCoreOf_le 2 H hq)) v⁻¹).mp (V₁.inv_mem hvV₁)
    have e : v * q * v⁻¹ * q⁻¹ = v * (q * v⁻¹ * q⁻¹) := by group
    rw [e]; exact V₁.mul_mem hvV₁ h1
  · have hlt : V₁ < V := lt_of_le_of_ne hV₁V hEq
    obtain ⟨z, hzV, hzV₁, hz⟩ := exists_fixed_mod hT.2.1 hVT hlt hTV hTV₁
    have hzH : z ∈ H := hVH hzV
    have hzN : z ∈ Subgroup.normalizer (V₁ : Set G) := hTV₁ (hVT hzV)
    have hzC : ∀ q ∈ pCoreOf 2 H, z * q * z⁻¹ * q⁻¹ ∈ V₁ := by
      intro q hq
      have := V₁.inv_mem (hz q (hQT hq))
      have e : (q * z * q⁻¹ * z⁻¹)⁻¹ = z * q * z⁻¹ * q⁻¹ := by group
      rwa [e] at this
    have hzQ : z ∈ pCoreOf 2 H := by
      have hDN : H ≤ Subgroup.normalizer
          ((centralizerMod V₁ H (pCoreOf 2 H) ⊓ Subgroup.centralizer (V₁ : Set G) :
            Subgroup G) : Set G) :=
        le_normalizer_inf (le_normalizer_centralizerMod hHV₁ Subgroup.le_normalizer hQN)
          (hHV₁.trans (normalizer_le_normalizer_centralizer V₁))
      have hDp : IsPGroup 2 (centralizerMod V₁ H (pCoreOf 2 H) ⊓
          Subgroup.centralizer (V₁ : Set G) : Subgroup G) := by
        rintro ⟨d, hd⟩
        obtain ⟨n, hn⟩ := exists_pow_two_pow_eq_one_of_stability hHV₁ (hV2.to_le hV₁V) hchar
          hd.1.1 hd.2 hd.1.2.2
        exact ⟨n, Subtype.ext (by simpa using hn)⟩
      have hDQ := le_pCoreOf_of_le_normalizer 2
        (inf_le_left.trans (centralizerMod_le_left _ _ _)) hDN hDp
      have hzcent : z ∈ Subgroup.centralizer (V₁ : Set G) :=
        Subgroup.mem_centralizer_iff.mpr fun y hy => isElemAbelian_comm hVel (hV₁V hy) hzV
      exact hDQ ⟨⟨hzH, hzN, hzC⟩, hzcent⟩
    have hYV : V ⊓ pCoreOf 2 H ⊓ centralizerMod V₁ ⊤ (pCoreOf 2 H) ≤ V :=
      inf_le_left.trans inf_le_left
    have hV₁Y : V₁ ≤ V ⊓ pCoreOf 2 H ⊓ centralizerMod V₁ ⊤ (pCoreOf 2 H) := by
      intro x hx
      refine ⟨⟨hV₁V hx, hV₁Q hx⟩, Subgroup.mem_top _, Subgroup.le_normalizer hx, fun u hu => ?_⟩
      have h1 : u * x⁻¹ * u⁻¹ ∈ V₁ :=
        (Subgroup.mem_normalizer_iff.mp (hHV₁ (pCoreOf_le 2 H hu)) x⁻¹).mp (V₁.inv_mem hx)
      have e : x * u * x⁻¹ * u⁻¹ = x * (u * x⁻¹ * u⁻¹) := by group
      rw [e]; exact V₁.mul_mem hx h1
    have hXY : X ≤ Subgroup.normalizer
        ((V ⊓ pCoreOf 2 H ⊓ centralizerMod V₁ ⊤ (pCoreOf 2 H) : Subgroup G) : Set G) :=
      le_normalizer_inf (le_normalizer_inf hXV (hXH.trans hQN))
        (hXH.trans (le_normalizer_centralizerMod hHV₁ (htop H) hQN))
    have hzY : z ∈ V ⊓ pCoreOf 2 H ⊓ centralizerMod V₁ ⊤ (pCoreOf 2 H) :=
      ⟨⟨hzV, hzQ⟩, Subgroup.mem_top _, hzN, hzC⟩
    rcases hirr _ hV₁Y hYV hXY with h | h
    · exact absurd (h ▸ hzY) hzV₁
    · have hVY : V ≤ V ⊓ pCoreOf 2 H ⊓ centralizerMod V₁ ⊤ (pCoreOf 2 H) := h.symm.le
      exact ⟨fun v hv => (hVY hv).1.2, fun v hv q hq => (hVY hv).2.2.2 q hq⟩

omit [Finite G] in
theorem pow_mul_mem_of_normalizes {L : Subgroup G} {l t : G} (hl : l ∈ L)
    (ht : t ∈ Subgroup.normalizer (L : Set G)) (n : ℕ) : ∃ l' ∈ L, (l * t) ^ n = l' * t ^ n := by
  induction n with
  | zero => exact ⟨1, L.one_mem, by simp⟩
  | succ n ih =>
    obtain ⟨l', hl', h⟩ := ih
    have hc : t ^ n * l * (t ^ n)⁻¹ ∈ L :=
      (Subgroup.mem_normalizer_iff.mp (Subgroup.pow_mem _ ht n) l).mp hl
    refine ⟨l' * (t ^ n * l * (t ^ n)⁻¹), L.mul_mem hl' hc, ?_⟩
    rw [pow_succ, h]
    group

theorem charTwo_sup_of_normalizes {L T : Subgroup G} (hT : IsPGroup 2 T)
    (hTL : T ≤ Subgroup.normalizer (L : Set G)) (hL : CharTwo L) : CharTwo (L ⊔ T) :=
  CFSG.QuasithinUnique.CharTwo.sup_of_le_normalizer hL hT hTL

omit [Finite G] in
theorem frattini_map_le_of_forall {U V₁ : Subgroup G} (hU : IsPGroup 2 U)
    (hcomm : ∀ x ∈ U, ∀ y ∈ U, x * y * x⁻¹ * y⁻¹ ∈ V₁) (hsq : ∀ x ∈ U, x ^ 2 ∈ V₁)
    [Finite U] : (frattini U).map U.subtype ≤ V₁ := by
  have : Fact (IsPGroup 2 U) := ⟨hU⟩
  rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), MonoidHom.map_closure,
    Subgroup.closure_le]
  rintro _ ⟨x, hx | ⟨r, rfl⟩, rfl⟩
  · have h1 : (_root_.commutator U).map U.subtype ≤ V₁ := by
      rw [_root_.commutator_def, Subgroup.map_commutator]
      have : (⊤ : Subgroup U).map U.subtype = U := by
        rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
      rw [this, Subgroup.commutator_le]
      exact fun a ha b hb => hcomm a ha b hb
    exact h1 ⟨x, hx, rfl⟩
  · exact hsq r r.2

end Aux

@[expose] def L₁Of (L V₁ : Subgroup G) : Subgroup G :=
  oTwoRes (L ⊓ Subgroup.normalizer (V₁ : Set G))

structure HypF81 (T V L V₁ H : Subgroup G) : Prop where
  sylow : IsSylowTwoOf T ⊤
  elemAbelian : IsElemAbelian 2 V
  normalizes_L : T ≤ Subgroup.normalizer (L : Set G)
  oTwoRes_eq : oTwoRes L = L
  charTwo_L : CharTwo L
  reduced : IsTwoReducedIn (L ⊔ T) V
  cT : T ⊓ Subgroup.centralizer (V : Set G) = pCoreOf 2 (L ⊔ T)
  V₁_ne_bot : V₁ ≠ ⊥
  V₁_le_V : V₁ ≤ V
  T_normalizes_V₁ : T ≤ Subgroup.normalizer (V₁ : Set G)
  weak_a : ∀ g : G, V₁ ⊓ conjSub g⁻¹ V ≠ ⊥ → ⁅V, conjSub g⁻¹ V⁆ = ⊥
  V₁_lt_V : V₁ < V
  irred : ∀ W : Subgroup G, V₁ ≤ W → W ≤ V → L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (W : Set G) →
    W = V₁ ∨ W = V
  H_normalizes_V₁ : H ≤ Subgroup.normalizer (V₁ : Set G)
  L₁T_le_H : L₁Of L V₁ ⊔ T ≤ H
  charTwo_H : CharTwo H
  ker_le : coreIn (centralizerMod V₁ H V) H ≤ pCoreOf 2 H
  o2_trivial : pCoreOf 2 ((L ⊔ T) ⊔ H) = ⊥

theorem L₁Of_sup_le (L V₁ T : Subgroup G) : L₁Of L V₁ ⊔ T ≤ L ⊔ T :=
  sup_le_sup ((oTwoRes_le _).trans inf_le_left) le_rfl

namespace HypF81

variable {T V L V₁ H : Subgroup G}

theorem isPGroup_V (h : HypF81 T V L V₁ H) : IsPGroup 2 V := isPGroup_of_isElemAbelian h.elemAbelian

theorem V_le_pCoreOf_LT (h : HypF81 T V L V₁ H) : V ≤ pCoreOf 2 (L ⊔ T) :=
  le_pCoreOf_of_le_normalizer 2 h.reduced.1 h.reduced.2.1 h.isPGroup_V

theorem V_le_T (h : HypF81 T V L V₁ H) : V ≤ T := by
  have := h.V_le_pCoreOf_LT
  rw [← h.cT] at this
  exact this.trans inf_le_left

theorem T_le_H (h : HypF81 T V L V₁ H) : T ≤ H := le_sup_right.trans h.L₁T_le_H

theorem V_le_H (h : HypF81 T V L V₁ H) : V ≤ H := h.V_le_T.trans h.T_le_H

theorem sylow_H (h : HypF81 T V L V₁ H) : IsSylowTwoOf T H :=
  isSylowTwoOf_mono_right h.sylow h.T_le_H le_top

theorem sylow_LT (h : HypF81 T V L V₁ H) : IsSylowTwoOf T (L ⊔ T) :=
  isSylowTwoOf_mono_right h.sylow le_sup_right le_top

theorem T_normalizes_V (h : HypF81 T V L V₁ H) : T ≤ Subgroup.normalizer (V : Set G) :=
  le_sup_right.trans h.reduced.2.1

theorem L₁T_normalizes_V (h : HypF81 T V L V₁ H) :
    L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (V : Set G) :=
  (L₁Of_sup_le L V₁ T).trans h.reduced.2.1

theorem V₁_le_pCoreOf (h : HypF81 T V L V₁ H) : V₁ ≤ pCoreOf 2 H :=
  le_pCoreOf_of_le_normalizer 2 (h.V₁_le_V.trans h.V_le_H) h.H_normalizes_V₁
    (h.isPGroup_V.to_le h.V₁_le_V)

theorem V_le_pCoreOf_and_commutator_le [Finite G] (h : HypF81 T V L V₁ H) :
    V ≤ pCoreOf 2 H ∧ ∀ v ∈ V, ∀ q ∈ pCoreOf 2 H, v * q * v⁻¹ * q⁻¹ ∈ V₁ :=
  CFSG.Quasithin.V_le_pCoreOf_and_commutator_le h.sylow_H h.V_le_T h.elemAbelian h.V₁_le_V
    h.T_normalizes_V₁ h.T_normalizes_V h.H_normalizes_V₁ h.charTwo_H h.L₁T_le_H
    h.L₁T_normalizes_V h.irred

section F82

variable [Finite G]

theorem conjClosure_V_le_pCoreOf (h : HypF81 T V L V₁ H) : conjClosure V H ≤ pCoreOf 2 H := by
  obtain ⟨hVQ, -⟩ := h.V_le_pCoreOf_and_commutator_le
  refine conjClosure_le fun x hx v hv => ?_
  exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H hx) v).mp (hVQ hv)

theorem commutator_conjClosure_le (h : HypF81 T V L V₁ H) :
    ∀ u ∈ conjClosure V H, ∀ q ∈ pCoreOf 2 H, u * q * u⁻¹ * q⁻¹ ∈ V₁ := by
  obtain ⟨-, hcomm⟩ := h.V_le_pCoreOf_and_commutator_le
  have hQN := le_normalizer_pCoreOf 2 H
  have hHC : H ≤ Subgroup.normalizer (centralizerMod V₁ ⊤ (pCoreOf 2 H) : Set G) :=
    le_normalizer_centralizerMod h.H_normalizes_V₁ (fun x _ => by
      rw [Subgroup.mem_normalizer_iff]; intro y; simp) hQN
  have : conjClosure V H ≤ centralizerMod V₁ ⊤ (pCoreOf 2 H) := by
    refine conjClosure_le fun x hx v hv => ?_
    have hvC : v ∈ centralizerMod V₁ ⊤ (pCoreOf 2 H) :=
      ⟨Subgroup.mem_top _, h.T_normalizes_V₁ (h.V_le_T hv), fun q hq => hcomm v hv q hq⟩
    exact (Subgroup.mem_normalizer_iff.mp (hHC hx) v).mp hvC
  exact fun u hu q hq => (this hu).2.2 q hq

theorem sq_mem_conjClosure (h : HypF81 T V L V₁ H) : ∀ u ∈ conjClosure V H, u ^ 2 ∈ V₁ := by
  have hUQ := h.conjClosure_V_le_pCoreOf
  have hcomm := h.commutator_conjClosure_le
  intro u hu
  have hu' : u ∈ Subgroup.closure {x | ∃ k ∈ H, ∃ z ∈ V, k * z * k⁻¹ = x} := hu
  clear hu
  induction hu' using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, z, hz, rfl⟩ := hx
    have e : (k * z * k⁻¹) ^ 2 = k * z ^ 2 * k⁻¹ := conj_pow
    rw [e, isElemAbelian_pow_eq_one h.elemAbelian hz]
    simp
  | one => simp
  | mul x y hx hy ihx ihy =>
    have hxU : x ∈ conjClosure V H := hx
    have hyU : y ∈ conjClosure V H := hy
    have hc : y * x * y⁻¹ * x⁻¹ ∈ V₁ := hcomm y hyU x (hUQ hxU)
    have hxN : x ∈ Subgroup.normalizer (V₁ : Set G) :=
      h.H_normalizes_V₁ (pCoreOf_le 2 H (hUQ hxU))
    have h1 : x * (y * x * y⁻¹ * x⁻¹) * x⁻¹ ∈ V₁ := (Subgroup.mem_normalizer_iff.mp hxN _).mp hc
    have e : (x * y) ^ 2 = (x * (y * x * y⁻¹ * x⁻¹) * x⁻¹) * x ^ 2 * y ^ 2 := by
      rw [pow_two]; group
    rw [e]
    exact V₁.mul_mem (V₁.mul_mem h1 ihx) ihy
  | inv x hx ih =>
    rw [inv_pow]
    exact V₁.inv_mem ih

theorem F82_1 (h : HypF81 T V L V₁ H) :
    conjClosure V H ≤ pCoreOf 2 H ∧
      (∀ u ∈ conjClosure V H, ∀ q ∈ pCoreOf 2 H, u * q * u⁻¹ * q⁻¹ ∈ V₁) ∧
      ∀ u ∈ conjClosure V H, u ^ 2 ∈ V₁ :=
  ⟨h.conjClosure_V_le_pCoreOf, h.commutator_conjClosure_le, h.sq_mem_conjClosure⟩

theorem isPGroup_conjClosure (h : HypF81 T V L V₁ H) : IsPGroup 2 (conjClosure V H) :=
  (pCoreOf_isPGroup 2 H).to_le h.conjClosure_V_le_pCoreOf

theorem F82_2 (h : HypF81 T V L V₁ H) :
    (frattini (conjClosure V H)).map (conjClosure V H).subtype ≤ V₁ :=
  frattini_map_le_of_forall h.isPGroup_conjClosure
    (fun x hx y hy => h.commutator_conjClosure_le x hx y (h.conjClosure_V_le_pCoreOf hy))
    h.sq_mem_conjClosure

theorem F82_3 (h : HypF81 T V L V₁ H) : pCoreOf 2 H = centralizerMod V₁ H (conjClosure V H) := by
  apply le_antisymm
  · intro q hq
    refine ⟨pCoreOf_le 2 H hq, h.H_normalizes_V₁ (pCoreOf_le 2 H hq), fun u hu => ?_⟩
    have := V₁.inv_mem (h.commutator_conjClosure_le u hu q hq)
    have e : (u * q * u⁻¹ * q⁻¹)⁻¹ = q * u * q⁻¹ * u⁻¹ := by group
    rwa [e] at this
  · have hHC : H ≤ Subgroup.normalizer (centralizerMod V₁ H (conjClosure V H) : Set G) :=
      le_normalizer_centralizerMod h.H_normalizes_V₁ Subgroup.le_normalizer
        (le_normalizer_conjClosure V H)
    have hle : centralizerMod V₁ H (conjClosure V H) ≤ coreIn (centralizerMod V₁ H V) H :=
      le_coreIn (centralizerMod_le_left _ _ _) hHC (centralizerMod_anti_right H (le_conjClosure V H))
    exact hle.trans h.ker_le

theorem F82_1_reduced (h : HypF81 T V L V₁ H) {D : Subgroup G} (hDH : D ≤ H)
    (hHD : H ≤ Subgroup.normalizer (D : Set G))
    (hD : ∀ d ∈ D, ∃ k : ℕ, d ^ 2 ^ k ∈ centralizerMod V₁ H (conjClosure V H)) :
    D ≤ centralizerMod V₁ H (conjClosure V H) := by
  have htop : ∀ K : Subgroup G, K ≤ Subgroup.normalizer ((⊤ : Subgroup G) : Set G) :=
    fun K x _ => by rw [Subgroup.mem_normalizer_iff]; intro y; simp
  have hHC : H ≤ Subgroup.normalizer (centralizerMod V₁ H (conjClosure V H) : Set G) :=
    le_normalizer_centralizerMod h.H_normalizes_V₁ Subgroup.le_normalizer
      (le_normalizer_conjClosure V H)
  have hXH : L₁Of L V₁ ⊔ T ≤ H := h.L₁T_le_H
  have hXV : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (V : Set G) := h.L₁T_normalizes_V
  have hXV₁ : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer (V₁ : Set G) := hXH.trans h.H_normalizes_V₁
  have hW : V ≤ conjClosure (V ⊓ centralizerMod V₁ ⊤ T) (L₁Of L V₁ ⊔ T) ⊔ V₁ := by
    have hWV : conjClosure (V ⊓ centralizerMod V₁ ⊤ T) (L₁Of L V₁ ⊔ T) ⊔ V₁ ≤ V :=
      sup_le (conjClosure_le fun x hx z hz =>
        (Subgroup.mem_normalizer_iff.mp (hXV hx) z).mp hz.1) h.V₁_le_V
    have hXW : L₁Of L V₁ ⊔ T ≤ Subgroup.normalizer
        ((conjClosure (V ⊓ centralizerMod V₁ ⊤ T) (L₁Of L V₁ ⊔ T) ⊔ V₁ : Subgroup G) : Set G) :=
      (le_inf (le_normalizer_conjClosure _ _) hXV₁).trans
        (Subgroup.inf_normalizer_le_normalizer_sup _ _)
    by_cases hEq : V₁ = V
    · exact hEq ▸ le_sup_right
    · have hlt := lt_of_le_of_ne h.V₁_le_V hEq
      obtain ⟨z, hzV, hzV₁, hz⟩ := exists_fixed_mod h.sylow.2.1 h.V_le_T hlt h.T_normalizes_V
        h.T_normalizes_V₁
      have hzZ : z ∈ V ⊓ centralizerMod V₁ ⊤ T :=
        ⟨hzV, Subgroup.mem_top _, h.T_normalizes_V₁ (h.V_le_T hzV), fun t ht => by
          have := V₁.inv_mem (hz t ht)
          have e : (t * z * t⁻¹ * z⁻¹)⁻¹ = z * t * z⁻¹ * t⁻¹ := by group
          rwa [e] at this⟩
      rcases h.irred _ le_sup_right hWV hXW with hEq' | hEq'
      · exact absurd (hEq' ▸ Subgroup.mem_sup_left (le_conjClosure _ _ hzZ)) hzV₁
      · exact hEq'.symm.le
  have hDsyl : IsSylowTwoOf (T ⊓ D) D :=
    isSylowTwoOf_inf_normal h.sylow_H hDH (h.T_le_H.trans hHD)
  have hDle := isSylowTwoOf_le_sup_of_two_power hDsyl (hDH.trans hHC) hD
  have hZU : V ⊓ centralizerMod V₁ ⊤ T ≤ conjClosure V H := inf_le_left.trans (le_conjClosure V H)
  have hC'C : centralizerMod V₁ H (conjClosure V H) ≤ centralizerMod V₁ ⊤ (V ⊓ centralizerMod V₁ ⊤ T) :=
    (centralizerMod_anti_right H hZU).trans (centralizerMod_mono_left _ le_top)
  have hC'T : T ⊓ D ≤ centralizerMod V₁ ⊤ (V ⊓ centralizerMod V₁ ⊤ T) := by
    rintro t ⟨ht, -⟩
    refine ⟨Subgroup.mem_top _, h.T_normalizes_V₁ ht, fun z hz => ?_⟩
    have := V₁.inv_mem (hz.2.2.2 t ht)
    have e : (z * t * z⁻¹ * t⁻¹)⁻¹ = t * z * t⁻¹ * z⁻¹ := by group
    rwa [e] at this
  have hDC' : D ≤ centralizerMod V₁ ⊤ (V ⊓ centralizerMod V₁ ⊤ T) :=
    hDle.trans (sup_le hC'C hC'T)
  have hSgen : conjClosure (V ⊓ centralizerMod V₁ ⊤ T) (L₁Of L V₁ ⊔ T) ≤
      centralizerMod V₁ ⊤ D := by
    refine conjClosure_le fun x hx z hz => ?_
    refine ⟨Subgroup.mem_top _, ?_, fun d hd => ?_⟩
    · exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hXV₁ hx) hz.2.2.1)
        (Subgroup.inv_mem _ (hXV₁ hx))
    · have hd' : x⁻¹ * d * x⁻¹⁻¹ ∈ D :=
        (Subgroup.mem_normalizer_iff.mp (hHD (H.inv_mem (hXH hx))) d).mp hd
      have h1 := (hDC' hd').2.2 z hz
      have h2 : x * ((x⁻¹ * d * x⁻¹⁻¹) * z * (x⁻¹ * d * x⁻¹⁻¹)⁻¹ * z⁻¹) * x⁻¹ ∈ V₁ :=
        (Subgroup.mem_normalizer_iff.mp (hXV₁ hx) _).mp h1
      have h3 := V₁.inv_mem h2
      have e : (x * ((x⁻¹ * d * x⁻¹⁻¹) * z * (x⁻¹ * d * x⁻¹⁻¹)⁻¹ * z⁻¹) * x⁻¹)⁻¹ =
          (x * z * x⁻¹) * d * (x * z * x⁻¹)⁻¹ * d⁻¹ := by group
      rwa [e] at h3
  have hV₁S : V₁ ≤ centralizerMod V₁ ⊤ D := by
    intro v hv
    refine ⟨Subgroup.mem_top _, Subgroup.le_normalizer hv, fun d hd => ?_⟩
    have h1 : d * v⁻¹ * d⁻¹ ∈ V₁ :=
      (Subgroup.mem_normalizer_iff.mp (h.H_normalizes_V₁ (hDH hd)) v⁻¹).mp (V₁.inv_mem hv)
    have e : v * d * v⁻¹ * d⁻¹ = v * (d * v⁻¹ * d⁻¹) := by group
    rw [e]; exact V₁.mul_mem hv h1
  have hVS : V ≤ centralizerMod V₁ ⊤ D := hW.trans (sup_le hSgen hV₁S)
  have hHS : H ≤ Subgroup.normalizer (centralizerMod V₁ ⊤ D : Set G) :=
    le_normalizer_centralizerMod h.H_normalizes_V₁ (htop H) hHD
  have hUS : conjClosure V H ≤ centralizerMod V₁ ⊤ D :=
    conjClosure_le fun x hx v hv => (Subgroup.mem_normalizer_iff.mp (hHS hx) v).mp (hVS hv)
  intro d hd
  refine ⟨hDH hd, h.H_normalizes_V₁ (hDH hd), fun u hu => ?_⟩
  have := V₁.inv_mem ((hUS hu).2.2 d hd)
  have e : (u * d * u⁻¹ * d⁻¹)⁻¹ = d * u * d⁻¹ * u⁻¹ := by group
  rwa [e] at this

end F82

section F83

variable [Finite G]

theorem charTwo_LT (h : HypF81 T V L V₁ H) : CharTwo (L ⊔ T) :=
  charTwo_sup_of_normalizes h.sylow.2.1 h.normalizes_L h.charTwo_L

theorem pCoreOf_LT_eq (h : HypF81 T V L V₁ H) :
    pCoreOf 2 (L ⊔ T) = pCoreOf 2 ((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := by
  have h1 : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (V : Set G) := by
    refine h.reduced.2.2.2 (pCoreOf 2 (L ⊔ T)) (pCoreOf_le 2 _) (le_normalizer_pCoreOf 2 _) ?_
    intro d hd
    obtain ⟨k, hk⟩ := pCoreOf_isPGroup 2 (L ⊔ T) ⟨d, hd⟩
    have : d ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
    exact ⟨k, by rw [this]; exact Subgroup.one_mem _⟩
  apply le_antisymm
  · exact le_pCoreOf_of_le_normalizer 2 (le_inf (pCoreOf_le 2 _) h1)
      (inf_le_left.trans (le_normalizer_pCoreOf 2 _)) (pCoreOf_isPGroup 2 _)
  · exact pCoreOf_mono_of_le_normalizer inf_le_left
      (le_normalizer_inf Subgroup.le_normalizer
        (h.reduced.2.1.trans (normalizer_le_normalizer_centralizer V)))

theorem amalgamHypV (h : HypF81 T V L V₁ H) : AmalgamHypV ((L ⊔ T) ⊔ H) (L ⊔ T) H T V :=
  { gen := rfl
    charTwo := h.charTwo_LT
    sylow₁ := h.sylow_LT
    sylow₂ := h.sylow_H
    o2_trivial := h.o2_trivial
    reduced := h.reduced
    cT := h.cT.trans h.pCoreOf_LT_eq }

theorem LT_inf_H (h : HypF81 T V L V₁ H) : (L ⊔ T) ⊓ H = L₁Of L V₁ ⊔ T := by
  apply le_antisymm
  · rintro x ⟨hxLT, hxH⟩
    have hmul : ((L ⊔ T : Subgroup G) : Set G) = (L : Set G) * T :=
      Subgroup.coe_mul_of_right_le_normalizer_left L T h.normalizes_L
    obtain ⟨l, hl, t, ht, rfl⟩ : x ∈ (L : Set G) * T := by rw [← hmul]; exact hxLT
    have hlN : l ∈ Subgroup.normalizer (V₁ : Set G) := by
      have := Subgroup.mul_mem _ (h.H_normalizes_V₁ hxH)
        (Subgroup.inv_mem _ (h.T_normalizes_V₁ ht))
      simpa using this
    have hsyl : IsSylowTwoOf (T ⊓ L) (L ⊓ Subgroup.normalizer (V₁ : Set G)) :=
      isSylowTwoOf_mono_right (isSylowTwoOf_inf_normal h.sylow (le_top : L ≤ ⊤) h.normalizes_L)
        (le_inf inf_le_right (inf_le_left.trans h.T_normalizes_V₁)) inf_le_left
    have hl' := le_oTwoRes_sup_of_isSylowTwoOf hsyl ⟨hl, hlN⟩
    have hle : oTwoRes (L ⊓ Subgroup.normalizer (V₁ : Set G)) ⊔ (T ⊓ L) ≤ L₁Of L V₁ ⊔ T :=
      sup_le_sup le_rfl inf_le_left
    exact Subgroup.mul_mem _ (hle hl') (le_sup_right (a := L₁Of L V₁) ht)
  · exact le_inf (L₁Of_sup_le L V₁ T) h.L₁T_le_H

end F83

end HypF81

end CFSG.Quasithin

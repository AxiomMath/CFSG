module

public import CFSG.Quasithin.H13.L32A753e
public import CFSG.Quasithin.EmptyFaithful.S152He9C
public import CFSG.Quasithin.Background.SmithB42U33

public section

namespace CFSG.Quasithin.H13.L32A.M753

open CFSG.Open CFSG.Quasithin

variable {V : Type} [CommGroup V] [Finite V]

@[expose] def IrrBetween (K : Subgroup (MulAut V)) (C J : Subgroup V) : Prop :=
  ∀ J' : Subgroup V, C ≤ J' → J' ≤ J → (∀ k ∈ K, ∀ v ∈ J', k v ∈ J') → J' = C ∨ J' = J

omit [Finite V] in
theorem le_stabSub_fixV {X K : Subgroup (MulAut V)}
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V))) : X ≤ stabSub (fixV K) :=
  CFSG.Quasithin.FixVLat.le_stabSub_fixV_of_le_normalizer hXN

omit [Finite V] in
theorem perfect_of_b42 {K : Subgroup (MulAut V)} (hP : B42TypeU33 ↥K) : ⁅K, K⁆ = K := by
  have hs : IsSimpleGroup ↥K := isSimpleGroup_of_b42 hP
  have hZ := hP.1
  refine He9.W5.perfect_of_simple hs ?_
  by_contra hab
  push Not at hab
  have hc : Subgroup.center ↥K = ⊤ := by
    rw [eq_top_iff]
    intro z _
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (hab y y.2 z z.2)
  have hbot : (⊤ : Subgroup ↥K) = ⊥ := hc ▸ hZ
  have h6048 : Nat.card ↥K = 6048 := B42U33.card_of_b42TypeU33 hP
  have := Subgroup.card_top (G := ↥K)
  rw [hbot, Subgroup.card_bot, h6048] at this
  norm_num at this

omit [Finite V] in
theorem trivial_of_le {K : Subgroup (MulAut V)} (hP : B42TypeU33 ↥K) {J : Subgroup V}
    (htriv : ∀ k ∈ K, ∀ j ∈ J, k j * j⁻¹ ∈ fixV K) : J ≤ fixV K := by
  intro j hj
  let φ : ↥K →* V :=
    { toFun := fun k => (k : MulAut V) j * j⁻¹
      map_one' := by simp
      map_mul' := fun a b => by
        have hb := htriv b b.2 j hj
        have h1 : (a : MulAut V) ((b : MulAut V) j * j⁻¹) = (b : MulAut V) j * j⁻¹ :=
          hb a a.2
        have h2 : (a : MulAut V) ((b : MulAut V) j) =
            (a : MulAut V) ((b : MulAut V) j * j⁻¹) * (a : MulAut V) j := by
          rw [map_mul, map_inv, inv_mul_cancel_right]
        change ((a : MulAut V) * (b : MulAut V)) j * j⁻¹ = _
        rw [MulAut.mul_apply, h2, h1]
        rw [mul_comm ((b : MulAut V) j * j⁻¹) ((a : MulAut V) j)]
        simp only [mul_assoc]
        rw [mul_left_comm j⁻¹ ((b : MulAut V) j) j⁻¹] }
  have hker : φ.ker = ⊤ := by
    have hcomm : ∀ x y : ↥K, φ (x * y * x⁻¹ * y⁻¹) = 1 := by
      intro x y
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, mul_comm (φ x) (φ y)]
      group
    have hle : ⁅(⊤ : Subgroup ↥K), ⊤⁆ ≤ φ.ker := by
      rw [Subgroup.commutator_le]
      intro x _ y _
      exact hcomm x y
    have htop : ⁅(⊤ : Subgroup ↥K), (⊤ : Subgroup ↥K)⁆ = ⊤ := by
      apply Subgroup.map_injective K.subtype_injective
      rw [Subgroup.map_commutator, ← MonoidHom.range_eq_map, Subgroup.range_subtype,
        perfect_of_b42 hP]
    exact le_antisymm le_top (htop ▸ hle)
  intro k hk
  have h1 : φ ⟨k, hk⟩ = 1 := (MonoidHom.mem_ker).1 (hker ▸ Subgroup.mem_top _)
  have h2 : (k : MulAut V) j * j⁻¹ = 1 := h1
  rw [mul_inv_eq_one] at h2
  exact h2

section Natural

variable {W : Type} [CommGroup W] [Finite W]

theorem card_le_index_of_equiv
    (e : W ≃* ModQ) {X' : Subgroup (MulAut W)}
    (hX : ∀ x ∈ X', MulAut.congr e x ∈ (g2QAct (ZMod 2)).range) {B : Subgroup (MulAut W)}
    (hBX : B ≤ X') (hB1 : B ≠ ⊥) (hBe : IsElemAbelian2 B) :
    Nat.card B ≤ (fixV B).index ∧
      ((fixV B).index = Nat.card B → Nat.card B = 8 ∧ Nat.card (fixV B) = 8) := by
  have hφinj : Function.Injective (MulAut.congr e).toMonoidHom := (MulAut.congr e).injective
  set B' := B.map (MulAut.congr e).toMonoidHom with hB'
  have hle : B' ≤ (g2QAct (ZMod 2)).range := by
    rintro _ ⟨b, hb, rfl⟩
    exact hX b (hBX hb)
  have hne : B' ≠ ⊥ := fun h =>
    hB1 ((Subgroup.map_eq_bot_iff_of_injective _ hφinj).1 h)
  have hea : IsElemAbelian2 B' := by
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hBe.1 a ha b hb]
    · rintro _ ⟨b, hb, rfl⟩
      rw [← map_pow, hBe.2 b hb, map_one]
  have hcardB : Nat.card B' = Nat.card B := Subgroup.card_map_of_injective hφinj
  have hfix : Nat.card (fixV B') = Nat.card (fixV B) := by
    rw [hB', B1Red.fixV_map_congr', Subgroup.card_map_of_injective (f := e.toMonoidHom) e.injective]
  have hW : Nat.card W = Nat.card ModQ := Nat.card_congr e.toEquiv
  have hidx := (fixV B).card_mul_index
  have hpos : 0 < Nat.card (fixV B) := Nat.card_pos
  have key : Nat.card ModQ ≤ Nat.card B' * Nat.card (fixV B') →
      Nat.card B' = 8 ∧ Nat.card (fixV B') = 8 :=
    B42U33.offender_exact hle hne hea
  constructor
  · by_contra hlt
    push Not at hlt
    have h1 : Nat.card ModQ ≤ Nat.card B' * Nat.card (fixV B') := by
      rw [hcardB, hfix, ← hW, ← hidx, mul_comm]
      exact Nat.mul_le_mul_right _ hlt.le
    obtain ⟨h8, hf8⟩ := key h1
    rw [hcardB] at h8
    rw [hfix] at hf8
    have h64 : Nat.card W = 64 := by rw [hW, card_ModQ]
    rw [h64, hf8] at hidx
    rw [h8] at hlt
    omega
  · intro heq
    have h1 : Nat.card ModQ ≤ Nat.card B' * Nat.card (fixV B') := by
      rw [hcardB, hfix, ← hW, ← hidx, heq, mul_comm]
    obtain ⟨h8, hf8⟩ := key h1
    exact ⟨hcardB ▸ h8, hfix ▸ hf8⟩

end Natural

section Sections

variable {X K : Subgroup (MulAut V)} {J C : Subgroup V}

omit [Finite V] in
theorem secHom_mono (hKX : K ≤ X) (hXJ : X ≤ stabSub J) (hXC : X ≤ stabSub C) (k : ↥K) :
    secHom (hKX.trans hXJ) (hKX.trans hXC) k = secHom hXJ hXC ⟨k, hKX k.2⟩ := rfl

omit [Finite V] in
theorem secHom_injective (hKJ : K ≤ stabSub J) (hKC : K ≤ stabSub C) (hs : IsSimpleGroup ↥K)
    (hnt : ∃ k ∈ K, ∃ j ∈ J, k j * j⁻¹ ∉ C) : Function.Injective (secHom hKJ hKC) := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (secHom hKJ hKC).ker with hb | ht
  · exact (MonoidHom.ker_eq_bot_iff _).1 hb
  · exfalso
    obtain ⟨k, hk, j, hj, hkj⟩ := hnt
    have h1 : (⟨k, hk⟩ : ↥K) ∈ (secHom hKJ hKC).ker := ht ▸ trivial
    exact hkj ((secHom_eq_one_iff hKJ hKC _).1 h1 j hj)

omit [Finite V] in
theorem secHom_injective_X (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hCK : X ⊓ Subgroup.centralizer (K : Set (MulAut V)) ≤ K) (hXJ : X ≤ stabSub J)
    (hXC : X ≤ stabSub C) (hs : IsSimpleGroup ↥K) (hnt : ∃ k ∈ K, ∃ j ∈ J, k j * j⁻¹ ∉ C) :
    Function.Injective (secHom hXJ hXC) := by
  have hK := secHom_injective (hKX.trans hXJ) (hKX.trans hXC) hs hnt
  rw [injective_iff_map_eq_one]
  intro x hx
  have hcomm : ∀ k ∈ K, (x : MulAut V) * k = k * x := by
    intro k hk
    have hc : (x : MulAut V) * k * (x : MulAut V)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hXN x.2) k).mp hk
    have h1 : secHom (hKX.trans hXJ) (hKX.trans hXC) ⟨_, hc⟩ =
        secHom (hKX.trans hXJ) (hKX.trans hXC) ⟨k, hk⟩ := by
      rw [secHom_mono hKX hXJ hXC, secHom_mono hKX hXJ hXC]
      have e1 : (⟨(x : MulAut V) * k * (x : MulAut V)⁻¹, hKX hc⟩ : ↥X) =
          x * ⟨k, hKX hk⟩ * x⁻¹ := rfl
      rw [e1, map_mul, map_mul, map_inv, hx, one_mul, inv_one, mul_one]
    have h2 := congrArg Subtype.val (hK h1)
    change (x : MulAut V) * k * (x : MulAut V)⁻¹ = k at h2
    calc (x : MulAut V) * k = (x : MulAut V) * k * (x : MulAut V)⁻¹ * x := by group
      _ = k * x := by rw [h2]
  have hxK : (x : MulAut V) ∈ K := hCK ⟨x.2, Subgroup.mem_centralizer_iff.2 fun k hk =>
    (hcomm k hk).symm⟩
  have h3 : secHom (hKX.trans hXJ) (hKX.trans hXC) ⟨x, hxK⟩ = 1 := by
    rw [secHom_mono hKX hXJ hXC]
    exact hx
  have h4 := congrArg Subtype.val (hK (h3.trans (map_one _).symm))
  exact Subtype.ext h4

omit [Finite V] in
theorem card_autSec_eq (hKX : K ≤ X) (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hCK : X ⊓ Subgroup.centralizer (K : Set (MulAut V)) ≤ K) (hXJ : X ≤ stabSub J)
    (hXC : X ≤ stabSub C) (hs : IsSimpleGroup ↥K) (hnt : ∃ k ∈ K, ∃ j ∈ J, k j * j⁻¹ ∉ C)
    {B : Subgroup (MulAut V)} (hBX : B ≤ X) : Nat.card (autSec B J C) = Nat.card B := by
  have hinj := secHom_injective_X hKX hXN hCK hXJ hXC hs hnt
  have hBi : Function.Injective (secHom (hBX.trans hXJ) (hBX.trans hXC)) := by
    intro a b hab
    have : secHom hXJ hXC ⟨a, hBX a.2⟩ = secHom hXJ hXC ⟨b, hBX b.2⟩ := hab
    exact Subtype.ext (congrArg (fun y : ↥X => (y : MulAut V)) (hinj this))
  rw [← range_secHom (hBX.trans hXJ) (hBX.trans hXC)]
  exact Nat.card_range_of_injective hBi

omit [Finite V] in
theorem exists_equiv_sec
    (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V))) (hXJ : X ≤ stabSub J)
    (hXC : X ≤ stabSub C) (hnat : G2NaturalDerived (autSec K J C) ⊤ ⊥ 1) :
    ∃ e : Sec J C ≃* ModQ,
      (autSec K J C).map (MulAut.congr e).toMonoidHom = (g2Derived (ZMod 2)).map (g2QAct (ZMod 2)) ∧
        ∀ x ∈ autSec X J C, MulAut.congr e x ∈ (g2QAct (ZMod 2)).range := by
  obtain ⟨e, hLe⟩ := B42U33.exists_equiv_of_g2NaturalDerived hnat
  refine ⟨e, hLe, fun x hx => ?_⟩
  set φ := (MulAut.congr e).toMonoidHom with hφ
  have hφinj : Function.Injective φ := (MulAut.congr e).injective
  rw [← range_secHom hXJ hXC] at hx
  obtain ⟨ξ, rfl⟩ := hx
  refine normalizer_two_Q _ fun h => ?_
  obtain ⟨h', rfl⟩ := (MulAut.congr e).surjective h
  rw [← hLe, ← map_inv, ← map_mul, ← map_mul]
  change φ h' ∈ (autSec K J C).map φ ↔ φ (_ * h' * _) ∈ (autSec K J C).map φ
  rw [Subgroup.mem_map_iff_mem hφinj, Subgroup.mem_map_iff_mem hφinj,
    ← range_secHom (hKX.trans hXJ) (hKX.trans hXC)]
  constructor
  · rintro ⟨κ, rfl⟩
    have hc : (ξ : MulAut V) * κ * (ξ : MulAut V)⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hXN ξ.2) κ).mp κ.2
    refine ⟨⟨_, hc⟩, ?_⟩
    rw [secHom_mono hKX hXJ hXC, secHom_mono hKX hXJ hXC]
    have e1 : (⟨(ξ : MulAut V) * κ * (ξ : MulAut V)⁻¹, hKX hc⟩ : ↥X) =
        ξ * ⟨κ, hKX κ.2⟩ * ξ⁻¹ := rfl
    rw [e1, map_mul, map_mul, map_inv]
  · rintro ⟨κ, hκ⟩
    have hc : (ξ : MulAut V)⁻¹ * κ * (ξ : MulAut V) ∈ K := by
      have := (Subgroup.mem_normalizer_iff.mp (hXN (X.inv_mem ξ.2)) κ).mp κ.2
      simpa using this
    refine ⟨⟨_, hc⟩, ?_⟩
    rw [secHom_mono hKX hXJ hXC]
    have e1 : (⟨(ξ : MulAut V)⁻¹ * κ * (ξ : MulAut V), hKX hc⟩ : ↥X) =
        ξ⁻¹ * ⟨κ, hKX κ.2⟩ * ξ := by
      apply Subtype.ext
      simp
    rw [e1, map_mul, map_mul, map_inv, ← secHom_mono hKX hXJ hXC, hκ]
    group

theorem sec_offender
    (hKX : K ≤ X)
    (hXN : X ≤ Subgroup.normalizer (K : Set (MulAut V)))
    (hCK : X ⊓ Subgroup.centralizer (K : Set (MulAut V)) ≤ K) (hXJ : X ≤ stabSub J)
    (hXC : X ≤ stabSub C) (hP : B42TypeU33 ↥K) (hnt : ∃ k ∈ K, ∃ j ∈ J, k j * j⁻¹ ∉ C)
    (hnat : G2NaturalDerived (autSec K J C) ⊤ ⊥ 1) {B : Subgroup (MulAut V)} (hBX : B ≤ X)
    (hB1 : B ≠ ⊥) (hBe : IsElemAbelian2 B) :
    Nat.card B ≤ (fixV (autSec B J C)).index ∧
      ((fixV (autSec B J C)).index = Nat.card B → Nat.card B = 8 ∧ ¬ B ≤ K) := by
  have hs : IsSimpleGroup ↥K := isSimpleGroup_of_b42 hP
  obtain ⟨e, -, he⟩ := exists_equiv_sec hKX hXN hXJ hXC hnat
  have hcard := card_autSec_eq hKX hXN hCK hXJ hXC hs hnt hBX
  have hB'X : autSec B J C ≤ autSec X J C := autSec_mono hBX J C
  have hB'1 : autSec B J C ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hcard
    exact hB1 (Subgroup.eq_bot_of_card_eq B hcard.symm)
  have hB'e : IsElemAbelian2 (autSec B J C) := by
    rw [← range_secHom (hBX.trans hXJ) (hBX.trans hXC)]
    refine ⟨?_, ?_⟩
    · rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (hBe.1 _ a.2 _ b.2)
    · rintro _ ⟨b, rfl⟩
      rw [← map_pow]
      have : b ^ 2 = 1 := Subtype.ext (hBe.2 _ b.2)
      rw [this, map_one]
  obtain ⟨h1, h2⟩ := card_le_index_of_equiv e he hB'X hB'1 hB'e
  rw [hcard] at h1 h2
  refine ⟨h1, fun heq => ?_⟩
  obtain ⟨h8, -⟩ := h2 heq
  refine ⟨h8, fun hBK => ?_⟩
  have hle : autSec B J C ≤ autSec K J C := autSec_mono hBK J C
  have hrk := B42U33.rank_le_two (b42TypeU33_autSec (hKX.trans hXJ) (hKX.trans hXC) hP hnt) hle
    hB'e (k := 3) (by rw [hcard, h8]; norm_num)
  omega

end Sections

end CFSG.Quasithin.H13.L32A.M753

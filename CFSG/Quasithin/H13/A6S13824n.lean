module

public import CFSG.Quasithin.H13.A6S13824c
public import CFSG.Quasithin.H13.A6S13826e

public section

namespace CFSG.Quasithin.H13.A6

open Equiv CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.Quasithin CFSG.LieType.BorelTits
open CFSG.Quasithin.F7
open scoped IsMulCommutative

namespace Setting4

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G} {S : Setting4 G T L V}

namespace SecHyp

variable {H K X W : Subgroup G} (hs : S.SecHyp H K X W) [IsMulCommutative ↥X]
include hs

theorem irrK7
    (hirr : ∀ W' : Subgroup G, W ≤ W' → W' ≤ X → H ≤ Subgroup.normalizer (W' : Set G) →
      W' = W ∨ W' = X)
    {α : ↥K →* alternatingGroup (Fin 7)} (hαs : Function.Surjective α)
    (hαk : ∀ k : ↥K, α k = 1 ↔ (k : G) ∈ pCoreOf 2 H)
    (hcard : Nat.card (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) ≤ 2 ^ 6) :
    XMod.IsIrrSec ↥(autSec (autOn K X) ⊤ (W.subgroupOf X))
      (⊥ : Subgroup (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))) ⊤ := by
  classical
  have : IsSimpleGroup (alternatingGroup (Fin 7)) :=
    alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; norm_num)
  set actK := hs.act.comp (Subgroup.inclusion hs.hKH) with hactK
  have hactK1 : ∀ k : ↥K, actK k = 1 ↔ α k = 1 := fun k => by
    rw [hαk]
    exact hs.act_eq_one_iff _
  refine ⟨bot_lt_iff_ne_bot.2 hs.top_ne_bot, fun J hJ _ _ => ?_⟩
  have hJinv : ∀ k : ↥K, ∀ y ∈ J, actK k y ∈ J := fun k y hy =>
    hJ ⟨_, (hs.mem_autSec_iff hs.hKH).2 ⟨_, k.2, rfl⟩⟩ y hy
  by_contra hne
  push Not at hne
  obtain ⟨M, ⟨hM1, hMinv, hMJ⟩, hmin⟩ := WellFounded.has_min
    (wellFounded_lt (α := Subgroup (Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))))
    {M | M ≠ ⊥ ∧ (∀ k : ↥K, ∀ y ∈ M, actK k y ∈ M) ∧ M ≤ J} ⟨J, hne.1, hJinv, le_rfl⟩
  have hMtop : M ≠ ⊤ := fun h => hne.2 (eq_top_iff.2 (h ▸ hMJ))
  have hfix := hs.fixV_eq_bot hirr
  obtain ⟨k₀, m₀, hm₀, hk₀⟩ : ∃ k₀ : ↥K, ∃ m₀ ∈ M, actK k₀ m₀ ≠ m₀ := by
    by_contra hcon
    push Not at hcon
    apply hM1
    rw [eq_bot_iff]
    intro y hy
    rw [← hfix, mem_fixV]
    intro ψ hψ
    obtain ⟨f, hf, rfl⟩ := (hs.mem_autSec_iff hs.hKH).1 hψ
    exact hcon ⟨f, hf⟩ y hy
  have hm : A7F.a7 * A7F.b7 ∈ alternatingGroup (Fin 7) :=
    Subgroup.mul_mem _ A7F.a7_mem A7F.b7_mem
  obtain ⟨k₅, hk₅⟩ := hαs ⟨A7F.a7 * A7F.b7, hm⟩
  have hg5 : actK k₅ ^ 5 = 1 := by
    rw [← map_pow, hactK1, map_pow, hk₅]
    exact Subtype.ext A7F.ab7_pow_five
  have hgM : ∃ m ∈ M, actK k₅ m ≠ m := by
    by_contra hcon
    push Not at hcon
    let N : Subgroup ↥K :=
      { carrier := {k | ∀ m ∈ M, actK k m = m}
        one_mem' := fun m _ => by simp
        mul_mem' := fun {a b} ha hb m hm => by
          rw [map_mul, MulAut.mul_apply, hb m hm, ha m hm]
        inv_mem' := fun {a} ha m hm => by
          rw [map_inv]
          calc (actK a)⁻¹ m = (actK a)⁻¹ (actK a m) := by rw [ha m hm]
            _ = m := MulAut.inv_apply_self _ _ _ }
    have hNn : N.Normal := ⟨fun n hn k m hm => by
      have h1 : (actK k)⁻¹ m ∈ M := by
        rw [← map_inv]
        exact hMinv k⁻¹ m hm
      simp only [map_mul, map_inv, MulAut.mul_apply]
      rw [hn _ h1, MulAut.apply_inv_self]⟩
    have hαN : N.map α = ⊤ := by
      have hn' : (N.map α).Normal := hNn.map α hαs
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map α) with h | h
      · exfalso
        have h1 : α k₅ ∈ N.map α := ⟨k₅, fun m hm => hcon m hm, rfl⟩
        rw [h, Subgroup.mem_bot, hk₅] at h1
        exact A7F.ab7_ne_one (congrArg Subtype.val h1)
      · exact h
    obtain ⟨n, hn, hnk⟩ : α k₀ ∈ N.map α := hαN ▸ Subgroup.mem_top _
    have h1 : actK (n⁻¹ * k₀) = 1 :=
      (hactK1 _).2 (by rw [map_mul, map_inv, hnk, inv_mul_cancel])
    rw [map_mul, map_inv, inv_mul_eq_one] at h1
    exact hk₀ (by rw [← h1]; exact hn m₀ hm₀)
  have hgMM : ∀ m ∈ M, actK k₅ m ∈ M := fun m hm => hMinv k₅ m hm
  let gM : ↥M →* ↥M :=
    ((actK k₅).toMonoidHom.comp M.subtype).codRestrict M fun m => hgMM m m.2
  have hgMi : Function.Injective gM := fun a b h =>
    Subtype.ext ((actK k₅).injective (congrArg Subtype.val h))
  let g' : MulAut ↥M := MulEquiv.ofBijective gM ⟨hgMi, Finite.injective_iff_surjective.1 hgMi⟩
  have hpow : ∀ (n : ℕ) (m : ↥M), (((g' ^ n) m : ↥M) : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) =
      (actK k₅ ^ n) (m : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) := by
    intro n
    induction n with
    | zero => intro m; rfl
    | succ n ih =>
      intro m
      rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
      rfl
  have hg'5 : g' ^ 5 = 1 := MulEquiv.ext fun m => Subtype.ext (by rw [hpow, hg5]; rfl)
  have hg'1 : g' ≠ 1 := by
    obtain ⟨m, hm, hgm⟩ := hgM
    intro h
    exact hgm (congrArg (fun φ : MulAut ↥M =>
      ((φ ⟨m, hm⟩ : ↥M) : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))) h)
  have h16 : 16 ≤ Nat.card ↥M := QuasithinUnique.B42A57.card_ge_sixteen_of_order_five
    (fun w => Subtype.ext (hs.sec_sq w)) g' hg'5 hg'1
  obtain ⟨h, hh⟩ : ∃ h : ↥H, ¬ ∀ y ∈ M, hs.act h y ∈ M := by
    by_contra hcon
    push Not at hcon
    rcases hs.irr hirr M hcon with h | h
    · exact hM1 h
    · exact hMtop h
  set M' := M.map (hs.act h).toMonoidHom with hM'
  have hM'inv : ∀ k : ↥K, ∀ y ∈ M', actK k y ∈ M' := by
    rintro k _ ⟨y, hy, rfl⟩
    have hk' : (h : G)⁻¹ * k * h ∈ K := by
      have := hs.hKn (H.inv_mem h.2)
      have h2 := (Subgroup.mem_normalizer_iff.mp this (k : G)).mp k.2
      simpa using h2
    refine ⟨actK ⟨_, hk'⟩ y, hMinv _ y hy, ?_⟩
    have e : Subgroup.inclusion hs.hKH k = h * Subgroup.inclusion hs.hKH ⟨_, hk'⟩ * h⁻¹ :=
      Subtype.ext (by simp [mul_assoc])
    show hs.act h (actK ⟨_, hk'⟩ y) = actK k (hs.act h y)
    rw [hactK, MonoidHom.comp_apply, MonoidHom.comp_apply, e, map_mul, map_mul, map_inv,
      MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self]
  have hcardM' : Nat.card ↥M' = Nat.card ↥M :=
    Subgroup.card_map_of_injective (hs.act h).injective
  have hinf : M ⊓ M' = ⊥ := by
    by_contra hb
    have hle : ¬ M ⊓ M' < M := hmin (M ⊓ M') ⟨hb, fun k y hy => ⟨hMinv k y hy.1,
      hM'inv k y hy.2⟩, inf_le_left.trans hMJ⟩
    have hMM' : M ≤ M' := by
      have : M ⊓ M' = M := by
        by_contra hne'
        exact hle (lt_of_le_of_ne inf_le_left hne')
      exact this ▸ inf_le_right
    have hEq : M = M' := Subgroup.eq_of_le_of_card_ge hMM' hcardM'.le
    apply hh
    intro y hy
    rw [hEq]
    exact ⟨y, hy, rfl⟩
  have hinj : Function.Injective (fun p : ↥M × ↥M' =>
      (p.1 : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) * p.2) := by
    rintro ⟨a, b⟩ ⟨a', b'⟩ hab
    simp only at hab
    have h1 : (a' : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))⁻¹ * a =
        b' * (b : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))⁻¹ := by
      calc (a' : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))⁻¹ * a =
            (a' : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))⁻¹ * (a * b) *
              (b : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))⁻¹ := by group
        _ = (a' : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))⁻¹ * (a' * b') *
              (b : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))⁻¹ := by
            rw [hab]
        _ = b' * (b : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))⁻¹ := by group
    have h2 : (a' : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X))⁻¹ * a ∈ M ⊓ M' :=
      ⟨M.mul_mem (M.inv_mem a'.2) a.2, h1 ▸ M'.mul_mem b'.2 (M'.inv_mem b.2)⟩
    rw [hinf, Subgroup.mem_bot, inv_mul_eq_one] at h2
    have h3 : (b : Sec (⊤ : Subgroup ↥X) (W.subgroupOf X)) = b' := by
      rw [← h2] at hab
      exact mul_left_cancel hab
    exact Prod.ext (Subtype.ext h2.symm) (Subtype.ext h3)
  have hle := Nat.card_le_card_of_injective _ hinj
  rw [Nat.card_prod, hcardM'] at hle
  nlinarith

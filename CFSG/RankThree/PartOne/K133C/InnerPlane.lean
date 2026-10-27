module

public import CFSG.RankThree.PartOne.K133.InnerRed
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.RankThree.PartOne.S11d.OutAbstract

public section

namespace CFSG.RankThree.PartOne.K133C

open CFSG CFSG.RankThree.GroupTheory CFSG.ComponentClassification.OuterAutomorphisms
  CFSG.RankThree.PartOne.OutStructure CFSG.RankThree.PartOne.K133

theorem exists_inner_plane {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hO : OutPChain p X)
    {Ē : Subgroup (MulAut X)} (hE : IsElementaryAbelian p Ē) (hc : Nat.card Ē = p ^ 3) :
    ∃ P : Subgroup (MulAut X), P ≤ Ē ∧ P ≤ inner X ∧ Nat.card P = p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  set φ : ↥Ē →* (MulAut X ⧸ inner X) := (QuotientGroup.mk' (inner X)).comp Ē.subtype with hφ
  have hpow : ∀ a : ↥Ē, a ^ p = 1 := fun a =>
    Monoid.exponent_dvd_iff_forall_pow_eq_one.mp (IsElementaryAbelian.exponent_dvd_p p Ē) a
  have hφpow : ∀ a : ↥Ē, φ a ^ p = 1 := fun a => by rw [← map_pow, hpow a, map_one]
  have hmemφ : ∀ a : ↥Ē, φ a = 1 ↔ (a : MulAut X) ∈ inner X := fun a => by
    simp only [hφ, MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
    exact QuotientGroup.eq_one_iff _
  have hcomp : ∀ a b : ↥Ē, φ a ∈ Subgroup.zpowers (φ b) ∨ φ b ∈ Subgroup.zpowers (φ a) := by
    intro a b
    have hab : (a : MulAut X) * b = b * a := congrArg Subtype.val (hE.is_comm.comm a b)
    have hapow : (a : MulAut X) ^ p = 1 := by
      have := congrArg Subtype.val (hpow a)
      simpa using this
    have hbpow : (b : MulAut X) ^ p = 1 := by
      have := congrArg Subtype.val (hpow b)
      simpa using this
    rcases OutPChain.comparable hO hab (k := 1) (l := 1)
      (by rw [pow_one, hapow]; exact (inner X).one_mem)
      (by rw [pow_one, hbpow]; exact (inner X).one_mem) with ⟨m, hm⟩ | ⟨m, hm⟩
    · left
      have h1 : φ (a * b ^ m) = 1 := (hmemφ _).2 (by simpa using hm)
      rw [map_mul, map_zpow] at h1
      have h2 : φ a = (φ b) ^ (-m) := by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
    · right
      have h1 : φ (b * a ^ m) = 1 := (hmemφ _).2 (by simpa using hm)
      rw [map_mul, map_zpow] at h1
      have h2 : φ b = (φ a) ^ (-m) := by rw [zpow_neg]; exact eq_inv_of_mul_eq_one_left h1
      rw [h2]
      exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers _) _
  have hrange : Nat.card φ.range ≤ p := by
    by_contra hgt
    push Not at hgt
    obtain ⟨b, hb⟩ : ∃ b : ↥Ē, φ b ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : φ.range = ⊥ := by
        rw [eq_bot_iff]
        rintro _ ⟨a, rfl⟩
        rw [hno a]
        exact Subgroup.one_mem _
      rw [hbot, Subgroup.card_bot] at hgt
      have := hp.two_le
      omega
    have hbord : orderOf (φ b) = p := orderOf_eq_prime (hφpow b) hb
    have hzcard : Nat.card (Subgroup.zpowers (φ b)) = p := by rw [Nat.card_zpowers, hbord]
    obtain ⟨a, ha⟩ : ∃ a : ↥Ē, φ a ∉ Subgroup.zpowers (φ b) := by
      by_contra hno
      push Not at hno
      have hle : φ.range ≤ Subgroup.zpowers (φ b) := by
        rintro _ ⟨a, rfl⟩
        exact hno a
      have := Subgroup.card_le_of_le hle
      omega
    have ha1 : φ a ≠ 1 := fun h => ha (h ▸ Subgroup.one_mem _)
    have haord : orderOf (φ a) = p := orderOf_eq_prime (hφpow a) ha1
    rcases hcomp a b with h | h
    · exact ha h
    · have hle : Subgroup.zpowers (φ b) ≤ Subgroup.zpowers (φ a) := Subgroup.zpowers_le.2 h
      have heq : Subgroup.zpowers (φ b) = Subgroup.zpowers (φ a) :=
        Subgroup.eq_of_le_of_card_ge hle (by rw [Nat.card_zpowers, Nat.card_zpowers, hbord, haord])
      exact ha (by rw [heq]; exact Subgroup.mem_zpowers _)
  have hmul := Subgroup.card_ker_mul_card_range φ
  rw [hc] at hmul
  have hker : p ^ 2 ≤ Nat.card φ.ker := by
    have h1 : p ^ 3 ≤ Nat.card φ.ker * p := hmul ▸ Nat.mul_le_mul_left _ hrange
    have h2 : p ^ 3 = p ^ 2 * p := by ring
    rw [h2] at h1
    exact Nat.le_of_mul_le_mul_right h1 hp.pos
  have hkerdvd : Nat.card φ.ker ∣ p ^ 3 := ⟨_, hmul.symm⟩
  obtain ⟨i, hi3, hi⟩ := (Nat.dvd_prime_pow hp).1 hkerdvd
  have hi2 : 2 ≤ i := by
    by_contra hlt
    push Not at hlt
    have h1 : p ^ i ≤ p ^ 1 := Nat.pow_le_pow_right hp.pos (by omega)
    have h2 : p ^ 1 < p ^ 2 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    rw [hi] at hker
    omega
  have hdvd2 : p ^ 2 ∣ Nat.card φ.ker := by rw [hi]; exact pow_dvd_pow p hi2
  obtain ⟨K₂, hK₂⟩ := Sylow.exists_subgroup_card_pow_prime p hdvd2
  refine ⟨(K₂.map φ.ker.subtype).map Ē.subtype, Subgroup.map_subtype_le _, ?_, ?_⟩
  · rintro _ ⟨_, ⟨k, -, rfl⟩, rfl⟩
    exact (hmemφ _).1 (MonoidHom.mem_ker.1 k.2)
  · rw [Subgroup.card_map_of_injective Ē.subtype_injective,
      Subgroup.card_map_of_injective φ.ker.subtype_injective, hK₂]

theorem conj_injective_of_center_bot {X : Type*} [Group X] (hZ : Subgroup.center X = ⊥) :
    Function.Injective (MulAut.conj : X →* MulAut X) := by
  rw [injective_iff_map_eq_one]
  intro g hg
  have hgc : g ∈ Subgroup.center X := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := DFunLike.congr_fun hg z
    rw [MulAut.conj_apply, MulAut.one_apply] at h1
    calc z * g = g * z * g⁻¹ * g * 1 := by rw [h1]; group
      _ = g * z := by group
  rw [hZ, Subgroup.mem_bot] at hgc
  exact hgc

@[expose] def MovingPlane (X : Type*) [Group X] (P : Subgroup X) : Prop :=
  ∃ S : Subgroup X, IsPGroup 2 S ∧ (∀ g ∈ P, ∀ s ∈ S, g * s * g⁻¹ ∈ S) ∧
    ∃ g ∈ P, ∃ s ∈ S, g * s * g⁻¹ ≠ s

theorem goodAction_of_movingPlane {X : Type} [Group X] {p : ℕ} (hZ : Subgroup.center X = ⊥)
    {Ē : Subgroup (MulAut X)} {P : Subgroup X} (hc : Nat.card P = p ^ 2)
    (hPĒ : P.map (MulAut.conj : X →* MulAut X) ≤ Ē) (hM : MovingPlane X P) : GoodAction p X Ē := by
  right
  obtain ⟨S, hS2, hSst, g, hg, s, hs, hmv⟩ := hM
  refine ⟨P.map (MulAut.conj : X →* MulAut X), hPĒ, ?_, S, hS2, ?_, MulAut.conj g,
    Subgroup.mem_map_of_mem _ hg, s, hs, ?_⟩
  · rw [Subgroup.card_map_of_injective (conj_injective_of_center_bot hZ), hc]
  · rintro _ ⟨x, hx, rfl⟩ t ht
    simpa [MulAut.conj_apply] using hSst x hx t ht
  · simpa [MulAut.conj_apply] using hmv

theorem good_of_movingPlanes {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime)
    (hZ : Subgroup.center X = ⊥) (hO : OutPChain p X)
    (hM : ∀ P : Subgroup X, IsElementaryAbelian p P → Nat.card P = p ^ 2 → MovingPlane X P) :
    Good p X := by
  intro Ē hE hc
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hPĒ, hPin, hPc⟩ := exists_inner_plane hp hO hE hc
  have hPe : IsElementaryAbelian p P := CFSG.IsElementaryAbelian.of_le hE hPĒ
  obtain ⟨A, hA, hAc, hPA⟩ := exists_pullback_inner hZ hPe hPin
  exact goodAction_of_movingPlane hZ (hAc.trans hPc) (by rw [← hPA]; exact hPĒ)
    (hM A hA (hAc.trans hPc))

end CFSG.RankThree.PartOne.K133C

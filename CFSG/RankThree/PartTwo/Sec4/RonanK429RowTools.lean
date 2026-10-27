module

public import CFSG.RankThree.PartTwo.Sec4.RonanK429Cfg

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.ComponentClassification.OuterAutomorphisms (Outer inner equivalence)

@[expose] def AutNoE27 (S : Type) [Group S] : Prop :=
  ∀ A : Subgroup (MulAut S), ¬ Late.IsE27 A

@[expose] def NoE27 (S : Type) [Group S] : Prop :=
  ∀ D : Subgroup S, ¬ Late.IsE27 D

theorem noCfgS429_of_autNoE27 {S : Type} [Group S] [Finite S] (h : AutNoE27 S) : NoCfgS429 S :=
  fun A _ _ hc => h A hc.isE27

theorem AutNoE27.of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : AutNoE27 T) :
    AutNoE27 S := fun A hA => h _ (hA.map (MulAut.congr e))

theorem NoE27.of_mulEquiv {S T : Type} [Group S] [Group T] (e : S ≃* T) (h : NoE27 T) :
    NoE27 S := fun D hD => h _ (hD.map e)

theorem noE27_of_not_dvd {S : Type} [Group S] [Finite S] (h : ¬ 27 ∣ Nat.card S) : NoE27 S :=
  fun D hD => h (hD.2 ▸ Subgroup.card_subgroup_dvd_card D)

theorem center_eq_bot_of_isSimpleGroup {S : Type} [Group S] (hs : IsSimpleGroup S)
    (hna : ∃ a b : S, a * b ≠ b * a) : Subgroup.center S = ⊥ := by
  haveI := hs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center S) with h | h
  · exact h
  · exfalso
    obtain ⟨a, b, hab⟩ := hna
    have ha : a ∈ Subgroup.center S := h ▸ Subgroup.mem_top a
    exact hab (Subgroup.mem_center_iff.mp ha b).symm

theorem conj_injective_of_center_eq_bot {S : Type} [Group S] (h : Subgroup.center S = ⊥) :
    Function.Injective (MulAut.conj : S →* MulAut S) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have hxZ : x ∈ Subgroup.center S := by
    rw [Subgroup.mem_center_iff]
    intro y
    have := congrArg (fun α : MulAut S => α y) hx
    simp only [MulAut.conj_apply, MulAut.one_apply] at this
    calc y * x = x * y * x⁻¹ * x := by rw [this]
      _ = x * y := by group
  rw [h, Subgroup.mem_bot] at hxZ
  exact hxZ

theorem mem_inner_of_pow_three {S : Type} [Group S] (hout : ¬ 3 ∣ Nat.card (Outer S))
    {α : MulAut S} (hα : α ^ 3 = 1) : α ∈ inner S := by
  have hne : Nat.card (Outer S) ≠ 0 := fun h0 => hout (h0 ▸ dvd_zero 3)
  have : Finite (Outer S) := Nat.finite_of_card_ne_zero hne
  set t : Outer S := (α : Outer S) with ht
  have ht3 : t ^ 3 = 1 := by rw [ht, ← QuotientGroup.mk_pow, hα, QuotientGroup.mk_one]
  have hcop : Nat.Coprime 3 (Nat.card (Outer S)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hout
  have hord : orderOf t ∣ Nat.gcd 3 (Nat.card (Outer S)) :=
    Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one ht3) (orderOf_dvd_natCard t)
  rw [hcop] at hord
  have ht1 : t = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp hord)
  exact (QuotientGroup.eq_one_iff α).mp ht1

theorem autNoE27_of_noE27 {S : Type} [Group S] (hout : ¬ 3 ∣ Nat.card (Outer S))
    (hcen : Subgroup.center S = ⊥) (hE : NoE27 S) : AutNoE27 S := by
  intro A hA
  have hAin : A ≤ (MulAut.conj : S →* MulAut S).range := fun a ha =>
    (mem_inner_of_pow_three hout (hA.1.2 a ha) : a ∈ inner S)
  have hinj := conj_injective_of_center_eq_bot hcen
  set P := A.comap (MulAut.conj : S →* MulAut S) with hP
  have hmap : P.map (MulAut.conj : S →* MulAut S) = A := Subgroup.map_comap_eq_self hAin
  apply hE P
  refine ⟨⟨⟨⟨fun x y => Subtype.ext (hinj ?_)⟩⟩, fun x hx => hinj ?_⟩, ?_⟩
  · rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    exact congrArg Subtype.val (hA.1.1.is_comm.comm ⟨_, x.2⟩ ⟨_, y.2⟩)
  · rw [map_pow, map_one]
    exact hA.1.2 _ hx
  · rw [← hA.2, ← hmap, Subgroup.card_map_of_injective hinj]

theorem autNoE27_of_mulEquiv_of_noE27 {S T : Type} [Group S] [Group T] (e : S ≃* T)
    (hs : IsSimpleGroup S) (hna : ∃ a b : S, a * b ≠ b * a) (hout : ¬ 3 ∣ Nat.card (Outer T))
    (hE : NoE27 T) : AutNoE27 S :=
  autNoE27_of_noE27 (by rwa [Nat.card_congr (equivalence e).toEquiv])
    (center_eq_bot_of_isSimpleGroup hs hna) (hE.of_mulEquiv e)

end CFSG.RankThree.PartTwo.Sec4.RonanK429

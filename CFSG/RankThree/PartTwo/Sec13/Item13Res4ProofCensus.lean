module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Res4Proof

section Fixed

variable {X : Type*} [Group X]

@[expose] def fixedSubgroup (B : Subgroup (MulAut X)) : Subgroup X where
  carrier := {x | ∀ β ∈ B, β x = x}
  mul_mem' := by
    intro x y hx hy β hβ
    rw [map_mul, hx β hβ, hy β hβ]
  one_mem' := fun β _ => map_one β
  inv_mem' := by
    intro x hx β hβ
    rw [map_inv, hx β hβ]

theorem mem_fixedSubgroup_iff {B : Subgroup (MulAut X)} {x : X} :
    x ∈ fixedSubgroup B ↔ ∀ β ∈ B, β x = x :=
  Iff.rfl

theorem exists_orderOf_eq_three_forall_fixed [Finite X] {B : Subgroup (MulAut X)}
    (hB : ∀ β ∈ B, β ^ 3 = 1) (h3 : 3 ∣ Nat.card X) :
    ∃ x : X, orderOf x = 3 ∧ ∀ β ∈ B, β x = x := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hBp : IsPGroup 3 B := fun β => ⟨1, Subtype.ext (by simpa using hB β β.2)⟩
  have hmod := hBp.card_modEq_card_fixedPoints X
  have hfix : Nat.card (MulAction.fixedPoints B X) = Nat.card (fixedSubgroup B) := by
    refine Nat.card_congr (Equiv.subtypeEquivRight fun x => ?_)
    constructor
    · intro hx β hβ
      exact hx ⟨β, hβ⟩
    · intro hx β
      exact hx β β.2
  have hF3 : 3 ∣ Nat.card (fixedSubgroup B) := by
    rw [hfix] at hmod
    exact Nat.modEq_zero_iff_dvd.mp (hmod.symm.trans (Nat.modEq_zero_iff_dvd.mpr h3))
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := fixedSubgroup B) 3 hF3
  exact ⟨x, by rw [Subgroup.orderOf_coe, hx], x.2⟩

theorem card_eq_card_ker_mul_card_range {H H' : Type*} [Group H] [Group H'] (f : H →* H') :
    Nat.card H = Nat.card f.ker * Nat.card f.range := by
  rw [← Subgroup.index_ker, Subgroup.card_mul_index]

theorem not_le_range_conj [Finite X] {B : Subgroup (MulAut X)} (hB : ∀ β ∈ B, β ^ 3 = 1)
    (hB9 : Nat.card B = 9) {Z₀ : Subgroup X} (hZ₀ : Nat.card Z₀ ≤ 3)
    (hF1 : ∀ x : X, orderOf x = 3 → (∀ β ∈ B, β x = x) → x ∈ Z₀)
    (hNP : ∀ y : X, MulAut.conj y ∈ B → ∀ β ∈ B, β y = y) :
    ¬ B ≤ (MulAut.conj : X →* MulAut X).range := by
  intro hBin
  set Y : Subgroup X := B.comap (MulAut.conj : X →* MulAut X) with hY
  have hcomm : ∀ y ∈ Y, ∀ y' ∈ Y, y * y' = y' * y := by
    intro y hy y' hy'
    have h := hNP y hy (MulAut.conj y') hy'
    rw [MulAut.conj_apply] at h
    calc y * y' = (y' * y * y'⁻¹) * y' := by rw [h]
      _ = y' * y := by group
  set ψ : Y →* MulAut X := (MulAut.conj : X →* MulAut X).comp Y.subtype with hψ
  have hψr : ψ.range = B := by
    ext β
    constructor
    · rintro ⟨y, rfl⟩
      exact y.2
    · intro hβ
      obtain ⟨y, hy⟩ := hBin hβ
      have hyY : y ∈ Y := by
        change MulAut.conj y ∈ B
        rw [hy]
        exact hβ
      exact ⟨⟨y, hyY⟩, hy⟩
  have hψk : Nat.card ψ.ker ≤ Nat.card (Subgroup.center X) := by
    refine Nat.card_le_card_of_injective (fun w => (⟨(w : Y), ?_⟩ : Subgroup.center X)) ?_
    · have hw : MulAut.conj ((w : Y) : X) = 1 := w.2
      rw [Subgroup.mem_center_iff]
      intro g
      have h1 := congrArg (fun φ : MulAut X => φ g) hw
      simp only [MulAut.conj_apply, MulAut.one_apply] at h1
      calc g * ((w : Y) : X) = (((w : Y) : X) * g * ((w : Y) : X)⁻¹) * ((w : Y) : X) := by
            rw [h1]
        _ = ((w : Y) : X) * g := by group
    · intro w w' h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
  set f : Y →* Y :=
    { toFun := fun w => w ^ 3
      map_one' := one_pow 3
      map_mul' := fun a b => by
        have hab : Commute a b := Subtype.ext (hcomm a a.2 b b.2)
        exact hab.mul_pow 3 } with hf
  have hfr : f.range ≤ ψ.ker := by
    rintro _ ⟨w, rfl⟩
    rw [MonoidHom.mem_ker]
    change ψ (w ^ 3) = 1
    rw [map_pow]
    exact hB _ w.2
  have hfk : Nat.card f.ker ≤ Nat.card Z₀ := by
    refine Nat.card_le_card_of_injective (fun w => (⟨((w : Y) : X), ?_⟩ : Z₀)) ?_
    · have hw3 : ((w : Y) : X) ^ 3 = 1 := by
        have hw : (w : Y) ^ 3 = 1 := w.2
        exact congrArg Subtype.val hw
      by_cases hw1 : ((w : Y) : X) = 1
      · rw [hw1]
        exact Z₀.one_mem
      · have hord : orderOf ((w : Y) : X) = 3 := orderOf_eq_prime hw3 hw1
        exact hF1 _ hord (hNP _ (w : Y).2)
    · intro w w' h
      simp only [Subtype.mk.injEq] at h
      exact Subtype.ext (Subtype.ext h)
  have h1 := card_eq_card_ker_mul_card_range ψ
  have h2 := card_eq_card_ker_mul_card_range f
  have h3 : Nat.card f.range ≤ Nat.card ψ.ker := Subgroup.card_le_of_le hfr
  rw [hψr, hB9] at h1
  have hk : 0 < Nat.card ψ.ker := Nat.card_pos
  have h4 : Nat.card f.ker * Nat.card f.range ≤ 3 * Nat.card ψ.ker :=
    Nat.mul_le_mul (hfk.trans hZ₀) h3
  omega

end Fixed

end Res4Proof

@[expose] def KS131CentralCensus : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec4.IsList46 X → IsQuasisimple X →
    ∀ B : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B = 9 →
    ∀ Z₀ : Subgroup X, Z₀ ≤ Subgroup.center X → Nat.card Z₀ ∣ 3 →
      (∀ x : X, orderOf x = 3 → (∀ β ∈ B, β x = x) → x ∈ Z₀) →
      (Nat.card Z₀ = 3 → Nat.card (Subgroup.center X) = 3 →
        ∀ y : X, MulAut.conj y ∈ B → ∀ β ∈ B, β y = y) → False

@[expose] def KS131ThreeFreeNoE9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec4.IsList46 X → IsQuasisimple X → ¬ 3 ∣ Nat.card X →
    ∀ B : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B = 9 → False

@[expose] def KS131CenterList46 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec4.IsList46 X → IsQuasisimple X →
    3 ∣ Nat.card (Subgroup.center X) → Nat.card (Subgroup.center X) = 3

@[expose] def KS131CenterOuterE9 : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec4.IsList46 X → IsQuasisimple X →
    Nat.card (Subgroup.center X) = 3 →
    ∀ B : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 B → Nat.card B = 9 →
      (∀ x : X, orderOf x = 3 → (∀ β ∈ B, β x = x) → x ∈ Subgroup.center X) →
      (∀ y : X, MulAut.conj y ∈ B → ∀ β ∈ B, β y = y) →
      ¬ B ≤ (MulAut.conj : X →* MulAut X).range → False

theorem ks131CentralCensus_of (h1 : KS131ThreeFreeNoE9) (h2 : KS131CenterList46)
    (h3 : KS131CenterOuterE9) : KS131CentralCensus := by
  intro X _ _ hl hq B hB hB9 Z₀ hZc hZ3 hF1 hNP
  have hBexp : ∀ β ∈ B, β ^ 3 = 1 := hB.2
  rcases (Nat.dvd_prime Nat.prime_three).mp hZ3 with h | h
  · by_cases h3X : 3 ∣ Nat.card X
    · obtain ⟨x, hx3, hfix⟩ := Res4Proof.exists_orderOf_eq_three_forall_fixed hBexp h3X
      have hx : x ∈ Z₀ := hF1 x hx3 hfix
      rw [Subgroup.eq_bot_of_card_eq Z₀ h, Subgroup.mem_bot] at hx
      rw [hx, orderOf_one] at hx3
      omega
    · exact h1 X hl hq h3X B hB hB9
  · have hZ3' : 3 ∣ Nat.card (Subgroup.center X) := h ▸ Subgroup.card_dvd_of_le hZc
    have hZX := h2 X hl hq hZ3'
    have hZeq : Z₀ = Subgroup.center X :=
      Subgroup.eq_of_le_of_card_ge hZc (by rw [h, hZX])
    have hNP' := hNP h hZX
    exact h3 X hl hq hZX B hB hB9 (fun x hx hfix => hZeq ▸ hF1 x hx hfix) hNP'
      (Res4Proof.not_le_range_conj hBexp hB9 h.le hF1 hNP')

theorem KS131CentralCensus.false_of_mulEquiv (hK : KS131CentralCensus) {X X' : Type}
    [Group X] [Finite X] [Group X'] [Finite X'] (e : X' ≃* X) (hl : Sec4.IsList46 X')
    (hq : IsQuasisimple X) {B : Subgroup (MulAut X)} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hB9 : Nat.card B = 9) {Z₀ : Subgroup X} (hZc : Z₀ ≤ Subgroup.center X)
    (hZ3 : Nat.card Z₀ ∣ 3) (hF1 : ∀ x : X, orderOf x = 3 → (∀ β ∈ B, β x = x) → x ∈ Z₀)
    (hNP : Nat.card Z₀ = 3 → Nat.card (Subgroup.center X) = 3 →
      ∀ y : X, MulAut.conj y ∈ B → ∀ β ∈ B, β y = y) : False := by
  set κ : MulAut X ≃* MulAut X' := MulAut.congr e.symm with hκ
  have hκapp : ∀ (β : MulAut X) (x : X'), κ β x = e.symm (β (e x)) := fun β x => rfl
  set B' : Subgroup (MulAut X') := B.map κ.toMonoidHom with hB'
  set Z₀' : Subgroup X' := Z₀.map e.symm.toMonoidHom with hZ₀'
  have hcardB : Nat.card B' = Nat.card B := Subgroup.card_map_of_injective κ.injective
  have hcardZ : Nat.card Z₀' = Nat.card Z₀ := Subgroup.card_map_of_injective e.symm.injective
  have hcen : (Subgroup.center X).map e.symm.toMonoidHom = Subgroup.center X' :=
    Subgroup.map_center_eq e.symm
  have hcardC : Nat.card (Subgroup.center X') = Nat.card (Subgroup.center X) := by
    rw [← hcen, Subgroup.card_map_of_injective e.symm.injective]
  have hq' : IsQuasisimple X' := CFSG.LocalCores.isQuasisimple_of_mulEquiv e.symm hq
  have hB'e : CFSG.Assembly.IsElemAbelian 3 B' := by
    have := hB.1
    refine ⟨⟨⟨fun β γ => ?_⟩⟩, ?_⟩
    · obtain ⟨_, β₀, hβ₀, rfl⟩ := β
      obtain ⟨_, γ₀, hγ₀, rfl⟩ := γ
      apply Subtype.ext
      change κ β₀ * κ γ₀ = κ γ₀ * κ β₀
      rw [← map_mul, ← map_mul]
      exact congrArg κ (congrArg Subtype.val (mul_comm' (⟨β₀, hβ₀⟩ : B) ⟨γ₀, hγ₀⟩))
    · rintro _ ⟨β₀, hβ₀, rfl⟩
      change (κ β₀) ^ 3 = 1
      rw [← map_pow, hB.2 β₀ hβ₀, map_one]
  have hfix' : ∀ x : X', (∀ β ∈ B', β x = x) → ∀ β ∈ B, β (e x) = e x := by
    intro x hx β hβ
    have h1 := hx (κ β) ⟨β, hβ, rfl⟩
    rw [hκapp] at h1
    have h2 := congrArg e h1
    simpa using h2
  refine hK X' hl hq' B' hB'e (hcardB.trans hB9) Z₀' ?_ (hcardZ ▸ hZ3) ?_ ?_
  · rw [← hcen]
    exact Subgroup.map_mono hZc
  · intro x hx3 hx
    have hex : e x ∈ Z₀ := hF1 (e x) (by rw [MulEquiv.orderOf_eq]; exact hx3) (hfix' x hx)
    exact ⟨e x, hex, by simp⟩
  · intro hZ3' hC3 y hy β hβ
    obtain ⟨β₀, hβ₀, rfl⟩ := hβ
    have hconj : κ (MulAut.conj (e y)) = MulAut.conj y := by
      ext z
      rw [hκapp, MulAut.conj_apply, MulAut.conj_apply, map_mul, map_mul, map_inv,
        MulEquiv.symm_apply_apply, MulEquiv.symm_apply_apply]
    have hyB : MulAut.conj (e y) ∈ B := by
      obtain ⟨γ, hγ, hγeq⟩ := hy
      have : γ = MulAut.conj (e y) := κ.injective (hγeq.trans hconj.symm)
      exact this ▸ hγ
    have h1 := hNP (hcardZ ▸ hZ3') (hcardC ▸ hC3) (e y) hyB β₀ hβ₀
    change κ β₀ y = y
    rw [hκapp, h1, MulEquiv.symm_apply_apply]

end CFSG.RankThree.PartTwo.Sec13

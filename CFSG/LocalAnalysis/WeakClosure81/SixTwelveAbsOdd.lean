module

public import CFSG.LocalAnalysis.WeakClosure81.SixTwelveAbsDefs
public import CFSG.GroupTheory.ConjFixedParity
public import CFSG.GroupTheory.ElemAbelianClosure

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.CGT.Timmesfeld75 CFSG.Open
open CFSG.RankThree.GF2n (conjSubgroup_mul card_conjSubgroup conjSubgroup_eq_self_iff)
open scoped commutatorElement

variable {X : Type} [Group X] [Finite X]

theorem odd_ncard_conjSubgroupOrbit {Y T : Subgroup X} (hTY : T ≤ Y) (hT : IsPGroup 2 T)
    (hfix : ∀ y ∈ Y, T ≤ Subgroup.normalizer (conjSubgroup y T : Set X) →
      conjSubgroup y T = T) :
    Odd (conjSubgroupOrbit Y T).ncard := by
  classical
  have h𝒜 : ∀ x ∈ T, ∀ C ∈ conjSubgroupOrbit Y T,
      C.map (MulAut.conj x).toMonoidHom ∈ conjSubgroupOrbit Y T := by
    intro x hx C hC
    obtain ⟨y, hy, rfl⟩ := hC
    refine ⟨x * y, Y.mul_mem (hTY hx) hy, ?_⟩
    show conjSubgroup x (conjSubgroup y T) = conjSubgroup (x * y) T
    rw [conjSubgroup_mul]
  have hfixset : {C ∈ conjSubgroupOrbit Y T |
      ∀ x ∈ T, C.map (MulAut.conj x).toMonoidHom = C} = {T} := by
    ext C
    constructor
    · rintro ⟨hC, hfixC⟩
      obtain ⟨y, hy, rfl⟩ := hC
      exact hfix y hy fun x hx =>
        Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hfixC x hx)
    · intro hC
      rw [Set.mem_singleton_iff] at hC
      rw [hC]
      refine ⟨⟨1, Y.one_mem, (CFSG.CGT.Timmesfeld75.conjSubgroup_one T).symm⟩, ?_⟩
      intro x hx
      exact Subgroup.mem_normalizer_iff_map_conj_eq.mp
        ((Subgroup.le_normalizer : T ≤ Subgroup.normalizer (T : Set X)) hx)
  have hmod := CFSG.GroupTheory.ncard_modEq_ncard_fixed (T := T) hT
    (𝒜 := conjSubgroupOrbit Y T) h𝒜
  rw [hfixset, Set.ncard_singleton] at hmod
  rw [Nat.odd_iff]
  simpa [Nat.ModEq] using hmod

theorem exists_fixed_of_odd_ncard {P : Subgroup X} (hP : IsPGroup 2 P) {𝒜 : Set (Subgroup X)}
    (h𝒜 : ∀ x ∈ P, ∀ C ∈ 𝒜, conjSubgroup x C ∈ 𝒜) (hodd : Odd 𝒜.ncard) :
    ∃ C ∈ 𝒜, ∀ x ∈ P, conjSubgroup x C = C := by
  classical
  have hmod := CFSG.GroupTheory.ncard_modEq_ncard_fixed (T := P) hP (𝒜 := 𝒜) h𝒜
  set F : Set (Subgroup X) :=
    {C ∈ 𝒜 | ∀ x ∈ P, C.map (MulAut.conj x).toMonoidHom = C} with hF
  have hmod' : 𝒜.ncard % 2 = F.ncard % 2 := by simpa [Nat.ModEq] using hmod
  have hFodd : Odd F.ncard := by
    rw [Nat.odd_iff]
    rw [← hmod']
    exact Nat.odd_iff.mp hodd
  have hFne : F.ncard ≠ 0 := by
    intro h0
    have h1 : F.ncard % 2 = 1 := Nat.odd_iff.mp hFodd
    rw [h0] at h1
    omega
  obtain ⟨C, hCF⟩ := Set.nonempty_of_ncard_ne_zero hFne
  exact ⟨C, hCF.1, fun x hx => hCF.2 x hx⟩

theorem exists_ne_one_centralizes {P W : Subgroup X} (hP : IsPGroup 2 P) (hW : IsPGroup 2 W)
    (hW1 : W ≠ ⊥) (hPW : P ≤ Subgroup.normalizer (W : Set X)) :
    ∃ b ∈ W, b ≠ 1 ∧ ∀ a ∈ P, a * b = b * a := by
  classical
  let Q : Subgroup X := W ⊔ P
  have hQ : IsPGroup 2 Q := IsPGroup.to_sup_of_normal_left' hW hP hPW
  have hWQ : W ≤ Q := le_sup_left
  have hnormW : Q ≤ Subgroup.normalizer (W : Set X) := sup_le Subgroup.le_normalizer hPW
  haveI : Finite ↥Q := Finite.of_injective (fun q : ↥Q => (q : X)) (fun a b h => Subtype.ext h)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsNilpotent ↥Q := hQ.isNilpotent
  have hNormal : (W.subgroupOf Q).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hWQ).mpr hnormW
  haveI := hNormal
  have hne : W.subgroupOf Q ≠ ⊥ := by
    intro hbot
    apply hW1
    have hd : W ⊓ Q = ⊥ := disjoint_iff.mp (Subgroup.subgroupOf_eq_bot.mp hbot)
    rwa [inf_eq_left.mpr hWQ] at hd
  obtain ⟨b, hb1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp
      (Group.IsNilpotent.inf_center_ne_bot_of_normal (G := ↥Q) hne)
  refine ⟨(b : X), Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp b.2).1, ?_, ?_⟩
  · intro hbX1
    exact hb1 (Subtype.ext (Subtype.ext (by simpa using hbX1)))
  · intro a ha
    have hPQ : P ≤ Q := le_sup_right
    have haQ : a ∈ Q := hPQ ha
    have hcomm : (⟨a, haQ⟩ : Q) * (b : ↥Q) = (b : ↥Q) * ⟨a, haQ⟩ :=
      Subgroup.mem_center_iff.mp (Subgroup.mem_inf.mp b.2).2 ⟨a, haQ⟩
    exact congrArg Subtype.val hcomm

namespace Abs612

variable {T T₁ Z E : Subgroup X}

theorem conjSubgroup_eq_of_le_normalizer (h : Abs612 T T₁ Z E) {y : X}
    (hy : T ≤ Subgroup.normalizer (conjSubgroup y T : Set X)) : conjSubgroup y T = T := by
  have hW2 : IsPGroup 2 (conjSubgroup y T) := (h.elem_conj y).isPGroup
  have hW1 : conjSubgroup y T ≠ ⊥ := by
    intro hbot
    have hcard := CFSG.RankThree.GF2n.card_conjSubgroup y T
    rw [hbot, Subgroup.card_bot] at hcard
    have h4 := h.four_le
    omega
  obtain ⟨b, hbW, hb1, hbcomm⟩ :=
    exists_ne_one_centralizes h.elem.isPGroup hW2 hW1 hy
  obtain ⟨a, ha1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.ne_bot
  have haT : (a : X) ∈ T := a.2
  have haX1 : (a : X) ≠ 1 := fun hh => ha1 (Subtype.ext (by simpa using hh))
  have hcomm : ⁅(a : X), b⁆ = 1 :=
    (commutatorElement_eq_one_iff_mul_comm).2 (hbcomm (a : X) haT)
  have hmem : (a : X) ∈ conjSubgroup 1 T := by
    rw [CFSG.CGT.Timmesfeld75.conjSubgroup_one]
    exact haT
  have hZ : ⁅(a : X), b⁆ ∈ Z := by rw [hcomm]; exact Z.one_mem
  have hclosed := h.closed 1 y (a : X) hmem haX1 b hbW hb1 hZ
  rw [CFSG.CGT.Timmesfeld75.conjSubgroup_one] at hclosed
  exact hclosed.symm

theorem odd_ncard_orbit (h : Abs612 T T₁ Z E) {Y : Subgroup X} (hTY : T ≤ Y) :
    Odd (conjSubgroupOrbit Y T).ncard :=
  odd_ncard_conjSubgroupOrbit hTY h.elem.isPGroup
    (fun y _ hy => h.conjSubgroup_eq_of_le_normalizer hy)

theorem exists_fixed_orbit (h : Abs612 T T₁ Z E) :
    ∃ x : X, ∀ s ∈ T₁, conjSubgroup s (conjSubgroup x T) = conjSubgroup x T := by
  have hodd : Odd (conjSubgroupOrbit (⊤ : Subgroup X) T).ncard := h.odd_ncard_orbit le_top
  have h𝒜 : ∀ s ∈ T₁, ∀ C ∈ conjSubgroupOrbit (⊤ : Subgroup X) T,
      conjSubgroup s C ∈ conjSubgroupOrbit (⊤ : Subgroup X) T := by
    intro s _ C hC
    obtain ⟨y, -, rfl⟩ := hC
    exact ⟨s * y, Subgroup.mem_top _, by rw [conjSubgroup_mul]⟩
  obtain ⟨C, hC, hfix⟩ := exists_fixed_of_odd_ncard h.elem₁.isPGroup h𝒜 hodd
  obtain ⟨x, -, rfl⟩ := hC
  exact ⟨x, hfix⟩

theorem exists_fixed_orbit_sup (h : Abs612 T T₁ Z E) {s : X} (hs : s ∈ T₁)
    (hconj : ∃ y ∈ T ⊔ conjSubgroup s T, conjSubgroup s T = conjSubgroup y T) :
    ∃ y ∈ T ⊔ conjSubgroup s T, conjSubgroup s (conjSubgroup y T) = conjSubgroup y T := by
  classical
  have hss : s * s = 1 := IsElemAbelian.mul_self_eq_one h.elem₁ hs
  have hsz : s ^ (2 : ℤ) = 1 := by
    rw [show (2 : ℤ) = ((2 : ℕ) : ℤ) by norm_num, zpow_natCast, pow_two, hss]
  have hmap : conjSubgroup s (conjSubgroup s T) = T := by
    rw [← conjSubgroup_mul, hss, CFSG.CGT.Timmesfeld75.conjSubgroup_one]
  have hYconj : conjSubgroup s (T ⊔ conjSubgroup s T) = T ⊔ conjSubgroup s T := by
    show (T ⊔ conjSubgroup s T).map (MulAut.conj s).toMonoidHom = T ⊔ conjSubgroup s T
    rw [Subgroup.map_sup]
    change conjSubgroup s T ⊔ conjSubgroup s (conjSubgroup s T) = T ⊔ conjSubgroup s T
    rw [hmap]
    exact sup_comm _ _
  have hsN : s ∈ Subgroup.normalizer ((T ⊔ conjSubgroup s T : Subgroup X) : Set X) :=
    CFSG.RankThree.GF2n.conjSubgroup_eq_self_iff.mp hYconj
  have hodd : Odd (conjSubgroupOrbit (T ⊔ conjSubgroup s T) T).ncard :=
    h.odd_ncard_orbit le_sup_left
  obtain ⟨y₀, hy₀, hconj₀⟩ := hconj
  have hconj_s : ∀ C ∈ conjSubgroupOrbit (T ⊔ conjSubgroup s T) T,
      conjSubgroup s C ∈ conjSubgroupOrbit (T ⊔ conjSubgroup s T) T := by
    intro C hC
    obtain ⟨y, hy, rfl⟩ := hC
    have hsy : s * y * s⁻¹ ∈ T ⊔ conjSubgroup s T :=
      (Subgroup.mem_normalizer_iff.mp hsN y).mp hy
    refine ⟨(s * y * s⁻¹) * y₀, (T ⊔ conjSubgroup s T).mul_mem hsy hy₀, ?_⟩
    show conjSubgroup s (conjSubgroup y T) = conjSubgroup ((s * y * s⁻¹) * y₀) T
    have key : conjSubgroup (s * y) T = conjSubgroup ((s * y * s⁻¹) * y₀) T := by
      calc conjSubgroup (s * y) T
          = conjSubgroup ((s * y * s⁻¹) * s) T := by
            rw [show (s * y * s⁻¹) * s = s * y by group]
        _ = conjSubgroup (s * y * s⁻¹) (conjSubgroup s T) := conjSubgroup_mul _ _ _
        _ = conjSubgroup (s * y * s⁻¹) (conjSubgroup y₀ T) := by rw [hconj₀]
        _ = conjSubgroup ((s * y * s⁻¹) * y₀) T := (conjSubgroup_mul _ _ _).symm
    rw [← conjSubgroup_mul]
    exact key
  let P : Subgroup X := Subgroup.zpowers s
  have hP : IsPGroup 2 P := h.elem₁.isPGroup.to_le (Subgroup.zpowers_le.mpr hs)
  have hpow : ∀ k : ℤ, s ^ k = 1 ∨ s ^ k = s := by
    intro k
    obtain ⟨m, hm | hm⟩ := Int.even_or_odd' k
    · left
      rw [hm, zpow_mul, hsz, one_zpow]
    · right
      rw [hm, zpow_add, zpow_mul, hsz, one_zpow, one_mul, zpow_one]
  have hP_closed : ∀ x ∈ P, ∀ C ∈ conjSubgroupOrbit (T ⊔ conjSubgroup s T) T,
      conjSubgroup x C ∈ conjSubgroupOrbit (T ⊔ conjSubgroup s T) T := by
    intro x hx C hC
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp (show x ∈ Subgroup.zpowers s from hx)
    rcases hpow k with hk | hk
    · rw [hk, CFSG.CGT.Timmesfeld75.conjSubgroup_one]
      exact hC
    · rw [hk]
      exact hconj_s C hC
  obtain ⟨C, hC, hfixC⟩ := exists_fixed_of_odd_ncard hP hP_closed hodd
  obtain ⟨y, hy, rfl⟩ := hC
  exact ⟨y, hy, hfixC s (show s ∈ P from Subgroup.mem_zpowers s)⟩

end Abs612

end CFSG.LocalAnalysis.WeakClosure81

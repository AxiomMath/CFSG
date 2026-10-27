module

public import CFSG.Timmesfeld.RankOne.Moufang
public import CFSG.LocalAnalysis.ZStar

public section

namespace CFSG.Timmesfeld

open RankOne

section

variable {X : Type*} [Group X]

@[expose] def pairStabilizer (A B : Subgroup X) : Subgroup X where
  carrier := {g | (A.map (MulAut.conj g).toMonoidHom = A ∧
      B.map (MulAut.conj g).toMonoidHom = B) ∨
    (A.map (MulAut.conj g).toMonoidHom = B ∧ B.map (MulAut.conj g).toMonoidHom = A)}
  one_mem' := Or.inl ⟨map_conj_one A, map_conj_one B⟩
  mul_mem' := by
    rintro g g' (⟨hA, hB⟩ | ⟨hA, hB⟩) (⟨hA', hB'⟩ | ⟨hA', hB'⟩) <;>
      simp only [Set.mem_ofPred_eq, map_conj_mul, hA, hB, hA', hB', and_true, true_or,
        or_true]
  inv_mem' := by
    rintro g (⟨hA, hB⟩ | ⟨hA, hB⟩)
    · left
      exact ⟨(map_conj_eq_iff.1 hA).symm, (map_conj_eq_iff.1 hB).symm⟩
    · right
      exact ⟨(map_conj_eq_iff.1 hB).symm, (map_conj_eq_iff.1 hA).symm⟩

theorem mem_pairStabilizer {A B : Subgroup X} {g : X} :
    g ∈ pairStabilizer A B ↔ (A.map (MulAut.conj g).toMonoidHom = A ∧
      B.map (MulAut.conj g).toMonoidHom = B) ∨
    (A.map (MulAut.conj g).toMonoidHom = B ∧ B.map (MulAut.conj g).toMonoidHom = A) :=
  Iff.rfl

namespace IsElemAbRankOne

variable {A B : Subgroup X} (h : IsElemAbRankOne A B)
include h

theorem mem_pairStabilizer_of_mem_weylSet {m : X} (hm : m ∈ weylSet A B) :
    m ∈ pairStabilizer A B :=
  Or.inr ⟨hm.2.2, h.map_conj_B_of_mem_weylSet hm⟩

theorem conj_mem_weylSet {g n : X} (hg : g ∈ pairStabilizer A B) (hn : n ∈ weylSet A B) :
    g * n * g⁻¹ ∈ weylSet A B := by
  obtain ⟨hn1, ⟨x, hx⟩, hnA⟩ := hn
  have hnB := h.map_conj_B_of_mem_weylSet ⟨hn1, ⟨x, hx⟩, hnA⟩
  refine ⟨?_, ⟨g * x, ?_⟩, ?_⟩
  · intro h1
    apply hn1
    calc n = g⁻¹ * (g * n * g⁻¹) * g := by group
      _ = 1 := by rw [h1]; group
  · rw [map_conj_mul]
    exact conj_mem_map_conj g hx
  · rw [map_conj_mul, map_conj_mul]
    rcases hg with ⟨hA, hB⟩ | ⟨hA, hB⟩
    · have hA' : A.map (MulAut.conj g⁻¹).toMonoidHom = A := (map_conj_eq_iff.1 hA).symm
      rw [hA', hnA, hB]
    · have hA' : A.map (MulAut.conj g⁻¹).toMonoidHom = B := (map_conj_eq_iff.1 hB).symm
      rw [hA', hnB, hA]

end IsElemAbRankOne

end

variable {X : Type} [Group X]

namespace IsElemAbRankOne

variable {A B : Subgroup X} (h : IsElemAbRankOne A B)
include h

theorem odd_card_hua [Finite X] : Odd (Nat.card (hua A B)) := by
  classical
  obtain ⟨n, hn⟩ := h.weylSet_nonempty
  set W := pairStabilizer A B
  have hnW : n ∈ W := h.mem_pairStabilizer_of_mem_weylSet hn
  have hnn : n * n = 1 := h.mul_self_of_mem_weylSet hn
  have hninv : n⁻¹ = n := inv_eq_of_mul_eq_one_right hnn
  let : Fintype W := Fintype.ofFinite W
  let t : W := ⟨n, hnW⟩
  have ht1 : t ≠ 1 := fun h1 => hn.1 (congrArg Subtype.val h1)
  have ht2 : t * t = 1 := Subtype.ext hnn
  have hcomm : ∀ m ∈ weylSet A B, n * m = m * n → m = n := by
    intro m hm hmn
    obtain ⟨x, hx⟩ := hn.2.1
    obtain ⟨y, hy⟩ := hm.2.1
    have hxy := h.eq_of_commute hx hn.1 hy hm.1 hmn
    exact h.eq_of_mem_weylSet hm hn (hxy ▸ hy) hx
  have hiso : ∀ g : W, g * t * g⁻¹ * t = t * (g * t * g⁻¹) → g * t * g⁻¹ = t := by
    intro g hg
    have hg' : (g : X) * n * (g : X)⁻¹ * n = n * ((g : X) * n * (g : X)⁻¹) :=
      congrArg Subtype.val hg
    apply Subtype.ext
    exact hcomm _ (h.conj_mem_weylSet g.2 hn) hg'.symm
  obtain ⟨N, -, hNodd, hN⟩ := CFSG.ZStar.glauberman_zStar W t ht1 ht2 hiso
  have hmn : ∀ m ∈ weylSet A B, ∀ hmW : m * n ∈ W, (⟨m * n, hmW⟩ : W) ∈ N := by
    intro m hm hmW
    by_cases hmeq : m = n
    · subst hmeq
      have : (⟨m * m, hmW⟩ : W) = 1 := Subtype.ext hnn
      rw [this]
      exact N.one_mem
    obtain ⟨x, hx⟩ := hn.2.1
    obtain ⟨y, hy⟩ := hm.2.1
    have hne : A.map (MulAut.conj x).toMonoidHom ≠ A.map (MulAut.conj y).toMonoidHom := by
      intro hxy
      exact hmeq (h.eq_of_mem_weylSet hm hn (hxy ▸ hy) hx)
    have hodd := h.odd_orderOf_mul hx hn.1 hy hm.1 hne
    obtain ⟨g, hg, hgnm⟩ := exists_conj_of_odd_orderOf_mul hnn
      (h.mul_self_of_mem_weylSet hm) hodd
    have hgW : g ∈ W := by
      have : Subgroup.closure ({n, m} : Set X) ≤ W := by
        rw [Subgroup.closure_le]
        rintro z (rfl | rfl)
        · exact hnW
        · exact h.mem_pairStabilizer_of_mem_weylSet hm
      exact this hg
    have := hN ⟨g, hgW⟩
    have heq : (⟨g, hgW⟩ * t * (⟨g, hgW⟩ : W)⁻¹ * t⁻¹ : W) = ⟨m * n, hmW⟩ := by
      apply Subtype.ext
      change g * n * g⁻¹ * n⁻¹ = m * n
      rw [hgnm, hninv]
    rwa [heq] at this
  have hle : hua A B ≤ N.map W.subtype := by
    rw [hua, Subgroup.closure_le]
    rintro _ ⟨m, hm, m', hm', rfl⟩
    have hmW : m * n ∈ W := W.mul_mem (h.mem_pairStabilizer_of_mem_weylSet hm) hnW
    have hm'W : m' * n ∈ W := W.mul_mem (h.mem_pairStabilizer_of_mem_weylSet hm') hnW
    refine ⟨⟨m * n, hmW⟩ * (⟨m' * n, hm'W⟩ : W)⁻¹,
      N.mul_mem (hmn m hm hmW) (N.inv_mem (hmn m' hm' hm'W)), ?_⟩
    change m * n * (m' * n)⁻¹ = m * m'
    rw [mul_inv_rev, hninv, inv_eq_of_mul_eq_one_right (h.mul_self_of_mem_weylSet hm'),
      mul_assoc, ← mul_assoc n n, hnn, one_mul]
  have hdvd := Subgroup.card_dvd_of_le hle
  rw [Subgroup.card_map_of_injective W.subtype_injective] at hdvd
  exact Odd.of_dvd_nat hNodd hdvd

theorem odd_card_normalizer_inf [Finite X] :
    Odd (Nat.card (Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) :
      Subgroup X)) := by
  rw [h.normalizer_inf_eq_hua]
  exact h.odd_card_hua

theorem isPGroup : IsPGroup 2 A := by
  intro a
  refine ⟨1, Subtype.ext ?_⟩
  rw [pow_one, SubgroupClass.coe_pow, OneMemClass.coe_one, pow_two]
  exact h.sq _ a.2

theorem exists_card_eq [Finite X] : ∃ m : ℕ, 1 ≤ m ∧ Nat.card A = 2 ^ m := by
  obtain ⟨m, hm⟩ := IsPGroup.iff_card.1 h.isPGroup
  refine ⟨m, ?_, hm⟩
  rcases Nat.eq_zero_or_pos m with rfl | hpos
  · exfalso
    obtain ⟨a, ha, ha1⟩ := h.exists_ne_one
    have hbot : A = ⊥ := Subgroup.card_eq_one.1 (by rw [hm, pow_zero])
    rw [hbot] at ha
    exact ha1 ha
  · exact hpos

theorem not_two_dvd_index [Finite X] : ¬ 2 ∣ A.index := by
  obtain ⟨m, hm1, hm⟩ := h.exists_card_eq
  have hodd1 : Odd (Nat.card A + 1) := by
    rw [hm]
    exact (Nat.even_pow.2 ⟨even_two, by omega⟩).add_one
  have hodd2 := h.odd_card_normalizer_inf
  have hidx : A.index = (Nat.card A + 1) *
      Nat.card (Subgroup.normalizer (A : Set X) ⊓ Subgroup.normalizer (B : Set X) :
        Subgroup X) := by
    have h1 := A.card_mul_index
    rw [h.card_eq] at h1
    have hpos : 0 < Nat.card A := Nat.card_pos
    apply Nat.eq_of_mul_eq_mul_left hpos
    rw [h1]
    ring
  rw [hidx, ← even_iff_two_dvd, Nat.not_even_iff_odd]
  exact hodd1.mul hodd2

noncomputable def sylow [Finite X] : Sylow 2 X :=
  h.isPGroup.toSylow h.not_two_dvd_index

@[simp] theorem coe_sylow [Finite X] : (h.sylow : Subgroup X) = A :=
  IsPGroup.toSylow_coe _ _

theorem mul_self_of_isPGroup [Finite X] {x : X} (hx : IsPGroup 2 (Subgroup.zpowers x)) :
    x * x = 1 := by
  obtain ⟨P, hP⟩ := hx.exists_le_sylow
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X h.sylow P
  have hxP : x ∈ (P : Subgroup X) := hP (Subgroup.mem_zpowers x)
  rw [← hg, Sylow.coe_subgroup_smul, coe_sylow] at hxP
  have : x ∈ A.map (MulAut.conj g).toMonoidHom := hxP
  exact h.mul_self_of_mem_map_conj this

end IsElemAbRankOne

end CFSG.Timmesfeld

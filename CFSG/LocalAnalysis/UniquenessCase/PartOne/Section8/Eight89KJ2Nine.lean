module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight89KJ2Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

open Subgroup

private theorem k91j2nine_exists_order_five {K : Type} [Group K] [Finite K]
    (hK : Nat.card K = 1080) (hZ : Nat.card (center K) = 3) :
    ∃ e : K, orderOf e = 5 ∧ e ∉ center K := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  obtain ⟨e, he⟩ := exists_prime_orderOf_dvd_card' (G := K) 5 (by rw [hK]; norm_num)
  refine ⟨e, he, fun h => ?_⟩
  have := orderOf_dvd_natCard (⟨e, h⟩ : center K)
  rw [Subgroup.orderOf_mk, he, hZ] at this
  norm_num at this

private theorem k91j2nine_isPGroup_zpowers {K : Type} [Group K] (e : K) (he : orderOf e = 5) :
    IsPGroup 5 (zpowers e) :=
  IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, he, pow_one])

private theorem k91j2nine_card_modEq_fixed {K A : Type} [Group K] [Group A] [Finite K] [Finite A]
    (φ : K →* MulAut A) (e : K) (he : orderOf e = 5) :
    ∃ F : Subgroup A, (∀ a : A, a ∈ F ↔ φ e a = a) ∧ Nat.card A ≡ Nat.card F [MOD 5] := by
  let : MulAction K A := MulAction.compHom A φ
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hH := k91j2nine_isPGroup_zpowers e he
  let F : Subgroup A :=
    { carrier := {a | φ e a = a}
      mul_mem' := fun {a b} ha hb => by simp only [Set.mem_setOf_eq] at *; rw [map_mul, ha, hb]
      one_mem' := by simp
      inv_mem' := fun {a} ha => by simp only [Set.mem_setOf_eq] at *; rw [map_inv, ha] }
  have hfix : ∀ a : A, a ∈ MulAction.fixedPoints (zpowers e) A ↔ a ∈ F := by
    intro a
    constructor
    · intro h
      exact h ⟨e, mem_zpowers e⟩
    · intro h ⟨g, hg⟩
      have hle : zpowers e ≤ (MulAction.stabilizer (MulAut A) a).comap φ := by
        rw [zpowers_le]
        exact h
      exact hle hg
  have hmod := hH.card_modEq_card_fixedPoints A
  rw [Nat.card_congr (Equiv.subtypeEquivRight hfix)] at hmod
  exact ⟨F, fun a => Iff.rfl, hmod⟩

private theorem k91j2nine_card_cases {A : Type} [Group A] [Finite A] (F : Subgroup A)
    (hA : Nat.card A ∣ 16) (hmod : Nat.card A ≡ Nat.card F [MOD 5]) :
    Nat.card F = Nat.card A ∨ (Nat.card A = 16 ∧ Nat.card F = 1) := by
  have hFA : Nat.card F ∣ Nat.card A := Subgroup.card_subgroup_dvd_card F
  have hApos : 0 < Nat.card A := Nat.card_pos
  have hFpos : 0 < Nat.card F := Nat.card_pos
  have hA16 : Nat.card A ≤ 16 := Nat.le_of_dvd (by norm_num) hA
  have hFle : Nat.card F ≤ Nat.card A := Nat.le_of_dvd hApos hFA
  unfold Nat.ModEq at hmod
  interval_cases hAc : Nat.card A <;> interval_cases hFc : Nat.card F <;> omega

private theorem k91j2nine_stabilizer_eq_top {K A : Type} [Group K] [Group A]
    (φ : K →* MulAut A) (hnorm : ∀ N : Subgroup K, N.Normal → N = ⊤ ∨ N ≤ center K)
    (e : K) (heZ : e ∉ center K) (he : ∀ a : A, φ e a = a) (t : A) :
    (MulAction.stabilizer (MulAut A) t).comap φ = ⊤ := by
  have hker : φ.ker = ⊤ := by
    rcases hnorm φ.ker inferInstance with h | h
    · exact h
    · exact absurd (h (by rw [MonoidHom.mem_ker]; ext a; exact he a)) heZ
  rw [eq_top_iff]
  intro k _
  rw [mem_comap, MulAction.mem_stabilizer_iff]
  have : k ∈ φ.ker := hker ▸ Subgroup.mem_top k
  rw [MonoidHom.mem_ker] at this
  rw [this]
  rfl

private theorem k91j2nine_orbit_dvd {K A : Type} [Group K] [Group A] [Finite K] [Finite A]
    (φ : K →* MulAut A) (hK : Nat.card K = 1080) (hA16 : Nat.card A = 16)
    (e : K) (he : orderOf e = 5) (hF1 : ∀ a : A, φ e a = a → a = 1) (t : A) (ht : t ≠ 1) :
    9 ∣ Nat.card ((MulAction.stabilizer (MulAut A) t).comap φ) := by
  let : MulAction K A := MulAction.compHom A φ
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hH := k91j2nine_isPGroup_zpowers e he
  have hstab : (MulAction.stabilizer K t) = (MulAction.stabilizer (MulAut A) t).comap φ := rfl
  rw [← hstab]
  have hos := (MulAction.stabilizer K t).index_mul_card
  rw [MulAction.index_stabilizer, hK] at hos
  have hnot1 : ∀ k : K, k • t ≠ 1 := by
    intro k hk
    apply ht
    have h1 : φ k t = 1 := hk
    have := congrArg (φ k⁻¹) h1
    rwa [map_one, ← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one,
      MulAut.one_apply] at this
  set O := MulAction.orbit K t
  have hfixO : Nat.card (MulAction.fixedPoints (zpowers e) O) = 0 := by
    rw [Nat.card_eq_zero]
    left
    constructor
    rintro ⟨⟨o, ho⟩, hof⟩
    have h1 : φ e o = o := by
      have := hof ⟨e, mem_zpowers e⟩
      exact congrArg Subtype.val this
    obtain ⟨k, hk⟩ := ho
    exact hnot1 k ((show k • t = o from hk).trans (hF1 o h1))
  have hmodO := hH.card_modEq_card_fixedPoints O
  rw [hfixO, Nat.card_coe_set_eq] at hmodO
  have hOlt : O.ncard < 16 := by
    have hss : O ⊂ Set.univ := by
      rw [Set.ssubset_univ_iff]
      intro h
      obtain ⟨k, hk⟩ := (h ▸ Set.mem_univ 1 : (1 : A) ∈ O)
      exact hnot1 k hk
    have := Set.ncard_lt_ncard hss
    rwa [Set.ncard_univ, hA16] at this
  have hOpos : 0 < O.ncard := by
    rw [Set.ncard_pos]
    exact ⟨t, MulAction.mem_orbit_self t⟩
  unfold Nat.ModEq at hmodO
  interval_cases hO : O.ncard <;> omega

theorem j2AutCore_nine_dvd_card_stabilizer {K A : Type} [Group K] [Group A] [Finite K] [Finite A]
    (φ : K →* MulAut A) (hK : Nat.card K = 1080)
    (hnorm : ∀ N : Subgroup K, N.Normal → N = ⊤ ∨ N ≤ center K)
    (hZ : Nat.card (center K) = 3) (hA : Nat.card A ∣ 16) (t : A) (ht : t ≠ 1) :
    9 ∣ Nat.card ((MulAction.stabilizer (MulAut A) t).comap φ) := by
  obtain ⟨e, he, heZ⟩ := k91j2nine_exists_order_five hK hZ
  obtain ⟨F, hF, hmod⟩ := k91j2nine_card_modEq_fixed φ e he
  rcases k91j2nine_card_cases F hA hmod with hc | ⟨hc16, hc1⟩
  · have hFtop : F = ⊤ := Subgroup.eq_top_of_card_eq F hc
    rw [k91j2nine_stabilizer_eq_top φ hnorm e heZ
      (fun a => (hF a).1 (hFtop ▸ Subgroup.mem_top a)) t, Subgroup.card_top, hK]
    norm_num
  · refine k91j2nine_orbit_dvd φ hK hc16 e he (fun a ha => ?_) t ht
    have hFbot : F = ⊥ := Subgroup.eq_bot_of_card_eq F hc1
    have : a ∈ F := (hF a).2 ha
    rwa [hFbot, Subgroup.mem_bot] at this

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.KInputs

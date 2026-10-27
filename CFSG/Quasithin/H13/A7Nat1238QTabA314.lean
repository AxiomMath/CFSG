module

public import CFSG.Quasithin.H13.A7Nat1238QTabOrd
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyP2Cover
public import CFSG.Quasithin.Background.A3Structure314Defs

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open scoped commutatorElement

theorem not_isSolvable_of_isQuasisimple_qtab {Q : Type*} [Group Q] (hQ : CFSG.IsQuasisimple Q) :
    ¬ Group.IsSolvable Q := by
  obtain ⟨hperf, -, a, b, hab⟩ := hQ
  have : Nontrivial Q := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have : Subsingleton (Q ⧸ center Q) := (QuotientGroup.mk'_surjective (center Q)).subsingleton
    exact hab (Subsingleton.elim _ _)
  exact Group.IsPerfect.not_isSolvable Q

theorem oddCore_eq_center_of_quasisimple {L : Type} [Group L] [Finite L]
    (hq : CFSG.IsQuasisimple L) (hZ : Odd (Nat.card (center L))) :
    CFSG.oddCore L = center L := by
  apply le_antisymm
  · rcases CFSG.LocalCores.quasisimple_normal_subgroups hq (CFSG.oddCore_normal (G := L)) with
      h | h
    · exfalso
      have hs := A312.oddCore_isSolvable L
      rw [h] at hs
      exact not_isSolvable_of_isQuasisimple_qtab hq
        (Group.isSolvable_of_surjective
          (f := (Subgroup.topEquiv : ↥(⊤ : Subgroup L) ≃* L).toMonoidHom)
          Subgroup.topEquiv.surjective)
    · exact h
  · exact le_sSup ⟨inferInstance, hZ⟩

theorem not_isSimpleGroup_SL_two {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) :
    ¬ IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
  intro hs
  have : Fact (Even (Fintype.card (Fin 2))) := ⟨by decide⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p))) with h | h
  · have hc : (-1 : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) ∈
        center (Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      rw [mul_neg_one, neg_one_mul]
    rw [h, Subgroup.mem_bot] at hc
    have h00 := congrArg (fun g : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) =>
      (g : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0) hc
    simp only [Matrix.SpecialLinearGroup.coe_neg, Matrix.SpecialLinearGroup.coe_one,
      Matrix.neg_apply, Matrix.one_apply_eq] at h00
    have h2 : ((2 : ℕ) : ZMod p) = 0 := by
      rw [Nat.cast_ofNat]
      linear_combination -h00
    rw [ZMod.natCast_eq_zero_iff] at h2
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 h2)
  · have : Fact (1 < p) := ⟨(Fact.out : p.Prime).one_lt⟩
    let u : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      ⟨!![1, 1; 0, 1], by simp [Matrix.det_fin_two]⟩
    let l : Matrix.SpecialLinearGroup (Fin 2) (ZMod p) :=
      ⟨!![1, 0; 1, 1], by simp [Matrix.det_fin_two]⟩
    have hcomm : l * u = u * l := Subgroup.mem_center_iff.1 (h ▸ mem_top u : u ∈ _) l
    have h00 : ((l * u : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
        Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 =
        ((u * l : Matrix.SpecialLinearGroup (Fin 2) (ZMod p)) :
          Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 := by rw [hcomm]
    change (!![1, 0; 1, 1] * !![1, 1; 0, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 =
      (!![1, 1; 0, 1] * !![1, 0; 1, 1] : Matrix (Fin 2) (Fin 2) (ZMod p)) 0 0 at h00
    simp [Matrix.mul_apply, Fin.sum_univ_two] at h00

theorem commutatorElement_mul_center {Q : Type*} [Group Q] {b b' z z' : Q} (hz : z ∈ center Q)
    (hz' : z' ∈ center Q) : ⁅b * z, b' * z'⁆ = ⁅b, b'⁆ := by
  have h1 : ∀ y : Q, ⁅b * z, y⁆ = ⁅b, y⁆ := fun y => by
    have hzy : z * y = y * z := (Subgroup.mem_center_iff.1 hz y).symm
    simp only [commutatorElement_def, mul_inv_rev]
    calc b * z * y * (z⁻¹ * b⁻¹) * y⁻¹ = b * (z * y) * z⁻¹ * b⁻¹ * y⁻¹ := by group
      _ = b * (y * z) * z⁻¹ * b⁻¹ * y⁻¹ := by rw [hzy]
      _ = b * y * b⁻¹ * y⁻¹ := by group
  have hzb : z' * b⁻¹ = b⁻¹ * z' := (Subgroup.mem_center_iff.1 hz' b⁻¹).symm
  rw [h1]
  simp only [commutatorElement_def, mul_inv_rev]
  calc b * (b' * z') * b⁻¹ * (z'⁻¹ * b'⁻¹) = b * b' * (z' * b⁻¹) * z'⁻¹ * b'⁻¹ := by group
    _ = b * b' * (b⁻¹ * z') * z'⁻¹ * b'⁻¹ := by rw [hzb]
    _ = b * b' * b⁻¹ * b'⁻¹ := by group

theorem not_a314_nonquasi {Q : Type} [Group Q] [Finite Q] {B L : Subgroup Q} (hBL : B < L)
    (hq : CFSG.IsQuasisimple ↥L) (hZ : Odd (Nat.card (center ↥L))) :
    ¬ (L = B ⊔ oddCoreSub L) ∧ ∀ p : ℕ, p.Prime → p ≠ 2 → ¬ IsSL2 p (↥L ⧸ CFSG.oddCore ↥L) := by
  have hO := oddCore_eq_center_of_quasisimple hq hZ
  refine ⟨fun h => ?_, fun p hp hp2 h => ?_⟩
  · have hBL' : B ≤ L := hBL.le
    set B' := B.subgroupOf L with hB'
    have htop : (⊤ : Subgroup ↥L) = B' ⊔ center ↥L := by
      have h1 := congrArg (fun H : Subgroup Q => H.subgroupOf L) h
      rw [Subgroup.subgroupOf_self, Subgroup.subgroupOf_sup hBL' (Subgroup.map_subtype_le _),
        A4.subgroupOf_map_subtype', hO] at h1
      exact h1
    have hZN : center ↥L ≤ normalizer (B' : Set ↥L) := by
      intro z hz
      rw [mem_normalizer_iff]
      intro b
      rw [← Subgroup.mem_center_iff.1 hz b, mul_inv_cancel_right]
    have hcomm : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ ≤ B' := by
      rw [Subgroup.commutator_le]
      intro x hx y hy
      rw [htop] at hx hy
      obtain ⟨b, hb, z, hz, rfl⟩ := Setup.Family.mem_sup_of_le_normalizer hZN hx
      obtain ⟨b', hb', z', hz', rfl⟩ := Setup.Family.mem_sup_of_le_normalizer hZN hy
      rw [commutatorElement_mul_center hz hz']
      exact B'.mul_mem (B'.mul_mem (B'.mul_mem hb hb') (B'.inv_mem hb)) (B'.inv_mem hb')
    have hperf : ⁅(⊤ : Subgroup ↥L), (⊤ : Subgroup ↥L)⁆ = ⊤ := hq.1.commutator_eq_top
    rw [hperf] at hcomm
    apply hBL.ne
    apply le_antisymm hBL'
    intro x hx
    have := hcomm (mem_top (⟨x, hx⟩ : ↥L))
    exact Subgroup.mem_subgroupOf.1 this
  · obtain ⟨e⟩ := h
    have : Fact p.Prime := ⟨hp⟩
    have : IsSimpleGroup (↥L ⧸ center ↥L) := hq.2.1
    exact not_isSimpleGroup_SL_two hp2
      (e.symm.trans (QuotientGroup.quotientMulEquivOfEq hO)).isSimpleGroup

theorem eleven_le_of_sq_mod_five {p : ℕ} (hp : p.Prime) (h : p ^ 2 % 5 = 1) : 11 ≤ p := by
  by_contra hlt
  push Not at hlt
  interval_cases p <;> revert hp h <;> decide

theorem a314_case_two_of_list
    {Q : Type} [Group Q] [Finite Q] {T B L : Subgroup Q} (h : A314Statement T B L)
    (hBL : B < L) (hq : CFSG.IsQuasisimple ↥L) (hZ : Odd (Nat.card (center ↥L)))
    (hlist : List1222 ↥L) :
    IsAlt 5 ↥B ∧ (IsAlt 7 ↥L ∨ IsHat ↥L (alternatingGroup (Fin 7))) ∧
      StabilizesFivePoints B L := by
  obtain ⟨h13, h14⟩ := not_a314_nonquasi hBL hq hZ
  unfold A314Statement at h
  rcases h with h1 | h2 | h3 | h4 | h5 | h6 | h7 | h8 | h9 | h10 | h11 | h12 | h13' | h14'
  · obtain ⟨-, -, hL, -⟩ := h1
    rcases hL with h | h | h | h | h
    · exact absurd hlist (not_list1222_of_psl_three_four hZ h)
    · exact absurd hlist (not_list1222_of_sl_three_four hZ h)
    · exact absurd hlist (not_list1222_of_psp_four_four hZ h)
    · exact absurd hlist (not_list1222_of_g_two_four hZ h)
    · exact absurd hlist (not_list1222_of_triality_four hZ h)
  · exact h2
  · obtain ⟨-, hL⟩ := h3
    rcases hL with h | ⟨p, hp, hp5, hp8, h⟩
    · exact absurd hlist (not_list1222_of_psl_two_twentyfive hZ h)
    · exact absurd hlist
        (not_list1222_of_psl_two_prime hp (eleven_le_of_sq_mod_five hp hp5) hp8 h)
  · obtain ⟨-, ⟨s, hL⟩, -⟩ := h4
    cases s
    · rcases hL with h | h
      · exact absurd hlist (not_list1222_of_psu_three_five hZ h)
      · exact absurd hlist (not_list1222_of_su_three_five hZ h)
    · rcases hL with h | h
      · exact absurd hlist (not_list1222_of_psl_three_five hZ h)
      · exact absurd hlist (not_list1222_of_sl_three_five hZ h)
  · obtain ⟨-, hL, -⟩ := h5
    rcases hL with h | h
    · exact absurd hlist (not_list1222_of_psl_three_five hZ h)
    · exact absurd hlist (not_list1222_of_sl_three_five hZ h)
  · obtain ⟨-, -, -, hL⟩ := h6
    rcases hL with h | h
    · exact absurd hlist (not_list1222_of_m22 hZ h)
    · exact absurd hlist (not_list1222_of_m22_hat hZ h)
  · obtain ⟨-, -, -, hL⟩ := h7
    exact absurd hlist (not_list1222_of_m23 hZ hL)
  · obtain ⟨-, hL, -⟩ := h8
    exact absurd hlist (not_list1222_of_j1 hZ hL)
  · obtain ⟨-, hL, -⟩ := h9
    exact absurd hlist (not_list1222_of_j2 hZ hL)
  · obtain ⟨-, -, hL⟩ := h10
    exact absurd hlist (not_list1222_of_j4 hZ hL)
  · obtain ⟨-, hL, -⟩ := h11
    exact absurd hlist (not_list1222_of_hs hZ hL)
  · obtain ⟨-, -, hL, -⟩ := h12
    exact absurd hlist (not_list1222_of_ru hZ hL)
  · exact absurd h13'.2 h13
  · obtain ⟨-, p, hp, hp5, -, hL⟩ := h14'
    exact absurd hL (h14 p hp (by rintro rfl; norm_num at hp5))

end CFSG.Quasithin.H13.A7

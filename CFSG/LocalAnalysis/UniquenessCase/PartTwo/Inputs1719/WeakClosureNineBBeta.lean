module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBBlocks
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineBSetting
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFifteenOuterPGL
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.WeakClosureNineNA6Gen

public section

namespace CFSG.LocalAnalysis.WeakClosure81.NGM

open Subgroup CFSG.Quasithin

structure IsBeta {X : Type} [Group X] (L S : Subgroup X) (β : MulAut L →* Equiv.Perm (Fin 8)) :
    Prop where
  inj : Function.Injective β
  mem : ∀ φ, β φ ∈ NFF7.G0
  inn : ∀ l : L, β (MulAut.conj l) ∈ H0
  innSurj : ∀ h ∈ H0, ∃ l : L, β (MulAut.conj l) = h
  syl : ∀ l : L, (l : X) ∈ S → β (MulAut.conj l) ∈ D
  sylSurj : ∀ d ∈ D, ∃ l : L, (l : X) ∈ S ∧ β (MulAut.conj l) = d

section

variable {L : Type} [Group L]

theorem conj_injective_of_center (h : center L = ⊥) :
    Function.Injective (MulAut.conj : L →* MulAut L) := by
  rw [injective_iff_map_eq_one]
  intro l hl
  have hc : l ∈ center L := by
    rw [mem_center_iff]
    intro g
    have h1 := congrArg (fun φ : MulAut L => φ g) hl
    simp only [MulAut.conj_apply, MulAut.one_apply] at h1
    calc g * l = l * g * l⁻¹ * l := by rw [h1]
      _ = l * g := by group
  rw [h, mem_bot] at hc
  exact hc

theorem conj_conj_inv (l m : L) :
    MulAut.conj (MulAut.conj l⁻¹) (MulAut.conj m) = MulAut.conj (l⁻¹ * m * l) := by
  rw [MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul, inv_inv]

end

theorem range_eq_H0 {L : Type} [Group L] [Finite L] {β₀ : MulAut L →* Equiv.Perm (Fin 8)}
    (hβ₀ : Function.Injective β₀) (hr : ∀ g ∈ NFF7.G0, ∃ φ, β₀ φ = g)
    (hcj : Function.Injective (MulAut.conj : L →* MulAut L)) (hL : Nat.card L = 168)
    (hA : Nat.card (MulAut L) = 336) :
    (β₀.comp (MulAut.conj : L →* MulAut L)).range = H0 := by
  set α₀ := β₀.comp (MulAut.conj : L →* MulAut L)
  have hα₀ : Function.Injective α₀ := hβ₀.comp hcj
  have hcardr : Nat.card α₀.range = 168 := by
    rw [← hL]
    exact Nat.card_congr (MonoidHom.ofInjective hα₀).toEquiv.symm
  have hidx : (MulAut.conj : L →* MulAut L).range.index = 2 := by
    have h1 := (MulAut.conj : L →* MulAut L).range.index_mul_card
    have h2 : Nat.card (MulAut.conj : L →* MulAut L).range = 168 := by
      rw [← hL]
      exact Nat.card_congr (MonoidHom.ofInjective hcj).toEquiv.symm
    rw [h2, hA] at h1
    omega
  have hsq : ∀ g ∈ NFF7.G0, g * g ∈ α₀.range := by
    intro g hg
    obtain ⟨φ, rfl⟩ := hr g hg
    obtain ⟨l, hl⟩ := mul_self_mem_of_index_two hidx φ
    exact ⟨l, by simp [α₀, hl]⟩
  have hle : H0 ≤ α₀.range := by
    rw [H0, closure_le]
    intro x hx
    simp only [Set.mem_setOf_eq, List.mem_cons, List.not_mem_nil, or_false] at hx
    rcases hx with rfl | rfl
    · rw [g1_sq]
      exact hsq _ (pow_mem g1_mem_G0 4)
    · rw [pw_sq]
      exact hsq _ pw_mem_G0
  exact (eq_of_le_of_card_ge hle (by rw [hcardr, card_H0])).symm

theorem isSylowIn_subgroupOf {X : Type} [Group X] {S L : Subgroup X} (hS : IsSylowIn 2 S L) :
    IsSylowIn 2 (S.subgroupOf L) ⊤ :=
  ⟨le_top, hS.isPGroup.of_equiv (subgroupOfEquivOfLe hS.le).symm, by
    rw [relIndex_top_right]
    exact hS.not_dvd_relIndex⟩

theorem exists_beta0 {X : Type} [Group X] {L : Subgroup X}
    (hL : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL3 ↥L 1) :
    ∃ β₀ : MulAut ↥L →* Equiv.Perm (Fin 8), Function.Injective β₀ ∧ (∀ φ, β₀ φ ∈ NFF7.G0) ∧
      Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) ∧
      (β₀.comp (MulAut.conj : ↥L →* MulAut ↥L)).range = H0 := by
  have h27 : CFSG.Blueprint.LieModel ↥L .PSL 2 7 1 :=
    CFSG.LocalAnalysis.ComponentInitial.PSL3_two_PSL2_seven_paired_isomorphism _ hL
  have hP : CFSG.Quasithin.F6.IsPGL2 7 (MulAut ↥L) :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17.isPGL2_mulAut_of_isL2Over17_seven
      ⟨7, 1, Nat.prime_seven, by norm_num, by norm_num, le_rfl, h27⟩
  obtain ⟨ψ⟩ := NFF7.nonempty_equiv_pgl2_zmod hP
  have hβ₀ : Function.Injective (NFF7.rho.comp ψ.toMonoidHom) :=
    NFF7.rho_injective.comp ψ.injective
  have hβ₀s : ∀ g ∈ NFF7.G0, ∃ φ, NFF7.rho.comp ψ.toMonoidHom φ = g := by
    intro g hg
    rw [← NFF7.rho_range] at hg
    obtain ⟨y, rfl⟩ := hg
    exact ⟨ψ.symm y, by simp⟩
  have hcard : Nat.card ↥L = 168 :=
    CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_three_two hL
  have hsimp : IsSimpleGroup ↥L := (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 1
    (CFSG.Blueprint.LieModel.statedClassicalModel hL (by decide))).2
  have hnc : ¬ IsMulCommutative ↥L := by
    intro h
    have hp := Group.is_simple_iff_prime_card.mp hsimp
    rw [hcard] at hp
    norm_num at hp
  have hcj : Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) :=
    conj_injective_of_center (TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hnc)
  have : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  exact ⟨_, hβ₀, fun φ => NFF7.rho_range ▸ ⟨ψ φ, rfl⟩, hcj, range_eq_H0 hβ₀ hβ₀s hcj hcard
    (CFSG.SeitzReduction.LinearPilot.card_mulAut_of_lieModel_PSL_three_two hL)⟩

theorem exists_isBeta {X : Type} [Group X] {L S : Subgroup X}
    (hL : CFSG.LocalAnalysis.UniquenessCase.UC22.IsL3 ↥L 1) (hS : IsSylowIn 2 S L) :
    ∃ β, IsBeta L S β := by
  obtain ⟨β₀, hβ₀, hβ₀m, hcj, hrange⟩ := exists_beta0 hL
  set α₀ := β₀.comp (MulAut.conj : ↥L →* MulAut ↥L) with hα₀def
  have hα₀ : Function.Injective α₀ := hβ₀.comp hcj
  have hcard : Nat.card ↥L = 168 :=
    CFSG.SeitzReduction.LinearPilot.card_of_lieModel_PSL_three_two hL
  have : Finite ↥L := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  set Q : Subgroup ↥L := D.comap α₀ with hQ
  have hQcard : Nat.card Q = 8 := by
    rw [← card_D, ← map_comap_eq_self (hrange ▸ D_le_H0 : D ≤ α₀.range),
      card_map_of_injective hα₀]
  have hQsyl : IsSylowIn 2 Q ⊤ := by
    refine ⟨le_top, IsPGroup.of_card (n := 3) (by rw [hQcard]; norm_num), ?_⟩
    rw [relIndex_top_right]
    have h1 := Q.index_mul_card
    rw [hQcard, hcard] at h1
    rw [show Q.index = 21 by omega]
    decide
  obtain ⟨l, hl⟩ := NFA6.exists_eq_map_conj (isSylowIn_subgroupOf hS) hQsyl
  refine ⟨β₀.comp (MulAut.conj (MulAut.conj l⁻¹)).toMonoidHom, ?_⟩
  have hβc : ∀ m : ↥L, β₀.comp (MulAut.conj (MulAut.conj l⁻¹)).toMonoidHom (MulAut.conj m) =
      α₀ (l⁻¹ * m * l) := by
    intro m
    rw [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, conj_conj_inv]
    rfl
  refine ⟨hβ₀.comp (MulAut.conj _).injective, fun φ => hβ₀m _, fun m => ?_, fun h hh => ?_,
    fun m hm => ?_, fun d hd => ?_⟩
  · rw [hβc, ← hrange]
    exact ⟨_, rfl⟩
  · rw [← hrange] at hh
    obtain ⟨m₀, rfl⟩ := hh
    exact ⟨l * m₀ * l⁻¹, by rw [hβc]; congr 1; group⟩
  · have hm' : m ∈ S.subgroupOf L := hm
    rw [hl, mem_map_conj_iff] at hm'
    rw [hβc]
    exact hm'
  · obtain ⟨q, rfl⟩ : d ∈ α₀.range := hrange ▸ D_le_H0 hd
    have hq : q ∈ Q := hd
    refine ⟨l * q * l⁻¹, ?_, ?_⟩
    · have h1 : l * q * l⁻¹ ∈ S.subgroupOf L := by
        rw [hl, mem_map_conj_iff]
        simpa [mul_assoc] using hq
      exact h1
    · rw [hβc]
      congr 1
      group

end CFSG.LocalAnalysis.WeakClosure81.NGM

module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94Cnt
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec9P4F94Iso

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

namespace Sec9Cfg

variable {L : ZLab Γ G} (S : Sec9Cfg L)

theorem eq_of_le_of_index_eq {A : Type*} [Group A] {N M : Subgroup A} (h : N ≤ M)
    (hi : N.index = M.index) (hfin : M.index ≠ 0) : N = M := by
  have h1 := Subgroup.relIndex_mul_index h
  rw [hi] at h1
  have h2 : N.relIndex M = 1 := by
    have := Nat.eq_of_mul_eq_mul_right (Nat.pos_of_ne_zero hfin) (h1.trans (one_mul _).symm)
    exact this
  exact le_antisymm h (Subgroup.relIndex_eq_one.1 h2)

theorem exists_mid_iso (F : FanTree Γ G) (h7 : Fan7 F L) (h65 : Fan65 F) (h81 : Fan81 F L)
    (h82 : Fan82 F L) (h83b : Fan83b F L) (h512 : Fan512 F L)
    (hw : S.w ∈ nbrStab Γ G S.beta) (hwA : S.wA 1 ∈ nbrStab Γ G S.beta)
    (hc : S.c ∈ nbrStab Γ G S.beta)
    (htop : 8 * Nat.card S.D.calpha ≤ (ballStab Γ G 2 S.beta).relIndex
      (Subgroup.closure ({S.w, S.wA 1, S.c} : Set G) ⊔ ballStab Γ G 2 S.beta)) :
    ∃ φ : ↥(ballStab Γ G 2 S.beta) →* (Fin 3 → Multiplicative (ZMod 2)),
      Function.Surjective φ ∧
        φ.ker = (ballStab Γ G 3 S.beta).subgroupOf (ballStab Γ G 2 S.beta) := by
  have h71c : Fan71c F L := h7.2.2.1
  obtain ⟨-, h8, -⟩ := S.fan94_exact_of F h7 h65 h81 h82 h83b h512 hw hwA hc htop
  obtain ⟨s, hs⟩ := S.exists_swap_hom F h71c
  have hrange : s.range = ⊤ := by
    have := S.swap_range_eq_top F h71c h81 h83b h512 hs (H := ballStab Γ G 2 S.beta) le_rfl
      (fun k => S.yMu_mem_ballStab_two F h71c h81 k) (S.ubs_mem_ballStab_two F h71c)
    exact this
  have hker : (ballStab Γ G 3 S.beta).subgroupOf (ballStab Γ G 2 S.beta) ≤ s.ker := by
    intro g hg
    rw [MonoidHom.mem_ker]
    funext i
    show s g i = 1
    rw [hs]
    exact mem_ballStab.1 (Subgroup.mem_subgroupOf.1 hg) _ (by rw [S.dist_beta_muV F h71c])
  have hfin : Finite ↥(ballStab Γ G 2 S.beta) :=
    have : Finite ↥(MulAction.stabilizer G S.beta) := F.loc_finite S.beta
    Finite.of_injective (Subgroup.inclusion S.ballStab_two_le_stabilizer)
      (Subgroup.inclusion_injective _)
  have hsker : s.ker.index = 8 := by
    rw [Subgroup.index_ker, hrange, Subgroup.card_top, Nat.card_eq_fintype_card]
    decide
  have hker_eq : (ballStab Γ G 3 S.beta).subgroupOf (ballStab Γ G 2 S.beta) = s.ker :=
    eq_of_le_of_index_eq hker (by
      show (ballStab Γ G 3 S.beta).relIndex (ballStab Γ G 2 S.beta) = _
      rw [h8, hsker]) (by rw [hsker]; norm_num)
  refine ⟨(MulEquiv.piCongrRight fun _ => unitsZMod3Equiv).toMonoidHom.comp s, ?_, ?_⟩
  · exact (MulEquiv.piCongrRight fun _ => unitsZMod3Equiv).surjective.comp
      (MonoidHom.range_eq_top.1 hrange)
  · rw [MonoidHom.ker_comp_of_injective _ _ (MulEquiv.piCongrRight fun _ =>
      unitsZMod3Equiv).injective, hker_eq]

end Sec9Cfg

end CFSG.Quasithin.Fan86

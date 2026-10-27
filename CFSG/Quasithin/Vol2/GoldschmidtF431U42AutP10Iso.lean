module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Gam
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutP10Ord
public import CFSG.Quasithin.H13.ModelsLinear

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.CosetTable
open scoped MatrixGroups

theorem isSimpleGroup_psl_four_three : IsSimpleGroup PSL(4, ZMod 3) :=
  CFSG.BenderSuzuki.External.huppert_II_6_13 (K := ZMod 3) 4 (by norm_num)
    (Or.inl (by norm_num)) (Or.inl (by norm_num))

theorem p10ModelHom_bijective : Function.Bijective p10ModelHom := by
  have h := card_PG_p10_le
  have := h.1
  exact p10ModelHom_surjective.bijective_of_nat_card_le (by rw [card_psl_four_three]; exact h.2)

theorem isSimpleGroup_PG_p10 : IsSimpleGroup (PG 7 p10Ws) := by
  have := isSimpleGroup_psl_four_three
  exact (MulEquiv.ofBijective p10ModelHom p10ModelHom_bijective).isSimpleGroup

namespace RhoData

variable {G : Type} [Group G] [Finite G] (d : RhoData G)

theorem nonempty_mulEquiv
    (hH : Nat.card d.H = 576) (hG : d.ι.range ⊔ d.H = ⊤)
    (hnt : ∃ g : G, g ≠ 1) : Nonempty (G ≃* PSL(4, ZMod 3)) := by
  have hsurj := d.toG_surjective hH hG
  have := isSimpleGroup_PG_p10
  have hker : (d.toG hH).ker = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (d.toG hH).ker with h | h
    · exact h
    · exfalso
      obtain ⟨a, ha⟩ := hnt
      obtain ⟨x, rfl⟩ := hsurj a
      exact ha (MonoidHom.mem_ker.1 (h ▸ Subgroup.mem_top x))
  have hbij : Function.Bijective (d.toG hH) :=
    ⟨(MonoidHom.ker_eq_bot_iff _).1 hker, hsurj⟩
  exact ⟨(MulEquiv.ofBijective (d.toG hH) hbij).symm.trans
    (MulEquiv.ofBijective p10ModelHom p10ModelHom_bijective)⟩

end RhoData

end CFSG.Quasithin.H13.F431.U42Aut

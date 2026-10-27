module

public import CFSG.Sporadic.Co2Jc.Cocycle
public import CFSG.Sporadic.Co2Jc.Derived
public import CFSG.Sporadic.Co2Jc.Forms
public import CFSG.Sporadic.Co2Jc.NoZ4
public import CFSG.Sporadic.Co2Jc.Offenders
public import CFSG.Sporadic.Co2Jc.Simple

public section

namespace CFSG.Sporadic.Co2Jc

open CFSG.Sporadic.Co2Smith Subgroup
open CFSG.EvenSporadicStandard.Co2Std.Exclusion

theorem isElementaryAbelian_Jc :
    IsElementaryAbelian 2 ↥Jc where
  is_comm := ⟨fun a b => Subtype.ext (Jc_comm a.2 b.2)⟩
  exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun x => by
    obtain ⟨m, -, rfl⟩ := exists_jcA x
    rw [sq, ← jcA_xor, Nat.xor_self, jcA_zero]

theorem commutator_Qj_le : ⁅Qj, Qj⁆ ≤ Qj :=
  commutator_le.2 fun g hg h hh => by
    rw [commutatorElement_def]
    exact mul_mem (mul_mem (mul_mem hg hh) (inv_mem hg)) (inv_mem hh)


theorem moduleFacts_Qj : @ModuleFacts ↥Jc Jc.toGroup Qj tA where
  card := card_Jc
  elemAb := isElementaryAbelian_Jc
  card_Q := card_Qj
  invariant_ncard _ h1 hS := invariant_ncard_Qj h1 hS
  overgroup _ hQX h31 h37 _ := eq_Qj_of_le hQX h31 h37
  normalizer_derived _ hg :=
    mem_Qj_of_normalizes qWord_g1w_mem qWord_g2w_mem commutator_Qj_le hg
  derived_simple := isSimpleGroup_commutator_Qj commutator_Qj_eq qA_one_mem_commutator
    qA_zero_mul_self_mem_commutator
  card_derived := card_commutator_Qj
  centralizer_derived := by
    rw [eq_bot_iff]
    rintro g ⟨-, hg⟩
    exact (mem_bot).2 <| eq_one_of_commute qWord_g1w_mem qWord_g2w_mem
      qA_one_mem_commutator qA_zero_mul_self_mem_commutator
      fun h hh => (mem_centralizer_iff.1 hg h hh).symm
  irreducible_derived _ hU := eq_bot_or_eq_top_of_invariant qWord_g1w_mem qWord_g2w_mem hU
  endo_derived _ hf := eq_one_or_eq_id_of_commute qWord_g1w_mem qWord_g2w_mem
    qA_one_mem_commutator qA_zero_mul_self_mem_commutator hf
  noOffenders := noOffenders_Qj
  noBilin := noBilin_Qj
  dual_cocycle := dual_cocycle_Qj
  noWedge := noWedge_Qj
  noZ4 := noZ4_Qj
  split_of_fixed := split_of_fixed_Qj

end CFSG.Sporadic.Co2Jc

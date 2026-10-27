module

public import CFSG.LocalAnalysis.WeakClosure81.EightThirteenPCitedAut
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarU3Outer
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.LocalAnalysis.SeitzReduction.RankOneHypStarDef

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsU3)
open CFSG.GH74.Uniqueness.Bender
open CFSG.SeitzReduction.RankOne

private theorem wccu_benderType_of_isU3 {M : Type} [Group M] [Finite M] (h : IsU3 M 2) :
    BenderType M 2 3 5 := by
  obtain ⟨e₁⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_psu3_of_lieModel_PSU3 h
  let e : M ≃* CFSG.Theory.Comparator.PSU3Model 2 := e₁
  have h_eq : (2 ^ 2 + 1) / Nat.gcd 3 (2 ^ 2 + 1) = 5 := by norm_num
  simpa [h_eq] using BenderType.unitary 2 le_rfl e

private theorem wccu_sq_one_commute {C : Type*} [Group C] (h : ∀ x : C, x * x = 1)
    (a b : C) : a * b = b * a := by
  have ha : a⁻¹ = a := inv_eq_of_mul_eq_one_right (h a)
  have hb : b⁻¹ = b := inv_eq_of_mul_eq_one_right (h b)
  have hab : (a * b)⁻¹ = a * b := inv_eq_of_mul_eq_one_right (h (a * b))
  calc a * b = (a * b)⁻¹ := hab.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [ha, hb]

private theorem wccu_fixed_exponent_two_implies_abelian {M : Type} [Group M] {β : MulAut M}
    (h : ∀ x : M, β x = x → x * x = 1) :
    ∀ a b : autFixed β, a * b = b * a := by
  have hsq : ∀ g : autFixed β, g * g = 1 := by
    intro g
    apply Subtype.ext
    simpa using h (g : M) ((mem_autFixed_iff).mp g.2)
  exact wccu_sq_one_commute hsq

private theorem wccu_simple_no_normal_two {C : Type*} [Group C] [Finite C] [IsSimpleGroup C]
    (hnab : ∃ a b : C, a * b ≠ b * a) {E : Subgroup C} [E.Normal] (hEp : IsPGroup 2 E) :
    E = ⊥ := by
  rcases Subgroup.Normal.eq_bot_or_eq_top E with h | h
  · exact h
  · exfalso
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hEp' : IsPGroup 2 (⊤ : Subgroup C) := h ▸ hEp
    have hCp : IsPGroup 2 C := hEp'.of_equiv Subgroup.topEquiv
    haveI : Group.IsNilpotent C := hCp.isNilpotent
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (mul_comm a b)

private theorem wccu_fixed_unitary_isSimple {M : Type} [Group M] [Finite M] (h : IsU3 M 2)
    (β : MulAut M) (hβ : β * β = 1) (hout : ¬ ∃ g : M, ∀ x : M, β x = g * x * g⁻¹) :
    IsSimpleGroup (autFixed β) := by
  have hB : BenderType M 2 3 5 := wccu_benderType_of_isU3 h
  obtain ⟨φ⟩ := hB.fixed_unitary β hβ hout
  have hpsl : IsSimpleGroup (CFSG.Theory.Comparator.PSL2Model 2) :=
    (psl2Model_simple_nonabelian (f := 2) (by norm_num)).1
  haveI := hpsl
  exact φ.isSimpleGroup

private theorem wccu_fixed_unitary_nonabelian {M : Type} [Group M] [Finite M] (h : IsU3 M 2)
    (β : MulAut M) (hβ : β * β = 1) (hout : ¬ ∃ g : M, ∀ x : M, β x = g * x * g⁻¹) :
    ∃ a b : autFixed β, a * b ≠ b * a := by
  have hB : BenderType M 2 3 5 := wccu_benderType_of_isU3 h
  obtain ⟨φ⟩ := hB.fixed_unitary β hβ hout
  obtain ⟨-, a, b, hab⟩ := psl2Model_simple_nonabelian (f := 2) (by norm_num)
  refine ⟨φ.symm a, φ.symm b, fun hh => hab ?_⟩
  have := congrArg φ hh
  simpa only [map_mul, MulEquiv.apply_symm_apply] using this

theorem outerFixedNotElem_isU3 {M : Type} [Group M] [Finite M] (h : IsU3 M 2) :
    OuterFixedNotElem M := by
  intro β hβ hout
  obtain ⟨a, b, hab⟩ := wccu_fixed_unitary_nonabelian h β hβ hout
  by_contra hcon
  have hall : ∀ x : M, β x = x → x * x = 1 := by
    intro x hx
    by_contra h2
    exact hcon ⟨x, hx, h2⟩
  exact hab (wccu_fixed_exponent_two_implies_abelian hall a b)

theorem outerFixedNoNormalTwo_isU3 {M : Type} [Group M] [Finite M] (h : IsU3 M 2) :
    OuterFixedNoNormalTwo M := by
  intro β hβ hout E hEp hfix hnorm
  haveI : IsSimpleGroup (autFixed β) := wccu_fixed_unitary_isSimple h β hβ hout
  have hnabC := wccu_fixed_unitary_nonabelian h β hβ hout
  have hE_le : E ≤ autFixed β := fun x hx => (mem_autFixed_iff).mpr (hfix x hx)
  haveI : (E.subgroupOf (autFixed β)).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hE_le]
    intro x y hx hy
    exact hnorm y ((mem_autFixed_iff).mp hy) x hx
  have hEp' : IsPGroup 2 (E.subgroupOf (autFixed β)) :=
    hEp.of_equiv (Subgroup.subgroupOfEquivOfLe hE_le).symm
  have hbot : E.subgroupOf (autFixed β) = ⊥ := wccu_simple_no_normal_two hnabC hEp'
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  have hmem : (⟨x, hE_le hx⟩ : autFixed β) ∈ E.subgroupOf (autFixed β) :=
    (Subgroup.mem_subgroupOf).mpr hx
  rw [hbot] at hmem
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hmem)

theorem outerFixedRigid_isU3 {M : Type} [Group M] [Finite M] (h : IsU3 M 2) :
    OuterFixedRigid M := by
  intro β hβ hout γ _ hγβ hγfix
  have hB : BenderType M 2 3 5 := wccu_benderType_of_isU3 h
  exact hB.centralizer_unitary β hβ hout γ hγβ
    (fun x hx => hγfix x ((mem_autFixed_iff).mp hx))

end CFSG.LocalAnalysis.WeakClosure81

end

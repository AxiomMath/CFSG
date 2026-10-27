module

public import CFSG.LieType.Chevalley.EvenF4OuterInvolutionsCanonical
public import CFSG.LieType.Ree.LargeReeExceptionalFullCentralizer
public import CFSG.LocalAnalysis.StandardType.GGFieldOuterModel
public import CFSG.LocalAnalysis.StandardType.GGSixOddIndexF4FactsRank
public import CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProofRank

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Ree CFSG.LieType.Chevalley

theorem outerInvolution_conj_ree
    {f : ℕ} (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ f) (m : ℕ) (hm : f = 2 * m + 1)
    (α : MulAut (adjointGroup ReeTag.F4.tag K)) (h2 : α * α = 1)
    (hout : ∀ c : adjointGroup ReeTag.F4.tag K, α ≠ MulAut.conj c) :
    ∃ h : adjointGroup ReeTag.F4.tag K,
      α = MulAut.conj h * ReeTag.F4.finiteReeAut K m * (MulAut.conj h)⁻¹ := by
  have hαo : α ∉ (MulAut.conj : adjointGroup ReeTag.F4.tag K →*
      MulAut (adjointGroup ReeTag.F4.tag K)).range := by
    rintro ⟨c, rfl⟩
    exact hout c rfl
  obtain ⟨ψ, hψ, -, hodd, -⟩ :=
    even_F4_all_outer_involutions_canonical (by omega) K hK α (by rw [sq, h2]) hαo
  obtain ⟨hF, k, rfl⟩ := hodd m hm
  refine ⟨k⁻¹, ?_⟩
  rw [← hF, ← hψ, map_inv]
  group

theorem exists_reeGamma_copy
    {m : ℕ} (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (E : Subgroup (adjointGroup ReeTag.F4.tag K)) (hE : E ≤ ReeTag.F4.finiteReeFixedGroup K m) :
    ∃ A : Subgroup (ReeTag.F4.reeGamma K m), Nat.card A = Nat.card E ∧
      (∀ n : ℕ, (∀ x ∈ E, x ^ n = 1) → ∀ x ∈ A, x ^ n = 1) ∧
      ((∀ x ∈ E, ∀ y ∈ E, x * y = y * x) → ∀ x ∈ A, ∀ y ∈ A, x * y = y * x) := by
  have hle : E.map (adjointGroup ReeTag.F4.tag K).subtype ≤ ReeTag.F4.reeGamma K m :=
    Subgroup.map_mono hE
  refine ⟨(E.map (adjointGroup ReeTag.F4.tag K).subtype).subgroupOf (ReeTag.F4.reeGamma K m),
    ?_, ?_, ?_⟩
  · rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv,
      Subgroup.card_map_of_injective (adjointGroup ReeTag.F4.tag K).subtype_injective]
  · intro n hn x hx
    rw [Subgroup.mem_subgroupOf] at hx
    obtain ⟨y, hy, hyx⟩ := hx
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hyx, ← map_pow, hn y hy, map_one]
    rfl
  · intro hc x hx y hy
    rw [Subgroup.mem_subgroupOf] at hx hy
    obtain ⟨x', hx', hxx⟩ := hx
    obtain ⟨y', hy', hyy⟩ := hy
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hxx, ← hyy]
    exact congrArg Subtype.val (hc x' hx' y' hy')

theorem fieldOuterInvModel_F4_odd
    (m : ℕ) (K : Type) [Field K] [Finite K]
    [CharP K ReeTag.F4.prime] (hK : Nat.card K = 2 ^ (2 * m + 1)) :
    GGFieldOuterInvModel (adjointGroup ReeTag.F4.tag K) := by
  rintro p b α hp hp2 - - ⟨E, hE, hbE, hcard, -⟩ h2 hout - - hfix
  obtain ⟨h, rfl⟩ := outerInvolution_conj_ree K hK m rfl α h2 hout
  have hcomm : ∀ x ∈ E, ∀ y ∈ E, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hE.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hEfix : ∀ x ∈ E, (MulAut.conj h * ReeTag.F4.finiteReeAut K m * (MulAut.conj h)⁻¹) x = x :=
    fun x hx => hfix x (Subgroup.mem_centralizer_singleton_iff.2 (hcomm b hbE x hx).symm)
  set E' := E.map (MulAut.conj h⁻¹).toMonoidHom
  have hE' : E' ≤ ReeTag.F4.finiteReeFixedGroup K m := by
    rintro _ ⟨x, hx, rfl⟩
    have e := hEfix x hx
    change ReeTag.F4.finiteReeAut K m (h⁻¹ * x * h⁻¹⁻¹) = h⁻¹ * x * h⁻¹⁻¹
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_inv, MulAut.inv_apply,
      MulAut.conj_symm_apply] at e
    rw [inv_inv]
    calc ReeTag.F4.finiteReeAut K m (h⁻¹ * x * h) = h⁻¹ * (h * ReeTag.F4.finiteReeAut K m
          (h⁻¹ * x * h) * h⁻¹) * h := by group
      _ = h⁻¹ * x * h := by rw [e]
  obtain ⟨A, hAc, hAp, hAcomm⟩ := exists_reeGamma_copy (m := m) K E' hE'
  have hcardE' : Nat.card E' = Nat.card E :=
    Subgroup.card_map_of_injective (MulAut.conj h⁻¹).injective
  have hpE' : ∀ x ∈ E', x ^ p = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hE.2 x hx, map_one]
  have hcE' : ∀ x ∈ E', ∀ y ∈ E', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hcomm x hx y hy]
  have hp2' : 2 ≤ p := hp.two_le
  have hbound : Nat.card A ≤ p ^ 2 := by
    have h35 : p = 3 ∨ 5 ≤ p := by
      rcases lt_or_ge p 5 with h | h
      · left
        interval_cases p <;> first | rfl | (exact absurd rfl hp2) | (norm_num at hp)
      · exact Or.inr h
    rcases h35 with h3 | h5
    · subst h3
      have := CFSG.RankThree.PartTwo.Sec21.ReeF4ThreeLocalProof.card_le_nine_of_reeGamma m K hK A
        ⟨⟨⟨fun x y => Subtype.ext (hAcomm hcE' x x.2 y y.2)⟩⟩, hAp 3 hpE'⟩
      simpa using this
    · exact ggF4_ree_card_le_sq hK hp h5 A (hAp p hpE') (hAcomm hcE')
  have : p ^ 4 ≤ p ^ 2 := le_trans hcard (by rw [← hcardE', ← hAc]; exact hbound)
  have := Nat.pow_le_pow_iff_right (by omega : 1 < p) |>.1 this
  omega

end CFSG.StandardType

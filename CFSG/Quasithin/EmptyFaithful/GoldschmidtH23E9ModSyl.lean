module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23E9ModSylB
public import CFSG.Quasithin.Background.A4Defs

public section

namespace CFSG.Quasithin.SixData151b

open CFSG.Open CFSG.QuasithinUnique
open scoped Pointwise commutatorElement

variable {W : Type*} [CommGroup W] [Finite W] (S : SixData151b W 5)

set_option linter.unusedSectionVars false in
theorem sylow_ptFix (hW : ∀ w : W, w ^ 2 = 1) (hcard : Nat.card W = 256)
    {Mb Tb : Subgroup (MulAut W)} (hTb : IsSylowTwoOf Tb Mb)
    (hnorm : ∀ g ∈ Mb, ∀ z ∈ S.A₁ ⊔ S.A₂, g * z * g⁻¹ ∈ S.A₁ ⊔ S.A₂) (hτ : S.τ ∈ Mb)
    {x₁ x₂ : MulAut W} (hx₁ : x₁ ∈ S.A₁ ⊓ Tb) (_hx₂ : x₂ ∈ S.A₂ ⊓ Tb) (hx₁2 : orderOf x₁ = 2)
    (_hx₂2 : orderOf x₂ = 2) :
    IsSylowTwoOf (Tb ⊓ ptFix Mb (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)))
      (ptFix Mb (S.W₁ ⊓ fixV (Subgroup.zpowers x₁))) := by
  have hx₁Tb : x₁ ∈ Tb := hx₁.2
  have hx₁A : x₁ ∈ S.A₁ := hx₁.1
  have hx₁Mb : x₁ ∈ Mb := hTb.1 hx₁Tb
  have hKH : ptFix Mb S.W₁ ≤ ptFix Mb (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) :=
    fun k hk => ⟨hk.1, fun z hz => hk.2 z hz.1⟩
  have hMb₀le : stabSub Mb S.W₁ ≤ Mb := fun g hg => hg.1
  have hKMb₀ : ptFix Mb S.W₁ ≤ stabSub Mb S.W₁ := by
    intro k hk
    refine ⟨hk.1, fun w => ⟨fun hw => by rw [hk.2 w hw]; exact hw, fun hkw => ?_⟩⟩
    have h2 : k w = w := k.injective (hk.2 (k w) hkw)
    rw [← h2]
    exact hkw
  have hτswap : S.Swap₁₂ S.τ := S.swap_of_conj hW (hnorm S.τ hτ) S.τ₁₂
  have hidx : ((stabSub Mb S.W₁).subgroupOf Mb).index = 2 := by
    rw [Subgroup.index_eq_two_iff_exists_notMem_and]
    refine ⟨⟨S.τ, hτ⟩, ?_, fun b => ?_⟩
    · intro h
      exact S.not_stab₁_of_swap hcard hτswap (Subgroup.mem_subgroupOf.mp h).2
    · rcases S.stab_or_swap hW (hnorm b.1 b.2) with hb | hb
      · exact Or.inr (Subgroup.mem_subgroupOf.mpr ⟨b.2, hb.1⟩)
      · exact Or.inl (Subgroup.mem_subgroupOf.mpr
          ⟨Mb.mul_mem b.2 hτ, (S.stab_mul_of_swap hb hτswap).1⟩)
  have hMbnorm : Mb ≤ Subgroup.normalizer (stabSub Mb S.W₁ : Set (MulAut W)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hMb₀le).mp (Subgroup.normal_of_index_eq_two hidx)
  have hKconj : ∀ g ∈ stabSub Mb S.W₁, ∀ k ∈ ptFix Mb S.W₁, g * k * g⁻¹ ∈ ptFix Mb S.W₁ := by
    intro g hg k hk
    refine ⟨Mb.mul_mem (Mb.mul_mem hg.1 hk.1) (Mb.inv_mem hg.1), fun w hw => ?_⟩
    have hgw : g⁻¹ w ∈ S.W₁ := (hg.2 (g⁻¹ w)).mpr (by rw [MulAut.apply_inv_self]; exact hw)
    show g (k (g⁻¹ w)) = w
    rw [hk.2 _ hgw, MulAut.apply_inv_self]
  have hKnorm : stabSub Mb S.W₁ ≤ Subgroup.normalizer (ptFix Mb S.W₁ : Set (MulAut W)) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro k
    refine ⟨fun hk => hKconj g hg k hk, fun hk => ?_⟩
    have := hKconj g⁻¹ ((stabSub Mb S.W₁).inv_mem hg) _ hk
    simpa [mul_assoc] using this
  have hS1 : IsSylowTwoOf (Tb ⊓ stabSub Mb S.W₁) (stabSub Mb S.W₁) :=
    A4.isSylowTwoOf_inf_normal hTb hMb₀le hMbnorm
  have hS2 : IsSylowTwoOf (Tb ⊓ ptFix Mb S.W₁) (ptFix Mb S.W₁) := by
    have := A4.isSylowTwoOf_inf_normal hS1 hKMb₀ hKnorm
    rwa [inf_assoc, inf_eq_right.mpr hKMb₀] at this
  have hxx : x₁ * x₁ = 1 := by
    rw [← pow_two]
    have := pow_orderOf_eq_one x₁
    rwa [hx₁2] at this
  have hx₁₁ : ∀ w : W, x₁ (x₁ w) = w := fun w => by
    have : (x₁ * x₁) w = w := by rw [hxx]; rfl
    exact this
  have hxH : x₁ ∈ ptFix Mb (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)) :=
    ⟨hx₁Mb, fun z hz => mem_fixV_zpowers_iff.mp hz.2⟩
  have hxK : x₁ ∉ ptFix Mb S.W₁ := by
    intro hxK
    have h1 : x₁ = 1 := S.eq_one_of_fix_W₁_W₂ hxK.2 (fun w hw => S.fix_W₂_of_mem_A₁ hx₁A hw)
    rw [h1, orderOf_one] at hx₁2
    omega
  have hcover : ∀ h ∈ ptFix Mb (S.W₁ ⊓ fixV (Subgroup.zpowers x₁)),
      h ∈ ptFix Mb S.W₁ ∨ h * x₁ ∈ ptFix Mb S.W₁ := by
    intro h hh
    rcases S.ptFix_dichotomy hW hcard hnorm hx₁A hx₁2 hh with h1 | h2
    · exact Or.inl ⟨hh.1, h1⟩
    · refine Or.inr ⟨Mb.mul_mem hh.1 hx₁Mb, fun w hw => ?_⟩
      show h (x₁ w) = w
      rw [h2 (x₁ w) (S.mem_W₁_of_mem_A₁ hx₁A hw), hx₁₁]
  exact isSylowTwoOf_inf_of_two_cosets hKH hTb.isPGroup hxH hx₁Tb hxK hcover hS2

end CFSG.Quasithin.SixData151b

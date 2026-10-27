module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableRankMap
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormBridge
public import CFSG.Quasithin.Background.B4ModelsIso

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open
open scoped Matrix

theorem s15k_table_nat_red {V : Type} [CommGroup V] [Finite V] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Γ : Subgroup (Matrix.GeneralLinearGroup ι (ZMod 2))}
    {K : Subgroup (MulAut V)} {Z : Subgroup V} (h : (FFModel.nat Γ).Realizes K Z ⊥) {z : V}
    (hz : z ∈ Z) :
    ∃ m : ι → ZMod 2, CFSG.Open.pRank 3 (Γ ⊓ s15kVecStab m) ≤
      CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z) := by
  obtain ⟨π, b, -, hstab, hb⟩ := s15k_norm_nat_extract h
  refine ⟨Multiplicative.toAdd (b ⟨z, hz⟩), ?_⟩
  let f : ↥Γ →* MulAut V := K.subtype.comp π
  have hfi : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro γ hγ
    have h1 : π γ = 1 := Subtype.ext hγ
    apply natAct_faithful Γ γ
    intro w
    obtain ⟨r, rfl⟩ := b.surjective w
    have h2 := hb γ r (hstab (π γ) r)
    have h3 : (⟨((π γ : ↥K) : MulAut V) (r : V), hstab (π γ) r⟩ : ↥Z) = r :=
      Subtype.ext (by rw [h1]; rfl)
    rw [h3] at h2
    rw [← h2, mul_inv_cancel]
  refine s15k_table_pRank_le_of_inj (by norm_num) f hfi inf_le_left ?_
  intro x hx
  refine Subgroup.mem_inf.2 ⟨(π x).2, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  have hr : ((π x : ↥K) : MulAut V) z ∈ Z := hstab (π x) ⟨z, hz⟩
  have h1 := hb x ⟨z, hz⟩ hr
  have h2 : natAct Γ x (b ⟨z, hz⟩) = b ⟨z, hz⟩ := by
    have hxm : ((x : Matrix.GeneralLinearGroup ι (ZMod 2)) : Matrix ι ι (ZMod 2)) *ᵥ
        Multiplicative.toAdd (b ⟨z, hz⟩) = Multiplicative.toAdd (b ⟨z, hz⟩) :=
      (Subgroup.mem_inf.1 hx).2
    exact congrArg Multiplicative.ofAdd hxm
  rw [h2] at h1
  have h3 := congrArg Subtype.val (b.injective h1)
  exact h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

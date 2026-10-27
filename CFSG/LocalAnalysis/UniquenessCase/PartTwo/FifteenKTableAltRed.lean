module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKTableRankMap
public import CFSG.Quasithin.Background.B4Models
import CFSG.Quasithin.Background.G64SymSec

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

theorem s15k_table_alt_red {V : Type} [CommGroup V] [Finite V] {n : ℕ} (hn : 5 ≤ n)
    {K : Subgroup (MulAut V)} {Z : Subgroup V} (h : (FFModel.altDn n).Realizes K Z ⊥) {z : V}
    (hz : z ∈ Z) :
    ∃ x : G6.PermMod n, CFSG.Open.pRank 3 (alternatingGroup (Fin n) ⊓ s15kPermStab n x) ≤
      CFSG.Open.pRank 3 (K ⊓ MulAction.stabilizer (MulAut V) z) := by
  obtain ⟨π, hπ⟩ := h
  have hinj : Function.Injective π :=
    FFModel.RealizesVia.injective_of_faithful_on (G64.altDn_faithful hn) hπ
  obtain ⟨-, -, -, hKU, -, hsec, -, β, -, hβk, hβe⟩ := hπ
  have hβinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    exact Subtype.ext (Subgroup.mem_bot.1 ((hβk u).1 hu))
  obtain ⟨m, hm⟩ := QuotientGroup.mk_surjective (β ⟨z, hz⟩)
  refine ⟨(m.1 : G6.PermMod n), ?_⟩
  let f : ↥(alternatingGroup (Fin n)) →* MulAut V := K.subtype.comp π
  have hfi : Function.Injective f := Subtype.val_injective.comp hinj
  refine s15k_table_pRank_le_of_inj (by norm_num) f hfi inf_le_left ?_
  intro σ hσ
  refine Subgroup.mem_inf.2 ⟨(π σ).2, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  have hfix : G6.permAct n (σ : Equiv.Perm (Fin n)) (m.1 : G6.PermMod n) = (m.1 : G6.PermMod n) :=
    (Subgroup.mem_inf.1 hσ).2
  have hu : ((π σ : ↥K) : MulAut V) z ∈ Z := hKU (π σ) z hz
  have hm' : (FFModel.altDn n).act σ (m.1 : G6.PermMod n) ∈ (FFModel.altDn n).sec :=
    hsec σ m m.2
  have h1 := hβe σ ⟨z, hz⟩ m hu hm' hm.symm
  have h2 : (⟨(FFModel.altDn n).act σ (m.1 : G6.PermMod n), hm'⟩ : ↥(FFModel.altDn n).sec) = m :=
    Subtype.ext hfix
  rw [h2, hm] at h1
  exact congrArg Subtype.val (hβinj h1)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8R95B0E1
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
import CFSG.Walter.J1Props.Factor
import CFSG.Walter.Models
import CFSG.Walter.AStar.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

theorem r95_gB_not_three_group {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 3 Q)
    {E : Subgroup Q} (hE : HasL32Quot E) : False := by
  obtain ⟨R, -, hR, a, ha, b, hb, hab⟩ := r95_exists_noncomm_two_subgroup hE
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hd : Disjoint R (⊤ : Subgroup Q) :=
    IsPGroup.disjoint_of_ne 2 3 (by norm_num) R ⊤ hR (hQ.to_subgroup ⊤)
  have hRbot : R = ⊥ := disjoint_top.mp hd
  have ha1 : a = 1 := Subgroup.mem_bot.mp (hRbot ▸ ha)
  exact hab (by rw [ha1, one_mul, mul_one])

theorem r95_gB_not_J1 {Q : Type} [Group Q] [Finite Q] (hQ : IsSpor Q .J1)
    {E : Subgroup Q} (hE : HasL32Quot E) : False := by
  obtain ⟨R, -, hR, a, ha, b, hb, hab⟩ := r95_exists_noncomm_two_subgroup hE
  obtain ⟨e⟩ : Nonempty (Q ≃* CFSG.Blueprint.NativeSporadic.Carrier .J1) := hQ
  have hA : CFSG.Walter.HasAbelianSylowTwo Q :=
    CFSG.Walter.J1Props.hasAbelianSylowTwo.of_surjective
      (f := (e.trans CFSG.Walter.walterJ1EquivNative.symm).symm.toMonoidHom)
      (MulEquiv.surjective _)
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hRP⟩ := hR.exists_le_sylow
  exact hab (congrArg Subtype.val ((hA P).is_comm.comm ⟨a, hRP ha⟩ ⟨b, hRP hb⟩))

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09

module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1Defs
public import CFSG.LieType.Universal.Spin.SpinCommRankTwo
public import CFSG.LieType.Universal.Catalog

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.LieType.Universal
open CFSG.Open (StatedLieTag)

theorem rckPOmegaMinus_false_of_le_one
    {X : Type} [Group X] {m g : ℕ} (hm : m ≤ 1) (φ : (ggU .POmegaMinus m g).K →* X)
    {K J : Subgroup X} {d : X} (hφr : φ.range = K)
    (hJ : IsComponentOf J (K ⊓ Subgroup.centralizer {d})) : False := by
  have hdim : Module.finrank (GaloisField 2 g)
      (Fin (m - 1) ⊕ Fin (m - 1) ⊕ Fin 2 → GaloisField 2 g) = 2 := by
    rw [Module.finrank_fintype_fun_eq_card]
    simp only [Fintype.card_sum, Fintype.card_fin]
    omega
  have hcomm : ∀ x y : ↥(spinGroup (Spin.quadMinus m (GaloisField 2 g) (minusCoeffs 2 g).1
      (minusCoeffs 2 g).2)), x * y = y * x :=
    Spin.spinGroup_comm_of_finrank_two _ hdim
  have hJK : J ≤ φ.range := by
    rw [hφr]
    exact hJ.1.trans inf_le_left
  haveI : IsMulCommutative ↥J := ⟨⟨fun a b => by
    obtain ⟨x, hx⟩ := hJK a.2
    obtain ⟨y, hy⟩ := hJK b.2
    apply Subtype.ext
    change (a : X) * b = b * a
    rw [← hx, ← hy, ← map_mul, ← map_mul]
    exact congrArg φ (hcomm x y)⟩⟩
  have hcenter : Subgroup.center ↥J = ⊤ := Subgroup.center_eq_top
  haveI : Subsingleton (↥J ⧸ Subgroup.center ↥J) := by
    rw [hcenter]
    exact QuotientGroup.subsingleton_quotient_top
  exact (not_subsingleton_iff_nontrivial (α := ↥J ⧸ Subgroup.center ↥J)).mpr
    hJ.2.2.2.toNontrivial inferInstance

end CFSG.StandardType.RCKRP

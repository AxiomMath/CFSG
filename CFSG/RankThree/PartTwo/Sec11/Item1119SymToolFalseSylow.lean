module

public import CFSG.RankThree.PartTwo.Sec11.Final
public import CFSG.RankThree.PartTwo.Sec11.Coprime

open CFSG.GH74.GLS (oResidual)

public section

namespace CFSG.RankThree.PartTwo.Sec11.Item1119Sym

theorem false_of_sylow_fixed {G : Type} [Group G] [Finite G]
    (P : Sylow 3 G) (W₀ : Subgroup G) (r : G)
    (hG : oResidual 3 G = ⊤)
    (hW : ∀ (K : Subgroup (P : Subgroup G)) [K.Normal], IsEmpty ((P : Subgroup G) ⧸ K ≃* W33))
    (hW0P : W₀ ≤ (P : Subgroup G)) (hPP : ⁅(P : Subgroup G), (P : Subgroup G)⁆ ≤ W₀)
    (hNW : Subgroup.normalizer ((P : Subgroup G) : Set G) ≤ Subgroup.normalizer (W₀ : Set G))
    (hr : r ∈ (P : Subgroup G)) (hrW : r ∉ W₀)
    (hfix : ∀ n ∈ Subgroup.normalizer ((P : Subgroup G) : Set G), n * r * n⁻¹ * r⁻¹ ∈ W₀) :
    False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPeq : (P : Subgroup G) =
      ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ :=
    CFSG.RankThree.PartTwo.Sec11.rank3II_11_31_of P hG hW
  have hcomm : ⁅(P : Subgroup G), Subgroup.normalizer ((P : Subgroup G) : Set G)⁆ =
      ⁅Subgroup.normalizer ((P : Subgroup G) : Set G), (P : Subgroup G)⁆ := by
    rw [Subgroup.commutator_comm]
  have htop : (P : Subgroup G) ≤ W₀ ⊔
      ⁅Subgroup.normalizer ((P : Subgroup G) : Set G), (P : Subgroup G)⁆ :=
    hPeq.le.trans (hcomm.le.trans le_sup_right)
  have hS : CFSG.ABGLocalTools.IsSylowOf 3 (P : Subgroup G)
      (Subgroup.normalizer ((P : Subgroup G) : Set G)) := by
    set N := Subgroup.normalizer ((P : Subgroup G) : Set G) with hNdef
    have hP3 : IsPGroup 3 (P : Subgroup G) := P.isPGroup'
    have hPN : (P : Subgroup G) ≤ N := Subgroup.le_normalizer
    obtain ⟨Q, hQ⟩ := (hP3.comap_subtype (K := N)).exists_le_sylow
    have hPS : (P : Subgroup G) ≤ (Q : Subgroup N).map N.subtype := fun x hx =>
      ⟨⟨x, hPN hx⟩, hQ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
    have hS3 : IsPGroup 3 ((Q : Subgroup N).map N.subtype) := Q.isPGroup'.map N.subtype
    exact ⟨Q, P.is_maximal' hS3 hPS⟩
  have key := CFSG.RankThree.PartTwo.Sec11.mem_of_commutator_mem_of_coprime (p := 3)
    (P := (P : Subgroup G)) (V := W₀) (N := Subgroup.normalizer ((P : Subgroup G) : Set G))
    (S := (P : Subgroup G)) P.isPGroup' hW0P hPP le_rfl hNW hS le_rfl htop hr hfix
  exact hrW key

end CFSG.RankThree.PartTwo.Sec11.Item1119Sym

end

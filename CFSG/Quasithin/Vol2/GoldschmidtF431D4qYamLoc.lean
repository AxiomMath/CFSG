module

public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsD4Data
public import CFSG.Quasithin.Recognition.CertTwoLocal
import CFSG.LieType.Chevalley.GraphFixedParabolicNormalizer

public section

namespace CFSG.Quasithin.H13.F431.D4q.Hex

open CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.Open
  CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup.X6 CFSG.Quasithin.H13.Sec53F.TriD4


variable {K : Type} [Field K] [Finite K] (σ : K ≃+* K)

theorem d4_twoLocal_parabolic [CharP K 2] (a : Fin TwistTag.D4.foldedTag.rank) :
    IsTwoLocal ((graphFixedParabolic TwistTag.D4 K σ.toRingHom {a}).subgroupOf
      (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)) := by
  have hex : ∀ a : Fin TwistTag.D4.foldedTag.rank, ∃ b, b ≠ a := by decide
  obtain ⟨b, hb⟩ := hex a
  set C := graphFixedRootGroup TwistTag.D4 K σ.toRingHom with hC
  have hUC : graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom ≤ C :=
    graphFixedPosUnipotent_le_graphFixedRootGroup _ _ _
  set Q := graphFixedParabolicRadical TwistTag.D4 K σ.toRingHom {a} with hQ
  have hQU : Q ≤ graphFixedPosUnipotent TwistTag.D4 K σ.toRingHom :=
    graphFixedParabolicRadical_le_graphFixedPosUnipotent {a}
  have hQC : Q ≤ C := hQU.trans hUC
  have hN := diagram_fixed_parabolic_root_radical_normalizers TwistTag.D4 K σ {a}
  have hmem := orbitX_mem_graphFixedParabolicRadical (t := TwistTag.D4) (K := K)
    (σ := σ.toRingHom) (J := {a}) (a := b) (by simpa using hb) 1
  refine ⟨Q.subgroupOf C, ?_, ?_, ?_⟩
  · intro hbot
    have hxC : (orbitX TwistTag.D4 K σ.toRingHom b 1 : ModGL TwistTag.D4.tag K) ∈ C :=
      hUC (orbitX_mem_graphFixedPosUnipotent _ _ _ _)
    have hx : (⟨(orbitX TwistTag.D4 K σ.toRingHom b 1 : ModGL TwistTag.D4.tag K), hxC⟩ : C) ∈
        Q.subgroupOf C := hmem
    rw [hbot, Subgroup.mem_bot] at hx
    have hx' : (orbitX TwistTag.D4 K σ.toRingHom b 1 : ModGL TwistTag.D4.tag K) = 1 :=
      congrArg Subtype.val hx
    have h1 : orbitX TwistTag.D4 K σ.toRingHom b 1 = orbitX TwistTag.D4 K σ.toRingHom b 0 := by
      rw [orbitX_zero]
      exact Subtype.ext hx'
    exact one_ne_zero (orbitX_injective σ.toRingHom b h1)
  · exact IsPGroup.to_le (d4_sylow σ).2.1 (fun x hx =>
      Subgroup.mem_subgroupOf.2 (hQU (Subgroup.mem_subgroupOf.1 hx)))
  · rw [normalizer_subgroupOf_eq' hQC, ← hN]

end CFSG.Quasithin.H13.F431.D4q.Hex

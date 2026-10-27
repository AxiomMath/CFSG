module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Suzuki.SylowThreeJoin
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

open scoped Pointwise

namespace CFSG.GorensteinWalter

universe u

/-! A disjointness transport used by the `R5-A` orbit route.  Once the base
pair `P` and `r • P` is disjoint, every Sylow-three subgroup obtained from
the double coset `N_G(P) r N_G(P)` is disjoint from `P`; the normalizer
factors are removed by mapping the intersection through conjugation.
-/

public theorem sylow3_inter_bot_of_mem_normalizer_doubleCoset
    {G : Type u} [Group G]
    (P : Sylow 3 G) (r : G)
    (hbase : (P : Subgroup G) ⊓ (r • P : Sylow 3 G) = ⊥)
    {n₁ n₂ : G}
    (hn₁ : n₁ ∈ Subgroup.normalizer (P : Set G))
    (hn₂ : n₂ ∈ Subgroup.normalizer (P : Set G)) :
    (P : Subgroup G) ⊓ ((n₁ * r * n₂) • P : Sylow 3 G) = ⊥ := by
  have hfix₂ : n₂ • P = P :=
    Sylow.smul_eq_iff_mem_normalizer.mpr hn₂
  rw [mul_smul, hfix₂]
  let e : G →* G := (MulAut.conj n₁).toMonoidHom
  have heinj : Function.Injective e := (MulAut.conj n₁).injective
  have hmapP : (P : Subgroup G).map e = (P : Subgroup G) := by
    simpa [e] using (Subgroup.mem_normalizer_iff_map_conj_eq.mp hn₁)
  have hmapR : ((r • P : Sylow 3 G) : Subgroup G).map e =
      ((n₁ * r) • P : Sylow 3 G) := by
    calc
      ((r • P : Sylow 3 G) : Subgroup G).map e =
          ((n₁ • (r • P) : Sylow 3 G) : Subgroup G) := by
            rw [Sylow.coe_subgroup_smul, Sylow.coe_subgroup_smul]
            rfl
      _ = ((n₁ * r) • P : Sylow 3 G) := by rw [← mul_smul]
  calc
    (P : Subgroup G) ⊓ ((n₁ * r) • P : Sylow 3 G) =
        (P : Subgroup G).map e ⊓
          ((r • P : Sylow 3 G) : Subgroup G).map e := by
          rw [hmapP, hmapR]
    _ = ((P : Subgroup G) ⊓
        ((r • P : Sylow 3 G) : Subgroup G)).map e := by
      symm
      exact Subgroup.map_inf (P : Subgroup G)
        ((r • P : Sylow 3 G) : Subgroup G) e heinj
    _ = ⊥ := by rw [hbase, Subgroup.map_bot]

end CFSG.GorensteinWalter

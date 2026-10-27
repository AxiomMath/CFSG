module

public import CFSG.Quasithin.EmptyFaithful.SzF53DichBase
public import CFSG.Quasithin.EmptyFaithful.SzF53B2Glue
public import CFSG.Quasithin.EmptyFaithful.SzF53BasD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53
open CFSG.Quasithin.CosetGeom

namespace SzF53B2

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem normal_of_zv_central (hA : F53Amalgam H M S)
    (hz : Zv (γ₀ (H ⊔ M) H M) ≤ centerOf (stab (γ₀ (H ⊔ M) H M))) :
    H ≤ Subgroup.normalizer (quasithinOmegaOneCenter S : Set G) := by
  have hnb : γ₁ (H ⊔ M) H M ∈ nbrs (γ₀ (H ⊔ M) H M) := adj_γ₀_γ₁
  have h1 := (Zv_eq_omegaOneCenter_inf hA hnb hz).1
  rw [stab_γ₀ hA.amalgam.le₁, stab_γ₁ hA.amalgam.le₂, hA.inf_eq] at h1
  rw [stab_γ₀ hA.amalgam.le₁] at hz
  have hc : H ≤ Subgroup.centralizer (Zv (γ₀ (H ⊔ M) H M) : Set G) :=
    Subgroup.le_centralizer_iff.mp (hz.trans inf_le_right)
  rw [h1] at hc
  exact hc.trans (Subgroup.centralizer_le_normalizer _)

theorem B2Setup.of_bAt (hA : F53Amalgam H M S) (hb : bMin H M = 2)
    (h1 : bAt (γ₁ (H ⊔ M) H M) = bMin H M)
    (hz : Zv (γ₀ (H ⊔ M) H M) ≤ centerOf (stab (γ₀ (H ⊔ M) H M))) : B2Setup H M S where
  amalgam := hA
  zb_normal := normal_of_zv_central hA hz
  crit := by
    have hC : M ⊓ Subgroup.centralizer (Zv (γ₁ (H ⊔ M) H M) : Set G) ≤ pCoreOf 2 M := by
      have := centralizer_Zv_eq_Qv_of_bAt hA h1
      rw [stab_γ₁ hA.amalgam.le₂, Qv_γ₁_eq hA] at this
      exact this.le
    have h2 := bAt_γ₁_eq_critDist hA hC
    rw [h1, hb, Zv_γ₁_eq hA] at h2
    rw [sup_comm M H]
    exact h2.symm

end SzF53B2

end CFSG.Quasithin

module

public import CFSG.RankThree.GF2n.Stroth80.Sec4Model
public import CFSG.RankThree.GF2n.Stroth80.Sec7StepsCentre

public section

namespace CFSG.RankThree.GF2n.Stroth80

open Subgroup CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement

section Stroth

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem Ctx.phi_Qf_eq [(Q.subgroupOf M).Normal] (hc : Ctx M Q Z B) {K : Type} [Field K]
    {γ : G → K} (M₀ : Tim79.QuadModel Q Z K γ) (φ : ↥(bar M Q (H0 M Z)) →* (M₀.E ≃ₗ[K] M₀.E))
    (hφπ : ∀ (y : ↥M) (hy : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z)) (x : G),
      x ∈ Q → M₀.π ((y : G) * x * (y : G)⁻¹) =
        φ ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy⟩ (M₀.π x))
    (x : ↥(bar M Q (H0 M Z))) (e : M₀.E) : M₀.Qf (φ x e) = M₀.Qf e := by
  obtain ⟨y, hy⟩ := QuotientGroup.mk'_surjective (Q.subgroupOf M) (x : Mbar M Q)
  have hy' : QuotientGroup.mk' (Q.subgroupOf M) y ∈ bar M Q (H0 M Z) := hy ▸ x.2
  have hxy : x = ⟨QuotientGroup.mk' (Q.subgroupOf M) y, hy'⟩ := Subtype.ext hy.symm
  have hyH : (y : G) ∈ H0 M Z := (mk_mem_bar_iff_sec4 hc.Q_le_H0' y).mp hy'
  obtain ⟨w, hwQ, rfl⟩ := M₀.π_surj e
  have hyw : (y : G) * w * (y : G)⁻¹ ∈ Q :=
    (Subgroup.mem_normalizer_iff.mp (hc.hyp.Q_normal.2 y.2) w).mp hwQ
  rw [hxy, ← hφπ y hy' w hwQ, ← M₀.sq_eq _ hyw, ← M₀.sq_eq _ hwQ]
  congr 1
  have hw2 : w ^ 2 ∈ Z := M₀.sq_mem w hwQ
  have hc2 : w ^ 2 * (y : G) = (y : G) * w ^ 2 :=
    Subgroup.mem_centralizer_iff.mp hyH.2 (w ^ 2) hw2
  rw [conj_pow, hc2.symm, mul_inv_cancel_right]

end Stroth

end CFSG.RankThree.GF2n.Stroth80

end

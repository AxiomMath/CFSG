module

public import CFSG.Quasithin.H13.L32AL2r
public import CFSG.Quasithin.H13.L32AL2x
public import CFSG.Quasithin.H13.L32AL3b

public section

namespace CFSG.Quasithin.H13.L32A.L2

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin
open CFSG.Quasithin.H.Om4 Matrix CFSG.Quasithin.H13.L32A.C
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G]

theorem mem_normalizer_sup_iff {V₁ : Subgroup G} {z z' : G} (hz : Subgroup.zpowers z = V₁)
    (h : A114Hyp (V₁ ⊔ Subgroup.zpowers z') z z') {g : G}
    (hg : g ∈ Subgroup.normalizer (V₁ : Set G)) (hgz : g * z * g⁻¹ = z) :
    g ∈ Subgroup.normalizer ((V₁ ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) ↔
      g * z' * g⁻¹ * z'⁻¹ ∈ V₁ := by
  have hzV : z ∈ V₁ := hz ▸ Subgroup.mem_zpowers z
  constructor
  · intro hgN
    have hz'V : g * z' * g⁻¹ ∈ V₁ ⊔ Subgroup.zpowers z' :=
      (Subgroup.mem_normalizer_iff.mp hgN z').mp h.mem₂
    rcases h.mem_V_cases hz'V with h0 | h0 | h0 | h0
    · exfalso
      apply h.ne_one₂
      calc z' = g⁻¹ * (g * z' * g⁻¹) * g := by group
        _ = 1 := by rw [h0]; group
    · exfalso
      apply h.ne
      calc z = g⁻¹ * (g * z * g⁻¹) * g := by group
        _ = g⁻¹ * (g * z' * g⁻¹) * g := by rw [hgz, h0]
        _ = z' := by group
    · rw [h0, mul_inv_cancel]
      exact V₁.one_mem
    · rw [h0, mul_inv_cancel_right]
      exact hzV
  · intro hc
    have hle : Quasithin.conjSub g (V₁ ⊔ Subgroup.zpowers z') ≤ V₁ ⊔ Subgroup.zpowers z' := by
      rw [Quasithin.conjSub_sup, L32A.conjSub_eq_self_iff.mpr hg]
      refine sup_le le_sup_left ?_
      have e : Quasithin.conjSub g (Subgroup.zpowers z') =
          Subgroup.zpowers (g * z' * g⁻¹) :=
        MonoidHom.map_zpowers (MulAut.conj g).toMonoidHom z'
      rw [e, Subgroup.zpowers_le]
      have e2 : g * z' * g⁻¹ = (g * z' * g⁻¹ * z'⁻¹) * z' := by group
      rw [e2]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hc) (Subgroup.mem_sup_right
        (Subgroup.mem_zpowers z'))
    have heq := Subgroup.eq_of_le_of_card_ge hle (by
      rw [show Nat.card ↥(Quasithin.conjSub g (V₁ ⊔ Subgroup.zpowers z')) =
          Nat.card ↥(V₁ ⊔ Subgroup.zpowers z') from
        Subgroup.card_map_of_injective (MulAut.conj g).injective])
    exact L32A.conjSub_eq_self_iff.mp heq

variable {T L V K : Subgroup G} {t₀ : G}

namespace TopCtx

variable (X : TopCtx T L V K (fsuV1 T V) t₀) [IsMulCommutative ↥(conjClosure V (A6.g1 T V))]
  {F : Type} [Field F] (e : Hat V (A6.g1 T V) (fsuV1 T V) ≃* VM F)

abbrev CfgAt (t : ↥(A6.g1 T V)) {z' : G} (hz'U : z' ∈ conjClosure V (A6.g1 T V)) : Prop :=
  L2Cfg F ((X.img (A6.g1 T V)).map (MulAut.congr e).toMonoidHom)
    ((X.img T).map (MulAut.congr e).toMonoidHom)
    ((X.img (l1 T L V)).map (MulAut.congr e).toMonoidHom)
    ((X.img (pCoreOf 2 (l1 T L V ⊔ T))).map (MulAut.congr e).toMonoidHom)
    ((X.img (pCoreOf 2 (l1 T L V))).map (MulAut.congr e).toMonoidHom)
    ((vHat V (A6.g1 T V) (fsuV1 T V)).map e.toMonoidHom) (MulAut.congr e (X.top.act t))
    (e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))) ⟨z', hz'U⟩))

variable {X e}

theorem fix_iff_comm (g : ↥(A6.g1 T V)) {z' : G} (hz'U : z' ∈ conjClosure V (A6.g1 T V)) :
    MulAut.congr e (X.top.act g)
        (e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))) ⟨z', hz'U⟩)) =
      e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))) ⟨z', hz'U⟩) ↔
    (g : G) * z' * (g : G)⁻¹ * z'⁻¹ ∈ fsuV1 T V := by
  rw [congr_apply_e, e.apply_eq_iff_eq, X.top.act_mk, ← mul_inv_eq_one, ← map_inv, ← map_mul,
    A6.A6Mod.secMk_eq_one_iff]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]

theorem mem_normalizer_iff_fix (hF : HypF98 T V L (fsuV1 T V) V (A6.g1 T V)) {z z' : G}
    (hz : Subgroup.zpowers z = fsuV1 T V) (h : A114Hyp (fsuV1 T V ⊔ Subgroup.zpowers z') z z')
    (hz'U : z' ∈ conjClosure V (A6.g1 T V)) (g : ↥(A6.g1 T V)) :
    (g : G) ∈ Subgroup.normalizer ((fsuV1 T V ⊔ Subgroup.zpowers z' : Subgroup G) : Set G) ↔
      MulAut.congr e (X.top.act g)
        (e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))) ⟨z', hz'U⟩)) =
      e (InternalSec.secMk ((fsuV1 T V).subgroupOf (conjClosure V (A6.g1 T V))) ⟨z', hz'U⟩) := by
  have hgz : (g : G) * z * (g : G)⁻¹ = z := by
    have hgC : (g : G) ∈ Subgroup.centralizer ({z} : Set G) := by
      rw [centralizer_singleton_eq hF hz]
      exact g.2
    rw [Subgroup.mem_centralizer_singleton_iff.mp hgC, mul_inv_cancel_right]
  rw [fix_iff_comm (X := X) (e := e), mem_normalizer_sup_iff hz h g.2 hgz]

end TopCtx

end CFSG.Quasithin.H13.L32A.L2

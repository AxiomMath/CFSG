module

public import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIDefs
import CFSG.RankThree.PartTwo.Sec18.Item189StepInspectIL2OddDickson
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec18

open scoped MatrixGroups

theorem inspect189L2Odd : Inspect189L2Odd := by
  rintro Y _ _ X Q x p f _ hd hp2 hp3 hf ⟨e⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φ : X ≃* PSL(2, GaloisField p f) := e.trans (Sec4.projSLEquivPSL (GaloisField p f))
  set J := (X ⊓ Subgroup.normalizer (Q : Set Y)) ⊔
    (X ⊓ Subgroup.normalizer (Subgroup.zpowers x : Set Y))
  set H : Subgroup PSL(2, GaloisField p f) := (J.subgroupOf X).map φ.toMonoidHom with hH
  set T : Subgroup PSL(2, GaloisField p f) := (Q.subgroupOf X).map φ.toMonoidHom with hTdef
  set x₀ : X := ⟨x, hd.mem⟩ with hx₀
  have hT : Nat.card T = 2 ^ (Nat.card PSL(2, GaloisField p f)).factorization 2 := by
    have hS := hd.sylow.inf_of_le_normalizer le_top
      (Subgroup.normalizer_eq_top_iff.mpr hd.normal).ge
    rw [hTdef, Subgroup.card_map_of_injective φ.injective, ← Subgroup.inf_subgroupOf_right,
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv, hS.card_eq,
      Nat.card_congr φ.toEquiv]
  have hTH : T ≤ H := by
    refine Subgroup.map_mono fun g hg => ?_
    rw [Subgroup.mem_subgroupOf] at hg ⊢
    exact Subgroup.mem_sup_left ⟨g.2, Subgroup.le_normalizer hg⟩
  have hx : orderOf (φ x₀) = 3 := by
    rw [MulEquiv.orderOf_eq, hx₀, Subgroup.orderOf_mk, hd.orderOf_eq]
  have hxT : φ x₀ ∈ Subgroup.normalizer (T : Set PSL(2, GaloisField p f)) := by
    rw [hTdef, ← Subgroup.map_equiv_normalizer_eq]
    refine Subgroup.mem_map_of_mem φ.toMonoidHom (Subgroup.le_normalizer_comap X.subtype ?_)
    exact hd.mem_normalizer
  have hN : Subgroup.normalizer (Subgroup.zpowers (φ x₀) : Set PSL(2, GaloisField p f)) ≤ H := by
    have hz : Subgroup.zpowers (φ x₀) = (Subgroup.zpowers x₀).map φ.toMonoidHom :=
      (MonoidHom.map_zpowers φ.toMonoidHom x₀).symm
    rw [hz, ← Subgroup.map_equiv_normalizer_eq]
    refine Subgroup.map_mono fun g hg => ?_
    rw [Subgroup.mem_subgroupOf]
    refine Subgroup.mem_sup_right ⟨g.2, ?_⟩
    have h := Subgroup.le_normalizer_map X.subtype (Subgroup.mem_map_of_mem X.subtype hg)
    rwa [MonoidHom.map_zpowers] at h
  have htop := eq_top_l2odd189 hp2 hp3 hf hT hTH hx hxT hN
  show X ≤ J
  intro g hg
  have hmem : φ ⟨g, hg⟩ ∈ H := htop ▸ Subgroup.mem_top _
  rw [hH, Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply] at hmem
  exact hmem

end CFSG.RankThree.PartTwo.Sec18

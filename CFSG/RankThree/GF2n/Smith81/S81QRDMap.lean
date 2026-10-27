module

public import CFSG.RankThree.GF2n.Smith81.S81VRoot

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

variable {K : Type} [Field K] {Γ Γ' : Type} [Group Γ] [Group Γ']

@[expose] def RootDatum.mapEquiv (R : RootDatum K Γ) (e : Γ ≃* Γ') : RootDatum K Γ' where
  N := R.N
  u n := e (R.u n)
  u_add n m := by rw [R.u_add, map_mul]
  τ := R.τ
  n₁ := R.n₁
  τ_n₁ := R.τ_n₁
  P := R.P.map (e : Γ →* Γ')
  Ad := R.Ad.comp (e.subgroupMap R.P).symm.toMonoidHom
  u_Ad g n := by
    have h := R.u_Ad ((e.subgroupMap R.P).symm g) n
    have hg : (g : Γ') = e (((e.subgroupMap R.P).symm g : R.P) : Γ) := by
      simp [MulEquiv.subgroupMap_symm_apply]
    show e (R.u (R.Ad ((e.subgroupMap R.P).symm g) n)) = (g : Γ') * e (R.u n) * (g : Γ')⁻¹
    rw [h, hg, map_mul, map_mul, map_inv]
  d := (e.subgroupMap R.P).toMonoidHom.comp R.d
  Ad_d c := by
    show R.Ad ((e.subgroupMap R.P).symm (e.subgroupMap R.P (R.d c))) R.n₁ = _
    rw [MulEquiv.symm_apply_apply]
    exact R.Ad_d c
  s := e R.s
  s_sq := by rw [← map_mul, R.s_sq, map_one]
  s_d c := by
    show e R.s * ((e.subgroupMap R.P (R.d c) : R.P.map (e : Γ →* Γ')) : Γ') * e R.s =
      ((e.subgroupMap R.P (R.d c) : R.P.map (e : Γ →* Γ')) : Γ')⁻¹
    rw [MulEquiv.coe_subgroupMap_apply, ← map_inv, ← map_mul, ← map_mul, R.s_d c]
  ker_stab n hn := by
    obtain ⟨g, hg⟩ := R.ker_stab n hn
    refine ⟨e.subgroupMap R.P g, ?_⟩
    rw [MulEquiv.coe_subgroupMap_apply, hg, map_mul, map_mul]
  lemmaS n hn := by
    obtain ⟨g, hg⟩ := R.lemmaS n hn
    refine ⟨e.subgroupMap R.P g, ?_⟩
    show R.τ (R.Ad ((e.subgroupMap R.P).symm (e.subgroupMap R.P g)) n) ≠ 0
    rw [MulEquiv.symm_apply_apply]
    exact hg
  braid := by
    show e R.s = e (R.u ((1 : K) • R.n₁)) * (e R.s * e (R.u ((1 : K) • R.n₁)) * e R.s) *
      e (R.u ((1 : K) • R.n₁))
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul, ← R.braid]

end CFSG.RankThree.GF2n.Smith81.S81V

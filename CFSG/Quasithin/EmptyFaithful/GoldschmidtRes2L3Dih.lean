module

public import CFSG.Walter.PSL2Facts.Odd
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.Quasithin.Gap6R2.L3

open scoped MatrixGroups

theorem odd_mem_zpowers_r {n : ℕ} [NeZero n] {x : DihedralGroup n} (hx : Odd (orderOf x)) :
    ∃ k : ℕ, x = DihedralGroup.r 1 ^ k := by
  cases x with
  | r i =>
    refine ⟨i.val, ?_⟩
    rw [DihedralGroup.r_one_pow, ZMod.natCast_zmod_val]
  | sr i =>
    rw [DihedralGroup.orderOf_sr] at hx
    exact absurd hx (by decide)

theorem exists_zpowers_of_odd_centralizer {X : Type} [Group X] {p f : ℕ} [Fact p.Prime]
    (hp : Odd p) (hf : 0 < f) (h7 : 7 ≤ p ^ f)
    (hmod : CFSG.Assembly.LowTwoRank.StatedClassicalModel X .PSL 2 p f) {g : X}
    (hg : orderOf g = 2) :
    ∃ c : X, ∀ x ∈ Subgroup.centralizer ({g} : Set X), Odd (orderOf x) →
      x ∈ Subgroup.zpowers c := by
  obtain ⟨-, K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hmod
  let e' : X ≃* PSL(2, K) :=
    e.trans (CFSG.Assembly.LowTwoRank.projectiveSpecialLinearGroupEquivStatedProj 2 K).symm
  have hg' : orderOf (e' g) = 2 := by rw [MulEquiv.orderOf_eq]; exact hg
  obtain ⟨n, hn4, -, -, ⟨d⟩⟩ :=
    CFSG.Walter.psl2_centralizer_involution_dihedral K hKcard hp hf h7 hg'
  have : NeZero n := ⟨by omega⟩
  set c₀ : PSL(2, K) := ((d.symm (DihedralGroup.r 1) : Subgroup.centralizer {e' g}) : PSL(2, K))
  refine ⟨e'.symm c₀, fun x hx hodd => ?_⟩
  have hxc : e' x ∈ Subgroup.centralizer ({e' g} : Set PSL(2, K)) := by
    rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
    rw [← map_mul, ← map_mul, hx]
  set z : Subgroup.centralizer ({e' g} : Set PSL(2, K)) := ⟨e' x, hxc⟩ with hz
  have hzodd : Odd (orderOf (d z)) := by
    rw [MulEquiv.orderOf_eq, ← Subgroup.orderOf_coe, hz]
    simp only
    rw [MulEquiv.orderOf_eq]
    exact hodd
  obtain ⟨k, hk⟩ := odd_mem_zpowers_r hzodd
  have hzk : z = (d.symm (DihedralGroup.r 1)) ^ k := by
    apply d.injective
    rw [map_pow, MulEquiv.apply_symm_apply, ← hk]
  have hxk : e' x = c₀ ^ k := by
    have := congrArg Subtype.val hzk
    simpa [hz, c₀] using this
  refine ⟨k, ?_⟩
  apply e'.injective
  simp [hxk, map_pow]

end CFSG.Quasithin.Gap6R2.L3

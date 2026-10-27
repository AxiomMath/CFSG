module

public import CFSG.RankThree.GF2n.Smith81.S81R213Four
public import CFSG.RankThree.GF2n.Smith81.S81RD8Model
public import CFSG.RankThree.GF2n.Smith81.S81R213Comm

public section

namespace CFSG.RankThree.GF2n.Smith81.E3LRoot

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Stroth80 CFSG.RankThree.GF2n.Smith81.EGeom
  CFSG.RankThree.GF2n.Smith81.A5Cube CFSG.RankThree.GF2n.Smith81.E3LBridge
  CFSG.RankThree.GF2n.Smith81.E3LCond CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement

@[expose] def E3LD8CentreStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G), Smith1981Below (Nat.card G) →
    SmithECfg M Q Z B → InCaseE3L M Q Z B → ∀ z ∈ Z, z ≠ 1 →
      ∀ x y : G, IsConj z x → IsConj z y → x ∈ M → y ∈ M → x ∉ Q → y ∉ Q → x * y ∉ Q →
        orderOf (x * y) = 4 → IsConj z ((x * y) ^ 2)

variable {G : Type} [Group G]

section K4

variable [Finite G] {M Q Z B : Subgroup G} {K : Type} [Field K]
  [Finite K] [CharP K 2] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ} {ψ : M₀.E ≃ₗ[K] Cube K}
  {φ : Lgen M (LB M Q B) →* (Cube K ≃ₗ[K] Cube K)} {z : G}

theorem concl_four (Dt : E3LDat M Q Z B K γ M₀ ψ φ z) (hNF : Smith212ENonfusedE3LStatement)
    (IH : Smith1981Below (Nat.card G)) (hSE : SmithECfg M Q Z B) (hc3 : InCaseE3L M Q Z B)
    (hD8 : E3LD8CentreStatement) {x y : G} (hxc : IsConj z x) (hxM : x ∈ M) (hxQ : x ∉ Q)
    (hyc : IsConj z y) (hyM : y ∈ M) (hyQ : y ∉ Q) {gx gy : GL (Fin 6) K}
    (hgx : IsTransvec K gx) (hgy : IsTransvec K gy) (hx : ActsAs φ x gx) (hy : ActsAs φ y gy)
    (h4 : orderOf (gx * gy) = 4) : orderOf (x * y) = 4 ∧ IsConj z ((x * y) ^ 2) := by
  have H : StrothHyp M Q Z := Dt.ctx.hyp
  have hxx : x * x = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hxc
  have hyy : y * y = 1 := mul_self_eq_one_of_isConj_Z H Dt.hz hyc
  have hyinv : y⁻¹ = y := inv_eq_of_mul_eq_one_right hyy
  have hgxx : gx * gx = 1 := isTransvec_mul_self hgx
  have hgyy : gy * gy = 1 := isTransvec_mul_self hgy
  have hgxinv : gx⁻¹ = gx := inv_eq_of_mul_eq_one_right hgxx
  have hgyinv : gy⁻¹ = gy := inv_eq_of_mul_eq_one_right hgyy
  have hx'A : ActsAs φ (y * x * y⁻¹) (gy * gx * gy⁻¹) := hx.conj hy
  have hx'M : y * x * y⁻¹ ∈ M := M.mul_mem (M.mul_mem hyM hxM) (M.inv_mem hyM)
  have hx'Q : y * x * y⁻¹ ∉ Q := by
    intro h
    apply hxQ
    have h1 := conj_mem_Q H (M.inv_mem hyM) h
    simpa [mul_assoc] using h1
  have hx'c : IsConj z (y * x * y⁻¹) := hxc.trans (isConj_iff.mpr ⟨y, rfl⟩)
  have hgx' : IsTransvec K (gy * gx * gy⁻¹) := by
    simpa only [inv_inv] using isTransvec_conj (c := gy⁻¹) hgx
  have hg4 : (gx * gy) ^ 4 = 1 := h4 ▸ pow_orderOf_eq_one _
  have hcomm : gx * (gy * gx * gy⁻¹) = (gy * gx * gy⁻¹) * gx := by
    have hw2 : ((gx * gy) ^ 2) * ((gx * gy) ^ 2) = 1 := by
      rw [← pow_add]
      exact hg4
    have hwinv : (gx * gy)⁻¹ = gy * gx := by rw [mul_inv_rev, hgyinv, hgxinv]
    calc gx * (gy * gx * gy⁻¹) = (gx * gy) ^ 2 := by rw [hgyinv, pow_two]; group
      _ = ((gx * gy) ^ 2)⁻¹ := (inv_eq_of_mul_eq_one_right hw2).symm
      _ = (gy * gx) ^ 2 := by rw [← inv_pow, hwinv]
      _ = (gy * gx * gy⁻¹) * gx := by rw [hgyinv, pow_two]; group
  have hnot := not_prop_conj_of_orderOf_four hgx hgy h4
  have hclose := two_close_of_comm Dt hxc hxM hxQ hx'c hx'M hx'Q hgx hgx' hx hx'A hcomm hnot
  have hsq : x * (y * x * y⁻¹) = (x * y) ^ 2 := by rw [hyinv, pow_two]; group
  have hv : (x * y) ^ 4 = 1 ∨ InZClass Z ((x * y) ^ 4) := by
    have e : ((x * y) ^ 2) ^ 2 = (x * y) ^ 4 := (pow_mul (x * y) 2 2).symm
    rw [hsq, e] at hclose
    exact hclose
  have h44 : (x * y) ^ 4 = 1 := pow_four_eq_one hNF IH hSE hc3 Dt.hz Dt.hz1 hxc hyc hv
  have hU : ActsAs φ ((x * y) ^ 2) ((gx * gy) ^ 2) := (hx.mul hy).pow 2
  have hsqQ : (x * y) ^ 2 ∉ Q := hU.not_mem_Q Dt (rho_sq_ne_one_of_orderOf_four h4)
  have hxyQ : x * y ∉ Q := fun h => hsqQ (Q.pow_mem h 2)
  have hdvd : orderOf (x * y) ∣ 4 := orderOf_dvd_of_pow_eq_one h44
  have hnd : ¬ orderOf (x * y) ∣ 2 := by
    intro h
    apply hsqQ
    rw [orderOf_dvd_iff_pow_eq_one.mp h]
    exact Q.one_mem
  have hord : orderOf (x * y) = 4 := by
    have hle : orderOf (x * y) ≤ 4 := Nat.le_of_dvd (by norm_num) hdvd
    have hpos : 0 < orderOf (x * y) := orderOf_pos _
    have h1 : orderOf (x * y) ≠ 1 := fun h => hnd (by rw [h]; exact one_dvd 2)
    have h2 : orderOf (x * y) ≠ 2 := fun h => hnd (by rw [h])
    have h3 : orderOf (x * y) ≠ 3 := fun h => by rw [h] at hdvd; omega
    omega
  exact ⟨hord, hD8 G M Q Z B IH hSE hc3 z Dt.hz Dt.hz1 x y hxc hyc hxM hyM hxQ hyQ hxyQ hord⟩

end K4

end CFSG.RankThree.GF2n.Smith81.E3LRoot

module

public import CFSG.RankThree.GF2n.Stroth80.DictModel

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}
variable {K : Type} [Field K] [Finite K] {γ : G → K} {M₀ : Tim79.QuadModel Q Z K γ}

@[expose] def eichlerMap (M₀ : Tim79.QuadModel Q Z K γ) (b u y : M₀.E) : M₀.E :=
  y + M₀.B y b • u + M₀.B y u • b + (M₀.Qf u * M₀.B y b) • b

theorem eichlerMap_add_smul [CharP K 2] (M₀ : Tim79.QuadModel Q Z K γ) {b v : M₀.E}
    (hbs : M₀.Qf b = 0) (hvb : M₀.B v b = 0) (lam : K) (y : M₀.E) :
    eichlerMap M₀ b (v + lam • b) y = eichlerMap M₀ b v y := by
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hQ : M₀.Qf (v + lam • b) = M₀.Qf v := by
    rw [M₀.Qf_add, M₀.Qf_smul, hbs, map_smul, hvb]
    simp
  unfold eichlerMap
  rw [hQ]
  simp only [map_add, map_smul, smul_eq_mul]
  have key' : (M₀.B y b * lam + lam * M₀.B y b) • b = 0 := by
    have : M₀.B y b * lam + lam * M₀.B y b = 0 := by linear_combination (lam * M₀.B y b) * h2
    rw [this, zero_smul]
  linear_combination (norm := module) key'

theorem Qf_eichlerMap_sub [CharP K 2] (M₀ : Tim79.QuadModel Q Z K γ) {b u : M₀.E}
    (hbs : M₀.Qf b = 0) (hub : M₀.B u b = 0) (hu : M₀.Qf u = 0) (y : M₀.E) :
    M₀.Qf (eichlerMap M₀ b u y - y) = 0 := by
  have hbu : M₀.B b u = 0 := by rw [Tim79.QuadModel.B_comm, hub, neg_zero]
  have e : eichlerMap M₀ b u y - y = M₀.B y b • u + (M₀.B y u + M₀.Qf u * M₀.B y b) • b := by
    unfold eichlerMap
    module
  rw [e, M₀.Qf_add, M₀.Qf_smul, M₀.Qf_smul, hu, hbs, map_smul, map_smul, LinearMap.smul_apply,
    hub]
  simp

end CFSG.RankThree.GF2n.Stroth80

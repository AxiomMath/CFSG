module

public import CFSG.Quasithin.EmptyFaithful.SzN17Dig

public section

namespace CFSG.Quasithin.SzN17

open CFSG.Open hiding StatedSL StatedClassicalModel StatedProj StatedLieTag StatedLieAdmissible
open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Assembly.LowTwoRank
open scoped commutatorElement

variable {V : Type} [CommGroup V] [Finite V]

theorem not_perfectCore_le_of_not_le (h56 : AsB56) (hV : ∀ v : V, v ^ 2 = 1)
    {Hs Js Ys Ss Ms : Subgroup (MulAut V)} (hJH : Js ≤ Hs)
    (hJn : ∀ h ∈ Hs, ∀ j ∈ Js, h * j * h⁻¹ ∈ Js) (hB53 : B53Hyp Js) (hYH : Ys ≤ Hs)
    (hYgen : Ys = Subgroup.closure {y | y ∈ Ys ∧ orderOf y = 3}) (hSyl : IsSylowTwoOf Ss Hs)
    (hSM : Ss ≤ Ms) (hKL : ∀ x ∈ Hs, (∀ y ∈ Ys, x * y = y * x) → x ∈ Ms) (hJM : ¬ Js ≤ Ms) :
    ¬ perfectCore Js ≤ Ms := by
  intro hperf
  have hJne : Js ≠ ⊥ := fun h => hJM (h ▸ bot_le)
  have hcases := h56 V hV Js hJne hB53
  have hJnorm : (Js.subgroupOf Hs).Normal :=
    (Subgroup.normal_subgroupOf_iff hJH).2 fun h k hh hk => hJn k hk h hh
  have hP : IsSylowTwoOf (Ss ⊓ Js) Js :=
    RankOneRecog.isSylowTwoOf_inf_of_subnormal hSyl hJH hJnorm.isSubnormal
  obtain ⟨Z, hZJ, hZ, hdec⟩ := digest_of_b56 hP hB53.2.1 hcases
  have hZM : Z ≤ Ms := by
    intro z hz
    refine hKL z (hJH (hZJ hz)) fun y hy => ?_
    have hYc : Ys ≤ Subgroup.centralizer {z} := by
      rw [hYgen]
      refine (Subgroup.closure_le _).2 ?_
      rintro y ⟨hyY, hy3⟩
      rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
      intro w hw
      rw [Set.mem_singleton_iff] at hw
      rw [hw]
      have hyH : y ∈ Hs := hYH hyY
      have hnorm : ∀ x, x ∈ Js ↔ y * x * y⁻¹ ∈ Js := fun x =>
        ⟨hJn y hyH x, fun hx => by
          have := hJn y⁻¹ (Hs.inv_mem hyH) _ hx
          simpa [mul_assoc] using this⟩
      have hy3' : y ^ 3 = 1 := by rw [← hy3]; exact pow_orderOf_eq_one y
      have hfix := hZ y hy3' hnorm z hz
      exact (mul_inv_eq_iff_eq_mul.1 hfix).symm
    have := Subgroup.mem_centralizer_iff.1 (hYc hy) z rfl
    exact this
  apply hJM
  refine hdec.trans (sup_le (sup_le hperf hZM) ?_)
  exact inf_le_left.trans hSM

end CFSG.Quasithin.SzN17

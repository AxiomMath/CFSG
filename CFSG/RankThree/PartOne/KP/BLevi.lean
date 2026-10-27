module

public import CFSG.RankThree.PartOne.KP.UnitaryTorus

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Fischer CFSG.Assembly.LowTwoRank

theorem isElementaryAbelian_of_subgroup {p : ℕ} {G : Type*} [Group G] [IsElementaryAbelian p G]
    (K : Subgroup G) : IsElementaryAbelian p K := by
  refine { toIsMulCommutative := ?_, exponent_dvd_p := ?_ }
  · exact ⟨⟨fun a b => Subtype.ext ((IsMulCommutative.is_comm (M := G)).comm a.1 b.1)⟩⟩
  · refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => Subtype.ext ?_
    have := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp
      (IsElementaryAbelian.exponent_dvd_p p G) x.1
    simpa using this

theorem exists_elementary_two_five {X : Type*} [Group X] (U9 : Subgroup X)
    (hU9 : IsElementaryAbelian 2 U9) (hc : Nat.card U9 = 2 ^ 9) :
    ∃ U : Subgroup X, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite U9 := Nat.finite_of_card_ne_zero (by rw [hc]; positivity)
  have hdvd : 2 ^ 5 ∣ Nat.card U9 := by
    rw [hc]
    exact Nat.pow_dvd_pow 2 (by norm_num)
  obtain ⟨K', hK'⟩ := Sylow.exists_subgroup_card_pow_prime 2 hdvd
  have := hU9
  have : IsElementaryAbelian 2 K' := isElementaryAbelian_of_subgroup K'
  refine ⟨K'.map U9.subtype, IsElementaryAbelian.map U9.subtype, ?_⟩
  rw [Subgroup.card_map_of_injective U9.subtype_injective, hK']

theorem elementary_two_five_of_levi {Cg : Type*} [Group Cg] (L : Subgroup Cg)
    (e : L ≃* StatedProj (StatedSU 6 (2 ^ 1) F4))
    (U9 : Subgroup (StatedProj (StatedSU 6 (2 ^ 1) F4))) (hU9 : IsElementaryAbelian 2 U9)
    (hc : Nat.card U9 = 2 ^ 9) :
    ∃ U : Subgroup Cg, IsElementaryAbelian 2 U ∧ Nat.card U = 2 ^ 5 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨U5, hU5, hc5⟩ := exists_elementary_two_five U9 hU9 hc
  have := hU5
  refine ⟨(U5.map e.symm.toMonoidHom).map L.subtype, ?_, ?_⟩
  · have : IsElementaryAbelian 2 (U5.map e.symm.toMonoidHom) := IsElementaryAbelian.map _
    exact IsElementaryAbelian.map _
  · rw [Subgroup.card_map_of_injective L.subtype_injective,
      Subgroup.card_map_of_injective e.symm.injective, hc5]

theorem central_cover_of_levi {Cg : Type*} [Group Cg] (L : Subgroup Cg)
    (e : L ≃* StatedProj (StatedSU 6 (2 ^ 1) F4)) (Y : Type) [Group Y] [Finite Y]
    (f : Y →* Cg) (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center Y) :
    ∃ V : Subgroup Y, IsElementaryAbelian 3 V ∧ Nat.card V = 3 ^ 4 := by
  let YL : Subgroup Y := L.comap f
  let φ : YL →* StatedProj (StatedSU 6 (2 ^ 1) F4) :=
    e.toMonoidHom.comp ((f.comp YL.subtype).codRestrict L (fun y => y.2))
  have hφ : Function.Surjective φ := by
    intro x
    obtain ⟨y, hy⟩ := hf (e.symm x : Cg)
    have hyL : y ∈ YL := by
      show f y ∈ L
      rw [hy]
      exact (e.symm x).2
    refine ⟨⟨y, hyL⟩, ?_⟩
    show e (⟨f y, hyL⟩ : L) = x
    rw [show (⟨f y, hyL⟩ : L) = e.symm x from Subtype.ext hy]
    exact e.apply_symm_apply x
  have hφk : φ.ker ≤ Subgroup.center YL := by
    intro y hy
    have h1 : f y = 1 := by
      rw [MonoidHom.mem_ker] at hy
      have h0 : e (⟨f y, y.2⟩ : L) = 1 := hy
      have h2 : (⟨f y, y.2⟩ : L) = 1 := e.injective (h0.trans (map_one e).symm)
      exact congrArg Subtype.val h2
    have h3 : (y : Y) ∈ Subgroup.center Y := hker ((MonoidHom.mem_ker).2 h1)
    rw [Subgroup.mem_center_iff]
    intro z
    exact Subtype.ext ((Subgroup.mem_center_iff.1 h3 z.1))
  obtain ⟨U, hU, hUc⟩ := stated_psu6_central_cover φ hφ hφk
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have := hU
  refine ⟨U.map YL.subtype, IsElementaryAbelian.map _, ?_⟩
  rw [Subgroup.card_map_of_injective YL.subtype_injective, hUc]

end CFSG.RankThree.PartOne

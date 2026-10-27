module

public import CFSG.Quasithin.Vol2.Ch10SecQ9H45
public import CFSG.Quasithin.Vol2.Ch10SecQ9H29

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.KRS

open Matrix C10P4F

theorem det_blk23 {g : SL5} (hg : g ∈ P2) : (blk23 g).det = 1 := by
  have h := blk23_mul hg (P2.inv_mem hg)
  rw [mul_inv_cancel, blk23_one] at h
  have h2 := congrArg Matrix.det h
  rw [Matrix.det_one, Matrix.det_mul] at h2
  exact eq_one_of_mul_eq_one h2.symm

@[expose] def mu3 : ↥P2 →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) where
  toFun g := ⟨blk23 g, det_blk23 g.2⟩
  map_one' := Subtype.ext blk23_one
  map_mul' g h := Subtype.ext (blk23_mul g.2 h.2)

theorem mem_uniSL_of_mu3 {g : ↥P2} (hg : mu3 g = 1) : (g : SL5) ∈ uniSL 5 :=
  radP2_le_uniSL ⟨g.2, congrArg Subtype.val hg⟩

theorem card_le_three_of_le_P2 {Q : Subgroup SL5} (hQ : Q ≤ P2) (h3 : IsPGroup 3 Q) :
    Nat.card Q ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let f : ↥Q →* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2) :=
    mu3.comp (Subgroup.inclusion hQ)
  have hinj : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro q hq
    have hU := mem_uniSL_of_mu3 hq
    obtain ⟨k, hk⟩ := isPGroup_uniSL_five ⟨q, hU⟩
    obtain ⟨m, hm⟩ := h3 q
    have hk' : (q : SL5) ^ 2 ^ k = 1 := congrArg Subtype.val hk
    have hm' : q ^ 3 ^ m = 1 := hm
    have h1 : orderOf q ∣ 3 ^ m := orderOf_dvd_of_pow_eq_one hm'
    have h2 : orderOf q ∣ 2 ^ k := by
      rw [← Subgroup.orderOf_coe]
      exact orderOf_dvd_of_pow_eq_one hk'
    have hc : Nat.Coprime (3 ^ m) (2 ^ k) := Nat.Coprime.pow _ _ (by norm_num)
    exact orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hc h1 h2)
  have hdvd : Nat.card Q ∣ 6 := by
    have := Subgroup.card_dvd_of_injective f hinj
    have h6 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
      rw [Nat.card_eq_fintype_card]
      decide
    rwa [h6] at this
  obtain ⟨n, hn⟩ := h3.exists_card_eq
  rw [hn] at hdvd ⊢
  have : n ≤ 1 := by
    by_contra h
    have h9 : 3 ^ 2 ∣ 3 ^ n := pow_dvd_pow 3 (by omega)
    have := h9.trans hdvd
    norm_num at this
  interval_cases n <;> norm_num

end CFSG.Quasithin.Vol2.Ch10.SecC.KRS

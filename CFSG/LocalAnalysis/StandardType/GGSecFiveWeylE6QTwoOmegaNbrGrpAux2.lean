module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveWeylE6QTwoOmegaNbrGrpAux
public import CFSG.GroupTheory.InvertingElements
public import CFSG.Quasithin.Background.A318PC7

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G]

private theorem E6QTwo.exists_mul_mem_zpowers_and_closure {Bs K' : Subgroup G} {y : G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hyB : y ∈ Bs)
    (hC : Nat.card (Subgroup.closure
      {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}) = 3 ^ 4)
    (hyC : (⟨y, hyB⟩ : ↥Bs) ∉
      Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹})
    {b : G} (hb : b ∈ Bs) :
    ∃ z ∈ Subgroup.zpowers y, ∃ c ∈
      (Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs,
        b = φ c * c⁻¹}).map Bs.subtype, b = z * c := by
  classical
  let Cb : Subgroup ↥Bs :=
    Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}
  let Zb : Subgroup ↥Bs := Subgroup.zpowers (⟨y, hyB⟩ : ↥Bs)
  have hy1 : y ≠ 1 := E6QTwo.y_ne_one_of_notMem_closure hyB hyC
  have hy3 : (⟨y, hyB⟩ : ↥Bs) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hBs.2 y hyB
  have hZcard : Nat.card Zb = 3 := by
    rw [Nat.card_zpowers, orderOf_eq_prime hy3 (fun h => hy1 (congrArg Subtype.val h))]
  have hCy : ∀ b : ↥Bs, b ∈ Cb → b ∈ Zb → b = 1 := by
    intro b hbC hbZ
    by_contra hb1
    have hb3 : b ^ 3 = 1 := by
      apply Subtype.ext
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact hBs.2 b.val b.2
    have hbord : Nat.card (Subgroup.zpowers b) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hb3 hb1]
    have hle : Subgroup.zpowers b ≤ Zb := Subgroup.zpowers_le.mpr hbZ
    have heq : Subgroup.zpowers b = Zb :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hbord, hZcard])
    have hy_mem : (⟨y, hyB⟩ : ↥Bs) ∈ Subgroup.zpowers b := by
      rw [heq]
      exact Subgroup.mem_zpowers _
    exact hyC (Subgroup.zpowers_le.mpr hbC hy_mem)
  have hdis : Zb ⊓ Cb = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    rintro x ⟨hxZ, hxC⟩
    exact hCy x hxC hxZ
  have hdisj : Disjoint Zb Cb := disjoint_iff_inf_le.mpr (by rw [hdis])
  have hcardMul : Nat.card Zb * Nat.card Cb = Nat.card ↥Bs := by
    rw [hZcard, hC, hcard]
    norm_num
  have hcomp : Zb.IsComplement' Cb :=
    Subgroup.isComplement'_of_card_mul_and_disjoint hcardMul hdisj
  obtain ⟨x, hx⟩ := hcomp.2 (⟨b, hb⟩ : ↥Bs)
  obtain ⟨z, c⟩ := x
  let zG : G := (z : ↥Bs)
  let cG : G := (c : ↥Bs)
  have hzc' : zG * cG = b := by
    have h := congrArg Subtype.val hx
    simpa [zG, cG] using h
  refine ⟨zG, ?_, cG, ?_, hzc'.symm⟩
  · obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (z.2 : (z : ↥Bs) ∈ Zb)
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have hk' := congrArg Subtype.val hk
    rw [Subgroup.coe_zpow] at hk'
    exact hk'
  · exact Subgroup.mem_map_of_mem Bs.subtype c.2

theorem E6QTwo.isPGroup_le_centralizer_bstar {Bs K' : Subgroup G} {y : G}
    (hBs : IsElemAbelian 3 Bs) (hcard : Nat.card Bs = 3 ^ 5) (hyB : y ∈ Bs)
    (hBsN : Bs ≤ Subgroup.normalizer (K' : Set G))
    (hC : Nat.card (Subgroup.closure
      {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}) = 3 ^ 4)
    (hyC : (⟨y, hyB⟩ : ↥Bs) ∉
      Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹})
    {Q : Subgroup G} (hQy : Q ≤ Subgroup.centralizer ({y} : Set G))
    (hQK : Q ≤ Subgroup.centralizer (K' : Set G)) :
    Q ≤ Subgroup.centralizer (Bs : Set G) := by
  classical
  let Cb : Subgroup ↥Bs :=
    Subgroup.closure {b : ↥Bs | ∃ φ ∈ ggAutomizer K' Bs, ∃ c : ↥Bs, b = φ c * c⁻¹}
  let Cg : Subgroup G := Cb.map Bs.subtype
  have hCgK : Cg ≤ K' := E6QTwo.closure_map_subtype_le_of_le_normalizer hBsN
  intro q hq
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨z, hz, c, hc, rfl⟩ :=
    E6QTwo.exists_mul_mem_zpowers_and_closure hBs hcard hyB hC hyC hb
  have hqy : q * y = y * q := Subgroup.mem_centralizer_singleton_iff.mp (hQy hq)
  have hzq : q * z = z * q := by
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hconjqy : (MulAut.conj q) y = y := by
      rw [MulAut.conj_apply, hqy, mul_assoc, mul_inv_cancel, mul_one]
    have hconj : q * (y ^ k) * q⁻¹ = y ^ k := by
      rw [← MulAut.conj_apply q (y ^ k), map_zpow, hconjqy]
    calc q * z = q * y ^ k := by rw [hk]
      _ = y ^ k * q := by
        calc q * y ^ k = (q * y ^ k * q⁻¹) * q := by group
          _ = y ^ k * q := by rw [hconj]
      _ = z * q := by rw [hk]
  have hcq : q * c = c * q :=
    (Subgroup.mem_centralizer_iff.mp (hQK hq) c (hCgK hc)).symm
  calc (z * c) * q = z * (c * q) := by group
    _ = z * (q * c) := by rw [← hcq]
    _ = (z * q) * c := by group
    _ = (q * z) * c := by rw [← hzq]
    _ = q * (z * c) := by group

private theorem E6QTwo.conj_eq_or_conj_eq_inv_of_isCyclic {X : Type} [Group X] [Finite X]
    {Q : Subgroup X} (hQ : IsCyclic Q) {y n : X} (hyQ : y ∈ Q) (hy : orderOf y = 3)
    (hn : n ∈ Subgroup.normalizer (Q : Set X)) :
    n * y * n⁻¹ = y ∨ n * y * n⁻¹ = y⁻¹ := by
  classical
  let yQ : Q := ⟨y, hyQ⟩
  have hy'Q_mem : n * y * n⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp hn y).mp hyQ
  let y'Q : Q := ⟨n * y * n⁻¹, hy'Q_mem⟩
  have hyQ3 : orderOf yQ = 3 := by
    rw [Subgroup.orderOf_mk]
    exact hy
  have hy'Q3 : orderOf y'Q = 3 := by
    rw [Subgroup.orderOf_mk]
    rw [← MulAut.conj_apply n y]
    rw [MulEquiv.orderOf_eq (MulAut.conj n) y, hy]
  have hcard : Nat.card (Subgroup.zpowers y'Q) = Nat.card (Subgroup.zpowers yQ) := by
    rw [Nat.card_zpowers, Nat.card_zpowers, hy'Q3, hyQ3]
  have hEq : Subgroup.zpowers y'Q = Subgroup.zpowers yQ :=
    (IsCyclic.subgroup_eq_iff_card_eq).mpr hcard
  have hmem : y'Q ∈ Subgroup.zpowers yQ := by
    rw [← hEq]
    exact Subgroup.mem_zpowers _
  obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hjden : j % (orderOf yQ : ℤ) = j % 3 := by
    rw [hyQ3]
    norm_num
  have hj' : yQ ^ (j % 3) = y'Q := by
    rw [← hjden, zpow_mod_orderOf, hj]
  have hge : 0 ≤ j % 3 := Int.emod_nonneg j (by norm_num)
  have hlt : j % 3 < 3 := Int.emod_lt_of_pos j (by norm_num)
  have h : y'Q = yQ ∨ y'Q = yQ⁻¹ := by
    interval_cases hj3 : j % 3
    · exfalso
      have h1 : y'Q = 1 := by simpa using hj'.symm
      rw [h1, orderOf_one] at hy'Q3
      omega
    · left
      simpa using hj'.symm
    · right
      have h3 : yQ ^ 3 = 1 := by
        rw [← hyQ3]
        exact pow_orderOf_eq_one yQ
      have h2 : yQ ^ (2 : ℤ) = yQ⁻¹ := by
        rw [← zpow_neg_one, zpow_eq_zpow_iff_modEq, hyQ3]
        norm_num
      exact hj'.symm.trans h2
  rcases h with h | h
  · left
    have := congrArg Subtype.val h
    simpa [y'Q, yQ] using this
  · right
    have := congrArg Subtype.val h
    simpa [y'Q, yQ] using this

theorem E6QTwo.eq_of_isPGroup_normalizes_isCyclic_three {X : Type} [Group X] [Finite X]
    {Q : Subgroup X} (hQ : IsCyclic Q) {y n : X} (hyQ : y ∈ Q)
    (hy1 : y ≠ 1) (hy3 : y ^ 3 = 1) (hnN : n ∈ Subgroup.normalizer (Q : Set X))
    (hn : IsPGroup 3 (Subgroup.zpowers n)) :
    n * y * n⁻¹ = y := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases E6QTwo.conj_eq_or_conj_eq_inv_of_isCyclic hQ hyQ (orderOf_eq_prime hy3 hy1) hnN
    with h | h
  · exact h
  · exfalso
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf (p := 3) (G := Subgroup.zpowers n)).mp hn
      ⟨n, Subgroup.mem_zpowers n⟩
    have hk' : orderOf n = 3 ^ k := by
      rw [show orderOf n = orderOf (⟨n, Subgroup.mem_zpowers n⟩ : ↥(Subgroup.zpowers n)) from
        (Subgroup.orderOf_coe (⟨n, Subgroup.mem_zpowers n⟩ : ↥(Subgroup.zpowers n)))]
      exact hk
    have hodd : Odd (orderOf n) := by
      rw [hk']
      exact Odd.pow (n := k) (by norm_num)
    have h2 := CFSG.GroupTheory.pow_odd_inverts h hodd (m := orderOf n)
    rw [pow_orderOf_eq_one, one_mul, inv_one, mul_one] at h2
    have hy2 : y ^ 2 = 1 := by
      rw [pow_two]
      exact eq_inv_iff_mul_eq_one.mp h2
    have hdvd : orderOf y ∣ 2 := orderOf_dvd_of_pow_eq_one hy2
    rw [orderOf_eq_prime hy3 hy1] at hdvd
    norm_num at hdvd

end CFSG.StandardType

end

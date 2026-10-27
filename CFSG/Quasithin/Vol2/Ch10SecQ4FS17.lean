module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS16

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G] [Finite G]

theorem card_le_three_of_centralizer (hK : quasithinIsQTKECat G) {R J : Subgroup G}
    (hR : R ≠ ⊥) (hR2 : IsPGroup 2 R) (hJR : J ≤ Subgroup.normalizer (R : Set G)) {y : G}
    (hy3 : y ^ 3 = 1) (hyR : y ∈ Subgroup.normalizer (R : Set G)) (hyJ : y ∉ J)
    (hJy : J ≤ Subgroup.centralizer ({y} : Set G)) {E : Subgroup G} (hEJ : E ≤ J)
    (hE : IsElemAbelian 3 E) : Nat.card E ≤ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hEc, hE3⟩ := hE
  have hcomm : ∀ e ∈ E, e * y = y * e := fun e he =>
    Subgroup.mem_centralizer_singleton_iff.mp (hJy (hEJ he))
  have hZE : Subgroup.zpowers y ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_iff.mpr hcomm)
  have hEE : E ≤ Subgroup.centralizer (E : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr hEc
  have hEZ : E ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) :=
    Subgroup.le_centralizer_iff.mpr hZE
  have hZZ : Subgroup.zpowers y ≤ Subgroup.centralizer (Subgroup.zpowers y : Set G) :=
    Subgroup.le_centralizer_iff_isMulCommutative.mpr inferInstance
  have hE'c : E ⊔ Subgroup.zpowers y ≤
      Subgroup.centralizer ((E ⊔ Subgroup.zpowers y : Subgroup G) : Set G) :=
    sup_le (Subgroup.le_centralizer_iff.mpr (sup_le hEE hZE))
      (Subgroup.le_centralizer_iff.mpr (sup_le hEZ hZZ))
  have hE'3 : ∀ x ∈ E ⊔ Subgroup.zpowers y, x ^ 3 = 1 := by
    intro x hx
    have hx' : x ∈ ((E ⊔ Subgroup.zpowers y : Subgroup G) : Set G) := hx
    rw [Subgroup.coe_mul_of_right_le_normalizer_left E _
      (hZE.trans (Subgroup.centralizer_le_normalizer _))] at hx'
    obtain ⟨e, he, z, hz, rfl⟩ := Set.mem_mul.mp hx'
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hc : Commute e (y ^ k) := (Commute.zpow_right (hcomm e he) k)
    rw [hc.mul_pow, hE3 e he, one_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul,
      zpow_natCast, hy3, one_zpow]
  have hE'el : IsElemAbelian 3 (E ⊔ Subgroup.zpowers y) :=
    ⟨Subgroup.le_centralizer_iff_isMulCommutative.mp hE'c, hE'3⟩
  have hp : ∀ {P : Subgroup G}, (∀ x ∈ P, x ^ 3 = 1) → IsPGroup 3 P := fun hP g =>
    ⟨1, Subtype.ext (by simpa using hP g g.2)⟩
  obtain ⟨j, hj⟩ := (hp hE'3).exists_card_eq
  obtain ⟨i, hi⟩ := (hp hE3).exists_card_eq
  have hloc : IsTwoLocal (Subgroup.normalizer (R : Set G)) := ⟨R, hR, hR2, rfl⟩
  have hj2 : j ≤ 2 := (CFSG.SectionRank.le_pRank (by norm_num)
    (sup_le (hEJ.trans hJR) (Subgroup.zpowers_le.mpr hyR)) hE'el hj).trans
    (pRank_le_two_of_isTwoLocal hK hloc Nat.prime_three (by norm_num))
  have hij : i < j := by
    have hdvd : 3 ^ i ∣ 3 ^ j := hi ▸ hj ▸ Subgroup.card_dvd_of_le le_sup_left
    have hle := (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < 3)).mp hdvd
    refine lt_of_le_of_ne hle fun h => hyJ (hEJ ?_)
    have heq : E = E ⊔ Subgroup.zpowers y :=
      Subgroup.eq_of_le_of_card_ge le_sup_left (by rw [hi, hj, h])
    rw [heq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  have hi1 : i ≤ 1 := by omega
  rw [hi]
  calc 3 ^ i ≤ 3 ^ 1 := Nat.pow_le_pow_right (by norm_num) hi1
    _ = 3 := by norm_num

namespace S5Data

variable {T L I H K : Subgroup G} {q t : G} (D : S5Data T L I H K q t)
include D

theorem orderOf_q2 : orderOf (t⁻¹ * q * t) = 3 := by
  have h := orderOf_injective (MulAut.conj t⁻¹).toMonoidHom (MulAut.conj t⁻¹).injective q
  rw [← D.hq3, ← h]
  simp

theorem L_le_centralizer_q2 (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat) :
    L ≤ Subgroup.centralizer ({t⁻¹ * q * t} : Set G) := by
  have hLL := commutator_conjugate_eq_bot h113 h37 D.hyp D.two D.block D.ht D.htn
  intro x hx
  have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hLL) hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp h1 _ (SecA.conj_mem_conjugate t D.hqL)).symm

theorem ne_conjugate (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat) :
    K ≠ CFSG.conjugate K t := by
  intro hKK
  have hq2K : t⁻¹ * q * t ∈ K := hKK ▸ SecA.conj_mem_conjugate t D.hqK
  have hc : ∀ x ∈ L, (t⁻¹ * q * t) * x = x * (t⁻¹ * q * t) := fun x hx =>
    (Subgroup.mem_centralizer_singleton_iff.mp (D.L_le_centralizer_q2 h113 h37 hx)).symm
  obtain ⟨α, hαs, hαk, -⟩ := D.hKa
  have h9 := nine_dvd_card_sup D.hq3 D.orderOf_q2 (hc q D.hqL).symm
    (not_mem_zpowers_of_forall_commute D.block.2 D.hqL D.orderOf_q2 hc)
  exact not_nine_dvd_card hαs hαk (h9.trans (Subgroup.card_dvd_of_le
    (sup_le (Subgroup.zpowers_le.mpr D.hqK) (Subgroup.zpowers_le.mpr hq2K))))

theorem commutator_conjugate_K (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat) :
    ⁅K, CFSG.conjugate K t⁆ = ⊥ := by
  have hK2c : CFSG.conjugate K t ∈ cComp H := by
    rw [SecA.conjugate_eq_map]
    exact LocDbl.map_conj_mem_cComp D.hK (Subgroup.le_normalizer (D.hTH (T.inv_mem D.ht)))
  have hK2s : IsShort2 (CFSG.conjugate K t) := by
    rw [SecA.conjugate_eq_map]
    exact Lin2.IsShort2.map_equiv D.hKs (MulAut.conj t⁻¹)
  exact commutator_eq_bot_of_mem_cComp D.hK hK2c D.hKs hK2s
    (isQuasisimple_of_isAltType D.hKs D.hKa) (D.ne_conjugate h113 h37)

theorem K_le_centralizer_q2 (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat) :
    K ≤ Subgroup.centralizer ({t⁻¹ * q * t} : Set G) := by
  intro x hx
  have h1 := (Subgroup.commutator_eq_bot_iff_le_centralizer.mp (D.commutator_conjugate_K h113
    h37)) hx
  exact Subgroup.mem_centralizer_singleton_iff.mpr
    (Subgroup.mem_centralizer_iff.mp h1 _ (SecA.conj_mem_conjugate t D.hqK)).symm

theorem K_le_centralizer_R (h113 : ASInputs.AS_C_1_13) (h37 : Vol2Native.A37ForSQTKCat) :
    K ≤ Subgroup.centralizer (CFSG.conjugate (fsuUL T L I ⊓ K) t : Set G) := by
  have hRK : CFSG.conjugate (fsuUL T L I ⊓ K) t ≤ CFSG.conjugate K t := fun x hx =>
    SecA.mem_conjugate_iff.mpr (SecA.mem_conjugate_iff.mp hx).2
  exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    (D.commutator_conjugate_K h113 h37)).trans (Subgroup.centralizer_le hRK)

end S5Data

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

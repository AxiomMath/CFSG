module

public import CFSG.RankThree.PartOne.Q1327T.Item7Basic
import CFSG.RankThree.PartOne.S9.OddCore.TorsionCommon

public section

namespace CFSG.RankThree.PartOne.Q1327F

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.Q1327T CFSG.RankThree.PartOne.Torsion37

theorem false_of_pGroup_plane {Q : Type} [Group Q] [Finite Q] {p : ℕ} [Fact p.Prime] (hp5 : 5 ≤ p)
    (hZ : Subgroup.center Q = ⊥) (hexp : ∀ y : Q, (∃ k : ℕ, y ^ (p ^ k) = 1) → y ^ p = 1)
    (hcard : p ^ 3 ∣ Nat.card Q) {Ē : Subgroup Q} (hE : IsElementaryAbelian p Ē)
    (hc : Nat.card Ē = p ^ 2)
    (hmax : ∀ F : Subgroup Q, IsElementaryAbelian p F → F ≤ Subgroup.centralizer (Ē : Set Q) →
      Ē ≤ F → F ≤ Ē ⊔ Subgroup.center Q)
    (hW : Nonempty (torusImage Ē ⊤ ≃* Equiv.Perm (Fin 3))) : False := by
  classical
  have hp := (Fact.out : p.Prime)
  obtain ⟨φ⟩ := hW
  obtain ⟨P, hEP⟩ := (IsElementaryAbelian.isPGroup p Ē).exists_le_sylow
  have hPcard : p ^ 3 ∣ Nat.card (P : Subgroup Q) := by
    rw [Sylow.card_eq_multiplicity P]
    exact pow_dvd_pow p ((hp.pow_dvd_iff_le_factorization Nat.card_pos.ne').1 hcard)
  have hPgt : p ^ 2 < Nat.card (P : Subgroup Q) := by
    have h1 : p ^ 3 ≤ Nat.card (P : Subgroup Q) := Nat.le_of_dvd Nat.card_pos hPcard
    have h2 : p ^ 2 < p ^ 3 := Nat.pow_lt_pow_right hp.one_lt (by norm_num)
    omega
  have hPnil : Group.IsNilpotent (P : Subgroup Q) := (P.isPGroup').isNilpotent
  set H : Subgroup (P : Subgroup Q) := Ē.subgroupOf P with hH
  have hHtop : H < ⊤ := by
    refine lt_top_iff_ne_top.2 fun htop => ?_
    have hle : (P : Subgroup Q) ≤ Ē := fun x hx => by
      have : (⟨x, hx⟩ : (P : Subgroup Q)) ∈ H := by rw [htop]; exact Subgroup.mem_top _
      exact this
    have := Subgroup.card_le_of_le hle
    rw [hc] at this
    omega
  obtain ⟨x, hxN, hxH⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent H hHtop)
  set y : Q := (x : Q) with hy
  have hyP : y ∈ (P : Subgroup Q) := x.2
  have hyE : y ∉ Ē := fun h => hxH h
  have hyN : y ∈ Subgroup.normalizer (Ē : Set Q) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      have hhP : h ∈ (P : Subgroup Q) := hEP hh
      exact (Subgroup.mem_normalizer_iff.1 hxN ⟨h, hhP⟩).1 hh
    · intro hh
      have hhP : h ∈ (P : Subgroup Q) := by
        have h1 : y * h * y⁻¹ ∈ (P : Subgroup Q) := hEP hh
        have h2 := (P : Subgroup Q).mul_mem ((P : Subgroup Q).mul_mem ((P : Subgroup Q).inv_mem hyP)
          h1) hyP
        simpa [mul_assoc] using h2
      exact (Subgroup.mem_normalizer_iff.1 hxN ⟨h, hhP⟩).2 hh
  set w : MulAut Ē := Ē.normalizerMonoidHom ⟨y, hyN⟩ with hw
  have hwmem : w ∈ torusImage Ē ⊤ := by
    rw [torusImage_top_eq_range]
    exact ⟨⟨y, hyN⟩, rfl⟩
  obtain ⟨k, hk⟩ := (P.isPGroup') ⟨y, hyP⟩
  have hyk : y ^ p ^ k = 1 := congrArg Subtype.val hk
  have hord_w : orderOf w ∣ p ^ k := by
    have h1 : orderOf w ∣ orderOf (⟨y, hyN⟩ : Subgroup.normalizer (Ē : Set Q)) :=
      orderOf_map_dvd Ē.normalizerMonoidHom _
    have h2 : orderOf (⟨y, hyN⟩ : Subgroup.normalizer (Ē : Set Q)) = orderOf y :=
      Subgroup.orderOf_mk _ _
    rw [h2] at h1
    exact h1.trans (orderOf_dvd_of_pow_eq_one hyk)
  have hord6 : orderOf w ∣ 6 := by
    have h1 : orderOf (φ ⟨w, hwmem⟩) ∣ Fintype.card (Equiv.Perm (Fin 3)) := orderOf_dvd_card
    rw [MulEquiv.orderOf_eq, Subgroup.orderOf_mk] at h1
    simpa [Fintype.card_perm, Nat.factorial] using h1
  have hcop : Nat.Coprime (p ^ k) 6 := by
    refine Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd hp).2 fun hd => ?_)
    have h23 : p ∣ 2 * 3 := by simpa using hd
    rcases hp.dvd_mul.1 h23 with h2 | h3
    · have := Nat.le_of_dvd (by norm_num) h2
      omega
    · have := Nat.le_of_dvd (by norm_num) h3
      omega
  have hw1 : w = 1 := by
    have := Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left hord_w hcop) hord6
    exact orderOf_eq_one_iff.1 this
  have hyC : ∀ e ∈ Ē, y * e * y⁻¹ = e := by
    intro e he
    have h1 := coe_normalizerMonoidHom_apply hyN ⟨e, he⟩
    rw [← hw, hw1] at h1
    simpa using h1.symm
  have hyp : y ^ p = 1 := hexp y ⟨k, hyk⟩
  have hcomm : ∀ e ∈ Ē, ∀ z ∈ Subgroup.zpowers y, e * z = z * e := by
    intro e he z hz
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    refine (Commute.zpow_right (show Commute e y from ?_) i).eq
    have := hyC e he
    exact (mul_inv_eq_iff_eq_mul.1 this).symm
  have hFel : IsElementaryAbelian p ↥(Ē ⊔ Subgroup.zpowers y) :=
    isElementaryAbelian_sup_of_commute hE (IsElementaryAbelian.zpowers_of_pow_eq_one hyp) hcomm
  have hFle : Ē ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer (Ē : Set Q) := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr ?_)
    · intro e he
      rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact congrArg Subtype.val (hE.is_comm.comm (⟨a, ha⟩ : ↥Ē) ⟨e, he⟩)
    · rw [Subgroup.mem_centralizer_iff]
      intro a ha
      exact (mul_inv_eq_iff_eq_mul.1 (hyC a ha)).symm
  have hFE := hmax _ hFel hFle le_sup_left
  rw [hZ, sup_bot_eq] at hFE
  exact hyE (hFE (Subgroup.mem_sup_right (Subgroup.mem_zpowers y)))

end CFSG.RankThree.PartOne.Q1327F

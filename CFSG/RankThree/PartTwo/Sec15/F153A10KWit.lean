module

public import CFSG.RankThree.PartTwo.Sec15.F153A10KDefs
public import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153A10K

open Equiv

theorem card_sup_zpowers_eq_25 {G : Type*} [Group G] {x y : G} (hxy : x * y = y * x)
    (hx : x ^ 5 = 1) (hx1 : x ≠ 1) (hy : y ^ 5 = 1) (hyx : ∀ k : ℕ, k < 5 → y ≠ x ^ k) :
    Nat.card ↥(Subgroup.zpowers x ⊔ Subgroup.zpowers y) = 25 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hx5 : orderOf x = 5 := orderOf_eq_prime hx hx1
  have hy1 : y ≠ 1 := by
    have := hyx 0 (by norm_num)
    rwa [pow_zero] at this
  have hy5 : orderOf y = 5 := orderOf_eq_prime hy hy1
  have hyfin : IsOfFinOrder y := isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, hy⟩
  haveI : Finite (Subgroup.zpowers y) := hyfin.finite_zpowers
  have hC : Subgroup.zpowers y ≤ Subgroup.centralizer (Subgroup.zpowers x : Set G) := by
    rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (Commute.zpow_left (show Commute x y from hxy) k).eq
  have hprod := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (hC.trans (Subgroup.centralizer_le_normalizer _))
  have hx5' : Nat.card (Subgroup.zpowers x) = 5 := by rw [Nat.card_zpowers, hx5]
  have hy5' : Nat.card (Subgroup.zpowers y) = 5 := by rw [Nat.card_zpowers, hy5]
  have hinf : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers y : Subgroup G) = 1 := by
    have hdvd : Nat.card (Subgroup.zpowers x ⊓ Subgroup.zpowers y : Subgroup G) ∣ 5 :=
      hy5' ▸ Subgroup.card_dvd_of_le inf_le_right
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1 | h5
    · exact h1
    · exfalso
      have hle : Subgroup.zpowers y ≤ Subgroup.zpowers x := by
        have heq : Subgroup.zpowers x ⊓ Subgroup.zpowers y = Subgroup.zpowers y :=
          Subgroup.eq_of_le_of_card_ge inf_le_right (by rw [h5, hy5'])
        rw [← heq]
        exact inf_le_left
      have hmem : y ∈ Subgroup.zpowers x := hle (Subgroup.mem_zpowers y)
      have hfin : IsOfFinOrder x := isOfFinOrder_iff_pow_eq_one.mpr ⟨5, by norm_num, hx⟩
      obtain ⟨m, hm, hxm⟩ := Finset.mem_image.mp (hfin.mem_zpowers_iff_mem_range_orderOf.mp hmem)
      rw [Finset.mem_range, hx5] at hm
      exact hyx m hm hxm.symm
  rw [hinf, hx5', hy5', mul_one] at hprod
  exact hprod

private theorem a10k_five_dvd_of_pow_five {G : Type*} [Group G] {K : Subgroup G} {c : G}
    (h : c ∈ K) (hc : c ^ 5 = 1) (hc1 : c ≠ 1) : 5 ∣ Nat.card K := by
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have h' := Subgroup.card_dvd_of_le (Subgroup.zpowers_le.mpr h)
  rwa [Nat.card_zpowers, orderOf_eq_prime hc hc1] at h'

private theorem a10k_twentyfive_dvd_of_pair {G : Type*} [Group G] {K : Subgroup G} {c₁ c₂ : G}
    (h₁ : c₁ ∈ K) (h₂ : c₂ ∈ K) (hcomm : c₁ * c₂ = c₂ * c₁) (hc₁ : c₁ ^ 5 = 1)
    (hc₁1 : c₁ ≠ 1) (hc₂ : c₂ ^ 5 = 1) (hyx : ∀ k : ℕ, k < 5 → c₂ ≠ c₁ ^ k) :
    25 ∣ Nat.card K := by
  have hsup : Subgroup.zpowers c₁ ⊔ Subgroup.zpowers c₂ ≤ K :=
    sup_le (Subgroup.zpowers_le.mpr h₁) (Subgroup.zpowers_le.mpr h₂)
  have h := Subgroup.card_dvd_of_le hsup
  rwa [card_sup_zpowers_eq_25 hcomm hc₁ hc₁1 hc₂ hyx] at h

private theorem a10k_conj_mem_map {G : Type*} [Group G] {E : Subgroup G} {g x : G}
    (hx : x ∈ E) : g * x * g⁻¹ ∈ E.map (MulAut.conj g).toMonoidHom :=
  Subgroup.mem_map_of_mem _ hx

theorem gZero_mem : gZero ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]; decide +kernel

theorem gOne_mem : gOne ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]; decide +kernel

theorem hOne_mem : hOne ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]; decide +kernel

theorem gA_mem : gA ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]; decide +kernel

theorem hA_mem : hA ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]; decide +kernel

theorem gB_mem : gB ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]; decide +kernel

theorem hB_mem : hB ∈ alternatingGroup (Fin 10) := by
  rw [Perm.mem_alternatingGroup]; decide +kernel

theorem five_dvd_of_tZero_mem {E : Subgroup (Perm (Fin 10))} (h : tZero ∈ E) :
    5 ∣ Nat.card ↥(E ⊔ E.map (MulAut.conj gZero).toMonoidHom) := by
  refine a10k_five_dvd_of_pow_five (c := tZero * (gZero * tZero * gZero⁻¹))
    (mul_mem (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right (a10k_conj_mem_map h))) ?_ ?_
  · decide +kernel
  · decide +kernel

theorem five_dvd_of_tOne_mem {E : Subgroup (Perm (Fin 10))} (h : tOne ∈ E) :
    5 ∣ Nat.card ↥(E ⊔ E.map (MulAut.conj gOne).toMonoidHom) := by
  refine a10k_five_dvd_of_pow_five (c := tOne * (gOne * tOne * gOne⁻¹))
    (mul_mem (Subgroup.mem_sup_left h) (Subgroup.mem_sup_right (a10k_conj_mem_map h))) ?_ ?_
  · decide +kernel
  · decide +kernel

theorem twentyfive_dvd_of_tOne_mem {E : Subgroup (Perm (Fin 10))} (h : tOne ∈ E) :
    25 ∣ Nat.card ↥(E ⊔ E.map (MulAut.conj gOne).toMonoidHom ⊔
      E.map (MulAut.conj hOne).toMonoidHom) := by
  have hu : tOne ∈ E ⊔ E.map (MulAut.conj gOne).toMonoidHom ⊔
      E.map (MulAut.conj hOne).toMonoidHom :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left h)
  have hu2 : gOne * tOne * gOne⁻¹ ∈ E ⊔ E.map (MulAut.conj gOne).toMonoidHom ⊔
      E.map (MulAut.conj hOne).toMonoidHom :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (a10k_conj_mem_map h))
  have hu3 : hOne * tOne * hOne⁻¹ ∈ E ⊔ E.map (MulAut.conj gOne).toMonoidHom ⊔
      E.map (MulAut.conj hOne).toMonoidHom :=
    Subgroup.mem_sup_right (a10k_conj_mem_map h)
  refine a10k_twentyfive_dvd_of_pair
    (c₁ := tOne * (gOne * tOne * gOne⁻¹) * (tOne * (hOne * tOne * hOne⁻¹))⁻¹)
    (c₂ := tOne * (hOne * tOne * hOne⁻¹))
    (mul_mem (mul_mem hu hu2) (inv_mem (mul_mem hu hu3))) (mul_mem hu hu3) ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem twentyfive_dvd_of_A_mem {E : Subgroup (Perm (Fin 10))} (h₁ : tZero ∈ E) (h₂ : taA ∈ E) :
    25 ∣ Nat.card ↥(E ⊔ E.map (MulAut.conj gA).toMonoidHom ⊔
      E.map (MulAut.conj hA).toMonoidHom) := by
  have ha : tZero ∈ E ⊔ E.map (MulAut.conj gA).toMonoidHom ⊔
      E.map (MulAut.conj hA).toMonoidHom :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left h₁)
  have hb : taA ∈ E ⊔ E.map (MulAut.conj gA).toMonoidHom ⊔
      E.map (MulAut.conj hA).toMonoidHom :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left h₂)
  have hd : gA * taA * gA⁻¹ ∈ E ⊔ E.map (MulAut.conj gA).toMonoidHom ⊔
      E.map (MulAut.conj hA).toMonoidHom :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (a10k_conj_mem_map h₂))
  have he : hA * tZero * hA⁻¹ ∈ E ⊔ E.map (MulAut.conj gA).toMonoidHom ⊔
      E.map (MulAut.conj hA).toMonoidHom :=
    Subgroup.mem_sup_right (a10k_conj_mem_map h₁)
  have hf : hA * taA * hA⁻¹ ∈ E ⊔ E.map (MulAut.conj gA).toMonoidHom ⊔
      E.map (MulAut.conj hA).toMonoidHom :=
    Subgroup.mem_sup_right (a10k_conj_mem_map h₂)
  refine a10k_twentyfive_dvd_of_pair
    (c₁ := gA * taA * gA⁻¹ * (hA * tZero * hA⁻¹) * (gA * taA * gA⁻¹) * (hA * taA * hA⁻¹))
    (c₂ := tZero * (gA * taA * gA⁻¹) * taA * (gA * taA * gA⁻¹))
    (mul_mem (mul_mem (mul_mem hd he) hd) hf) (mul_mem (mul_mem (mul_mem ha hd) hb) hd)
    ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

theorem twentyfive_dvd_of_B_mem {E : Subgroup (Perm (Fin 10))} (h₁ : tZero ∈ E) (h₂ : tbB ∈ E) :
    25 ∣ Nat.card ↥(E ⊔ E.map (MulAut.conj gB).toMonoidHom ⊔
      E.map (MulAut.conj hB).toMonoidHom) := by
  have ha : tZero ∈ E ⊔ E.map (MulAut.conj gB).toMonoidHom ⊔
      E.map (MulAut.conj hB).toMonoidHom :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left h₁)
  have hb : tbB ∈ E ⊔ E.map (MulAut.conj gB).toMonoidHom ⊔
      E.map (MulAut.conj hB).toMonoidHom :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_left h₂)
  have hc : gB * tZero * gB⁻¹ ∈ E ⊔ E.map (MulAut.conj gB).toMonoidHom ⊔
      E.map (MulAut.conj hB).toMonoidHom :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (a10k_conj_mem_map h₁))
  have hd : gB * tbB * gB⁻¹ ∈ E ⊔ E.map (MulAut.conj gB).toMonoidHom ⊔
      E.map (MulAut.conj hB).toMonoidHom :=
    Subgroup.mem_sup_left (Subgroup.mem_sup_right (a10k_conj_mem_map h₂))
  have he : hB * tZero * hB⁻¹ ∈ E ⊔ E.map (MulAut.conj gB).toMonoidHom ⊔
      E.map (MulAut.conj hB).toMonoidHom :=
    Subgroup.mem_sup_right (a10k_conj_mem_map h₁)
  have hf : hB * tbB * hB⁻¹ ∈ E ⊔ E.map (MulAut.conj gB).toMonoidHom ⊔
      E.map (MulAut.conj hB).toMonoidHom :=
    Subgroup.mem_sup_right (a10k_conj_mem_map h₂)
  refine a10k_twentyfive_dvd_of_pair
    (c₁ := tbB * (gB * tZero * gB⁻¹) * (hB * tbB * hB⁻¹) * (gB * tZero * gB⁻¹))
    (c₂ := tZero * (gB * tZero * gB⁻¹) * (gB * tbB * gB⁻¹) * (hB * tZero * hB⁻¹))
    (mul_mem (mul_mem (mul_mem hb hc) hf) hc) (mul_mem (mul_mem (mul_mem ha hc) hd) he)
    ?_ ?_ ?_ ?_ ?_
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel
  · decide +kernel

end CFSG.RankThree.PartTwo.Sec15.F153A10K


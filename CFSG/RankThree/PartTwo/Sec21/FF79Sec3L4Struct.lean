module

public import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4Esimple6
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4StructBase
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4StructElem
import CFSG.RankThree.PartTwo.Sec21.FF79Sec3L4StructA5

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21 Subgroup

theorem alt5_nonab : ∃ x y : alternatingGroup (Fin 5), x * y ≠ y * x := by decide +kernel

section Setting

variable {H : Type} [Group H] [Finite H] {β : MulAut H} {Z K : Subgroup H} {z₀ : H}

theorem layer_normal_of_ap : (layer H).Normal := by
  have := CFSG.LocalCores.layer_characteristic (G := H)
  infer_instance

theorem K_simple (hd : FF79APData β Z K z₀) :
    IsSimpleGroup ↥K ∧ ∃ x y : ↥K, x * y ≠ y * x := by
  obtain ⟨e⟩ := hd.K_a5
  obtain ⟨x, y, hxy⟩ := alt5_nonab
  exact ⟨e.isSimpleGroup, e.symm x, e.symm y, fun h => hxy (e.symm.injective (by simpa using h))⟩

theorem K_central (hd : FF79APData β Z K z₀) {k : H} (hk : k ∈ K)
    (h : ∀ w ∈ K, w * k = k * w) : k = 1 := by
  obtain ⟨hs, hn⟩ := K_simple hd
  haveI := hs
  have := eq_one_of_central_of_simple (X := ↥K) hn (x := ⟨k, hk⟩) fun w =>
    Subtype.ext (h w w.2)
  exact congrArg Subtype.val this

theorem K_order3 (hd : FF79APData β Z K z₀) : ∃ a ∈ K, orderOf a = 3 := by
  obtain ⟨e⟩ := hd.K_a5
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Nat.card K = 60 := by rw [Nat.card_congr e.toEquiv]; exact A5Klein.card_A5
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := ↥K) 3 (by rw [hc]; norm_num)
  exact ⟨x, x.2, by rw [Subgroup.orderOf_coe]; exact hx⟩

variable (hd : FF79APData β Z K z₀)
include hd

theorem L_facts_simple : IsSimpleGroup ↥(layer H) := (ap_E_simple hd).2.1
theorem K_le_L : K ≤ layer H := (ap_E_simple hd).2.2.1
theorem L_stable : ∀ x : H, x ∈ layer H → β x ∈ layer H := (ap_E_simple hd).2.2.2

theorem L_nonab : ∃ x y : ↥(layer H), x * y ≠ y * x := by
  obtain ⟨-, x, y, hxy⟩ := K_simple hd
  refine ⟨⟨x, K_le_L hd x.2⟩, ⟨y, K_le_L hd y.2⟩, fun h => hxy ?_⟩
  exact Subtype.ext (congrArg (fun x : ↥(layer H) => (x : H)) h)

theorem L_central {x : H} (hx : x ∈ layer H) (h : ∀ w ∈ layer H, w * x = x * w) : x = 1 := by
  haveI := L_facts_simple hd
  have := eq_one_of_central_of_simple (X := ↥(layer H)) (L_nonab hd) (x := ⟨x, hx⟩) fun w =>
    Subtype.ext (h w w.2)
  exact congrArg Subtype.val this

theorem Z_inf_L {x : H} (hxZ : x ∈ Z) (hxL : x ∈ layer H) : x = 1 := by
  refine L_central hd hxL fun w _ => ?_
  exact Subgroup.mem_center_iff.1 (hd.Z_central hxZ) w

theorem z₀_not_mem_L : z₀ ∉ layer H := fun h => by
  have := Z_inf_L hd hd.z₀_mem h
  have h3 := hd.z₀_ord
  rw [this, orderOf_one] at h3
  omega

theorem z₀_comm (g : H) : g * z₀ = z₀ * g :=
  Subgroup.mem_center_iff.1 (hd.Z_central hd.z₀_mem) g

theorem no_fixed_pair {x y : H} (hxL : x ∈ layer H) (hyL : y ∈ layer H) (hx : orderOf x = 3)
    (hy : orderOf y = 3) (hxy : x * y = y * x) (fx : β x = x) (fy : β y = y)
    (hny : y ∉ zpowers x) : False := by
  have hcl : closure ({x, y} : Set H) ≤ layer H := by
    rw [closure_le]
    rintro a (rfl | rfl)
    · exact hxL
    · exact hyL
  refine false_of_fixed_triple (β := β) hd.no27 (x := x) (y := y) (z := z₀) hxy
    (z₀_comm hd x) (z₀_comm hd y) hx (by rw [← hy]; exact pow_orderOf_eq_one y)
    (by rw [← hd.z₀_ord]; exact pow_orderOf_eq_one z₀) hny
    (fun h => z₀_not_mem_L hd (hcl h)) fx fy hd.z₀_fix

end Setting

end CFSG.RankThree.PartTwo.Sec21.FF79

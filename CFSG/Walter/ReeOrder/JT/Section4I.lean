module

public import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.DicksonClassification
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Walter.ReeOrder.JT.PSL2Unipotent
public import CFSG.Walter.ReeOrder.JT.Section2

public section

namespace CFSG.Walter.JT

open scoped IsMulCommutative Pointwise MatrixGroups
open CFSG

variable {G : Type} [Group G] [Finite G]

section General

variable {X : Type*} [Group X] [Finite X]

noncomputable def conjEndo (K : Subgroup X) {u : X} (huK : u ∈ Subgroup.normalizer (K : Set X)) :
    K →* K where
  toFun x := ⟨u * x * u⁻¹, (Subgroup.mem_normalizer_iff.mp huK x).mp x.2⟩
  map_one' := Subtype.ext (by simp)
  map_mul' x y := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem inv_of_fpf_involution {K : Subgroup X} {u : X} (hu : u * u = 1)
    (huK : u ∈ Subgroup.normalizer (K : Set X))
    (hfix : ∀ x ∈ K, u * x * u⁻¹ = x → x = 1) : ∀ x ∈ K, u * x * u⁻¹ = x⁻¹ := by
  have hφ : MonoidHom.FixedPointFree (conjEndo K huK) := fun x hx =>
    Subtype.ext (hfix x x.2 (congrArg Subtype.val hx))
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have h2 : Function.Involutive (conjEndo K huK) := fun x => Subtype.ext (by
    change u * (u * (x : X) * u⁻¹) * u⁻¹ = x
    rw [hinv]
    calc u * (u * (x : X) * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by rw [hu]; group)
  have := MonoidHom.FixedPointFree.coe_eq_inv_of_involutive hφ h2
  intro x hx
  have h := congrFun this ⟨x, hx⟩
  exact congrArg Subtype.val h

theorem commute_of_fpf_involution {K : Subgroup X} {u : X} (hu : u * u = 1)
    (huK : u ∈ Subgroup.normalizer (K : Set X))
    (hfix : ∀ x ∈ K, u * x * u⁻¹ = x → x = 1) : ∀ x ∈ K, ∀ y ∈ K, x * y = y * x := by
  have hφ : MonoidHom.FixedPointFree (conjEndo K huK) := fun x hx =>
    Subtype.ext (hfix x x.2 (congrArg Subtype.val hx))
  have hinv : u⁻¹ = u := inv_eq_of_mul_eq_one_right hu
  have h2 : Function.Involutive (conjEndo K huK) := fun x => Subtype.ext (by
    change u * (u * (x : X) * u⁻¹) * u⁻¹ = x
    rw [hinv]
    calc u * (u * (x : X) * u) * u = (u * u) * x * (u * u) := by group
      _ = x := by rw [hu]; group)
  intro x hx y hy
  exact congrArg Subtype.val
    ((MonoidHom.FixedPointFree.commute_all_of_involutive hφ h2 ⟨x, hx⟩ ⟨y, hy⟩).eq)

end General

theorem card_alternatingGroup_four : Nat.card (alternatingGroup (Fin 4)) = 12 := by
  rw [Nat.card_eq_fintype_card]
  have := two_mul_card_alternatingGroup (α := Fin 4)
  rw [Fintype.card_perm, Fintype.card_fin] at this
  have h24 : (4 : ℕ).factorial = 24 := by decide
  rw [h24] at this
  convert (by omega : Fintype.card ↥(alternatingGroup (Fin 4)) = 12)

theorem card_alternatingGroup_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card]
  have := two_mul_card_alternatingGroup (α := Fin 5)
  rw [Fintype.card_perm, Fintype.card_fin] at this
  have h120 : (5 : ℕ).factorial = 120 := by decide
  rw [h120] at this
  convert (by omega : Fintype.card ↥(alternatingGroup (Fin 5)) = 60)

theorem card_perm_four : Nat.card (Equiv.Perm (Fin 4)) = 24 := by
  rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
  decide

namespace JTHyp

variable (h : JTHyp G)

theorem f_pos : h.f ≠ 0 := by
  intro hf0
  have := h.five_lt
  rw [hf0, pow_zero] at this
  omega

theorem abelian_odd_cases_F
    (hp : h.p ≠ 2) {H : Subgroup G} (hHF : H ≤ h.F)
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hodd : Odd (Nat.card H)) :
    IsPGroup h.p H ∨
      (IsCyclic H ∧ (Nat.card H ∣ (h.q - 1) / 2 ∨ Nat.card H ∣ (h.q + 1) / 2)) := by
  classical
  have hq := h.five_lt
  have hqodd : Odd h.q := by
    rw [JTHyp.q_eq]
    exact ((Fact.out : h.p.Prime).odd_of_ne_two hp).pow
  by_cases hpH : h.p ∣ Nat.card H
  · left
    obtain ⟨⟨x, hxH⟩, hx⟩ := exists_prime_orderOf_dvd_card' (G := H) h.p hpH
    have hxo : orderOf x = h.p := by rw [← hx, Subgroup.orderOf_mk]
    have hx1 : x ≠ 1 := by
      intro h0
      rw [h0, orderOf_one] at hxo
      exact (Fact.out : h.p.Prime).one_lt.ne hxo
    have hu := psl2UnipotentFacts h.F h.iso hp h.f_pos
    obtain ⟨R, hxR, hRF, hRcard⟩ := hu.exists_le (Subgroup.zpowers x)
      ((Subgroup.zpowers_le).mpr (hHF hxH))
      (IsPGroup.of_card (by rw [Nat.card_zpowers, hxo, pow_one] :
        Nat.card (Subgroup.zpowers x) = h.p ^ 1))
    have hC := hu.centralizer R hRF hRcard x (hxR (Subgroup.mem_zpowers x)) hx1
    have hHR : H ≤ R := by
      rw [← hC]
      intro y hy
      exact ⟨hHF hy, Subgroup.mem_centralizer_singleton_iff.mpr (hHc y hy x hxH)⟩
    exact (IsPGroup.of_card hRcard).to_le hHR
  · right
    set K := GaloisField h.p h.f
    have hKcard : Nat.card K = h.p ^ h.f := GaloisField.card h.p h.f h.f_pos
    set H' := (H.subgroupOf h.F).map h.iso.toMonoidHom with hH'def
    have eH : H ≃* H' :=
      (Subgroup.subgroupOfEquivOfLe hHF).symm.trans
        ((H.subgroupOf h.F).equivMapOfInjective _ h.iso.injective)
    have hH'card : Nat.card H' = Nat.card H := (Nat.card_congr eH.toEquiv).symm
    have hgcd : Nat.gcd (Nat.card K - 1) 2 = 2 := by
      rw [hKcard, ← JTHyp.q_eq]
      have : 2 ∣ h.q - 1 := by
        obtain ⟨k, hk⟩ := hqodd
        omega
      exact Nat.gcd_eq_right this
    rcases Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part hKcard H'
        (by rw [hH'card]; exact hpH) with
      ⟨z, hz, hcard, hcyc⟩ | ⟨z, -, hcard, -⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
    · refine ⟨isCyclic_of_surjective eH.symm.toMonoidHom eH.symm.surjective, ?_⟩
      rw [← hH'card, hcard]
      rw [hgcd, hKcard, ← JTHyp.q_eq] at hz
      exact hz
    · exfalso
      rw [← hH'card, hcard] at hodd
      exact (Nat.not_even_iff_odd.mpr hodd) (even_two_mul z)
    · exfalso
      rw [← hH'card, Nat.card_congr e.toEquiv, card_alternatingGroup_four] at hodd
      exact absurd hodd (by decide)
    · exfalso
      rw [← hH'card, Nat.card_congr e.toEquiv, card_perm_four] at hodd
      exact absurd hodd (by decide)
    · exfalso
      rw [← hH'card, Nat.card_congr e.toEquiv, card_alternatingGroup_five] at hodd
      exact absurd hodd (by decide)

theorem abelian_odd_cases
    (hp : h.p ≠ 2) {u : G} (hu : orderOf u = 2) {H : Subgroup G}
    (hHu : H ≤ Subgroup.centralizer ({u} : Set G))
    (hHc : ∀ x ∈ H, ∀ y ∈ H, x * y = y * x) (hodd : Odd (Nat.card H)) :
    IsPGroup h.p H ∨
      (IsCyclic H ∧ (Nat.card H ∣ (h.q - 1) / 2 ∨ Nat.card H ∣ (h.q + 1) / 2)) := by
  obtain ⟨g, hg⟩ := h.exists_conj_eq_t hp hu
  set H' := H.map (MulAut.conj g).toMonoidHom with hH'def
  have eH : H ≃* H' := H.equivMapOfInjective _ (MulAut.conj g).injective
  have hH'card : Nat.card H' = Nat.card H := (Nat.card_congr eH.toEquiv).symm
  have hH't : H' ≤ Subgroup.centralizer ({h.t} : Set G) := by
    rintro _ ⟨x, hx, rfl⟩
    rw [Subgroup.mem_centralizer_singleton_iff, ← hg]
    have hxu := Subgroup.mem_centralizer_singleton_iff.mp (hHu hx)
    change g * x * g⁻¹ * (g * u * g⁻¹) = g * u * g⁻¹ * (g * x * g⁻¹)
    calc g * x * g⁻¹ * (g * u * g⁻¹) = g * (x * u) * g⁻¹ := by group
      _ = g * (u * x) * g⁻¹ := by rw [hxu]
      _ = g * u * g⁻¹ * (g * x * g⁻¹) := by group
  have hH'F : H' ≤ h.F := h.le_F_of_odd hH't (hH'card ▸ hodd)
  have hH'c : ∀ x ∈ H', ∀ y ∈ H', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simp only [MulEquiv.coe_toMonoidHom]
    rw [← map_mul, ← map_mul, hHc x hx y hy]
  rcases h.abelian_odd_cases_F hp hH'F hH'c (hH'card ▸ hodd) with hpg | ⟨hcyc, hdvd⟩
  · left
    exact hpg.of_injective eH.toMonoidHom eH.injective
  · right
    refine ⟨isCyclic_of_surjective eH.symm.toMonoidHom eH.symm.surjective, ?_⟩
    rw [← hH'card]
    exact hdvd

end JTHyp

end CFSG.Walter.JT

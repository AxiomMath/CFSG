module

import all CFSG.Quasithin.Background.G6Transvection
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem19M
public import CFSG.Quasithin.Vol2.Ch6Sec1Lem24

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique CFSG.Quasithin.E3
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L V : Subgroup G} {n : ℕ}

namespace Hyp611Nat

theorem eq_one_of_odd_of_commute (h : Hyp611Nat G T M L V n) {ℓ : G} (hℓ : ℓ ∈ L)
    (hodd : Odd (orderOf ℓ)) {v : G} (hv : v ∈ V) (hv1 : v ≠ 1) (hc : ℓ * v = v * ℓ) :
    ℓ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := h.data with hD
  set ℓ' : ↥L := ⟨ℓ, hℓ⟩ with hℓ'
  set vV : ↥V := ⟨v, hv⟩ with hvV
  have hvC : (vV : G) ∈
      Subgroup.centralizer ((Subgroup.zpowers (ℓ' : G) : Subgroup G) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    obtain ⟨j, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact ((show Commute ℓ v from hc).zpow_left j).eq
  have hρfix := (D.fixed_iff (Subgroup.zpowers_le.mpr ℓ'.2) vV).mp hvC ℓ'
    (Subgroup.mem_zpowers _)
  have : CharP D.K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (le_trans (by norm_num) h.toHyp5_0_1.two_le) D.card
  by_contra hℓ1
  have hρ1 : D.rho ℓ' ≠ 1 := by
    intro hρ
    have hℓC : (ℓ' : G) ∈ Subgroup.centralizer (V : Set G) :=
      (D.mem_ker_rho_iff ℓ').mp (MonoidHom.mem_ker.mpr hρ)
    have hℓO : ℓ ∈ pCoreOf 2 (L ⊔ T) := by
      rw [← h.toHyp5_0_1.sup_inf_centralizer_eq h.module]
      exact ⟨Subgroup.mem_sup_left hℓ, hℓC⟩
    obtain ⟨j, hj⟩ := (IsPGroup.iff_orderOf.mp
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (L ⊔ T))) ⟨ℓ, hℓO⟩
    have hj' : orderOf ℓ = 2 ^ j := by rw [← hj, Subgroup.orderOf_mk]
    rw [hj'] at hodd
    have hj0 : j = 0 := by
      by_contra hj0
      exact (Nat.not_even_iff_odd.mpr hodd) ((Nat.even_pow' hj0).mpr even_two)
    rw [hj0, pow_zero, orderOf_eq_one_iff] at hj'
    exact hℓ1 hj'
  have hℓodd : Odd (orderOf ℓ') := by rwa [hℓ', Subgroup.orderOf_mk]
  have hρodd : Odd (orderOf (D.rho ℓ')) := Odd.of_dvd_nat hℓodd (orderOf_map_dvd _ _)
  have hdet := det_sub_one_ne_zero_of_odd (D.rho ℓ') hρ1 hρodd
  apply hdet
  rw [← Matrix.exists_mulVec_eq_zero_iff]
  refine ⟨Multiplicative.toAdd (D.E vV), ?_, ?_⟩
  · intro h0
    apply hv1
    have : D.E vV = 1 := by
      apply Multiplicative.toAdd.injective
      rw [h0]
      rfl
    rw [← map_one D.E] at this
    exact congrArg Subtype.val (D.E.injective this)
  · rw [Matrix.sub_mulVec, Matrix.one_mulVec, hρfix, sub_self]

theorem inf_centralizer_ZS_eq_bot (h : Hyp611Nat G T M L V n) {D : Subgroup G} (hDL : D ≤ L)
    (hD : Odd (Nat.card D)) : D ⊓ Subgroup.centralizer (ch6ZS T L V : Set G) = ⊥ := by
  obtain ⟨⟨v, hvZ⟩, hv1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp h.ZS_ne_bot
  have hv1' : v ≠ 1 := fun h0 => hv1 (Subtype.ext h0)
  rw [eq_bot_iff]
  intro d hd
  rw [Subgroup.mem_bot]
  have hodd : Odd (orderOf d) := by
    have h1 : orderOf d ∣ Nat.card D := by
      rw [← Subgroup.orderOf_mk d hd.1]
      exact orderOf_dvd_natCard _
    exact Odd.of_dvd_nat hD h1
  exact h.eq_one_of_odd_of_commute (hDL hd.1) hodd hvZ.1 hv1'
    (Subgroup.mem_centralizer_iff.mp hd.2 v hvZ).symm

end Hyp611Nat

namespace L619

@[expose] def threePart (X : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ 3 ^ k = 1}

omit [Finite G] in
theorem threePart_le (X : Subgroup G) : threePart X ≤ X :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

omit [Finite G] in
theorem mem_threePart {X : Subgroup G} {x : G} (hx : x ∈ X) {k : ℕ} (hk : x ^ 3 ^ k = 1) :
    x ∈ threePart X :=
  Subgroup.subset_closure ⟨hx, k, hk⟩

theorem normalizer_le_normalizer_threePart (X : Subgroup G) :
    Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (threePart X : Set G) := by
  intro g hg
  refine mem_normalizer_of_forall_conj_mem_of_le fun x hx => ?_
  have key : threePart X ≤ (threePart X).comap (MulAut.conj g).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨hy, k, hk⟩
    show g * y * g⁻¹ ∈ threePart X
    refine mem_threePart ((Subgroup.mem_normalizer_iff.mp hg y).mp hy) (k := k) ?_
    rw [conj_pow, hk, mul_one, mul_inv_cancel]
  exact key hx

variable {W : Subgroup G} (hW : IsElemAbelian 2 W) (Z X : Subgroup G)

omit [Finite G] in
theorem act0_conj_mem_img0 (g : ↥(normWZX W Z X)) {k : MulAut ↥(V0 hW Z X)}
    (hk : k ∈ img0 hW Z X) : act0 hW Z X g * k * (act0 hW Z X g)⁻¹ ∈ img0 hW Z X := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hk
  refine Subgroup.mem_map.mpr ⟨g * x * g⁻¹, ?_, by rw [map_mul, map_mul, map_inv]⟩
  rw [Subgroup.mem_subgroupOf] at hx ⊢
  exact (Subgroup.mem_normalizer_iff.mp g.2.2 _).mp hx

end L619

end CFSG.Quasithin.H13

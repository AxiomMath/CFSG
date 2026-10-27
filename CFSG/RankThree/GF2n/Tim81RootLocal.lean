module

public import CFSG.RankThree.GF2n.Tim81RootCore
public import CFSG.RankThree.GF2n.Tim78S45Aux

public section

namespace CFSG.RankThree.GF2n.Tim78

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.RankThree.GF2n
open scoped commutatorElement

variable {G : Type} [Group G]

private theorem comm_mul_of_conj {z u : G} (hz : z * z = 1)
    (hpu : z * u * z * u = u * (z * u * z)) :
    z * (z * u * z * u) = z * u * z * u * z :=
  calc z * (z * u * z * u) = z * z * u * z * u := by group
    _ = u * z * u := by rw [hz]; group
    _ = u * z * u * (z * z) := by rw [hz]; group
    _ = u * (z * u * z) * z := by group
    _ = z * u * z * u * z := by rw [← hpu]

namespace RootCore

variable [Finite G] {M B Q : Subgroup G} (H : RootCore M B Q)
include H

theorem normalizer_le_centralizer_of_not_le_M {g : G} (hgM : ¬ conjSubgroup g B ≤ M) :
    Q ⊓ Subgroup.normalizer (conjSubgroup g B : Set G) ≤
      Subgroup.centralizer ((conjSubgroup g B ⊓ M : Subgroup G) : Set G) := by
  have hAQ := H.conj_inf_R_eq_bot_of_not_le_M hgM
  intro n hn
  obtain ⟨hnQ, hnN⟩ := Subgroup.mem_inf.mp hn
  rw [Subgroup.mem_centralizer_iff]
  intro a ha
  obtain ⟨haA, haM⟩ := Subgroup.mem_inf.mp ha
  have h1 : a * n * a⁻¹ * n⁻¹ ∈ conjSubgroup g B := by
    have : n * a⁻¹ * n⁻¹ ∈ conjSubgroup g B :=
      (Subgroup.mem_normalizer_iff.mp hnN _).mp (inv_mem haA)
    have h2 := mul_mem haA this
    rwa [show a * (n * a⁻¹ * n⁻¹) = a * n * a⁻¹ * n⁻¹ by group] at h2
  have h3 : a * n * a⁻¹ * n⁻¹ ∈ Q := by
    have : a * n * a⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (H.M_le_normalizer_Q haM) n).mp hnQ
    exact mul_mem this (inv_mem hnQ)
  have h4 : a * n * a⁻¹ * n⁻¹ ∈ conjSubgroup g B ⊓ Q := Subgroup.mem_inf.mpr ⟨h1, h3⟩
  rw [hAQ, Subgroup.mem_bot] at h4
  have h5 : a * n * a⁻¹ = n := by
    have := congrArg (· * n) h4
    simpa [mul_assoc] using this
  calc a * n = a * n * a⁻¹ * a := by group
    _ = n * a := by rw [h5]

theorem centralizer_Q_eq_of_not_le_M {g y : G} (hgM : ¬ conjSubgroup g B ≤ M)
    (hy : y ∈ conjSubgroup g B ⊓ M) (hy1 : y ≠ 1) :
    Q ⊓ Subgroup.centralizer ({y} : Set G) =
        Q ⊓ Subgroup.centralizer ((conjSubgroup g B ⊓ M : Subgroup G) : Set G) ∧
      Q ⊓ Subgroup.centralizer ((conjSubgroup g B ⊓ M : Subgroup G) : Set G) =
        Q ⊓ Subgroup.normalizer (conjSubgroup g B : Set G) := by
  have hNC : Q ⊓ Subgroup.normalizer (conjSubgroup g B : Set G) ≤
      Q ⊓ Subgroup.centralizer ((conjSubgroup g B ⊓ M : Subgroup G) : Set G) := fun n hn =>
    Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hn).1,
      H.normalizer_le_centralizer_of_not_le_M hgM hn⟩
  have hCN : Q ⊓ Subgroup.centralizer ({y} : Set G) ≤
      Q ⊓ Subgroup.normalizer (conjSubgroup g B : Set G) := by
    intro c hc
    obtain ⟨hcQ, hcC⟩ := Subgroup.mem_inf.mp hc
    refine Subgroup.mem_inf.mpr ⟨hcQ, ?_⟩
    rw [H.normalizer_conj_eq]
    exact H.centralizer_le_conj (Subgroup.mem_inf.mp hy).1 hy1 hcC
  have hCy : Q ⊓ Subgroup.centralizer ((conjSubgroup g B ⊓ M : Subgroup G) : Set G) ≤
      Q ⊓ Subgroup.centralizer ({y} : Set G) :=
    inf_le_inf_left _ (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hy))
  exact ⟨le_antisymm (hCN.trans hNC) hCy, le_antisymm (hCy.trans hCN) hNC⟩

theorem sq_eq_one_of_mem_normalizer_of_not_le_M {g y : G} (hgM : ¬ conjSubgroup g B ≤ M)
    (hyQ : y ∈ Q)
    (hyN : y ∈ Subgroup.normalizer (conjSubgroup g B : Set G)) : y ^ 2 = 1 := by
  by_contra hz1
  obtain ⟨z, hz⟩ : ∃ z, z = y * y := ⟨_, rfl⟩
  have hzy2 : y ^ 2 = z := by rw [hz, sq]
  rw [hzy2] at hz1
  have hzB : z ∈ B := hzy2 ▸ H.sq_mem hyQ
  have hzN : z ∈ Subgroup.normalizer (conjSubgroup g B : Set G) := hz ▸ mul_mem hyN hyN
  have hyC := H.normalizer_le_centralizer_of_not_le_M hgM (Subgroup.mem_inf.mpr ⟨hyQ, hyN⟩)
  have hCM : Subgroup.centralizer ({z} : Set G) ≤ M :=
    H.normalizer_eq_and_centralizer_le.2 _ hzB hz1
  have hE := isElemAbelian_conjSubgroup H.elemAb g
  have hcomm : ∀ u ∈ conjSubgroup g B, ∀ v ∈ conjSubgroup g B, u * v = v * u := by
    intro u hu v hv
    have := hE.1
    exact congrArg Subtype.val (mul_comm' (⟨u, hu⟩ : conjSubgroup g B) ⟨v, hv⟩)
  have hsq : ∀ u ∈ conjSubgroup g B, u * u = 1 := fun u hu => by
    rw [← sq]; exact hE.2 u hu
  have hzz : z * z = 1 := by rw [← sq]; exact H.sq_eq_one _ hzB
  have hzinv : z⁻¹ = z := inv_eq_of_mul_eq_one_right hzz
  have hzy : z * y = y * z := by rw [hz]; group
  have hyinvz : y⁻¹ * z = z * y⁻¹ := by rw [hz]; group
  have hyc : ∀ c ∈ conjSubgroup g B, z * c = c * z → y * c = c * y := by
    intro c hc hzc
    have hcM : c ∈ M := hCM (Subgroup.mem_centralizer_singleton_iff.mpr hzc.symm)
    exact ((Subgroup.mem_centralizer_iff.mp hyC) c (Subgroup.mem_inf.mpr ⟨hc, hcM⟩)).symm
  have hzA : ∀ u ∈ conjSubgroup g B, z * u * z ∈ conjSubgroup g B := fun u hu => by
    have := (Subgroup.mem_normalizer_iff.mp hzN u).mp hu
    rwa [hzinv] at this
  have hyA : ∀ u ∈ conjSubgroup g B, y * u * y⁻¹ ∈ conjSubgroup g B := fun u hu =>
    (Subgroup.mem_normalizer_iff.mp hyN u).mp hu
  refine hgM fun u hu => hCM (Subgroup.mem_centralizer_singleton_iff.mpr ?_)
  have hp := hzA u hu
  have hc : z * u * z * u ∈ conjSubgroup g B := mul_mem hp hu
  have hyc' := hyc _ hc (comm_mul_of_conj hzz (hcomm _ hp _ hu))
  have hw : y * u * y⁻¹ * u ∈ conjSubgroup g B := mul_mem (hyA u hu) hu
  have e1 : z * (y * u * y⁻¹ * u) * z = y * (z * u * z) * y⁻¹ * (z * u * z) := by
    calc z * (y * u * y⁻¹ * u) * z = (z * y) * u * (y⁻¹ * z) * (z * u * z) := by
          have e : (z * y) * u * (y⁻¹ * z) * (z * u * z) = z * y * u * y⁻¹ * (z * z) * u * z := by
            group
          rw [e, hzz]; group
      _ = (y * z) * u * (z * y⁻¹) * (z * u * z) := by rw [hzy, hyinvz]
      _ = y * (z * u * z) * y⁻¹ * (z * u * z) := by group
  have e2 : z * u * z = (z * u * z * u) * u := by
    calc z * u * z = z * u * z * (u * u) := by rw [hsq u hu]; group
      _ = (z * u * z * u) * u := by group
  have e3 : y * (z * u * z * u) * y⁻¹ = z * u * z * u := by
    calc y * (z * u * z * u) * y⁻¹ = (z * u * z * u) * y * y⁻¹ := by rw [hyc']
      _ = z * u * z * u := by group
  have e4 : z * (y * u * y⁻¹ * u) * z = y * u * y⁻¹ * u := by
    rw [e1, e2]
    obtain ⟨c, hcdef⟩ : ∃ c, c = z * u * z * u := ⟨_, rfl⟩
    rw [← hcdef] at e3 hc ⊢
    have e5 : y * (c * u) * y⁻¹ = c * (y * u * y⁻¹) := by
      calc y * (c * u) * y⁻¹ = (y * c * y⁻¹) * (y * u * y⁻¹) := by group
        _ = c * (y * u * y⁻¹) := by rw [e3]
    rw [e5]
    calc c * (y * u * y⁻¹) * (c * u) = c * ((y * u * y⁻¹) * c) * u := by group
      _ = c * (c * (y * u * y⁻¹)) * u := by rw [hcomm _ (hyA u hu) _ hc]
      _ = (c * c) * (y * u * y⁻¹) * u := by group
      _ = y * u * y⁻¹ * u := by rw [hsq c hc]; group
  have hzw : z * (y * u * y⁻¹ * u) = y * u * y⁻¹ * u * z := by
    calc z * (y * u * y⁻¹ * u) = z * (y * u * y⁻¹ * u) * (z * z) := by rw [hzz]; group
      _ = (z * (y * u * y⁻¹ * u) * z) * z := by group
      _ = y * u * y⁻¹ * u * z := by rw [e4]
  have hyw := hyc _ hw hzw
  have e6 : y * u * y⁻¹ = (y * u * y⁻¹ * u) * u := by
    calc y * u * y⁻¹ = y * u * y⁻¹ * (u * u) := by rw [hsq u hu]; group
      _ = (y * u * y⁻¹ * u) * u := by group
  obtain ⟨w, hwdef⟩ : ∃ w, w = y * u * y⁻¹ * u := ⟨_, rfl⟩
  rw [← hwdef] at hw hyw e6
  have e7 : z * u * z⁻¹ = u := by
    calc z * u * z⁻¹ = y * (y * u * y⁻¹) * y⁻¹ := by rw [hz]; group
      _ = y * (w * u) * y⁻¹ := by rw [← e6]
      _ = (y * w * y⁻¹) * (y * u * y⁻¹) := by group
      _ = w * (w * u) := by
          rw [e6, hyw]; group
      _ = (w * w) * u := by group
      _ = u := by rw [hsq w hw]; group
  calc u * z = z * u * z⁻¹ * z := by rw [e7]
    _ = z * u := by group

end RootCore

end CFSG.RankThree.GF2n.Tim78

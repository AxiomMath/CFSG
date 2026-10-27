module

public import CFSG.RankThree.GF2n.Parrott.PSp43Model
public import CFSG.RankThree.GF2n.Parrott.Proposition6IndexTwoModelFacts
public import CFSG.Sporadic.Co2Smith.GlC0JankoA
public import CFSG.LocalAnalysis.OddStandard.Solomon75LPlusDefs
public import CFSG.LieType.HighestRoot.CentChevalleySLThree
public import Certificates.Certificate2012
public import Certificates.Certificate946005
public import CFSG.LocalAnalysis.OddStandard.Solomon75Basic

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG.ComponentClassification.CatFactsSmall.PSp43
open CFSG.Sporadic.Co2Smith
open CFSG.OddStandard.Solomon75 (SL23)
open CFSG.ClassicalInvolution.Q3.Q3T6

section Injective

private theorem sl23L1_inv (A : SL23) : sl23L1 A⁻¹ = (sl23L1 A)⁻¹ := by
  have h := sl23L1_mul A A⁻¹
  rw [mul_inv_cancel, sl23L1_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

private theorem sl23L1_injective : Function.Injective sl23L1 := by
  intro A B h
  have h1 : sl23L1 (A * B⁻¹) = 1 := by
    rw [sl23L1_mul, sl23L1_inv, h, mul_inv_cancel]
  exact mul_inv_eq_one.1 (sl23L1_eq_one h1)

end Injective

section Pure

private theorem sl23L1_mem (A : SL23) : sl23L1 A ∈ QP45.originalSubgroup := by
  rw [sl23L1]
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _
    (Subgroup.pow_mem _ alpha1_mem_Q _) (Subgroup.pow_mem _ beta1_mem_Q _))
    (Subgroup.pow_mem _ sigma1_mem_Q _)) (Subgroup.pow_mem _ t_mem_Q _)

private def p6Iota (A : SL23) : ↥QP45.originalSubgroup :=
  ⟨sl23L1 A, sl23L1_mem A⟩

private def p6w : ↥QP45.originalSubgroup := ⟨u, u_mem_Q⟩

private def p6t : ↥QP45.originalSubgroup := ⟨t, t_mem_Q⟩

private theorem p6w_sq : p6w * p6w = 1 := by
  apply Subtype.ext
  simpa [p6w] using u_sq

private theorem p6w_inv : p6w⁻¹ = p6w :=
  inv_eq_of_mul_eq_one_right p6w_sq

private theorem p6w_mul_t : p6w * x45P = x45P * p6w := by
  apply Subtype.ext
  simpa [p6w, x45P, t] using t_commute_u.symm

private theorem p6w_centralizer_t :
    p6w ∈ Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup) :=
  Subgroup.mem_centralizer_singleton_iff.2 p6w_mul_t

private theorem p6w_conj_t : (MulAut.conj p6w) x45P = x45P := by
  rw [MulAut.conj_apply]
  calc
    p6w * x45P * p6w⁻¹ = p6w * x45P * p6w := by rw [p6w_inv]
    _ = (x45P * p6w) * p6w := by rw [p6w_mul_t]
    _ = x45P * (p6w * p6w) := by rw [mul_assoc]
    _ = x45P := by rw [p6w_sq, mul_one]

private theorem p6w_conj_conj (b : ↥QP45.originalSubgroup) :
    (MulEquiv.toMonoidHom (MulAut.conj p6w))
      ((MulEquiv.toMonoidHom (MulAut.conj p6w)) b) = b := by
  change (MulAut.conj p6w) ((MulAut.conj p6w) b) = b
  calc
    (MulAut.conj p6w) ((MulAut.conj p6w) b)
        = (MulAut.conj p6w * MulAut.conj p6w) b := by rw [MulAut.mul_apply]
    _ = (MulAut.conj (p6w * p6w)) b := by rw [map_mul]
    _ = (MulAut.conj (1 : ↥QP45.originalSubgroup)) b := by rw [p6w_sq]
    _ = b := by simp

private theorem p6_conj_apply_eq (c : ↥QP45.originalSubgroup) :
    (MulEquiv.toMonoidHom (MulAut.conj p6w)) c = p6w * c * p6w := by
  change (MulAut.conj p6w) c = p6w * c * p6w
  rw [MulAut.conj_apply, p6w_inv]

end Pure

section All

private def p6IotaHom : SL23 →* ↥QP45.originalSubgroup where
  toFun := p6Iota
  map_one' := Subtype.ext sl23L1_one
  map_mul' A B := Subtype.ext (sl23L1_mul A B)

private def p6L1 : Subgroup ↥QP45.originalSubgroup := p6IotaHom.range

private def p6L2 : Subgroup ↥QP45.originalSubgroup :=
  p6L1.map (MulAut.conj p6w).toMonoidHom

private theorem p6Iota_injective : Function.Injective p6IotaHom := by
  intro A B h
  apply sl23L1_injective
  exact congrArg Subtype.val h

private theorem p6L1_iso : Nonempty (↥p6L1 ≃* SL23) :=
  ⟨(MonoidHom.ofInjective p6Iota_injective).symm⟩

private theorem p6_comm :
    ∀ a ∈ p6L1, ∀ b ∈ p6L2, a * b = b * a := by
  intro a ha b hb
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 (by simpa only [p6L1] using ha)
  obtain ⟨c, hc, hbc⟩ := Subgroup.mem_map.1 (by simpa only [p6L2] using hb)
  obtain ⟨B, hB⟩ := MonoidHom.mem_range.1 (by simpa only [p6L1] using hc)
  have ha' : a = p6IotaHom A := hA.symm
  have hb' : b = (MulEquiv.toMonoidHom (MulAut.conj p6w)) (p6IotaHom B) := by
    rw [← hbc, ← hB]
  calc
    a * b = p6IotaHom A *
        (MulEquiv.toMonoidHom (MulAut.conj p6w)) (p6IotaHom B) := by rw [ha', hb']
    _ = (MulEquiv.toMonoidHom (MulAut.conj p6w)) (p6IotaHom B) * p6IotaHom A := by
      rw [p6_conj_apply_eq]
      apply Subtype.ext
      exact sl23L1_commute_conj_u A B u_sq
    _ = b * a := by rw [← hb', ← ha']

private theorem p6L1_centralizer_t :
    p6L1 ≤ Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup) := by
  intro a ha
  rw [Subgroup.mem_centralizer_singleton_iff]
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 (by simpa only [p6L1] using ha)
  rw [← hA]
  apply Subtype.ext
  simpa [p6Iota, p6IotaHom, x45P, t] using sl23L1_commute_t A

private theorem p6L2_centralizer_t :
    p6L2 ≤ Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup) := by
  calc
    p6L2 = p6L1.map (MulAut.conj p6w).toMonoidHom := rfl
    _ ≤ (Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup)).map
        (MulAut.conj p6w).toMonoidHom := Subgroup.map_mono p6L1_centralizer_t
    _ ≤ Subgroup.centralizer ((MulAut.conj p6w) '' ({x45P} : Set _)) :=
      Subgroup.map_centralizer_le_centralizer_image _ _
    _ = Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup) := by
      rw [Set.image_singleton, p6w_conj_t]

private theorem p6_swap1 :
    ∀ a ∈ p6L1, p6w * a * p6w⁻¹ ∈ p6L2 := by
  intro a ha
  rw [p6w_inv, p6L2, ← p6_conj_apply_eq a]
  exact Subgroup.mem_map_of_mem _ ha

private theorem p6_swap2 :
    ∀ a ∈ p6L2, p6w * a * p6w⁻¹ ∈ p6L1 := by
  intro a ha
  rw [p6L2] at ha
  obtain ⟨b, hb, hba⟩ := Subgroup.mem_map.1 ha
  rw [← hba, p6w_inv,
    ← p6_conj_apply_eq ((MulEquiv.toMonoidHom (MulAut.conj p6w)) b)]
  rw [p6w_conj_conj]
  exact hb

private theorem p6Iota_neg_one_eq_t : p6IotaHom (-1) = p6t := by
  apply Subtype.ext
  simpa [p6IotaHom, p6Iota, p6t] using sl23L1_neg_one

private theorem p6_iota_neg_one_conj :
    (MulEquiv.toMonoidHom (MulAut.conj p6w)) (p6IotaHom (-1)) = p6IotaHom (-1) := by
  rw [p6Iota_neg_one_eq_t, p6_conj_apply_eq]
  apply Subtype.ext
  change u * t * u = t
  rw [← t_commute_u, mul_assoc, u_sq, mul_one]

private theorem p6_iota_neg_one_mem_L2 : p6IotaHom (-1) ∈ p6L2 := by
  rw [p6L2]
  have h := Subgroup.mem_map_of_mem (MulEquiv.toMonoidHom (MulAut.conj p6w))
    (MonoidHom.mem_range.2 ⟨-1, rfl⟩ : p6IotaHom (-1) ∈ p6L1)
  rwa [p6_iota_neg_one_conj] at h

private theorem p6_inf_le_center :
    p6L1 ⊓ p6L2 ≤ (Subgroup.center p6L1).map p6L1.subtype := by
  intro a ha
  obtain ⟨ha1, ha2⟩ := Subgroup.mem_inf.1 ha
  refine Subgroup.mem_map.2 ⟨⟨a, ha1⟩, ?_, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  exact p6_comm y y.2 a ha2

private theorem p6_center_le_L2 :
    (Subgroup.center p6L1).map p6L1.subtype ≤ p6L2 := by
  intro g hg
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.1 hg
  change (↑z : ↥QP45.originalSubgroup) ∈ p6L2
  obtain ⟨A, hA⟩ := MonoidHom.mem_range.1 (by simpa only [p6L1] using z.2)
  have hAcen : A ∈ Subgroup.center SL23 := by
    rw [Subgroup.mem_center_iff]
    intro B
    apply sl23L1_injective
    rw [sl23L1_mul, sl23L1_mul]
    have hmem := (Subgroup.mem_center_iff.1 hz)
      (⟨p6IotaHom B, MonoidHom.mem_range.2 ⟨B, rfl⟩⟩ : ↥p6L1)
    have h' : p6IotaHom B * (↑z : ↥QP45.originalSubgroup) =
        (↑z : ↥QP45.originalSubgroup) * p6IotaHom B := by
      simpa only [Subgroup.coe_mul, Subtype.coe_mk] using congrArg Subtype.val hmem
    rw [← hA] at h'
    simpa [p6IotaHom, p6Iota] using congrArg Subtype.val h'
  have hA1 : A = 1 ∨ A = -1 :=
    (CFSG.LieType.HighestRoot.mem_center_SL23_iff A).1 hAcen
  rcases hA1 with rfl | rfl
  · have hz1 : (↑z : ↥QP45.originalSubgroup) = 1 := by
      rw [← hA]
      simpa [p6IotaHom, p6Iota] using sl23L1_one
    rw [hz1]
    exact p6L2.one_mem
  · have hzn : (↑z : ↥QP45.originalSubgroup) = p6IotaHom (-1) := by
      rw [← hA]
    rw [hzn]
    exact p6_iota_neg_one_mem_L2

private theorem p6_inf_eq_center :
    p6L1 ⊓ p6L2 = (Subgroup.center p6L1).map p6L1.subtype :=
  le_antisymm p6_inf_le_center
    (le_inf (Subgroup.map_subtype_le _) p6_center_le_L2)

private theorem p6w_not_mem_sup : p6w ∉ p6L1 ⊔ p6L2 := by
  intro hx
  have hL2_cent : p6L2 ≤ Subgroup.centralizer (p6L1 : Set ↥QP45.originalSubgroup) := by
    intro b hb
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact p6_comm a ha b hb
  have hL2_norm : p6L2 ≤ Subgroup.normalizer (p6L1 : Set ↥QP45.originalSubgroup) :=
    hL2_cent.trans (Subgroup.centralizer_le_normalizer _)
  have hN : p6L1 ⊔ p6L2 ≤ Subgroup.normalizer (p6L1 : Set ↥QP45.originalSubgroup) :=
    sup_le p6L1.le_normalizer hL2_norm
  have hw : p6w ∈ Subgroup.normalizer (p6L1 : Set ↥QP45.originalSubgroup) := hN hx
  have hmap : p6L1.map (MulAut.conj p6w).toMonoidHom = p6L1 := by
    simpa using (Subgroup.mem_normalizer_iff_map_conj_eq.1 hw)
  have hL2eq : p6L2 = p6L1 := by
    rw [p6L2, hmap]
  have hL1center : p6L1 = (Subgroup.center p6L1).map p6L1.subtype := by
    rw [← p6_inf_eq_center, hL2eq, inf_idem]
  have hL1comm : ∀ x y : ↥p6L1, x * y = y * x := by
    intro x y
    apply Subtype.ext
    let x' : ↥QP45.originalSubgroup := x
    have hxmem : x' ∈ p6L1 := x.2
    have hxc : x' ∈ (Subgroup.center p6L1).map p6L1.subtype := by
      rw [hL1center] at hxmem
      exact hxmem
    obtain ⟨z, hz, hzx⟩ := Subgroup.mem_map.1 hxc
    have hxcent : x ∈ Subgroup.center p6L1 := by
      rw [show x = z from Subtype.ext hzx.symm]
      exact hz
    have h := Subgroup.mem_center_iff.1 hxcent y
    exact (congrArg Subtype.val h).symm
  have hSLcomm : ∀ A B : SL23, A * B = B * A := by
    obtain ⟨e⟩ := p6L1_iso
    intro A B
    obtain ⟨a, rfl⟩ := e.surjective A
    obtain ⟨b, rfl⟩ := e.surjective B
    calc
      e a * e b = e (a * b) := (e.map_mul a b).symm
      _ = e (b * a) := congrArg e (hL1comm a b)
      _ = e b * e a := e.map_mul b a
  have hST : autGenS * autGenT ≠ autGenT * autGenS := by decide
  exact hST (hSLcomm autGenS autGenT)

end All

theorem exists_sl23_swap_centralizer_x45P :
    ∃ (L1 L2 : Subgroup ↥QP45.originalSubgroup) (w : ↥QP45.originalSubgroup),
      Nonempty (↥L1 ≃* SL23) ∧ (∀ a ∈ L1, ∀ b ∈ L2, a * b = b * a) ∧
      L1 ⊓ L2 = (Subgroup.center L1).map L1.subtype ∧
      (∀ a ∈ L1, w * a * w⁻¹ ∈ L2) ∧ (∀ a ∈ L2, w * a * w⁻¹ ∈ L1) ∧ w * w = 1 ∧
      w ∉ L1 ⊔ L2 ∧
      L1 ≤ Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup) ∧
      L2 ≤ Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup) ∧
      w ∈ Subgroup.centralizer ({x45P} : Set ↥QP45.originalSubgroup) :=
  ⟨p6L1, p6L2, p6w, p6L1_iso, p6_comm, p6_inf_eq_center, p6_swap1, p6_swap2, p6w_sq,
    p6w_not_mem_sup, p6L1_centralizer_t, p6L2_centralizer_t, p6w_centralizer_t⟩

end CFSG.RankThree.GF2n.Parrott

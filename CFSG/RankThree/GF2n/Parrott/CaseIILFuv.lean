module

public import CFSG.RankThree.GF2n.Parrott.CaseIILemma36A
public import CFSG.RankThree.GF2n.Parrott.CaseIISpinCoord
public import CFSG.RankThree.GF2n.Parrott.SpinCoordUV
public import CFSG.RankThree.GF2n.Parrott.SpinUVChecks
public import CFSG.RankThree.GF2n.Parrott.A1LocalData
public import CFSG.GroupTheory.ConjugateDerivedCentralizer
public import CFSG.GroupTheory.OddConjTwoClasses

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.Open Subgroup
open CFSG.ComponentClassification.CatFactsSmall.PSp43
open scoped Matrix

set_option quotPrecheck false in
local notation "A45" => ↥QA45.originalSubgroup
set_option quotPrecheck false in
local notation "uA" => (⟨u, u_mem_A⟩ : A45)
set_option quotPrecheck false in
local notation "vA" => (⟨v, v_mem_A⟩ : A45)
local notation "GL8" => Matrix.GeneralLinearGroup (Fin 8) (ZMod 2)
local notation "Mat8" => Matrix (Fin 8) (Fin 8) (ZMod 2)

variable {G : Type} [Group G] [Finite G] {z : G}

private theorem conj_mem_J {y : G} (hy : y ∈ H z) {j : G} (hj : j ∈ J z) : y * j * y⁻¹ ∈ J z :=
  (mem_normalizer_iff.mp (J_le_normalizer_A hy) j).mp hj

private theorem card_centralizer_eq_of_isConj {A : Type*} [Group A] [Finite A] {x x' : A}
    (hx : IsConj x x') :
    Nat.card (centralizer ({x} : Set A)) = Nat.card (centralizer ({x'} : Set A)) := by
  have h1 := Subgroup.card_mul_index (centralizer ({x} : Set A))
  have h2 := Subgroup.card_mul_index (centralizer ({x'} : Set A))
  rw [Subgroup.index_centralizer_eq_ncard] at h1 h2
  rw [isConj_iff_conjugatesOf_eq.mp hx] at h1
  have hpos : 0 < (conjugatesOf x').ncard :=
    Set.ncard_pos (Set.toFinite _) |>.mpr ⟨x', mem_conjugatesOf_self⟩
  exact Nat.eq_of_mul_eq_mul_right hpos (h1.trans h2.symm)


theorem exists_centralizer_lift_uv_A (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    {a : G} (haH : a ∈ H z) (haa : a * a = 1) {g : A45}
    (hg : g * qH D ⟨a, haH⟩ * g⁻¹ = uA * vA) {c : A45}
    (hc : (uA * vA) * c = c * (uA * vA)) (hodd : Odd (orderOf c)) (hc1 : 1 < orderOf c) :
    ∃ (r : G) (hr : r ∈ H z), r * a = a * r ∧ qH D ⟨r, hr⟩ = g⁻¹ * c * g ∧
      orderOf r = orderOf c := by
  obtain ⟨κ, hadd, hsurj, hker, hsq, -, hact⟩ := exists_spinCoord_A h D hIII g
  have hzJ : z ∈ J z := z_mem_J_A h
  have hzc : ∀ j ∈ J z, z * j = j * z := fun j hj =>
    (mem_centralizer_singleton_iff.mp (J_le_H hj)).symm
  have hza : z * a = a * z := (mem_centralizer_singleton_iff.mp haH).symm
  have haJ : ∀ j ∈ J z, a * j * a⁻¹ ∈ J z := fun j hj => conj_mem_J haH hj
  have haκ : ∀ j ∈ J z, κ (a * j * a⁻¹) = spinMuv *ᵥ κ j := by
    intro j hj
    rw [hact a haH j hj, hg, rhoA_uv_eq_spinMuv]
  have hS := spinCoord_two_classes hzJ hzc hza hadd hsurj hker hsq haa haJ haκ
    spinMuv_fixed_mem_range
  have hqa : qH D ⟨a, haH⟩ = g⁻¹ * (uA * vA) * g := by
    rw [← hg]
    group
  have hordc' : orderOf (g⁻¹ * c * g) = orderOf c :=
    (SemiconjBy.orderOf_eq g⁻¹ (x := c) (y := g⁻¹ * c * g) (by unfold SemiconjBy; group)).symm
  have hker2 : IsPGroup 2 (qH D).ker := by
    rw [ker_qH D]
    exact isPGroup_J_subgroupOf
  obtain ⟨x₀, hx₀⟩ := qH_surjective D (g⁻¹ * c * g)
  obtain ⟨n, hn, hnord⟩ := exists_pow_lift_orderOf_eq (qH D) hker2 (c := x₀) (m := orderOf c)
    hodd hc1 (by rw [hx₀, hordc'])
  set r₀ : ↥(H z) := x₀ ^ n with hr₀
  have hqr₀ : qH D r₀ = g⁻¹ * c * g := by rw [hr₀, hn, hx₀]
  have hr₀J : ∀ j ∈ J z, (r₀ : G) * j * (r₀ : G)⁻¹ ∈ J z := fun j hj => conj_mem_J r₀.2 hj
  have hr₀J' : ∀ j ∈ J z, (r₀ : G)⁻¹ * j * (r₀ : G) ∈ J z := fun j hj => by
    simpa using conj_mem_J (inv_mem r₀.2) hj
  have hra : a⁻¹ * ((r₀ : G) * a * (r₀ : G)⁻¹) ∈ J z := by
    have hmem : (⟨a, haH⟩ : ↥(H z))⁻¹ * (r₀ * ⟨a, haH⟩ * r₀⁻¹) ∈ (J z).subgroupOf (H z) := by
      rw [J_mem_iff D, map_mul, map_inv, map_mul, map_mul, map_inv, hqr₀, hqa]
      calc (g⁻¹ * (uA * vA) * g)⁻¹ * (g⁻¹ * c * g * (g⁻¹ * (uA * vA) * g) * (g⁻¹ * c * g)⁻¹)
          = g⁻¹ * ((uA * vA)⁻¹ * (c * (uA * vA)) * c⁻¹) * g := by group
        _ = g⁻¹ * ((uA * vA)⁻¹ * ((uA * vA) * c) * c⁻¹) * g := by rw [hc]
        _ = 1 := by group
    exact Subgroup.mem_subgroupOf.mp hmem
  have hodd₀ : Odd (orderOf (r₀ : G)) := by
    rw [Subgroup.orderOf_coe, hnord]
    exact hodd
  obtain ⟨k, hkJ, hk⟩ := CFSG.GroupTheory.exists_conj_eq_of_odd_of_two_classes (J z) (b := a * z)
    haa haJ hr₀J hr₀J' hS hra hodd₀
  have hr₁H : k⁻¹ * (r₀ : G) ∈ H z := mul_mem (inv_mem (J_le_H hkJ)) r₀.2
  have hr₁a : (k⁻¹ * (r₀ : G)) * a = a * (k⁻¹ * (r₀ : G)) := by
    have e : k⁻¹ * (r₀ : G) * a * (k⁻¹ * (r₀ : G))⁻¹ = a := by
      calc k⁻¹ * (r₀ : G) * a * (k⁻¹ * (r₀ : G))⁻¹
          = k⁻¹ * ((r₀ : G) * a * (r₀ : G)⁻¹) * k := by group
        _ = k⁻¹ * (k * a * k⁻¹) * k := by rw [hk]
        _ = a := by group
    calc (k⁻¹ * (r₀ : G)) * a
        = (k⁻¹ * (r₀ : G) * a * (k⁻¹ * (r₀ : G))⁻¹) * (k⁻¹ * (r₀ : G)) := by group
      _ = a * (k⁻¹ * (r₀ : G)) := by rw [e]
  have hqr₁ : qH D ⟨k⁻¹ * (r₀ : G), hr₁H⟩ = g⁻¹ * c * g := by
    have e : (⟨k⁻¹ * (r₀ : G), hr₁H⟩ : ↥(H z)) = (⟨k, J_le_H hkJ⟩ : ↥(H z))⁻¹ * r₀ :=
      Subtype.ext rfl
    rw [e, map_mul, map_inv, (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr hkJ), inv_one,
      one_mul, hqr₀]
  obtain ⟨n', hn', hn'ord⟩ := exists_pow_lift_orderOf_eq (qH D) hker2
    (c := ⟨k⁻¹ * (r₀ : G), hr₁H⟩) (m := orderOf c) hodd hc1 (by rw [hqr₁, hordc'])
  refine ⟨(k⁻¹ * (r₀ : G)) ^ n', pow_mem hr₁H n', (Commute.pow_left hr₁a n').eq, ?_, ?_⟩
  · have e : (⟨(k⁻¹ * (r₀ : G)) ^ n', pow_mem hr₁H n'⟩ : ↥(H z)) =
        (⟨k⁻¹ * (r₀ : G), hr₁H⟩ : ↥(H z)) ^ n' := Subtype.ext (by simp)
    rw [e, hn', hqr₁]
  · have e : (k⁻¹ * (r₀ : G)) ^ n' = (((⟨k⁻¹ * (r₀ : G), hr₁H⟩ : ↥(H z)) ^ n' : ↥(H z)) : G) := by
      simp
    rw [e, Subgroup.orderOf_coe, hn'ord]

theorem z_mem_commutator_centralizer_of_uv_A (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    {a : G} (haH : a ∈ H z) (haa : a * a = 1) (hq : IsConj (qH D ⟨a, haH⟩) (uA * vA)) :
    z ∈ ⁅centralizer ({z} : Set G) ⊓ centralizer {a},
      centralizer ({z} : Set G) ⊓ centralizer {a}⁆ := by
  obtain ⟨g, hg⟩ := isConj_iff.mp hq
  obtain ⟨κ, hadd, hsurj, hker, hsq, hcomm, hact⟩ := exists_spinCoord_A h D hIII g
  have hzJ : z ∈ J z := z_mem_J_A h
  have hza : z * a = a * z := (mem_centralizer_singleton_iff.mp haH).symm
  have haJ : ∀ j ∈ J z, a * j * a⁻¹ ∈ J z := fun j hj => conj_mem_J haH hj
  have haκ : ∀ j ∈ J z, κ (a * j * a⁻¹) = spinMuv *ᵥ κ j := by
    intro j hj
    rw [hact a haH j hj, hg, rhoA_uv_eq_spinMuv]
  obtain ⟨r₁, hr₁H, hr₁a, hqr₁, -⟩ := exists_centralizer_lift_uv_A h D hIII haH haa hg
    uvFive_commute (by rw [orderOf_uvFive]; exact ⟨2, rfl⟩) (by rw [orderOf_uvFive]; norm_num)
  obtain ⟨r₂, hr₂H, hr₂a, hqr₂, -⟩ := exists_centralizer_lift_uv_A h D hIII haH haa hg
    uvThree_commute (by rw [orderOf_uvThree]; exact ⟨1, rfl⟩) (by rw [orderOf_uvThree]; norm_num)
  have hr₁κ : ∀ j ∈ J z, κ (r₁ * j * r₁⁻¹) = spinM5uv *ᵥ κ j := by
    intro j hj
    rw [hact r₁ hr₁H j hj, hqr₁, show g * (g⁻¹ * uvFive * g) * g⁻¹ = uvFive by group, rhoA_uvFive]
  have hr₂κ : ∀ j ∈ J z, κ (r₂ * j * r₂⁻¹) = spinM3uv *ᵥ κ j := by
    intro j hj
    rw [hact r₂ hr₂H j hj, hqr₂, show g * (g⁻¹ * uvThree * g) * g⁻¹ = uvThree by group,
      rhoA_uvThree]
  have hmem := spinCoord_z_mem_closure hzJ hza hadd hsurj hker hsq hcomm haa haJ haκ
    spinMuv_mul_self spinMuv_fixed_singular spinMuv_fixed_mem_range hr₁a hr₂a
    (fun j hj => conj_mem_J hr₁H hj) (fun j hj => conj_mem_J hr₂H hj) hr₁κ hr₂κ spinMuv_no_psi
  refine (Subgroup.closure_le _).mpr ?_ hmem
  rintro x ⟨c, hcJ, hca, rfl | rfl⟩
  · have hr₁K : r₁ ∈ centralizer ({z} : Set G) ⊓ centralizer {a} :=
      ⟨hr₁H, mem_centralizer_singleton_iff.mpr hr₁a⟩
    have hcK : c ∈ centralizer ({z} : Set G) ⊓ centralizer {a} :=
      ⟨J_le_H hcJ, mem_centralizer_singleton_iff.mpr hca.symm⟩
    exact commutator_mem_commutator hr₁K hcK
  · have hr₂K : r₂ ∈ centralizer ({z} : Set G) ⊓ centralizer {a} :=
      ⟨hr₂H, mem_centralizer_singleton_iff.mpr hr₂a⟩
    have hcK : c ∈ centralizer ({z} : Set G) ⊓ centralizer {a} :=
      ⟨J_le_H hcJ, mem_centralizer_singleton_iff.mpr hca.symm⟩
    exact commutator_mem_commutator hr₂K hcK

theorem not_isConj_z_of_uv_A (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    (hF1 : ∀ j ∈ J z, orderOf j = 2 → j ∉ zpowers z → ¬ IsConj z j) :
    ∀ (a : G) (ha : a ∈ H z), a * a = 1 → IsConj (qH D ⟨a, ha⟩) (uA * vA) → ¬ IsConj z a := by
  intro a haH haa hq hza
  obtain ⟨c, hca⟩ := isConj_iff.mp hza
  have hz2 : orderOf z = 2 := orderOf_z_A h
  have hzz : z * z = 1 := by
    rw [← sq, ← hz2]
    exact pow_orderOf_eq_one z
  have hz1 : z ≠ 1 := by
    intro hz
    rw [hz, orderOf_one] at hz2
    norm_num at hz2
  have haz : a * z = z * a := mem_centralizer_singleton_iff.mp haH
  set y : G := c⁻¹ * z * c with hy
  have hyH : y ∈ H z := by
    rw [H, mem_centralizer_singleton_iff]
    calc y * z = c⁻¹ * (z * (c * z * c⁻¹)) * c := by rw [hy]; group
      _ = c⁻¹ * ((c * z * c⁻¹) * z) * c := by rw [hca, haz]
      _ = z * y := by rw [hy]; group
  have hyy : y * y = 1 := by
    calc y * y = c⁻¹ * (z * z) * c := by rw [hy]; group
      _ = 1 := by rw [hzz]; group
  have hy1 : y ≠ 1 := by
    intro h1
    apply hz1
    calc z = c * y * c⁻¹ := by rw [hy]; group
      _ = 1 := by rw [h1]; group
  have huv1 : uA * vA ≠ 1 := fun h1 => uv_not_mem_QP45 (h1 ▸ Subgroup.one_mem _)
  have hyz : y ≠ z := by
    intro h1
    have hcz : c * z = z * c := by
      calc c * z = c * y := by rw [h1]
        _ = z * c := by rw [hy]; group
    have haz' : a = z := by
      rw [← hca, hcz]
      group
    have haJ : a ∈ J z := by
      rw [haz']
      exact z_mem_J_A h
    have hq1 : qH D ⟨a, haH⟩ = 1 := (J_mem_iff D _).mp (Subgroup.mem_subgroupOf.mpr haJ)
    obtain ⟨g', hg'⟩ := isConj_iff.mp hq
    rw [hq1, mul_one, mul_inv_cancel] at hg'
    exact huv1 hg'.symm
  obtain ⟨g, hg⟩ := isConj_iff.mp hq
  obtain ⟨r, hrH, hra, -, hrord⟩ := exists_centralizer_lift_uv_A h D hIII haH haa hg
    uvFive_commute (by rw [orderOf_uvFive]; exact ⟨2, rfl⟩) (by rw [orderOf_uvFive]; norm_num)
  rw [orderOf_uvFive] at hrord
  have hrz : r * z = z * r := mem_centralizer_singleton_iff.mp hrH
  set f : G := c⁻¹ * r * c with hf
  have hfH : f ∈ H z := by
    rw [H, mem_centralizer_singleton_iff]
    calc f * z = c⁻¹ * (r * (c * z * c⁻¹)) * c := by rw [hf]; group
      _ = c⁻¹ * ((c * z * c⁻¹) * r) * c := by rw [hca, hra]
      _ = z * f := by rw [hf]; group
  have hfy : f * y = y * f := by
    calc f * y = c⁻¹ * (r * z) * c := by rw [hf, hy]; group
      _ = c⁻¹ * (z * r) * c := by rw [hrz]
      _ = y * f := by rw [hf, hy]; group
  have hford : orderOf f = 5 := by
    rw [← hrord]
    exact (SemiconjBy.orderOf_eq c⁻¹ (x := r) (y := f) (by unfold SemiconjBy; rw [hf]; group)).symm
  by_cases hyJ : y ∈ J z
  ·
    refine hF1 y hyJ (orderOf_eq_prime (by rw [sq]; exact hyy) hy1) ?_
      (isConj_iff.mpr ⟨c⁻¹, by rw [hy, inv_inv]⟩)
    intro hyz'
    rcases (Subgroup.mem_zpowers_iff_of_orderOf_eq_two hz2).mp hyz' with h1 | h1
    · exact hy1 h1
    · exact hyz h1
  ·
    have hq1 : qH D ⟨y, hyH⟩ ≠ 1 := fun h1 =>
      hyJ (Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr h1))
    have hqy2 : orderOf (qH D ⟨y, hyH⟩) = 2 := by
      refine orderOf_eq_prime ?_ hq1
      rw [sq, ← map_mul]
      have e : (⟨y, hyH⟩ : ↥(H z)) * ⟨y, hyH⟩ = 1 := Subtype.ext hyy
      rw [e, map_one]
    have hqf : orderOf (qH D ⟨f, hfH⟩) = 5 := by
      have hdvd : orderOf (qH D ⟨f, hfH⟩) ∣ 5 := by
        rw [← hford, ← Subgroup.orderOf_mk f hfH]
        exact orderOf_map_dvd _ _
      rcases (Nat.dvd_prime (by norm_num)).mp hdvd with h1 | h5
      · exfalso
        have hfJ : f ∈ J z :=
          Subgroup.mem_subgroupOf.mp ((J_mem_iff D _).mpr (orderOf_eq_one_iff.mp h1))
        obtain ⟨k, hk⟩ := IsPGroup.iff_orderOf.mp (isPGroup_J_A h) ⟨f, hfJ⟩
        rw [Subgroup.orderOf_mk, hford] at hk
        have h2 : 2 ∣ 5 := by
          have hk0 : k ≠ 0 := by
            rintro rfl
            norm_num at hk
          rw [hk]
          exact dvd_pow_self 2 hk0
        norm_num at h2
      · exact h5
    have hcomm' : qH D ⟨f, hfH⟩ * qH D ⟨y, hyH⟩ = qH D ⟨y, hyH⟩ * qH D ⟨f, hfH⟩ := by
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext hfy
    have h5 : 5 ∣ Nat.card (centralizer ({qH D ⟨y, hyH⟩} : Set A45)) := by
      have hmem : qH D ⟨f, hfH⟩ ∈ centralizer ({qH D ⟨y, hyH⟩} : Set A45) :=
        mem_centralizer_singleton_iff.mpr hcomm'
      rw [← hqf, ← Subgroup.orderOf_mk _ hmem]
      exact orderOf_dvd_natCard _
    obtain ⟨hC1, hC2, hC3, -⟩ := qa45_involution_centralizers
    have hyuv : IsConj (qH D ⟨y, hyH⟩) (uA * vA) := by
      rcases qa45_involution_classes _ hqy2 with ht | hut | hv | huv
      · rw [card_centralizer_eq_of_isConj ht, hC1] at h5
        norm_num at h5
      · rw [card_centralizer_eq_of_isConj hut, hC2] at h5
        norm_num at h5
      · rw [card_centralizer_eq_of_isConj hv, hC3] at h5
        norm_num at h5
      · exact huv
    have hLF := z_mem_commutator_centralizer_of_uv_A h D hIII hyH hyy hyuv
    have hpart := CFSG.GroupTheory.mul_mul_inv_mem_commutator_centralizer_of_mem (z := z) (g := c)
      hLF
    rw [hca] at hpart
    exact not_mem_commutator_of_qH_not_mem_QP45 D haH
      (not_mem_QP45_of_isConj hq uv_not_mem_QP45) hpart

theorem exists_index_two_inf_eq_commutator_A_of_uv_involution_of_F1
    (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    (hF1 : ∀ j ∈ J z, orderOf j = 2 → j ∉ zpowers z → ¬ IsConj z j)
    {x : G} (hxH : x ∈ H z) (hxx : x * x = 1) (hxq : IsConj (qH D ⟨x, hxH⟩) (uA * vA)) :
    ∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ z ∈ G₀ ∧ H z ⊓ G₀ = ⁅H z, H z⁆ :=
  exists_index_two_inf_eq_commutator_A_of_uv_involution h D hIII hF1
    (not_isConj_z_of_uv_A h D hIII hF1) hxH hxx hxq

theorem exists_index_two_inf_eq_commutator_A_of_F1
    (h : Tim79a.ParrottHypA z)
    (D : QuotientData (z := z) (J_subgroupOf_normal z))
    (hIII : ¬ ∃ σ₂ : ↥(H z), orderOf σ₂ = 3 ∧
      qH D σ₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup) ∧
      centralizerJ (sigma1Nine D) = centralizerJ σ₂)
    (hF1 : ∀ j ∈ J z, orderOf j = 2 → j ∉ zpowers z → ¬ IsConj z j)
    (hv : (∀ (a : G) (ha : a ∈ H z), IsConj (qH D ⟨a, ha⟩) (uA * vA) → a * a ≠ 1) →
      ∀ (a : G) (ha : a ∈ H z), a * a = 1 → IsConj (qH D ⟨a, ha⟩) vA → ¬ IsConj z a) :
    ∃ G₀ : Subgroup G, G₀.Normal ∧ G₀.index = 2 ∧ z ∈ G₀ ∧ H z ⊓ G₀ = ⁅H z, H z⁆ := by
  by_cases hA : ∃ (x : G) (hxH : x ∈ H z), x * x = 1 ∧ IsConj (qH D ⟨x, hxH⟩) (uA * vA)
  · obtain ⟨x, hxH, hxx, hxq⟩ := hA
    exact exists_index_two_inf_eq_commutator_A_of_uv_involution_of_F1 h D hIII hF1 hxH hxx hxq
  · have hnouv : ∀ (a : G) (ha : a ∈ H z), IsConj (qH D ⟨a, ha⟩) (uA * vA) → a * a ≠ 1 :=
      fun a ha hq haa => hA ⟨a, ha, haa, hq⟩
    exact exists_index_two_inf_eq_commutator_A_of_no_uv_involution h D hIII hF1 hnouv (hv hnouv)

end CFSG.RankThree.GF2n.Parrott

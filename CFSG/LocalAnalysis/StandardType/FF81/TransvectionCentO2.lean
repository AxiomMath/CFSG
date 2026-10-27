module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup
public import Mathlib.GroupTheory.PGroup
import CFSG.LocalAnalysis.StandardType.FF81.TransvectionAut
import Mathlib.GroupTheory.Subgroup.Centralizer

public section

namespace CFSG.StandardType.FF81

open Matrix

private noncomputable def o2c_conjAut {G : Type*} [Group G] {L : Subgroup G} {m : ℕ}
    (e : ↥L ≃* SpecialLinearGroup (Fin m) (ZMod 2)) {p : G}
    (hp : p ∈ Subgroup.normalizer (L : Set G)) :
    MulAut (SpecialLinearGroup (Fin m) (ZMod 2)) :=
  MulAut.congr e (L.normalizerMonoidHom ⟨p, hp⟩)

private theorem o2c_conjAut_apply {G : Type*} [Group G] {L : Subgroup G} {m : ℕ}
    {e : ↥L ≃* SpecialLinearGroup (Fin m) (ZMod 2)} {p : G}
    (hp : p ∈ Subgroup.normalizer (L : Set G)) (x : ↥L) :
    o2c_conjAut e hp (e x) = e (L.normalizerMonoidHom ⟨p, hp⟩ x) := by
  rw [o2c_conjAut, MulAut.congr_apply]
  simp

private theorem o2c_conjAut_fix {G : Type*} [Group G] {L P : Subgroup G} {s : G} {m : ℕ}
    (e : ↥L ≃* SpecialLinearGroup (Fin m) (ZMod 2)) (hs : s ∈ L)
    (hPs : P ≤ Subgroup.centralizer ({s} : Set G)) {p : G} (hpP : p ∈ P)
    (hpN : p ∈ Subgroup.normalizer (L : Set G)) :
    o2c_conjAut e hpN (e ⟨s, hs⟩) = e ⟨s, hs⟩ := by
  rw [o2c_conjAut_apply]
  congr 1
  apply Subtype.ext
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hps : p * s = s * p := Subgroup.mem_centralizer_singleton_iff.mp (hPs hpP)
  rw [hps, mul_inv_cancel_right]

private theorem o2c_centralizer_le_normalizer_map {G : Type*} [Group G]
    {L P : Subgroup G} {s : G} {m : ℕ}
    (e : ↥L ≃* SpecialLinearGroup (Fin m) (ZMod 2)) (hs : s ∈ L)
    (hPs : P ≤ Subgroup.centralizer ({s} : Set G))
    (hnor : L ⊓ Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer (P : Set G)) :
    Subgroup.centralizer ({e ⟨s, hs⟩} : Set (SpecialLinearGroup (Fin m) (ZMod 2))) ≤
      Subgroup.normalizer ((P.subgroupOf L).map e.toMonoidHom :
        Set (SpecialLinearGroup (Fin m) (ZMod 2))) := by
  rw [Subgroup.le_normalizer_iff]
  intro k hk y hy
  obtain ⟨c, rfl⟩ := e.surjective k
  have hkc : (c : G) ∈ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c * ⟨s, hs⟩ = ⟨s, hs⟩ * c := by
      apply e.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hk
    exact congrArg Subtype.val h1
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
  have hcz : (c : G) * (z : G) * (c : G)⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hnor ⟨c.2, hkc⟩) (z : G)).mp hz
  have himg : e c * e z * (e c)⁻¹ = e (c * z * c⁻¹) := by
    simp only [map_mul, map_inv]
  change e c * e z * (e c)⁻¹ ∈ (P.subgroupOf L).map e.toMonoidHom
  rw [himg]
  exact Subgroup.mem_map_of_mem e.toMonoidHom
    (Subgroup.mem_subgroupOf.mpr (by simpa using hcz))

private theorem o2c_conjAut_mul_inv_mem {G : Type*} [Group G] {L P : Subgroup G} {s : G}
    {m : ℕ} (e : ↥L ≃* SpecialLinearGroup (Fin m) (ZMod 2)) (hs : s ∈ L)
    (hPs : P ≤ Subgroup.centralizer ({s} : Set G))
    (hnor : L ⊓ Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer (P : Set G)) {p : G} (hpP : p ∈ P)
    (hpN : p ∈ Subgroup.normalizer (L : Set G))
    {k : SpecialLinearGroup (Fin m) (ZMod 2)}
    (hk : k ∈ Subgroup.centralizer ({e ⟨s, hs⟩} :
      Set (SpecialLinearGroup (Fin m) (ZMod 2)))) :
    o2c_conjAut e hpN k * k⁻¹ ∈ (P.subgroupOf L).map e.toMonoidHom := by
  obtain ⟨c, rfl⟩ := e.surjective k
  have hkc : (c : G) ∈ Subgroup.centralizer ({s} : Set G) := by
    rw [Subgroup.mem_centralizer_singleton_iff]
    have h1 : c * ⟨s, hs⟩ = ⟨s, hs⟩ * c := by
      apply e.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_centralizer_singleton_iff.mp hk
    exact congrArg Subtype.val h1
  have hcp : (c : G) * p * (c : G)⁻¹ ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hnor ⟨c.2, hkc⟩) p).mp hpP
  have hmemP : p * (c : G) * p⁻¹ * (c : G)⁻¹ ∈ P := by
    simpa only [mul_inv_rev, inv_inv, mul_assoc] using P.mul_mem hpP (P.inv_mem hcp)
  have hmem : L.normalizerMonoidHom ⟨p, hpN⟩ c * c⁻¹ ∈ P.subgroupOf L := by
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv,
      Subgroup.normalizerMonoidHom_apply_apply_coe]
    exact hmemP
  have himg : o2c_conjAut e hpN (e c) * (e c)⁻¹ =
      e (L.normalizerMonoidHom ⟨p, hpN⟩ c * c⁻¹) := by
    rw [o2c_conjAut_apply, map_mul, map_inv]
  rw [himg]
  exact Subgroup.mem_map_of_mem e.toMonoidHom hmem

private theorem o2c_mem_centralizer_of_conj {G : Type*} [Group G] {L : Subgroup G} {p l : G}
    (hlconj : ∀ x ∈ L, p * x * p⁻¹ = l * x * l⁻¹) :
    l⁻¹ * p ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have h := hlconj y hy
  have hy' : p * y = l * y * l⁻¹ * p := by
    calc p * y = (p * y * p⁻¹) * p := by group
      _ = (l * y * l⁻¹) * p := by rw [h]
  exact (show l⁻¹ * p * y = y * (l⁻¹ * p) by
    calc l⁻¹ * p * y = l⁻¹ * (p * y) := by group
      _ = l⁻¹ * (l * y * l⁻¹ * p) := by rw [hy']
      _ = y * (l⁻¹ * p) := by group).symm

private theorem o2c_exists_conj_four {G : Type*} [Group G] {L P : Subgroup G} {s : G}
    {m : ℕ} (hm : 5 ≤ m) (e : ↥L ≃* SpecialLinearGroup (Fin m) (ZMod 2)) (hs : s ∈ L)
    (hes : ∃ (i j : Fin m) (hij : i ≠ j),
      e ⟨s, hs⟩ = SpecialLinearGroup.transvection hij 1)
    (hP : IsPGroup 2 P) (hPs : P ≤ Subgroup.centralizer ({s} : Set G))
    (hnor : L ⊓ Subgroup.centralizer ({s} : Set G) ≤
      Subgroup.normalizer (P : Set G)) {p : G} (hpP : p ∈ P)
    (hpN : p ∈ Subgroup.normalizer (L : Set G)) :
    ∃ l : G, l ∈ L ∧ l ^ 4 = 1 ∧ ∀ x ∈ L, p * x * p⁻¹ = l * x * l⁻¹ := by
  classical
  obtain ⟨i, j, hij, heq⟩ := hes
  let τ : SpecialLinearGroup (Fin m) (ZMod 2) := e ⟨s, hs⟩
  let α : MulAut (SpecialLinearGroup (Fin m) (ZMod 2)) := o2c_conjAut e hpN
  let N : Subgroup (SpecialLinearGroup (Fin m) (ZMod 2)) :=
    (P.subgroupOf L).map e.toMonoidHom
  have hN : IsPGroup 2 N := by
    have hsub : IsPGroup 2 (P.subgroupOf L) :=
      hP.comap_of_injective L.subtype L.subtype_injective
    exact hsub.map e.toMonoidHom
  have hNC : N ≤ Subgroup.centralizer ({τ} :
      Set (SpecialLinearGroup (Fin m) (ZMod 2))) := by
    intro x hx
    obtain ⟨y, hy, rfl⟩ := Subgroup.mem_map.mp hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    change e y * e ⟨s, hs⟩ = e ⟨s, hs⟩ * e y
    have hyc : y * ⟨s, hs⟩ = ⟨s, hs⟩ * y :=
      Subtype.ext (Subgroup.mem_centralizer_singleton_iff.mp (hPs hy))
    calc e y * e ⟨s, hs⟩ = e (y * ⟨s, hs⟩) := (map_mul e y ⟨s, hs⟩).symm
      _ = e (⟨s, hs⟩ * y) := by rw [hyc]
      _ = e ⟨s, hs⟩ * e y := map_mul e ⟨s, hs⟩ y
  have hCN : Subgroup.centralizer ({τ} :
      Set (SpecialLinearGroup (Fin m) (ZMod 2))) ≤ Subgroup.normalizer (N :
        Set (SpecialLinearGroup (Fin m) (ZMod 2))) := by
    have h := o2c_centralizer_le_normalizer_map (L := L) (P := P) (s := s) e hs hPs hnor
    simpa [τ, N] using h
  have hfix : α τ = τ := by
    simpa [α, τ] using o2c_conjAut_fix (L := L) (P := P) (s := s) e hs hPs hpP hpN
  have hmod : ∀ k ∈ Subgroup.centralizer ({τ} :
      Set (SpecialLinearGroup (Fin m) (ZMod 2))), α k * k⁻¹ ∈ N := by
    intro k hk
    simpa [α, N, τ] using
      o2c_conjAut_mul_inv_mem (L := L) (P := P) (s := s) e hs hPs hnor hpP hpN hk
  obtain ⟨c₀, hc₀pow, hc₀conj⟩ :=
    exists_conj_of_map_transvection_eq hm hij (by simpa [τ] using heq) α N hN hNC hCN hfix hmod
  refine ⟨e.symm c₀, (e.symm c₀).2, ?_, ?_⟩
  · have h : (e.symm c₀ : ↥L) ^ 4 = 1 := by
      simpa using congrArg e.symm hc₀pow
    simpa using congrArg Subtype.val h
  · intro x hx
    have h := hc₀conj (e ⟨x, hx⟩)
    dsimp only [α] at h
    rw [o2c_conjAut_apply] at h
    have h2 := congrArg e.symm h
    simp only [MulEquiv.symm_apply_apply, map_mul, map_inv] at h2
    have h3 := congrArg Subtype.val h2
    simpa [Subgroup.normalizerMonoidHom_apply_apply_coe] using h3

theorem le_of_isPGroup_of_le_centralizer_transvection {G : Type*} [Group G]
    {L M P : Subgroup G} {s : G} {m : ℕ} (hm : 5 ≤ m)
    (e : ↥L ≃* SpecialLinearGroup (Fin m) (ZMod 2)) (hs : s ∈ L)
    (hes : ∃ (i j : Fin m) (hij : i ≠ j), e ⟨s, hs⟩ = SpecialLinearGroup.transvection hij 1)
    (hLM : L ≤ M) (hMN : M ≤ Subgroup.normalizer (L : Set G))
    (hodd : Odd (Nat.card ↥(M ⊓ Subgroup.centralizer (L : Set G))))
    (hP : IsPGroup 2 P) (hPM : P ≤ M) (hPs : P ≤ Subgroup.centralizer ({s} : Set G))
    (hnor : L ⊓ Subgroup.centralizer ({s} : Set G) ≤ Subgroup.normalizer (P : Set G)) :
    P ≤ L := by
  intro p hpP
  have hpN : p ∈ Subgroup.normalizer (L : Set G) := hMN (hPM hpP)
  obtain ⟨l, hlL, hl4, hlconj⟩ :=
    o2c_exists_conj_four hm e hs hes hP hPs hnor hpP hpN
  have hpl : p * l = l * p := by
    have h := hlconj l hlL
    have h' : p * l * p⁻¹ = l := by simpa using h
    calc p * l = (p * l * p⁻¹) * p := by group
      _ = l * p := by rw [h']
  have hxM : l⁻¹ * p ∈ M := M.mul_mem (hLM (L.inv_mem hlL)) (hPM hpP)
  have hxC := o2c_mem_centralizer_of_conj hlconj
  have hx : l⁻¹ * p ∈ M ⊓ Subgroup.centralizer (L : Set G) := ⟨hxM, hxC⟩
  obtain ⟨a, ha⟩ := IsPGroup.iff_orderOf.mp hP ⟨p, hpP⟩
  rw [Subgroup.orderOf_mk] at ha
  have hlpow : l ^ 2 ^ max a 2 = 1 := by
    obtain ⟨t, ht⟩ := Nat.pow_dvd_pow 2 (le_max_right a 2)
    rw [ht, pow_mul, hl4, one_pow]
  have hppow : p ^ 2 ^ max a 2 = 1 := by
    have hp0 : p ^ 2 ^ a = 1 := by
      rw [← ha]
      exact pow_orderOf_eq_one p
    obtain ⟨t, ht⟩ := Nat.pow_dvd_pow 2 (le_max_left a 2)
    rw [ht, pow_mul, hp0, one_pow]
  have hcomm : Commute l p := hpl.symm
  have hxpow : (l⁻¹ * p) ^ 2 ^ max a 2 = 1 := by
    rw [hcomm.inv_left.mul_pow, inv_pow, hlpow, inv_one, hppow, one_mul]
  have hdvd : orderOf (l⁻¹ * p) ∣ 2 ^ max a 2 := orderOf_dvd_of_pow_eq_one hxpow
  have hdvdM : orderOf (l⁻¹ * p) ∣
      Nat.card ↥(M ⊓ Subgroup.centralizer (L : Set G)) :=
    Subgroup.orderOf_dvd_natCard _ hx
  have hoddx : Odd (orderOf (l⁻¹ * p)) := Odd.of_dvd_nat hodd hdvdM
  have hcop : Nat.Coprime (orderOf (l⁻¹ * p)) (2 ^ max a 2) :=
    (Nat.coprime_two_right.mpr hoddx).pow_right (max a 2)
  have hx1 : l⁻¹ * p = 1 :=
    orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes hcop (dvd_refl _) hdvd)
  have hp_eq : p = l := by
    calc p = l * (l⁻¹ * p) := by group
      _ = l := by rw [hx1, mul_one]
  rw [hp_eq]
  exact hlL

end CFSG.StandardType.FF81

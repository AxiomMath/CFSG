module

public import CFSG.LinearAlgebra.LinearGroups.TameProjectiveSubgroups
import CFSG.Quasithin.EmptyFaithful.GoldschmidtH23P4Mul
import CFSG.Quasithin.Vol2.Ch3Sec3L2qFacts

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open Subgroup
open scoped MatrixGroups Pointwise

private theorem uc22s2112r34_pgl_dihedral_rot {J : Type*} [Group J] {z : ℕ}
    (e : J ≃* DihedralGroup z) {y : J} (hy : Odd (orderOf y)) :
    ∃ i, e y = DihedralGroup.r i := by
  rcases h : e y with i | i
  · exact ⟨i, rfl⟩
  · exfalso
    have h2 : orderOf y = 2 := by
      rw [← MulEquiv.orderOf_eq e, h, DihedralGroup.orderOf_sr]
    rw [h2] at hy
    exact (by decide : ¬ Odd 2) hy

theorem uc22s2112r34_dihedral_inv_or_comm {J : Type*} [Group J] {z : ℕ}
    (e : J ≃* DihedralGroup z) (g : J) :
    (∀ y : J, Odd (orderOf y) → g * y * g⁻¹ = y⁻¹) ∨
      ∀ y : J, Odd (orderOf y) → g * y * g⁻¹ = y := by
  rcases h : e g with i | i
  · right
    intro y hy
    obtain ⟨j, hj⟩ := uc22s2112r34_pgl_dihedral_rot e hy
    apply e.injective
    simp only [map_mul, map_inv, h, hj, DihedralGroup.inv_r]
    rw [DihedralGroup.r_mul_r, DihedralGroup.r_mul_r]
    congr 1
    abel
  · left
    intro y hy
    obtain ⟨j, hj⟩ := uc22s2112r34_pgl_dihedral_rot e hy
    apply e.injective
    simp only [map_mul, map_inv, h, hj, DihedralGroup.inv_sr, DihedralGroup.inv_r]
    rw [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    congr 1
    abel

theorem uc22s2112r34_dihedral_exists_inv {J : Type*} [Group J] [Finite J] {z : ℕ}
    (e : J ≃* DihedralGroup z) {H : Subgroup J} (hH : ¬ IsCyclic H) :
    ∃ h ∈ H, ∀ y : J, Odd (orderOf y) → h * y * h⁻¹ = y⁻¹ := by
  have hz : z ≠ 0 := by
    rintro rfl
    have hcard : Nat.card J = Nat.card (DihedralGroup 0) := Nat.card_congr e.toEquiv
    rw [DihedralGroup.nat_card] at hcard
    have hpos : 0 < Nat.card J := Nat.card_pos
    omega
  have : NeZero z := ⟨hz⟩
  have hmap_nc : ¬ IsCyclic (H.map e.toMonoidHom) := by
    intro hc
    exact hH ((MulEquiv.isCyclic (e.subgroupMap H)).mpr hc)
  obtain ⟨j, hj⟩ := CFSG.Quasithin.H13.L2q.exists_sr_mem (z := z) hmap_nc
  refine ⟨e.symm (DihedralGroup.sr j), ?_, ?_⟩
  · exact (Subgroup.mem_map_equiv (f := e) (K := H)).mp hj
  · intro y hy
    obtain ⟨i, hi⟩ := uc22s2112r34_pgl_dihedral_rot e hy
    apply e.injective
    simp only [map_mul, map_inv, e.apply_symm_apply, hi, DihedralGroup.inv_sr,
      DihedralGroup.inv_r]
    rw [DihedralGroup.sr_mul_r, DihedralGroup.sr_mul_sr]
    congr 1
    abel

theorem uc22s2112r34_perm_four_exists_inv (y : Equiv.Perm (Fin 4)) (hy : y ^ 3 = 1) :
    ∃ σ : Equiv.Perm (Fin 4), σ * y * σ⁻¹ = y⁻¹ := by
  revert y
  decide +kernel


theorem uc22s2112r34_pgl_tame_cases_iso {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Finite k]
    [CharP k p] (J : Subgroup PGL(Fin 2, k)) (hJ : ¬ p ∣ Nat.card J) :
    IsCyclic J ∨ (∃ z : ℕ, Nonempty (J ≃* DihedralGroup z)) ∨
      Nonempty (J ≃* alternatingGroup (Fin 4)) ∨ Nonempty (J ≃* Equiv.Perm (Fin 4)) ∨
        Nonempty (J ≃* alternatingGroup (Fin 5)) := by
  have := Fintype.ofFinite k
  let E := FiniteField.Extension k p 2
  have := Fintype.ofFinite E
  have hEcard : Nat.card E = Nat.card k ^ 2 := FiniteField.natCard_extension k p 2
  obtain ⟨f, -, hkcard⟩ := FiniteField.card k p
  have hEp : Nat.card E = p ^ (2 * (f : ℕ)) := by
    rw [hEcard, Nat.card_eq_fintype_card, hkcard, ← pow_mul, mul_comm]
  have hsq : ∀ x : k, IsSquare (algebraMap k E x) :=
    CFSG.LinearGroups.isSquare_algebraMap_of_card_eq_sq (by
      rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, hEcard])
  set ι := Matrix.ProjectiveSpecialLinearGroup.toPGL (n := Fin 2) (R := E)
  set J₁ := J.map (CFSG.LinearGroups.pglExtend k E)
  have hJ₁ : J₁ ≤ ι.range := by
    rintro _ ⟨x, -, rfl⟩
    exact CFSG.LinearGroups.pglExtend_mem_range_toPGL hsq x
  set H : Subgroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) E) := J₁.comap ι
  have hmap : H.map ι = J₁ := Subgroup.map_comap_eq_self hJ₁
  let eH : H ≃* J :=
    ((H.equivMapOfInjective ι Matrix.ProjectiveSpecialLinearGroup.toPGL_injective).trans
      (MulEquiv.subgroupCongr hmap)).trans
      (J.equivMapOfInjective (CFSG.LinearGroups.pglExtend k E)
        CFSG.LinearGroups.pglExtend_injective).symm
  have hcard : Nat.card H = Nat.card J := Nat.card_congr eH.toEquiv
  have hHp : ¬ p ∣ Nat.card H := hcard ▸ hJ
  rcases CFSG.Glauberman.Dickson.huppert_II_8_24_dickson_case_no_p_part hEp H hHp with
    ⟨z, -, -, hcyc⟩ | ⟨z, -, -, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩ | ⟨-, ⟨e⟩⟩
  · exact Or.inl (isCyclic_of_surjective eH.toMonoidHom eH.surjective)
  · exact Or.inr (Or.inl ⟨z, ⟨eH.symm.trans e⟩⟩)
  · exact Or.inr (Or.inr (Or.inl ⟨eH.symm.trans e⟩))
  · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨eH.symm.trans e⟩)))
  · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨eH.symm.trans e⟩)))

private theorem uc22s2112r34_pgl_conj_inv_of_mul {X : Type*} [Group X] {Y : Subgroup X}
    (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a) {y σ s a : X} (haY : a ∈ Y)
    (hσ : σ = s * a) (hinv : σ * y * σ⁻¹ = y⁻¹) (hyY : y ∈ Y) :
    s * y * s⁻¹ = y⁻¹ := by
  have hcomm : a * y = y * a := hYc a haY y hyY
  calc
    s * y * s⁻¹ = s * (a * y * a⁻¹) * s⁻¹ := by rw [hcomm]; group
    _ = (s * a) * y * (s * a)⁻¹ := by group
    _ = σ * y * σ⁻¹ := by rw [hσ]
    _ = y⁻¹ := hinv

private theorem uc22s2112r34_pgl_inv_of_gen {X : Type*} [Group X] {Y : Subgroup X}
    {y₀ s : X} (hgen : ∀ y ∈ Y, ∃ n : ℤ, y₀ ^ n = y)
    (hs0 : s * y₀ * s⁻¹ = y₀⁻¹) :
    ∀ y ∈ Y, s * y * s⁻¹ = y⁻¹ := by
  intro y hy
  obtain ⟨n, rfl⟩ := hgen y hy
  calc
    s * y₀ ^ n * s⁻¹ = (s * y₀ * s⁻¹) ^ n := by rw [conj_zpow]
    _ = (y₀⁻¹) ^ n := by rw [hs0]
    _ = (y₀ ^ n)⁻¹ := by rw [inv_zpow]

theorem uc22s2112r34_pgl_exists_inv {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Finite k]
    [CharP k p] {Y S : Subgroup PGL(Fin 2, k)} (hYc : ∀ a ∈ Y, ∀ b ∈ Y, a * b = b * a)
    (hYo : Odd (Nat.card Y)) (hS : IsPGroup 2 S) (hSc : ¬ IsCyclic S) (hS8 : 8 ≤ Nat.card S)
    (hYS : (Y : Set PGL(Fin 2, k)) * (S : Set PGL(Fin 2, k)) =
      (S : Set PGL(Fin 2, k)) * (Y : Set PGL(Fin 2, k)))
    (hp : ¬ p ∣ Nat.card (Y ⊔ S : Subgroup PGL(Fin 2, k))) :
    ∃ s ∈ S, ∀ y ∈ Y, s * y * s⁻¹ = y⁻¹ := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : Finite (GL (Fin 2) k) := Finite.of_fintype _
  have : Finite (PGL(Fin 2, k)) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let J : Subgroup PGL(Fin 2, k) := Y ⊔ S
  have hJp : ¬ p ∣ Nat.card J := hp
  have hJcoe : (J : Set PGL(Fin 2, k)) =
      (Y : Set PGL(Fin 2, k)) * (S : Set PGL(Fin 2, k)) :=
    CFSG.Quasithin.H23P4.coe_sup_eq_mul_of_mul_comm hYS
  rcases uc22s2112r34_pgl_tame_cases_iso J hJp with
    hcyc | hdih | hA4 | hS4 | hA5
  · exfalso
    let : IsCyclic J := hcyc
    exact hSc (Subgroup.isCyclic_of_le (H := S) (H' := J) le_sup_right)
  · obtain ⟨z, ⟨e⟩⟩ := hdih
    have hSsub_nc : ¬ IsCyclic (S.subgroupOf J) := by
      intro h
      exact hSc ((MulEquiv.isCyclic
        (Subgroup.subgroupOfEquivOfLe (le_sup_right : S ≤ J))).mp h)
    obtain ⟨h, hhH, hinv⟩ := uc22s2112r34_dihedral_exists_inv e hSsub_nc
    refine ⟨(h : PGL(Fin 2, k)), ?_, ?_⟩
    · simpa using Subgroup.mem_subgroupOf.mp hhH
    · intro y hy
      have hodd : Odd (orderOf (⟨y, Subgroup.mem_sup_left hy⟩ : J)) := by
        rw [Subgroup.orderOf_mk]
        exact Odd.of_dvd_nat hYo (Subgroup.orderOf_dvd_natCard Y hy)
      have hh := hinv ⟨y, Subgroup.mem_sup_left hy⟩ hodd
      simpa using congrArg (fun z : J => (z : PGL(Fin 2, k))) hh
  · obtain ⟨eA4⟩ := hA4
    exfalso
    have hcardJ : Nat.card J = 12 := by
      rw [Nat.card_congr eA4.toEquiv]
      exact alternatingGroup.card_of_card_eq_four (by simp)
    have hSdvd : Nat.card S ∣ 12 := by
      rw [← hcardJ]
      exact Subgroup.card_dvd_of_le le_sup_right
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    have hdvd4 : 2 ^ k ∣ 4 := by
      have hcop : Nat.Coprime (2 ^ k) 3 := (by decide : Nat.Coprime 2 3).pow_left k
      refine hcop.dvd_mul_right.mp ?_
      rw [hk] at hSdvd
      simpa [show (12 : ℕ) = 4 * 3 by norm_num] using hSdvd
    have hk2 : k ≤ 2 :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < (2 : ℕ))).mp (by simpa using hdvd4)
    have hSle : Nat.card S ≤ 4 := by
      rw [hk]
      calc
        2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 4 := by norm_num
    omega
  · obtain ⟨eS4⟩ := hS4
    have hcardJ : Nat.card J = 24 := by
      rw [Nat.card_congr eS4.toEquiv, Nat.card_perm, Nat.card_fin]
      norm_num
    have hYdvd24 : Nat.card Y ∣ 24 := by
      rw [← hcardJ]
      exact Subgroup.card_dvd_of_le le_sup_left
    have hYdvd3 : Nat.card Y ∣ 3 := by
      have hcop : Nat.Coprime (Nat.card Y) 8 := by
        have h2 : Nat.Coprime (Nat.card Y) 2 := hYo.coprime_two_right
        simpa using h2.pow_right 3
      exact (hcop.dvd_mul_left).mp (by
        simpa [show (24 : ℕ) = 8 * 3 by norm_num] using hYdvd24)
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hYcyc : IsCyclic Y := isCyclic_of_card_dvd_prime (p := 3) hYdvd3
    obtain ⟨y₀, hy₀⟩ := (Subgroup.isCyclic_iff_exists_zpowers_eq_top Y).mp hYcyc
    have hy₀Y : y₀ ∈ Y := by
      rw [← hy₀]
      exact Subgroup.mem_zpowers y₀
    let y₀J : J := ⟨y₀, Subgroup.mem_sup_left hy₀Y⟩
    have hy03 : y₀J ^ 3 = 1 := by
      apply Subtype.ext
      have h3 : y₀ ^ 3 = 1 :=
        orderOf_dvd_iff_pow_eq_one.mp
          ((Subgroup.orderOf_dvd_natCard Y hy₀Y).trans hYdvd3)
      simpa [y₀J] using h3
    obtain ⟨τ, hτ⟩ := uc22s2112r34_perm_four_exists_inv (eS4 y₀J) (by
      rw [← map_pow, hy03, map_one])
    let σ : J := eS4.symm τ
    have hσ : σ * y₀J * σ⁻¹ = y₀J⁻¹ := by
      apply eS4.injective
      simpa [σ] using hτ
    have hσamb : (σ : PGL(Fin 2, k)) * (y₀ : PGL(Fin 2, k)) *
        (σ : PGL(Fin 2, k))⁻¹ = (y₀ : PGL(Fin 2, k))⁻¹ := by
      simpa using congrArg (fun z : J => (z : PGL(Fin 2, k))) hσ
    have hσJ : (σ : PGL(Fin 2, k)) ∈ (J : Set PGL(Fin 2, k)) := σ.2
    rw [hJcoe, hYS] at hσJ
    obtain ⟨s, hsS, a, haY, hsa⟩ := hσJ
    have hs0 : s * (y₀ : PGL(Fin 2, k)) * s⁻¹ = (y₀ : PGL(Fin 2, k))⁻¹ :=
      uc22s2112r34_pgl_conj_inv_of_mul hYc haY hsa.symm hσamb hy₀Y
    have hgen : ∀ y ∈ Y, ∃ n : ℤ, (y₀ : PGL(Fin 2, k)) ^ n = y := by
      intro y hy
      have hmem : ((⟨y, hy⟩ : Y) : PGL(Fin 2, k)) ∈ Subgroup.zpowers y₀ := by
        rw [hy₀]
        exact (⟨y, hy⟩ : Y).2
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
      exact ⟨n, by simpa using hn⟩
    exact ⟨s, hsS, uc22s2112r34_pgl_inv_of_gen hgen hs0⟩
  · obtain ⟨eA5⟩ := hA5
    exfalso
    have hcardJ : Nat.card J = 60 := by
      rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hSdvd : Nat.card S ∣ 60 := by
      rw [← hcardJ]
      exact Subgroup.card_dvd_of_le le_sup_right
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    have hdvd4 : 2 ^ k ∣ 4 := by
      have hcop : Nat.Coprime (2 ^ k) 15 := (by decide : Nat.Coprime 2 15).pow_left k
      refine hcop.dvd_mul_right.mp ?_
      rw [hk] at hSdvd
      simpa [show (60 : ℕ) = 4 * 15 by norm_num] using hSdvd
    have hk2 : k ≤ 2 :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < (2 : ℕ))).mp (by simpa using hdvd4)
    have hSle : Nat.card S ≤ 4 := by
      rw [hk]
      calc
        2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 4 := by norm_num
    omega

theorem uc22s2112r34_pgl_inv_or_comm {p : ℕ} [Fact p.Prime] {k : Type*} [Field k] [Finite k]
    [CharP k p] {Y S : Subgroup PGL(Fin 2, k)}
    (hYo : Odd (Nat.card Y)) (hS : IsPGroup 2 S) (hS8 : 8 ≤ Nat.card S)
    (hp : ¬ p ∣ Nat.card (Y ⊔ S : Subgroup PGL(Fin 2, k))) {r : ℕ} (hr : r.Prime) (hr5 : 5 ≤ r)
    (hrY : r ∣ Nat.card Y) {H : Subgroup PGL(Fin 2, k)} (hHS : H ≤ S) (hH : ¬ IsCyclic H) :
    (∃ h ∈ H, ∀ y ∈ Y, h * y * h⁻¹ = y⁻¹) ∧
      ∀ g ∈ S, (∀ y ∈ Y, g * y * g⁻¹ = y⁻¹) ∨ ∀ y ∈ Y, g * y * g⁻¹ = y := by
  classical
  have : Fintype k := Fintype.ofFinite k
  have : Finite (GL (Fin 2) k) := Finite.of_fintype _
  have : Finite (PGL(Fin 2, k)) :=
    Finite.of_surjective Matrix.ProjGenLinGroup.mk Matrix.ProjGenLinGroup.mk_surjective
  let J : Subgroup PGL(Fin 2, k) := Y ⊔ S
  have hJp : ¬ p ∣ Nat.card J := hp
  have hSc : ¬ IsCyclic S := by
    rintro hcycS
    let : IsCyclic S := hcycS
    exact hH (Subgroup.isCyclic_of_le hHS)
  have hodd_mem : ∀ (y : PGL(Fin 2, k)) (hy : y ∈ Y),
      Odd (orderOf (⟨y, Subgroup.mem_sup_left hy⟩ : J)) := by
    intro y hy
    rw [Subgroup.orderOf_mk]
    exact Odd.of_dvd_nat hYo (Subgroup.orderOf_dvd_natCard Y hy)
  rcases uc22s2112r34_pgl_tame_cases_iso J hJp with
    hcyc | hdih | hA4 | hS4 | hA5
  · exfalso
    let : IsCyclic J := hcyc
    exact hSc (Subgroup.isCyclic_of_le (H := S) (H' := J) le_sup_right)
  · obtain ⟨z, ⟨e⟩⟩ := hdih
    have hHleJ : H ≤ J := hHS.trans le_sup_right
    have hHsub_nc : ¬ IsCyclic (H.subgroupOf J) := by
      intro hcycH
      exact hH ((MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hHleJ)).mp hcycH)
    obtain ⟨h, hhH, hinv⟩ := uc22s2112r34_dihedral_exists_inv e hHsub_nc
    refine ⟨?_, ?_⟩
    · refine ⟨(h : PGL(Fin 2, k)), ?_, ?_⟩
      · simpa using Subgroup.mem_subgroupOf.mp hhH
      · intro y hy
        have hh := hinv ⟨y, Subgroup.mem_sup_left hy⟩ (hodd_mem y hy)
        simpa using congrArg (fun z : J => (z : PGL(Fin 2, k))) hh
    · intro g hg
      let gJ : J := ⟨g, Subgroup.mem_sup_right hg⟩
      rcases uc22s2112r34_dihedral_inv_or_comm e gJ with hinvY | hcenY
      · left
        intro y hy
        have hh := hinvY ⟨y, Subgroup.mem_sup_left hy⟩ (hodd_mem y hy)
        simpa [gJ] using congrArg (fun z : J => (z : PGL(Fin 2, k))) hh
      · right
        intro y hy
        have hh := hcenY ⟨y, Subgroup.mem_sup_left hy⟩ (hodd_mem y hy)
        simpa [gJ] using congrArg (fun z : J => (z : PGL(Fin 2, k))) hh
  · obtain ⟨eA4⟩ := hA4
    exfalso
    have hcardJ : Nat.card J = 12 := by
      rw [Nat.card_congr eA4.toEquiv]
      exact alternatingGroup.card_of_card_eq_four (by simp)
    have hrdvd : r ∣ 12 := by
      rw [← hcardJ]
      exact hrY.trans (Subgroup.card_dvd_of_le le_sup_left)
    have hrdvd' : r ∣ 4 * 3 := by
      simpa [show (12 : ℕ) = 4 * 3 by norm_num] using hrdvd
    rcases hr.dvd_mul.mp hrdvd' with h | h
    · have := Nat.le_of_dvd (by norm_num) h
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  · obtain ⟨eS4⟩ := hS4
    exfalso
    have hcardJ : Nat.card J = 24 := by
      rw [Nat.card_congr eS4.toEquiv, Nat.card_perm, Nat.card_fin]
      norm_num
    have hrdvd : r ∣ 24 := by
      rw [← hcardJ]
      exact hrY.trans (Subgroup.card_dvd_of_le le_sup_left)
    have hrdvd' : r ∣ 8 * 3 := by
      simpa [show (24 : ℕ) = 8 * 3 by norm_num] using hrdvd
    rcases hr.dvd_mul.mp hrdvd' with h | h
    · have h8 : r ∣ 2 ^ 3 := by
        simpa [show (8 : ℕ) = 2 ^ 3 by norm_num] using h
      have h2 : r ∣ 2 := hr.dvd_of_dvd_pow h8
      have := Nat.le_of_dvd (by norm_num) h2
      omega
    · have := Nat.le_of_dvd (by norm_num) h
      omega
  · obtain ⟨eA5⟩ := hA5
    exfalso
    have hcardJ : Nat.card J = 60 := by
      rw [Nat.card_congr eA5.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      norm_num
    have hSdvd : Nat.card S ∣ 60 := by
      rw [← hcardJ]
      exact Subgroup.card_dvd_of_le le_sup_right
    obtain ⟨k, hk⟩ := hS.exists_card_eq
    have hdvd4 : 2 ^ k ∣ 4 := by
      have hcop : Nat.Coprime (2 ^ k) 15 := (by decide : Nat.Coprime 2 15).pow_left k
      refine hcop.dvd_mul_right.mp ?_
      rw [hk] at hSdvd
      simpa [show (60 : ℕ) = 4 * 15 by norm_num] using hSdvd
    have hk2 : k ≤ 2 :=
      (Nat.pow_dvd_pow_iff_le_right (by norm_num : 1 < (2 : ℕ))).mp (by simpa using hdvd4)
    have hSle : Nat.card S ≤ 4 := by
      rw [hk]
      calc
        2 ^ k ≤ 2 ^ 2 := Nat.pow_le_pow_right (by norm_num) hk2
        _ = 4 := by norm_num
    omega

end CFSG.LocalAnalysis.UniquenessCase.UC22

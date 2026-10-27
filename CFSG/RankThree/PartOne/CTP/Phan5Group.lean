module

public import CFSG.RankThree.PartOne.S12.InputsCT
public import CFSG.RankThree.PartOne.Assembly

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne

section Cyclic

variable {G : Type*} [Group G]

theorem commute_of_cyclic_normalized (Y : Subgroup G) [IsCyclic Y] {y e : G} (hy : y ∈ Y)
    (hy5 : orderOf y = 5) (he : e ^ 5 = 1) (hnorm : ∀ x ∈ Y, e * x * e⁻¹ ∈ Y) :
    e * y = y * e := by
  let σ : Y →* Y :=
    ((MulAut.conj e).toMonoidHom.comp Y.subtype).codRestrict Y (fun x => hnorm x x.2)
  obtain ⟨m, hm⟩ := MonoidHom.map_cyclic σ
  have hy' : e * y * e⁻¹ = y ^ m := by
    have := congrArg Subtype.val (hm ⟨y, hy⟩)
    simpa [σ] using this
  have hit : ∀ j : ℕ, e ^ j * y * (e ^ j)⁻¹ = y ^ (m ^ j) := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      calc e ^ (j + 1) * y * (e ^ (j + 1))⁻¹
          = e * (e ^ j * y * (e ^ j)⁻¹) * e⁻¹ := by rw [pow_succ']; group
        _ = e * y ^ (m ^ j) * e⁻¹ := by rw [ih]
        _ = (e * y * e⁻¹) ^ (m ^ j) := by rw [conj_zpow]
        _ = y ^ (m ^ (j + 1)) := by rw [hy', ← zpow_mul, pow_succ']
  have h5 : y ^ (m ^ 5) = y := by
    have := hit 5
    rw [he] at this
    simpa using this.symm
  have hdvd : (5 : ℤ) ∣ m ^ 5 - 1 := by
    have h1 : y ^ (m ^ 5 - 1) = 1 := by rw [zpow_sub_one, h5, mul_inv_cancel]
    have := (orderOf_dvd_iff_zpow_eq_one (x := y) (i := m ^ 5 - 1)).mpr h1
    rwa [hy5] at this
  have hz : (m : ZMod 5) ^ 5 = 1 := by
    have h1 : (((m ^ 5 - 1 : ℤ)) : ZMod 5) = 0 := (ZMod.intCast_zmod_eq_zero_iff_dvd _ 5).mpr hdvd
    push_cast at h1
    exact sub_eq_zero.mp h1
  have hz1 : (m : ZMod 5) = 1 := by
    generalize (m : ZMod 5) = a at hz
    revert a
    decide
  have hdvd1 : (5 : ℤ) ∣ m - 1 := by
    have := (ZMod.intCast_eq_intCast_iff_dvd_sub 1 m 5).mp (by simpa using hz1.symm)
    simpa using this
  have hym : y ^ m = y := by
    have h1 : y ^ (m - 1) = 1 := by
      rw [← orderOf_dvd_iff_zpow_eq_one, hy5]
      exact hdvd1
    rw [zpow_sub_one, mul_inv_eq_one] at h1
    exact h1
  rw [hym] at hy'
  exact (mul_inv_eq_iff_eq_mul.mp hy')

end Cyclic

section Torus

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem mem_centralizer_sup {A A' : Subgroup G} {x : G}
    (h : x ∈ Subgroup.centralizer (A : Set G)) (h' : x ∈ Subgroup.centralizer (A' : Set G)) :
    x ∈ Subgroup.centralizer ((A ⊔ A' : Subgroup G) : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  have hle : A ⊔ A' ≤ Subgroup.centralizer {x} := by
    refine sup_le (fun u hu => ?_) (fun u hu => ?_)
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (Subgroup.mem_centralizer_iff.mp h u hu).symm
    · rw [Subgroup.mem_centralizer_iff]
      intro z hz
      rw [Set.mem_singleton_iff] at hz
      rw [hz]
      exact (Subgroup.mem_centralizer_iff.mp h' u hu).symm
  intro u hu
  exact (Subgroup.mem_centralizer_iff.mp (hle hu) x (Set.mem_singleton x)).symm

theorem eq_one_of_torus_centralizes {B : Subgroup G} {M : Fin 4 → Subgroup G}
    (hBcard : Nat.card B = 5 ^ 3) (htor : CTTorusCondition 5 B M)
    (h30 : M 3 ≤ Subgroup.centralizer (M 0 : Set G))
    (h31 : M 3 ≤ Subgroup.centralizer (M 1 : Set G)) {y : G} (hyB : y ∈ B)
    (h0 : y ∈ Subgroup.centralizer (M 0 : Set G)) (h1 : y ∈ Subgroup.centralizer (M 1 : Set G))
    (h3 : y ∈ Subgroup.centralizer (M 3 : Set G)) : y = 1 := by
  obtain ⟨hdec3, hidx3⟩ := htor.1 3
  have ht : ∃ t ∈ B ⊓ M 3, t ∉ Subgroup.centralizer (M 3 : Set G) := by
    by_contra hcon
    push Not at hcon
    have hle : B ⊓ M 3 ≤ B ⊓ Subgroup.centralizer (M 3 : Set G) :=
      fun t ht => ⟨ht.1, hcon t ht⟩
    have hBle : B ≤ B ⊓ Subgroup.centralizer (M 3 : Set G) := by
      conv_lhs => rw [hdec3]
      exact sup_le le_rfl hle
    rw [Subgroup.relIndex_eq_one.mpr hBle] at hidx3
    omega
  obtain ⟨t, htmem, htn⟩ := ht
  have hidx01 : (B ⊓ Subgroup.centralizer ((M 0 ⊔ M 1 : Subgroup G) : Set G)).relIndex B = 25 := by
    have := htor.2 0 1 (by decide)
    rwa [show (5 : ℕ) ^ 2 = 25 by norm_num] at this
  have hcard01 : Nat.card ↥(B ⊓ Subgroup.centralizer ((M 0 ⊔ M 1 : Subgroup G) : Set G)) = 5 := by
    have h := Subgroup.relIndex_mul_card
      (H := B ⊓ Subgroup.centralizer ((M 0 ⊔ M 1 : Subgroup G) : Set G)) (K := B)
    rw [inf_eq_left.mpr inf_le_left, hidx01, hBcard] at h
    omega
  have htH : t ∈ B ⊓ Subgroup.centralizer ((M 0 ⊔ M 1 : Subgroup G) : Set G) :=
    ⟨htmem.1, mem_centralizer_sup (h30 htmem.2) (h31 htmem.2)⟩
  have hyH : y ∈ B ⊓ Subgroup.centralizer ((M 0 ⊔ M 1 : Subgroup G) : Set G) :=
    ⟨hyB, mem_centralizer_sup h0 h1⟩
  set H01 := B ⊓ Subgroup.centralizer ((M 0 ⊔ M 1 : Subgroup G) : Set G) with hH01
  set D := H01 ⊓ (B ⊓ Subgroup.centralizer (M 3 : Set G)) with hD
  have hdvd : Nat.card D ∣ 5 := hcard01 ▸ Subgroup.card_dvd_of_le (inf_le_left : D ≤ H01)
  rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h1' | h5
  · have hbot : D = ⊥ := Subgroup.eq_bot_of_card_eq D h1'
    have hyD : y ∈ D := ⟨hyH, hyB, h3⟩
    rw [hbot] at hyD
    exact Subgroup.mem_bot.mp hyD
  · exfalso
    have hDeq : D = H01 := Subgroup.eq_of_le_of_card_ge inf_le_left (by rw [h5, hcard01])
    have htD : t ∈ D := by rw [hDeq]; exact htH
    exact htn htD.2.2

end Torus

section Outer

variable {G : Type} [Group G] [Finite G]

theorem inf_le_of_outer {E B X : Subgroup G} {c : G} (hBE : B ≤ E)
    (hEcard : Nat.card E = 5 * Nat.card B) (hBX : B ≤ X) (hcE : c ∈ E) (hcX : c ∉ X) :
    E ⊓ X ≤ B := by
  have hBin : B ≤ E ⊓ X := le_inf hBE hBX
  have hpos : 0 < Nat.card B := Nat.card_pos
  obtain ⟨k, hk⟩ := Subgroup.card_dvd_of_le hBin
  have hdvd : Nat.card ↥(E ⊓ X) ∣ Nat.card E := Subgroup.card_dvd_of_le inf_le_left
  rw [hk, hEcard] at hdvd
  have hk5 : k ∣ 5 := by
    have : Nat.card B * k ∣ Nat.card B * 5 := by rwa [mul_comm 5] at hdvd
    exact Nat.dvd_of_mul_dvd_mul_left hpos this
  rcases (Nat.dvd_prime Nat.prime_five).mp hk5 with h1 | h5
  · have : B = E ⊓ X := Subgroup.eq_of_le_of_card_ge hBin (by rw [hk, h1]; simp)
    rw [← this]
  · exfalso
    have hEX : E ⊓ X = E := Subgroup.eq_of_le_of_card_ge inf_le_left (by
      rw [hk, h5, hEcard, mul_comm])
    apply hcX
    have : c ∈ E ⊓ X := by rw [hEX]; exact hcE
    exact this.2

end Outer

end CFSG.RankThree.PartOne.CTP

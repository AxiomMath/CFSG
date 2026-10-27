module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5Tetra
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightD5CoordCor

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
  {K : Fin 4 → Subgroup (MulAut W)} {Z : Fin 4 → Subgroup W}

private theorem s16e_d5_K_inf_eq_bot (hfr : s16e_d5_Frame L K Z) {i j : Fin 4} (hij : i ≠ j) :
    K i ⊓ K j = ⊥ := by
  have hdvd : Nat.card ↥(K i ⊓ K j) ∣ 3 := by
    rw [← hfr.K_card i]
    exact Subgroup.card_dvd_of_le inf_le_left
  rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h1 | h3
  · exact Subgroup.card_eq_one.mp h1
  · have hcard : Nat.card ↥(K i ⊓ K j) = Nat.card ↥(K i) := by rw [h3, hfr.K_card i]
    have hEq : K i ⊓ K j = K i :=
      Subgroup.eq_of_le_of_card_ge inf_le_left (le_of_eq hcard.symm)
    have hle : K i ≤ K j := by rw [← hEq]; exact inf_le_right
    have hEq2 : K i = K j :=
      Subgroup.eq_of_le_of_card_ge hle (by rw [hfr.K_card j, hfr.K_card i])
    exact absurd (hfr.K_inj hEq2) hij

private theorem s16e_d5_gen_rel {φ : ↥L ≃* Multiplicative (Fin 2 → ZMod 3)} {m n : ℕ}
    (h : (φ.symm (Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : ZMod 3)))) ^ m *
        (φ.symm (Multiplicative.ofAdd (Pi.single (1 : Fin 2) (1 : ZMod 3)))) ^ n = 1) :
    (m : ZMod 3) = 0 ∧ (n : ZMod 3) = 0 := by
  have h1 : (Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : ZMod 3))) ^ m *
      (Multiplicative.ofAdd (Pi.single (1 : Fin 2) (1 : ZMod 3))) ^ n =
      (1 : Multiplicative (Fin 2 → ZMod 3)) := by
    have h2 := congrArg φ h
    simpa using h2
  constructor
  · have h0 := congrFun (congrArg Multiplicative.toAdd h1) (0 : Fin 2)
    simpa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] using h0
  · have h0 := congrFun (congrArg Multiplicative.toAdd h1) (1 : Fin 2)
    simpa [Pi.add_apply, Pi.smul_apply, nsmul_eq_mul] using h0

theorem s16e_d5_minors (hfr : s16e_d5_Frame L K Z)
    {κ : ↥(Subgroup.centralizer (L : Set (MulAut W))) →* Multiplicative (Fin 4 → ZMod 3)}
    (hκ : ∀ (g : ↥(Subgroup.centralizer (L : Set (MulAut W)))) (i : Fin 4),
      (Multiplicative.toAdd (κ g)) i = 0 ↔ ∀ z ∈ Z i, (g : MulAut W) z = z) :
    ∃ x y : ↥(Subgroup.centralizer (L : Set (MulAut W))), (x : MulAut W) ∈ L ∧ (y : MulAut W) ∈ L ∧
      ∀ i j : Fin 4, i ≠ j →
        (Multiplicative.toAdd (κ x)) i * (Multiplicative.toAdd (κ y)) j ≠
          (Multiplicative.toAdd (κ x)) j * (Multiplicative.toAdd (κ y)) i := by
  classical
  obtain ⟨φ⟩ := hfr.elem_L
  let e₀ : Multiplicative (Fin 2 → ZMod 3) :=
    Multiplicative.ofAdd (Pi.single (0 : Fin 2) (1 : ZMod 3))
  let e₁ : Multiplicative (Fin 2 → ZMod 3) :=
    Multiplicative.ofAdd (Pi.single (1 : Fin 2) (1 : ZMod 3))
  let x : ↥(Subgroup.centralizer (L : Set (MulAut W))) :=
    ⟨(φ.symm e₀ : MulAut W), s16e_d5_L_le_cent hfr (φ.symm e₀).2⟩
  let y : ↥(Subgroup.centralizer (L : Set (MulAut W))) :=
    ⟨(φ.symm e₁ : MulAut W), s16e_d5_L_le_cent hfr (φ.symm e₁).2⟩
  have hxL : (x : MulAut W) ∈ L := (φ.symm e₀).2
  have hyL : (y : MulAut W) ∈ L := (φ.symm e₁).2
  refine ⟨x, y, hxL, hyL, ?_⟩
  intro i j hij hminor
  let u : Fin 4 → ZMod 3 := Multiplicative.toAdd (κ x)
  let v : Fin 4 → ZMod 3 := Multiplicative.toAdd (κ y)
  obtain ⟨a, b, hab, hi, hj⟩ := s16e_d5_cols_prop (u i) (v i) (u j) (v j) hminor
  let z : ↥(Subgroup.centralizer (L : Set (MulAut W))) := x ^ a.val * y ^ b.val
  have hzκ : ∀ k, Multiplicative.toAdd (κ z) k = a * u k + b * v k := by
    intro k
    have hz_eq : κ z = (κ x) ^ a.val * (κ y) ^ b.val := by
      simp only [z, map_mul, map_pow]
    rw [hz_eq]
    simp only [toAdd_mul, toAdd_pow, Pi.add_apply, Pi.mul_apply, Pi.natCast_apply,
      nsmul_eq_mul, ZMod.natCast_zmod_val]
    rfl
  have hzL : (z : MulAut W) ∈ L := by
    change (x : MulAut W) ^ a.val * (y : MulAut W) ^ b.val ∈ L
    exact L.mul_mem (L.pow_mem hxL a.val) (L.pow_mem hyL b.val)
  have hfixi : ∀ w ∈ Z i, (z : MulAut W) w = w := (hκ z i).1 (by rw [hzκ i, hi])
  have hfixj : ∀ w ∈ Z j, (z : MulAut W) w = w := (hκ z j).1 (by rw [hzκ j, hj])
  have hzKi : (z : MulAut W) ∈ K i := (hfr.kernel i hzL).1 hfixi
  have hzKj : (z : MulAut W) ∈ K j := (hfr.kernel j hzL).1 hfixj
  have hzbot : (z : MulAut W) ∈ (⊥ : Subgroup (MulAut W)) := by
    rw [← s16e_d5_K_inf_eq_bot hfr hij]
    exact Subgroup.mem_inf.mpr ⟨hzKi, hzKj⟩
  have hzval : (z : MulAut W) = 1 := by simpa using hzbot
  have hgen : (φ.symm e₀) ^ a.val * (φ.symm e₁) ^ b.val = 1 := by
    apply Subtype.ext
    show (x : MulAut W) ^ a.val * (y : MulAut W) ^ b.val = 1
    exact hzval
  have hmn := s16e_d5_gen_rel (φ := φ) (by simpa only [e₀, e₁] using hgen)
  have ha0 : a = 0 := by
    have h := hmn.1
    rwa [ZMod.natCast_zmod_val a] at h
  have hb0 : b = 0 := by
    have h := hmn.2
    rwa [ZMod.natCast_zmod_val b] at h
  rcases hab with ha | hb
  · exact ha ha0
  · exact hb hb0

theorem s16e_d5_exists_axis (hfr : s16e_d5_Frame L K Z) {A : Subgroup (MulAut W)} (hLA : L ≤ A)
    (h27 : 27 ≤ Nat.card ↥(A ⊓ Subgroup.centralizer (L : Set (MulAut W)))) :
    ∃ (i : Fin 4) (a : MulAut W), a ∈ A ∧ a ∈ Subgroup.centralizer (L : Set (MulAut W)) ∧
      a ≠ 1 ∧ ∀ k, k ≠ i → ∀ z ∈ Z k, a z = z := by
  classical
  let C := Subgroup.centralizer (L : Set (MulAut W))
  obtain ⟨κ, hinj, hκ0, _⟩ := s16e_d5_coord hfr
  obtain ⟨x, y, hxL, hyL, hmin⟩ := s16e_d5_minors hfr hκ0
  let S : Subgroup (Multiplicative (Fin 4 → ZMod 3)) := ((A ⊓ C).subgroupOf C).map κ
  have hS_eq : S = ((A ⊓ C).subgroupOf C).map κ := rfl
  have hS_card : Nat.card ↥S = Nat.card ↥(A ⊓ C) := by
    rw [hS_eq, Subgroup.card_map_of_injective (f := κ) hinj]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv
  have hS : 27 ≤ Nat.card ↥S := by rw [hS_card]; exact h27
  have hxS : κ x ∈ S := by
    rw [hS_eq]
    refine Subgroup.mem_map.mpr ⟨x, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨hLA hxL, x.2⟩
  have hyS : κ y ∈ S := by
    rw [hS_eq]
    refine Subgroup.mem_map.mpr ⟨y, ?_, rfl⟩
    rw [Subgroup.mem_subgroupOf]
    exact Subgroup.mem_inf.mpr ⟨hLA hyL, y.2⟩
  obtain ⟨i, hi⟩ := s16e_d5_tetra hmin hxS hyS hS
  have hi' : Multiplicative.ofAdd (Pi.single i (1 : ZMod 3)) ∈
      ((A ⊓ C).subgroupOf C).map κ := by simpa only [hS_eq] using hi
  obtain ⟨g, hg, hgκ⟩ := Subgroup.mem_map.mp hi'
  have hgAC : (g : MulAut W) ∈ A ⊓ C := Subgroup.mem_subgroupOf.mp hg
  refine ⟨i, (g : MulAut W), hgAC.1, hgAC.2, ?_, ?_⟩
  · intro hg1
    have hg_eq : g = 1 := Subtype.ext hg1
    have hcoord : Multiplicative.toAdd (κ g) i = 1 := by
      rw [hgκ, toAdd_ofAdd, Pi.single_eq_same]
    rw [hg_eq, map_one] at hcoord
    simp only [toAdd_one, Pi.zero_apply] at hcoord
    exact zero_ne_one hcoord
  · intro k hk z hz
    exact (hκ0 g k).1 (by rw [hgκ, toAdd_ofAdd, Pi.single_eq_of_ne' (Ne.symm hk)]) z hz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

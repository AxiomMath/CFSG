module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7RGrp

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.F6.GoldAmL
open scoped commutatorElement

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D]

theorem isKleinFour_of_natural {H T V : Subgroup D} {z : D} (hn : IsNaturalAt H T z V) :
    IsKleinFour ↥V := by
  have hsq : ∀ x : V, x ^ 2 = 1 := fun x =>
    Subtype.ext (by simpa using isElemAbelian_pow_eq_one hn.reduced.2.2.1 x.2)
  refine ⟨hn.card_eq, ?_⟩
  rcases (Nat.dvd_prime Nat.prime_two).mp (Monoid.exponent_dvd_of_forall_pow_eq_one hsq) with
    h | h
  · have : Subsingleton V := Monoid.exp_eq_one_iff.mp h
    have h1 := Nat.card_of_subsingleton (1 : V)
    have h4 := hn.card_eq
    omega
  · exact h

theorem eq_mul_of_ne_all' {V : Subgroup D} [IsKleinFour ↥V] {n m x : D} (hn : n ∈ V) (hm : m ∈ V)
    (hx : x ∈ V) (hn1 : n ≠ 1) (hm1 : m ≠ 1) (hnm : n ≠ m) (hx1 : x ≠ 1) (hxn : x ≠ n)
    (hxm : x ≠ m) : x = n * m := by
  have := IsKleinFour.eq_mul_of_ne_all (G := ↥V) (x := ⟨n, hn⟩) (y := ⟨m, hm⟩) (z := ⟨x, hx⟩)
    (fun h => hn1 (congrArg Subtype.val h)) (fun h => hm1 (congrArg Subtype.val h))
    (fun h => hnm (congrArg Subtype.val h)) (fun h => hx1 (congrArg Subtype.val h))
    (fun h => hxn (congrArg Subtype.val h)) (fun h => hxm (congrArg Subtype.val h))
  exact congrArg Subtype.val this

variable [Finite D]

theorem exists_moved_of_natural {A B V₂ : Subgroup D} {c : D} (h : GoldHyp A B)
    (hne : pCoreOf 2 A ≠ pCoreOf 2 B) (hn : IsNaturalAt B (A ⊓ B) c V₂) :
    ∃ a ∈ pCoreOf 2 A, ∃ n ∈ V₂, a * n * a⁻¹ ≠ n := by
  have h2 := relIndex_inf_pCoreOf_left' h hne
  have hnle : ¬ pCoreOf 2 A ≤ pCoreOf 2 A ⊓ pCoreOf 2 B := fun hle => by
    have := Subgroup.relIndex_eq_one.mpr hle
    omega
  obtain ⟨a, haA, haR⟩ := IsConcreteLE.not_le_iff_exists.mp hnle
  have haB : a ∉ pCoreOf 2 B := fun hb => haR ⟨haA, hb⟩
  have haTB : a ∈ B := (h.pCoreOf_left_le haA).2
  have hnc : a ∉ Subgroup.centralizer (V₂ : Set D) := fun hc => haB (by
    rw [← hn.centralizer_eq]
    exact ⟨haTB, hc⟩)
  refine ⟨a, haA, ?_⟩
  by_contra hall
  push Not at hall
  exact hnc (Subgroup.mem_centralizer_iff.mpr fun n hnV => (mul_eq_of_conj_eq (hall n hnV)).symm)

theorem fixed_point_free_of_natural {H T V : Subgroup D} {z : D} (hv : Vertex H T)
    (hn : IsNaturalAt H T z V) {y : D} (hy : y ∈ H) (hy3 : orderOf y = 3) :
    ∀ n ∈ V, y * n * y⁻¹ = n → n = 1 := by
  intro n hnV hyn
  by_contra hn1
  have := isKleinFour_of_natural hn
  have hyN : y ∈ Subgroup.normalizer (V : Set D) := hn.reduced.2.1 hy
  have hy3' : y * y * y = 1 := by
    have := pow_orderOf_eq_one y
    rwa [hy3, pow_three'] at this
  have hσ3 : ∀ x : D, y * (y * (y * x * y⁻¹) * y⁻¹) * y⁻¹ = x := fun x => by
    calc y * (y * (y * x * y⁻¹) * y⁻¹) * y⁻¹ = (y * y * y) * x * (y * y * y)⁻¹ := by group
      _ = x := by rw [hy3']; group
  obtain ⟨a, ha1, hac, hset⟩ := hn.basis
  have hz : z ∈ V := by
    have : z ∈ (V : Set D) := by rw [hset]; simp
    exact this
  have ha : a ∈ V := by
    have : a ∈ (V : Set D) := by rw [hset]; simp
    exact this
  obtain ⟨m, hmV, hm1, hmn⟩ : ∃ m ∈ V, m ≠ 1 ∧ m ≠ n := by
    by_cases hnz : n = z
    · exact ⟨a, ha, ha1, fun h => hac (h.trans hnz)⟩
    · exact ⟨z, hz, hn.z_ne, fun h => hnz h.symm⟩
  have hnn : n * n = 1 := by
    rw [← pow_two]
    exact isElemAbelian_pow_eq_one hn.reduced.2.2.1 hnV
  have hσm : y * m * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyN m).mp hmV
  have hfix : y * m * y⁻¹ = m := by
    by_contra hne
    have h1 : y * m * y⁻¹ ≠ 1 := fun h => hm1 (by
      have := congrArg (fun w => y⁻¹ * w * y) h
      simpa [mul_assoc] using this)
    have h2 : y * m * y⁻¹ ≠ n := fun h => hmn (by
      have h3 : y * m * y⁻¹ = y * n * y⁻¹ := h.trans hyn.symm
      exact mul_left_cancel (mul_right_cancel h3))
    have hm' : y * m * y⁻¹ = n * m :=
      eq_mul_of_ne_all' hnV hmV hσm hn1 hm1 (Ne.symm hmn) h1 h2 hne
    have h4 : y * (y * m * y⁻¹) * y⁻¹ = m := by
      rw [hm']
      calc y * (n * m) * y⁻¹ = (y * n * y⁻¹) * (y * m * y⁻¹) := by group
        _ = n * (n * m) := by rw [hyn, hm']
        _ = m := by rw [← mul_assoc, hnn, one_mul]
    have h5 := hσ3 m
    rw [h4] at h5
    exact hne h5
  have hall : ∀ x ∈ V, y * x * y⁻¹ = x := by
    intro x hx
    by_cases hx1 : x = 1
    · rw [hx1]; group
    by_cases hxn : x = n
    · rw [hxn]; exact hyn
    by_cases hxm : x = m
    · rw [hxm]; exact hfix
    have hx_eq : x = n * m := eq_mul_of_ne_all' hnV hmV hx hn1 hm1 (Ne.symm hmn) hx1 hxn hxm
    rw [hx_eq]
    calc y * (n * m) * y⁻¹ = (y * n * y⁻¹) * (y * m * y⁻¹) := by group
      _ = n * m := by rw [hyn, hfix]
  have hyC : y ∈ Subgroup.centralizer (V : Set D) :=
    Subgroup.mem_centralizer_iff.mpr fun x hx => (mul_eq_of_conj_eq (hall x hx)).symm
  have hyQ : y ∈ pCoreOf 2 H := by
    rw [← hn.centralizer_eq]
    exact ⟨hy, hyC⟩
  exact hv.not_mem_of_orderOf hy3 (hv.pCoreOf_le hyQ)

theorem exists_comm_eq_of_fixed_free {V : Subgroup D} (hab : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a)
    {y : D} (hyV : ∀ x ∈ V, y * x * y⁻¹ ∈ V) (hfree : ∀ n ∈ V, y * n * y⁻¹ = n → n = 1) :
    ∀ n ∈ V, ∃ m ∈ V, ⁅m, y⁆ = n := by
  let φ : V → V := fun m =>
    ⟨(m : D) * (y * (m : D) * y⁻¹)⁻¹, V.mul_mem m.2 (V.inv_mem (hyV m m.2))⟩
  have hinj : Function.Injective φ := by
    intro m m' hmm
    have h1 : (m : D) * (y * (m : D) * y⁻¹)⁻¹ = (m' : D) * (y * (m' : D) * y⁻¹)⁻¹ :=
      congrArg Subtype.val hmm
    have hu : y * (m : D) * y⁻¹ ∈ V := hyV m m.2
    have hu' : y * (m' : D) * y⁻¹ ∈ V := hyV m' m'.2
    have e1 : (m' : D)⁻¹ * m = (y * (m' : D) * y⁻¹)⁻¹ * (y * (m : D) * y⁻¹) := by
      calc (m' : D)⁻¹ * m
          = (m' : D)⁻¹ * ((m : D) * (y * (m : D) * y⁻¹)⁻¹) * (y * (m : D) * y⁻¹) := by group
        _ = (m' : D)⁻¹ * ((m' : D) * (y * (m' : D) * y⁻¹)⁻¹) * (y * (m : D) * y⁻¹) := by
          rw [h1]
        _ = (y * (m' : D) * y⁻¹)⁻¹ * (y * (m : D) * y⁻¹) := by group
    have e2 : (m : D) * (m' : D)⁻¹ = (m' : D)⁻¹ * m := hab _ m.2 _ (V.inv_mem m'.2)
    have e3 : (y * (m' : D) * y⁻¹)⁻¹ * (y * (m : D) * y⁻¹) =
        (y * (m : D) * y⁻¹) * (y * (m' : D) * y⁻¹)⁻¹ := hab _ (V.inv_mem hu') _ hu
    have hfixed : y * ((m : D) * (m' : D)⁻¹) * y⁻¹ = (m : D) * (m' : D)⁻¹ := by
      calc y * ((m : D) * (m' : D)⁻¹) * y⁻¹
          = (y * (m : D) * y⁻¹) * (y * (m' : D) * y⁻¹)⁻¹ := by group
        _ = (y * (m' : D) * y⁻¹)⁻¹ * (y * (m : D) * y⁻¹) := e3.symm
        _ = (m' : D)⁻¹ * m := e1.symm
        _ = (m : D) * (m' : D)⁻¹ := e2.symm
    have h0 := hfree _ (V.mul_mem m.2 (V.inv_mem m'.2)) hfixed
    exact Subtype.ext (mul_inv_eq_one.mp h0)
  have hsurj := Finite.injective_iff_surjective.mp hinj
  intro n hnV
  obtain ⟨m, hm⟩ := hsurj ⟨n, hnV⟩
  refine ⟨m, m.2, ?_⟩
  have h1 : (m : D) * (y * (m : D) * y⁻¹)⁻¹ = n := congrArg Subtype.val hm
  rw [← h1, commutatorElement_def]
  group

end GoldAmLab7

end F6

end CFSG.Quasithin

module

public import CFSG.Quasithin.H13.NQCatLieCartanTools
public import CFSG.Quasithin.H13.NQCatCartanSp4

public section

namespace CFSG.Quasithin.H13.NQCat.LieCartan.Sp4

open Matrix CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
  CFSG.LocalAnalysis.ComponentInitial.SymplecticTorusWeyl CFSG.QuasithinUnique.Vol2Native.A312L
  CFSG.Quasithin.H13.NQCat.Sp4

variable {K : Type} [Field K]

theorem torusHom_conj_xC (t : Fin 2 → Kˣ) (c : K) :
    torusHom t * xC c * (torusHom t)⁻¹ = xC ((t 0 : K) * (t 0 : K) * c) := by
  rw [← map_inv]
  apply statedSp_ext
  change spMat (torusHom t) * spMat (xC c) * spMat (torusHom t⁻¹) = spMat (xC _)
  rw [show spMat (torusHom t) = _ from coe_torusHom t,
    show spMat (torusHom t⁻¹) = _ from coe_torusHom t⁻¹, spMat_xC, spMat_xC]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, single_apply, Matrix.one_apply, diagonal_apply]
  all_goals ring

theorem torusHom_conj_xAB (t : Fin 2 → Kˣ) (c : K) :
    torusHom t * xAB c * (torusHom t)⁻¹ = xAB ((t 0 : K) * (t 1 : K) * c) := by
  rw [← map_inv]
  apply statedSp_ext
  change spMat (torusHom t) * spMat (xAB c) * spMat (torusHom t⁻¹) = spMat (xAB _)
  rw [show spMat (torusHom t) = _ from coe_torusHom t,
    show spMat (torusHom t⁻¹) = _ from coe_torusHom t⁻¹, spMat_xAB, spMat_xAB]
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, single_apply, Matrix.one_apply, diagonal_apply]
  all_goals ring

theorem spMat_xC_mul_xAB (c₀ c₁ : K) :
    spMat (xC c₀ * xAB c₁) (Sum.inl 0) (Sum.inr 0) = c₀ ∧
      spMat (xC c₀ * xAB c₁) (Sum.inl 0) (Sum.inr 1) = c₁ := by
  change (spMat (xC c₀) * spMat (xAB c₁)) (Sum.inl 0) (Sum.inr 0) = c₀ ∧
    (spMat (xC c₀) * spMat (xAB c₁)) (Sum.inl 0) (Sum.inr 1) = c₁
  rw [spMat_xC, spMat_xAB]
  constructor <;>
    simp [Matrix.mul_apply, Fintype.sum_sum_type, single_apply, Matrix.one_apply]

theorem eq_xC_mul_xAB_of_commute [CharP K 2] {u : StatedSp 2 K} (hu : u ∈ unipotent 2 K)
    (hA : u * xA 1 = xA 1 * u) (hB : u * xB 1 = xB 1 * u) :
    ∃ c₀ c₁ : K, u = xC c₀ * xAB c₁ := by
  obtain ⟨x, c₀, c₁, c₂, rfl⟩ := exists_eq_prod_of_mem_unipotent hu
  have hB' : spMat (xA x) * spMat (xC c₀) * spMat (xAB c₁) * spMat (xB c₂) * spMat (xB 1) =
      spMat (xB 1) * (spMat (xA x) * spMat (xC c₀) * spMat (xAB c₁) * spMat (xB c₂)) :=
    congrArg spMat hB
  have hA' : spMat (xA x) * spMat (xC c₀) * spMat (xAB c₁) * spMat (xB c₂) * spMat (xA 1) =
      spMat (xA 1) * (spMat (xA x) * spMat (xC c₀) * spMat (xAB c₁) * spMat (xB c₂)) :=
    congrArg spMat hA
  rw [spMat_xA, spMat_xC, spMat_xAB, spMat_xB, spMat_xB] at hB'
  rw [spMat_xA, spMat_xC, spMat_xAB, spMat_xB, spMat_xA] at hA'
  have e1 := congrFun (congrFun hB' (Sum.inl 0)) (Sum.inr 1)
  have e2 := congrFun (congrFun hA' (Sum.inl 1)) (Sum.inr 0)
  simp [Matrix.mul_apply, Fintype.sum_sum_type, Fin.sum_univ_two, single_apply,
    Matrix.one_apply] at e1 e2
  subst e1 e2
  have hA0 : xA (0 : K) = 1 :=
    mul_left_cancel ((xA_mul (0 : K) 0).trans (by rw [add_zero, mul_one]))
  have hB0 : xB (0 : K) = 1 :=
    mul_left_cancel ((xB_mul (0 : K) 0).trans (by rw [add_zero, mul_one]))
  exact ⟨c₀, c₁, by rw [hA0, hB0, one_mul, mul_one]⟩

theorem eq_one_of_mul_self [CharP K 2] {t : K} (h : t * t = 1) : t = 1 := by
  have h3 : (t - 1) ^ 2 = 0 := by
    have h5 : (2 : K) = 0 := CharTwo.two_eq_zero
    linear_combination h + (1 - t) * h5
  exact sub_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 h3)

theorem torusConcl_sp4 [Finite K] [CharP K 2] (hK4 : 4 ≤ Nat.card K) :
    TorusConcl (StatedSp 2 K) True := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hQ⟩ := exists_sylow_unipotent (K := K) 2 2
  have hU : IsSylowTwoOf (unipotent 2 K) ⊤ := hQ ▸ isSylowTwoOf_top_of_sylow Q
  have hHN : torus 2 K ≤ Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) := by
    rw [normalizer_unipotent]
    exact torus_le_borelSubgroup
  have hNH : Subgroup.normalizer (unipotent 2 K : Set (StatedSp 2 K)) ≤
      unipotent 2 K ⊔ torus 2 K := by
    rw [normalizer_unipotent]
    intro b hb
    have h1 : (⟨b, hb⟩ * (⟨torusHom (diagHom 2 K ⟨b, hb⟩),
        torus_le_borelSubgroup ⟨_, rfl⟩⟩ : borelSubgroup 2 K)⁻¹ : borelSubgroup 2 K) ∈
        (diagHom 2 K).ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, CartanSp4.diagHom_torusHom, mul_inv_cancel]
    rw [ker_diagHom, Subgroup.mem_subgroupOf] at h1
    have e : b = (b * (torusHom (diagHom 2 K ⟨b, hb⟩))⁻¹) * torusHom (diagHom 2 K ⟨b, hb⟩) := by
      group
    rw [e]
    exact mul_mem (Subgroup.mem_sup_left h1) (Subgroup.mem_sup_right ⟨_, rfl⟩)
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨m, -, hm⟩ := FiniteField.card K 2
  have hKm : Nat.card K = 2 ^ (m : ℕ) := by rw [Nat.card_eq_fintype_card, hm]
  have hodd1 : Odd (Nat.card K - 1) := by
    rw [hKm, Nat.odd_iff]
    have h2 : 2 ∣ 2 ^ (m : ℕ) := dvd_pow_self 2 m.ne_zero
    have h1 : 1 ≤ 2 ^ (m : ℕ) := Nat.one_le_two_pow
    omega
  have hcardT : Nat.card (Fin 2 → Kˣ) = (Nat.card K - 1) ^ 2 := by
    rw [Nat.card_fun, Nat.card_units, Nat.card_eq_fintype_card (α := Fin 2), Fintype.card_fin]
  have hodd : Odd (Nat.card (torus 2 K)) := by
    rw [torus, MonoidHom.range_eq_map, Subgroup.card_map_of_injective torusHom_injective,
      Subgroup.card_top, hcardT]
    exact hodd1.pow
  have hcomm : ∀ a ∈ torus 2 K, ∀ b ∈ torus 2 K, a * b = b * a := by
    rintro _ ⟨s, rfl⟩ _ ⟨s', rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  refine torusConcl_of_torus hU hHN hNH hodd hcomm fun E hEU hE hE16 hEC =>
    ⟨?_, fun _ => trivial⟩
  have hc : ∀ x : E, ∃ c : K × K, (x : StatedSp 2 K) = xC c.1 * xAB c.2 := by
    intro x
    have hxA := Subgroup.mem_centralizer_iff.1 (hEC x.2) (xA 1) (xA_mem 1)
    have hxB := Subgroup.mem_centralizer_iff.1 (hEC x.2) (xB 1) (xB_mem 1)
    obtain ⟨c₀, c₁, h⟩ := eq_xC_mul_xAB_of_commute (hEU x.2) hxA.symm hxB.symm
    exact ⟨(c₀, c₁), h⟩
  choose β hβ using hc
  have hcoord : ∀ {a b a' b' : K}, xC a * xAB b = xC a' * xAB b' → a = a' ∧ b = b' := by
    intro a b a' b' h
    have h1 := spMat_xC_mul_xAB a b
    have h2 := spMat_xC_mul_xAB a' b'
    rw [h] at h1
    exact ⟨h1.1.symm.trans h2.1, h1.2.symm.trans h2.2⟩
  have hβinj : Function.Injective β := fun x y hxy =>
    Subtype.ext (by rw [hβ x, hβ y, hxy])
  have hβ1 : ∀ x : E, β x = (0, 0) → x = 1 := fun x hx =>
    Subtype.ext (by
      rw [hβ x, hx, Subgroup.coe_one]
      have hC0 : xC (0 : K) = 1 :=
        mul_left_cancel ((xC_mul (0 : K) 0).trans (by rw [add_zero, mul_one]))
      have hAB0 : xAB (0 : K) = 1 :=
        mul_left_cancel ((xAB_mul (0 : K) 0).trans (by rw [add_zero, mul_one]))
      rw [hC0, hAB0, one_mul])
  have hfix : ∀ (t : Fin 2 → Kˣ) (x : E),
      torusHom t ∈ Subgroup.centralizer (E : Set (StatedSp 2 K)) →
      (t 0 : K) * t 0 * (β x).1 = (β x).1 ∧ (t 0 : K) * t 1 * (β x).2 = (β x).2 := by
    intro t x ht
    have h1 := Subgroup.mem_centralizer_iff.1 ht (x : StatedSp 2 K) x.2
    rw [hβ x] at h1
    have h2 : torusHom t * xC (β x).1 * (torusHom t)⁻¹ *
        (torusHom t * xAB (β x).2 * (torusHom t)⁻¹) = xC (β x).1 * xAB (β x).2 := by
      calc torusHom t * xC (β x).1 * (torusHom t)⁻¹ *
            (torusHom t * xAB (β x).2 * (torusHom t)⁻¹) =
          torusHom t * (xC (β x).1 * xAB (β x).2) * (torusHom t)⁻¹ := by group
        _ = xC (β x).1 * xAB (β x).2 := by rw [← h1]; group
    rw [torusHom_conj_xC, torusHom_conj_xAB] at h2
    exact hcoord h2
  have hE1 : ∃ x : E, x ≠ 1 := by
    have : Nontrivial E := Finite.one_lt_card_iff_nontrivial.1 (by rw [hE16]; norm_num)
    exact exists_ne 1
  by_cases h0 : ∃ x : E, (β x).1 ≠ 0
  · obtain ⟨x₀, hx₀⟩ := h0
    by_cases h1 : ∃ x : E, (β x).2 ≠ 0
    ·
      obtain ⟨x₁, hx₁⟩ := h1
      refine lt_of_lt_of_le ?_ (card_le_relIndex_of_hom torusHom (fun t => ⟨t, rfl⟩)
        fun t ht => ?_)
      · rw [hcardT]
        have : 3 ≤ Nat.card K - 1 := by omega
        nlinarith
      · have ha := (mul_left_eq_self₀.1 (hfix t x₀ ht).1).resolve_right hx₀
        have hb := (mul_left_eq_self₀.1 (hfix t x₁ ht).2).resolve_right hx₁
        have h0' : t 0 = 1 := Units.ext (eq_one_of_mul_self ha)
        have h1' : t 1 = 1 := by
          rw [h0', Units.val_one, one_mul] at hb
          exact Units.ext hb
        funext i
        fin_cases i
        · exact h0'
        · exact h1'
    ·
      push Not at h1
      have hinj : Function.Injective fun x : E => (β x).1 := by
        intro x y hxy
        apply hβinj
        exact Prod.ext hxy ((h1 x).trans (h1 y).symm)
      have h16 : 16 ≤ Nat.card K := by
        rw [← hE16]
        exact Nat.card_le_card_of_injective _ hinj
      refine lt_of_lt_of_le ?_ (card_le_relIndex_of_hom
        (torusHom.comp (MonoidHom.mulSingle (fun _ : Fin 2 => Kˣ) 0)) (fun s => ⟨_, rfl⟩)
        fun s hs => ?_)
      · rw [Nat.card_units]
        omega
      · have ha := (mul_left_eq_self₀.1 (hfix _ x₀ hs).1).resolve_right hx₀
        simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same] at ha
        exact Units.ext (eq_one_of_mul_self ha)
  ·
    push Not at h0
    obtain ⟨x₁, hx₁⟩ : ∃ x : E, (β x).2 ≠ 0 := by
      obtain ⟨x, hx⟩ := hE1
      refine ⟨x, fun h2 => hx (hβ1 x (Prod.ext (h0 x) h2))⟩
    have hinj : Function.Injective fun x : E => (β x).2 := by
      intro x y hxy
      apply hβinj
      exact Prod.ext ((h0 x).trans (h0 y).symm) hxy
    have h16 : 16 ≤ Nat.card K := by
      rw [← hE16]
      exact Nat.card_le_card_of_injective _ hinj
    refine lt_of_lt_of_le ?_ (card_le_relIndex_of_hom
      (torusHom.comp (MonoidHom.mulSingle (fun _ : Fin 2 => Kˣ) 1)) (fun s => ⟨_, rfl⟩)
      fun s hs => ?_)
    · rw [Nat.card_units]
      omega
    · have hb := (mul_left_eq_self₀.1 (hfix _ x₁ hs).2).resolve_right hx₁
      simp only [MonoidHom.mulSingle_apply, Pi.mulSingle_eq_same, Pi.mulSingle_apply] at hb
      simpa using hb

end CFSG.Quasithin.H13.NQCat.LieCartan.Sp4

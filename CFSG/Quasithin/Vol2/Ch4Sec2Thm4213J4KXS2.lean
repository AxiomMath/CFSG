module

public import CFSG.Quasithin.Vol2.Ch4Sec2Thm4213J4KXQS
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Generation
public import CFSG.LocalAnalysis.ABGTheoremB.Basic

public section

namespace CFSG.Quasithin.H13.Ch4.J4KX

open CFSG.Open
open scoped commutatorElement

section FourGroup

variable {Γ : Type} [Group Γ]

def fourGroup {r z : Γ} (h1 : r * r = 1) (h2 : z * z = 1) (h3 : z * r = r * z) : Subgroup Γ where
  carrier := {g | g = 1 ∨ g = r ∨ g = z ∨ g = r * z}
  mul_mem' := by
    intro a b ha hb
    have q1 : r * z * r = z := by
      calc r * z * r = z * r * r := by rw [← h3]
        _ = z := by rw [mul_assoc, h1, mul_one]
    have q2 : r * z * z = r := by rw [mul_assoc, h2, mul_one]
    have q3 : r * (r * z) = z := by rw [← mul_assoc, h1, one_mul]
    have q4 : z * (r * z) = r := by
      calc z * (r * z) = z * r * z := by rw [mul_assoc]
        _ = r * z * z := by rw [h3]
        _ = r := by rw [mul_assoc, h2, mul_one]
    have q5 : r * z * (r * z) = 1 := by
      calc r * z * (r * z) = r * (z * r) * z := by group
        _ = r * (r * z) * z := by rw [h3]
        _ = z * z := by rw [q3]
        _ = 1 := h2
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      simp only [Set.mem_setOf_eq, one_mul, mul_one, h1, h2, h3, q1, q2, q3, q4, q5, true_or,
        or_true, or_self, eq_self_iff_true, mul_assoc] <;> simp_all
  one_mem' := Or.inl rfl
  inv_mem' := by
    intro a ha
    rcases ha with rfl | rfl | rfl | rfl
    · exact Or.inl (inv_one)
    · exact Or.inr (Or.inl (inv_eq_of_mul_eq_one_right h1))
    · exact Or.inr (Or.inr (Or.inl (inv_eq_of_mul_eq_one_right h2)))
    · right; right; right
      apply inv_eq_of_mul_eq_one_right
      calc r * z * (r * z) = 1 := by
            calc r * z * (r * z) = r * (z * r) * z := by group
              _ = r * (r * z) * z := by rw [h3]
              _ = z * z := by rw [show r * (r * z) = z from by rw [← mul_assoc, h1, one_mul]]
              _ = 1 := h2

theorem fourGroup_isElemAbelian {r z : Γ} (h1 : r * r = 1) (h2 : z * z = 1) (h3 : z * r = r * z) :
    CFSG.Open.IsElemAbelian 2 (fourGroup h1 h2 h3) := by
  have q1 : r * z * r = z := by
    calc r * z * r = z * r * r := by rw [← h3]
      _ = z := by rw [mul_assoc, h1, mul_one]
  have q3 : r * (r * z) = z := by rw [← mul_assoc, h1, one_mul]
  have q2 : r * z * z = r := by rw [mul_assoc, h2, mul_one]
  have q4 : z * (r * z) = r := by
    calc z * (r * z) = z * r * z := by rw [mul_assoc]
      _ = r * z * z := by rw [h3]
      _ = r := by rw [mul_assoc, h2, mul_one]
  have q5 : r * z * (r * z) = 1 := by
    calc r * z * (r * z) = r * (z * r) * z := by group
      _ = r * (r * z) * z := by rw [h3]
      _ = z * z := by rw [q3]
      _ = 1 := h2
  refine ⟨⟨⟨fun x y => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    have hx : (x : Γ) = 1 ∨ (x : Γ) = r ∨ (x : Γ) = z ∨ (x : Γ) = r * z := x.2
    have hy : (y : Γ) = 1 ∨ (y : Γ) = r ∨ (y : Γ) = z ∨ (y : Γ) = r * z := y.2
    rw [Subgroup.coe_mul, Subgroup.coe_mul]
    rcases hx with hx | hx | hx | hx <;> rcases hy with hy | hy | hy | hy <;>
      simp only [hx, hy, one_mul, mul_one, h1, h2, h3, q1, q2, q3, q4, q5]
  · intro x hx
    have hx' : x = 1 ∨ x = r ∨ x = z ∨ x = r * z := hx
    rcases hx' with h | h | h | h
    · rw [h, one_pow]
    · rw [h, pow_two, h1]
    · rw [h, pow_two, h2]
    · rw [h, pow_two, q5]

end FourGroup

section Step2

variable {Γ : Type} [Group Γ] [Finite Γ]

theorem four_card_ge {r z : Γ} (h1 : r * r = 1) (h2 : z * z = 1) (h3 : z * r = r * z)
    (hr1 : r ≠ 1) (hz1 : z ≠ 1) (hrz : r ≠ z) : 4 ≤ Nat.card (fourGroup h1 h2 h3) := by
  have d1 : (1 : Γ) ≠ r := fun h => hr1 h.symm
  have d2 : (1 : Γ) ≠ z := fun h => hz1 h.symm
  have d3 : (1 : Γ) ≠ r * z := by
    intro h
    apply hrz
    have hzr : z = r := by
      calc z = r * (r * z) := by rw [← mul_assoc, h1, one_mul]
        _ = r * 1 := by rw [h]
        _ = r := mul_one r
    exact hzr.symm
  have d4 : r ≠ z := hrz
  have d5 : r ≠ r * z := by
    intro h
    apply hz1
    have : (1 : Γ) = z := mul_left_cancel (a := r) (by rw [mul_one]; exact h)
    exact this.symm
  have d6 : z ≠ r * z := by
    intro h
    apply hr1
    have : (1 : Γ) = r := mul_right_cancel (b := z) (by rw [one_mul]; exact h)
    exact this.symm
  let f : Fin 4 → fourGroup h1 h2 h3 := fun i =>
    ⟨![1, r, z, r * z] i, by
      fin_cases i
      · exact Or.inl rfl
      · exact Or.inr (Or.inl rfl)
      · exact Or.inr (Or.inr (Or.inl rfl))
      · exact Or.inr (Or.inr (Or.inr rfl))⟩
  have hinj : Function.Injective f := by
    intro i j hij
    have h := congrArg Subtype.val hij
    fin_cases i <;> fin_cases j <;> simp_all [f]
  have := Nat.card_le_card_of_injective f hinj
  simpa using this

theorem odd_core_le_normalizer {K : Subgroup Γ} {r z : Γ} (h1 : r * r = 1) (h2 : z * z = 1)
    (h3 : z * r = r * z) (hr1 : r ≠ 1) (hz1 : z ≠ 1) (hrz : r ≠ z)
    (hNr : Subgroup.centralizer ({r} : Set Γ) ≤ Subgroup.normalizer (K : Set Γ))
    (hNz : Subgroup.centralizer ({z} : Set Γ) ≤ Subgroup.normalizer (K : Set Γ))
    (hNrz : Subgroup.centralizer ({r * z} : Set Γ) ≤ Subgroup.normalizer (K : Set Γ)) :
    CFSG.oddCore Γ ≤ Subgroup.normalizer (K : Set Γ) := by
  have hA := fourGroup_isElemAbelian h1 h2 h3
  have hrank : 2 ^ 2 ≤ Nat.card (fourGroup h1 h2 h3) := by
    have := four_card_ge h1 h2 h3 hr1 hz1 hrz
    norm_num
    omega
  have hNO : Subgroup.normalizer ((CFSG.oddCore Γ : Subgroup Γ) : Set Γ) = ⊤ :=
    Subgroup.normalizer_eq_top_iff.mpr inferInstance
  have hAX : fourGroup h1 h2 h3 ≤ Subgroup.normalizer ((CFSG.oddCore Γ : Subgroup Γ) : Set Γ) :=
    hNO ▸ le_top
  have hodd := CFSG.ABGTheoremB.odd_card_oddCore Γ
  have hX : Nat.Coprime 2 (Nat.card (CFSG.oddCore Γ)) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr (by
      intro h
      have := Nat.odd_iff.mp hodd
      omega)
  have hsup := CFSG.SignalizerFunctorTheorem.McBride.iSup_centralizer_nonidentity Nat.prime_two
    hA hrank hAX hX
  rw [← hsup]
  refine iSup₂_le fun a ha => iSup_le fun hne => ?_
  have ha' : a = 1 ∨ a = r ∨ a = z ∨ a = r * z := ha
  rcases ha' with h | h | h | h
  · exact absurd h hne
  · rw [h]; exact inf_le_right.trans hNr
  · rw [h]; exact inf_le_right.trans hNz
  · rw [h]; exact inf_le_right.trans hNrz

theorem odd_core_centralizes {K : Subgroup Γ} (hK : CFSG.IsQuasisimple ↥K)
    (hKe : ¬ Odd (Nat.card ↥K)) (hON : CFSG.oddCore Γ ≤ Subgroup.normalizer (K : Set Γ)) :
    ∀ o ∈ CFSG.oddCore Γ, ∀ k ∈ K, o * k = k * o := by
  have hOn : (CFSG.oddCore Γ).Normal := inferInstance
  have hcen : ∀ g ∈ CFSG.oddCore Γ ⊓ K, ∀ k ∈ K, g * k = k * g := by
    intro g hg k hk
    have hN : ((CFSG.oddCore Γ ⊓ K).subgroupOf K).Normal := by
      rw [Subgroup.normal_subgroupOf_iff inf_le_right]
      intro h m hh hm
      exact Subgroup.mem_inf.mpr ⟨Subgroup.Normal.conj_mem hOn h (Subgroup.mem_inf.mp hh).1 m,
        K.mul_mem (K.mul_mem hm (Subgroup.mem_inf.mp hh).2) (K.inv_mem hm)⟩
    have hne : (CFSG.oddCore Γ ⊓ K).subgroupOf K ≠ ⊤ := by
      intro htop
      have hKO : K ≤ CFSG.oddCore Γ ⊓ K := Subgroup.subgroupOf_eq_top.mp htop
      have hdvd : Nat.card ↥K ∣ Nat.card ↥(CFSG.oddCore Γ) := by
        have hle : K ≤ CFSG.oddCore Γ := hKO.trans inf_le_left
        exact Subgroup.card_dvd_of_le hle
      exact hKe ((CFSG.ABGTheoremB.odd_card_oddCore Γ).of_dvd_nat hdvd)
    have hcenK := normal_le_center_or_top hK ((CFSG.oddCore Γ ⊓ K).subgroupOf K)
    have hmem : (⟨g, (Subgroup.mem_inf.mp hg).2⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rcases hcenK with h | h
      · exact h (Subgroup.mem_subgroupOf.mpr hg)
      · exact absurd h hne
    have := Subgroup.mem_center_iff.mp hmem ⟨k, hk⟩
    exact (congrArg Subtype.val this).symm
  intro o ho k hk
  have hmemK : ∀ q ∈ K, ⁅o, q⁆ ∈ CFSG.oddCore Γ ⊓ K := by
    intro q hq
    have hoN : o * q * o⁻¹ ∈ K := (Subgroup.mem_normalizer_iff.mp (hON ho) q).mp hq
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [commutatorElement_def]
      have : o * q * o⁻¹ * q⁻¹ = o * (q * o⁻¹ * q⁻¹) := by group
      rw [this]
      exact (CFSG.oddCore Γ).mul_mem ho (Subgroup.Normal.conj_mem hOn o⁻¹ ((CFSG.oddCore Γ).inv_mem ho) q)
    · rw [commutatorElement_def]
      have : o * q * o⁻¹ * q⁻¹ = (o * q * o⁻¹) * q⁻¹ := rfl
      rw [this]
      exact K.mul_mem hoN (K.inv_mem hq)
  have hcentral : ∀ q ∈ K, ∀ a ∈ K, a * ⁅o, q⁆ = ⁅o, q⁆ * a := fun q hq a ha =>
    (hcen _ (hmemK q hq) a ha).symm
  let f : ↥K →* ↥K := MonoidHom.mk' (fun q => ⟨⁅o, (q : Γ)⁆, (Subgroup.mem_inf.mp (hmemK q q.2)).2⟩)
    (by
      intro a b
      apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [commutatorElement_mul_expand]
      congr 1
      have := hcentral (b : Γ) b.2 (a : Γ) a.2
      calc (a : Γ) * ⁅o, (b : Γ)⁆ * (a : Γ)⁻¹ = ⁅o, (b : Γ)⁆ := by
            rw [this]; group)
  have hS : ∀ x ∈ (Subgroup.center ↥K : Set ↥K), ∀ y ∈ (Subgroup.center ↥K : Set ↥K),
      x * y = y * x := fun x hx y hy => (Subgroup.mem_center_iff.mp hx y).symm
  have hf : ∀ q, f q ∈ (Subgroup.center ↥K : Set ↥K) := by
    intro q
    refine Subgroup.mem_center_iff.mpr fun g => ?_
    have := hcen _ (hmemK q q.2) g.1 g.2
    exact Subtype.ext this.symm
  have htriv := hom_trivial_of_commuting_values hK.1.commutator_eq_top f _ hS hf
  have hk' : f ⟨k, hk⟩ = 1 := htriv _
  have h1 : ⁅o, k⁆ = 1 := congrArg Subtype.val hk'
  exact commutatorElement_eq_one_iff_mul_comm.mp h1

end Step2

end CFSG.Quasithin.H13.Ch4.J4KX

end

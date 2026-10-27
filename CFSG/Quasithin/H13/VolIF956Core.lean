module

public import CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices
public import CFSG.Quasithin.EmptyFaithful.S1421F112

public section

namespace CFSG.Quasithin.H13.VolI

open Subgroup

variable {G : Type*} [Group G]

theorem card_sup_mul_card_inf [Finite G] {H K : Subgroup G}
    (hHK : H ≤ normalizer (K : Set G)) :
    Nat.card (H ⊔ K : Subgroup G) * Nat.card (H ⊓ K : Subgroup G) = Nat.card H * Nat.card K := by
  set J : Subgroup G := H ⊔ K with hJ
  have hJN : J ≤ normalizer (K : Set G) := sup_le hHK le_normalizer
  have hKn : (K.subgroupOf J).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_right).mpr hJN
  have htop : H.subgroupOf J ⊔ K.subgroupOf J = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self J
  have e := Subgroup.relIndex_sup_right (H.subgroupOf J) (K.subgroupOf J)
  rw [htop, Subgroup.relIndex_top_right] at e
  have hcK : Nat.card (K.subgroupOf J) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_right).toEquiv
  have hcH : Nat.card (H.subgroupOf J) = Nat.card H :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe le_sup_left).toEquiv
  have h1 := (K.subgroupOf J).card_mul_index
  have h2 := ((K.subgroupOf J).subgroupOf (H.subgroupOf J)).card_mul_index
  have h3 : Nat.card ((K.subgroupOf J).subgroupOf (H.subgroupOf J)) =
      Nat.card (H ⊓ K : Subgroup G) := by
    let f : ((K.subgroupOf J).subgroupOf (H.subgroupOf J)) ≃ (H ⊓ K : Subgroup G) :=
      { toFun := fun x => ⟨x.1.1.1, x.1.2, x.2⟩
        invFun := fun x => ⟨⟨⟨x.1, Subgroup.mem_sup_left x.2.1⟩, x.2.1⟩, x.2.2⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    exact Nat.card_congr f
  rw [hcK] at h1
  rw [h3, hcH] at h2
  change Nat.card (H ⊓ K : Subgroup G) * (K.subgroupOf J).relIndex (H.subgroupOf J) =
    Nat.card H at h2
  rw [← e] at h2
  calc Nat.card J * Nat.card (H ⊓ K : Subgroup G)
      = (Nat.card K * (K.subgroupOf J).index) * Nat.card (H ⊓ K : Subgroup G) := by rw [h1]
    _ = Nat.card K * (Nat.card (H ⊓ K : Subgroup G) * (K.subgroupOf J).index) := by ring
    _ = Nat.card H * Nat.card K := by rw [h2, mul_comm]

theorem mem_four_cosets [Finite G] {X V₁ : Subgroup G} (hV₁X : V₁ ≤ X)
    (hcard : Nat.card X = 4 * Nat.card V₁) {e₁ e₂ : G} (he₁ : e₁ ∈ X) (he₂ : e₂ ∈ X)
    (hc : e₁ * e₂ = e₂ * e₁) (h1 : e₁ ∉ V₁) (h2 : e₂ ∉ V₁) (h12 : e₁ * e₂ ∉ V₁)
    (h21 : e₁⁻¹ * e₂ ∉ V₁) :
    ∀ x ∈ X, x ∈ V₁ ∨ e₁⁻¹ * x ∈ V₁ ∨ e₂⁻¹ * x ∈ V₁ ∨ (e₁ * e₂)⁻¹ * x ∈ V₁ := by
  classical
  set N : Subgroup X := V₁.subgroupOf X with hN
  have hNc : Nat.card N = Nat.card V₁ :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV₁X).toEquiv
  have hQ : Nat.card (X ⧸ N) = 4 := by
    have h := N.card_mul_index
    rw [hNc, hcard] at h
    have hpos : 0 < Nat.card V₁ := Nat.card_pos
    have : N.index = 4 := by
      apply Nat.eq_of_mul_eq_mul_left hpos
      rw [h, mul_comm]
    rw [← this]
    rfl
  have := Fintype.ofFinite (X ⧸ N)
  let q : X → X ⧸ N := QuotientGroup.mk
  have hq : ∀ a b : X, q a = q b ↔ (a : G)⁻¹ * b ∈ V₁ := by
    intro a b
    rw [QuotientGroup.eq]
    rfl
  let E₁ : X := ⟨e₁, he₁⟩
  let E₂ : X := ⟨e₂, he₂⟩
  have hd : ∀ a b : X, (a : G)⁻¹ * b ∉ V₁ → q a ≠ q b := fun a b h hab => h ((hq a b).1 hab)
  have d01 : q 1 ≠ q E₁ := hd 1 E₁ (by simpa using h1)
  have d02 : q 1 ≠ q E₂ := hd 1 E₂ (by simpa using h2)
  have d03 : q 1 ≠ q (E₁ * E₂) := hd 1 _ (by simpa using h12)
  have d12 : q E₁ ≠ q E₂ := hd E₁ E₂ h21
  have d13 : q E₁ ≠ q (E₁ * E₂) := hd E₁ _ (by simpa using h2)
  have d23 : q E₂ ≠ q (E₁ * E₂) := hd E₂ _ (by
    have e : (e₂ : G)⁻¹ * (e₁ * e₂) = e₁ := by rw [hc]; group
    simpa [E₁, E₂, e] using h1)
  have hcardF : ({q 1, q E₁, q E₂, q (E₁ * E₂)} : Finset (X ⧸ N)).card = 4 := by
    rw [Finset.card_insert_of_notMem (by simp [d01, d02, d03]),
      Finset.card_insert_of_notMem (by simp [d12, d13]),
      Finset.card_insert_of_notMem (by simp [d23]), Finset.card_singleton]
  have huniv : ({q 1, q E₁, q E₂, q (E₁ * E₂)} : Finset (X ⧸ N)) = Finset.univ := by
    apply Finset.eq_univ_of_card
    rw [hcardF, ← Nat.card_eq_fintype_card, hQ]
  intro x hx
  have hmem : q ⟨x, hx⟩ ∈ ({q 1, q E₁, q E₂, q (E₁ * E₂)} : Finset (X ⧸ N)) := by
    rw [huniv]
    exact Finset.mem_univ _
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  rcases hmem with h | h | h | h
  · left
    simpa using (hq 1 ⟨x, hx⟩).1 h.symm
  · right; left
    exact (hq E₁ ⟨x, hx⟩).1 h.symm
  · right; right; left
    exact (hq E₂ ⟨x, hx⟩).1 h.symm
  · right; right; right
    exact (hq (E₁ * E₂) ⟨x, hx⟩).1 h.symm

theorem comm_of_sq {a b : G} (ha : a * a = 1) (hb : b * b = 1) (hab : a * b * (a * b) = 1) :
    a * b = b * a := by
  have hai : a⁻¹ = a := inv_eq_of_mul_eq_one_right ha
  have hbi : b⁻¹ = b := inv_eq_of_mul_eq_one_right hb
  calc a * b = (a * b)⁻¹ := (inv_eq_of_mul_eq_one_right hab).symm
    _ = b * a := by rw [mul_inv_rev, hai, hbi]

theorem sq_mul_of_inv {e f : G} (he : e * e = 1) (hf : f * f = 1) :
    (e * f) ^ 2 = e * f * e⁻¹ * f⁻¹ := by
  rw [inv_eq_of_mul_eq_one_right he, inv_eq_of_mul_eq_one_right hf, sq]
  group

section Basis

variable {z : G}

theorem q8_rel (hz2 : z * z = 1) {e f m : G} (he : e * e = 1) (hf : f * f = 1)
    (hc : e * f * e⁻¹ * f⁻¹ = z)
    (hm2 : m ^ 2 = z) (hme : m * e = e * m) (hmf : m * f = f * m) :
    (e * f) ^ 4 = 1 ∧ (e * m) * (e * f) * (e * m)⁻¹ = (e * f)⁻¹ ∧ (e * m) ^ 2 = (e * f) ^ 2 := by
  have hx2 : (e * f) ^ 2 = z := by rw [sq_mul_of_inv he hf, hc]
  have hei : e⁻¹ = e := inv_eq_of_mul_eq_one_right he
  have hfi : f⁻¹ = f := inv_eq_of_mul_eq_one_right hf
  refine ⟨?_, ?_, ?_⟩
  · rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, hx2, sq, hz2]
  · have hmx : m * (e * f) = (e * f) * m := by
      rw [← mul_assoc, hme, mul_assoc, hmf, ← mul_assoc]
    calc (e * m) * (e * f) * (e * m)⁻¹ = e * (m * (e * f)) * m⁻¹ * e⁻¹ := by group
      _ = e * ((e * f) * m) * m⁻¹ * e⁻¹ := by rw [hmx]
      _ = (e * e) * f * e⁻¹ := by group
      _ = f * e := by rw [he, one_mul, hei]
      _ = (e * f)⁻¹ := by rw [mul_inv_rev, hei, hfi]
  · rw [hx2, sq]
    calc e * m * (e * m) = e * (m * e) * m := by group
      _ = e * (e * m) * m := by rw [hme]
      _ = (e * e) * (m * m) := by group
      _ = z := by rw [he, one_mul, ← sq, hm2]

theorem q8_injective (hz1 : z ≠ 1) {x y : G} (hx4 : x ^ 4 = 1) (hyx : y * x * y⁻¹ = x⁻¹)
    (hy2 : y ^ 2 = x ^ 2)
    (hx2 : x ^ 2 = z) :
    Function.Injective
      (CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift hx4 hyx hy2) := by
  rw [injective_iff_map_eq_one]
  intro q hq
  have hx1 : x ≠ 1 := fun h => hz1 (by rw [← hx2, h, one_pow])
  rcases q with k | k
  · rw [CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift_a] at hq
    fin_cases k
    · rfl
    · exfalso
      change x ^ 1 = 1 at hq
      exact hx1 (by simpa using hq)
    · exfalso
      change x ^ 2 = 1 at hq
      exact hz1 (by rw [← hx2, hq])
    · exfalso
      apply hx1
      have h3 : x ^ 3 = 1 := hq
      calc x = x ^ 4 * (x ^ 3)⁻¹ := by group
        _ = 1 := by rw [hx4, h3]; group
  · exfalso
    rw [CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift_xa] at hq
    have hy : y = (x ^ k.val)⁻¹ := eq_inv_of_mul_eq_one_left hq
    have hcomm : y * x * y⁻¹ = x := by
      rw [hy]
      group
    apply hz1
    have : x⁻¹ = x := by rw [← hyx, hcomm]
    rw [← hx2, sq]
    calc x * x = x⁻¹ * x := by rw [this]
      _ = 1 := by group

theorem isQ8Sq_of_basis [Finite G] {P : Subgroup G} (hP : Nat.card P = 32) {e₁ e₂ f₁ f₂ : G}
    (he₁P : e₁ ∈ P) (he₂P : e₂ ∈ P) (hf₁P : f₁ ∈ P) (hf₂P : f₂ ∈ P) (hz1 : z ≠ 1)
    (hz2 : z * z = 1) (hze₁ : z * e₁ = e₁ * z) (hze₂ : z * e₂ = e₂ * z)
    (he₁e : e₁ * e₁ = 1) (he₂e : e₂ * e₂ = 1) (hf₁e : f₁ * f₁ = 1) (hf₂e : f₂ * f₂ = 1)
    (hee : e₁ * e₂ = e₂ * e₁) (hff : f₁ * f₂ = f₂ * f₁)
    (h11 : e₁ * f₁ * e₁⁻¹ * f₁⁻¹ = z) (h22 : e₂ * f₂ * e₂⁻¹ * f₂⁻¹ = z)
    (h12 : e₁ * f₂ = f₂ * e₁) (h21 : e₂ * f₁ = f₁ * e₂) : IsQ8Sq ↥P := by
  have hx₁x₀ : (e₂ * f₂) * (e₁ * f₁) = (e₁ * f₁) * (e₂ * f₂) := by
    calc e₂ * f₂ * (e₁ * f₁) = e₂ * (f₂ * e₁) * f₁ := by group
      _ = e₂ * (e₁ * f₂) * f₁ := by rw [h12]
      _ = (e₂ * e₁) * (f₂ * f₁) := by group
      _ = (e₁ * e₂) * (f₁ * f₂) := by rw [hee, hff]
      _ = e₁ * (e₂ * f₁) * f₂ := by group
      _ = e₁ * (f₁ * e₂) * f₂ := by rw [h21]
      _ = e₁ * f₁ * (e₂ * f₂) := by group
  have he₁x₁ : e₁ * (e₂ * f₂) = (e₂ * f₂) * e₁ := by
    calc e₁ * (e₂ * f₂) = (e₁ * e₂) * f₂ := by group
      _ = (e₂ * e₁) * f₂ := by rw [hee]
      _ = e₂ * (e₁ * f₂) := by group
      _ = e₂ * (f₂ * e₁) := by rw [h12]
      _ = (e₂ * f₂) * e₁ := by group
  have he₂x₀ : e₂ * (e₁ * f₁) = (e₁ * f₁) * e₂ := by
    calc e₂ * (e₁ * f₁) = (e₂ * e₁) * f₁ := by group
      _ = (e₁ * e₂) * f₁ := by rw [← hee]
      _ = e₁ * (e₂ * f₁) := by group
      _ = e₁ * (f₁ * e₂) := by rw [h21]
      _ = (e₁ * f₁) * e₂ := by group
  have hf₁x₁ : (e₂ * f₂) * f₁ = f₁ * (e₂ * f₂) := by
    calc (e₂ * f₂) * f₁ = e₂ * (f₂ * f₁) := by group
      _ = e₂ * (f₁ * f₂) := by rw [← hff]
      _ = (e₂ * f₁) * f₂ := by group
      _ = (f₁ * e₂) * f₂ := by rw [h21]
      _ = f₁ * (e₂ * f₂) := by group
  have hf₂x₀ : (e₁ * f₁) * f₂ = f₂ * (e₁ * f₁) := by
    calc (e₁ * f₁) * f₂ = e₁ * (f₁ * f₂) := by group
      _ = e₁ * (f₂ * f₁) := by rw [hff]
      _ = (e₁ * f₂) * f₁ := by group
      _ = (f₂ * e₁) * f₁ := by rw [h12]
      _ = f₂ * (e₁ * f₁) := by group
  have hm₀2 : (e₂ * f₂) ^ 2 = z := by rw [sq_mul_of_inv he₂e hf₂e, h22]
  have hm₁2 : (e₁ * f₁) ^ 2 = z := by rw [sq_mul_of_inv he₁e hf₁e, h11]
  obtain ⟨hx4, hyx, hy2⟩ := q8_rel hz2 he₁e hf₁e h11 hm₀2 he₁x₁.symm hf₁x₁
  obtain ⟨hx4', hyx', hy2'⟩ := q8_rel hz2 he₂e hf₂e h22 hm₁2 he₂x₀.symm hf₂x₀
  set φ := CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift hx4 hyx hy2
    with hφ
  set ψ := CFSG.LocalAnalysis.ComponentInitial.QuaternionMatrices.quaternionLift hx4' hyx' hy2'
    with hψ
  have hφi := q8_injective hz1 hx4 hyx hy2 hm₁2
  have hψi := q8_injective hz1 hx4' hyx' hy2' hm₀2
  have hφa : ∀ k, φ (.a k) = (e₁ * f₁) ^ k.val := fun k => rfl
  have hφx : ∀ k, φ (.xa k) = (e₁ * (e₂ * f₂)) * (e₁ * f₁) ^ k.val := fun k => rfl
  have hψa : ∀ k, ψ (.a k) = (e₂ * f₂) ^ k.val := fun k => rfl
  have hψx : ∀ k, ψ (.xa k) = (e₂ * (e₁ * f₁)) * (e₂ * f₂) ^ k.val := fun k => rfl
  have hx₀P : e₁ * f₁ ∈ P := mul_mem he₁P hf₁P
  have hx₁P : e₂ * f₂ ∈ P := mul_mem he₂P hf₂P
  have hAP : φ.range ≤ P := by
    rintro _ ⟨q, rfl⟩
    rcases q with k | k
    · rw [hφa]
      exact pow_mem hx₀P _
    · rw [hφx]
      exact mul_mem (mul_mem he₁P hx₁P) (pow_mem hx₀P _)
  have hBP : ψ.range ≤ P := by
    rintro _ ⟨q, rfl⟩
    rcases q with k | k
    · rw [hψa]
      exact pow_mem hx₁P _
    · rw [hψx]
      exact mul_mem (mul_mem he₂P hx₀P) (pow_mem hx₁P _)
  have hy₀y₁ : (e₁ * (e₂ * f₂)) * (e₂ * (e₁ * f₁)) = (e₂ * (e₁ * f₁)) * (e₁ * (e₂ * f₂)) := by
    have hx₁e₂ : (e₂ * f₂) * e₂ = z * (e₂ * (e₂ * f₂)) := by
      have h := h22
      rw [inv_eq_of_mul_eq_one_right he₂e, inv_eq_of_mul_eq_one_right hf₂e] at h
      calc (e₂ * f₂) * e₂ = (e₂ * f₂ * e₂ * f₂) * f₂ := by
            rw [mul_assoc (e₂ * f₂ * e₂) f₂ f₂, hf₂e, mul_one]
        _ = z * (e₂ * (e₂ * f₂)) := by rw [h, ← mul_assoc e₂ e₂ f₂, he₂e, one_mul]
    have hx₀e₁ : (e₁ * f₁) * e₁ = z * (e₁ * (e₁ * f₁)) := by
      have h := h11
      rw [inv_eq_of_mul_eq_one_right he₁e, inv_eq_of_mul_eq_one_right hf₁e] at h
      calc (e₁ * f₁) * e₁ = (e₁ * f₁ * e₁ * f₁) * f₁ := by
            rw [mul_assoc (e₁ * f₁ * e₁) f₁ f₁, hf₁e, mul_one]
        _ = z * (e₁ * (e₁ * f₁)) := by rw [h, ← mul_assoc e₁ e₁ f₁, he₁e, one_mul]
    calc (e₁ * (e₂ * f₂)) * (e₂ * (e₁ * f₁)) = e₁ * ((e₂ * f₂) * e₂) * (e₁ * f₁) := by group
      _ = e₁ * (z * (e₂ * (e₂ * f₂))) * (e₁ * f₁) := by rw [hx₁e₂]
      _ = (e₁ * z) * e₂ * (e₂ * f₂) * (e₁ * f₁) := by group
      _ = (z * e₁) * e₂ * (e₂ * f₂) * (e₁ * f₁) := by rw [hze₁]
      _ = z * (e₁ * e₂) * ((e₂ * f₂) * (e₁ * f₁)) := by group
      _ = z * (e₂ * e₁) * ((e₁ * f₁) * (e₂ * f₂)) := by rw [hee, hx₁x₀]
      _ = (z * e₂) * (e₁ * (e₁ * f₁)) * (e₂ * f₂) := by group
      _ = (e₂ * z) * (e₁ * (e₁ * f₁)) * (e₂ * f₂) := by rw [hze₂]
      _ = e₂ * (z * (e₁ * (e₁ * f₁))) * (e₂ * f₂) := by group
      _ = e₂ * ((e₁ * f₁) * e₁) * (e₂ * f₂) := by rw [hx₀e₁]
      _ = (e₂ * (e₁ * f₁)) * (e₁ * (e₂ * f₂)) := by group
  have hx₀C : ψ.range ≤ centralizer ({e₁ * f₁} : Set G) := by
    have h1 : e₂ * f₂ ∈ centralizer ({e₁ * f₁} : Set G) := by
      rw [mem_centralizer_singleton_iff]; exact hx₁x₀
    have h2 : e₂ * (e₁ * f₁) ∈ centralizer ({e₁ * f₁} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact Commute.mul_left he₂x₀ (Commute.refl _)
    rintro _ ⟨q, rfl⟩
    rcases q with k | k
    · rw [hψa]; exact pow_mem h1 _
    · rw [hψx]; exact mul_mem h2 (pow_mem h1 _)
  have hy₀C : ψ.range ≤ centralizer ({e₁ * (e₂ * f₂)} : Set G) := by
    have h1 : e₂ * f₂ ∈ centralizer ({e₁ * (e₂ * f₂)} : Set G) := by
      rw [mem_centralizer_singleton_iff]
      exact Commute.mul_right (Commute.symm he₁x₁) (Commute.refl _)
    have h2 : e₂ * (e₁ * f₁) ∈ centralizer ({e₁ * (e₂ * f₂)} : Set G) := by
      rw [mem_centralizer_singleton_iff]; exact hy₀y₁.symm
    rintro _ ⟨q, rfl⟩
    rcases q with k | k
    · rw [hψa]; exact pow_mem h1 _
    · rw [hψx]; exact mul_mem h2 (pow_mem h1 _)
  have hAC : φ.range ≤ centralizer (ψ.range : Set G) := by
    have h1 : e₁ * f₁ ∈ centralizer (ψ.range : Set G) := by
      rw [mem_centralizer_iff]
      intro b hb
      exact (mem_centralizer_singleton_iff.mp (hx₀C hb))
    have h2 : e₁ * (e₂ * f₂) ∈ centralizer (ψ.range : Set G) := by
      rw [mem_centralizer_iff]
      intro b hb
      exact (mem_centralizer_singleton_iff.mp (hy₀C hb))
    rintro _ ⟨q, rfl⟩
    rcases q with k | k
    · rw [hφa]; exact pow_mem h1 _
    · rw [hφx]; exact mul_mem h2 (pow_mem h1 _)
  have hcomm : ∀ a ∈ φ.range, ∀ b ∈ ψ.range, a * b = b * a := fun a ha b hb =>
    (mem_centralizer_iff.mp (hAC ha) b hb).symm
  have hcenter : ∀ q : QuaternionGroup 2, (∀ r, q * r = r * q) → q = 1 ∨ q = .a 2 := by
    decide
  have hinf : φ.range ⊓ ψ.range ≤ zpowers z := by
    rintro _ ⟨⟨q, rfl⟩, hqB⟩
    have hq : ∀ r, q * r = r * q := by
      intro r
      apply hφi
      rw [map_mul, map_mul]
      exact (hcomm (φ r) ⟨r, rfl⟩ (φ q) hqB).symm
    rcases hcenter q hq with rfl | rfl
    · rw [map_one]
      exact one_mem _
    · have : φ (.a 2) = z := by rw [hφa]; exact hm₁2
      rw [this]
      exact mem_zpowers z
  have hz : Nat.card (zpowers z) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (by rw [sq]; exact hz2) hz1
  have hQ8 : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hA8 : Nat.card φ.range = 8 := by
    rw [← hQ8]
    exact Nat.card_congr (MonoidHom.ofInjective hφi).symm.toEquiv
  have hB8 : Nat.card ψ.range = 8 := by
    rw [← hQ8]
    exact Nat.card_congr (MonoidHom.ofInjective hψi).symm.toEquiv
  have hAN : φ.range ≤ normalizer (ψ.range : Set G) := by
    intro a ha
    rw [mem_normalizer_iff]
    intro b
    constructor
    · intro hb
      rw [hcomm a ha b hb, mul_inv_cancel_right]
      exact hb
    · intro hb
      have h := hcomm a ha _ hb
      have e : a * b * a⁻¹ = b := mul_left_cancel (h.trans (by group))
      exact e ▸ hb
  have h64 := card_sup_mul_card_inf hAN
  rw [hA8, hB8] at h64
  have hle2 : Nat.card ↥(φ.range ⊓ ψ.range) ≤ 2 := (card_le_of_le hinf).trans hz.le
  have hle32 : Nat.card ↥(φ.range ⊔ ψ.range) ≤ 32 :=
    (card_le_of_le (sup_le hAP hBP)).trans hP.le
  have hpos : 0 < Nat.card ↥(φ.range ⊓ ψ.range) := Nat.card_pos
  have h32 : Nat.card ↥(φ.range ⊔ ψ.range) = 32 := by
    rcases Nat.lt_or_ge (Nat.card ↥(φ.range ⊓ ψ.range)) 2 with h | h
    · have h1 : Nat.card ↥(φ.range ⊓ ψ.range) = 1 := by omega
      rw [h1] at h64
      omega
    · have h2 : Nat.card ↥(φ.range ⊓ ψ.range) = 2 := by omega
      rw [h2] at h64
      omega
  have hAB : φ.range ⊔ ψ.range = P :=
    eq_of_le_of_card_ge (sup_le hAP hBP) (by rw [hP, h32])
  refine ⟨hP, φ.range.subgroupOf P, ψ.range.subgroupOf P, ⟨?_, ?_⟩,
    ⟨(subgroupOfEquivOfLe hAP).trans (MonoidHom.ofInjective hφi).symm⟩,
    ⟨(subgroupOfEquivOfLe hBP).trans (MonoidHom.ofInjective hψi).symm⟩⟩
  · intro a ha
    rw [mem_centralizer_iff]
    intro b hb
    exact Subtype.ext (hcomm a ha b hb).symm
  · rw [← subgroupOf_sup hAP hBP, hAB, subgroupOf_self]

end Basis

structure F956Data (H V₁ X Y : Subgroup G) (z v i : G) : Prop where
  mem_V₁ : ∀ t, t ∈ V₁ ↔ t = 1 ∨ t = z
  z_ne : z ≠ 1
  z_comm : ∀ g ∈ H, z * g = g * z
  X_le : X ≤ H
  Y_le : Y ≤ H
  v_mem : v ∈ H
  i_mem : i ∈ H
  V₁_le_X : V₁ ≤ X
  V₁_le_Y : V₁ ≤ Y
  inf_le : X ⊓ Y ≤ V₁
  card_X : Nat.card X = 8
  card_Y : Nat.card Y = 8
  card_V₁ : Nat.card V₁ = 2
  sq_X : ∀ a ∈ X, a * a = 1
  sq_Y : ∀ b ∈ Y, b * b = 1
  comm_X : ∀ a ∈ X, ∀ a' ∈ X, a * a' = a' * a
  comm_Y : ∀ b ∈ Y, ∀ b' ∈ Y, b * b' = b' * b
  comm_XY : ∀ a ∈ X, ∀ b ∈ Y, a * b * a⁻¹ * b⁻¹ ∈ V₁
  v_X : ∀ a ∈ X, v * a = a * v
  i_Y : ∀ b ∈ Y, i * b = b * i
  v_Y : ∀ b ∈ Y, v * b * v⁻¹ * b⁻¹ ∈ X
  i_X : ∀ a ∈ X, i * a * i⁻¹ * a⁻¹ ∈ Y
  v_fix : ∀ b ∈ Y, v * b * v⁻¹ * b⁻¹ ∈ V₁ → b ∈ V₁
  i_fix : ∀ a ∈ X, i * a * i⁻¹ * a⁻¹ ∈ V₁ → a ∈ V₁
  nonab : ∃ a ∈ X, ∃ b ∈ Y, a * b ≠ b * a

namespace F956Data

variable {H V₁ X Y : Subgroup G} {z v i : G} (D : F956Data H V₁ X Y z v i)
include D

theorem z_mem : z ∈ V₁ := (D.mem_V₁ z).2 (Or.inr rfl)

theorem z_sq : z * z = 1 := D.sq_X z (D.V₁_le_X D.z_mem)

theorem comm_of_mem {t g : G} (ht : t ∈ V₁) (hg : g ∈ H) : t * g = g * t := by
  rcases (D.mem_V₁ t).1 ht with rfl | rfl
  · simp
  · exact D.z_comm g hg

theorem sq_of_mem {t : G} (ht : t ∈ V₁) : t * t = 1 := D.sq_X t (D.V₁_le_X ht)

theorem inv_of_mem_X {a : G} (ha : a ∈ X) : a⁻¹ = a := inv_eq_of_mul_eq_one_right (D.sq_X a ha)

theorem inv_of_mem_Y {b : G} (hb : b ∈ Y) : b⁻¹ = b := inv_eq_of_mul_eq_one_right (D.sq_Y b hb)

theorem a_comm {b : G} (hb : b ∈ Y) :
    (v * b * v⁻¹ * b⁻¹) * b = b * (v * b * v⁻¹ * b⁻¹) := by
  have hX := D.v_Y b hb
  refine comm_of_sq (D.sq_X _ hX) (D.sq_Y b hb) ?_
  have e : v * b * v⁻¹ * b⁻¹ * b * (v * b * v⁻¹ * b⁻¹ * b) = v * (b * b) * v⁻¹ := by group
  rw [e, D.sq_Y b hb]
  group

theorem b_comm {a : G} (ha : a ∈ X) :
    (i * a * i⁻¹ * a⁻¹) * a = a * (i * a * i⁻¹ * a⁻¹) := by
  have hY := D.i_X a ha
  refine comm_of_sq (D.sq_Y _ hY) (D.sq_X a ha) ?_
  have e : i * a * i⁻¹ * a⁻¹ * a * (i * a * i⁻¹ * a⁻¹ * a) = i * (a * a) * i⁻¹ := by group
  rw [e, D.sq_X a ha]
  group

theorem a_symm {b b' : G} (hb : b ∈ Y) (hb' : b' ∈ Y) :
    b * (v * b' * v⁻¹ * b'⁻¹) * b⁻¹ * (v * b' * v⁻¹ * b'⁻¹)⁻¹ =
      b' * (v * b * v⁻¹ * b⁻¹) * b'⁻¹ * (v * b * v⁻¹ * b⁻¹)⁻¹ := by
  set A := v * b * v⁻¹ * b⁻¹ with hA
  set A' := v * b' * v⁻¹ * b'⁻¹ with hA'
  have hAX : A ∈ X := D.v_Y b hb
  have hA'X : A' ∈ X := D.v_Y b' hb'
  set c₁ := b * A' * b⁻¹ * A'⁻¹ with hc₁
  set c₂ := b' * A * b'⁻¹ * A⁻¹ with hc₂
  have hc₁V : c₁ ∈ V₁ := by
    have := V₁.inv_mem (D.comm_XY A' hA'X b hb)
    have e : (A' * b * A'⁻¹ * b⁻¹)⁻¹ = b * A' * b⁻¹ * A'⁻¹ := by group
    rwa [e] at this
  have hc₂V : c₂ ∈ V₁ := by
    have := V₁.inv_mem (D.comm_XY A hAX b' hb')
    have e : (A * b' * A⁻¹ * b'⁻¹)⁻¹ = b' * A * b'⁻¹ * A⁻¹ := by group
    rwa [e] at this
  have hbA' : b * A' = c₁ * A' * b := by rw [hc₁]; group
  have hb'A : b' * A = c₂ * A * b' := by rw [hc₂]; group
  have hcomm : (A * b) * (A' * b') = (A' * b') * (A * b) := by
    have e1 : A * b = v * b * v⁻¹ := by rw [hA]; group
    have e2 : A' * b' = v * b' * v⁻¹ := by rw [hA']; group
    rw [e1, e2]
    have e3 : v * b * v⁻¹ * (v * b' * v⁻¹) = v * (b * b') * v⁻¹ := by group
    have e4 : v * b' * v⁻¹ * (v * b * v⁻¹) = v * (b' * b) * v⁻¹ := by group
    rw [e3, e4, D.comm_Y b hb b' hb']
  have hAA' : A * A' = A' * A := D.comm_X A hAX A' hA'X
  have hbb' : b * b' = b' * b := D.comm_Y b hb b' hb'
  have hAH : A ∈ H := D.X_le hAX
  have hA'H : A' ∈ H := D.X_le hA'X
  have l : (A * b) * (A' * b') = c₁ * (A * A' * (b * b')) := by
    calc (A * b) * (A' * b') = A * (b * A') * b' := by group
      _ = A * (c₁ * A' * b) * b' := by rw [hbA']
      _ = (A * c₁) * A' * b * b' := by group
      _ = (c₁ * A) * A' * b * b' := by rw [D.comm_of_mem hc₁V hAH]
      _ = c₁ * (A * A' * (b * b')) := by group
  have r : (A' * b') * (A * b) = c₂ * (A * A' * (b * b')) := by
    calc (A' * b') * (A * b) = A' * (b' * A) * b := by group
      _ = A' * (c₂ * A * b') * b := by rw [hb'A]
      _ = (A' * c₂) * A * b' * b := by group
      _ = (c₂ * A') * A * b' * b := by rw [D.comm_of_mem hc₂V hA'H]
      _ = c₂ * (A' * A * (b' * b)) := by group
      _ = c₂ * (A * A' * (b * b')) := by rw [hAA', hbb']
  rw [l, r] at hcomm
  exact mul_right_cancel hcomm

theorem comm_of_cosets {K : Subgroup G} {f₁ f₂ g : G} (hY : ∀ y ∈ K, y ∈ V₁ ∨ f₁⁻¹ * y ∈ V₁ ∨
      f₂⁻¹ * y ∈ V₁ ∨ (f₁ * f₂)⁻¹ * y ∈ V₁) (hg : g ∈ H) (h1 : g * f₁ = f₁ * g)
    (h2 : g * f₂ = f₂ * g) {y : G} (hy : y ∈ K) : g * y = y * g := by
  have key : ∀ f t : G, g * f = f * g → t ∈ V₁ → g * (f * t) = (f * t) * g := by
    intro f t hf ht
    calc g * (f * t) = (g * f) * t := by group
      _ = (f * g) * t := by rw [hf]
      _ = f * (g * t) := by group
      _ = f * (t * g) := by rw [D.comm_of_mem ht hg]
      _ = (f * t) * g := by group
  have h12 : g * (f₁ * f₂) = (f₁ * f₂) * g := by
    calc g * (f₁ * f₂) = (g * f₁) * f₂ := by group
      _ = f₁ * (g * f₂) := by rw [h1]; group
      _ = (f₁ * f₂) * g := by rw [h2]; group
  rcases hY y hy with h | h | h | h
  · exact (D.comm_of_mem h hg).symm
  · have e : y = f₁ * (f₁⁻¹ * y) := by group
    rw [e]
    exact key f₁ _ h1 h
  · have e : y = f₂ * (f₂⁻¹ * y) := by group
    rw [e]
    exact key f₂ _ h2 h
  · have e : y = (f₁ * f₂) * ((f₁ * f₂)⁻¹ * y) := by group
    rw [e]
    exact key _ _ h12 h

theorem exists_basis [Finite G] : ∃ e₁ e₂ f₁ f₂ : G, e₁ ∈ X ∧ e₂ ∈ X ∧ f₁ ∈ Y ∧ f₂ ∈ Y ∧
    e₁ * f₁ * e₁⁻¹ * f₁⁻¹ = z ∧ e₂ * f₂ * e₂⁻¹ * f₂⁻¹ = z ∧ e₁ * f₂ = f₂ * e₁ ∧
    e₂ * f₁ = f₁ * e₂ ∧ v * f₁ * v⁻¹ = e₂ * f₁ ∧ v * f₂ * v⁻¹ = e₁ * f₂ ∧
    (∀ x ∈ X, x ∈ V₁ ∨ e₁⁻¹ * x ∈ V₁ ∨ e₂⁻¹ * x ∈ V₁ ∨ (e₁ * e₂)⁻¹ * x ∈ V₁) ∧
    (∀ y ∈ Y, y ∈ V₁ ∨ f₁⁻¹ * y ∈ V₁ ∨ f₂⁻¹ * y ∈ V₁ ∨ (f₁ * f₂)⁻¹ * y ∈ V₁) := by
  have hYV : ¬ Y ≤ V₁ := fun hle => by
    have := Subgroup.card_le_of_le hle
    rw [D.card_Y, D.card_V₁] at this
    omega
  obtain ⟨f₁, hf₁Y, hf₁V⟩ := IsConcreteLE.not_le_iff_exists.mp hYV
  have hf₁1 : f₁ ≠ 1 := fun h => hf₁V (h ▸ V₁.one_mem)
  have hord : orderOf f₁ = 2 := orderOf_eq_prime (by rw [sq]; exact D.sq_Y f₁ hf₁Y) hf₁1
  have hW : Nat.card (zpowers f₁ ⊔ V₁ : Subgroup G) ≤ 4 := by
    have hN : zpowers f₁ ≤ normalizer (V₁ : Set G) := by
      rw [zpowers_le]
      apply centralizer_le_normalizer
      rw [mem_centralizer_iff]
      intro t ht
      exact D.comm_of_mem ht (D.Y_le hf₁Y)
    have h := card_sup_mul_card_inf hN
    rw [Nat.card_zpowers, hord, D.card_V₁] at h
    have hpos : 0 < Nat.card (zpowers f₁ ⊓ V₁ : Subgroup G) := Nat.card_pos
    nlinarith
  have hYW : ¬ Y ≤ zpowers f₁ ⊔ V₁ := fun hle => by
    have := Subgroup.card_le_of_le hle
    rw [D.card_Y] at this
    omega
  obtain ⟨f₂, hf₂Y, hf₂W⟩ := IsConcreteLE.not_le_iff_exists.mp hYW
  have hf₂V : f₂ ∉ V₁ := fun h => hf₂W (mem_sup_right h)
  have hf₁₂ : f₁⁻¹ * f₂ ∉ V₁ := fun h => hf₂W (by
    have e : f₂ = f₁ * (f₁⁻¹ * f₂) := by group
    rw [e]
    exact mul_mem (mem_sup_left (mem_zpowers f₁)) (mem_sup_right h))
  have hf₁i : f₁⁻¹ = f₁ := D.inv_of_mem_Y hf₁Y
  have hf₂i : f₂⁻¹ = f₂ := D.inv_of_mem_Y hf₂Y
  have hf₁f₂ : f₁ * f₂ ∉ V₁ := by rwa [← hf₁i]
  set e₂ := v * f₁ * v⁻¹ * f₁⁻¹ with he₂
  set e₁ := v * f₂ * v⁻¹ * f₂⁻¹ with he₁
  have he₂X : e₂ ∈ X := D.v_Y f₁ hf₁Y
  have he₁X : e₁ ∈ X := D.v_Y f₂ hf₂Y
  have he₂V : e₂ ∉ V₁ := fun h => hf₁V (D.v_fix f₁ hf₁Y h)
  have he₁V : e₁ ∉ V₁ := fun h => hf₂V (D.v_fix f₂ hf₂Y h)
  have he₁i : e₁⁻¹ = e₁ := D.inv_of_mem_X he₁X
  have hv₁ : v * f₁ * v⁻¹ = e₂ * f₁ := by rw [he₂]; group
  have hv₂ : v * f₂ * v⁻¹ = e₁ * f₂ := by rw [he₁]; group
  have hc₂₁ : e₂ * f₁ = f₁ * e₂ := D.a_comm hf₁Y
  have hc₁₂ : e₁ * f₂ = f₂ * e₁ := D.a_comm hf₂Y
  have hsymm : f₁ * e₁ * f₁⁻¹ * e₁⁻¹ = f₂ * e₂ * f₂⁻¹ * e₂⁻¹ := D.a_symm hf₁Y hf₂Y
  set c := f₁ * e₁ * f₁⁻¹ * e₁⁻¹ with hc
  have hcV : c ∈ V₁ := by
    have := V₁.inv_mem (D.comm_XY e₁ he₁X f₁ hf₁Y)
    have e : (e₁ * f₁ * e₁⁻¹ * f₁⁻¹)⁻¹ = f₁ * e₁ * f₁⁻¹ * e₁⁻¹ := by group
    rwa [e] at this
  have he₁e₂ : e₁ * e₂ = e₂ * e₁ := D.comm_X e₁ he₁X e₂ he₂X
  have he₁₂V : e₁ * e₂ ∉ V₁ := by
    intro h
    have hf : v * (f₁ * f₂) * v⁻¹ * (f₁ * f₂)⁻¹ = c * (e₁ * e₂) := by
      calc v * (f₁ * f₂) * v⁻¹ * (f₁ * f₂)⁻¹
          = (v * f₁ * v⁻¹) * (v * f₂ * v⁻¹) * f₂⁻¹ * f₁⁻¹ := by group
        _ = e₂ * f₁ * (e₁ * f₂) * f₂⁻¹ * f₁⁻¹ := by rw [hv₁, hv₂]
        _ = e₂ * (f₁ * e₁ * f₁⁻¹ * e₁⁻¹) * e₁ := by group
        _ = e₂ * (c * e₁) := by rw [hc]; group
        _ = (e₂ * c) * e₁ := by group
        _ = (c * e₂) * e₁ := by rw [D.comm_of_mem hcV (D.X_le he₂X)]
        _ = c * (e₁ * e₂) := by rw [mul_assoc, ← he₁e₂]
    have := D.v_fix _ (mul_mem hf₁Y hf₂Y) (hf ▸ mul_mem hcV h)
    exact hf₁f₂ this
  have he₁₂V' : e₁⁻¹ * e₂ ∉ V₁ := by rwa [he₁i]
  have hXc := mem_four_cosets D.V₁_le_X (by rw [D.card_X, D.card_V₁]) he₁X he₂X he₁e₂ he₁V he₂V
    he₁₂V he₁₂V'
  have hYc := mem_four_cosets D.V₁_le_Y (by rw [D.card_Y, D.card_V₁]) hf₁Y hf₂Y
    (D.comm_Y f₁ hf₁Y f₂ hf₂Y) hf₁V hf₂V hf₁f₂ hf₁₂
  have hc1 : c ≠ 1 := by
    intro hc1
    obtain ⟨a, ha, b, hb, hab⟩ := D.nonab
    have h11 : e₁ * f₁ = f₁ * e₁ := by
      have : f₁ * e₁ * f₁⁻¹ * e₁⁻¹ = 1 := hc1
      have e : f₁ * e₁ = (f₁ * e₁ * f₁⁻¹ * e₁⁻¹) * (e₁ * f₁) := by group
      rw [e, this, one_mul]
    have h22 : e₂ * f₂ = f₂ * e₂ := by
      have : f₂ * e₂ * f₂⁻¹ * e₂⁻¹ = 1 := hsymm ▸ hc1
      have e : f₂ * e₂ = (f₂ * e₂ * f₂⁻¹ * e₂⁻¹) * (e₂ * f₂) := by group
      rw [e, this, one_mul]
    have he₁Y : ∀ y ∈ Y, e₁ * y = y * e₁ := fun y hy =>
      D.comm_of_cosets hYc (D.X_le he₁X) h11 hc₁₂ hy
    have he₂Y : ∀ y ∈ Y, e₂ * y = y * e₂ := fun y hy =>
      D.comm_of_cosets hYc (D.X_le he₂X) hc₂₁ h22 hy
    apply hab
    have hb' : b * e₁ = e₁ * b ∧ b * e₂ = e₂ * b := ⟨(he₁Y b hb).symm, (he₂Y b hb).symm⟩
    exact (D.comm_of_cosets hXc (D.Y_le hb) hb'.1 hb'.2 ha).symm
  have hcz : c = z := ((D.mem_V₁ c).1 hcV).resolve_left hc1
  have hzi : z⁻¹ = z := inv_eq_of_mul_eq_one_right D.z_sq
  refine ⟨e₁, e₂, f₁, f₂, he₁X, he₂X, hf₁Y, hf₂Y, ?_, ?_, hc₁₂, hc₂₁, hv₁, hv₂, hXc, hYc⟩
  · have e : e₁ * f₁ * e₁⁻¹ * f₁⁻¹ = c⁻¹ := by rw [hc]; group
    rw [e, hcz, hzi]
  · have e : e₂ * f₂ * e₂⁻¹ * f₂⁻¹ = (f₂ * e₂ * f₂⁻¹ * e₂⁻¹)⁻¹ := by group
    rw [e, ← hsymm, hcz, hzi]

theorem not_mem_of_comm_eq {x y : G} (hy : y ∈ H) (h : x * y * x⁻¹ * y⁻¹ = z) :
    x ∉ V₁ := by
  intro hxV
  apply D.z_ne
  rw [← h, D.comm_of_mem hxV hy]
  group

theorem not_mem_of_comm_eq' {x y : G} (hx : x ∈ H) (h : x * y * x⁻¹ * y⁻¹ = z) :
    y ∉ V₁ := by
  intro hyV
  apply D.z_ne
  rw [← h, ← D.comm_of_mem hyV hx]
  group

theorem b_basis {e₁ e₂ f₁ f₂ : G} (he₁ : e₁ ∈ X) (he₂ : e₂ ∈ X) (hf₁ : f₁ ∈ Y) (hf₂ : f₂ ∈ Y)
    (h11 : e₁ * f₁ * e₁⁻¹ * f₁⁻¹ = z) (h22 : e₂ * f₂ * e₂⁻¹ * f₂⁻¹ = z)
    (h12 : e₁ * f₂ = f₂ * e₁) (h21 : e₂ * f₁ = f₁ * e₂)
    (hY : ∀ y ∈ Y, y ∈ V₁ ∨ f₁⁻¹ * y ∈ V₁ ∨ f₂⁻¹ * y ∈ V₁ ∨ (f₁ * f₂)⁻¹ * y ∈ V₁) :
    f₂⁻¹ * (i * e₁ * i⁻¹ * e₁⁻¹) ∈ V₁ ∧ f₁⁻¹ * (i * e₂ * i⁻¹ * e₂⁻¹) ∈ V₁ := by
  have hz : ∀ {e f : G}, e ∈ X → f ∈ Y → e * f * e⁻¹ * f⁻¹ = z → e * f ≠ f * e := by
    intro e f he hf h hc
    apply D.z_ne
    rw [← h, hc]
    group
  have hcancel : ∀ {e f t : G}, e ∈ X → f ∈ H → t ∈ V₁ → e * (f * t) = (f * t) * e →
      e * f = f * e := by
    intro e f t he hf ht h
    have h' : e * f * t = f * e * t := by
      calc e * f * t = e * (f * t) := by group
        _ = (f * t) * e := h
        _ = f * (t * e) := by group
        _ = f * (e * t) := by rw [D.comm_of_mem ht (D.X_le he)]
        _ = f * e * t := by group
    exact mul_right_cancel h'
  have key : ∀ {e f f' : G}, e ∈ X → f ∈ Y → f' ∈ Y → e * f * e⁻¹ * f⁻¹ = z →
      e * f' = f' * e →
      (∀ y ∈ Y, y ∈ V₁ ∨ f⁻¹ * y ∈ V₁ ∨ f'⁻¹ * y ∈ V₁ ∨ (f * f')⁻¹ * y ∈ V₁) →
      f'⁻¹ * (i * e * i⁻¹ * e⁻¹) ∈ V₁ := by
    intro e f f' he hf hf' hef hef' hYc
    set β := i * e * i⁻¹ * e⁻¹ with hβ
    have hβY : β ∈ Y := D.i_X e he
    have hβV : β ∉ V₁ := fun h => (D.not_mem_of_comm_eq (D.Y_le hf) hef) (D.i_fix e he h)
    have hβc : β * e = e * β := D.b_comm he
    rcases hYc β hβY with h | h | h | h
    · exact absurd h hβV
    · exfalso
      apply hz he hf hef
      have e1 : β = f * (f⁻¹ * β) := by group
      have := hβc.symm
      rw [e1] at this
      exact hcancel he (D.Y_le hf) h this
    · exact h
    · exfalso
      apply hz he hf hef
      have e1 : β = (f * f') * ((f * f')⁻¹ * β) := by group
      have := hβc.symm
      rw [e1] at this
      have h2 := hcancel he (mul_mem (D.Y_le hf) (D.Y_le hf')) h this
      have h3 : e * f * f' = f * e * f' := by
        calc e * f * f' = e * (f * f') := by group
          _ = (f * f') * e := h2
          _ = f * (f' * e) := by group
          _ = f * (e * f') := by rw [hef']
          _ = f * e * f' := by group
      exact mul_right_cancel h3
  refine ⟨key he₁ hf₁ hf₂ h11 h12 hY, key he₂ hf₂ hf₁ h22 h21 ?_⟩
  intro y hy
  rcases hY y hy with h | h | h | h
  · exact Or.inl h
  · exact Or.inr (Or.inr (Or.inl h))
  · exact Or.inr (Or.inl h)
  · refine Or.inr (Or.inr (Or.inr ?_))
    rwa [D.comm_Y f₁ hf₁ f₂ hf₂] at h

theorem cube_cycle {w e f t : G} (hw : w ∈ H) (he : e ∈ H) (hf : f ∈ H) (ht : t ∈ V₁)
    (hwe : w * e * w⁻¹ = f * t) (hwf : w * f * w⁻¹ = e * f) (hef : e * f = f * e)
    (hff : f * f = 1) :
    w ^ 3 * e = e * w ^ 3 ∧ w ^ 3 * f = f * w ^ 3 := by
  have htt : t * t = 1 := D.sq_of_mem ht
  have hwt : w * t * w⁻¹ = t := by
    rw [← D.comm_of_mem ht hw]
    group
  have hte : t * e = e * t := D.comm_of_mem ht he
  have htf : t * f = f * t := D.comm_of_mem ht hf
  have hconj : ∀ g : G, w ^ 3 * g * (w ^ 3)⁻¹ = w * (w * (w * g * w⁻¹) * w⁻¹) * w⁻¹ := by
    intro g
    rw [pow_three]
    group
  have hfef : f * e * f = e := by rw [← hef, mul_assoc, hff, mul_one]
  have s2 : w * (f * t) * w⁻¹ = e * f * t := by
    calc w * (f * t) * w⁻¹ = (w * f * w⁻¹) * (w * t * w⁻¹) := by group
      _ = e * f * t := by rw [hwf, hwt]
  have s3 : w * (e * f * t) * w⁻¹ = e := by
    calc w * (e * f * t) * w⁻¹ = (w * e * w⁻¹) * (w * f * w⁻¹) * (w * t * w⁻¹) := by group
      _ = f * t * (e * f) * t := by rw [hwe, hwf, hwt]
      _ = f * (t * e) * f * t := by group
      _ = f * (e * t) * f * t := by rw [hte]
      _ = f * e * (t * f) * t := by group
      _ = f * e * (f * t) * t := by rw [htf]
      _ = (f * e * f) * (t * t) := by group
      _ = e := by rw [hfef, htt, mul_one]
  have s4 : w * (e * f) * w⁻¹ = t * e := by
    calc w * (e * f) * w⁻¹ = (w * e * w⁻¹) * (w * f * w⁻¹) := by group
      _ = f * t * (e * f) := by rw [hwe, hwf]
      _ = t * (f * e * f) := by rw [show f * t = t * f from htf.symm]; group
      _ = t * e := by rw [hfef]
  have s5 : w * (t * e) * w⁻¹ = f := by
    calc w * (t * e) * w⁻¹ = (w * t * w⁻¹) * (w * e * w⁻¹) := by group
      _ = t * (f * t) := by rw [hwt, hwe]
      _ = (t * f) * t := by group
      _ = (f * t) * t := by rw [htf]
      _ = f * (t * t) := by group
      _ = f := by rw [htt, mul_one]
  have h1 : w ^ 3 * e * (w ^ 3)⁻¹ = e := by rw [hconj, hwe, s2, s3]
  have h2 : w ^ 3 * f * (w ^ 3)⁻¹ = f := by rw [hconj, hwf, s4, s5]
  constructor
  · calc w ^ 3 * e = (w ^ 3 * e * (w ^ 3)⁻¹) * w ^ 3 := by group
      _ = e * w ^ 3 := by rw [h1]
  · calc w ^ 3 * f = (w ^ 3 * f * (w ^ 3)⁻¹) * w ^ 3 := by group
      _ = f * w ^ 3 := by rw [h2]

theorem cube_comm [Finite G] {u : G} (hu : u ∈ X ⊔ Y) : (v * i) ^ 3 * u = u * (v * i) ^ 3 := by
  obtain ⟨e₁, e₂, f₁, f₂, he₁, he₂, hf₁, hf₂, h11, h22, h12, h21, hv₁, hv₂, hX, hY⟩ :=
    D.exists_basis
  obtain ⟨hb₁, hb₂⟩ := D.b_basis he₁ he₂ hf₁ hf₂ h11 h22 h12 h21 hY
  have hwH : v * i ∈ H := mul_mem D.v_mem D.i_mem
  have hve : ∀ e ∈ X, v * e * v⁻¹ = e := fun e he => by rw [D.v_X e he]; group
  have hwf : ∀ f ∈ Y, v * i * f * (v * i)⁻¹ = v * f * v⁻¹ := fun f hf => by
    have : i * f * i⁻¹ = f := by rw [D.i_Y f hf]; group
    calc v * i * f * (v * i)⁻¹ = v * (i * f * i⁻¹) * v⁻¹ := by group
      _ = v * f * v⁻¹ := by rw [this]
  have hwe : ∀ {e f : G}, e ∈ X → f ∈ Y → f⁻¹ * (i * e * i⁻¹ * e⁻¹) ∈ V₁ →
      e * f = f * e → v * f * v⁻¹ = e * f →
      v * i * e * (v * i)⁻¹ = f * (f⁻¹ * (i * e * i⁻¹ * e⁻¹)) := by
    intro e f he hf hb hef hvf
    set t := f⁻¹ * (i * e * i⁻¹ * e⁻¹) with ht
    have hie : i * e * i⁻¹ = f * t * e := by rw [ht]; group
    have hvt : v * t * v⁻¹ = t := by rw [← D.comm_of_mem hb D.v_mem]; group
    have hee : e * e = 1 := D.sq_X e he
    calc v * i * e * (v * i)⁻¹ = v * (i * e * i⁻¹) * v⁻¹ := by group
      _ = v * (f * t * e) * v⁻¹ := by rw [hie]
      _ = (v * f * v⁻¹) * (v * t * v⁻¹) * (v * e * v⁻¹) := by group
      _ = e * f * t * e := by rw [hvf, hvt, hve e he]
      _ = e * f * (e * t) := by rw [mul_assoc (e * f) t e, D.comm_of_mem hb (D.X_le he)]
      _ = (e * f * e) * t := by group
      _ = f * t := by rw [hef, mul_assoc f e e, hee, mul_one]
  have hc₁ := D.cube_cycle hwH (D.X_le he₁) (D.Y_le hf₂) hb₁ (hwe he₁ hf₂ hb₁ h12 hv₂)
    (by rw [hwf f₂ hf₂, hv₂]) h12 (D.sq_Y f₂ hf₂)
  have hc₂ := D.cube_cycle hwH (D.X_le he₂) (D.Y_le hf₁) hb₂ (hwe he₂ hf₁ hb₂ h21 hv₁)
    (by rw [hwf f₁ hf₁, hv₁]) h21 (D.sq_Y f₁ hf₁)
  have hw3H : (v * i) ^ 3 ∈ H := pow_mem hwH 3
  have hXc : X ≤ centralizer ({(v * i) ^ 3} : Set G) := fun x hx => by
    rw [mem_centralizer_singleton_iff]
    exact (D.comm_of_cosets hX hw3H hc₁.1 hc₂.1 hx).symm
  have hYc : Y ≤ centralizer ({(v * i) ^ 3} : Set G) := fun y hy => by
    rw [mem_centralizer_singleton_iff]
    exact (D.comm_of_cosets hY hw3H hc₂.2 hc₁.2 hy).symm
  exact (mem_centralizer_singleton_iff.mp ((sup_le hXc hYc) hu)).symm

theorem card_sup [Finite G] : Nat.card (X ⊔ Y : Subgroup G) = 32 := by
  have hfw : ∀ x ∈ X, ∀ y ∈ Y, x * y * x⁻¹ ∈ Y := by
    intro x hx y hy
    have hc := D.comm_XY x hx y hy
    have e : x * y * x⁻¹ = (x * y * x⁻¹ * y⁻¹) * y := by group
    rw [e]
    exact mul_mem (D.V₁_le_Y hc) hy
  have hN : X ≤ normalizer (Y : Set G) := by
    intro x hx
    rw [mem_normalizer_iff]
    intro y
    refine ⟨fun hy => hfw x hx y hy, fun hy => ?_⟩
    have := hfw x⁻¹ (inv_mem hx) _ hy
    simpa [mul_assoc] using this
  have hinf : X ⊓ Y = V₁ := le_antisymm D.inf_le (le_inf D.V₁_le_X D.V₁_le_Y)
  have h := card_sup_mul_card_inf hN
  rw [hinf, D.card_X, D.card_Y, D.card_V₁] at h
  omega

theorem isQ8Sq [Finite G] : IsQ8Sq ↥(X ⊔ Y) := by
  obtain ⟨e₁, e₂, f₁, f₂, he₁, he₂, hf₁, hf₂, h11, h22, h12, h21, -, -, -, -⟩ := D.exists_basis
  exact isQ8Sq_of_basis D.card_sup (mem_sup_left he₁) (mem_sup_left he₂) (mem_sup_right hf₁)
    (mem_sup_right hf₂) D.z_ne D.z_sq (D.z_comm e₁ (D.X_le he₁)) (D.z_comm e₂ (D.X_le he₂))
    (D.sq_X e₁ he₁) (D.sq_X e₂ he₂) (D.sq_Y f₁ hf₁) (D.sq_Y f₂ hf₂) (D.comm_X e₁ he₁ e₂ he₂)
    (D.comm_Y f₁ hf₁ f₂ hf₂) h11 h22 h12 h21

end F956Data

end CFSG.Quasithin.H13.VolI

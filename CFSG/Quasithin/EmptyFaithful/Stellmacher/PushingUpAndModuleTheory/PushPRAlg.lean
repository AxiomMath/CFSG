module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushPRBase

public section

namespace CFSG.Quasithin.F53Push

open scoped commutatorElement

variable {G : Type*} [Group G]

theorem decomp_left {P Q Q' Z : Subgroup G} (hQP : Q ≤ P) (hZQ : Z ≤ Q) (hZP : Z ≤ P)
    (hPQ' : P ≤ Subgroup.normalizer (Q' : Set G)) (hP1 : P ≤ Q' ⊔ Z) {a : G} (ha : a ∈ Q) :
    ∃ r ∈ Q ⊓ Q', ∃ z ∈ Z, a = r * z := by
  obtain ⟨n, hn, k, hk, hnk⟩ := mem_sup_of_le_normalizer (fun x hx => hPQ' (hZP hx))
    (hP1 (hQP ha))
  refine ⟨n, ⟨?_, hn⟩, k, hk, hnk⟩
  have : n = a * k⁻¹ := by rw [hnk]; group
  rw [this]
  exact Q.mul_mem ha (Q.inv_mem (hZQ hk))

theorem decomp_right {P Q Q' Z' : Subgroup G} (hQ'P : Q' ≤ P) (hZ'Q' : Z' ≤ Q') (hZ'P : Z' ≤ P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hP2 : P ≤ Q ⊔ Z') {b : G} (hb : b ∈ Q') :
    ∃ r ∈ Q ⊓ Q', ∃ z ∈ Z', b = r * z := by
  obtain ⟨n, hn, k, hk, hnk⟩ := mem_sup_of_le_normalizer (fun x hx => hPQ (hZ'P hx))
    (hP2 (hQ'P hb))
  refine ⟨n, ⟨hn, ?_⟩, k, hk, hnk⟩
  have : n = b * k⁻¹ := by rw [hnk]; group
  rw [this]
  exact Q'.mul_mem hb (Q'.inv_mem (hZ'Q' hk))

theorem commutator_decomp {Q Q' Z Z' : Subgroup G}
    (hZc : ∀ z ∈ Z, ∀ a ∈ Q, z * a = a * z) (hZ'c : ∀ z ∈ Z', ∀ a ∈ Q', z * a = a * z)
    (hcZ : ∀ z ∈ Z, ∀ b ∈ Z', ⁅z, b⁆ ∈ Z) {r z b : G} (hr : r ∈ Q ⊓ Q') (hz : z ∈ Z)
    (hb : b ∈ Z') : ⁅r * z, b⁆ = ⁅z, b⁆ := by
  have hbr : b * r⁻¹ * b⁻¹ = r⁻¹ := by
    have := hZ'c b hb r⁻¹ (Q'.inv_mem hr.2)
    rw [this]; group
  have hrc : ⁅z, b⁆ * r = r * ⁅z, b⁆ := hZc _ (hcZ z hz b hb) r hr.1
  calc ⁅r * z, b⁆ = r * (z * b * z⁻¹ * b⁻¹) * (b * r⁻¹ * b⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = r * ⁅z, b⁆ * r⁻¹ := by rw [hbr]; rfl
    _ = ⁅z, b⁆ := by rw [← hrc]; group

theorem pr_alg {P Q Q' Z Z' : Subgroup G}
    (hQP : Q ≤ P) (hQ'P : Q' ≤ P)
    (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hPQ' : P ≤ Subgroup.normalizer (Q' : Set G))
    (hZQ : Z ≤ Q) (hZ'Q' : Z' ≤ Q') (hZP : Z ≤ P) (hZ'P : Z' ≤ P)
    (hZc : ∀ z ∈ Z, ∀ a ∈ Q, z * a = a * z) (hZ'c : ∀ z ∈ Z', ∀ a ∈ Q', z * a = a * z)
    (hZe : ∀ z ∈ Z, z * z = 1) (hZ'e : ∀ z ∈ Z', z * z = 1)
    (hP1 : P ≤ Q' ⊔ Z) (hP2 : P ≤ Q ⊔ Z')
    (hcZ : ∀ z ∈ Z, ∀ b ∈ Z', ⁅z, b⁆ ∈ Z)
    (hG : ∀ z ∈ Z, z ∉ Q' → ∀ b ∈ Z', b ∉ Q → ⁅z, b⁆ ∉ phi Q) :
    phi Q' = phi Q ∧ ∀ E : Subgroup G, E ≤ P → (∀ x ∈ E, x * x ∈ phi Q) → E ≤ Q ∨ E ≤ Q' := by
  have hR'Q : Q ⊓ Q' ≤ Q := inf_le_left
  have hR'Q' : Q ⊓ Q' ≤ Q' := inf_le_right
  have h1 : phi Q = phi (Q ⊓ Q') :=
    phi_eq_of_decomp hR'Q hZQ hZc hZe (fun a ha => decomp_left hQP hZQ hZP hPQ' hP1 ha)
  have h2 : phi Q' = phi (Q ⊓ Q') :=
    phi_eq_of_decomp hR'Q' hZ'Q' hZ'c hZ'e
      (fun b hb => decomp_right hQ'P hZ'Q' hZ'P hPQ hP2 hb)
  refine ⟨h2.trans h1.symm, fun E hEP hsq => ?_⟩
  refine le_or_le_of_forall_mem fun e he => ?_
  obtain ⟨a, ha, b, hb, hab⟩ := mem_sup_of_le_normalizer (fun x hx => hPQ (hZ'P hx))
    (hP2 (hEP he))
  by_cases hbQ : b ∈ Q
  · left
    rw [hab]; exact Q.mul_mem ha hbQ
  by_cases haQ' : a ∈ Q'
  · right
    rw [hab]; exact Q'.mul_mem haQ' (hZ'Q' hb)
  exfalso
  obtain ⟨r, hr, z, hz, rfl⟩ := decomp_left hQP hZQ hZP hPQ' hP1 ha
  have hzQ' : z ∉ Q' := fun hzQ' => haQ' (Q'.mul_mem hr.2 hzQ')
  have hcomm := commutator_decomp hZc hZ'c hcZ hr hz hb
  have hnot := hG z hz hzQ' b hb hbQ
  apply hnot
  rw [← hcomm]
  have hsqe := hsq e he
  have hbn : b ∈ Subgroup.normalizer (Q : Set G) := hPQ (hZ'P hb)
  have hconj : b * (r * z * (r * z)) * b⁻¹ ∈ phi Q := conj_mem_phi hbn (sq_mem_phi ha)
  have hbb : b * b = 1 := hZ'e b hb
  have e1 : ⁅r * z, b⁆ = e * e * (b * (r * z * (r * z)) * b⁻¹)⁻¹ := by
    have hm : b * (r * z * (r * z)) * b⁻¹ = b * (r * z * (r * z)) * b := by
      calc b * (r * z * (r * z)) * b⁻¹ = b * (r * z * (r * z)) * b⁻¹ * (b * b) := by
            rw [hbb, mul_one]
        _ = b * (r * z * (r * z)) * b := by group
    rw [hm, hab]
    simp only [commutatorElement_def]
    group
  rw [e1]
  exact Subgroup.mul_mem _ hsqe (Subgroup.inv_mem _ hconj)

end CFSG.Quasithin.F53Push

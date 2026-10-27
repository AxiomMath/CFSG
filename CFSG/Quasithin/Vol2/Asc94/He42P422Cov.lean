module

public import CFSG.Quasithin.Vol2.Asc94.He42Spec
public import CFSG.Quasithin.Vol2.Asc94.He42BaseFacts

public section

namespace CFSG.Quasithin.A94.He42

open Subgroup

variable {G : Type} [Group G] [Finite G]

namespace HeSetup

variable (S : HeSetup G)

@[expose] def conjZ_422 (g : G) : Subgroup G := S.Z.map (MulAut.conj g).toMonoidHom

theorem mem_conjZ_422 {g x : G} : x ∈ S.conjZ_422 g ↔ ∃ z ∈ S.Z, g * z * g⁻¹ = x := by
  simp only [conjZ_422, Subgroup.mem_map, MulAut.conj_apply, MulEquiv.coe_toMonoidHom]

theorem card_conjZ_422 (g : G) : Nat.card ↥(S.conjZ_422 g) = 16 := by
  have hB := S.baseFacts
  rw [conjZ_422, Subgroup.card_map_of_injective (MulAut.conj g).injective, hB.card_Z]

theorem pair_422 (hSp : ∀ g ∈ S.L2, g ∉ S.K → ∀ z ∈ S.Z, g * z * g⁻¹ ∈ S.Z → z ∈ S.B)
    {g₁ g₂ x : G} (h₁ : g₁ ∈ S.L2) (h₂ : g₂ ∈ S.L2)
    (hx₁ : x ∈ S.conjZ_422 g₁) (hx₂ : x ∈ S.conjZ_422 g₂) (hxB : x ∉ S.B) : g₂⁻¹ * g₁ ∈ S.K := by
  have hB := S.baseFacts
  by_contra hK
  obtain ⟨z₁, hz₁, rfl⟩ := (mem_conjZ_422 S).mp hx₁
  obtain ⟨z₂, hz₂, hzz⟩ := (mem_conjZ_422 S).mp hx₂
  have hL : g₂⁻¹ * g₁ ∈ S.L2 := S.L2.mul_mem (S.L2.inv_mem h₂) h₁
  have hcz : g₂⁻¹ * g₁ * z₁ * (g₂⁻¹ * g₁)⁻¹ = z₂ := by
    calc g₂⁻¹ * g₁ * z₁ * (g₂⁻¹ * g₁)⁻¹ = g₂⁻¹ * (g₁ * z₁ * g₁⁻¹) * g₂ := by group
      _ = g₂⁻¹ * (g₂ * z₂ * g₂⁻¹) * g₂ := by rw [hzz]
      _ = z₂ := by group
  have hz2 : g₂⁻¹ * g₁ * z₁ * (g₂⁻¹ * g₁)⁻¹ ∈ S.Z := by rw [hcz]; exact hz₂
  have hz1B : z₁ ∈ S.B := hSp (g₂⁻¹ * g₁) hL hK z₁ hz₁ hz2
  have hcomm : g₁ * z₁ = z₁ * g₁ :=
    (mem_centralizer_iff.mp (hB.L2_le_centralizer h₁) z₁ hz1B).symm
  have hconj : g₁ * z₁ * g₁⁻¹ = z₁ := (mul_inv_eq_iff_eq_mul).2 hcomm
  apply hxB
  rw [hconj]
  exact hz1B

theorem covering_422 (hSp : ∀ g ∈ S.L2, g ∉ S.K → ∀ z ∈ S.Z, g * z * g⁻¹ ∈ S.Z → z ∈ S.B)
    {c : G} (hcA : c ∈ S.A') (hcB : c ∉ S.B) : ∃ g ∈ S.L2, c ∈ S.conjZ_422 g := by
  classical
  haveI : Fintype G := Fintype.ofFinite G
  have hB := S.baseFacts
  let K' : Subgroup ↥S.L2 := S.K.subgroupOf S.L2
  haveI : Fintype (↥S.L2 ⧸ K') := Fintype.ofFinite _
  have hQ : Fintype.card (↥S.L2 ⧸ K') = 5 := by
    rw [← Nat.card_eq_fintype_card]
    exact hB.relIndex_K_L2
  let rep : (↥S.L2 ⧸ K') → G := fun q => ((Quotient.out q : ↥S.L2) : G)
  have hrep_mem : ∀ q, rep q ∈ S.L2 := fun q => (Quotient.out q : ↥S.L2).2
  have hrep_eq : ∀ q q' : ↥S.L2 ⧸ K', (rep q')⁻¹ * rep q ∈ S.K → q = q' := by
    intro q q' h
    have h2 : (Quotient.out q : ↥S.L2)⁻¹ * (Quotient.out q' : ↥S.L2) ∈ K' := by
      rw [Subgroup.mem_subgroupOf]
      have h3 := S.K.inv_mem h
      simpa only [mul_inv_rev, inv_inv, Subgroup.coe_mul, Subgroup.coe_inv, rep] using h3
    calc q = QuotientGroup.mk (Quotient.out q : ↥S.L2) := (Quotient.out_eq q).symm
      _ = QuotientGroup.mk (Quotient.out q' : ↥S.L2) := QuotientGroup.eq.2 h2
      _ = q' := Quotient.out_eq q'
  let T : (↥S.L2 ⧸ K') → Finset G := fun q =>
    Finset.univ.filter (fun x : G => x ∈ S.conjZ_422 (rep q) ∧ x ∉ S.B)
  have hfilter_card : ∀ H : Subgroup G, (Finset.univ.filter (fun x : G => x ∈ H)).card = Nat.card ↥H := by
    intro H
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have hT_card : ∀ q, (T q).card = 12 := by
    intro q
    have hg := hrep_mem q
    have hBle : S.B ≤ S.conjZ_422 (rep q) := by
      intro b hb
      have hbZ : b ∈ S.Z := (Subgroup.mem_inf.mp hb).1
      have hcomm : b * rep q = rep q * b := mem_centralizer_iff.mp (hB.L2_le_centralizer hg) b hb
      exact (mem_conjZ_422 S).mpr ⟨b, hbZ, (mul_inv_eq_iff_eq_mul).2 hcomm.symm⟩
    have hsub : (Finset.univ.filter (fun x : G => x ∈ S.B)) ⊆
        (Finset.univ.filter (fun x : G => x ∈ S.conjZ_422 (rep q))) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact hBle hx
    have e : T q = (Finset.univ.filter (fun x : G => x ∈ S.conjZ_422 (rep q))) \
        (Finset.univ.filter (fun x : G => x ∈ S.B)) := by
      ext x
      simp only [T, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    rw [e, Finset.card_sdiff_of_subset hsub, hfilter_card, hfilter_card, card_conjZ_422 S,
      hB.card_B]
  have hdisj : ∀ q q' : ↥S.L2 ⧸ K', q ≠ q' → Disjoint (T q) (T q') := by
    intro q q' hne
    rw [Finset.disjoint_left]
    intro x hx hx'
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hx hx'
    apply hne
    apply hrep_eq q q'
    exact pair_422 S hSp (hrep_mem q) (hrep_mem q') hx.1 hx'.1 hx.2
  have hU_card : (Finset.univ.biUnion T).card = 60 := by
    rw [Finset.card_biUnion]
    · simp only [hT_card, Finset.sum_const, Finset.card_univ, hQ, smul_eq_mul]
    · intro q _ q' _ hne
      exact hdisj q q' hne
  have hUsub : Finset.univ.biUnion T ⊆ Finset.univ.filter (fun x : G => x ∈ S.A' ∧ x ∉ S.B) := by
    intro x hx
    obtain ⟨q, -, hxq⟩ := Finset.mem_biUnion.mp hx
    simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hxq ⊢
    refine ⟨?_, hxq.2⟩
    obtain ⟨z, hz, rfl⟩ := (mem_conjZ_422 S).mp hxq.1
    have hn := Subgroup.mem_normalizer_iff.mp (hB.L2_le_normalizer (hrep_mem q)) z
    exact hn.mp (Subgroup.mem_inf.mp hz).2
  have hA'B : (Finset.univ.filter (fun x : G => x ∈ S.A' ∧ x ∉ S.B)).card = 60 := by
    have hsub : (Finset.univ.filter (fun x : G => x ∈ S.B)) ⊆
        (Finset.univ.filter (fun x : G => x ∈ S.A')) := by
      intro x hx
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hx ⊢
      exact (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hx).1).2
    have e : (Finset.univ.filter (fun x : G => x ∈ S.A' ∧ x ∉ S.B)) =
        (Finset.univ.filter (fun x : G => x ∈ S.A')) \
          (Finset.univ.filter (fun x : G => x ∈ S.B)) := by
      ext x
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_sdiff]
    rw [e, Finset.card_sdiff_of_subset hsub, hfilter_card, hfilter_card, hB.card_A', hB.card_B]
  have heq := Finset.eq_of_subset_of_card_le hUsub (by rw [hU_card, hA'B])
  have hc : c ∈ Finset.univ.filter (fun x : G => x ∈ S.A' ∧ x ∉ S.B) :=
    Finset.mem_filter.mpr ⟨Finset.mem_univ _, hcA, hcB⟩
  rw [← heq] at hc
  obtain ⟨q, -, hcq⟩ := Finset.mem_biUnion.mp hc
  simp only [T, Finset.mem_filter, Finset.mem_univ, true_and] at hcq
  exact ⟨rep q, hrep_mem q, hcq.1⟩

end HeSetup

end CFSG.Quasithin.A94.He42

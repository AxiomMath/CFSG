module

public import CFSG.Quasithin.EmptyFaithfulMultiple.Lemma15418Inspection
public import CFSG.Quasithin.Background.F6Cat

public section

namespace CFSG.Quasithin.EmptyFaithfulMultiple

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open scoped commutatorElement

namespace Insp15418

@[expose] def CommInf {D : Type*} [Group D] (H₁ H₂ : Subgroup D) : Prop :=
  ∀ x ∈ H₁ ⊓ H₂, ∀ y ∈ H₁ ⊓ H₂, x * y = y * x

theorem commInf_comm {D : Type*} [Group D] {H₁ H₂ : Subgroup D} :
    CommInf H₁ H₂ ↔ CommInf H₂ H₁ := by
  unfold CommInf
  rw [inf_comm]

theorem mul_comm_of_card_dvd_four {P : Type*} [Group P] (hP : IsPGroup 2 P)
    (h4 : Nat.card P ∣ 4) (a b : P) : a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite P := Nat.finite_of_card_ne_zero fun h => by rw [h] at h4; norm_num at h4
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  have hk2 : k ≤ 2 := by
    have h : 2 ^ k ∣ 2 ^ 2 := by rw [← hk]; exact h4
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h
  rcases Nat.lt_or_ge k 2 with hlt | hge
  · have hdvd : Nat.card P ∣ 2 := by
      rw [hk]
      exact (Nat.pow_dvd_pow 2 (show k ≤ 1 by omega)).trans (by norm_num)
    have := isCyclic_of_card_dvd_prime hdvd
    exact (IsCyclic.isMulCommutative (α := P)).is_comm.comm a b
  · have hc : IsMulCommutative P :=
      IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (by rw [hk, le_antisymm hk2 hge])
    exact hc.is_comm.comm a b

theorem mul_comm_of_card_dvd {P : Type*} [Group P] (hP : IsPGroup 2 P) {m : ℕ} (hm : Odd m)
    (h : Nat.card P ∣ 4 * m) (a b : P) : a * b = b * a := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite P := Nat.finite_of_card_ne_zero fun h0 => by
    rw [h0, zero_dvd_iff] at h
    rcases hm with ⟨j, rfl⟩
    omega
  obtain ⟨k, hk⟩ := hP.exists_card_eq
  refine mul_comm_of_card_dvd_four hP ?_ a b
  rw [hk] at h ⊢
  exact (Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hm)).dvd_of_dvd_mul_right h

theorem commInf_of_mulEquiv {D A : Type*} [Group D] [Group A] {H₁ H₂ : Subgroup D}
    (e : ↥(H₁ ⊓ H₂) ≃* A) (hA : ∀ a b : A, a * b = b * a) : CommInf H₁ H₂ := by
  intro x hx y hy
  have h := hA (e ⟨x, hx⟩) (e ⟨y, hy⟩)
  rw [← map_mul, ← map_mul] at h
  exact congrArg Subtype.val (e.injective h)

theorem commInf_of_card_dvd {D : Type*} [Group D] {H₁ H₂ : Subgroup D}
    (hP : IsPGroup 2 ↥(H₁ ⊓ H₂)) {m : ℕ} (hm : Odd m) (h : Nat.card ↥(H₁ ⊓ H₂) ∣ 4 * m) :
    CommInf H₁ H₂ := fun x hx y hy =>
  congrArg Subtype.val (mul_comm_of_card_dvd hP hm h ⟨x, hx⟩ ⟨y, hy⟩)

section Cases

variable {D : Type} [Group D] {H₁ H₂ : Subgroup D}

theorem commInf_of_caseOne (h : F6.IsF618CaseOne H₁ H₂) : CommInf H₁ H₂ :=
  commInf_of_mulEquiv h.1.some fun a b => mul_comm a b

theorem commInf_of_caseFour (h : F6.IsF618CaseFour H₁ H₂) : CommInf H₁ H₂ :=
  commInf_of_mulEquiv h.2.1.some fun a b => mul_comm a b

theorem commInf_of_caseTwo [Finite D] (hT : IsGoldschmidtTriple H₁ H₂)
    (h : F6.IsF618CaseTwo D) : CommInf H₁ H₂ := by
  have hP := hT.isPGroup_inf
  have hdvd : Nat.card ↥(H₁ ⊓ H₂) ∣ Nat.card D := Subgroup.card_subgroup_dvd_card _
  rcases h with he | ⟨φ, hφ, hN⟩
  · obtain ⟨e⟩ := he
    refine commInf_of_card_dvd hP (m := 9) (by decide) ?_
    rw [Nat.card_congr e.toEquiv, Nat.card_prod, Nat.card_perm, Nat.card_fin] at hdvd
    exact hdvd
  · refine commInf_of_card_dvd hP (m := 27) (by decide) ?_
    have hc : Nat.card D = 4 * 27 := by
      rw [Subgroup.card_eq_card_quotient_mul_card_subgroup φ.ker,
        Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective φ hφ).toEquiv, hN.2.1,
        Nat.card_prod]
      simp
    rwa [hc] at hdvd

end Cases

theorem not_isQuasisimple_of_isSolvable {Γ : Type*} [Group Γ] [Group.IsSolvable Γ]
    (K : Subgroup Γ) : ¬ CFSG.IsQuasisimple ↥K := by
  rintro ⟨-, hsimple, a, b, hab⟩
  have : Group.IsSolvable (↥K ⧸ Subgroup.center ↥K) := inferInstance
  exact hab ((IsSimpleGroup.comm_iff_isSolvable).mpr this a b)

end Insp15418

open Insp15418

namespace InspectionData15418

variable {G : Type} [Group G] [Finite G] {I G₁ G₂ S T Z : Subgroup G}

section Setting

variable (d : InspectionData15418 I G₁ G₂ S T Z)
include d

theorem G₁_le : G₁ ≤ I := d.triple.1 ▸ le_sup_left

theorem G₂_le : G₂ ≤ I := d.triple.1 ▸ le_sup_right

theorem isSylowTwoOf : IsSylowTwoOf S I := d.inf_eq ▸ d.triple.2.2.2

theorem S_le : S ≤ I := d.isSylowTwoOf.1

theorem S_le_G₁ : S ≤ G₁ := d.inf_eq ▸ inf_le_left

theorem S_le_G₂ : S ≤ G₂ := d.inf_eq ▸ inf_le_right

theorem isPGroup_S : IsPGroup 2 S := d.isPGroup.to_le d.le_T

theorem inf_subgroupOf : G₁.subgroupOf I ⊓ G₂.subgroupOf I = S.subgroupOf I := by
  rw [← d.inf_eq]
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem isGoldschmidtAmalgam :
    (G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
        (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) =
      (S.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ∧
    IsGoldschmidtAmalgam ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
      ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) := by
  rcases d.triple.goldschmidt_mod_pPrimeCore with ⟨h₁, h₂, -⟩ | ⟨e₁, e₂, -⟩
  · exact ⟨h₁.trans (by rw [d.inf_subgroupOf]), h₂⟩
  · exfalso
    apply d.pCoreOf_ne
    rw [← F6.map_pCoreOf_subgroupOf d.G₁_le, ← F6.map_pCoreOf_subgroupOf d.G₂_le, e₁, e₂]

theorem f618 (hF618 : F6.TheoremF618Cat) :
    F6.F618ConclusionCat ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
      ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I))) :=
  hF618 _ _ _ d.isGoldschmidtAmalgam.2.toIsGoldschmidtTriple
    ⟨↥I, inferInstance, inferInstance, d.sqtk, ⟨MulEquiv.refl _⟩⟩

theorem inf_pPrimeCore_eq :
    S.subgroupOf I ⊓ CFSG.pPrimeCore 3 ↥I = Open.pCore 2 ↥I := by
  rw [← d.inf_subgroupOf]
  exact F6.inf_inf_pPrimeCore_eq_pCore d.triple.subgroupOf

theorem commutator_le_of_commInf
    (h : CommInf ((G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))
      ((G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)))) :
    ⁅S, S⁆ ≤ pCoreOf 2 I := by
  have hmem : ∀ x (hx : x ∈ S), QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) ⟨x, d.S_le hx⟩ ∈
      (G₁.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) ⊓
        (G₂.subgroupOf I).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I)) := by
    intro x hx
    rw [d.isGoldschmidtAmalgam.1]
    exact ⟨⟨x, d.S_le hx⟩, by simpa [Subgroup.mem_subgroupOf] using hx, rfl⟩
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have hc := h _ (hmem a ha) _ (hmem b hb)
  set x : ↥I := ⟨a, d.S_le ha⟩ with hx
  set y : ↥I := ⟨b, d.S_le hb⟩ with hy
  have hk : x * y * x⁻¹ * y⁻¹ ∈ CFSG.pPrimeCore 3 ↥I := by
    rw [← QuotientGroup.eq_one_iff]
    change QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥I) (x * y * x⁻¹ * y⁻¹) = 1
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  have hs : x * y * x⁻¹ * y⁻¹ ∈ S.subgroupOf I := by
    rw [Subgroup.mem_subgroupOf]
    exact S.mul_mem (S.mul_mem (S.mul_mem ha hb) (S.inv_mem ha)) (S.inv_mem hb)
  have hO : x * y * x⁻¹ * y⁻¹ ∈ Open.pCore 2 ↥I := d.inf_pPrimeCore_eq ▸ ⟨hs, hk⟩
  exact ⟨_, hO, by simp [x, y, commutatorElement_def]⟩

end Setting

end InspectionData15418

end CFSG.Quasithin.EmptyFaithfulMultiple

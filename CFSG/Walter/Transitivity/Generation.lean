module

public import Mathlib.GroupTheory.PGroup
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.GroupAction.NoncyclicAbelianPGroup
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.SubgroupConjAction

public section

namespace CFSG.Walter.Transitivity

open CFSG

private theorem card_le_two_of_isCyclic {E : Type*} [Group E] [IsCyclic E]
    (hexp : ∀ x : E, x ^ 2 = 1) : Nat.card E ≤ 2 := by
  rw [← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd two_pos (Monoid.exponent_dvd_of_forall_pow_eq_one hexp)

variable {G : Type*} [Group G] [Finite G]

omit [Finite G] in
private theorem mem_centralizer_of_smul_eq {V Q : Subgroup G} [Subgroup.Normalizes V Q]
    {v : V} {x : Q} (h : v • x = x) :
    (x : G) ∈ Subgroup.centralizer ({(v : G)} : Set G) := by
  have h' : (v : G) * x * (v : G)⁻¹ = x := by
    simpa only [Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe] using
      congrArg Subtype.val h
  rw [mul_inv_eq_iff_eq_mul] at h'
  exact Subgroup.mem_centralizer_singleton_iff.mpr h'.symm

theorem exists_ne_one_centralizer_not_le {V Q₁ Q₂ D : Subgroup G}
    (hVcomm : IsMulCommutative V) (hVexp : ∀ x ∈ V, x ^ 2 = 1) (hVcard : 8 ≤ Nat.card V)
    (hQ₁ : Nat.Coprime 2 (Nat.card Q₁)) (hQ₂ : Nat.Coprime 2 (Nat.card Q₂))
    (hVQ₁ : V ≤ Subgroup.normalizer (Q₁ : Set G))
    (hVQ₂ : V ≤ Subgroup.normalizer (Q₂ : Set G)) (hQ₁D : ¬ Q₁ ≤ D) (hQ₂D : ¬ Q₂ ≤ D) :
    ∃ v ∈ V, v ≠ 1 ∧ ¬ Q₁ ⊓ Subgroup.centralizer ({v} : Set G) ≤ D ∧
      ¬ Q₂ ⊓ Subgroup.centralizer ({v} : Set G) ≤ D := by
  classical
  let : CommGroup V := IsMulCommutative.instCommGroup
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hexp : ∀ x : V, x ^ 2 = 1 := fun x => Subtype.ext (hVexp x x.2)
  have hVp : IsPGroup 2 V := fun x => ⟨1, by simpa using hexp x⟩
  have : Fact (IsPGroup 2 V) := ⟨hVp⟩
  have : Subgroup.Normalizes V Q₁ := ⟨hVQ₁⟩
  have : Subgroup.Normalizes V Q₂ := ⟨hVQ₂⟩
  have hVnc : ¬ IsCyclic V := fun _ => by
    have := card_le_two_of_isCyclic hexp
    omega
  have hsup₁ := iSup_fixedPointSubgroup_cyclicQuot_eq_top_of_noncyclic_abelian_pGroup_action
    (G := Q₁) (A := V) 2 hQ₁ hVnc
  obtain ⟨B, hBcyc, hBfix⟩ : ∃ B : Subgroup V, IsCyclic (V ⧸ B) ∧
      ¬ fixedPointSubgroup B Q₁ ≤ D.subgroupOf Q₁ := by
    by_contra! h
    apply hQ₁D
    intro x hx
    have htop : (⊤ : Subgroup Q₁) ≤ D.subgroupOf Q₁ := hsup₁ ▸ iSup₂_le h
    exact htop (Subgroup.mem_top ⟨x, hx⟩)
  have hBnc : ¬ IsCyclic B := fun _ => by
    have h₁ : Nat.card (V ⧸ B) ≤ 2 := card_le_two_of_isCyclic fun x => by
      induction x using QuotientGroup.induction_on with
      | H v => rw [← QuotientGroup.mk_pow, hexp v, QuotientGroup.mk_one]
    have h₂ : Nat.card B ≤ 2 := card_le_two_of_isCyclic fun x => Subtype.ext (hexp x)
    have := Subgroup.card_eq_card_quotient_mul_card_subgroup B
    have := Nat.mul_le_mul h₁ h₂
    omega
  have : Fact (IsPGroup 2 B) := ⟨hVp.to_subgroup B⟩
  have hsup₂ := iSup_fixedPointSubgroup_zpowers_eq_top_of_noncyclic_abelian_pGroup_action
    (G := Q₂) (A := B) 2 hQ₂ hBnc
  obtain ⟨b, hb1, hbfix⟩ : ∃ b : B, b ≠ 1 ∧
      ¬ fixedPointSubgroup (Subgroup.zpowers b) Q₂ ≤ D.subgroupOf Q₂ := by
    by_contra! h
    apply hQ₂D
    intro x hx
    have htop : (⊤ : Subgroup Q₂) ≤ D.subgroupOf Q₂ := hsup₂ ▸ iSup₂_le h
    exact htop (Subgroup.mem_top ⟨x, hx⟩)
  refine ⟨((b : V) : G), (b : V).2, fun h => hb1 (Subtype.ext (Subtype.ext h)), ?_, ?_⟩
  · intro hle
    apply hBfix
    intro x hx
    have hbx : (b : V) • x = x := (FixedPoints.mem_subgroup B Q₁ x).mp hx b
    exact hle ⟨x.2, mem_centralizer_of_smul_eq hbx⟩
  · intro hle
    apply hbfix
    intro x hx
    have hbx : (b : V) • x = x :=
      (FixedPoints.mem_subgroup (Subgroup.zpowers b) Q₂ x).mp hx ⟨b, Subgroup.mem_zpowers b⟩
    exact hle ⟨x.2, mem_centralizer_of_smul_eq hbx⟩

end CFSG.Walter.Transitivity

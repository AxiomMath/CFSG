module

public import CFSG.RankThree.PartTwo.KFacts.ONanKS152Core

public section

namespace CFSG.RankThree.PartTwo.KFacts

open Subgroup
open scoped commutatorElement Pointwise

namespace KS152

theorem exists_action {Γ : Type*} [Group Γ] (L P Q : Subgroup Γ) (hPQ : Disjoint P Q)
    (hPN : P ≤ Subgroup.normalizer (Q : Set Γ))
    (hLH : L ≤ Subgroup.normalizer ((P ⊔ Q : Subgroup Γ) : Set Γ))
    (hLQ : L ≤ Subgroup.normalizer (Q : Set Γ)) :
    ∃ ρ : L →* MulAut P, ∀ (l : L) (u : P), ρ l u = u → ⁅(l : Γ), (u : Γ)⁆ ∈ Q := by
  set H : Subgroup Γ := P ⊔ Q with hH
  have hPH : P ≤ H := le_sup_left
  have hQH : Q ≤ H := le_sup_right
  have hHN : H ≤ Subgroup.normalizer (Q : Set Γ) := sup_le hPN Subgroup.le_normalizer
  have hN : (Q.subgroupOf H).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQH).mpr hHN
  set ρ₁ : L →* MulAut H := H.normalizerMonoidHom.comp (Subgroup.inclusion hLH) with hρ₁def
  have hρ₁ : ∀ (l : L) (h : H), ((ρ₁ l h : H) : Γ) = (l : Γ) * h * (l : Γ)⁻¹ := fun l h => by
    simp [hρ₁def, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hmapQ : ∀ l : L, (Q.subgroupOf H).map (ρ₁ l).toMonoidHom = Q.subgroupOf H := by
    intro l
    have hl : (l : Γ) ∈ Subgroup.normalizer (Q : Set Γ) := hLQ l.2
    have hl' : (l : Γ)⁻¹ ∈ Subgroup.normalizer (Q : Set Γ) := inv_mem hl
    ext x
    simp only [Subgroup.mem_map, Subgroup.mem_subgroupOf, MulEquiv.coe_toMonoidHom]
    constructor
    · rintro ⟨y, hy, rfl⟩
      rw [hρ₁]
      exact (Subgroup.mem_normalizer_iff.mp hl y).mp hy
    · intro hx
      refine ⟨(ρ₁ l)⁻¹ x, ?_, by simp⟩
      have h1 : (ρ₁ l)⁻¹ = ρ₁ l⁻¹ := (map_inv ρ₁ l).symm
      rw [h1, hρ₁]
      exact (Subgroup.mem_normalizer_iff.mp hl' x).mp hx
  let ρ₂ : L →* MulAut (H ⧸ Q.subgroupOf H) :=
    { toFun := fun l => QuotientGroup.congr (Q.subgroupOf H) (Q.subgroupOf H) (ρ₁ l) (hmapQ l)
      map_one' := by
        apply MulEquiv.ext
        intro x
        refine QuotientGroup.induction_on x ?_
        intro y
        simp [QuotientGroup.congr]
      map_mul' := by
        intro a b
        apply MulEquiv.ext
        intro x
        refine QuotientGroup.induction_on x ?_
        intro y
        simp [QuotientGroup.congr] }
  let κ : P →* H ⧸ Q.subgroupOf H :=
    (QuotientGroup.mk' (Q.subgroupOf H)).comp (Subgroup.inclusion hPH)
  have hκinj : Function.Injective κ := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    have hxQ : (x : Γ) ∈ Q := by
      have : (QuotientGroup.mk' (Q.subgroupOf H)) (Subgroup.inclusion hPH x) = 1 := hx
      exact Subgroup.mem_subgroupOf.mp
        ((QuotientGroup.eq_one_iff (N := Q.subgroupOf H) (Subgroup.inclusion hPH x)).mp this)
    have : (x : Γ) = 1 := Subgroup.mem_bot.mp (hPQ.le_bot ⟨x.2, hxQ⟩)
    exact Subgroup.mem_bot.mpr (Subtype.ext this)
  have hκsurj : Function.Surjective κ := by
    intro z
    obtain ⟨⟨h, hh⟩, rfl⟩ := QuotientGroup.mk_surjective z
    have hset : ((P ⊔ Q : Subgroup Γ) : Set Γ) = (P : Set Γ) * (Q : Set Γ) :=
      Subgroup.coe_mul_of_left_le_normalizer_right P Q hPN
    have hh' : h ∈ (P : Set Γ) * (Q : Set Γ) := by rw [← hset]; exact hh
    obtain ⟨u, hu, q, hq, rfl⟩ := Set.mem_mul.mp hh'
    refine ⟨⟨u, hu⟩, ?_⟩
    change (QuotientGroup.mk' (Q.subgroupOf H)) (Subgroup.inclusion hPH ⟨u, hu⟩) = _
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq]
    simpa [Subgroup.mem_subgroupOf] using hq
  let e : P ≃* H ⧸ Q.subgroupOf H := MulEquiv.ofBijective κ ⟨hκinj, hκsurj⟩
  refine ⟨(MulAut.congr e).symm.toMonoidHom.comp ρ₂, ?_⟩
  intro l u hlu
  have hlu' : e.symm (ρ₂ l (e u)) = u := by
    have h := hlu
    change ((MulAut.congr e).symm (ρ₂ l)) u = u at h
    rw [MulAut.congr_symm_apply] at h
    exact h
  have h1 : ρ₂ l (e u) = e u := by
    apply e.symm.injective
    rw [hlu', e.symm_apply_apply]
  have h2 : (QuotientGroup.mk' (Q.subgroupOf H)) (ρ₁ l (Subgroup.inclusion hPH u)) =
      (QuotientGroup.mk' (Q.subgroupOf H)) (Subgroup.inclusion hPH u) := h1
  have h3 : (QuotientGroup.mk' (Q.subgroupOf H))
      (ρ₁ l (Subgroup.inclusion hPH u) * (Subgroup.inclusion hPH u)⁻¹) = 1 := by
    rw [map_mul, map_inv, h2, mul_inv_cancel]
  have h4 := Subgroup.mem_subgroupOf.mp ((QuotientGroup.eq_one_iff
    (N := Q.subgroupOf H) (ρ₁ l (Subgroup.inclusion hPH u) * (Subgroup.inclusion hPH u)⁻¹)).mp h3)
  rw [Subgroup.coe_mul, Subgroup.coe_inv, hρ₁] at h4
  rw [commutatorElement_def]
  simpa using h4

end KS152

theorem ks152HJAct :
    ∀ (Γ : Type) [Group Γ] [Finite Γ] (L P Q : Subgroup Γ) (p : ℕ), p.Prime → p ≠ 2 →
      Group.IsPerfect ↥L →
      Nonempty (↥L ⧸ CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥L ≃*
        CFSG.Blueprint.NativeSporadic.J2) →
      IsPGroup 2 Q → P ≤ Subgroup.normalizer (Q : Set Γ) →
      ((CFSG.IsElementaryAbelian p ↥P ∧ Nat.card P = p ^ 2) ∨
        (CFSG.IsExtraspecialPGroup p ↥P ∧ Nat.card P = p ^ 3)) →
      L ≤ Subgroup.normalizer ((P ⊔ Q : Subgroup Γ) : Set Γ) →
      L ≤ Subgroup.normalizer (Q : Set Γ) →
        ∀ l ∈ L, ∀ u ∈ P, ⁅l, u⁆ ∈ Q := by
  intro Γ _ _ L P Q p hp hp2 hperf he hQ hPN hP hLH hLQ
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have := hperf
  have hPp : IsPGroup p P := by
    rcases hP with ⟨-, h⟩ | ⟨-, h⟩
    · exact IsPGroup.of_card (n := 2) h
    · exact IsPGroup.of_card (n := 3) h
  have hW : Nat.card (↥P ⧸ frattini ↥P) ≤ p ^ 2 := by
    rcases hP with ⟨-, h⟩ | ⟨hext, h⟩
    · rw [← h]
      exact Nat.card_le_card_of_surjective _ (QuotientGroup.mk'_surjective _)
    · obtain ⟨-, -, hfr, hcen⟩ := hext
      have hfc : Nat.card (frattini ↥P) = p := by rw [hfr]; exact hcen
      have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥P)
      rw [hfc, h] at h1
      have h2 : Nat.card (↥P ⧸ frattini ↥P) = p ^ 2 := by
        apply Nat.eq_of_mul_eq_mul_right hp.pos
        rw [← h1]
        ring
      exact h2.le
  have hdisj : Disjoint P Q := IsPGroup.disjoint_of_ne p 2 hp2 P Q hPp hQ
  obtain ⟨ρ, hρ⟩ := KS152.exists_action L P Q hdisj hPN hLH hLQ
  obtain ⟨hθs, hθc, hθ3, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
  have := hθc
  have hρ1 := KS152.action_trivial hPp hW (CFSG.RankThree.LocalRank.aschbacherSolvableCore 3 ↥L)
    hθs hθ3 he ρ
  intro l hl u hu
  exact hρ ⟨l, hl⟩ ⟨u, hu⟩ (by rw [hρ1]; rfl)

end CFSG.RankThree.PartTwo.KFacts

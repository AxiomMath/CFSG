module

public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Hyp
public import CFSG.RankThree.PartTwo.Sec3.ThompsonFamilyG
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
import CFSG.GroupTheory.Fitting.CharacteristicP

public section

namespace CFSG.RankThree.PartTwo.Sec20

open Subgroup
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {X : Type} [Group X] [Finite X] {L S : Subgroup X}

private lemma mem_map_of_forall_conj_eq (h : Hyp1411 X L S) {s l : X ⧸ CFSG.pPrimeCore 3 X}
    (hl : l ∈ L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)))
    (hcon : ∀ y ∈ L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)), s * y * s⁻¹ = l * y * l⁻¹) :
    s ∈ L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) := by
  have hF : CFSG.generalizedFitting (X ⧸ CFSG.pPrimeCore 3 X) =
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) := h.2.2.2.1
  have hc : l⁻¹ * s ∈ L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) := by
    rw [← hF]
    refine CFSG.centralizer_generalizedFitting_le _ ?_
    rw [hF, mem_centralizer_iff]
    intro y hy
    calc y * (l⁻¹ * s) = l⁻¹ * (l * y * l⁻¹) * s := by group
      _ = l⁻¹ * (s * y * s⁻¹) * s := by rw [hcon y hy]
      _ = l⁻¹ * s * y := by group
  simpa using mul_mem hl hc

private lemma exists_hom_outer_eq_one (h : Hyp1411 X L S)
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥) :
    ∃ ρ : X ⧸ CFSG.pPrimeCore 3 X →*
        Outer ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))),
      ∀ b ∈ S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)), ρ b = 1 → b = 1 := by
  set K := CFSG.pPrimeCore 3 X
  have : (L.map (QuotientGroup.mk' K)).Normal := h.2.1.map _ (QuotientGroup.mk'_surjective K)
  refine ⟨(QuotientGroup.mk' (CFSG.ComponentClassification.OuterAutomorphisms.inner _)).comp
    MulAut.conjNormal, fun b hbS hb => ?_⟩
  have hb' : (QuotientGroup.mk (MulAut.conjNormal b : MulAut ↥(L.map (QuotientGroup.mk' K))) :
      Outer ↥(L.map (QuotientGroup.mk' K))) = 1 := hb
  obtain ⟨l, hl⟩ := (QuotientGroup.eq_one_iff _).1 hb'
  have hmem : b ∈ L.map (QuotientGroup.mk' K) := by
    refine mem_map_of_forall_conj_eq h l.2 fun y hy => ?_
    have h1 := congrArg Subtype.val (DFunLike.congr_fun hl ⟨y, hy⟩)
    simp only [MulAut.conj_apply, MulAut.conjNormal_apply, Subgroup.coe_mul,
      Subgroup.coe_inv] at h1
    exact h1.symm
  exact mem_bot.1 (hSL ▸ mem_inf.2 ⟨hbS, hmem⟩)

theorem not_inner_of_inf_eq_bot_of_hyp1411 (h : Hyp1411 X L S)
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥)
    {t : X} (htS : t ∈ S) (htQ : t ∉ CFSG.pCore 2 X) :
    ∀ l ∈ L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)),
      ∃ y ∈ L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)),
        QuotientGroup.mk' (CFSG.pPrimeCore 3 X) t * y *
            (QuotientGroup.mk' (CFSG.pPrimeCore 3 X) t)⁻¹ ≠ l * y * l⁻¹ := by
  intro l hl
  by_contra hcon
  push Not at hcon
  have hmem := mem_map_of_forall_conj_eq h hl hcon
  have hbot : QuotientGroup.mk' (CFSG.pPrimeCore 3 X) t ∈
      (⊥ : Subgroup (X ⧸ CFSG.pPrimeCore 3 X)) :=
    hSL ▸ mem_inf.2 ⟨mem_map_of_mem _ htS, hmem⟩
  rw [mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hbot
  exact htQ (mem_pCore_of_mem_pPrimeCore_of_hyp1411 h htS hbot)

theorem relIndex_pCore_le_two_of_isCyclic_outer (h : Hyp1411 X L S)
    (hSL : S.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) ⊓
      L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X)) = ⊥)
    (hcyc : IsCyclic (Outer ↥(L.map (QuotientGroup.mk' (CFSG.pPrimeCore 3 X))))) :
    ∀ A : Subgroup X, A ≤ S → Sec3.IsElemTwo A → (CFSG.pCore 2 X).relIndex A ≤ 2 := by
  intro A hAS hA
  obtain ⟨ρ, hρ⟩ := exists_hom_outer_eq_one h hSL
  set K := CFSG.pPrimeCore 3 X
  have hinj : Function.Injective (ρ.comp (A.map (QuotientGroup.mk' K)).subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨b, hb⟩ hb1
    exact Subtype.ext (hρ b (map_mono hAS hb) hb1)
  have : IsCyclic ↥(A.map (QuotientGroup.mk' K)) := isCyclic_of_injective _ hinj
  have hexp : Monoid.exponent ↥(A.map (QuotientGroup.mk' K)) ∣ 2 := by
    refine Monoid.exponent_dvd_of_forall_pow_eq_one fun ⟨y, hy⟩ => ?_
    obtain ⟨a, haA, rfl⟩ := hy
    refine Subtype.ext ?_
    change QuotientGroup.mk' K a ^ 2 = 1
    rw [← map_pow, pow_two, hA.2 a haA, map_one]
  rw [IsCyclic.exponent_eq_card] at hexp
  have hKA : K ⊓ A ≤ CFSG.pCore 2 X := fun x hx =>
    mem_pCore_of_mem_pPrimeCore_of_hyp1411 h (hAS hx.2) hx.1
  have h1 : (CFSG.pCore 2 X).relIndex A ∣ Nat.card (A.map (QuotientGroup.mk' K)) := by
    rw [← relIndex_ker, QuotientGroup.ker_mk', ← inf_relIndex_right K A]
    exact relIndex_dvd_of_le_left A hKA
  exact Nat.le_of_dvd two_pos (h1.trans hexp)

end CFSG.RankThree.PartTwo.Sec20

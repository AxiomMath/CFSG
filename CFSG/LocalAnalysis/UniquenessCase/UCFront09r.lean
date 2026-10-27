module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09Shape92A5
import CFSG.LocalAnalysis.UniquenessCase.UCFront09i
import CFSG.LocalAnalysis.UniquenessCase.UCFront09l
import CFSG.GroupTheory.PCore.OpenTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas
import CFSG.LocalAnalysis.UniquenessCase.UCFront09h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open scoped commutatorElement

private theorem nonempty_bar2_mulEquiv {A B : Type*} [Group A] [Group B] (f : A →* B)
    (hf : Function.Surjective f) (hk : f.ker ≤ CFSG.pCore 2 A) :
    Nonempty (A ⧸ CFSG.pCore 2 A ≃* B ⧸ CFSG.pCore 2 B) := by
  have hker : ((QuotientGroup.mk' (CFSG.pCore 2 B)).comp f).ker = CFSG.pCore 2 A := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    refine le_antisymm (le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := B)).comap f,
      (CFSG.pCore_isPGroup (p := 2) (G := B)).comap_of_ker_isPGroup f
        ((CFSG.pCore_isPGroup (p := 2) (G := A)).to_le hk)⟩) ?_
    exact Subgroup.map_le_iff_le_comap.1 (le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := A)).map f hf,
      (CFSG.pCore_isPGroup (p := 2) (G := A)).map f⟩)
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hker.symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective ((QuotientGroup.mk' (CFSG.pCore 2 B)).comp f)
      ((QuotientGroup.mk'_surjective _).comp hf))⟩

variable {G : Type} [Group G] [Finite G]

theorem false_of_le_centralizer_I9 (hKF : KFactShape92NoFaithfulA5) {M L X H : Subgroup G}
    (hLM : L ≤ M) (hA5 : IsAlt (Bar2 L) 5) (hX : Opp 3 X = X) (hXL : X ≤ L)
    (hcov : L = X ⊔ pCoreOf 2 L)
    (hZ : ⁅pCoreOf 2 M ⊓ centralizer (pCoreOf 2 M : Set G) ⊓ X, X⁆ ≠ ⊥) (hXH : X ≤ H)
    (hXI : X ≤ centralizer (I9 H : Set G)) (h92 : Shape92 (Lbar9 X H)) : False := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXM : X ≤ M := hXL.trans hLM
  have hEX : E9 M X ≤ X := (E9_le M X).trans ((commutator_zO2_le hXM).trans inf_le_right)
  have hEE : ⁅E9 M X, X⁆ = E9 M X := commutator_E9_eq hLM hXL hcov hA5 hX
  have hno : ¬ ⁅E9 M X, X⁆ ≤ I9 H := fun h => E9_ne_bot hLM hXL hcov hA5 hX hZ (by
    have h2 : ⁅⁅E9 M X, X⁆, X⁆ = ⊥ := le_bot_iff.1 ((commutator_mono h le_rfl).trans
      (commutator_eq_bot_iff_le_centralizer.2 (le_centralizer_iff.1 hXI)).le)
    rwa [hEE, hEE] at h2)
  obtain ⟨ψ, hψ⟩ : ∃ ψ : ↥X →* Lbar9 X H, ∀ x, ψ x = 1 → (x : G) ∈ I9 H := by
    refine ⟨((QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H)).comp (inclusion hXH)).codRestrict
      (img9 H (L9 X H)) fun x => Subgroup.mem_map_of_mem _ (mem_subgroupOf.2 (le_L9 hX x.2)),
      fun x hx => ?_⟩
    have h1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥H) (inclusion hXH x) = 1 :=
      congrArg Subtype.val hx
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact Subgroup.mem_map_of_mem H.subtype h1
  have hker : ψ.ker ≤ CFSG.pCore 2 ↥X := fun x hx => (CFSG.mem_openPCoreOf_iff x).1
    ((inf_pCoreOf_eq_of_isAlt_bar2 hXL hcov hA5).le (mem_inf.2 ⟨x.2,
      inf_I9_le_pCoreOf hXL hcov hA5 hXH (mem_inf.2 ⟨x.2, hψ x (MonoidHom.mem_ker.1 hx)⟩)⟩))
  have hKA5 : IsAlt (Bar2 ψ.range) 5 := by
    obtain ⟨e⟩ := isAlt_bar2_of_isAlt_bar2 hXL hcov hA5
    obtain ⟨f⟩ := nonempty_bar2_mulEquiv ψ.rangeRestrict ψ.rangeRestrict_surjective
      ((MonoidHom.ker_rangeRestrict ψ).le.trans hker)
    exact ⟨f.symm.trans e⟩
  set Q : Subgroup (Lbar9 X H) := ((E9 M X).subgroupOf X).map ψ with hQ
  have hQ2 : ∀ a ∈ Q, a ^ 2 = 1 := by
    intro a ha
    obtain ⟨e, he, rfl⟩ := Subgroup.mem_map.1 ha
    rw [← map_pow, show e ^ 2 = 1 from Subtype.ext (by
      simpa using sq_eq_one_of_mem_E9 hXM _ (mem_subgroupOf.1 he)), map_one]
  have hKQ : ψ.range ≤ normalizer (Q : Set (Lbar9 X H)) := by
    rw [hQ, MonoidHom.range_eq_map, ← normalizer_eq_top_iff.2
      ((normal_subgroupOf_iff_le_normalizer hEX).2 (normalizer_commutator_ge_right _ _))]
    exact le_normalizer_map ψ
  have hall : (∀ x : ↥X, ψ x ∈ centralizer (Q : Set (Lbar9 X H))) → False := fun h =>
    hno (commutator_le.2 fun e he x hx => hψ ⁅(⟨e, hEX he⟩ : ↥X), ⟨x, hx⟩⁆ (by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_commute]
      exact mem_centralizer_iff.1 (h ⟨x, hx⟩) (ψ ⟨e, hEX he⟩)
        (Subgroup.mem_map_of_mem ψ (mem_subgroupOf.2 he))))
  have hQ1 : Q ≠ ⊥ := fun h => hall fun x => mem_centralizer_iff.2 fun q hq => by
    rw [h] at hq
    rw [mem_bot.1 hq, one_mul, mul_one]
  obtain ⟨C, hCX, hCmem⟩ : ∃ C : Subgroup G, C ≤ X ∧
      ∀ x : ↥X, (x : G) ∈ C ↔ ψ x ∈ centralizer (Q : Set (Lbar9 X H)) :=
    ⟨((centralizer (Q : Set (Lbar9 X H))).comap ψ).map X.subtype, map_subtype_le _,
      fun x => (mem_map_iff_mem X.subtype_injective).trans mem_comap⟩
  have hCN : ψ.range ≤ normalizer
      ((centralizer (Q : Set (Lbar9 X H)) : Subgroup (Lbar9 X H)) : Set (Lbar9 X H)) :=
    hKQ.trans (le_normalizer_of_normal_subgroupOf (centralizer_le_normalizer _))
  have hXC : X ≤ normalizer (C : Set G) := le_normalizer_iff.2 fun x hx c hc => by
    have h := (hCmem ⟨c, hCX hc⟩).1 hc
    refine (hCmem (⟨x, hx⟩ * ⟨c, hCX hc⟩ * ⟨x, hx⟩⁻¹)).2 ?_
    rw [map_mul, map_mul, map_inv]
    exact (mem_normalizer_iff.1 (hCN ⟨⟨x, hx⟩, rfl⟩) _).1 h
  rcases le_pCoreOf_or_le_of_le_normalizer hXL hcov hA5 hX hCX hXC with hC | hC
  ·
    refine hKF (Lbar9 X H) h92 Q ψ.range hQ1 hQ2 hKQ hKA5 fun y hy => ?_
    obtain ⟨x, rfl⟩ := (mem_inf.1 hy).1
    have hx : x ∈ CFSG.pCore 2 ↥X :=
      (CFSG.mem_openPCoreOf_iff x).1 (hC ((hCmem x).2 (mem_inf.1 hy).2))
    have hmap : (CFSG.pCore 2 ↥X).map ψ.rangeRestrict ≤ CFSG.pCore 2 ↥ψ.range :=
      le_sSup ⟨(CFSG.pCore_normal (p := 2) (G := ↥X)).map _ ψ.rangeRestrict_surjective,
        (CFSG.pCore_isPGroup (p := 2) (G := ↥X)).map _⟩
    exact (CFSG.mem_openPCoreOf_iff (ψ.rangeRestrict x)).2
      (hmap (Subgroup.mem_map_of_mem _ hx))
  · exact hall fun x => (hCmem x).1 (hC x.2)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09

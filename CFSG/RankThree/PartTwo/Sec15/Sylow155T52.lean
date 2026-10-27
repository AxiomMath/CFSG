module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155T51
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Comp
import CFSG.RankThree.PartTwo.Sec15.Sylow155T52Lem
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.CentralizerLemmas

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

namespace Sylow155T52

variable {G : Type} [Group G] [Finite G]

theorem exists_invariant_component_point (h1 : Sec4.Item4_1LargePrime)
    (h2 : Sec4.Item4_1ThreeCover) (h43 : Sec4.Item4_3) (hin : Sec4.Census.CoverInputs46)
    (hT : TheoremFourHyp G) (hS : partTwoS G = ∅) {A : Subgroup G} (hA : A ∈ partTwoF G)
    {B : Subgroup G} (hBA : B ≤ A) (hB9 : Nat.card B = 9)
    (hcon : ¬ CFSG.ABGLocalTools.IsPConstrained 3 ↥(Subgroup.centralizer (B : Set G))) :
    ∃ K : Subgroup G, K ≤ A ∧ K ≠ ⊥ ∧ ¬ B ≤ K ∧
      (∀ w ∈ Subgroup.normalizer (A : Set G), w ∈ Subgroup.normalizer (B : Set G) →
        K.map (MulAut.conj w).toMonoidHom = K) ∧
      (K ≤ B → ∃ d ∈ Subgroup.centralizer (B : Set G), d ∈ Subgroup.normalizer (A : Set G) ∧
        (∃ k : ℕ, d ^ 3 ^ k = 1) ∧ ∃ a ∈ A, d * a * d⁻¹ ≠ a) := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set C : Subgroup G := Subgroup.centralizer (B : Set G) with hCdef
  obtain ⟨Y, hY, hYaut, ⟨a, haA, ha1, haY⟩, hBY⟩ :=
    Sylow155T51.exists_centralizer_component_data h1 h2 h43 hin hT hS hA hBA hB9 hcon
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hAC : A ≤ C := by
    intro x hx
    rw [hCdef, Subgroup.mem_centralizer_iff]
    intro b hb
    exact congrArg Subtype.val (hAab.1.is_comm.comm ⟨b, hBA hb⟩ ⟨x, hx⟩)
  set K : Subgroup G :=
    (A.subgroupOf C ⊓ Y.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C))).map C.subtype with hKdef
  refine ⟨K, ?_, ?_, ?_, fun w hwA hwB => Sylow155T51.map_conj_inf_comap_eq hYaut A hwA hwB, ?_⟩
  · rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_inf.mp hx).1
  · intro hK
    apply ha1
    have haK : (a : G) ∈ K := ⟨a, Subgroup.mem_inf.mpr ⟨haA, haY⟩, rfl⟩
    rw [hK, Subgroup.mem_bot] at haK
    exact Subtype.ext haK
  ·
    intro hBK
    apply hBY
    rintro _ ⟨b, hb, rfl⟩
    obtain ⟨x, hx, hxb⟩ := hBK (show (b : G) ∈ B from hb)
    have hxb' : x = b := Subtype.ext hxb
    rw [← hxb']
    exact (Subgroup.mem_inf.mp hx).2
  ·
    intro hKB
    have hN3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥C) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
    have hO : CFSG.pPrimeCore 3 (↥C ⧸ CFSG.pPrimeCore 3 ↥C) = ⊥ :=
      CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
    obtain ⟨u, huY, hu3, y, hyY, huy⟩ :=
      Sylow155T51.exists_pow_three_not_commute_of_isComponent hO hY
    have hYn : ∀ q : ↥C ⧸ CFSG.pPrimeCore 3 ↥C,
        q ∈ Subgroup.normalizer (Y : Set (↥C ⧸ CFSG.pPrimeCore 3 ↥C)) := fun q =>
      Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hYaut (MulAut.conj q))
    have hA'ab : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf C) := hAab.subgroupOf C
    have hA'max : ∀ E : Subgroup C, CFSG.Assembly.IsElemAbelian 3 E → A.subgroupOf C ≤ E →
        E = A.subgroupOf C := by
      intro E hE hAE'
      have hAEm : A ≤ E.map C.subtype := fun x hx =>
        ⟨⟨x, hAC hx⟩, hAE' (show (⟨x, hAC hx⟩ : C) ∈ A.subgroupOf C from hx), rfl⟩
      have hEq : E.map C.subtype = A := hA.2.1 _ (hE.map _) hAEm
      rw [← hEq]
      exact (Subgroup.comap_map_eq_self_of_injective C.subtype_injective E).symm
    have hEY : ∀ e ∈ A.subgroupOf C, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) e ∈ Y →
        ∀ z ∈ Y, QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) e * z =
          z * QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) e := by
      intro e he heY z _
      have heB : (e : G) ∈ B := hKB ⟨e, Subgroup.mem_inf.mpr ⟨he, heY⟩, rfl⟩
      obtain ⟨m, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pPrimeCore 3 ↥C) z
      rw [← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp m.2 (e : G) heB)
    obtain ⟨d, hdN, ⟨k, hk⟩, e, he, hde⟩ :=
      Sylow155T52.exists_mem_normalizer_not_commute (CFSG.pPrimeCore 3 ↥C) hN3 hA'ab hA'max hYn
        huY hu3 hyY huy hEY
    refine ⟨d, d.2, ?_, ⟨k, by simpa using congrArg Subtype.val hk⟩, e, he, fun h => hde ?_⟩
    · rw [Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        exact (Subgroup.mem_normalizer_iff.mp hdN ⟨x, hAC hx⟩).mp hx
      · intro hx
        have hxC : x ∈ C := by
          have hx' : x = (d : G)⁻¹ * ((d : G) * x * (d : G)⁻¹) * (d : G) := by group
          rw [hx']
          exact C.mul_mem (C.mul_mem (C.inv_mem d.2) (hAC hx)) d.2
        exact (Subgroup.mem_normalizer_iff.mp hdN ⟨x, hxC⟩).mpr hx
    · exact Subtype.ext (by simpa using h)

end Sylow155T52

end CFSG.RankThree.PartTwo.Sec15

module

public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofTen
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofCase
public import CFSG.RankThree.PartTwo.Sec4.Statements426
public import CFSG.RankThree.PartTwo.Sec10.Sec10XProofW

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL)


@[expose] def Item1011Two : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      ∀ e ∈ Subgroup.closure ({a, c} : Set G), e ≠ 1 →
        ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G) ⊓
          Subgroup.centralizer ({e} : Set G)), Subgroup.zpowers c⁆ ≠ ⊥ →
        sec10U L a ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e} : Set G))

@[expose] def Step1011Two : Prop :=
  Sec4.Item4_5 → Sec9.Item97 →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      sec10U L a ∈
        maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2) →
      ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G) ⊓
        Subgroup.centralizer ({a} : Set G)), Subgroup.zpowers c⁆ ≠ ⊥ →
      ¬ sec10U L a ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) →
      ∀ Y ∈ thetaComponentsAt 3 a, sec10U L a ≤ Y →
        (Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* projSL 2 (GaloisField 3 3)) ∨
          Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* CFSG.Blueprint.NativeSporadic.J2) ∨
          Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* CFSG.Blueprint.NativeSporadic.M12)) →
        ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G) ⊓
            Subgroup.centralizer ({a} : Set G)),
          Subgroup.closure ({c, a} : Set G)⁆ ≤
          inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) →
        False

@[expose] def Step1012S : Prop :=
  Sec4.Item4_5 → Sec9.Item97 → Item107 → Sec4.Item4_26Theta → Item1011Two →
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a : G)
    (R : Subgroup G), Sec10Std G A c L a R → ∀ d : G, A ⊓ L = Subgroup.zpowers d →
      sec10U L a ≤ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G)) →
      sec10U L a ∈
        maxInvariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers c : Set G)) A (piOf 2) →
      ∀ S ∈ maxInvariantPiSubgroups
          (inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set G))) A (piOf 2),
        sec10U L a ≤ S → S ⊓ Subgroup.centralizer ({c} : Set G) = sec10U L a →
        S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥ →
      ∀ w ∈ Subgroup.normalizer (A : Set G), w ∈ Subgroup.normalizer (S : Set G) →
        w * a * w⁻¹ = a → w * d * w⁻¹ = d → w * c * w⁻¹ = c * d →
      ∃ e ∈ Subgroup.closure ({a, c} : Set G), e ∉ Subgroup.zpowers c ∧
        ∃ U ∈ fourGroupsMinus A, U ≤ inSubgroup (aschbacherSolvableCore 3)
          (Subgroup.centralizer ((Subgroup.closure {e, d} : Subgroup G) : Set G))

namespace Sec10XProof

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L : Subgroup G} {a : G}
  {R : Subgroup G}

theorem not_mem_zpowers_of_commutator_ne_bot (h : Sec10Std G A c L a R) {e : G} (he1 : e ≠ 1)
    {K : Subgroup G} (hK : K ≤ Subgroup.centralizer ({e} : Set G))
    (hcomm : ⁅K, Subgroup.zpowers c⁆ ≠ ⊥) : e ∉ Subgroup.zpowers c := by
  intro hec
  apply hcomm
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hce : c ∈ Subgroup.zpowers e := by
    have hle : Subgroup.zpowers e ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hec
    have heq : Subgroup.zpowers e = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge hle ?_
      rw [Nat.card_zpowers, Nat.card_zpowers, h.orderOf_c]
      have he3 : e ^ 3 = 1 := by
        obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hec
        rw [← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast,
          h.pow_three h.mem_A, one_zpow]
      rw [orderOf_eq_prime he3 he1]
    rw [heq]
    exact Subgroup.mem_zpowers c
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.le_centralizer_iff,
    Subgroup.zpowers_le]
  refine Subgroup.mem_centralizer_iff.mpr fun x hx => ?_
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp hce
  have hxe : Commute x e := Subgroup.mem_centralizer_singleton_iff.mp (hK hx)
  exact (hxe.zpow_right m).eq

end Sec10XProof

theorem item1011Two_of (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h1010 : Step1010)
    (hU : Step1010U) (hcore : Step1011Two) : Item1011Two := by
  intro G _ _ A c L a R h d hdL e he he1 hcomm
  have hec := Sec10XProof.not_mem_zpowers_of_commutator_ne_bot h he1
    ((Subgroup.map_subtype_le _).trans inf_le_right) hcomm
  have h' := Sec10XProof.sec10Std_of_mem_closure h he hec
  have hUe := Sec10XProof.sec10U_eq_of_mem_closure h he hec
  obtain ⟨-, halt⟩ := h1010 G A c L e R h'
  obtain ⟨-, -, hmax⟩ := hU h45 G A c L e R h'
  rw [hUe] at halt
  rcases halt with h1 | ⟨Y, hY, hUY, hiso, hbound⟩
  · exact h1
  · by_contra hnot
    exact hcore h45 h97 G A c L e R h' d hdL hmax (by rw [hUe]; exact hcomm)
      (by rw [hUe]; exact hnot) Y hY (by rw [hUe]; exact hUY) hiso (by rw [hUe]; exact hbound)

theorem item1012_of (h462 : Sec4.Item4_62) (h45 : Sec4.Item4_5) (h97 : Sec9.Item97)
    (h107 : Item107) (h426 : Sec4.Item4_26Theta) (hU : Step1010U) (hcore : Step1011Two)
    (hrest : Step1012S) : Item1012 := by
  intro G _ _ A c L a R h d hdL
  have h1010 := step1010_of h462 h45 h97 h107 hU
  have h1011 := item1011Two_of h45 h97 h1010 hU hcore
  obtain ⟨hU1, -⟩ := h1010 G A c L a R h
  obtain ⟨e₀, he₀, he₀1, hcomm⟩ := Sec10XProof.rank3II_10_11_one h hU1
  have hcomm' : ⁅inSubgroup (CFSG.pCore 2) (Subgroup.centralizer (sec10U L a : Set G) ⊓
      Subgroup.centralizer ({e₀} : Set G)), Subgroup.zpowers c⁆ ≠ ⊥ := fun hbot =>
    hcomm (le_bot_iff.mp (hbot ▸ Subgroup.commutator_mono
      (Sec10XProof.inf_centralizer_le_pCore_inf _ _) le_rfl))
  have hUθ := h1011 G A c L a R h d hdL e₀ he₀ he₀1 hcomm'
  have hec₀ := Sec10XProof.not_mem_zpowers_of_commutator_ne_bot h he₀1
    ((Subgroup.map_subtype_le _).trans inf_le_right) hcomm'
  have h₀ := Sec10XProof.sec10Std_of_mem_closure h he₀ hec₀
  have hU₀ := Sec10XProof.sec10U_eq_of_mem_closure h he₀ hec₀
  have hUθ₀ : sec10U L e₀ ≤
      inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({e₀} : Set G)) := by
    rw [hU₀]
    exact hUθ
  have hU1₀ : sec10U L e₀ ∈ fourGroupsMinus A := by
    rw [hU₀]
    exact hU1
  obtain ⟨-, -, hUmax₀⟩ := hU h45 G A c L e₀ R h₀
  obtain ⟨S, hS, hUS, w, hwA, hwS, hwa, hwd, hwc⟩ :=
    Sec10XProof.exists_w h107 h97 h₀ hdL hU1₀ hUθ₀
  by_cases hSd : S ⊓ Subgroup.centralizer ({d} : Set G) = ⊥
  · obtain ⟨hSθ, hS2, hSA⟩ := hS.prop
    have hSc := Sec10XProof.inf_centralizer_c_eq h₀
      ((isPiSubgroup_piOf_iff Nat.prime_two S).mp hS2) hSA hUS hUmax₀
    obtain ⟨e, he, hec, U', hU', hU'θ⟩ :=
      hrest h45 h97 h107 h426 h1011 G A c L e₀ R h₀ d hdL hUθ₀ hUmax₀ S hS hUS hSc hSd w hwA hwS
        hwa hwd hwc
    have he' := Sec10XProof.closure_le_closure_of_mem he₀ he
    exact ⟨e, Sec10XProof.sec10Std_of_mem_closure h he' hec, U', hU', hU'θ⟩
  · obtain ⟨U', hU', hU'θ⟩ := Sec10XProof.exists_fourGroupsMinus_of_inf_centralizer_ne_bot h97 h₀
      hdL hU1₀ hUmax₀ hS.prop hUS hSd
    exact ⟨e₀, h₀, U', hU', hU'θ⟩

section Main


theorem sec10X_of (h45 : Sec4.Item4_5) (h97 : Sec9.Item97) (h107 : Item107)
    (h462 : Sec4.Item4_62) (h426 : Sec4.Item4_26Theta) (h463 : Item463Inv) (hU : Step1010U)
    (hcore : Step1011Two) (hrest : Step1012S) : Sec10X :=
  sec10X_of_item1012 h45 h97 (item1012_of h462 h45 h97 h107 h426 hU hcore hrest) h463

end Main

end CFSG.RankThree.PartTwo.Sec10

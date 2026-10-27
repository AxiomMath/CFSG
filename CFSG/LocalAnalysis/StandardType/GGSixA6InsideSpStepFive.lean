module

public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTorus
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpPull
public import CFSG.Assembly.LargeEvenDefs
public import CFSG.LocalAnalysis.StandardType.GGIOneOrthEndSmall
public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveSpRootBig

public section

open Polynomial Module CFSG.RankThree.Classical CFSG.Assembly CFSG.Assembly.LowTwoRank
  CFSG.LocalAnalysis.ComponentInitial CFSG.RankThree.PartOne.KCPrimary CFSG.RankThree.PartOne
open CFSG.RankThree.PartOne.KCOrthogonal (reciprocalPolynomial)
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (proj)
open scoped commutatorElement
open CFSG.StandardType.ChoiceTwo

namespace CFSG.StandardType.A6InsideSp

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ} {L : Type} [Field L] [Algebra K L]
  {ζ : L} {E : Subgroup (StatedSp n K)} (F : ChoiceTwo.SpFrame K n ζ E)

variable [NeZero n] [Module.Finite K L]

private theorem zeroSet_add_eq {i₀ : Fin F.s} {c d' : Fin F.s → ZMod 3}
    (hc : ∀ i, c i ≠ 0 ↔ i = i₀) (hd'0 : d' i₀ = 0) :
    F.zeroSet (c + d') = Finset.univ.filter fun i => i ≠ i₀ ∧ d' i = 0 := by
  ext i
  simp only [ChoiceTwo.SpFrame.mem_zeroSet, Finset.mem_filter, Finset.mem_univ, true_and]
  by_cases hi : i = i₀
  · subst hi
    have hci : c i ≠ 0 := (hc i).mpr rfl
    constructor
    · intro h
      exfalso
      rw [Pi.add_apply, hd'0, add_zero] at h
      exact hci h
    · rintro ⟨h, -⟩
      exact absurd rfl h
  · have hci : c i = 0 := by
      by_contra h
      exact hi ((hc i).mp h)
    rw [Pi.add_apply, hci, zero_add]
    exact ⟨fun h => ⟨hi, h⟩, fun h => h.2⟩

private theorem independent_of_single {i₀ : Fin F.s} {c d' : Fin F.s → ZMod 3}
    (hc : ∀ i, c i ≠ 0 ↔ i = i₀) (hd'0 : d' i₀ = 0) (hd' : d' ≠ 0) :
    ∀ α β : ZMod 3, α • c + β • d' = 0 → α = 0 ∧ β = 0 := by
  intro α β h
  have hci₀ : c i₀ ≠ 0 := (hc i₀).mpr rfl
  have hα : α = 0 := by
    have h1 := congrFun h i₀
    simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hd'0, mul_zero,
      add_zero] at h1
    exact (mul_eq_zero.mp h1).resolve_right hci₀
  refine ⟨hα, ?_⟩
  by_contra hβ0
  apply hd'
  funext i
  have h1 := congrFun h i
  simp only [Pi.add_apply, Pi.smul_apply, Pi.zero_apply, smul_eq_mul, hα, zero_mul,
    zero_add] at h1
  exact (mul_eq_zero.mp h1).resolve_left hβ0

theorem exists_not_small (hK : Nat.card K = 2) (hζo : IsPrimitiveRoot ζ 3)
    (hL : Module.finrank K L = 2) (hs6 : F.s ≤ 6) {c : Fin F.s → ZMod 3} {i₀ : Fin F.s}
    (hc : ∀ i, c i ≠ 0 ↔ i = i₀) {B : Subgroup (StatedSp n K)} (hBE : B ≤ E)
    (hcB : F.tor c ∈ B) {d' : Fin F.s → ZMod 3} (hd'B : F.tor d' ∈ B) (hd'0 : d' i₀ = 0)
    (hd' : d' ≠ 0) (h3 : 3 ≤ (Finset.univ.filter fun i => i ≠ i₀ ∧ d' i = 0).card)
    (hker : ∀ f, F.tor f ∈ B → (∀ i, i ≠ i₀ → d' i = 0 → f i = 0) →
      ∃ α β : ZMod 3, f = α • c + β • d') :
    ∃ D₁ K₁ : Subgroup (StatedSp n K),
      LargeEvenStdSubPre 3 B (F.tor c) (spFixedFactor (F.tor c)) D₁ K₁ ∧ ¬ LargeEvenSmall K₁ := by
  classical
  have hζ : ζ ^ 3 = 1 := hζo.pow_eq_one
  have hci₀ : c i₀ ≠ 0 := (hc i₀).mpr rfl
  set Z₁ : Finset (Fin F.s) := Finset.univ.filter fun i => i ≠ i₀ ∧ d' i = 0 with hZ₁
  let D₁ : Subgroup (StatedSp n K) := Subgroup.closure {F.tor c, F.tor d'}
  let K₁ : Subgroup (StatedSp n K) := spFixedFactor (F.tor (c + d'))
  have hind : ∀ α β : ZMod 3, α • c + β • d' = 0 → α = 0 ∧ β = 0 :=
    independent_of_single F hc hd'0 hd'
  have hD₁B : D₁ ≤ B := by
    refine (Subgroup.closure_le B).mpr ?_
    rintro g (rfl | rfl)
    · exact hcB
    · exact hd'B
  have hDelem : IsElemAbelian 3 D₁ := isElemAbelian_closure_pair F hζ c d'
  have hDcard : Nat.card D₁ = 3 ^ 2 := by
    rw [card_closure_pair F hζo hind]
    norm_num
  have hxD : F.tor c ∈ D₁ := Subgroup.subset_closure (by simp)
  have hyD : F.tor d' ∈ D₁ := Subgroup.subset_closure (by simp)
  have hzD : F.tor (c + d') ∈ D₁ := by
    rw [F.tor_add hζ]
    exact mul_mem hxD hyD
  have hcondc : ∀ i, (c + d') i = 0 → c i = 0 := by
    intro i hi
    by_contra hci
    have hii : i = i₀ := (hc i).mp hci
    subst hii
    rw [Pi.add_apply, hd'0, add_zero] at hi
    exact hci hi
  have hcondd : ∀ i, (c + d') i = 0 → d' i = 0 := by
    intro i hi
    by_contra hdi
    by_cases hii : i = i₀
    · subst hii
      rw [Pi.add_apply, hd'0, add_zero] at hi
      exact hci₀ hi
    · have hci : c i = 0 := by
        by_contra h
        exact hii ((hc i).mp h)
      rw [Pi.add_apply, hci, zero_add] at hi
      exact hdi hi
  have hK₁x : K₁ ≤ Subgroup.centralizer {F.tor c} :=
    spFixedFactor_le_centralizer_tor F hK hζo hcondc
  have hK₁y : K₁ ≤ Subgroup.centralizer {F.tor d'} :=
    spFixedFactor_le_centralizer_tor F hK hζo hcondd
  have hK₁C : K₁ ≤ Subgroup.centralizer (D₁ : Set (StatedSp n K)) := by
    have hcl : Subgroup.centralizer (D₁ : Set (StatedSp n K)) =
        Subgroup.centralizer ({F.tor c, F.tor d'} : Set (StatedSp n K)) := by
      rw [show D₁ = Subgroup.closure ({F.tor c, F.tor d'} : Set (StatedSp n K)) from rfl,
        Subgroup.centralizer_closure]
    rw [hcl]
    intro g hg
    rw [Subgroup.mem_centralizer_iff]
    rintro h (rfl | rfl)
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hK₁x hg)).symm
    · exact (Subgroup.mem_centralizer_singleton_iff.mp (hK₁y hg)).symm
  have hK₁Lx : K₁ ≤ spFixedFactor (F.tor c) := by
    intro g hg
    refine mem_spFixedFactor_of_supp F hK hζo ?_ hg ?_
    · intro i hi
      have hii : i = i₀ := (hc i).mp hi
      subst hii
      simpa [Pi.add_apply, hd'0] using hi
    · exact Subgroup.mem_centralizer_singleton_iff.mp (hK₁x hg)
  have hzero : F.zeroSet (c + d') = Z₁ := by
    rw [hZ₁]
    exact zeroSet_add_eq F hc hd'0
  have hz_ne : c + d' ≠ 0 := by
    intro h
    have h1 : (c + d') i₀ = 0 := by rw [h, Pi.zero_apply]
    rw [Pi.add_apply, hd'0, add_zero] at h1
    exact hci₀ h1
  have hzne : (F.zeroSet (c + d')).Nonempty := by
    rw [hzero]
    exact Finset.card_pos.mp (by omega)
  have hsuppd' : (F.suppSet d').card ≤ 3 := by
    have hsum : (F.zeroSet d').card + (F.suppSet d').card = F.s := by
      have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin F.s)))
        (p := fun i => d' i = 0)
      simpa [ChoiceTwo.SpFrame.zeroSet, ChoiceTwo.SpFrame.suppSet, Nat.add_comm] using h
    have hnot : i₀ ∉ Z₁ := by
      rw [hZ₁]
      simp
    have hins : (insert i₀ Z₁).card = Z₁.card + 1 := Finset.card_insert_of_notMem hnot
    have hsub : insert i₀ Z₁ ⊆ F.zeroSet d' := by
      intro i hi
      rw [Finset.mem_insert] at hi
      rcases hi with rfl | hi
      · rw [ChoiceTwo.SpFrame.mem_zeroSet]
        exact hd'0
      · simp only [hZ₁, Finset.mem_filter, Finset.mem_univ, true_and] at hi
        rw [ChoiceTwo.SpFrame.mem_zeroSet]
        exact hi.2
    have hle : (insert i₀ Z₁).card ≤ (F.zeroSet d').card := Finset.card_le_card hsub
    omega
  have hqK₁ : CFSG.IsQuasisimple ↥K₁ := by
    have hdim : spFixedDim (F.tor (c + d')) = 2 * Z₁.card := by
      rw [F.spFixedDim_tor hζo hL, hzero]
    have hlist : SpFixedListed (F.tor (c + d')) := by
      refine ⟨by omega, ?_⟩
      omega
    have h42 : ¬ (spFixedDim (F.tor (c + d')) = 4 ∧ Nat.card K = 2) := by
      omega
    exact spFixedFactor_isQuasisimple (ℓ := 2) (f := 1) (x := F.tor (c + d'))
      (by rw [hK, pow_one]) Nat.prime_two le_rfl
      (F.blocks_tor hK hζo hz_ne) hlist h42
  have hKcomp : IsComponentOf K₁
      (spFixedFactor (F.tor c) ⊓ Subgroup.centralizer (D₁ : Set (StatedSp n K))) := by
    refine SpNonsplitComp.isComponentOf_of_normalizes (le_inf hK₁Lx hK₁C) ?_ hqK₁
    intro m hm g hg
    have hmD : m ∈ Subgroup.centralizer (D₁ : Set (StatedSp n K)) := hm.2
    have hmz : m ∈ Subgroup.centralizer {F.tor (c + d')} := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact (Subgroup.mem_centralizer_iff.mp hmD _ hzD).symm
    exact spFixedFactor_normalized (F.tor (c + d')) m hmz g hg
  have hQx : ∀ {Q : Subgroup (StatedSp n K)},
      IsComponentOf Q (spFixedFactor (F.tor c) ⊓
        Subgroup.centralizer (D₁ : Set (StatedSp n K))) → Q ≤ Subgroup.centralizer {F.tor c} :=
    fun hQ => (hQ.1.trans inf_le_left).trans (spFixedFactor_le_centralizer (F.tor c))
  have hQy : ∀ {Q : Subgroup (StatedSp n K)},
      IsComponentOf Q (spFixedFactor (F.tor c) ⊓
        Subgroup.centralizer (D₁ : Set (StatedSp n K))) → Q ≤ Subgroup.centralizer {F.tor d'} :=
    fun hQ =>
      (hQ.1.trans inf_le_right).trans
        (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hyD))
  have hlayer_le : LargeEvenLayer
      (spFixedFactor (F.tor c) ⊓ Subgroup.centralizer (D₁ : Set (StatedSp n K))) ≤ K₁ := by
    refine sSup_le ?_
    intro Q hQ
    have hperf : ⁅Q, Q⁆ = Q := LayerFacts.ggCommutator_eq_of_isQuasisimple
      ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native ↥Q).1 hQ.2.2)
    have hQd : Q ≤ spFixedFactor (F.tor d') :=
      F.le_spFixedFactor hK hζo hL hsuppd' hperf (hQy hQ)
    have hQK : Q ≤ spFixedFactor (F.tor (c + d')) := by
      intro g hg
      have h1 : g ∈ spFixedFactor (F.tor c) := hQ.1.trans inf_le_left hg
      have h2 : g ∈ spFixedFactor (F.tor d') := hQd hg
      simpa using mem_spFixedFactor_add F hK hζo h1 h2
    exact hQK
  have hK₁eq : K₁ = LargeEvenLayer
      (spFixedFactor (F.tor c) ⊓ Subgroup.centralizer (D₁ : Set (StatedSp n K))) :=
    le_antisymm (le_sSup hKcomp) hlayer_le
  have hD₁eq : D₁ = B ⊓ Subgroup.centralizer (K₁ : Set (StatedSp n K)) := by
    refine le_antisymm (le_inf hD₁B ?_) ?_
    · rw [Subgroup.le_centralizer_iff]
      exact hK₁C
    · rintro g ⟨hgB, hgC⟩
      have hgE : g ∈ E := hBE hgB
      obtain ⟨f, hf⟩ := F.mem_tor g hgE
      have hf0 : ∀ i, i ≠ i₀ → d' i = 0 → f i = 0 := by
        intro i hi hdi
        obtain ⟨j, hjZ, hji⟩ := Finset.exists_mem_ne (by omega : 1 < Z₁.card) i
        have hjZ' : j ≠ i₀ ∧ d' j = 0 := by
          simp only [hZ₁, Finset.mem_filter, Finset.mem_univ, true_and] at hjZ
          exact hjZ
        have hzi : (c + d') i = 0 := by
          have hci : c i = 0 := by
            by_contra h
            exact hi ((hc i).mp h)
          rw [Pi.add_apply, hci, hdi, add_zero]
        have hzj : (c + d') j = 0 := by
          have hcj : c j = 0 := by
            by_contra h
            exact hjZ'.1 ((hc j).mp h)
          rw [Pi.add_apply, hcj, hjZ'.2, add_zero]
        have hswF : F.swap i j false ∈ K₁ :=
          F.swap_mem_spFixedFactor hK hζo (c + d') false hzi hzj
        have hswT : F.swap i j true ∈ K₁ :=
          F.swap_mem_spFixedFactor hK hζo (c + d') true hzi hzj
        have hcf : F.swap i j false * F.tor f = F.tor f * F.swap i j false := by
          rw [hf]
          exact Subgroup.mem_centralizer_iff.mp hgC _ hswF
        have hct : F.swap i j true * F.tor f = F.tor f * F.swap i j true := by
          rw [hf]
          exact Subgroup.mem_centralizer_iff.mp hgC _ hswT
        have hf1 := eq_sgnZ_of_swap_comm F hζo (Ne.symm hji) false hcf
        have hf2 := eq_sgnZ_of_swap_comm F hζo (Ne.symm hji) true hct
        rw [sgnZ_false] at hf1
        rw [sgnZ_true] at hf2
        have hneg : f i = -f i := by
          rw [← hf1] at hf2
          exact hf2
        have h1 : f i + f i = 0 := by
          nth_rewrite 2 [hneg]
          exact add_neg_cancel _
        have h2 : (2 : ZMod 3) * f i = 0 := by
          rw [two_mul]
          exact h1
        exact (mul_eq_zero.mp h2).resolve_left (by decide)
      obtain ⟨α, β, hαβ⟩ := hker f (hf ▸ hgB) hf0
      rw [mem_closure_pair_iff F hζ]
      exact ⟨α, β, by rw [← hf, hαβ]⟩
  have hm3 : 3 ≤ (F.zeroSet (c + d')).card := by
    rw [hzero]
    exact h3
  have hnotsmall : ¬ LargeEvenSmall K₁ := by
    obtain ⟨e⟩ := nonempty_spFixedFactor_equiv F hK hζo hL hz_ne hzne
    have h7 : 7 ∣ Nat.card K₁ := by
      rw [Nat.card_congr e.toEquiv]
      exact SpRootBig.seven_dvd_card_statedSp K hm3
    exact IOneOrthEnd.not_largeEvenSmall_of_seven_dvd h7
  exact ⟨D₁, K₁, ⟨hD₁B, hDelem, hDcard, hxD, hK₁eq, hKcomp, hD₁eq⟩, hnotsmall⟩

end CFSG.StandardType.A6InsideSp

end

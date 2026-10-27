module

public import CFSG.Quasithin.EmptyFaithfulMultiple.InputB19Proof
public import CFSG.Quasithin.Background.B1MoreSeven
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentClassification.Quasisimple
public import CFSG.Quasithin.Background.B1MoreElevenA
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.Quasithin.EmptyFaithfulMultiple
open scoped commutatorElement

namespace B69

theorem card_sl2 : Nat.card (Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)) = 6 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_eq_two_of_sylow {Ω : Type*} [Group Ω] {H A : Subgroup Ω}
    (hH : Nonempty (↥H ≃* Matrix.SpecialLinearGroup (Fin 2) (ZMod 2)))
    (hA : CFSG.QuasithinUnique.IsSylowTwoOf A H) : Nat.card A = 2 := by
  obtain ⟨e⟩ := hH
  have h6 : Nat.card H = 6 := by rw [Nat.card_congr e.toEquiv, card_sl2]
  have : Finite ↥H := Finite.of_equiv _ e.symm.toEquiv
  have : Finite ↥A := Finite.of_injective (Subgroup.inclusion hA.1)
    (Subgroup.inclusion_injective hA.1)
  have h1 := Subgroup.card_mul_index (A.subgroupOf H)
  have h2 : Nat.card (A.subgroupOf H) = Nat.card A :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hA.1).toEquiv
  rw [h2, h6] at h1
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card).1 hA.2.1
  rw [hn] at h1
  have hodd := hA.2.2
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · interval_cases n
    · exfalso
      apply hodd
      simp at h1
      omega
    · simpa using hn
  · exfalso
    have h4 : 4 ∣ 6 := by
      rw [← h1]
      exact Dvd.dvd.mul_right (by
        have : (4 : ℕ) = 2 ^ 2 := by norm_num
        rw [this]
        exact pow_dvd_pow 2 hn2) _
    omega

variable {V : Type} [CommGroup V] [Finite V]

theorem not_rAV_lt_one_of_card_two (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsA2 X A) (h2 : Nat.card A = 2) : ¬ rAV A < 1 := by
  intro hlt
  have h := (rAV_lt_one_iff hV hA).1 hlt
  rw [h2] at h
  have hidx := B1.card_eq_index_mul A
  have hpos := B1.card_fixV_pos A
  have hi : (fixV A).index < 2 := by
    by_contra hge
    push Not at hge
    have : 2 * Nat.card (fixV A) ≤ Nat.card V := by
      rw [hidx]
      exact Nat.mul_le_mul_right _ hge
    omega
  have hi0 : 0 < (fixV A).index := Nat.pos_of_ne_zero Subgroup.index_ne_zero_of_finite
  have htop : fixV A = ⊤ := Subgroup.index_eq_one.1 (by omega)
  apply hA.2.1
  rw [eq_bot_iff]
  intro a ha
  rw [Subgroup.mem_bot]
  ext v
  have hv : v ∈ fixV A := by rw [htop]; trivial
  exact hv a ha

theorem strong_centralizes_fitting (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 X = ⊥) (hA : IsFFStarMin X A) (hs : rAV A < 1) :
    ⁅fittingOfSub X, A⁆ = ⊥ := by
  by_cases hJ : ⁅fittingOfSub X, ffJP {A | IsFFStarMin X A} X⁆ = ⊥
  · have hAJ : A ≤ ffJP {A | IsFFStarMin X A} X :=
      le_iSup₂_of_le (f := fun (B : Subgroup (MulAut V)) (_ : B ∈ {A | IsFFStarMin X A}) =>
        ⨆ (_ : B ≤ X), B) A hA (le_iSup (fun _ : A ≤ X => A) hA.1.1)
    exact le_bot_iff.1 (hJ ▸ Subgroup.commutator_mono le_rfl hAJ)
  · obtain ⟨s, H, h1, -, -, -, -, -, -, -, h4, -⟩ := CFSG.Quasithin.EmptyFaithfulMultiple.inputB19_holds V hV X hO2 hJ
    by_contra hne
    obtain ⟨i, hi⟩ := (h4 A).1 ⟨hA, hne⟩
    have hcard := card_eq_two_of_sylow (H := H i) (A := A) (h1 i).2 hi
    exact not_rAV_lt_one_of_card_two hV hA.1.isA2 hcard hs

omit [Finite V] in
theorem commutator_eq_of_ne_bot {K A : Subgroup (MulAut V)} (hK : CFSG.Open.IsQuasisimple ↥K)
    (hn : A ≤ Subgroup.normalizer (K : Set (MulAut V))) (hne : ⁅K, A⁆ ≠ ⊥) : ⁅K, A⁆ = K := by
  have hBn : ∀ b ∈ A, ∀ x ∈ K, b * x * b⁻¹ ∈ K := fun b hb x hx =>
    B19Aux.conj_mem_of_le_normalizer hn hb hx
  set N := ⁅K, A⁆ with hN
  have hNL : N ≤ K := by
    rw [hN, Subgroup.commutator_le]
    intro l hl b hb
    have h1 := hBn b hb l⁻¹ (K.inv_mem hl)
    have e : l * b * l⁻¹ * b⁻¹ = l * (b * l⁻¹ * b⁻¹) := by group
    show l * b * l⁻¹ * b⁻¹ ∈ K
    rw [e]
    exact K.mul_mem hl h1
  by_contra hne'
  have hnle : ¬ K ≤ N := fun h => hne' (le_antisymm hNL h)
  have hLN : ∀ l ∈ K, ∀ n ∈ N, l * n * l⁻¹ ∈ N := by
    intro l hl n hn'
    have hn'' : n ∈ ⁅A, K⁆ := by rw [Subgroup.commutator_comm]; exact hn'
    have := conj_mem_commutator (H := A) (A := K) hl hn''
    rw [Subgroup.commutator_comm] at this
    exact this
  have hcomm := B1Red.commute_of_normal_not_le hK
    (fun n hn' l hl => K.mul_mem (K.mul_mem (hNL hn') hl) (K.inv_mem (hNL hn'))) hLN hnle
  have hNc : N ≤ Subgroup.centralizer (K : Set (MulAut V)) := fun n hn' =>
    Subgroup.mem_centralizer_iff.2 fun l hl => (hcomm n hn' l hl).symm
  have hdouble : ⁅⁅K, A⁆, K⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.2 hNc
  have : Group.IsPerfect ↥K := ⟨hK.1⟩
  exact hne (CFSG.ComponentClassification.Quasisimple.perfect_double_commutator K A hdouble)

theorem exists_component (hV : ∀ v : V, v ^ 2 = 1) (hP4 : AsB15Part4) {X A : Subgroup (MulAut V)}
    (hO2 : pCoreOf 2 X = ⊥) (hA : IsFFStarMin X A) (hFA : ⁅fittingOfSub X, A⁆ = ⊥) :
    ∃ L : Subgroup (MulAut V), CFSG.Open.IsComponentOf L X ∧ ⁅L, A⁆ = L := by
  by_contra hno
  push Not at hno
  have hAX : A ≤ X := hA.1.1
  have hA2 : IsPGroup 2 ↥A := hA.1.2.2.1.isPGroup
  have hcomp : ∀ K : Subgroup (MulAut V), CFSG.Open.IsComponentOf K X → ⁅K, A⁆ = ⊥ := by
    intro K hK
    by_contra hne
    exact hno K hK (commutator_eq_of_ne_bot hK.2.2 (hP4 V hV X A hA.1 K hK) hne)
  have hFstar : quasithinGenFitting X ≤ Subgroup.centralizer (A : Set (MulAut V)) := by
    refine sup_le (sSup_le ?_) (sSup_le ?_)
    · rintro N ⟨hNX, hNn, hNnil⟩
      have hnil : Group.IsNilpotent (N.subgroupOf X) :=
        (Group.isNilpotent_congr (Subgroup.subgroupOfEquivOfLe hNX)).mpr hNnil
      have hle : N.subgroupOf X ≤ CFSG.fittingSubgroup ↥X := le_sSup ⟨hNn, hnil⟩
      have hNF : N ≤ fittingOfSub X := by
        intro x hx
        exact ⟨⟨x, hNX hx⟩, hle (by simpa [Subgroup.mem_subgroupOf] using hx), rfl⟩
      exact hNF.trans (Subgroup.commutator_eq_bot_iff_le_centralizer.1 hFA)
    · intro K hK
      exact Subgroup.commutator_eq_bot_iff_le_centralizer.1 (hcomp K hK)
  have hAF : A ≤ Subgroup.centralizer (quasithinGenFitting X : Set (MulAut V)) :=
    Subgroup.le_centralizer_iff.2 hFstar
  have hAC : A ≤ Subgroup.centralizer (X : Set (MulAut V)) :=
    centralizer_of_centralizes_genFitting (p := 2) hA2 (hAX.trans Subgroup.le_normalizer) hO2 hAF
  have hXA : X ≤ Subgroup.normalizer (A : Set (MulAut V)) := fun x hx =>
    Subgroup.centralizer_le_normalizer (A : Set (MulAut V)) ((Subgroup.le_centralizer_iff.1 hAC) hx)
  have hle : A ≤ pCoreOf 2 X := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hAX hXA hA2
  rw [hO2] at hle
  exact hA.1.2.1 (le_bot_iff.1 hle)

end B69

end CFSG.Quasithin

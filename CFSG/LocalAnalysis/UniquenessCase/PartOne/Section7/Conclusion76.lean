module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Steps
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76Basic
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.GroupTheory.PrimeField.SteinbergBNPowerComparison
import CFSG.RankThree.PartTwo.Sec3.ThreeGroupCentralizer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

@[expose] def Step74w (k : Sec7Core4 G) : Prop :=
  ∀ H : Subgroup G, Config k H → Nat.card ↥(CFSG.Open.pCoreOf 2 k.M ⊓ H) ≤ 2

theorem Step74.toWeak {k : Sec7Core4 G} (h : Step74 k) : Step74w k := by
  intro H hH
  rw [h H hH, Subgroup.card_bot]
  norm_num

theorem config_normalizer (k : Sec7Core4 G) {Y : Subgroup G} (hY : Y ≠ ⊥) (hYM : Y ≤ k.M)
    (hrank : 2 ≤ CFSG.Open.pRank k.p (k.M ⊓ Subgroup.normalizer (Y : Set G)))
    (hnot : ¬ Subgroup.normalizer (Y : Set G) ≤ k.M) :
    Config k (Subgroup.normalizer (Y : Set G)) where
  ne_top := by
    intro htop
    have hYnormal : Y.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff]
      exact htop
    rcases (k.standing.simple.eq_bot_or_eq_top_of_normal Y) with hbot | htopY
    · exact hY hbot
    · exact k.M_ne_top (top_le_iff.mp (htopY ▸ hYM))
  not_le := hnot
  two_le_pRank := by
    rw [inf_comm]
    exact hrank

theorem normalizer_le_of_step74 (k : Sec7Core4 G) (h74 : Step74 k) {Y : Subgroup G}
    (hY : Y ≠ ⊥) (hYM : Y ≤ k.M)
    (hrank : 2 ≤ CFSG.Open.pRank k.p (k.M ⊓ Subgroup.normalizer (Y : Set G)))
    (hQ : CFSG.Open.pCoreOf 2 k.M ⊓ Subgroup.normalizer (Y : Set G) ≠ ⊥) :
    Subgroup.normalizer (Y : Set G) ≤ k.M := by
  by_contra hnot
  exact hQ (h74 _ (k.config_normalizer hY hYM hrank hnot))

theorem normalizer_le_of_step74w (k : Sec7Core4 G) (h74 : Step74w k) {Y : Subgroup G}
    (hY : Y ≠ ⊥) (hYM : Y ≤ k.M)
    (hrank : 2 ≤ CFSG.Open.pRank k.p (k.M ⊓ Subgroup.normalizer (Y : Set G)))
    (hQ : 2 < Nat.card ↥(CFSG.Open.pCoreOf 2 k.M ⊓ Subgroup.normalizer (Y : Set G))) :
    Subgroup.normalizer (Y : Set G) ≤ k.M := by
  by_contra hnot
  exact absurd (h74 _ (k.config_normalizer hY hYM hrank hnot)) (not_le.mpr hQ)

theorem two_lt_card_pCoreOf_inf_centralizer {M E Y : Subgroup G} (hEM : E ≤ M)
    (hEE : E ≤ Subgroup.centralizer (E : Set G)) (hYE : Y ≤ E)
    (hnot : ¬ E ≤ Subgroup.centralizer
      ((CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G)) :
    2 < Nat.card ↥(CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (Y : Set G)) := by
  by_contra hle
  push Not at hle
  apply hnot
  intro e he
  have heQ : e ∈ Subgroup.normalizer (CFSG.Open.pCoreOf 2 M : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hEM he)
  have heC : e ∈ Subgroup.normalizer (Subgroup.centralizer (Y : Set G) : Set G) :=
    Subgroup.le_normalizer
      ((Subgroup.centralizer_le (show (Y : Set G) ⊆ (E : Set G) from hYE)) (hEE he))
  have hnorm : e ∈ Subgroup.normalizer
      ((CFSG.Open.pCoreOf 2 M ⊓ Subgroup.centralizer (Y : Set G) : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨heQ, heC⟩
  rw [Subgroup.mem_centralizer_iff]
  intro s hs
  exact CFSG.RankThree.PartTwo.Sec3.commute_of_card_le_two hle hnorm hs

theorem conclusion76_of_steps (k : Sec7Core4 G) (h74 : Step74w k) (h75 : Step75 k)
    (h72L : Step72L k) (h76C : Step76C k) :
    Conclusion76 k.M k.p := by
  classical
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  have hstrong : IsStronglyPEmbedded k.p k.M := k.strong
  intro r hr E hEM hE hEcard hEcent hX
  haveI : Fact r.Prime := ⟨hr⟩
  by_cases hrp : r = k.p
  · subst hrp
    exact rankThreeGamma_self_le hstrong hEM hE.isPGroup
  by_cases hr2 : r = 2
  · subst hr2
    exact rankThreeGamma_two_le hstrong (k.huniq) hE hX
  obtain ⟨Y, hYE, hYcard, hYnotcent⟩ :=
    exists_card_eq_not_le_centralizer_pCoreOf_inf_centralizer k.standing.charTwo
      k.maxLocal.1 hr2 hEM hE hEcard
  have hYne : Y ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at hYcard
    exact hr.ne_one hYcard.symm
  have hYM : Y ≤ k.M := hYE.trans hEM
  have hCQ : 2 < Nat.card ↥(CFSG.Open.pCoreOf 2 k.M ⊓ Subgroup.centralizer (Y : Set G)) :=
    two_lt_card_pCoreOf_inf_centralizer hEM
      (Subgroup.le_centralizer_iff_isMulCommutative.mpr hE.1) hYE hYnotcent
  have hQ : 2 < Nat.card ↥(CFSG.Open.pCoreOf 2 k.M ⊓ Subgroup.normalizer (Y : Set G)) :=
    hCQ.trans_le (Subgroup.card_le_of_le
      (inf_le_inf_left _ (Subgroup.centralizer_le_normalizer (Y : Set G))))
  have hNYM : Subgroup.normalizer (Y : Set G) ≤ k.M :=
    normalizer_le_of_step74w k h74 hYne hYM (by
      have h := hX Y hYE hYcard
      omega) hQ
  obtain ⟨y₀, hy₀⟩ := (isCyclic_of_prime_card (p := r) hYcard).exists_generator
  have hy₀ord : orderOf (y₀ : G) = r := by
    rw [Subgroup.orderOf_coe, orderOf_eq_card_of_forall_mem_zpowers (fun x => hy₀ x), hYcard]
  have hy₀z : Subgroup.zpowers (y₀ : G) = Y := by
    refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr y₀.2) ?_
    rw [hYcard, Nat.card_zpowers, hy₀ord]
  obtain ⟨y, hyY, hyord, hYz⟩ : ∃ y : G, y ∈ Y ∧ orderOf y = r ∧ Subgroup.zpowers y = Y :=
    ⟨(y₀ : G), y₀.2, hy₀ord, hy₀z⟩
  have hN : ∀ X : Subgroup G, X ≤ E → Nat.card X = r →
      Subgroup.normalizer (X : Set G) ≤ k.M := by
    intro X hXE hXcard
    by_contra hXM
    set H : Subgroup G := Subgroup.normalizer (X : Set G) with hHdef
    have hXne : X ≠ ⊥ := by
      intro hbot
      rw [hbot, Subgroup.card_bot] at hXcard
      exact hr.ne_one hXcard.symm
    have hHtop : H ≠ ⊤ := by
      intro htop
      have hXnormal : X.Normal := by
        rw [← Subgroup.normalizer_eq_top_iff]
        exact hHdef ▸ htop
      haveI : X.Normal := hXnormal
      rcases (k.standing.simple.eq_bot_or_eq_top_of_normal X) with hbot | htopX
      · exact hXne hbot
      · have hEtop : E = ⊤ := top_le_iff.mp (htopX ▸ hXE)
        exact k.M_ne_top (top_le_iff.mp (hEtop ▸ hEM))
    have hConfig : Config k H :=
      { ne_top := hHtop
        not_le := hXM
        two_le_pRank := by
          have h := hX X hXE hXcard
          rw [hHdef, inf_comm]
          omega }
    let K : Subgroup G := (CFSG.pPrimeCore k.p ↥H).map H.subtype
    let J : Subgroup G := layerLift k.p H
    have hKcop : Nat.Coprime k.p (Nat.card K) := by
      dsimp [K]
      rw [Subgroup.card_map_of_injective H.subtype_injective]
      exact CFSG.pPrimeCore_coprime_card
    have hKnotdvd : ¬ k.p ∣ Nat.card K :=
      (Fact.out : k.p.Prime).coprime_iff_not_dvd.mp hKcop
    have hcommJK : ⁅J, K⁆ = ⊥ := by
      simpa [J, K] using h75 H hConfig
    have hcentJK : J ≤ Subgroup.centralizer (K : Set G) :=
      (Subgroup.commutator_eq_bot_iff_le_centralizer (H₁ := J) (H₂ := K)).mp hcommJK
    have hnotYK : ¬ Y ≤ K := by
      intro hYK
      apply h72L H hConfig
      have hJM : J ≤ k.M :=
        (hcentJK.trans (Subgroup.centralizer_le hYK)).trans
          ((Subgroup.centralizer_le_normalizer (Y : Set G)).trans hNYM)
      simpa [J] using hJM
    have hyK : y ∉ K := by
      intro hyMem
      apply hnotYK
      rw [← hYz]
      exact Subgroup.zpowers_le.mpr hyMem
    obtain ⟨x, hxMCE, hxord⟩ :=
      CFSG.GroupTheory.exists_mem_orderOf_eq_of_one_le_pRank (p := k.p) (Fact.out : k.p.Prime)
        hEcent
    have hxH : x ∈ H := by
      rw [hHdef]
      exact (Subgroup.centralizer_le_normalizer (X : Set G))
        ((Subgroup.centralizer_le (show (X : Set G) ⊆ (E : Set G) from hXE)) hxMCE.2)
    have hxHM : x ∈ H ⊓ k.M := ⟨hxH, hxMCE.1⟩
    have hxP : IsPGroup k.p (Subgroup.zpowers x) :=
      IsPGroup.of_card (G := Subgroup.zpowers x) (n := 1) (by
        rw [Nat.card_zpowers, hxord, pow_one])
    have hxK : x ∉ K := by
      intro hxMem
      have hdvd : k.p ∣ Nat.card K := by
        rw [← hxord]
        exact Subgroup.orderOf_dvd_natCard K hxMem
      exact hKnotdvd hdvd
    have hyE : y ∈ E := hYE hyY
    have hyH : y ∈ H := by
      rw [hHdef]
      exact (Subgroup.centralizer_le_normalizer (X : Set G))
        ((Subgroup.centralizer_le (show (X : Set G) ⊆ (E : Set G) from hXE))
          ((Subgroup.le_centralizer_iff_isMulCommutative.mpr hE.1) hyE))
    have hyHM : y ∈ H ⊓ k.M := ⟨hyH, hYM hyY⟩
    have hxy : x * y = y * x :=
      (Subgroup.mem_centralizer_iff.mp hxMCE.2 y hyE).symm
    obtain ⟨j, hjJ, hjP, hjM, hjcomm⟩ :=
      h76C H hConfig x y hxHM hyHM hxP hxK (by rw [hyord]; exact hr)
        (by rw [hyord]; exact hr2) (by rw [hyord]; exact hrp) hyK hxy
    let c' : G := ⁅j, y⁆
    have hcK : c' ∈ K := by
      rw [show c' = j * y * j⁻¹ * y⁻¹ by simp [c', commutatorElement_def]]
      exact hjcomm
    have hcj : Commute c' j := Subgroup.mem_centralizer_iff.mp (hcentJK hjJ) c' hcK
    obtain ⟨e, he⟩ := hjP.exists_card_eq
    have hjpow : j ^ Nat.card (Subgroup.zpowers j) = 1 := by
      rw [Nat.card_zpowers]
      exact pow_orderOf_eq_one j
    have hcpow : c' ^ Nat.card (Subgroup.zpowers j) = 1 := by
      have h := CFSG.commutator_pow_eq_one_of_pow_eq_one_of_commute
        (x := j) (g := y) (p := Nat.card (Subgroup.zpowers j))
        (by simpa [c'] using hcj) hjpow
      simpa [c'] using h
    have hcop : Nat.Coprime (Nat.card (Subgroup.zpowers j)) (Nat.card K) := by
      rw [he]
      exact Nat.Coprime.pow_left e hKcop
    have hc1 : c' = 1 := by
      exact CFSG.GroupTheory.PrimeField.eq_one_of_pow_eq_one_of_coprime hcK hcop.symm hcpow
    have hjy : j * y = y * j := by
      have hpc : j * y * j⁻¹ * y⁻¹ = 1 := by
        simpa [c', commutatorElement_def] using hc1
      calc j * y = (j * y * j⁻¹ * y⁻¹) * (y * j) := by group
        _ = y * j := by rw [hpc]; simp
    have hjC : j ∈ Subgroup.centralizer (Y : Set G) := by
      rw [← hYz, Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff]
      exact hjy
    exact hjM (hNYM ((Subgroup.centralizer_le_normalizer (Y : Set G)) hjC))
  exact rankThreeGamma_le_of_forall_normalizer_le hstrong hE hX hN

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

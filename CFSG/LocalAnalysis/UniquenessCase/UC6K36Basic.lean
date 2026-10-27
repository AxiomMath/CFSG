module

public import CFSG.LocalAnalysis.UniquenessCase.UC6Dict
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6

structure Hyp36 (G : Type) [Group G] [Finite G] (M : Subgroup G) (p : ℕ) (E : Subgroup G) : Prop where
  ne_top : M ≠ ⊤
  pCore_ne_bot : pCoreOf 2 M ≠ ⊥
  prime : p.Prime
  odd : p ≠ 2
  elem : IsElemAbelian p E
  card : Nat.card E = p ^ 2
  gamma : rankThreeGamma 1 p E ≤ M
  uniq : calMOf E = {M}

namespace Hyp36

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ} (h : Hyp36 G M p E)
include h

theorem E_le : E ≤ M := by
  have : M ∈ calMOf E := by rw [h.uniq]; rfl
  exact this.2

theorem maxTwoLocal : IsMaxTwoLocalSubgroup M := by
  have : M ∈ calMOf E := by rw [h.uniq]; rfl
  exact this.1

theorem isPGroup : IsPGroup p E := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  exact IsPGroup.of_card (n := 2) (by rw [h.card])

theorem pCoreOf_top_eq_bot : pCoreOf 2 (⊤ : Subgroup G) = ⊥ := by
  by_contra hne
  have hp : IsPGroup 2 (pCoreOf 2 (⊤ : Subgroup G)) := by
    rw [pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  have hloc : IsTwoLocal (⊤ : Subgroup G) := by
    refine ⟨pCoreOf 2 ⊤, hne, hp, ?_⟩
    have hn : ((pCoreOf 2 (⊤ : Subgroup G)).subgroupOf ⊤).Normal := by
      rw [CFSG.openPCoreOf_subgroupOf 2 ⊤]
      exact CFSG.pCore_normal
    exact (eq_top_iff.2 ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).1 hn)).symm
  have hmax : IsMaxTwoLocalSubgroup (⊤ : Subgroup G) :=
    ⟨hloc, fun H _ hle => top_le_iff.1 hle⟩
  have : (⊤ : Subgroup G) ∈ calMOf E := ⟨hmax, le_top⟩
  rw [h.uniq] at this
  exact h.ne_top this.symm

theorem inU : InU M E := by
  refine ⟨h.E_le, fun g hg => ?_⟩
  have hmem : uniqueFourConj g M ∈ calMOf E := ⟨isMaxTwoLocal_conj h.maxTwoLocal g, hg⟩
  rw [h.uniq] at hmem
  exact hmem

theorem mem_of_conj_le {g : G} (hg : ∀ x ∈ E, g⁻¹ * x * g ∈ M) : g ∈ M :=
  ((inU_iff_fixed (normalizer_eq_of_isMaxTwoLocal h.maxTwoLocal)).1 h.inU).2 g hg

theorem normalizer_le_of_le {X : Subgroup G} (hEX : E ≤ X) (hXM : X ≤ M) :
    normalizer (X : Set G) ≤ M := by
  have hM := normalizer_eq_of_isMaxTwoLocal h.maxTwoLocal
  exact (show InU M X from ⟨hXM, fun g hg => h.inU.2 g (hEX.trans hg)⟩).normalizer_le hM

theorem le_of_isPGroup {P : Subgroup G} (hP : IsPGroup p P) (hEP : E ≤ P) : P ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  set X : Subgroup G := P ⊓ M with hX
  have hEX : E ≤ X := le_inf hEP h.E_le
  by_contra hPM
  have hXP : X < P :=
    lt_of_le_of_ne (fun x hx => (Subgroup.mem_inf.1 hx).1) (fun heq => hPM (heq ▸ inf_le_right))
  haveI : Group.IsNilpotent P := hP.isNilpotent
  have hnc := normalizerCondition_of_isNilpotent (G := P)
  have hlt : X.subgroupOf P < (⊤ : Subgroup P) := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hXP.ne
    ext x
    constructor
    · exact fun hx => (Subgroup.mem_inf.1 hx).1
    · intro hx
      have : (⟨x, hx⟩ : P) ∈ X.subgroupOf P := htop ▸ Subgroup.mem_top _
      exact this
  obtain ⟨y, hyN, hyX⟩ := SetLike.exists_of_lt (hnc _ hlt)
  have hXP' : ∀ z : G, z ∈ X → z ∈ P := fun z hz => (Subgroup.mem_inf.1 hz).1
  have hyNG : (y : G) ∈ normalizer (X : Set G) := by
    rw [mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      exact (mem_normalizer_iff.1 hyN ⟨x, hXP' x hx⟩).1 hx
    · intro hx
      have hxP : x ∈ P := by
        have h1 : (y : G)⁻¹ * ((y : G) * x * (y : G)⁻¹) * (y : G) ∈ P :=
          P.mul_mem (P.mul_mem (P.inv_mem y.2) (hXP' _ hx)) y.2
        simpa [mul_assoc] using h1
      exact (mem_normalizer_iff.1 hyN ⟨x, hxP⟩).2 hx
  have hyM : (y : G) ∈ M := h.normalizer_le_of_le hEX (fun z hz => (Subgroup.mem_inf.1 hz).2) hyNG
  exact hyX (show (y : G) ∈ X from Subgroup.mem_inf.2 ⟨y.2, hyM⟩)

theorem normal_pCoreOf_top (q : ℕ) : (pCoreOf q (⊤ : Subgroup G)).Normal := by
  have hn : ((pCoreOf q (⊤ : Subgroup G)).subgroupOf ⊤).Normal := by
    rw [CFSG.openPCoreOf_subgroupOf q ⊤]
    exact CFSG.pCore_normal
  exact Subgroup.normalizer_eq_top_iff.1
    (eq_top_iff.2 ((Subgroup.normal_subgroupOf_iff_le_normalizer le_top).1 hn))

theorem pCoreOf_le : pCoreOf p (⊤ : Subgroup G) ≤ M := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI := h.normal_pCoreOf_top p
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow h.isPGroup
  have hO : IsPGroup p (pCoreOf p (⊤ : Subgroup G)) := by
    rw [pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  exact (hO.le_sylow_of_normal P).trans (h.le_of_isPGroup P.isPGroup' hEP)

theorem comm_pCoreOf_top {q x : G} (hq : q ∈ pCoreOf 2 M) (hx : x ∈ pCoreOf p (⊤ : Subgroup G)) :
    q * x = x * q := by
  haveI : Fact p.Prime := ⟨h.prime⟩
  haveI := h.normal_pCoreOf_top p
  have hxM : x ∈ M := h.pCoreOf_le hx
  have hQn : ((pCoreOf 2 M).subgroupOf M).Normal := by
    rw [CFSG.openPCoreOf_subgroupOf 2 M]
    exact CFSG.pCore_normal
  have hQM : pCoreOf 2 M ≤ M := CFSG.openPCoreOf_le 2 M
  have h1 : x * q * x⁻¹ ∈ pCoreOf 2 M := by
    have := hQn.conj_mem ⟨q, hQM hq⟩ hq ⟨x, hxM⟩
    exact this
  have h2 : q * x * q⁻¹ ∈ pCoreOf p (⊤ : Subgroup G) := (inferInstance : (pCoreOf p ⊤).Normal).conj_mem x hx q
  have hc : (x * q * x⁻¹) * q⁻¹ ∈ pCoreOf 2 M ⊓ pCoreOf p (⊤ : Subgroup G) := by
    refine Subgroup.mem_inf.2 ⟨(pCoreOf 2 M).mul_mem h1 ((pCoreOf 2 M).inv_mem hq), ?_⟩
    have h3 : x * (q * x⁻¹ * q⁻¹) ∈ pCoreOf p (⊤ : Subgroup G) :=
      (pCoreOf p ⊤).mul_mem hx (by
        have := (pCoreOf p ⊤).inv_mem h2
        simpa [mul_assoc] using this)
    simpa [mul_assoc] using h3
  have hcoprime : (pCoreOf 2 M ⊓ pCoreOf p (⊤ : Subgroup G)) = ⊥ := by
    have hQ2 : IsPGroup 2 (pCoreOf 2 M) := by
      rw [pCoreOf]
      exact CFSG.pCore_isPGroup.map _
    have hO : IsPGroup p (pCoreOf p (⊤ : Subgroup G)) := by
      rw [pCoreOf]
      exact CFSG.pCore_isPGroup.map _
    obtain ⟨a, ha⟩ := hQ2.exists_card_eq
    obtain ⟨b, hb⟩ := hO.exists_card_eq
    refine Subgroup.inf_eq_bot_of_coprime ?_
    rw [ha, hb]
    exact Nat.Coprime.pow _ _ ((Nat.coprime_primes Nat.prime_two h.prime).2 (Ne.symm h.odd))
  rw [hcoprime, Subgroup.mem_bot] at hc
  have h4 : x * q * x⁻¹ = q := by
    calc x * q * x⁻¹ = (x * q * x⁻¹ * q⁻¹) * q := by group
      _ = q := by rw [hc, one_mul]
  calc q * x = (x * q * x⁻¹) * x := by rw [h4]
    _ = x * q := by group

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK

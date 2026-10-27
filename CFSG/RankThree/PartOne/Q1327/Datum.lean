module

public import CFSG.RankThree.PartOne.Q1327.Quasi
public import CFSG.RankThree.PartOne.N143.SectionListBound

public section

namespace CFSG.RankThree.PartOne.Q1327

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320
  CFSG.RankThree.PartOne.K1327
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}
  {f r : ℕ} {R : Subgroup G} {s s' zs : MulAut E}

theorem S_le_Jc (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G} (hJ : JcData p E c R s Jc)
    {A₀ S : Subgroup G} (hSJ : S ≤ Jof p R) (hA₀E : A₀ ≤ E) (hSA₀ : ⁅S, A₀⁆ = S) : S ≤ Jc := by
  have hnorm := Jof_le_normalizer H hJ
  rw [← hSA₀, Subgroup.commutator_le]
  intro x hx a ha
  have hxN : x ∈ Subgroup.normalizer (Jc : Set G) := hnorm (hSJ hx)
  have haJ : a ∈ Jc := hJ.E_le (hA₀E ha)
  have h1 : x * a * x⁻¹ ∈ Jc := (Subgroup.mem_normalizer_iff.mp hxN a).mp haJ
  rw [commutatorElement_def]
  exact mul_mem h1 (inv_mem haJ)

theorem mem_torusImage_Jc (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) {t : MulAut E} (ht : t ∈ clsOf p E s) : t ∈ torusImage E Jc := by
  obtain ⟨-, hKt, -, -⟩ := class_facts H (Or.inl rfl) ht
  obtain ⟨-, -, -, -, k, hk, hkK, hkt⟩ := hKt
  exact Sec12Three.mem_torusImage_iff.2 ⟨k, hJ.K_le t ht hkK, hk, hkt⟩

theorem t123Base_Jc (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (hTwo : TwoActionInputs)
    (hFull : K156.Full106Stmt) (H : Hyp G p A c L E f r R s s' zs) {Jc : Subgroup G}
    (hJ : JcData p E c R s Jc) {A₀ S : Subgroup G} (hA₀E : A₀ ≤ E)
    (hA₀el : IsElementaryAbelian p ↥A₀) (hA₀card : Nat.card A₀ = p ^ 2) (hSJ : S ≤ Jof p R)
    (hS1 : S ≠ ⊥) (hS2 : IsPGroup 2 ↥S) (hA₀S : A₀ ≤ Subgroup.normalizer (S : Set G))
    (hSA₀ : ⁅S, A₀⁆ = S) : T123Base p Jc A₀ E := by
  have h := H.h12
  have hp := h.prime
  have hcard : Nat.card E = p ^ 3 := by rw [H.hEA]; exact h.A_card
  have hSJc := S_le_Jc H hJ hSJ hA₀E hSA₀
  refine ⟨hp, Sec12Three.five_le h, (Jc_isQuasisimple hGA hS hRe hTwo hFull H hJ).1,
    (CFSG.RankThree.PartOne.Sec9A.evenRank_subgroup_le Jc).trans h.evenRank_eq.le,
    center_Jc_pPrime H hJ, hA₀E.trans hJ.E_le, hA₀el, hA₀card, ⟨S, hSJc, hS1, hS2, hA₀S, hSA₀.symm⟩,
    hJ.E_le, h.E_elem, hcard, hA₀E, ?_, ?_⟩
  · intro e he
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact congrArg Subtype.val (h.E_elem.is_comm.comm (⟨a, hA₀E ha⟩ : ↥E) ⟨e, he⟩)
  · intro F' hF'L hF'el hF'c hEF'
    refine h.E_max F' hF'el ?_ hEF'
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have haE : a ∈ F' := hEF' (show a ∈ E by rw [H.hEA]; exact ha)
    exact congrArg Subtype.val (hF'el.is_comm.comm (⟨a, haE⟩ : ↥F') ⟨x, hx⟩)

theorem list_Jc (hSLB : N143.SectionListBound) (H : Hyp G p A c L E f r R s s' zs)
    {Jc : Subgroup G} (hJ : JcData p E c R s Jc) (hq : CFSG.IsQuasisimple ↥Jc) :
    Census3.TheoremThreeList (↥Jc ⧸ Subgroup.center ↥Jc) := by
  have h := H.h12
  have hK : CFSG.IsKGroup ↥(Subgroup.centralizer (R : Set G)) :=
    h.setup.2.2.1 _ (centralizer_R_ne_top H)
  have he : CFSG.Assembly.evenRank ↥(Subgroup.centralizer (R : Set G)) ≤ 3 :=
    (CFSG.RankThree.PartOne.Sec9A.evenRank_subgroup_le _).trans h.evenRank_eq.le
  have e := Subgroup.subgroupOfEquivOfLe hJ.le_M
  exact (hSLB.listHyp hK he (Jc.subgroupOf (Subgroup.centralizer (R : Set G))) hq e.toMonoidHom
    e.surjective).onList

end CFSG.RankThree.PartOne.Q1327

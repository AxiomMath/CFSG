module

public import CFSG.RankThree.PartOne.KE8F.HIFix

public noncomputable section

namespace CFSG.RankThree.PartOne.KE8F

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley CFSG.RankThree.Lattice CFSG.RankThree.PartOne.KE
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.ComponentClassification.OuterAutomorphisms CFSG.RankThree.LocalRank
open scoped Matrix Pointwise MatrixGroups commutatorElement

set_option linter.unusedSectionVars false


section Inner

variable {K L : Type} [Field K] [Finite K] [Field L] [Algebra K L] [IsAlgClosed L] {ℓ f p : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem eq_one_of_commute_pinnedX {Y : ModGL .E8 L} (hYmem : Y ∈ adjointGroup .E8 L)
    (h : ∀ α, IsRoot .E8 α → ∀ t : L, pinnedX .E8 L α t * Y = Y * pinnedX .E8 L α t) :
    Y = 1 := by
  have hle : adjointGroup .E8 L ≤ Subgroup.centralizer ({Y} : Set (ModGL .E8 L)) := by
    refine (Subgroup.closure_le _).2 ?_
    rintro g ⟨i, t, hg⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    subst hy
    rcases hg with hg | hg
    · have hgx : g = xUnit .E8 L i t := Units.ext hg
      rw [hgx, ← pinnedX_single]
      exact (h (Pi.single i 1) (IsRoot.basis i) t).symm
    · have hgy : g = yUnit .E8 L i t := Units.ext hg
      rw [hgy, ← pinnedX_neg_single]
      exact (h (-Pi.single i 1) (IsRoot.neg (IsRoot.basis i)) t).symm
  have hcen : (⟨Y, hYmem⟩ : adjointGroup .E8 L) ∈ Subgroup.center (adjointGroup .E8 L) := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subtype.ext (Subgroup.mem_centralizer_iff.1 (hle g.2) Y rfl).symm
  rw [center_adjointGroup_eq_bot_field .E8 L] at hcen
  exact congrArg Subtype.val (Subgroup.mem_bot.1 hcen)

theorem rootDiagUnit_mem_centralizer_cls {Fr : L →+* L} {b : Fin Tag.E8.rank → Lˣ}
    (hb : b ∈ fixedCharTuples e8P4V Fr) {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α)
    (h1 : rootChar b α = 1) :
    rootDiagUnit .E8 b ∈ Subgroup.centralizer (rootSpan .E8 L (cls α) : Set (ModGL .E8 L)) := by
  have hF : ∀ a ∈ ({b} : Set (Fin Tag.E8.rank → Lˣ)), a ∈ fixedCharTuples e8P4V Fr := by
    intro a ha
    rw [Set.mem_singleton_iff] at ha
    rw [ha]
    exact hb
  have hα' : α ∈ famKernel ({b} : Set (Fin Tag.E8.rank → Lˣ)) :=
    ⟨hα, fun a ha => by rw [Set.mem_singleton_iff] at ha; rw [ha]; exact h1⟩
  have hsub : cls α ⊆ rootCharKernel b := by
    intro γ hγ
    have hγ' : γ ∈ famKernel ({b} : Set (Fin Tag.E8.rank → Lˣ)) := by
      rcases mem_cls_iff.1 hγ with rfl | rfl | rfl | rfl
      · exact hα'
      · exact famKernel_neg' hα'
      · exact famKernel_v hF hα'
      · exact famKernel_neg' (famKernel_v hF hα')
    exact famKernel_subset _ (Set.mem_singleton b) hγ'
  have hle := rootSpan_le_centralizer (K := L) b hsub
  rw [Subgroup.mem_centralizer_iff]
  intro g hg
  exact Subgroup.mem_centralizer_singleton_iff.1 (hle hg)

theorem exists_visible (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hpf : p ∣ Nat.card K * Nat.card K + 1) (c : adjointGroup .E8 K)
    {A₀ : Subgroup (adjointGroup .E8 K)} (hA₀ : A₀ ≤ torsionC p F c) (hcard : Nat.card A₀ = p ^ 2)
    {α : Fin Tag.E8.rank → ℤ} (hα : IsRoot .E8 α) :
    ∃ x ∈ A₀, x ≠ 1 ∧ psiC F c x ∈
      Subgroup.centralizer (rootSpan .E8 L (cls α) : Set (ModGL .E8 L)) := by
  have hpℓ : ¬ ℓ ∣ p := not_dvd_char hf hK hp hpf
  have hYT : ∀ y ∈ A₀, psiC F c y ∈
      twistedTorusOf F.n (Units.map (entrywiseHom (iterateFrobenius L ℓ f))) :=
    fun y hy => torsionC_torus F c (hA₀ hy)
  have hYp : ∀ y ∈ A₀, y ^ p = 1 := fun y hy => torsionC_pow F c (hA₀ hy)
  have hle := tupleGroup_le_T0tors F c hYT hYp
  have hcard' : p ^ 2 ≤ Nat.card (tupleGroup F c A₀) := by
    rw [card_tupleGroup F c hYT, hcard]
  obtain ⟨b, hb, hb1, hbα⟩ := exists_ne_one_trivial hp hpℓ hle hcard' α
  have hbT := hle (show b ∈ tupleGroup F c A₀ from hb)
  obtain ⟨y, hy, hyb⟩ := hb
  have hyb' : psiC F c y = rootDiagUnit .E8 b := hyb
  refine ⟨y, hy, ?_, ?_⟩
  · intro h1
    apply hb1
    apply rootDiagUnit_injective (τ := .E8) (K := L)
    rw [← hyb', h1, map_one, rootDiagUnit_one]
  · rw [hyb']
    exact rootDiagUnit_mem_centralizer_cls hbT.1 hα hbα

theorem inner_core_trivial (F : E8P4Frame0 K L ℓ f) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f)
    (hp : p.Prime) (hp10 : 10 < p) (hpf : p ∣ Nat.card K * Nat.card K + 1)
    (hC : Subgroup.center (adjointGroup .E8 K) = ⊥) (c : adjointGroup .E8 K)
    (hcard : Nat.card (torsionC p F c) = p ^ 4) {A₀ : Subgroup (adjointGroup .E8 K)}
    (hA₀ : A₀ ≤ torsionC p F c) (hA₀card : Nat.card A₀ = p ^ 2)
    {B : Subgroup (MulAut (adjointGroup .E8 K))}
    (hB : (MulAut.conj : adjointGroup .E8 K →* MulAut (adjointGroup .E8 K)).range ≤ B)
    {w : adjointGroup .E8 K}
    (hw : ∀ x ∈ A₀, x ≠ 1 → (MulAut.conj w : MulAut (adjointGroup .E8 K)) ∈ coreR p B x) :
    w = 1 := by
  apply psiC_injective F c
  rw [map_one]
  refine eq_one_of_commute_pinnedX (psiC_mem_adjoint F c w) fun α hα t => ?_
  obtain ⟨x, hxA, hx1, hvis⟩ := exists_visible F hf hK hp hpf c hA₀ hA₀card hα
  have hwR := hw x hxA hx1
  have hwM := coreR_le_coreM B x hwR
  have hwx : w ∈ Subgroup.centralizer ({x} : Set (adjointGroup .E8 K)) := by
    have := fix_of_mem_coreM hC hwM
    refine Subgroup.mem_centralizer_singleton_iff.2 ?_
    have h2 : w * x * w⁻¹ = x := by simpa [MulAut.conj_apply] using this
    calc w * x = (w * x * w⁻¹) * w := by group
      _ = x * w := by rw [h2]
  have hwV : w ∈ coreV p B x := mem_coreV.2 ⟨hwR, hwx⟩
  obtain ⟨P, hP, hrat, hfix⟩ := eta_fixes_pairC F hf hK hp hp10 hpf hC c hcard (hA₀ hxA) hB hα hvis
  have hcomm : ∀ i : Unit, ∀ u ∈ P i, psiC F c w * u = u * psiC F c w := by
    intro i u hu
    obtain ⟨d, hd⟩ := hrat u hu
    have h := (hfix d (by rw [hd]; exact hu)).1 w hwV
    rw [← hd, ← map_mul, ← map_mul, h]
  have hT := coreV_le_torus F hf hK hp hp10 hpf hC c hcard (hA₀ hxA) hB w hwV
  obtain ⟨hwH, hwfix⟩ := mem_twistedTorusOf.1 hT
  have hmem := hP.2.2.2.2.2.2 (psiC F c w) (Subgroup.mem_sup_left hwH)
    (mem_twistedFixedPoints.2 hwfix) hcomm
  exact Subgroup.mem_centralizer_iff.1 hmem.2 (pinnedX .E8 L α t)
    (pinnedX_mem_rootSpan (mem_cls_iff.2 (Or.inl rfl)) t)

end Inner

end CFSG.RankThree.PartOne.KE8F

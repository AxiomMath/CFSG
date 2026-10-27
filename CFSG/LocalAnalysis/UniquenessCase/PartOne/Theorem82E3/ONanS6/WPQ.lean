module

public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.LieType.SeitzGeneration.SubfieldPairSUPhan
public import CFSG.LocalAnalysis.AGLEmbedding.SeitzEqTwo.DescentE
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KS1523ON.NoIndex
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.LocalAnalysis.UniquenessCase.UC1K326P1Inner
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.LocalRank.InvolutionCentralizerLocalRank
public import CFSG.RankThree.PartOne.SP4GA.Pointwise
public import CFSG.RankThree.PartTwo.KFacts.KS21Mult
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.ONAut.Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan
section
open CFSG.Open
open CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo.Sec4
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data IsSpor IsAlt)
open scoped commutatorElement
variable {G : Type} [Group G] [Finite G]
variable {D : Data G}

@[expose] def modCentralizer (M L O : Subgroup G) : Subgroup G where
  carrier := {m | m ∈ M ∧ m ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L, ⁅m, l⁆ ∈ O}
  one_mem' := by
    refine ⟨M.one_mem, Subgroup.one_mem _, ?_⟩
    intro l _
    simp
  mul_mem' := by
    intro m₁ m₂ hm₁ hm₂
    obtain ⟨hm₁M, hm₁N, hm₁⟩ := hm₁
    obtain ⟨hm₂M, hm₂N, hm₂⟩ := hm₂
    refine ⟨M.mul_mem hm₁M hm₂M, Subgroup.mul_mem _ hm₁N hm₂N, fun l hl => ?_⟩
    have hl₂ : m₂ * l * m₂⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hm₂N l).mp hl
    have h1 : ⁅m₁, m₂ * l * m₂⁻¹⁆ ∈ O := hm₁ _ hl₂
    have h2 : ⁅m₂, l⁆ ∈ O := hm₂ l hl
    rw [show ⁅m₁ * m₂, l⁆ = ⁅m₁, m₂ * l * m₂⁻¹⁆ * ⁅m₂, l⁆ by
      simp only [commutatorElement_def]
      group]
    exact O.mul_mem h1 h2
  inv_mem' := by
    intro m hm
    obtain ⟨hmM, hmN, hm⟩ := hm
    refine ⟨M.inv_mem hmM, Subgroup.inv_mem _ hmN, fun l hl => ?_⟩
    have hl' : m⁻¹ * l * m ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hmN) l).mp hl
    have h1 : ⁅m, m⁻¹ * l * m⁆ ∈ O := hm _ hl'
    rw [show ⁅m⁻¹, l⁆ = (⁅m, m⁻¹ * l * m⁆)⁻¹ by
      simp only [commutatorElement_def]
      group]
    exact O.inv_mem h1

theorem mem_modCentralizer_iff {M L O : Subgroup G} {m : G} :
    m ∈ modCentralizer M L O ↔
      m ∈ M ∧ m ∈ Subgroup.normalizer (L : Set G) ∧ ∀ l ∈ L, ⁅m, l⁆ ∈ O :=
  Iff.rfl

theorem conj_mem_modCentralizer {M L O : Subgroup G}
    (hLM : M ≤ Subgroup.normalizer (L : Set G)) (hOM : M ≤ Subgroup.normalizer (O : Set G))
    {m₀ : G} (hm₀ : m₀ ∈ M) {m : G} (hm : m ∈ modCentralizer M L O) :
    m₀ * m * m₀⁻¹ ∈ modCentralizer M L O := by
  obtain ⟨hmM, -, hm⟩ := hm
  have hm₀N : m₀ ∈ Subgroup.normalizer (L : Set G) := hLM hm₀
  refine mem_modCentralizer_iff.mpr ⟨Subgroup.mul_mem _ (Subgroup.mul_mem _ hm₀ hmM)
    (Subgroup.inv_mem _ hm₀), Subgroup.mul_mem _ (Subgroup.mul_mem _ hm₀N ?_)
      (Subgroup.inv_mem _ hm₀N), ?_⟩
  · exact hLM hmM
  · intro l hl
    have hl' : m₀⁻¹ * l * m₀ ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hm₀N) l).mp hl
    have h1 : ⁅m, m₀⁻¹ * l * m₀⁆ ∈ O := hm _ hl'
    have h2 : m₀ * ⁅m, m₀⁻¹ * l * m₀⁆ * m₀⁻¹ ∈ O :=
      (Subgroup.mem_normalizer_iff.mp (hOM hm₀) _).mp h1
    rwa [show ⁅m₀ * m * m₀⁻¹, l⁆ = m₀ * ⁅m, m₀⁻¹ * l * m₀⁆ * m₀⁻¹ by
      simp only [commutatorElement_def]
      group]

theorem eq_one_of_mul_inv_mem_center {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (σ : MulAut H) (h : ∀ x : H, σ x * x⁻¹ ∈ Subgroup.center H) : σ = 1 := by
  classical
  let φ : H →* H :=
    { toFun := fun x => σ x * x⁻¹
      map_one' := by
        simp
      map_mul' := by
        intro x y
        have hc : ∀ w : H, w * (σ y * y⁻¹) = (σ y * y⁻¹) * w :=
          Subgroup.mem_center_iff.mp (h y)
        calc σ (x * y) * (x * y)⁻¹ = σ x * σ y * (y⁻¹ * x⁻¹) := by rw [map_mul]; group
          _ = σ x * ((σ y * y⁻¹) * x⁻¹) := by group
          _ = σ x * (x⁻¹ * (σ y * y⁻¹)) := by rw [hc]
          _ = σ x * x⁻¹ * (σ y * y⁻¹) := by group }
  have hle : φ.range ≤ Subgroup.center H := by
    rintro _ ⟨y, rfl⟩
    exact h y
  haveI : Group.IsPerfect ↥φ.range := Group.IsPerfect.range φ
  haveI : IsMulCommutative ↥φ.range := isMulCommutative_iff.mpr (by
    intro a b
    have ha : (a : H) ∈ Subgroup.center H := hle a.2
    exact Subtype.ext (Subgroup.mem_center_iff.mp ha (b : H)).symm)
  haveI : Subsingleton ↥φ.range := Group.IsPerfect.subsingleton_of_isMulCommutative
  have hbot : φ.range = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (⟨x, hx⟩ : ↥φ.range) = 1 := Subsingleton.elim _ _
    have h2 : x = 1 := congrArg Subtype.val h1
    simpa using h2
  ext x
  have h1 : φ x = 1 := by
    have hx : φ x ∈ φ.range := ⟨x, rfl⟩
    rw [hbot] at hx
    simpa using hx
  rw [MulAut.one_apply]
  exact mul_inv_eq_one.mp h1

theorem le_center_of_normal_isSolvable {H : Type*} [Group H] [Finite H] [Group.IsPerfect H]
    (hZ : IsSimpleGroup (H ⧸ Subgroup.center H)) {K : Subgroup H} [K.Normal]
    (hK : Group.IsSolvable ↥K) : K ≤ Subgroup.center H := by
  classical
  haveI : Nontrivial (H ⧸ Subgroup.center H) := hZ.toNontrivial
  haveI : Nontrivial H := (QuotientGroup.mk'_surjective (Subgroup.center H)).nontrivial
  by_contra hcon
  rw [SetLike.le_def] at hcon
  simp only [not_forall, not_imp] at hcon
  obtain ⟨x, hxK, hxZ⟩ := hcon
  set π : H →* (H ⧸ Subgroup.center H) := QuotientGroup.mk' _
  have hKimg : Subgroup.map π K = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.map π K) with h | h
    · exfalso
      have hxπ : π x ∈ Subgroup.map π K := Subgroup.mem_map_of_mem π hxK
      rw [h] at hxπ
      have h1 : π x = 1 := by simpa using hxπ
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact hxZ h1
    · exact h
  have hsup : K ⊔ Subgroup.center H = ⊤ := by
    have hc := congrArg (Subgroup.comap π) hKimg
    rw [Subgroup.comap_map_eq, QuotientGroup.ker_mk', Subgroup.comap_top] at hc
    exact hc
  set ρ : H →* (H ⧸ K) := QuotientGroup.mk' K
  have hZtop : Subgroup.map ρ (Subgroup.center H) = ⊤ := by
    have h := Subgroup.map_sup K (Subgroup.center H) ρ
    have hbot : Subgroup.map ρ K = ⊥ := by
      rw [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    rw [hsup, Subgroup.map_top_of_surjective ρ (QuotientGroup.mk'_surjective K), hbot] at h
    simpa using h.symm
  have hsurj : Function.Surjective ((ρ.comp (Subgroup.center H).subtype) :
      Subgroup.center H →* (H ⧸ K)) := by
    intro y
    have hy : y ∈ Subgroup.map ρ (Subgroup.center H) := hZtop ▸ Subgroup.mem_top y
    obtain ⟨z, hz, hzy⟩ := Subgroup.mem_map.mp hy
    exact ⟨⟨z, hz⟩, hzy⟩
  have hcommquot : ∀ u v : H ⧸ K, u * v = v * u := by
    intro u v
    obtain ⟨a, rfl⟩ := hsurj u
    obtain ⟨b, rfl⟩ := hsurj v
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext (Subgroup.mem_center_iff.mp a.2 b).symm)
  have hsolquot : Group.IsSolvable (H ⧸ K) := Group.isSolvable_of_comm hcommquot
  haveI : Group.IsSolvable ↥K := hK
  haveI := hsolquot
  have hsol : Group.IsSolvable H := Group.isSolvable_of_subgroup_quotient K
  exact Group.IsPerfect.not_isSolvable H hsol

end
end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.ONan

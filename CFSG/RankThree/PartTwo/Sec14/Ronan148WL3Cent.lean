module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148APGLConjLeaves
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentTransport
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3CentCases
import CFSG.RankThree.PartTwo.Sec14.Ronan148WL3TwoLocal
import CFSG.RankThree.PartTwo.Sec4.LThreePiProj
import CFSG.RankThree.PartTwo.Sec4.LThreePiProjInner
import CFSG.RankThree.PartTwo.Sec4.LThreePiMain
import CFSG.RankThree.PartTwo.Sec4.LThreePiTypes
import CFSG.RankThree.PartTwo.Sec4.LThreePiCaseA
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofD4
import CFSG.RankThree.PartTwo.Sec13.Item13Models
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.Foundations.QuasisimpleMulEquiv
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Foundations
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LieType.Chevalley.LangRootArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.LocalAnalysis.SectionRank.SQT
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructure
public import CFSG.RankThree.PartTwo.NotationBlocks
public import CFSG.RankThree.PartTwo.Sec8.Pairs
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.StronglyEmbedded.ParityCriterion
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148W

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Assembly.RankThreeEven (projImage)
open Matrix

local notation "pmk" => Matrix.ProjGenLinGroup.mk

@[expose] def KFact148L3CentL34 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D E : Subgroup X), Sec4.IsoLThreePi ↥D 2 2 →
    E ≤ Subgroup.normalizer (D : Set X) → IsMulCommutative ↥E → (∀ x ∈ E, x ^ 3 = 1) →
    Nat.card E = 27 → (∃ a ∈ E, a ≠ 1 ∧ a ∈ Subgroup.centralizer (D : Set X)) →
    ∀ e ∈ E ⊓ D, e ≠ 1 → E ⊓ D ≤ Subgroup.zpowers e →
    (∀ w ∈ Subgroup.centralizer (E : Set X), w ^ 3 = 1 → w ∈ E) →
    (∀ V : Subgroup X, V ≤ D → ¬ 3 ∣ Nat.card V → E ≤ Subgroup.normalizer (V : Set X) →
      ⁅V, E⁆ = ⊥) →
    False

@[expose] def KFact148L3CentU38 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (D E : Subgroup X), Sec4.IsoLThreePi ↥D 2 3 →
    E ≤ Subgroup.normalizer (D : Set X) → IsMulCommutative ↥E → (∀ x ∈ E, x ^ 3 = 1) →
    Nat.card E = 27 → (∃ a ∈ E, a ≠ 1 ∧ a ∈ Subgroup.centralizer (D : Set X)) →
    ∀ e ∈ E ⊓ D, e ≠ 1 → E ⊓ D ≤ Subgroup.zpowers e →
    (∀ w ∈ Subgroup.centralizer (E : Set X), w ^ 3 = 1 → w ∈ E) →
    (∀ V : Subgroup X, V ≤ D → ¬ 3 ∣ Nat.card V → E ≤ Subgroup.normalizer (V : Set X) →
      ⁅V, E⁆ = ⊥) →
    False

section Conj

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem conj_mem_projImage (hπ : π = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) {m : ProjGenLinGroup (Fin 3) K}
    (hm : m ∈ projImage (slPi π 3 (p ^ f) K)) :
    pmk g * m * (pmk g)⁻¹ ∈ projImage (slPi π 3 (p ^ f) K) := by
  obtain ⟨t, ht, rfl⟩ := hm
  exact ⟨g * t * g⁻¹, conj_mem_slPi hπ hg ht, by simp only [map_mul, map_inv]⟩

@[expose] noncomputable def conjModel (hπ : π = false → UnitaryFieldData p f K)
    {g : GL (Fin 3) K} (hg : g ∈ glPi π 3 (p ^ f) K) :
    projImage (slPi π 3 (p ^ f) K) ≃* projImage (slPi π 3 (p ^ f) K) where
  toFun m := ⟨pmk g⁻¹ * m * (pmk g⁻¹)⁻¹, conj_mem_projImage hπ (inv_mem hg) m.2⟩
  invFun m := ⟨pmk g * m * (pmk g)⁻¹, conj_mem_projImage hπ hg m.2⟩
  left_inv m := Subtype.ext (by simp only [map_inv]; group)
  right_inv m := Subtype.ext (by simp only [map_inv]; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem coe_conjModel (hπ : π = false → UnitaryFieldData p f K) {g : GL (Fin 3) K}
    (hg : g ∈ glPi π 3 (p ^ f) K) (m : projImage (slPi π 3 (p ^ f) K)) :
    (conjModel hπ hg m : ProjGenLinGroup (Fin 3) K) = pmk g⁻¹ * m * (pmk g⁻¹)⁻¹ :=
  rfl

end Conj

theorem kFact148L3Cent_of (h4 : KFact148L3CentL34) (h8 : KFact148L3CentU38) :
    Ronan148A.KFact148L3Cent := by
  intro X _ _ D E p f _ hf hD hED hEc hE3 hE27 ha e heED he1 heE hF3 hV
  have hp : p.Prime := Fact.out
  by_contra hcon
  have heE' : e ∈ E := (Subgroup.mem_inf.mp heED).1
  have heD : e ∈ D := (Subgroup.mem_inf.mp heED).2
  have hq2 : 2 < p ^ f := by
    by_contra h
    have hle := Nat.le_self_pow (by omega : f ≠ 0) p
    have h2 : p ^ f = 2 := by have := hp.two_le; omega
    have hp2 : p = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (h2 ▸ dvd_pow_self p (by omega))
    exact hcon ⟨hp2, by rw [h2], by rw [h2]; norm_num⟩
  have hpow : ∀ n m : ℕ, p ^ f = 2 ^ n → 1 ≤ n → m = n → p = 2 ∧ f = n := by
    intro n m h hn _
    have hp2 : p = 2 := by
      have : p ∣ 2 ^ n := h ▸ dvd_pow_self p (by omega)
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow this)
    subst hp2
    exact ⟨rfl, Nat.pow_right_injective le_rfl h⟩
  have h4' : p ^ f ≠ 4 := by
    intro h
    obtain ⟨rfl, rfl⟩ := hpow 2 2 (by rw [h]; norm_num) (by norm_num) rfl
    exact h4 X D E hD hED hEc hE3 hE27 ha e heED he1 heE hF3 hV
  have h8' : p ^ f ≠ 8 := by
    intro h
    obtain ⟨rfl, rfl⟩ := hpow 3 3 (by rw [h]; norm_num) (by norm_num) rfl
    exact h8 X D E hD hED hEc hE3 hE27 ha e heED he1 heE hF3 hV
  obtain ⟨π, K, _, _, hK, hq, ⟨φ⟩⟩ := exists_projImage_model hf hD
  have hexc : ¬ (p = 2 ∧ π = false ∧ ¬ 9 ∣ p ^ f + 1) := by
    rintro ⟨hp2, rfl, h9⟩
    exact hcon ⟨hp2, hq, h9⟩
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  have hperf := Sec13.isPerfect_projImage_slPi hK hq2
  haveI hsimp := Sec8.Item8KFacts2Proof.isSimpleGroup_projImage_slPi hK hq2
  have hMq : CFSG.IsQuasisimple (projImage (slPi π 3 (p ^ f) K)) :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
      (Sec8.Item8KFacts2Proof.exists_ne_comm_of_isPerfect hperf)).1
  have hθ := aschbacherSolvableCore_eq_bot_proj hK hq (CFSG.IsQuasisimple.of_mulEquiv φ hMq) φ
  have hφe1 : φ ⟨e, heD⟩ ≠ 1 := fun h => he1 (by
    have := congrArg Subtype.val (φ.injective (h.trans (map_one φ).symm))
    exact this)
  have hφe3 : φ ⟨e, heD⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have : (⟨e, heD⟩ : ↥D) ^ 3 = 1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hE3 e heE')
    rw [this, map_one]
  obtain ⟨s, hs, hse⟩ := (φ ⟨e, heD⟩).2
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hsH : s ∈ glPi π 3 (p ^ f) K := slPi_le_glPi hπ hs
  have hsZ : s ∉ zPi π 3 (p ^ f) K := fun h => hφe1 (Subtype.ext (by
    rw [← hse, mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h)]
    rfl))
  have hs3 : s ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    refine Subgroup.mem_inf.mpr ⟨pow_mem hsH 3, ?_⟩
    rw [← mk_eq_one_iff_mem_statedScalars, map_pow, hse]
    exact congrArg Subtype.val hφe3
  have hnf := (rank3II_4_10_two hK hq hτ hτ1 hsH hsZ hs3).mp ⟨s, hs, fun _ _ => rfl⟩
  obtain ⟨g, hg, hd⟩ : ∃ g ∈ glPi π 3 (p ^ f) K,
      (pmk (g⁻¹ * s * g) = pmk (diagTau hτ)) ∨
      (∃ ε : Kˣ, (ε : K) ^ 3 = 1 ∧ ε ≠ 1 ∧ pmk (g⁻¹ * s * g) = pmk (diagE ε) ∧
        ModNine π (p ^ f)) := by
    have hmk : ∀ (g z : GL (Fin 3) K), z ∈ zPi π 3 (p ^ f) K →
        pmk (g⁻¹ * (s * z) * g) = pmk (g⁻¹ * s * g) := by
      intro g z hz
      rw [map_mul, map_mul, map_mul, map_mul, map_mul,
        mk_eq_one_iff_mem_statedScalars.mpr (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz),
        mul_one]
    rcases hnf with ⟨y, ⟨z, hz, rfl⟩, g, hg, hgy⟩ | ⟨⟨y, ⟨z, hz, rfl⟩, g, hg, ε, hε, hgy⟩, h9⟩
    · exact ⟨g, hg, Or.inl (by rw [← hmk g z hz, hgy])⟩
    · have hε3 : (ε : K) ^ 3 = 1 := by
        rcases hε with h | h <;> rw [h]
        · exact hτ
        · rw [← pow_mul, pow_mul', hτ, one_pow]
      have hε1 : ε ≠ 1 := by
        rintro rfl
        rw [Units.val_one] at hε
        rcases hε with h | h
        · exact hτ1 h.symm
        · apply hτ1
          calc τ = τ ^ 3 / τ ^ 2 := by
                have hτ0 : τ ≠ 0 := by rintro rfl; simp at hτ
                field_simp
            _ = 1 := by rw [hτ, ← h, div_one]
      exact ⟨g, hg, Or.inr ⟨ε, hε3, hε1, by rw [← hmk g z hz, hgy], h9⟩⟩
  set φ' := φ.trans (conjModel hπ hg) with hφ'
  set e₀ := φ' ⟨e, heD⟩ with he₀
  have he₀c : (e₀ : ProjGenLinGroup (Fin 3) K) = pmk (g⁻¹ * s * g) := by
    rw [he₀, hφ', MulEquiv.trans_apply, coe_conjModel, ← hse]
    simp only [map_mul, map_inv, inv_inv]
  have he₀1 : e₀ ≠ 1 := fun h => hφe1 ((conjModel hπ hg).injective (h.trans (map_one _).symm))
  have he₀3 : e₀ ^ 3 = 1 := by
    rw [he₀, hφ', MulEquiv.trans_apply, ← map_pow, hφe3, map_one]
  set α : ↥E → MulAut (projImage (slPi π 3 (p ^ f) K)) :=
    fun x => slAct φ' ⟨(x : X), hED x.2⟩ with hα
  have hx3 : ∀ x : ↥E, (⟨(x : X), hED x.2⟩ : Subgroup.normalizer (D : Set X)) ^ 3 = 1 :=
    fun x => Subtype.ext (by rw [Subgroup.coe_pow]; exact hE3 x x.2)
  have hc : CentConfig π p f K α e₀ := by
    refine ⟨fun x => ?_, fun x => ?_, fun x y => ?_, ?_, ?_, ?_, fun x => ?_⟩
    · exact slAct_apply_self_of_commute φ' heD _
        (congrArg Subtype.val (hEc.is_comm.comm x ⟨e, heE'⟩))
    · rw [hα, ← map_pow, hx3, map_one]
    · rw [hα, ← map_mul, ← map_mul]
      congr 1
      exact Subtype.ext (show (x : X) * y = y * x from
        congrArg Subtype.val (hEc.is_comm.comm x y))
    · exact ⟨⟨e, heE'⟩, slAct_of_mem φ' heD _⟩
    · intro W hW3 hWinv x w hw
      exact slAct_eq_self_of_hV φ' hED hV W hW3 (fun y hy => hWinv ⟨y, hy⟩) x x.2 w hw
    · intro u hu3 hfix
      exact mem_zpowers_of_slAct_fixed φ' hED hF3 heD heE u hu3 fun y hy => hfix ⟨y, hy⟩
    · rcases pslAct_pgl_or_field hK hq2 hθ φ' ⟨(x : X), hED x.2⟩ (hx3 x) with h | ⟨-, h⟩
      · exact Or.inl h
      · exact Or.inr h
  refine hc.false_of_normalForm hK hq hq2 h4' h8' hexc he₀1 he₀3 ?_
  rcases hd with hd | ⟨ε, hε3, hε1, hd, h9⟩
  · exact Or.inl ⟨τ, hτ, hτ1, he₀c.trans hd⟩
  · exact Or.inr ⟨ε, hε3, hε1, he₀c.trans hd, h9⟩

end CFSG.RankThree.PartTwo.Sec14.Ronan148W

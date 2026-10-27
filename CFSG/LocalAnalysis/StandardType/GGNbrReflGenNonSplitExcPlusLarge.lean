module

public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusE7
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitExcPlusBump
public import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfSylow
public import CFSG.LocalAnalysis.StandardType.GGIrred937ExcLang
import CFSG.LocalAnalysis.StandardType.GGSixBstarExcFramesHalfToralDescent
import CFSG.LocalAnalysis.StandardType.GGExcToralSylow

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Assembly
open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartOne.KE CFSG.RankThree.E6
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.StandardType.ExcFrames CFSG.StandardType.ExcFramesHalf

open scoped Matrix

open TableBExc.E6Three (zetaVec zetaVec_apply)

theorem bigElemAbelianToralBar_E7_E8_of_eleven_le
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) :
    BigElemAbelianToralBar τ p := by
  refine bigElemAbelianToralBar_of_finite hp (by omega) le_rfl
    fun K₁ _ _ _ hqM A hA _ hpow _ => ?_
  have hA' : IsPGroup p (A.subgroupOf (adjointGroup τ K₁)) := fun x =>
    ⟨1, Subtype.ext (Subtype.ext (by
      simpa using hpow _ (Subgroup.mem_subgroupOf.mp x.2)))⟩
  obtain ⟨g, hg⟩ := ExcToralSylow.ggExcToral_of_splitCoprime
    (by rcases hτ with rfl | rfl <;> simp) hp (by simpa using hqM)
    (by rcases hτ with rfl | rfl <;> exact h11) hA'
  refine ⟨((g⁻¹ : adjointGroup τ K₁) : ModGL τ K₁), (g⁻¹).2, fun x hx => ?_⟩
  have := hg ⟨x, hA hx⟩ (Subgroup.mem_subgroupOf.mpr hx)
  simpa using this

theorem exists_langFrame_of_sc_large
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} [Fact p.Prime] (h11 : 11 ≤ p) (K : Type)
    [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup τ K))
    (hE : IsElemAbelian p E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E) :
    Irred937.LangFrameData τ p K E := by
  have hp : p.Prime := Fact.out
  have hT : SylowTorus (adjointGroup τ K) p τ.rank := by
    rcases hτ with rfl | rfl
    · exact sylowTorus_E7_half K hp h11 hpq
    · exact sylowTorus_E8_half K hp h11 hpq
  have hsc' : ∀ g : adjointGroup τ K, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E :=
    fun g hg hgp => hSC g (Subgroup.mem_centralizer_iff.mpr fun e he => (hg e he).symm) hgp
  have hcardE : Nat.card E = p ^ τ.rank := card_eq_of_selfCentralizing_of_sylowTorus hp hT hE hsc'
  exact Irred937.exists_langFrame_of_sc_of_toral hτ (by omega)
    (bigElemAbelianToralBar_E7_E8_of_eleven_le hτ hp h11) K hpq E hE
    (hcardE ▸ Nat.pow_le_pow_right hp.pos (Nat.sub_le _ _)) hSC

theorem exists_langFrame_of_sc_odd
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) (K : Type)
    [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K + 1) (E : Subgroup (adjointGroup τ K))
    (hE : IsElemAbelian p E) (hcard : p ^ (τ.rank - 1) ≤ Nat.card E)
    (hSC : ∀ x ∈ Subgroup.centralizer (E : Set (adjointGroup τ K)), x ^ p = 1 → x ∈ E) :
    Irred937.LangFrameData τ p K E := by
  by_cases h35 : p = 3 ∨ p = 5
  · exact Irred937.exists_langFrame_of_sc hτ h35 K hpq E hE hcard hSC
  · have : Fintype K := Fintype.ofFinite K
    obtain ⟨f, -, hf⟩ := FiniteField.card K 2
    have hK : Nat.card K = 2 ^ (f : ℕ) := by rw [Nat.card_eq_fintype_card, hf]
    have h11 : 11 ≤ p := ExcFramesHalf.eleven_le_of_dvd_two_pow_add_one Fact.out hp2 (hK ▸ hpq)
      (fun h3 => h35 (Or.inl h3)) (fun h5 => h35 (Or.inr h5))
    exact exists_langFrame_of_sc_large hτ h11 K hpq E hE hSC

theorem excPlusFrameModel_large
    {τ : Tag} (hτ : τ = .E7 ∨ τ = .E8) {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (K : Type)
    [Field K] [Finite K] [CharP K 2] (hpq : p ∣ Nat.card K + 1)
    (hrat : ∀ Fr : AlgebraicClosure K →+* AlgebraicClosure K, (∀ c, Fr c = c ^ Nat.card K) →
      ∀ X : Subgroup (ModGL τ (AlgebraicClosure K)), Finite X →
        X ≤ adjointGroup τ (AlgebraicClosure K) → (∀ x ∈ X, Units.map (entrywiseHom Fr) x = x) →
          X ≤ (adjointGroup τ K).map (baseChangeGL (algebraMap K (AlgebraicClosure K)))) :
    GGExcPlusFrameModel τ p K := by
  intro E hE _ hsc
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨w', Fr', g0, ζ, hζ, ι₀, hFr', hg0C, hg0', hcent, -, hι₀, hrange, hbase⟩ :=
    exists_langFrame_of_sc_large hτ h11 K hpq E hE hsc
  obtain ⟨m, hm⟩ := exists_simpleRealization_of_frame hFr' (hrat Fr' hFr') hg0C hg0' hcent hbase
  exact ⟨ι₀, m, hι₀, hrange, hm,
    fun g hg => exists_weyl_of_mem_normalizer_of_frame hg0C hι₀ hrange hbase hg⟩

theorem ggTorusReflGenW_E8Plus_large
    {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) :
    GGTorusReflGenW p (Tag.E8.rank - 1) (TableBExc.RecipeGroup .E8 K)
      (TableBExc.RecipeID .E8 K) := by
  have hp2 : p ≠ 2 := by omega
  refine ggTorusReflGenW_of_excPlusModel hp hp2
    (ggExcPlusWeylModelSCr_of_frameModel (Or.inr rfl) hp hp2 K
      (excPlusFrameModel_large (Or.inr rfl) hp h11 K hpq fun Fr hFr X hX hXC hXF => ?_))
  haveI := hX
  exact Subgroup.relIndex_eq_one.1 (Nat.dvd_one.1
    (CFSG.RankThree.PartOne.KE.finite_fixed_subgroup_rational_perfect (τ := .E8) (K := K)
      (L := AlgebraicClosure K) 1 (Or.inr (Or.inr ⟨rfl, rfl⟩)) Fr hFr X hXC hXF).1)

theorem ggTorusReflGenW_E7Plus_large
    {p : ℕ} (hp : p.Prime) (h11 : 11 ≤ p) (K : Type) [Field K] [Finite K] [CharP K 2]
    (hpq : p ∣ Nat.card K + 1) :
    GGTorusReflGenW p (Tag.E7.rank - 1) (TableBExc.RecipeGroup .E7 K)
      (TableBExc.RecipeID .E7 K) := by
  have hp2 : p ≠ 2 := by omega
  refine ggTorusReflGenW_of_excPlusModel hp hp2
    (ggExcPlusWeylModelSCr_of_frameModel (Or.inl rfl) hp hp2 K
      (excPlusFrameModel_large (Or.inl rfl) hp h11 K hpq fun Fr hFr X hX hXC hXF => ?_))
  haveI := hX
  exact finite_fixed_le_map_adjointGroup_E7 Fr hFr X hXC hXF

end CFSG.StandardType

end

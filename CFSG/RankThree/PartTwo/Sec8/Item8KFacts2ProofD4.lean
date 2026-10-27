module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofD4
import CFSG.RankThree.PartTwo.Sec13.Item136PGL
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.K71Item89
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.RankThree.PartTwo.Sec8.Item87Res2ProofUnitary
public import CFSG.RankThree.PartTwo.Sec21.LangTwistedProofD4SecIrred

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.Assembly.RankThreeEven (projImage projSL)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)

namespace Item8KFacts2Proof

section PGL

variable {K : Type} [Field K] {π : Bool} {p f : ℕ}

noncomputable def inSubgroupPerfectResidualEquiv {H M : Type*} [Group H] [Group M]
    {C : Subgroup H} (φ : C ≃* M) : inSubgroup perfectResidual C ≃* perfectResidual M :=
  ((perfectResidual C).equivMapOfInjective C.subtype C.subtype_injective).symm.trans
    (((perfectResidual C).equivMapOfInjective φ.toMonoidHom φ.injective).trans
      (MulEquiv.subgroupCongr (KFacts.perfectResidual_map_mulEquiv φ)))

theorem inSubgroup_perfectResidual_eq_bot_or_of_mulEquiv {H M : Type*} [Group H] [Group M]
    {C : Subgroup H} (φ : C ≃* M)
    (h : perfectResidual M = ⊥ ∨ IsQuasisimple (perfectResidual M)) :
    inSubgroup perfectResidual C = ⊥ ∨ IsQuasisimple (inSubgroup perfectResidual C) := by
  rcases h with h | h
  · left
    have e := inSubgroupPerfectResidualEquiv φ
    rw [eq_bot_iff]
    intro x hx
    have h1 : e ⟨x, hx⟩ = 1 :=
      Subtype.ext ((Subgroup.eq_bot_iff_forall _).mp h _ (e ⟨x, hx⟩).2)
    have h2 : (⟨x, hx⟩ : inSubgroup perfectResidual C) = 1 := by
      rw [← map_one e] at h1
      exact e.injective h1
    rw [Subgroup.mem_bot]
    exact congrArg Subtype.val h2
  · right
    exact LocalCores.isQuasisimple_of_mulEquiv (inSubgroupPerfectResidualEquiv φ).symm h

theorem exists_ne_comm_of_isPerfect {X : Type*} [Group X] [Nontrivial X] (hp : Group.IsPerfect X) :
    ∃ a b : X, a * b ≠ b * a := by
  by_contra hab
  push Not at hab
  have hc : commutator X = ⊥ := by
    rw [commutator_def, Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro x _
    rw [Subgroup.mem_centralizer_iff]
    intro y _
    exact hab y x
  rw [hp.commutator_eq_top] at hc
  exact top_ne_bot hc

theorem perfectResidual_projImage_glPi_eq (hK : Sec4.PiField π p f K) (hq2 : 2 < p ^ f) :
    perfectResidual (projImage (Sec4.glPi π 3 (p ^ f) K)) =
      (projImage (Sec4.slPi π 3 (p ^ f) K)).subgroupOf (projImage (Sec4.glPi π 3 (p ^ f) K)) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hSP : projImage (Sec4.slPi π 3 (p ^ f) K) ≤ projImage (Sec4.glPi π 3 (p ^ f) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
  have hperfS : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
    Sec13.isPerfect_projImage_slPi hK hq2
  have hperfS' : Group.IsPerfect
      ((projImage (Sec4.slPi π 3 (p ^ f) K)).subgroupOf (projImage (Sec4.glPi π 3 (p ^ f) K))) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hSP).symm.toMonoidHom)
      (MulEquiv.surjective _)
  refine le_antisymm ?_ (Item87Res2Proof.le_perfectResidual_of_isPerfect hperfS')
  rw [← Sec13.commutator_projImage_glPi hK hq2, ← derivedSeries_one]
  exact iInf_le _ 1

theorem isSimpleGroup_projImage_slPi (hK : Sec4.PiField π p f K) (hq2 : 2 < p ^ f) :
    IsSimpleGroup (projImage (Sec4.slPi π 3 (p ^ f) K)) := by
  have hp := hK.prime
  cases π
  · have := hK.finite
    have : Fact p.Prime := ⟨hp⟩
    have hcard : Nat.card K = (p ^ f) ^ 2 := hK.card
    have hs : IsSimpleGroup (CFSG.Assembly.LowTwoRank.StatedProj
        (CFSG.Assembly.LowTwoRank.StatedSU 3 (p ^ f) K)) :=
      CFSG.ClassicalGroups.Unitary.isSimpleGroup_statedProj_statedSU K p f hcard 3 le_rfl
        (fun h => by
          have := (Prod.mk.inj h).2
          omega)
    have hs' : IsSimpleGroup
        (CFSG.Assembly.LowTwoRank.StatedProj (Sec4.slPi false 3 (p ^ f) K)) := hs
    exact (CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk
      (Sec4.slPi false 3 (p ^ f) K)).symm.isSimpleGroup
  · rw [← Sec4.projSL_eq_projImage]
    exact Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field K

theorem perfectResidual_projImage_glPi_eq_bot_or_isQuasisimple (hK : Sec4.PiField π p f K)
    (hπ2 : π = true → 2 < p ^ f) :
    perfectResidual (projImage (Sec4.glPi π 3 (p ^ f) K)) = ⊥ ∨
      IsQuasisimple (perfectResidual (projImage (Sec4.glPi π 3 (p ^ f) K))) := by
  have := hK.finite
  have : Finite (Matrix.ProjGenLinGroup (Fin 3) K) :=
    Finite.of_surjective (Matrix.ProjGenLinGroup.mk : GL (Fin 3) K →* _)
      (QuotientGroup.mk'_surjective _)
  have hp := hK.prime
  have hf := hK.one_le
  have hq2' : 2 ≤ p ^ f := le_trans hp.two_le (Nat.le_self_pow (by omega) _)
  by_cases hq2 : 2 < p ^ f
  · have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
    have hSP : projImage (Sec4.slPi π 3 (p ^ f) K) ≤ projImage (Sec4.glPi π 3 (p ^ f) K) :=
      Subgroup.map_mono (Sec4.slPi_le_glPi hπ)
    have hperfS : Group.IsPerfect (projImage (Sec4.slPi π 3 (p ^ f) K)) :=
      Sec13.isPerfect_projImage_slPi hK hq2
    have hs := isSimpleGroup_projImage_slPi hK hq2
    right
    rw [perfectResidual_projImage_glPi_eq hK hq2]
    have : Nontrivial (projImage (Sec4.slPi π 3 (p ^ f) K)) := hs.toNontrivial
    have hq := (LocalCores.isQuasisimple_of_isSimpleGroup (exists_ne_comm_of_isPerfect hperfS)).1
    exact LocalCores.isQuasisimple_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hSP).symm hq
  · have h2 : p ^ f = 2 := by omega
    cases π
    · left
      have hsolv := Sec13.isSolvable_projImage_glPi_two hK h2
      exact (perfect_residual_characterization.2.2.2.2.2).mpr hsolv
    · exact absurd (hπ2 rfl) hq2

theorem not_nonempty_perfectResidual_pglThree_mulEquiv_A6
    {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) :
    ¬ Nonempty (perfectResidual (projImage (Sec4.glPi true 3 (2 ^ n) K)) ≃*
      alternatingGroup (Fin 6)) := by
  rintro ⟨ι⟩
  have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hPi : Sec4.PiField true 2 n K := ⟨Nat.prime_two, by omega, hK⟩
  have hq : 4 ≤ 2 ^ n := (Nat.pow_le_pow_right (by norm_num) hn : 2 ^ 2 ≤ 2 ^ n)
  have hP := perfectResidual_projImage_glPi_eq hPi (by omega)
  have hSP : projImage (Sec4.slPi true 3 (2 ^ n) K) ≤ projImage (Sec4.glPi true 3 (2 ^ n) K) :=
    Subgroup.map_mono (Sec4.slPi_le_glPi (π := true) (fun h => absurd h (by decide)))
  have hPS : Nat.card (projImage (Sec4.slPi true 3 (2 ^ n) K)) = 360 := by
    rw [← KFacts.card_alternatingGroup_six, ← Nat.card_congr ι.toEquiv, hP]
    exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hSP).toEquiv).symm
  have hc := KFacts.KS14.card_projSL_three_mul_gcd K
  rw [Sec4.projSL_eq_projImage (2 ^ n) K, hPS, hK] at hc
  have hg : Nat.gcd 3 (2 ^ n - 1) ≤ 3 := Nat.le_of_dvd (by norm_num) (Nat.gcd_dvd_left _ _)
  have h1 : 64 ≤ (2 ^ n) ^ 3 := (Nat.pow_le_pow_left hq 3 : 4 ^ 3 ≤ (2 ^ n) ^ 3)
  have h2' : 16 ≤ (2 ^ n) ^ 2 := (Nat.pow_le_pow_left hq 2 : 4 ^ 2 ≤ (2 ^ n) ^ 2)
  have h2 : 15 ≤ (2 ^ n) ^ 2 - 1 := by omega
  have h3 : 63 ≤ (2 ^ n) ^ 3 - 1 := by omega
  have h4 : 64 * (15 * 63) ≤ (2 ^ n) ^ 3 * (((2 ^ n) ^ 2 - 1) * ((2 ^ n) ^ 3 - 1)) :=
    Nat.mul_le_mul h1 (Nat.mul_le_mul h2 h3)
  have h5 : 360 * Nat.gcd 3 (2 ^ n - 1) ≤ 360 * 3 := Nat.mul_le_mul_left _ hg
  omega

end PGL

end Item8KFacts2Proof

@[expose] def KF82D4SecondCentY0Even : Prop :=
  ∀ n : ℕ, Even n → 1 ≤ n → ∀ (K : Type) [Field K] [Finite K] (σ : K ≃+* K),
    Nat.card K = (2 ^ n) ^ 3 → (∀ c, σ c = c ^ 2 ^ n) →
      ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 2 ^ n ∧
        Nonempty (Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ) ≃*
          projImage (Sec4.glPi true 3 (2 ^ n) F))

namespace Item8KFacts2Proof

variable {f : ℕ} {K : Type} [Field K] [Finite K] {σ : K ≃+* K}

theorem autFix_inv {X : Type*} [Group X] (α : MulAut X) : Sec4.autFix α⁻¹ = Sec4.autFix α := by
  ext x
  rw [Sec4.mem_autFix, Sec4.mem_autFix]
  constructor
  · intro h
    have := congrArg α h
    rw [MulAut.inv_apply, MulEquiv.apply_symm_apply] at this
    exact this.symm
  · intro h
    rw [MulAut.inv_apply, MulEquiv.symm_apply_eq]
    exact h.symm

theorem conj_or_nonempty_autFix_equiv_of_coset
    (hK : Nat.card K = (2 ^ f) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ f)
    (g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
    (hg3 : (MulAut.conj g * fieldActor σ σ) ^ 3 = 1) :
    (∃ β : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom),
        MulAut.conj g * fieldActor σ σ = β * fieldActor σ σ * β⁻¹) ∨
      Nonempty (Sec4.autFix (MulAut.conj g * fieldActor σ σ) ≃*
        Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ)) := by
  obtain ⟨h, y, hy, hyy⟩ := exists_conj_eq_of_geom d4TrialityGeomClasses_holds
    d4DiagramCentIrred_holds d4SecondCentIrred_holds hK hσ g hg3
  rcases hy with hy1 | hy0
  · left
    have hy'1 : y = 1 := Subtype.ext hy1
    refine ⟨MulAut.conj h⁻¹, ?_⟩
    rw [hyy, hy'1, map_one, one_mul]
  · right
    have hy'0 : y = d4TrialityY0Elt K σ := Subtype.ext hy0
    rw [hyy, hy'0, ← LangTwistedProof.mulAut_congr_eq]
    exact ⟨Sec4.autFixCongrEquiv _ _⟩

theorem isStdGraphFieldConj_or_nonempty_autFix_equiv
    (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 3)
    (hσ : ∀ c, σ c = c ^ 2 ^ f) {α : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom)}
    (hα3 : α ^ 3 = 1) (hαout : ¬ KFacts.IsInnerAut α) :
    Sec4.IsStdGraphFieldConj σ α ∨
      Nonempty (Sec4.autFix α ≃*
        Sec4.autFix (MulAut.conj (d4TrialityY0Elt K σ) * fieldActor σ σ)) := by
  obtain ⟨g, hg | hg⟩ := Item8ModelProof.exists_conj_mul_sigma hf hK hσ hα3 hαout
  · subst hg
    rcases conj_or_nonempty_autFix_equiv_of_coset hK hσ g hα3 with ⟨β, hβ⟩ | h
    · exact Or.inl ⟨β, Or.inl hβ⟩
    · exact Or.inr h
  · set σ₀ := fieldActor (t := TwistTag.D4) σ σ with hσ₀
    have hinv : α⁻¹ = MulAut.conj (σ₀ g⁻¹) * σ₀ := by
      rw [hg, mul_inv_rev, inv_inv, ← map_inv MulAut.conj g, ← KFacts.mul_mulAutConj_mul_inv,
        inv_mul_cancel_right]
    have hinv3 : (MulAut.conj (σ₀ g⁻¹) * σ₀) ^ 3 = 1 := by
      rw [← hinv, inv_pow, hα3, inv_one]
    rcases conj_or_nonempty_autFix_equiv_of_coset hK hσ (σ₀ g⁻¹) hinv3 with ⟨β, hβ⟩ | he
    · refine Or.inl ⟨β, Or.inr ?_⟩
      have h1 : α⁻¹ = β * σ₀ * β⁻¹ := hinv.trans hβ
      calc α = (α⁻¹)⁻¹ := (inv_inv α).symm
        _ = β * σ₀⁻¹ * β⁻¹ := by rw [h1]; group
    · obtain ⟨e⟩ := he
      refine Or.inr ⟨?_⟩
      rw [← autFix_inv α, hinv]
      exact e

end Item8KFacts2Proof

theorem kF89D4OtherClass_of
    (hE : KF82D4SecondCentY0Even) : KF89D4OtherClass := by
  intro f hf hfe K _ _ hK σ hσ τ hτ3 hτin hτconj
  rcases Item8KFacts2Proof.isStdGraphFieldConj_or_nonempty_autFix_equiv hf hK hσ hτ3 hτin with
    ⟨β, hβ | hβ⟩ | he₁
  · exact absurd hβ (hτconj β).1
  · exact absurd hβ (hτconj β).2
  · obtain ⟨e₁⟩ := he₁
    obtain ⟨F, _, _, hF, ⟨e₂⟩⟩ := hE f hfe hf K σ hK hσ
    rintro ⟨ψ⟩
    have hfix : τ.toMonoidHom.eqLocus (MonoidHom.id _) = Sec4.autFix τ := by
      ext x
      rfl
    set φ := (MulEquiv.subgroupCongr hfix).trans (e₁.trans e₂) with hφ
    have hf2 : 2 ≤ f := by
      obtain ⟨k, rfl⟩ := hfe
      omega
    apply Item8KFacts2Proof.not_nonempty_perfectResidual_pglThree_mulEquiv_A6
      hf2 hF
    exact ⟨((MulEquiv.subgroupCongr (KFacts.perfectResidual_map_mulEquiv φ)).symm.trans
      ((perfectResidual _).equivMapOfInjective φ.toMonoidHom φ.injective).symm).trans ψ⟩

end CFSG.RankThree.PartTwo.Sec8

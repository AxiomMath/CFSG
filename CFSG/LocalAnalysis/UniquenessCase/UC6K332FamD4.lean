module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432Defs
import CFSG.RankThree.PartTwo.Sec4.RonanK432RowD4Outer
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddEllMain
import CFSG.HardMathSupport.Lang.E6Descent.OuterFixedTrialityOddRot
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusionTrialityConj
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosureLieExcTwWit
import CFSG.HardMathSupport.Timmesfeld.LangTorus.TorusAtDatum
public import CFSG.LieType.Chevalley.WeylRoots
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCoreLinear

public section

set_option linter.unusedSectionVars false

namespace CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

open CFSG.Blueprint (LieModel)
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE
  CFSG.RankThree.PartOne.KGD CFSG.RankThree.Lattice CFSG.HardMathSupport.Timmesfeld.LangTorus
open CFSG.RankThree.PartTwo.Sec4.RonanK432 (ListRow OuterRow WeaklyClosed)
open CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof (Exp3 tup wordExp gA gB d4S0 d4S0_mem d4T0
  d4T0_mem rootDiagUnit_tup_eq_conj exists_conj_d4S0 exists_conj_d4T0 isPointIrreducible_gA
  isPointIrreducible_gB)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.Stroth.WeakClosure.ExcCross
  (tw_mem_fixedCharTuples_of_vec tw_rootDiagUnit_mem_torus)
open CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.T29.Parrott.InnerFusion
  (exists_conj_eq_d4S0_or_d4T0)
open scoped Matrix

private theorem not_weaklyClosed_of_conj_commute {G : Type} [Group G] {z : G}
    (h : ∃ g : G, Commute (g * z * g⁻¹) z ∧ g * z * g⁻¹ ∉ Subgroup.zpowers z) :
    ¬ WeaklyClosed (Subgroup.zpowers z) := by
  obtain ⟨g, hc, hn⟩ := h
  intro hw
  have hmap : (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom =
      Subgroup.zpowers (g * z * g⁻¹) := by
    rw [MonoidHom.map_zpowers]
    rfl
  have hle : (Subgroup.zpowers z).map (MulAut.conj g).toMonoidHom ≤
      Subgroup.normalizer (Subgroup.zpowers z : Set G) := by
    rw [hmap, Subgroup.zpowers_le]
    apply Subgroup.centralizer_le_normalizer
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    exact (hc.symm.zpow_left k).eq
  have h1 := hw g hle
  rw [hmap] at h1
  apply hn
  rw [← h1]
  exact Subgroup.mem_zpowers _

private theorem conj_commute_of_conj {G : Type} [Group G] {z s : G} (a : G)
    (has : a * z * a⁻¹ = s)
    (h : ∃ g : G, Commute (g * s * g⁻¹) s ∧ g * s * g⁻¹ ∉ Subgroup.zpowers s) :
    ∃ g : G, Commute (g * z * g⁻¹) z ∧ g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  obtain ⟨g, hc, hn⟩ := h
  refine ⟨a⁻¹ * g * a, ?_, ?_⟩
  · have e1 : a * (a⁻¹ * g * a * z * (a⁻¹ * g * a)⁻¹) * a⁻¹ = g * s * g⁻¹ := by
      rw [← has]
      group
    rw [← Commute.conj_iff a, e1, has]
    exact hc
  · intro hm
    apply hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← has, conj_zpow, hk]
    group

private theorem conj_commute_of_mulEquiv {G H : Type} [Group G] [Group H] (e : G ≃* H) {z : G}
    (h : ∃ g : H, Commute (g * e z * g⁻¹) (e z) ∧ g * e z * g⁻¹ ∉ Subgroup.zpowers (e z)) :
    ∃ g : G, Commute (g * z * g⁻¹) z ∧ g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  obtain ⟨g, hc, hn⟩ := h
  refine ⟨e.symm g, ?_, ?_⟩
  · simpa only [map_mul, map_inv, MulEquiv.symm_apply_apply] using hc.map e.symm
  · intro hm
    apply hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    simpa only [map_zpow, map_mul, map_inv, MulEquiv.apply_symm_apply] using congrArg e hk

private theorem conj_commute_of_pair {G : Type} [Group G] {s z₁ z₂ a₁ a₂ : G}
    (hc : Commute z₁ z₂) (hn : z₂ ∉ Subgroup.zpowers z₁) (h₁ : a₁ * z₁ * a₁⁻¹ = s)
    (h₂ : a₂ * z₂ * a₂⁻¹ = s) :
    ∃ g : G, Commute (g * s * g⁻¹) s ∧ g * s * g⁻¹ ∉ Subgroup.zpowers s := by
  have e : a₁ * a₂⁻¹ * s * (a₁ * a₂⁻¹)⁻¹ = a₁ * z₂ * a₁⁻¹ := by
    rw [← h₂]
    group
  refine ⟨a₁ * a₂⁻¹, ?_, ?_⟩
  · rw [e, ← h₁]
    exact hc.symm.conj a₁
  · rw [e]
    intro hm
    apply hn
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    refine Subgroup.mem_zpowers_iff.2 ⟨k, ?_⟩
    rw [← h₁, conj_zpow] at hk
    exact mul_left_cancel (mul_right_cancel hk)

private theorem three_dvd_of_check {n : ℕ} {M : Matrix (Fin n) (Fin n) ℤ} {b : Fin n → ℤ}
    {q : ℕ} {ε : ℤ} (hq : (3 : ℤ) ∣ (q : ℤ) - ε)
    (h : ∀ j, (3 : ℤ) ∣ (M.transpose *ᵥ b) j - ε * b j) (j : Fin n) :
    ((3 : ℕ) : ℤ) ∣ (M.transpose *ᵥ b) j - (q : ℤ) * b j := by
  have e : (M.transpose *ᵥ b) j - (q : ℤ) * b j =
      ((M.transpose *ᵥ b) j - ε * b j) - ((q : ℤ) - ε) * b j := by
    ring
  rw [e]
  exact_mod_cast dvd_sub (h j) (Dvd.dvd.mul_right hq (b j))

private theorem three_dvd_sub_d4Row {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) :
    (3 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) - 1 ∨ (3 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) - (-1) := by
  have h3 : ¬ 3 ∣ ℓ ^ f := fun h =>
    hℓ3 ((Nat.prime_dvd_prime_iff_eq Nat.prime_three hℓ).1
      (Nat.prime_three.dvd_of_dvd_pow h)).symm
  generalize ℓ ^ f = q at h3 ⊢
  omega

private theorem exists_orderOf_three_d4Row {L : Type} [Field L] [IsAlgClosed L] {ℓ : ℕ}
    [CharP L ℓ] (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) : ∃ ζ : Lˣ, orderOf ζ = 3 := by
  haveI : NeZero ((3 : ℕ) : L) := ⟨by
    intro h
    have := (CharP.cast_eq_zero_iff L ℓ 3).1 h
    exact hℓ3 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 this)⟩
  obtain ⟨ζ0, hζ0⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot L 3
  exact ⟨(hζ0.isUnit (by norm_num)).unit, (hζ0.isUnit_unit (by norm_num)).eq_orderOf.symm⟩

private def d4RowPList : List (List ℤ) := [[0, 0, 0, 1], [1, 0, 0, 0], [0, 0, 1, 0], [0, 1, 0, 0]]

private theorem toMat_d4RowPList : toMat 4 d4RowPList =
    Matrix.of (fun i j => if j = TwistTag.D4.perm.symm i then (1 : ℤ) else 0) := by
  ext i j
  fin_cases i <;> fin_cases j <;> decide

private theorem permLattice_d4Row (x : Fin TwistTag.D4.tag.rank → ℤ) :
    permLattice TwistTag.D4.perm x = toMat 4 d4RowPList *ᵥ x := by
  rw [toMat_d4RowPList]
  funext i
  change x (TwistTag.D4.perm.symm i) =
    ∑ j : Fin TwistTag.D4.tag.rank, (if j = TwistTag.D4.perm.symm i then (1 : ℤ) else 0) * x j
  simp only [ite_mul, one_mul, zero_mul]
  rw [Finset.sum_ite_eq']
  simp

section ListRowProof


private theorem wordProd_smul_permLattice_d4Row {lw : List (Fin TwistTag.D4.tag.rank)}
    {Wl : List (List ℤ)} (hW : lword Tag.D4.rank (cartanList Tag.D4) (lw.map Fin.val) = Wl)
    (x : Fin TwistTag.D4.tag.rank → ℤ) :
    (coxeterSystem TwistTag.D4.tag).wordProd lw • permLattice TwistTag.D4.perm x =
      (toMat 4 Wl * toMat 4 d4RowPList) *ᵥ x := by
  rw [permLattice_d4Row]
  have h1 := wordProd_smul_eq_wordMat_mulVec Tag.D4 lw (toMat 4 d4RowPList *ᵥ x)
  rw [wordMat_eq_toMat Tag.D4 lw hW] at h1
  exact h1.trans (Matrix.mulVec_mulVec x (toMat 4 Wl) (toMat 4 d4RowPList))

variable {K : Type} [Field K] [Finite K]

private theorem exists_commute_pair_d4Row {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {L : Type} [Field L] [Algebra K L] [IsAlgClosure K L] [CharP L ℓ]
    {ζ : Lˣ} (hζ : orderOf ζ = 3) {ε : ℤ} (hq : (3 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) - ε)
    (lw : List (Fin TwistTag.D4.tag.rank)) (Wl : List (List ℤ))
    (hW : lword Tag.D4.rank (cartanList Tag.D4) (lw.map Fin.val) = Wl)
    (β₁ β₂ γ : Exp3) (ω₁ ω₂ : List (Fin TwistTag.D4.tag.rank))
    (hβ₁ : ∀ j, (3 : ℤ) ∣ ((toMat 4 Wl * toMat 4 d4RowPList).transpose *ᵥ
      fun i => ((β₁ i).val : ℤ)) j - ε * ((β₁ j).val : ℤ))
    (hβ₂ : ∀ j, (3 : ℤ) ∣ ((toMat 4 Wl * toMat 4 d4RowPList).transpose *ᵥ
      fun i => ((β₂ i).val : ℤ)) j - ε * ((β₂ j).val : ℤ))
    (hω₁ : wordExp ω₁ β₁ = γ) (hω₂ : wordExp ω₂ β₂ = γ)
    (j₀ : Fin TwistTag.D4.tag.rank) (hj₁ : (β₁ j₀).val = 0) (hj₂ : (β₂ j₀).val = 1) :
    ∃ z₁ z₂ : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      Commute z₁ z₂ ∧ z₂ ∉ Subgroup.zpowers z₁ ∧
      (∃ x ∈ adjointGroup TwistTag.D4.tag L,
        triEmb K σ L z₁ = x * rootDiagUnit TwistTag.D4.tag (tup ζ γ) * x⁻¹) ∧
      (∃ x ∈ adjointGroup TwistTag.D4.tag L,
        triEmb K σ L z₂ = x * rootDiagUnit TwistTag.D4.tag (tup ζ γ) * x⁻¹) := by
  have hζ3 : ζ ^ 3 = 1 := by
    rw [← hζ]
    exact pow_orderOf_eq_one ζ
  haveI : IsAlgClosed L := IsAlgClosure.isAlgClosed K
  have hFr : ∀ c, iterateFrobenius L ℓ f c = c ^ (ℓ ^ f) := fun c => iterateFrobenius_def ℓ f c
  obtain ⟨g0, hg0C, hg0⟩ := lang_conjugator_D4 (K := K) (ℓ := ℓ) hf L
    (canonicalRep (coxeterSystem TwistTag.D4.tag) L ((coxeterSystem TwistTag.D4.tag).wordProd lw))
    (canonicalRep_mem_adjointGroup (coxeterSystem TwistTag.D4.tag) L _)
  let D : LangDatum TwistTag.D4.tag L := LangDatum.ofTwist TwistTag.D4 (iterateFrobenius L ℓ f)
    (ℓ ^ f) hFr ((coxeterSystem TwistTag.D4.tag).wordProd lw) hg0C hg0
  have hD : D.Φ = twistHom TwistTag.D4 L (iterateFrobenius L ℓ f) := rfl
  have hn : D.n = canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd lw) := rfl
  have hfixD : D.fix = (triEmb K σ L).range := by
    rw [triEmb_range hℓ hf hK hσ (iterateFrobenius L ℓ f) hFr]
    ext x
    rw [LangDatum.mem_fix, hD]
    rfl
  have hrat : ∀ d ∈ D.torus, ∃ z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      triEmb K σ L z = g0 * d * g0⁻¹ := by
    intro d hd
    have h1 : (MulAut.conj D.g0).toMonoidHom d ∈ D.fix := by
      rw [← D.map_conj_model]
      exact Subgroup.mem_map_of_mem _ (D.torus_le_model hd)
    rw [hfixD] at h1
    obtain ⟨z, hz⟩ := MonoidHom.mem_range.1 h1
    exact ⟨z, hz⟩
  have hmem : ∀ β : Exp3, (∀ j, (3 : ℤ) ∣ ((toMat 4 Wl * toMat 4 d4RowPList).transpose *ᵥ
      fun i => ((β i).val : ℤ)) j - ε * ((β j).val : ℤ)) →
      rootDiagUnit TwistTag.D4.tag (tup ζ β) ∈ D.torus := by
    intro β hβ
    have e : tup ζ β = fun i => ζ ^ ((β i).val : ℤ) := by
      funext i
      rw [zpow_natCast]
      rfl
    rw [e]
    exact tw_rootDiagUnit_mem_torus (t := TwistTag.D4) D hD hn
      (wordProd_smul_permLattice_d4Row hW)
      (tw_mem_fixedCharTuples_of_vec (p := 3) hζ3 hFr (three_dvd_of_check hq hβ))
  obtain ⟨z₁, hz₁⟩ := hrat _ (hmem β₁ hβ₁)
  obtain ⟨z₂, hz₂⟩ := hrat _ (hmem β₂ hβ₂)
  have hconj : ∀ (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom) (β : Exp3)
      (ω : List (Fin TwistTag.D4.tag.rank)), wordExp ω β = γ →
      triEmb K σ L z = g0 * rootDiagUnit TwistTag.D4.tag (tup ζ β) * g0⁻¹ →
      ∃ x ∈ adjointGroup TwistTag.D4.tag L,
        triEmb K σ L z = x * rootDiagUnit TwistTag.D4.tag (tup ζ γ) * x⁻¹ := by
    intro z β ω hω hz
    refine ⟨g0 * (canonicalRep (coxeterSystem TwistTag.D4.tag) L
      ((coxeterSystem TwistTag.D4.tag).wordProd ω))⁻¹,
      mul_mem hg0C (inv_mem (canonicalRep_mem_adjointGroup _ L _)), ?_⟩
    rw [hz, rootDiagUnit_tup_eq_conj hζ3 ω β, hω]
    group
  refine ⟨z₁, z₂, ?_, ?_, hconj z₁ β₁ ω₁ hω₁ hz₁, hconj z₂ β₂ ω₂ hω₂ hz₂⟩
  · show z₁ * z₂ = z₂ * z₁
    apply triEmb_injective (K := K) (σ := σ) (L := L)
    rw [map_mul, map_mul, hz₁, hz₂]
    have hc : Commute (rootDiagUnit TwistTag.D4.tag (tup ζ β₁))
        (rootDiagUnit TwistTag.D4.tag (tup ζ β₂)) := by
      show _ * _ = _ * _
      rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm (tup ζ β₁)]
    exact (hc.conj g0).eq
  · intro hm
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 hm
    have h1 := congrArg (triEmb K σ L) hk
    rw [map_zpow, hz₁, hz₂, conj_zpow] at h1
    have h2 := mul_left_cancel (mul_right_cancel h1)
    have h3 : tup ζ β₁ ^ k = tup ζ β₂ := by
      apply rootDiagUnit_injective (K := L) (τ := TwistTag.D4.tag)
      rw [← h2]
      exact map_zpow (rootDiagUnitHom TwistTag.D4.tag L) (tup ζ β₁) k
    have h4 : (ζ ^ (β₁ j₀).val) ^ k = ζ ^ (β₂ j₀).val := congrFun h3 j₀
    rw [hj₁, hj₂, pow_zero, one_zpow, pow_one] at h4
    rw [← h4, orderOf_one] at hζ
    exact absurd hζ (by norm_num)

private theorem conj_commute_of_d4Row_torus {ℓ f : ℕ} [Fact ℓ.Prime] (hℓ : ℓ.Prime) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    [CharP (AlgebraicClosure K) ℓ] {ζ : (AlgebraicClosure K)ˣ} (hζ : orderOf ζ = 3) {γ : Exp3}
    {s : graphFixedRootGroup TwistTag.D4 K σ.toRingHom}
    (hdesc : ∀ (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (x : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      x ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) →
      triEmb K σ (AlgebraicClosure K) z = x * rootDiagUnit TwistTag.D4.tag (tup ζ γ) * x⁻¹ →
      ∃ a, a * z * a⁻¹ = s)
    {ε : ℤ} (hq : (3 : ℤ) ∣ ((ℓ ^ f : ℕ) : ℤ) - ε)
    (lw : List (Fin TwistTag.D4.tag.rank)) (Wl : List (List ℤ))
    (hW : lword Tag.D4.rank (cartanList Tag.D4) (lw.map Fin.val) = Wl)
    (β₁ β₂ : Exp3) (ω₁ ω₂ : List (Fin TwistTag.D4.tag.rank))
    (hβ₁ : ∀ j, (3 : ℤ) ∣ ((toMat 4 Wl * toMat 4 d4RowPList).transpose *ᵥ
      fun i => ((β₁ i).val : ℤ)) j - ε * ((β₁ j).val : ℤ))
    (hβ₂ : ∀ j, (3 : ℤ) ∣ ((toMat 4 Wl * toMat 4 d4RowPList).transpose *ᵥ
      fun i => ((β₂ i).val : ℤ)) j - ε * ((β₂ j).val : ℤ))
    (hω₁ : wordExp ω₁ β₁ = γ) (hω₂ : wordExp ω₂ β₂ = γ)
    (j₀ : Fin TwistTag.D4.tag.rank) (hj₁ : (β₁ j₀).val = 0) (hj₂ : (β₂ j₀).val = 1) :
    ∃ g, Commute (g * s * g⁻¹) s ∧ g * s * g⁻¹ ∉ Subgroup.zpowers s := by
  obtain ⟨z₁, z₂, hc, hn, ⟨x₁, hx₁, h₁⟩, ⟨x₂, hx₂, h₂⟩⟩ :=
    exists_commute_pair_d4Row (L := AlgebraicClosure K) hℓ hf hK hσ hζ hq lw Wl hW β₁ β₂ γ ω₁ ω₂
      hβ₁ hβ₂ hω₁ hω₂ j₀ hj₁ hj₂
  obtain ⟨a₁, ha₁⟩ := hdesc z₁ x₁ hx₁ h₁
  obtain ⟨a₂, ha₂⟩ := hdesc z₂ x₂ hx₂ h₂
  exact conj_commute_of_pair hc hn ha₁ ha₂

private theorem conj_commute_d4S0 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      Commute (g * ⟨d4S0 σ, d4S0_mem σ⟩ * g⁻¹) ⟨d4S0 σ, d4S0_mem σ⟩ ∧
        g * ⟨d4S0 σ, d4S0_mem σ⟩ * g⁻¹ ∉ Subgroup.zpowers ⟨d4S0 σ, d4S0_mem σ⟩ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨ζ, hζ⟩ := exists_orderOf_three_d4Row (L := AlgebraicClosure K) hℓ hℓ3
  obtain ⟨k, hk, hkeq⟩ := exists_conj_d4S0 (algebraMap K (AlgebraicClosure K)) σ hζ
  have hdesc : ∀ (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (x : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      x ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) →
      triEmb K σ (AlgebraicClosure K) z = x * rootDiagUnit TwistTag.D4.tag (tup ζ gA) * x⁻¹ →
      ∃ a, a * z * a⁻¹ = ⟨d4S0 σ, d4S0_mem σ⟩ := fun z x hx hzx =>
    CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_conj_of_triEmb_conj hf hK hσ
      (isPointIrreducible_gA hζ) (z := z) (s := ⟨d4S0 σ, d4S0_mem σ⟩) hx hk hzx hkeq
  rcases three_dvd_sub_d4Row (f := f) hℓ hℓ3 with hq | hq
  · exact conj_commute_of_d4Row_torus hℓ hf hK hσ hζ hdesc hq [1, 2, 3, 1, 0, 2, 1, 0]
      [[0, -1, 0, 1], [0, -1, 0, 0], [-1, -1, 0, 1], [-1, -1, 1, 0]] (by decide +kernel)
      ![1, 1, 0, 0] ![0, 1, 1, 1] [1, 2, 0, 3, 2, 1] [1, 2, 3, 2, 0, 1, 2]
      (by decide +kernel) (by decide +kernel) (by decide) (by decide) 2 (by decide) (by decide)
  · exact conj_commute_of_d4Row_torus hℓ hf hK hσ hζ hdesc hq [1, 2, 1, 0]
      [[-1, 0, 1, 0], [-1, 0, 0, 1], [-1, -1, 1, 1], [0, 0, 0, 1]] (by decide +kernel)
      ![0, 1, 0, 1] ![1, 1, 1, 0] [] [3, 2, 1]
      (by decide +kernel) (by decide +kernel) (by decide) (by decide) 0 (by decide) (by decide)

private theorem conj_commute_d4T0 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f)) :
    ∃ g : graphFixedRootGroup TwistTag.D4 K σ.toRingHom,
      Commute (g * ⟨d4T0 σ, d4T0_mem σ⟩ * g⁻¹) ⟨d4T0 σ, d4T0_mem σ⟩ ∧
        g * ⟨d4T0 σ, d4T0_mem σ⟩ * g⁻¹ ∉ Subgroup.zpowers ⟨d4T0 σ, d4T0_mem σ⟩ := by
  haveI : Fact ℓ.Prime := ⟨hℓ⟩
  haveI : CharP K ℓ := finite_field_prime_power_characteristic hℓ (k := f * 3) (by omega)
    (by rw [hK, pow_mul])
  haveI : CharP (AlgebraicClosure K) ℓ :=
    charP_of_injective_algebraMap (algebraMap K (AlgebraicClosure K)).injective ℓ
  obtain ⟨ζ, hζ⟩ := exists_orderOf_three_d4Row (L := AlgebraicClosure K) hℓ hℓ3
  obtain ⟨k, hk, hkeq⟩ := exists_conj_d4T0 (algebraMap K (AlgebraicClosure K)) σ hζ
  have hdesc : ∀ (z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom)
      (x : ModGL TwistTag.D4.tag (AlgebraicClosure K)),
      x ∈ adjointGroup TwistTag.D4.tag (AlgebraicClosure K) →
      triEmb K σ (AlgebraicClosure K) z = x * rootDiagUnit TwistTag.D4.tag (tup ζ gB) * x⁻¹ →
      ∃ a, a * z * a⁻¹ = ⟨d4T0 σ, d4T0_mem σ⟩ := fun z x hx hzx =>
    CFSG.RankThree.PartTwo.Sec11.KS11Lie6Proof.exists_conj_of_triEmb_conj hf hK hσ
      (isPointIrreducible_gB hζ) (z := z) (s := ⟨d4T0 σ, d4T0_mem σ⟩) hx hk hzx hkeq
  rcases three_dvd_sub_d4Row (f := f) hℓ hℓ3 with hq | hq
  · exact conj_commute_of_d4Row_torus hℓ hf hK hσ hζ hdesc hq []
      [[1, 0, 0, 0], [0, 1, 0, 0], [0, 0, 1, 0], [0, 0, 0, 1]] (by decide +kernel)
      ![0, 0, 1, 0] ![1, 1, 1, 1] [] [2, 0, 1, 3, 2]
      (by decide +kernel) (by decide +kernel) (by decide) (by decide) 0 (by decide) (by decide)
  · exact conj_commute_of_d4Row_torus hℓ hf hK hσ hζ hdesc hq [2, 1, 0, 2, 1, 0]
      [[0, -1, 0, 1], [-1, 0, 0, 1], [0, 0, -1, 2], [0, 0, 0, 1]] (by decide +kernel)
      ![1, 0, 1, 0] ![1, 1, 1, 1] [2, 1, 3, 2, 0] [2, 0, 1, 3, 2]
      (by decide +kernel) (by decide +kernel) (by decide) (by decide) 1 (by decide) (by decide)

private theorem conj_commute_trialityD4 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hℓ3 : ℓ ≠ 3) (hf : 1 ≤ f)
    (hK : Nat.card K = (ℓ ^ f) ^ 3) {σ : K ≃+* K} (hσ : ∀ c, σ c = c ^ (ℓ ^ f))
    {z : graphFixedRootGroup TwistTag.D4 K σ.toRingHom} (hz : orderOf z = 3) :
    ∃ g, Commute (g * z * g⁻¹) z ∧ g * z * g⁻¹ ∉ Subgroup.zpowers z := by
  obtain ⟨a, ha | ha⟩ := exists_conj_eq_d4S0_or_d4T0 hℓ hℓ3 hf hK hσ hz
  · exact conj_commute_of_conj a ha (conj_commute_d4S0 hℓ hℓ3 hf hK hσ)
  · exact conj_commute_of_conj a ha (conj_commute_d4T0 hℓ hℓ3 hf hK hσ)

theorem listRow_trialityD4 :
    ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .trialityD4 0 p f →
      p ≠ 2 → p ≠ 3 → ListRow S := by
  intro S _ _ p f h _ hp3 z hz hw
  have hadm := h.admissible
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hm := h.chevalleyExceptionalModel (by decide)
  have htw : CFSG.Blueprint.TwistedChevalleyModel S .D4 (p ^ f) := hm.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  exact absurd hw (not_weaklyClosed_of_conj_commute (conj_commute_of_mulEquiv e
    (conj_commute_trialityD4 hp hp3 hf hK3 hσ (by rw [MulEquiv.orderOf_eq]; exact hz))))

end ListRowProof

section OuterRowProof


theorem outerRow_trialityD4 :
    ∀ (S : Type) [Group S] [Finite S] (p f : ℕ), LieModel S .trialityD4 0 p f →
      p ≠ 2 → p ≠ 3 → OuterRow S := by
  intro S _ _ p f h hp2 hp3
  have hadm := h.admissible
  have hp : p.Prime := hadm.1
  have hf : 1 ≤ f := hadm.2.1
  have hp5 : 5 ≤ p := by
    have h2 := hp.two_le
    rcases (show p = 2 ∨ p = 3 ∨ p = 4 ∨ 5 ≤ p by omega) with h' | h' | h' | h'
    · exact absurd h' hp2
    · exact absurd h' hp3
    · subst h'
      exact absurd hp (by norm_num)
    · exact h'
  have hm := h.chevalleyExceptionalModel (by decide)
  have htw : CFSG.Blueprint.TwistedChevalleyModel S .D4 (p ^ f) := hm.2
  obtain ⟨K, _, _, σ, hK, hσ, ⟨e⟩⟩ := exists_mulEquiv_graphFixedRootGroup_card .D4 hp hf htw
  have hK3 : Nat.card K = (p ^ f) ^ 3 := hK
  obtain ⟨-, -, -, -, -, -, hZC, -⟩ :=
    odd_triality_exact_automorphism_normal_form hp hp2 hf K hK3 σ hσ
  have hZ : Subgroup.center S = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have hex : e x ∈ Subgroup.center (graphFixedRootGroup TwistTag.D4 K σ.toRingHom) := by
      rw [Subgroup.mem_center_iff] at hx ⊢
      intro y
      obtain ⟨y, rfl⟩ := e.surjective y
      simpa only [map_mul] using congrArg e (hx y)
    rw [hZC, Subgroup.mem_bot] at hex
    rw [Subgroup.mem_bot]
    exact e.injective (hex.trans (map_one e).symm)
  have hcard : Nat.card S = CFSG.Open.ordTrialityD4 (p ^ f) :=
    CFSG.ClassicalInvolution.card_chevalleyExceptionalModel_of_ne_two hp2 hm
  refine CFSG.RankThree.PartTwo.Sec4.RonanK432.outerRow_of_fixed_card_dvd hZ
    fun α hα3 hout => ?_
  have hdvd := CFSG.HardMathSupport.Lang.E6Descent.outerFixedOrder_trialityD4_three_odd_aux
    (CFSG.HardMathSupport.Lang.E6Descent.ellQ1Bound_of_rotLang
      CFSG.HardMathSupport.Lang.E6Descent.rotLang_holds)
    CFSG.HardMathSupport.Lang.E6Descent.minusToralBound
    (CFSG.HardMathSupport.Lang.E6Descent.minusEllBound_of_rotLang
      CFSG.HardMathSupport.Lang.E6Descent.rotLang_holds)
    hp hp5 hf S htw α hα3 hout
  refine ⟨CFSG.ComponentClassification.FixedCommutingProduct.fixedSubgroup α,
    CFSG.Open.ordG2 (p ^ f), fun x => Iff.rfl, hdvd, ?_⟩
  rw [hcard]
  exact CFSG.RankThree.PartTwo.Sec4.RonanK432.three_mul_ordG2_dvd_ordTrialityD4 (p ^ f)

end OuterRowProof

end CFSG.LocalAnalysis.UniquenessCase.UCK.K332Route

end

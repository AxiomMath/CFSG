module

public import CFSG.LocalAnalysis.StandardType.GGInndiagNormalOtherCore
public import CFSG.LieType.Chevalley.DiagonalFieldActorData
public import CFSG.LieType.Chevalley.E6ToralGraphInvolution
public import CFSG.LieType.Chevalley.AdjointCenter

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley

namespace InndiagE6

section RootSet

variable {r : ℕ} (S : (Fin r → ℤ) → Prop) (K : Type) [Field K]

theorem markDiag_single_inl (a : Fin r → Kˣ) (i : Fin r) (c : K) :
    TableB.markDiag S K a (Finsupp.single (Sum.inl i) c) = Finsupp.single (Sum.inl i) c := by
  simp [TableB.markDiag, MarkChev.hVec]

theorem markDiag_single_inr (a : Fin r → Kˣ) (α : {v : Fin r → ℤ // S v}) (c : K) :
    TableB.markDiag S K a (Finsupp.single (Sum.inr α) c) =
      ((∏ i, a i ^ α.1 i : Kˣ) : K) • Finsupp.single (Sum.inr α) c := by
  simp [TableB.markDiag, mul_comm]

theorem markDiag_mul (a b : Fin r → Kˣ) :
    TableB.markDiag S K (a * b) = TableB.markDiag S K a * TableB.markDiag S K b := by
  apply Finsupp.lhom_ext
  rintro (i | α) c
  · simp [markDiag_single_inl]
  · simp only [Module.End.mul_apply, markDiag_single_inr, map_smul, smul_smul]
    congr 1
    simp only [Pi.mul_apply, mul_zpow, Finset.prod_mul_distrib, Units.val_mul]
    ring

theorem markDiag_one : TableB.markDiag S K 1 = 1 := by
  apply Finsupp.lhom_ext
  rintro (i | α) c
  · simp [markDiag_single_inl]
  · simp [markDiag_single_inr]

@[expose] noncomputable def markDiagUnit (a : Fin r → Kˣ) : MarkChev.GLS S K :=
  ⟨TableB.markDiag S K a, TableB.markDiag S K a⁻¹,
    by rw [← markDiag_mul, mul_inv_cancel, markDiag_one],
    by rw [← markDiag_mul, inv_mul_cancel, markDiag_one]⟩

theorem diagHom_eq_markDiagUnit (A : Matrix (Fin r) (Fin r) ℤ) :
    TableB.diagHom A K = markDiagUnit (LargeEvenIsRoot A) K :=
  funext fun a => Units.ext (TableB.largeEvenDiagMap_eq_markDiag A K a)

theorem markDiagUnit_isRoot (τ : Tag) :
    markDiagUnit (IsRoot τ) K = rootDiagUnit τ :=
  funext fun a => Units.ext (TableB.TwE6.markDiag_isRoot a)

@[expose] def ChevNFOn (τ : Tag) (S : (Fin τ.rank → ℤ) → Prop) : Prop :=
  Subgroup.center (MarkChev.chevH τ.cartan S K false) = ⊥ ∧
    DiagNF (MarkChev.chevH τ.cartan S K false) (markDiagUnit S K)

variable {K} in
theorem ChevNFOn.of_eq {τ : Tag} {S S' : (Fin τ.rank → ℤ) → Prop} (hS : S = S')
    (h : ChevNFOn K τ S) : ChevNFOn K τ S' :=
  hS ▸ h

end RootSet

section E6

variable (K : Type) [Field K]

theorem exactQ_E6_mul_rootDiagUnit
    (ε : ℕ) (c : Fin TwistTag.E6.tag.rank → Kˣ) :
    ∃ c' : Fin TwistTag.E6.tag.rank → Kˣ,
      exactQ TwistTag.E6.tag K ε * rootDiagUnit TwistTag.E6.tag c =
        rootDiagUnit TwistTag.E6.tag c' * exactQ TwistTag.E6.tag K ε := by
  have hP : ∀ b : Fin TwistTag.E6.tag.rank → Kˣ,
      (diagramMap TwistTag.E6 K : ModGL TwistTag.E6.tag K) * rootDiagUnit TwistTag.E6.tag b =
        rootDiagUnit TwistTag.E6.tag (fun i => b (TwistTag.E6.perm.symm i)) *
          (diagramMap TwistTag.E6 K : ModGL TwistTag.E6.tag K) :=
    fun b => diagramMap_mul_rootDiagUnit (t := TwistTag.E6) b
  induction ε generalizing c with
  | zero =>
    refine ⟨c, ?_⟩
    change (diagramMap TwistTag.E6 K : ModGL TwistTag.E6.tag K) ^ 0 * _ =
      _ * (diagramMap TwistTag.E6 K : ModGL TwistTag.E6.tag K) ^ 0
    rw [pow_zero, one_mul, mul_one]
  | succ ε ih =>
    obtain ⟨c'', hc''⟩ := ih (fun i => c (TwistTag.E6.perm.symm i))
    refine ⟨c'', ?_⟩
    change (diagramMap TwistTag.E6 K : ModGL TwistTag.E6.tag K) ^ ε * _ =
      _ * (diagramMap TwistTag.E6 K : ModGL TwistTag.E6.tag K) ^ ε at hc''
    change (diagramMap TwistTag.E6 K : ModGL TwistTag.E6.tag K) ^ (ε + 1) * _ =
      _ * (diagramMap TwistTag.E6 K : ModGL TwistTag.E6.tag K) ^ (ε + 1)
    rw [pow_succ, mul_assoc, hP, ← mul_assoc, hc'', mul_assoc]


theorem diagNF_adjointGroup_E6 [Finite K] :
    DiagNF (adjointGroup TwistTag.E6.tag K) (rootDiagUnit TwistTag.E6.tag) := by
  intro α b _ _
  obtain ⟨-, -, hnf⟩ := ordinary_E_exact_automorphism_normal_form TwistTag.E6.tag (Or.inl rfl) K
  obtain ⟨g, a, σ, ε, hα⟩ := hnf α
  set c : Fin TwistTag.E6.tag.rank → Kˣ := fun i => Units.map σ.toRingHom.toMonoidHom (b i) with hc
  obtain ⟨c', hc'⟩ := exactQ_E6_mul_rootDiagUnit K (ε : ℕ) c
  have hσd : Units.map (entrywiseHom σ.toRingHom) (rootDiagUnit TwistTag.E6.tag b) =
      rootDiagUnit TwistTag.E6.tag c :=
    units_map_entrywiseHom_rootDiagUnit_ringEquiv σ b
  have hcomm : rootDiagUnit TwistTag.E6.tag a * rootDiagUnit TwistTag.E6.tag c' =
      rootDiagUnit TwistTag.E6.tag c' * rootDiagUnit TwistTag.E6.tag a := by
    rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]
  refine ⟨g, g.2, c', fun h hh => conj_rootDiagUnit_mem_adjointGroup c' hh, fun h hh => ?_,
    fun h hh => ?_⟩
  · have := conj_rootDiagUnit_mem_adjointGroup (K := K) (c'⁻¹) hh
    rwa [rootDiagUnit_inv c'⁻¹, inv_inv, ← rootDiagUnit_inv] at this
  · have e1 := hα ⟨_, hh⟩
    have e2 := hα h
    rw [Subgroup.coe_mk, map_mul, map_mul, map_inv, hσd] at e1
    rw [e1, e2]
    set Q := exactQ TwistTag.E6.tag K (ε : ℕ)
    set S := Units.map (entrywiseHom σ.toRingHom) (h : ModGL TwistTag.E6.tag K)
    set G : ModGL TwistTag.E6.tag K := (g : ModGL TwistTag.E6.tag K)
    set da := rootDiagUnit TwistTag.E6.tag a
    set dc := rootDiagUnit TwistTag.E6.tag c
    set dc' := rootDiagUnit TwistTag.E6.tag c'
    calc G * da * Q * (dc * S * dc⁻¹) * Q⁻¹ * da⁻¹ * G⁻¹
        = G * da * (Q * dc) * S * (Q * dc)⁻¹ * da⁻¹ * G⁻¹ := by group
      _ = G * (da * dc') * Q * S * Q⁻¹ * (da * dc')⁻¹ * G⁻¹ := by rw [hc']; group
      _ = G * (dc' * da) * Q * S * Q⁻¹ * (dc' * da)⁻¹ * G⁻¹ := by rw [hcomm]
      _ = _ := by group

theorem chevNFOn_isRoot_E6 [Finite K] : ChevNFOn K TwistTag.E6.tag (IsRoot TwistTag.E6.tag) := by
  unfold ChevNFOn
  rw [chevH_false_eq_adjointGroup K TwistTag.E6.tag, markDiagUnit_isRoot]
  exact ⟨center_adjointGroup_eq_bot, diagNF_adjointGroup_E6 K⟩

theorem ggInndiagNormal_E6 [Finite K] :
    GGInndiagNormal (LargeEvenCenterQuot (LargeEvenChevH TwistTag.E6.tag.cartan K false))
      (LargeEvenChevIDImage TwistTag.E6.tag.cartan K
        (LargeEvenChevH TwistTag.E6.tag.cartan K false)) := by
  obtain ⟨hZ, hNF⟩ := (chevNFOn_isRoot_E6 K).of_eq (largeEvenIsRoot_eq_isRoot TwistTag.E6.tag).symm
  apply ggInndiagNormal_chevID_of_diagNF
  · rw [largeEvenChevH_eq]
    exact hZ
  · rw [largeEvenChevH_eq, diagHom_eq_markDiagUnit]
    exact hNF

end E6

end InndiagE6

end CFSG.StandardType

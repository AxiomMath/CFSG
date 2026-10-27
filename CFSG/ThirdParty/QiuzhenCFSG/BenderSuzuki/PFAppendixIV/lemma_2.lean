module

public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.InducedIrreducible
public import CFSG.ThirdParty.QiuzhenCFSG.Theory.Representation.Clifford
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.problem_7_1
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_1
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection1.PFsection1_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection2.PFsection2_6
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection3.PFsection3_5
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PFsection5.Basic

namespace CFSG
end CFSG
open CFSG

/-!
# Peterfalvi Appendix IV, Lemma 2

The statement follows the authoritative PFpart2 PNG (printed pages 144--145).
It concerns the exceptional irreducible characters of `H`.
-/

noncomputable section

open scoped BigOperators

attribute [local instance] Fintype.ofFinite

namespace CFSG.BenderSuzuki
namespace PFAppendixIV

open Section1 Section5 PFchapter1section1

universe u v

/-- The subgroup data fixed in Peterfalvi Appendix IV.  All four named factors
are subgroups of `H`, as in the printed statement.  The explicit oddness of
`Q₁` restores the standing hypothesis used (but not restated) in Lemma 2(c). -/
public structure FeitSibleyData (G : Type u) [Group G] where
  H : Subgroup G
  Q : Subgroup H
  D : Subgroup H
  S : Subgroup H
  Q1 : Subgroup H
  H_ne_top : H ≠ ⊤
  Q_normal : Q.Normal
  H_eq_Q_sup_D : Q ⊔ D = ⊤
  Q_disjoint_D : Disjoint Q D
  S_le_Q : S ≤ Q
  Q1_le_Q : Q1 ≤ Q
  Q_eq_S_sup_Q1 : S ⊔ Q1 = Q
  S_disjoint_Q1 : Disjoint S Q1
  S_commutes_Q1 :
    ∀ s q : H, s ∈ S → q ∈ Q1 → s * q = q * s
  card_Q_coprime_card_D : Nat.Coprime (Nat.card Q) (Nat.card D)
  card_S_coprime_card_Q1 : Nat.Coprime (Nat.card S) (Nat.card Q1)
  Q1_normal_in_Q : (Q1.subgroupOf Q).Normal
  D_normalizes_Q1 :
    ∀ d : D, ∀ q : Q1, (d : H) * (q : H) * (d : H)⁻¹ ∈ Q1
  D_fixedPointFree_on_Q1 :
    ∀ d : D, (d : H) ≠ 1 → ∀ q : Q1,
      (d : H) * (q : H) * (d : H)⁻¹ = (q : H) → q = 1
  Q_TI_in_G :
    ∀ g : G, g ∉ H →
      Disjoint (Q.map H.subtype) (rightConjugate (Q.map H.subtype) g)
  Q1_not_two_group : ¬ IsPGroup 2 Q1
  Q1_odd : Odd (Nat.card Q1)
  S_nilpotent : Group.IsNilpotent S

/-- `Q` viewed as a subgroup of `G`. -/
@[expose] public def FeitSibleyData.QInG
    {G : Type u} [Group G] (d : FeitSibleyData G) : Subgroup G :=
  d.Q.map d.H.subtype

/-- The exceptional family: precisely the irreducible characters of `H`
whose kernels do not contain `Q₁`. -/
@[expose] public def IsFeitSibleyExceptionalFamily
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H)) : Prop :=
  ∀ chi : ClassFunction d.H,
    chi ∈ chars ↔
      IsIrreducibleCharacterOnGroup chi ∧
        ¬ subgroupInKernel' chi d.Q1

private theorem classFunction_eq_of_irreducible_scalarProduct_ne_zero_appendixIV
    {L : Type u} [Group L] [Finite L]
    {φ ψ : Section1.ClassFunction L}
    (hφ : Section1.IsIrreducibleCharacterOnGroup φ)
    (hψ : Section1.IsIrreducibleCharacterOnGroup ψ)
    (hinner : Section1.scalarProduct L φ ψ ≠ 0) :
    φ = ψ := by
  by_contra hne
  have hzero :
      Section1.scalarProduct L φ ψ = 0 :=
    Section1.scalarProduct_irreducibleCharacter_eq_zero_of_ne hφ hψ hne
  exact hinner hzero

private theorem inducedCF_eq_of_irreducible_constituent_appendixIV
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {χ : Section1.ClassFunction L} {ψ : Section1.ClassFunction K}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ)
    (hIndψ : Section1.IsIrreducibleCharacterOnGroup (Section1.inducedCF K ψ))
    (hinner :
      Section1.scalarProduct K ψ (Section1.subgroupRestriction K χ) ≠ 0) :
    χ = Section1.inducedCF K ψ := by
  have hχclass : Section1.IsClassFunction χ := by
    rcases hχ with ⟨_n, ρ, _hρirr, hχeq⟩
    intro x g
    rw [hχeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρ) g x
  have hinnerInd :
      Section1.scalarProduct L (Section1.inducedCF K ψ) χ ≠ 0 := by
    rw [Section1.scalarProduct_inducedCF_left K ψ χ hχclass]
    exact hinner
  exact (classFunction_eq_of_irreducible_scalarProduct_ne_zero_appendixIV
    hIndψ hχ hinnerInd).symm


private theorem constituent_not_subgroupInKernel'_of_subgroupRestriction_not_kernel_appendixIV
    {L : Type u} [Group L] [Finite L]
    (K A : Subgroup L) [K.Normal] [A.Normal] (hAK : A ≤ K)
    {χ : Section1.ClassFunction L} {θ : Section1.ClassFunction K}
    (hχirr : Section1.IsIrreducibleCharacterOnGroup χ)
    (hχnotker : ¬ Section1.subgroupInKernel' χ A)
    (hθirr : Section1.IsIrreducibleCharacterOnGroup θ)
    (hinner :
      Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0) :
    ¬ Section1.subgroupInKernel' θ (A.subgroupOf K) := by
  classical
  intro hθker
  rcases hχirr with ⟨nχ, ρχ, hρχirr, hχeq⟩
  rcases hθirr with ⟨nθ, ρθ, _hρθirr, hθeq⟩
  let indρθ : Representation ℂ L (Representation.IndV K.subtype ρθ) :=
    Representation.ind K.subtype ρθ
  haveI : FiniteDimensional ℂ (Representation.IndV K.subtype ρθ) :=
    Theory.Representation.finiteDimensional_ind K ρθ
  have hIndCharKer :
      Section1.subgroupInKernel' (Section1.inducedCF K ρθ.character) A :=
    (Section1.proposition_1_6_a K A hAK ρθ).mp
      (by simpa [hθeq] using hθker)
  have hIndRepKer : Section1.subgroupInRepresentationKernel indρθ A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      indρθ A).mp (by
        simpa [indρθ, Section1.inducedCF_eq_representation_character K ρθ]
          using hIndCharKer)
  have hχclass : Section1.IsClassFunction χ := by
    intro x g
    rw [hχeq]
    simpa [mul_assoc] using Representation.char_conj (ρ := ρχ) g x
  have hIndInner :
      Section1.scalarProduct L (Section1.inducedCF K θ) χ ≠ 0 := by
    rw [Section1.scalarProduct_inducedCF_left K θ χ hχclass]
    exact hinner
  have hIndInnerRep :
      Section1.scalarProduct L indρθ.character ρχ.character ≠ 0 := by
    simpa [indρθ, hχeq, hθeq,
      Section1.inducedCF_eq_representation_character K ρθ] using hIndInner
  have hfinrank_ne :
      (Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) : ℂ) ≠ 0 := by
    simpa [Section1.scalarProduct_representation_char_eq_finrank ρχ indρθ]
      using hIndInnerRep
  have hfinrank_nat_ne :
      Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) ≠ 0 := by
    intro hzero
    apply hfinrank_ne
    simp [hzero]
  have hfinrank_pos :
      0 < Module.finrank ℂ (Representation.IntertwiningMap ρχ indρθ) :=
    Nat.pos_of_ne_zero hfinrank_nat_ne
  rw [Module.finrank_pos_iff_exists_ne_zero] at hfinrank_pos
  rcases hfinrank_pos with ⟨f, hf⟩
  have hχRepKer : Section1.subgroupInRepresentationKernel ρχ A := by
    letI : Representation.IsIrreducible ρχ := hρχirr
    have hf_inj : Function.Injective f := by
      rcases (Representation.IsIrreducible.injective_or_eq_zero
          (ρ := ρχ) (σ := indρθ) f) with hinj | hzero
      · exact hinj
      · exact (hf hzero).elim
    intro a
    apply LinearMap.ext
    intro v
    apply hf_inj
    calc
      f (ρχ (a : L) v) = indρθ (a : L) (f v) := by
        exact Representation.IntertwiningMap.isIntertwining ρχ indρθ f (a : L) v
      _ = f v := by
        rw [hIndRepKer a]
        simp
  have hχkerChar : Section1.subgroupInKernel' ρχ.character A :=
    (Section1.subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      ρχ A).mpr hχRepKer
  exact hχnotker (by simpa [hχeq] using hχkerChar)

private theorem exists_irreducible_constituent_of_subgroupRestriction_appendixIV
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L)
    {χ : Section1.ClassFunction L}
    (hχ : Section1.IsIrreducibleCharacterOnGroup χ) :
    ∃ θ : Section1.ClassFunction K,
      Section1.IsIrreducibleCharacterOnGroup θ ∧
        Section1.scalarProduct K θ (Section1.subgroupRestriction K χ) ≠ 0 := by
  rcases hχ with ⟨n, ρ, hρirr, hρchar⟩
  let ρK : Representation ℂ K (Fin n → ℂ) := ρ.comp K.subtype
  letI : Nontrivial (Fin n → ℂ) :=
    Subrepresentation.irreducible_module_nontrivial ρ
  obtain ⟨φ, hφirr⟩ :=
    Subrepresentation.irreducible_subrepresentation_of_finite_dimensional ρK
  letI : Nontrivial φ.toSubmodule :=
    Subrepresentation.irreducible_module_nontrivial φ.toRepresentation
  let incl : Theory.Representation.RepMap φ.toRepresentation ρK := by
    refine Theory.Representation.RepMap.mk φ.toSubmodule.subtype ?_
    intro k
    ext v
    rfl
  have hincl_ne : incl ≠ 0 := by
    intro hzero
    obtain ⟨v, hv⟩ := exists_ne (0 : φ.toSubmodule)
    have hval : incl v = 0 := by
      simpa using
        congrArg (fun f : Theory.Representation.RepMap φ.toRepresentation ρK => f v)
          hzero
    have hsub : v = 0 := by
      apply Subtype.ext
      simpa [incl] using hval
    exact hv hsub
  have hinner_res :
      Section1.scalarProduct K ρK.character φ.toRepresentation.character ≠ 0 := by
    have hfinpos :
        0 < Module.finrank ℂ
          (Representation.IntertwiningMap φ.toRepresentation ρK) := by
      rw [Module.finrank_pos_iff_exists_ne_zero]
      exact ⟨incl, hincl_ne⟩
    rw [Section1.scalarProduct_representation_char_eq_finrank]
    exact_mod_cast (Nat.ne_of_gt hfinpos)
  have hresChar :
      Section1.subgroupRestriction K χ = ρK.character := by
    ext k
    simp [ρK, Section1.subgroupRestriction, hρchar, Representation.character]
  refine ⟨φ.toRepresentation.character, ?_, ?_⟩
  · refine ⟨Module.finrank ℂ φ.toSubmodule,
      Section1.standardizeRepresentation φ.toRepresentation, ?_, ?_⟩
    · exact Section1.standardizeRepresentation_irreducible φ.toRepresentation hφirr
    · ext k
      symm
      exact Section1.standardizeRepresentation_character φ.toRepresentation k
  · have hinner_res' :
        Section1.scalarProduct K (Section1.subgroupRestriction K χ)
          φ.toRepresentation.character ≠ 0 := by
      simpa [hresChar] using hinner_res
    exact
      (Section1.scalarProduct_ne_zero_swap
        φ.toRepresentation.character (Section1.subgroupRestriction K χ)).2
        hinner_res'


/-- The printed direct-product and semidirect-product hypotheses make `Q₁`
normal in `H`. -/
public theorem FeitSibleyData.Q1_normal
    {G : Type u} [Group G] [Finite G] (d : FeitSibleyData G) :
    d.Q1.Normal := by
  letI : d.Q.Normal := d.Q_normal
  refine ⟨?_⟩
  intro n hn g
  have hg : g ∈ d.Q ⊔ d.D := by
    rw [d.H_eq_Q_sup_D]
    trivial
  rcases (Subgroup.mem_sup_of_normal_left.mp hg) with ⟨q, hq, e, he, rfl⟩
  have hen : e * n * e⁻¹ ∈ d.Q1 :=
    d.D_normalizes_Q1 ⟨e, he⟩ ⟨n, hn⟩
  let qQ : d.Q := ⟨q, hq⟩
  let enQ : d.Q := ⟨e * n * e⁻¹, d.Q1_le_Q hen⟩
  have hconjQ : qQ * enQ * qQ⁻¹ ∈ d.Q1.subgroupOf d.Q :=
    d.Q1_normal_in_Q.conj_mem enQ hen qQ
  have hconjH : q * (e * n * e⁻¹) * q⁻¹ ∈ d.Q1 := by
    exact hconjQ
  rw [mul_inv_rev]
  simpa only [mul_assoc] using hconjH

/-- Fixed-point-free action of `D` supplies the centralizer hypothesis of
Isaacs 6.34 inside `Q1 D`. -/
private theorem FeitSibleyData.Q1D_centralizer
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) (hDne : d.D ≠ ⊥) :
    let K : Subgroup d.H := d.Q1 ⊔ d.D
    let N : Subgroup K := d.Q1.subgroupOf K
    ∀ n : N, n ≠ 1 →
      Subgroup.centralizer ({(n : K)} : Set K) ≤ N := by
  letI : d.Q1.Normal := d.Q1_normal
  let K : Subgroup d.H := d.Q1 ⊔ d.D
  let N : Subgroup K := d.Q1.subgroupOf K
  let E : Subgroup K := d.D.subgroupOf K
  haveI : N.Normal := by
    simpa [N, K] using
      (Subgroup.Normal.subgroupOf (inferInstance : d.Q1.Normal) K)
  have hQ1ne : d.Q1 ≠ ⊥ := by
    intro hQ1
    apply d.Q1_not_two_group
    rw [hQ1]
    exact IsPGroup.of_bot
  have hNne : N ≠ ⊥ := by
    intro hN
    apply hQ1ne
    exact (Subgroup.subgroupOf_eq_bot.mp hN).eq_bot_of_le le_sup_left
  have hEne : E ≠ ⊥ := by
    intro hE
    apply hDne
    exact (Subgroup.subgroupOf_eq_bot.mp hE).eq_bot_of_le le_sup_right
  have hsup : N ⊔ E = ⊤ := by
    rw [← Subgroup.subgroupOf_sup le_sup_left le_sup_right]
    exact Subgroup.subgroupOf_self K
  have hdisj : Disjoint N E := by
    rw [Subgroup.disjoint_def]
    intro x hxN hxE
    apply Subtype.ext
    have hxQ1 : ((x : K) : d.H) ∈ d.Q1 := hxN
    have hxQ : ((x : K) : d.H) ∈ d.Q := d.Q1_le_Q hxQ1
    have hxD : ((x : K) : d.H) ∈ d.D := hxE
    have hxbot : ((x : K) : d.H) ∈ (⊥ : Subgroup d.H) :=
      (Subgroup.disjoint_def.mp d.Q_disjoint_D) hxQ hxD
    simpa using hxbot
  have hfixed :
      ∀ n : N, n ≠ 1 → ∀ e : E,
        (e : K) * (n : K) = (n : K) * (e : K) → e = 1 := by
    intro n hn e hcomm
    by_contra he
    let nQ1 : d.Q1 := ⟨((n : K) : d.H), n.property⟩
    let eD : d.D := ⟨((e : K) : d.H), e.property⟩
    have hnQ1 : nQ1 ≠ 1 := by
      intro hn1
      apply hn
      apply Subtype.ext
      apply Subtype.ext
      simpa [nQ1] using congrArg Subtype.val hn1
    have heD : eD ≠ 1 := by
      intro he1
      apply he
      apply Subtype.ext
      apply Subtype.ext
      simpa [eD] using congrArg Subtype.val he1
    have heDH : (eD : d.H) ≠ 1 := by
      intro he1
      apply heD
      apply Subtype.ext
      exact he1
    have hcommH :
        (eD : d.H) * (nQ1 : d.H) = (nQ1 : d.H) * (eD : d.H) :=
      congrArg (fun x : K => (x : d.H)) hcomm
    have hfix :
        (eD : d.H) * (nQ1 : d.H) * (eD : d.H)⁻¹ = (nQ1 : d.H) := by
      rw [hcommH]
      simp
    exact hnQ1 (d.D_fixedPointFree_on_Q1 eD heDH nQ1 hfix)
  exact
    (External.Isaacs.VII.isaacs_problem_7_1
      N E hNne hEne hsup hdisj).1.mpr hfixed

public theorem FeitSibleyData.exists_Q_mul_D
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) (g : d.H) :
    ∃ q : d.Q, ∃ e : d.D, (q : d.H) * (e : d.H) = g := by
  letI : d.Q.Normal := d.Q_normal
  have hg : g ∈ d.Q ⊔ d.D := by
    rw [d.H_eq_Q_sup_D]
    trivial
  rcases Subgroup.mem_sup_of_normal_left.mp hg with ⟨q, hq, e, he, hqe⟩
  exact ⟨⟨q, hq⟩, ⟨e, he⟩, hqe⟩

public theorem FeitSibleyData.exists_Q1_inner_conjugator
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) (q : d.Q) :
    ∃ q1 : d.Q1, ∀ x : d.Q1,
      (q : d.H) * (x : d.H) * (q : d.H)⁻¹ =
        (q1 : d.H) * (x : d.H) * (q1 : d.H)⁻¹ := by
  letI : d.Q1.Normal := d.Q1_normal
  have hq : (q : d.H) ∈ d.S ⊔ d.Q1 := by
    rw [d.Q_eq_S_sup_Q1]
    exact q.property
  rcases Subgroup.mem_sup_of_normal_right.mp hq with ⟨s, hs, q1, hq1, hsq⟩
  let q1' : d.Q1 := ⟨q1, hq1⟩
  refine ⟨q1', ?_⟩
  intro x
  have hy : q1 * (x : d.H) * q1⁻¹ ∈ d.Q1 :=
    d.Q1_normal.conj_mem (x : d.H) x.property q1
  have hcomm : s * (q1 * (x : d.H) * q1⁻¹) =
      (q1 * (x : d.H) * q1⁻¹) * s :=
    d.S_commutes_Q1 s (q1 * (x : d.H) * q1⁻¹) hs hy
  rw [← hsq]
  change (s * q1) * (x : d.H) * (s * q1)⁻¹ =
    q1 * (x : d.H) * q1⁻¹
  rw [mul_inv_rev]
  calc
    (s * q1) * (x : d.H) * (q1⁻¹ * s⁻¹) =
        s * (q1 * (x : d.H) * q1⁻¹) * s⁻¹ := by group
    _ = (q1 * (x : d.H) * q1⁻¹) * s * s⁻¹ := by rw [hcomm]
    _ = q1 * (x : d.H) * q1⁻¹ := by simp
private noncomputable def subrepresentationOrderIso_compMulEquiv_appendixIV
    {A B V : Type*} [Group A] [Group B] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ A V) (e : B ≃* A) :
    Subrepresentation rho ≃o Subrepresentation (rho.comp e.toMonoidHom) where
  toFun S :=
    { toSubmodule := S.toSubmodule
      apply_mem_toSubmodule := by
        intro b v hv
        exact S.apply_mem_toSubmodule (e b) hv }
  invFun T :=
    { toSubmodule := T.toSubmodule
      apply_mem_toSubmodule := by
        intro a v hv
        have hmem := T.apply_mem_toSubmodule (e.symm a) hv
        simpa using hmem }
  left_inv S := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  right_inv T := by
    apply Subrepresentation.toSubmodule_injective
    rfl
  map_rel_iff' := by
    intro S T
    rfl

private theorem irreducible_compMulEquiv_appendixIV
    {A B V : Type*} [Group A] [Group B] [AddCommGroup V] [Module ℂ V]
    (rho : Representation ℂ A V) (e : B ≃* A)
    [Representation.IsIrreducible rho] :
    Representation.IsIrreducible (rho.comp e.toMonoidHom) := by
  exact (OrderIso.isSimpleOrder_iff
    (subrepresentationOrderIso_compMulEquiv_appendixIV rho e)).mp inferInstance

private theorem FeitSibleyData.Q_conjugates_Q1_rep_equiv
    {G V : Type*} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    (d : FeitSibleyData G) [(d.Q1.subgroupOf d.Q).Normal]
    (rho : Representation ℂ (d.Q1.subgroupOf d.Q) V) (q : d.Q) :
    Nonempty (rho ≃ₗ Theory.Representation.conjugateRep
      (G := d.Q) (H := d.Q1.subgroupOf d.Q) rho q) := by
  rcases d.exists_Q1_inner_conjugator q with ⟨q1, hq1⟩
  let q1Q : d.Q := ⟨(q1 : d.H), d.Q1_le_Q q1.property⟩
  let q1N : d.Q1.subgroupOf d.Q := ⟨q1Q, q1.property⟩
  have hconj : Theory.Representation.conjugateRep
      (G := d.Q) (H := d.Q1.subgroupOf d.Q) rho q =
      Theory.Representation.conjugateRep rho q1Q := by
    ext x v
    simp only [Theory.Representation.conjugateRep_apply]
    congr 2
    apply Subtype.ext
    apply Subtype.ext
    let xQ1 : d.Q1 := ⟨((x : d.Q1.subgroupOf d.Q) : d.Q), x.property⟩
    exact hq1 xQ1
  rw [hconj]
  exact ⟨conj_equiv_of_mem rho q1N⟩

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
/-- An irreducible `Q`-representation restricts homogeneously to `Q1` once one
irreducible constituent is fixed. -/
public theorem lemma_2_Q1_restriction_homogeneous
    {G : Type u} {V : Type v} [Group G] [Finite G] [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V]
    (d : FeitSibleyData G) (rho : Representation ℂ d.Q V)
    (hrho : Representation.IsIrreducible rho)
    (W : Subrepresentation (rho.comp (d.Q1.subgroupOf d.Q).subtype))
    (hW : Representation.IsIrreducible W.toRepresentation) :
    ∃ m : ℕ, m ≠ 0 ∧
      (show Representation ℂ (d.Q1.subgroupOf d.Q) V from
        rho.comp (d.Q1.subgroupOf d.Q).subtype).character =
          (m : ℂ) • W.toRepresentation.character := by
  letI : (d.Q1.subgroupOf d.Q).Normal := d.Q1_normal_in_Q
  let rhoN : Representation ℂ (d.Q1.subgroupOf d.Q) V :=
    rho.comp (d.Q1.subgroupOf d.Q).subtype
  letI : Nontrivial V :=
    Subrepresentation.irreducible_module_nontrivial rho
  rcases Theory.Representation.isaacs_theorem_6_5.{0, u, v, v} rho
      (d.Q1.subgroupOf d.Q) hrho W hW with
    ⟨m, g, hInternal, _hIrr, hConj, _hMultiplicity⟩
  let U : Fin m → Subrepresentation rhoN := fun i =>
    Theory.Representation.conjugateSubrepresentation rho
      (d.Q1.subgroupOf d.Q) W (g i)
  change DirectSum.IsInternal (fun i => (U i).toSubmodule) at hInternal
  have hUequiv (i : Fin m) :
      Nonempty ((U i).toRepresentation ≃ₗ W.toRepresentation) := by
    rcases hConj i with ⟨eU⟩
    rcases d.Q_conjugates_Q1_rep_equiv W.toRepresentation (g i) with ⟨eW⟩
    exact ⟨eU.trans eW.symm⟩
  have hchar : rhoN.character = (m : ℂ) • W.toRepresentation.character := by
    funext x
    change LinearMap.trace ℂ V (rhoN x) =
      (m : ℂ) * W.toRepresentation.character x
    calc
      LinearMap.trace ℂ V (rhoN x) =
          ∑ i : Fin m, LinearMap.trace ℂ ↥(U i).toSubmodule
            ((rhoN x).restrict ((U i).apply_mem_toSubmodule x)) := by
        exact LinearMap.trace_eq_sum_trace_restrict hInternal
          (fun i => (U i).apply_mem_toSubmodule x)
      _ = ∑ i : Fin m, W.toRepresentation.character x := by
        apply Finset.sum_congr rfl
        intro i _hi
        change (U i).toRepresentation.character x =
          W.toRepresentation.character x
        exact congrFun (Representation.char_iso (Theory.Representation.RepEquiv.toRepresentationEquiv (hUequiv i).some)) x
      _ = (m : ℂ) * W.toRepresentation.character x := by simp
  have hm : m ≠ 0 := by
    intro hm0
    have hzero : rhoN.character 1 = 0 := by
      rw [hchar]
      simp [hm0]
    have hpos : 0 < Module.finrank ℂ V := Module.finrank_pos
    have hcharOne : rhoN.character 1 = (Module.finrank ℂ V : ℂ) := by
      exact Representation.char_one rhoN
    rw [hcharOne] at hzero
    exact (Nat.ne_of_gt hpos) (Nat.cast_eq_zero.mp hzero)
  exact ⟨m, hm, hchar⟩
/-- The forward source step of Lemma 2(a).  Its proof is the direct-product
constituent argument, Isaacs 6.34 on `Q₁ ⋊ D`, and Isaacs 6.11. -/
private theorem inducedCF_irreducible_of_subgroup_eq_top_appendixIV
    {L : Type u} [Group L] [Finite L]
    (K : Subgroup L) [K.Normal]
    (hKtop : K = ⊤)
    {phi : ClassFunction K}
    (hphi : IsIrreducibleCharacterOnGroup phi) :
    IsIrreducibleCharacterOnGroup (inducedCF K phi) := by
  rcases hphi with ⟨n, rho, hrhoirr, hphieq⟩
  have hclass : IsClassFunction rho.character := by
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := rho) g x
  have hKleI : K ≤ inertiaSubgroup K rho.character := by
    intro k hk
    change conjugateOnNormal K rho.character k = rho.character
    funext x
    exact hclass ⟨k, hk⟩ x
  have hIleK : inertiaSubgroup K rho.character ≤ K := by
    intro x _hx
    rw [hKtop]
    trivial
  have hr : K.relIndex (inertiaSubgroup K rho.character) = 1 :=
    (Subgroup.relIndex_eq_one).2 hIleK
  simpa [hphieq] using
    proposition_1_5_b_irreducible_rep_orbit_relIndex_canonical K rho hrhoirr hr

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem lemma_2_D_eq_one_of_mem_inertia
    {G : Type u} {V : Type v} [Group G] [Finite G]
    [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (d : FeitSibleyData G) [d.Q.Normal] (hDne : d.D ≠ ⊥)
    (rho : Representation ℂ d.Q V)
    (W : Subrepresentation (rho.comp (d.Q1.subgroupOf d.Q).subtype))
    (hW : Representation.IsIrreducible W.toRepresentation)
    (hWnonprincipal :
      ¬ Nonempty (W.toRepresentation ≃ₗ
        Representation.trivial ℂ (d.Q1.subgroupOf d.Q) ℂ))
    {m : ℕ} (hm : m ≠ 0)
    (hhom :
      (show Representation ℂ (d.Q1.subgroupOf d.Q) V from
        rho.comp (d.Q1.subgroupOf d.Q).subtype).character =
          (m : ℂ) • W.toRepresentation.character)
    (e : d.D)
    (he : (e : d.H) ∈ inertiaSubgroup d.Q rho.character) :
    e = 1 := by
  classical
  letI : d.Q1.Normal := d.Q1_normal
  let NQ : Subgroup d.Q := d.Q1.subgroupOf d.Q
  let K : Subgroup d.H := d.Q1 ⊔ d.D
  let NK : Subgroup K := d.Q1.subgroupOf K
  haveI : NK.Normal := by
    simpa [NK, K] using
      (Subgroup.Normal.subgroupOf (inferInstance : d.Q1.Normal) K)
  let eNQ : NQ ≃* d.Q1 := Subgroup.subgroupOfEquivOfLe d.Q1_le_Q
  let eNK : NK ≃* d.Q1 := Subgroup.subgroupOfEquivOfLe le_sup_left
  let eQK : NQ ≃* NK := eNQ.trans eNK.symm
  let rhoN : Representation ℂ NQ V := rho.comp NQ.subtype
  let sigma : Representation ℂ NK W.toSubmodule :=
    W.toRepresentation.comp eQK.symm.toMonoidHom
  letI : Representation.IsIrreducible W.toRepresentation := hW
  have hsigmaIrr : Representation.IsIrreducible sigma := by
    exact irreducible_compMulEquiv_appendixIV W.toRepresentation eQK.symm
  letI : Representation.IsIrreducible sigma := hsigmaIrr
  letI : FiniteDimensional ℂ W.toSubmodule :=
    FiniteDimensional.of_injective W.toSubmodule.subtype Subtype.val_injective
  have hsigmaNonprincipal :
      ¬ Nonempty (sigma ≃ₗ Representation.trivial ℂ NK ℂ) := by
    rintro ⟨f⟩
    apply hWnonprincipal
    refine ⟨Theory.Representation.RepEquiv.mk f.toLinearEquiv ?_⟩
    intro x
    ext w
    have htemp := f.isIntertwining (eQK x) w
    have htemp_simp : f (W.toRepresentation (eQK.symm (eQK x)) w) = f w := by
      calc
        f (W.toRepresentation (eQK.symm (eQK x)) w) = f (sigma (eQK x) w) := by
          dsimp [sigma]; rfl
        _ = ((Representation.trivial ℂ NK ℂ) (eQK x)) (f w) := htemp
        _ = f w := by simp
    have h_eq_rep : W.toRepresentation (eQK.symm (eQK x)) = W.toRepresentation x :=
      congrArg W.toRepresentation (MulEquiv.symm_apply_apply eQK x)
    have htemp' : f (W.toRepresentation x w) = f w := by
      calc
        f (W.toRepresentation x w) = f (W.toRepresentation (eQK.symm (eQK x)) w) := by
          rw [← h_eq_rep]
        _ = f w := htemp_simp
    simpa using htemp'
  let eK : K := ⟨(e : d.H), show (e : d.H) ∈ d.Q1 ⊔ d.D from
    (show d.D ≤ d.Q1 ⊔ d.D from le_sup_right) e.property⟩
  have hsigmaChar : sigma.character =
      (Theory.Representation.conjugateRep (G := K) (H := NK) sigma eK).character := by
    funext x
    let xQ : NQ := eQK.symm x
    let exK : NK := ⟨eK * (x : K) * eK⁻¹,
      (inferInstance : NK.Normal).conj_mem (x : K) x.property eK⟩
    let exQ : NQ := eQK.symm exK
    have hRho :
        rhoN.character exQ =
          rhoN.character xQ := by
      have hx := congrFun he (xQ : d.Q)
      have hx_exp : rho.character (show d.Q from
          ⟨(e : d.H) * (((xQ : NQ) : d.Q) : d.H) * (e : d.H)⁻¹,
            d.Q_normal.conj_mem ((xQ : NQ) : d.Q) (Subtype.mem _) (e : d.H)⟩) =
          rho.character ((xQ : NQ) : d.Q) := by
        simpa [conjugateOnNormal] using hx
      have h_eq : ((exQ : NQ) : d.Q) = (show d.Q from
          ⟨(e : d.H) * (((xQ : NQ) : d.Q) : d.H) * (e : d.H)⁻¹,
            d.Q_normal.conj_mem ((xQ : NQ) : d.Q) (Subtype.mem _) (e : d.H)⟩) := by
        apply Subtype.ext
        simp [exQ, exK, xQ, eQK, eNQ, eNK, eK, NK, NQ, K]
      rw [← h_eq] at hx_exp
      -- hx_exp: rho.character ((exQ : NQ) : d.Q) = rho.character ((xQ : NQ) : d.Q)
      have h_char (z : NQ) : rhoN.character z = rho.character ((z : NQ) : d.Q) := by
        dsimp [rhoN, NQ]; rfl
      calc
        rhoN.character exQ = rho.character ((exQ : NQ) : d.Q) := h_char exQ
        _ = rho.character ((xQ : NQ) : d.Q) := hx_exp
        _ = rhoN.character xQ := (h_char xQ).symm
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    have hWchar : W.toRepresentation.character exQ =
        W.toRepresentation.character xQ := by
      apply mul_left_cancel₀ hmC
      calc
        (m : ℂ) * W.toRepresentation.character exQ =
            rhoN.character exQ := by
          exact (congrFun hhom exQ).symm
        _ = rhoN.character xQ := hRho
        _ = (m : ℂ) * W.toRepresentation.character xQ := by
          exact congrFun hhom xQ
    change W.toRepresentation.character xQ =
      W.toRepresentation.character exQ
    exact hWchar.symm
  letI : Representation.IsIrreducible
      (Theory.Representation.conjugateRep (G := K) (H := NK) sigma eK) :=
    conjugateRep_irreducible (G := K) (H := NK) (ρ := sigma) eK
  have hsigmaEquiv : Nonempty (sigma ≃ₗ
      Theory.Representation.conjugateRep (G := K) (H := NK) sigma eK) := by
    exact Theory.Character.repEquiv_of_irreducible_char_eq
      (F := ℂ) (G := NK) (ρ :=
        Theory.Representation.conjugateRep (G := K) (H := NK) sigma eK)
      (σ := sigma) (by
        rw [show ringChar ℂ = 0 from ringChar.eq_zero, zero_dvd_iff]
        exact Nat.ne_of_gt Nat.card_pos) hsigmaChar.symm
  have hcentral := d.Q1D_centralizer hDne
  have hInertia :=
    ((Theory.Representation.isaacs_theorem_6_34.{u, v, v, v} NK hcentral).1
      sigma hsigmaIrr hsigmaNonprincipal).1
  have heKN : eK ∈ NK := (hInertia eK).mp hsigmaEquiv
  have heQ1 : (e : d.H) ∈ d.Q1 := heKN
  have heQ : (e : d.H) ∈ d.Q := d.Q1_le_Q heQ1
  have heBot : (e : d.H) ∈ (⊥ : Subgroup d.H) :=
    (Subgroup.disjoint_def.mp d.Q_disjoint_D) heQ e.property
  apply Subtype.ext
  simpa using heBot
set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem lemma_2_inertia_eq_Q_nontrivial_complement_core
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) [d.Q.Normal]
    (hDne : d.D ≠ ⊥)
    {n : ℕ} (rho : Representation ℂ d.Q (Fin n → ℂ))
    (hrho : Representation.IsIrreducible rho)
    (hnotker : ¬ subgroupInKernel' rho.character (d.Q1.subgroupOf d.Q)) :
    inertiaSubgroup d.Q rho.character = d.Q := by
  classical
  letI : d.Q.Normal := d.Q_normal
  letI : (d.Q1.subgroupOf d.Q).Normal := d.Q1_normal_in_Q
  let rhoN : Representation ℂ (d.Q1.subgroupOf d.Q) (Fin n → ℂ) :=
    rho.comp (d.Q1.subgroupOf d.Q).subtype
  have hQ1notker :
      ¬ subgroupInRepresentationKernel rho (d.Q1.subgroupOf d.Q) := by
    intro hker
    apply hnotker
    have hcharKer :
        subgroupInKernel' rho.character (d.Q1.subgroupOf d.Q) :=
      (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
        rho (d.Q1.subgroupOf d.Q)).mpr hker
    exact hcharKer
  let moduleRhoNV : Module (MonoidAlgebra ℂ (d.Q1.subgroupOf d.Q))
      (Fin n → ℂ) :=
    Module.compHom (Fin n → ℂ) (Representation.asAlgebraHom rhoN).toRingHom
  have moduleRhoN : Module (MonoidAlgebra ℂ (d.Q1.subgroupOf d.Q))
      rhoN.asModule := by
    simpa [rhoN, Representation.asModule] using moduleRhoNV
  letI : Module (MonoidAlgebra ℂ (d.Q1.subgroupOf d.Q)) rhoN.asModule :=
    moduleRhoN
  have hcr : rhoN.IsCompletelyReducible :=
    Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
      (ρ := rhoN) (Or.inl ringChar.eq_zero)
  have htop : ¬ (⊤ : Subgroup (d.Q1.subgroupOf d.Q)) ≤ rhoN.ker := by
    intro htopKer
    apply hQ1notker
    intro a
    have ha := htopKer (show (a : d.Q1.subgroupOf d.Q) ∈
      (⊤ : Subgroup (d.Q1.subgroupOf d.Q)) by trivial)
    rw [MonoidHom.mem_ker] at ha
    simpa [rhoN] using ha
  obtain ⟨mW, hmWSimple, hmWNontrivial⟩ :=
    @exists_simple_submodule_not_le_ker_of_semisimple
      (d.Q1.subgroupOf d.Q) inferInstance ℂ inferInstance (Fin n → ℂ)
      inferInstance inferInstance rhoN hcr
      (⊤ : Subgroup (d.Q1.subgroupOf d.Q)) htop
  let W : Subrepresentation rhoN := Subrepresentation.ofSubmodule' mW
  have hWirr : Representation.IsIrreducible W.toRepresentation :=
    irreducible_subrepresentation_of_simple_asModuleSubmodule rhoN hmWSimple
  letI : Representation.IsIrreducible W.toRepresentation := hWirr
  letI : FiniteDimensional ℂ W.toSubmodule :=
    FiniteDimensional.of_injective W.toSubmodule.subtype Subtype.val_injective
  have hWnonprincipal :
      ¬ Nonempty (W.toRepresentation ≃ₗ
        Representation.trivial ℂ (d.Q1.subgroupOf d.Q) ℂ) := by
    rintro ⟨f⟩
    apply hmWNontrivial
    intro a _ha
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro w
    have hw : W.toRepresentation a w = w :=
      f.injective (by simpa using f.isIntertwining a w)
    apply Subtype.ext
    exact congrArg Subtype.val hw
  rcases lemma_2_Q1_restriction_homogeneous d rho hrho W hWirr with
    ⟨m, hm, hhom⟩
  have hclass : IsClassFunction rho.character := by
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := rho) g x
  have hQleI : d.Q ≤ inertiaSubgroup d.Q rho.character := by
    intro q hq
    change conjugateOnNormal d.Q rho.character q = rho.character
    funext x
    exact hclass ⟨q, hq⟩ x
  have hIleQ : inertiaSubgroup d.Q rho.character ≤ d.Q := by
    intro x hx
    rcases d.exists_Q_mul_D x with ⟨q, e, hqe⟩
    have hqI : (q : d.H) ∈ inertiaSubgroup d.Q rho.character :=
      hQleI q.property
    have heI : (e : d.H) ∈ inertiaSubgroup d.Q rho.character := by
      have hmul := (inertiaSubgroup d.Q rho.character).mul_mem
        ((inertiaSubgroup d.Q rho.character).inv_mem hqI) hx
      rw [← hqe] at hmul
      simpa [mul_assoc] using hmul
    have heOne : e = 1 :=
      lemma_2_D_eq_one_of_mem_inertia d hDne rho W hWirr
        hWnonprincipal hm hhom e heI
    have heOneH : (e : d.H) = 1 := congrArg Subtype.val heOne
    rw [← hqe, heOneH]
    simp
  exact le_antisymm hIleQ hQleI

private theorem lemma_2_inertia_eq_Q
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) [d.Q.Normal]
    {n : ℕ} (rho : Representation ℂ d.Q (Fin n → ℂ))
    (hrho : Representation.IsIrreducible rho)
    (hnotker : ¬ subgroupInKernel' rho.character (d.Q1.subgroupOf d.Q)) :
    inertiaSubgroup d.Q rho.character = d.Q := by
  letI : d.Q.Normal := d.Q_normal
  have hclass : IsClassFunction rho.character := by
    intro x g
    simpa [mul_assoc] using Representation.char_conj (ρ := rho) g x
  by_cases hD : d.D = ⊥
  · have hQtop : d.Q = ⊤ := by
      simpa [hD] using d.H_eq_Q_sup_D
    apply le_antisymm
    · intro x _hx
      rw [hQtop]
      trivial
    · intro q hq
      change conjugateOnNormal d.Q rho.character q = rho.character
      funext x
      exact hclass ⟨q, hq⟩ x
  · exact lemma_2_inertia_eq_Q_nontrivial_complement_core
      d hD rho hrho hnotker

private theorem lemma_2_induced_irreducible_nontrivial_complement_core
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (hDne : d.D ≠ ⊥)
    {phi : ClassFunction d.Q}
    (hphi : IsIrreducibleCharacterOnGroup phi)
    (hnotker : ¬ subgroupInKernel' phi (d.Q1.subgroupOf d.Q)) :
    IsIrreducibleCharacterOnGroup (inducedCF d.Q phi) := by
  letI : d.Q.Normal := d.Q_normal
  rcases hphi with ⟨n, rho, hrho, hphieq⟩
  have hnotker' :
      ¬ subgroupInKernel' rho.character (d.Q1.subgroupOf d.Q) := by
    simpa [hphieq] using hnotker
  have hIeq : inertiaSubgroup d.Q rho.character = d.Q :=
    lemma_2_inertia_eq_Q_nontrivial_complement_core
      d hDne rho hrho hnotker'
  have hrel : d.Q.relIndex (inertiaSubgroup d.Q rho.character) = 1 :=
    (Subgroup.relIndex_eq_one).2 (by rw [hIeq])
  simpa [hphieq] using
    proposition_1_5_b_irreducible_rep_orbit_relIndex_canonical
      d.Q rho hrho hrel

private theorem lemma_2_induced_irreducible_source_core
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    {phi : ClassFunction d.Q}
    (hphi : IsIrreducibleCharacterOnGroup phi)
    (hnotker : ¬ subgroupInKernel' phi (d.Q1.subgroupOf d.Q)) :
    IsIrreducibleCharacterOnGroup (inducedCF d.Q phi) := by
  letI : d.Q.Normal := d.Q_normal
  by_cases hD : d.D = ⊥
  · have hQtop : d.Q = ⊤ := by
      simpa [hD] using d.H_eq_Q_sup_D
    exact inducedCF_irreducible_of_subgroup_eq_top_appendixIV
      d.Q hQtop hphi
  · exact lemma_2_induced_irreducible_nontrivial_complement_core
      d hD hphi hnotker

private theorem lemma_2_induced_irreducible_core
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    {phi : ClassFunction d.Q}
    (hphi : IsIrreducibleCharacterOnGroup phi)
    (hnotker : ¬ subgroupInKernel' phi (d.Q1.subgroupOf d.Q)) :
    IsIrreducibleCharacterOnGroup (inducedCF d.Q phi) ∧
      ¬ subgroupInKernel' (inducedCF d.Q phi) d.Q1 := by
  letI : d.Q.Normal := d.Q_normal
  letI : d.Q1.Normal := d.Q1_normal
  constructor
  · exact lemma_2_induced_irreducible_source_core d hphi hnotker
  · intro hindker
    apply hnotker
    rcases hphi with ⟨n, rho, _hrhoirr, hphieq⟩
    have hindker' :
        subgroupInKernel' (inducedCF d.Q rho.character) d.Q1 := by
      simpa [hphieq] using hindker
    have hrhoker :
        subgroupInKernel' rho.character (d.Q1.subgroupOf d.Q) :=
      (Section1.proposition_1_6_a d.Q d.Q1 d.Q1_le_Q rho).mpr hindker'
    simpa [hphieq] using hrhoker
/-- Source core for Lemma 2(a): the exceptional characters are exactly the
irreducible characters induced from `Q`. -/
private theorem lemma_2_a_source_core
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars) :
    ∀ chi : ClassFunction d.H,
      chi ∈ chars ↔
        ∃ phi : ClassFunction d.Q,
          IsIrreducibleCharacterOnGroup phi ∧
            ¬ subgroupInKernel' phi (d.Q1.subgroupOf d.Q) ∧
            inducedCF d.Q phi = chi := by
  letI : d.Q.Normal := d.Q_normal
  letI : d.Q1.Normal := d.Q1_normal
  intro chi
  rw [hchars chi]
  constructor
  · rintro ⟨hchi, hchinotker⟩
    rcases exists_irreducible_constituent_of_subgroupRestriction_appendixIV
        d.Q hchi with ⟨phi, hphi, hinner⟩
    have hphinotker :
        ¬ subgroupInKernel' phi (d.Q1.subgroupOf d.Q) :=
      constituent_not_subgroupInKernel'_of_subgroupRestriction_not_kernel_appendixIV
        d.Q d.Q1 d.Q1_le_Q hchi hchinotker hphi hinner
    have hind := lemma_2_induced_irreducible_core d hphi hphinotker
    have heq : chi = inducedCF d.Q phi :=
      inducedCF_eq_of_irreducible_constituent_appendixIV
        d.Q hchi hind.1 hinner
    exact ⟨phi, hphi, hphinotker, heq.symm⟩
  · rintro ⟨phi, hphi, hphinotker, rfl⟩
    exact lemma_2_induced_irreducible_core d hphi hphinotker
/-- Peterfalvi Appendix IV, Lemma 2(a). -/
public theorem lemma_2_a
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars) :
    ∀ chi : ClassFunction d.H,
      chi ∈ chars ↔
        ∃ phi : ClassFunction d.Q,
          IsIrreducibleCharacterOnGroup phi ∧
            ¬ subgroupInKernel' phi (d.Q1.subgroupOf d.Q) ∧
            inducedCF d.Q phi = chi := by
  exact lemma_2_a_source_core d chars hchars


private theorem lemma_2_b_TI {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) :
    ∀ g : G,
      ((fun x : G => g * x * g⁻¹) '' (d.QInG : Set G) = d.QInG) ∨
        (((fun x : G => g * x * g⁻¹) '' (d.QInG : Set G)) ∩ d.QInG ⊆
          ({1} : Set G)) := by
  intro g
  by_cases hgH : g ∈ d.H
  · left
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      rcases hx with ⟨q, hq, rfl⟩
      let gh : d.H := ⟨g, hgH⟩
      refine ⟨gh * q * gh⁻¹, d.Q_normal.conj_mem q hq gh, ?_⟩
      rfl
    · intro hy
      rcases hy with ⟨q, hq, rfl⟩
      let gh : d.H := ⟨g, hgH⟩
      let q' : d.Q := ⟨gh⁻¹ * q * gh, by simpa using d.Q_normal.conj_mem q hq gh⁻¹⟩
      refine ⟨d.H.subtype q', ⟨q', q'.property, rfl⟩, ?_⟩
      dsimp [q', gh]
      group
  · right
    intro y hy
    rcases hy with ⟨⟨x, hx, rfl⟩, hyQ⟩
    have hgInv : g⁻¹ ∉ d.H := by
      intro hgInv
      exact hgH (by simpa using d.H.inv_mem hgInv)
    have hdis := d.Q_TI_in_G g⁻¹ hgInv
    have hyConj : g * x * g⁻¹ ∈ rightConjugate d.QInG g⁻¹ := by
      change g * x * g⁻¹ ∈ d.QInG.conjBy (g⁻¹)⁻¹
      exact Subgroup.mem_map.mpr ⟨x, hx, by simp⟩
    have hyBot : g * x * g⁻¹ ∈ (⊥ : Subgroup G) :=
      hdis.le_bot ⟨hyQ, hyConj⟩
    simpa using hyBot

private theorem lemma_2_b_normalizer_eq_H {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) :
    Subgroup.normalizer (d.QInG : Set G) = d.H := by
  have hQ_ne : d.QInG ≠ ⊥ := by
    have hQ1_ne : d.Q1 ≠ ⊥ := by
      intro hQ1
      apply d.Q1_not_two_group
      exact hQ1.symm ▸ (IsPGroup.of_bot (p := 2) (G := d.H))
    have hQ_ne' : d.Q ≠ ⊥ := by
      intro hQ
      apply hQ1_ne
      apply le_bot_iff.mp
      simpa [hQ] using d.Q1_le_Q
    exact (Subgroup.map_eq_bot_iff_of_injective
      (H := d.Q) (f := d.H.subtype) d.H.subtype_injective).not.mpr hQ_ne'
  apply le_antisymm
  · intro g hgNorm
    by_contra hgH
    have hgInv : g⁻¹ ∉ d.H := by
      intro hgInv
      exact hgH (by simpa using d.H.inv_mem hgInv)
    have hdis := d.Q_TI_in_G g⁻¹ hgInv
    have hnotle : ¬ d.QInG ≤ (⊥ : Subgroup G) := by
      intro hle
      exact hQ_ne (le_bot_iff.mp hle)
    rcases SetLike.not_le_iff_exists.mp hnotle with ⟨q, hqQ, hqBot⟩
    have hqNe : q ≠ 1 := by simpa using hqBot
    have hconjQ : g * q * g⁻¹ ∈ d.QInG :=
      (Subgroup.mem_normalizer_iff.mp hgNorm q).1 hqQ
    have hconjRight : g * q * g⁻¹ ∈ rightConjugate d.QInG g⁻¹ := by
      change g * q * g⁻¹ ∈ d.QInG.conjBy (g⁻¹)⁻¹
      exact Subgroup.mem_map.mpr ⟨q, hqQ, by simp⟩
    have hconjBot : g * q * g⁻¹ ∈ (⊥ : Subgroup G) :=
      hdis.le_bot ⟨hconjQ, hconjRight⟩
    have hconjOne : g * q * g⁻¹ = 1 := by simpa using hconjBot
    apply hqNe
    calc
      q = g⁻¹ * (g * q * g⁻¹) * g := by group
      _ = 1 := by rw [hconjOne]; simp
  · intro g hgH
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rcases hx with ⟨q, hq, rfl⟩
      let gh : d.H := ⟨g, hgH⟩
      exact ⟨gh * q * gh⁻¹, d.Q_normal.conj_mem q hq gh, rfl⟩
    · intro hx
      rcases hx with ⟨q, hq, hqx⟩
      let gh : d.H := ⟨g, hgH⟩
      have hback : gh⁻¹ * q * gh ∈ d.Q := by
        simpa using d.Q_normal.conj_mem q hq gh⁻¹
      refine Subgroup.mem_map.mpr ⟨(gh⁻¹ * (q : d.H) * gh : d.H), hback, ?_⟩
      change g⁻¹ * (q : G) * g = x
      have := congrArg (fun z : G => g⁻¹ * z * g) hqx
      simpa [mul_assoc] using this

private theorem lemma_2_b_integerSpan_isClassFunction
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    {theta : ClassFunction d.H}
    (htheta : integerSpan chars theta) :
    IsClassFunction theta := by
  classical
  rcases htheta with ⟨v, rfl⟩
  unfold Section1.evalCoeff
  intro x g
  have hterm : ∀ chi : chars,
      (v chi : ℂ) * (chi : ClassFunction d.H) (x * g * x⁻¹) =
        (v chi : ℂ) * (chi : ClassFunction d.H) g := by
    intro chi
    rw [Section1.isCharacter_isClassFunction (chi : ClassFunction d.H)
      (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
        ((hchars (chi : ClassFunction d.H)).mp chi.property).1) x g]
  simpa using Finset.sum_congr rfl (fun chi _ => hterm chi)

private theorem lemma_2_b_char_vanish_outside_Q
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    {chi : ClassFunction d.H} (hchi : chi ∈ chars)
    {x : d.H} (hx : x ∉ d.Q) : chi x = 0 := by
  letI : d.Q.Normal := d.Q_normal
  rcases (lemma_2_a d chars hchars chi).mp hchi with
    ⟨phi, _hphi, _hnotker, hind⟩
  rw [← hind]
  simpa [Section1.inducedCF] using
    Section1.inducedClassFunction_eq_zero_of_not_mem_of_normal d.Q phi hx

private theorem lemma_2_b_vanish_outside_Q
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    {theta : ClassFunction d.H}
    (htheta : integerSpan chars theta)
    {x : d.H} (hx : x ∉ d.Q) : theta x = 0 := by
  classical
  rcases htheta with ⟨v, rfl⟩
  unfold Section1.evalCoeff
  have hzero : ∀ chi : chars, (chi : ClassFunction d.H) x = 0 := by
    intro chi
    exact lemma_2_b_char_vanish_outside_Q d chars hchars chi.property hx
  simp [hzero]

private theorem lemma_2_b_virtualCharacter_zsmul
    {X : Type u} [Group X]
    (z : ℤ) {chi : ClassFunction X}
    (hchi : Theory.Character.IsVirtualCharacter chi) :
    Theory.Character.IsVirtualCharacter ((z : ℂ) • chi) := by
  classical
  rcases hchi with ⟨r, m, k, rho, rfl⟩
  refine ⟨r, fun i => z * m i, k, rho, ?_⟩
  ext x
  simp [Theory.Character.virtualCharacterOfRepresentations, Finset.mul_sum, mul_assoc]

private theorem lemma_2_b_virtualCharacter_finset_sum
    {X : Type u} [Group X]
    {iota : Type*} (s : Finset iota) (Phi : iota → ClassFunction X)
    (hPhi : ∀ i ∈ s, Theory.Character.IsVirtualCharacter (Phi i)) :
    Theory.Character.IsVirtualCharacter (s.sum Phi) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
      refine ⟨0, (fun i => nomatch i), (fun i => nomatch i),
        (fun i => nomatch i), ?_⟩
      ext x
      simp [Theory.Character.virtualCharacterOfRepresentations]
  | @insert a s ha ih =>
      have ha' := hPhi a (Finset.mem_insert_self a s)
      have hs' := ih (fun i hi => hPhi i (Finset.mem_insert_of_mem hi))
      simpa [Finset.sum_insert ha] using Section3.isVirtualCharacter_add ha' hs'

private theorem lemma_2_b_integerSpan_virtualCharacter
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    {theta : ClassFunction d.H}
    (htheta : integerSpan chars theta) :
    Theory.Character.IsVirtualCharacter theta := by
  classical
  rcases htheta with ⟨v, rfl⟩
  rw [Section1.evalCoeff]
  apply lemma_2_b_virtualCharacter_finset_sum (Finset.univ : Finset chars)
  intro chi _hchi
  apply lemma_2_b_virtualCharacter_zsmul
  exact Section5.isVirtualCharacter_of_isCharacter
    (Section1.isCharacter_of_isIrreducibleCharacterOnGroup
      ((hchars (chi : ClassFunction d.H)).mp chi.property).1)

private theorem lemma_2_b_mem_QInG_iff
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G) (x : d.H) :
    (x : G) ∈ d.QInG ↔ x ∈ d.Q := by
  constructor
  · rintro ⟨q, hq, hqx⟩
    have hqxeq : q = x := d.H.subtype_injective hqx
    simpa [hqxeq] using hq
  · intro hx
    exact ⟨x, hx, rfl⟩

private theorem lemma_2_b_isaacs_7_7_lattice
    {G : Type u} [Group G] [Finite G]
    {X : Set G} {H : Subgroup G}
    (hnorm : Subgroup.normalizer X = H)
    (hTI : ∀ g : G,
      ((fun x : G => g * x * g⁻¹) '' X = X) ∨
        (((fun x : G => g * x * g⁻¹) '' X) ∩ X ⊆ ({1} : Set G)))
    {theta phi : ClassFunction H}
    (hphiClass : IsClassFunction phi)
    (hthetaClass : IsClassFunction theta)
    (hphiVanish : ∀ n : H, (n : G) ∉ X → phi n = 0)
    (hthetaVanish : ∀ n : H, (n : G) ∉ X → theta n = 0)
    (hthetaOne : theta 1 = 0) :
    scalarProduct G (inducedCF H theta) (inducedCF H phi) =
      scalarProduct H theta phi := by
  subst H
  exact (External.Isaacs.VII.isaacs_lemma_7_7 hTI
    hphiClass hthetaClass hphiVanish hthetaVanish hthetaOne).2

/-- Peterfalvi Appendix IV, Lemma 2(b). -/
public theorem lemma_2_b
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars) :
    isCFLinearIsometryOnSpanOn chars puncturedSet
        (inducedCFLinear d.H) ∧
      ∀ theta : ClassFunction d.H,
        integerSpanOn chars puncturedSet theta →
          Theory.Character.IsVirtualCharacter (inducedCF d.H theta) ∧
            supportedOn (inducedCF d.H theta) puncturedSet := by
  have hTI := lemma_2_b_TI d
  have hnorm := lemma_2_b_normalizer_eq_H d
  constructor
  · intro theta phi htheta hphi
    apply lemma_2_b_isaacs_7_7_lattice hnorm hTI
      (lemma_2_b_integerSpan_isClassFunction d chars hchars hphi.1)
      (lemma_2_b_integerSpan_isClassFunction d chars hchars htheta.1)
    · intro n hn
      apply lemma_2_b_vanish_outside_Q d chars hchars hphi.1
      intro hnQ
      exact hn ((lemma_2_b_mem_QInG_iff d n).2 hnQ)
    · intro n hn
      apply lemma_2_b_vanish_outside_Q d chars hchars htheta.1
      intro hnQ
      exact hn ((lemma_2_b_mem_QInG_iff d n).2 hnQ)
    · exact (supportedOn_puncturedSet_iff_degree_eq_zero theta).mp htheta.2
  · intro theta htheta
    constructor
    · apply Section2.inducedCF_isVirtualCharacter_of_virtualCharacter
      exact lemma_2_b_integerSpan_virtualCharacter d chars hchars htheta.1
    · apply (supportedOn_puncturedSet_iff_degree_eq_zero _).2
      rw [Section1.degree_inducedClassFunction,
        (supportedOn_puncturedSet_iff_degree_eq_zero theta).mp htheta.2]
      simp

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem lemma_2_c_character_self_of_induced_self
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (hDodd : Odd (Nat.card d.D))
    {n : ℕ} (rho : Representation ℂ d.Q (Fin n → ℂ))
    (hrho : Representation.IsIrreducible rho)
    (hnotker : ¬ subgroupInKernel' rho.character (d.Q1.subgroupOf d.Q))
    (hself : conjugateCharacter (inducedCF d.Q rho.character) =
      inducedCF d.Q rho.character) :
    rho.character = conjugateCharacter rho.character := by
  classical
  letI : d.Q.Normal := d.Q_normal
  have hdualIrr : Representation.IsIrreducible rho.dual :=
    representation_dual_irreducible_of rho hrho
  have hInd : inducedCF d.Q rho.dual.character =
      inducedCF d.Q rho.character := by
    calc
      inducedCF d.Q rho.dual.character =
          inducedCF d.Q (conjugateCharacter rho.character) := by
        rw [conjugateCharacter_representationCharacter_eq_dual]
      _ = conjugateCharacter (inducedCF d.Q rho.character) :=
        (conjugateCharacter_inducedCF d.Q rho.character).symm
      _ = inducedCF d.Q rho.character := hself
  rcases proposition_1_5_c_induced_eq_imp_conjugate_orbit_canonical
      d.Q rho.dual rho hdualIrr hrho hInd with ⟨i, hi⟩
  obtain ⟨g, hg⟩ : ∃ g : d.H,
      rho.dual.character = conjugateOnNormal d.Q rho.character g := by
    revert hi
    refine Quotient.inductionOn i ?_
    intro g hi
    exact ⟨g, hi⟩
  have hbar : conjugateOnNormal d.Q rho.character g =
      conjugateCharacter rho.character := by
    calc
      conjugateOnNormal d.Q rho.character g = rho.dual.character := hg.symm
      _ = conjugateCharacter rho.character :=
        (conjugateCharacter_representationCharacter_eq_dual rho).symm
  have hconjMul (theta : ClassFunction d.Q) (a b : d.H) :
      conjugateOnNormal d.Q theta (a * b) =
        conjugateOnNormal d.Q (conjugateOnNormal d.Q theta a) b := by
    funext x
    simp [conjugateOnNormal, mul_assoc]
  have hconjBar (theta : ClassFunction d.Q) (a : d.H) :
      conjugateOnNormal d.Q (conjugateCharacter theta) a =
        conjugateCharacter (conjugateOnNormal d.Q theta a) := by
    funext x
    rfl
  have hg2fix : conjugateOnNormal d.Q rho.character (g * g) =
      rho.character := by
    calc
      conjugateOnNormal d.Q rho.character (g * g) =
          conjugateOnNormal d.Q
            (conjugateOnNormal d.Q rho.character g) g :=
        hconjMul rho.character g g
      _ = conjugateOnNormal d.Q (conjugateCharacter rho.character) g := by
        rw [hbar]
      _ = conjugateCharacter (conjugateOnNormal d.Q rho.character g) :=
        hconjBar rho.character g
      _ = conjugateCharacter (conjugateCharacter rho.character) := by
        rw [hbar]
      _ = rho.character := by
        funext x
        simp [conjugateCharacter]
  have hg2I : g * g ∈ inertiaSubgroup d.Q rho.character :=
    hg2fix
  have hIeq : inertiaSubgroup d.Q rho.character = d.Q :=
    lemma_2_inertia_eq_Q d rho hrho hnotker
  have hg2Q : g * g ∈ d.Q := by
    rw [← hIeq]
    exact hg2I
  rcases d.exists_Q_mul_D g with ⟨q, e, hqe⟩
  have heqeQ : (e : d.H) * (q : d.H) * (e : d.H)⁻¹ ∈ d.Q :=
    d.Q_normal.conj_mem (q : d.H) q.property (e : d.H)
  have hleftQ :
      (q : d.H) * ((e : d.H) * (q : d.H) * (e : d.H)⁻¹) ∈ d.Q :=
    d.Q.mul_mem q.property heqeQ
  have hcancelQ :
      ((q : d.H) * ((e : d.H) * (q : d.H) * (e : d.H)⁻¹))⁻¹ *
          (g * g) ∈ d.Q :=
    d.Q.mul_mem (d.Q.inv_mem hleftQ) hg2Q
  have he2Q : (e : d.H) * (e : d.H) ∈ d.Q := by
    convert hcancelQ using 1
    rw [← hqe]
    group
  have he2D : (e : d.H) * (e : d.H) ∈ d.D :=
    d.D.mul_mem e.property e.property
  have he2Bot : (e : d.H) * (e : d.H) ∈ (⊥ : Subgroup d.H) :=
    (Subgroup.disjoint_def.mp d.Q_disjoint_D) he2Q he2D
  have he2OneH : (e : d.H) * (e : d.H) = 1 := by
    simpa using he2Bot
  have he2One : e * e = 1 := by
    apply Subtype.ext
    exact he2OneH
  have hsquareRoot : ∃ k : ℕ, (e * e) ^ k = e := by
    have hoddOrder : Odd (orderOf e) :=
      Odd.of_dvd_nat hDodd (orderOf_dvd_natCard e)
    rcases hoddOrder with ⟨m, hm⟩
    use m + 1
    calc
      (e * e) ^ (m + 1) = e ^ (2 * (m + 1)) := by
        rw [show e * e = e ^ 2 by simp [pow_succ]]
        rw [← pow_mul]
      _ = e ^ (orderOf e + 1) := by
        congr 1
        omega
      _ = e := by
        rw [pow_add, pow_orderOf_eq_one]
        simp
  rcases hsquareRoot with ⟨k, hk⟩
  have heOne : e = 1 := by
    simpa [he2One] using hk.symm
  have heOneH : (e : d.H) = 1 := congrArg Subtype.val heOne
  have hgQ : g ∈ d.Q := by
    rw [← hqe, heOneH]
    simp
  have hclass : IsClassFunction rho.character := by
    intro x y
    simpa [mul_assoc] using Representation.char_conj (ρ := rho) y x
  have hfix : conjugateOnNormal d.Q rho.character g = rho.character := by
    funext x
    exact hclass ⟨g, hgQ⟩ x
  exact hfix.symm.trans hbar

set_option maxHeartbeats 800000 in
set_option backward.isDefEq.respectTransparency false in
private theorem lemma_2_c_Q1_constituent_nonselfconjugate
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    {n : ℕ} (rho : Representation ℂ d.Q (Fin n → ℂ))
    (hrho : Representation.IsIrreducible rho)
    (hnotker : ¬ subgroupInKernel' rho.character (d.Q1.subgroupOf d.Q)) :
    rho.character ≠ conjugateCharacter rho.character := by
  classical
  intro hself
  letI : (d.Q1.subgroupOf d.Q).Normal := d.Q1_normal_in_Q
  let NQ : Subgroup d.Q := d.Q1.subgroupOf d.Q
  let rhoN : Representation ℂ NQ (Fin n → ℂ) := rho.comp NQ.subtype
  have hQ1notker : ¬ subgroupInRepresentationKernel rho NQ := by
    intro hker
    apply hnotker
    exact (subgroupInKernel'_character_iff_subgroupInRepresentationKernel
      rho NQ).mpr hker
  letI : Module (MonoidAlgebra ℂ NQ) rhoN.asModule :=
    Representation.instModuleMonoidAlgebraAsModule rhoN
  have hcr : rhoN.IsCompletelyReducible :=
    Representation.isCompletelyReducible_of_ringChar_eq_zero_or_prime_coprime
      (ρ := rhoN) (Or.inl ringChar.eq_zero)
  have htop : ¬ (⊤ : Subgroup NQ) ≤ rhoN.ker := by
    intro htopKer
    apply hQ1notker
    intro a
    have ha := htopKer (show a ∈ (⊤ : Subgroup NQ) by trivial)
    rw [MonoidHom.mem_ker] at ha
    simpa [rhoN] using ha
  obtain ⟨mW, hmWSimple, hmWNontrivial⟩ :=
    @exists_simple_submodule_not_le_ker_of_semisimple
      NQ inferInstance ℂ inferInstance (Fin n → ℂ)
      inferInstance inferInstance rhoN hcr (⊤ : Subgroup NQ) htop
  let W : Subrepresentation rhoN := Subrepresentation.ofSubmodule' mW
  have hWirr : Representation.IsIrreducible W.toRepresentation :=
    irreducible_subrepresentation_of_simple_asModuleSubmodule rhoN hmWSimple
  letI : Representation.IsIrreducible W.toRepresentation := hWirr
  letI : FiniteDimensional ℂ W.toSubmodule :=
    FiniteDimensional.of_injective W.toSubmodule.subtype Subtype.val_injective
  have hWnonprincipal :
      ¬ Nonempty (W.toRepresentation ≃ₗ Representation.trivial ℂ NQ ℂ) := by
    rintro ⟨f⟩
    apply hmWNontrivial
    intro a _ha
    rw [MonoidHom.mem_ker]
    apply LinearMap.ext
    intro w
    have hw : W.toRepresentation a w = w :=
      f.injective (by simpa using f.isIntertwining a w)
    apply Subtype.ext
    exact congrArg Subtype.val hw
  rcases lemma_2_Q1_restriction_homogeneous d rho hrho W hWirr with
    ⟨m, hm, hhom⟩
  have hrhoNSelf : rhoN.character = conjugateCharacter rhoN.character := by
    funext x
    have hx := congrFun hself (x : d.Q)
    dsimp [rhoN, NQ, conjugateCharacter, Representation.character] at *
    simpa using hx
  have hscaledSelf : (m : ℂ) • W.toRepresentation.character =
      conjugateCharacter ((m : ℂ) • W.toRepresentation.character) := by
    simpa [rhoN, NQ, hhom] using hrhoNSelf
  have hWself : W.toRepresentation.character =
      conjugateCharacter W.toRepresentation.character := by
    funext x
    have hx := congrFun hscaledSelf x
    have hmC : (m : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hm
    apply mul_left_cancel₀ hmC
    simpa [conjugateCharacter] using hx
  have hWcharNonprincipal :
      W.toRepresentation.character ≠ principalCharacter NQ := by
    intro hWchar
    apply hWnonprincipal
    have htrivialIrr : Representation.IsIrreducible
        (Representation.trivial ℂ NQ ℂ) :=
      Theory.Character.trivial_complex_irreducible
    have htrivialChar :
        (Representation.trivial ℂ NQ ℂ).character = principalCharacter NQ := by
      ext x
      simp [Representation.character, principalCharacter, Representation.isTrivial_def]
    exact Theory.Character.repEquiv_of_irreducible_char_eq
      (F := ℂ) (G := NQ)
      (ρ := Representation.trivial ℂ NQ ℂ) (σ := W.toRepresentation)
      (by
        rw [show ringChar ℂ = 0 from ringChar.eq_zero, zero_dvd_iff]
        exact Nat.ne_of_gt Nat.card_pos)
      (htrivialChar.trans hWchar.symm)
  have hNQodd : Odd (Nat.card NQ) := by
    have hcardNQ : Nat.card NQ = Nat.card d.Q1 := by
      simpa [NQ] using natCard_subgroupOf_eq d.Q1 d.Q d.Q1_le_Q
    rw [hcardNQ]
    exact d.Q1_odd
  exact (proposition_1_1 hNQodd W.toRepresentation hWirr
    hWcharNonprincipal) hWself

/-- Peterfalvi Appendix IV, Lemma 2(c), with the oddness needed by the printed
restriction-to-`Q₁D` argument made explicit in `FeitSibleyData`. -/
public theorem lemma_2_c
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars)
    (hDodd : Odd (Nat.card d.D)) :
    ∀ chi : ClassFunction d.H, chi ∈ chars →
      conjugateCharacter chi ≠ chi := by
  intro chi hchi hself
  rcases (lemma_2_a d chars hchars chi).mp hchi with
    ⟨phi, hphi, hnotker, hind⟩
  rcases hphi with ⟨n, rho, hrho, hphieq⟩
  have hnotker' :
      ¬ subgroupInKernel' rho.character (d.Q1.subgroupOf d.Q) := by
    simpa [hphieq] using hnotker
  have hind' : inducedCF d.Q rho.character = chi := by
    simpa [hphieq] using hind
  have hIndSelf : conjugateCharacter (inducedCF d.Q rho.character) =
      inducedCF d.Q rho.character := by
    rw [hind']
    exact hself
  have hphiSelf : rho.character = conjugateCharacter rho.character :=
    lemma_2_c_character_self_of_induced_self
      d hDodd rho hrho hnotker' hIndSelf
  exact (lemma_2_c_Q1_constituent_nonselfconjugate
    d rho hrho hnotker') hphiSelf

/-- Peterfalvi Appendix IV, Lemma 2, with its three printed parts. -/
public theorem lemma_2
    {G : Type u} [Group G] [Finite G]
    (d : FeitSibleyData G)
    (chars : Finset (ClassFunction d.H))
    (hchars : IsFeitSibleyExceptionalFamily d chars) :
    (∀ chi : ClassFunction d.H,
      chi ∈ chars ↔
        ∃ phi : ClassFunction d.Q,
          IsIrreducibleCharacterOnGroup phi ∧
            ¬ subgroupInKernel' phi (d.Q1.subgroupOf d.Q) ∧
            inducedCF d.Q phi = chi) ∧
    (isCFLinearIsometryOnSpanOn chars puncturedSet
        (inducedCFLinear d.H) ∧
      ∀ theta : ClassFunction d.H,
        integerSpanOn chars puncturedSet theta →
          Theory.Character.IsVirtualCharacter (inducedCF d.H theta) ∧
            supportedOn (inducedCF d.H theta) puncturedSet) ∧
    (Odd (Nat.card d.D) →
      ∀ chi : ClassFunction d.H, chi ∈ chars →
        conjugateCharacter chi ≠ chi) := by
  exact ⟨lemma_2_a d chars hchars, lemma_2_b d chars hchars,
    lemma_2_c d chars hchars⟩

end PFAppendixIV
end CFSG.BenderSuzuki



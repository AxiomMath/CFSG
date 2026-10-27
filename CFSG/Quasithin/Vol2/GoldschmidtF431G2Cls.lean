module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2UNorm
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ClsRoot
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2ClsChar2
public import CFSG.Quasithin.Vol2.GoldschmidtF431NFSpecial
public import CFSG.LocalAnalysis.QuasithinUnique.Defs
import Mathlib.FieldTheory.Finite.Basic
import Mathlib.Tactic.FieldSimp
public import CFSG.Sporadic.Schreier.J4SFrattini
public import CFSG.GroupTheory.PerfectResidualNodes
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.PGroupRankOneClassification
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionSquareFieldAction
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.L239PairsLieFrame
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Lemma115Reduce
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasic
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeListed
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeThree
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Lin2.Equivariance
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3Structure312
public import CFSG.Quasithin.Background.A3Structure318Red
public import CFSG.Quasithin.Background.A3Structure36A
public import CFSG.Quasithin.Background.A3Structure36BAction
public import CFSG.Quasithin.Background.A3Structure36BBase
public import CFSG.Quasithin.Background.A3Structure36BCase3Base
public import CFSG.Quasithin.Background.A3Structure36BCasesBase
public import CFSG.Quasithin.Background.A3Structure36BCommonBase
public import CFSG.Quasithin.Background.A3Structure36BFrattini
public import CFSG.Quasithin.Background.A3Structure36BHeisBase
public import CFSG.Quasithin.Background.A3Structure36BHomocyclic
public import CFSG.Quasithin.Background.A3Structure36BPrimeDataBase
public import CFSG.Quasithin.Background.A3Structure36BStarBase
public import CFSG.Quasithin.Background.A3Structure36Base
public import CFSG.Quasithin.Background.A3Structure38Part3
public import CFSG.Quasithin.Background.B1MoreElevenE
public import CFSG.Quasithin.Background.B1MoreNineG
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Quasithin.Background.B4ModelsIso
public import CFSG.Quasithin.Background.C2Basic
public import CFSG.Quasithin.Background.C2Inputs
public import CFSG.Quasithin.Background.E1
public import CFSG.Quasithin.Background.E1Sec4
public import CFSG.Quasithin.Background.E1Sec5
public import CFSG.Quasithin.Background.E1Sec8
public import CFSG.Quasithin.Background.E1Solv
public import CFSG.Quasithin.Background.E1Twelve
public import CFSG.Quasithin.Background.E3Cent
public import CFSG.Quasithin.Vol2.Ch1Local
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.PSL2Contragredient
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.ProjectiveSemilinear
public import CFSG.Walter.Defs
public import Certificates.Certificate8026Base

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.Cls

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.QuasithinUnique
  CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2

set_option linter.unusedSectionVars false

variable {K : Type} [Field K] [CharP K 2]

theorem isConj_z_xa {s : K} (hs : s ≠ 0) : IsConj (xc 1) (xa s) :=
  isConj_z_of_long (γ := ![1, 0]) (Or.inl rfl) hs

theorem isConj_z_xb {s : K} (hs : s ≠ 0) : IsConj (xc 1) (xb s) :=
  isConj_z_of_long (γ := ![1, 3]) (Or.inr (Or.inl rfl)) hs

theorem isConj_z_xc {s : K} (hs : s ≠ 0) : IsConj (xc 1) (xc s) :=
  isConj_z_of_long (γ := ![2, 3]) (Or.inr (Or.inr (Or.inl rfl))) hs

theorem isConj_t_xr {s : K} (hs : s ≠ 0) : IsConj (xv 1) (xr s) :=
  isConj_t_of_short (γ := ![0, 1]) (Or.inl rfl) hs

theorem isConj_t_xu {s : K} (hs : s ≠ 0) : IsConj (xv 1) (xu s) :=
  isConj_t_of_short (γ := ![1, 1]) (Or.inr (Or.inl rfl)) hs

theorem isConj_t_xv {s : K} (hs : s ≠ 0) : IsConj (xv 1) (xv s) :=
  isConj_t_of_short (γ := ![1, 2]) (Or.inr (Or.inr (Or.inl rfl))) hs

theorem isConj_nf_a (l : K) {α ρ μ ν β γ μ' ν' β' γ' : K} (hμ : μ' = μ + l * ρ)
    (hν : ν' = ν + l * ρ ^ 2) (hβ : β' = β + l * ρ ^ 3) (hγ : γ' = γ + l * β + l * ρ ^ 2 * μ) :
    IsConj (nf α ρ μ ν β γ) (nf α ρ μ' ν' β' γ') := by
  subst hμ hν hβ hγ
  refine isConj_iff.mpr ⟨xa l, ?_⟩
  rw [xa_inv, xa_eq_nf, nf_mul, nf_mul]
  exact nf_congr (by g2char2) (by g2char2) (by g2char2) (by g2char2) (by g2char2) (by g2char2)

theorem isConj_nf_r (l : K) {α ρ μ ν β γ μ' ν' β' γ' : K} (hμ : μ' = μ + α * l)
    (hν : ν' = ν + α * l ^ 2)
    (hβ : β' = β + α * l ^ 3 + α * l ^ 2 * ρ + α * l * ρ ^ 2 + l ^ 2 * μ + l * ν)
    (hγ : γ' = γ + α ^ 2 * l ^ 3 + α ^ 2 * l ^ 2 * ρ + α * l ^ 2 * μ + l * μ ^ 2) :
    IsConj (nf α ρ μ ν β γ) (nf α ρ μ' ν' β' γ') := by
  subst hμ hν hβ hγ
  refine isConj_iff.mpr ⟨xr l, ?_⟩
  rw [xr_inv, xr_eq_nf, nf_mul, nf_mul]
  exact nf_congr (by g2char2) (by g2char2) (by g2char2) (by g2char2) (by g2char2) (by g2char2)

theorem isConj_nf_u (l : K) {α ρ μ ν β γ β' γ' : K} (hβ : β' = β + l * ρ ^ 2)
    (hγ : γ' = γ + l ^ 2 * ρ + l * ν) :
    IsConj (nf α ρ μ ν β γ) (nf α ρ μ ν β' γ') := by
  subst hβ hγ
  refine isConj_iff.mpr ⟨xu l, ?_⟩
  rw [xu_inv, xu_eq_nf, nf_mul, nf_mul]
  exact nf_congr (by g2char2) (by g2char2) (by g2char2) (by g2char2) (by g2char2) (by g2char2)

theorem isConj_nf_v (l : K) {α ρ μ ν β γ β' γ' : K} (hβ : β' = β + l * ρ)
    (hγ : γ' = γ + l * μ) :
    IsConj (nf α ρ μ ν β γ) (nf α ρ μ ν β' γ') := by
  subst hβ hγ
  refine isConj_iff.mpr ⟨xv l, ?_⟩
  rw [xv_inv, xv_eq_nf, nf_mul, nf_mul]
  exact nf_congr (by g2char2) (by g2char2) (by g2char2) (by g2char2) (by g2char2) (by g2char2)

theorem isConj_nf_b (l : K) {α ρ μ ν β γ γ' : K} (hγ : γ' = γ + α * l) :
    IsConj (nf α ρ μ ν β γ) (nf α ρ μ ν β γ') := by
  subst hγ
  refine isConj_iff.mpr ⟨xb l, ?_⟩
  rw [xb_inv, xb_eq_nf, nf_mul, nf_mul]
  exact nf_congr (by g2char2) (by g2char2) (by g2char2) (by g2char2) (by g2char2) (by g2char2)

theorem nf_sq_eq_one {α ρ μ ν β γ : K} (h : nf α ρ μ ν β γ * nf α ρ μ ν β γ = 1) :
    (ρ = 0 ∧ α * β = μ * ν) ∨ (ρ ≠ 0 ∧ α = 0 ∧ ν = ρ * μ) := by
  rw [nf_mul, ← nf_one] at h
  obtain ⟨-, -, e3, -, e5, e6⟩ := nf_injective h
  have hαρ : α * ρ = 0 := by linear_combination (norm := g2char2) e3
  by_cases hρ : ρ = 0
  · left
    refine ⟨hρ, ?_⟩
    subst hρ
    linear_combination (norm := g2char2) e6
  · right
    have hα : α = 0 := (mul_eq_zero.mp hαρ).resolve_right hρ
    subst hα
    refine ⟨hρ, rfl, ?_⟩
    have h5 : ρ * (ρ * μ + ν) = 0 := by linear_combination (norm := g2char2) e5
    have h5' := (mul_eq_zero.mp h5).resolve_left hρ
    linear_combination (norm := g2char2) h5'

theorem exists_mul_self_eq [Finite K] (a : K) : ∃ y : K, y * y = a := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨y, hy⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) a
  exact ⟨y, hy.symm⟩

theorem isConj_t_caseB [Finite K] {ρ l m γ : K} (hρ : ρ ≠ 0) :
    IsConj (xv 1) (nf 0 ρ (l * ρ) (ρ * (l * ρ)) (m * ρ + l * ρ ^ 3) γ) := by
  obtain ⟨y, hy⟩ := exists_mul_self_eq ((γ + l * m * ρ) / ρ)
  have hy' : y ^ 2 * ρ = γ + l * m * ρ := by
    rw [sq, hy]
    field_simp
  have s1 := isConj_nf_a (α := 0) (ρ := ρ) (μ := l * ρ) (ν := ρ * (l * ρ))
    (β := m * ρ + l * ρ ^ 3) (γ := γ) (μ' := 0) (ν' := 0) (β' := m * ρ)
    (γ' := γ + l * m * ρ) l (by g2char2) (by g2char2) (by g2char2) (by g2char2)
  have s2 := isConj_nf_v m (α := 0) (ρ := ρ) (μ := 0) (ν := 0) (β := m * ρ)
    (γ := γ + l * m * ρ) (β' := 0) (γ' := γ + l * m * ρ) (by g2char2) (by g2char2)
  have s3 := isConj_nf_u y (α := 0) (ρ := ρ) (μ := 0) (ν := 0) (β := 0) (γ := γ + l * m * ρ)
    (β' := y * ρ ^ 2) (γ' := γ + l * m * ρ + y ^ 2 * ρ) (by g2char2) (by g2char2)
  have s4 := isConj_nf_v (y * ρ) (α := 0) (ρ := ρ) (μ := 0) (ν := 0) (β := y * ρ ^ 2)
    (γ := γ + l * m * ρ + y ^ 2 * ρ) (β' := 0) (γ' := 0) (by g2char2)
    (by linear_combination (norm := g2char2) hy')
  have chain := s1.trans (s2.trans (s3.trans s4))
  rw [← xr_eq_nf] at chain
  exact (isConj_t_xr hρ).trans chain.symm

theorem isConj_z_or_t_caseA [Finite K] {α l ν γ : K} (hα : α ≠ 0) :
    IsConj (xc 1) (nf α 0 (l * α) ν (l * ν) γ) ∨ IsConj (xv 1) (nf α 0 (l * α) ν (l * ν) γ) := by
  have s1 := isConj_nf_r l (α := α) (ρ := 0) (μ := l * α) (ν := ν) (β := l * ν) (γ := γ)
    (μ' := 0) (ν' := ν + α * l ^ 2) (β' := 0) (γ' := γ + α ^ 2 * l ^ 3)
    (by g2char2) (by g2char2) (by g2char2) (by g2char2)
  by_cases hν : ν + α * l ^ 2 = 0
  · left
    rw [hν] at s1
    obtain ⟨w, hw⟩ : ∃ w, α * w = γ + α ^ 2 * l ^ 3 :=
      ⟨(γ + α ^ 2 * l ^ 3) / α, by field_simp⟩
    have s2 := isConj_nf_b w (α := α) (ρ := 0) (μ := 0) (ν := 0) (β := 0)
      (γ := γ + α ^ 2 * l ^ 3) (γ' := 0) (by linear_combination (norm := g2char2) hw)
    have chain := s1.trans s2
    rw [← xa_eq_nf] at chain
    exact (isConj_z_xa hα).trans chain.symm
  · right
    obtain ⟨y, hy⟩ := exists_mul_self_eq (α / (ν + α * l ^ 2))
    have hy' : (ν + α * l ^ 2) * y ^ 2 = α := by
      rw [show y ^ 2 = y * y from sq y, hy]
      field_simp
    obtain ⟨w, hw⟩ : ∃ w, w * (ν + α * l ^ 2) =
        (ν + α * l ^ 2) ^ 2 * y + (γ + α ^ 2 * l ^ 3) :=
      ⟨((ν + α * l ^ 2) ^ 2 * y + (γ + α ^ 2 * l ^ 3)) / (ν + α * l ^ 2), by field_simp⟩
    have s2 := isConj_nf_u w (α := α) (ρ := 0) (μ := 0) (ν := ν + α * l ^ 2) (β := 0)
      (γ := γ + α ^ 2 * l ^ 3) (β' := 0) (γ' := (ν + α * l ^ 2) ^ 2 * y) (by g2char2)
      (by linear_combination (norm := g2char2) hw)
    have s3 : IsConj (xv (ν + α * l ^ 2))
        (nf α 0 0 (ν + α * l ^ 2) 0 ((ν + α * l ^ 2) ^ 2 * y)) := by
      refine isConj_iff.mpr ⟨xnr y, ?_⟩
      rw [xnr_inv, cj_nrv (ν + α * l ^ 2) y, hy']
      simp only [nf, xr_zero, xu_zero, xb_zero, mul_one]
      rw [mul_assoc, ← (cc_vc (ν + α * l ^ 2) ((ν + α * l ^ 2) ^ 2 * y)).eq, ← mul_assoc]
    exact (isConj_t_xv hν).trans (s3.trans (s1.trans s2).symm)

theorem isConj_z_nf_V {β γ : K} (hβ : β ≠ 0) : IsConj (xc 1) (nf 0 0 0 0 β γ) := by
  obtain ⟨l, hl⟩ : ∃ l, l * β = γ := ⟨γ / β, by field_simp⟩
  have s1 := isConj_nf_a l (α := 0) (ρ := 0) (μ := 0) (ν := 0) (β := β) (γ := γ)
    (μ' := 0) (ν' := 0) (β' := β) (γ' := 0) (by g2char2) (by g2char2) (by g2char2)
    (by linear_combination (norm := g2char2) (-1 : K) * hl)
  rw [← xb_eq_nf] at s1
  exact (isConj_z_xb hβ).trans s1.symm

theorem isConj_z_or_t_caseA0 [Finite K] {μ ν β γ : K} (hμν : μ * ν = 0)
    (hne : nf 0 0 μ ν β γ ≠ 1) :
    IsConj (xc 1) (nf 0 0 μ ν β γ) ∨ IsConj (xv 1) (nf 0 0 μ ν β γ) := by
  by_cases hμ : μ = 0
  · subst hμ
    by_cases hν : ν = 0
    · subst hν
      by_cases hβ : β = 0
      · subst hβ
        left
        have hγ : γ ≠ 0 := by
          rintro rfl
          exact hne nf_one
        rw [← xc_eq_nf]
        exact isConj_z_xc hγ
      · exact Or.inl (isConj_z_nf_V hβ)
    · right
      obtain ⟨l, hl⟩ : ∃ l, l * ν = β := ⟨β / ν, by field_simp⟩
      obtain ⟨l', hl'⟩ : ∃ l', l' * ν = γ := ⟨γ / ν, by field_simp⟩
      have s1 := isConj_nf_r l (α := 0) (ρ := 0) (μ := 0) (ν := ν) (β := β) (γ := γ)
        (μ' := 0) (ν' := ν) (β' := 0) (γ' := γ) (by g2char2) (by g2char2)
        (by linear_combination (norm := g2char2) (-1 : K) * hl) (by g2char2)
      have s2 := isConj_nf_u l' (α := 0) (ρ := 0) (μ := 0) (ν := ν) (β := 0) (γ := γ)
        (β' := 0) (γ' := 0) (by g2char2) (by linear_combination (norm := g2char2) (-1 : K) * hl')
      have chain := s1.trans s2
      rw [← xv_eq_nf] at chain
      exact (isConj_t_xv hν).trans chain.symm
  · have hν : ν = 0 := (mul_eq_zero.mp hμν).resolve_left hμ
    subst hν
    right
    obtain ⟨lam, hlam⟩ := exists_mul_self_eq (β / μ)
    have hlam' : lam ^ 2 * μ = β := by
      rw [sq, hlam]
      field_simp
    obtain ⟨l', hl'⟩ : ∃ l', l' * μ = γ + lam * μ ^ 2 :=
      ⟨(γ + lam * μ ^ 2) / μ, by field_simp⟩
    have s1 := isConj_nf_r lam (α := 0) (ρ := 0) (μ := μ) (ν := 0) (β := β) (γ := γ)
      (μ' := μ) (ν' := 0) (β' := 0) (γ' := γ + lam * μ ^ 2) (by g2char2) (by g2char2)
      (by linear_combination (norm := g2char2) (-1 : K) * hlam') (by g2char2)
    have s2 := isConj_nf_v l' (α := 0) (ρ := 0) (μ := μ) (ν := 0) (β := 0)
      (γ := γ + lam * μ ^ 2) (β' := 0) (γ' := 0) (by g2char2)
      (by linear_combination (norm := g2char2) (-1 : K) * hl')
    have chain := s1.trans s2
    rw [← xu_eq_nf] at chain
    exact (isConj_t_xu hμ).trans chain.symm

theorem isConj_z_or_t_of_nf [Finite K] {α ρ μ ν β γ : K}
    (h : nf α ρ μ ν β γ * nf α ρ μ ν β γ = 1) (hne : nf α ρ μ ν β γ ≠ 1) :
    IsConj (xc 1) (nf α ρ μ ν β γ) ∨ IsConj (xv 1) (nf α ρ μ ν β γ) := by
  rcases nf_sq_eq_one h with ⟨hρ, hαβ⟩ | ⟨hρ, hα, hν⟩
  · subst hρ
    by_cases hα : α = 0
    · subst hα
      exact isConj_z_or_t_caseA0 (by linear_combination (-1 : K) * hαβ) hne
    · obtain ⟨l, rfl⟩ : ∃ l, μ = l * α := ⟨μ / α, by field_simp⟩
      have hβ : β = l * ν := by
        apply mul_left_cancel₀ hα
        linear_combination hαβ
      subst hβ
      exact isConj_z_or_t_caseA hα
  · subst hα
    subst hν
    obtain ⟨l, rfl⟩ : ∃ l, μ = l * ρ := ⟨μ / ρ, by field_simp⟩
    obtain ⟨m, rfl⟩ : ∃ m, β = m * ρ + l * ρ ^ 3 := ⟨(β - l * ρ ^ 3) / ρ, by field_simp; ring⟩
    exact Or.inr (isConj_t_caseB hρ)

theorem isConj_z_or_t_of_mem_U [Finite K] {u : C K} (hu : u ∈ U K) (h : u * u = 1) (hne : u ≠ 1) :
    IsConj (xc 1) u ∨ IsConj (xv 1) u := by
  obtain ⟨α, ρ, μ, ν, β, γ, rfl⟩ := exists_nf hu
  exact isConj_z_or_t_of_nf h hne

theorem cls_involution_of_sylow [Finite K] (hS : IsSylowTwoOf (U K) ⊤) {x : C K}
    (hx : orderOf x = 2) : IsConj (xc 1) x ∨ IsConj (xv 1) x := by
  have hx2 : x * x = 1 := by
    rw [← pow_two]
    exact hx ▸ pow_orderOf_eq_one x
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, orderOf_one] at hx
    exact absurd hx (by norm_num)
  have hzp : IsPGroup 2 ↥(Subgroup.zpowers x) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hx]
    norm_num
  obtain ⟨m, -, hm⟩ := CFSG.Quasithin.H13.F431.NF.exists_conj_le_of_isPGroup le_top hS.2.1 hS.2.2
    (le_top : Subgroup.zpowers x ≤ ⊤) hzp
  have hmem : m * x * m⁻¹ ∈ U K := hm x (Subgroup.mem_zpowers x)
  have hsq : (m * x * m⁻¹) * (m * x * m⁻¹) = 1 := by
    calc (m * x * m⁻¹) * (m * x * m⁻¹) = m * (x * x) * m⁻¹ := by group
      _ = 1 := by rw [hx2]; group
  have hne : m * x * m⁻¹ ≠ 1 := by
    intro h
    apply hx1
    calc x = m⁻¹ * (m * x * m⁻¹) * m := by group
      _ = 1 := by rw [h]; group
  have hconj : IsConj x (m * x * m⁻¹) := isConj_iff.mpr ⟨m, rfl⟩
  rcases isConj_z_or_t_of_mem_U hmem hsq hne with h | h
  · exact Or.inl (h.trans hconj.symm)
  · exact Or.inr (h.trans hconj.symm)

end CFSG.Quasithin.H13.F431.G2.Cls

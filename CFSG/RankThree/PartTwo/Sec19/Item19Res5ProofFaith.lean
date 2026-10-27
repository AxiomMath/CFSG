module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithField
public import CFSG.RankThree.PartTwo.Sec19.Item19Res4ProofXGen
import CFSG.RankThree.PartTwo.Sec19.Item194Proof
import CFSG.RankThree.PartTwo.Sec19.Step199Proof
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late CFSG.RankThree.PartTwo.Sec13

@[expose] def KS1917XGenFaithfulUnitary :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X E : Subgroup G) (c : G),
    Group.IsPerfect X → IsQuasisimple (X ⧸ CFSG.pCore 2 X) →
    E ≤ Subgroup.normalizer (X : Set G) → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    c ∈ E →
    (∀ a ∈ E, (∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) → a = 1) →
    (∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ 2 < p ^ e ∧ p ^ (3 * e) % 3 = 2 ∧
        Nonempty ((X ⧸ CFSG.pCore 2 X) ≃* CFSG.Assembly.RankThreeEven.projSU 3 p (3 * e)) ∧
        KFacts.InducesStdKind X c .field) →
    X ≤ (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
      (⨆ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
        X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G)) ⊔ CFSG.Open.pCoreOf 2 X

@[expose] def KS1917XGenFaithfulD4 :
    Prop :=
  ∀ (G : Type) [Group G] [Finite G] (X E : Subgroup G) (c : G),
    Group.IsPerfect X → IsQuasisimple (X ⧸ CFSG.pCore 2 X) →
    E ≤ Subgroup.normalizer (X : Set G) → CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
    c ∈ E →
    (∀ a ∈ E, (∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) → a = 1) →
    (∃ n : ℕ, 2 ≤ n ∧ CFSG.Blueprint.ChevalleyExceptionalModel (X ⧸ CFSG.pCore 2 X)
        .trialityD4 2 n ∧ Sec4.InducesOuterTheta c X) →
    X ≤ (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
      (⨆ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
        X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G)) ⊔ CFSG.Open.pCoreOf 2 X

namespace Item19Res5Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.LieType.SeitzGeneration CFSG.RankThree.PartTwo.KFacts
open CFSG.RankThree.PartTwo.Sec14.Item148Rank
open CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
open CFSG.LocalAnalysis.ComponentInitial.ProjectivePlane (finite_mulAut_projectiveSL)

section Core

variable {K : Type} [Field K] [Finite K]

theorem closure_fix_eq_top_of_not_inner {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ (3 * f)) (hK : p ^ f % 3 = 1) (hq4 : 4 ≤ p ^ f)
    (B : Subgroup (MulAut (projectiveSL 3 K))) (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x)
    (hB3 : ∀ x ∈ B, x ^ 3 = 1) (hB27 : Nat.card B = 27) {c : MulAut (projectiveSL 3 K)}
    (hcB : c ∈ B) (hc : ¬ IsInnerAut c) :
    ∃ F₀ : Subgroup (MulAut (projectiveSL 3 K)), F₀ ≤ B ∧ Nat.card F₀ = 9 ∧
      Subgroup.closure ({x | c x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x}) = ⊤ := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hK3 : p ^ (3 * f) % 3 = 1 := by rw [pow_mul', pow_three_mod_three148, hK]
  have hf3 : 1 ≤ 3 * f := by omega
  have hcD : c ∉ linearAutGroup 3 K := by
    intro hcD
    have hBD : B ≤ linearAutGroup 3 K := by
      intro β hβ
      obtain ⟨j, hj⟩ := exists_isInnerAut_mul_pow_linear148 hp hf3 hcard hK3 (hB3 c hcB)
        (hB3 β hβ) (hBab _ hcB _ hβ) hc
      have h1 : β * c ^ j ∈ linearAutGroup 3 K := innAut_le_linearAutGroup 3 K hj
      have h2 : β = β * c ^ j * (c ^ j)⁻¹ := by group
      rw [h2]
      exact mul_mem h1 (inv_mem (pow_mem hcD j))
    have hle := card_le_nine_of_le_linearAutGroup (by rw [hcard]; omega) B hBD hBab hB3
    omega
  obtain ⟨σ, hσ, H, hcH⟩ := linear_order_three_field_descent le_rfl c (hB3 c hcB) hcD
  obtain ⟨-, -, -, -, -, hfix⟩ :=
    finite_field_automorphism_fixed_field_cardinality hp hf3 hcard
  obtain ⟨hdvd, k, hkset, hkcard⟩ := hfix (Subgroup.zpowers σ)
  rw [Nat.card_zpowers, hσ, Nat.mul_div_cancel_left f (by norm_num)] at hkcard
  have hk : ∀ x, x ∈ k ↔ σ x = x := by
    intro x
    have hmem : x ∈ k ↔ ∀ τ ∈ Subgroup.zpowers σ, τ x = x := by
      rw [← SetLike.mem_coe, hkset, Set.mem_ofPred_eq]
    rw [hmem]
    constructor
    · intro h
      exact h σ (Subgroup.mem_zpowers σ)
    · intro h τ hτ
      have hle : Subgroup.zpowers σ ≤ MulAction.stabilizer (K ≃+* K) x := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact h
      have := hle hτ
      rwa [MulAction.mem_stabilizer_iff] at this
  have hkK : Nat.card K = Nat.card k ^ 3 := by rw [hcard, hkcard, ← pow_mul, mul_comm]
  have hk4 : 4 ≤ Nat.card k := by rw [hkcard]; exact hq4
  set cH : MulAut (projectiveSL 3 K) := conjAut 3 K H with hcHdef
  set θ : MulAut (MulAut (projectiveSL 3 K)) := MulAut.conj cH⁻¹ with hθ
  set B' : Subgroup (MulAut (projectiveSL 3 K)) := B.map θ.toMonoidHom with hB'
  have hθinj : Function.Injective θ.toMonoidHom := θ.injective
  have hB'ab : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hBab x hx y hy]
  have hB'3 : ∀ x ∈ B', x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hB3 x hx, map_one]
  have hB'27 : Nat.card B' = 27 := by rw [hB', Subgroup.card_map_of_injective hθinj, hB27]
  have hσB' : fieldAut 3 K σ ∈ B' := by
    refine ⟨c, hcB, ?_⟩
    change cH⁻¹ * c * cH⁻¹⁻¹ = fieldAut 3 K σ
    rw [hcH, inv_inv]
    group
  obtain ⟨F₀', hF₀'B', hF₀'9, hgen⟩ := closure_fix_eq_top_field hp hf3 hcard hK3 hσ hk hkK hk4
    B' hB'ab hB'3 hB'27 hσB'
  set F₀ : Subgroup (MulAut (projectiveSL 3 K)) := F₀'.map θ.symm.toMonoidHom with hF₀
  have hF₀B : F₀ ≤ B := by
    rintro _ ⟨φ', hφ', rfl⟩
    obtain ⟨β, hβ, rfl⟩ := hF₀'B' hφ'
    change θ.symm (θ β) ∈ B
    rw [MulEquiv.symm_apply_apply]
    exact hβ
  have hF₀9 : Nat.card F₀ = 9 := by
    rw [hF₀, Subgroup.card_map_of_injective θ.symm.injective, hF₀'9]
  refine ⟨F₀, hF₀B, hF₀9, ?_⟩
  have himage : (cH : projectiveSL 3 K →* projectiveSL 3 K) ''
      ({x | fieldAut 3 K σ x = x} ∪ {x | ∀ φ ∈ F₀', φ x = x}) ⊆
      {x | c x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x} := by
    rintro _ ⟨y, hy | hy, rfl⟩
    · left
      change c (cH y) = cH y
      rw [hcH]
      simp only [MulAut.mul_apply]
      rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      exact congrArg cH hy
    · right
      rintro _ ⟨φ', hφ', rfl⟩
      change (θ.symm φ') (cH y) = cH y
      rw [hθ, MulAut.conj_symm_apply, inv_inv]
      simp only [MulAut.mul_apply]
      rw [MulAut.inv_apply, MulEquiv.symm_apply_apply]
      exact congrArg cH (hy φ' hφ')
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective (cH : projectiveSL 3 K →* projectiveSL 3 K)
    cH.surjective, ← hgen, MonoidHom.map_closure]
  exact Subgroup.closure_mono himage

end Core

section Transport

variable {Y : Type*} [Group Y] {K : Type} [Field K] [Finite K]

omit [Finite K] in
theorem isInnerAut_of_congr (ψ : Y ≃* projectiveSL 3 K) {τ : MulAut Y}
    (h : IsInnerAut (MulAut.congr ψ τ)) : IsInnerAut τ := by
  obtain ⟨z, hz⟩ := h
  refine ⟨ψ.symm z, ?_⟩
  have h1 := congr_conj ψ.symm z
  rw [hz, congr_symm_congr] at h1
  exact h1.symm

theorem closure_fix_eq_top_of_mulEquiv {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f)
    (hcard : Nat.card K = p ^ (3 * f)) (hK : p ^ f % 3 = 1) (hq4 : 4 ≤ p ^ f)
    (ψ : Y ≃* projectiveSL 3 K) (B : Subgroup (MulAut Y))
    (hBab : ∀ x ∈ B, ∀ y ∈ B, x * y = y * x) (hB3 : ∀ x ∈ B, x ^ 3 = 1)
    (hB27 : Nat.card B = 27) {c : MulAut Y} (hcB : c ∈ B) (hc : ¬ IsInnerAut c) :
    ∃ F₀ : Subgroup (MulAut Y), F₀ ≤ B ∧ Nat.card F₀ = 9 ∧
      Subgroup.closure ({x | c x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x}) = ⊤ := by
  set B' := mapAut ψ B with hB'
  have hinj : Function.Injective (MulAut.congr ψ).toMonoidHom := (MulAut.congr ψ).injective
  have hB'ab : ∀ x ∈ B', ∀ y ∈ B', x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    rw [← map_mul, ← map_mul, hBab x hx y hy]
  have hB'3 : ∀ x ∈ B', x ^ 3 = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    rw [← map_pow, hB3 x hx, map_one]
  have hB'27 : Nat.card B' = 27 := by
    rw [hB', mapAut, Subgroup.card_map_of_injective hinj, hB27]
  have hcB' : MulAut.congr ψ c ∈ B' := ⟨c, hcB, rfl⟩
  have hc' : ¬ IsInnerAut (MulAut.congr ψ c) := fun h => hc (isInnerAut_of_congr ψ h)
  obtain ⟨F₀', hF₀'B', hF₀'9, hgen⟩ := closure_fix_eq_top_of_not_inner hp hf hcard hK hq4 B'
    hB'ab hB'3 hB'27 hcB' hc'
  set F₀ : Subgroup (MulAut Y) := F₀'.map (MulAut.congr ψ.symm).toMonoidHom with hF₀
  have hF₀B : F₀ ≤ B := by
    rintro _ ⟨φ', hφ', rfl⟩
    exact mem_mapAut.1 (hF₀'B' hφ')
  have hF₀9 : Nat.card F₀ = 9 := by
    rw [hF₀, Subgroup.card_map_of_injective (MulAut.congr ψ.symm).injective, hF₀'9]
  refine ⟨F₀, hF₀B, hF₀9, ?_⟩
  have himage : (ψ.symm : projectiveSL 3 K →* Y) ''
      ({x | MulAut.congr ψ c x = x} ∪ {x | ∀ φ ∈ F₀', φ x = x}) ⊆
      {x | c x = x} ∪ {x | ∀ φ ∈ F₀, φ x = x} := by
    rintro _ ⟨y, hy | hy, rfl⟩
    · left
      change c (ψ.symm y) = ψ.symm y
      rw [Set.mem_ofPred_eq, congr_apply'] at hy
      have h1 := congrArg ψ.symm hy
      rwa [MulEquiv.symm_apply_apply] at h1
    · right
      rintro _ ⟨φ', hφ', rfl⟩
      change MulAut.congr ψ.symm φ' (ψ.symm y) = ψ.symm y
      rw [congr_apply', MulEquiv.symm_symm, MulEquiv.apply_symm_apply, hy φ' hφ']
  rw [eq_top_iff, ← Subgroup.map_top_of_surjective (ψ.symm : projectiveSL 3 K →* Y)
    ψ.symm.surjective, ← hgen, MonoidHom.map_closure]
  exact Subgroup.closure_mono himage

end Transport

section Lift

variable {G : Type} [Group G] [Finite G]

theorem le_sup_of_closure_fix_eq_top {X E : Subgroup G}
    (hEX : E ≤ Subgroup.normalizer (X : Set G)) (hE3 : IsPGroup 3 E) {c : G} (hcE : c ∈ E)
    {F : Subgroup G} (hFE : F ≤ E)
    (hgen : Subgroup.closure ({y | Step1910Proof.quotAct hEX ⟨c, hcE⟩ y = y} ∪
      {y | ∀ b : E, (b : G) ∈ F → Step1910Proof.quotAct hEX b y = y}) = ⊤) :
    X ≤ (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ (X ⊓ Subgroup.centralizer (F : Set G)) ⊔
      CFSG.Open.pCoreOf 2 X := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set ρ := Step1910Proof.quotAct hEX with hρ
  set O := CFSG.Open.pCoreOf 2 X with hO
  set S := (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔ (X ⊓ Subgroup.centralizer (F : Set G)) ⊔ O
    with hS
  have hOX : O ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hO3 : ¬ 3 ∣ Nat.card O := by
    obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X).exists_card_eq
    rw [hk]
    intro h
    have := Nat.prime_three.dvd_of_dvd_pow h
    norm_num at this
  have hEO : E ≤ Subgroup.normalizer (O : Set G) :=
    hEX.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 X)
  set T : Subgroup (X ⧸ CFSG.pCore 2 X) := (S.subgroupOf X).map (QuotientGroup.mk' _) with hT
  have hlift : ∀ (B : Subgroup G), B ≤ E → (S' : Subgroup G) → (∀ y : G, y ∈ X →
      (∀ b ∈ B, b * y = y * b) → y ∈ S') → S' ≤ S → ∀ x : X,
      (∀ b : E, (b : G) ∈ B → ρ b (x : X ⧸ CFSG.pCore 2 X) = x) →
      ((x : X) : X ⧸ CFSG.pCore 2 X) ∈ T := by
    intro B hBE S' hS' hS'S x hx
    have hkx : ∀ b ∈ B, (x : G)⁻¹ * (b * x * b⁻¹) ∈ O := by
      intro b hb
      exact (Item19Res4Proof.quotAct_mk_eq_iff hEX ⟨b, hBE hb⟩ x).mp (hx ⟨b, hBE hb⟩ hb)
    obtain ⟨y₁, hy₁, hy₁F⟩ :=
      Step199Proof.exists_fixed_mem_coset (hE3.to_le hBE) hO3 (hBE.trans hEO) hkx
    have hy₁X : y₁ ∈ X := by
      have := X.mul_mem x.2 (hOX hy₁)
      simpa using this
    refine ⟨⟨y₁, hy₁X⟩, Subgroup.mem_subgroupOf.mpr (hS'S (hS' y₁ hy₁X hy₁F)), ?_⟩
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Item194Proof.mem_pCore_iff, Subgroup.coe_mul,
      Subgroup.coe_inv]
    have := O.inv_mem hy₁
    simpa using this
  have hgenT : ({y | ρ ⟨c, hcE⟩ y = y} ∪ {y | ∀ b : E, (b : G) ∈ F → ρ b y = y}) ⊆
      (T : Set (X ⧸ CFSG.pCore 2 X)) := by
    rintro y (hy | hy)
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      refine hlift (Subgroup.zpowers c) (Subgroup.zpowers_le.2 hcE)
        (X ⊓ Subgroup.centralizer ({c} : Set G)) ?_ (le_sup_left.trans le_sup_left) x ?_
      · intro y hyX hyc
        refine ⟨hyX, Subgroup.mem_centralizer_iff.2 ?_⟩
        intro h hh
        rw [Set.mem_singleton_iff.1 hh]
        exact hyc c (Subgroup.mem_zpowers c)
      · rintro ⟨b, hbE⟩ ⟨m, rfl⟩
        have hb : (⟨c ^ m, hbE⟩ : E) = ⟨c, hcE⟩ ^ m := Subtype.ext (by simp)
        rw [hb, map_zpow]
        exact Item19Res4Proof.zpow_apply_eq_self hy m
    · obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
      refine hlift F hFE (X ⊓ Subgroup.centralizer (F : Set G)) ?_
        (le_sup_right.trans le_sup_left) x ?_
      · intro y hyX hyF
        exact ⟨hyX, Subgroup.mem_centralizer_iff.2 hyF⟩
      · intro b hb
        exact hy b hb
  have hTtop : T = ⊤ := by
    rw [eq_top_iff, ← hgen, Subgroup.closure_le]
    exact hgenT
  intro x hx
  have hxT : ((⟨x, hx⟩ : X) : X ⧸ CFSG.pCore 2 X) ∈ T := by rw [hTtop]; trivial
  obtain ⟨s, hs, hsx⟩ := hxT
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq, Item194Proof.mem_pCore_iff, Subgroup.coe_mul,
    Subgroup.coe_inv] at hsx
  have hsS : (s : G) ∈ S := Subgroup.mem_subgroupOf.mp hs
  have e : x = (s : G) * ((s : G)⁻¹ * x) := by group
  rw [e]
  exact S.mul_mem hsS (le_sup_right (a := (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
    (X ⊓ Subgroup.centralizer (F : Set G))) hsx)

end Lift

open Item19Res4Proof in
theorem ks1917XGenFaithful_linear
    (G : Type) [Group G] [Finite G] (X E : Subgroup G) (c : G)
    (hEX : E ≤ Subgroup.normalizer (X : Set G)) (hEab : CFSG.Assembly.IsElemAbelian 3 E)
    (hE27 : Nat.card E = 27) (hcE : c ∈ E)
    (hfaith : ∀ a ∈ E, (∀ x ∈ X, a * x * a⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 X) → a = 1)
    {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e) (hq2 : 2 < p ^ e) (hq1 : p ^ (3 * e) % 3 = 1)
    (ι : (X ⧸ CFSG.pCore 2 X) ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField p (3 * e)))
    (hind : KFacts.InducesStdKind X c .field) :
    X ≤ (X ⊓ Subgroup.centralizer ({c} : Set G)) ⊔
      (⨆ F : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9},
        X ⊓ Subgroup.centralizer ((F : Subgroup G) : Set G)) ⊔ CFSG.Open.pCoreOf 2 X := by
  classical
  have hp : p.Prime := Fact.out
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set K := GaloisField p (3 * e) with hKdef
  have hcard : Nat.card K = p ^ (3 * e) := GaloisField.card p (3 * e) (by omega)
  have hK1 : p ^ e % 3 = 1 := by
    rw [pow_mul', pow_three_mod_three148] at hq1
    exact hq1
  have hq4 : 4 ≤ p ^ e := by omega
  obtain ⟨φ⟩ := nonempty_projSL_mulEquiv 3 K
  set ψ : (X ⧸ CFSG.pCore 2 X) ≃* projectiveSL 3 K := ι.trans φ with hψ
  set ρ := Step1910Proof.quotAct hEX with hρ
  have hρinj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have h1 := (quotAct_eq_one_iff hEX a).mp ha
    have h2 := hfaith a a.2 (fun x hx => (commutator_mem_pCoreOf_iff hx).mpr (h1 x hx))
    exact Subtype.ext h2
  have hR := isElemAbelian_range_quotAct hEX hEab
  have hRab : ∀ x ∈ ρ.range, ∀ y ∈ ρ.range, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hR.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hR27 : Nat.card ρ.range = 27 := by
    rw [← hE27]
    exact Nat.card_congr (MonoidHom.ofInjective hρinj).toEquiv.symm
  have hout : Sec4.InducesOuterTheta c X :=
    KFacts.InducesStdKind.inducesOuterTheta X hind (by decide)
  have hcout := quotAct_not_mem_range_conj hEX hcE hout
  obtain ⟨F₀, hF₀R, hF₀9, hgen⟩ := closure_fix_eq_top_of_mulEquiv hp he hcard hK1 hq4 ψ ρ.range
    hRab hR.2 hR27 (c := ρ ⟨c, hcE⟩) ⟨_, rfl⟩ hcout
  set FE : Subgroup E := F₀.comap ρ with hFE
  set F : Subgroup G := FE.map E.subtype with hF
  have hFEle : F ≤ E := Subgroup.map_subtype_le FE
  have hFE9 : Nat.card FE = 9 := by
    have h1 : FE.map ρ = F₀ := by
      rw [hFE, Subgroup.map_comap_eq, inf_eq_right.2 hF₀R]
    rw [← hF₀9, ← h1, Subgroup.card_map_of_injective hρinj]
  have hF9 : Nat.card F = 9 := by
    rw [hF, Subgroup.card_map_of_injective E.subtype_injective, hFE9]
  have hE3 : IsPGroup 3 E := IsPGroup.of_card (n := 3) (by rw [hE27]; norm_num)
  have hgen' : Subgroup.closure ({y | ρ ⟨c, hcE⟩ y = y} ∪
      {y | ∀ b : E, (b : G) ∈ F → ρ b y = y}) = ⊤ := by
    rw [eq_top_iff, ← hgen]
    refine Subgroup.closure_mono ?_
    rintro y (hy | hy)
    · exact Or.inl hy
    · refine Or.inr fun b hb => ?_
      obtain ⟨b', hb', hbb'⟩ := hb
      have : b' = b := Subtype.ext hbb'
      subst this
      exact hy _ hb'
  have hle := le_sup_of_closure_fix_eq_top hEX hE3 hcE hFEle hgen'
  refine hle.trans (sup_le_sup_right (sup_le_sup_left ?_ _) _)
  exact le_iSup_of_le (⟨F, hFEle, hF9⟩ : {F : Subgroup G // F ≤ E ∧ Nat.card F = 9}) le_rfl

end Item19Res5Proof

open Item19Res5Proof in
theorem ks1917XGenFaithful_of_cases
    (hU : KS1917XGenFaithfulUnitary) (hD : KS1917XGenFaithfulD4) : KS1917XGenFaithful := by
  intro G _ _ X E c hXp hXq hEX hEab hE27 hcE hfaith htype
  rcases htype with ⟨p, e, hpF, he, hq2, hiso, hind⟩ | hD4
  · rcases hiso with ⟨hq1, ⟨ι⟩⟩ | ⟨hq2', hι⟩
    · exact ks1917XGenFaithful_linear G X E c hEX hEab hE27 hcE hfaith he hq2 hq1 ι hind
    · exact hU G X E c hXp hXq hEX hEab hE27 hcE hfaith ⟨p, e, hpF, he, hq2, hq2', hι, hind⟩
  · exact hD G X E c hXp hXq hEX hEab hE27 hcE hfaith hD4

end CFSG.RankThree.PartTwo.Sec19

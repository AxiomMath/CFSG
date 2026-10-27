module

public import CFSG.LocalAnalysis.QuasithinUnique.Defs
public import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderShape
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.A11CharNormal
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.S11Setup
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.NaturalSectionOfOffender
import CFSG.LocalAnalysis.AGL81TheoremCD.Section14.LemmaF
import CFSG.LocalAnalysis.AGLEmbeddingD2.GN.BlockLift
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.FiveThreeBridge
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.ClCells
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.Holt.PermFacts
public import CFSG.LieType.BorelTits.Basic
import CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.OffenderOfNatural

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique Subgroup
open CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData
open CFSG.AGLEmbeddingD2.GN
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry
open CFSG.HardMathSupport.Cooperstein.AlternatingGeometry.Offender
open CFSG.LocalAnalysis.AGL81TheoremCD.Section14

variable {X : Type} [Group X] [Finite X]

theorem not_isPGroup_two_alternatingGroup_fin {n : ℕ} (hn : 4 ≤ n) :
    ¬ IsPGroup 2 (alternatingGroup (Fin n)) := by
  intro h
  haveI : Nontrivial (alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
  have hnt : Nontrivial (Subgroup.center (alternatingGroup (Fin n))) := h.center_nontrivial
  rw [alternatingGroup.center_eq_bot (α := Fin n) (by rw [Nat.card_fin]; omega)] at hnt
  obtain ⟨a, b, hab⟩ := hnt
  exact hab (Subsingleton.elim a b)

theorem eq_bot_of_isPGroup_two_of_alternatingGroup_le {n : ℕ} (hn : 5 ≤ n)
    {K N : Subgroup (Equiv.Perm (Fin n))} (hAK : alternatingGroup (Fin n) ≤ K)
    (hNK : N ≤ K) (hKN : K ≤ Subgroup.normalizer (N : Set (Equiv.Perm (Fin n))))
    (hN2 : IsPGroup 2 N) : N = ⊥ := by
  rcases CFSG.Holt.eq_bot_or_alternatingGroup_le (Λ := Fin n)
    (by rw [Nat.card_fin]; omega) (hAK.trans hKN) with h | h
  · exact h
  · exfalso
    exact not_isPGroup_two_alternatingGroup_fin (by omega) (hN2.to_le h)

theorem exists_swap_mem_of_offenderShape {n : ℕ} {E : Subgroup (Equiv.Perm (Fin n))}
    (hE2 : IsPGroup 2 E) (hEne : E ≠ ⊥) (hshape : OffenderShapeConcl E)
    (hfix : ∃ p, ∀ g ∈ E, g p = p) :
    ∃ i j : Fin n, i ≠ j ∧ Equiv.swap i j ∈ E := by
  classical
  have hEeq : E = orbitStab E := (hshape.1 hfix).2
  have hmove : ∃ g ∈ E, ∃ i : Fin n, g i ≠ i := by
    by_contra h
    push Not at h
    apply hEne
    rw [Subgroup.eq_bot_iff_forall]
    intro g hg
    exact Equiv.ext (fun i => h g hg i)
  obtain ⟨g, hgE, i, hi⟩ := hmove
  refine ⟨i, g i, hi.symm, ?_⟩
  have hswap : Equiv.swap i (g i) ∈ orbitStab E := Classif.swap_mem_orbitStab hgE i
  rwa [← hEeq] at hswap

private theorem range_eq_alternatingGroup_of_ker_eq {n : ℕ}
    {φ θ : X →* Equiv.Perm (Fin n)} (hker : φ.ker = θ.ker)
    (hφ : φ.range = alternatingGroup (Fin n))
    (hθ : alternatingGroup (Fin n) ≤ θ.range) :
    θ.range = alternatingGroup (Fin n) := by
  have hcardθ : Nat.card θ.range = Nat.card (X ⧸ θ.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange θ).toEquiv).symm
  have hcardφ : Nat.card φ.range = Nat.card (X ⧸ φ.ker) :=
    (Nat.card_congr (QuotientGroup.quotientKerEquivRange φ).toEquiv).symm
  have hcard : Nat.card θ.range = Nat.card (alternatingGroup (Fin n)) := by
    rw [hcardθ, ← hker, ← hcardφ, hφ]
  exact (Subgroup.eq_of_le_of_card_ge hθ (le_of_eq hcard)).symm

theorem exists_conj_of_ker_eq_of_range_eq_alternatingGroup {n : ℕ} (hn : 5 ≤ n) (hn6 : n ≠ 6)
    {φ θ : X →* Equiv.Perm (Fin n)} (hker : φ.ker = θ.ker)
    (hφ : φ.range = alternatingGroup (Fin n))
    (hθ : alternatingGroup (Fin n) ≤ θ.range) :
    ∃ σ : Equiv.Perm (Fin n), ∀ x : X, θ x = σ * φ x * σ⁻¹ := by
  classical
  have hθrange := range_eq_alternatingGroup_of_ker_eq hker hφ hθ
  let φA : X →* alternatingGroup (Fin n) :=
    φ.codRestrict _ (fun x => by
      rw [← hφ]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  let θA : X →* alternatingGroup (Fin n) :=
    θ.codRestrict _ (fun x => by
      rw [← hθrange]
      exact MonoidHom.mem_range.mpr ⟨x, rfl⟩)
  have hφmem : ∀ a : alternatingGroup (Fin n), (a : Equiv.Perm (Fin n)) ∈ φ.range := by
    intro a
    rw [hφ]
    exact a.2
  have hθmem : ∀ a : alternatingGroup (Fin n), (a : Equiv.Perm (Fin n)) ∈ θ.range := by
    intro a
    rw [hθrange]
    exact a.2
  have hφAs : Function.Surjective φA := by
    intro a
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hφmem a)
    exact ⟨x, Subtype.ext hx⟩
  have hθAs : Function.Surjective θA := by
    intro a
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp (hθmem a)
    exact ⟨x, Subtype.ext hx⟩
  have hkerA : φA.ker = θA.ker := by
    rw [MonoidHom.ker_codRestrict, MonoidHom.ker_codRestrict, hker]
  let eφ := QuotientGroup.quotientKerEquivOfSurjective φA hφAs
  let eθ := QuotientGroup.quotientKerEquivOfSurjective θA hθAs
  let ψ : alternatingGroup (Fin n) ≃* alternatingGroup (Fin n) :=
    eφ.symm.trans ((QuotientGroup.quotientMulEquivOfEq hkerA).trans eθ)
  have hψ : ∀ x : X, ψ (φA x) = θA x := by
    intro x
    have h1 : eφ.symm (φA x) = QuotientGroup.mk x := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show eθ ((QuotientGroup.quotientMulEquivOfEq hkerA) (eφ.symm (φA x))) = θA x
    rw [h1]
    rfl
  obtain ⟨σ, hσ⟩ :=
    (CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj n hn hn6).2 ψ
  refine ⟨σ, fun x => ?_⟩
  have hx := hψ x
  change (θA x : Equiv.Perm (Fin n)) = σ * (φA x : Equiv.Perm (Fin n)) * σ⁻¹
  rw [← hx, ← hσ, MulAut.conjNormal_apply]

theorem ne_bot_of_pCoreOf_le_of_range_eq {n : ℕ} (hn : 3 ≤ n) {T : Subgroup X}
    (hC : CharTwo (⊤ : Subgroup X)) (φ : X →* Equiv.Perm (Fin n))
    (hrange : φ.range = alternatingGroup (Fin n))
    (hQT : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ T) : T ≠ ⊥ := by
  intro hT
  have hQbot : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) = ⊥ :=
    le_bot_iff.mp (hQT.trans (le_of_eq hT))
  have htop : (⊤ : Subgroup X) = ⊥ := by
    have hcent : Subgroup.centralizer ((⊥ : Subgroup X) : Set X) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      have hy1 : y = 1 := by simpa using hy
      simp [hy1]
    have h := hC
    change (⊤ : Subgroup X) ⊓ Subgroup.centralizer
      ((CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) : Set X) ≤
        CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) at h
    rw [hQbot, hcent, inf_top_eq] at h
    exact le_bot_iff.mp h
  have hx1 : ∀ x : X, x = 1 := by
    intro x
    have hxbot : x ∈ (⊥ : Subgroup X) := by rw [← htop]; exact Subgroup.mem_top x
    simpa using hxbot
  haveI : Nontrivial (alternatingGroup (Fin n)) :=
    alternatingGroup.nontrivial_of_three_le_card (by rw [Nat.card_fin]; omega)
  obtain ⟨σ, hσne⟩ := exists_ne (1 : alternatingGroup (Fin n))
  have hσmem : (σ : Equiv.Perm (Fin n)) ∈ alternatingGroup (Fin n) := σ.2
  have hσrange : (σ : Equiv.Perm (Fin n)) ∈ φ.range := by
    rw [hrange]
    exact hσmem
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hσrange
  refine hσne (Subtype.ext ?_)
  rw [← hx, hx1 x, map_one]
  simp

private theorem sup_eq_top_of_map_eq_alternatingGroup {n : ℕ} {L T : Subgroup X}
    {φ : X →* Equiv.Perm (Fin n)} (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hrange : φ.range = alternatingGroup (Fin n))
    (hL : L.map φ = alternatingGroup (Fin n))
    (hQT : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ T) : L ⊔ T = ⊤ := by
  have hmap : (L ⊔ T).map φ = φ.range := by
    rw [Subgroup.map_sup, hL, hrange]
    exact sup_eq_left.mpr (by rw [← hrange]; exact Subgroup.map_le_range φ T)
  have hcomap := Subgroup.comap_map_eq φ (L ⊔ T)
  rw [hmap] at hcomap
  have hrangecomap : (φ.range).comap φ = ⊤ := by
    have h := Subgroup.comap_map_eq φ (⊤ : Subgroup X)
    rwa [Subgroup.map_top, top_sup_eq] at h
  rw [hrangecomap] at hcomap
  have hkerle : φ.ker ≤ L ⊔ T := by
    rw [hker]
    exact hQT.trans le_sup_right
  rw [sup_eq_left.mpr hkerle] at hcomap
  exact hcomap.symm

private theorem pCoreOf_le_ker_topEquiv_comp {n : ℕ} (hn : 5 ≤ n)
    {θ : ↥(⊤ : Subgroup X) →* Equiv.Perm (Fin n)}
    (hθ : alternatingGroup (Fin n) ≤ θ.range) :
    CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤
      (θ.comp (Subgroup.topEquiv (G := X)).symm.toMonoidHom).ker := by
  let Q' : Subgroup ↥(⊤ : Subgroup X) := (CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)).subgroupOf ⊤
  let N : Subgroup (Equiv.Perm (Fin n)) := Q'.map θ
  have hQn : (CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)).Normal := normal_pCoreOf_top
  have hQ2 : IsPGroup 2 (CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)) :=
    CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (⊤ : Subgroup X)
  have hQ'n : Q'.Normal := hQn.subgroupOf ⊤
  have hQ'2 : IsPGroup 2 Q' :=
    hQ2.of_equiv (Subgroup.subgroupOfEquivOfLe (le_top : _ ≤ ⊤)).symm
  have hθsurj : Function.Surjective θ.rangeRestrict := by
    intro y
    obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp y.2
    exact ⟨x, Subtype.ext hx⟩
  have hNmap : N.subgroupOf θ.range = Q'.map θ.rangeRestrict := by
    ext n
    constructor
    · intro hn'
      rw [Subgroup.mem_subgroupOf, Subgroup.mem_map] at hn'
      obtain ⟨q, hq, hqn⟩ := hn'
      exact ⟨q, hq, Subtype.ext hqn⟩
    · rintro ⟨q, hq, rfl⟩
      exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_map_of_mem θ hq)
  have hNn : (N.subgroupOf θ.range).Normal := by
    have h' : (Q'.map θ.rangeRestrict).Normal := hQ'n.map θ.rangeRestrict hθsurj
    rwa [← hNmap] at h'
  have hNK : N ≤ θ.range := Subgroup.map_le_range θ Q'
  have hKN : θ.range ≤ Subgroup.normalizer (N : Set (Equiv.Perm (Fin n))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hNK).mp hNn
  have hN2 : IsPGroup 2 N := hQ'2.map θ
  have hNbot : N = ⊥ :=
    eq_bot_of_isPGroup_two_of_alternatingGroup_le (n := n) hn hθ hNK hKN hN2
  have hQ'ker : Q' ≤ θ.ker := (Subgroup.map_eq_bot_iff Q').mp hNbot
  intro q hq
  have hqmem : (⟨q, Subgroup.mem_top q⟩ : ↥(⊤ : Subgroup X)) ∈ Q' :=
    Subgroup.mem_subgroupOf.mpr hq
  have hqker : θ ⟨q, Subgroup.mem_top q⟩ = 1 := MonoidHom.mem_ker.mp (hQ'ker hqmem)
  show θ ((Subgroup.topEquiv (G := X)).symm q) = 1
  rw [show (Subgroup.topEquiv (G := X)).symm q = ⟨q, Subgroup.mem_top q⟩ from
    Subtype.ext (Subgroup.topEquiv_symm_apply_coe q)]
  exact hqker

private theorem exists_offender_image_a10
    {L T A : Subgroup X} (hLn : L.Normal)
    (φ : X →* Equiv.Perm (Fin 10)) (hkerW : φ.ker = gnC T)
    (hL : L.map φ = alternatingGroup (Fin 10))
    (hW : CFSG.Open.IsElemAbelian 2 (gnV T)) (hWle : gnV T ≤ T)
    (hAmax : CFSG.Quasithin.IsMaxElemAbelian T A) (hAW : ¬ A ≤ gnC T)
    (hoff : Nat.card (gnV T) ≤ (gnC T).relIndex A *
      Nat.card ↥(gnV T ⊓ Subgroup.centralizer (A : Set X))) :
    ∃ (θ : ↥(⊤ : Subgroup X) →* Equiv.Perm (Fin 10))
      (E : Subgroup (Equiv.Perm (Fin 10))),
      (∀ σ ∈ alternatingGroup (Fin 10), ∃ l ∈ L, ∃ hl : l ∈ (⊤ : Subgroup X),
        θ ⟨l, hl⟩ = σ) ∧
      (∀ m : ↥(⊤ : Subgroup X), θ m = 1 →
        (m : X) ∈ Subgroup.centralizer (gnV T : Set X)) ∧
      E = (A.subgroupOf ⊤).map θ ∧ OffenderShapeConcl E ∧
      IsPGroup 2 E ∧ E ≠ ⊥ := by
  classical
  have hWn : (gnV T).Normal := normal_gnV T
  have hnat : NaturalSectionOn (gnV T) L ⊤ 10 :=
    naturalSectionOn_top_of_offender (W := gnV T) (L := L) (A := A) (n := 10)
      hW hWn hLn (by norm_num) φ hkerW hL hAmax.2.1 hAW hoff
  obtain ⟨π, θ, hπ, -, hLθ, hequiv, hθker⟩ := hnat
  have hU : ⁅gnV T, L⁆ ≤ gnV T := by
    rw [Subgroup.commutator_comm]
    exact (Subgroup.le_normalizer_iff_commutator_le_right (H := L)
      (K := gnV T)).mp Subgroup.le_normalizer_of_normal
  let E : Subgroup (Equiv.Perm (Fin 10)) := (A.subgroupOf ⊤).map θ
  have hshape : OffenderShapeConcl E :=
    offender_shape_of_section (d := 10) (Or.inr (by norm_num)) hπ hequiv
      (isElemAb2_of_isElemAbelian hW) hWle hU
      (isElemAb2_of_isElemAbelian hAmax.2.1) hAmax.1 le_top
      (fun B hBT hB => hAmax.2.2 B hBT (isElemAbelian_of_isElemAb2 hB)) hθker
  have hE2 : IsPGroup 2 E := by
    have hAp : IsPGroup 2 (A.subgroupOf ⊤) :=
      hAmax.2.1.isPGroup.of_equiv
        (Subgroup.subgroupOfEquivOfLe (le_top : A ≤ ⊤)).symm
    exact hAp.map θ
  have hEne : E ≠ ⊥ := by
    intro hbot
    apply hAW
    intro a ha
    have hmem : θ ⟨a, Subgroup.mem_top a⟩ ∈ E := by
      rw [show E = (A.subgroupOf ⊤).map θ from rfl]
      exact Subgroup.mem_map_of_mem θ (Subgroup.mem_subgroupOf.mpr ha)
    rw [hbot] at hmem
    exact hθker ⟨a, Subgroup.mem_top a⟩ (by simpa using hmem)
  exact ⟨θ, E, hLθ, hθker, rfl, hshape, hE2, hEne⟩

private theorem exists_conj_offender_a10 {T : Subgroup X}
    {φ : X →* Equiv.Perm (Fin 10)} (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hCeq : gnC T = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (θ : ↥(⊤ : Subgroup X) →* Equiv.Perm (Fin 10))
    (hθker : ∀ m : ↥(⊤ : Subgroup X), θ m = 1 →
      (m : X) ∈ Subgroup.centralizer (gnV T : Set X))
    (hθrange : alternatingGroup (Fin 10) ≤ θ.range)
    (hrange : φ.range = alternatingGroup (Fin 10)) :
    ∃ (θ' : X →* Equiv.Perm (Fin 10)) (σ : Equiv.Perm (Fin 10)),
      (∀ x : X, θ' x = θ ⟨x, Subgroup.mem_top x⟩) ∧
      θ'.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ∧
      θ'.range = alternatingGroup (Fin 10) ∧
      (∀ x : X, θ' x = σ * φ x * σ⁻¹) := by
  let θ' : X →* Equiv.Perm (Fin 10) :=
    θ.comp (Subgroup.topEquiv (G := X)).symm.toMonoidHom
  have hθ'apply : ∀ x : X, θ' x = θ ⟨x, Subgroup.mem_top x⟩ := by
    intro x
    change θ ((Subgroup.topEquiv (G := X)).symm x) = θ ⟨x, Subgroup.mem_top x⟩
    exact congrArg θ (Subtype.ext (Subgroup.topEquiv_symm_apply_coe x))
  have hθ'ker_le : θ'.ker ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) := by
    intro x hx
    rw [MonoidHom.mem_ker, hθ'apply] at hx
    have hxW : x ∈ Subgroup.centralizer (gnV T : Set X) :=
      hθker ⟨x, Subgroup.mem_top x⟩ hx
    have hxW' : x ∈ gnC T := hxW
    rwa [hCeq] at hxW'
  have hQ_le : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ θ'.ker :=
    pCoreOf_le_ker_topEquiv_comp (n := 10) (by norm_num) hθrange
  have hθ'ker_eq : θ'.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) :=
    le_antisymm hθ'ker_le hQ_le
  have hθle : θ.range ≤ θ'.range := by
    rintro _ ⟨m, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨(m : X), by rw [hθ'apply]⟩
  have hAlt : alternatingGroup (Fin 10) ≤ θ'.range := hθrange.trans hθle
  have hθ'range_eq : θ'.range = alternatingGroup (Fin 10) :=
    range_eq_alternatingGroup_of_ker_eq (hker.trans hθ'ker_eq.symm) hrange hAlt
  obtain ⟨σ, hσ⟩ :=
    exists_conj_of_ker_eq_of_range_eq_alternatingGroup (X := X) (n := 10)
      (by norm_num) (by norm_num) (φ := φ) (θ := θ')
      (hker.trans hθ'ker_eq.symm) hrange hAlt
  exact ⟨θ', σ, hθ'apply, hθ'ker_eq, hθ'range_eq, hσ⟩

private theorem exists_fixed_point_of_offender {n : ℕ} {A T : Subgroup X}
    {φ θ' : X →* Equiv.Perm (Fin n)}
    {θ : ↥(⊤ : Subgroup X) →* Equiv.Perm (Fin n)}
    (hθ'apply : ∀ x : X, θ' x = θ ⟨x, Subgroup.mem_top x⟩)
    (hAT : A ≤ T) {σ : Equiv.Perm (Fin n)}
    (hσ : ∀ x : X, θ' x = σ * φ x * σ⁻¹)
    {i : Fin n} (hi : ∀ t ∈ T, φ t i = i) :
    ∃ p : Fin n, ∀ g ∈ (A.subgroupOf ⊤).map θ, g p = p := by
  refine ⟨σ i, ?_⟩
  intro g hg
  rw [Subgroup.mem_map] at hg
  obtain ⟨a, ha, rfl⟩ := hg
  have haA : ((a : ↥(⊤ : Subgroup X)) : X) ∈ A := Subgroup.mem_subgroupOf.mp ha
  have haT : ((a : ↥(⊤ : Subgroup X)) : X) ∈ T := hAT haA
  have hφa : φ ((a : ↥(⊤ : Subgroup X)) : X) i = i := hi _ haT
  have hθ'a : θ a = θ' ((a : ↥(⊤ : Subgroup X)) : X) := by
    rw [hθ'apply]
  calc θ a (σ i) = θ' ((a : ↥(⊤ : Subgroup X)) : X) (σ i) := by rw [hθ'a]
    _ = (σ * φ ((a : ↥(⊤ : Subgroup X)) : X) * σ⁻¹) (σ i) := by rw [hσ]
    _ = σ (φ ((a : ↥(⊤ : Subgroup X)) : X) i) := by simp
    _ = σ i := by rw [hφa]

private theorem false_of_swap_mem_alternatingGroup {n : ℕ}
    {E K : Subgroup (Equiv.Perm (Fin n))} (hE2 : IsPGroup 2 E) (hEne : E ≠ ⊥)
    (hshape : OffenderShapeConcl E) (hfixE : ∃ p, ∀ g ∈ E, g p = p)
    (hEK : E ≤ K) (hK : K = alternatingGroup (Fin n)) : False := by
  obtain ⟨p, q, hpq, hswapE⟩ :=
    exists_swap_mem_of_offenderShape hE2 hEne hshape hfixE
  have hswapK := hEK hswapE
  rw [hK] at hswapK
  have hsign : Equiv.Perm.sign (Equiv.swap p q) = -1 := Equiv.Perm.sign_swap hpq
  rw [Equiv.Perm.mem_alternatingGroup, hsign] at hswapK
  norm_num at hswapK

private theorem false_of_offender_of_a10
    {L T A : Subgroup X} (hLn : L.Normal)
    (φ : X →* Equiv.Perm (Fin 10)) (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hrange : φ.range = alternatingGroup (Fin 10)) (hL : L.map φ = alternatingGroup (Fin 10))
    (hCeq : gnC T = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hW : CFSG.Open.IsElemAbelian 2 (gnV T)) (hWle : gnV T ≤ T)
    (hAmax : CFSG.Quasithin.IsMaxElemAbelian T A) (hAW : ¬ A ≤ gnC T)
    (hoff : Nat.card (gnV T) ≤ (gnC T).relIndex A *
      Nat.card ↥(gnV T ⊓ Subgroup.centralizer (A : Set X)))
    (hfix : ∃ i : Fin 10, ∀ t ∈ T, φ t i = i) : False := by
  have hkerW : φ.ker = gnC T := hker.trans hCeq.symm
  obtain ⟨θ, E, hLθ, hθker, hEeq, hshape, hE2, hEne⟩ :=
    exists_offender_image_a10 hLn φ hkerW hL hW hWle hAmax hAW hoff
  have hθrange : alternatingGroup (Fin 10) ≤ θ.range := by
    intro σ hσ
    obtain ⟨l, _, hlM, hval⟩ := hLθ σ hσ
    exact MonoidHom.mem_range.mpr ⟨⟨l, hlM⟩, hval⟩
  obtain ⟨θ', σ, hθ'apply, hθ'ker_eq, hθ'range_eq, hσ⟩ :=
    exists_conj_offender_a10 hker hCeq θ hθker hθrange hrange
  obtain ⟨i, hi⟩ := hfix
  have hfixE := exists_fixed_point_of_offender hθ'apply hAmax.1 hσ hi
  rw [← hEeq] at hfixE
  have hE_le : E ≤ θ'.range := by
    rw [hEeq]
    intro g hg
    rw [Subgroup.mem_map] at hg
    obtain ⟨a, -, rfl⟩ := hg
    refine MonoidHom.mem_range.mpr ⟨((a : ↥(⊤ : Subgroup X)) : X), ?_⟩
    rw [hθ'apply]
  exact false_of_swap_mem_alternatingGroup hE2 hEne hshape hfixE hE_le hθ'range_eq

theorem exists_char_normal_of_a10
    {L T : Subgroup X} (hC : CFSG.QuasithinUnique.CharTwo (⊤ : Subgroup X)) (hLn : L.Normal)
    (φ : X →* Equiv.Perm (Fin 10)) (hker : φ.ker = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X))
    (hrange : φ.range = alternatingGroup (Fin 10)) (hLker : ¬ L ≤ φ.ker)
    (hQT : CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) ≤ T) (hT2 : IsPGroup 2 T)
    (hfix : ∃ i : Fin 10, ∀ t ∈ T, φ t i = i) :
    ∃ C : Subgroup X, C ≠ ⊥ ∧ C ≤ T ∧ (C.subgroupOf T).Characteristic ∧ C.Normal := by
  classical
  have hL : L.map φ = alternatingGroup (Fin 10) :=
    map_eq_alternatingGroup_of_range_eq (by norm_num) hLn φ hrange hLker
  have hsup : L ⊔ T = ⊤ := sup_eq_top_of_map_eq_alternatingGroup hker hrange hL hQT
  have hTne : T ≠ ⊥ := ne_bot_of_pCoreOf_le_of_range_eq (n := 10) (by norm_num) hC φ hrange hQT
  have hW : CFSG.Open.IsElemAbelian 2 (gnV T) :=
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.isElemAbelian_gnV_of_le hC hQT
  have hWle : gnV T ≤ T :=
    CFSG.AGLEmbeddingD2.McLaughlin.OrdinaryProofs.gnV_le_of_le hC hQT
  by_cases hLW : L ≤ gnC T
  · exact ⟨omegaOneCenterOf T,
      CFSG.QuasithinUnique.Setup.omegaOneCenterOf_ne_bot hT2 hTne,
      CFSG.QuasithinUnique.Setup.omegaOneCenterOf_le T,
      CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf T,
      normal_omegaOneCenterOf_of_le_gnC hLn hsup hLW⟩
  · have hKz := center_quotient_pCore_eq_bot_of_map (n := 10) (by norm_num) hLn φ hker hL
    have hKsimple := isSimpleGroup_quotient_pCore_of_map (n := 10) (by norm_num) hLn φ hker hL
    have hCeq : gnC T = CFSG.Open.pCoreOf 2 (⊤ : Subgroup X) :=
      (gnC_eq_pCoreOf_or_le_gnC (K := L) (S := T) hC hT2 hQT hLn hsup hKz hKsimple).resolve_left
        hLW
    by_cases hJ : thompsonJ T ≤ CFSG.Open.pCoreOf 2 (⊤ : Subgroup X)
    · exact ⟨thompsonJ T,
        CFSG.QuasithinUnique.Setup.thompsonJ_ne_bot hT2 hTne,
        CFSG.Quasithin.B6.thompsonJ_le T,
        CFSG.QuasithinUnique.Setup.characteristic_thompsonJ T,
        normal_thompsonJ_of_le_pCoreOf hQT hJ⟩
    · exfalso
      have hJ' : ¬ thompsonJ T ≤ Subgroup.centralizer (gnV T : Set X) := by
        intro h
        apply hJ
        have h' : thompsonJ T ≤ gnC T := h
        rwa [hCeq] at h'
      obtain ⟨A, hAmax, hAW, hoff⟩ :=
        exists_maxElemAbelian_offender_of_not_thompsonJ_le (R := T) (W := gnV T) hW hWle hJ'
      exact false_of_offender_of_a10 hLn φ hker hrange hL hCeq hW hWle hAmax hAW hoff hfix

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10Gen

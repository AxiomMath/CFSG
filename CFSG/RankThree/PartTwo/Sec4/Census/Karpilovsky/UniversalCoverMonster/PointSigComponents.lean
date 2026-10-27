module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSigCores
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenNamed
public import CFSG.RankThree.PartTwo.Sec6.Item65Tools
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.CoreSubgroup
public import CFSG.Sporadic.Suz.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig

attribute [local irreducible] dotProduct

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.Native.ONTriple Subgroup
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37 (pslEquivProjSL
  card_psl_three_seven isSimpleGroup_psl_three_seven)

@[expose] def TwoLines {X : Type} [Group X] (P Y : Subgroup X) : Prop :=
  ∃ p ∈ P, ∃ q ∈ P, p ∉ Subgroup.center X ∧ q ∉ Subgroup.center X ∧
    Subgroup.centralizer ({p} : Set X) ≠ Subgroup.centralizer ({q} : Set X) ∧
    pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p} : Set X)) ≠ ⊥ ∧
    pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({q} : Set X)) ≠ ⊥

section Model

set_option linter.unusedSectionVars false

@[expose] def L37OvergroupTransfer : Prop :=
  ∀ j < 2, ∀ Y : Subgroup GM, AG j ≤ Subgroup.normalizer (Y : Set GM) →
    ∀ l₁ l₂ : ℕ, l₁ < l₂ → l₂ < 4 → core j Y l₁ ≠ ⊥ → core j Y l₂ ≠ ⊥ →
      Y ≤ Subgroup.normalizer ((⨆ ℓ : Fin 4, core j Y ℓ : Subgroup GM) : Set GM) ∨ Y = ⊤

theorem uL_ne_zero : ∀ j < 2, ∀ l < 4, uL j l ≠ 0 := by decide +kernel

theorem mL_not_mem_zpowers {j l : ℕ} (hj : j < 2) (hl : l < 4) : mL j l ∉ zpowers zG := by
  intro h
  have h0 : relG.coord ⟨mL j l, mL_mem_P0 hj hl⟩ = 0 := (relG.coord_eq_zero_iff _).2 h
  rw [coord_mL hj hl] at h0
  exact uL_ne_zero j hj l hl h0

theorem exists_noncomm_of_card {Q : Type*} [Group Q] [Finite Q] [IsSimpleGroup Q]
    (hc : ¬ (Nat.card Q).Prime) : ∃ a b : Q, a * b ≠ b * a := by
  by_contra h
  push Not at h
  let _ : CommGroup Q := { ‹Group Q› with mul_comm := fun a b => h a b }
  exact hc (IsSimpleGroup.prime_card (α := Q))

theorem tuple_mem_thetaComponentsIn {j : ℕ} (hj : j < 2) {Y : Subgroup GM}
    (hY : AG j ≤ Subgroup.normalizer (Y : Set GM)) {l₁ l₂ : ℕ} (hl : l₁ < l₂) (h₂ : l₂ < 4)
    (hv₁ : core j Y l₁ ≠ ⊥) (hv₂ : core j Y l₂ ≠ ⊥)
    (hov : Y ≤ Subgroup.normalizer ((⨆ ℓ : Fin 4, core j Y ℓ : Subgroup GM) : Set GM) ∨ Y = ⊤) :
    (⨆ ℓ : Fin 4, core j Y ℓ : Subgroup GM) ∈ thetaComponentsIn Y ∧
      Nat.card (⨆ ℓ : Fin 4, core j Y ℓ : Subgroup GM) = 1876896 := by
  obtain ⟨hcard, hf7, ⟨e⟩⟩ := tuple_L37 hj hY hl h₂ hv₁ hv₂
  have hYN : Y ≤ Subgroup.normalizer ((⨆ ℓ : Fin 4, core j Y ℓ : Subgroup GM) : Set GM) := by
    rcases hov with h | h
    · exact h
    · exfalso
      subst h
      exact hv₁ (core_top_eq_bot hj (hl.trans h₂))
  set T : Subgroup GM := ⨆ ℓ : Fin 4, core j Y ℓ with hT
  have hTY : T ≤ Y := iSup_le fun ℓ => core_le_left j Y ℓ
  have hn : (T.subgroupOf Y).Normal := by
    refine ⟨fun a ha h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    simpa using (Subgroup.mem_normalizer_iff.mp (hYN h.2) a).mp ha
  have hsn : (T.subgroupOf Y).IsSubnormal := Subgroup.Normal.isSubnormal hn
  have hcardS : Nat.card (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) = 1876896 := by
    rw [← Nat.card_congr pslEquivProjSL.toEquiv, card_psl_three_seven]
  have hsimpS : IsSimpleGroup (CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1)) :=
    haveI := isSimpleGroup_psl_three_seven
    pslEquivProjSL.symm.isSimpleGroup
  have hθ : aschbacherSolvableCore 3 ↥T = ⊥ := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (aschbacherSolvableCore 3 ↥T)
    rw [hcard, Nat.card_congr e.toEquiv, hcardS] at h1
    have h2 : Nat.card (aschbacherSolvableCore 3 ↥T) = 1 := by
      have : 1876896 * Nat.card (aschbacherSolvableCore 3 ↥T) = 1876896 * 1 := by omega
      exact Nat.eq_of_mul_eq_mul_left (by norm_num) this
    exact Subgroup.eq_bot_of_card_eq _ h2
  have eT : ↥T ≃* CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1) :=
    (((QuotientGroup.quotientMulEquivOfEq hθ).trans QuotientGroup.quotientBot).symm).trans e
  have hsimpT : IsSimpleGroup ↥T := haveI := hsimpS; eT.isSimpleGroup
  have hnc : ¬ (Nat.card ↥T).Prime := by rw [hcard]; norm_num
  have hncQ : ¬ (Nat.card (↥T ⧸ aschbacherSolvableCore 3 ↥T)).Prime := by
    rw [Nat.card_congr e.toEquiv, hcardS]; norm_num
  have hqT := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (exists_noncomm_of_card (Q := ↥T) hnc)).1
  have hsimpQ : IsSimpleGroup (↥T ⧸ aschbacherSolvableCore 3 ↥T) := haveI := hsimpS; e.isSimpleGroup
  have hqQ := (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (exists_noncomm_of_card (Q := ↥T ⧸ aschbacherSolvableCore 3 ↥T) hncQ)).1
  exact ⟨Sec6.mem_thetaComponentsIn_of hTY hqT.1 hsn hqQ, hcard⟩

section Transport

variable {X : Type} [Group X]

theorem map_pPrimeCore_inf_centralizer {G' : Type*} [Group G'] (φ : X ≃* G') (Y : Subgroup X)
    (p : X) :
    (pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p} : Set X))).map φ.toMonoidHom =
      pPrimeCoreOf 3 (Y.map φ.toMonoidHom ⊓ Subgroup.centralizer ({φ p} : Set G')) := by
  rw [pPrimeCoreOf_map_equiv, Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective,
    centralizer_map_equiv]

theorem map_map_symm {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (K : Subgroup G) :
    (K.map φ.toMonoidHom).map φ.symm.toMonoidHom = K := by
  ext x
  rw [Subgroup.mem_map_equiv, Subgroup.mem_map_equiv]
  simp

theorem core_map_eq {φ : X ≃* GM} {P Y : Subgroup X} {j : ℕ} (hj : j < 2)
    (hPφ : P.map φ.toMonoidHom = AG j) (hc : ∀ x, x ∈ Subgroup.center X ↔ φ x ∈ zpowers zG)
    {p : X} (hp : p ∈ P) (hpz : p ∉ Subgroup.center X) :
    ∃ l < 4, (pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p} : Set X))).map φ.toMonoidHom =
      core j (Y.map φ.toMonoidHom) l ∧
      Subgroup.centralizer ({φ p} : Set GM) = Subgroup.centralizer ({mL j l} : Set GM) := by
  have hap : φ p ∈ AG j := by rw [← hPφ]; exact ⟨p, hp, rfl⟩
  have hapz : φ p ∉ zpowers zG := fun h => hpz ((hc p).2 h)
  obtain ⟨l, hl, hcl⟩ := centralizer_AG hj hap hapz
  refine ⟨l, hl, ?_, hcl⟩
  rw [map_pPrimeCore_inf_centralizer, hcl]
  rfl

theorem core_le_map {φ : X ≃* GM} {P Y : Subgroup X} {j : ℕ} (hj : j < 2)
    (hPφ : P.map φ.toMonoidHom = AG j) (hc : ∀ x, x ∈ Subgroup.center X ↔ φ x ∈ zpowers zG)
    {l : ℕ} (hl : l < 4) :
    core j (Y.map φ.toMonoidHom) l ≤ (coreSup P Y).map φ.toMonoidHom := by
  have hmP : mL j l ∈ AG j := mL_mem_AG hj hl
  rw [← hPφ] at hmP
  obtain ⟨p₀, hp₀, hp₀e⟩ := hmP
  have hp₀e' : φ p₀ = mL j l := hp₀e
  have hz : p₀ ∉ Subgroup.center X := fun h =>
    mL_not_mem_zpowers hj hl (by rw [← hp₀e']; exact (hc p₀).1 h)
  have e : core j (Y.map φ.toMonoidHom) l =
      (pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p₀} : Set X))).map φ.toMonoidHom := by
    rw [map_pPrimeCore_inf_centralizer, hp₀e']
    rfl
  rw [e]
  exact Subgroup.map_mono (le_iSup_of_le p₀ (le_iSup_of_le hp₀ (le_iSup_of_le hz le_rfl)))

theorem map_coreSup {φ : X ≃* GM} {P Y : Subgroup X} {j : ℕ} (hj : j < 2)
    (hPφ : P.map φ.toMonoidHom = AG j) (hc : ∀ x, x ∈ Subgroup.center X ↔ φ x ∈ zpowers zG) :
    (coreSup P Y).map φ.toMonoidHom = ⨆ ℓ : Fin 4, core j (Y.map φ.toMonoidHom) ℓ := by
  apply le_antisymm
  · rw [Subgroup.map_le_iff_le_comap]
    refine iSup_le fun p => iSup_le fun hp => iSup_le fun hpz => ?_
    obtain ⟨l, hl, he, -⟩ := core_map_eq (Y := Y) hj hPφ hc hp hpz
    rw [← Subgroup.map_le_iff_le_comap, he]
    exact le_iSup (fun ℓ : Fin 4 => core j (Y.map φ.toMonoidHom) ℓ) ⟨l, hl⟩
  · exact iSup_le fun ℓ => core_le_map (Y := Y) hj hPφ hc ℓ.2

end Transport

theorem coreSup_mem_of_twoLines {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hT : Sec4.IsTripleCover X CFSG.Blueprint.NativeSporadic.ON) {P Y : Subgroup X}
    (hP : Late.IsE27 P) (hPY : P ≤ Subgroup.normalizer (Y : Set X))
    (hov : L37OvergroupTransfer) (htwo : TwoLines P Y) :
    coreSup P Y ∈ thetaComponentsIn Y ∧ Nat.card (coreSup P Y) = 1876896 := by
  obtain ⟨ψ⟩ := Sec13.ON134.nonempty_equiv_model hperf hT
  have hP' := Sec13.ON134.isE27_map hP ψ.toMonoidHom ψ.injective
  obtain ⟨h, j, hj, hPj⟩ := exists_conj_AG hP'
  let φ : X ≃* GM := ψ.trans (MulAut.conj h)
  have hPφ : P.map φ.toMonoidHom = AG j := by
    rw [← hPj, Subgroup.map_map]
    rfl
  have hc : ∀ x, x ∈ Subgroup.center X ↔ φ x ∈ zpowers zG := fun x => by
    rw [← center_GM]
    exact (MulEquivClass.apply_mem_center_iff φ).symm
  have hYnorm : AG j ≤ Subgroup.normalizer ((Y.map φ.toMonoidHom : Subgroup GM) : Set GM) := by
    intro a ha
    rw [← hPφ] at ha
    obtain ⟨p0, hp0, rfl⟩ := ha
    change φ p0 ∈ Subgroup.normalizer ((Y.map φ.toMonoidHom : Subgroup GM) : Set GM)
    rw [Subgroup.mem_normalizer_iff]
    intro y'
    obtain ⟨y, rfl⟩ := φ.surjective y'
    have h1 : φ y ∈ Y.map φ.toMonoidHom ↔ y ∈ Y := by
      rw [Subgroup.mem_map_equiv]; simp
    have h2 : φ p0 * φ y * (φ p0)⁻¹ ∈ Y.map φ.toMonoidHom ↔ p0 * y * p0⁻¹ ∈ Y := by
      rw [← map_inv, ← map_mul, ← map_mul, Subgroup.mem_map_equiv]; simp
    rw [h1, h2]
    exact Subgroup.mem_normalizer_iff.1 (hPY hp0) y
  have hmap := map_coreSup (Y := Y) hj hPφ hc
  have key : ∀ a b : ℕ, a < b → b < 4 → core j (Y.map φ.toMonoidHom) a ≠ ⊥ →
      core j (Y.map φ.toMonoidHom) b ≠ ⊥ →
      coreSup P Y ∈ thetaComponentsIn Y ∧ Nat.card (coreSup P Y) = 1876896 := by
    intro a b hab hb hva hvb
    obtain ⟨hmem, hcard⟩ := tuple_mem_thetaComponentsIn hj hYnorm hab hb hva hvb
      (hov j hj _ hYnorm a b hab hb hva hvb)
    rw [← hmap] at hmem hcard
    refine ⟨?_, ?_⟩
    · have := map_mem_thetaComponentsIn φ.symm hmem
      rwa [map_map_symm, map_map_symm] at this
    · rwa [Subgroup.card_map_of_injective φ.injective] at hcard
  obtain ⟨p, hp, q, hq, hpz, hqz, hne, hcp, hcq⟩ := htwo
  obtain ⟨l₁, hl₁, he₁, hC₁⟩ := core_map_eq (Y := Y) hj hPφ hc hp hpz
  obtain ⟨l₂, hl₂, he₂, hC₂⟩ := core_map_eq (Y := Y) hj hPφ hc hq hqz
  have hv₁ : core j (Y.map φ.toMonoidHom) l₁ ≠ ⊥ := by
    rw [← he₁]
    exact fun h0 => hcp ((Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h0)
  have hv₂ : core j (Y.map φ.toMonoidHom) l₂ ≠ ⊥ := by
    rw [← he₂]
    exact fun h0 => hcq ((Subgroup.map_eq_bot_iff_of_injective _ φ.injective).1 h0)
  have hl : l₁ ≠ l₂ := by
    rintro rfl
    apply hne
    have h3 : Subgroup.centralizer ({φ p} : Set GM) = Subgroup.centralizer ({φ q} : Set GM) :=
      hC₁.trans hC₂.symm
    rw [← centralizer_map_equiv, ← centralizer_map_equiv] at h3
    exact Subgroup.map_injective φ.injective h3
  rcases lt_or_gt_of_ne hl with h | h
  · exact key l₁ l₂ h hl₂ hv₁ hv₂
  · exact key l₂ l₁ h hl₁ hv₂ hv₁

theorem l37OvergroupTransfer_of_lSub
    (h : ∀ j < 2, ∀ k < 9, ∀ Y : Subgroup GM, LSub j k ≤ Y →
      Y ≤ Subgroup.normalizer (LSub j k : Set GM) ∨ Y = ⊤) :
    L37OvergroupTransfer := by
  intro j hj Y hY l₁ l₂ hl h₂ hv₁ hv₂
  obtain ⟨⟨k, hk, hT⟩, -⟩ := tuple_eq_L37 hj hY hl h₂ hv₁ hv₂
  have hTY : (⨆ ℓ : Fin 4, core j Y ℓ : Subgroup GM) ≤ Y :=
    iSup_le fun ℓ => core_le_left j Y ℓ
  rw [hT] at hTY ⊢
  exact h j hj k hk Y hTY

end Model

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.UniversalCoverMonster.PointSig

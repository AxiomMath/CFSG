module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenCores
public import CFSG.RankThree.PartTwo.Sec13.Item134ONProof

public noncomputable section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

attribute [local irreducible] dotProduct

open CFSG.ONSchreier CFSG.ONSchreier.Native CFSG.RankThree.Native.ONTriple Subgroup
open CFSG.GH74.GLS (pPrimeCoreOf)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)
open CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13

@[expose] def coreSub {X : Type*} [Group X] (Y P : Subgroup X) : Subgroup X :=
  ⨆ (p : X) (_ : p ∈ P) (_ : p ∉ Subgroup.center X),
    pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({p} : Set X))

theorem coreSub_le {X : Type*} [Group X] (Y P : Subgroup X) : coreSub Y P ≤ Y :=
  iSup_le fun _ => iSup_le fun _ => iSup_le fun _ =>
    (Subgroup.map_subtype_le _).trans inf_le_left

theorem comm_of_sq_eq_one {G : Type*} [Group G] {a b : G} (ha : a ^ 2 = 1) (hb : b ^ 2 = 1)
    (hab : (a * b) ^ 2 = 1) : a * b = b * a := by
  have h1 : a⁻¹ = a := by rw [inv_eq_iff_mul_eq_one, ← sq]; exact ha
  have h2 : b⁻¹ = b := by rw [inv_eq_iff_mul_eq_one, ← sq]; exact hb
  have h3 : (a * b)⁻¹ = a * b := by rw [inv_eq_iff_mul_eq_one, ← sq]; exact hab
  calc a * b = (a * b)⁻¹ := h3.symm
    _ = b⁻¹ * a⁻¹ := mul_inv_rev a b
    _ = b * a := by rw [h1, h2]

theorem pPrimeCoreOf_map_equiv {G G' : Type*} [Group G] [Group G'] (p : ℕ) (e : G ≃* G')
    (K : Subgroup G) :
    (pPrimeCoreOf p K).map e.toMonoidHom = pPrimeCoreOf p (K.map e.toMonoidHom) := by
  unfold pPrimeCoreOf
  let ψ : ↥K ≃* ↥(K.map e.toMonoidHom) := e.subgroupMap K
  rw [← CFSG.pPrimeCore_map_iso p ψ, Subgroup.map_map, Subgroup.map_map]
  congr 1

section Abstract

set_option linter.unusedSectionVars false


theorem inL_decomp' : ∀ j < 2, ∀ v : Fin 4 → ZMod 3, inL j v →
    v = (v 0).val • (Pi.single 0 1 : Fin 4 → ZMod 3) + (v 1).val • yv j := by
  decide +kernel

theorem centralizer_AG {j : ℕ} (hj : j < 2) {a : GM} (ha : a ∈ AG j) (haz : a ∉ zpowers zG) :
    ∃ l < 4, centralizer {a} = centralizer {mL j l} := by
  obtain ⟨hP, hin⟩ := mem_AG.1 ha
  set v := relG.coord ⟨a, hP⟩ with hv
  have hdec := inL_decomp' j hj v hin
  set p : Multiplicative (ZMod 3 × ZMod 3) := Multiplicative.ofAdd (v 0, v 1) with hp
  have hce := coord_eHom hj p
  have hcoord : relG.coord ⟨eHom j hj p, eHom_mem_P0 hj p⟩ = relG.coord ⟨a, hP⟩ := by
    rw [hce, ← hv]
    simp only [hp, toAdd_ofAdd]
    exact hdec.symm
  obtain ⟨c, hc⟩ := eq_mul_zpow_of_coord hP (eHom_mem_P0 hj p) hcoord.symm
  have hne : (⟨eHom j hj p, ⟨p, rfl⟩⟩ : EG j hj) ≠ 1 := by
    intro h1
    have h2 : eHom j hj p = 1 := congrArg Subtype.val h1
    apply haz
    rw [hc, h2, one_mul]
    simp
  obtain ⟨l, hl, hcl⟩ := centralizer_EG hj ⟨eHom j hj p, ⟨p, rfl⟩⟩ hne
  refine ⟨l, hl, ?_⟩
  rw [hc, centralizer_mul_zpow]
  exact hcl

theorem centralizer_map_equiv {G G' : Type*} [Group G] [Group G'] (φ : G ≃* G') (g : G) :
    (centralizer ({g} : Set G)).map φ.toMonoidHom = centralizer ({φ g} : Set G') := by
  ext x
  simp only [Subgroup.mem_map_equiv, mem_centralizer_singleton_iff]
  constructor
  · intro h
    have := congrArg φ h
    simpa [map_mul] using this
  · intro h
    apply φ.injective
    simpa [map_mul] using h

theorem uL_ne_zero : ∀ j < 2, ∀ l < 4, uL j l ≠ 0 := by decide +kernel

theorem mL_not_mem_zpowers {j : ℕ} (hj : j < 2) {l : ℕ} (hl : l < 4) : mL j l ∉ zpowers zG := by
  intro h
  have h0 := (relG.coord_eq_zero_iff ⟨mL j l, mL_mem_P0 hj hl⟩).2 h
  rw [coord_mL hj hl] at h0
  exact uL_ne_zero j hj l hl h0

theorem tuple_comm {j : ℕ} (hj : j < 2) {Y : Subgroup GM} (hY : AG j ≤ normalizer (Y : Set GM))
    (hex : ¬ ∃ l₁ l₂ : ℕ, l₁ < l₂ ∧ l₂ < 4 ∧ core j Y l₁ ≠ ⊥ ∧ core j Y l₂ ≠ ⊥) :
    ∀ a b : GM, a ∈ (⨆ ℓ : Fin 4, core j Y ℓ) → b ∈ (⨆ ℓ : Fin 4, core j Y ℓ) →
      a * b = b * a := by
  push Not at hex
  by_cases hl : ∃ l < 4, core j Y l ≠ ⊥
  · obtain ⟨l0, hl0, hne⟩ := hl
    obtain ⟨m, hm, hX⟩ := (core_cases hj hl0 hY).resolve_left hne
    have hTle : (⨆ ℓ : Fin 4, core j Y ℓ) ≤ XG j l0 m hj hm := by
      refine iSup_le fun ℓ => ?_
      by_cases hℓ : (ℓ : ℕ) = l0
      · rw [hℓ, hX]
      · have : core j Y ℓ = ⊥ := by
          by_contra hc
          rcases Nat.lt_or_gt_of_ne hℓ with h | h
          · exact hne (hex ℓ l0 h hl0 hc)
          · exact hc (hex l0 ℓ h ℓ.2 hne)
        rw [this]
        exact bot_le
    intro a b ha hb
    have hsq : ∀ g ∈ XG j l0 m hj hm, g ^ 2 = 1 := fun g hg => XG_sq hg
    exact comm_of_sq_eq_one (hsq a (hTle ha)) (hsq b (hTle hb))
      (hsq (a * b) (hTle (mul_mem ha hb)))
  · push Not at hl
    have : (⨆ ℓ : Fin 4, core j Y ℓ) = ⊥ := le_bot_iff.1 (iSup_le fun ℓ => (hl ℓ ℓ.2).le)
    intro a b ha hb
    rw [this, mem_bot] at ha hb
    subst ha hb
    simp

theorem coreSub_dichotomy {X : Type} [Group X] [Finite X] (hperf : Group.IsPerfect X)
    (hT : Sec4.IsTripleCover X Blueprint.NativeSporadic.ON) {P Y : Subgroup X}
    (hP : Late.IsE27 P) (hPY : P ≤ normalizer (Y : Set X)) :
    (∀ a ∈ coreSub Y P, ∀ b ∈ coreSub Y P, a * b = b * a) ∨
      (Nat.card ↥(coreSub Y P) = 1876896 ∧ ∃ _ : Fact (Nat.Prime 7),
        Nonempty (↥(coreSub Y P) ⧸ aschbacherSolvableCore 3 ↥(coreSub Y P) ≃*
          CFSG.Assembly.RankThreeEven.projSL 3 (GaloisField 7 1))) := by
  obtain ⟨ψ⟩ := ON134.nonempty_equiv_model hperf hT
  have hP' := ON134.isE27_map hP ψ.toMonoidHom ψ.injective
  obtain ⟨h, j, hj, hPj⟩ := exists_conj_AG hP'
  let φ : X ≃* GM := ψ.trans (MulAut.conj h)
  have hφ : ∀ x, φ x = h * ψ x * h⁻¹ := fun x => by simp [φ, MulAut.conj_apply]
  have hPφ : P.map φ.toMonoidHom = AG j := by
    rw [← hPj, Subgroup.map_map]
    rfl
  have hcenter : ∀ x : X, x ∈ center X ↔ φ x ∈ zpowers zG := by
    intro x
    rw [ON134.mem_center_iff_model ψ]
    have hc : (MulAut.conj h).toMonoidHom zG = zG := conj_zG h
    have hc' : (MulAut.conj h⁻¹).toMonoidHom zG = zG := conj_zG h⁻¹
    constructor
    · intro hx
      have hm : (MulAut.conj h).toMonoidHom (ψ x) ∈
          (zpowers zG).map (MulAut.conj h).toMonoidHom := ⟨ψ x, hx, rfl⟩
      rw [MonoidHom.map_zpowers, hc] at hm
      exact hm
    · intro hx
      have hm : (MulAut.conj h⁻¹).toMonoidHom (φ x) ∈
          (zpowers zG).map (MulAut.conj h⁻¹).toMonoidHom := ⟨φ x, hx, rfl⟩
      rw [MonoidHom.map_zpowers, hc'] at hm
      have e : (MulAut.conj h⁻¹).toMonoidHom (φ x) = ψ x := by
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, hφ]
        group
      rwa [e] at hm
  set Y' : Subgroup GM := Y.map φ.toMonoidHom with hY'
  have hY'norm : AG j ≤ normalizer (Y' : Set GM) := by
    intro a ha
    rw [← hPφ] at ha
    obtain ⟨p0, hp0, rfl⟩ := ha
    change φ p0 ∈ normalizer (Y' : Set GM)
    rw [mem_normalizer_iff]
    intro y'
    obtain ⟨y, rfl⟩ := φ.surjective y'
    have h1 : φ y ∈ Y' ↔ y ∈ Y := by
      rw [hY', Subgroup.mem_map_equiv]; simp
    have h2 : φ p0 * φ y * (φ p0)⁻¹ ∈ Y' ↔ p0 * y * p0⁻¹ ∈ Y := by
      rw [← map_inv, ← map_mul, ← map_mul, hY', Subgroup.mem_map_equiv]; simp
    rw [h1, h2]
    exact mem_normalizer_iff.1 (hPY hp0) y
  set T' : Subgroup GM := ⨆ ℓ : Fin 4, core j Y' ℓ with hT'
  have hcore : ∀ p : X, p ∈ P → ∀ l < 4, centralizer ({φ p} : Set GM) = centralizer {mL j l} →
      (pPrimeCoreOf 3 (Y ⊓ centralizer ({p} : Set X))).map φ.toMonoidHom = core j Y' l := by
    intro p _ l _ hcl
    rw [pPrimeCoreOf_map_equiv, Subgroup.map_inf_eq _ _ φ.toMonoidHom φ.injective,
      centralizer_map_equiv, hcl]
    rfl
  have hkey : (coreSub Y P).map φ.toMonoidHom = T' := by
    apply le_antisymm
    · rw [Subgroup.map_le_iff_le_comap]
      refine iSup_le fun p => iSup_le fun hpP => iSup_le fun hpz => ?_
      have hap : φ p ∈ AG j := by rw [← hPφ]; exact ⟨p, hpP, rfl⟩
      have hapz : φ p ∉ zpowers zG := fun hz => hpz ((hcenter p).2 hz)
      obtain ⟨l, hl, hcl⟩ := centralizer_AG hj hap hapz
      intro x hx
      have hmem : φ x ∈ (pPrimeCoreOf 3 (Y ⊓ centralizer ({p} : Set X))).map φ.toMonoidHom :=
        ⟨x, hx, rfl⟩
      rw [hcore p hpP l hl hcl] at hmem
      exact le_iSup (fun ℓ : Fin 4 => core j Y' ℓ) ⟨l, hl⟩ hmem
    · refine iSup_le fun ℓ => ?_
      have hmL : mL j ℓ ∈ AG j := mL_mem_AG hj ℓ.2
      rw [← hPφ] at hmL
      obtain ⟨p, hpP, hp⟩ := hmL
      have hpz : p ∉ center X := by
        intro hc
        have := (hcenter p).1 hc
        rw [show φ p = mL j ℓ from hp] at this
        exact mL_not_mem_zpowers hj ℓ.2 this
      have hle : (pPrimeCoreOf 3 (Y ⊓ centralizer ({p} : Set X))).map φ.toMonoidHom ≤
          (coreSub Y P).map φ.toMonoidHom :=
        Subgroup.map_mono (le_iSup₂_of_le p hpP (le_iSup_of_le hpz le_rfl))
      rw [hcore p hpP ℓ ℓ.2 (by rw [show φ p = mL j ℓ from hp])] at hle
      exact hle
  by_cases hex : ∃ l₁ l₂ : ℕ, l₁ < l₂ ∧ l₂ < 4 ∧ core j Y' l₁ ≠ ⊥ ∧ core j Y' l₂ ≠ ⊥
  · right
    obtain ⟨l₁, l₂, hl, h₂, hv₁, hv₂⟩ := hex
    obtain ⟨hcard, hFact, ⟨e⟩⟩ := tuple_L37 hj hY'norm hl h₂ hv₁ hv₂
    let eT : ↥(coreSub Y P) ≃* ↥T' :=
      (Subgroup.equivMapOfInjective (coreSub Y P) φ.toMonoidHom φ.injective).trans
        (MulEquiv.subgroupCongr hkey)
    refine ⟨by rw [Nat.card_congr eT.toEquiv]; exact hcard, hFact, ?_⟩
    have hmap := CFSG.RankThree.aschbacherSolvableCore_map_mulEquiv Nat.prime_three eT
    exact ⟨(QuotientGroup.congr (aschbacherSolvableCore 3 ↥(coreSub Y P))
      (aschbacherSolvableCore 3 ↥T') eT hmap).trans e⟩
  · left
    intro a ha b hb
    apply φ.injective
    rw [map_mul, map_mul]
    have haT : φ a ∈ T' := hkey ▸ ⟨a, ha, rfl⟩
    have hbT : φ b ∈ T' := hkey ▸ ⟨b, hb, rfl⟩
    exact tuple_comm hj hY'norm hex _ _ haT hbT

end Abstract

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven

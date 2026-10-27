module

public import CFSG.Timmesfeld.ARS.CaseHBasic
public import CFSG.Timmesfeld.ARS.CaseBChain

set_option linter.unusedSectionVars false

public section

namespace CFSG.RankThree.PartOne.D4RC

open scoped commutatorElement
open CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def rccOrbit (Γ A₀ : Subgroup G) : Set (Subgroup G) :=
  {A | ∃ g ∈ Γ, conjSub A₀ g = A}

theorem rccOrbit_eq_range (Γ A₀ : Subgroup G) :
    rccOrbit Γ A₀ = Set.range (fun g : ↥Γ => conjSub A₀ (g : G)) := by
  ext A
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨⟨g, hg⟩, rfl⟩
  · rintro ⟨g, rfl⟩
    exact ⟨g, g.2, rfl⟩

theorem rccOrbit_self {Γ : Subgroup G} (A₀ : Subgroup G) : A₀ ∈ rccOrbit Γ A₀ :=
  ⟨1, Γ.one_mem, conjSub_one A₀⟩

theorem rccOrbit_conj {Γ A₀ A : Subgroup G} (hA : A ∈ rccOrbit Γ A₀) {g : G} (hg : g ∈ Γ) :
    conjSub A g ∈ rccOrbit Γ A₀ := by
  obtain ⟨x, hx, rfl⟩ := hA
  exact ⟨g * x, Γ.mul_mem hg hx, conjSub_mul A₀ g x⟩

theorem rccOrbit_le {Γ A₀ A : Subgroup G} (hA₀ : A₀ ≤ Γ) (hA : A ∈ rccOrbit Γ A₀) : A ≤ Γ := by
  obtain ⟨x, hx, rfl⟩ := hA
  exact conjSub_le hA₀ hx

theorem rccOrbit_subset (hR : IsRootClass R) {Γ A₀ : Subgroup G} (hA₀ : A₀ ∈ R) :
    rccOrbit Γ A₀ ⊆ R := by
  rintro _ ⟨x, -, rfl⟩
  exact hR.conjSub_mem hA₀ x

theorem rcc_conjSub_conjSub_inv (H : Subgroup G) (g : G) : conjSub (conjSub H g) g⁻¹ = H := by
  rw [← conjSub_mul, inv_mul_cancel, conjSub_one]

theorem rcc_conjSub_sup (H K : Subgroup G) (g : G) :
    conjSub (H ⊔ K) g = conjSub H g ⊔ conjSub K g :=
  Subgroup.map_sup _ _ _

theorem rcc_opposite_of_off_line (h : Hyp G R) (hH : SigmaEqLambda R) {A B A'' : Subgroup G}
    (hA : A ∈ R) (hB : B ∈ R) (hs : Special R A B) (hA'' : A'' ∈ lambdaSet R B)
    (hoff : ¬ A'' ≤ B ⊔ ⁅A, B⁆) : Opposite A'' A := by
  have hR := h.root
  have hA''R : A'' ∈ R := hA''.1.1
  obtain ⟨hMA, hMB⟩ := CaseH.commutator_mem_lambdaSet h hA hB hs
  have hBM : B ∈ lambdaSet R ⁅A, B⁆ := mem_lambdaSet_comm hB hMB
  have hAne : A ≠ A'' := by
    rintro rfl
    exact hs.not_commuting hR hA''.1.2.2.symm
  rcases hR.rel A hA A'' hA''R hAne with hc | hop | hs'
  · exfalso
    have hA''A : A'' ∈ lambdaSet R A := CaseH.mem_lambdaSet_of_commuting hH hA hA''R hAne.symm hc
    refine CaseH.false_of_quadrangle h hH (A := A) (B := ⁅A, B⁆) (C := B) (D := A'') hA hMA hBM
      hA'' (mem_lambdaSet_comm hA hA''A) (fun hBA => hs.not_commuting hR hBA.1.2.2)
      (hs.ne hR hA).symm ?_
    rintro rfl
    exact hoff le_sup_right
  · exact hop.symm
  · exfalso
    obtain ⟨hNA, hNA''⟩ := CaseH.commutator_mem_lambdaSet h hA hA''R hs'
    refine CaseH.false_of_pentagon h hH (A := A) (B := ⁅A, B⁆) (C := B) (D := A'')
      (E := ⁅A, A''⁆) hA hMA hBM hA'' hNA'' (mem_lambdaSet_comm hA hNA)
      (fun hBA => hs.not_commuting hR hBA.1.2.2) (hs.ne hR hA).symm
      (fun hDA => hs'.not_commuting hR hDA.1.2.2) hAne.symm ?_
    intro hMN
    apply hoff
    refine CaseH.le_line h hH hB hMB hB le_sup_left hs.1 le_sup_right hBM.1.2.1 hA''R
      hA''.1.2.2.symm ?_
    rw [hMN]
    exact hNA''.1.2.2

theorem rcc_commutator_mem (h : Hyp G R) (hH : SigmaEqLambda R) {Γ : Subgroup G}
    {R₀ : Set (Subgroup G)} (hsub : R₀ ⊆ R) (hle : ∀ A ∈ R₀, A ≤ Γ)
    (hinv : ∀ A ∈ R₀, ∀ g ∈ Γ, conjSub A g ∈ R₀) {A B : Subgroup G} (hA : A ∈ R₀)
    (hB : B ∈ R₀) (hs : Special R A B)
    (hoff : ∃ A'' ∈ R₀, A'' ∈ lambdaSet R B ∧ ¬ A'' ≤ B ⊔ ⁅A, B⁆) : ⁅A, B⁆ ∈ R₀ := by
  have := h.finite
  obtain ⟨A'', hA''₀, hA''B, hoff⟩ := hoff
  have hAR := hsub hA
  have hBR := hsub hB
  have hA''R := hsub hA''₀
  have hop := rcc_opposite_of_off_line h hH hAR hBR hs hA''B hoff
  obtain ⟨-, -, -, w, -, -, hw, hwA'', -⟩ := Sec5.exists_swap h.root hA''R hAR hop
  have hBw : conjSub B w = ⁅A, B⁆ :=
    CaseB.conjSub_eq_commutator_of_swap h.root h.noIsolated hA''R hAR hop
      (mem_lambdaSet_comm hBR hA''B) ⟨hBR, hs⟩ hw hwA''
  rw [← hBw]
  exact hinv B hB w (sup_le (hle A'' hA''₀) (hle A hA) hw)

theorem rcc_closure (h : Hyp G R) (hH : SigmaEqLambda R) {Γ : Subgroup G}
    {R₀ : Set (Subgroup G)} (hsub : R₀ ⊆ R) (hle : ∀ A ∈ R₀, A ≤ Γ)
    (hinv : ∀ A ∈ R₀, ∀ g ∈ Γ, conjSub A g ∈ R₀)
    (hoff : ∀ B ∈ R₀, ∀ M ∈ lambdaSet R B, ∃ A'' ∈ R₀, A'' ∈ lambdaSet R B ∧ ¬ A'' ≤ B ⊔ M)
    {A B : Subgroup G} (hA : A ∈ R₀) (hB : B ∈ R₀) (hs : Special R A B) : ⁅A, B⁆ ∈ R₀ :=
  rcc_commutator_mem h hH hsub hle hinv hA hB hs
    (hoff B hB _ (CaseH.commutator_mem_lambdaSet h (hsub hA) (hsub hB) hs).2)

theorem rcc_off_line_orbit (h : Hyp G R) {Γ A₀ : Subgroup G}
    (hoff : ∀ M ∈ lambdaSet R A₀,
      ∃ A'' ∈ rccOrbit Γ A₀, A'' ∈ lambdaSet R A₀ ∧ ¬ A'' ≤ A₀ ⊔ M) :
    ∀ B ∈ rccOrbit Γ A₀, ∀ M ∈ lambdaSet R B,
      ∃ A'' ∈ rccOrbit Γ A₀, A'' ∈ lambdaSet R B ∧ ¬ A'' ≤ B ⊔ M := by
  rintro _ ⟨g, hg, rfl⟩ M hM
  have hM' : conjSub M g⁻¹ ∈ lambdaSet R A₀ := by
    have := conjSub_mem_lambdaSet h.root hM g⁻¹
    rwa [rcc_conjSub_conjSub_inv] at this
  obtain ⟨A'', hA''o, hA''Λ, hA''off⟩ := hoff _ hM'
  refine ⟨conjSub A'' g, rccOrbit_conj hA''o hg, conjSub_mem_lambdaSet h.root hA''Λ g,
    fun hle => hA''off ?_⟩
  have := Subgroup.map_mono (f := (MulAut.conj g⁻¹).toMonoidHom) hle
  change conjSub (conjSub A'' g) g⁻¹ ≤ conjSub (conjSub A₀ g ⊔ M) g⁻¹ at this
  rwa [rcc_conjSub_conjSub_inv, rcc_conjSub_sup, rcc_conjSub_conjSub_inv] at this

theorem rcc_closure_orbit (h : Hyp G R) (hH : SigmaEqLambda R) {Γ A₀ : Subgroup G}
    (hA₀ : A₀ ∈ R) (hΓ : A₀ ≤ Γ)
    (hoff : ∀ M ∈ lambdaSet R A₀,
      ∃ A'' ∈ rccOrbit Γ A₀, A'' ∈ lambdaSet R A₀ ∧ ¬ A'' ≤ A₀ ⊔ M)
    {A B : Subgroup G} (hA : A ∈ rccOrbit Γ A₀) (hB : B ∈ rccOrbit Γ A₀)
    (hs : Special R A B) : ⁅A, B⁆ ∈ rccOrbit Γ A₀ :=
  rcc_closure h hH (rccOrbit_subset h.root hA₀) (fun _ hA => rccOrbit_le hΓ hA)
    (fun _ hA _ hg => rccOrbit_conj hA hg) (rcc_off_line_orbit h hoff) hA hB hs

theorem rcc_off_line_of_two (h : Hyp G R) {R₀ : Set (Subgroup G)} {B A₁ A₂ : Subgroup G}
    (hB : B ∈ R) (hA₁ : A₁ ∈ R₀) (hA₂ : A₂ ∈ R₀) (h₁ : A₁ ∈ lambdaSet R B)
    (h₂ : A₂ ∈ lambdaSet R B) (hne : ¬ A₂ ≤ B ⊔ A₁) :
    ∀ M ∈ lambdaSet R B, ∃ A'' ∈ R₀, A'' ∈ lambdaSet R B ∧ ¬ A'' ≤ B ⊔ M := by
  intro M hM
  by_cases hA₁M : A₁ ≤ B ⊔ M
  · refine ⟨A₂, hA₂, h₂, fun hle => hne ?_⟩
    have hline : B ⊔ A₁ = B ⊔ M :=
      CaseH.eq_of_le_of_le h hB h₁ hB hM hB h₁.1.1 h₁.1.2.1.symm le_sup_left le_sup_right
        le_sup_left hA₁M
    rwa [hline]
  · exact ⟨A₁, hA₁, h₁, hA₁M⟩

theorem rcc_off_line_of_special (h : Hyp G R) {Γ : Subgroup G} {R₀ : Set (Subgroup G)}
    (hsub : R₀ ⊆ R) (hle : ∀ A ∈ R₀, A ≤ Γ) (hinv : ∀ A ∈ R₀, ∀ g ∈ Γ, conjSub A g ∈ R₀)
    {A B : Subgroup G} (hA : A ∈ R₀) (hB : B ∈ R₀) (hs : Special R A B) {y : G} (hy : y ∈ Γ)
    (hyB : conjSub B y = B) (hyL : conjSub (B ⊔ ⁅A, B⁆) y ≠ B ⊔ ⁅A, B⁆) :
    ∀ M ∈ lambdaSet R B, ∃ A'' ∈ R₀, A'' ∈ lambdaSet R B ∧ ¬ A'' ≤ B ⊔ M := by
  intro M hM
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hAR := hsub hA
  have hBR := hsub hB
  obtain ⟨-, hMB⟩ := CaseH.commutator_mem_lambdaSet h hAR hBR hs
  obtain ⟨a, haA, ha1⟩ := hR.exists_ne_one hAR
  have hCR₀ : conjSub B a ∈ R₀ := hinv B hB a (hle A hA haA)
  have hCB : conjSub B a ≠ B := Sec3.conjSub_ne_of_special hR hiso hAR hBR hs haA ha1
  have hCL : conjSub B a ≤ B ⊔ ⁅A, B⁆ := by
    have := conjSub_le_commutator_sup (A := B) (B := A) haA
    rwa [Subgroup.commutator_comm, sup_comm] at this
  have hCΛ : conjSub B a ∈ lambdaSet R B :=
    (mem_lambdaSet_of_le_sup hR hiso hBR hMB hBR le_sup_left (hsub hCR₀) hCL hCB.symm).1
  have hC'R₀ : conjSub (conjSub B a) y ∈ R₀ := hinv _ hCR₀ y hy
  have hC'B : conjSub (conjSub B a) y ≠ B := by
    intro e
    apply hCB
    exact CFSG.Timmesfeld.RankOne.map_conj_inj.1 (e.trans hyB.symm)
  have hC'Λ : conjSub (conjSub B a) y ∈ lambdaSet R B := by
    have := conjSub_mem_lambdaSet hR hCΛ y
    rwa [hyB] at this
  by_cases hline : B ⊔ M = B ⊔ ⁅A, B⁆
  · refine ⟨conjSub (conjSub B a) y, hC'R₀, hC'Λ, fun hle' => hyL ?_⟩
    rw [hline] at hle'
    have hMy : conjSub ⁅A, B⁆ y ∈ lambdaSet R B := by
      have := conjSub_mem_lambdaSet hR hMB y
      rwa [hyB] at this
    have hLy : conjSub (B ⊔ ⁅A, B⁆) y = B ⊔ conjSub ⁅A, B⁆ y := by
      rw [rcc_conjSub_sup, hyB]
    have hC'y : conjSub (conjSub B a) y ≤ B ⊔ conjSub ⁅A, B⁆ y := by
      rw [← hLy]
      exact Subgroup.map_mono hCL
    have hL := CaseH.eq_of_le_of_le h hBR hMB hBR hMy hBR (hsub hC'R₀) hC'B.symm le_sup_left
      hle' le_sup_left hC'y
    rw [hLy]
    exact hL.symm
  · refine ⟨conjSub B a, hCR₀, hCΛ, fun hle' => hline ?_⟩
    exact CaseH.eq_of_le_of_le h hBR hM hBR hMB hBR (hsub hCR₀) hCB.symm le_sup_left hle'
      le_sup_left hCL

theorem rcc_closure_of_two (h : Hyp G R) (hH : SigmaEqLambda R) {Γ A₀ A₁ A₂ : Subgroup G}
    (hA₀ : A₀ ∈ R) (hΓ : A₀ ≤ Γ) (hA₁ : A₁ ∈ rccOrbit Γ A₀) (hA₂ : A₂ ∈ rccOrbit Γ A₀)
    (h₁ : A₁ ∈ lambdaSet R A₀) (h₂ : A₂ ∈ lambdaSet R A₀) (hne : ¬ A₂ ≤ A₀ ⊔ A₁)
    {A B : Subgroup G} (hA : A ∈ rccOrbit Γ A₀) (hB : B ∈ rccOrbit Γ A₀)
    (hs : Special R A B) : ⁅A, B⁆ ∈ rccOrbit Γ A₀ :=
  rcc_closure_orbit h hH hA₀ hΓ (rcc_off_line_of_two h hA₀ hA₁ hA₂ h₁ h₂ hne) hA hB hs

theorem rcc_closure_of_special (h : Hyp G R) (hH : SigmaEqLambda R) {Γ A₀ A₁ : Subgroup G}
    {y : G} (hA₀ : A₀ ∈ R) (hΓ : A₀ ≤ Γ) (hA₁ : A₁ ∈ rccOrbit Γ A₀) (hs₁ : Special R A₁ A₀)
    (hy : y ∈ Γ) (hyA : conjSub A₀ y = A₀)
    (hyL : conjSub (A₀ ⊔ ⁅A₁, A₀⁆) y ≠ A₀ ⊔ ⁅A₁, A₀⁆) {A B : Subgroup G}
    (hA : A ∈ rccOrbit Γ A₀) (hB : B ∈ rccOrbit Γ A₀) (hs : Special R A B) :
    ⁅A, B⁆ ∈ rccOrbit Γ A₀ :=
  rcc_closure_orbit h hH hA₀ hΓ
    (fun M hM => rcc_off_line_of_special h (rccOrbit_subset h.root hA₀)
      (fun _ hA => rccOrbit_le hΓ hA) (fun _ hA _ hg => rccOrbit_conj hA hg) hA₁
      (rccOrbit_self A₀) hs₁ hy hyA hyL M hM) hA hB hs

end CFSG.RankThree.PartOne.D4RC

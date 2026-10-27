module

public import CFSG.Timmesfeld.ARS.Sec8Basic
public import CFSG.Timmesfeld.ARS.Sec5Centralizer

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def SigmaEqLambda (R : Set (Subgroup G)) : Prop :=
  ∀ D ∈ R, sigmaSet R D = lambdaSet R D

@[expose] def IsLine (R : Set (Subgroup G)) (V : Subgroup G) : Prop :=
  ∃ A ∈ R, ∃ D ∈ lambdaSet R A, V = A ⊔ D

theorem sigmaEqLambda_of_mem (hR : IsRootClass R) {A : Subgroup G} (hA : A ∈ R)
    (h : sigmaSet R A = lambdaSet R A) : SigmaEqLambda R := fun D hD => by
  by_contra hD'
  exact sigmaSet_ne_lambdaSet_of_mem hR hD hA hD' h

namespace CaseH

theorem commuting_sup_self (hR : IsRootClass R) {A D : Subgroup G} (hA : A ∈ R)
    (hD : D ∈ lambdaSet R A) : Commuting (A ⊔ D) (A ⊔ D) :=
  Commuting.sup_left (Commuting.sup_right (hR.commuting_self hA) hD.1.2.2)
    (Commuting.sup_right hD.1.2.2.symm (hR.commuting_self hD.1.1))

section Local

variable (h : Hyp G R)
include h

omit h in
theorem mem_lambdaSet_of_commuting (hH : SigmaEqLambda R) {B C : Subgroup G} (hB : B ∈ R)
    (hC : C ∈ R) (hne : C ≠ B) (hBC : Commuting B C) : C ∈ lambdaSet R B := by
  rw [← hH B hB]
  exact ⟨hC, hne, hBC⟩

theorem special_of_mem_lambdaSet_of_mem_lambdaSet {B E C : Subgroup G} (hB : B ∈ R)
    (hE : E ∈ lambdaSet R B) (hC : C ∈ lambdaSet R B) (hEC : ¬ Commuting E C) :
    Special R E C ∧ ⁅E, C⁆ = B := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hER : E ∈ R := hE.1.1
  have hCR : C ∈ R := hC.1.1
  obtain ⟨-, -, hMM, -, hMp⟩ := Q_eq_M h hB
  have hne : E ≠ C := fun e => hEC (e ▸ hR.commuting_self hER)
  have hs : Special R E C := by
    rcases hR.rel E hER C hCR hne with hc | hop | hs
    · exact absurd hc hEC
    · exact absurd hop (Sec3.not_opposite_of_isPGroup_sup hR hER hCR
        (hMp.to_le (sup_le (QD.le_M hE) (QD.le_M hC))))
    · exact hs
  refine ⟨hs, QD.eq_of_le_of_mem hR hiso hs.1 hB ?_⟩
  rw [← hMM]
  exact Subgroup.commutator_mono (QD.le_M hE) (QD.le_M hC)

theorem eq_commutator {A B C : Subgroup G} (hA : A ∈ R) (hB : B ∈ R) (hs : Special R A B)
    (hCA : C ∈ lambdaSet R A) (hCB : C ∈ lambdaSet R B) : C = ⁅A, B⁆ :=
  ((special_of_mem_lambdaSet_of_mem_lambdaSet h hCA.1.1 (mem_lambdaSet_comm hA hCA)
    (mem_lambdaSet_comm hB hCB) (Special.not_commuting h.root hs)).2).symm

theorem commutator_mem_lambdaSet {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ R)
    (hs : Special R A B) : ⁅A, B⁆ ∈ lambdaSet R A ∧ ⁅A, B⁆ ∈ lambdaSet R B := by
  have := h.finite
  obtain ⟨h1, h2⟩ := mem_lambdaSet_commutator h.root h.noIsolated hA hB hs
  exact ⟨mem_lambdaSet_comm hs.1 h1, mem_lambdaSet_comm hs.1 h2⟩

theorem notMem_lambdaSet_of_opposite {A B C : Subgroup G} (hA : A ∈ R) (hAB : Opposite A B)
    (hCA : C ∈ lambdaSet R A) : C ∉ lambdaSet R B := fun hCB => by
  have := h.finite
  exact not_commuting_of_opposite_of_mem_lambdaSet h.root hA hAB hCB hCA.1.2.2

theorem special_of_mem_lambdaSet (hH : SigmaEqLambda R) {A B C : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ lambdaSet R A) (hC : C ∈ lambdaSet R B) (hCA : C ∉ lambdaSet R A) (hne : C ≠ A) :
    Special R A C ∧ ⁅A, C⁆ = B := by
  have hR := h.root
  have hCR : C ∈ R := hC.1.1
  have hBC : B ∈ lambdaSet R C := mem_lambdaSet_comm hB.1.1 hC
  have hs : Special R A C := by
    rcases hR.rel A hA C hCR hne.symm with hc | hop | hs
    · exact absurd (mem_lambdaSet_of_commuting hH hA hCR hne hc) hCA
    · exact absurd hBC (notMem_lambdaSet_of_opposite h hA hop hB)
    · exact hs
  exact ⟨hs, (eq_commutator h hA hCR hs hB hBC).symm⟩

omit h in
theorem gen_setOf_le_sup {A D : Subgroup G} (hA : A ∈ R) (hD : D ∈ lambdaSet R A) :
    gen {B | B ∈ R ∧ B ≤ A ⊔ D} = A ⊔ D :=
  le_antisymm (gen_le fun _ hB => hB.2)
    (sup_le (le_gen ⟨hA, le_sup_left⟩) (le_gen ⟨hD.1.1, le_sup_right⟩))

omit h in
theorem conjSet_setOf_le_eq (hR : IsRootClass R) {V : Subgroup G} {g : G}
    (hg : conjSub V g = V) : conjSet {B | B ∈ R ∧ B ≤ V} g = {B | B ∈ R ∧ B ≤ V} := by
  have hg' : conjSub V g⁻¹ = V := by
    conv_lhs => rw [← hg]
    rw [← conjSub_mul, inv_mul_cancel, conjSub_one]
  ext E
  rw [mem_conjSet]
  constructor
  · rintro ⟨hE, hEV⟩
    have h1 := hR.conjSub_mem hE g
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at h1
    refine ⟨h1, ?_⟩
    have h2 : conjSub (conjSub E g⁻¹) g ≤ conjSub V g := Subgroup.map_mono hEV
    rwa [← conjSub_mul, mul_inv_cancel, conjSub_one, hg] at h2
  · rintro ⟨hE, hEV⟩
    refine ⟨hR.conjSub_mem hE g⁻¹, ?_⟩
    have h2 : conjSub E g⁻¹ ≤ conjSub V g⁻¹ := Subgroup.map_mono hEV
    rwa [hg'] at h2

theorem conjSub_line_eq (hH : SigmaEqLambda R) {A D : Subgroup G} (hA : A ∈ R)
    (hD : D ∈ lambdaSet R A) {E : Subgroup G} (hE : E ∈ R) {d : G} (hd : d ∈ E) (hd1 : d ≠ 1)
    {B : Subgroup G} (hB : B ∈ R) (hBV : B ≤ A ⊔ D) (hBdV : conjSub B d ≤ A ⊔ D) :
    conjSub (A ⊔ D) d = A ⊔ D := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  set V := A ⊔ D with hV
  have hVV : Commuting V V := commuting_sup_self hR hA hD
  have hDR : D ∈ R := hD.1.1
  have hdd : d * d = 1 := hR.mul_self E hE d hd
  suffices hle : conjSub V d ≤ V by
    refine le_antisymm hle ?_
    have h2 : conjSub (conjSub V d) d ≤ conjSub V d := Subgroup.map_mono hle
    rwa [Sec5.conjSub_conjSub_of_mul_self hdd] at h2
  have hpts : ∀ C₀ ∈ R, C₀ ≤ V → C₀ ≠ B → V = B ⊔ C₀ := fun C₀ hC₀ hC₀V hne =>
    ((mem_lambdaSet_of_le_sup hR hiso hA hD hB hBV hC₀ hC₀V hne.symm).2).symm
  have hle_of : ∀ C₀ ∈ R, C₀ ≤ V → C₀ ≠ B → conjSub C₀ d ≤ V → conjSub V d ≤ V := by
    intro C₀ hC₀ hC₀V hne hC₀d
    rw [hpts C₀ hC₀ hC₀V hne]
    change (B ⊔ C₀).map _ ≤ _
    rw [Subgroup.map_sup, ← hpts C₀ hC₀ hC₀V hne]
    exact sup_le hBdV hC₀d
  obtain ⟨C₀, hC₀, hC₀V, hC₀B⟩ : ∃ C₀ ∈ R, C₀ ≤ V ∧ C₀ ≠ B := by
    by_cases hAB : A = B
    · exact ⟨D, hDR, le_sup_right, fun e => hD.1.2.1 (e.trans hAB.symm)⟩
    · exact ⟨A, hA, le_sup_left, hAB⟩
  by_cases hEB : Commuting E B
  ·
    refine hle_of C₀ hC₀ hC₀V hC₀B ?_
    by_cases hEC : Commuting E C₀
    · rw [conjSub_of_forall_commute fun c hc => hEC d hd c hc]
      exact hC₀V
    have hEne : E ≠ B := fun e => hEC (by rw [e]; exact hVV.mono hBV hC₀V)
    have hEl : E ∈ lambdaSet R B := mem_lambdaSet_of_commuting hH hB hE hEne hEB.symm
    have hCl : C₀ ∈ lambdaSet R B :=
      (mem_lambdaSet_of_le_sup hR hiso hA hD hB hBV hC₀ hC₀V hC₀B.symm).1
    obtain ⟨-, hcomm⟩ := special_of_mem_lambdaSet_of_mem_lambdaSet h hB hEl hCl hEC
    refine (conjSub_le_commutator_sup hd).trans ?_
    rw [Subgroup.commutator_comm, hcomm, hpts C₀ hC₀ hC₀V hC₀B]
  · have hEne : E ≠ B := fun e => hEB (by rw [e]; exact hR.commuting_self hB)
    rcases hR.rel E hE B hB hEne with hc | hop | hs
    · exact absurd hc hEB
    ·
      exfalso
      have hBd : conjSub B d ≠ B := fun e => hd1 (hop.eq_one_of_conjSub_eq hd e)
      have hsup := Opposite.sup_conjSub_eq (hR.mul_self B hB) hop.symm
        (Subgroup.one_mem (B ⊔ E)) (Subgroup.mem_sup_right hd) (by rw [conjSub_one]; exact hBd.symm)
      rw [conjSub_one] at hsup
      have hcomm : Commuting B E := (hVV.mono (sup_le hBV hBdV) (sup_le hBV hBdV)).mono
        le_sup_left (hsup ▸ le_sup_right)
      exact hop.symm.not_commuting (hR.ne_bot B hB) hcomm
    ·
      have hs' := hs.symm
      have hBd : conjSub B d ≠ B := Sec3.conjSub_ne_of_special hR hiso hE hB hs hd hd1
      have hCl : ⁅B, E⁆ ∈ lambdaSet R B := (commutator_mem_lambdaSet h hB hE hs').1
      have hBdl : conjSub B d ≤ B ⊔ ⁅B, E⁆ :=
        (conjSub_le_commutator_sup hd).trans (sup_comm _ _).le
      have hline := (mem_lambdaSet_of_le_sup hR hiso hB hCl hB le_sup_left
        (hR.conjSub_mem hB d) hBdl hBd.symm).2
      have hV' : V = B ⊔ ⁅B, E⁆ := by
        rw [← hline]
        exact hpts _ (hR.conjSub_mem hB d) hBdV hBd
      have hEV : ⁅B, E⁆ ≤ V := by rw [hV']; exact le_sup_right
      refine hle_of _ hs'.1 hEV (Special.ne_commutator hR hs').symm ?_
      rw [conjSub_of_forall_commute fun c hc => (hs'.2.2 c hc d hd).symm]
      exact hEV

theorem isWeakTI_line (hH : SigmaEqLambda R) {A D : Subgroup G} (hA : A ∈ R)
    (hD : D ∈ lambdaSet R A) : IsWeakTI R {B | B ∈ R ∧ B ≤ A ⊔ D} := by
  have hR := h.root
  have hiso := h.noIsolated
  refine ⟨fun B hB => hB.1, ⟨A, ⟨hA, le_sup_left⟩, D, ⟨hD.1.1, le_sup_right⟩, hD.1.2.1.symm⟩,
    ?_, ?_⟩
  · intro heq
    obtain ⟨B, hB, hAB⟩ := hiso A hA
    have hBV : B ≤ A ⊔ D := by
      have : B ∈ {B | B ∈ R ∧ B ≤ A ⊔ D} := by rw [heq]; exact hB
      exact this.2
    exact hAB.not_commuting (hR.ne_bot A hA)
      ((commuting_sup_self hR hA hD).mono le_sup_left hBV)
  · rintro d ⟨E, hE, hd, hd1⟩
    by_cases hne : {B | B ∈ R ∧ B ≤ A ⊔ D} ∩ conjSet {B | B ∈ R ∧ B ≤ A ⊔ D} d = ∅
    · exact Or.inl hne
    right
    obtain ⟨X, hX, hXd⟩ := Set.nonempty_iff_ne_empty.2 hne
    rw [mem_conjSet] at hXd
    have hdd : d * d = 1 := hR.mul_self E hE d hd
    have hdinv : d⁻¹ = d := inv_eq_of_mul_eq_one_right hdd
    rw [hdinv] at hXd
    have hVd := conjSub_line_eq h hH hA hD hE hd hd1 hXd.1 hXd.2
      (by rw [Sec5.conjSub_conjSub_of_mul_self hdd]; exact hX.2)
    rw [conjSet_setOf_le_eq hR hVd, Set.inter_self]

theorem le_of_commuting_line (hH : SigmaEqLambda R) {A D : Subgroup G} (hA : A ∈ R)
    (hD : D ∈ lambdaSet R A) {E : Subgroup G} (hE : E ∈ R) (hEV : Commuting E (A ⊔ D)) :
    E ≤ A ⊔ D := by
  have := h.finite
  have hΔ := isWeakTI_line h hH hA hD
  have hmem : E ∈ {C | C ∈ R ∧ Commuting C (gen {B | B ∈ R ∧ B ≤ A ⊔ D})} :=
    ⟨hE, by rw [gen_setOf_le_sup hA hD]; exact hEV⟩
  rw [Sec5.setOf_commuting_gen_eq h.root h.noIsolated h.nondeg
    (fun A hA B hB e => eq_of_omegaSet_eq h hA hB e) hΔ] at hmem
  exact hmem.2

theorem le_line (hH : SigmaEqLambda R) {A D : Subgroup G} (hA : A ∈ R) (hD : D ∈ lambdaSet R A)
    {B C E : Subgroup G} (hB : B ∈ R) (hBV : B ≤ A ⊔ D) (hC : C ∈ R) (hCV : C ≤ A ⊔ D)
    (hBC : B ≠ C) (hE : E ∈ R) (hEB : Commuting E B) (hEC : Commuting E C) : E ≤ A ⊔ D := by
  have := h.finite
  refine le_of_commuting_line h hH hA hD hE ?_
  rw [← (mem_lambdaSet_of_le_sup h.root h.noIsolated hA hD hB hBV hC hCV hBC).2]
  exact hEB.sup_right hEC

theorem eq_of_le_of_le {A D A' D' : Subgroup G} (hA : A ∈ R) (hD : D ∈ lambdaSet R A)
    (hA' : A' ∈ R) (hD' : D' ∈ lambdaSet R A') {B C : Subgroup G} (hB : B ∈ R) (hC : C ∈ R)
    (hBC : B ≠ C) (hBV : B ≤ A ⊔ D) (hCV : C ≤ A ⊔ D) (hBV' : B ≤ A' ⊔ D')
    (hCV' : C ≤ A' ⊔ D') : A ⊔ D = A' ⊔ D' := by
  have := h.finite
  rw [← (mem_lambdaSet_of_le_sup h.root h.noIsolated hA hD hB hBV hC hCV hBC).2,
    (mem_lambdaSet_of_le_sup h.root h.noIsolated hA' hD' hB hBV' hC hCV' hBC).2]

theorem special_conjSub_of_mem_psiSet (hH : SigmaEqLambda R) {C E F : Subgroup G} (hC : C ∈ R)
    (hE : E ∈ psiSet R C) (hF : F ∈ psiSet R C) (hEF : F ∈ lambdaSet R E)
    (hne : ⁅C, E⁆ ≠ ⁅C, F⁆) {c : G} (hc : c ∈ C) (hc1 : c ≠ 1) :
    Special R (conjSub E c) F ∧ ⁅conjSub E c, F⁆ = E := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hER : E ∈ R := hE.1
  have hFR : F ∈ R := hF.1
  have hFE : E ∈ lambdaSet R F := mem_lambdaSet_comm hER hEF
  obtain ⟨hE'C, hE'E⟩ := commutator_mem_lambdaSet h hC hER hE.2
  have hE'R : ⁅C, E⁆ ∈ R := hE.2.1
  have hE'F : ⁅C, E⁆ ≠ F := fun e => Special.not_commuting hR hF.2 (e ▸ hE'C.1.2.2)
  have hE'V : ¬ ⁅C, E⁆ ≤ E ⊔ F := fun hle => hne (eq_commutator h hC hFR hF.2 hE'C
    (mem_lambdaSet_of_le_sup hR hiso hER hEF hFR le_sup_right hE'R hle hE'F.symm).1)
  have hEcR : conjSub E c ∈ R := hR.conjSub_mem hER c
  have hEcle : conjSub E c ≤ E ⊔ ⁅C, E⁆ := by
    refine (conjSub_le_commutator_sup hc).trans ?_
    rw [Subgroup.commutator_comm, sup_comm]
  have hEcE : conjSub E c ≠ E := Sec3.conjSub_ne_of_special hR hiso hC hER hE.2 hc hc1
  obtain ⟨hEcl, hline⟩ := mem_lambdaSet_of_le_sup hR hiso hER hE'E hER le_sup_left hEcR hEcle
    hEcE.symm
  have hEcF : ¬ Commuting (conjSub E c) F := by
    intro hcomm
    have hEcneF : conjSub E c ≠ F := by
      intro e
      apply hne
      refine eq_commutator h hC hFR hF.2 hE'C ?_
      exact (mem_lambdaSet_of_le_sup hR hiso hER hE'E hFR (e ▸ hEcle) hE'R le_sup_right
        hE'F.symm).1
    have hEcV : conjSub E c ≤ E ⊔ F :=
      le_line h hH hER hEF hER le_sup_left hFR le_sup_right hEF.1.2.1.symm hEcR
        hEcl.1.2.2.symm hcomm
    apply hE'V
    rw [eq_of_le_of_le h hER hEF hER hE'E hER hEcR hEcE.symm le_sup_left hEcV le_sup_left hEcle]
    exact le_sup_right
  have hEcneF : conjSub E c ≠ F := fun e => hEcF (by rw [e]; exact hR.commuting_self hFR)
  have hs : Special R (conjSub E c) F := by
    rcases hR.rel _ hEcR F hFR hEcneF with hc' | hop | hs
    · exact absurd hc' hEcF
    · exact absurd hFE (notMem_lambdaSet_of_opposite h hEcR hop (mem_lambdaSet_comm hER hEcl))
    · exact hs
  exact ⟨hs, (eq_commutator h hEcR hFR hs (mem_lambdaSet_comm hER hEcl) hFE).symm⟩

theorem commutator_eq_of_mem_psiSet (hH : SigmaEqLambda R) {C E F : Subgroup G} (hC : C ∈ R)
    (hE : E ∈ psiSet R C) (hF : F ∈ psiSet R C) (hEF : F ∈ lambdaSet R E) :
    ⁅C, E⁆ = ⁅C, F⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  by_contra hne
  have hER : E ∈ R := hE.1
  have hFR : F ∈ R := hF.1
  have hFE : E ∈ lambdaSet R F := mem_lambdaSet_comm hER hEF
  obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hC
  obtain ⟨-, h1⟩ := special_conjSub_of_mem_psiSet h hH hC hE hF hEF hne hc hc1
  obtain ⟨-, h2⟩ := special_conjSub_of_mem_psiSet h hH hC hF hE hFE (Ne.symm hne) hc hc1
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
  obtain ⟨f, hf, hf1⟩ := hR.exists_ne_one hFR
  have hef1 : e * f ≠ 1 := by
    intro h0
    have hfe : f ∈ E ⊓ F := ⟨by rw [eq_inv_of_mul_eq_one_right h0]; exact E.inv_mem he, hf⟩
    rw [inf_eq_bot hR hiso hER hFR hEF.1.2.1.symm, Subgroup.mem_bot] at hfe
    exact hf1 hfe
  obtain ⟨X, hX, -, hefX⟩ := hEF.2 (e * f)
    (Subgroup.mul_mem _ (Subgroup.mem_sup_left he) (Subgroup.mem_sup_right hf)) hef1
  have key := commutator_conjSub_eq hR hiso hER hC hFR hE.2.symm hF.2 hEF.1.2.2 he he1 hf hf1
    ⟨X, hX, hefX, hef1⟩ hc hc1
  rw [h1, Subgroup.commutator_comm, h2] at key
  exact hEF.1.2.1 key

theorem false_of_quadrangle (hH : SigmaEqLambda R) {A B C D : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ lambdaSet R A) (hC : C ∈ lambdaSet R B) (hD : D ∈ lambdaSet R C)
    (hDA : A ∈ lambdaSet R D) (hCA : C ∉ lambdaSet R A) (hCA' : C ≠ A) (hDB : D ≠ B) : False := by
  obtain ⟨hs, hBc⟩ := special_of_mem_lambdaSet h hH hA hB hC hCA hCA'
  apply hDB
  rw [eq_commutator h hA hC.1.1 hs (mem_lambdaSet_comm hD.1.1 hDA) hD, hBc]

theorem false_of_pentagon (hH : SigmaEqLambda R) {A B C D E : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ lambdaSet R A) (hC : C ∈ lambdaSet R B) (hD : D ∈ lambdaSet R C)
    (hE : E ∈ lambdaSet R D) (hEA : A ∈ lambdaSet R E) (hCA : C ∉ lambdaSet R A) (hCA' : C ≠ A)
    (hDA : D ∉ lambdaSet R A) (hDA' : D ≠ A) (hBE : B ≠ E) : False := by
  obtain ⟨hsC, hBc⟩ := special_of_mem_lambdaSet h hH hA hB hC hCA hCA'
  obtain ⟨hsD, hEc⟩ := special_of_mem_lambdaSet h hH hA (mem_lambdaSet_comm hE.1.1 hEA)
    (mem_lambdaSet_comm hD.1.1 hE) hDA hDA'
  apply hBE
  rw [← hBc, ← hEc]
  exact commutator_eq_of_mem_psiSet h hH hA ⟨hC.1.1, hsC⟩ ⟨hD.1.1, hsD⟩ hD

theorem opposite_of_le_line (hH : SigmaEqLambda R) {A B D P X : Subgroup G} (hA : A ∈ R)
    (hB : B ∈ R) (hAB : Opposite A B) (hD : D ∈ lambdaSet R A) (hP : P ∈ R) (hPV : P ≤ A ⊔ D)
    (hPB : P ∈ psiSet R B) (hX : X ∈ R) (hXV : X ≤ A ⊔ D) (hXP : X ≠ P) : Opposite B X := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨P₀, -, huniq⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hB hAB hD
  have hPu := huniq P ⟨hP, hPV, hPB⟩
  have hXB : X ≠ B := by
    rintro rfl
    exact hAB.not_commuting (hR.ne_bot A hA) ((commuting_sup_self hR hA hD).mono le_sup_left hXV)
  rcases hR.rel B hB X hX hXB.symm with hc | hop | hs
  · exfalso
    by_cases hXA : X = A
    · exact hAB.not_commuting (hR.ne_bot A hA) (hXA ▸ hc.symm)
    · have hXl : X ∈ lambdaSet R A :=
        (mem_lambdaSet_of_le_sup hR hiso hA hD hA le_sup_left hX hXV (Ne.symm hXA)).1
      exact notMem_lambdaSet_of_opposite h hA hAB hXl
        (mem_lambdaSet_of_commuting hH hB hX hXB hc)
  · exact hop
  · exact absurd ((huniq X ⟨hX, hXV, ⟨hX, hs⟩⟩).trans hPu.symm) hXP

theorem exists_opposite_of_le_line (hH : SigmaEqLambda R) {A D C : Subgroup G} (hA : A ∈ R)
    (hD : D ∈ lambdaSet R A) (hC : C ∈ R)
    (hfar : ∀ X ∈ R, X ≤ A ⊔ D → X ≠ C ∧ X ∉ lambdaSet R C) :
    ∃ X ∈ R, X ≤ A ⊔ D ∧ Opposite C X := by
  have hR := h.root
  by_contra hno
  push Not at hno
  have hpsi : ∀ X ∈ R, X ≤ A ⊔ D → X ∈ psiSet R C := by
    intro X hX hXV
    obtain ⟨hXC, hXl⟩ := hfar X hX hXV
    rcases hR.rel C hC X hX hXC.symm with hc | hop | hs
    · exact absurd (mem_lambdaSet_of_commuting hH hC hX hXC hc) hXl
    · exact absurd hop (hno X hX hXV)
    · exact ⟨hX, hs⟩
  have hAψ := hpsi A hA le_sup_left
  have hDψ := hpsi D hD.1.1 le_sup_right
  have heq := commutator_eq_of_mem_psiSet h hH hC hAψ hDψ hD
  obtain ⟨hZC, hZA⟩ := commutator_mem_lambdaSet h hC hA hAψ.2
  obtain ⟨-, hZD⟩ := commutator_mem_lambdaSet h hC hD.1.1 hDψ.2
  rw [← heq] at hZD
  have hZV : ⁅C, A⁆ ≤ A ⊔ D := le_line h hH hA hD hA le_sup_left hD.1.1 le_sup_right
    hD.1.2.1.symm hAψ.2.1 hZA.1.2.2.symm hZD.1.2.2.symm
  exact (hfar _ hAψ.2.1 hZV).2 hZC

end Local

end CaseH

end CFSG.Timmesfeld.ARS

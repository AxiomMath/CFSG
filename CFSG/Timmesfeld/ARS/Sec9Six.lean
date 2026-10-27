module

public import CFSG.Timmesfeld.ARS.Sec9Cases
public import CFSG.Timmesfeld.ARS.Sec8LeviAction

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open _root_.CFSG.Timmesfeld.ARS.Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec9

theorem commutator_eq_of_mem_lambdaSet (h : Hyp G R) {A X Y : Subgroup G} (hA : A ∈ R)
    (hX : X ∈ lambdaSet R A) (hY : Y ∈ lambdaSet R A) (hXY : ¬ Commuting X Y) : ⁅X, Y⁆ = A := by
  have := h.finite
  have hR := h.root
  have hXR : X ∈ R := hX.1.1
  have hYR : Y ∈ R := hY.1.1
  have hne : X ≠ Y := fun e => hXY (by rw [← e]; exact hR.commuting_self hXR)
  rcases hR.rel X hXR Y hYR hne with hc | ho | hs
  · exact absurd hc hXY
  · exact absurd hX.1.2.2.symm
      (not_commuting_of_opposite_of_mem_lambdaSet hR hXR ho (mem_lambdaSet_comm hA hY))
  · refine Subgroup.eq_of_le_of_card_ge ?_ (hR.card_eq hA hs.1).le
    rw [← (Q_eq_M h hA).2.2.1]
    exact Subgroup.commutator_mono (QD.le_M hX) (QD.le_M hY)

section Six

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hmax hA₀

omit hAne hmax in
theorem exists_not_commuting_mem_lambdaStar :
    ∃ B ∈ lambdaStar R A A₀, ∃ B₂ ∈ lambdaStar R A A₀, ¬ Commuting B B₂ := by
  have := h.finite
  have hR := h.root
  by_contra! hall
  have hM : Commuting (M R A) (M R A) := by
    rw [M_eq_gen_lambdaStar h hA hA₀]
    exact commuting_gen_gen hall
  have h1 : ⁅M R A, M R A⁆ = ⊥ := commuting_iff_commutator_eq_bot.1 hM
  rw [(Q_eq_M h hA).2.2.1] at h1
  exact hR.ne_bot A hA h1

omit hAne hmax in
theorem commuting_of_mem_lambdaSet_of_commuting {D X Y : Subgroup G} (hD : D ∈ leviSet R A A₀)
    (hX : X ∈ lambdaSet R A) (hY : Y ∈ lambdaSet R A) (hXD : X ∈ lambdaSet R D)
    (hDY : Commuting D Y) : Commuting X Y := by
  have := h.finite
  have hR := h.root
  have hDR : D ∈ R := hD.1.1
  by_contra hXY
  have hle : A ≤ M R D := by
    rw [← commutator_eq_of_mem_lambdaSet h hA hX hY hXY]
    exact commutator_le_of_le_normalizer (QD.le_M hXD)
      (QD.le_normalizer_M hR hDR ⟨hY.1.1, hDY⟩)
  have hmem : A ∈ {Z | Z ∈ R ∧ Z ≤ M R D} := ⟨hA, hle⟩
  rw [(Q_eq_M h hDR).2.1] at hmem
  rcases hmem with e | hAD
  · exact hD.1.2.1 e.symm
  · have hle' : D ≤ M R A ⊓ levi R A A₀ :=
      le_inf (QD.le_M (mem_lambdaSet_comm hDR hAD)) (le_gen hD)
    rw [M_inf_levi_eq_bot h hA hA₀] at hle'
    exact hR.ne_bot D hDR (le_bot_iff.1 hle')

omit hmax in
theorem mem_of_le_gen {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) {X : Subgroup G}
    (hX : X ∈ R) (hle : X ≤ gen Δ) : X ∈ Δ := by
  obtain ⟨E, hE, rfl⟩ := hΔ
  exact mem_comp_of_le h hA hAne hA₀ hE hX hle

variable {Blk : Set (Subgroup G)} (hBlk : Blk ⊆ leviSet R A A₀)
  (hcl : ∀ Y ∈ Blk, comp R A A₀ Y ⊆ Blk)
include hBlk hcl

omit hmax in
theorem commuting_conjSub_of_mem_lambdaSet {D X Y : Subgroup G} (hD : D ∈ leviSet R A A₀)
    (hDout : D ∉ Blk) (hX : X ∈ lambdaSet R A) (hY : Y ∈ lambdaSet R A)
    (hXD : X ∈ lambdaSet R D) (hDY : Commuting D Y) {w : G} (hw : w ∈ gen Blk) :
    Commuting X (conjSub Y w) ∧ Commuting (conjSub X w) Y := by
  have hR := h.root
  have hwV : w ∈ levi R A A₀ := gen_le_levi hBlk hw
  have hAw : conjSub A w = A := conjSub_of_forall_commute fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left A A₀ hwV) a ha).symm
  have hDw : conjSub D w = D := conjSub_of_forall_commute fun d hd =>
    (commute_of_mem_gen h hA hAne hA₀ hBlk hcl hD hDout hd hw).symm
  have hXw : conjSub X w ∈ lambdaSet R A := by
    have := conjSub_mem_lambdaSet hR hX w
    rwa [hAw] at this
  have hYw : conjSub Y w ∈ lambdaSet R A := by
    have := conjSub_mem_lambdaSet hR hY w
    rwa [hAw] at this
  have hXwD : conjSub X w ∈ lambdaSet R D := by
    have := conjSub_mem_lambdaSet hR hXD w
    rwa [hDw] at this
  exact ⟨commuting_of_mem_lambdaSet_of_commuting h hA hA₀ hD hX hYw hXD
    (commuting_of_mem_orbit h hA hAne hA₀ hBlk hcl hD hDout hDY ⟨w, hw, rfl⟩),
    commuting_of_mem_lambdaSet_of_commuting h hA hA₀ hD hXw hY hXwD hDY⟩

omit hmax in
theorem mem_lambdaSet_of_mem_lambdaSet (h3 : OrbitCollinear R A A₀ Blk)
    {Δ : Set (Subgroup G)} (hΔ : Δ ∈ leviComps R A A₀) (hout : ∀ Y ∈ Δ, Y ∉ Blk)
    {B B₂ : Subgroup G} (hB : B ∈ lambdaStar R A A₀) (hB₂ : B₂ ∈ lambdaStar R A A₀)
    (hBB₂ : ¬ Commuting B B₂) {E F : Subgroup G} (hE : E ∈ Δ) (hBE : B ∈ lambdaSet R E)
    (hF : F ∈ Δ) (hFE : F ∈ lambdaSet R E) : B ∈ lambdaSet R F := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hEl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hE
  have hFl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hF
  have hER : E ∈ R := hEl.1.1
  have hFR : F ∈ R := hFl.1.1
  have hBR : B ∈ R := hB.1.1.1
  have hEB : E ∈ lambdaSet R B := mem_lambdaSet_comm hER hBE
  have hEF : E ∈ lambdaSet R F := mem_lambdaSet_comm hER hFE
  have hFB : Commuting F B := by
    by_contra hFB
    have hs : Special R B F := (special_of_not_commuting h hA hFl hB hFB).symm
    have hst := (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hFl hB hs).1 _ hs.1 le_sup_right
    have hle : ⁅B, F⁆ ≤ E := by
      rw [← (Q_eq_M h hER).2.2.1]
      exact Subgroup.commutator_mono (QD.le_M hBE) (QD.le_M hFE)
    rw [Subgroup.eq_of_le_of_card_ge hle (hR.card_eq hER hs.1).le] at hst
    exact ne_of_mem_leviSet h hA hA₀ hst hEl rfl
  obtain ⟨C, hCO, hCB⟩ := h3 B hB B₂ hB₂
  have hCst : C ∈ lambdaStar R A A₀ := orbit_subset_lambdaStar hR hBlk hB₂ hCO
  have hCR : C ∈ R := hCst.1.1.1
  have hBC : B ∈ lambdaSet R C := mem_lambdaSet_comm hBR hCB
  obtain ⟨w, hw, hCw⟩ := exists_conjSub_eq_of_mem_orbit hCO (mem_orbit_self Blk B₂)
  have hEC : ¬ Commuting E C := by
    intro hc
    have := (commuting_conjSub_of_mem_lambdaSet h hA hAne hA₀ hBlk hcl hEl (hout E hE) hB.1
      hCst.1 hBE hc hw).1
    rw [hCw] at this
    exact hBB₂ this
  have hsEC : Special R E C := special_of_not_commuting h hA hEl hCst hEC
  have hECB : ⁅E, C⁆ = B := by
    refine Subgroup.eq_of_le_of_card_ge ?_ (hR.card_eq hBR hsEC.1).le
    rw [← (Q_eq_M h hBR).2.2.1]
    exact Subgroup.commutator_mono (QD.le_M hEB) (QD.le_M hCB)
  by_cases hFC : Commuting F C
  · have hle : B ≤ M R F := by
      rw [← hECB]
      exact commutator_le_of_le_normalizer (QD.le_M hEF) (QD.le_normalizer_M hR hFR ⟨hCR, hFC⟩)
    have hmem : B ∈ {X | X ∈ R ∧ X ≤ M R F} := ⟨hBR, hle⟩
    rw [(Q_eq_M h hFR).2.1] at hmem
    exact hmem.resolve_left fun e => ne_of_mem_leviSet h hA hA₀ hB hFl e.symm
  have hsCF : Special R C F := (special_of_not_commuting h hA hFl hCst hFC).symm
  obtain ⟨hpts, F', hF'l, hFF', hCF'⟩ :=
    exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hFl hCst hsCF
  have hC'R : ⁅C, F⁆ ∈ R := hsCF.1
  have hC'st : ⁅C, F⁆ ∈ lambdaStar R A A₀ := hpts _ hC'R le_sup_right
  obtain ⟨hCC', hFC'⟩ := mem_lambdaSet_commutator hR hiso hCR hFR hsCF
  have hC'C : ⁅C, F⁆ ∈ lambdaSet R C := mem_lambdaSet_comm hC'R hCC'
  by_cases hC'B : ⁅C, F⁆ = B
  · rw [← hC'B]
    exact mem_lambdaSet_comm hC'R hFC'
  exfalso
  have hEC' : Commuting E ⁅C, F⁆ := by
    obtain ⟨c, hc, hc1⟩ := hR.exists_ne_one hCR
    have h1 : Commuting (conjSub E c) F := by
      have hle : conjSub E c ≤ B ⊔ E := by
        have := conjSub_le_commutator_sup (A := E) hc
        rwa [hECB] at this
      exact (Commuting.sup_left hFB.symm hFE.1.2.2).mono hle le_rfl
    have h2 := commuting_conjSub_of_commuting hR hiso hER hCR hsEC hFE.1.2.2 hc hc1 h1
    have h3' : Commuting E (F ⊔ ⁅F, C⁆) := by
      rw [← sup_conjSub_eq_sup_commutator hR hiso hFR hCR hsCF.symm hc hc1]
      exact Commuting.sup_right hFE.1.2.2 h2
    rw [Subgroup.commutator_comm C F]
    exact h3'.mono le_rfl le_sup_right
  have hC'Bl : ⁅C, F⁆ ∈ lambdaSet R B := by
    have hle : ⁅C, F⁆ ≤ M R B :=
      commutator_le_of_le_normalizer (QD.le_M hCB) (QD.le_normalizer_M hR hBR ⟨hFR, hFB.symm⟩)
    have hmem : ⁅C, F⁆ ∈ {X | X ∈ R ∧ X ≤ M R B} := ⟨hC'R, hle⟩
    rw [(Q_eq_M h hBR).2.1] at hmem
    exact hmem.resolve_left hC'B
  obtain ⟨Y, hYl, hBY⟩ := exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hB hC'st
    (mem_lambdaSet_comm hBR hC'Bl)
  have hsBY : Special R B Y := by
    refine (special_of_not_commuting h hA hYl hB fun hc => ?_).symm
    have h0 := commuting_iff_commutator_eq_bot.1 hc.symm
    rw [hBY] at h0
    exact hR.ne_bot _ hC'R h0
  have hLst : ∀ P ∈ R, P ≤ B ⊔ ⁅C, F⁆ → P ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hYl hB hsBY).1
    rwa [hBY] at this
  have hLM : B ⊔ ⁅C, F⁆ ≤ M R C := sup_le (QD.le_M hBC) (QD.le_M hC'C)
  have hEL : Commuting E (B ⊔ ⁅C, F⁆) := Commuting.sup_right hBE.1.2.2 hEC'
  have hCL : ¬ C ≤ B ⊔ ⁅C, F⁆ := fun hle => hEC (hEL.mono le_rfl hle)
  have hLC : ∀ P ∈ R, P ≤ B ⊔ ⁅C, F⁆ → P ∈ lambdaSet R C := by
    intro P hP hPle
    have hmem : P ∈ {X | X ∈ R ∧ X ≤ M R C} := ⟨hP, hPle.trans hLM⟩
    rw [(Q_eq_M h hCR).2.1] at hmem
    exact hmem.resolve_left fun e => hCL ((le_of_eq e.symm).trans hPle)
  have hF'R : F' ∈ R := hF'l.1.1
  obtain ⟨P, hPR, hPle, hF'P⟩ :=
    exists_commuting_of_le_M h hCR hBR hC'Bl hLM hF'R (QD.le_M (mem_lambdaSet_comm hF'R hCF'))
  have hPst := hLst P hPR hPle
  have hF'out : F' ∉ Blk := hout F' (mem_of_opposite h hA hAne hA₀ hΔ hF hF'l hFF')
  have hB₂P : Commuting B₂ P := by
    have := (commuting_conjSub_of_mem_lambdaSet h hA hAne hA₀ hBlk hcl hF'l hF'out hCst.1
      hPst.1 hCF' hF'P hw).2
    rwa [hCw] at this
  obtain ⟨D, hDl, hPD⟩ :=
    exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hPst hCst (hLC P hPR hPle)
  have hDR : D ∈ R := hDl.1.1
  have hsPD : Special R P D := by
    refine (special_of_not_commuting h hA hDl hPst fun hc => ?_).symm
    have h0 := commuting_iff_commutator_eq_bot.1 hc.symm
    rw [hPD] at h0
    exact hR.ne_bot _ hCR h0
  have hDC : D ∈ lambdaSet R C := by
    have := (mem_lambdaSet_commutator hR hiso hPR hDR hsPD).2
    rwa [hPD] at this
  by_cases hDB : D ∈ Blk
  ·
    obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
    have hEP : Commuting E P := hEL.mono le_rfl hPle
    have hEd : conjSub E d = E := conjSub_of_forall_commute fun e he =>
      (commute_of_mem_gen h hA hAne hA₀ hBlk hcl hEl (hout E hE) he (le_gen hDB hd)).symm
    have hEPd : Commuting E (conjSub P d) := by
      have := hEP.conjSub d
      rwa [hEd] at this
    have hPC : Commuting E (P ⊔ C) := by
      rw [← hPD, ← sup_conjSub_eq_sup_commutator hR hiso hPR hDR hsPD hd hd1]
      exact Commuting.sup_right hEP hEPd
    exact hEC (hPC.mono le_rfl le_sup_right)
  ·
    obtain ⟨R₀, hR₀R, hR₀le, hDR₀⟩ :=
      exists_commuting_of_le_M h hCR hBR hC'Bl hLM hDR (QD.le_M hDC)
    have hB₂R₀ : Commuting B₂ R₀ := by
      have := (commuting_conjSub_of_mem_lambdaSet h hA hAne hA₀ hBlk hcl hDl hDB hCst.1
        (hLst R₀ hR₀R hR₀le).1 (mem_lambdaSet_comm hCR hDC) hDR₀ hw).2
      rwa [hCw] at this
    have hPR₀ : P ≠ R₀ := by
      rintro rfl
      exact hsPD.not_commuting hR hDR₀.symm
    obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hBR hC'Bl hPR hPle hR₀R hR₀le hPR₀
    have hB₂L : Commuting B₂ (B ⊔ ⁅C, F⁆) := by
      rw [← hsup]
      exact Commuting.sup_right hB₂P hB₂R₀
    exact hBB₂ (hB₂L.mono le_rfl le_sup_left).symm

theorem notMem_lambdaSet_of_notMem (h3 : OrbitCollinear R A A₀ Blk) {Δ : Set (Subgroup G)}
    (hΔ : Δ ∈ leviComps R A A₀) (hout : ∀ Y ∈ Δ, Y ∉ Blk) {E F : Subgroup G} (hE : E ∈ Δ)
    (hF : F ∈ Δ) : F ∉ lambdaSet R E := by
  intro hFE
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨B, hB, B₂, hB₂, hBB₂⟩ := exists_not_commuting_mem_lambdaStar h hA hA₀
  have hstar : ∀ {X Y : Subgroup G}, X ∈ Δ → B ∈ lambdaSet R X → Y ∈ Δ →
      Y ∈ lambdaSet R X → B ∈ lambdaSet R Y := fun hX hBX hY hYX =>
    mem_lambdaSet_of_mem_lambdaSet h hA hAne hA₀ hBlk hcl h3 hΔ hout hB hB₂ hBB₂ hX hBX hY hYX
  have hRΔ : ∀ {X : Subgroup G}, X ∈ Δ → X ∈ R := fun hX =>
    (mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hX).1.1
  have hpsi : ∀ {X Y : Subgroup G}, X ∈ Δ → B ∈ lambdaSet R X → Y ∈ Δ → Special R X Y →
      B ∈ lambdaSet R Y := by
    intro X Y hX hBX hY hs
    obtain ⟨h1, h2⟩ := mem_lambdaSet_commutator hR hiso (hRΔ hX) (hRΔ hY) hs
    have hW : ⁅X, Y⁆ ∈ Δ :=
      mem_of_le_gen h hA hAne hA₀ hΔ hs.1 (QD.commutator_le_of_le (le_gen hX) (le_gen hY))
    exact hstar hW (hstar hX hBX hW (mem_lambdaSet_comm hs.1 h1)) hY h2
  obtain ⟨E₁, hE₁, hBE₁⟩ := exists_mem_lambdaSet h hA hAne hmax hA₀ hΔ hB
  obtain ⟨k, hk, hEk⟩ := exists_conjSub_eq h hΔ hE hE₁
  have hkV : k ∈ levi R A A₀ :=
    gen_le_levi (fun _ hX => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hX) hk
  have hY₁ : conjSub F k ∈ Δ := conjSub_mem h hA hAne hA₀ hΔ hF hkV
  have hY₁l : conjSub F k ∈ lambdaSet R E₁ := by
    have := conjSub_mem_lambdaSet hR hFE k
    rwa [hEk] at this
  obtain ⟨E₁', hE₁', hopp⟩ := exists_opposite_mem h hA hAne hA₀ hΔ hE₁
  have hE₁R := hRΔ hE₁
  have hE₁'R := hRΔ hE₁'
  have hBE₁' : B ∈ lambdaSet R E₁' := by
    have hnc : ¬ Commuting E₁' (conjSub F k) :=
      not_commuting_of_opposite_of_mem_lambdaSet hR hE₁'R hopp.symm hY₁l
    have hne : E₁' ≠ conjSub F k := fun e => hnc (by rw [← e]; exact hR.commuting_self hE₁'R)
    rcases hR.rel E₁' hE₁'R (conjSub F k) (hRΔ hY₁) hne with hc | ho | hs
    · exact absurd hc hnc
    ·
      obtain ⟨D, ⟨hDR, hDle, hDψ⟩, -⟩ :=
        existsUnique_mem_psiSet_of_le hR hiso hE₁R hE₁'R hopp hY₁l
      have hDΔ : D ∈ Δ :=
        mem_of_le_gen h hA hAne hA₀ hΔ hDR (hDle.trans (sup_le (le_gen hE₁) (le_gen hY₁)))
      have hDne : E₁ ≠ D := fun e =>
        Special.not_opposite hR hE₁'R hDψ.2 (by rw [← e]; exact hopp.symm)
      have hDl : D ∈ lambdaSet R E₁ :=
        (mem_lambdaSet_of_le_sup hR hiso hE₁R hY₁l hE₁R le_sup_left hDR hDle hDne).1
      exact hpsi hDΔ (hstar hE₁ hBE₁ hDΔ hDl) hE₁' hDψ.2.symm
    · exact hpsi hY₁ (hstar hE₁ hBE₁ hY₁ hY₁l) hE₁' hs.symm
  exact not_commuting_of_opposite_of_mem_lambdaSet hR hE₁'R hopp.symm hBE₁ hBE₁'.1.2.2

theorem not_special_of_notMem (h3 : OrbitCollinear R A A₀ Blk) {Δ : Set (Subgroup G)}
    (hΔ : Δ ∈ leviComps R A A₀) (hout : ∀ Y ∈ Δ, Y ∉ Blk) {X Y : Subgroup G} (hX : X ∈ Δ)
    (hY : Y ∈ Δ) : ¬ Special R X Y := by
  intro hs
  have := h.finite
  have hXR : X ∈ R := (mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hX).1.1
  have hYR : Y ∈ R := (mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hY).1.1
  have hW : ⁅X, Y⁆ ∈ Δ :=
    mem_of_le_gen h hA hAne hA₀ hΔ hs.1 (QD.commutator_le_of_le (le_gen hX) (le_gen hY))
  exact notMem_lambdaSet_of_notMem h hA hAne hmax hA₀ hBlk hcl h3 hΔ hout hX hW
    (mem_lambdaSet_comm hs.1 (mem_lambdaSet_commutator h.root h.noIsolated hXR hYR hs).1)

theorem collinearComp_of_notMem (h3 : OrbitCollinear R A A₀ Blk) {Δ : Set (Subgroup G)}
    (hΔ : Δ ∈ leviComps R A A₀) (hout : ∀ Y ∈ Δ, Y ∉ Blk) : CollinearComp R A A₀ Δ := by
  intro Y hY X hX hYX
  have hdeg := fun X' (hX' : X' ∈ Δ) Y' (hY' : Y' ∈ Δ) =>
    not_special_of_notMem h hA hAne hmax hA₀ hBlk hcl h3 hΔ hout hX' hY'
  obtain ⟨E₀, hE₀, rfl⟩ := hΔ
  have heq := sigmaSet_inter_lambdaStar_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hE₀ hdeg hY
  have hYl := comp_subset h hA hAne hA₀ hE₀ hY
  have hmem : X ∈ sigmaSet R Y ∩ lambdaStar R A A₀ :=
    ⟨⟨hX.1.1.1, (ne_of_mem_leviSet h hA hA₀ hX hYl).symm, hYX⟩, hX⟩
  rw [heq] at hmem
  exact hmem.1

end Six

end Sec9

end CFSG.Timmesfeld.ARS

module

public import CFSG.Timmesfeld.ARS.Sec9Six
public import CFSG.Timmesfeld.ARS.Sec9Natural

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open _root_.CFSG.Timmesfeld.ARS.Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec9

section Three

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  {Δ₁ : Set (Subgroup G)} (hΔ₁ : Δ₁ ∈ leviComps R A A₀) {B X : Subgroup G}
  (hB : B ∈ lambdaStar R A A₀) (hX : X ∈ lambdaStar R A A₀)
  (hno : ∀ D ∈ orbit Δ₁ B, ∀ Y ∈ orbit Δ₁ X, Y ∉ lambdaSet R D)
  (hBO : ∀ D ∈ orbit Δ₁ B, D ∉ orbit Δ₁ X)
include h hA hAne hmax hA₀ hΔ₁ hB hX hno hBO

omit hmax hX hno hBO in
theorem mem_orbit_of_le_sup {D C₁ P : Subgroup G} (hD : D ∈ orbit Δ₁ B)
    (hC₁ : C₁ ∈ orbit Δ₁ B) (hDC₁ : C₁ ∈ lambdaSet R D) (hP : P ∈ R) (hPle : P ≤ D ⊔ C₁) :
    P ∈ orbit Δ₁ B := by
  have := h.finite
  have hR := h.root
  have hΔl : Δ₁ ⊆ leviSet R A A₀ := fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hY
  have hcl₁ := (isBlock_of_mem h hA hAne hA₀ hΔ₁).2
  have hDst := orbit_subset_lambdaStar hR hΔl hB hD
  have hC₁st := orbit_subset_lambdaStar hR hΔl hB hC₁
  have hC₁R : C₁ ∈ R := hC₁st.1.1.1
  obtain ⟨Y, hYl, hDY⟩ := exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hDst hC₁st
    (mem_lambdaSet_comm hDst.1.1.1 hDC₁)
  have hsDY : Special R D Y := by
    refine (special_of_not_commuting h hA hYl hDst fun hc => ?_).symm
    have h0 := commuting_iff_commutator_eq_bot.1 hc.symm
    rw [hDY] at h0
    exact hR.ne_bot _ hC₁R h0
  have hYΔ : Y ∈ Δ₁ := by
    by_contra hYout
    obtain ⟨g, hg, hDg⟩ := exists_conjSub_eq_of_mem_orbit hD hC₁
    have hYg : conjSub Y g = Y := conjSub_of_forall_commute fun y hy =>
      (commute_of_mem_gen h hA hAne hA₀ hΔl hcl₁ hYl hYout hy hg).symm
    have h1 : ⁅C₁, Y⁆ = conjSub C₁ g :=
      calc ⁅C₁, Y⁆ = ⁅conjSub D g, conjSub Y g⁆ := by rw [hDg, hYg]
        _ = conjSub ⁅D, Y⁆ g := (Subgroup.map_commutator _ _ _).symm
        _ = conjSub C₁ g := by rw [hDY]
    have h2 : ⁅C₁, Y⁆ = ⊥ := by
      have := hsDY.2.2
      rw [hDY] at this
      exact commuting_iff_commutator_eq_bot.1 this
    exact hR.ne_bot _ (hR.conjSub_mem hC₁R g) (h1 ▸ h2)
  obtain ⟨D', hD', hYD', hpts⟩ := natural_points h hA hAne hA₀ hYl hDst hsDY
  obtain ⟨-, g, hg, hDg⟩ := hpts P hP (hDY ▸ hPle)
  rw [← hDg]
  exact conjSub_mem_orbit hD
    (sup_le (le_gen (mem_of_opposite h hA hAne hA₀ hΔ₁ hYΔ hD' hYD')) (le_gen hYΔ) hg)

omit hmax in
theorem commuting_of_mem_orbit_of_mem_lambdaSet {D E C : Subgroup G} (hD : D ∈ orbit Δ₁ B)
    (hE : E ∈ Δ₁) (hDE : D ∈ lambdaSet R E) (hC : C ∈ orbit Δ₁ X) (hCD : Commuting C D) :
    Commuting E C := by
  have := h.finite
  have hR := h.root
  have hΔl : Δ₁ ⊆ leviSet R A A₀ := fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hY
  have hEl := hΔl hE
  have hER : E ∈ R := hEl.1.1
  have hCst := orbit_subset_lambdaStar hR hΔl hX hC
  have hCR : C ∈ R := hCst.1.1.1
  have hDR : D ∈ R := (orbit_subset_lambdaStar hR hΔl hB hD).1.1.1
  by_contra hEC
  have hs : Special R E C := special_of_not_commuting h hA hEl hCst hEC
  obtain ⟨D', hD', hED', hpts⟩ := natural_points h hA hAne hA₀ hEl hCst hs.symm
  obtain ⟨-, g, hg, hCg⟩ := hpts ⁅C, E⁆ hs.symm.1 le_sup_right
  have hWO : ⁅C, E⁆ ∈ orbit Δ₁ X := by
    rw [← hCg]
    exact conjSub_mem_orbit hC
      (sup_le (le_gen (mem_of_opposite h hA hAne hA₀ hΔ₁ hE hD' hED')) (le_gen hE) hg)
  have hle : ⁅C, E⁆ ≤ M R D := by
    rw [Subgroup.commutator_comm]
    exact commutator_le_of_le_normalizer (QD.le_M (mem_lambdaSet_comm hER hDE))
      (QD.le_normalizer_M hR hDR ⟨hCR, hCD.symm⟩)
  have hmem : ⁅C, E⁆ ∈ {Z | Z ∈ R ∧ Z ≤ M R D} := ⟨hs.symm.1, hle⟩
  rw [(Q_eq_M h hDR).2.1] at hmem
  rcases hmem with e | hl
  · exact hBO D hD (by rw [← e]; exact hWO)
  · exact hno D hD _ hWO hl

theorem notMem_lambdaSet_of_mem_orbit {D E C₁ : Subgroup G} (hD : D ∈ orbit Δ₁ B) (hE : E ∈ Δ₁)
    (hDE : D ∈ lambdaSet R E) (hC₁ : C₁ ∈ orbit Δ₁ B) (hDC₁ : C₁ ∈ lambdaSet R D) :
    C₁ ∉ lambdaSet R E := by
  intro hC₁E
  have := h.finite
  have hR := h.root
  have hΔl : Δ₁ ⊆ leviSet R A A₀ := fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hY
  have hEl := hΔl hE
  have hER : E ∈ R := hEl.1.1
  have hDst := orbit_subset_lambdaStar hR hΔl hB hD
  have hC₁st := orbit_subset_lambdaStar hR hΔl hB hC₁
  have hcomm : ∀ Z ∈ orbit Δ₁ X, Commuting E Z := by
    intro Z hZ
    have hZst := orbit_subset_lambdaStar hR hΔl hX hZ
    obtain ⟨P, hPR, hPle, hZP⟩ := exists_commuting_of_le_M h hA hDst.1.1.1 hDC₁
      (sup_le (QD.le_M hDst.1) (QD.le_M hC₁st.1)) hZst.1.1.1 (QD.le_M hZst.1)
    have hPO := mem_orbit_of_le_sup h hA hAne hA₀ hΔ₁ hB hD hC₁ hDC₁ hPR hPle
    have hPst := orbit_subset_lambdaStar hR hΔl hB hPO
    have hPE : P ∈ lambdaSet R E := by
      have hmem : P ∈ {Y | Y ∈ R ∧ Y ≤ M R E} :=
        ⟨hPR, hPle.trans (sup_le (QD.le_M hDE) (QD.le_M hC₁E))⟩
      rw [(Q_eq_M h hER).2.1] at hmem
      exact hmem.resolve_left fun e => ne_of_mem_leviSet h hA hA₀ hPst hEl e.symm
    exact commuting_of_mem_orbit_of_mem_lambdaSet h hA hAne hA₀ hΔ₁ hB hX hno hBO hPO hE hPE hZ
      hZP
  refine not_forall_commuting h hA hAne hA₀ hmax hΔ₁ hX fun E' hE' => ?_
  obtain ⟨k, hk, hkE⟩ := exists_conjSub_eq h hΔ₁ hE hE'
  have h1 := (hcomm (conjSub X k⁻¹) ⟨k⁻¹, Subgroup.inv_mem _ hk, rfl⟩).conjSub k
  rwa [hkE, Plane.conjSub_inv_conjSub] at h1

theorem commuting_of_commuting_of_mem_orbit {D E Y : Subgroup G} (hD : D ∈ orbit Δ₁ B)
    (hE : E ∈ Δ₁) (hDE : D ∈ lambdaSet R E) (hY : Y ∈ Δ₁) (hEY : Commuting E Y) :
    Commuting Y D := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hΔl : Δ₁ ⊆ leviSet R A A₀ := fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hY
  have hYl := hΔl hY
  have hYR : Y ∈ R := hYl.1.1
  have hDst := orbit_subset_lambdaStar hR hΔl hB hD
  have hDR : D ∈ R := hDst.1.1.1
  by_contra hYD
  have hs : Special R Y D := special_of_not_commuting h hA hYl hDst hYD
  obtain ⟨y, hy, hy1⟩ := hR.exists_ne_one hYR
  have hne : conjSub D y ≠ D := Sec3.conjSub_ne_of_special hR hiso hYR hDR hs hy hy1
  have hDyO : conjSub D y ∈ orbit Δ₁ B := conjSub_mem_orbit hD (le_gen hY hy)
  have hDyl : conjSub D y ∈ lambdaSet R D := by
    have hW : ⁅D, Y⁆ ∈ lambdaSet R D :=
      mem_lambdaSet_comm hs.symm.1 (mem_lambdaSet_commutator hR hiso hDR hYR hs.symm).1
    exact (mem_lambdaSet_of_le_sup hR hiso hDR hW hDR le_sup_left (hR.conjSub_mem hDR y)
      ((conjSub_le_commutator_sup hy).trans (sup_comm _ _).le) hne.symm).1
  have hDyE : conjSub D y ∈ lambdaSet R E := by
    have := conjSub_mem_lambdaSet hR hDE y
    rwa [conjSub_of_forall_commute fun e he => (hEY e he y hy).symm] at this
  exact notMem_lambdaSet_of_mem_orbit h hA hAne hmax hA₀ hΔ₁ hB hX hno hBO hD hE hDE hDyO hDyl
    hDyE

theorem false_of_special_pair {Y₀ Y₀' : Subgroup G} (hY₀ : Y₀ ∈ Δ₁) (hY₀' : Y₀' ∈ Δ₁)
    (hs₀ : Special R Y₀ Y₀') : False := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hΔl : Δ₁ ⊆ leviSet R A A₀ := fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hY
  have hcl₁ := (isBlock_of_mem h hA hAne hA₀ hΔ₁).2
  have hRΔ : ∀ {Y : Subgroup G}, Y ∈ Δ₁ → Y ∈ R := fun hY => (hΔl hY).1.1
  have hVΔ : ∀ {Y : Subgroup G} {g : G}, Y ∈ Δ₁ → g ∈ gen Δ₁ → conjSub Y g ∈ Δ₁ :=
    fun hY hg => conjSub_mem h hA hAne hA₀ hΔ₁ hY (gen_le_levi hΔl hg)
  have hBR : B ∈ R := hB.1.1.1
  have hstar := fun {D E C₁ : Subgroup G} => @notMem_lambdaSet_of_mem_orbit G _ R h A A₀ hA hAne
    hmax hA₀ Δ₁ hΔ₁ B X hB hX hno hBO D E C₁
  obtain ⟨D, hD, E₁, hE₁, E₂, hE₂, hDE₁, hDE₂, hE₂E₁⟩ : ∃ D ∈ orbit Δ₁ B, ∃ E₁ ∈ Δ₁,
      ∃ E₂ ∈ Δ₁, D ∈ lambdaSet R E₁ ∧ D ∈ lambdaSet R E₂ ∧ E₂ ∈ lambdaSet R E₁ := by
    obtain ⟨E, hE, hBE⟩ := exists_mem_lambdaSet h hA hAne hmax hA₀ hΔ₁ hB
    have hER := hRΔ hE
    obtain ⟨k, hk, hkE⟩ := exists_conjSub_eq h hΔ₁ hY₀ hE
    have hF : conjSub Y₀' k ∈ Δ₁ := hVΔ hY₀' hk
    have hsEF : Special R E (conjSub Y₀' k) := by
      have := Sec3.special_conjSub hR hs₀ k
      rwa [hkE] at this
    set F := conjSub Y₀' k with hFdef
    have hFl := hΔl hF
    have hFR : F ∈ R := hFl.1.1
    obtain ⟨f, hf, hf1⟩ := hR.exists_ne_one hFR
    have hfV : f ∈ gen Δ₁ := le_gen hF hf
    have hEf : conjSub E f ∈ Δ₁ := hVΔ hE hfV
    by_cases hFB : Commuting F B
    ·
      refine ⟨B, mem_orbit_self Δ₁ B, E, hE, conjSub E f, hEf, hBE, ?_, ?_⟩
      · have := conjSub_mem_lambdaSet hR hBE f
        rwa [conjSub_of_forall_commute fun b hb => hFB f hf b hb] at this
      · have hW : ⁅E, F⁆ ∈ lambdaSet R E :=
          mem_lambdaSet_comm hsEF.1 (mem_lambdaSet_commutator hR hiso hER hFR hsEF).1
        exact (mem_lambdaSet_of_le_sup hR hiso hER hW hER le_sup_left (hR.conjSub_mem hER f)
          ((conjSub_le_commutator_sup hf).trans (sup_comm _ _).le)
          (Sec3.conjSub_ne_of_special hR hiso hFR hER hsEF.symm hf hf1).symm).1
    have hsFB : Special R F B := special_of_not_commuting h hA hFl hB hFB
    obtain ⟨D'', hD'', hFD'', hpts⟩ := natural_points h hA hAne hA₀ hFl hB hsFB.symm
    obtain ⟨-, g, hg, hBg⟩ := hpts ⁅B, F⁆ hsFB.symm.1 le_sup_right
    have hB'O : ⁅B, F⁆ ∈ orbit Δ₁ B := by
      rw [← hBg]
      exact conjSub_mem_orbit (mem_orbit_self Δ₁ B)
        (sup_le (le_gen (mem_of_opposite h hA hAne hA₀ hΔ₁ hF hD'' hFD'')) (le_gen hF) hg)
    have hB'F : ⁅B, F⁆ ∈ lambdaSet R F :=
      mem_lambdaSet_comm hsFB.symm.1 (mem_lambdaSet_commutator hR hiso hBR hFR hsFB.symm).2
    rcases commuting_or_special_conjSub hR hiso hBR hFR hER hsFB.symm hsEF.symm hBE.1.2.2.symm hf
      hf1 with ⟨-, h2⟩ | ⟨h1, h2⟩
    ·
      have hEB' : Commuting E ⁅B, F⁆ := by
        have h3 : Commuting E (B ⊔ conjSub B f) := Commuting.sup_right hBE.1.2.2 h2.symm
        rw [sup_conjSub_eq_sup_commutator hR hiso hBR hFR hsFB.symm hf hf1] at h3
        exact h3.mono le_rfl le_sup_right
      obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
      refine ⟨⁅B, F⁆, hB'O, F, hF, conjSub F e, hVΔ hF (le_gen hE he), hB'F, ?_, ?_⟩
      · have := conjSub_mem_lambdaSet hR hB'F e
        rwa [conjSub_of_forall_commute fun x hx => hEB' e he x hx] at this
      · have hW : ⁅F, E⁆ ∈ lambdaSet R F :=
          mem_lambdaSet_comm hsEF.symm.1 (mem_lambdaSet_commutator hR hiso hFR hER hsEF.symm).1
        exact (mem_lambdaSet_of_le_sup hR hiso hFR hW hFR le_sup_left (hR.conjSub_mem hFR e)
          ((conjSub_le_commutator_sup he).trans (sup_comm _ _).le)
          (Sec3.conjSub_ne_of_special hR hiso hER hFR hsEF he he1).symm).1
    ·
      exfalso
      have hEfR : conjSub E f ∈ R := hR.conjSub_mem hER f
      have hBfR : conjSub B f ∈ R := hR.conjSub_mem hBR f
      obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hBR
      obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
      have hbe : b * e ∈ rootElts R := by
        have hEB : E ≠ B := ne_of_mem_leviSet h hA hA₀ hB (hΔl hE)
        have hbe1 : b * e ≠ 1 := by
          intro e1
          have hbE : b ∈ B ⊓ E := ⟨hb, by
            rw [mul_eq_one_iff_eq_inv] at e1
            rw [e1]
            exact E.inv_mem he⟩
          rw [inf_eq_bot hR hiso hBR hER hEB.symm, Subgroup.mem_bot] at hbE
          exact hb1 hbE
        obtain ⟨C, hC, -, hbeC⟩ := hBE.2 (b * e)
          (Subgroup.mul_mem _ (Subgroup.mem_sup_right hb) (Subgroup.mem_sup_left he)) hbe1
        exact ⟨C, hC, hbeC, hbe1⟩
      have heq := commutator_conjSub_eq hR hiso hBR hFR hER hsFB.symm hsEF.symm hBE.1.2.2.symm hb
        hb1 he he1 hbe hf hf1
      have hWR : ⁅B, conjSub E f⁆ ∈ R := h1.1
      have hWB : ⁅B, conjSub E f⁆ ∈ lambdaSet R B :=
        mem_lambdaSet_comm hWR (mem_lambdaSet_commutator hR hiso hBR hEfR h1).1
      have hWE : ⁅B, conjSub E f⁆ ∈ lambdaSet R E := by
        have := (mem_lambdaSet_commutator hR hiso hBfR hER h2).2
        rw [← heq] at this
        exact mem_lambdaSet_comm hWR this
      have hWO : ⁅B, conjSub E f⁆ ∈ orbit Δ₁ B := by
        obtain ⟨D₃, hD₃, hEfD₃, hpts₃⟩ := natural_points h hA hAne hA₀ (hΔl hEf) hB h1
        obtain ⟨-, g₃, hg₃, hBg₃⟩ := hpts₃ _ hWR le_sup_right
        rw [← hBg₃]
        exact conjSub_mem_orbit (mem_orbit_self Δ₁ B)
          (sup_le (le_gen (mem_of_opposite h hA hAne hA₀ hΔ₁ hEf hD₃ hEfD₃)) (le_gen hEf) hg₃)
      exact hstar (mem_orbit_self Δ₁ B) hE hBE hWO hWB hWE
  have hDst := orbit_subset_lambdaStar hR hΔl hB hD
  have hDR : D ∈ R := hDst.1.1.1
  have hE₁R := hRΔ hE₁
  have hE₂R := hRΔ hE₂
  obtain ⟨F, hF, hE₁F⟩ := exists_opposite_mem h hA hAne hA₀ hΔ₁ hE₁
  have hFR := hRΔ hF
  obtain ⟨E₃, hE₃, hDE₃, hsE₃⟩ : ∃ E₃ ∈ Δ₁, D ∈ lambdaSet R E₃ ∧ Special R E₃ F := by
    have hnc : ¬ Commuting F E₂ := not_commuting_of_opposite_of_mem_lambdaSet hR hFR hE₁F.symm hE₂E₁
    have hne : F ≠ E₂ := fun e => hnc (by rw [← e]; exact hR.commuting_self hFR)
    rcases hR.rel F hFR E₂ hE₂R hne with hc | ho | hs
    · exact absurd hc hnc
    · obtain ⟨E₃, ⟨hE₃R, hE₃le, hE₃ψ⟩, -⟩ :=
        existsUnique_mem_psiSet_of_le hR hiso hE₁R hFR hE₁F hE₂E₁
      have hE₃Δ : E₃ ∈ Δ₁ := mem_of_le_gen h hA hAne hA₀ hΔ₁ hE₃R
        (hE₃le.trans (sup_le (le_gen hE₁) (le_gen hE₂)))
      refine ⟨E₃, hE₃Δ, ?_, hE₃ψ.2.symm⟩
      have hmem : E₃ ∈ {Y | Y ∈ R ∧ Y ≤ M R D} := ⟨hE₃R, hE₃le.trans
        (sup_le (QD.le_M (mem_lambdaSet_comm hE₁R hDE₁)) (QD.le_M (mem_lambdaSet_comm hE₂R hDE₂)))⟩
      rw [(Q_eq_M h hDR).2.1] at hmem
      exact mem_lambdaSet_comm hDR
        (hmem.resolve_left fun e => ne_of_mem_leviSet h hA hA₀ hDst (hΔl hE₃Δ) e)
    · exact ⟨E₂, hE₂, hDE₂, hs.symm⟩
  have hE₃R := hRΔ hE₃
  obtain ⟨v, hv, hDv⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hDst hX
  have hcomm₁ : Commuting (gen Δ₁) (gen {Y | Y ∈ leviSet R A A₀ ∧ Y ∉ Δ₁}) :=
    commuting_gen_gen fun Y hY Y' hY' =>
      (commuting_of_notMem h hA hAne hA₀ hΔl hcl₁ hY'.1 hY'.2 hY).symm
  have hvle : v ∈ gen Δ₁ ⊔ gen {Y | Y ∈ leviSet R A A₀ ∧ Y ∉ Δ₁} := by
    refine (gen_le fun Y hY => ?_ : levi R A A₀ ≤ _) hv
    by_cases hYΔ : Y ∈ Δ₁
    · exact le_sup_of_le_left (le_gen hYΔ)
    · exact le_sup_of_le_right (le_gen ⟨hY, hYΔ⟩)
  have hN : gen Δ₁ ≤ Subgroup.normalizer
      ((gen {Y | Y ∈ leviSet R A A₀ ∧ Y ∉ Δ₁} : Subgroup G) : Set G) := fun x hx =>
    conjSub_eq_self_iff.1 (conjSub_of_forall_commute fun y hy => hcomm₁ x hx y hy)
  have hv' : v ∈ ((gen Δ₁ ⊔ gen {Y | Y ∈ leviSet R A A₀ ∧ Y ∉ Δ₁} : Subgroup G) : Set G) := hvle
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hN] at hv'
  obtain ⟨v₁, hv₁, w, hw, rfl⟩ := hv'
  have hDw : conjSub D w ∈ orbit Δ₁ X :=
    ⟨v₁⁻¹, Subgroup.inv_mem _ hv₁, by
      change conjSub X v₁⁻¹ = conjSub D w
      rw [← hDv, conjSub_mul, Plane.conjSub_conjSub_inv]⟩
  have hwΔ : ∀ {Y : Subgroup G}, Y ∈ Δ₁ → conjSub Y w = Y := fun hY =>
    conjSub_of_forall_commute fun y hy => (hcomm₁ y (le_gen hY hy) w hw).symm
  obtain ⟨f, hf, hf1⟩ := hR.exists_ne_one hFR
  have hfV : f ∈ gen Δ₁ := le_gen hF hf
  set D₂ := conjSub (conjSub D f) w with hD₂def
  have hD₂O : D₂ ∈ orbit Δ₁ X := by
    have e : D₂ = conjSub (conjSub D w) f := by
      rw [hD₂def, ← conjSub_mul, ← conjSub_mul, (hcomm₁ f hfV w hw).eq]
    rw [e]
    exact conjSub_mem_orbit hDw hfV
  have hD₂st := orbit_subset_lambdaStar hR hΔl hX hD₂O
  have hD₂R : D₂ ∈ R := hD₂st.1.1.1
  have hD₂l : ∀ {Y : Subgroup G}, Y ∈ Δ₁ → D ∈ lambdaSet R Y →
      D₂ ∈ lambdaSet R (conjSub Y f) := fun hY hDY => by
    have := conjSub_mem_lambdaSet hR (conjSub_mem_lambdaSet hR hDY f) w
    rwa [hwΔ (hVΔ hY hfV)] at this
  by_cases hDD₂ : Commuting D D₂
  ·
    have hEf : conjSub E₁ f ∈ Δ₁ := hVΔ hE₁ hfV
    have hEfl := hΔl hEf
    have hEfR : conjSub E₁ f ∈ R := hEfl.1.1
    have hopp : Opposite E₁ (conjSub E₁ f) := Sec5.opposite_conjSub_self hE₁F hf hf1
    have hsD : Special R (conjSub E₁ f) D := special_of_not_commuting h hA hEfl hDst
      (not_commuting_of_opposite_of_mem_lambdaSet hR hEfR hopp.symm hDE₁)
    obtain ⟨D₃, hD₃, hEfD₃, hpts₃⟩ := natural_points h hA hAne hA₀ hEfl hDst hsD.symm
    obtain ⟨-, g₃, hg₃, hDg₃⟩ := hpts₃ ⁅D, conjSub E₁ f⁆ hsD.symm.1 le_sup_right
    have hWO : ⁅D, conjSub E₁ f⁆ ∈ orbit Δ₁ B := by
      rw [← hDg₃]
      exact conjSub_mem_orbit hD
        (sup_le (le_gen (mem_of_opposite h hA hAne hA₀ hΔ₁ hEf hD₃ hEfD₃)) (le_gen hEf) hg₃)
    have hle : ⁅D, conjSub E₁ f⁆ ≤ M R D₂ := by
      rw [Subgroup.commutator_comm]
      exact commutator_le_of_le_normalizer (QD.le_M (mem_lambdaSet_comm hEfR (hD₂l hE₁ hDE₁)))
        (QD.le_normalizer_M hR hD₂R ⟨hDR, hDD₂.symm⟩)
    have hmem : ⁅D, conjSub E₁ f⁆ ∈ {Y | Y ∈ R ∧ Y ≤ M R D₂} := ⟨hsD.symm.1, hle⟩
    rw [(Q_eq_M h hD₂R).2.1] at hmem
    rcases hmem with e | hl
    · exact hBO _ hWO (by rw [e]; exact hD₂O)
    · exact hno _ hWO D₂ hD₂O (mem_lambdaSet_comm hD₂R hl)
  ·
    have hE₃f : conjSub E₃ f ∈ Δ₁ := hVΔ hE₃ hfV
    have hE₃fD := commuting_of_commuting_of_mem_orbit h hA hAne hmax hA₀ hΔ₁ hB hX hno hBO hD hE₃
      hDE₃ hE₃f (commuting_conjSub_of_special hR hE₃R hsE₃ hf)
    exact hDD₂ (commuting_of_mem_lambdaSet_of_commuting h hA hA₀ (hΔl hE₃f) hD₂st.1 hDst.1
      (hD₂l hE₃ hDE₃) hE₃fD).symm

theorem isSL2Comp_of_not_special
    (h813 : ∀ E ∈ Δ₁, ∀ E' ∈ Δ₁, (∀ Z ∈ leviSet R A A₀, Commuting E Z ↔ Commuting E' Z) →
      E = E')
    (hdeg : ∀ Y ∈ Δ₁, ∀ Y' ∈ Δ₁, ¬ Special R Y Y') : IsSL2Comp Δ₁ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hΔl : Δ₁ ⊆ leviSet R A A₀ := fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hY
  have hcl₁ := (isBlock_of_mem h hA hAne hA₀ hΔ₁).2
  have hRΔ : ∀ {Y : Subgroup G}, Y ∈ Δ₁ → Y ∈ R := fun hY => (hΔl hY).1.1
  have hBR : B ∈ R := hB.1.1.1
  have hdich := fun {D E Y : Subgroup G} => @commuting_of_commuting_of_mem_orbit G _ R h A A₀ hA
    hAne hmax hA₀ Δ₁ hΔ₁ B X hB hX hno hBO D E Y
  have hD1 : ∀ {Y P : Subgroup G}, Y ∈ Δ₁ → P ∈ lambdaStar R A A₀ → Commuting Y P →
      P ∈ lambdaSet R Y := by
    obtain ⟨E₀, hE₀, rfl⟩ := id hΔ₁
    intro Y P hY hP hYP
    have heq := sigmaSet_inter_lambdaStar_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hE₀ hdeg hY
    have hmem : P ∈ sigmaSet R Y ∩ lambdaStar R A A₀ :=
      ⟨⟨hP.1.1.1, (ne_of_mem_leviSet h hA hA₀ hP (hΔl hY)).symm, hYP⟩, hP⟩
    rw [heq] at hmem
    exact hmem.1
  have hpair : ∀ {D Y Z : Subgroup G}, Y ∈ Δ₁ → Z ∈ Δ₁ → D ∈ lambdaSet R Y →
      D ∈ lambdaSet R Z → Commuting Y Z := by
    intro D Y Z hY hZ hDY hDZ
    by_cases hYZ : Y = Z
    · rw [hYZ]
      exact hR.commuting_self (hRΔ hZ)
    rcases hR.rel Y (hRΔ hY) Z (hRΔ hZ) hYZ with hc | ho | hs
    · exact hc
    · exact absurd hDZ.1.2.2 (not_commuting_of_opposite_of_mem_lambdaSet hR (hRΔ hZ) ho.symm hDY)
    · exact absurd hs (hdeg Y hY Z hZ)
  have hD2 : ∀ {D E Y : Subgroup G}, D ∈ orbit Δ₁ B → E ∈ Δ₁ → D ∈ lambdaSet R E → Y ∈ Δ₁ →
      Commuting E Y → Y = E := by
    intro D E Y hD hE hDE hY hEY
    have hDst := orbit_subset_lambdaStar hR hΔl hB hD
    have hDY : D ∈ lambdaSet R Y := hD1 hY hDst (hdich hD hE hDE hY hEY)
    refine (h813 E hE Y hY fun Z hZ => ?_).symm
    by_cases hZΔ : Z ∈ Δ₁
    · exact ⟨fun hEZ => hpair hY hZΔ hDY (hD1 hZΔ hDst (hdich hD hE hDE hZΔ hEZ)),
        fun hYZ => hpair hE hZΔ hDE (hD1 hZΔ hDst (hdich hD hY hDY hZΔ hYZ))⟩
    · exact ⟨fun _ => (commuting_of_notMem h hA hAne hA₀ hΔl hcl₁ hZ hZΔ hY).symm,
        fun _ => (commuting_of_notMem h hA hAne hA₀ hΔl hcl₁ hZ hZΔ hE).symm⟩
  obtain ⟨E, hE, hBE⟩ := exists_mem_lambdaSet h hA hAne hmax hA₀ hΔ₁ hB
  have hopp : ∀ {Y Y' : Subgroup G}, Y ∈ Δ₁ → Y' ∈ Δ₁ → Y ≠ Y' → Opposite Y Y' := by
    intro Y Y' hY hY' hne
    rcases hR.rel Y (hRΔ hY) Y' (hRΔ hY') hne with hc | ho | hs
    · obtain ⟨k, hk, hkY⟩ := exists_conjSub_eq h hΔ₁ hE hY
      have hBkY : conjSub B k ∈ lambdaSet R Y := by
        have := conjSub_mem_lambdaSet hR hBE k
        rwa [hkY] at this
      exact absurd (hD2 ⟨k, hk, rfl⟩ hY hBkY hY' hc) (Ne.symm hne)
    · exact ho
    · exact absurd hs (hdeg Y hY Y' hY')
  obtain ⟨F, hF, hEF⟩ := exists_opposite_mem h hA hAne hA₀ hΔ₁ hE
  have hFB : Special R F B := special_of_not_commuting h hA (hΔl hF) hB
    (not_commuting_of_opposite_of_mem_lambdaSet hR (hRΔ hF) hEF.symm hBE)
  have hg2 : E ⊔ F ≤ gen Δ₁ := sup_le (le_gen hE) (le_gen hF)
  refine ⟨E, hE, F, hF, hEF, le_antisymm (gen_le fun D' hD' => ?_) hg2⟩
  by_contra hD'le
  have hD'l := hΔl hD'
  have hD'R : D' ∈ R := hD'l.1.1
  have hDP : ∀ x ∈ E ⊔ F, Special R (conjSub B x) D' := by
    intro x hx
    have hxV : x ∈ levi R A A₀ := gen_le_levi hΔl (hg2 hx)
    have hEx : conjSub E x ∈ Δ₁ := conjSub_mem h hA hAne hA₀ hΔ₁ hE hxV
    have hne : conjSub E x ≠ D' := fun e => hD'le (e ▸ conjSub_le le_sup_left hx)
    have hnc : ¬ Commuting D' (conjSub B x) := not_commuting_of_opposite_of_mem_lambdaSet hR hD'R
      (hopp hD' hEx hne.symm) (conjSub_mem_lambdaSet hR hBE x)
    exact (special_of_not_commuting h hA hD'l (conjSub_mem_lambdaStar_of_mem_levi hR hB hxV)
      hnc).symm
  have hline := mem_lambdaSet_commutator_commutator h hA hAne hA₀ (hΔl hE) (hΔl hF) hEF hB hBE
    hFB hD'l hDP
  have hBD' : Special R B D' := by
    have := hDP 1 (Subgroup.one_mem _)
    rwa [conjSub_one] at this
  obtain ⟨x₀, hx₀, hBbx₀⟩ : ∃ x ∈ E ⊔ F, conjSub B x = ⁅F, B⁆ := by
    obtain ⟨p, hp, hp1⟩ := hR.exists_ne_one hFB.1
    obtain ⟨x, hx, hpx⟩ := Sec3.exists_mem_conjSub_of_mem_sup hR hiso (hRΔ hE) (hRΔ hF) hEF hBE
      ⟨hBR, hFB⟩ (Subgroup.mem_sup_right hp) hp1
    exact ⟨x, hx, Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hBR x) hFB.1 hpx hp hp1⟩
  have hBbO : ⁅F, B⁆ ∈ orbit Δ₁ B := ⟨x₀, hg2 hx₀, hBbx₀⟩
  have hBbst := orbit_subset_lambdaStar hR hΔl hB hBbO
  have hBbD' : Special R ⁅F, B⁆ D' := hBbx₀ ▸ hDP x₀ hx₀
  have hcO : ∀ {P : Subgroup G}, P ∈ orbit Δ₁ B → (hPst : P ∈ lambdaStar R A A₀) →
      Special R P D' → ⁅P, D'⁆ ∈ orbit Δ₁ B := fun hPO hPst hPD => by
    obtain ⟨D₃, hD₃, hD'D₃, hpts₃⟩ := natural_points h hA hAne hA₀ hD'l hPst hPD
    obtain ⟨-, g₃, hg₃, hPg₃⟩ := hpts₃ _ hPD.1 le_sup_right
    rw [← hPg₃]
    exact conjSub_mem_orbit hPO
      (sup_le (le_gen (mem_of_opposite h hA hAne hA₀ hΔ₁ hD' hD₃ hD'D₃)) (le_gen hD') hg₃)
  exact notMem_lambdaSet_of_mem_orbit h hA hAne hmax hA₀ hΔ₁ hB hX hno hBO
    (hcO (mem_orbit_self Δ₁ B) hB hBD') hD'
    (mem_lambdaSet_comm hBD'.1 (mem_lambdaSet_commutator hR hiso hBR hD'R hBD').2)
    (hcO hBbO hBbst hBbD') hline
    (mem_lambdaSet_comm hBbD'.1 (mem_lambdaSet_commutator hR hiso hFB.1 hD'R hBbD').2)

end Three

theorem orbitCollinear_of_not_isSL2Comp (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) {Δ₁ : Set (Subgroup G)} (hΔ₁ : Δ₁ ∈ leviComps R A A₀)
    (hS : ¬ IsSL2Comp Δ₁)
    (h813 : (∀ Y ∈ Δ₁, ∀ Y' ∈ Δ₁, ¬ Special R Y Y') → ∀ E ∈ Δ₁, ∀ E' ∈ Δ₁,
      (∀ Z ∈ leviSet R A A₀, Commuting E Z ↔ Commuting E' Z) → E = E') :
    OrbitCollinear R A A₀ Δ₁ := by
  intro B hB X hX
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hΔl : Δ₁ ⊆ leviSet R A A₀ := fun _ hY => mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hY
  have hBR : B ∈ R := hB.1.1.1
  by_cases hBO : B ∈ orbit Δ₁ X
  · obtain ⟨Y, hY, hBY⟩ := exists_special h hA hAne hmax hA₀ hΔ₁ hB
    obtain ⟨D', hD', hYD', hpts⟩ := natural_points h hA hAne hA₀ (hΔl hY) hB hBY
    obtain ⟨-, g, hg, hBg⟩ := hpts ⁅B, Y⁆ hBY.1 le_sup_right
    refine ⟨⁅B, Y⁆, ?_, mem_lambdaSet_comm hBY.1
      (mem_lambdaSet_commutator hR hiso hBR (hΔl hY).1.1 hBY).1⟩
    rw [← orbit_eq_of_mem hBO, ← hBg]
    exact conjSub_mem_orbit (mem_orbit_self Δ₁ B)
      (sup_le (le_gen (mem_of_opposite h hA hAne hA₀ hΔ₁ hY hD' hYD')) (le_gen hY) hg)
  by_contra hno₀
  simp only [not_exists, not_and] at hno₀
  have hBO' : ∀ D ∈ orbit Δ₁ B, D ∉ orbit Δ₁ X := fun D hD hDX =>
    hBO ((orbit_eq_of_mem_of_mem hD hDX) ▸ mem_orbit_self Δ₁ B)
  have hno : ∀ D ∈ orbit Δ₁ B, ∀ Y ∈ orbit Δ₁ X, Y ∉ lambdaSet R D := by
    rintro _ ⟨g, hg, rfl⟩ Y hY hYD
    refine hno₀ (conjSub Y g⁻¹) (conjSub_mem_orbit hY (Subgroup.inv_mem _ hg)) ?_
    have := conjSub_mem_lambdaSet hR hYD g⁻¹
    rwa [Plane.conjSub_conjSub_inv] at this
  by_cases hdeg : ∀ Y ∈ Δ₁, ∀ Y' ∈ Δ₁, ¬ Special R Y Y'
  · exact hS (isSL2Comp_of_not_special h hA hAne hmax hA₀ hΔ₁ hB hX hno hBO' (h813 hdeg) hdeg)
  · push Not at hdeg
    obtain ⟨Y₀, hY₀, Y₀', hY₀', hs₀⟩ := hdeg
    exact false_of_special_pair h hA hAne hmax hA₀ hΔ₁ hB hX hno hBO' hY₀ hY₀' hs₀

end Sec9

end CFSG.Timmesfeld.ARS

module

public import CFSG.Timmesfeld.ARS.Sec9Cases
public import CFSG.Timmesfeld.ARS.Sec9Natural
public import CFSG.Timmesfeld.ARS.Sec8Projection

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open _root_.CFSG.Timmesfeld.ARS.Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec9

section Single

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A)
  {Blk : Set (Subgroup G)} (hBlk : Blk ⊆ leviSet R A A₀)
  (hcl : ∀ Y ∈ Blk, comp R A A₀ Y ⊆ Blk) (h3 : OrbitCollinear R A A₀ Blk)
  {Δ₂ : Set (Subgroup G)} (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (h2out : ∀ Y ∈ Δ₂, Y ∉ Blk)
  (honly : ∀ X ∈ leviSet R A A₀, X ∉ Blk → X ∈ Δ₂) (hcol : CollinearComp R A A₀ Δ₂)
include h hA hAne hA₀ hBlk hcl h3 hΔ₂ h2out honly hcol

omit h3 honly hcol in
theorem exists_centralized_orbit {E : Subgroup G} (hE : E ∈ Δ₂) :
    ∃ X ∈ lambdaStar R A A₀, ∀ Z ∈ orbit Blk X, Commuting E Z := by
  have hEl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hE
  obtain ⟨X, hX, hEX⟩ := exists_commuting_mem_lambdaStar h hA hAne hA₀ hEl
  exact ⟨X, hX, fun Z hZ =>
    commuting_of_mem_orbit h hA hAne hA₀ hBlk hcl hEl (h2out E hE) hEX hZ⟩

omit hBlk hcl h3 h2out honly in
theorem commuting_of_commuting_commuting {E E' X : Subgroup G} (hE : E ∈ Δ₂) (hE' : E' ∈ Δ₂)
    (hX : X ∈ lambdaStar R A A₀) (hEX : Commuting E X) (hE'X : Commuting E' X) :
    Commuting E E' := by
  have := h.finite
  have hR := h.root
  have hEl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hE
  have hE'l := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hE'
  have hXE : E ∈ lambdaSet R X := mem_lambdaSet_comm hEl.1.1 (hcol E hE X hX hEX)
  have hXE' : E' ∈ lambdaSet R X := mem_lambdaSet_comm hE'l.1.1 (hcol E' hE' X hX hE'X)
  by_cases hee : E = E'
  · rw [← hee]
    exact hR.commuting_self hEl.1.1
  rcases hR.rel E hEl.1.1 E' hE'l.1.1 hee with hc | ho | hs
  · exact hc
  · exact absurd hE'X (not_commuting_of_opposite_of_mem_lambdaSet hR hE'l.1.1 ho.symm
      (hcol E hE X hX hEX))
  · exfalso
    have hle : ⁅E, E'⁆ ≤ X := by
      rw [← (Q_eq_M h hX.1.1.1).2.2.1]
      exact Subgroup.commutator_mono (QD.le_M hXE) (QD.le_M hXE')
    have heq : ⁅E, E'⁆ = X := Subgroup.eq_of_le_of_card_ge hle (hR.card_eq hX.1.1.1 hs.1).le
    exact ne_of_mem_leviSet h hA hA₀ hX (commutator_mem_leviSet hR hA hA₀ hEl hE'l hs) heq

omit honly in
theorem commuting_orbit_of_commuting {E E' X : Subgroup G} (hE : E ∈ Δ₂) (hE' : E' ∈ Δ₂)
    (hEE' : Commuting E E') (hX : X ∈ lambdaStar R A A₀)
    (hEX : ∀ Z ∈ orbit Blk X, Commuting E Z) : Commuting E' X := by
  have := h.finite
  have hR := h.root
  have hEl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hE
  have hE'l := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hE'
  refine commuting_of_normalizes h hA hAne hA₀ hBlk hcl hE'l (h2out E' hE') hX fun e' he' => ?_
  have hyB : ∀ g ∈ gen Blk, Commute e' g := fun g hg =>
    commute_of_mem_gen h hA hAne hA₀ hBlk hcl hE'l (h2out E' hE') he' hg
  have hXe : conjSub X e' ∈ lambdaStar R A A₀ :=
    conjSub_mem_lambdaStar_of_mem_levi hR hX (le_gen hE'l he')
  have hO' : ∀ Z ∈ orbit Blk (conjSub X e'), Commuting E Z := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 := (hEX (conjSub X g) ⟨g, hg, rfl⟩).conjSub e'
    rw [conjSub_of_forall_commute fun e he => (hEE' e he e' he').symm] at h1
    change Commuting E (conjSub (conjSub X e') g)
    rw [← conjSub_mul, ← (hyB g hg).eq, conjSub_mul]
    exact h1
  have heq := orbit_eq_of_commuting h hA hA₀ hBlk h3 hEl (hcol E hE) hXe hX hO' hEX
  rw [← heq]
  exact mem_orbit_self Blk (conjSub X e')

omit honly in
theorem not_special {E E' : Subgroup G} (hE : E ∈ Δ₂) (hE' : E' ∈ Δ₂) : ¬ Special R E E' := by
  have := h.finite
  have hR := h.root
  intro hs
  have hEl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hE
  have hE'l := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hE'
  have hDl := commutator_mem_leviSet hR hA hA₀ hEl hE'l hs
  have hD : ⁅E, E'⁆ ∈ Δ₂ := by
    obtain ⟨E₀, hE₀, rfl⟩ := hΔ₂
    exact mem_comp_of_le h hA hAne hA₀ hE₀ hs.1
      (QD.commutator_le_of_le (le_gen hE) (le_gen hE'))
  obtain ⟨X, hX, hDX⟩ := exists_centralized_orbit h hA hAne hA₀ hBlk hcl hΔ₂ h2out hD
  have hEX := commuting_orbit_of_commuting h hA hAne hA₀ hBlk hcl h3 hΔ₂ h2out hcol hD
    hE hs.2.1 hX hDX
  have hE'X := commuting_orbit_of_commuting h hA hAne hA₀ hBlk hcl h3 hΔ₂ h2out hcol hD
    hE' hs.2.2 hX hDX
  exact hs.not_commuting hR (commuting_of_commuting_commuting h hA hAne hA₀ hΔ₂ hcol hE hE' hX hEX
    hE'X)

theorem eq_of_commuting
    (h813 : ∀ E ∈ Δ₂, ∀ E' ∈ Δ₂, (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) →
      E = E')
    {E E' : Subgroup G} (hE : E ∈ Δ₂) (hE' : E' ∈ Δ₂) (hEE' : Commuting E E') : E = E' := by
  have key : ∀ {E E' : Subgroup G}, E ∈ Δ₂ → E' ∈ Δ₂ → Commuting E E' →
      ∀ Z ∈ leviSet R A A₀, Commuting E Z → Commuting E' Z := by
    intro E E' hE hE' hEE' Z hZ hEZ
    have hE'l := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hE'
    by_cases hZB : Z ∈ Blk
    · exact commuting_of_notMem h hA hAne hA₀ hBlk hcl hE'l (h2out E' hE') hZB
    have hZ2 := honly Z hZ hZB
    obtain ⟨X, hX, hEX⟩ := exists_centralized_orbit h hA hAne hA₀ hBlk hcl hΔ₂ h2out hE
    have hZX := commuting_orbit_of_commuting h hA hAne hA₀ hBlk hcl h3 hΔ₂ h2out hcol hE hZ2
      hEZ hX hEX
    have hE'X := commuting_orbit_of_commuting h hA hAne hA₀ hBlk hcl h3 hΔ₂ h2out hcol hE hE'
      hEE' hX hEX
    exact commuting_of_commuting_commuting h hA hAne hA₀ hΔ₂ hcol hE' hZ2 hX hE'X hZX
  exact h813 E hE E' hE' fun Z hZ => ⟨key hE hE' hEE' Z hZ, key hE' hE hEE'.symm Z hZ⟩

theorem opposite_of_ne
    (h813 : ∀ E ∈ Δ₂, ∀ E' ∈ Δ₂, (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) →
      E = E')
    {E E' : Subgroup G} (hE : E ∈ Δ₂) (hE' : E' ∈ Δ₂) (hEE' : E ≠ E') : Opposite E E' := by
  have := h.finite
  have hR := h.root
  rcases hR.rel E (mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hE).1.1 E'
    (mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hE').1.1 hEE' with hc | ho | hs
  · exact absurd (eq_of_commuting h hA hAne hA₀ hBlk hcl h3 hΔ₂ h2out honly hcol h813 hE hE' hc)
      hEE'
  · exact ho
  · exact absurd hs (not_special h hA hAne hA₀ hBlk hcl h3 hΔ₂ h2out hcol hE hE')

theorem le_sup_of_opposite
    (h813 : ∀ E ∈ Δ₂, ∀ E' ∈ Δ₂, (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) →
      E = E')
    {E F D : Subgroup G} (hE : E ∈ Δ₂) (hF : F ∈ Δ₂) (hEF : Opposite E F) (hD : D ∈ Δ₂) :
    D ≤ E ⊔ F := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hEl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hE
  have hFl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hF
  have hDl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hD
  have hER : E ∈ R := hEl.1.1
  have hFR : F ∈ R := hFl.1.1
  have hDR : D ∈ R := hDl.1.1
  have hg2 : E ⊔ F ≤ gen Δ₂ := sup_le (le_gen hE) (le_gen hF)
  by_contra hDle
  obtain ⟨B, hB, hEO⟩ := exists_centralized_orbit h hA hAne hA₀ hBlk hcl hΔ₂ h2out hE
  have hBR : B ∈ R := hB.1.1.1
  have hEB : Commuting E B := hEO B (mem_orbit_self Blk B)
  have hBE : B ∈ lambdaSet R E := hcol E hE B hB hEB
  have hFB : Special R F B := by
    refine special_of_not_commuting h hA hFl hB fun hc => ?_
    exact hEF.not_commuting (hR.ne_bot E hER)
      (commuting_of_commuting_commuting h hA hAne hA₀ hΔ₂ hcol hE hF hB hEB hc)
  have hBψ : B ∈ psiSet R F := ⟨hBR, hFB⟩
  set Bb := ⁅F, B⁆ with hBbdef
  have hBbR : Bb ∈ R := hFB.1
  have hpt : ∀ P ∈ R, P ≤ B ⊔ Bb → ∃ x ∈ E ⊔ F, conjSub B x = P := by
    intro P hP hPle
    obtain ⟨p, hp, hp1⟩ := hR.exists_ne_one hP
    obtain ⟨x, hx, hpx⟩ := Sec3.exists_mem_conjSub_of_mem_sup hR hiso hER hFR hEF hBE hBψ
      (hPle hp) hp1
    exact ⟨x, hx, Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hBR x) hP hpx hp hp1⟩
  have hDP : ∀ x ∈ E ⊔ F, Special R (conjSub B x) D := by
    intro x hx
    have hPst : conjSub B x ∈ lambdaStar R A A₀ :=
      conjSub_mem_lambdaStar_of_mem_levi hR hB (gen_le_levi (fun _ hY =>
        mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hY) (hg2 hx))
    have hEx : conjSub E x ∈ Δ₂ := by
      obtain ⟨E₀, hE₀, rfl⟩ := hΔ₂
      exact mem_comp_of_le h hA hAne hA₀ hE₀ (hR.conjSub_mem hER x)
        ((conjSub_le le_sup_left hx).trans hg2)
    have hExD : conjSub E x ≠ D := fun e => hDle (e ▸ conjSub_le le_sup_left hx)
    have hop : Opposite D (conjSub E x) :=
      opposite_of_ne h hA hAne hA₀ hBlk hcl h3 hΔ₂ h2out honly hcol h813 hD hEx hExD.symm
    have hnc : ¬ Commuting D (conjSub B x) :=
      not_commuting_of_opposite_of_mem_lambdaSet hR hDR hop (conjSub_mem_lambdaSet hR hBE x)
    exact (special_of_not_commuting h hA hDl hPst hnc).symm
  obtain ⟨x₀, hx₀, hBbx₀⟩ := hpt Bb hBbR le_sup_right
  have hlev : ∀ x ∈ E ⊔ F, x ∈ levi R A A₀ := fun x hx => gen_le_levi (fun _ hY =>
    mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hY) (hg2 hx)
  have hBbst : Bb ∈ lambdaStar R A A₀ :=
    hBbx₀ ▸ conjSub_mem_lambdaStar_of_mem_levi hR hB (hlev x₀ hx₀)
  have hBD : Special R B D := by
    have := hDP 1 (Subgroup.one_mem _)
    rwa [conjSub_one] at this
  have hBbD : Special R Bb D := hBbx₀ ▸ hDP x₀ hx₀
  set C₁ := ⁅B, D⁆ with hC₁def
  set C₂ := ⁅Bb, D⁆ with hC₂def
  have hC₁R : C₁ ∈ R := hBD.1
  have hC₂R : C₂ ∈ R := hBbD.1
  have hC₁st : C₁ ∈ lambdaStar R A A₀ :=
    (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hDl hB hBD).1 C₁ hC₁R le_sup_right
  have hC₂st : C₂ ∈ lambdaStar R A A₀ :=
    (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hDl hBbst hBbD).1 C₂ hC₂R le_sup_right
  have hC₂C₁ : C₂ ∈ lambdaSet R C₁ :=
    mem_lambdaSet_commutator_commutator h hA hAne hA₀ hEl hFl hEF hB hBE hFB hDl hDP
  have hC12ne : C₁ ≠ C₂ := hC₂C₁.1.2.1.symm
  obtain ⟨F', hF'l, hF'⟩ := exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hC₁st hC₂st
    (mem_lambdaSet_comm hC₁R hC₂C₁)
  have hF'R : F' ∈ R := hF'l.1.1
  have hsF' : Special R F' C₁ := by
    refine special_of_not_commuting h hA hF'l hC₁st fun hc => ?_
    have : ⁅C₁, F'⁆ = ⊥ := commuting_iff_commutator_eq_bot.1 hc.symm
    rw [hF'] at this
    exact hR.ne_bot C₂ hC₂R this
  have hC₂F' : Commuting F' C₂ := by
    have := hsF'.symm.2.2
    rw [hF'] at this
    exact this.symm
  have hDC₁ : Commuting D C₁ := hBD.2.2.symm
  have hDC₂ : Commuting D C₂ := hBbD.2.2.symm
  have hF'B : F' ∈ Blk := by
    by_contra hF'B
    have hF'2 := honly F' hF'l hF'B
    have hF'D : Commuting F' D :=
      commuting_of_commuting_commuting h hA hAne hA₀ hΔ₂ hcol hF'2 hD hC₂st hC₂F' hDC₂
    have e := eq_of_commuting h hA hAne hA₀ hBlk hcl h3 hΔ₂ h2out honly hcol h813 hF'2 hD hF'D
    exact hsF'.not_commuting hR (e ▸ hDC₁)
  obtain ⟨-, D', hD'l, hF'D', hC₁D'⟩ :=
    exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hF'l hC₁st hsF'.symm
  have hD'R : D' ∈ R := hD'l.1.1
  have hD'B : D' ∈ Blk :=
    hcl F' hF'B (Relation.ReflTransGen.single ⟨hF'l, hD'l, hF'D'⟩)
  have hfix : ∀ n ∈ C₁ ⊔ ⁅F', C₁⁆, (∀ a ∈ D', Commute a n) → n ∈ C₁ := fun n hn hnD =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hD'R hF'R hF'D'.symm hC₁D' ⟨hC₁R, hsF'⟩ hn hnD
  rw [Subgroup.commutator_comm F' C₁, hF'] at hfix
  have hΔ₂l : ∀ Y ∈ Δ₂, Y ∈ leviSet R A A₀ := fun Y hY =>
    mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hY
  obtain ⟨D₁, hD₁, hDD₁, hpts₁⟩ := natural_points h hA hAne hA₀ hDl hB hBD
  obtain ⟨-, g₁, hg₁, hBg₁⟩ := hpts₁ C₁ hC₁R le_sup_right
  obtain ⟨D₂, hD₂, hDD₂, hpts₂⟩ := natural_points h hA hAne hA₀ hDl hBbst hBbD
  obtain ⟨-, g₂, hg₂, hBbg₂⟩ := hpts₂ C₂ hC₂R le_sup_right
  have hD₁2 : D₁ ∈ Δ₂ := mem_of_opposite h hA hAne hA₀ hΔ₂ hD hD₁ hDD₁
  have hD₂2 : D₂ ∈ Δ₂ := mem_of_opposite h hA hAne hA₀ hΔ₂ hD hD₂ hDD₂
  set g := g₂ * x₀ * g₁⁻¹ with hgdef
  have hg : g ∈ gen Δ₂ := Subgroup.mul_mem _ (Subgroup.mul_mem _
    (sup_le (le_gen hD₂2) (le_gen hD) hg₂) (hg2 hx₀))
    (Subgroup.inv_mem _ (sup_le (le_gen hD₁2) (le_gen hD) hg₁))
  have hC₁g : conjSub C₁ g = C₂ := by
    rw [← hBg₁, ← conjSub_mul, hgdef, inv_mul_cancel_right, conjSub_mul, hBbx₀, hBbg₂]
  have hD'g : ∀ d' ∈ D', Commute d' g := by
    intro d' hd'
    have hc : Commuting D' (gen Δ₂) := commuting_iff_le_centralizer.2 (gen_le fun Y hY =>
      commuting_iff_le_centralizer.1 (commuting_of_notMem h hA hAne hA₀ hBlk hcl (hΔ₂l Y hY)
        (h2out Y hY) hD'B).symm)
    exact hc d' hd' g hg
  have hD'C₂ : Commuting D' C₂ := by
    refine Sec3.commuting_of_forall_conjSub_eq hR hD'R hC₂R (fun d' hd' => ?_) hiso
    rw [← hC₁g, ← conjSub_mul, (hD'g d' hd').eq, conjSub_mul,
      conjSub_of_forall_commute fun c hc => hC₁D'.1.2.2 d' hd' c hc]
  have hle : C₂ ≤ C₁ := fun n hn => hfix n (Subgroup.mem_sup_right hn) fun a ha => hD'C₂ a ha n hn
  exact hC12ne (Subgroup.eq_of_le_of_card_ge hle (hR.card_eq hC₁R hC₂R).le).symm

theorem isSL2Comp_of_single
    (h813 : ∀ E ∈ Δ₂, ∀ E' ∈ Δ₂, (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) →
      E = E') : IsSL2Comp Δ₂ := by
  obtain ⟨E, hE⟩ := nonempty_of_mem hΔ₂
  obtain ⟨F, hF, hEF⟩ := exists_opposite_mem h hA hAne hA₀ hΔ₂ hE
  refine ⟨E, hE, F, hF, hEF, le_antisymm (gen_le fun D hD => ?_) (sup_le (le_gen hE) (le_gen hF))⟩
  exact le_sup_of_opposite h hA hAne hA₀ hBlk hcl h3 hΔ₂ h2out honly hcol h813 hE hF hEF hD

end Single

end Sec9

end CFSG.Timmesfeld.ARS

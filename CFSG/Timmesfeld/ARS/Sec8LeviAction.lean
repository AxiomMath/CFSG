module

public import CFSG.Timmesfeld.ARS.Sec8Sigma
public import CFSG.Timmesfeld.ARS.Sec8Components
public import CFSG.Timmesfeld.ARS.Sec8Projection

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

open Levi

theorem exists_mem_leviSet_not_commuting (h : Hyp G R) {A A₀ F : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hF : F ∈ lambdaStar R A A₀) : ∃ X ∈ leviSet R A A₀, ¬ Commuting F X := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hFR : F ∈ R := hF.1.1.1
  obtain ⟨E, hER, hEle, hEcol⟩ := exists_plane_of_sigmaSet_ne h hA hF.1 hAne
  obtain ⟨-, -, -, -, hcoll, -⟩ := plane hR hiso hER hA hF.1 hEcol
  have hAN : A ≤ E ⊔ A ⊔ F := le_sup_right.trans le_sup_left
  have hEN : E ≤ E ⊔ A ⊔ F := le_sup_left.trans le_sup_left
  have hFN : F ≤ E ⊔ A ⊔ F := le_sup_right
  have hEA : E ≠ A := fun e => hEle (by rw [e]; exact le_sup_left)
  have hEl : E ∈ lambdaSet R A := hcoll A hA hAN E hER hEN hEA.symm
  obtain ⟨F', ⟨hF'R, hF'le, hF'ψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hEl
  have hF'A : F' ≠ A := fun e =>
    Special.not_opposite hR hA₀.1 hF'ψ.2 (by rw [e]; exact hA₀.2.symm)
  have hF'N : F' ≤ E ⊔ A ⊔ F := hF'le.trans (sup_le hAN hEN)
  have hF'l : F' ∈ lambdaSet R A := hcoll A hA hAN F' hF'R hF'N hF'A.symm
  have hF'F : F' ≠ F := by
    intro e
    have hFle : F ≤ A ⊔ E := by rw [← e]; exact hF'le
    have h1 := (mem_lambdaSet_of_le_sup hR hiso hA hEl hA le_sup_left hFR hFle
      hF.1.1.2.1.symm).2
    exact hEle ((le_sup_right : E ≤ A ⊔ E).trans h1.symm.le)
  have hF'Fl : F' ∈ lambdaSet R F := hcoll F hFR hFN F' hF'R hF'N hF'F.symm
  obtain ⟨D, hD, hFD⟩ := exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hF ⟨hF'l, hF'ψ⟩
    (mem_lambdaSet_comm hFR hF'Fl)
  refine ⟨D, hD, fun hc => hR.ne_bot F' hF'R ?_⟩
  rw [← hFD]
  exact commuting_iff_commutator_eq_bot.1 hc

namespace Levi

theorem conjSub_mem_comp (h : Hyp G R) {A A₀ E X : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE : E ∈ leviSet R A A₀) (hX : X ∈ comp R A A₀ E) {g : G} (hg : g ∈ levi R A A₀) :
    conjSub X g ∈ comp R A A₀ E := by
  have := h.finite
  have hR := h.root
  obtain ⟨-, h2, -, -⟩ := component_decomposition hR h.noIsolated (leviSet R A A₀)
    (fun _ hX => hX.1.1) (fun g hg _ hB => conjSub_mem_leviSet_of_mem_levi hR hB hg)
    (fun _ hB _ hC hs => commutator_mem_leviSet hR hA hA₀ hB hC hs)
  exact (h2 E hE (exists_opposite_mem_leviSet h hA hAne hA₀ hE) X hX).2 g hg

theorem notMem_comp_of_notMem_comp {A A₀ E X Y : Subgroup G} (hY : Y ∈ comp R A A₀ E)
    (hXE : X ∉ comp R A A₀ E) : Y ∉ comp R A A₀ X := fun hYX => hXE (by
  rw [← comp_eq_of_mem hY, comp_eq_of_mem hYX]
  exact Relation.ReflTransGen.refl)

end Levi

theorem eq_empty_of_forall_commuting (h : Hyp G R) {A A₀ F : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (hF : F ∈ lambdaStar R A A₀) {S : Set (Subgroup G)}
    (hSΛ : S ⊆ leviSet R A A₀) (hSV : ∀ X ∈ S, ∀ g ∈ levi R A A₀, conjSub X g ∈ S)
    (hSF : ∀ X ∈ S, Commuting F X) : S = ∅ := by
  have := h.finite
  refine Set.eq_empty_iff_forall_notMem.2 fun X hX => ?_
  have hcomm : ∀ F' ∈ lambdaStar R A A₀, Commuting X F' := by
    intro F' hF'
    obtain ⟨w, hw, rfl⟩ := exists_mem_levi_conjSub_eq_of_isSigmaMaximal h hA hAne hmax hA₀ hF hF'
    have := (hSF _ (hSV X hX w⁻¹ (Subgroup.inv_mem _ hw))).conjSub w
    rw [← conjSub_mul, mul_inv_cancel, conjSub_one] at this
    exact this.symm
  have hXM : Commuting X (M R A) := by
    rw [M_eq_gen_lambdaStar h hA hA₀]
    exact commuting_iff_le_centralizer.2
      (gen_le fun F' hF' => commuting_iff_le_centralizer.1 (hcomm F' hF'))
  have hmem : X ∈ {Y | Y ∈ R ∧ Commuting Y (M R A)} := ⟨(hSΛ hX).1.1, hXM⟩
  rw [(Q_eq_M h hA).2.2.2.1] at hmem
  exact (hSΛ hX).1.2.1 hmem

theorem exists_mem_comp_not_commuting_of_isSigmaMaximal (h : Hyp G R) {A A₀ E F : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (hE : E ∈ leviSet R A A₀) (hF : F ∈ lambdaStar R A A₀) :
    ∃ X ∈ comp R A A₀ E, ¬ Commuting F X := by
  by_contra! hall
  have h0 := eq_empty_of_forall_commuting h hA hAne hmax hA₀ hF (comp_subset h hA hAne hA₀ hE)
    (fun X hX g hg => conjSub_mem_comp h hA hAne hA₀ hE hX hg) hall
  exact (Set.eq_empty_iff_forall_notMem.1 h0) E Relation.ReflTransGen.refl

theorem exists_mem_gen_comp_conjSub_ne (h : Hyp G R) {A A₀ E F : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (hE : E ∈ leviSet R A A₀) (hF : F ∈ lambdaStar R A A₀) :
    ∃ v ∈ gen (comp R A A₀ E), conjSub F v ≠ F := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨X, hX, hFX⟩ := exists_mem_comp_not_commuting_of_isSigmaMaximal h hA hAne hmax hA₀ hE hF
  have hXl := comp_subset h hA hAne hA₀ hE hX
  have hXR : X ∈ R := hXl.1.1
  obtain ⟨hs, -, -, -⟩ := CentralOrbit.commutator_mem_lambdaSet h hA hXl.1
    (fun hl => not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hl hXl.2.2.2)
    hF.1 fun hc => hFX hc.symm
  obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hXR
  exact ⟨x, le_gen hX hx, Sec3.conjSub_ne_of_special hR hiso hXR hF.1.1.1 hs hx hx1⟩

theorem commuting_conjSub_of_isSigmaMaximal (h : Hyp G R) {A A₀ E E' F : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (hE : E ∈ leviSet R A A₀) (hE' : E' ∈ leviSet R A A₀) (hE'E : E' ∉ comp R A A₀ E)
    (hF : F ∈ lambdaStar R A A₀) {v : G} (hv : v ∈ gen (comp R A A₀ E)) :
    Commuting F (conjSub F v) := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨-, -, hcommA, -, -⟩ := Q_eq_M h hA
  obtain ⟨X, hX, hXE, hFX⟩ : ∃ X ∈ leviSet R A A₀, X ∉ comp R A A₀ E ∧ ¬ Commuting F X := by
    by_contra! hall
    have h0 := eq_empty_of_forall_commuting h hA hAne hmax hA₀ hF
      (S := {X | X ∈ leviSet R A A₀ ∧ X ∉ comp R A A₀ E}) (fun X hX => hX.1)
      (fun X hX g hg => ⟨conjSub_mem_leviSet_of_mem_levi hR hX.1 hg, fun hm => hX.2 (by
        have := conjSub_mem_comp h hA hAne hA₀ hE hm (Subgroup.inv_mem _ hg)
        rwa [← conjSub_mul, inv_mul_cancel, conjSub_one] at this)⟩)
      fun X hX => hall X hX.1 hX.2
    exact (Set.eq_empty_iff_forall_notMem.1 h0) E' ⟨hE', hE'E⟩
  have hXR : X ∈ R := hX.1.1
  obtain ⟨hs, -, -, -⟩ := CentralOrbit.commutator_mem_lambdaSet h hA hX.1
    (fun hl => not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hl hX.2.2.2)
    hF.1 fun hc => hFX hc.symm
  obtain ⟨-, D, hD, hXD, hFD⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hX hF hs.symm
  have hDE : D ∉ comp R A A₀ E := fun hDE => hXE (hDE.tail ⟨hD, hX, hXD.symm⟩)
  have hVD : gen (comp R A A₀ E) ≤ Subgroup.centralizer (D : Set G) :=
    gen_le fun Y hY => commuting_iff_le_centralizer.1 (commuting_of_notMem_comp h hA hAne hA₀ hD
      (comp_subset h hA hAne hA₀ hE hY) (notMem_comp_of_notMem_comp hY hDE))
  have hvD : conjSub D v = D := conjSub_of_forall_commute fun d hd =>
    (Subgroup.mem_centralizer_iff.1 (hVD hv) d hd).symm
  have hvV : v ∈ levi R A A₀ := gen_mono (comp_subset h hA hAne hA₀ hE) hv
  have hvA : conjSub A v = A := conjSub_of_forall_commute fun a ha =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left A A₀ hvV) a ha).symm
  have hFvA : conjSub F v ∈ lambdaSet R A := by
    have := conjSub_mem_lambdaSet hR hF.1 v
    rwa [hvA] at this
  have hFvD : conjSub F v ∈ lambdaSet R D := by
    have := conjSub_mem_lambdaSet hR hFD v
    rwa [hvD] at this
  rw [commuting_iff_commutator_eq_bot, ← le_bot_iff]
  have h1 : ⁅F, conjSub F v⁆ ≤ A :=
    (Subgroup.commutator_mono (QD.le_M hF.1) (QD.le_M hFvA)).trans hcommA.le
  have h2 : ⁅F, conjSub F v⁆ ≤ D :=
    (Subgroup.commutator_mono (QD.le_M hFD) (QD.le_M hFvD)).trans (Q_eq_M h hD.1.1).2.2.1.le
  exact (le_inf h1 h2).trans (inf_eq_bot hR hiso hA hD.1.1 hD.1.2.1.symm).le

theorem commuting_conjSub_conjSub_of_isSigmaMaximal (h : Hyp G R) {A A₀ E E' F : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (hE : E ∈ leviSet R A A₀) (hE' : E' ∈ leviSet R A A₀) (hE'E : E' ∉ comp R A A₀ E)
    (hF : F ∈ lambdaStar R A A₀) {v w : G} (hv : v ∈ gen (comp R A A₀ E))
    (hw : w ∈ gen (comp R A A₀ E)) : Commuting (conjSub F v) (conjSub F w) := by
  have := (commuting_conjSub_of_isSigmaMaximal h hA hAne hmax hA₀ hE hE' hE'E hF
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) hw)).conjSub v
  rwa [← conjSub_mul, mul_inv_cancel_left] at this

namespace Levi

theorem mem_lambdaSet_of_opposite_of_degenerate (h : Hyp G R) {A A₀ E₀ E F B : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE₀ : E₀ ∈ leviSet R A A₀)
    (hdeg : ∀ X ∈ comp R A A₀ E₀, ∀ Y ∈ comp R A A₀ E₀, ¬ Special R X Y)
    (hE : E ∈ comp R A A₀ E₀) (hF : F ∈ comp R A A₀ E₀) (hFE : Opposite F E)
    (hB : B ∈ lambdaStar R A A₀) (hFB : Commuting F B) (hEB : ¬ Commuting E B) :
    B ∈ lambdaSet R F := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  by_contra hBF
  have hEl := comp_subset h hA hAne hA₀ hE₀ hE
  have hFl := comp_subset h hA hAne hA₀ hE₀ hF
  have hER : E ∈ R := hEl.1.1
  have hFR : F ∈ R := hFl.1.1
  have hBR : B ∈ R := hB.1.1.1
  have hspec : ∀ {X P : Subgroup G}, X ∈ leviSet R A A₀ → P ∈ lambdaSet R A →
      ¬ Commuting X P → Special R X P := fun hX hP hXP =>
    (CentralOrbit.commutator_mem_lambdaSet h hA hX.1 (fun hl =>
      not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hl hX.2.2.2) hP hXP).1
  have hsEB : Special R E B := hspec hEl hB.1 hEB
  obtain ⟨⟨-, hD₁ψ, -, -, -⟩, ⟨-, hMM, hMnorm, -, -, hNZ, hNZbot⟩, ⟨-, -, hZiff⟩⟩ :=
    natural_module_of_commuting hR hiso hFR hER hFE ⟨hBR, hsEB⟩ hFB rfl rfl rfl
  obtain ⟨hZ, hMcov⟩ := centralizer_eq_bot_or_mem_of_commuting h hFR hER hFE ⟨hBR, hsEB⟩ hFB
    rfl rfl
  set D₁ := ⁅E, B⁆ with hD₁def
  set D₂ := ⁅F, D₁⁆ with hD₂def
  set M := B ⊔ (D₁ ⊔ D₂) with hMdef
  set Z := M ⊓ Subgroup.centralizer ((F ⊔ E ⊔ B : Subgroup G) : Set G) with hZdef
  have hZR : Z ∈ R := hZ.resolve_left fun e => hBF (hZiff.1 e)
  have hD₁R : D₁ ∈ R := hsEB.1
  have hsFD₁ : Special R F D₁ := hD₁ψ.2
  have hD₂R : D₂ ∈ R := hsFD₁.1
  obtain ⟨hED₁, hBD₁⟩ := mem_lambdaSet_commutator hR hiso hER hBR hsEB
  obtain ⟨hFD₂, hD₁D₂⟩ := mem_lambdaSet_commutator hR hiso hFR hD₁R hsFD₁
  have hD₁st : D₁ ∈ lambdaStar R A A₀ :=
    (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hEl hB hsEB.symm).1 D₁ hD₁R
      (by rw [hD₁def, Subgroup.commutator_comm]; exact le_sup_right)
  have hD₂st : D₂ ∈ lambdaStar R A A₀ :=
    (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hFl hD₁st hsFD₁.symm).1 D₂ hD₂R
      (by rw [hD₂def, Subgroup.commutator_comm]; exact le_sup_right)
  have hsED₂ : Special R E D₂ := hspec hEl hD₂st.1
    (not_commuting_of_opposite_of_mem_lambdaSet hR hER hFE.symm (mem_lambdaSet_comm hD₂R hFD₂))
  have hZc : Z ≤ Subgroup.centralizer ((F ⊔ E ⊔ B : Subgroup G) : Set G) := inf_le_right
  have hZM : Z ≤ M := inf_le_left
  have hZX : ∀ {X : Subgroup G}, X ≤ F ⊔ E ⊔ B → Commuting X Z := fun hX =>
    (commuting_iff_le_centralizer.2 hZc).mono hX le_rfl
  have hEZ : Commuting E Z := hZX (le_sup_right.trans le_sup_left)
  have hFZ : Commuting F Z := hZX (le_sup_left.trans le_sup_left)
  have hNM : D₁ ⊔ D₂ ≤ M := le_sup_right
  have hZne : ∀ {P : Subgroup G}, P ∈ R → P ≤ D₁ ⊔ D₂ → Z ≠ P := by
    intro P hP hPN e
    have : Z ≤ (D₁ ⊔ D₂) ⊓ Z := le_inf (e ▸ hPN) le_rfl
    rw [hNZbot] at this
    exact hR.ne_bot Z hZR (le_bot_iff.1 this)
  have hcent : ∀ {X P P' : Subgroup G}, X ∈ R → X ≤ F ⊔ E ⊔ B → Commuting X P →
      P' ∈ R → Special R X P' → P ⊔ P' = D₁ ⊔ D₂ → Commuting P P' → ∀ m ∈ M,
      (∀ x ∈ X, Commute m x) → m ∈ Z ⊔ P := by
    intro X P P' hXR hXle hXP hP'R hsXP' hPP' hcPP' m hm hmX
    have hmNZ : m ∈ (D₁ ⊔ D₂) ⊔ Z := by rw [hNZ]; exact hm
    obtain ⟨n, hn, z, hz, rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => hMM a (hNM ha) b (hZM hb)) hmNZ
    rw [← hPP'] at hn
    obtain ⟨p, hp, p', hp', rfl⟩ := CFSG.GroupTheory.exists_mul_of_mem_sup_of_commute
      (fun a ha b hb => hcPP' a ha b hb) hn
    obtain ⟨x, hx, hx1⟩ := hR.exists_ne_one hXR
    have hzx : Commute z x := (hZX hXle x hx z hz).symm
    have hpx : Commute p x := (hXP x hx p hp).symm
    have hp'x : Commute p' x := by
      have e : p' = p⁻¹ * (p * p' * z) * z⁻¹ := by group
      rw [e]
      exact (hpx.inv_left.mul_left (hmX x hx)).mul_left hzx.inv_left
    have hp'1 : p' = 1 := eq_one_of_commute_of_special hR hiso hXR hP'R hsXP' hx hx1 hp' hp'x.symm
    rw [hp'1, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right hp) (Subgroup.mem_sup_left hz)
  have hline : ∀ {X P P' : Subgroup G}, X ∈ R → X ≤ F ⊔ E ⊔ B → Commuting X P →
      P' ∈ R → Special R X P' → P ⊔ P' = D₁ ⊔ D₂ → Commuting P P' → P ∈ R →
      P ≤ D₁ ⊔ D₂ → P ∈ lambdaSet R Z := by
    intro X P P' hXR hXle hXP hP'R hsXP' hPP' hcPP' hPR hPN
    have hZPM : Z ⊔ P ≤ M := sup_le hZM (hPN.trans hNM)
    have hXZP : Commuting X (Z ⊔ P) := Commuting.sup_right (hZX hXle) hXP
    refine ⟨⟨hPR, (hZne hPR hPN).symm, hMM.mono hZM (hPN.trans hNM)⟩, fun y hy hy1 => ?_⟩
    obtain ⟨Q, hQR, hQM, hyQ⟩ := hMcov y (hZPM hy) hy1
    have hXQ : Commuting X Q := by
      refine Sec3.commuting_of_forall_conjSub_eq hR hXR hQR (fun x hx => ?_) hiso
      have hyx : y ∈ conjSub Q x := by
        have e : x * y * x⁻¹ = y := by rw [(hXZP x hx y hy).eq, mul_inv_cancel_right]
        rw [← e]
        exact conj_mem_conjSub x hyQ
      exact (Sec3.eq_of_mem_of_mem hR hiso hQR (hR.conjSub_mem hQR x) hyQ hyx hy1).symm
    exact ⟨Q, hQR, fun q hq => hcent hXR hXle hXP hP'R hsXP' hPP' hcPP' q (hQM hq)
      fun x hx => (hXQ x hx q hq).symm, hyQ⟩
  have hD₁Z : D₁ ∈ lambdaSet R Z := hline hER (le_sup_right.trans le_sup_left)
    hED₁.1.2.2.symm hD₂R hsED₂ rfl hD₁D₂.1.2.2.symm hD₁R le_sup_left
  have hD₂Z : D₂ ∈ lambdaSet R Z := hline hFR (le_sup_left.trans le_sup_left)
    hFD₂.1.2.2.symm hD₁R hsFD₁ (sup_comm _ _) hD₁D₂.1.2.2 hD₂R le_sup_right
  have hBle : B ≤ Z ⊔ D₂ := fun b hb => hcent hFR (le_sup_left.trans le_sup_left)
    hFD₂.1.2.2.symm hD₁R hsFD₁ (sup_comm _ _) hD₁D₂.1.2.2 b ((le_sup_left : B ≤ M) hb)
    fun x hx => (hFB x hx b hb).symm
  have hBZ : B ≠ Z := fun e => hEB (by rw [e]; exact hEZ)
  have hBD₂ : B ≠ D₂ := fun e => hBF (by rw [e]; exact mem_lambdaSet_comm hD₂R hFD₂)
  obtain ⟨hZB, -⟩ := mem_lambdaSet_of_le_sup hR hiso hZR hD₂Z hBR hBle hZR le_sup_left hBZ
  obtain ⟨hBD₂l, hsup⟩ :=
    mem_lambdaSet_of_le_sup hR hiso hZR hD₂Z hD₂R le_sup_right hBR hBle hBD₂.symm
  obtain ⟨D₃, hD₃, hD₂D₃⟩ := exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hD₂st hB
    (mem_lambdaSet_comm hD₂R hBD₂l)
  have hsD₂D₃ : Special R D₂ D₃ := (hspec hD₃ hD₂st.1 fun hc => hR.ne_bot B hBR (by
    rw [← hD₂D₃]; exact commuting_iff_commutator_eq_bot.1 hc.symm)).symm
  have hZst : Z ∈ lambdaStar R A A₀ :=
    (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hD₃ hD₂st hsD₂D₃).1 Z hZR
      (by rw [hD₂D₃, hsup]; exact le_sup_left)
  obtain ⟨Y, hY, hD₁Y⟩ := exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hD₁st hZst hD₁Z
  have hYR : Y ∈ R := hY.1.1
  have hYZ : Y ∈ lambdaSet R Z := mem_lambdaSet_of_commutator_eq hR hiso hZR hYR hD₁R
    (by rw [Subgroup.commutator_comm]; exact hD₁Y)
  have hYD₁ : ¬ Commuting Y D₁ := fun hc => hR.ne_bot Z hZR (by
    rw [← hD₁Y]; exact commuting_iff_commutator_eq_bot.1 hc.symm)
  set S : Set (Subgroup G) := {B, D₁, Z} with hSdef
  have hS : S ⊆ R := by
    rintro P (rfl | rfl | rfl)
    exacts [hBR, hD₁R, hZR]
  have hcolS : ∀ P ∈ S, ∀ Q ∈ S, P ≠ Q → Q ∈ lambdaSet R P := by
    rintro P (rfl | rfl | rfl) Q (rfl | rfl | rfl) hPQ
    · exact absurd rfl hPQ
    · exact mem_lambdaSet_comm hD₁R hBD₁
    · exact hZB
    · exact hBD₁
    · exact absurd rfl hPQ
    · exact mem_lambdaSet_comm hZR hD₁Z
    · exact mem_lambdaSet_comm hBR hZB
    · exact hD₁Z
    · exact absurd rfl hPQ
  have hBT : B ∈ pts R (gen S) := ⟨hBR, le_gen (Or.inl rfl)⟩
  have hD₁T : D₁ ∈ pts R (gen S) := ⟨hD₁R, le_gen (Or.inr (Or.inl rfl))⟩
  have hZT : Z ∈ pts R (gen S) := ⟨hZR, le_gen (Or.inr (Or.inr rfl))⟩
  have hYN : Y ∈ normSet R (gen S) :=
    Singular.mem_normSet_of_le_M h hS hcolS hZT hYR (QD.le_M hYZ)
  have hEY : ¬ Commuting E Y := by
    intro hc
    apply hYD₁
    refine Sec3.commuting_of_forall_conjSub_eq hR hYR hD₁R (fun y hy => ?_) hiso
    have hEy : conjSub E y = E := conjSub_of_forall_commute fun e he => (hc e he y hy).symm
    have hBy : conjSub B y ≤ gen S := by
      rw [← hYN.2 y hy]
      exact Subgroup.map_mono hBT.2
    refine Singular.conjSub_eq_of_le h ?_
    rw [hD₁def, conjSub, Subgroup.map_commutator]
    change ⁅conjSub E y, conjSub B y⁆ ≤ ⁅E, B⁆
    rw [hEy, ← hD₁def]
    calc ⁅E, conjSub B y⁆ ≤ ⁅E, gen S⁆ := Subgroup.commutator_mono le_rfl hBy
      _ = ⁅gen S, E⁆ := Subgroup.commutator_comm _ _
      _ ≤ D₁ := Singular.commutator_le_of_mem_lambdaSet h hS hcolS hD₁T hED₁
  have hEY' : ¬ Opposite E Y := fun ho =>
    not_commuting_of_opposite_of_mem_lambdaSet hR hER ho (mem_lambdaSet_comm hZR hYZ) hEZ
  have hsEY : Special R E Y := by
    have hne : E ≠ Y := fun e => hYD₁ (by rw [← e]; exact hED₁.1.2.2.symm)
    rcases hR.rel E hER Y hYR hne with hc | ho | hs
    · exact absurd hc hEY
    · exact absurd ho hEY'
    · exact hs
  have hYK : Y ∈ comp R A A₀ E₀ := by
    rw [← comp_eq_of_mem hE]
    by_contra hYE
    exact hEY (commuting_of_notMem_comp h hA hAne hA₀ hEl hY hYE)
  exact hdeg E hE Y hYK hsEY

theorem mem_lambdaSet_of_commuting_of_degenerate (h : Hyp G R) {A A₀ E₀ F B : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE₀ : E₀ ∈ leviSet R A A₀)
    (hdeg : ∀ X ∈ comp R A A₀ E₀, ∀ Y ∈ comp R A A₀ E₀, ¬ Special R X Y)
    (hex : ∃ X ∈ comp R A A₀ E₀, ¬ Commuting B X) (hF : F ∈ comp R A A₀ E₀)
    (hB : B ∈ lambdaStar R A A₀) (hFB : Commuting F B) : B ∈ lambdaSet R F := by
  have := h.finite
  by_contra hBF
  have hK : comp R A A₀ F = comp R A A₀ E₀ := comp_eq_of_mem hF
  have key : ∀ Y, Relation.ReflTransGen (oppGraph (leviSet R A A₀)) F Y →
      Commuting Y B ∧ B ∉ lambdaSet R Y := by
    intro Y hY
    induction hY with
    | refl => exact ⟨hFB, hBF⟩
    | @tail Y₁ Y₂ hpath hedge ih =>
      obtain ⟨hY₁B, hBY₁⟩ := ih
      have hY₁K : Y₁ ∈ comp R A A₀ E₀ := by rw [← hK]; exact hpath
      have hY₂K : Y₂ ∈ comp R A A₀ E₀ := by rw [← hK]; exact hpath.tail hedge
      have hY₂B : Commuting Y₂ B := by
        by_contra hc
        exact hBY₁ (mem_lambdaSet_of_opposite_of_degenerate h hA hAne hA₀ hE₀ hdeg hY₂K hY₁K
          hedge.2.2 hB hY₁B hc)
      exact ⟨hY₂B, fun hl =>
        not_commuting_of_opposite_of_mem_lambdaSet h.root hedge.1.1.1 hedge.2.2 hl hY₁B⟩
  obtain ⟨X, hX, hBX⟩ := hex
  exact hBX (key X (by rw [← hK] at hX; exact hX)).1.symm

end Levi

theorem sigmaSet_inter_lambdaStar_eq_of_isSigmaMaximal (h : Hyp G R)
    {A A₀ E₀ F : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (hE₀ : E₀ ∈ leviSet R A A₀)
    (hdeg : ∀ X ∈ comp R A A₀ E₀, ∀ Y ∈ comp R A A₀ E₀, ¬ Special R X Y)
    (hF : F ∈ comp R A A₀ E₀) :
    sigmaSet R F ∩ lambdaStar R A A₀ = lambdaSet R F ∩ lambdaStar R A A₀ := by
  refine Set.Subset.antisymm (fun B hB => ⟨?_, hB.2⟩) fun B hB => ⟨hB.1.1, hB.2⟩
  obtain ⟨X, hX, hBX⟩ :=
    exists_mem_comp_not_commuting_of_isSigmaMaximal h hA hAne hmax hA₀ hE₀ hB.2
  exact Levi.mem_lambdaSet_of_commuting_of_degenerate h hA hAne hA₀ hE₀ hdeg ⟨X, hX, hBX⟩ hF
    hB.2 hB.1.2.2

theorem sigmaSet_inter_lambdaStar_eq_of_subset_comp (h : Hyp G R) {A A₀ E₀ F : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE₀ : E₀ ∈ leviSet R A A₀) (hsub : leviSet R A A₀ ⊆ comp R A A₀ E₀)
    (hdeg : ∀ X ∈ leviSet R A A₀, ∀ Y ∈ leviSet R A A₀, ¬ Special R X Y)
    (hF : F ∈ leviSet R A A₀) :
    sigmaSet R F ∩ lambdaStar R A A₀ = lambdaSet R F ∩ lambdaStar R A A₀ := by
  have hdeg' : ∀ X ∈ comp R A A₀ E₀, ∀ Y ∈ comp R A A₀ E₀, ¬ Special R X Y :=
    fun X hX Y hY => hdeg X (comp_subset h hA hAne hA₀ hE₀ hX) Y (comp_subset h hA hAne hA₀ hE₀ hY)
  refine Set.Subset.antisymm (fun B hB => ⟨?_, hB.2⟩) fun B hB => ⟨hB.1.1, hB.2⟩
  obtain ⟨X, hX, hBX⟩ := exists_mem_leviSet_not_commuting h hA hAne hA₀ hB.2
  exact Levi.mem_lambdaSet_of_commuting_of_degenerate h hA hAne hA₀ hE₀ hdeg' ⟨X, hsub hX, hBX⟩
    (hsub hF) hB.2 hB.1.2.2

end CFSG.Timmesfeld.ARS

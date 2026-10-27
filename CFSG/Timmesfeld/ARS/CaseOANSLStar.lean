module

public import CFSG.Timmesfeld.ARS.CaseOANSLMain

public section

open scoped commutatorElement

namespace CFSG.Timmesfeld.ARS

namespace CaseOANSL

variable {G : Type} [Group G] {R : Set (Subgroup G)} {A A₀ : Subgroup G}
  {Δ₁ Δ₂ : Set (Subgroup G)}

theorem exists_mem₂_commuting (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hA₀ : A₀ ∈ omegaSet R A) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hS₂ : IsSL2Comp Δ₂)
    {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) : ∃ Z ∈ Δ₂, Commuting Z B := by
  have := h.finite
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX
  obtain ⟨P₂, hP₂, -⟩ := hS₂
  by_cases hc : Commuting B P₂
  · exact ⟨P₂, hP₂, hc.symm⟩
  · have hs := special_of_not_commuting_of_mem_leviSet h hA hB (hl₂ hP₂) hc
    obtain ⟨-, D'', hD'', hPD'', hBD''⟩ :=
      exists_opposite_of_mem_lambdaStar h hA hAne hA₀ (hl₂ hP₂) hB hs
    exact ⟨D'', Sec9.mem_of_opposite h hA hAne hA₀ hΔ₂ hP₂ hD'' hPD'', hBD''.1.2.2⟩

theorem eq_of_commuting₂ (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hS₂ : IsSL2Comp Δ₂) {B Z Z' : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hZ : Z ∈ Δ₂) (hZ' : Z' ∈ Δ₂) (hZB : Commuting Z B)
    (hZ'B : Commuting Z' B) : Z = Z' := by
  have := h.finite
  have hΔ₂R : Δ₂ ⊆ R := fun Y hY =>
    (Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hY).1.1
  by_contra hne'
  obtain ⟨-, hgen⟩ := hS₂.opposite_of_ne h.root hΔ₂R hZ hZ' hne'
  have hBV : Commuting B (gen Δ₂) := by
    rw [← hgen]
    exact hZB.symm.sup_right hZ'B.symm
  exact Sec9.not_forall_commuting h hA hAne hA₀ hmax hΔ₂ hB fun Y hY =>
    (hBV.mono le_rfl (le_gen hY)).symm

theorem mem_lambdaSet_commutator_of_commuting' (h : Hyp G R) {F D' Z : Subgroup G} (hF : F ∈ R)
    (hD' : D' ∈ R) (hZ : Z ∈ R) (hs : Special R D' Z) (hFZ : Commuting F Z)
    (hFD' : F ∈ lambdaSet R D') (hne : ⁅D', Z⁆ ≠ F) : F ∈ lambdaSet R ⁅D', Z⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨z, hz, hz1⟩ := hR.exists_ne_one hZ
  have hsup := sup_conjSub_eq_sup_commutator hR hiso hD' hZ hs hz hz1
  have hFz : conjSub F z = F := conjSub_of_forall_commute fun f hf => (hFZ f hf z hz).symm
  have h1 : D' ∈ lambdaSet R F := mem_lambdaSet_comm hD' hFD'
  have h2 : conjSub D' z ∈ lambdaSet R F := by
    have := conjSub_mem_lambdaSet hR h1 z
    rwa [hFz] at this
  have hle : ⁅D', Z⁆ ≤ M R F := by
    calc ⁅D', Z⁆ ≤ D' ⊔ ⁅D', Z⁆ := le_sup_right
      _ = D' ⊔ conjSub D' z := hsup.symm
      _ ≤ M R F := sup_le (QD.le_M h1) (QD.le_M h2)
  exact mem_lambdaSet_comm hF (mem_lambdaSet_of_le_M_of_hyp h hF hs.1 hle hne)

theorem exists_mem₁_lambdaSet (h : Hyp G R) (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
    (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
    (hΔ₁ : Δ₁ ∈ leviComps R A A₀) {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    ∃ F ∈ Δ₁, F ∈ lambdaSet R B := by
  have := h.finite
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  obtain ⟨X, hX, hXB⟩ : ∃ X ∈ Δ₁, ¬ Commuting X B := by
    by_contra! hall
    exact Sec9.not_forall_commuting h hA hAne hA₀ hmax hΔ₁ hB hall
  have hs := special_of_not_commuting_of_mem_leviSet h hA hB (hl₁ hX) fun hc => hXB hc.symm
  obtain ⟨-, Y, hY, hXY, hBY⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ (hl₁ hX) hB hs
  exact ⟨Y, Sec9.mem_of_opposite h hA hAne hA₀ hΔ₁ hX hY hXY, mem_lambdaSet_comm hY.1.1 hBY⟩

theorem exists_mem₁_of_commuting₂ (h : Hyp G R) (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) (h2 : Nat.card (leviComps R A A₀) = 2)
    (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
    (hS₂ : IsSL2Comp Δ₂) {B D Z₀ : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hD : D ∈ lambdaStar R A A₀) (hDB : D ∈ lambdaSet R B) (hZ₀ : Z₀ ∈ Δ₂)
    (hZ₀B : Commuting Z₀ B) (hZ₀D : Commuting Z₀ D) :
    ∃ F ∈ Δ₁, F ∈ lambdaSet R B ∧ F ∈ lambdaSet R D := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX
  have hBR : B ∈ R := hB.1.1.1
  have hDR : D ∈ R := hD.1.1.1
  have hBD : B ∈ lambdaSet R D := mem_lambdaSet_comm hBR hDB
  obtain ⟨Z₁, hZ₁, hZ₀₁⟩ := Sec9.exists_opposite_mem h hA hAne hA₀ hΔ₂ hZ₀
  have hZne : Z₀ ≠ Z₁ := hZ₀₁.1
  have hDZ₁ : ¬ Commuting D Z₁ := fun hc =>
    hZne (eq_of_commuting₂ h hA hAne hmax hA₀ hΔ₂ hS₂ hD hZ₀ hZ₁ hZ₀D hc.symm)
  have hsDZ₁ : Special R D Z₁ := special_of_not_commuting_of_mem_leviSet h hA hD (hl₂ hZ₁) hDZ₁
  obtain ⟨hD₁, hD₁D, hD₁Z₁⟩ := commutator_mem_lambdaStar h hA hAne hA₀ hD (hl₂ hZ₁) hsDZ₁
  set D₁ := ⁅D, Z₁⁆ with hD₁def
  have hD₁R : D₁ ∈ R := hD₁.1.1.1
  have hZ₁D₁ : Commuting Z₁ D₁ := hD₁Z₁.1.2.2
  have hZ₀D₁ : ¬ Commuting Z₀ D₁ := fun hc =>
    hZne (eq_of_commuting₂ h hA hAne hmax hA₀ hΔ₂ hS₂ hD₁ hZ₀ hZ₁ hc hZ₁D₁)
  have hBD₁ : Commuting B D₁ := by
    rw [commuting_iff_commutator_eq_bot, eq_bot_iff,
      ← inf_eq_bot hR hiso hA hDR hD.1.1.2.1.symm]
    refine le_inf ?_ ?_
    · rw [← (Q_eq_M h hA).2.2.1]
      exact Subgroup.commutator_mono (QD.le_M hB.1) (QD.le_M hD₁.1)
    · rw [← (Q_eq_M h hDR).2.2.1]
      exact Subgroup.commutator_mono (QD.le_M hBD) (QD.le_M hD₁D)
  have hD₁B : D₁ ∉ lambdaSet R B := by
    intro hD₁B
    have e1 := CaseOA.eq_commutator_of_mem_lambdaSet h hA hAne hmax hA₀ hΔ₂ hS₂ hZ₀ hB hD₁ hZ₀B
      (fun hc => hZ₀D₁ hc.symm) (mem_lambdaSet_comm hBR hD₁B)
    have e2 := CaseOA.eq_commutator_of_mem_lambdaSet h hA hAne hmax hA₀ hΔ₂ hS₂ hZ₀ hD hD₁ hZ₀D
      (fun hc => hZ₀D₁ hc.symm) (mem_lambdaSet_comm hDR hD₁D)
    exact hDB.1.2.1 (e2.trans e1.symm)
  obtain ⟨hZst, hZD₁c, hAZ, -⟩ := CaseD4.commutator_props h hA hA₀ hD₁
  set Z := ⁅A₀, D₁⁆ with hZdef
  have hZR : Z ∈ R := hZst.1.1.1
  have hsAZ : Special R A Z := hZst.2.2
  have hZD₁ : Z ∈ lambdaSet R D₁ := by
    have := (mem_lambdaSet_commutator hR hiso hA hZR hsAZ).2
    rwa [hAZ] at this
  have hBZ : B ≠ Z := fun e => hsAZ.not_commuting hR (by rw [← e]; exact hB.1.1.2.2)
  have hnc : ¬ Commuting B Z := by
    intro hc
    obtain ⟨z, hz, hz1⟩ := hR.exists_ne_one hZR
    have hsup := sup_conjSub_eq_sup_commutator hR hiso hA hZR hsAZ hz hz1
    rw [hAZ] at hsup
    have hBz : conjSub B z = B := conjSub_of_forall_commute fun b hb => (hc b hb z hz).symm
    have hAB : A ∈ lambdaSet R B := mem_lambdaSet_comm hA hB.1
    have hAzB : conjSub A z ∈ lambdaSet R B := by
      have := conjSub_mem_lambdaSet hR hAB z
      rwa [hBz] at this
    have hle : D₁ ≤ M R B := by
      calc D₁ ≤ A ⊔ D₁ := le_sup_right
        _ = A ⊔ conjSub A z := hsup.symm
        _ ≤ M R B := sup_le (QD.le_M hAB) (QD.le_M hAzB)
    exact hD₁B (mem_lambdaSet_of_le_M_of_hyp h hBR hD₁R hle fun e =>
      hZ₀D₁ (by rw [e]; exact hZ₀B))
  have hno : ¬ Opposite B Z := by
    intro hopp
    obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hD₁R
    have hdZA : d ∈ ⁅Z, A⁆ := by
      rw [Subgroup.commutator_comm, hAZ]
      exact hd
    exact hd1 (Sec3.eq_one_of_conjSub_eq_of_mem_commutator hR hiso hBR hZR hopp
      (mem_lambdaSet_comm hA hB.1) ⟨hA, hsAZ.symm⟩ hdZA
      (conjSub_of_forall_commute fun b hb => (hBD₁ b hb d hd).symm))
  have hsBZ : Special R B Z := by
    rcases hR.rel B hBR Z hZR hBZ with hc | ho | hs
    · exact absurd hc hnc
    · exact absurd ho hno
    · exact hs
  set E := ⁅B, Z⁆ with hEdef
  have hER : E ∈ R := hsBZ.1
  obtain ⟨hBE, hZE⟩ := mem_lambdaSet_commutator hR hiso hBR hZR hsBZ
  have hEB : E ∈ lambdaSet R B := mem_lambdaSet_comm hER hBE
  have hED₁ : E ∈ lambdaSet R D₁ := by
    obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hBR
    have hsup := sup_conjSub_eq_sup_commutator hR hiso hZR hBR hsBZ.symm hb hb1
    rw [Subgroup.commutator_comm] at hsup
    have hD₁b : conjSub D₁ b = D₁ := conjSub_of_forall_commute fun d hd => hBD₁ b hb d hd
    have hZb : conjSub Z b ∈ lambdaSet R D₁ := by
      have := conjSub_mem_lambdaSet hR hZD₁ b
      rwa [hD₁b] at this
    have hle : E ≤ M R D₁ := by
      calc E ≤ Z ⊔ E := le_sup_right
        _ = Z ⊔ conjSub Z b := hsup.symm
        _ ≤ M R D₁ := sup_le (QD.le_M hZD₁) (QD.le_M hZb)
    exact mem_lambdaSet_of_le_M_of_hyp h hD₁R hER hle fun e => hD₁B (by rw [← e]; exact hEB)
  have hEA : Commuting A E := by
    have h1 : ⁅⁅Z, A⁆, B⁆ = ⊥ := by
      rw [Subgroup.commutator_comm Z A, hAZ, Subgroup.commutator_comm]
      exact commuting_iff_commutator_eq_bot.1 hBD₁
    have h2' : ⁅⁅A, B⁆, Z⁆ = ⊥ := by
      rw [commuting_iff_commutator_eq_bot.1 hB.1.1.2.2, Subgroup.commutator_bot_left]
    have h3 := Subgroup.commutator_commutator_eq_bot_of_rotate h1 h2'
    rw [commuting_iff_commutator_eq_bot, Subgroup.commutator_comm]
    exact h3
  have hEA' : E ≠ A := fun e => hsAZ.not_commuting hR (by rw [← e]; exact hZE.1.2.2)
  have hEl : E ∉ lambdaSet R A := by
    intro hEA''
    have hAE : A ∈ lambdaSet R E := mem_lambdaSet_comm hA hEA''
    have hle : D₁ ≤ E := by
      rw [← hAZ, ← (Q_eq_M h hER).2.2.1]
      exact Subgroup.commutator_mono (QD.le_M hAE) (QD.le_M hZE)
    have hD₁E : D₁ = E := Subgroup.eq_of_le_of_card_ge hle (hR.card_eq hER hD₁R).le
    exact hD₁B (by rw [hD₁E]; exact hEB)
  obtain ⟨hFΔ, ⟨m, hm, hEm⟩, -⟩ :=
    sup_inf_levi_mem_leviSet h hA hAne hA₀ (⟨hER, hEA', hEA⟩ : E ∈ sigmaSet R A) hEl
  rw [← hEm] at hFΔ
  set F := conjSub E m with hFdef
  have hmA : conjSub A m = A := conjSub_eq_self_iff.2 ((isPGroup_M hR hA).2.1 hm)
  have hfix : ∀ {X : Subgroup G}, X ∈ lambdaStar R A A₀ → E ∈ lambdaSet R X →
      conjSub X m = X := by
    intro X hX hEX
    have h1 : conjSub X m ∈ lambdaSet R A := by
      have := conjSub_mem_lambdaSet hR hX.1 m
      rwa [hmA] at this
    have h2' : conjSub X m ∈ lambdaSet R F :=
      conjSub_mem_lambdaSet hR (mem_lambdaSet_comm hX.1.1.1 hEX) m
    have h3 := mem_lambdaStar_of_mem_lambdaSet hR hA₀ hFΔ h1 h2'
    have hle : conjSub X m ≤ A ⊔ X := by
      have h4 : ⁅X, M R A⁆ ≤ A :=
        (Subgroup.commutator_mono (QD.le_M hX.1) le_rfl).trans (Q_eq_M h hA).2.2.1.le
      exact (conjSub_le_commutator_sup (A := X) hm).trans (sup_le_sup_right h4 _)
    exact eq_of_le_sup_of_mem_lambdaStar h hA hA₀ hX h3 hle
  have hFB : F ∈ lambdaSet R B := by
    have := conjSub_mem_lambdaSet hR hEB m
    rwa [hfix hB hEB] at this
  have hFD₁ : F ∈ lambdaSet R D₁ := by
    have := conjSub_mem_lambdaSet hR hED₁ m
    rwa [hfix hD₁ hED₁] at this
  have hF₁ : F ∈ Δ₁ := by
    have hFc : Levi.comp R A A₀ F ∈ leviComps R A A₀ := ⟨F, hFΔ, rfl⟩
    rcases CaseOA.eq_or_eq_of_card_two h2 hΔ₁ hΔ₂ hne hFc with e | e
    · exact e ▸ Sec9.self_mem_comp A A₀ F
    · exfalso
      have hF₂ : F ∈ Δ₂ := e ▸ Sec9.self_mem_comp A A₀ F
      have e0 := eq_of_commuting₂ h hA hAne hmax hA₀ hΔ₂ hS₂ hB hF₂ hZ₀ hFB.1.2.2.symm hZ₀B
      have e1 := eq_of_commuting₂ h hA hAne hmax hA₀ hΔ₂ hS₂ hD₁ hF₂ hZ₁ hFD₁.1.2.2.symm
        hZ₁D₁
      exact hZne (e0.symm.trans e1)
  have hDeq := CaseOA.eq_commutator_of_mem_lambdaSet h hA hAne hmax hA₀ hΔ₂ hS₂ hZ₀ hD hD₁ hZ₀D
    (fun hc => hZ₀D₁ hc.symm) (mem_lambdaSet_comm hDR hD₁D)
  have hsD₁Z₀ : Special R D₁ Z₀ :=
    special_of_not_commuting_of_mem_leviSet h hA hD₁ (hl₂ hZ₀) fun hc => hZ₀D₁ hc.symm
  have hFZ₀ : Commuting F Z₀ := Sec9.commuting_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne hF₁ hZ₀
  have hFD : F ∈ lambdaSet R D := by
    rw [hDeq]
    refine mem_lambdaSet_commutator_of_commuting' h hFΔ.1.1 hD₁R (hl₂ hZ₀).1.1 hsD₁Z₀ hFZ₀
      hFD₁ ?_
    rw [← hDeq]
    intro e
    exact hD.2.2.not_commuting hR (by rw [e]; exact hFΔ.2.2.2)
  exact ⟨F, hF₁, hFB, hFD⟩

end CaseOANSL

open CaseOANSL in
theorem oaStarInput : OAStarInput := by
  intro G _ R A A₀ Δ₁ Δ₂ hset _ B hB D hD hDB
  obtain ⟨h, hA, -, hAne, hmax, hA₀, h2, hΔ₁, hΔ₂, hne, -, hS₂⟩ := hset
  have := h.finite
  have hR := h.root
  have hl₁ := fun {X : Subgroup G} (hX : X ∈ Δ₁) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₁ hX
  have hl₂ := fun {X : Subgroup G} (hX : X ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hX
  have hBD : B ∈ lambdaSet R D := mem_lambdaSet_comm hB.1.1.1 hDB
  have fin : ∀ F ∈ Δ₁, F ∈ lambdaSet R B → F ∈ lambdaSet R D →
      (deltaSet R A A₀ B ∩ deltaSet R A A₀ D ∩ Δ₁).Nonempty := fun F hF hFB hFD =>
    ⟨F, ⟨⟨hl₁ hF, hFB⟩, hl₁ hF, hFD⟩, hF⟩
  have diff : ∀ {X Y : Subgroup G}, X ∈ lambdaStar R A A₀ → Y ∈ lambdaStar R A A₀ →
      Y ∈ lambdaSet R X → ∀ Z ∈ Δ₂, Commuting Z X → ¬ Commuting Z Y →
        ∃ F ∈ Δ₁, F ∈ lambdaSet R X ∧ F ∈ lambdaSet R Y := by
    intro X Y hX hY hYX Z hZ hZX hZY
    have hXeq := CaseOA.eq_commutator_of_mem_lambdaSet h hA hAne hmax hA₀ hΔ₂ hS₂ hZ hX hY hZX
      (fun hc => hZY hc.symm) (mem_lambdaSet_comm hX.1.1.1 hYX)
    obtain ⟨F, hF, hFY⟩ := exists_mem₁_lambdaSet h hA hAne hmax hA₀ hΔ₁ hY
    have hsYZ : Special R Y Z :=
      special_of_not_commuting_of_mem_leviSet h hA hY (hl₂ hZ) fun hc => hZY hc.symm
    have hFZ : Commuting F Z := Sec9.commuting_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne hF hZ
    refine ⟨F, hF, ?_, hFY⟩
    rw [hXeq]
    refine mem_lambdaSet_commutator_of_commuting' h (hl₁ hF).1.1 hY.1.1.1 (hl₂ hZ).1.1 hsYZ
      hFZ hFY ?_
    rw [← hXeq]
    intro e
    exact hX.2.2.not_commuting hR (by rw [e]; exact (hl₁ hF).2.2.2)
  by_cases hc1 : ∃ Z ∈ Δ₂, Commuting Z B ∧ ¬ Commuting Z D
  · obtain ⟨Z, hZ, hZB, hZD⟩ := hc1
    obtain ⟨F, hF, hFB, hFD⟩ := diff hB hD hDB Z hZ hZB hZD
    exact fin F hF hFB hFD
  by_cases hc2 : ∃ Z ∈ Δ₂, Commuting Z D ∧ ¬ Commuting Z B
  · obtain ⟨Z, hZ, hZD, hZB⟩ := hc2
    obtain ⟨F, hF, hFD, hFB⟩ := diff hD hB hBD Z hZ hZD hZB
    exact fin F hF hFB hFD
  push Not at hc1
  obtain ⟨Z₀, hZ₀, hZ₀B⟩ := exists_mem₂_commuting h hA hAne hA₀ hΔ₂ hS₂ hB
  obtain ⟨F, hF, hFB, hFD⟩ := exists_mem₁_of_commuting₂ h hA hAne hmax hA₀ h2 hΔ₁ hΔ₂ hne hS₂
    hB hD hDB hZ₀ hZ₀B (hc1 Z₀ hZ₀ hZ₀B)
  exact fin F hF hFB hFD

theorem oaNonSimplyLacedInput : OANonSimplyLacedInput :=
  oaNonSimplyLacedInput_of oaStarInput

end CFSG.Timmesfeld.ARS

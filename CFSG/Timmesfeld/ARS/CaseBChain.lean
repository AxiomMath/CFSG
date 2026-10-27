module

public import CFSG.Timmesfeld.ARS.CaseBConfig
public import CFSG.Timmesfeld.ARS.SimplyLacedConfigA

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseB

section Natural

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {A B C : Subgroup G} (hA : A ∈ R)
  (hB : B ∈ R) (hAB : Opposite A B) (hAC : C ∈ lambdaSet R A) (hBC : C ∈ psiSet R B)
include hR hiso hA hB hAB hAC hBC

theorem mem_commutator_of_forall_commute_of_mem_sup {x : G} (hx : x ∈ C ⊔ ⁅B, C⁆)
    (hxB : ∀ b ∈ B, Commute b x) : x ∈ ⁅B, C⁆ := by
  obtain ⟨n, -, -, φ, hφA, hφB⟩ := hAB.exists_mulEquiv_SL2' hR hA
  obtain ⟨w, hw, hw1⟩ := hR.exists_ne_one hAC.1.1
  obtain ⟨θ, hθ, hrange, he⟩ := Sec3.exists_isNaturalModule hR hiso hA hB hAB hAC hBC φ hφA hw hw1
  have hx' : x ∈ Set.range θ := by
    rw [hrange]
    exact hx
  obtain ⟨v, rfl⟩ := hx'
  have h0 : v 0 = 0 := (hθ.forall_commute_lower_iff hφB le_sup_right v).1 hxB
  have hv : v = ![0, v 1] := by
    ext i
    fin_cases i <;> simp [h0]
  rw [hv]
  have h := FrameSL3.commutatorElement_lowPar hθ (v 1) ![1, 0]
  rw [show v 1 * (![1, 0] : Fin 2 → _) 0 = v 1 by simp, he] at h
  rw [← h]
  exact Subgroup.commutator_mem_commutator (FrameSL3.lowPar_mem hφB (v 1)) hw

theorem conjSub_eq_commutator_of_swap {w : G} (hw : w ∈ A ⊔ B) (hwA : conjSub A w = B) :
    conjSub C w = ⁅B, C⁆ := by
  have hCR : C ∈ R := hAC.1.1
  have hle : conjSub C w ≤ ⁅B, C⁆ := by
    rintro _ ⟨c, hc, rfl⟩
    have hN := Sec3.conjSub_sup_commutator_eq hR hiso hA hB hAB hAC hBC hw
    have hmem : (MulAut.conj w).toMonoidHom c ∈ C ⊔ ⁅B, C⁆ := by
      rw [← hN]
      exact ⟨c, Subgroup.mem_sup_left hc, rfl⟩
    refine mem_commutator_of_forall_commute_of_mem_sup hR hiso hA hB hAB hAC hBC hmem ?_
    intro b hb
    have hcomm := hAC.1.2.2.conjSub w
    rw [hwA] at hcomm
    exact hcomm b hb _ ⟨c, hc, rfl⟩
  exact Subgroup.eq_of_le_of_card_ge hle (hR.card_eq hBC.2.1 (hR.conjSub_mem hCR w)).le

end Natural

theorem commuting_of_le_M_inf (h : Hyp G R) {X Y Z W : Subgroup G} (hX : X ∈ R) (hY : Y ∈ R)
    (hXY : X ⊓ Y = ⊥) (hZX : Z ≤ M R X) (hZY : Z ≤ M R Y) (hWX : W ≤ M R X)
    (hWY : W ≤ M R Y) : Commuting Z W := by
  refine commuting_iff_commutator_eq_bot.2 (eq_bot_iff.2 ?_)
  rw [← hXY]
  refine le_inf ?_ ?_
  · rw [← (Q_eq_M h hX).2.2.1]
    exact Subgroup.commutator_mono hZX hWX
  · rw [← (Q_eq_M h hY).2.2.1]
    exact Subgroup.commutator_mono hZY hWY

theorem commutator_le_of_le_M (h : Hyp G R) {X Y Z : Subgroup G} (hX : X ∈ R)
    (hY : Y ≤ M R X) (hZ : Z ≤ M R X) : ⁅Y, Z⁆ ≤ X :=
  (Subgroup.commutator_mono hY hZ).trans (le_of_eq (Q_eq_M h hX).2.2.1)

section Chain

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (h8 : Sec8 R A)
  (hA₀ : A₀ ∈ omegaSet R A) {Δ : Set (Subgroup G)} (hΔ : IsWeakTI R Δ) (hAΔ : A ∈ Δ)
include h hA h8 hA₀ hΔ hAΔ

theorem conjSub_eq_of_levi {X A₁ B₁ : Subgroup G} (hX : X ∈ lambdaStar R A A₀)
    (hA₁ : A₁ ∈ leviSet R A A₀) (hB₁ : B₁ ∈ leviSet R A A₀) (hne : A₁ ≠ B₁)
    (hA₁X : Commuting A₁ X) {w : G} (hw : w ∈ A₁ ⊔ B₁) (hwA : conjSub A₁ w = B₁) :
    conjSub X w = ⁅B₁, X⁆ :=
  have := h.finite
  conjSub_eq_commutator_of_swap h.root h.noIsolated hA₁.1.1 hB₁.1.1
    (opposite_of_mem_leviSet h hA h8 hA₀ hΔ hAΔ hA₁ hB₁ hne)
    (mem_lambdaSet_of_commuting h hA h8 hA₀ hΔ hAΔ hX hA₁ hA₁X)
    ⟨hX.1.1.1, special_of_commuting h hA h8 hA₀ hΔ hAΔ hX hA₁ hB₁ hne hA₁X⟩ hw hwA

omit h8 hΔ hAΔ in
theorem conjSub_eq_of_swap {D : Subgroup G} (hD : D ∈ lambdaStar R A A₀) {w : G}
    (hw : w ∈ A ⊔ A₀) (hwA : conjSub A w = A₀) : conjSub D w = ⁅A₀, D⁆ :=
  have := h.finite
  conjSub_eq_commutator_of_swap h.root h.noIsolated hA hA₀.1 hA₀.2 hD.1 hD.2 hw hwA

variable {A₁ B₁ E C : Subgroup G} (hA₁ : A₁ ∈ leviSet R A A₀) (hB₁ : B₁ ∈ leviSet R A A₀)
  (hne : A₁ ≠ B₁) (hE : E ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀)
  (hB₁E : Commuting B₁ E) (hA₁C : Commuting A₁ C) (hECA : ⁅E, C⁆ = A)
include hA₁ hB₁ hne hE hC hB₁E hA₁C hECA

theorem chain_node :
    ⁅B₁, C⁆ ∈ lambdaStar R A A₀ ∧ Commuting B₁ ⁅B₁, C⁆ ∧ ⁅A₀, ⁅A₁, E⁆⁆ ∈ lambdaStar R A₀ A ∧
      Commuting A₁ ⁅A₀, ⁅A₁, E⁆⁆ ∧ Opposite ⁅B₁, C⁆ ⁅A₀, ⁅A₁, E⁆⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hop : Opposite A₁ B₁ := opposite_of_mem_leviSet h hA h8 hA₀ hΔ hAΔ hA₁ hB₁ hne
  have hsAE : Special R A₁ E :=
    special_of_commuting h hA h8 hA₀ hΔ hAΔ hE hB₁ hA₁ hne.symm hB₁E
  have hC' : ⁅A₁, E⁆ ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA h8.2 hA₀ hA₁ hE hsAE.symm).1 _ hsAE.1
    rw [Subgroup.commutator_comm E A₁] at this
    exact this le_sup_right
  have hsBC : Special R B₁ C := special_of_commuting h hA h8 hA₀ hΔ hAΔ hC hA₁ hB₁ hne hA₁C
  have hP : ⁅B₁, C⁆ ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA h8.2 hA₀ hB₁ hC hsBC.symm).1 _ hsBC.1
    rw [Subgroup.commutator_comm C B₁] at this
    exact this le_sup_right
  obtain ⟨hP', hP'C', hAP'C', hYP'⟩ := CaseD4.commutator_props h hA hA₀ hC'
  obtain ⟨-, -, -, w, -, -, hw, hwA₁, hwB₁⟩ := Sec5.exists_swap hR hA₁.1.1 hB₁.1.1 hop
  have hCw : conjSub C w = ⁅B₁, C⁆ :=
    conjSub_eq_of_levi h hA h8 hA₀ hΔ hAΔ hC hA₁ hB₁ hne hA₁C hw hwA₁
  have hEw : conjSub E w = ⁅A₁, E⁆ :=
    conjSub_eq_of_levi h hA h8 hA₀ hΔ hAΔ hE hB₁ hA₁ hne.symm hB₁E (by rwa [sup_comm]) hwB₁
  have hwV : w ∈ levi R A A₀ := by
    rw [levi_eq_sup_of_ne h hA h8 hA₀ hΔ hAΔ hA₁ hB₁ hne]
    exact hw
  have hwA : conjSub A w = A := conjSub_of_forall_commute fun a ha =>
    ((Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left A A₀ hwV)) a ha).symm
  have hPC' : ⁅⁅B₁, C⁆, ⁅A₁, E⁆⁆ = A := by
    rw [← hCw, ← hEw, conjSub, conjSub, ← Subgroup.map_commutator, Subgroup.commutator_comm C E,
      hECA]
    exact hwA
  have hnc : ¬ Commuting ⁅B₁, C⁆ ⁅A₁, E⁆ := fun hc =>
    hR.ne_bot A hA (by rw [← hPC']; exact commuting_iff_commutator_eq_bot.1 hc)
  have hsPC' := (special_of_not_commuting h hA hP.1 hC'.1 hnc).1
  exact ⟨hP, hsBC.2.1.symm, hP', hYP' A₁ hA₁ hsAE.2.1.symm,
    CaseD4.opposite_of_extremal hR hiso hA hC'.1.1.1 hP.1.1.1 hP'.1.1.1 hC'.1.1.2.2
      hP.1.1.2.2.symm hsPC' hPC' hP'C' hP'.2.2 hAP'C'⟩

omit hC hA₁C hECA in
theorem chain_C' : Special R A₁ E ∧ ⁅A₁, E⁆ ∈ lambdaStar R A A₀ := by
  have hsAE : Special R A₁ E :=
    special_of_commuting h hA h8 hA₀ hΔ hAΔ hE hB₁ hA₁ hne.symm hB₁E
  refine ⟨hsAE, ?_⟩
  have := (exists_opposite_of_mem_lambdaStar h hA h8.2 hA₀ hA₁ hE hsAE.symm).1 _ hsAE.1
  rw [Subgroup.commutator_comm E A₁] at this
  exact this le_sup_right

theorem chain_commuting :
    Commuting ⁅B₁, C⁆ E ∧ Commuting ⁅B₁, C⁆ ⁅A₀, C⁆ ∧ Commuting ⁅A₀, ⁅A₁, E⁆⁆ E ∧
      Commuting ⁅A₀, ⁅A₁, E⁆⁆ ⁅A₀, C⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨hA₀R, h8₀, hAΩ, Δ₀, hΔ₀, hA₀Δ₀⟩ := hyp_symm h hA h8 hA₀ hΔ hAΔ
  obtain ⟨hP, hB₁P, hP', hA₁P', -⟩ :=
    chain_node h hA h8 hA₀ hΔ hAΔ hA₁ hB₁ hne hE hC hB₁E hA₁C hECA
  obtain ⟨hsAE, hC'⟩ := chain_C' h hA h8 hA₀ hΔ hAΔ hA₁ hB₁ hne hE hB₁E
  obtain ⟨hF, hFC, hAFC, hYF⟩ := CaseD4.commutator_props h hA hA₀ hC
  obtain ⟨-, -, hAP'C', -⟩ := CaseD4.commutator_props h hA hA₀ hC'
  have hA₁' : A₁ ∈ leviSet R A₀ A := by rw [leviSet_comm]; exact hA₁
  have hA₁F : Commuting A₁ ⁅A₀, C⁆ := hYF A₁ hA₁ hA₁C
  have hsBC : Special R B₁ C := special_of_commuting h hA h8 hA₀ hΔ hAΔ hC hA₁ hB₁ hne hA₁C
  have hER : E ∈ R := hE.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  have hPR : ⁅B₁, C⁆ ∈ R := hP.1.1.1
  have hC'R : ⁅A₁, E⁆ ∈ R := hC'.1.1.1
  have hP'R : ⁅A₀, ⁅A₁, E⁆⁆ ∈ R := hP'.1.1.1
  have hFR : ⁅A₀, C⁆ ∈ R := hF.1.1.1
  have hinj : ∀ w : G, Function.Injective (MulAut.conj w).toMonoidHom := fun w =>
    (MulAut.conj w).injective
  have hPE := commuting_of_le_M_inf h hA hB₁.1.1 (inf_eq_bot hR hiso hA hB₁.1.1 hB₁.1.2.1.symm)
    (QD.le_M hP.1) (QD.le_M (mem_lambdaSet_of_commuting h hA h8 hA₀ hΔ hAΔ hP hB₁ hB₁P))
    (QD.le_M hE.1) (QD.le_M (mem_lambdaSet_of_commuting h hA h8 hA₀ hΔ hAΔ hE hB₁ hB₁E))
  have hP'F := commuting_of_le_M_inf h hA₀R hA₁.1.1
    (inf_eq_bot hR hiso hA₀R hA₁.1.1 hA₁.2.2.1.symm) (QD.le_M hP'.1)
    (QD.le_M (mem_lambdaSet_of_commuting h hA₀R h8₀ hAΩ hΔ₀ hA₀Δ₀ hP' hA₁' hA₁P'))
    (QD.le_M hF.1) (QD.le_M (mem_lambdaSet_of_commuting h hA₀R h8₀ hAΩ hΔ₀ hA₀Δ₀ hF hA₁' hA₁F))
  obtain ⟨-, -, -, w, -, -, hw, hwA, hwA₀⟩ := Sec5.exists_swap hR hA hA₀R hA₀.2
  have hw' : w ∈ A₀ ⊔ A := by rwa [sup_comm]
  have hCw := conjSub_eq_of_swap h hA hA₀ hC hw hwA
  have hPw := conjSub_eq_of_swap h hA hA₀ hP hw hwA
  have hEw := conjSub_eq_of_swap h hA hA₀ hE hw hwA
  have hC'w := conjSub_eq_of_swap h hA hA₀ hC' hw hwA
  have hFw := conjSub_eq_of_swap h hA₀R hAΩ hF hw' hwA₀
  have hP'w := conjSub_eq_of_swap h hA₀R hAΩ hP' hw' hwA₀
  rw [hAFC] at hFw
  rw [hAP'C'] at hP'w
  have hFlC : ⁅A₀, C⁆ ∈ lambdaSet R C :=
    mem_lambdaSet_comm hFR (mem_lambdaSet_commutator hR hiso hA₀R hCR hC.2.2).2
  have hClP : C ∈ lambdaSet R ⁅B₁, C⁆ := (mem_lambdaSet_commutator hR hiso hB₁.1.1 hCR hsBC).2
  have hPlC : ⁅B₁, C⁆ ∈ lambdaSet R C := mem_lambdaSet_comm hPR hClP
  have hC₁lP : ⁅A₀, ⁅B₁, C⁆⁆ ∈ lambdaSet R ⁅B₁, C⁆ :=
    mem_lambdaSet_comm hP.2.2.1 (mem_lambdaSet_commutator hR hiso hA₀R hPR hP.2.2).2
  have hP'lC' : ⁅A₀, ⁅A₁, E⁆⁆ ∈ lambdaSet R ⁅A₁, E⁆ :=
    mem_lambdaSet_comm hP'R (mem_lambdaSet_commutator hR hiso hA₀R hC'R hC'.2.2).2
  have hElC' : E ∈ lambdaSet R ⁅A₁, E⁆ := (mem_lambdaSet_commutator hR hiso hA₁.1.1 hER hsAE).2
  have hC'lE : ⁅A₁, E⁆ ∈ lambdaSet R E := mem_lambdaSet_comm hC'R hElC'
  have hC₀lE : ⁅A₀, E⁆ ∈ lambdaSet R E :=
    mem_lambdaSet_comm hE.2.2.1 (mem_lambdaSet_commutator hR hiso hA₀R hER hE.2.2).2
  have hPF : Commuting ⁅B₁, C⁆ ⁅A₀, C⁆ := by
    have hle : ⁅⁅B₁, C⁆, ⁅A₀, C⁆⁆ ≤ C :=
      commutator_le_of_le_M h hCR (QD.le_M hPlC) (QD.le_M hFlC)
    have hPF' : ⁅B₁, C⁆ ≠ ⁅A₀, C⁆ := fun e => hP.2.2.not_commuting hR (e ▸ hF.1.1.2.2)
    refine commuting_iff_commutator_eq_bot.2 ?_
    rw [← Subgroup.map_eq_bot_iff_of_injective _ (hinj w), eq_bot_iff,
      ← inf_eq_bot hR hiso hPR hFR hPF']
    refine le_inf ?_ ?_
    · rw [Subgroup.map_commutator]
      change ⁅conjSub ⁅B₁, C⁆ w, conjSub ⁅A₀, C⁆ w⁆ ≤ _
      rw [hPw, hFw]
      exact commutator_le_of_le_M h hPR (QD.le_M hC₁lP) (QD.le_M hClP)
    · exact (Subgroup.map_mono hle).trans (le_of_eq hCw)
  have hP'E : Commuting ⁅A₀, ⁅A₁, E⁆⁆ E := by
    have hle : ⁅⁅A₀, ⁅A₁, E⁆⁆, E⁆ ≤ ⁅A₁, E⁆ :=
      commutator_le_of_le_M h hC'R (QD.le_M hP'lC') (QD.le_M hElC')
    have hEP' : E ≠ ⁅A₀, ⁅A₁, E⁆⁆ := fun e => hE.2.2.not_commuting hR (e ▸ hP'.1.1.2.2)
    refine commuting_iff_commutator_eq_bot.2 ?_
    rw [← Subgroup.map_eq_bot_iff_of_injective _ (hinj w), eq_bot_iff,
      ← inf_eq_bot hR hiso hER hP'R hEP']
    refine le_inf ?_ ?_
    · rw [Subgroup.map_commutator]
      change ⁅conjSub ⁅A₀, ⁅A₁, E⁆⁆ w, conjSub E w⁆ ≤ _
      rw [hP'w, hEw]
      exact commutator_le_of_le_M h hER (QD.le_M hC'lE) (QD.le_M hC₀lE)
    · exact (Subgroup.map_mono hle).trans (le_of_eq hC'w)
  exact ⟨hPE, hPF, hP'E, hP'F⟩

theorem isConfig_chain (hEC : Special R E C) :
    IsConfig R (edgeA 3) ![⁅B₁, C⁆, A₁, E] ![⁅A₀, ⁅A₁, E⁆⁆, B₁, ⁅A₀, C⁆] := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨hP, hB₁P, hP', hA₁P', hPP'⟩ :=
    chain_node h hA h8 hA₀ hΔ hAΔ hA₁ hB₁ hne hE hC hB₁E hA₁C hECA
  obtain ⟨hPE, hPF, hP'E, hP'F⟩ :=
    chain_commuting h hA h8 hA₀ hΔ hAΔ hA₁ hB₁ hne hE hC hB₁E hA₁C hECA
  obtain ⟨hF, hFC, hAFC, hYF⟩ := CaseD4.commutator_props h hA hA₀ hC
  have hA₁F : Commuting A₁ ⁅A₀, C⁆ := hYF A₁ hA₁ hA₁C
  have hEF : Opposite E ⁅A₀, C⁆ := CaseD4.opposite_of_extremal hR hiso hA hC.1.1.1 hE.1.1.1
    hF.1.1.1 hC.1.1.2.2 hE.1.1.2.2.symm hEC hECA hFC hF.2.2 hAFC
  obtain ⟨a1, a2, a3, a4, a5, a6⟩ := config h hA h8 hA₀ hΔ hAΔ hA₁ hB₁ hne hP hB₁P hP' hA₁P' hPP'
  have e12 := config h hA h8 hA₀ hΔ hAΔ hA₁ hB₁ hne hE hB₁E hF hA₁F hEF
  refine ⟨fun k => ?_, fun k => ?_, fun k => ?_, fun i j hij => ?_, fun i j hij h1 h2 => ?_⟩
  · fin_cases k
    exacts [hP.1.1.1, hA₁.1.1, hE.1.1.1]
  · fin_cases k
    exacts [hP'.1.1.1, hB₁.1.1, hF.1.1.1]
  · fin_cases k
    exacts [hPP', opposite_of_mem_leviSet h hA h8 hA₀ hΔ hAΔ hA₁ hB₁ hne, hEF]
  · fin_cases i <;> fin_cases j <;> simp only [edgeA] at hij <;> try omega
    · refine ⟨a1.symm, a4.symm, ?_, a2.symm, ?_, a6.symm⟩
      · change ⁅⁅A₀, ⁅A₁, E⁆⁆, ⁅⁅B₁, C⁆, A₁⁆⁆ = A₁
        rw [Subgroup.commutator_comm _ A₁, Subgroup.commutator_comm]
        exact a5
      · change ⁅⁅⁅B₁, C⁆, A₁⁆, B₁⁆ = ⁅B₁, C⁆
        rw [Subgroup.commutator_comm _ A₁, Subgroup.commutator_comm]
        exact a3
    · exact e12
  · revert hij h1 h2
    fin_cases i <;> fin_cases j <;> simp [edgeA]
    · exact ⟨hPE, hPF, hP'E, hP'F⟩
    · exact ⟨hPE.symm, hP'E.symm, hPF.symm, hP'F.symm⟩

end Chain

end CaseB

end CFSG.Timmesfeld.ARS

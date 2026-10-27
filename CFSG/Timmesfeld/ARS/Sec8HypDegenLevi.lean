module

public import CFSG.Timmesfeld.ARS.Sec8HypDegen
public import CFSG.Timmesfeld.ARS.Sec8HypRadical

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Levi

section Comp

variable (h : Hyp G R) {A A₀ E₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A) (hE₀ : E₀ ∈ leviSet R A A₀)
include h hA hAne hA₀ hE₀

theorem commuting_iff_of_equiv {X Y : Subgroup G} (hX : X ∈ comp R A A₀ E₀)
    (hY : Y ∈ comp R A A₀ E₀) (hXY : Degen.Equiv (comp R A A₀ E₀) X Y) :
    ∀ Z ∈ leviSet R A A₀, Commuting X Z ↔ Commuting Y Z := by
  intro Z hZ
  by_cases hZΔ : Z ∈ comp R A A₀ E₀
  · exact hXY Z hZΔ
  · have hc : ∀ {W : Subgroup G}, W ∈ comp R A A₀ E₀ → Commuting W Z := fun hW =>
      commuting_of_notMem_comp h hA hAne hA₀ (comp_subset h hA hAne hA₀ hE₀ hW) hZ (by
        rw [comp_eq_of_mem hW]
        exact hZΔ)
    exact ⟨fun _ => hc hY, fun _ => hc hX⟩

theorem commute_of_mem_gen_cl {E B : Subgroup G} (hE : E ∈ comp R A A₀ E₀)
    (hB : B ∈ lambdaStar R A A₀) (hBE : Commuting B E) {z : G}
    (hz : z ∈ gen (Degen.cl (comp R A A₀ E₀) E)) {b : G} (hb : b ∈ B) : Commute b z := by
  have hΔΛ := comp_subset h hA hAne hA₀ hE₀
  have hle : gen (Degen.cl (comp R A A₀ E₀) E) ≤ Subgroup.centralizer (B : Set G) := by
    refine gen_le fun X hX => commuting_iff_le_centralizer.1 ?_
    exact (commuting_iff_of_mem_lambdaStar h hA hAne hA₀ (hΔΛ hE) (hΔΛ hX.1)
      (commuting_iff_of_equiv h hA hAne hA₀ hE₀ hE hX.1 hX.2) hB).1 hBE
  exact (Subgroup.mem_centralizer_iff.1 (hle hz) b hb)

theorem commutatorElement_mem_of_mem_gen_cl {E B : Subgroup G} (hE : E ∈ comp R A A₀ E₀)
    (hB : B ∈ lambdaStar R A A₀) (hBE : ¬ Commuting B E) {y : G}
    (hy : y ∈ gen (Degen.cl (comp R A A₀ E₀) E)) {b : G} (hb : b ∈ B) : ⁅b, y⁆ ∈ ⁅B, E⁆ := by
  have := h.finite
  have hR := h.root
  have hΔΛ := comp_subset h hA hAne hA₀ hE₀
  have hEΛ := hΔΛ hE
  have hsBE : Special R B E :=
    (CentralOrbit.commutator_mem_lambdaSet h hA hEΛ.1 (fun hl =>
      not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hl hEΛ.2.2.2) hB.1
      fun hc => hBE hc.symm).1.symm
  obtain ⟨hline, -⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hEΛ hB hsBE
  have hDst : ⁅B, E⁆ ∈ lambdaStar R A A₀ := hline _ hsBE.1 le_sup_right
  have hDE : Commuting ⁅B, E⁆ E := hsBE.2.2
  refine (gen_induction (p := fun y => y ∈ gen (Degen.cl (comp R A A₀ E₀) E) ∧
      ∀ b ∈ B, ⁅b, y⁆ ∈ ⁅B, E⁆) hy (fun X hX x hx => ⟨le_gen hX hx, fun b hb => ?_⟩)
    ⟨one_mem _, fun b _ => by rw [commutatorElement_one_right]; exact one_mem _⟩
    (fun y z ⟨hy, h1⟩ ⟨hz, h2⟩ => ⟨mul_mem hy hz, fun b hb => ?_⟩)).2 b hb
  ·
    have hXE : ⁅B, E⁆ = ⁅B, X⁆ := commutator_eq_of_commuting_iff h hA hAne hA₀ hEΛ (hΔΛ hX.1)
      (commuting_iff_of_equiv h hA hAne hA₀ hE₀ hE hX.1 hX.2) hB hBE
    rw [hXE]
    exact Subgroup.commutator_mem_commutator hb hx
  · have e : ⁅b, y * z⁆ = ⁅b, y⁆ * (y * ⁅b, z⁆ * y⁻¹) := by
      simp only [commutatorElement_def]
      group
    have hyD : Commute (⁅b, z⁆) y :=
      commute_of_mem_gen_cl h hA hAne hA₀ hE₀ hE hDst hDE hy (h2 b hb)
    rw [e, hyD.symm.eq, mul_inv_cancel_right]
    exact mul_mem (h1 b hb) (h2 b hb)

theorem inf_gen_cl_eq_bot {E F : Subgroup G} (hE : E ∈ comp R A A₀ E₀)
    (hF : F ∈ comp R A A₀ E₀) (hEF : Opposite E F) :
    gen (Degen.cl (comp R A A₀ E₀) E) ⊓ gen (Degen.cl (comp R A A₀ E₀) F) = ⊥ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hΔΛ := comp_subset h hA hAne hA₀ hE₀
  have hER : E ∈ R := (hΔΛ hE).1.1
  have hFR : F ∈ R := (hΔΛ hF).1.1
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  obtain ⟨hzE, hzF⟩ := Subgroup.mem_inf.1 hz
  have hzV : z ∈ levi R A A₀ :=
    gen_mono hΔΛ (Degen.gen_cl_le E hzE)
  have hzB : ∀ B ∈ lambdaStar R A A₀, ∀ b ∈ B, Commute b z := by
    intro B hB b hb
    by_cases hBE : Commuting B E
    · exact commute_of_mem_gen_cl h hA hAne hA₀ hE₀ hE hB hBE hzE hb
    by_cases hBF : Commuting B F
    · exact commute_of_mem_gen_cl h hA hAne hA₀ hE₀ hF hB hBF hzF hb
    have h1 := commutatorElement_mem_of_mem_gen_cl h hA hAne hA₀ hE₀ hE hB hBE hzE hb
    have h2 := commutatorElement_mem_of_mem_gen_cl h hA hAne hA₀ hE₀ hF hB hBF hzF hb
    have hsBE : Special R B E :=
      (CentralOrbit.commutator_mem_lambdaSet h hA (hΔΛ hE).1 (fun hl =>
        not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hl (hΔΛ hE).2.2.2)
        hB.1 fun hc => hBE hc.symm).1.symm
    have hsBF : Special R B F :=
      (CentralOrbit.commutator_mem_lambdaSet h hA (hΔΛ hF).1 (fun hl =>
        not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hl (hΔΛ hF).2.2.2)
        hB.1 fun hc => hBF hc.symm).1.symm
    have hne : ⁅B, E⁆ ≠ ⁅B, F⁆ := by
      intro e
      obtain ⟨-, hED⟩ := mem_lambdaSet_commutator hR hiso hB.1.1.1 hER hsBE
      have hDE : ⁅B, E⁆ ∈ lambdaSet R E := mem_lambdaSet_comm hsBE.1 hED
      exact not_commuting_of_opposite_of_mem_lambdaSet hR hFR hEF.symm hDE (e ▸ hsBF.2.2).symm
    have hmem : ⁅b, z⁆ ∈ ⁅B, E⁆ ⊓ ⁅B, F⁆ := Subgroup.mem_inf.2 ⟨h1, h2⟩
    rw [inf_eq_bot hR hiso hsBE.1 hsBF.1 hne, Subgroup.mem_bot] at hmem
    exact commutatorElement_eq_one_iff_mul_comm.1 hmem
  have hzM : ∀ m ∈ M R A, Commute z m := by
    have hle : M R A ≤ Subgroup.centralizer ({z} : Set G) := by
      rw [M_eq_gen_lambdaStar h hA hA₀]
      refine gen_le fun B hB b hb => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff.1 hy]
      exact (hzB B hB b hb).eq.symm
    exact fun m hm => (Subgroup.mem_centralizer_iff.1 (hle hm) z rfl)
  exact eq_one_of_forall_commute_lambdaSet hR hiso h.nondeg h.center hA hA₀
    (fun E₁ hE₁ e₁ he₁ => hzM e₁ (QD.le_M hE₁ he₁)) fun b hb =>
      (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_right A A₀ hzV) b hb).symm

end Comp

theorem eq_of_commuting_iff_of_forall (h : Hyp G R) {A A₀ E₀ E E' : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE₀ : E₀ ∈ leviSet R A A₀) (hE : E ∈ comp R A A₀ E₀) (hE' : E' ∈ comp R A A₀ E₀)
    (hEE' : ∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) {e e' : G} (he : e ∈ E)
    (he' : e' ∈ E') (he'1 : e' ≠ 1)
    (hFx : ∀ F ∈ comp R A A₀ E₀, Opposite E F → ∀ X ∈ leviSet R A A₀,
      (Commuting F X ↔ Commuting (conjSub F (e⁻¹ * e')) X)) : E = E' := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hΔΛ : comp R A A₀ E₀ ⊆ leviSet R A A₀ := comp_subset h hA hAne hA₀ hE₀
  have hEΛ := hΔΛ hE
  have hE'Λ := hΔΛ hE'
  have hER : E ∈ R := hEΛ.1.1
  have hE'R : E' ∈ R := hE'Λ.1.1
  set x : G := e⁻¹ * e' with hxdef
  have hxlevi : x ∈ levi R A A₀ :=
    mul_mem (inv_mem (le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ leviSet R A A₀) => B) E hEΛ
      he)) (le_iSup₂ (f := fun (B : Subgroup G) (_ : B ∈ leviSet R A A₀) => B) E' hE'Λ he')
  have hxA₀ : ∀ b ∈ A₀, Commute x b := fun b hb =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_right A A₀ hxlevi) b hb).symm
  have hxB : ∀ B ∈ lambdaStar R A A₀, ∀ b ∈ B, Commute x b := by
    intro B hB b hb
    have hBR : B ∈ R := hB.1.1.1
    by_cases hBE : Commuting B E
    · have hBE' : Commuting B E' :=
        (commuting_iff_of_mem_lambdaStar h hA hAne hA₀ hEΛ hE'Λ hEE' hB).1 hBE
      exact ((hBE b hb e he).symm.inv_left).mul_left (hBE' b hb e' he').symm
    have hsBE : Special R B E :=
      (CentralOrbit.commutator_mem_lambdaSet h hA hEΛ.1 (fun hl =>
        not_commuting_of_opposite_of_mem_lambdaSet hR hA₀.1 hA₀.2.symm hl hEΛ.2.2.2) hB.1
        fun hc => hBE hc.symm).1.symm
    obtain ⟨hline, F, hFΛ, hEF, hBF⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hEΛ hB hsBE
    have hF : F ∈ comp R A A₀ E₀ := by
      have h1 : F ∈ comp R A A₀ E := Relation.ReflTransGen.single ⟨hEΛ, hFΛ, hEF⟩
      rw [comp_eq_of_mem hE] at h1
      exact h1
    have hFR : F ∈ R := hFΛ.1.1
    have hFxΛ : conjSub F x ∈ leviSet R A A₀ := conjSub_mem_leviSet_of_mem_levi hR hFΛ hxlevi
    have hFFx := hFx F hF hEF
    set D := ⁅B, E⁆ with hDdef
    have hDR : D ∈ R := hsBE.1
    have hDE' : D = ⁅B, E'⁆ :=
      commutator_eq_of_commuting_iff h hA hAne hA₀ hEΛ hE'Λ hEE' hB fun hc => hBE hc
    have hDst : D ∈ lambdaStar R A A₀ := hline D hDR le_sup_right
    obtain ⟨hBD, hED⟩ := mem_lambdaSet_commutator hR hiso hBR hER hsBE
    have hDEc : Commuting D E := hED.1.2.2
    have hFD : ¬ Commuting D F := fun hc =>
      not_commuting_of_opposite_of_mem_lambdaSet hR hFR hEF.symm (mem_lambdaSet_comm hDR hED)
        hc.symm
    have hFxD : ¬ Commuting D (conjSub F x) := fun hc =>
      hFD ((commuting_iff_of_mem_lambdaStar h hA hAne hA₀ hFΛ hFxΛ hFFx hDst).2 hc)
    have hBFc : Commuting B F := hBF.1.2.2.symm
    have hBFx : Commuting B (conjSub F x) :=
      (commuting_iff_of_mem_lambdaStar h hA hAne hA₀ hFΛ hFxΛ hFFx hB).1 hBFc
    have hxbD : ∀ b' ∈ B, ⁅x, b'⁆ ∈ D := by
      intro b' hb'
      have e1 : ⁅x, b'⁆ = (e⁻¹ * ⁅e', b'⁆ * e) * ⁅e⁻¹, b'⁆ := by
        simp only [hxdef, commutatorElement_def]
        group
      have hc1 : ⁅e', b'⁆ ∈ D := by
        rw [hDE', Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator he' hb'
      have hc2 : ⁅e⁻¹, b'⁆ ∈ D := by
        rw [hDdef, Subgroup.commutator_comm]
        exact Subgroup.commutator_mem_commutator (E.inv_mem he) hb'
      have hc3 : e⁻¹ * ⁅e', b'⁆ * e = ⁅e', b'⁆ := by
        rw [mul_assoc, (hDEc _ hc1 e he).eq, inv_mul_cancel_left]
      rw [e1, hc3]
      exact D.mul_mem hc1 hc2
    have hBDl : D ∈ lambdaSet R B := mem_lambdaSet_comm hDR hBD
    have hBxle : conjSub B x ≤ B ⊔ D := by
      rintro _ ⟨b', hb', rfl⟩
      change x * b' * x⁻¹ ∈ B ⊔ D
      rw [show x * b' * x⁻¹ = ⁅x, b'⁆ * b' by rw [commutatorElement_def]; group]
      exact Subgroup.mul_mem _ (Subgroup.mem_sup_right (hxbD b' hb')) (Subgroup.mem_sup_left hb')
    have hBx : conjSub B x = B := by
      by_contra hne'
      have hBxR : conjSub B x ∈ R := hR.conjSub_mem hBR x
      obtain ⟨-, hsup⟩ := mem_lambdaSet_of_le_sup hR hiso hBR hBDl hBR le_sup_left hBxR hBxle
        (Ne.symm hne')
      have hBxFx : Commuting (conjSub B x) (conjSub F x) := hBFc.conjSub x
      have hLFx : Commuting (B ⊔ D) (conjSub F x) := hsup ▸ Commuting.sup_left hBFx hBxFx
      exact hFxD (hLFx.mono le_sup_right le_rfl)
    have hxbB : ⁅x, b⁆ ∈ B := by
      rw [commutatorElement_def]
      have hxb : x * b * x⁻¹ ∈ B := by
        rw [← hBx]
        exact conj_mem_conjSub x hb
      exact B.mul_mem hxb (B.inv_mem hb)
    have hmem : ⁅x, b⁆ ∈ B ⊓ D := ⟨hxbB, hxbD b hb⟩
    rw [inf_eq_bot hR hiso hBR hDR hBD.1.2.1, Subgroup.mem_bot,
      commutatorElement_eq_one_iff_mul_comm] at hmem
    exact hmem
  have hxM : ∀ m ∈ M R A, Commute x m := by
    have hle : M R A ≤ Subgroup.centralizer ({x} : Set G) := by
      rw [M_eq_gen_lambdaStar h hA hA₀]
      refine gen_le fun B hB b hb => Subgroup.mem_centralizer_iff.2 fun y hy => ?_
      rw [Set.mem_singleton_iff.1 hy]
      exact (hxB B hB b hb).eq
    exact fun m hm => (Subgroup.mem_centralizer_iff.1 (hle hm) x rfl)
  have hx1 : x = 1 := eq_one_of_forall_commute_lambdaSet hR hiso h.nondeg h.center hA hA₀
    (fun E₁ hE₁ e₁ he₁ => hxM e₁ (QD.le_M hE₁ he₁)) hxA₀
  have hee : e = e' := by
    have := hx1
    rw [hxdef, inv_mul_eq_one] at this
    exact this
  exact Sec3.eq_of_mem_of_mem hR hiso hER hE'R (hee ▸ he) he' he'1

theorem eq_of_commuting_iff_of_degenerate (h : Hyp G R) {A A₀ E₀ E E' : Subgroup G}
    (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE₀ : E₀ ∈ leviSet R A A₀)
    (hdeg : ∀ X ∈ comp R A A₀ E₀, ∀ Y ∈ comp R A A₀ E₀, ¬ Special R X Y)
    (hE : E ∈ comp R A A₀ E₀) (hE' : E' ∈ comp R A A₀ E₀)
    (hEE' : ∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) : E = E' := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  set Δ := comp R A A₀ E₀ with hΔdef
  have hΔΛ : Δ ⊆ leviSet R A A₀ := comp_subset h hA hAne hA₀ hE₀
  have hΔR : Δ ⊆ R := comp_subset_R h hA hAne hA₀ hE₀
  have hΔconj : ∀ X ∈ Δ, ∀ g ∈ gen Δ, conjSub X g ∈ Δ := fun X hX g hg =>
    conjSub_mem_comp_of_mem_gen h hA hAne hA₀ hE₀ hX hg
  have hE'cl : E' ∈ Degen.cl Δ E := ⟨hE', fun Z hZ => hEE' Z (hΔΛ hZ)⟩
  obtain ⟨F₀, hF₀, hEF₀⟩ := exists_opposite_mem_comp h hA hAne hA₀ hE₀ hE
  have hEF₀' : ¬ Commuting E F₀ := hEF₀.not_commuting (hR.ne_bot E (hΔR hE))
  obtain ⟨e', he', he'1⟩ := hR.exists_ne_one (hΔR hE')
  obtain ⟨a, ha, hxN⟩ :=
    Degen.exists_mul_mem_normCl hR hΔR hΔconj hdeg hE hF₀ hEF₀' hE'cl he'
  have hcomm : e' * a = a * e' :=
    (Degen.commuting_of_equiv hR hΔR hE hE'cl.2 a ha e' he').symm.eq
  refine eq_of_commuting_iff_of_forall h hA hAne hA₀ hE₀ hE hE' hEE' (E.inv_mem ha) he' he'1
    fun F hF hEF => ?_
  have hEF' : ¬ Commuting E F := hEF.not_commuting (hR.ne_bot E (hΔR hE))
  have hxF := Degen.mem_normCl_of_mem_normCl hR hiso hΔR hΔconj hdeg hE hF₀ hF hEF₀' hEF'
    (inf_gen_cl_eq_bot h hA hAne hA₀ hE₀ hE hF hEF) hxN
  have hequiv := ((Degen.mem_normCl_iff hΔconj hF).1 hxF).2
  rw [inv_inv, ← hcomm]
  have hFx : conjSub F (e' * a) ∈ Δ :=
    hΔconj F hF _ (Degen.gen_cl_le E (Subgroup.mem_inf.1 hxF).1)
  exact commuting_iff_of_equiv h hA hAne hA₀ hE₀ hF hFx hequiv

theorem eq_of_commuting_iff' (h : Hyp G R) {A A₀ E₀ E E' : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE₀ : E₀ ∈ leviSet R A A₀) (hE : E ∈ comp R A A₀ E₀) (hE' : E' ∈ comp R A A₀ E₀)
    (hEE' : ∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) : E = E' := by
  by_cases hnd : ∃ X ∈ comp R A A₀ E₀, ∃ Y ∈ comp R A A₀ E₀, Special R X Y
  · exact eq_of_commuting_iff h hA hAne hA₀ hE₀ hnd hE hE' hEE'
  · exact eq_of_commuting_iff_of_degenerate h hA hAne hA₀ hE₀
      (fun X hX Y hY hs => hnd ⟨X, hX, Y, hY, hs⟩) hE hE' hEE'

theorem eq_of_commuting_iff_of_mem_leviSet' (h : Hyp G R) {A A₀ E E' : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE : E ∈ leviSet R A A₀) (hE' : E' ∈ leviSet R A A₀)
    (hEE' : ∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) : E = E' := by
  refine eq_of_commuting_iff' h hA hAne hA₀ hE Relation.ReflTransGen.refl ?_ hEE'
  by_contra hn
  obtain ⟨F, hF, hEF⟩ := exists_opposite_mem_comp h hA hAne hA₀ hE Relation.ReflTransGen.refl
  have hFΛ := comp_subset h hA hAne hA₀ hE hF
  have hFE' : Commuting F E' := commuting_of_notMem_comp h hA hAne hA₀ hFΛ hE' (by
    rw [comp_eq_of_mem hF]
    exact hn)
  exact hEF.not_commuting (h.root.ne_bot E hE.1.1) ((hEE' F hFΛ).2 hFE'.symm)

theorem forall_eq_of_commuting_iff (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) :
    ∀ E ∈ leviSet R A A₀, ∀ E' ∈ leviSet R A A₀,
      (∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) → E = E' :=
  fun _ hE _ hE' => eq_of_commuting_iff_of_mem_leviSet' h hA hAne hA₀ hE hE'

end Levi

end CFSG.Timmesfeld.ARS

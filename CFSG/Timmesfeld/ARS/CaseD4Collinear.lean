module

public import CFSG.Timmesfeld.ARS.CaseD4Basic
public import CFSG.Timmesfeld.ARS.Sec5Seven

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseD4

theorem mem_lambdaSet_of_commuting_of_not (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) {Y Y' : Subgroup G}
    (hYl : Y ∈ leviSet R A A₀) (hY'l : Y' ∈ leviSet R A A₀) (hYY' : Opposite Y Y')
    (hfix : ∀ T ∈ lambdaStar R A A₀, Commuting Y' T → Commuting Y T → False) {X : Subgroup G}
    (hX : X ∈ lambdaStar R A A₀) (hQX : Commuting Y X) : X ∈ lambdaSet R Y := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hY : Y ∈ R := hYl.1.1
  have hY' : Y' ∈ R := hY'l.1.1
  have hXR : X ∈ R := hX.1.1.1
  have hs : Special R Y' X :=
    special_of_commuting_of_not hR hA hX hY'l (fun h1 h2 => hfix X hX h2 h1) hQX
  set D := ⁅Y', X⁆ with hDdef
  set E := ⁅Y, D⁆ with hEdef
  set N := D ⊔ E with hNdef
  set W := X ⊔ N with hWdef
  set Z := W ⊓ Subgroup.centralizer ((Y ⊔ Y' ⊔ X : Subgroup G) : Set G) with hZdef
  obtain ⟨⟨hDl, hDp, -, hNinv, -⟩, ⟨-, -, hMinv, -, -, -, hNZ'⟩, ⟨-, hFZ, hZiff⟩⟩ :=
    natural_module_of_commuting hR hiso hY hY' hYY' ⟨hXR, hs⟩ hQX (N := N) (M := W) (Z := Z)
      rfl rfl rfl
  rw [← hZiff]
  by_contra hZne
  have hDR : D ∈ R := hDl.1.1
  have hD : D ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hY'l hX hs.symm).1 D hDR
    rw [Subgroup.commutator_comm X Y'] at this
    exact this le_sup_right
  have hDY : Special R D Y := hDp.2.symm
  have hER : E ∈ R := hDp.2.1
  have hNinv' : ∀ x ∈ Y' ⊔ Y, conjSub N x = N := fun x hx =>
    Sec3.conjSub_sup_commutator_eq hR hiso hY' hY hYY'.symm hDl hDp hx
  have hfixY' : ∀ n ∈ N, (∀ a ∈ Y', Commute a n) → n ∈ D := fun n hn hnA =>
    Sec3.mem_of_forall_commute_of_mem_sup hR hiso hY' hY hYY'.symm hDl hDp hn hnA
  have hE : E ∈ lambdaStar R A A₀ := by
    have := (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hYl hD hDY).1 E hER
    rw [Subgroup.commutator_comm D Y] at this
    exact this le_sup_right
  have hDE : D ≠ E := by
    have := hDY.ne_commutator hR
    rwa [Subgroup.commutator_comm D Y] at this
  have hEl : E ∈ lambdaSet R Y :=
    mem_lambdaSet_comm hER (mem_lambdaSet_commutator hR hiso hY hDR hDp.2).1
  have hEN : E ≤ N := le_sup_right
  have hY'N : Y' ≤ Subgroup.normalizer ((N : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (hNinv' y (Subgroup.mem_sup_left hy))
  have hYN : Y ≤ Subgroup.normalizer ((N : Subgroup G) : Set G) := fun y hy =>
    conjSub_eq_self_iff.1 (hNinv' y (Subgroup.mem_sup_right hy))
  have hEs : Special R Y' E := by
    have hnc : ¬ Commuting Y' E := by
      intro hc
      refine hDE (Subgroup.eq_of_le_of_card_ge (fun e he => ?_) (hR.card_eq hDR hER).le).symm
      exact hfixY' e (hEN he) fun y hy => hc y hy e he
    have hne : Y' ≠ E := fun e => hnc (by rw [← e]; exact hR.commuting_self hY')
    rcases hR.rel _ hY' _ hER hne with hc | ho | hs'
    · exact absurd hc hnc
    · exact absurd ho (not_opposite_of_mem_leviSet hR hA hE hY'l)
    · exact hs'
  have hY'E : ⁅Y', E⁆ = D := by
    refine Subgroup.eq_of_le_of_card_ge (fun x hx => ?_) (hR.card_eq hDR hEs.1).le
    have hle : ⁅Y', E⁆ ≤ N := by
      rw [Subgroup.commutator_comm]
      exact commutator_le_of_le_normalizer hEN hY'N
    exact hfixY' x (hle hx) fun y hy => (hEs.2.1 x hx y hy).symm
  have hfixY : ∀ n ∈ N, (∀ a ∈ Y, Commute a n) → n ∈ E := fun n hn hnA => by
    refine Sec3.mem_of_forall_commute_of_mem_sup hR hiso hY hY' hYY' hEl ⟨hER, hEs⟩ ?_ hnA
    rw [hY'E, sup_comm]
    exact hn
  have hXN : X ≤ Subgroup.normalizer ((N : Subgroup G) : Set G) := fun x hx =>
    conjSub_eq_self_iff.1 (hNinv x (Subgroup.mem_sup_right hx))
  have hCM : ∀ m ∈ W, (∀ y ∈ Y, Commute y m) → m ∈ E ⊔ X := by
    intro m hm hmY
    have hm' : m ∈ ((N ⊔ X : Subgroup G) : Set G) := by rw [sup_comm]; exact hm
    rw [Subgroup.coe_mul_of_right_le_normalizer_left _ _ hXN] at hm'
    obtain ⟨n, hn, x, hx, rfl⟩ := hm'
    have hnY : ∀ y ∈ Y, Commute y n := fun y hy => by
      have h1 := hmY y hy
      have h2 : Commute y x := hQX y hy x hx
      have h3 := h1.mul_right h2.inv_right
      rwa [mul_inv_cancel_right] at h3
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left (hfixY n hn hnY)) (Subgroup.mem_sup_right hx)
  have hZXE : Z ≤ E ⊔ X := fun z hz => hCM z hz.1 fun y hy =>
    (Subgroup.mem_centralizer_iff.1 hz.2) y (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))
  have hXE : X ≠ E := by
    intro e
    apply hZne
    have hMN : W = N := le_antisymm (sup_le (e ▸ hEN) le_rfl) le_sup_right
    have : Z ≤ N ⊓ Z := le_inf (inf_le_left.trans hMN.le) le_rfl
    rw [hNZ'] at this
    exact le_bot_iff.1 this
  have hMMD : W ≤ M R D := by
    refine sup_le (QD.le_M (mem_lambdaSet_commutator hR hiso hY' hXR hs).2)
      (sup_le QD.le_M_self (QD.le_M (mem_lambdaSet_comm hER
        (mem_lambdaSet_commutator hR hiso hY hDR hDp.2).2)))
  obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hDR
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
  obtain ⟨g, hg, hge⟩ := Sec3.exists_conj_eq_of_mem_sup hR hiso hY' hY hYY'.symm hDl hDp
    (Subgroup.mem_sup_left hd) hd1 (Subgroup.mem_sup_right he) he1
  have hDg : conjSub D g = E :=
    Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hDR g) hER (hge ▸ conj_mem_conjSub g hd) he he1
  have hMME : W ≤ M R E := by
    rw [← hDg, ← Sec5.conjSub_M hR D g, ← hMinv g (Subgroup.mem_sup_left (sup_comm Y' Y ▸ hg))]
    exact Subgroup.map_mono hMMD
  have hXEl : X ∈ lambdaSet R E := by
    have hmem : X ∈ {B | B ∈ R ∧ B ≤ M R E} := ⟨hXR, le_sup_left.trans hMME⟩
    rw [(Q_eq_M h hER).2.1] at hmem
    exact hmem.resolve_left hXE
  obtain ⟨z, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hZne
  obtain ⟨T, hTR, hTle, hzT⟩ := hXEl.2 z (hZXE z.2) (fun h1 => hz1 (Subtype.ext h1))
  have hTM : T ≤ W := hTle.trans (sup_le (hEN.trans le_sup_right) le_sup_left)
  have hTZ : T = Z := by
    rcases hFZ T hTR hTM with h1 | h1
    · exfalso
      have : (z : G) ∈ T ⊓ Z := ⟨hzT, z.2⟩
      rw [h1, Subgroup.mem_bot] at this
      exact hz1 (Subtype.ext this)
    · exact h1
  have hZR : Z ∈ R := hTZ ▸ hTR
  have hZYY' : Commuting Y Z ∧ Commuting Y' Z := by
    refine ⟨fun y hy w hw => ?_, fun y hy w hw => ?_⟩
    · exact (Subgroup.mem_centralizer_iff.1 hw.2) y
        (Subgroup.mem_sup_left (Subgroup.mem_sup_left hy))
    · exact (Subgroup.mem_centralizer_iff.1 hw.2) y
        (Subgroup.mem_sup_left (Subgroup.mem_sup_right hy))
  have hZMA : Z ≤ M R A := hZXE.trans (sup_le (QD.le_M hE.1) (QD.le_M hX.1))
  have hmem : Z ∈ {B | B ∈ R ∧ B ≤ M R A} := ⟨hZR, hZMA⟩
  rw [(Q_eq_M h hA).2.1] at hmem
  rcases hmem with hZA | hZl
  ·
    have hline := sup_eq_of_le_of_commuting hR hiso hER hXR hA hXR hXEl.1.2.2
      (hZA ▸ hZXE) le_sup_right hX.1.1.2.1.symm
    obtain ⟨T', -, huniq⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hX.1
    exact hXE ((huniq X ⟨hXR, le_sup_right, hX.2⟩).trans
      (huniq E ⟨hER, hline ▸ le_sup_left, hE.2⟩).symm)
  ·
    obtain ⟨T', ⟨hT'R, hT'le, hT'ψ⟩, -⟩ :=
      existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hZl
    have hT'A : T' ≠ A := fun e => hT'ψ.2.not_opposite hR hA₀.1 (e ▸ hA₀.2.symm)
    have hT'l : T' ∈ lambdaSet R A := by
      have hm : T' ∈ {B | B ∈ R ∧ B ≤ M R A} :=
        ⟨hT'R, hT'le.trans (sup_le QD.le_M_self hZMA)⟩
      rw [(Q_eq_M h hA).2.1] at hm
      exact hm.resolve_left hT'A
    have hc : ∀ W : Subgroup G, W ∈ leviSet R A A₀ → Commuting W Z → Commuting W T' :=
      fun W hW hWZ => (Commuting.sup_right hW.1.2.2.symm hWZ).mono le_rfl hT'le
    exact hfix T' ⟨hT'l, hT'ψ⟩ (hc Y' hY'l hZYY'.2) (hc Y hYl hZYY'.1)

section Factors

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  {ι : Type*} {P Q : ι → Subgroup G} (hPQ : LeviSL2Family R A A₀ P Q)
include h hA hAne hmax hA₀ hPQ

theorem mem_lambdaSet_of_commuting {X : Subgroup G} (hX : X ∈ lambdaStar R A A₀) (i : ι)
    (hQX : Commuting (Q i) X) : X ∈ lambdaSet R (Q i) :=
  mem_lambdaSet_of_commuting_of_not h hA hAne hA₀ (hPQ.mem_right i) (hPQ.mem_left i)
    (hPQ.opposite i).symm (fun _ hT hP hQ => not_commuting_and_commuting h hA hAne hmax hA₀ hPQ hT i
      hP hQ) hX hQX

theorem mem_lambdaSet_of_commuting' {X : Subgroup G} (hX : X ∈ lambdaStar R A A₀) (i : ι)
    (hPX : Commuting (P i) X) : X ∈ lambdaSet R (P i) :=
  mem_lambdaSet_of_commuting h hA hAne hmax hA₀ hPQ.swap hX i hPX

end Factors

end CaseD4

end CFSG.Timmesfeld.ARS

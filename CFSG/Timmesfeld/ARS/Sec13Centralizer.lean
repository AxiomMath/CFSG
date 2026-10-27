module

public import CFSG.Timmesfeld.ARS.Sec13Bijection
public import CFSG.Timmesfeld.ARS.CaseD4Frame

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem commuting_of_mem_deltaSet_of_mem_lambdaSet (h : Hyp G R) {A A₀ B E X : Subgroup G}
    (hA : A ∈ R) (hA₀ : A₀ ∈ omegaSet R A) (hB : B ∈ lambdaStar R A A₀)
    (hE : E ∈ deltaSet R A A₀ B) (hX : X ∈ leviSet R A A₀) (hXE : X ∈ lambdaSet R E) :
    Commuting X B :=
  (commuting_of_mem_lambdaSet_of_mem_leviSet h hA hA₀ hB.1 hE.1
    (mem_lambdaSet_comm hB.1.1.1 hE.2) hX hXE).symm

theorem conjSet_deltaSet_eq_of_commuting (hR : IsRootClass R) {A A₀ B X : Subgroup G}
    (hX : X ∈ leviSet R A A₀) (hXB : Commuting X B) {x : G} (hx : x ∈ X) :
    conjSet (deltaSet R A A₀ B) x = deltaSet R A A₀ B := by
  rw [conjSet_deltaSet hR (le_gen hX hx),
    conjSub_of_forall_commute fun b hb => hXB x hx b hb]

theorem le_stabSet_deltaSet_of_commuting (hR : IsRootClass R) {A A₀ B X : Subgroup G}
    (hX : X ∈ leviSet R A A₀) (hXB : Commuting X B) : X ≤ stabSet (deltaSet R A A₀ B) :=
  fun _ hx => mem_stabSet.2 (conjSet_deltaSet_eq_of_commuting hR hX hXB hx)

namespace Sec13

variable {A A₀ : Subgroup G} (hS : Sec13 R A A₀)
include hS

theorem commuting_of_forall_conjSet_eq {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀)
    (hXN : ∀ x ∈ X, conjSet (deltaSet R A A₀ B) x = deltaSet R A A₀ B) : Commuting X B := by
  have hR := hS.hyp.root
  refine Sec3.commuting_of_forall_conjSub_eq hR hX.1.1 hB.1.1.1 (fun x hx => ?_)
    hS.hyp.noIsolated
  have hxV : x ∈ levi R A A₀ := le_gen hX hx
  refine hS.eq_of_deltaSet_eq (conjSub_mem_lambdaStar_of_mem_levi hR hB hxV) hB ?_
  rw [← conjSet_deltaSet hR hxV, hXN x hx]

theorem setOf_commuting_eq {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    {X | X ∈ leviSet R A A₀ ∧ Commuting X B} =
      {X | X ∈ leviSet R A A₀ ∧ ∀ x ∈ X, conjSet (deltaSet R A A₀ B) x = deltaSet R A A₀ B} := by
  ext X
  exact ⟨fun ⟨hX, hXB⟩ => ⟨hX, fun x hx => conjSet_deltaSet_eq_of_commuting hS.hyp.root hX hXB hx⟩,
    fun ⟨hX, hXN⟩ => ⟨hX, hS.commuting_of_forall_conjSet_eq hB hX hXN⟩⟩

theorem commuting_of_forall_commuting {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) (hXΔ : ∀ Y ∈ deltaSet R A A₀ B, Commuting X Y) :
    Commuting X B := by
  refine hS.commuting_of_forall_conjSet_eq hB hX fun x hx => ?_
  ext Y
  rw [mem_conjSet]
  constructor
  · intro hY
    have hc := hXΔ _ hY
    have h1 : conjSub (conjSub Y x⁻¹) x = conjSub Y x⁻¹ :=
      conjSub_of_forall_commute fun y hy => hc x hx y hy
    rw [Plane.conjSub_inv_conjSub] at h1
    rwa [h1]
  · intro hY
    rwa [conjSub_of_forall_commute fun y hy => (hXΔ Y hY x⁻¹ (X.inv_mem hx) y hy)]

theorem conjSub_mem_of_mem_stabSet {B X : Subgroup G} {g : G} (hg : g ∈ levi R A A₀)
    (hgB : g ∈ stabSet (deltaSet R A A₀ B)) (hX : X ∈ leviSet R A A₀)
    (hXΔ : ∀ Y ∈ deltaSet R A A₀ B, Commuting X Y) :
    conjSub X g ∈ leviSet R A A₀ ∧ ∀ Y ∈ deltaSet R A A₀ B, Commuting (conjSub X g) Y := by
  refine ⟨Levi.conjSub_mem_leviSet_of_mem_levi hS.hyp.root hX hg, fun Y hY => ?_⟩
  have hY' : Y ∈ conjSet (deltaSet R A A₀ B) g := by rw [mem_stabSet.1 hgB]; exact hY
  obtain ⟨Y', hY'Δ, rfl⟩ := hY'
  exact (hXΔ Y' hY'Δ).conjSub g

theorem setOf_forall_commuting_eq {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    {X | X ∈ leviSet R A A₀ ∧ ∀ Y ∈ deltaSet R A A₀ B, Commuting X Y} = deltaSet R A A₀ B := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hA₀ := hS.opp
  have hBR : B ∈ R := hB.1.1.1
  refine Set.Subset.antisymm (fun X₀ ⟨hX₀, hX₀Δ⟩ => ?_) fun X hX =>
    ⟨hX.1, fun Y hY => commuting_of_mem_deltaSet hS.hyp hA hA₀ hB hX hY⟩
  by_contra hX₀B
  set S := {X | X ∈ leviSet R A A₀ ∧ (∀ Y ∈ deltaSet R A A₀ B, Commuting X Y) ∧
    X ∉ deltaSet R A A₀ B} with hSdef
  obtain ⟨E, ⟨hE, hEΔ, hEB⟩, F, hF, hEF, hFB⟩ : ∃ E ∈ S, ∃ F ∈ leviSet R A A₀,
      Opposite E F ∧ ¬ Commuting F B := by
    by_contra! hall
    have hclosed : ∀ E F, E ∈ S → oppGraph (leviSet R A A₀) E F → F ∈ S := by
      rintro E F ⟨hE, hEΔ, hEB⟩ ⟨-, hF, hEF⟩
      have hFB := hall E ⟨hE, hEΔ, hEB⟩ F hF hEF
      have hEB' := hS.commuting_of_forall_commuting hB hE hEΔ
      obtain ⟨y, hy, hyF⟩ := Sec3.exists_mem_sup_conjSub_eq hR hE.1.1 hEF
      have hyV : y ∈ levi R A A₀ := sup_le (le_gen hE) (le_gen hF) hy
      have hyS : y ∈ stabSet (deltaSet R A A₀ B) :=
        sup_le (le_stabSet_deltaSet_of_commuting hR hE hEB')
          (le_stabSet_deltaSet_of_commuting hR hF hFB) hy
      obtain ⟨-, hFΔ⟩ := hS.conjSub_mem_of_mem_stabSet hyV hyS hE hEΔ
      rw [hyF] at hFΔ
      refine ⟨hF, hFΔ, fun hFB' => ?_⟩
      exact hEF.not_commuting (hR.ne_bot E hE.1.1) (hEΔ F hFB')
    have hpathS : ∀ Z, Relation.ReflTransGen (oppGraph (leviSet R A A₀)) X₀ Z → Z ∈ S := by
      intro Z hZ
      induction hZ with
      | refl => exact ⟨hX₀, hX₀Δ, hX₀B⟩
      | tail _ hcd ih => exact hclosed _ _ ih hcd
    obtain ⟨Y, hY⟩ := deltaSet_nonempty hS.hyp hA hS.sec8.2 hA₀ hB
    exact (hpathS Y (hS.conn X₀ hX₀ Y hY.1)).2.2 hY
  have hEB' : Commuting E B := hS.commuting_of_forall_commuting hB hE hEΔ
  have hBF : Special R B F :=
    special_of_not_commuting_of_mem_leviSet hS.hyp hA hB hF fun h' => hFB h'.symm
  have hER : E ∈ R := hE.1.1
  have hFR : F ∈ R := hF.1.1
  obtain ⟨hP, hPB, hPF⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hA₀ hB hF hBF
  set P := ⁅B, F⁆ with hPdef
  have hPR : P ∈ R := hP.1.1.1
  have hPE : Special R P E := by
    refine special_of_not_commuting_of_mem_leviSet hS.hyp hA hP hE fun h' => ?_
    exact not_commuting_of_opposite_of_mem_lambdaSet hR hER hEF hPF h'.symm
  obtain ⟨hC, hCP, hCE⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hA₀ hP hE hPE
  set C := ⁅P, E⁆ with hCdef
  have hCR : C ∈ R := hC.1.1.1
  have hBψ : B ∈ psiSet R F := ⟨hBR, hBF.symm⟩
  have hFB' : ⁅F, B⁆ = P := Subgroup.commutator_comm F B
  have hEP : ⁅E, P⁆ = C := Subgroup.commutator_comm E P
  have hNinv : ∀ x ∈ E ⊔ F ⊔ B, conjSub (B ⊔ (P ⊔ C)) x = B ⊔ (P ⊔ C) := by
    intro x hx
    have := Sec3.conjSub_sup_sup_eq_of_commuting hR hiso hER hFR hEF hBψ hEB' hx
    rwa [hFB', hEP] at this
  have hNM : B ⊔ (P ⊔ C) ≤ M R P :=
    sup_le (QD.le_M (mem_lambdaSet_comm hBR hPB)) (sup_le QD.le_M_self (QD.le_M hCP))
  have hPψE : P ∈ psiSet R E := ⟨hPR, hPE.symm⟩
  obtain ⟨n, hn, hn1⟩ := hR.exists_ne_one hPR
  obtain ⟨n', hn', hn'1⟩ := hR.exists_ne_one hCR
  have hPl : P ∈ lambdaSet R F := hPF
  obtain ⟨x, hx, hxn⟩ := Sec3.exists_conj_eq_of_mem_sup hR hiso hFR hER hEF.symm hPl hPψE
    (Subgroup.mem_sup_left hn) hn1 (by rw [hEP]; exact Subgroup.mem_sup_right hn') hn'1
  have hPx : conjSub P x = C :=
    Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hPR x) hCR (hxn ▸ conj_mem_conjSub x hn) hn'
      hn'1
  have hxN : x ∈ E ⊔ F ⊔ B := (le_sup_left : E ⊔ F ≤ E ⊔ F ⊔ B) (by rwa [sup_comm] at hx)
  have hBC : B ∈ lambdaSet R C := by
    have hBx : conjSub B x⁻¹ ≤ M R P := by
      calc conjSub B x⁻¹ ≤ conjSub (B ⊔ (P ⊔ C)) x⁻¹ := Subgroup.map_mono le_sup_left
        _ = B ⊔ (P ⊔ C) := hNinv _ (Subgroup.inv_mem _ hxN)
        _ ≤ M R P := hNM
    have hmem : conjSub B x⁻¹ ∈ {X | X ∈ R ∧ X ≤ M R P} := ⟨hR.conjSub_mem hBR _, hBx⟩
    rw [(Q_eq_M hS.hyp hPR).2.1] at hmem
    rcases hmem with h1 | h1
    · exfalso
      have : B = C := by
        rw [← hPx, ← h1, ← conjSub_mul, mul_inv_cancel, conjSub_one]
      rw [← this] at hCE
      exact hEB (⟨hE, mem_lambdaSet_comm hER hCE⟩ : E ∈ deltaSet R A A₀ B)
    · have := conjSub_mem_lambdaSet hR h1 x
      rwa [← conjSub_mul, mul_inv_cancel, conjSub_one, hPx] at this
  obtain ⟨D, hD, hCDB⟩ := exists_commutator_eq_of_mem_lambdaStar hS.hyp hA hS.sec8.2 hA₀ hC hB
    (mem_lambdaSet_comm hCR hBC)
  have hsCD : Special R C D := special_of_commutator_mem_of_mem_leviSet hS.hyp hA hC hD
    (hCDB ▸ hBR)
  have hDB : D ∈ lambdaSet R B := by
    have := (mem_lambdaSet_commutator hR hiso hCR hD.1.1 hsCD).2
    rwa [hCDB] at this
  have hED : Commuting E D := hEΔ D ⟨hD, hDB⟩
  have hBle : B ≤ M R E := by
    rw [← hCDB]
    exact commutator_le_of_le_normalizer (QD.le_M hCE) (QD.le_normalizer_M hR hER ⟨hD.1.1, hED⟩)
  have hBE : B ∈ lambdaSet R E := mem_lambdaSet_of_le_M_of_hyp hS.hyp hER hBR hBle
    fun e => hB.2.2.not_commuting hR (by rw [e]; exact hE.2.2.2)
  exact hEB ⟨hE, mem_lambdaSet_comm hER hBE⟩

theorem setOf_le_gen_deltaSet_eq {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) :
    {X | X ∈ leviSet R A A₀ ∧ X ≤ gen (deltaSet R A A₀ B)} = deltaSet R A A₀ B := by
  refine Set.Subset.antisymm (fun X ⟨hX, hXle⟩ => ?_) fun X hX => ⟨hX.1, le_gen hX⟩
  rw [← hS.setOf_forall_commuting_eq hB]
  exact ⟨hX, fun Y hY => ((commuting_gen_deltaSet hS.hyp hS.mem hS.opp hB).mono hXle
    (le_gen hY))⟩

end Sec13

end CFSG.Timmesfeld.ARS

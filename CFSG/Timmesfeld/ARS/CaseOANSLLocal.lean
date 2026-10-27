module

public import CFSG.Timmesfeld.ARS.CaseOAInter
public import CFSG.Timmesfeld.ARS.CaseOALevi

public section

open scoped commutatorElement

namespace CFSG.Timmesfeld.ARS

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseOANSL

theorem eq_of_deltaSet_eq (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hint : ∀ B ∈ lambdaStar R A A₀, ∀ C ∈ lambdaStar R A A₀, Commuting B C →
      (lambdaStar R A A₀ ∩ lambdaSet R B ∩ lambdaSet R C).Nonempty)
    {B C : Subgroup G} (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀)
    (heq : deltaSet R A A₀ B = deltaSet R A A₀ C) : B = C := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hBR : B ∈ R := hB.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  by_contra hne
  obtain ⟨Y, hY⟩ := deltaSet_nonempty h hA hAne hA₀ hB
  have hYC : Y ∈ deltaSet R A A₀ C := heq ▸ hY
  have hYR : Y ∈ R := hY.1.1.1
  have hBC : Commuting B C := by
    rcases commuting_or_commutator_eq_of_mem_lambdaSet h hA hB.1 hC.1 hne with hc | ⟨-, hBCA⟩
    · exact hc
    · rcases commuting_or_commutator_eq_of_mem_lambdaSet h hYR (mem_lambdaSet_comm hBR hY.2)
          (mem_lambdaSet_comm hCR hYC.2) hne with hc | ⟨-, hBCY⟩
      · exact hc
      · exact absurd (hBCA.symm.trans hBCY) (fun e => hY.1.1.2.1 e.symm)
  have hCB : C ∉ lambdaSet R B := by
    intro hCB
    obtain ⟨X, hX, hBXC⟩ :=
      exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hB hC (mem_lambdaSet_comm hBR hCB)
    have hs : Special R B X := special_of_commutator_mem_of_mem_leviSet h hA hB hX (hBXC ▸ hCR)
    have hXC : X ∈ lambdaSet R C := by
      have := (mem_lambdaSet_commutator hR hiso hBR hX.1.1 hs).2
      rwa [hBXC] at this
    have hXB : X ∈ deltaSet R A A₀ B := by
      rw [heq]
      exact ⟨hX, hXC⟩
    exact hs.not_commuting hR hXB.2.1.2.2
  obtain ⟨D, ⟨hD, hDB⟩, hDC⟩ := hint B hB C hC hBC
  have hDR : D ∈ R := hD.1.1.1
  obtain ⟨X, hX, hDXB⟩ :=
    exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hD hB hDB
  have hs : Special R D X := special_of_commutator_mem_of_mem_leviSet h hA hD hX (hDXB ▸ hBR)
  have hXB : X ∈ lambdaSet R B := by
    have := (mem_lambdaSet_commutator hR hiso hDR hX.1.1 hs).2
    rwa [hDXB] at this
  have hXC : X ∈ lambdaSet R C := by
    have hXΔ : X ∈ deltaSet R A A₀ B := ⟨hX, hXB⟩
    rw [heq] at hXΔ
    exact hXΔ.2
  have hle : B ≤ C := by
    rw [← hDXB, ← (Q_eq_M h hCR).2.2.1]
    exact Subgroup.commutator_mono (QD.le_M hDC) (QD.le_M hXC)
  exact hne (Subgroup.eq_of_le_of_card_ge hle (hR.card_eq hCR hBR).le)

section OA

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
  (h2 : Nat.card (leviComps R A A₀) = 2) {Δ₁ Δ₂ : Set (Subgroup G)}
  (hΔ₁ : Δ₁ ∈ leviComps R A A₀) (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂)
include h hA hAne hmax hA₀ hΔ₁ hΔ₂ hne

theorem eq_of_deltaSet_eq_OA {B C : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (heq : deltaSet R A A₀ B = deltaSet R A A₀ C) : B = C :=
  eq_of_deltaSet_eq h hA hAne hA₀ (fun _ hB' _ hC' hBC =>
    CaseOA.lambdaStar_inter_nonempty h hA hAne hmax hA₀ hΔ₁ hΔ₂ hne hB' hC' hBC) hB hC heq

theorem conjSub_eq_of_forall_commute {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) {z : G}
    (hz : z ∈ levi R A A₀) (hzΔ : ∀ X ∈ leviSet R A A₀, ∀ x ∈ X, Commute z x) :
    conjSub B z = B := by
  have hR := h.root
  have hfix : ∀ X ∈ leviSet R A A₀, conjSub X z = X := fun X hX =>
    conjSub_of_forall_commute fun x hx => hzΔ X hX x hx
  refine eq_of_deltaSet_eq_OA h hA hAne hmax hA₀ hΔ₁ hΔ₂ hne
    (conjSub_mem_lambdaStar_of_mem_levi hR hB hz) hB ?_
  rw [← conjSet_deltaSet hR hz]
  ext X
  constructor
  · rintro ⟨Y, hY, rfl⟩
    show conjSub Y z ∈ _
    rw [hfix Y hY.1]
    exact hY
  · intro hX
    exact ⟨X, hX, hfix X hX.1⟩

omit hmax in
theorem commute_of_mem_center (h2 : Nat.card (leviComps R A A₀) = 2) {z : ↥(gen Δ₁)}
    (hz : z ∈ Subgroup.center ↥(gen Δ₁)) {X : Subgroup G} (hX : X ∈ leviSet R A A₀)
    {x : G} (hx : x ∈ X) : Commute (z : G) x := by
  have hxV : x ∈ gen Δ₁ ⊔ gen Δ₂ := by
    rw [← CaseOA.levi_eq_sup h hA hAne hA₀ h2 hΔ₁ hΔ₂ hne]
    exact le_gen hX hx
  have hc := Sec9.commuting_gen_of_ne h hA hAne hA₀ hΔ₁ hΔ₂ hne
  have h1 : gen Δ₁ ≤ Subgroup.centralizer {(z : G)} := fun y hy => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (Subgroup.mem_center_iff.1 hz ⟨y, hy⟩)
  have h2' : gen Δ₂ ≤ Subgroup.centralizer {(z : G)} := fun y hy => by
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hc _ z.2 y hy).symm.eq
  have := sup_le h1 h2' hxV
  rw [Subgroup.mem_centralizer_singleton_iff] at this
  exact this.symm

end OA

section General

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hA₀ : A₀ ∈ omegaSet R A)
  (hint : ∀ B ∈ lambdaStar R A A₀, ∀ C ∈ lambdaStar R A A₀, Commuting B C →
    (lambdaStar R A A₀ ∩ lambdaSet R B ∩ lambdaSet R C).Nonempty)
include h hA hAne hA₀

omit hint in
theorem exists_mem_deltaSet_reflTransGen (hmax : IsSigmaMaximal R (centralGroup R A))
    {B : Subgroup G} (hB : B ∈ lambdaStar R A A₀) {X : Subgroup G} (hX : X ∈ leviSet R A A₀) :
    ∃ Y ∈ deltaSet R A A₀ B, Relation.ReflTransGen (oppGraph (leviSet R A A₀)) X Y := by
  have hΔ : Levi.comp R A A₀ X ∈ leviComps R A A₀ := ⟨X, hX, rfl⟩
  obtain ⟨Y, hY, hYB⟩ : ∃ Y ∈ Levi.comp R A A₀ X, ¬ Commuting Y B := by
    by_contra! hall
    exact Sec9.not_forall_commuting h hA hAne hA₀ hmax hΔ hB hall
  have hYl := Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hY
  have hs := special_of_not_commuting_of_mem_leviSet h hA hB hYl fun hc => hYB hc.symm
  obtain ⟨-, D, hD, hYD, hBD⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hYl hB hs
  have hDc : D ∈ Levi.comp R A A₀ X := Sec9.mem_of_opposite h hA hAne hA₀ hΔ hY hD hYD
  exact ⟨D, ⟨hD, mem_lambdaSet_comm hD.1.1 hBD⟩, hDc⟩

include hint

theorem commuting_of_forall_conjSet_eq' {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀)
    (hXN : ∀ x ∈ X, conjSet (deltaSet R A A₀ B) x = deltaSet R A A₀ B) : Commuting X B := by
  have hR := h.root
  refine Sec3.commuting_of_forall_conjSub_eq hR hX.1.1 hB.1.1.1 (fun x hx => ?_) h.noIsolated
  have hxV : x ∈ levi R A A₀ := le_gen hX hx
  refine eq_of_deltaSet_eq h hA hAne hA₀ hint (conjSub_mem_lambdaStar_of_mem_levi hR hB hxV)
    hB ?_
  rw [← conjSet_deltaSet hR hxV, hXN x hx]

theorem commuting_of_forall_commuting' {B X : Subgroup G} (hB : B ∈ lambdaStar R A A₀)
    (hX : X ∈ leviSet R A A₀) (hXΔ : ∀ Y ∈ deltaSet R A A₀ B, Commuting X Y) :
    Commuting X B := by
  refine commuting_of_forall_conjSet_eq' h hA hAne hA₀ hint hB hX fun x hx => ?_
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

omit hA hAne hA₀ hint in
theorem conjSub_mem_of_mem_stabSet' {B X : Subgroup G} {g : G} (hg : g ∈ levi R A A₀)
    (hgB : g ∈ stabSet (deltaSet R A A₀ B)) (hX : X ∈ leviSet R A A₀)
    (hXΔ : ∀ Y ∈ deltaSet R A A₀ B, Commuting X Y) :
    conjSub X g ∈ leviSet R A A₀ ∧ ∀ Y ∈ deltaSet R A A₀ B, Commuting (conjSub X g) Y := by
  refine ⟨Levi.conjSub_mem_leviSet_of_mem_levi h.root hX hg, fun Y hY => ?_⟩
  have hY' : Y ∈ conjSet (deltaSet R A A₀ B) g := by rw [mem_stabSet.1 hgB]; exact hY
  obtain ⟨Y', hY'Δ, rfl⟩ := hY'
  exact (hXΔ Y' hY'Δ).conjSub g

theorem setOf_forall_commuting_eq' (hmax : IsSigmaMaximal R (centralGroup R A)) {B : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) :
    {X | X ∈ leviSet R A A₀ ∧ ∀ Y ∈ deltaSet R A A₀ B, Commuting X Y} = deltaSet R A A₀ B := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hBR : B ∈ R := hB.1.1.1
  refine Set.Subset.antisymm (fun X₀ ⟨hX₀, hX₀Δ⟩ => ?_) fun X hX =>
    ⟨hX.1, fun Y hY => commuting_of_mem_deltaSet h hA hA₀ hB hX hY⟩
  by_contra hX₀B
  set S := {X | X ∈ leviSet R A A₀ ∧ (∀ Y ∈ deltaSet R A A₀ B, Commuting X Y) ∧
    X ∉ deltaSet R A A₀ B} with hSdef
  obtain ⟨E, ⟨hE, hEΔ, hEB⟩, F, hF, hEF, hFB⟩ : ∃ E ∈ S, ∃ F ∈ leviSet R A A₀,
      Opposite E F ∧ ¬ Commuting F B := by
    by_contra! hall
    have hclosed : ∀ E F, E ∈ S → oppGraph (leviSet R A A₀) E F → F ∈ S := by
      rintro E F ⟨hE, hEΔ, hEB⟩ ⟨-, hF, hEF⟩
      have hFB := hall E ⟨hE, hEΔ, hEB⟩ F hF hEF
      have hEB' := commuting_of_forall_commuting' h hA hAne hA₀ hint hB hE hEΔ
      obtain ⟨y, hy, hyF⟩ := Sec3.exists_mem_sup_conjSub_eq hR hE.1.1 hEF
      have hyV : y ∈ levi R A A₀ := sup_le (le_gen hE) (le_gen hF) hy
      have hyS : y ∈ stabSet (deltaSet R A A₀ B) :=
        sup_le (le_stabSet_deltaSet_of_commuting hR hE hEB')
          (le_stabSet_deltaSet_of_commuting hR hF hFB) hy
      obtain ⟨-, hFΔ⟩ := conjSub_mem_of_mem_stabSet' h hyV hyS hE hEΔ
      rw [hyF] at hFΔ
      refine ⟨hF, hFΔ, fun hFB' => ?_⟩
      exact hEF.not_commuting (hR.ne_bot E hE.1.1) (hEΔ F hFB')
    have hpathS : ∀ Z, Relation.ReflTransGen (oppGraph (leviSet R A A₀)) X₀ Z → Z ∈ S := by
      intro Z hZ
      induction hZ with
      | refl => exact ⟨hX₀, hX₀Δ, hX₀B⟩
      | tail _ hcd ih => exact hclosed _ _ ih hcd
    obtain ⟨Y, hY, hpath⟩ := exists_mem_deltaSet_reflTransGen h hA hAne hA₀ hmax hB hX₀
    exact (hpathS Y hpath).2.2 hY
  have hEB' : Commuting E B := commuting_of_forall_commuting' h hA hAne hA₀ hint hB hE hEΔ
  have hBF : Special R B F :=
    special_of_not_commuting_of_mem_leviSet h hA hB hF fun h' => hFB h'.symm
  have hER : E ∈ R := hE.1.1
  have hFR : F ∈ R := hF.1.1
  obtain ⟨hP, hPB, hPF⟩ := commutator_mem_lambdaStar h hA hAne hA₀ hB hF hBF
  set P := ⁅B, F⁆ with hPdef
  have hPR : P ∈ R := hP.1.1.1
  have hPE : Special R P E := by
    refine special_of_not_commuting_of_mem_leviSet h hA hP hE fun h' => ?_
    exact not_commuting_of_opposite_of_mem_lambdaSet hR hER hEF hPF h'.symm
  obtain ⟨hC, hCP, hCE⟩ := commutator_mem_lambdaStar h hA hAne hA₀ hP hE hPE
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
    rw [(Q_eq_M h hPR).2.1] at hmem
    rcases hmem with h1 | h1
    · exfalso
      have : B = C := by
        rw [← hPx, ← h1, ← conjSub_mul, mul_inv_cancel, conjSub_one]
      rw [← this] at hCE
      exact hEB (⟨hE, mem_lambdaSet_comm hER hCE⟩ : E ∈ deltaSet R A A₀ B)
    · have := conjSub_mem_lambdaSet hR h1 x
      rwa [← conjSub_mul, mul_inv_cancel, conjSub_one, hPx] at this
  obtain ⟨D, hD, hCDB⟩ := exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hC hB
    (mem_lambdaSet_comm hCR hBC)
  have hsCD : Special R C D := special_of_commutator_mem_of_mem_leviSet h hA hC hD
    (hCDB ▸ hBR)
  have hDB : D ∈ lambdaSet R B := by
    have := (mem_lambdaSet_commutator hR hiso hCR hD.1.1 hsCD).2
    rwa [hCDB] at this
  have hED : Commuting E D := hEΔ D ⟨hD, hDB⟩
  have hBle : B ≤ M R E := by
    rw [← hCDB]
    exact commutator_le_of_le_normalizer (QD.le_M hCE) (QD.le_normalizer_M hR hER ⟨hD.1.1, hED⟩)
  have hBE : B ∈ lambdaSet R E := mem_lambdaSet_of_le_M_of_hyp h hER hBR hBle
    fun e => hB.2.2.not_commuting hR (by rw [e]; exact hE.2.2.2)
  exact hEB ⟨hE, mem_lambdaSet_comm hER hBE⟩

theorem setOf_le_gen_deltaSet_eq' (hmax : IsSigmaMaximal R (centralGroup R A)) {B : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) :
    {X | X ∈ leviSet R A A₀ ∧ X ≤ gen (deltaSet R A A₀ B)} = deltaSet R A A₀ B := by
  refine Set.Subset.antisymm (fun X ⟨hX, hXle⟩ => ?_) fun X hX => ⟨hX.1, le_gen hX⟩
  rw [← setOf_forall_commuting_eq' h hA hAne hA₀ hint hmax hB]
  exact ⟨hX, fun Y hY => ((commuting_gen_deltaSet h hA hA₀ hB).mono hXle (le_gen hY))⟩

omit hA hAne hA₀ hint in
theorem commutator_le_gen_deltaSet' {B X Y : Subgroup G} (hX : X ∈ deltaSet R A A₀ B)
    (hY : Y ∈ leviSet R A A₀) (hYB : Commuting Y B) : ⁅X, Y⁆ ≤ gen (deltaSet R A A₀ B) := by
  have hR := h.root
  rw [Subgroup.commutator_le]
  intro x hx y hy
  have hXy : conjSub X y ∈ deltaSet R A A₀ B := by
    rw [← conjSet_deltaSet_eq_of_commuting hR hY hYB hy]
    exact conjSub_mem_conjSet hX y
  rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * (y * x⁻¹ * y⁻¹) by group]
  exact Subgroup.mul_mem _ (le_gen hX hx) (le_gen hXy (conj_mem_conjSub y (X.inv_mem hx)))

omit hint in
theorem exists_mem_deltaSet_not_commuting' {C D : Subgroup G} (hC : C ∈ lambdaStar R A A₀)
    (hD : D ∈ lambdaStar R A A₀) (hCD : C ∈ lambdaSet R D) :
    ∃ X ∈ deltaSet R A A₀ D, ¬ Commuting C X := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hDR : D ∈ R := hD.1.1.1
  obtain ⟨X, hX, hCXD⟩ :=
    exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hC hD hCD
  have hs : Special R C X :=
    special_of_commutator_mem_of_mem_leviSet h hA hC hX (hCXD ▸ hDR)
  have hXD : X ∈ lambdaSet R D := by
    have := (mem_lambdaSet_commutator hR hiso hC.1.1.1 hX.1.1 hs).2
    rwa [hCXD] at this
  exact ⟨X, ⟨hX, hXD⟩, hs.not_commuting hR⟩

theorem eq_of_forall_commuting' (hmax : IsSigmaMaximal R (centralGroup R A)) {B C : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀)
    (hCB : ∀ X ∈ deltaSet R A A₀ C, Commuting X B) : C = B := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hBR : B ∈ R := hB.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  by_contra hne
  by_cases h1 : ∃ E ∈ deltaSet R A A₀ B, ¬ Commuting E C
  ·
    obtain ⟨E, hE, hEC⟩ := h1
    have hER : E ∈ R := hE.1.1.1
    have hsCE : Special R C E :=
      special_of_not_commuting_of_mem_leviSet h hA hC hE.1 fun h' => hEC h'.symm
    obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
    have heV : e ∈ levi R A A₀ := le_gen hE.1 he
    have hCe : conjSub C e ∈ lambdaStar R A A₀ := conjSub_mem_lambdaStar_of_mem_levi hR hC heV
    have hCene : conjSub C e ≠ C := Sec3.conjSub_ne_of_special hR hiso hER hCR hsCE.symm he he1
    obtain ⟨-, hKC, -⟩ := commutator_mem_lambdaStar h hA hAne hA₀ hC hE.1 hsCE
    have hCeC : conjSub C e ∈ lambdaSet R C :=
      (mem_lambdaSet_of_le_sup hR hiso hCR hKC hCR le_sup_left hCe.1.1.1
        ((conjSub_le_commutator_sup (A := C) he).trans (sup_comm _ _).le) hCene.symm).1
    have hsub : ∀ L ∈ deltaSet R A A₀ (conjSub C e), Commuting L C := by
      intro L hL
      rw [← conjSet_deltaSet hR heV] at hL
      obtain ⟨F, hF, rfl⟩ := hL
      dsimp only
      have hFC : Commuting F C := hF.2.1.2.2.symm
      by_cases hFE : Commuting F E
      · rwa [conjSub_of_forall_commute fun f hf => (hFE f hf e he).symm]
      · have hFB := hCB F hF
        have hsFE : Special R F E := by
          have hne' : F ≠ E := fun e' => hFE (e' ▸ hR.commuting_self hF.1.1.1)
          rcases hR.rel _ hF.1.1.1 _ hER hne' with h2 | h2 | h2
          · exact absurd h2 hFE
          · exact absurd hFB (not_commuting_of_opposite_of_mem_lambdaSet hR hF.1.1.1 h2
              (mem_lambdaSet_comm hBR hE.2))
          · exact h2
        have hKΔ := Levi.commutator_mem_leviSet hR hA hA₀ hF.1 hE.1 hsFE
        have hKF : ⁅F, E⁆ ∈ lambdaSet R F :=
          mem_lambdaSet_comm hsFE.1 (mem_lambdaSet_commutator hR hiso hF.1.1.1 hER hsFE).1
        have hKCc := commuting_of_mem_deltaSet_of_mem_lambdaSet h hA hA₀ hC hF hKΔ hKF
        exact (Commuting.sup_left hKCc hFC).mono (conjSub_le_commutator_sup he) le_rfl
    obtain ⟨X, hX, hCX⟩ := exists_mem_deltaSet_not_commuting' h hA hAne hA₀ hC hCe
      (mem_lambdaSet_comm hCR hCeC)
    exact hCX (hsub X hX).symm
  ·
    push Not at h1
    have h2 : ∃ X ∈ deltaSet R A A₀ B, ∃ Y ∈ deltaSet R A A₀ C, ¬ Commuting X Y := by
      by_contra! h3
      apply hne
      refine eq_of_deltaSet_eq h hA hAne hA₀ hint hC hB (Set.Subset.antisymm ?_ ?_)
      · rw [← setOf_forall_commuting_eq' h hA hAne hA₀ hint hmax hB]
        exact fun Y hY => ⟨hY.1, fun X hX => (h3 X hX Y hY).symm⟩
      · rw [← setOf_forall_commuting_eq' h hA hAne hA₀ hint hmax hC]
        exact fun X hX => ⟨hX.1, fun Y hY => h3 X hX Y hY⟩
    obtain ⟨X, hX, Y, hY, hXY⟩ := h2
    have hsXY : Special R X Y := by
      have hne' : X ≠ Y := fun e' => hXY (e' ▸ hR.commuting_self hX.1.1.1)
      rcases hR.rel _ hX.1.1.1 _ hY.1.1.1 hne' with h3 | h3 | h3
      · exact absurd h3 hXY
      · exact absurd (hCB Y hY) (not_commuting_of_opposite_of_mem_lambdaSet hR hY.1.1.1 h3.symm
          (mem_lambdaSet_comm hBR hX.2))
      · exact h3
    have hKΔ := Levi.commutator_mem_leviSet hR hA hA₀ hX.1 hY.1 hsXY
    have hKB : ⁅X, Y⁆ ∈ deltaSet R A A₀ B := by
      rw [← setOf_le_gen_deltaSet_eq' h hA hAne hA₀ hint hmax hB]
      exact ⟨hKΔ, commutator_le_gen_deltaSet' h hX hY.1 (hCB Y hY)⟩
    have hKC : ⁅X, Y⁆ ∈ deltaSet R A A₀ C := by
      rw [← setOf_le_gen_deltaSet_eq' h hA hAne hA₀ hint hmax hC, Subgroup.commutator_comm]
      exact ⟨Subgroup.commutator_comm X Y ▸ hKΔ,
        commutator_le_gen_deltaSet' h hY hX.1 (h1 X hX)⟩
    have hBC : B ∉ lambdaSet R C := by
      intro hBC
      obtain ⟨Z, hZ, hBZ⟩ := exists_mem_deltaSet_not_commuting' h hA hAne hA₀ hB hC hBC
      exact hBZ (hCB Z hZ).symm
    have hBCc : Commuting B C := by
      rcases commuting_or_commutator_eq_of_mem_lambdaSet h hA hB.1 hC.1
        (fun e' => hne e'.symm) with h3 | h3
      · exact h3
      · exfalso
        have hle : A ≤ ⁅X, Y⁆ := by
          rw [← h3.2, ← (Q_eq_M h hKB.1.1.1).2.2.1]
          exact Subgroup.commutator_mono (QD.le_M (mem_lambdaSet_comm hBR hKB.2))
            (QD.le_M (mem_lambdaSet_comm hCR hKC.2))
        exact hKΔ.1.2.1 (QD.eq_of_le_of_mem hR hiso hA hKΔ.1.1 hle).symm
    obtain ⟨D, ⟨hD, hDB⟩, hDC⟩ := hint B hB C hC hBCc
    obtain ⟨X', hX', hX'B⟩ :=
      exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hD hB hDB
    have hsDX' : Special R D X' :=
      special_of_commutator_mem_of_mem_leviSet h hA hD hX' (hX'B ▸ hBR)
    have hX'Bl : X' ∈ lambdaSet R B := by
      have := (mem_lambdaSet_commutator hR hiso hD.1.1.1 hX'.1.1 hsDX').2
      rwa [hX'B] at this
    have hX'C := h1 X' ⟨hX', hX'Bl⟩
    have hle : B ≤ M R C := by
      rw [← hX'B]
      exact commutator_le_of_le_normalizer (QD.le_M hDC)
        (QD.le_normalizer_M hR hCR ⟨hX'.1.1, hX'C.symm⟩)
    exact hBC (mem_lambdaSet_of_le_M_of_hyp h hCR hBR hle fun e' => hne e'.symm)

end General

end CaseOANSL

end CFSG.Timmesfeld.ARS

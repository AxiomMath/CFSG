module

public import CFSG.Timmesfeld.ARS.Sec9Orbits

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open Levi

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec9

section Block

variable (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R) (hAne : sigmaSet R A ≠ lambdaSet R A)
  (hmax : IsSigmaMaximal R (centralGroup R A)) (hA₀ : A₀ ∈ omegaSet R A)
include h hA hAne hmax hA₀

omit hmax in
theorem exists_commuting_mem_lambdaStar {E : Subgroup G} (hE : E ∈ leviSet R A A₀) :
    ∃ X ∈ lambdaStar R A A₀, Commuting E X := by
  have := h.finite
  have hR := h.root
  obtain ⟨B, hB⟩ := CaseD4.lambdaStar_nonempty h hA hA₀
  by_cases hEB : Commuting E B
  · exact ⟨B, hB, hEB⟩
  have hs : Special R B E := by
    have hne : B ≠ E := fun e => hEB (by rw [e]; exact hR.commuting_self hE.1.1)
    rcases hR.rel B hB.1.1.1 E hE.1.1 hne with hc | ho | hs
    · exact absurd hc.symm hEB
    · exact absurd ho.symm (CaseD4.not_opposite_of_mem_leviSet hR hA hB hE)
    · exact hs
  exact ⟨⁅B, E⁆, (exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hE hB hs).1 _ hs.1
    le_sup_right, hs.2.2.symm⟩

omit hAne hmax in
theorem exists_not_commuting {E : Subgroup G} (hE : E ∈ leviSet R A A₀) :
    ∃ D ∈ lambdaStar R A A₀, ¬ Commuting E D := by
  have := h.finite
  by_contra! hall
  have hEM : Commuting E (M R A) := by
    rw [M_eq_gen_lambdaStar h hA hA₀, commuting_iff_le_centralizer]
    exact gen_le fun Y hY => commuting_iff_le_centralizer.1 (hall Y hY)
  have hmem : E ∈ {B | B ∈ R ∧ Commuting B (M R A)} := ⟨hE.1.1, hEM⟩
  rw [(Q_eq_M h hA).2.2.2.1, Set.mem_singleton_iff] at hmem
  exact hE.1.2.1 hmem

omit hAne hmax hA₀ in
theorem special_of_not_commuting {E D : Subgroup G} (hE : E ∈ leviSet R A A₀)
    (hD : D ∈ lambdaStar R A A₀) (hED : ¬ Commuting E D) : Special R E D := by
  have := h.finite
  have hR := h.root
  have hne : E ≠ D := fun e => hED (by rw [← e]; exact hR.commuting_self hE.1.1)
  rcases hR.rel E hE.1.1 D hD.1.1.1 hne with hc | ho | hs
  · exact absurd hc hED
  · exact absurd ho (CaseD4.not_opposite_of_mem_leviSet hR hA hD hE)
  · exact hs

variable {Blk : Set (Subgroup G)} (hBlk : Blk ⊆ leviSet R A A₀)
  (hcl : ∀ Y ∈ Blk, comp R A A₀ Y ⊆ Blk)
include hBlk hcl

omit hmax in
theorem commuting_of_notMem {E Y : Subgroup G} (hE : E ∈ leviSet R A A₀) (hEout : E ∉ Blk)
    (hY : Y ∈ Blk) : Commuting E Y :=
  (commuting_of_notMem_comp h hA hAne hA₀ (hBlk hY) hE fun hEY => hEout (hcl Y hY hEY)).symm

omit hmax in
theorem commute_of_mem_gen {E : Subgroup G} (hE : E ∈ leviSet R A A₀) (hEout : E ∉ Blk)
    {e y : G} (he : e ∈ E) (hy : y ∈ gen Blk) : Commute e y :=
  (commuting_gen_gen (S := {E}) (T := Blk) fun _ hX _ hY => by
    rw [Set.mem_singleton_iff] at hX
    subst hX
    exact commuting_of_notMem h hA hAne hA₀ hBlk hcl hE hEout hY) e
    (le_gen (Set.mem_singleton E) he) y hy

omit hmax in
theorem commuting_of_mem_orbit {E X Z : Subgroup G} (hE : E ∈ leviSet R A A₀) (hEout : E ∉ Blk)
    (hEX : Commuting E X) (hZ : Z ∈ orbit Blk X) : Commuting E Z := by
  obtain ⟨y, hy, rfl⟩ := hZ
  have h1 := hEX.conjSub y
  rwa [conjSub_of_forall_commute fun e he =>
    (commute_of_mem_gen h hA hAne hA₀ hBlk hcl hE hEout he hy).symm] at h1

omit hmax in
theorem commuting_of_normalizes {E X : Subgroup G} (hE : E ∈ leviSet R A A₀) (hEout : E ∉ Blk)
    (hX : X ∈ lambdaStar R A A₀) (hnorm : ∀ e ∈ E, conjSub X e ∈ orbit Blk X) :
    Commuting E X := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  by_contra hEX
  have hs : Special R E X := special_of_not_commuting h hA hE hX hEX
  obtain ⟨-, D, hD, hED, hXD⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hE hX hs.symm
  have hDout : D ∉ Blk := fun hDB =>
    hEout (hcl D hDB (Sec3.reflTransGen_oppGraph_symm (Relation.ReflTransGen.single
      ⟨hE, hD, hED⟩)))
  obtain ⟨e, he, he1⟩ := h.root.exists_ne_one hE.1.1
  obtain ⟨y, hy, hXy⟩ := hnorm e he
  have hcen : ∀ d ∈ D, ∀ n ∈ conjSub X e, Commute d n := by
    rw [← hXy]
    rintro d hd _ ⟨x, hx, rfl⟩
    have hdy : Commute d y := commute_of_mem_gen h hA hAne hA₀ hBlk hcl hD hDout hd hy
    have hdx : Commute d x := hXD.1.2.2 d hd x hx
    change Commute d (y * x * y⁻¹)
    exact (hdy.mul_right hdx).mul_right hdy.inv_right
  have hle : conjSub X e ≤ X := by
    intro n hn
    refine Sec3.mem_of_forall_commute_of_mem_sup hR hiso hD.1.1 hE.1.1 hED.symm hXD ⟨hX.1.1.1, hs⟩
      ?_ fun d hd => hcen d hd n hn
    have := conjSub_le_commutator_sup (A := X) he hn
    rwa [sup_comm, Subgroup.commutator_comm X E] at this
  have heq : conjSub X e = X :=
    Subgroup.eq_of_le_of_card_ge hle (by rw [conjSub, Subgroup.card_map_of_injective
      (MulAut.conj e).injective])
  exact Sec3.conjSub_ne_of_special hR hiso hE.1.1 hX.1.1.1 hs he he1 heq

omit hAne hmax hcl in
theorem orbit_eq_of_commuting
    (h3 : ∀ B ∈ lambdaStar R A A₀, ∀ X ∈ lambdaStar R A A₀,
      ∃ Y ∈ orbit Blk X, Y ∈ lambdaSet R B)
    {E : Subgroup G} (hE : E ∈ leviSet R A A₀)
    (hcol : ∀ Z ∈ lambdaStar R A A₀, Commuting E Z → Z ∈ lambdaSet R E) {X₁ X₂ : Subgroup G}
    (hX₁ : X₁ ∈ lambdaStar R A A₀) (hX₂ : X₂ ∈ lambdaStar R A A₀)
    (h1 : ∀ Z ∈ orbit Blk X₁, Commuting E Z) (h2 : ∀ Z ∈ orbit Blk X₂, Commuting E Z) :
    orbit Blk X₁ = orbit Blk X₂ := by
  have := h.finite
  have hR := h.root
  obtain ⟨D, hD, hED⟩ := exists_not_commuting h hA hA₀ hE
  have hs : Special R E D := special_of_not_commuting h hA hE hD hED
  have key : ∀ {X : Subgroup G}, X ∈ lambdaStar R A A₀ → (∀ Z ∈ orbit Blk X, Commuting E Z) →
      ∃ F ∈ orbit Blk X, ⁅E, D⁆ = F := by
    intro X hX hXc
    obtain ⟨F, hFO, hFD⟩ := h3 D hD X hX
    have hFst : F ∈ lambdaStar R A A₀ := orbit_subset_lambdaStar hR hBlk hX hFO
    have hFE : F ∈ lambdaSet R E := hcol F hFst (hXc F hFO)
    have hle : ⁅E, D⁆ ≤ F := by
      rw [← (Q_eq_M h hFst.1.1.1).2.2.1]
      exact Subgroup.commutator_mono (QD.le_M (mem_lambdaSet_comm hE.1.1 hFE))
        (QD.le_M (mem_lambdaSet_comm hD.1.1.1 hFD))
    exact ⟨F, hFO, Subgroup.eq_of_le_of_card_ge hle (hR.card_eq hs.1 hFst.1.1.1).ge⟩
  obtain ⟨F, hFO, hF⟩ := key hX₁ h1
  obtain ⟨C, hCO, hC⟩ := key hX₂ h2
  exact orbit_eq_of_mem_of_mem hFO (hF.symm.trans hC ▸ hCO)

theorem false_of_two_outside
    (h3 : ∀ B ∈ lambdaStar R A A₀, ∀ X ∈ lambdaStar R A A₀,
      ∃ Y ∈ orbit Blk X, Y ∈ lambdaSet R B)
    {Δ₂ Δ₃ : Set (Subgroup G)} (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hΔ₃ : Δ₃ ∈ leviComps R A A₀)
    (h23 : Δ₂ ≠ Δ₃) (h2out : ∀ Y ∈ Δ₂, Y ∉ Blk) (h3out : ∀ Y ∈ Δ₃, Y ∉ Blk)
    (hcol : ∀ E ∈ Δ₂, ∀ Z ∈ lambdaStar R A A₀, Commuting E Z → Z ∈ lambdaSet R E) : False := by
  have := h.finite
  have hR := h.root
  obtain ⟨E₀, hE₀, rfl⟩ := hΔ₂
  set E := E₀
  have hEΔ : E ∈ comp R A A₀ E₀ := self_mem_comp A A₀ E₀
  obtain ⟨X, hX, hEX⟩ := exists_commuting_mem_lambdaStar h hA hAne hA₀ hE₀
  have hcen : ∀ {E' X' : Subgroup G}, E' ∈ leviSet R A A₀ → E' ∉ Blk → Commuting E' X' →
      ∀ Z ∈ orbit Blk X', Commuting E' Z := by
    rintro E' X' hE' hE'out hE'X' _ ⟨y, hy, rfl⟩
    have h1 := hE'X'.conjSub y
    rwa [conjSub_of_forall_commute fun e he =>
      (commute_of_mem_gen h hA hAne hA₀ hBlk hcl hE' hE'out he hy).symm] at h1
  have hO := hcen hE₀ (h2out E hEΔ) hEX
  refine not_forall_commuting h hA hAne hA₀ hmax hΔ₃ hX fun Y hY => ?_
  have hYl := mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₃ hY
  have hYE : Commuting Y E :=
    commuting_of_ne h hA hAne hA₀ hΔ₃ ⟨E₀, hE₀, rfl⟩ (Ne.symm h23) hY hEΔ
  refine commuting_of_normalizes h hA hAne hA₀ hBlk hcl hYl (h3out Y hY) hX fun y hy => ?_
  have hyB : ∀ g ∈ gen Blk, Commute y g := fun g hg =>
    commute_of_mem_gen h hA hAne hA₀ hBlk hcl hYl (h3out Y hY) hy hg
  have hXy : conjSub X y ∈ lambdaStar R A A₀ :=
    conjSub_mem_lambdaStar_of_mem_levi hR hX (le_gen hYl hy)
  have hO' : ∀ Z ∈ orbit Blk (conjSub X y), Commuting E Z := by
    rintro _ ⟨g, hg, rfl⟩
    have h1 := (hO (conjSub X g) ⟨g, hg, rfl⟩).conjSub y
    rw [conjSub_of_forall_commute fun e he => (hYE y hy e he)] at h1
    change Commuting E (conjSub (conjSub X y) g)
    rw [← conjSub_mul, ← (hyB g hg).eq, conjSub_mul]
    exact h1
  have heq := orbit_eq_of_commuting h hA hA₀ hBlk h3 hE₀
    (hcol E hEΔ) hXy hX hO' hO
  rw [← heq]
  exact mem_orbit_self Blk (conjSub X y)

end Block

end Sec9

end CFSG.Timmesfeld.ARS

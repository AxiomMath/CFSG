module

public import CFSG.Timmesfeld.ARS.CaseOAFrame

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace CaseOA

theorem conjSub_mem_lambdaStar_conj (hR : IsRootClass R) {B D X : Subgroup G}
    (hX : X ∈ lambdaStar R B D) (g : G) :
    conjSub X g ∈ lambdaStar R (conjSub B g) (conjSub D g) :=
  ⟨conjSub_mem_lambdaSet hR hX.1 g, hR.conjSub_mem hX.2.1 g, Sec3.special_conjSub hR hX.2.2 g⟩

theorem exists_conjSub_eq_of_mem_omegaSet (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) {B D : Subgroup G}
    (hB : B ∈ R) (hD : D ∈ omegaSet R B) : ∃ g : G, conjSub A g = B ∧ conjSub A₀ g = D := by
  have := h.finite
  have hR := h.root
  obtain ⟨g, hg⟩ := hR.exists_conjSub_eq hA hB
  have hA₀g : conjSub A₀ g ∈ omegaSet R B :=
    ⟨hR.conjSub_mem hA₀.1 g, hg ▸ Opposite.conj hA₀.2 g⟩
  obtain ⟨m, hm, hmD⟩ := exists_mem_M_conjSub_eq_of_mem_omegaSet h hB
    (sigmaSet_ne_lambdaSet_of_mem hR hA hB hAne) hA₀g hD
  have hmB : conjSub B m = B := conjSub_eq_self_iff.2 ((isPGroup_M hR hB).2.1 hm)
  exact ⟨m * g, by rw [conjSub_mul, hg, hmB], by rw [conjSub_mul, hmD]⟩

theorem exists_special_commuting (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) {Δ₁ Δ₂ : Set (Subgroup G)} (hΔ₁ : Δ₁ ∈ leviComps R A A₀)
    (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂) {T C : Subgroup G}
    (hT : T ∈ lambdaStar R A A₀) (hC : C ∈ leviSet R A A₀) :
    ∃ Y ∈ leviSet R A A₀, Special R T Y ∧ Commuting C Y := by
  have hCc : C ∈ Levi.comp R A A₀ C := Sec9.self_mem_comp A A₀ C
  have hΔC : Levi.comp R A A₀ C ∈ leviComps R A A₀ := Sec9.comp_mem_leviComps hC
  obtain ⟨Δ, hΔ, hne'⟩ : ∃ Δ ∈ leviComps R A A₀, Levi.comp R A A₀ C ≠ Δ := by
    by_cases h1 : Levi.comp R A A₀ C = Δ₁
    · exact ⟨Δ₂, hΔ₂, h1 ▸ hne⟩
    · exact ⟨Δ₁, hΔ₁, h1⟩
  obtain ⟨Y, hY, hYT⟩ : ∃ Y ∈ Δ, ¬ Commuting Y T := by
    by_contra hcon
    push Not at hcon
    exact Sec9.not_forall_commuting h hA hAne hA₀ hmax hΔ hT hcon
  have hYl := Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ hY
  exact ⟨Y, hYl, special_of_not_commuting_of_mem_leviSet h hA hT hYl fun hc => hYT hc.symm,
    Sec9.commuting_of_ne h hA hAne hA₀ hΔC hΔ hne' hCc hY⟩

theorem lambdaStar_inter_nonempty (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) {Δ₁ Δ₂ : Set (Subgroup G)} (hΔ₁ : Δ₁ ∈ leviComps R A A₀)
    (hΔ₂ : Δ₂ ∈ leviComps R A A₀) (hne : Δ₁ ≠ Δ₂) {B C : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀) (hBC : Commuting B C) :
    (lambdaStar R A A₀ ∩ lambdaSet R B ∩ lambdaSet R C).Nonempty := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hBR : B ∈ R := hB.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  by_cases he : B = C
  · subst he
    obtain ⟨X, hX, hBX⟩ := exists_mem_leviSet_special h hA hAne hA₀ hB
    obtain ⟨h1, h2, -⟩ := commutator_mem_lambdaStar h hA hAne hA₀ hB hX hBX
    exact ⟨_, ⟨h1, h2⟩, h2⟩
  by_cases hCB : C ∈ lambdaSet R B
  · obtain ⟨X, hX, hBXC⟩ := exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hB hC
      (mem_lambdaSet_comm hBR hCB)
    have hs : Special R B X :=
      special_of_commutator_mem_of_mem_leviSet h hA hB hX (hBXC ▸ hCR)
    obtain ⟨hpts, -⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hX hB hs
    obtain ⟨P, hPR, hPle, hPB, hPC⟩ := exists_mem_le_sup_ne_ne hR hiso hBR hCB B C
    refine ⟨P, ⟨hpts P hPR (by rw [hBXC]; exact hPle), ?_⟩, ?_⟩
    · exact (mem_lambdaSet_of_le_sup hR hiso hBR hCB hBR le_sup_left hPR hPle hPB.symm).1
    · exact (mem_lambdaSet_of_le_sup hR hiso hBR hCB hCR le_sup_right hPR hPle hPC.symm).1
  have hBne : sigmaSet R B ≠ lambdaSet R B := sigmaSet_ne_lambdaSet_of_mem hR hA hBR hAne
  obtain ⟨D₀, hD₀R, hBD₀⟩ := hiso B hBR
  obtain ⟨m, hm, hCm⟩ := exists_mem_M_conjSub_mem_leviSet h hBR hBne ⟨hD₀R, hBD₀⟩
    ⟨hCR, fun e => he e.symm, hBC⟩ hCB
  have hmB : conjSub B m⁻¹ = B :=
    conjSub_eq_self_iff.2 (Subgroup.inv_mem _ ((isPGroup_M hR hBR).2.1 hm))
  set D := conjSub D₀ m⁻¹ with hDdef
  have hD : D ∈ omegaSet R B := ⟨hR.conjSub_mem hD₀R _, by
    have := Opposite.conj hBD₀ m⁻¹
    rwa [hmB] at this⟩
  have hDR : D ∈ R := hD.1
  have hCΔ' : C ∈ leviSet R B D := by
    have := conjSub_mem_conjSet hCm m⁻¹
    rwa [Plane.conjSub_conjSub_inv, ← leviSet_conjSub hR, hmB] at this
  have hAB : A ∈ lambdaSet R B := mem_lambdaSet_comm hA hB.1
  have hAs : A ∈ lambdaStar R B D := by
    refine ⟨hAB, hA, ?_⟩
    have hne : D ≠ A := fun e => not_commuting_of_opposite_of_mem_lambdaSet hR hDR hD.2.symm hAB
      (by rw [e]; exact hR.commuting_self hA)
    rcases hR.rel _ hDR _ hA hne with h1 | h1 | h1
    · exact absurd h1 (not_commuting_of_opposite_of_mem_lambdaSet hR hDR hD.2.symm hAB)
    · exact absurd hCΔ'.2.2.2 (not_commuting_of_opposite_of_mem_lambdaSet hR hDR h1 hC.1)
    · exact h1
  obtain ⟨g, hgB, hgD⟩ := exists_conjSub_eq_of_mem_omegaSet h hA hAne hA₀ hBR hD
  have hAs' : conjSub A g⁻¹ ∈ lambdaStar R A A₀ := by
    have := conjSub_mem_lambdaStar_conj hR hAs g⁻¹
    rwa [← hgB, ← hgD, Plane.conjSub_conjSub_inv, Plane.conjSub_conjSub_inv] at this
  have hCl' : conjSub C g⁻¹ ∈ leviSet R A A₀ := by
    have := conjSub_mem_conjSet hCΔ' g⁻¹
    rwa [← leviSet_conjSub hR, ← hgB, ← hgD, Plane.conjSub_conjSub_inv,
      Plane.conjSub_conjSub_inv] at this
  obtain ⟨Y', hY', hsY', hcY'⟩ :=
    exists_special_commuting h hA hAne hmax hA₀ hΔ₁ hΔ₂ hne hAs' hCl'
  set Y := conjSub Y' g with hYdef
  have hYR : Y ∈ R := hR.conjSub_mem hY'.1.1 g
  have hYB : Commuting B Y := by
    have := hY'.1.2.2.conjSub g
    rwa [hgB] at this
  have hsAY : Special R A Y := by
    have := Sec3.special_conjSub hR hsY' g
    rwa [Plane.conjSub_inv_conjSub] at this
  have hCY : Commuting C Y := by
    have := hcY'.conjSub g
    rwa [Plane.conjSub_inv_conjSub] at this
  obtain ⟨y, hy, hy1⟩ := hR.exists_ne_one hYR
  have hAy : conjSub A y ≠ A := Sec3.conjSub_ne_of_special hR hiso hYR hA hsAY.symm hy hy1
  have hAYA : ⁅A, Y⁆ ∈ lambdaSet R A :=
    mem_lambdaSet_comm hsAY.1 (mem_lambdaSet_commutator hR hiso hA hYR hsAY).1
  have hAyΛ : conjSub A y ∈ lambdaSet R A :=
    (mem_lambdaSet_of_le_sup hR hiso hA hAYA hA le_sup_left (hR.conjSub_mem hA y)
      ((conjSub_le_commutator_sup (A := A) hy).trans (sup_comm _ _).le) (Ne.symm hAy)).1
  have hyB : conjSub B y = B := conjSub_of_forall_commute fun b hb => (hYB b hb y hy).symm
  have hyC : conjSub C y = C := conjSub_of_forall_commute fun c hc => (hCY c hc y hy).symm
  set A' := conjSub A y with hA'def
  have hA'R : A' ∈ R := hR.conjSub_mem hA y
  have hA'B : A' ∈ lambdaSet R B := by
    have := conjSub_mem_lambdaSet hR hAB y
    rwa [hyB] at this
  have hCA' : C ∈ lambdaSet R A' := by
    have := conjSub_mem_lambdaSet hR hC.1 y
    rwa [hyC] at this
  obtain ⟨P, ⟨hPR, hPle, hPψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hAyΛ
  have hPA : P ≠ A := by
    rintro rfl
    exact Special.not_opposite hR hA₀.1 hPψ.2 hA₀.2.symm
  have hPΛ : P ∈ lambdaSet R A :=
    (mem_lambdaSet_of_le_sup hR hiso hA hAyΛ hA le_sup_left hPR hPle hPA.symm).1
  have hMB : A ⊔ A' ≤ M R B := sup_le (QD.le_M hAB) (QD.le_M hA'B)
  have hMC : A ⊔ A' ≤ M R C :=
    sup_le (QD.le_M (mem_lambdaSet_comm hA hC.1)) (QD.le_M (mem_lambdaSet_comm hA'R hCA'))
  have hPB : P ≠ B := by
    rintro rfl
    exact hCB (mem_lambdaSet_comm hCR (mem_lambdaSet_of_le_M_of_hyp h hCR hPR
      (hPle.trans hMC) he))
  have hPC : P ≠ C := by
    rintro rfl
    exact hCB (mem_lambdaSet_of_le_M_of_hyp h hBR hPR (hPle.trans hMB) (Ne.symm he))
  exact ⟨P, ⟨⟨hPΛ, hPψ⟩, mem_lambdaSet_of_le_M_of_hyp h hBR hPR (hPle.trans hMB) hPB⟩,
    mem_lambdaSet_of_le_M_of_hyp h hCR hPR (hPle.trans hMC) hPC⟩

theorem eq_commutator_of_mem_lambdaSet (h : Hyp G R) {A A₀ : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hmax : IsSigmaMaximal R (centralGroup R A))
    (hA₀ : A₀ ∈ omegaSet R A) {Δ₂ : Set (Subgroup G)} (hΔ₂ : Δ₂ ∈ leviComps R A A₀)
    (hS₂ : IsSL2Comp Δ₂) {Q₂ X P : Subgroup G} (hQ₂ : Q₂ ∈ Δ₂) (hX : X ∈ lambdaStar R A A₀)
    (hP : P ∈ lambdaStar R A A₀) (hXQ : Commuting Q₂ X) (hPQ : ¬ Commuting P Q₂)
    (hXP : X ∈ lambdaSet R P) : X = ⁅P, Q₂⁆ := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hXR : X ∈ R := hX.1.1.1
  have hPR : P ∈ R := hP.1.1.1
  have hl := fun {Y : Subgroup G} (hY : Y ∈ Δ₂) =>
    Sec9.mem_leviSet_of_mem_leviComps h hA hAne hA₀ hΔ₂ hY
  have hΔ₂R : Δ₂ ⊆ R := fun Y hY => (hl hY).1.1
  obtain ⟨Z, hZ, hPZX⟩ := exists_commutator_eq_of_mem_lambdaStar h hA hAne hA₀ hP hX
    (mem_lambdaSet_comm hPR hXP)
  have hsPZ : Special R P Z := special_of_commutator_mem_of_mem_leviSet h hA hP hZ (hPZX ▸ hXR)
  by_cases hZΔ : Z ∈ Δ₂
  · by_cases hZQ : Z = Q₂
    · rw [← hZQ]
      exact hPZX.symm
    · exfalso
      obtain ⟨-, hgen⟩ := hS₂.opposite_of_ne hR hΔ₂R hZΔ hQ₂ hZQ
      have hXZ : Commuting X Z := hPZX ▸ hsPZ.2.2
      have hXV : Commuting X (gen Δ₂) := by
        rw [← hgen]
        exact hXZ.sup_right hXQ.symm
      exact Sec9.not_forall_commuting h hA hAne hA₀ hmax hΔ₂ hX fun Y hY =>
        (hXV.mono le_rfl (le_gen hY)).symm
  · exfalso
    have hsPQ : Special R P Q₂ := special_of_not_commuting_of_mem_leviSet h hA hP (hl hQ₂) hPQ
    obtain ⟨-, D', hD', hQD', hPD'⟩ :=
      exists_opposite_of_mem_lambdaStar h hA hAne hA₀ (hl hQ₂) hP hsPQ
    have hD'Δ : D' ∈ Δ₂ := Sec9.mem_of_opposite h hA hAne hA₀ hΔ₂ hQ₂ hD' hQD'
    have hgen : gen Δ₂ = D' ⊔ Q₂ :=
      (hS₂.opposite_of_ne hR hΔ₂R hD'Δ hQ₂ hQD'.1.symm).2.symm
    obtain ⟨-, hsDX⟩ := natural_of_sl2 h hA hAne hmax hA₀ hΔ₂ hD'Δ hQ₂ hQD'.symm hgen hX hXQ
    have hZD' : Commuting Z D' := by
      obtain ⟨Δ, hΔ, hZΔ'⟩ := Sec9.mem_comp_self hZ
      exact Sec9.commuting_of_ne h hA hAne hA₀ hΔ hΔ₂ (fun e => hZΔ (e ▸ hZΔ')) hZΔ' hD'Δ
    obtain ⟨d, hd, hd1⟩ := hR.exists_ne_one hD'.1.1
    have hPd : conjSub P d = P := conjSub_of_forall_commute fun p hp => hPD'.1.2.2 d hd p hp
    have hZd : conjSub Z d = Z := conjSub_of_forall_commute fun z hz => (hZD' z hz d hd).symm
    have hXd : conjSub X d = X := by
      have e : conjSub ⁅P, Z⁆ d = ⁅conjSub P d, conjSub Z d⁆ := Subgroup.map_commutator _ _ _
      rw [← hPZX, e, hPd, hZd]
    exact Sec3.conjSub_ne_of_special hR hiso hD'.1.1 hXR hsDX hd hd1 hXd

end CaseOA

end CFSG.Timmesfeld.ARS

module

public import CFSG.Timmesfeld.ARS.Sec13Star
public import CFSG.Timmesfeld.ARS.Sec13Connected

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

theorem deltaSet_inter_nonempty_of_notMem_lambdaSet (h : Hyp G R) {A A₀ : Subgroup G}
    (hA : A ∈ R) (h8 : Sec8 R A) (hA₀ : A₀ ∈ omegaSet R A) {D C : Subgroup G}
    (hD : D ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀) (hDCc : Commuting D C)
    (hDC : D ≠ C) (hCD : C ∉ lambdaSet R D) :
    (deltaSet R A A₀ D ∩ deltaSet R A A₀ C).Nonempty := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hDR : D ∈ R := hD.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  rw [Set.nonempty_iff_ne_empty]
  intro hemp
  have hAD : A ∈ lambdaSet R D := mem_lambdaSet_comm hA hD.1
  have hAC : A ∈ lambdaSet R C := mem_lambdaSet_comm hA hC.1
  have hDCl : D ∉ lambdaSet R C := fun h => hCD (mem_lambdaSet_comm hCR h)
  obtain ⟨E, hED, hAE⟩ := QD.exists_mem_lambdaSet_not_commuting hR hiso hDR hAD
  have hER : E ∈ R := hED.1.1
  have hAEne : A ≠ E := fun e => hAE (e ▸ hR.commuting_self hA)
  obtain ⟨hsAE, hAED⟩ :=
    (commuting_or_commutator_eq_of_mem_lambdaSet h hDR hAD hED hAEne).resolve_left hAE
  have hEC : ¬ Commuting E C := by
    intro hc
    have hle : D ≤ M R C := by
      rw [← hAED]
      exact commutator_le_of_le_normalizer (QD.le_M hAC)
        (QD.le_normalizer_M hR hCR ⟨hER, hc.symm⟩)
    exact hDCl (mem_lambdaSet_of_le_M_of_hyp h hCR hDR hle hDC)
  have hsEC : Special R E C := by
    have hne : E ≠ C := fun e => hEC (e ▸ hR.commuting_self hER)
    rcases hR.rel _ hER _ hCR hne with h1 | h1 | h1
    · exact absurd h1 hEC
    · exact absurd hDCc.symm (not_commuting_of_opposite_of_mem_lambdaSet hR hCR h1.symm
        (mem_lambdaSet_comm hDR hED))
    · exact h1
  set K := ⁅E, C⁆ with hKdef
  have hKR : K ∈ R := hsEC.1
  obtain ⟨hEK, hCK⟩ := mem_lambdaSet_commutator hR hiso hER hCR hsEC
  have hKC : K ∈ lambdaSet R C := mem_lambdaSet_comm hKR hCK
  have hKE : K ∈ lambdaSet R E := mem_lambdaSet_comm hKR hEK
  have hKDne : K ≠ D := fun e => hDCl (e ▸ hKC)
  have hKD : K ∈ lambdaSet R D := mem_lambdaSet_of_le_M_of_hyp h hDR hKR
    (commutator_le_of_le_normalizer (QD.le_M hED) (QD.le_normalizer_M hR hDR ⟨hCR, hDCc⟩))
    hKDne
  have hKA : K ≠ A := fun e => hAE (by rw [← e]; exact hKE.1.2.2.symm)
  have hKΛ : K ∈ lambdaSet R A :=
    (eq_or_mem_lambdaSet_of_inter_eq_empty h hA h8 hA₀ hD hC hDC hemp hKD hKC).resolve_left hKA
  obtain ⟨e, he, he1⟩ := hR.exists_ne_one hER
  have hee : e * e = 1 := hR.mul_self E hER e he
  have hinv : ∀ X : Subgroup G, conjSub (conjSub X e) e = X := fun X => by
    rw [← conjSub_mul, hee, conjSub_one]
  have hDe : conjSub D e = D := conjSub_of_forall_commute fun d hd => (hED.1.2.2 d hd e he).symm
  have hCeR : conjSub C e ∈ R := hR.conjSub_mem hCR e
  have hCele : conjSub C e ≤ C ⊔ K :=
    (conjSub_le_commutator_sup (A := C) he).trans (by rw [Subgroup.commutator_comm C E, sup_comm])
  have hCeM : conjSub C e ≤ M R A := hCele.trans (sup_le (QD.le_M hC.1) (QD.le_M hKΛ))
  have hAele : conjSub A e ≤ A ⊔ D :=
    (conjSub_le_commutator_sup (A := A) he).trans (by rw [hAED, sup_comm])
  have hCeA : conjSub C e ≠ A := by
    intro hCe
    have hCle : C ≤ A ⊔ D := by
      have := hinv C
      rw [hCe] at this
      exact this ▸ hAele
    exact hCD (mem_lambdaSet_of_le_sup hR hiso hA hD.1 hDR le_sup_right hCR hCle
      hDC).1
  have hCeΛ : conjSub C e ∈ lambdaSet R A :=
    mem_lambdaSet_of_le_M_of_hyp h hA hCeR hCeM hCeA
  have hCeΛe : conjSub C e ∈ lambdaSet R (conjSub A e) := conjSub_mem_lambdaSet hR hC.1 e
  have hAeA : conjSub A e ≠ A := Sec3.conjSub_ne_of_special hR hiso hER hA hsAE.symm he he1
  have hsup := (mem_lambdaSet_of_le_sup hR hiso hA hD.1 hA le_sup_left (hR.conjSub_mem hA e)
    hAele hAeA.symm).2
  have hDle : D ≤ M R (conjSub C e) := by
    calc D ≤ A ⊔ D := le_sup_right
      _ = A ⊔ conjSub A e := hsup.symm
      _ ≤ M R (conjSub C e) := sup_le (QD.le_M (mem_lambdaSet_comm hA hCeΛ))
          (QD.le_M (mem_lambdaSet_comm (hR.conjSub_mem hA e) hCeΛe))
  have hDCe : D ≠ conjSub C e := by
    intro h1
    have := hinv C
    rw [← h1, hDe] at this
    exact hDC this
  have hDΛ := mem_lambdaSet_of_le_M_of_hyp h hCeR hDR hDle hDCe
  have := conjSub_mem_lambdaSet hR hDΛ e
  rw [hDe, hinv] at this
  exact hDCl this

namespace Sec13

variable {A A₀ : Subgroup G} (hS : Sec13 R A A₀)
include hS

theorem deltaSet_inter_nonempty_of_notMem_lambdaSet {D C : Subgroup G}
    (hD : D ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀) (hDCc : Commuting D C)
    (hDC : D ≠ C) (hCD : C ∉ lambdaSet R D) :
    (deltaSet R A A₀ D ∩ deltaSet R A A₀ C).Nonempty :=
  _root_.CFSG.Timmesfeld.ARS.deltaSet_inter_nonempty_of_notMem_lambdaSet hS.hyp hS.mem hS.sec8
    hS.opp hD hC hDCc hDC hCD

theorem deltaSet_inter_nonempty {D C : Subgroup G} (hD : D ∈ lambdaStar R A A₀)
    (hC : C ∈ lambdaStar R A A₀) (hDC : Commuting D C) :
    (deltaSet R A A₀ D ∩ deltaSet R A A₀ C).Nonempty := by
  by_cases he : D = C
  · subst he
    rw [Set.inter_self]
    exact deltaSet_nonempty hS.hyp hS.mem hS.sec8.2 hS.opp hD
  by_cases hCD : C ∈ lambdaSet R D
  · exact hS.deltaSet_inter_nonempty_of_mem_lambdaSet hD hC hCD
  · exact hS.deltaSet_inter_nonempty_of_notMem_lambdaSet hD hC hDC he hCD

theorem lambdaStar_inter_nonempty (hcl : LeviClosed R A A₀) {B C : Subgroup G}
    (hB : B ∈ lambdaStar R A A₀) (hC : C ∈ lambdaStar R A A₀) (hBC : Commuting B C) :
    (lambdaStar R A A₀ ∩ lambdaSet R B ∩ lambdaSet R C).Nonempty := by
  have := hS.hyp.finite
  have hR := hS.hyp.root
  have hiso := hS.hyp.noIsolated
  have hA := hS.mem
  have hA₀ := hS.opp
  have hBR : B ∈ R := hB.1.1.1
  have hCR : C ∈ R := hC.1.1.1
  by_cases he : B = C
  · subst he
    obtain ⟨X, hX, hBX⟩ := exists_mem_leviSet_special hS.hyp hA hS.sec8.2 hA₀ hB
    obtain ⟨h1, h2, -⟩ := commutator_mem_lambdaStar hS.hyp hA hS.sec8.2 hA₀ hB hX hBX
    exact ⟨_, ⟨h1, h2⟩, h2⟩
  by_cases hCB : C ∈ lambdaSet R B
  · obtain ⟨P, hPR, hPle, hPB, hPC⟩ := exists_mem_le_sup_ne_ne hR hiso hBR hCB B C
    exact ⟨P, ⟨hS.mem_lambdaStar_of_le_sup hB hC hCB hPR hPle,
      (mem_lambdaSet_of_le_sup hR hiso hBR hCB hBR le_sup_left hPR hPle hPB.symm).1⟩,
      (mem_lambdaSet_of_le_sup hR hiso hBR hCB hCR le_sup_right hPR hPle hPC.symm).1⟩
  have hBne : sigmaSet R B ≠ lambdaSet R B := (Sec8.of_mem hR hA hBR hS.sec8).2
  obtain ⟨D₀, hD₀R, hBD₀⟩ := hiso B hBR
  obtain ⟨m, hm, hCm⟩ := exists_mem_M_conjSub_mem_leviSet hS.hyp hBR hBne ⟨hD₀R, hBD₀⟩
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
  have hCΔ : C ∈ deltaSet R B D A := ⟨hCΔ', hC.1⟩
  have hS' := hS.of_mem_omegaSet hBR hD
  have hcl' := hcl.of_mem_omegaSet hS hBR hD
  obtain ⟨Y, hY, y, hy, hAy, Q, hQ1, hQ2⟩ := hS'.exists_conjSub_ne_inter_nonempty hAs
  have hyV : y ∈ levi R B D := le_gen hY hy
  rw [conjSet_deltaSet hR hyV] at hQ2
  obtain ⟨g, hg, hQg⟩ := hS'.exists_mem_gen_conjSub_eq hcl' hAs hQ1 hCΔ
  have hgV : g ∈ levi R B D := centGen_le_levi A hg
  have hgA : conjSub A g = A := by
    have hle : centGen R B D A ≤ Subgroup.centralizer (A : Set G) :=
      gen_le fun X hX => commuting_iff_le_centralizer.1 hX.2.symm
    exact conjSub_of_forall_commute fun a ha => (Subgroup.mem_centralizer_iff.1 (hle hg) a ha).symm
  set A' := conjSub (conjSub A y) g with hA'def
  have hA'R : A' ∈ R := hR.conjSub_mem (hR.conjSub_mem hA y) g
  have hCA' : C ∈ lambdaSet R A' := by
    have := conjSub_mem_conjSet hQ2 g
    rw [conjSet_deltaSet hR hgV, hQg] at this
    exact this.2
  have hA'A : A' ≠ A := by
    intro h1
    apply hAy
    have h2 : conjSub (conjSub A y) g = conjSub A g := h1.trans hgA.symm
    have h3 := congrArg (fun X => conjSub X g⁻¹) h2
    simpa only [Plane.conjSub_conjSub_inv] using h3
  have hsAY : Special R A Y := special_of_not_commuting_of_mem_leviSet hS'.hyp hBR hAs hY
    fun hc => hAy (conjSub_of_forall_commute fun a ha => (hc a ha y hy).symm)
  obtain ⟨-, hAYA, -⟩ := commutator_mem_lambdaStar hS'.hyp hBR hS'.sec8.2 hD hAs hY hsAY
  have hAyΛ : conjSub A y ∈ lambdaSet R A :=
    (mem_lambdaSet_of_le_sup hR hiso hA hAYA hA le_sup_left (hR.conjSub_mem hA y)
      ((conjSub_le_commutator_sup (A := A) hy).trans (sup_comm _ _).le) (Ne.symm hAy)).1
  have hA'Λ : A' ∈ lambdaSet R A := by
    have := conjSub_mem_lambdaSet hR hAyΛ g
    rwa [hgA] at this
  have hBy : conjSub B y = B := conjSub_of_forall_commute fun b hb =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left B D hyV) b hb).symm
  have hBg : conjSub B g = B := conjSub_of_forall_commute fun b hb =>
    (Subgroup.mem_centralizer_iff.1 (levi_le_centralizer_left B D hgV) b hb).symm
  have hA'B : A' ∈ lambdaSet R B := by
    have h1 := conjSub_mem_lambdaSet hR hAB y
    rw [hBy] at h1
    have h2 := conjSub_mem_lambdaSet hR h1 g
    rwa [hBg] at h2
  obtain ⟨P, ⟨hPR, hPle, hPψ⟩, -⟩ := existsUnique_mem_psiSet_of_le hR hiso hA hA₀.1 hA₀.2 hA'Λ
  have hPA : P ≠ A := by
    rintro rfl
    exact Special.not_opposite hR hA₀.1 hPψ.2 hA₀.2.symm
  have hPΛ : P ∈ lambdaSet R A :=
    (mem_lambdaSet_of_le_sup hR hiso hA hA'Λ hA le_sup_left hPR hPle hPA.symm).1
  have hMB : A ⊔ A' ≤ M R B := sup_le (QD.le_M hAB) (QD.le_M hA'B)
  have hMC : A ⊔ A' ≤ M R C :=
    sup_le (QD.le_M (mem_lambdaSet_comm hA hC.1)) (QD.le_M (mem_lambdaSet_comm hA'R hCA'))
  have hPB : P ≠ B := by
    rintro rfl
    exact hCB (mem_lambdaSet_comm hCR (mem_lambdaSet_of_le_M_of_hyp hS.hyp hCR hPR
      (hPle.trans hMC) he))
  have hPC : P ≠ C := by
    rintro rfl
    exact hCB (mem_lambdaSet_of_le_M_of_hyp hS.hyp hBR hPR (hPle.trans hMB) (Ne.symm he))
  exact ⟨P, ⟨⟨hPΛ, hPψ⟩, mem_lambdaSet_of_le_M_of_hyp hS.hyp hBR hPR (hPle.trans hMB) hPB⟩,
    mem_lambdaSet_of_le_M_of_hyp hS.hyp hCR hPR (hPle.trans hMC) hPC⟩

end Sec13

end CFSG.Timmesfeld.ARS

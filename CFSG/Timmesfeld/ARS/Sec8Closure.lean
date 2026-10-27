module

public import CFSG.Timmesfeld.ARS.Sec8Components
public import CFSG.Timmesfeld.ARS.Sec8Natural

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Levi

theorem opposite_of_commuting_iff (h : Hyp G R) {A A₀ E E' B : Subgroup G}
    (hE : E ∈ leviSet R A A₀) (hE' : E' ∈ leviSet R A A₀)
    (hEE' : ∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X) (hB : B ∈ leviSet R A A₀)
    (hEB : Opposite E B) : Opposite E' B := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hER : E ∈ R := hE.1.1
  have hE'R : E' ∈ R := hE'.1.1
  have hBR : B ∈ R := hB.1.1
  have hEE'c : Commuting E E' := ((hEE' E hE).1 (hR.commuting_self hER)).symm
  have hBnc : ¬ Commuting E' B := fun hc =>
    hEB.not_commuting (hR.ne_bot E hER) ((hEE' B hB).2 hc)
  by_contra hno
  have hs : Special R E' B := by
    have hne : E' ≠ B := fun e => hBnc (e ▸ hR.commuting_self hE'R)
    rcases hR.rel E' hE'R B hBR hne with hc | ho | hs
    · exact absurd hc hBnc
    · exact absurd ho hno
    · exact hs
  have hD := Sec3.commutator_mem_psiSet_of_commuting hR hiso hER hBR hEB ⟨hE'R, hs.symm⟩ hEE'c
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hBR
  obtain ⟨a, ha, ha1⟩ := hR.exists_ne_one hER
  have hE'b : conjSub E' b ∈ leviSet R A A₀ :=
    conjSub_mem_leviSet_of_mem_levi hR hE' (le_gen hB hb)
  have h1 : Commuting E (conjSub E' b) :=
    (hEE' _ hE'b).2 (commuting_conjSub_of_special hR hE'R hs hb)
  obtain ⟨a', ha', ha'1⟩ := hR.exists_ne_one hE'R
  have hcomm : Commute a ⁅b, a'⁆ := by
    have e1 : Commute a (b * a' * b⁻¹) := h1 a ha _ (conj_mem_conjSub b ha')
    have e2 : Commute a a' := hEE'c a ha a' ha'
    have := e1.mul_right e2.inv_right
    rwa [show b * a' * b⁻¹ * a'⁻¹ = ⁅b, a'⁆ from (commutatorElement_def b a').symm] at this
  have hba' := eq_one_of_commute_of_special hR hiso hER hD.1 hD.2 ha ha1
    (Subgroup.commutator_mem_commutator hb ha') hcomm
  rw [commutatorElement_eq_one_iff_mul_comm] at hba'
  exact ha'1 (eq_one_of_commute_of_special hR hiso hBR hE'R hs.symm hb hb1 ha' hba')

theorem commuting_iff_of_mem_lambdaStar (h : Hyp G R) {A A₀ E E' B : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A)
    (hE : E ∈ leviSet R A A₀) (hE' : E' ∈ leviSet R A A₀)
    (hEE' : ∀ X ∈ leviSet R A A₀, Commuting E X ↔ Commuting E' X)
    (hB : B ∈ lambdaStar R A A₀) : Commuting B E ↔ Commuting B E' := by
  have key : ∀ {X X' : Subgroup G}, X ∈ leviSet R A A₀ → X' ∈ leviSet R A A₀ →
      (∀ Y ∈ leviSet R A A₀, Commuting X Y ↔ Commuting X' Y) → Commuting B X →
      Commuting B X' := by
    intro X X' hX hX' hXX' hBX
    have := h.finite
    have hR := h.root
    have hBR : B ∈ R := hB.1.1.1
    have hX'R : X' ∈ R := hX'.1.1
    by_contra hBX'
    have hs : Special R B X' := by
      have hne : B ≠ X' := fun e => hBX' (e ▸ hR.commuting_self hBR)
      rcases hR.rel B hBR X' hX'R hne with hc | ho | hs
      · exact absurd hc hBX'
      · exact absurd hX'.1.2.2.symm (not_commuting_of_opposite_of_mem_lambdaSet hR hX'R ho.symm
          (mem_lambdaSet_comm hA hB.1))
      · exact hs
    obtain ⟨-, D, hD, hX'D, hBD⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hX' hB hs
    have hXD : Opposite X D :=
      opposite_of_commuting_iff h hX' hX (fun Y hY => (hXX' Y hY).symm) hD hX'D
    exact not_commuting_of_opposite_of_mem_lambdaSet hR hX.1.1 hXD hBD hBX.symm
  exact ⟨key hE hE' hEE', key hE' hE fun X hX => (hEE' X hX).symm⟩

end Levi

end CFSG.Timmesfeld.ARS

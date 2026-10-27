module

public import CFSG.Timmesfeld.ARS.Sec8Natural

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

namespace Sec9

theorem commutatorElement_mul_right_of_commute {z n n' : G} (h : Commute n ⁅z, n'⁆) :
    ⁅z, n * n'⁆ = ⁅z, n⁆ * ⁅z, n'⁆ := by
  have h' : n * ⁅z, n'⁆ * n⁻¹ = ⁅z, n'⁆ := by rw [h.eq, mul_inv_cancel_right]
  calc ⁅z, n * n'⁆ = ⁅z, n⁆ * (n * ⁅z, n'⁆ * n⁻¹) := by
        simp only [commutatorElement_def]; group
    _ = ⁅z, n⁆ * ⁅z, n'⁆ := by rw [h']

theorem exists_commuting_of_le_M (h : Hyp G R) {A P₁ P₂ Z : Subgroup G} (hA : A ∈ R)
    (hP₁ : P₁ ∈ R) (hP₂ : P₂ ∈ lambdaSet R P₁) (hℓ : P₁ ⊔ P₂ ≤ M R A) (hZ : Z ∈ R)
    (hZM : Z ≤ M R A) : ∃ P ∈ R, P ≤ P₁ ⊔ P₂ ∧ Commuting Z P := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨-, -, hcomm, -, hMP⟩ := Q_eq_M h hA
  have hcen : Commuting A (M R A) := QD.commuting_M hR hA
  obtain ⟨z, hz, hz1⟩ := hR.exists_ne_one hZ
  set L := P₁ ⊔ P₂ with hL
  have hmemA : ∀ n ∈ L, ⁅z, n⁆ ∈ A := fun n hn => by
    rw [← hcomm]
    exact Subgroup.commutator_mem_commutator (hZM hz) (hℓ hn)
  let f : ↥L →* G :=
    { toFun := fun n => ⁅z, (n : G)⁆
      map_one' := by simp
      map_mul' := fun n n' => by
        change ⁅z, (n : G) * n'⁆ = ⁅z, (n : G)⁆ * ⁅z, (n' : G)⁆
        exact commutatorElement_mul_right_of_commute
          ((hcen _ (hmemA n' n'.2) n (hℓ n.2)).symm) }
  have hrange : f.range ≤ A := by
    rintro _ ⟨n, rfl⟩
    exact hmemA n n.2
  have hcardL : Nat.card ↥L = Nat.card A ^ 2 := by
    refine le_antisymm ?_ ?_
    · calc Nat.card ↥L ≤ Nat.card P₁ * Nat.card P₂ := card_sup_le_of_commuting hP₂.1.2.2
        _ = Nat.card A ^ 2 := by rw [hR.card_eq hP₁ hA, hR.card_eq hP₂.1.1 hA, sq]
    · calc Nat.card A ^ 2 = Nat.card P₁ * Nat.card P₂ := by
            rw [hR.card_eq hP₁ hA, hR.card_eq hP₂.1.1 hA, sq]
        _ ≤ Nat.card ↥L :=
            card_mul_card_le_card_sup (inf_eq_bot hR hiso hP₁ hP₂.1.1 (Ne.symm hP₂.1.2.1))
  have hq : 2 ≤ Nat.card A := (Subgroup.one_lt_card_iff_ne_bot A).2 (hR.ne_bot A hA)
  have hker : f.ker ≠ ⊥ := by
    intro hbot
    have h1 := Subgroup.card_mul_index f.ker
    rw [Subgroup.index_ker, hbot, Subgroup.card_bot, one_mul, hcardL] at h1
    have h2 : Nat.card f.range ≤ Nat.card A := Subgroup.card_le_of_le hrange
    rw [h1, sq] at h2
    nlinarith
  obtain ⟨n, hn1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hker
  have hnL : (n : ↥L) ≠ 1 := fun e => hn1 (Subtype.ext (by rw [e]; rfl))
  have hn1' : ((n : ↥L) : G) ≠ 1 := fun e => hnL (Subtype.ext e)
  have hfn : ⁅z, ((n : ↥L) : G)⁆ = 1 := n.2
  obtain ⟨P, hP, hPL, hnP⟩ := hP₂.2 _ (n : ↥L).2 hn1'
  refine ⟨P, hP, hPL, ?_⟩
  by_cases hZP : Z = P
  · rw [← hZP]
    exact hR.commuting_self hZ
  have hzn : Commute z ((n : ↥L) : G) := commutatorElement_eq_one_iff_commute.1 hfn
  rcases hR.rel Z hZ P hP hZP with hc | ho | hs
  · exact hc
  · exact absurd ho (Sec3.not_opposite_of_isPGroup_sup hR hZ hP
      (hMP.to_le (sup_le hZM (hPL.trans hℓ))))
  · exact absurd (eq_one_of_commute_of_special hR hiso hZ hP hs hz hz1 hnP hzn) hn1'

theorem natural_points (h : Hyp G R) {A A₀ F X : Subgroup G} (hA : A ∈ R)
    (hAne : sigmaSet R A ≠ lambdaSet R A) (hA₀ : A₀ ∈ omegaSet R A) (hF : F ∈ leviSet R A A₀)
    (hX : X ∈ lambdaStar R A A₀) (hXF : Special R X F) :
    ∃ D ∈ leviSet R A A₀, Opposite F D ∧ ∀ P ∈ R, P ≤ X ⊔ ⁅X, F⁆ →
      P ∈ lambdaStar R A A₀ ∧ ∃ g ∈ D ⊔ F, conjSub X g = P := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  obtain ⟨hpts, D, hD, hFD, hXD⟩ := exists_opposite_of_mem_lambdaStar h hA hAne hA₀ hF hX hXF
  refine ⟨D, hD, hFD, fun P hP hPle => ⟨hpts P hP hPle, ?_⟩⟩
  have hXD' : X ∈ lambdaSet R D := hXD
  have hXψ : X ∈ psiSet R F := ⟨hX.1.1.1, hXF.symm⟩
  obtain ⟨p, hp, hp1⟩ := hR.exists_ne_one hP
  have hpN : p ∈ X ⊔ ⁅F, X⁆ := by
    rw [Subgroup.commutator_comm F X]
    exact hPle hp
  obtain ⟨g, hg, hpg⟩ := Sec3.exists_mem_conjSub_of_mem_sup hR hiso hD.1.1 hF.1.1 hFD.symm hXD'
    hXψ hpN hp1
  exact ⟨g, hg, Sec3.eq_of_mem_of_mem hR hiso (hR.conjSub_mem hX.1.1.1 g) hP hpg hp hp1⟩

end Sec9

end CFSG.Timmesfeld.ARS

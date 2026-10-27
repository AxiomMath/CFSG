module

public import Mathlib.Algebra.Field.Defs
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.Group.Subgroup.Finite
public import Mathlib.GroupTheory.Coset.Card

public section

namespace CFSG.Quasithin

namespace SBc8

section Projection

variable {F : Type} [Field F] {k : ℕ}

private def coordProj (𝒱 : AddSubgroup (Fin k → Fin 3 → F)) (i : Fin k) :
    AddSubgroup (Fin 3 → F) :=
  𝒱.map (Pi.evalAddMonoidHom (fun _ : Fin k => Fin 3 → F) i)

private theorem mem_coordProj {𝒱 : AddSubgroup (Fin k → Fin 3 → F)} {i : Fin k} {e : Fin 3 → F} :
    e ∈ coordProj 𝒱 i ↔ ∃ x ∈ 𝒱, x i = e :=
  AddSubgroup.mem_map

private theorem exists_surjective_coordProj (𝒱 : AddSubgroup (Fin k → Fin 3 → F)) (i : Fin k) :
    ∃ ψ : 𝒱 → coordProj 𝒱 i, Function.Surjective ψ ∧
      ∀ x : 𝒱, (ψ x : Fin 3 → F) = (x : Fin k → Fin 3 → F) i := by
  refine ⟨fun x => ⟨(x : Fin k → Fin 3 → F) i, mem_coordProj.2 ⟨x, x.2, rfl⟩⟩, ?_, fun _ => rfl⟩
  rintro ⟨e, he⟩
  obtain ⟨x, hx, rfl⟩ := mem_coordProj.1 he
  exact ⟨⟨x, hx⟩, rfl⟩

private theorem card_dvd_eight [Fintype F] (hF : Fintype.card F = 2) (E : AddSubgroup (Fin 3 → F)) :
    Nat.card E ∣ 8 := by
  have hamb : Nat.card (Fin 3 → F) = 2 ^ 3 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_pi_const, hF]
  have hdvd := AddSubgroup.card_addSubgroup_dvd_card E
  rw [hamb] at hdvd
  simpa using hdvd

end Projection

theorem exists_plane_coordinate {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2) {k : ℕ}
    (𝒱 : AddSubgroup (Fin k → Fin 3 → F)) (h𝒱 : Nat.card 𝒱 = 4)
    (𝒢 : Set (Matrix (Fin 3) (Fin 3) F)) (hdet : ∀ A ∈ 𝒢, IsUnit A)
    (hinv : ∀ A ∈ 𝒢, ∀ x ∈ 𝒱, (fun i => A.mulVec (x i)) ∈ 𝒱)
    (hfix : ∀ x ∈ 𝒱, (∀ A ∈ 𝒢, (fun i => A.mulVec (x i)) = x) → x = 0) :
    ∃ i : Fin k, ∃ E : AddSubgroup (Fin 3 → F), (∀ e, e ∈ E ↔ ∃ x ∈ 𝒱, x i = e) ∧
      Nat.card E = 4 ∧ (∀ e ∈ E, (∀ A ∈ 𝒢, A.mulVec e = e) → e = 0) := by
  classical
  obtain ⟨i, A, hA, x, hx, hAx⟩ : ∃ i : Fin k, ∃ A ∈ 𝒢, ∃ x ∈ 𝒱, A.mulVec (x i) ≠ x i := by
    refine Classical.byContradiction fun hmove => ?_
    have hbot : 𝒱 = ⊥ := (AddSubgroup.eq_bot_iff_forall 𝒱).2 fun y hy =>
      hfix y hy fun B hB => funext fun j =>
        Classical.byContradiction fun hne => hmove ⟨j, B, hB, y, hy, hne⟩
    rw [hbot, AddSubgroup.card_bot] at h𝒱
    omega
  obtain ⟨ψ, hψs, hψ⟩ := exists_surjective_coordProj 𝒱 i
  have hcard : Nat.card (coordProj 𝒱 i) = 4 := by
    have hx0 : x i ≠ 0 := fun h0 => hAx (by rw [h0, Matrix.mulVec_zero])
    have hAx0 : A.mulVec (x i) ≠ 0 := fun h0 =>
      hx0 (Matrix.mulVec_injective_of_isUnit (hdet A hA) (h0.trans (Matrix.mulVec_zero A).symm))
    have h3 : 2 < Fintype.card (coordProj 𝒱 i) := by
      refine Fintype.two_lt_card_iff.2
        ⟨⟨0, AddSubgroup.zero_mem _⟩, ⟨x i, mem_coordProj.2 ⟨x, hx, rfl⟩⟩,
          ⟨A.mulVec (x i), mem_coordProj.2 ⟨fun j => A.mulVec (x j), hinv A hA x hx, rfl⟩⟩,
          ?_, ?_, ?_⟩
      · exact fun h => hx0 (congrArg Subtype.val h).symm
      · exact fun h => hAx0 (congrArg Subtype.val h).symm
      · exact fun h => hAx (congrArg Subtype.val h).symm
    rw [← Nat.card_eq_fintype_card] at h3
    have h4 : Nat.card (coordProj 𝒱 i) ≤ 4 :=
      (Nat.card_le_card_of_surjective ψ hψs).trans h𝒱.le
    have h8 := card_dvd_eight hF (coordProj 𝒱 i)
    rcases (by omega : Nat.card (coordProj 𝒱 i) = 3 ∨ Nat.card (coordProj 𝒱 i) = 4) with h | h
    · rw [h] at h8
      omega
    · exact h
  have hbij : Function.Bijective ψ := hψs.bijective_of_nat_card_le (h𝒱.trans hcard.symm).le
  refine ⟨i, coordProj 𝒱 i, fun e => mem_coordProj, hcard, ?_⟩
  intro e he hfixe
  obtain ⟨y, hy, rfl⟩ := mem_coordProj.1 he
  have hy0 : y = 0 := by
    refine hfix y hy fun B hB => ?_
    have hψeq : ψ ⟨fun j => B.mulVec (y j), hinv B hB y hy⟩ = ψ ⟨y, hy⟩ :=
      Subtype.ext (by rw [hψ, hψ]; exact hfixe B hB)
    exact congrArg Subtype.val (hbij.1 hψeq)
  simp [hy0]

end SBc8

end CFSG.Quasithin

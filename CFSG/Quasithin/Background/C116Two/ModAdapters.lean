module

public import CFSG.Quasithin.Background.C116Two.NatMod

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

theorem modData_of_lin2 {L : Subgroup G} {n : ℕ} (h : IsLin2Type L n) :
    ∃ (F : Type) (_ : Field F) (_ : Fintype F) (D : ModData L (Multiplicative (Fin 2 → F))),
      Fintype.card F = 2 ^ n ∧ D.ρ.range = (slAct F).range := by
  obtain ⟨F, _, _, hcard, α, hαs, hαk, β, hβs, hβk, hβact⟩ := h
  refine ⟨F, inferInstance, inferInstance,
    { ρ := (slAct F).comp α
      β := β
      surj := hβs
      ker := hβk
      equiv := ?_
      faithful := ?_ }, hcard, ?_⟩
  · intro ℓ u v hv
    have := hβact ℓ u v hv
    apply Multiplicative.toAdd.injective
    rw [this]
    simp [slAct_apply]
  · intro ℓ hℓ
    have hfix : ∀ x : Fin 2 → F, (α ℓ : Matrix (Fin 2) (Fin 2) F).mulVec x = x := by
      intro x
      have := congrArg (fun φ => Multiplicative.toAdd (φ (Multiplicative.ofAdd x))) hℓ
      simpa [slAct_apply] using this
    have hα1 : α ℓ = 1 := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_one]
      exact Matrix.ext_iff_mulVec.mpr fun v => by rw [hfix v, Matrix.one_mulVec]
    have hmem : ℓ ∈ α.ker := hα1
    rw [hαk] at hmem
    exact ⟨ℓ, hmem, rfl⟩
  · show ((slAct F).comp α).range = (slAct F).range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hαs, Subgroup.map_top]

def pairV (m : ℕ) (i j : Fin m) : Fin m → ZMod 2 :=
  fun k => (if k = i then 1 else 0) + (if k = j then 1 else 0)

theorem pairV_mem (m : ℕ) (i j : Fin m) : pairV m i j ∈ evenWeight m := by
  show ∑ k, pairV m i j k = 0
  unfold pairV
  rw [Finset.sum_add_distrib]
  simp
  decide

theorem perm_eq_one_of_fixes_evenWeight {m : ℕ} (hm : 3 ≤ m) (σ : Equiv.Perm (Fin m))
    (h : ∀ x : evenWeight m, ∀ i, (x : Fin m → ZMod 2) i = (x : Fin m → ZMod 2) (σ⁻¹ i)) :
    σ = 1 := by
  have key : ∀ i j : Fin m, i ≠ j → σ⁻¹ i = i ∨ σ⁻¹ i = j := by
    intro i j hij
    have := h ⟨pairV m i j, pairV_mem m i j⟩ i
    simp only [pairV] at this
    by_contra hcon
    push_neg at hcon
    generalize σ⁻¹ i = k at this hcon
    simp [hij, hcon.1, hcon.2] at this
  have hfix : ∀ i, σ⁻¹ i = i := by
    intro i
    obtain ⟨j, -, hj⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({i} : Finset (Fin m))) (t := Finset.univ) (by simp; omega)
    obtain ⟨j', -, hj'⟩ := Finset.exists_mem_notMem_of_card_lt_card
      (s := ({i, j} : Finset (Fin m))) (t := Finset.univ)
      (by rw [Finset.card_univ, Fintype.card_fin]; exact lt_of_le_of_lt (Finset.card_le_two) (by omega))
    have hji : j ≠ i := by simpa using hj
    have hj'i : j' ≠ i := fun e => hj' (by simp [e])
    have hj'j : j' ≠ j := fun e => hj' (by simp [e])
    rcases key i j (Ne.symm hji) with h1 | h1
    · exact h1
    · rcases key i j' (Ne.symm hj'i) with h2 | h2
      · exact h2
      · exact absurd (h1.symm.trans h2) (Ne.symm hj'j)
  refine Equiv.ext fun i => ?_
  have h2 : σ i = i := by
    have := congrArg σ (hfix i)
    simpa using this.symm
  simpa using h2

theorem modData_of_alt {L : Subgroup G} {m : ℕ} (hm3 : 3 ≤ m) (h : IsAltType L m) :
    ∃ D : ModData L (Multiplicative (evenWeight m)), D.ρ.range = (altAct m).range := by
  obtain ⟨α, hαs, hαk, β, hβs, hβk, hβact⟩ := h
  refine ⟨{ ρ := (altAct m).comp α
            β := β
            surj := hβs
            ker := hβk
            equiv := ?_
            faithful := ?_ }, ?_⟩
  · intro ℓ u v hv
    apply Multiplicative.toAdd.injective
    apply Subtype.ext
    funext i
    exact hβact ℓ u v hv i
  · intro ℓ hℓ
    have h1 : permAct m ((α ℓ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m)) = 1 := hℓ
    have hfix : ∀ x : evenWeight m, ∀ i, (x : Fin m → ZMod 2) i =
        (x : Fin m → ZMod 2) (((α ℓ : alternatingGroup (Fin m)) : Equiv.Perm (Fin m))⁻¹ i) := by
      intro x i
      have := congrArg (fun φ => ((Multiplicative.toAdd (φ (Multiplicative.ofAdd x)) :
        evenWeight m) : Fin m → ZMod 2) i) h1
      simp only [permAct_apply, MulAut.one_apply, toAdd_ofAdd] at this
      exact this.symm
    have hσ := perm_eq_one_of_fixes_evenWeight hm3 _ hfix
    have hα1 : α ℓ = 1 := Subtype.ext hσ
    have hmem : ℓ ∈ α.ker := hα1
    rw [hαk] at hmem
    exact ⟨ℓ, hmem, rfl⟩
  · show ((altAct m).comp α).range = (altAct m).range
    rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr hαs, Subgroup.map_top]

end CFSG.Quasithin.C116Two

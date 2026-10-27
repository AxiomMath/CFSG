module

public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.Simplicity.TitsElements
public import CFSG.Quasithin.Background.F918V2Defs2
public import CFSG.Quasithin.Background.HSL
public import CFSG.Quasithin.EmptyFaithful.SzN15Nat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup

open scoped Matrix

theorem s16c167_endUnits_ln {W : Type} [CommGroup W] [Finite W] {H : Subgroup (MulAut W)}
    {I : Subgroup W} {m : ℕ} (hm : 3 ≤ m) (h : BinaryNaturalSL H I ⊥ m 1) :
    Z391.EndUnitsTrivial H I := by
  obtain ⟨K, hK, hKf, hK2, π, hπ⟩ := h
  letI := hK
  haveI : Finite K := hKf
  have hK2' : Nat.card K = 2 := by simpa using hK2
  let R := CFSG.Quasithin.SzN15.NatReal.of_realizesVia hπ
  obtain ⟨β, hβsurj, hβker, hβe⟩ := R.exists_β
  have hβinj : Function.Injective β := by
    intro a b hab
    have h1 : β (a * b⁻¹) = 1 := by rw [map_mul, map_inv, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : ↥I) : W) ∈ (⊥ : Subgroup W) := (hβker (a * b⁻¹)).1 h1
    have h3 : a * b⁻¹ = 1 := Subtype.ext (by simpa using Subgroup.mem_bot.1 h2)
    exact mul_inv_eq_one.1 h3
  let βe : ↥I ≃* Multiplicative (Fin m → K) := MulEquiv.ofBijective β ⟨hβinj, hβsurj⟩
  have hβe_apply : ∀ p : ↥I, βe p = β p := fun _ => rfl
  intro φ hφ
  let f : Multiplicative (Fin m → K) ≃* Multiplicative (Fin m → K) :=
    βe.symm.trans (φ.trans βe)
  have hfβ : ∀ p : ↥I, f (βe p) = βe (φ p) := fun p => by simp [f]
  let g : (Fin m → K) →+ (Fin m → K) := AddMonoidHom.toMultiplicative.symm f.toMonoidHom
  have hgapp : ∀ v : Fin m → K, g v = Multiplicative.toAdd (f (Multiplicative.ofAdd v)) :=
    fun _ => rfl
  have hg0 : ∀ p : ↥I, g (Multiplicative.toAdd (βe p)) =
      Multiplicative.toAdd (βe (φ p)) := by
    intro p
    rw [hgapp, ofAdd_toAdd, hfβ]
  have hg : ∀ γ ∈ StatedSL m K, ∀ v : Fin m → K,
      g ((γ : Matrix (Fin m) (Fin m) K) *ᵥ v) =
        (γ : Matrix (Fin m) (Fin m) K) *ᵥ g v := by
    intro γ hγ v
    let γ' : ↥(StatedSL m K) := ⟨γ, hγ⟩
    obtain ⟨x, rfl⟩ : ∃ x : ↥I, Multiplicative.toAdd (βe x) = v :=
      ⟨βe.symm (Multiplicative.ofAdd v), by rw [MulEquiv.apply_symm_apply, toAdd_ofAdd]⟩
    have hnat : ∀ (y : ↥I) (hu : ((π γ' : ↥H) : MulAut W) (y : W) ∈ I),
        Multiplicative.toAdd (βe ⟨((π γ' : ↥H) : MulAut W) (y : W), hu⟩) =
          (γ : Matrix (Fin m) (Fin m) K) *ᵥ Multiplicative.toAdd (βe y) := by
      intro y hu
      have h := hβe γ' y hu
      calc Multiplicative.toAdd (βe ⟨((π γ' : ↥H) : MulAut W) (y : W), hu⟩)
          = Multiplicative.toAdd (β ⟨((π γ' : ↥H) : MulAut W) (y : W), hu⟩) := by
            simp only [hβe_apply]
        _ = Multiplicative.toAdd (natAct (StatedSL m K) γ' (β y)) :=
            congrArg Multiplicative.toAdd h
        _ = (γ : Matrix (Fin m) (Fin m) K) *ᵥ Multiplicative.toAdd (βe y) := by
            simp only [hβe_apply]
            rfl
    have hmemx : ((π γ' : ↥H) : MulAut W) (x : W) ∈ I := R.U_inv (π γ') x x.2
    have e2 : φ ⟨((π γ' : ↥H) : MulAut W) (x : W), hmemx⟩ =
        ⟨((π γ' : ↥H) : MulAut W) ((φ x : ↥I) : W),
          R.U_inv (π γ') (φ x) (φ x).2⟩ :=
      Subtype.ext (hφ (π γ') x ⟨((π γ' : ↥H) : MulAut W) (x : W), hmemx⟩ rfl).symm
    rw [← hnat x hmemx, hg0, e2, hg0, hnat (φ x) (R.U_inv (π γ') (φ x) (φ x).2)]
  obtain ⟨c, hc⟩ := CFSG.Quasithin.H.hasScalarCommutant_statedSL (K := K) (d := m)
    (by omega : 2 ≤ m) g hg
  let e0 : Fin m → K := Pi.single ⟨0, by omega⟩ 1
  have he0 : e0 ⟨0, by omega⟩ = 1 := by simp [e0]
  have he0ne : e0 ≠ 0 := by
    intro h0
    have h1 : (1 : K) = 0 := by
      rw [← he0]
      exact congrFun h0 ⟨0, by omega⟩
    exact one_ne_zero h1
  have hg_e0_ne : g e0 ≠ 0 := by
    have h1 : Multiplicative.ofAdd e0 ≠ (1 : Multiplicative (Fin m → K)) := by
      intro h0
      exact he0ne (by simpa using congrArg Multiplicative.toAdd h0)
    have h2 : f (Multiplicative.ofAdd e0) ≠ 1 := by
      intro h0
      exact h1 (f.injective (by simp [h0]))
    intro h0
    exact h2 (Multiplicative.toAdd.injective (by
      rw [← hgapp e0]
      simpa using h0))
  have hcne : c ≠ 0 := fun hc0 => hg_e0_ne (by rw [hc e0, hc0, zero_smul])
  have hc1 : c = 1 := by
    rcases CFSG.LieType.Simplicity.TitsBits.eq_zero_or_eq_one_of_card_eq_two hK2' c with
      h | h
    · exact absurd h hcne
    · exact h
  refine MulEquiv.ext fun x => ?_
  apply βe.injective
  apply Multiplicative.toAdd.injective
  rw [← hg0 x, hc (Multiplicative.toAdd (βe x)), hc1, one_smul]
  rfl

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

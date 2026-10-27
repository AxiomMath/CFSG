module

public import CFSG.Quasithin.Vol2.Ch11SecAKA8
public import CFSG.Quasithin.Vol2.Ch11SecAFacts15c
public import CFSG.Quasithin.Vol2.Ch11SecAKA2

public section

namespace CFSG.Quasithin.Vol2.KGNat

open CFSG.Quasithin
open CFSG.Assembly.LowTwoRank (StatedSp)

namespace KA

theorem radicalConj_of {K : Type} [Field K] [Finite K] {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n) {W : Type} [CommGroup W] [Finite W] (hW : ∀ w : W, w ^ 2 = 1)
    {H : Subgroup (MulAut W)} {Z : Subgroup W} {π : ↥(StatedSp 2 K) →* ↥H}
    (hπ : (FFModel.nat (StatedSp 2 K)).RealizesVia H ⊤ Z π) {P : Subgroup (MulAut W)}
    (hP : QuasithinUnique.IsSylowTwoOf P H) {U : Subgroup W}
    (hU : Ch11.SecA.IsFlagW H P Z (2 ^ n) 1 U) {τ : MulAut W} (hτ2 : ∃ k : ℕ, τ ^ 2 ^ k = 1)
    (hτZ : τ ∈ Ch11.SecA.stabW Z) (hτH : ∀ h ∈ H, τ * h * τ⁻¹ ∈ H)
    (hτc : ∀ x : ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)),
      ∃ y : ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)),
        y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)) ∧
          τ * (x : MulAut W) * τ⁻¹ = (y : MulAut W) * x) :
    ∃ y : ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)),
      y ∈ CFSG.pCore 2 ↥(perfectCore (H ⊓ Ch11.SecA.stabW U)) ∧
        (∀ h ∈ H, τ * h * τ⁻¹ = (y : MulAut W) * h * (y : MulAut W)⁻¹) ∧
        ∀ u ∈ U, τ u * u⁻¹ ∈ Z := by
  have : CharP K 2 := charP_two_of_card (by omega) hK
  have hK4 := CFSG.QuasithinUnique.Vol2Native.A312L.exists_finset_card_four (four_le_card hn hK)
  have hfix := factRadicalFixedSp4_holds K n hn hK W hW H Z π hπ P hP U hU
  have hpt := factPointSp4_holds K n hn hK W hW H Z π hπ P hP U hU
  obtain ⟨f, hf, g, -, hUeq⟩ := exists_point_coords hn hK hW hπ hP hU
  obtain ⟨N, hN, hact⟩ := exists_core hK4 hf g hUeq hfix hpt hτ2 hτZ hτH hτc
  subst hUeq
  have : Finite (MulAut W) := Finite.of_injective _ MulEquiv.toEquiv_injective
  obtain ⟨y, hy, hyN⟩ := exists_pCore_of_mem hf g hN
  have hyH : (y : MulAut W) ∈ H := (perfectCore_le _ y.2).1
  have hact' : ∀ w, f (τ w) = f ((y : MulAut W) w) := fun w => by rw [hyN]; exact hact w
  refine ⟨y, hy, fun h hh => ?_, fun u hu => ?_⟩
  · refine eq_of_forall_f_eq hf (hτH h hh) (H.mul_mem (H.mul_mem hyH hh) (H.inv_mem hyH))
      fun w => ?_
    have h1 : f (τ⁻¹ w) = f ((y : MulAut W)⁻¹ w) := by
      have h2 := hact' (τ⁻¹ w)
      rw [MulAut.apply_inv_self] at h2
      exact act_cancel hf hyH (by rw [MulAut.apply_inv_self]; exact h2.symm)
    simp only [MulAut.mul_apply]
    rw [hact']
    exact act_congr hf hyH (act_congr hf hh h1)
  · have h1 := hpt _ y.2 u hu
    rw [← hf.eq_iff] at h1 ⊢
    rw [hact', h1]

end KA

theorem factRadicalInnerSp4_holds : Ch11.SecA.FactRadicalInnerSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU τ hτ2 hτZ hτH _ hτc
  obtain ⟨y, hy, hinner, -⟩ := KA.radicalConj_of hn hK hW hπ hP hU hτ2 hτZ hτH hτc
  exact ⟨y, hy, hinner⟩

theorem factRadicalPointSp4_holds : Ch11.SecA.FactRadicalPointSp4 := by
  intro K _ _ n hn hK W _ _ hW H Z π hπ P hP U hU τ hτ2 hτZ hτH _ hτc
  obtain ⟨y, -, -, hpt⟩ := KA.radicalConj_of hn hK hW hπ hP hU hτ2 hτZ hτH hτc
  exact hpt

end CFSG.Quasithin.Vol2.KGNat

module

public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobDefs
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobFour
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobSelected
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobGrowth
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobBound
public import CFSG.LocalAnalysis.StandardType.GGTBJConfigFacts
public import CFSG.LocalAnalysis.StandardType.ZS.ClassReflClosure
public import CFSG.LocalAnalysis.StandardType.ZS.OrderBound
public import CFSG.LinearAlgebra.F3ConnectedPairingScalar
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobExc
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobOrthIndex
public import CFSG.LocalAnalysis.StandardType.GGQTwoGlobOrthOrbit

public section
namespace CFSG.StandardType.QTwo
open CFSG.StandardType

variable {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {U : Submodule (ZMod 3) V} {Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U)}
    {ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar}

include ι in
theorem qTwoGlobLin_finite : Finite V :=
  Finite.of_equiv (Additive ↥Bs) ι.toEquiv

include ι in
theorem qTwoGlobLin_finrank {m : ℕ} (hLM : QTwoLocalModel m Bs L x) :
    Module.finrank (ZMod 3) V = m := by
  letI : Finite V := qTwoGlobLin_finite (ι := ι)
  letI : Fintype V := Fintype.ofFinite V
  have hc : Nat.card V = 3 ^ m := by
    calc Nat.card V = Nat.card (Additive ↥Bs) := (Nat.card_congr ι.toEquiv).symm
      _ = Nat.card ↥Bs := Nat.card_congr Additive.toMul
      _ = 3 ^ m := hLM.card
  have hp := FiniteField.pow_finrank_eq_card 3 V
  rw [Fintype.card_eq_nat_card, hc] at hp
  exact Nat.pow_right_injective (by norm_num : 2 ≤ 3) hp

theorem qTwoGlobLin_not_h4 {m : ℕ} (hm : 5 ≤ m) (hLM : QTwoLocalModel m Bs L x)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hdeg : Module.finrank (ZMod 3) U = 4)
    (hneg : (LinearEquiv.neg (ZMod 3) : ↥U ≃ₗ[ZMod 3] ↥U) ∈ Abar) : False := by
  have htop := hD.2.2.2.2.2.2 hneg
  have hfr := qTwoGlobLin_finrank (ι := ι) hLM
  rw [htop, finrank_top] at hdeg
  omega

theorem qTwoGlobLin_orth_four {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {m N : ℕ} (hm : 5 ≤ m) (hN1 : m + 1 ≤ N) (hN2 : N ≤ m + 2)
    (hA : GGWeylOfType 3 (CoxeterMatrix.A (N - 1)) (ggAutomizerJoin L Bs 𝒦))
    (hLM : QTwoLocalModel m Bs L x)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hdim : Module.finrank (ZMod 3) U = m ∨ Module.finrank (ZMod 3) U + 1 = m)
    (Q : QuadraticForm (ZMod 3) U) (hQ : (qTwoPolar Q).Nondegenerate)
    (hcase : (∀ g, g ∈ Abar ↔ ZS.IsIsom 3 Q g) ∨
      (∃ c : ZMod 3, c ≠ 0 ∧ Abar = Subgroup.closure (ZS.ClassRefl 3 Q c)))
    (hd : Module.finrank (ZMod 3) U = 4) : ZS.LinWeyl 3 Abar := by
  letI : Finite V := qTwoGlobLin_finite (ι := ι)
  letI : Module.Finite (ZMod 3) U := Module.Finite.of_finite
  have hm5 : m = 5 := by omega
  have hfac := qTwoGlobSel_factorial_dvd_card_Abar hcfg (by omega : 1 ≤ N) hA hD
  obtain ⟨hN, hc⟩ := qTwoGlobFour_selected_card Q hQ hd
    (qTwoGlobFour_orth_le Q hcase) (by omega : 6 ≤ N) (by omega : N ≤ 7)
    hfac (qTwoGlobLin_not_h4 hm hLM hD hd)
  apply qTwoGlobSel_linWeyl_of_card_eq hcfg (by omega) (by omega) hA hD
  rw [hN]
  norm_num [Nat.factorial, hc]

theorem qTwoGlobLin_exists_refl {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {N : ℕ} (hN : 2 ≤ N)
    (hA : GGWeylOfType 3 (CoxeterMatrix.A (N - 1)) (ggAutomizerJoin L Bs 𝒦))
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ) :
    ∃ r ∈ Abar, ZS.IsRefl 3 r := by
  obtain ⟨e, he⟩ := hA
  let i : Fin (N - 1) := ⟨0, by omega⟩
  let a : ggAInf 3 B Bs x L D J :=
    ⟨(e ((CoxeterMatrix.A (N - 1)).simple i) : MulAut ↥Bs),
      qTwoGlobSel_join_le_ggAInf hcfg (e ((CoxeterMatrix.A (N - 1)).simple i)).2⟩
  refine ⟨(ρ a : ↥U ≃ₗ[ZMod 3] ↥U), (ρ a).2, ?_⟩
  exact (hD.2.2.2.2.2.1 a).mp (he i)

theorem qTwoGlobLin_distinguished_five {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    (hLM : QTwoLocalModel 5 Bs L x)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hd : Module.finrank (ZMod 3) U = 5) :
    ∃ u : U, u ≠ 0 ∧
      Nat.card {g : Abar // (g : ↥U ≃ₗ[ZMod 3] ↥U) u = u} ≤ 240 := by
  letI : Finite V := qTwoGlobLin_finite (ι := ι)
  letI : Module.Finite (ZMod 3) V := Module.Finite.of_finite
  have htop : U = ⊤ := Submodule.eq_top_of_finrank_eq
    (hd.trans (qTwoGlobLin_finrank (ι := ι) hLM).symm)
  let v : V := ι (Additive.ofMul (⟨x, hLM.mem⟩ : ↥Bs))
  let u : U := ⟨v, by rw [htop]; trivial⟩
  have hx : x ≠ 1 := (GGConfig.data_L hcfg.1.1).2.1
  refine ⟨u, ?_, ?_⟩
  · intro hu
    exact qTwoGlobBnd_vx_ne_zero hLM hx (congrArg (fun z : U => (z : V)) hu)
  · have hs := qTwoGlobBnd_stab_le hLM hD u (by rfl)
    norm_num [Nat.factorial] at hs
    exact hs

include ι in
theorem qTwoGlobLin_orth_commutators
    (Q : QuadraticForm (ZMod 3) U) (hQ : (qTwoPolar Q).Nondegenerate)
    (hcase : (∀ g, g ∈ Abar ↔ ZS.IsIsom 3 Q g) ∨
      (∃ c : ZMod 3, c ≠ 0 ∧ Abar = Subgroup.closure (ZS.ClassRefl 3 Q c)))
    (hd : 5 ≤ Module.finrank (ZMod 3) U) :
    ∀ g h : ↥U ≃ₗ[ZMod 3] ↥U, ZS.IsIsom 3 Q g → ZS.IsIsom 3 Q h →
      g * h * g⁻¹ * h⁻¹ ∈ Abar := by
  letI : Finite V := qTwoGlobLin_finite (ι := ι)
  letI : Module.Finite (ZMod 3) U := Module.Finite.of_finite
  rcases hcase with hf | ⟨c, hc, heq⟩
  · intro g h hg hh
    apply (hf _).mpr
    apply TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
    exact (TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
      ((TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
        ((TauCeti.QuadraticMap.orthogonalGroup Q).mul_mem
          (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg)
          (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hh))
        ((TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem
          (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hg)))
      ((TauCeti.QuadraticMap.orthogonalGroup Q).inv_mem
        (TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr hh))
  · intro g h hg hh
    rw [heq]
    exact ZS.commutator_mem_closure_classRefl (by decide) hd hQ hc hg hh

theorem qTwoGlobLin_slpm {m : ℕ} (hm : 5 ≤ m)
    (hLM : QTwoLocalModel m Bs L x)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hSL : ∀ g : ↥U ≃ₗ[ZMod 3] ↥U,
      g ∈ Abar ↔ (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1)) : False := by
  letI : Finite V := qTwoGlobLin_finite (ι := ι)
  letI : Module.Finite (ZMod 3) U := Module.Finite.of_finite
  let z := LinearEquiv.det (LinearEquiv.neg (ZMod 3) : ↥U ≃ₗ[ZMod 3] ↥U)
  have hz : z = 1 ∨ z = -1 := by
    rcases CFSG.LinearAlgebra.zmod_three_eq_one_or_neg_one
      (z : ZMod 3) (Units.ne_zero z) with h | h
    · exact Or.inl (Units.ext h)
    · exact Or.inr (Units.ext h)
  have htop := hD.2.2.2.2.2.2 ((hSL _).mpr hz)
  have hd : Module.finrank (ZMod 3) U = m := by
    rw [htop, finrank_top]
    exact qTwoGlobLin_finrank (ι := ι) hLM
  have hlower := ZS.pow_le_card_of_sl_le hd Abar
    (fun g hg => (hSL g).mpr (Or.inl hg))
  have hupper := qTwoGlobBnd_actionCard_le hLM hD
  rw [hd] at hupper
  have hgrowth := qTwoGlobGrw_sl_order hm
  nlinarith

theorem qTwoGlobLin_orth {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {m N : ℕ} (hm : 5 ≤ m) (hN1 : m + 1 ≤ N) (hN2 : N ≤ m + 2)
    (hA : GGWeylOfType 3 (CoxeterMatrix.A (N - 1)) (ggAutomizerJoin L Bs 𝒦))
    (hLM : QTwoLocalModel m Bs L x)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hdim : Module.finrank (ZMod 3) U = m ∨ Module.finrank (ZMod 3) U + 1 = m)
    (Q : QuadraticForm (ZMod 3) U) (hQ : (qTwoPolar Q).Nondegenerate)
    (hcase : (∀ g, g ∈ Abar ↔ ZS.IsIsom 3 Q g) ∨
      (∃ c : ZMod 3, c ≠ 0 ∧ Abar = Subgroup.closure (ZS.ClassRefl 3 Q c))) :
    ZS.LinWeyl 3 Abar := by
  letI : Finite V := qTwoGlobLin_finite (ι := ι)
  letI : Module.Finite (ZMod 3) U := Module.Finite.of_finite
  have hd4 : 4 ≤ Module.finrank (ZMod 3) U := by omega
  by_cases h4 : Module.finrank (ZMod 3) U = 4
  · exact qTwoGlobLin_orth_four hcfg hm hN1 hN2 hA hLM hD hdim Q hQ hcase h4
  have hd5 : 5 ≤ Module.finrank (ZMod 3) U := by omega
  have hle := qTwoGlobFour_orth_le Q hcase
  have hcomm := qTwoGlobLin_orth_commutators (ι := ι) Q hQ hcase hd5
  have hrefl := qTwoGlobLin_exists_refl hcfg (by omega : 2 ≤ N) hA hD
  have hidx := qTwoGlobIdx_orthogonal_le_two_mul_card hQ hd5 Abar hcomm hrefl
  have hupper := qTwoGlobBnd_actionCard_le hLM hD
  have hmle : m ≤ Module.finrank (ZMod 3) U + 1 := by omega
  by_cases h6 : Module.finrank (ZMod 3) U = 6
  · apply False.elim
    apply qTwoGlobIdx_degSix_false hQ h6 Abar hcomm hrefl
    have hmf : m.factorial ≤ (7 : ℕ).factorial := Nat.factorial_le (by omega)
    rw [h6] at hupper
    nlinarith
  by_cases h5 : Module.finrank (ZMod 3) U = 5
  · have hm56 : m = 5 ∨ m = 6 := by omega
    rcases hm56 with hm5 | hm6
    · subst m
      obtain ⟨u, hu, hs⟩ := qTwoGlobLin_distinguished_five hcfg hLM hD h5
      exact False.elim (qTwoGlobOrb_false Q hQ h5 hle hidx hu hs)
    · subst m
      have hfac := qTwoGlobSel_factorial_dvd_card_Abar hcfg (by omega : 1 ≤ N) hA hD
      exact False.elim (qTwoGlobFour_five_factorial Q hQ h5 hle (by omega : 7 ≤ N) hfac)
  · have hd7 : 7 ≤ Module.finrank (ZMod 3) U := by omega
    have hlower := ZS.pow_le_card_of_commutator_isometry_mem (p := 3) (by decide)
      rfl hd5 hQ Abar hcomm
    exact False.elim (qTwoGlobGrw_excl hd7 hmle hupper hlower)

theorem qTwo_family_linWeyl
    {G : Type} [Group G] [Finite G]
    {B Bs L D J : Subgroup G} {x : G} {𝒦 : Finset (Subgroup G)}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V}
    {U : Submodule (ZMod 3) V} {Abar : Subgroup (↥U ≃ₗ[ZMod 3] ↥U)}
    {ρ : ↥(ggAInf 3 B Bs x L D J) ≃* ↥Abar}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {m N : ℕ} (hm : 5 ≤ m) (hN1 : m + 1 ≤ N) (hN2 : N ≤ m + 2)
    (hA : GGWeylOfType 3 (CoxeterMatrix.A (N - 1)) (ggAutomizerJoin L Bs 𝒦))
    (hLM : QTwoLocalModel m Bs L x)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hdim : Module.finrank (ZMod 3) U = m ∨ Module.finrank (ZMod 3) U + 1 = m)
    (hFam : ZS.Family 3 Abar) :
    ZS.LinWeyl 3 Abar := by
  letI : Finite V := qTwoGlobLin_finite (ι := ι)
  letI : Module.Finite (ZMod 3) U := Module.Finite.of_finite
  have hd4 : 4 ≤ Module.finrank (ZMod 3) U := by omega
  cases hFam with
  | weyl hW => exact hW
  | slpm hSL => exact False.elim (qTwoGlobLin_slpm hm hLM hD hSL)
  | orth Q hQ hO =>
    exact qTwoGlobLin_orth hcfg hm hN1 hN2 hA hLM hD hdim Q hQ (Or.inl hO)
  | orthClass Q c hQ hc hO =>
    exact qTwoGlobLin_orth hcfg hm hN1 hN2 hA hLM hD hdim Q hQ (Or.inr ⟨c, hc, hO⟩)
  | gmmn f i₀ i₁ ζ t hi ht hζ hO =>
    exact False.elim (qTwo_family_imprimitive_excl f i₀ i₁ ζ t hi (Or.inl ⟨ht, hζ, hO⟩))
  | g2mmn f i₀ i₁ ζ t hi ht hζ hO =>
    exact False.elim (qTwo_family_imprimitive_excl f i₀ i₁ ζ t hi (Or.inr ⟨ht, hζ, hO⟩))
  | exc k hadm hdeg hord hcen hmax hclass hmodel =>
    have hk := qTwo_family_exc_excl k hadm hD.2.2.1 hdeg hd4 hcen
    subst k
    exact False.elim (qTwo_family_H4_excl hdeg hord)
  | h4 hadm hdeg _ hneg hmax hclass =>
    exact False.elim (qTwoGlobLin_not_h4 hm hLM hD hdeg hneg)

theorem qTwoGlobLin_ainf_weyl {𝒦 : Finset (Subgroup G)}
    (hcfg : GGSecFiveRouteCfg 3 B Bs x L D J 𝒦)
    {m N : ℕ} (hm : 5 ≤ m) (hN1 : m + 1 ≤ N) (hN2 : N ≤ m + 2)
    (hA : GGWeylOfType 3 (CoxeterMatrix.A (N - 1)) (ggAutomizerJoin L Bs 𝒦))
    (hLM : QTwoLocalModel m Bs L x)
    (hD : GGSecFiveBarData 3 B Bs x L D J ι U Abar ρ)
    (hdim : Module.finrank (ZMod 3) U = m ∨ Module.finrank (ZMod 3) U + 1 = m)
    (hFam : ZS.Family 3 Abar) : GGWeylReflectionGroup 3 (ggAInf 3 B Bs x L D J) :=
  ggSecFive_weyl_of_linWeyl hD
    (qTwo_family_linWeyl hcfg hm hN1 hN2 hA hLM hD hdim hFam)

end CFSG.StandardType.QTwo
end

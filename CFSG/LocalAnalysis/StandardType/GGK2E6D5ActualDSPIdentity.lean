module

public import CFSG.LocalAnalysis.StandardType.GGK2E6D5DSPCard

public section

namespace CFSG.StandardType

open Module CFSG.StandardType.HdRo7D CFSG.StandardType.HdRo7C

theorem d5_actual_AL_eq_DSP
    {G : Type} [Group G] {Bs : Subgroup G} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] (ι : Additive ↥Bs ≃+ V)
    (b : Module.Basis (Fin 6) (ZMod 3) V)
    (AL : Subgroup (MulAut ↥Bs))
    (f : (ggCoxeterMatrixD 5).Group ≃* AL)
    (φ : Fin 5 → MulAut ↥Bs)
    (hf : ∀ i : Fin 5,
      (f ((ggCoxeterMatrixD 5).simple i) : MulAut ↥Bs) = φ i)
    (hclos : AL = Subgroup.closure (Set.range φ))
    (hC2 : ∀ i : Fin 5, C2SP 3 b (ggLin (p := 3) ι (φ i)))
    (hR : ∀ i : Fin 5, GGIsReflection 3 (φ i)) :
    ∀ a : V ≃ₗ[ZMod 3] V,
      DSP 3 b a ↔ a ∈ AL.map (ggLin (p := 3) ι) := by
  classical
  let mapAL : Subgroup (V ≃ₗ[ZMod 3] V) := AL.map (ggLin (p := 3) ι)
  let P : Subgroup (V ≃ₗ[ZMod 3] V) := DSPSubgroup 3 b
  have hgen : ∀ i : Fin 5, DSP 3 b (ggLin (p := 3) ι (φ i)) :=
    d5_actual_simple_dsp ι b AL f φ hf hC2 hR
  have hle : mapAL ≤ P := by
    intro x hx
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp (by simpa [mapAL] using hx)
    exact d5_actual_AL_le_DSP ι b AL φ hclos hgen a ha
  have hcardAL : Nat.card AL = 1920 := by
    calc Nat.card AL = Nat.card (ggCoxeterMatrixD 5).Group :=
          (Nat.card_congr f.toEquiv).symm
      _ = 2 ^ (5 - 1) * Nat.factorial 5 := CFSG.StandardType.OrthF3.card_coxeterD_eq 5 (by norm_num)
      _ = 1920 := by norm_num
  have hcardMap : Nat.card mapAL = 1920 := by
    calc Nat.card mapAL = Nat.card AL :=
          (Nat.card_congr (Subgroup.equivMapOfInjective AL (ggLin (p := 3) ι)
            (ggLin_injective (p := 3) ι)).toEquiv).symm
      _ = 1920 := hcardAL
  haveI : Fintype V := Fintype.ofEquiv (Fin 6 → ZMod 3) b.equivFun.symm.toEquiv
  haveI : Finite (V → V) := inferInstance
  haveI : Finite (V ≃ₗ[ZMod 3] V) := Finite.of_injective
    (fun e : V ≃ₗ[ZMod 3] V => (e : V → V))
    (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  haveI : Finite P := inferInstance
  have hcardP : Nat.card P ≤ 1920 := card_dspSubgroup_le b
  have hcardPle : Nat.card P ≤ Nat.card mapAL := by
    rw [hcardMap]
    exact hcardP
  have heq : mapAL = P := Subgroup.eq_of_le_of_card_ge hle hcardPle
  intro a
  constructor
  · intro ha
    change a ∈ mapAL
    rw [heq]
    exact ha
  · intro ha
    change a ∈ mapAL at ha
    rw [heq] at ha
    exact ha

end CFSG.StandardType

end

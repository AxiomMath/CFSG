module

public import CFSG.LocalAnalysis.StandardType.StarFour.Shape
public import CFSG.LocalAnalysis.StandardType.StarFour.ShapeThree
public import CFSG.LocalAnalysis.StandardType.StarFour.ShapeFieldExt
public import CFSG.LocalAnalysis.StandardType.StarFour.Items123
public import CFSG.LocalAnalysis.StandardType.StarFour.ItemsK
public import CFSG.LocalAnalysis.StandardType.StarFour.ItemFourFrame

public section

namespace CFSG.StandardType.StarFour

open CFSG.Assembly CFSG.Blueprint CFSG.StandardType CFSG.Open

variable {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [AddCommGroup V] [Module F V]
  [Module.Finite F V] {X : Type} [Group X]

theorem starFour_of_vlevel
    {f : ℕ} (hF : Nat.card F = 2 ^ f)
    (hcop : Nat.Coprime (Module.finrank F V) (Nat.card F - 1)) [Finite X]
    (ψ : SpecialLinearGroup F V →* X) (hψ : Function.Injective ψ) (p : ℕ) (hp : p.Prime)
    (hp2 : p ≠ 2) (B₁ D J : Subgroup X) (hat : B₁ →* SpecialLinearGroup F V)
    (hhat : ∀ (b : B₁) (u : SpecialLinearGroup F V),
      (b : X) * ψ u * (b : X)⁻¹ = ψ (hat b * u * (hat b)⁻¹))
    (hElem : IsElemAbelian p B₁) (hcard : p ^ 4 ≤ Nat.card B₁) (hDB : D ≤ B₁)
    (hDcard : Nat.card D = p ^ 2) (hB₁C : B₁ ⊓ Subgroup.centralizer (J : Set X) = D)
    (hJ : CFSG.Assembly.IsComponentOf J (ψ.range ⊓ Subgroup.centralizer (D : Set X)))
    (hfe : GGSixLSevenFieldExtCase J .PSL f) :
    ∃ R J₀ : Subgroup X, R ≤ J ∧ R ≠ ⊥ ∧ IsPGroup 2 R ∧ J₀ ≤ J ∧
      pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) ⊔ J₀ = ψ.range ∧
      (∀ e ∈ D, e ≠ 1 → ∀ K : Subgroup X, K ≤ ψ.range →
        CFSG.Assembly.IsComponentOf K (Subgroup.centralizer {e}) → J ≤ K → K ≠ J →
        Odd (Nat.card (Subgroup.center ↥K)) → GGRootInnerAt K R ∧ GGRootNoCentralAt K R) ∧
      (∀ Y : Subgroup X, IsPGroup 2 Y → Y ≤ Subgroup.normalizer (ψ.range : Set X) →
        Y ≤ Subgroup.normalizer (R : Set X) →
        ⁅Y, ψ.range ⊓ Subgroup.normalizer (R : Set X)⁆ ≤
          pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
        Y ≤ ψ.range ⊔ Subgroup.centralizer (ψ.range : Set X)) ∧
      (∀ U : Subgroup X, ggCenterOf (pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X))) ≤ U →
        U ≤ pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
        U ≠ pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) →
        ¬ pCoreOf 2 (ψ.range ⊓ Subgroup.normalizer (R : Set X)) ≤
          Subgroup.centralizer (U : Set X) →
        ψ.range ⊓ Subgroup.normalizer (R : Set X) ≤ Subgroup.normalizer (U : Set X) →
        ∀ g ∈ Subgroup.centralizer (J : Set X), g ∈ Subgroup.normalizer (U : Set X) →
          ∃ h ∈ ψ.range, g * h⁻¹ ∈ Subgroup.centralizer ((J ⊔ U : Subgroup X) : Set X)) := by
  classical
  have hp_odd : Odd p := hp.odd_of_ne_two hp2
  have hDodd : Odd (Nat.card D) := by
    rw [hDcard]
    exact hp_odd.pow (n := 2)
  have hpF : (p : F) ≠ 0 := by
    intro h0
    have h2dvd : 2 ∣ p := (CharP.cast_eq_zero_iff F 2 p).mp h0
    exact hp_odd.not_two_dvd_nat h2dvd
  have hD0 : (Nat.card D : F) ≠ 0 := by
    rw [hDcard, Nat.cast_pow]
    exact pow_ne_zero 2 hpF
  have hDab : ∀ a ∈ D, ∀ b ∈ D, a * b = b * a := by
    intro a ha b hb
    have hcomm := hElem.1.is_comm.comm ⟨a, hDB ha⟩ ⟨b, hDB hb⟩
    simpa using congrArg Subtype.val hcomm
  obtain ⟨P, instP, η, fr, i, hη, hgood, hJψ⟩ :=
    exists_frame_of_component ψ hψ B₁ D J hat hhat hDB hDab hD0 hJ
  letI : CommGroup P := instP
  have hm : 3 ≤ fr.m i :=
    three_le_of_shape η fr i hgood ψ hψ p hp hp2 B₁ D J hat hhat hElem hcard hDB hDcard hη
      hJψ hB₁C
  have hc : 2 ≤ Module.finrank F (fr.E i) :=
    two_le_finrank_of_fieldExt η fr i hm ψ hψ J hJψ f hF hfe
  have hm2 : 2 ≤ fr.m i := by omega
  have key := items_of_whole η fr i hm hc ψ hψ
  have hkey2 := rootInnerNoCentral_of_component η fr i hm hc ψ hψ B₁ D hat hhat hDB hη hDodd
  have hkey4 := exists_mem_range_mul_inv_mem_centralizer η fr i hm hc hcop ψ hψ
  refine ⟨(fr.blockRoot i hm2).map ψ, (fr.blockJ0 i hm2).map ψ,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  ·
    rw [hJψ]
    exact Subgroup.map_mono ((fr.blockRoot_le_blockJ0 i hm2).trans
      (fr.blockJ0_le_slOnBlock i hm2))
  ·
    intro hbot
    rw [Subgroup.map_eq_bot_iff_of_injective _ hψ] at hbot
    exact fr.blockRoot_ne_bot i hm2 hbot
  ·
    exact (fr.isPGroup_blockRoot i hm2).map ψ
  ·
    rw [hJψ]
    exact Subgroup.map_mono (fr.blockJ0_le_slOnBlock i hm2)
  ·
    exact key.1
  ·
    intro e he _ K hK hcomp hJK hKJ _
    have hJK' : (fr.slOnBlock i).map ψ ≤ K := by rwa [hJψ] at hJK
    have hKJ' : K ≠ (fr.slOnBlock i).map ψ := by rwa [hJψ] at hKJ
    exact hkey2 e he K hK hcomp hJK' hKJ'
  ·
    exact key.2.2.2
  ·
    intro U hU₁ hU₂ hU₃ hU₄ hU₅ g hgJ hgU
    rw [hJψ] at hgJ ⊢
    exact hkey4 U hU₁ hU₂ hU₃ hU₄ hU₅ g hgJ hgU

end CFSG.StandardType.StarFour

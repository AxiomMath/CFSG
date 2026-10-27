module

public import CFSG.Quasithin.Vol2.GoldschmidtSevenFrattini
public import CFSG.Quasithin.Vol2.GoldschmidtSevenSL

public section

namespace CFSG.Quasithin.H13.Seven

open Matrix
open CFSG.ComponentClassification.CatalogueBGraphForm (slGraphAut)

variable {X : Type} [Group X]

theorem conj_ker_le {Y : Subgroup X} {m : ℕ} (hm : m = 3 ∨ m = 4)
    (ρ : ↥Y →* SpecialLinearGroup (Fin m) (ZMod 2)) (hρ : Function.Surjective ρ)
    (hK : IsPGroup 2 ρ.ker) {t : X} (ht : t ∈ Subgroup.normalizer (Y : Set X)) :
    ρ.ker.map (Y.normalizerMonoidHom ⟨t, ht⟩).toMonoidHom ≤ ρ.ker := by
  set c : ↥Y ≃* ↥Y := Y.normalizerMonoidHom ⟨t, ht⟩
  have hn : (ρ.ker.map c.toMonoidHom).Normal :=
    Subgroup.Normal.map inferInstance c.toMonoidHom c.surjective
  have hp : IsPGroup 2 (ρ.ker.map c.toMonoidHom) := hK.map c.toMonoidHom
  have : ((ρ.ker.map c.toMonoidHom).map ρ).Normal := hn.map ρ hρ
  have hbot := eq_bot_of_normal_isPGroup_two hm ((ρ.ker.map c.toMonoidHom).map ρ) (hp.map ρ)
  intro x hx
  have hmem : ρ x ∈ (ρ.ker.map c.toMonoidHom).map ρ := Subgroup.mem_map_of_mem ρ hx
  rw [hbot, Subgroup.mem_bot] at hmem
  exact hmem

theorem induced_graph_or_inner {Y : Subgroup X} {m : ℕ} (hm : m = 3 ∨ m = 4)
    (ρ : ↥Y →* SpecialLinearGroup (Fin m) (ZMod 2)) (hρ : Function.Surjective ρ)
    (hK : IsPGroup 2 ρ.ker) {t : X} (ht : t ∈ Subgroup.normalizer (Y : Set X)) :
    (∃ y₀ : ↥Y, ∀ y y' : ↥Y, (y' : X) = t * y * t⁻¹ → ρ y' = ρ (y₀ * y * y₀⁻¹)) ∨
      ∃ yA : ↥Y, ∀ y y' : ↥Y, (y' : X) = (yA : X)⁻¹ * t * y * ((yA : X)⁻¹ * t)⁻¹ →
        ρ y' = slGraphAut m (ZMod 2) (ρ y) := by
  set c : ↥Y ≃* ↥Y := Y.normalizerMonoidHom ⟨t, ht⟩ with hc
  have hcy : ∀ y : ↥Y, ((c y : ↥Y) : X) = t * y * t⁻¹ := fun y => rfl
  have ht' : t⁻¹ ∈ Subgroup.normalizer (Y : Set X) := inv_mem ht
  have hker : ρ.ker.map c.toMonoidHom = ρ.ker := by
    refine le_antisymm (conj_ker_le hm ρ hρ hK ht) ?_
    intro x hx
    have h1 := conj_ker_le hm ρ hρ hK ht' ⟨x, hx, rfl⟩
    refine ⟨Y.normalizerMonoidHom ⟨t⁻¹, ht'⟩ x, h1, ?_⟩
    apply Subtype.ext
    show t * (t⁻¹ * (x : X) * t⁻¹⁻¹) * t⁻¹ = x
    group
  let e : (↥Y ⧸ ρ.ker) ≃* SpecialLinearGroup (Fin m) (ZMod 2) :=
    QuotientGroup.quotientKerEquivOfSurjective ρ hρ
  let β : MulAut (SpecialLinearGroup (Fin m) (ZMod 2)) :=
    e.symm.trans ((QuotientGroup.congr ρ.ker ρ.ker c hker).trans e)
  have hβ : ∀ y : ↥Y, β (ρ y) = ρ (c y) := by
    intro y
    have h1 : e.symm (ρ y) = (y : ↥Y ⧸ ρ.ker) := by
      rw [MulEquiv.symm_apply_eq]
      rfl
    show e (QuotientGroup.congr ρ.ker ρ.ker c hker (e.symm (ρ y))) = ρ (c y)
    rw [h1]
    rfl
  rcases mulAut_eq_conj_or_graph (by omega) β with ⟨A, hA⟩ | ⟨A, hA⟩
  · left
    obtain ⟨y₀, hy₀⟩ := hρ A
    refine ⟨y₀, fun y y' hy' => ?_⟩
    have hyy : y' = c y := Subtype.ext (hy'.trans (hcy y).symm)
    rw [hyy, ← hβ, hA, MulAut.conj_apply, map_mul, map_mul, map_inv, hy₀]
  · right
    obtain ⟨yA, hyA⟩ := hρ A
    refine ⟨yA, fun y y' hy' => ?_⟩
    have hyy : y' = yA⁻¹ * c y * yA := by
      apply Subtype.ext
      rw [hy', Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hcy]
      group
    rw [hyy, map_mul, map_mul, map_inv, ← hβ, hA, hyA, MulAut.mul_apply, MulAut.conj_apply]
    group

theorem innerOn_of_not_real [Finite X] (h49 : ¬ 49 ∣ Nat.card X)
    (hreal : ∀ x g : X, orderOf x = 7 → g * x * g⁻¹ ≠ x⁻¹)
    {Y : Subgroup X} {m : ℕ} (hm : m = 3 ∨ m = 4)
    (ρ : ↥Y →* SpecialLinearGroup (Fin m) (ZMod 2)) (hρ : Function.Surjective ρ)
    (hK : IsPGroup 2 ρ.ker) {t : X} (ht : t ∈ Subgroup.normalizer (Y : Set X)) :
    ∃ y₀ : ↥Y, ∀ y y' : ↥Y, (y' : X) = t * y * t⁻¹ → ρ y' = ρ (y₀ * y * y₀⁻¹) := by
  rcases induced_graph_or_inner hm ρ hρ hK ht with h | ⟨yA, hyA⟩
  · exact h
  · exfalso
    obtain ⟨a, ha, hia⟩ := exists_symmetric_seven hm
    have hn : (yA : X)⁻¹ * t ∈ Subgroup.normalizer (Y : Set X) :=
      Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.le_normalizer yA.2)) ht
    obtain ⟨x, g, hx, hg⟩ := exists_inverting_of_induced h49 ρ hρ hn (slGraphAut m (ZMod 2))
      (fun y y' hy' => hyA y y' hy') ha hia
    exact hreal x g hx hg

end CFSG.Quasithin.H13.Seven

module

public import CFSG.LieType.Universal.RootData
public import CFSG.LieType.Steinberg.Extras
public import CFSG.Timmesfeld.ARS.CaseEWeight
import CFSG.LieType.Steinberg.OfCartan
import CFSG.LieType.RootSystem.Parabolic

public section

namespace CFSG.StandardType

open CFSG.LieType.RootSystem CFSG.LieType.Universal CFSG.LieType.Steinberg CFSG.Timmesfeld.ARS

open scoped commutatorElement

private theorem pair_add_smul {I : Type} [Fintype I] (A : Matrix I I ℤ) (u x y : I → ℤ)
    (a b : ℤ) :
    cartanPair A u (a • x + b • y) = a * cartanPair A u x + b * cartanPair A u y := by
  simp only [cartanPair, Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_mul,
    Finset.sum_add_distrib, Finset.mul_sum, mul_assoc]

private theorem pair_zero {I : Type} [Fintype I] (A : Matrix I I ℤ) (u : I → ℤ) :
    cartanPair A u 0 = 0 := by
  simp [cartanPair]

private theorem pair_neg_left {I : Type} [Fintype I] (A : Matrix I I ℤ) (u v : I → ℤ) :
    cartanPair A (-u) v = -cartanPair A u v := by
  simp [cartanPair, map_neg, Finset.sum_neg_distrib]

theorem ggKGCent_root_trichotomy {I : Type} [Fintype I] [DecidableEq I] {A : Matrix I I ℤ}
    (hA : TauCeti.IsFiniteType A) (hpd : (A.map (Int.cast : ℤ → ℚ)).PosDef)
    (w : (coxeterMatrix hA).Group) (i : I) {γ : I → ℤ} (hγ : γ ∈ roots hA ∅)
    (h1 : γ ≠ weylAction hA w (Pi.single i 1)) (h2 : γ ≠ -weylAction hA w (Pi.single i 1)) :
    weylAction hA w (Pi.single i 1) + γ ∈ roots hA ∅ ∨
      weylAction hA w (Pi.single i 1) - γ ∈ roots hA ∅ ∨
      cartanPair A (weylAction hA w (Pi.single i 1)) γ = 0 := by
  have hsymm := cartan_symm_of_posDef hpd
  set γ' := weylAction hA w⁻¹ γ
  have hγw : γ = weylAction hA w γ' := (weylAction_apply_inv_apply hA w γ).symm
  have hr : γ' ∈ roots hA ∅ := weylAction_mem_roots hA w⁻¹ hγ
  have hne1 : γ' ≠ Pi.single i 1 := fun h => h1 (by rw [hγw, h])
  have hne2 : γ' ≠ -Pi.single i 1 := fun h => h2 (by rw [hγw, h, map_neg])
  have hle := coroot_le_one hA hpd hr hne1
  have hge := neg_one_le_coroot hA hpd hr hne2
  have hs : weylAction hA (w * (coxeterMatrix hA).toCoxeterSystem.simple i) γ' ∈ roots hA ∅ :=
    weylAction_mem_roots hA _ hr
  rw [weylAction_mul_apply, weylAction_simple, reflection_apply_coroot, map_sub, map_smul,
    ← hγw] at hs
  have hpair : cartanPair A (weylAction hA w (Pi.single i 1)) γ = coroot A i γ' := by
    rw [hγw, cartanPair_weylAction hA hsymm, cartanPair_comm hsymm, cartanPair_single]
  rcases (show coroot A i γ' = -1 ∨ coroot A i γ' = 0 ∨ coroot A i γ' = 1 by omega) with
    hc | hc | hc
  · left
    rw [hc, neg_one_smul, sub_neg_eq_add, add_comm] at hs
    exact hs
  · exact Or.inr (Or.inr (hpair.trans hc))
  · right
    left
    rw [hc, one_smul] at hs
    have h := CFSG.LieType.Steinberg.OfCartan.neg_mem_roots hA hs
    rwa [neg_sub] at h

private theorem commute_of_pair_zero {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H)
    (hdiv : D.divisible = ∅) (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {β γ : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (hγ : γ ∈ D.roots)
    (h0 : cartanPair D.cartan β γ = 0) :
    ∀ a ∈ D.rootGroup β, ∀ b ∈ D.rootGroup γ, a * b = b * a := by
  have hsymm := cartan_symm_of_posDef hpd
  have hβ' : β ∈ roots D.isFiniteType ∅ := hdiv ▸ hβ
  have hγ' : γ ∈ roots D.isFiniteType ∅ := hdiv ▸ hγ
  have hββ : cartanPair D.cartan β β = 2 := cartanForm_eq_two D.isFiniteType hsymm hβ'
  have hγγ : cartanPair D.cartan γ γ = 2 := cartanForm_eq_two D.isFiniteType hsymm hγ'
  have hγβ : cartanPair D.cartan γ β = 0 := by rw [cartanPair_comm hsymm, h0]
  have hlin : LinIndepPair β γ := by
    intro a b hab
    have e1 := pair_add_smul D.cartan β β γ a b
    have e2 := pair_add_smul D.cartan γ β γ a b
    rw [hab, pair_zero, hββ, h0] at e1
    rw [hab, pair_zero, hγβ, hγγ] at e2
    omega
  have hcone : openCone D.roots β γ = ∅ := by
    ext ε
    simp only [Set.mem_empty_iff_false, iff_false]
    rintro ⟨hε, a, b, ha, hb, rfl⟩
    have hε' : a • β + b • γ ∈ roots D.isFiniteType ∅ := hdiv ▸ hε
    have hq := cartanForm_eq_two D.isFiniteType hsymm hε'
    have he : a • β + b • γ = (a : ℤ) • β + (b : ℤ) • γ := by
      rw [natCast_zsmul, natCast_zsmul]
    rw [he, ← cartanPair_self, pair_add_smul, cartanPair_comm hsymm _ β,
      cartanPair_comm hsymm _ γ, pair_add_smul, pair_add_smul, hββ, h0, hγβ, hγγ] at hq
    have ha' : (1 : ℤ) ≤ a := by omega
    have hb' : (1 : ℤ) ≤ b := by omega
    nlinarith [ha', hb']
  intro a ha b hb
  have hmem := hext.commutator_mem β hβ γ hγ hlin a ha b hb
  have hbot : ⁅a, b⁆ = 1 := by simpa [hcone] using hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp hbot

theorem ggKGCent_rootGroup_commute {K : Type*} [Group K] {D : UniversalRootDatum K}
    {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} (hext : SteinbergExtras D n H)
    (hdiv : D.divisible = ∅) (hpd : (D.cartan.map (Int.cast : ℤ → ℚ)).PosDef)
    {β γ : Fin D.rank → ℤ} (hβ : β ∈ D.roots) (hγ : γ ∈ D.roots)
    (h0 : cartanPair D.cartan β γ = 0) :
    (∀ a ∈ D.rootGroup β, ∀ b ∈ D.rootGroup γ, a * b = b * a) ∧
      ∀ a ∈ D.rootGroup (-β), ∀ b ∈ D.rootGroup γ, a * b = b * a :=
  ⟨commute_of_pair_zero hext hdiv hpd hβ hγ h0,
    commute_of_pair_zero hext hdiv hpd (OfCartan.neg_mem_roots D.isFiniteType hβ) hγ
      (by rw [pair_neg_left, h0, neg_zero])⟩

end CFSG.StandardType

end

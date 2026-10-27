module

public import CFSG.Quasithin.Background.HSp4Alpha
public import CFSG.Quasithin.Background.HSp4Bridge
public import CFSG.Quasithin.Background.HSp4A6Pair
public import Certificates.Certificate7067

public section

namespace CFSG.Quasithin

namespace H

open CFSG.Open CFSG.Assembly.LowTwoRank Matrix Equiv PairG

theorem isPGroup_of_equiv_pairMod {V : Type*} [CommGroup V] {K : Type} [Field K] [Finite K]
    {n : ℕ} (hK : Nat.card K = 2 ^ n) (e : V ≃* PairMod (Fin 2 ⊕ Fin 2) K) : IsPGroup 2 V := by
  refine IsPGroup.of_card (n := 8 * n) ?_
  rw [Nat.card_congr e.toEquiv, Nat.card_prod, card_stdMod, hK, Fintype.card_sum,
    Fintype.card_fin, ← pow_mul, ← pow_add]
  congr 1
  ring

namespace Sp4

theorem H7_Sp4Pair_alpha {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} {n : ℕ} (hn : 2 ≤ n) (hreal : BinaryNaturalSp4 H V₁ ⊥ n) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom))
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    ¬ IsFOneModule M ∧ alphaH M = 1 ∧ ¬ IsFFModule M := by
  obtain ⟨K, _, _, hK, hreal'⟩ := hreal
  have : CharP K 2 := CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic
    Nat.prime_two (by omega : 1 ≤ n) hK
  obtain ⟨e, he⟩ := Sp4.exists_pair_model hreal' hφ hinf hsup hniso
  have : Finite (PairMod (Fin 2 ⊕ Fin 2) K) := Finite.of_equiv V e.toEquiv
  have h2 := map_le_pairNormSp e he hMN
  have hF : ¬ IsFOneModule M := by
    rw [← isFOneModule_map_congrHom e]
    exact not_isFOneModule (by omega) hK h2
  exact ⟨hF, alphaH_eq_one_of_not_isFOneModule hF,
    not_isFFModule_of_not_isFOneModule (isPGroup_of_equiv_pairMod hK e) hF⟩

end Sp4

namespace Sp4A6

theorem exists_model
    {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : AlternatingNatural H V₁ ⊥ 6) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom))
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    ∃ e : V ≃* PairMod (Fin 2 ⊕ Fin 2) (ZMod 2),
      M.map (congrHom e) ≤ Sp4.pairNormSp (ZMod 2) := by
  obtain ⟨π, hπ⟩ := hreal
  have hπs : Function.Surjective π := hπ.1
  have hU : ∀ h : ↥H, ∀ u ∈ V₁, (h : MulAut V) u ∈ V₁ := hπ.2.2.2.1
  obtain ⟨e₁, he₁⟩ := exists_natural hπ
  set π' : ↥Γ₆ →* ↥H := π.comp psiEquiv.symm.toMonoidHom with hπ'
  have hπ's : Function.Surjective π' := hπs.comp psiEquiv.symm.surjective
  have he₁' : ∀ (γ : ↥Γ₆) (u : ↥V₁) (hu : ((π' γ : ↥H) : MulAut V) (u : V) ∈ V₁),
      e₁ ⟨_, hu⟩ = matAut (γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) (e₁ u) := by
    intro γ u hu
    have h := he₁ (psiEquiv.symm γ) u hu
    have e : psiHom ((psiEquiv.symm γ : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) =
        (γ : GL (Fin 2 ⊕ Fin 2) (ZMod 2)) := by
      have := congrArg Subtype.val (psiEquiv.apply_symm_apply γ)
      exact this
    rw [← e]
    exact h
  obtain ⟨e, he⟩ := PairG.exists_pair_model tau₆ π' hπ's hU e₁ he₁' hAut hφ hinf hsup hniso
  exact ⟨e, (PairG.map_le_pairNorm tau₆ e he hMN).trans pairNorm_le⟩

theorem H7_A6Pair_alpha
    {V : Type*} [CommGroup V] [Finite V] {H M : Subgroup (MulAut V)}
    {V₁ : Subgroup V} (hreal : AlternatingNatural H V₁ ⊥ 6) {φ : MulAut V}
    (hφ : φ ∈ Subgroup.normalizer (H : Set (MulAut V)))
    (hinf : V₁ ⊓ V₁.map φ.toMonoidHom = ⊥) (hsup : V₁ ⊔ V₁.map φ.toMonoidHom = ⊤)
    (hniso : ¬ Pair.IsoMod H V₁ (V₁.map φ.toMonoidHom))
    (hMN : M ≤ Subgroup.normalizer (H : Set (MulAut V))) :
    ¬ IsFOneModule M ∧ alphaH M = 1 ∧ ¬ IsFFModule M := by
  obtain ⟨e, h2⟩ := exists_model hreal hφ hinf hsup hniso hMN
  have : Finite (PairMod (Fin 2 ⊕ Fin 2) (ZMod 2)) := Finite.of_equiv V e.toEquiv
  have hK : Nat.card (ZMod 2) = 2 ^ 1 := by rw [Nat.card_zmod, pow_one]
  have hF : ¬ IsFOneModule M := by
    rw [← isFOneModule_map_congrHom e]
    exact Sp4.not_isFOneModule le_rfl hK h2
  exact ⟨hF, alphaH_eq_one_of_not_isFOneModule hF,
    not_isFFModule_of_not_isFOneModule (isPGroup_of_equiv_pairMod hK e) hF⟩

end Sp4A6

end H

end CFSG.Quasithin

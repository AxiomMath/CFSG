module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7CKCoordBWeight
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpFrame
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoKey
public import CFSG.LocalAnalysis.StandardType.GGSixA6InsideSpTorus
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CCoordDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentySpCoord
public import CFSG.LocalAnalysis.StandardType.GGHdRo7CDefs

public section

namespace CFSG.StandardType.HdRo7C

open CFSG.StandardType
open CFSG.Open
open CFSG.Assembly
open CFSG.RankThree.Classical CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KCPrimary
open Polynomial Module

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

theorem hdRo7CKCoordAux_spFixedDim_conj {r : ℕ} {K : Type} [Field K]
    (g t : StatedSp r K) : spFixedDim (g * t * g⁻¹) = spFixedDim t := by
  let u : (Fin r ⊕ Fin r → K) ≃ₗ[K] (Fin r ⊕ Fin r → K) :=
    (spLin r K g).toLinearEquiv
  have hcoe : ((spLin r K g : LinearMap.GeneralLinearGroup K (Fin r ⊕ Fin r → K)) :
      Module.End K (Fin r ⊕ Fin r → K)) = (u : _ →ₗ[K] _) := rfl
  have hker : KCPrimary.primaryComponent (spEnd (g * t * g⁻¹)) (X - 1) =
      (KCPrimary.primaryComponent (spEnd t) (X - 1)).map ((u : _ →ₗ[K] _)) := by
    ext v
    rw [KCPrimary.mem_primaryComponent, Submodule.mem_map_equiv, KCPrimary.mem_primaryComponent]
    have key : (aeval (spEnd (g * t * g⁻¹)) (X - 1 : K[X])) v = u (spEnd t (u.symm v)) - v := by
      rw [Polynomial.aeval_sub, Polynomial.aeval_X, map_one]
      change spEnd (g * t * g⁻¹) v - v = u (spEnd t (u.symm v)) - v
      rw [ChoiceTwo.spEnd_mul_apply, ChoiceTwo.spEnd_mul_apply]
      have h1 : spEnd g = (u : _ →ₗ[K] _) := hcoe
      have h2 : spEnd g⁻¹ = (u.symm : (Fin r ⊕ Fin r → K) →ₗ[K] (Fin r ⊕ Fin r → K)) := by
        change (↑(spLin r K g⁻¹) : Module.End K (Fin r ⊕ Fin r → K)) =
          (↑u.symm : Module.End K (Fin r ⊕ Fin r → K))
        rw [map_inv]
        rfl
      rw [h1, h2]
      simp
    rw [key]
    have hR : ((aeval (spEnd t)) (X - 1 : K[X])) (u.symm v) = spEnd t (u.symm v) - u.symm v := by
      rw [Polynomial.aeval_sub, Polynomial.aeval_X, map_one]
      rfl
    rw [hR]
    constructor
    · intro h
      have h' : u (spEnd t (u.symm v)) = u (u.symm v) := by
        rw [sub_eq_zero] at h
        rw [h, u.apply_symm_apply]
      exact sub_eq_zero.mpr (u.injective h')
    · intro h
      have h' : spEnd t (u.symm v) = u.symm v := sub_eq_zero.mp h
      rw [h', u.apply_symm_apply, sub_self]
  rw [spFixedDim, spFixedDim, hker, LinearEquiv.finrank_map_eq]

theorem hdRo7CKCoordAux_spFixedDim_tor_gen {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}
    {L : Type} [Field L] [Algebra K L] [Module.Finite K L] {ζ : L}
    {E : Subgroup (StatedSp n K)} (F : ChoiceTwo.SpFrame K n ζ E)
    (hζ : IsPrimitiveRoot ζ 3) (c : Fin F.s → ZMod 3) :
    spFixedDim (F.tor c) = (F.zeroSet c).card * Module.finrank K L := by
  rw [spFixedDim, F.fix_eq_map hζ, LinearEquiv.finrank_map_eq, ChoiceTwo.finrank_suppSub]

theorem hdRo7CKCoordAux_zeroSet_card_add_suppSet_card {K : Type} [Field K] {n : ℕ}
    {L : Type} [Field L] [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)}
    (F : ChoiceTwo.SpFrame K n ζ E) (c : Fin F.s → ZMod 3) :
    (F.zeroSet c).card + (F.suppSet c).card = F.s := by
  have h := Finset.card_filter_add_card_filter_not (s := Finset.univ)
    (p := fun i : Fin F.s => c i = 0)
  simpa [ChoiceTwo.SpFrame.zeroSet, ChoiceTwo.SpFrame.suppSet, Finset.card_univ,
    Fintype.card_fin] using h

theorem hdRo7CKCoordAux_tor_add {K : Type} [Field K] {n : ℕ} {L : Type} [Field L]
    [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)} (F : ChoiceTwo.SpFrame K n ζ E)
    (hζ3 : ζ ^ 3 = 1) (c c' : Fin F.s → ZMod 3) :
    F.tor (c + c') = F.tor c * F.tor c' := by
  refine ChoiceTwo.ActsAs.eq (F.tor_acts (c + c')) ?_
  refine ((F.tor_acts c).mul (F.tor_acts c')).congr fun d => ?_
  exact (ChoiceTwo.torE_add hζ3 c c' d).symm

theorem hdRo7CKCoordAux_zeta_cube {G : Type} [Group G] {Bs K : Subgroup G}
    (n : ℕ) (τ : (Fin (n + 1) → Multiplicative (ZMod 3)) ≃* ↥Bs)
    {m : ℕ} (φ : StatedSp m (GaloisField 2 1) →* G) (hinj : Function.Injective φ)
    {L : Type} [Field L] [Algebra (GaloisField 2 1) L]
    {ζ : L} {E : Subgroup (StatedSp m (GaloisField 2 1))}
    (F : ChoiceTwo.SpFrame (GaloisField 2 1) m ζ E) (c : Fin F.s → ZMod 3)
    (hE : E = (Bs ⊓ K).comap φ) (hsupp : (F.suppSet c).card = 2) :
    ζ ^ 3 = 1 := by
  have hBs3 : ∀ b : ↥Bs, b ^ 3 = 1 := by
    intro b
    obtain ⟨f, rfl⟩ := τ.surjective b
    rw [← map_pow]
    have hf3 : f ^ 3 = 1 := by
      funext l
      have h3all : ∀ y : Multiplicative (ZMod 3), y ^ 3 = 1 := by decide
      exact h3all (f l)
    rw [hf3, map_one]
  have hE3 : ∀ x ∈ E, x ^ 3 = 1 := by
    intro x hx
    have hφx : (φ x : G) ∈ Bs := by
      have hx' : x ∈ (Bs ⊓ K).comap φ := by rw [← hE]; exact hx
      exact (Subgroup.mem_comap.mp hx').1
    have h3 : (φ x) ^ 3 = 1 := by
      have := congrArg Subtype.val (hBs3 ⟨φ x, hφx⟩)
      simpa using this
    apply hinj
    rw [map_pow, h3, map_one]
  have hne : (F.suppSet c).Nonempty := Finset.card_pos.mp (by rw [hsupp]; norm_num)
  obtain ⟨i₀, -⟩ := hne
  let ui : Fin F.s → ZMod 3 := Pi.single i₀ 1
  have hpow : (F.tor ui) ^ 3 = 1 := hE3 _ (F.tor_mem ui)
  have heq : (spEnd (F.tor ui)) ^ 3 = 1 := by
    rw [← ChoiceTwo.spEnd_pow, hpow, ChoiceTwo.spEnd_one]
  have happ : ∀ a : L,
      spEnd (F.tor ui) (F.Φ (Pi.single i₀ a)) = F.Φ (Pi.single i₀ (ζ * a)) := by
    intro a
    rw [F.tor_acts ui]
    congr 1
    ext j
    by_cases hj : j = i₀
    · subst hj
      simp [ChoiceTwo.torE_apply, ui, Pi.single_eq_same, ZMod.val_one, pow_one]
    · simp [ChoiceTwo.torE_apply, ui, Pi.single_eq_of_ne hj]
  have hv : (spEnd (F.tor ui)) ((spEnd (F.tor ui))
      ((spEnd (F.tor ui)) (F.Φ (Pi.single i₀ (1 : L)))))
      = F.Φ (Pi.single i₀ (1 : L)) := by
    have h := congrArg (fun e : Module.End (GaloisField 2 1)
        (Fin m ⊕ Fin m → GaloisField 2 1) => e (F.Φ (Pi.single i₀ (1 : L)))) heq
    change (spEnd (F.tor ui)) ((spEnd (F.tor ui))
      ((spEnd (F.tor ui)) (F.Φ (Pi.single i₀ (1 : L)))))
      = (1 : Module.End (GaloisField 2 1) (Fin m ⊕ Fin m → GaloisField 2 1))
        (F.Φ (Pi.single i₀ (1 : L))) at h
    simpa using h
  have hvv : F.Φ (Pi.single i₀ (ζ * (ζ * (ζ * 1)))) = F.Φ (Pi.single i₀ (1 : L)) := by
    simpa only [happ] using hv
  have h2 := congrFun (F.Φ.injective hvv) i₀
  have h2' : ζ * (ζ * (ζ * 1)) = 1 := by
    simpa [Pi.single_eq_same] using h2
  calc ζ ^ 3 = ζ * (ζ * (ζ * 1)) := by ring
    _ = 1 := h2'

theorem hdRo7CKCoordAux_tor_zero {K : Type} [Field K] {n : ℕ} {L : Type} [Field L]
    [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)} (F : ChoiceTwo.SpFrame K n ζ E) :
    F.tor 0 = 1 := by
  apply ChoiceTwo.eq_of_spEnd_eq'
  intro v
  obtain ⟨x, rfl⟩ := F.Φ.surjective v
  rw [F.tor_acts 0, ChoiceTwo.torE_zero, ChoiceTwo.spEnd_one_apply]

theorem hdRo7CKCoordAux_tor_injective {K : Type} [Field K] {n : ℕ} {L : Type} [Field L]
    [Algebra K L] {ζ : L} {E : Subgroup (StatedSp n K)} (F : ChoiceTwo.SpFrame K n ζ E)
    (hζ : IsPrimitiveRoot ζ 3) : Function.Injective F.tor := by
  intro c c' h
  apply ChoiceTwo.torE_injective hζ
  intro d
  have h1 := F.tor_acts c d
  have h2 := F.tor_acts c' d
  rw [← h] at h2
  exact F.Φ.injective (h1.symm.trans h2)

end CFSG.StandardType.HdRo7C

end

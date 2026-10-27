module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveRest
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGNsq2QuotNorm
import CFSG.LocalAnalysis.StandardType.GGSecFiveL2SplitOrthA
import CFSG.LocalAnalysis.StandardType.GGTypeABstarFarProofCoxeter
import CFSG.LocalAnalysis.StandardType.GGTBJTypeBFrameChange
import TauCeti.GroupTheory.Coxeter.Geometric

public section

namespace CFSG.StandardType

open SpCoord Multiplicative

variable {G : Type} [Group G] {p : ℕ} {Bs : Subgroup G}

theorem natCard_eq_pow_of_mulEquiv {n : ℕ} (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) :
    Nat.card Bs = p ^ n := by
  rw [Nat.card_congr eta.toEquiv, Nat.card_fun, Nat.card_fin]
  exact congrArg (· ^ n) (Nat.card_zmod p)

private theorem pxA_permAutHom_range (n p : ℕ) :
    (TypeBDatum.permAutHom n p).range = aPermutationFull n p := by
  apply le_antisymm
  · rw [MonoidHom.range_eq_map, ← Equiv.Perm.closure_isSwap (α := Fin n),
      MonoidHom.map_closure, aPermutationFull]
    refine Subgroup.closure_mono ?_
    rintro _ ⟨σ, hσ, rfl⟩
    obtain ⟨a, b, hab, rfl⟩ := hσ
    exact ⟨a, b, hab, rfl⟩
  · rw [aPermutationFull, Subgroup.closure_le]
    rintro _ ⟨a, b, hab, rfl⟩
    exact MonoidHom.mem_range.mpr ⟨Equiv.swap a b, rfl⟩

private theorem pxA_isReflection_coord {n p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {G : Type} [Group G] {Bs : Subgroup G}
    (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) {a b : Fin n} (hab : a ≠ b) :
    GGIsReflection p ((MulAut.congr eta).symm (permAut (p := p) (Equiv.swap a b))) := by
  constructor
  · apply (MulEquiv.map_eq_one_iff (MulAut.congr eta)).mp
    rw [map_pow, MulEquiv.apply_symm_apply, SpCoord.permAut_swap_sq]
  · have hcf := card_fixed_congr eta
      ((MulAut.congr eta).symm (permAut (p := p) (Equiv.swap a b)))
    rw [← hcf]
    simp only [MulEquiv.apply_symm_apply]
    rw [SpCoord.card_fix_permAut_swap hp hp2 hab]
    exact (Nat.card_congr eta.toEquiv).symm

private noncomputable def pxA_permHom {m : ℕ} {A : Subgroup (MulAut ↥Bs)}
    (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p)))
    (hA : A.map (MulAut.congr eta).toMonoidHom = aPermutationFull (m + 1) p) :
    Equiv.Perm (Fin (m + 1)) →* ↥A :=
  { toFun := fun σ => ⟨(MulAut.congr eta).symm (permAut (p := p) σ), by
      rw [← Subgroup.mem_map_equiv (f := MulAut.congr eta), hA, ← pxA_permAutHom_range]
      exact MonoidHom.mem_range.mpr ⟨σ, rfl⟩⟩
    map_one' := by
      apply Subtype.ext
      change (MulAut.congr eta).symm ((TypeBDatum.permAutHom (m + 1) p) 1) = 1
      rw [map_one, map_one]
    map_mul' := by
      intro σ τ
      apply Subtype.ext
      change (MulAut.congr eta).symm ((TypeBDatum.permAutHom (m + 1) p) (σ * τ)) =
        (MulAut.congr eta).symm ((TypeBDatum.permAutHom (m + 1) p) σ) *
          (MulAut.congr eta).symm ((TypeBDatum.permAutHom (m + 1) p) τ)
      rw [map_mul, map_mul] }

private theorem pxA_permHom_apply {m : ℕ} {A : Subgroup (MulAut ↥Bs)}
    {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    {hA : A.map (MulAut.congr eta).toMonoidHom = aPermutationFull (m + 1) p}
    (σ : Equiv.Perm (Fin (m + 1))) :
    ((pxA_permHom eta hA σ : ↥A) : MulAut ↥Bs) =
      (MulAut.congr eta).symm (permAut (p := p) σ) := rfl

private theorem pxA_permHom_injective [Fact p.Prime] {m : ℕ} {A : Subgroup (MulAut ↥Bs)}
    {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    {hA : A.map (MulAut.congr eta).toMonoidHom = aPermutationFull (m + 1) p} :
    Function.Injective (pxA_permHom eta hA) := by
  have hp : p.Prime := Fact.out
  intro σ τ h
  apply Equiv.ext
  intro i
  have h2 : permAut (p := p) σ = permAut (p := p) τ :=
    (MulAut.congr eta).symm.injective (congrArg Subtype.val h)
  have h1 := DFunLike.congr_fun h2 (Pi.mulSingle i (ofAdd (1 : ZMod p)))
  rw [SpCoord.permAut_mulSingle, SpCoord.permAut_mulSingle] at h1
  exact (SpCoord.mulSingle_ofAdd_eq_iff (p := p)
    (fun h0 => SpCoord.coord_zero_ne_one hp h0.symm) h1).1

private theorem pxA_permHom_surjective {m : ℕ} {A : Subgroup (MulAut ↥Bs)}
    {eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p))}
    {hA : A.map (MulAut.congr eta).toMonoidHom = aPermutationFull (m + 1) p} :
    Function.Surjective (pxA_permHom eta hA) := by
  intro a
  have ha : MulAut.congr eta (a : MulAut ↥Bs) ∈
      (TypeBDatum.permAutHom (m + 1) p).range := by
    rw [pxA_permAutHom_range, ← hA]
    exact Subgroup.mem_map_of_mem _ a.2
  obtain ⟨σ, hσ⟩ := MonoidHom.mem_range.mp ha
  refine ⟨σ, ?_⟩
  apply Subtype.ext
  rw [pxA_permHom_apply]
  change (MulAut.congr eta).symm (permAut (p := p) σ) = (a : MulAut ↥Bs)
  have hσ' : permAut (p := p) σ = MulAut.congr eta (a : MulAut ↥Bs) := hσ
  rw [hσ']
  exact MulEquiv.symm_apply_apply _ _

theorem ggWeylOfType_A_of_map_eq_aPermutationFull [Fact p.Prime] (hp2 : p ≠ 2) {m : ℕ}
    {A : Subgroup (MulAut ↥Bs)} (eta : ↥Bs ≃* (Fin (m + 1) → Multiplicative (ZMod p)))
    (hA : A.map (MulAut.congr eta).toMonoidHom = aPermutationFull (m + 1) p) :
    GGWeylOfType p (CoxeterMatrix.A m) A := by
  have hp : p.Prime := Fact.out
  have hφinj : Function.Injective (pxA_permHom eta hA) := pxA_permHom_injective
  have hφsurj : Function.Surjective (pxA_permHom eta hA) := pxA_permHom_surjective
  let ε : Equiv.Perm (Fin (m + 1)) ≃* ↥A :=
    MulEquiv.ofBijective (pxA_permHom eta hA) ⟨hφinj, hφsurj⟩
  obtain ⟨ψ, hψ⟩ := ggOrthA_exists_groupEquiv_of_eq
    (coxeterMatrix_isFiniteType_A_eq m).symm
  refine ⟨ψ.trans ((typeAWeylEquiv m).symm.trans ε), fun k => ?_⟩
  have he : (ψ.trans ((typeAWeylEquiv m).symm.trans ε)) ((CoxeterMatrix.A m).simple k) =
      ε (Equiv.swap k.castSucc k.succ) := by
    rw [MulEquiv.trans_apply, MulEquiv.trans_apply, hψ k, ← typeAWeylEquiv_swap m k,
      MulEquiv.symm_apply_apply]
  rw [he]
  change GGIsReflection p ((MulAut.congr eta).symm
    (permAut (p := p) (Equiv.swap k.castSucc k.succ)))
  exact pxA_isReflection_coord hp hp2 eta (Fin.castSucc_lt_succ (i := k)).ne

theorem not_ggWeylOfType_G₂_of_le {A X : Subgroup (MulAut ↥Bs)} (hAX : A ≤ X)
    (hX : ∀ s ∈ X, ∀ t ∈ X, GGIsReflection p s → GGIsReflection p t → orderOf (s * t) ≤ 4) :
    ¬ GGWeylOfType p CoxeterMatrix.G₂ A := by
  rintro ⟨e, he⟩
  let s : MulAut ↥Bs := ((e (CoxeterMatrix.G₂.simple 0) : ↥A) : MulAut ↥Bs)
  let t : MulAut ↥Bs := ((e (CoxeterMatrix.G₂.simple 1) : ↥A) : MulAut ↥Bs)
  have hsX : s ∈ X := hAX (e (CoxeterMatrix.G₂.simple 0)).2
  have htX : t ∈ X := hAX (e (CoxeterMatrix.G₂.simple 1)).2
  have hs : GGIsReflection p s := he 0
  have ht : GGIsReflection p t := he 1
  have hle : orderOf (s * t) ≤ 4 := hX s hsX t htX hs ht
  have hst : ((e (CoxeterMatrix.G₂.simple 0 * CoxeterMatrix.G₂.simple 1) : ↥A) :
      MulAut ↥Bs) = s * t := by
    rw [map_mul]
    rfl
  have hord : orderOf (s * t) = 6 := by
    rw [← hst, Subgroup.orderOf_coe, MulEquiv.orderOf_eq e]
    rw [← CoxeterMatrix.toCoxeterSystem_simple]
    rw [CoxeterSystem.orderOf_simple_mul_simple (CoxeterMatrix.G₂.toCoxeterSystem) 0 1]
    rfl
  omega

end CFSG.StandardType

end

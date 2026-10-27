module

public import CFSG.LocalAnalysis.StandardType.GGTBTorDefs
public import CFSG.GroupTheory.CenterlessInnerCentralizer
public import TauCeti.Algebra.BigOperators.ZPow
public import TauCeti.LinearAlgebra.Matrix.Cartan.Classical
public import TauCeti.LinearAlgebra.IntegralLattice.RootLattice.TypeD.SimpleRoots
public import CFSG.GroupTheory.PCore.SubgroupCore
public import CFSG.HardMathSupport.Solomon.LocalBalance.Defs
public import CFSG.LocalAnalysis.GLTheoremB.UniqInputs

@[expose] public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

variable {N : ℕ} {μ : Type} [CommGroup μ]

def corTuple (C : Matrix (Fin N) (Fin N) ℤ) (k : Fin N) (z : μ) : Fin N → μ :=
  fun j => z ^ C k j

@[simp] theorem corTuple_apply (C : Matrix (Fin N) (Fin N) ℤ) (k : Fin N) (z : μ)
    (j : Fin N) : corTuple C k z j = z ^ C k j := rfl

def corTupleHom (C : Matrix (Fin N) (Fin N) ℤ) (k : Fin N) : μ →* (Fin N → μ) where
  toFun z := corTuple C k z
  map_one' := by
    funext j
    simp [corTuple]
  map_mul' z w := by
    funext j
    exact mul_zpow z w (C k j)

@[simp] theorem corTupleHom_apply (C : Matrix (Fin N) (Fin N) ℤ) (k : Fin N) (z : μ) :
    corTupleHom C k z = corTuple C k z := rfl

theorem corTuple_injective (C B : Matrix (Fin N) (Fin N) ℤ) (hCB : C * B = 1) (k : Fin N) :
    Function.Injective (corTuple (μ := μ) C k) := by
  intro z w h
  have hsum : ∑ j, C k j * B j k = 1 := by
    have := congrFun (congrFun hCB k) k
    simpa [Matrix.mul_apply, Matrix.one_apply] using this
  calc z = z ^ (1 : ℤ) := (zpow_one z).symm
    _ = z ^ (∑ j, C k j * B j k) := by rw [hsum]
    _ = ∏ j, z ^ (C k j * B j k) := by rw [Finset.prod_zpow_eq_zpow_sum]
    _ = ∏ j, (z ^ C k j) ^ B j k := by simp only [zpow_mul]
    _ = ∏ j, (w ^ C k j) ^ B j k := by
        refine Finset.prod_congr rfl fun j _ => ?_
        have hzj : z ^ C k j = w ^ C k j := by
          simpa only [corTuple_apply] using congrFun h j
        rw [hzj]
    _ = ∏ j, w ^ (C k j * B j k) := by simp only [zpow_mul]
    _ = w ^ (∑ j, C k j * B j k) := by rw [Finset.prod_zpow_eq_zpow_sum]
    _ = w ^ (1 : ℤ) := by rw [hsum]
    _ = w := zpow_one w

theorem corTuple_prod_mul_eq (C B : Matrix (Fin N) (Fin N) ℤ) (hBC : B * C = 1)
    (a : Fin N → μ) :
    (∏ k, corTuple C k (∏ j, a j ^ B j k)) = a := by
  funext j
  rw [Finset.prod_apply]
  simp only [corTuple_apply]
  calc (∏ k, (∏ j', a j' ^ B j' k) ^ C k j)
      = ∏ k, ∏ j', (a j' ^ B j' k) ^ C k j := by
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [Finset.prod_zpow]
    _ = ∏ k, ∏ j', a j' ^ (B j' k * C k j) := by
          refine Finset.prod_congr rfl fun k _ => ?_
          refine Finset.prod_congr rfl fun j' _ => ?_
          rw [zpow_mul]
    _ = ∏ j', ∏ k, a j' ^ (B j' k * C k j) := by rw [Finset.prod_comm]
    _ = ∏ j', a j' ^ (∑ k, B j' k * C k j) := by
          refine Finset.prod_congr rfl fun j' _ => ?_
          rw [Finset.prod_zpow_eq_zpow_sum]
    _ = a j := by
          rw [Finset.prod_eq_single j (fun j' _ hj => ?_)
            (fun hj => absurd (Finset.mem_univ j) hj)]
          · have hsum : ∑ k, B j k * C k j = 1 := by
              have := congrFun (congrFun hBC j) j
              simpa [Matrix.mul_apply, Matrix.one_apply] using this
            rw [hsum, zpow_one]
          · have hsum : ∑ k, B j' k * C k j = 0 := by
              have := congrFun (congrFun hBC j') j
              simpa [Matrix.mul_apply, Matrix.one_apply, hj] using this
            rw [hsum, zpow_zero]

theorem zpow_eq_zpow_of_intCast_eq {m : ℕ} (l : μ ≃* Multiplicative (ZMod m)) (z : μ) {a b : ℤ}
    (h : (a : ZMod m) = (b : ZMod m)) : z ^ a = z ^ b := by
  apply l.injective
  rw [map_zpow, map_zpow]
  apply Multiplicative.toAdd.injective
  rw [toAdd_zpow, toAdd_zpow, zsmul_eq_mul, zsmul_eq_mul, h]

theorem intCast_apply_of_mapMatrix_eq_one {m : ℕ} {X : Matrix (Fin N) (Fin N) ℤ}
    (h : (Int.castRingHom (ZMod m)).mapMatrix X = 1) (i j : Fin N) :
    (X i j : ZMod m) = ((if i = j then 1 else 0 : ℤ) : ZMod m) := by
  have hij := congrFun (congrFun h i) j
  rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.one_apply, eq_intCast] at hij
  rw [hij]
  split_ifs <;> simp

theorem corTuple_injective_mod {m : ℕ} (l : μ ≃* Multiplicative (ZMod m))
    (C B : Matrix (Fin N) (Fin N) ℤ)
    (hCB : (Int.castRingHom (ZMod m)).mapMatrix (C * B) = 1) (k : Fin N) :
    Function.Injective (corTuple (μ := μ) C k) := by
  intro z w h
  have hkk : ((∑ j, C k j * B j k : ℤ) : ZMod m) = ((1 : ℤ) : ZMod m) := by
    simpa [Matrix.mul_apply] using intCast_apply_of_mapMatrix_eq_one hCB k k
  calc z = z ^ (1 : ℤ) := (zpow_one z).symm
    _ = z ^ (∑ j, C k j * B j k) := zpow_eq_zpow_of_intCast_eq l z hkk.symm
    _ = ∏ j, z ^ (C k j * B j k) := by rw [Finset.prod_zpow_eq_zpow_sum]
    _ = ∏ j, (z ^ C k j) ^ B j k := by simp only [zpow_mul]
    _ = ∏ j, (w ^ C k j) ^ B j k := by
        refine Finset.prod_congr rfl fun j _ => ?_
        have hzj : z ^ C k j = w ^ C k j := by
          simpa only [corTuple_apply] using congrFun h j
        rw [hzj]
    _ = ∏ j, w ^ (C k j * B j k) := by simp only [zpow_mul]
    _ = w ^ (∑ j, C k j * B j k) := by rw [Finset.prod_zpow_eq_zpow_sum]
    _ = w ^ (1 : ℤ) := zpow_eq_zpow_of_intCast_eq l w hkk
    _ = w := zpow_one w

theorem corTuple_prod_mul_eq_mod {m : ℕ} (l : μ ≃* Multiplicative (ZMod m))
    (C B : Matrix (Fin N) (Fin N) ℤ)
    (hBC : (Int.castRingHom (ZMod m)).mapMatrix (B * C) = 1) (a : Fin N → μ) :
    (∏ k, corTuple C k (∏ j, a j ^ B j k)) = a := by
  funext j
  rw [Finset.prod_apply]
  simp only [corTuple_apply]
  calc (∏ k, (∏ j', a j' ^ B j' k) ^ C k j)
      = ∏ k, ∏ j', (a j' ^ B j' k) ^ C k j := by
          refine Finset.prod_congr rfl fun k _ => ?_
          rw [Finset.prod_zpow]
    _ = ∏ k, ∏ j', a j' ^ (B j' k * C k j) := by
          refine Finset.prod_congr rfl fun k _ => ?_
          refine Finset.prod_congr rfl fun j' _ => ?_
          rw [zpow_mul]
    _ = ∏ j', ∏ k, a j' ^ (B j' k * C k j) := by rw [Finset.prod_comm]
    _ = ∏ j', a j' ^ (∑ k, B j' k * C k j) := by
          refine Finset.prod_congr rfl fun j' _ => ?_
          rw [Finset.prod_zpow_eq_zpow_sum]
    _ = a j := by
          rw [Finset.prod_eq_single j (fun j' _ hj => ?_)
            (fun hj => absurd (Finset.mem_univ j) hj)]
          · have hsum : ((∑ k, B j k * C k j : ℤ) : ZMod m) = ((1 : ℤ) : ZMod m) := by
              simpa [Matrix.mul_apply] using intCast_apply_of_mapMatrix_eq_one hBC j j
            rw [zpow_eq_zpow_of_intCast_eq l (a j) hsum, zpow_one]
          · have hsum : ((∑ k, B j' k * C k j : ℤ) : ZMod m) = ((0 : ℤ) : ZMod m) := by
              simpa [Matrix.mul_apply, hj] using intCast_apply_of_mapMatrix_eq_one hBC j' j
            rw [zpow_eq_zpow_of_intCast_eq l (a j') hsum, zpow_zero]

section Coordinates

variable {G : Type} [Group G]

def corMu (φ : (Fin N → μ) →* G) (C : Matrix (Fin N) (Fin N) ℤ) (k : Fin N) : μ →* G :=
  φ.comp (corTupleHom C k)

@[simp] theorem corMu_apply (φ : (Fin N → μ) →* G) (C : Matrix (Fin N) (Fin N) ℤ)
    (k : Fin N) (z : μ) : corMu φ C k z = φ (corTuple C k z) := rfl

def scalarCor {m : ℕ} (l : μ ≃* Multiplicative (ZMod m)) (φ : (Fin N → μ) →* G)
    (C : Matrix (Fin N) (Fin N) ℤ) (k : Fin N) : Multiplicative (ZMod m) →* G :=
  (corMu φ C k).comp l.symm.toMonoidHom

@[simp] theorem scalarCor_eq_phi {m : ℕ} (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G) (C : Matrix (Fin N) (Fin N) ℤ) (k : Fin N)
    (z : Multiplicative (ZMod m)) :
    scalarCor l φ C k z = φ (corTuple C k (l.symm z)) := by
  simp [scalarCor]

@[simp] theorem scalarCor_apply_l {m : ℕ} (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G) (C : Matrix (Fin N) (Fin N) ℤ) (k : Fin N) (z : μ) :
    scalarCor l φ C k (l z) = φ (corTuple C k z) := by
  simp [scalarCor]

theorem scalarCor_injective {m : ℕ} (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G) (C B : Matrix (Fin N) (Fin N) ℤ)
    (hφ : Function.Injective φ) (hCB : (Int.castRingHom (ZMod m)).mapMatrix (C * B) = 1)
    (k : Fin N) :
    Function.Injective (scalarCor l φ C k) := by
  intro z w h
  have hz : l.symm z = l.symm w := by
    apply corTuple_injective_mod l C B hCB k
    apply hφ
    simpa only [scalarCor_eq_phi] using h
  calc z = l (l.symm z) := (l.apply_symm_apply z).symm
    _ = l (l.symm w) := by rw [hz]
    _ = w := l.apply_symm_apply w

theorem phi_mem_iSup_scalarCor {m : ℕ} (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G) (C B : Matrix (Fin N) (Fin N) ℤ)
    (hBC : (Int.castRingHom (ZMod m)).mapMatrix (B * C) = 1)
    (a : Fin N → μ) :
    φ a ∈ ⨆ k, (scalarCor l φ C k).range := by
  let x : Fin N → μ := fun k => ∏ j, a j ^ B j k
  have htuple_finset : (∏ k, corTuple C k (x k)) = a := corTuple_prod_mul_eq_mod l C B hBC a
  have htuple_list : (List.ofFn fun k => corTuple C k (x k)).prod = a := by
    rw [List.prod_ofFn, htuple_finset]
  have hphi_list : φ a =
      (List.ofFn fun k => scalarCor l φ C k (l (x k))).prod := by
    calc φ a = φ ((List.ofFn fun k => corTuple C k (x k)).prod) := by rw [htuple_list]
      _ = (List.ofFn fun k => φ (corTuple C k (x k))).prod := by
            rw [map_list_prod, List.map_ofFn]
            rfl
      _ = (List.ofFn fun k => scalarCor l φ C k (l (x k))).prod := by
            congr 1
            rw [List.ofFn_inj]
            funext k
            rw [scalarCor_apply_l]
  rw [hphi_list]
  exact Subgroup.list_prod_mem (K := ⨆ k, (scalarCor l φ C k).range)
    (fun y hy => by
      obtain ⟨k, rfl⟩ := List.mem_ofFn.mp hy
      exact Subgroup.mem_iSup_of_mem k ⟨l (x k), rfl⟩)

theorem scalar_range_eq_iSup_cor {m : ℕ} (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G) (C B : Matrix (Fin N) (Fin N) ℤ)
    (hBC : (Int.castRingHom (ZMod m)).mapMatrix (B * C) = 1) :
    φ.range = ⨆ k, (scalarCor l φ C k).range := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨a, rfl⟩
    exact phi_mem_iSup_scalarCor l φ C B hBC a
  · refine iSup_le fun k => ?_
    rintro _ ⟨z, rfl⟩
    rw [scalarCor_eq_phi]
    exact ⟨_, rfl⟩

end Coordinates

abbrev scalarA {G : Type} [Group G] (E : Subgroup G) : Subgroup (MulAut G) :=
  E.map (MulAut.conj : G →* MulAut G)

theorem exists_ggTorusTorWit_of_rootCoordinates_columns_mod
    {m N p : ℕ} {G : Type} [Group G] {μ : Type} [CommGroup μ]
    (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G)
    (hφconj : Function.Injective ((MulAut.conj : G →* MulAut G).comp φ))
    (C B : Matrix (Fin N) (Fin N) ℤ)
    (hCB : (Int.castRingHom (ZMod m)).mapMatrix (C * B) = 1)
    (hBC : (Int.castRingHom (ZMod m)).mapMatrix (B * C) = 1)
    (E : Subgroup G)
    (hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range)
    (ζ : μ) (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (n : Fin N → G)
    (hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer ((scalarA E) : Set (MulAut G)))
    (hnformula : ∀ k (a : Fin N → μ),
      n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple C.transpose k (a k)))⁻¹)
    (Tsc : Subgroup G)
    (hoddTsc : ∀ z ∈ Subgroup.center G, Odd (orderOf z) → z ∈ Tsc)
    (hcent : ∀ g : G, (∀ a ∈ scalarA E, MulAut.conj g * a = a * MulAut.conj g) →
      g ∈ Tsc ⊔ Subgroup.center G)
    (hfixTsc : ∀ a : Fin N → μ, ∀ t ∈ Tsc, Commute (φ a) t)
    (htorsTsc : ∀ t ∈ Tsc, t ^ m = 1 → t ∈ φ.range)
    (M : CoxeterMatrix (Fin N))
    (ρ : M.Group →* MulAut ↥(scalarA E))
    (hρ : Function.Injective ρ)
    (hρrange : ρ.range = ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA E))
    (hρsimple : ∀ k (a : ↥(scalarA E)),
      ((ρ (M.simple k) a : ↥(scalarA E)) : MulAut G) =
        MulAut.conj (n k) * (a : MulAut G) * (MulAut.conj (n k))⁻¹) :
    ∃ w : GGTorusTorWit m N G (scalarA E),
      w.T = ((MulAut.conj : G →* MulAut G).comp φ).range ∧ w.Tsc = Tsc ∧
        (∀ k, w.cor k = scalarCor l φ C.transpose k) ∧ (∀ k, w.n k = n k) ∧ w.Holds C M := by
  classical
  have hCBt : (Int.castRingHom (ZMod m)).mapMatrix (C.transpose * B.transpose) = 1 := by
    rw [← Matrix.transpose_mul, RingHom.mapMatrix_apply, Matrix.transpose_map,
      ← RingHom.mapMatrix_apply, hBC, Matrix.transpose_one]
  have hBCt : (Int.castRingHom (ZMod m)).mapMatrix (B.transpose * C.transpose) = 1 := by
    rw [← Matrix.transpose_mul, RingHom.mapMatrix_apply, Matrix.transpose_map,
      ← RingHom.mapMatrix_apply, hCB, Matrix.transpose_one]
  have hφ : Function.Injective φ := by
    intro a b hab
    apply hφconj
    exact congrArg (MulAut.conj : G →* MulAut G) hab
  let f : (Fin N → μ) →* MulAut G := (MulAut.conj : G →* MulAut G).comp φ
  have hf : Function.Injective f := hφconj
  let T : Subgroup (MulAut G) := f.range
  let coord : T →* (Fin N → μ) := (MonoidHom.ofInjective hf).symm.toMonoidHom
  let alpha : Fin N → MulAut G → Multiplicative (ZMod m) := fun k ψ =>
    if h : ψ ∈ T then l (coord ⟨ψ, h⟩ k) else 1
  have hcoord : ∀ (ψ : MulAut G) (h : ψ ∈ T), f (coord ⟨ψ, h⟩) = ψ := by
    intro ψ h
    have h1 := MonoidHom.ofInjective_apply (f := f) hf (x := coord ⟨ψ, h⟩)
    rw [show (MonoidHom.ofInjective hf) (coord ⟨ψ, h⟩) = ⟨ψ, h⟩ from
      MulEquiv.apply_symm_apply (MonoidHom.ofInjective hf) ⟨ψ, h⟩] at h1
    exact h1.symm
  have hfaT : ∀ a : Fin N → μ, f a ∈ T := by
    intro a
    change f a ∈ f.range
    exact ⟨a, rfl⟩
  have hcoord_self : ∀ a : Fin N → μ, coord ⟨f a, hfaT a⟩ = a := by
    intro a
    apply hf
    rw [hcoord]
  have halpha_mem : ∀ k ψ (h : ψ ∈ T),
      alpha k ψ = l (coord ⟨ψ, h⟩ k) := by
    intro k ψ h
    dsimp [alpha]
    rw [dif_pos h]
  have halpha_f : ∀ (k : Fin N) (a : Fin N → μ), alpha k (f a) = l (a k) := by
    intro k a
    rw [halpha_mem k (f a) (hfaT a), hcoord_self a]
  have hphi_comm : ∀ a b : Fin N → μ, Commute (φ a) (φ b) := by
    intro a b
    change φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul, mul_comm]
  have hTcomm : ∀ x ∈ T, ∀ y ∈ T, x * y = y * x := by
    rintro x ⟨a, rfl⟩ y ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  have hAT : scalarA E ≤ T := by
    intro a ha
    obtain ⟨e, heE, rfl⟩ := Subgroup.mem_map.mp ha
    obtain ⟨b, rfl⟩ := MonoidHom.mem_range.mp ((hE e).mp heE).2
    change MulAut.conj (φ b) ∈ f.range
    exact ⟨b, rfl⟩
  have hconjT : ∀ k ζ, MulAut.conj (scalarCor l φ C.transpose k ζ) ∈ T := by
    intro k ζ
    change MulAut.conj (scalarCor l φ C.transpose k ζ) ∈ f.range
    refine ⟨corTuple C.transpose k (l.symm ζ), ?_⟩
    rw [scalarCor_eq_phi]
    rfl
  have hαadd : ∀ j, ∀ x ∈ T, ∀ y ∈ T, alpha j (x * y) = alpha j x * alpha j y := by
    rintro j x ⟨a, rfl⟩ y ⟨b, rfl⟩
    rw [← map_mul, halpha_f j (a * b), halpha_f j a, halpha_f j b, Pi.mul_apply, map_mul]
  have hcorinj : ∀ k, Function.Injective (scalarCor l φ C.transpose k) := fun k =>
    scalarCor_injective l φ C.transpose B.transpose hφ hCBt k
  have hcorcomm : ∀ j k ζ ξ,
      Commute (scalarCor l φ C.transpose j ζ) (scalarCor l φ C.transpose k ξ) := by
    rintro j k ζ ξ
    rw [scalarCor_eq_phi, scalarCor_eq_phi]
    exact (hphi_comm (corTuple C.transpose j (l.symm ζ)) (corTuple C.transpose k (l.symm ξ))).eq
  have hfixcor : ∀ τ ∈ T, ∀ k ζ,
      τ (scalarCor l φ C.transpose k ζ) = scalarCor l φ C.transpose k ζ := by
    rintro τ ⟨a, rfl⟩ k ζ
    rw [scalarCor_eq_phi]
    change (MulAut.conj (φ a)) (φ (corTuple C.transpose k (l.symm ζ))) =
      φ (corTuple C.transpose k (l.symm ζ))
    rw [MulAut.conj_apply, (hphi_comm a (corTuple C.transpose k (l.symm ζ))).eq]
    group
  have hpair : ∀ i j ζ, alpha i (MulAut.conj (scalarCor l φ C.transpose j ζ)) = ζ ^ C i j := by
    rintro i j ζ
    rw [scalarCor_eq_phi]
    change alpha i (f (corTuple C.transpose j (l.symm ζ))) = ζ ^ C i j
    rw [halpha_f i (corTuple C.transpose j (l.symm ζ))]
    rw [show corTuple C.transpose j (l.symm ζ) i = (l.symm ζ) ^ C.transpose j i from rfl,
      Matrix.transpose_apply, map_zpow, MulEquiv.apply_symm_apply]
  have hnconj : ∀ k, ∀ τ ∈ T,
      MulAut.conj (n k) * τ * (MulAut.conj (n k))⁻¹ =
        τ * (MulAut.conj (scalarCor l φ C.transpose k (alpha k τ)))⁻¹ := by
    rintro k τ ⟨a, rfl⟩
    have hcor : scalarCor l φ C.transpose k (alpha k (f a)) = φ (corTuple C.transpose k (a k)) := by
      rw [halpha_f k a, scalarCor_apply_l]
    rw [hcor]
    change MulAut.conj (n k) * MulAut.conj (φ a) * (MulAut.conj (n k))⁻¹ =
      MulAut.conj (φ a) * (MulAut.conj (φ (corTuple C.transpose k (a k))))⁻¹
    rw [← map_mul, ← map_inv, ← map_mul, hnformula, map_mul, map_inv]
  have hnel : ∀ k, ∀ τ ∈ T,
      n k * (τ (n k))⁻¹ = (scalarCor l φ C.transpose k (alpha k τ))⁻¹ := by
    rintro k τ ⟨a, rfl⟩
    have hcor : scalarCor l φ C.transpose k (alpha k (f a)) = φ (corTuple C.transpose k (a k)) := by
      rw [halpha_f k a, scalarCor_apply_l]
    rw [hcor]
    change n k * ((MulAut.conj (φ a)) (n k))⁻¹ = (φ (corTuple C.transpose k (a k)))⁻¹
    rw [MulAut.conj_apply]
    calc n k * (φ a * n k * (φ a)⁻¹)⁻¹
        = n k * φ a * (n k)⁻¹ * (φ a)⁻¹ := by group
      _ = (φ a * (φ (corTuple C.transpose k (a k)))⁻¹) * (φ a)⁻¹ := by rw [hnformula]
      _ = (φ (corTuple C.transpose k (a k)))⁻¹ := by
            rw [(hphi_comm a (corTuple C.transpose k (a k))).inv_right.eq]
            group
  have hsep : ∀ τ ∈ T, (∀ k, alpha k τ = 1) → τ = 1 := by
    rintro τ ⟨a, rfl⟩ h
    have ha : a = 1 := by
      funext k
      have hk : l (a k) = 1 := by
        rw [← halpha_f k a]
        exact h k
      exact l.injective (by simpa using hk)
    rw [ha]
    simp [f]
  have hαA : ∀ k, ∃ a ∈ scalarA E, alpha k a ≠ 1 := by
    intro k
    let u : Fin N → μ := (Pi.mulSingle k ζ : Fin N → μ)
    let e : G := φ u
    have hu_pow : u ^ p = 1 := by
      change ((Pi.mulSingle k ζ : Fin N → μ)) ^ p = 1
      rw [← Pi.mulSingle_pow, hζp, Pi.mulSingle_one]
    have heE : e ∈ E := by
      refine (hE e).mpr ⟨?_, ?_⟩
      · change (φ u) ^ p = 1
        rw [← map_pow, hu_pow, map_one]
      · change φ u ∈ φ.range
        exact ⟨u, rfl⟩
    refine ⟨MulAut.conj e, ?_, ?_⟩
    · exact Subgroup.mem_map.mpr ⟨e, heE, rfl⟩
    · have hfu : MulAut.conj e = f u := rfl
      rw [hfu, halpha_f k u]
      change l ((Pi.mulSingle k ζ : Fin N → μ) k) ≠ 1
      rw [Pi.mulSingle_eq_same]
      intro h
      exact hζ1 (l.injective (by rw [map_one]; exact h))
  have hinnA : ∀ a ∈ scalarA E,
      a ∈ (MulAut.conj : G →* MulAut G).range →
        ∃ t ∈ ⨆ k, (scalarCor l φ C.transpose k).range, a = MulAut.conj t := by
    rintro a ha _
    obtain ⟨e, heE, rfl⟩ := Subgroup.mem_map.mp ha
    refine ⟨e, ?_, rfl⟩
    rw [← scalar_range_eq_iSup_cor l φ C.transpose B.transpose hBCt]
    exact ((hE e).mp heE).2
  have hCscB : ∀ τ ∈ T, ∀ t ∈ Tsc, τ t = t := by
    rintro τ ⟨a, rfl⟩ t ht
    change (MulAut.conj (φ a)) t = t
    rw [MulAut.conj_apply, (hfixTsc a t ht).eq]
    group
  have hCscC : ∀ t ∈ Tsc, t ^ m = 1 →
      t ∈ ⨆ k, (scalarCor l φ C.transpose k).range := by
    intro t ht hm
    rw [← scalar_range_eq_iSup_cor l φ C.transpose B.transpose hBCt]
    exact htorsTsc t ht hm
  have hsimple_eq : ∀ k, ρ (M.simple k) = ggConjAut (scalarA E) (hn k) := by
    intro k
    ext a x
    rw [ggConjAut_apply]
    exact congrArg (fun f : MulAut G => f x) (hρsimple k a)
  have hgenM : Subgroup.closure (Set.range M.simple) = ⊤ := by
    simpa only [CoxeterMatrix.toCoxeterSystem_simple] using
      M.toCoxeterSystem.subgroup_closure_range_simple
  have hgenρ : ρ.range = Subgroup.closure (Set.range fun k => ρ (M.simple k)) := by
    rw [MonoidHom.range_eq_map, ← hgenM, MonoidHom.map_closure]
    congr 1
    exact (Set.range_comp (⇑ρ) M.simple).symm
  have haut : ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA E) =
      Subgroup.closure (Set.range fun k => ggConjAut (scalarA E) (hn k)) := by
    rw [← hρrange, hgenρ]
    rw [show (fun k => ρ (M.simple k)) =
      (fun k => ggConjAut (scalarA E) (hn k)) from funext hsimple_eq]
  have hweyl : ∃ e : M.Group ≃*
      ↥(ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA E)),
      ∀ k, (e (M.simple k) : MulAut ↥(scalarA E)) =
        ggConjAut (scalarA E) (hn k) := by
    refine ⟨(MonoidHom.ofInjective hρ).trans (MulEquiv.subgroupCongr hρrange), ?_⟩
    intro k
    simp only [MulEquiv.trans_apply, MulEquiv.subgroupCongr_apply]
    rw [MonoidHom.ofInjective_apply]
    exact hsimple_eq k
  refine ⟨⟨T, alpha, scalarCor l φ C.transpose, n, hn, Tsc⟩, rfl, rfl, fun _ => rfl,
    fun _ => rfl, ?_⟩
  exact ⟨hTcomm, hAT, hconjT, hαadd, hcorinj, hcorcomm, hfixcor, hpair,
    hnconj, hnel, hsep, hαA, hinnA, hoddTsc, ⟨hcent, hCscB, hCscC⟩,
    haut, hweyl⟩

theorem exists_ggTorusTorWit_of_rootCoordinates_tsc
    {m N p : ℕ} {G : Type} [Group G] {μ : Type} [CommGroup μ]
    (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G) (hφ : Function.Injective φ)
    (C B : Matrix (Fin N) (Fin N) ℤ)
    (hCB : (Int.castRingHom (ZMod m)).mapMatrix (C * B) = 1)
    (hBC : (Int.castRingHom (ZMod m)).mapMatrix (B * C) = 1)
    (hφZ : ∀ a, φ a ∈ Subgroup.center G → a = 1)
    (Tsc : Subgroup G)
    (hTsc_comm : ∀ a, ∀ t ∈ Tsc, Commute (φ a) t)
    (hTsc_tors : ∀ t ∈ Tsc, t ^ m = 1 → t ∈ φ.range)
    (hTsc_odd : ∀ z ∈ Subgroup.center G, Odd (orderOf z) → z ∈ Tsc)
    (E : Subgroup G)
    (hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range)
    (ζ : μ) (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (n : Fin N → G)
    (hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer ((scalarA E) : Set (MulAut G)))
    (hnformula : ∀ k (a : Fin N → μ),
      n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple C.transpose k (a k)))⁻¹)
    (hcent : ∀ g : G, (∀ e ∈ E, g * e * g⁻¹ * e⁻¹ ∈ Subgroup.center G) →
      g ∈ Tsc ⊔ Subgroup.center G)
    (M : CoxeterMatrix (Fin N))
    (ρ : M.Group →* MulAut ↥(scalarA E))
    (hρ : Function.Injective ρ)
    (hρrange : ρ.range = ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA E))
    (hρsimple : ∀ k (a : ↥(scalarA E)),
      ((ρ (M.simple k) a : ↥(scalarA E)) : MulAut G) =
        MulAut.conj (n k) * (a : MulAut G) * (MulAut.conj (n k))⁻¹) :
    ∃ w : GGTorusTorWit m N G (scalarA E),
      w.T = ((MulAut.conj : G →* MulAut G).comp φ).range ∧ w.Tsc = Tsc ∧
        (∀ k, w.cor k = scalarCor l φ C.transpose k) ∧ (∀ k, w.n k = n k) ∧ w.Holds C M := by
  classical
  let f : (Fin N → μ) →* MulAut G := (MulAut.conj : G →* MulAut G).comp φ
  have hf : Function.Injective f := by
    rw [injective_iff_map_eq_one]
    intro a ha
    refine hφZ a (Subgroup.mem_center_iff.mpr fun g => ?_)
    have h1 := congrArg (fun ψ : MulAut G => ψ g) ha
    simp only [f, MonoidHom.coe_comp, Function.comp_apply, MulAut.conj_apply,
      MulAut.one_apply] at h1
    calc g * φ a = φ a * g * (φ a)⁻¹ * φ a := by rw [h1]
      _ = φ a * g := by group
  have hCscA : ∀ g : G,
      (∀ a ∈ scalarA E, MulAut.conj g * a = a * MulAut.conj g) →
        g ∈ Tsc ⊔ Subgroup.center G := by
    intro g hg
    refine hcent g fun e he => ?_
    have haA : MulAut.conj e ∈ scalarA E := Subgroup.mem_map.mpr ⟨e, he, rfl⟩
    have hd : (e * g)⁻¹ * (g * e) ∈ Subgroup.center G := by
      refine Subgroup.mem_center_iff.mpr fun x => ?_
      have h1 := congrArg (fun ψ : MulAut G => ψ x) (hg (MulAut.conj e) haA)
      simp only [MulAut.mul_apply, MulAut.conj_apply] at h1
      calc x * ((e * g)⁻¹ * (g * e)) = (e * g)⁻¹ * (e * (g * x * g⁻¹) * e⁻¹) * (g * e) := by
            group
        _ = (e * g)⁻¹ * (g * (e * x * e⁻¹) * g⁻¹) * (g * e) := by rw [← h1]
        _ = (e * g)⁻¹ * (g * e) * x := by group
    have hcomm := Subgroup.mem_center_iff.mp hd (e * g)
    have hc : g * e * g⁻¹ * e⁻¹ = (e * g)⁻¹ * (g * e) :=
      calc g * e * g⁻¹ * e⁻¹ = (e * g) * ((e * g)⁻¹ * (g * e)) * (e * g)⁻¹ := by group
        _ = ((e * g)⁻¹ * (g * e)) * (e * g) * (e * g)⁻¹ := by rw [hcomm]
        _ = (e * g)⁻¹ * (g * e) := by group
    rw [hc]
    exact hd
  exact exists_ggTorusTorWit_of_rootCoordinates_columns_mod
    l φ hf C B hCB hBC E hE ζ hζp hζ1 n hn hnformula
    Tsc hTsc_odd hCscA hTsc_comm hTsc_tors M ρ hρ hρrange hρsimple

theorem ggTorusTorData_of_rootCoordinates_tsc
    {m N p : ℕ} {G : Type} [Group G] {μ : Type} [CommGroup μ]
    (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G) (hφ : Function.Injective φ)
    (C B : Matrix (Fin N) (Fin N) ℤ)
    (hCB : (Int.castRingHom (ZMod m)).mapMatrix (C * B) = 1)
    (hBC : (Int.castRingHom (ZMod m)).mapMatrix (B * C) = 1)
    (hφZ : ∀ a, φ a ∈ Subgroup.center G → a = 1)
    (Tsc : Subgroup G)
    (hTsc_comm : ∀ a, ∀ t ∈ Tsc, Commute (φ a) t)
    (hTsc_tors : ∀ t ∈ Tsc, t ^ m = 1 → t ∈ φ.range)
    (hTsc_odd : ∀ z ∈ Subgroup.center G, Odd (orderOf z) → z ∈ Tsc)
    (E : Subgroup G)
    (hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range)
    (ζ : μ) (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (n : Fin N → G)
    (hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer ((scalarA E) : Set (MulAut G)))
    (hnformula : ∀ k (a : Fin N → μ),
      n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple C.transpose k (a k)))⁻¹)
    (hcent : ∀ g : G, (∀ e ∈ E, g * e * g⁻¹ * e⁻¹ ∈ Subgroup.center G) →
      g ∈ Tsc ⊔ Subgroup.center G)
    (M : CoxeterMatrix (Fin N))
    (ρ : M.Group →* MulAut ↥(scalarA E))
    (hρ : Function.Injective ρ)
    (hρrange : ρ.range = ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA E))
    (hρsimple : ∀ k (a : ↥(scalarA E)),
      ((ρ (M.simple k) a : ↥(scalarA E)) : MulAut G) =
        MulAut.conj (n k) * (a : MulAut G) * (MulAut.conj (n k))⁻¹) :
    GGTorusTorData m N C M G (scalarA E) := by
  obtain ⟨w, -, -, -, -, hw⟩ := exists_ggTorusTorWit_of_rootCoordinates_tsc l φ hφ C B hCB hBC
    hφZ Tsc hTsc_comm hTsc_tors hTsc_odd E hE ζ hζp hζ1 n hn hnformula hcent M ρ hρ hρrange
    hρsimple
  exact ⟨w, hw⟩


theorem exists_ggTorusTorWit_of_scalarRootCoordinates_columns_mod
    {m N p : ℕ} {G : Type} [Group G] {μ : Type} [CommGroup μ]
    (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G) (hφ : Function.Injective φ)
    (C B : Matrix (Fin N) (Fin N) ℤ)
    (hCB : (Int.castRingHom (ZMod m)).mapMatrix (C * B) = 1)
    (hBC : (Int.castRingHom (ZMod m)).mapMatrix (B * C) = 1)
    (hcenter : Subgroup.center G = ⊥)
    (E : Subgroup G)
    (hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range)
    (ζ : μ) (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (n : Fin N → G)
    (hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer ((scalarA E) : Set (MulAut G)))
    (hnformula : ∀ k (a : Fin N → μ),
      n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple C.transpose k (a k)))⁻¹)
    (hcent : Subgroup.centralizer (E : Set G) ≤ φ.range)
    (M : CoxeterMatrix (Fin N))
    (ρ : M.Group →* MulAut ↥(scalarA E))
    (hρ : Function.Injective ρ)
    (hρrange : ρ.range = ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA E))
    (hρsimple : ∀ k (a : ↥(scalarA E)),
      ((ρ (M.simple k) a : ↥(scalarA E)) : MulAut G) =
        MulAut.conj (n k) * (a : MulAut G) * (MulAut.conj (n k))⁻¹) :
    ∃ w : GGTorusTorWit m N G (scalarA E),
      w.T = ((MulAut.conj : G →* MulAut G).comp φ).range ∧ w.Tsc = φ.range ∧
        (∀ k, w.cor k = scalarCor l φ C.transpose k) ∧ (∀ k, w.n k = n k) ∧ w.Holds C M := by
  have hconj : Function.Injective (MulAut.conj : G →* MulAut G) :=
    CFSG.mulAutConj_injective_of_center_eq_bot hcenter
  refine exists_ggTorusTorWit_of_rootCoordinates_columns_mod l φ (hconj.comp hφ)
    C B hCB hBC E hE ζ hζp hζ1 n hn hnformula φ.range ?_ ?_ ?_ ?_
    M ρ hρ hρrange hρsimple
  · rintro z hz _
    rw [hcenter, Subgroup.mem_bot] at hz
    rw [hz]
    exact φ.range.one_mem
  · intro g hg
    have hgcent : g ∈ Subgroup.centralizer (E : Set G) := by
      refine Subgroup.mem_centralizer_iff.mpr ?_
      intro h hh
      have haA : MulAut.conj h ∈ scalarA E := Subgroup.mem_map.mpr ⟨h, hh, rfl⟩
      have hconj_eq : MulAut.conj (h * g) = MulAut.conj (g * h) := by
        simpa only [map_mul] using (hg (MulAut.conj h) haA).symm
      exact hconj hconj_eq
    exact Subgroup.mem_sup_left (hcent hgcent)
  · rintro a t ⟨b, rfl⟩
    change φ a * φ b = φ b * φ a
    rw [← map_mul, ← map_mul, mul_comm]
  · intro t ht _
    exact ht

theorem ggTorusTorData_of_scalarRootCoordinates_columns_mod
    {m N p : ℕ} {G : Type} [Group G] {μ : Type} [CommGroup μ]
    (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G) (hφ : Function.Injective φ)
    (C B : Matrix (Fin N) (Fin N) ℤ)
    (hCB : (Int.castRingHom (ZMod m)).mapMatrix (C * B) = 1)
    (hBC : (Int.castRingHom (ZMod m)).mapMatrix (B * C) = 1)
    (hcenter : Subgroup.center G = ⊥)
    (E : Subgroup G)
    (hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range)
    (ζ : μ) (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (n : Fin N → G)
    (hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer ((scalarA E) : Set (MulAut G)))
    (hnformula : ∀ k (a : Fin N → μ),
      n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple C.transpose k (a k)))⁻¹)
    (hcent : Subgroup.centralizer (E : Set G) ≤ φ.range)
    (M : CoxeterMatrix (Fin N))
    (ρ : M.Group →* MulAut ↥(scalarA E))
    (hρ : Function.Injective ρ)
    (hρrange : ρ.range = ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA E))
    (hρsimple : ∀ k (a : ↥(scalarA E)),
      ((ρ (M.simple k) a : ↥(scalarA E)) : MulAut G) =
        MulAut.conj (n k) * (a : MulAut G) * (MulAut.conj (n k))⁻¹) :
    GGTorusTorData m N C M G (scalarA E) := by
  obtain ⟨w, -, -, -, -, hw⟩ := exists_ggTorusTorWit_of_scalarRootCoordinates_columns_mod l φ hφ
    C B hCB hBC hcenter E hE ζ hζp hζ1 n hn hnformula hcent M ρ hρ hρrange hρsimple
  exact ⟨w, hw⟩

theorem ggTorusTorData_of_scalarRootCoordinates_columns
    {m N p : ℕ} {G : Type} [Group G] {μ : Type} [CommGroup μ]
    (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G) (hφ : Function.Injective φ)
    (C B : Matrix (Fin N) (Fin N) ℤ)
    (hCB : C * B = 1) (hBC : B * C = 1)
    (hcenter : Subgroup.center G = ⊥)
    (E : Subgroup G)
    (hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range)
    (ζ : μ) (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (n : Fin N → G)
    (hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer ((scalarA E) : Set (MulAut G)))
    (hnformula : ∀ k (a : Fin N → μ),
      n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple C.transpose k (a k)))⁻¹)
    (hcent : Subgroup.centralizer (E : Set G) ≤ φ.range)
    (M : CoxeterMatrix (Fin N))
    (ρ : M.Group →* MulAut ↥(scalarA E))
    (hρ : Function.Injective ρ)
    (hρrange : ρ.range = ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA E))
    (hρsimple : ∀ k (a : ↥(scalarA E)),
      ((ρ (M.simple k) a : ↥(scalarA E)) : MulAut G) =
        MulAut.conj (n k) * (a : MulAut G) * (MulAut.conj (n k))⁻¹) :
    GGTorusTorData m N C M G (scalarA E) :=
  ggTorusTorData_of_scalarRootCoordinates_columns_mod l φ hφ C B (by rw [hCB, map_one])
    (by rw [hBC, map_one]) hcenter E hE ζ hζp hζ1 n hn hnformula hcent M ρ hρ hρrange hρsimple

theorem ggTorusTorData_of_scalarRootCoordinates
    {m N p : ℕ} {G : Type} [Group G] {μ : Type} [CommGroup μ]
    (l : μ ≃* Multiplicative (ZMod m))
    (φ : (Fin N → μ) →* G) (hφ : Function.Injective φ)
    (C B : Matrix (Fin N) (Fin N) ℤ)
    (hCB : C * B = 1) (hBC : B * C = 1) (hsymm : C.IsSymm)
    (hcenter : Subgroup.center G = ⊥)
    (E : Subgroup G)
    (hE : ∀ g, g ∈ E ↔ g ^ p = 1 ∧ g ∈ φ.range)
    (ζ : μ) (hζp : ζ ^ p = 1) (hζ1 : ζ ≠ 1)
    (n : Fin N → G)
    (hn : ∀ k, MulAut.conj (n k) ∈ Subgroup.normalizer ((scalarA E) : Set (MulAut G)))
    (hnformula : ∀ k (a : Fin N → μ),
      n k * φ a * (n k)⁻¹ = φ a * (φ (corTuple C k (a k)))⁻¹)
    (hcent : Subgroup.centralizer (E : Set G) ≤ φ.range)
    (M : CoxeterMatrix (Fin N))
    (ρ : M.Group →* MulAut ↥(scalarA E))
    (hρ : Function.Injective ρ)
    (hρrange : ρ.range = ggAutomizer (MulAut.conj : G →* MulAut G).range (scalarA E))
    (hρsimple : ∀ k (a : ↥(scalarA E)),
      ((ρ (M.simple k) a : ↥(scalarA E)) : MulAut G) =
        MulAut.conj (n k) * (a : MulAut G) * (MulAut.conj (n k))⁻¹) :
    GGTorusTorData m N C M G (scalarA E) :=
  ggTorusTorData_of_scalarRootCoordinates_columns l φ hφ C B hCB hBC hcenter E hE ζ hζp hζ1 n hn
    (fun k a => by rw [hsymm.eq]; exact hnformula k a) hcent M ρ hρ hρrange hρsimple

theorem exists_int_matrix_inverse_mod_of_isUnit_det {m N : ℕ} (C : Matrix (Fin N) (Fin N) ℤ)
    (hdet : IsUnit (C.det : ZMod m)) :
    ∃ B : Matrix (Fin N) (Fin N) ℤ,
      (Int.castRingHom (ZMod m)).mapMatrix (C * B) = 1 ∧
        (Int.castRingHom (ZMod m)).mapMatrix (B * C) = 1 := by
  obtain ⟨v, hv⟩ := ZMod.intCast_surjective (↑hdet.unit⁻¹ : ZMod m)
  have hvd : (v : ZMod m) * (C.det : ZMod m) = 1 := by
    rw [hv]
    exact hdet.val_inv_mul
  have hmap : (Int.castRingHom (ZMod m)).mapMatrix
      ((v * C.det) • (1 : Matrix (Fin N) (Fin N) ℤ)) = 1 := by
    ext i j
    rw [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
      Matrix.one_apply]
    split_ifs
    · simp only [smul_eq_mul, mul_one, map_mul, eq_intCast]
      exact hvd
    · simp
  refine ⟨v • C.adjugate, ?_, ?_⟩
  · rw [Matrix.mul_smul, Matrix.mul_adjugate, smul_smul]
    exact hmap
  · rw [Matrix.smul_mul, Matrix.adjugate_mul, smul_smul]
    exact hmap

theorem exists_int_matrix_inverse_mod_E₇ {m : ℕ} (hm : Odd m) :
    ∃ B : Matrix (Fin 7) (Fin 7) ℤ,
      (Int.castRingHom (ZMod m)).mapMatrix (CartanMatrix.E 7 * B) = 1 ∧
        (Int.castRingHom (ZMod m)).mapMatrix (B * CartanMatrix.E 7) = 1 := by
  refine exists_int_matrix_inverse_mod_of_isUnit_det _ ?_
  rw [CartanMatrix.E₇_det]
  have h := (ZMod.isUnit_iff_coprime 2 m).mpr (Nat.coprime_two_left.mpr hm)
  simpa using h

theorem exists_int_matrix_inverse_mod_C {m n : ℕ} (hn : 0 < n) (hm : Odd m) :
    ∃ B : Matrix (Fin n) (Fin n) ℤ,
      (Int.castRingHom (ZMod m)).mapMatrix (CartanMatrix.C n * B) = 1 ∧
        (Int.castRingHom (ZMod m)).mapMatrix (B * CartanMatrix.C n) = 1 := by
  refine exists_int_matrix_inverse_mod_of_isUnit_det _ ?_
  rw [CartanMatrix.C_det hn]
  have h := (ZMod.isUnit_iff_coprime 2 m).mpr (Nat.coprime_two_left.mpr hm)
  simpa using h

theorem exists_int_matrix_inverse_mod_D {m n : ℕ} (hn : 2 ≤ n) (hm : Odd m) :
    ∃ B : Matrix (Fin n) (Fin n) ℤ,
      (Int.castRingHom (ZMod m)).mapMatrix (CartanMatrix.D n * B) = 1 ∧
        (Int.castRingHom (ZMod m)).mapMatrix (B * CartanMatrix.D n) = 1 := by
  refine exists_int_matrix_inverse_mod_of_isUnit_det _ ?_
  rw [CartanMatrix.D_det hn]
  have h4 : Nat.Coprime 4 m := by
    simpa using Nat.Coprime.pow_left 2 (Nat.coprime_two_left.mpr hm)
  have h := (ZMod.isUnit_iff_coprime 4 m).mpr h4
  simpa using h

end CFSG.StandardType

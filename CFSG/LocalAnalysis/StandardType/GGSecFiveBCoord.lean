module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
public import CFSG.LocalAnalysis.StandardType.GGSignedCoordBlocks
import CFSG.LocalAnalysis.StandardType.GGSignedCoordRefl
import CFSG.LocalAnalysis.StandardType.ZS.MonomialBasic

public section

namespace CFSG.StandardType

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Coord

variable {G : Type} [Group G] {p n : ℕ} [Fact p.Prime] {Bs : Subgroup G}

@[expose] noncomputable def bCoordIota (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))) :
    Additive ↥Bs ≃+ (Fin n → ZMod p) :=
  (MulEquiv.toAdditive eta).trans
    ((MulEquiv.toAdditive (MulEquiv.piMultiplicative fun _ : Fin n => ZMod p).symm).trans
      (AddEquiv.additiveMultiplicative (Fin n → ZMod p)))

theorem bCoordIota_apply_ofMul (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (b : ↥Bs) :
    bCoordIota eta (Additive.ofMul b) = fun k => Multiplicative.toAdd (eta b k) := by
  rfl

theorem ggLin_bCoordIota_sgnAut (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (i : Fin n) :
    ggLin (p := p) (bCoordIota eta) ((MulAut.congr eta).symm (SpCoord.sgnAut i)) =
      ZS.diagMap p (Pi.basisFun (ZMod p) (Fin n)) (fun j => if j = i then -1 else 1) := by
  set b := Pi.basisFun (ZMod p) (Fin n)
  set ι := bCoordIota eta
  set φ : MulAut ↥Bs := (MulAut.congr eta).symm (SpCoord.sgnAut i)
  refine Module.Basis.ext' b fun k => ?_
  rw [ZS.diagMap_apply_basis]
  let y : ↥Bs := eta.symm (fun j => Multiplicative.ofAdd ((b k) j))
  have hbk : b k = ι (Additive.ofMul y) := by
    rw [bCoordIota_apply_ofMul]
    simp [y]
  conv_lhs => rw [hbk]
  rw [ggLin_apply_ofMul]
  have hφ : eta (φ y) = SpCoord.sgnAut i (eta y) := by
    simp [φ, MulAut.congr_symm_apply, MulEquiv.trans_apply]
  rw [bCoordIota_apply_ofMul, hφ]
  funext j
  by_cases hj : j = i
  · by_cases hk : j = k
    · subst hj
      subst hk
      simp [y, SpCoord.sgnAut_apply, b, Pi.basisFun_apply, Pi.single_eq_same]
    · have hik : i ≠ k := by
        intro h
        exact hk (by rw [hj, h])
      simp [y, hj, hik, SpCoord.sgnAut_apply, b, Pi.basisFun_apply, Pi.single_eq_of_ne]
  · by_cases hk : j = k
    · have hik : k ≠ i := by
        intro h
        exact hj (by rw [hk, h])
      simp [y, hk, hik, SpCoord.sgnAut_apply, b, Pi.basisFun_apply, Pi.single_eq_same]
    · simp [y, hj, hk, SpCoord.sgnAut_apply, b, Pi.basisFun_apply, Pi.single_eq_of_ne]

theorem ggLin_bCoordIota_permAut (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (σ : Equiv.Perm (Fin n)) :
    ggLin (p := p) (bCoordIota eta) ((MulAut.congr eta).symm (SpCoord.permAut σ)) =
      ZS.permMap p (Pi.basisFun (ZMod p) (Fin n)) σ := by
  set b := Pi.basisFun (ZMod p) (Fin n)
  set ι := bCoordIota eta
  set φ : MulAut ↥Bs := (MulAut.congr eta).symm (SpCoord.permAut σ)
  refine Module.Basis.ext' b fun k => ?_
  rw [ZS.permMap_apply_basis]
  let y : ↥Bs := eta.symm (fun j => Multiplicative.ofAdd ((b k) j))
  have hbk : b k = ι (Additive.ofMul y) := by
    rw [bCoordIota_apply_ofMul]
    simp [y]
  conv_lhs => rw [hbk]
  rw [ggLin_apply_ofMul]
  have hφ : eta (φ y) = SpCoord.permAut σ (eta y) := by
    simp [φ, MulAut.congr_symm_apply, MulEquiv.trans_apply]
  rw [bCoordIota_apply_ofMul, hφ]
  funext j
  by_cases hj : j = σ k
  · have hjk : σ.symm j = k := by rw [hj, Equiv.symm_apply_apply]
    simp [y, hj, SpCoord.permAut_apply, b, Pi.basisFun_apply, Pi.single_eq_same, toAdd_ofAdd]
  · have hjk : σ.symm j ≠ k := by
      intro h
      apply hj
      rw [← h, Equiv.apply_symm_apply]
    simp [y, hjk, hj, SpCoord.permAut_apply, b, Pi.basisFun_apply, Pi.single_eq_of_ne]

private theorem congr_mem_bSignedFull_forward (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (φ : MulAut ↥Bs) (h : MulAut.congr eta φ ∈ bSignedFull n p) :
    ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i = 1 ∨ c i = -1) ∧
      ∀ i, ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i) =
        c i • Pi.basisFun (ZMod p) (Fin n) (σ i) := by
  have hsp : SpCoord.IsSignedPerm ⇑(MulAut.congr eta φ) := by
    rwa [bSignedFull_eq_signedPermSubgroup] at h
  obtain ⟨σ, c, hc, hperm⟩ := hsp
  refine ⟨σ, c, hc, fun i => ?_⟩
  let b := Pi.basisFun (ZMod p) (Fin n)
  let y : ↥Bs := eta.symm (fun j => Multiplicative.ofAdd ((b i) j))
  have hbi : b i = bCoordIota eta (Additive.ofMul y) := by
    rw [bCoordIota_apply_ofMul]
    simp [y, b, Pi.basisFun_apply, toAdd_ofAdd]
  conv_lhs => rw [hbi]
  rw [ggLin_apply_ofMul, bCoordIota_apply_ofMul]
  funext j
  by_cases hj : j = σ i
  · have h1 := hperm (eta y) i
    simp [MulAut.congr_apply, MulEquiv.trans_apply] at h1
    rw [hj]
    simp [b, Pi.basisFun_apply, Pi.single_eq_same, y] at h1 ⊢
    exact h1
  · have hji : σ.symm j ≠ i := by
      intro h
      exact hj (by rw [← h, Equiv.apply_symm_apply])
    have h1 := hperm (eta y) (σ.symm j)
    simp [MulAut.congr_apply, MulEquiv.trans_apply] at h1
    simp [b, Pi.basisFun_apply, Pi.single_eq_of_ne hj, y, Pi.single_eq_of_ne hji] at h1 ⊢
    exact h1

private theorem congr_mem_bSignedFull_backward (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (φ : MulAut ↥Bs)
    (h : ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i = 1 ∨ c i = -1) ∧
      ∀ i, ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i) =
        c i • Pi.basisFun (ZMod p) (Fin n) (σ i)) :
    MulAut.congr eta φ ∈ bSignedFull n p := by
  obtain ⟨σ, c, hc, hlin⟩ := h
  let u : MulAut (Fin n → Multiplicative (ZMod p)) :=
    SpCoord.permAut σ * SpCoord.diagAut c (fun i => SpCoord.coord_sign_mul_self (hc i))
  have hu : SpCoord.IsSignedPerm ⇑u :=
    SpCoord.isSignedPerm_permAut_mul_diagAut σ c hc
  have heq : MulAut.congr eta φ = u := by
    have : NeZero p := ⟨Nat.Prime.ne_zero (Fact.out : p.Prime)⟩
    have hhom : (MulAut.congr eta φ).toMonoidHom = u.toMonoidHom := by
      refine SpCoord.hom_ext_mulSingle fun i => ?_
      let b := Pi.basisFun (ZMod p) (Fin n)
      let y : ↥Bs := eta.symm (Pi.mulSingle i (Multiplicative.ofAdd 1))
      have hbi : b i = bCoordIota eta (Additive.ofMul y) := by
        rw [bCoordIota_apply_ofMul]
        funext k
        simp only [b, Pi.basisFun_apply, y]
        by_cases hk : k = i
        · subst hk
          simp [toAdd_ofAdd]
        · simp [hk, toAdd_one]
      have h1 : ggLin (p := p) (bCoordIota eta) φ (b i) = c i • b (σ i) := hlin i
      rw [hbi, ggLin_apply_ofMul, bCoordIota_apply_ofMul] at h1
      have hφ : eta (φ y) = Pi.mulSingle (σ i) (Multiplicative.ofAdd (c i)) := by
        funext k
        apply Multiplicative.toAdd.injective
        have hk := congrFun h1 k
        rw [hk]
        simp only [b, Pi.basisFun_apply, Pi.smul_apply]
        by_cases hk' : k = σ i
        · subst hk'
          simp
        · simp [hk']
      have hφ' : (MulAut.congr eta φ) (Pi.mulSingle i (Multiplicative.ofAdd 1)) = eta (φ y) := by
        simp [MulAut.congr_apply, y]
      have hu_action : u (Pi.mulSingle i (Multiplicative.ofAdd 1)) =
          Pi.mulSingle (σ i) (Multiplicative.ofAdd (c i)) := by
        simp [u, MulAut.mul_apply, SpCoord.diagAut_mulSingle, SpCoord.permAut_mulSingle]
      rw [MulEquiv.coe_toMonoidHom, MulEquiv.coe_toMonoidHom, hφ', hu_action, hφ]
    exact MulEquiv.ext fun f => congrArg (fun g => g f) hhom
  rw [heq, bSignedFull_eq_signedPermSubgroup]
  exact hu

theorem congr_mem_bSignedFull_iff (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    (φ : MulAut ↥Bs) :
    MulAut.congr eta φ ∈ bSignedFull n p ↔
      ∃ (σ : Equiv.Perm (Fin n)) (c : Fin n → ZMod p), (∀ i, c i = 1 ∨ c i = -1) ∧
        ∀ i, ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i) =
          c i • Pi.basisFun (ZMod p) (Fin n) (σ i) :=
  ⟨congr_mem_bSignedFull_forward eta φ, congr_mem_bSignedFull_backward eta φ⟩

theorem fix_of_coord_single (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {i0 : Fin n} {b : ↥Bs} (hb : ∀ k, k ≠ i0 → eta b k = 1) {φ : MulAut ↥Bs}
    (hφ : ggLin (p := p) (bCoordIota eta) φ (Pi.basisFun (ZMod p) (Fin n) i0) =
      Pi.basisFun (ZMod p) (Fin n) i0) : φ b = b := by
  let v := bCoordIota eta (Additive.ofMul b)
  have hv : v = (Multiplicative.toAdd (eta b i0)) • Pi.basisFun (ZMod p) (Fin n) i0 := by
    funext k
    by_cases hk : k = i0
    · subst hk
      simp [v, bCoordIota_apply_ofMul, Pi.basisFun_apply, Pi.smul_apply]
    · have h1 : eta b k = 1 := hb k hk
      simp [v, bCoordIota_apply_ofMul, Pi.basisFun_apply, Pi.single_eq_of_ne hk, h1, Pi.smul_apply]
  have hfix : ggLin (p := p) (bCoordIota eta) φ v = v := by
    rw [hv, map_smul, hφ]
  have h1 : bCoordIota eta (Additive.ofMul (φ b)) = bCoordIota eta (Additive.ofMul b) := by
    simpa only [v, ggLin_apply_ofMul] using hfix
  exact Additive.ofMul.injective ((bCoordIota eta).injective h1)

theorem fix_of_coord_const (eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p)))
    {b : ↥Bs} (hb : ∀ k l, eta b k = eta b l) {φ : MulAut ↥Bs}
    (hφ : ggLin (p := p) (bCoordIota eta) φ (∑ i, Pi.basisFun (ZMod p) (Fin n) i) =
      ∑ i, Pi.basisFun (ZMod p) (Fin n) i) : φ b = b := by
  by_cases hn : n = 0
  · have : Subsingleton ↥Bs := by
      have : Subsingleton (Fin n → Multiplicative (ZMod p)) := by
        rw [hn]
        infer_instance
      exact Function.Injective.subsingleton eta.injective
    exact Subsingleton.elim _ _
  · have hnpos : 0 < n := Nat.pos_of_ne_zero hn
    let i0 : Fin n := ⟨0, hnpos⟩
    let v := bCoordIota eta (Additive.ofMul b)
    have hv : v = (Multiplicative.toAdd (eta b i0)) •
        (∑ i, Pi.basisFun (ZMod p) (Fin n) i) := by
      funext k
      have hconst : eta b k = eta b i0 := hb k i0
      simp [v, bCoordIota_apply_ofMul, Pi.basisFun_apply, Pi.smul_apply, hconst]
    have hfix : ggLin (p := p) (bCoordIota eta) φ v = v := by
      rw [hv, map_smul, hφ]
    have h1 : bCoordIota eta (Additive.ofMul (φ b)) = bCoordIota eta (Additive.ofMul b) := by
      simpa only [v, ggLin_apply_ofMul] using hfix
    exact Additive.ofMul.injective ((bCoordIota eta).injective h1)

end Coord

end CFSG.StandardType

end

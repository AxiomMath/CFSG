module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinModel

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open

private def sixteenC8SpinUniqPolar (Q : SpinW → ZMod 2) (x y : SpinW) : ZMod 2 :=
  Q (x * y) - Q x - Q y

private lemma sixteenC8SpinUniq_polarQ_comm (Q : SpinW → ZMod 2) (x y : SpinW) :
    sixteenC8SpinUniqPolar Q x y = sixteenC8SpinUniqPolar Q y x := by
  unfold sixteenC8SpinUniqPolar
  rw [mul_comm x y]
  ring

private lemma sixteenC8SpinUniq_polarQ_one_left {Q : SpinW → ZMod 2} (hQ : IsQuadF2 Q)
    (z : SpinW) : sixteenC8SpinUniqPolar Q 1 z = 0 := by
  have h := hQ.1 1 1 z
  change sixteenC8SpinUniqPolar Q 1 z
    = sixteenC8SpinUniqPolar Q 1 z + sixteenC8SpinUniqPolar Q 1 z at h
  have h' : sixteenC8SpinUniqPolar Q 1 z + sixteenC8SpinUniqPolar Q 1 z
      = sixteenC8SpinUniqPolar Q 1 z + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h'

private lemma sixteenC8SpinUniq_polarQ_one_right {Q : SpinW → ZMod 2} (hQ : IsQuadF2 Q)
    (z : SpinW) : sixteenC8SpinUniqPolar Q z 1 = 0 := by
  have h := hQ.2 z 1 1
  change sixteenC8SpinUniqPolar Q z 1
    = sixteenC8SpinUniqPolar Q z 1 + sixteenC8SpinUniqPolar Q z 1 at h
  have h' : sixteenC8SpinUniqPolar Q z 1 + sixteenC8SpinUniqPolar Q z 1
      = sixteenC8SpinUniqPolar Q z 1 + 0 := by
    rw [add_zero]
    exact h.symm
  exact add_left_cancel h'

private lemma sixteenC8SpinUniq_quad_mul (Q : SpinW → ZMod 2) (x y : SpinW) :
    Q (x * y) = Q x + Q y + sixteenC8SpinUniqPolar Q x y := by
  unfold sixteenC8SpinUniqPolar
  ring

private lemma sixteenC8SpinUniq_quad_one {Q : SpinW → ZMod 2} (hQ : IsQuadF2 Q) : Q 1 = 0 := by
  have h := hQ.1 1 1 1
  change sixteenC8SpinUniqPolar Q 1 1
    = sixteenC8SpinUniqPolar Q 1 1 + sixteenC8SpinUniqPolar Q 1 1 at h
  have hp : sixteenC8SpinUniqPolar Q 1 1 = 0 := by
    have h' : sixteenC8SpinUniqPolar Q 1 1 + sixteenC8SpinUniqPolar Q 1 1
        = sixteenC8SpinUniqPolar Q 1 1 + 0 := by
      rw [add_zero]
      exact h.symm
    exact add_left_cancel h'
  have hp' : sixteenC8SpinUniqPolar Q 1 1 = - Q 1 := by
    unfold sixteenC8SpinUniqPolar
    simp only [one_mul, sub_self, zero_sub]
  rw [hp'] at hp
  exact neg_eq_zero.mp hp

private lemma sixteenC8SpinUniq_zmod_two : ∀ c : ZMod 2, c = 0 ∨ c = 1 := by decide

private abbrev sixteenC8SpinUniqBilin (Q : SpinW → ZMod 2) (hQ : IsQuadF2 Q) :
    LinearMap.BilinForm (ZMod 2) (Fin (2 * 4) → ZMod 2) :=
  LinearMap.mk₂ (ZMod 2)
    (fun x y => sixteenC8SpinUniqPolar Q (Multiplicative.ofAdd x) (Multiplicative.ofAdd y))
    (fun x y z => hQ.1 (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) (Multiplicative.ofAdd z))
    (fun c x y => by
      rcases sixteenC8SpinUniq_zmod_two c with rfl | rfl
      · simpa using sixteenC8SpinUniq_polarQ_one_left hQ (Multiplicative.ofAdd y)
      · simp)
    (fun x y z => hQ.2 (Multiplicative.ofAdd x) (Multiplicative.ofAdd y) (Multiplicative.ofAdd z))
    (fun c x y => by
      rcases sixteenC8SpinUniq_zmod_two c with rfl | rfl
      · simpa using sixteenC8SpinUniq_polarQ_one_right hQ (Multiplicative.ofAdd x)
      · simp)

private lemma sixteenC8SpinUniqBilin_nondegenerate {Q : SpinW → ZMod 2} (hQ : IsNondegQuadF2 Q) :
    (sixteenC8SpinUniqBilin Q hQ.1).Nondegenerate := by
  refine ⟨fun x hx => ?_, fun y hy => ?_⟩
  · by_contra hne
    have hne' : Multiplicative.ofAdd x ≠ 1 := fun h => hne (by simpa using h)
    obtain ⟨w, hw⟩ := hQ.2 (Multiplicative.ofAdd x) hne'
    refine hw ?_
    have h := hx w.toAdd
    change sixteenC8SpinUniqPolar Q (Multiplicative.ofAdd x) w = 0 at h
    exact h
  · by_contra hne
    have hne' : Multiplicative.ofAdd y ≠ 1 := fun h => hne (by simpa using h)
    obtain ⟨w, hw⟩ := hQ.2 (Multiplicative.ofAdd y) hne'
    refine hw ?_
    change sixteenC8SpinUniqPolar Q (Multiplicative.ofAdd y) w = 0
    have hthis : sixteenC8SpinUniqPolar Q w (Multiplicative.ofAdd y) = 0 := by
      have h := hy w.toAdd
      change sixteenC8SpinUniqPolar Q w (Multiplicative.ofAdd y) = 0 at h
      exact h
    rw [← sixteenC8SpinUniq_polarQ_comm Q w (Multiplicative.ofAdd y)]
    exact hthis

private noncomputable def sixteenC8SpinUniqAutLin (h : MulAut SpinW) :
    (Fin (2 * 4) → ZMod 2) →ₗ[ZMod 2] (Fin (2 * 4) → ZMod 2) :=
  (AddMonoidHom.mk' (fun v => Multiplicative.toAdd (h (Multiplicative.ofAdd v))) (by
    intro a b
    simp only [ofAdd_add, map_mul, toAdd_mul])).toZModLinearMap 2

private lemma sixteenC8SpinUniqAutLin_apply (h : MulAut SpinW) (v : Fin (2 * 4) → ZMod 2) :
    sixteenC8SpinUniqAutLin h v =
      Multiplicative.toAdd (h (Multiplicative.ofAdd v)) := rfl

private lemma sixteenC8SpinUniqAutLin_inv (h : MulAut SpinW) (v : Fin (2 * 4) → ZMod 2) :
    sixteenC8SpinUniqAutLin h (sixteenC8SpinUniqAutLin h⁻¹ v) = v := by
  simp only [sixteenC8SpinUniqAutLin_apply, ofAdd_toAdd, MulAut.apply_inv_self, toAdd_ofAdd]

private lemma sixteenC8SpinUniqBilin_invariant {Q : SpinW → ZMod 2} (hQ : IsQuadF2 Q)
    {H : Subgroup (MulAut SpinW)} (hinv : QuadInvariant Q H) {h : MulAut SpinW} (hh : h ∈ H)
    (x y : Fin (2 * 4) → ZMod 2) :
    sixteenC8SpinUniqBilin Q hQ (sixteenC8SpinUniqAutLin h x) (sixteenC8SpinUniqAutLin h y) =
      sixteenC8SpinUniqBilin Q hQ x y := by
  change sixteenC8SpinUniqPolar Q (Multiplicative.ofAdd (sixteenC8SpinUniqAutLin h x))
      (Multiplicative.ofAdd (sixteenC8SpinUniqAutLin h y))
    = sixteenC8SpinUniqPolar Q (Multiplicative.ofAdd x) (Multiplicative.ofAdd y)
  simp only [sixteenC8SpinUniqAutLin_apply, ofAdd_toAdd]
  unfold sixteenC8SpinUniqPolar
  rw [← map_mul]
  simp only [hinv h hh]

private lemma sixteenC8SpinUniqBilin_ext
    {B : LinearMap.BilinForm (ZMod 2) (Fin (2 * 4) → ZMod 2)} (hB : B.Nondegenerate)
    {a b : Fin (2 * 4) → ZMod 2} (h : ∀ y, B a y = B b y) : a = b := by
  have h0 : ∀ y, B (a - b) y = 0 := by
    intro y
    rw [map_sub, LinearMap.sub_apply, h y, sub_self]
  exact sub_eq_zero.mp (hB.1 (a - b) h0)

private noncomputable def sixteenC8SpinUniqMulAut
    (φ : (Fin (2 * 4) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * 4) → ZMod 2)) : MulAut SpinW where
  toFun w := Multiplicative.ofAdd (φ (Multiplicative.toAdd w))
  invFun w := Multiplicative.ofAdd (φ.symm (Multiplicative.toAdd w))
  left_inv w := by simp
  right_inv w := by simp
  map_mul' x y := by simp only [toAdd_mul, map_add, ofAdd_add]

private lemma sixteenC8SpinUniqMulAut_ofAdd
    (φ : (Fin (2 * 4) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * 4) → ZMod 2))
    (v : Fin (2 * 4) → ZMod 2) :
    sixteenC8SpinUniqMulAut φ (Multiplicative.ofAdd v) = Multiplicative.ofAdd (φ v) := by
  simp [sixteenC8SpinUniqMulAut]

private def sixteenC8SpinUniqLam (Q Q' : SpinW → ZMod 2) (x : SpinW) : ZMod 2 := Q x + Q' x

private lemma sixteenC8SpinUniqLam_mul {Q Q' : SpinW → ZMod 2}
    (hB : ∀ x y, polarQ Q x y = polarQ Q' x y) (x y : SpinW) :
    sixteenC8SpinUniqLam Q Q' (x * y) =
      sixteenC8SpinUniqLam Q Q' x + sixteenC8SpinUniqLam Q Q' y := by
  have h1 : Q (x * y) = Q x + Q y + sixteenC8SpinUniqPolar Q x y :=
    sixteenC8SpinUniq_quad_mul Q x y
  have h2 : Q' (x * y) = Q' x + Q' y + sixteenC8SpinUniqPolar Q' x y :=
    sixteenC8SpinUniq_quad_mul Q' x y
  have hB' : sixteenC8SpinUniqPolar Q x y = sixteenC8SpinUniqPolar Q' x y := hB x y
  change (Q (x * y) + Q' (x * y)) = (Q x + Q' x) + (Q y + Q' y)
  rw [h1, h2, ← hB']
  rw [show (Q x + Q y + sixteenC8SpinUniqPolar Q x y)
        + (Q' x + Q' y + sixteenC8SpinUniqPolar Q x y)
      = (Q x + Q y + Q' x + Q' y)
        + (sixteenC8SpinUniqPolar Q x y + sixteenC8SpinUniqPolar Q x y) by ring,
    ZModModule.add_self, add_zero]
  ring

private noncomputable def sixteenC8SpinUniqLamHom (Q Q' : SpinW → ZMod 2) (hQ : IsQuadF2 Q)
    (hQ' : IsQuadF2 Q') (hB : ∀ x y, polarQ Q x y = polarQ Q' x y) :
    SpinW →* Multiplicative (ZMod 2) where
  toFun x := Multiplicative.ofAdd (sixteenC8SpinUniqLam Q Q' x)
  map_one' := by
    simp only [sixteenC8SpinUniqLam, sixteenC8SpinUniq_quad_one hQ,
      sixteenC8SpinUniq_quad_one hQ', add_zero, ofAdd_zero]
  map_mul' x y := by
    rw [sixteenC8SpinUniqLam_mul hB x y, ofAdd_add]

theorem quad_unique_of_cent_irr (H : Subgroup (MulAut SpinW))
    (hC : ∀ c : MulAut SpinW, (∀ h ∈ H, c * h = h * c) → c = 1)
    (hI : IsIrrOn H (⊤ : Subgroup SpinW) ⊥) {Q Q' : SpinW → ZMod 2}
    (hQ : IsNondegQuadF2 Q) (hQ' : IsNondegQuadF2 Q')
    (hinv : QuadInvariant Q H) (hinv' : QuadInvariant Q' H) : Q = Q' := by
  classical
  let B : LinearMap.BilinForm (ZMod 2) (Fin (2 * 4) → ZMod 2) :=
    sixteenC8SpinUniqBilin Q hQ.1
  let B' : LinearMap.BilinForm (ZMod 2) (Fin (2 * 4) → ZMod 2) :=
    sixteenC8SpinUniqBilin Q' hQ'.1
  have hB : B.Nondegenerate := sixteenC8SpinUniqBilin_nondegenerate hQ
  have hB' : B'.Nondegenerate := sixteenC8SpinUniqBilin_nondegenerate hQ'
  let φ : (Fin (2 * 4) → ZMod 2) →ₗ[ZMod 2] (Fin (2 * 4) → ZMod 2) :=
    B'.symmCompOfNondegenerate B hB
  have hφ : ∀ x y, B (φ x) y = B' x y := fun x y =>
    LinearMap.BilinForm.symmCompOfNondegenerate_left_apply B' hB y x
  have hφinj : Function.Injective φ := by
    intro x y hxy
    have h0 : ∀ z, B' (x - y) z = 0 := by
      intro z
      rw [map_sub, LinearMap.sub_apply, ← hφ x z, ← hφ y z, hxy, sub_self]
    exact sub_eq_zero.mp (hB'.1 (x - y) h0)
  let φe : (Fin (2 * 4) → ZMod 2) ≃ₗ[ZMod 2] (Fin (2 * 4) → ZMod 2) :=
    LinearEquiv.ofInjectiveEndo φ hφinj
  let c : MulAut SpinW := sixteenC8SpinUniqMulAut φe
  have hc_apply : ∀ v, c (Multiplicative.ofAdd v) = Multiplicative.ofAdd (φe v) := by
    intro v
    simp only [c, sixteenC8SpinUniqMulAut_ofAdd]
  have key : ∀ h ∈ H, ∀ v, φe (sixteenC8SpinUniqAutLin h v) =
      sixteenC8SpinUniqAutLin h (φe v) := by
    intro h hh v
    refine sixteenC8SpinUniqBilin_ext hB fun y => ?_
    have hBinv : ∀ x y,
        B (sixteenC8SpinUniqAutLin h x) (sixteenC8SpinUniqAutLin h y) = B x y :=
      fun x y => sixteenC8SpinUniqBilin_invariant hQ.1 hinv hh x y
    have hB'inv : ∀ x y,
        B' (sixteenC8SpinUniqAutLin h x) (sixteenC8SpinUniqAutLin h y) = B' x y :=
      fun x y => sixteenC8SpinUniqBilin_invariant hQ'.1 hinv' hh x y
    have h1 : B' (sixteenC8SpinUniqAutLin h v) y =
        B' v (sixteenC8SpinUniqAutLin h⁻¹ y) := by
      have h := hB'inv v (sixteenC8SpinUniqAutLin h⁻¹ y)
      rw [sixteenC8SpinUniqAutLin_inv] at h
      exact h
    have h2 : B' v (sixteenC8SpinUniqAutLin h⁻¹ y) =
        B (φe v) (sixteenC8SpinUniqAutLin h⁻¹ y) := (hφ v _).symm
    have h3 : B (φe v) (sixteenC8SpinUniqAutLin h⁻¹ y) =
        B (sixteenC8SpinUniqAutLin h (φe v)) y := by
      have h := hBinv (φe v) (sixteenC8SpinUniqAutLin h⁻¹ y)
      rw [sixteenC8SpinUniqAutLin_inv] at h
      exact h.symm
    calc B (φe (sixteenC8SpinUniqAutLin h v)) y
        = B' (sixteenC8SpinUniqAutLin h v) y := hφ _ y
      _ = B' v (sixteenC8SpinUniqAutLin h⁻¹ y) := h1
      _ = B (φe v) (sixteenC8SpinUniqAutLin h⁻¹ y) := h2
      _ = B (sixteenC8SpinUniqAutLin h (φe v)) y := h3
  have hcomm : ∀ h ∈ H, c * h = h * c := by
    intro h hh
    apply MulEquiv.ext
    intro w
    obtain ⟨v, rfl⟩ : ∃ v, Multiplicative.ofAdd v = w := ⟨w.toAdd, ofAdd_toAdd w⟩
    rw [MulAut.mul_apply, MulAut.mul_apply]
    have ha : ∀ u, h (Multiplicative.ofAdd u) =
        Multiplicative.ofAdd (sixteenC8SpinUniqAutLin h u) := by
      intro u
      rw [sixteenC8SpinUniqAutLin_apply]
      exact (ofAdd_toAdd _).symm
    calc c (h (Multiplicative.ofAdd v))
        = c (Multiplicative.ofAdd (sixteenC8SpinUniqAutLin h v)) := by rw [ha v]
      _ = Multiplicative.ofAdd (φe (sixteenC8SpinUniqAutLin h v)) := hc_apply _
      _ = Multiplicative.ofAdd (sixteenC8SpinUniqAutLin h (φe v)) := by rw [key h hh v]
      _ = h (Multiplicative.ofAdd (φe v)) := (ha (φe v)).symm
      _ = h (c (Multiplicative.ofAdd v)) := by rw [hc_apply v]
  have hc1 : c = 1 := hC c hcomm
  have hφid : ∀ v, φ v = v := by
    intro v
    have h1 : Multiplicative.ofAdd (φ v) = Multiplicative.ofAdd v := by
      have h2 := congrArg (fun f : MulAut SpinW => f (Multiplicative.ofAdd v)) hc1
      simp only [hc_apply v, MulAut.one_apply] at h2
      exact h2
    simpa using congrArg Multiplicative.toAdd h1
  have hBB' : B' = B := by
    apply LinearMap.ext
    intro x
    apply LinearMap.ext
    intro y
    rw [← hφ x y, hφid x]
  have hpol : ∀ x y : SpinW, polarQ Q x y = polarQ Q' x y := by
    intro x y
    change sixteenC8SpinUniqPolar Q x y = sixteenC8SpinUniqPolar Q' x y
    have h := congrArg (fun (B : LinearMap.BilinForm (ZMod 2) (Fin (2 * 4) → ZMod 2)) =>
      B x.toAdd y.toAdd) hBB'
    change sixteenC8SpinUniqPolar Q' x y = sixteenC8SpinUniqPolar Q x y at h
    exact h.symm
  let lamH : SpinW →* Multiplicative (ZMod 2) :=
    sixteenC8SpinUniqLamHom Q Q' hQ.1 hQ'.1 hpol
  let K : Subgroup SpinW := lamH.ker
  have hKmem : ∀ x : SpinW, x ∈ K ↔ Q x + Q' x = 0 := by
    intro x
    change x ∈ (sixteenC8SpinUniqLamHom Q Q' hQ.1 hQ'.1 hpol).ker ↔ Q x + Q' x = 0
    rw [MonoidHom.mem_ker]
    show Multiplicative.ofAdd (Q x + Q' x) = 1 ↔ Q x + Q' x = 0
    exact ofAdd_eq_one
  have hKstab : StableUnder H K := by
    intro h hh u hu
    rw [hKmem (h u)]
    rw [hKmem u] at hu
    rw [hinv h hh u, hinv' h hh u]
    exact hu
  have hKcases : K = ⊥ ∨ K = ⊤ := hI.2.2.2 K hKstab bot_le le_top
  have hKne : K ≠ ⊥ := by
    intro hKbot
    have hKbot' : lamH.ker = ⊥ := hKbot
    have hinj : Function.Injective lamH := (MonoidHom.ker_eq_bot_iff lamH).mp hKbot'
    have hle : Fintype.card SpinW ≤ Fintype.card (Multiplicative (ZMod 2)) :=
      Fintype.card_le_of_injective lamH hinj
    have hcard : Fintype.card SpinW = 256 := by
      change Fintype.card (Multiplicative (Fin (2 * 4) → ZMod 2)) = 256
      simp only [Fintype.card_multiplicative, Fintype.card_fun, Fintype.card_fin, ZMod.card]
      norm_num
    have hcard2 : Fintype.card (Multiplicative (ZMod 2)) = 2 := by
      simp [ZMod.card]
    rw [hcard, hcard2] at hle
    norm_num at hle
  have hKtop : K = ⊤ := hKcases.resolve_left hKne
  have hlam0 : ∀ x : SpinW, Q x + Q' x = 0 := by
    intro x
    have hxK : x ∈ K := by rw [hKtop]; exact Subgroup.mem_top x
    exact (hKmem x).mp hxK
  funext x
  exact add_right_cancel ((hlam0 x).trans (ZModModule.add_self (Q' x)).symm)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

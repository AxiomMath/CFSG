module

public import CFSG.LocalAnalysis.ComponentClassification.GMS78Sec5RuGammaS5
public import CFSG.Quasithin.Background.SzG11TensorB

public section

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F4Tensor

open CFSG.ComponentClassification.GMS78.RuGamma CFSG.Quasithin.RuType
  CFSG.Quasithin.RuType.Sigma

@[expose] def frobElt (t : Bool) : Multiplicative (ZMod 2) :=
  if t then Multiplicative.ofAdd 1 else 1

@[expose] def sqVec {K : Type} [Field K] (w : Fin 2 → K) : Fin 2 → K := fun i => w i ^ 2

@[expose] noncomputable def ringEquivF4 : F4 ≃+* GaloisField 2 2 := by
  letI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  exact FiniteField.ringEquivOfCardEq (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card, Nat.card_eq_fintype_card (α := F4),
      F4.card, GaloisField.card 2 2 (by norm_num)]
    norm_num)

theorem sigmaAct_transport (x : SigmaL2F4) (w : Fin 2 → F4) :
    (fun i => ringEquivF4 (sigmaAct x w i)) =
      ((Matrix.SpecialLinearGroup.map (ringEquivF4 : F4 →+* GaloisField 2 2) x.left :
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec
        (if decide (Multiplicative.toAdd x.right ≠ 0) then sqVec (fun i => ringEquivF4 (w i))
          else fun i => ringEquivF4 (w i)) := by
  have hmap : ((Matrix.SpecialLinearGroup.map (ringEquivF4 : F4 →+* GaloisField 2 2) x.left :
      Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
        Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) =
      (x.left : Matrix (Fin 2) (Fin 2) F4).map ringEquivF4 := rfl
  rw [hmap]
  funext i
  have key : ∀ v : Fin 2 → F4, ringEquivF4 (((x.left : Matrix (Fin 2) (Fin 2) F4).mulVec v) i) =
      ((x.left : Matrix (Fin 2) (Fin 2) F4).map ringEquivF4).mulVec
        (fun j => ringEquivF4 (v j)) i := fun v =>
    RingHom.map_mulVec (ringEquivF4 : F4 →+* GaloisField 2 2) _ v i
  rcases zmod2_cases (Multiplicative.toAdd x.right) with hk | hk
  · have hd : decide (Multiplicative.toAdd x.right ≠ 0) = false := by simp [hk]
    rw [hd]
    simp only [sigmaAct, frobVec_of_eq_zero hk]
    exact key _
  · have hd : decide (Multiplicative.toAdd x.right ≠ 0) = true := by
      simp [hk]
    rw [hd]
    simp only [sigmaAct, frobVec_of_eq_one hk]
    refine (key _).trans ?_
    congr 1
    funext j
    simp [sqVec, frobF4_apply, sq]

theorem exists_sigma_of (A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) (t : Bool) :
    ∃ x : SigmaL2F4, Matrix.SpecialLinearGroup.map (ringEquivF4 : F4 →+* GaloisField 2 2)
      x.left = A ∧ decide (Multiplicative.toAdd x.right ≠ 0) = t := by
  refine ⟨⟨Matrix.SpecialLinearGroup.map (ringEquivF4.symm : GaloisField 2 2 →+* F4) A,
    frobElt t⟩, ?_, ?_⟩
  · show Matrix.SpecialLinearGroup.map (ringEquivF4 : F4 →+* GaloisField 2 2)
      (Matrix.SpecialLinearGroup.map (ringEquivF4.symm : GaloisField 2 2 →+* F4) A) = A
    refine Subtype.ext ?_
    ext i j
    simp
  · cases t <;> simp [frobElt]

theorem exists_semilin_coords {Bsp : Type} [AddCommGroup Bsp] [Module (ZMod 2) Bsp] [Finite Bsp]
    (hB : Module.finrank (ZMod 2) Bsp = 4) {G : Type} [Group G]
    (ρ : G →* (Bsp ≃ₗ[ZMod 2] Bsp)) (hρ : Function.Injective ρ) (hG : Nat.card G = 120)
    (htr : ∀ b b' : Bsp, b ≠ 0 → b' ≠ 0 → ∃ g : G, ρ g b = b') :
    ∃ lam : Bsp ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2),
      (∀ g : G, ∃ (A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) (t : Bool),
        ∀ b : Bsp, lam (ρ g b) = (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec
          (if t then sqVec (lam b) else lam b)) ∧
      (∀ (A : Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) (t : Bool), ∃ g : G,
        ∀ b : Bsp, lam (ρ g b) = (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec
          (if t then sqVec (lam b) else lam b)) := by
  haveI : Module.Finite (ZMod 2) Bsp := Module.Finite.of_finite
  let b : Bsp ≃ₗ[ZMod 2] (Fin 4 → ZMod 2) :=
    (Module.finBasisOfFinrankEq (ZMod 2) Bsp hB).equivFun
  let ρ4 : G →* GL4 :=
    { toFun := fun g => (b.symm.trans (ρ g)).trans b
      map_one' := by
        ext v
        simp
      map_mul' := fun g g' => by
        ext v
        simp }
  have hρ4 : ∀ g (x : Bsp), ρ4 g (b x) = b (ρ g x) := fun g x => by simp [ρ4]
  have hρ4inj : Function.Injective ρ4 := by
    intro g g' h
    apply hρ
    refine LinearEquiv.ext fun x => b.injective ?_
    rw [← hρ4, ← hρ4, h]
  let Γ4 : Subgroup GL4 := ρ4.range
  have hΓ4card : Nat.card Γ4 = 120 := by
    rw [← hG]
    exact (Nat.card_congr (MonoidHom.ofInjective hρ4inj).toEquiv).symm
  have htr4 : ∀ v w : Fin 4 → ZMod 2, v ≠ 0 → w ≠ 0 → ∃ g ∈ Γ4, g v = w := by
    intro v w hv hw
    obtain ⟨g, hg⟩ := htr (b.symm v) (b.symm w) (fun h => hv (b.symm.map_eq_zero_iff.1 h))
      (fun h => hw (b.symm.map_eq_zero_iff.1 h))
    refine ⟨ρ4 g, ⟨g, rfl⟩, ?_⟩
    have := hρ4 g (b.symm v)
    rw [LinearEquiv.apply_symm_apply, hg, LinearEquiv.apply_symm_apply] at this
    exact this
  obtain ⟨κ, hκ⟩ := exists_coords hΓ4card htr4
  have hgx : ∀ g : G, ∃ x : SigmaL2F4, ∀ v, κ (ρ4 g v) = sigmaAct x (κ v) :=
    fun g => hκ ⟨g, rfl⟩
  choose xf hxf using hgx
  let lam : Bsp ≃ₗ[ZMod 2] (Fin 2 → GaloisField 2 2) :=
    SzG11S.Tensor.zmodEquiv (b.toAddEquiv.trans (κ.trans
      (AddEquiv.piCongrRight fun _ => (ringEquivF4 : F4 ≃+* GaloisField 2 2).toAddEquiv)))
  have hlam : ∀ x : Bsp, lam x = fun i => ringEquivF4 (κ (b x) i) := fun x => rfl
  have hform : ∀ (g : G) (x : Bsp), lam (ρ g x) =
      ((Matrix.SpecialLinearGroup.map (ringEquivF4 : F4 →+* GaloisField 2 2) (xf g).left :
        Matrix.SpecialLinearGroup (Fin 2) (GaloisField 2 2)) :
          Matrix (Fin 2) (Fin 2) (GaloisField 2 2)).mulVec
        (if decide (Multiplicative.toAdd (xf g).right ≠ 0) then sqVec (lam x) else lam x) := by
    intro g x
    have h1 : lam (ρ g x) = fun i => ringEquivF4 (sigmaAct (xf g) (κ (b x)) i) := by
      rw [hlam, ← hρ4, hxf g]
    rw [h1, hlam x]
    exact sigmaAct_transport (xf g) (κ (b x))
  have hinj : Function.Injective xf := by
    intro g g' h
    apply hρ4inj
    refine LinearEquiv.ext fun v => κ.injective ?_
    rw [hxf g, hxf g', h]
  have hbij : Function.Bijective xf :=
    hinj.bijective_of_nat_card_le (by rw [card_Sigma', hG])
  refine ⟨lam, fun g => ⟨_, _, hform g⟩, fun A t => ?_⟩
  obtain ⟨x, hxA, hxt⟩ := exists_sigma_of A t
  obtain ⟨g, rfl⟩ := hbij.2 x
  refine ⟨g, fun y => ?_⟩
  rw [hform g y, hxA, hxt]

end F4Tensor

end Canon

end G11

end CFSG.Quasithin

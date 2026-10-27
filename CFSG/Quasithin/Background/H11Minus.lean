module

public import CFSG.Quasithin.Background.H11MinusField
import CFSG.Quasithin.Background.H11Plus
import CFSG.Quasithin.Background.Harris.L2.OmegaMinusRep
import CFSG.Quasithin.Vol2.Ch6H11Holds
public import CFSG.Quasithin.Vol2.Ch6H11Norm
import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin.H11Proof

open CFSG.Quasithin

section MinusGroup

open scoped Matrix

variable {F : Type} [Field F] [CharP F 2]

private noncomputable abbrev sigQ (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] : AdjoinRoot (quadPoly a) →+* AdjoinRoot (quadPoly a) :=
  iterateFrobenius (AdjoinRoot (quadPoly a)) 2 n

private noncomputable abbrev WQ (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] :=
  ↥(SteinbergCB.twistedForm (sigQ n a))

private noncomputable def iotaRing (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] (hF : Nat.card F = 2 ^ n) :
    F →+* SteinbergCB.frobFixed (sigQ n a) where
  toFun c := ⟨algebraMap F (AdjoinRoot (quadPoly a)) c,
    SteinbergCB.mem_frobFixed.mpr (iterate_frob_algebraMap_fix hF c)⟩
  map_one' := Subtype.ext (map_one _)
  map_mul' c d := Subtype.ext (map_mul _ _ _)
  map_zero' := Subtype.ext (map_zero _)
  map_add' c d := Subtype.ext (map_add _ _ _)

private theorem iotaRing_bijective (n : ℕ) (a : F)
    [Fact (Irreducible (quadPoly a))] [CharP (AdjoinRoot (quadPoly a)) 2]
    [Finite F] [Finite (AdjoinRoot (quadPoly a))] (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) :
    Function.Bijective (iotaRing n a hF) := by
  refine ⟨fun c d h => ?_, fun y => ?_⟩
  · have := congrArg Subtype.val h
    exact (algebraMap F (AdjoinRoot (quadPoly a))).injective this
  · obtain ⟨c, hc⟩ := fixed_mem_range_algebraMap hn hF hK y.1
      (SteinbergCB.mem_frobFixed.mp y.2)
    exact ⟨c, Subtype.ext hc⟩

private noncomputable def thetaAdd (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (hF : Nat.card F = 2 ^ n) (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) :
    (Fin 4 → F) →+ WQ n a where
  toFun x := ⟨hermOf n a x, SteinbergCB.mem_twistedForm.mpr (hermOf_mem hF hK x)⟩
  map_zero' := Subtype.ext (by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hermOf])
  map_add' x y := Subtype.ext (hermOf_add x y)

private theorem thetaAdd_apply (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (hF : Nat.card F = 2 ^ n) (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2)
    (x : Fin 4 → F) :
    ((thetaAdd n a hF hK x : WQ n a) : Matrix (Fin 2) (Fin 2) (AdjoinRoot (quadPoly a))) =
      hermOf n a x := rfl

private theorem thetaAdd_smul (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (hF : Nat.card F = 2 ^ n) (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2)
    (c : F) (x : Fin 4 → F) :
    thetaAdd n a hF hK (c • x) = iotaRing n a hF c • thetaAdd n a hF hK x := by
  apply Subtype.ext
  rw [thetaAdd_apply, Submodule.coe_smul]
  change hermOf n a (c • x) = algebraMap F (AdjoinRoot (quadPoly a)) c • hermOf n a x
  exact hermOf_smul hF c x

private noncomputable def thetaEquiv (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) : (Fin 4 → F) ≃+ WQ n a :=
  AddEquiv.ofBijective (thetaAdd n a hF hK)
    ⟨fun x y h => (hermOf_eq_iff (ha := ha) x y).mp (congrArg Subtype.val h),
      fun X => by
        obtain ⟨x, hx⟩ := hermOf_surj hn hF hK X.1 (SteinbergCB.mem_twistedForm.mp X.2)
        exact ⟨x, Subtype.ext hx⟩⟩

private theorem thetaEquiv_apply (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) (x : Fin 4 → F) :
    thetaEquiv n a ha hn hF hK x = thetaAdd n a hF hK x := rfl

private theorem thetaEquiv_symm_smul (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) (c : F) (X : WQ n a) :
    (thetaEquiv n a ha hn hF hK).symm (iotaRing n a hF c • X) =
      c • (thetaEquiv n a ha hn hF hK).symm X := by
  rw [AddEquiv.symm_apply_eq]
  have key := thetaAdd_smul n a hF hK c ((thetaEquiv n a ha hn hF hK).symm X)
  have hX : thetaAdd n a hF hK ((thetaEquiv n a ha hn hF hK).symm X) = X :=
    (thetaEquiv n a ha hn hF hK).apply_symm_apply X
  rw [hX] at key
  exact key.symm

private noncomputable def cjSemi (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2)
    (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) :
    WQ n a ≃ₗ[SteinbergCB.frobFixed (sigQ n a)] WQ n a where
  toFun X := thetaEquiv n a ha hn hF hK (g ((thetaEquiv n a ha hn hF hK).symm X))
  invFun X := thetaEquiv n a ha hn hF hK (g.symm ((thetaEquiv n a ha hn hF hK).symm X))
  map_add' X Y := by simp
  map_smul' r X := by
    obtain ⟨c, rfl⟩ := (iotaRing_bijective n a hn hF hK).2 r
    simp only [RingHom.id_apply]
    rw [thetaEquiv_symm_smul n a ha hn hF hK c X, LinearEquiv.map_smul, thetaEquiv_apply,
      thetaAdd_smul]
    rfl
  left_inv X := by simp
  right_inv X := by simp

private theorem cjSemi_apply (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2)
    (g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) (X : WQ n a) :
    cjSemi n a ha hn hF hK g X =
      thetaEquiv n a ha hn hF hK (g ((thetaEquiv n a ha hn hF hK).symm X)) := rfl

private noncomputable def cjHomSemi (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) :
    ((Fin 4 → F) ≃ₗ[F] (Fin 4 → F)) →*
      (WQ n a ≃ₗ[SteinbergCB.frobFixed (sigQ n a)] WQ n a) where
  toFun g := cjSemi n a ha hn hF hK g
  map_one' := LinearEquiv.ext fun X => by simp [cjSemi_apply]
  map_mul' g h := LinearEquiv.ext fun X => by simp [cjSemi_apply]

private noncomputable def uncjSemi (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2)
    (h : WQ n a ≃ₗ[SteinbergCB.frobFixed (sigQ n a)] WQ n a) :
    (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) where
  toFun x := (thetaEquiv n a ha hn hF hK).symm (h (thetaEquiv n a ha hn hF hK x))
  invFun x := (thetaEquiv n a ha hn hF hK).symm (h.symm (thetaEquiv n a ha hn hF hK x))
  map_add' x y := by simp
  map_smul' c x := by
    simp only [RingHom.id_apply]
    have h1 : thetaEquiv n a ha hn hF hK (c • x) =
        iotaRing n a hF c • thetaEquiv n a ha hn hF hK x :=
      thetaAdd_smul n a hF hK c x
    rw [h1, LinearEquiv.map_smul, thetaEquiv_symm_smul n a ha hn hF hK c]
  left_inv x := by simp
  right_inv x := by simp

private theorem cjSemi_uncjSemi (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2)
    (h : WQ n a ≃ₗ[SteinbergCB.frobFixed (sigQ n a)] WQ n a) :
    cjSemi n a ha hn hF hK (uncjSemi n a ha hn hF hK h) = h := by
  refine LinearEquiv.ext fun X => ?_
  rw [cjSemi_apply]
  simp [uncjSemi]

private theorem twistedDet_thetaEquiv (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) (x : Fin 4 → F) :
    SteinbergCB.twistedDet (sigQ n a) (thetaEquiv n a ha hn hF hK x) =
      iotaRing n a hF (orthMinus F a x) := by
  apply Subtype.ext
  rw [SteinbergCB.twistedDet_apply]
  exact hermOf_det hn hF hK ha x

private theorem map_isometry_minus (n : ℕ) (a : F) [Fact (Irreducible (quadPoly a))]
    [CharP (AdjoinRoot (quadPoly a)) 2] [Finite F] [Finite (AdjoinRoot (quadPoly a))]
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n) (hF : Nat.card F = 2 ^ n)
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) :
    Subgroup.map (cjHomSemi n a ha hn hF hK) (isometryGroup F (orthMinus F a)) =
      SteinbergCB.isometryGroup (SteinbergCB.twistedDet (sigQ n a)) := by
  ext h
  constructor
  · rintro ⟨g, hg, rfl⟩
    intro X
    obtain ⟨y, rfl⟩ := (thetaEquiv n a ha hn hF hK).surjective X
    have hg' : ∀ x, orthMinus F a (g x) = orthMinus F a x := hg
    change SteinbergCB.twistedDet (sigQ n a) (cjSemi n a ha hn hF hK g
      (thetaEquiv n a ha hn hF hK y)) = SteinbergCB.twistedDet (sigQ n a)
      (thetaEquiv n a ha hn hF hK y)
    rw [cjSemi_apply, AddEquiv.symm_apply_apply, twistedDet_thetaEquiv, twistedDet_thetaEquiv,
      hg' y]
  · intro hh
    refine ⟨uncjSemi n a ha hn hF hK h, ?_, cjSemi_uncjSemi n a ha hn hF hK h⟩
    intro x
    have h2 : thetaEquiv n a ha hn hF hK (uncjSemi n a ha hn hF hK h x) =
        h (thetaEquiv n a ha hn hF hK x) := by
      simp [uncjSemi]
    have h3 : SteinbergCB.twistedDet (sigQ n a)
        (thetaEquiv n a ha hn hF hK (uncjSemi n a ha hn hF hK h x)) =
        SteinbergCB.twistedDet (sigQ n a) (thetaEquiv n a ha hn hF hK x) := by
      rw [h2]
      exact hh _
    rw [twistedDet_thetaEquiv, twistedDet_thetaEquiv] at h3
    exact (iotaRing_bijective n a hn hF hK).1 h3

end MinusGroup

section MinusBridge

open scoped Matrix

open CFSG.Quasithin.H13.H11M (VH hm mkH rhoH LH NH SigInv hm_rhoH hm_injective hm_mem)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)

variable {F : Type} [Field F] [CharP F 2] {n : ℕ} {a : F}
  [Fact (Irreducible (quadPoly a))] [CharP (AdjoinRoot (quadPoly a)) 2]

private theorem sigInv_sigQ [Finite (AdjoinRoot (quadPoly a))]
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) :
    ∀ x, sigQ n a (sigQ n a x) = x := fun x => frob_iter_iter hK x

private theorem sigInv_of_card [Finite (AdjoinRoot (quadPoly a))]
    (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) :
    SigInv n (AdjoinRoot (quadPoly a)) := sigInv_sigQ hK

private theorem herm_of_twisted (hinv : ∀ x, sigQ n a (sigQ n a x) = x)
    {X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (quadPoly a))}
    (hX : X ∈ SteinbergCB.twistedForm (sigQ n a)) :
    X ∈ JonesParshall.hermA n (AdjoinRoot (quadPoly a)) := by
  rw [JonesParshall.mem_hermA, JonesParshall.frobPow_eq_map]
  have hX' : Xᵀ = X.map (sigQ n a) := hX
  change (X.map (sigQ n a))ᵀ = X
  rw [← Matrix.transpose_map, hX']
  ext i j
  simp [hinv]

private theorem twisted_of_herm
    {X : Matrix (Fin 2) (Fin 2) (AdjoinRoot (quadPoly a))}
    (hX : X ∈ JonesParshall.hermA n (AdjoinRoot (quadPoly a))) :
    X ∈ SteinbergCB.twistedForm (sigQ n a) := by
  rw [SteinbergCB.mem_twistedForm]
  have h := JonesParshall.mem_hermA.mp hX
  rw [JonesParshall.frobPow_eq_map] at h
  calc Xᵀ = (((JonesParshall.sig n).mapMatrix X)ᵀ)ᵀ := by rw [h]
    _ = X.map (sigQ n a) := by rw [Matrix.transpose_transpose]; rfl

private noncomputable def phiEquiv (hinv : ∀ x, sigQ n a (sigQ n a x) = x) :
    Multiplicative (WQ n a) ≃* VH n (AdjoinRoot (quadPoly a)) where
  toFun X := mkH (Multiplicative.toAdd X : WQ n a).1
    (herm_of_twisted hinv (Multiplicative.toAdd X).2)
  invFun v := Multiplicative.ofAdd ⟨hm v, twisted_of_herm (hm_mem v)⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

private theorem congr_phiEquiv_twistRep (hinv : ∀ x, sigQ n a (sigQ n a x) = x)
    (g : SL₂ (AdjoinRoot (quadPoly a))) :
    MulAut.congr (phiEquiv hinv)
      (linToMulAut (SteinbergCB.frobFixed (sigQ n a)) (WQ n a) (SteinbergCB.twistRep hinv g)) =
      rhoH hinv g :=
  MulEquiv.ext fun v => hm_injective rfl

variable [Finite F] [Finite (AdjoinRoot (quadPoly a))]

private theorem map_omegaFour_theta (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) :
    (omegaFour F (orthMinus F a)).map
      (MulAut.congr (AddEquiv.toMultiplicative (thetaEquiv n a ha hn hF hK))).toMonoidHom =
    (SteinbergCB.twistRep (sigInv_sigQ hK)).range.map
      (linToMulAut (SteinbergCB.frobFixed (sigQ n a)) (WQ n a)) := by
  unfold omegaFour
  rw [Subgroup.map_map]
  have hcomp : (MulAut.congr
      (AddEquiv.toMultiplicative (thetaEquiv n a ha hn hF hK))).toMonoidHom.comp
        (linToMulAut F (Fin 4 → F)) =
      (linToMulAut (SteinbergCB.frobFixed (sigQ n a)) (WQ n a)).comp
        (cjHomSemi n a ha hn hF hK) :=
    MonoidHom.ext fun g => MulEquiv.ext fun X => rfl
  rw [hcomp, ← Subgroup.map_map, Subgroup.map_commutator,
    map_isometry_minus n a ha hn hF hK,
    CFSG.Quasithin.G11.Harris.L2.twistRep_range_eq hn hK (fun x => iterateFrobenius_def 2 n x)]

private noncomputable def psiEquiv (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) :
    Multiplicative (Fin 4 → F) ≃* VH n (AdjoinRoot (quadPoly a)) :=
  (AddEquiv.toMultiplicative (thetaEquiv n a ha hn hF hK)).trans (phiEquiv (sigInv_sigQ hK))

private theorem omega_minus_map (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2) :
    (omegaFour F (orthMinus F a)).map (MulAut.congr (psiEquiv ha hn hF hK)).toMonoidHom =
      LH (sigInv_of_card hK) := by
  have hcomp : (MulAut.congr (psiEquiv ha hn hF hK)).toMonoidHom =
      (MulAut.congr (phiEquiv (sigInv_sigQ hK))).toMonoidHom.comp
        (MulAut.congr (AddEquiv.toMultiplicative (thetaEquiv n a ha hn hF hK))).toMonoidHom :=
    MonoidHom.ext fun x => MulEquiv.ext fun y => by
      simp [psiEquiv, MulAut.congr_apply, MulEquiv.trans_apply]
  rw [hcomp, ← Subgroup.map_map, map_omegaFour_theta ha hn hF hK, Subgroup.map_map,
    MonoidHom.map_range]
  exact congrArg MonoidHom.range
    (MonoidHom.ext fun g => congr_phiEquiv_twistRep (sigInv_sigQ hK) g)

end MinusBridge

section ModelK

open CFSG.Assembly.LowTwoRank (StatedSL)
open CFSG.Quasithin.H13.H11P (slE)
open CFSG.Quasithin.H13.H11M (VH hm mkH rhoH LH NH SigInv hm_rhoH hm_injective hm_mem)
open CFSG.RankThree.PartOne.KCRootAxis (SL₂)

variable {K : Type} [Field K] [CharP K 2] {n : ℕ}

private theorem realizes_minus (hσ : SigInv n K) {V : Type} [CommGroup V]
    {L : Subgroup (MulAut V)} (E : V ≃* VH n K) (h : L.map (MulAut.congr E).toMonoidHom = LH hσ) :
    (FFModel.twistTensor n (StatedSL 2 K)).Realizes L ⊤ ⊥ := by
  classical
  have hmem : ∀ g : SL₂ K, (MulAut.congr E).symm (rhoH hσ g) ∈ L := by
    intro g
    have hp : rhoH hσ g ∈ L.map (MulAut.congr E).toMonoidHom := by
      rw [h]; exact ⟨g, rfl⟩
    obtain ⟨x, hx, hxp⟩ := hp
    have hxe : x = (MulAut.congr E).symm (rhoH hσ g) := by
      rw [MulEquiv.eq_symm_apply]; exact hxp
    rw [← hxe]; exact hx
  let π₀ : StatedSL 2 K →* MulAut V :=
    (MulAut.congr E).symm.toMonoidHom.comp ((rhoH hσ).comp (slE K).toMonoidHom)
  have hπ₀ : ∀ γ, π₀ γ ∈ L := fun γ => hmem _
  let π : ↥(StatedSL 2 K) →* ↥L := π₀.codRestrict L hπ₀
  have hπγ : ∀ γ, ((π γ : ↥L) : MulAut V) = (MulAut.congr E).symm (rhoH hσ (slE K γ)) :=
    fun γ => rfl
  have key : ∀ (γ : ↥(StatedSL 2 K)) (u : V),
      E (((π γ : ↥L) : MulAut V) u) = rhoH hσ (slE K γ) (E u) := by
    intro γ u
    rw [hπγ]
    have hf : MulAut.congr E ((MulAut.congr E).symm (rhoH hσ (slE K γ))) =
        rhoH hσ (slE K γ) := MulEquiv.apply_symm_apply _ _
    have h2 := congrArg (fun g : MulAut (VH n K) => g (E u)) hf
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h2
    exact h2
  let φ : (⊤ : Subgroup V) →* ↥(CFSG.Quasithin.hermSub n (Fin 2) K) :=
    E.toMonoidHom.comp (⊤ : Subgroup V).subtype
  let β := (QuotientGroup.mk' ((⊥ : Subgroup (Multiplicative (Matrix (Fin 2) (Fin 2) K))).subgroupOf
    (CFSG.Quasithin.hermSub n (Fin 2) K))).comp φ
  refine ⟨π, ?_, bot_le, bot_le, fun _ _ _ => Subgroup.mem_top _, ?_, ?_, ?_, β, ?_, ?_, ?_⟩
  ·
    intro x
    have hx : (MulAut.congr E).toMonoidHom (x : MulAut V) ∈
        L.map (MulAut.congr E).toMonoidHom := Subgroup.mem_map_of_mem _ x.2
    rw [h] at hx
    obtain ⟨g, hg⟩ := hx
    refine ⟨(slE K).symm g, Subtype.ext ?_⟩
    refine (hπγ _).trans ?_
    simp only [MulEquiv.apply_symm_apply]
    rw [hg]
    exact MulEquiv.symm_apply_apply _ _
  · intro h' z hz
    have hz1 : z = 1 := (Subgroup.mem_bot (G := V)).mp hz
    subst hz1
    rw [map_one]
    exact Subgroup.one_mem _
  · intro γ m hm'
    have h1 := CFSG.Quasithin.H13.H11M.act_eq_rhoH hσ γ ⟨m, hm'⟩
    have h2 := (rhoH hσ (slE K γ) ⟨m, hm'⟩).2
    rwa [← h1] at h2
  · intro γ m hm'
    have hm1 : m = 1 := (Subgroup.mem_bot (G := Multiplicative (Matrix (Fin 2) (Fin 2) K))).mp hm'
    subst hm1
    have h1 : (FFModel.twistTensor n (StatedSL 2 K)).act γ 1 = 1 := by
      show Multiplicative.ofAdd (_ * (0 : Matrix (Fin 2) (Fin 2) K) * _) =
        (1 : Multiplicative (Matrix (Fin 2) (Fin 2) K))
      rw [mul_zero, zero_mul]
      rfl
    rw [h1]
    exact Subgroup.one_mem _
  · intro q
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective q
    refine ⟨⟨E.symm (m : VH n K), Subgroup.mem_top _⟩, ?_⟩
    change (QuotientGroup.mk (E (E.symm (m : VH n K))) : _ ⧸ _) = QuotientGroup.mk m
    exact congrArg QuotientGroup.mk (MulEquiv.apply_symm_apply E _)
  · intro u
    change (QuotientGroup.mk (E u.1) : _ ⧸ _) = 1 ↔ (u : V) ∈ (⊥ : Subgroup V)
    refine (QuotientGroup.eq_one_iff _).trans ?_
    rw [Subgroup.mem_subgroupOf]
    simp only [Subgroup.mem_bot, OneMemClass.coe_eq_one]
    exact E.map_eq_one_iff.trans OneMemClass.coe_eq_one
  · rintro γ u ⟨m₀, hm₀⟩ hu hm0 hβu
    let mm : VH n K := ⟨m₀, hm₀⟩
    have h0 : (QuotientGroup.mk (E u.1) : _ ⧸ _) = QuotientGroup.mk mm := hβu
    have h1 := Subgroup.mem_subgroupOf.mp (QuotientGroup.eq.mp h0)
    have h2 : (E u.1)⁻¹ * mm = 1 := OneMemClass.coe_eq_one.mp (Subgroup.mem_bot.mp h1)
    have h3 : mm = E u.1 := (inv_mul_eq_one.mp h2).symm
    show (QuotientGroup.mk (E (((π γ : ↥L) : MulAut V) u.1)) : _ ⧸ _) = QuotientGroup.mk ⟨_, hm0⟩
    refine congrArg QuotientGroup.mk (Subtype.ext ?_)
    show ((E (((π γ : ↥L) : MulAut V) u.1) : VH n K) : Multiplicative (Matrix (Fin 2) (Fin 2) K)) =
      (FFModel.twistTensor n (StatedSL 2 K)).act γ m₀
    rw [show (FFModel.twistTensor n (StatedSL 2 K)).act γ m₀ =
      ((rhoH hσ (slE K γ) mm : VH n K) : Multiplicative (Matrix (Fin 2) (Fin 2) K)) from
        CFSG.Quasithin.H13.H11M.act_eq_rhoH hσ γ mm, h3]
    exact congrArg Subtype.val (key γ u.1)

private theorem hm_smul_of_involution [Fintype K] (hσ : SigInv n K) (hn : 1 ≤ n)
    (hKc : Fintype.card K = 2 ^ (2 * n)) {t' : MulAut (VH n K)} (ht'N : t' ∈ NH hσ)
    (ht'2 : t' * t' = 1) (c : K) (hc : JonesParshall.sig n c = c) (v w : VH n K)
    (hvw : hm w = c • hm v) : hm (t' w) = c • hm (t' v) := by
  obtain ⟨θ₀, hθ₀⟩ := CFSG.Quasithin.H13.H11M.exists_sig_ne hn hKc
  rcases CFSG.Quasithin.H13.H11M.mem_LH_or_formS hσ hn hKc hθ₀ ht'N ht'2 with ⟨g, rfl⟩ | ⟨M, hM⟩
  · rw [hm_rhoH, hm_rhoH, hvw, Matrix.mul_smul, Matrix.smul_mul]
  · rw [hM.2, hM.2, hvw, CFSG.Quasithin.H13.H11M.frobPow_smul, hc, Matrix.mul_smul,
      Matrix.smul_mul]

end ModelK

section MinusMain

open CFSG.Quasithin.H13.H11M (VH hm rhoH LH NH SigInv)

variable {F : Type} [Field F]

private theorem fin4_transvection [CharP F 2] [Finite F] (hF4 : Nat.card F = 4)
    (T : MulAut (Multiplicative (Fin 4 → F))) (hT2 : T * T = 1)
    (hlin : ∀ (c : F) (x : Fin 4 → F),
      Multiplicative.toAdd (T (Multiplicative.ofAdd (c • x))) =
        c • Multiplicative.toAdd (T (Multiplicative.ofAdd x)))
    (hcard : Nat.card (fixV (Subgroup.zpowers T)) = 64) :
    IsFTransvection F (Fin 4) T := by
  classical
  have hTT : ∀ y, T (T y) = y := fun y => by
    rw [← MulAut.mul_apply, hT2, MulAut.one_apply]
  let g : (Fin 4 → F) ≃ₗ[F] (Fin 4 → F) :=
    { toFun := fun x => Multiplicative.toAdd (T (Multiplicative.ofAdd x))
      invFun := fun x => Multiplicative.toAdd (T (Multiplicative.ofAdd x))
      map_add' := fun x y => by
        show Multiplicative.toAdd (T (Multiplicative.ofAdd (x + y))) =
          Multiplicative.toAdd (T (Multiplicative.ofAdd x)) +
            Multiplicative.toAdd (T (Multiplicative.ofAdd y))
        rw [ofAdd_add, map_mul]
        rfl
      map_smul' := fun c x => hlin c x
      left_inv := fun x => by
        show Multiplicative.toAdd (T (Multiplicative.ofAdd
          (Multiplicative.toAdd (T (Multiplicative.ofAdd x))))) = x
        rw [ofAdd_toAdd, hTT]
        rfl
      right_inv := fun x => by
        show Multiplicative.toAdd (T (Multiplicative.ofAdd
          (Multiplicative.toAdd (T (Multiplicative.ofAdd x))))) = x
        rw [ofAdd_toAdd, hTT]
        rfl }
  have hgX : ∀ x, g x = Multiplicative.toAdd (T (Multiplicative.ofAdd x)) := fun x => rfl
  have hgg : ∀ x, g (g x) = x := by
    intro x
    rw [hgX, hgX, ofAdd_toAdd, hTT]
    rfl
  set N := g.toLinearMap - LinearMap.id with hN
  have hNX : ∀ Z, N Z = g Z - Z := fun Z => rfl
  refine ⟨g, MulEquiv.ext fun y => rfl, ?_, ?_⟩
  · show Module.finrank F (LinearMap.range N) = 1
    have hrn := LinearMap.finrank_range_add_finrank_ker N
    have hfin : Module.finrank F (Fin 4 → F) = 4 := by simp
    have hker_iff : ∀ x : Fin 4 → F, x ∈ LinearMap.ker N ↔ T (Multiplicative.ofAdd x) =
        Multiplicative.ofAdd x := by
      intro x
      rw [LinearMap.mem_ker, hNX, sub_eq_zero]
      constructor
      · intro h
        exact h
      · intro h
        exact h
    have hkerNat : Nat.card (LinearMap.ker N) = 64 := by
      rw [← hcard]
      refine Nat.card_congr
        { toFun := fun x => ⟨Multiplicative.ofAdd (x : Fin 4 → F),
            CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mpr ((hker_iff _).mp x.2)⟩
          invFun := fun y => ⟨Multiplicative.toAdd (y : Multiplicative (Fin 4 → F)),
            (hker_iff _).mpr (CFSG.Quasithin.mem_fixV_zpowers_iff_apply.mp y.2)⟩
          left_inv := fun x => rfl
          right_inv := fun y => rfl }
    have hkerf : Module.finrank F (LinearMap.ker N) = 3 := by
      have h := Module.natCard_eq_pow_finrank (K := F) (V := LinearMap.ker N)
      rw [hkerNat, hF4] at h
      have h' : (4 : ℕ) ^ Module.finrank F (LinearMap.ker N) = 4 ^ 3 := by
        rw [← h]
        norm_num
      exact Nat.pow_right_injective (by norm_num) h'
    rw [hfin, hkerf] at hrn
    omega
  · show N ∘ₗ N = 0
    apply LinearMap.ext
    intro X
    have h2 : ∀ Y : Fin 4 → F, Y + Y = 0 := fun Y => CharTwo.add_self_eq_zero Y
    rw [LinearMap.comp_apply, LinearMap.zero_apply, hNX (N X), hNX X, map_sub, hgg]
    have h3 : X - g X - (g X - X) = (X + X) - (g X + g X) := by abel
    rw [h3, h2 X, h2 (g X), sub_self]

end MinusMain

section MinusAssembly

open CFSG.Quasithin.H13.H11M (VH hm rhoH LH NH SigInv)

variable {F : Type} [Field F] [CharP F 2] {n : ℕ} {a : F}
  [Fact (Irreducible (quadPoly a))] [CharP (AdjoinRoot (quadPoly a)) 2]
  [Finite F] [Finite (AdjoinRoot (quadPoly a))]

private theorem fin4_linear (ha : ∀ t : F, t ^ 2 + t + a ≠ 0) (hn : 1 ≤ n)
    (hF : Nat.card F = 2 ^ n) (hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2)
    (T : MulAut (Multiplicative (Fin 4 → F)))
    (hT : MulAut.congr (psiEquiv ha hn hF hK) T ∈ NH (sigInv_of_card hK)) (hT2 : T * T = 1)
    (c : F) (x : Fin 4 → F) :
    Multiplicative.toAdd (T (Multiplicative.ofAdd (c • x))) =
      c • Multiplicative.toAdd (T (Multiplicative.ofAdd x)) := by
  classical
  have : Fintype (AdjoinRoot (quadPoly a)) := Fintype.ofFinite _
  have hKc : Fintype.card (AdjoinRoot (quadPoly a)) = 2 ^ (2 * n) := by
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul, mul_comm]
  set Ψ := psiEquiv ha hn hF hK with hΨ
  set t' := MulAut.congr Ψ T with ht'
  have ht'2 : t' * t' = 1 := by rw [ht', ← map_mul, hT2, map_one]
  have hΨT : ∀ y, Ψ (T y) = t' (Ψ y) := fun y => by
    rw [ht', MulAut.congr_apply]
    simp
  have hfix : JonesParshall.sig n (algebraMap F (AdjoinRoot (quadPoly a)) c) =
      algebraMap F (AdjoinRoot (quadPoly a)) c := iterate_frob_algebraMap_fix hF c
  refine (hermOf_eq_iff (n := n) (ha := ha) _ _).mp ?_
  have e1 : hermOf n a (Multiplicative.toAdd (T (Multiplicative.ofAdd (c • x)))) =
      hm (t' (Ψ (Multiplicative.ofAdd (c • x)))) := by
    rw [← hΨT]
    rfl
  have e2 : hermOf n a (Multiplicative.toAdd (T (Multiplicative.ofAdd x))) =
      hm (t' (Ψ (Multiplicative.ofAdd x))) := by
    rw [← hΨT]
    rfl
  have e3 : hm (Ψ (Multiplicative.ofAdd (c • x))) =
      algebraMap F (AdjoinRoot (quadPoly a)) c • hm (Ψ (Multiplicative.ofAdd x)) :=
    hermOf_smul hF c x
  rw [hermOf_smul hF, e1, e2]
  exact hm_smul_of_involution (sigInv_of_card hK) hn hKc hT ht'2 _ hfix _ _ e3

end MinusAssembly

theorem h11_minus {F : Type} [Field F] [Finite F] [CharP F 2] {V : Type} [CommGroup V]
    [Finite V] (hV2 : ∀ v : V, v ^ 2 = 1) {n : ℕ} (hn : 2 ≤ n) (hF : Nat.card F = 2 ^ n)
    (M : Subgroup (MulAut V)) (e : V ≃* Multiplicative (Fin 4 → F)) (a : F)
    (ha : ∀ t : F, t ^ 2 + t + a ≠ 0)
    (hO : (perfectCore M).map (MulAut.congr e).toMonoidHom = omegaFour F (orthMinus F a))
    (A : Subgroup (MulAut V)) (hA : IsA2 M A) :
    rk ↥A + n ≤ rkIdx (fixV A) + 1 ∧
      (rk ↥A + 2 ≤ rkIdx (fixV A) ∨
        (n = 2 ∧ ∃ t ∈ A, IsFTransvection F (Fin 4) (MulAut.congr e t))) ∧
      (A ≤ perfectCore M → rk ↥A + n ≤ rkIdx (fixV A)) := by
  classical
  haveI : Fact (Irreducible (quadPoly a)) := ⟨quadPoly_irreducible ha⟩
  haveI : CharP (AdjoinRoot (quadPoly a)) 2 :=
    charP_of_injective_algebraMap (algebraMap F (AdjoinRoot (quadPoly a))).injective 2
  have hK : Nat.card (AdjoinRoot (quadPoly a)) = (2 ^ n) ^ 2 := by
    rw [natCard_adjoinRoot_quad a hF, ← pow_mul, mul_comm]
  haveI : Finite (AdjoinRoot (quadPoly a)) := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
  have hn1 : 1 ≤ n := by omega
  set Ψ := psiEquiv ha hn1 hF hK with hΨ
  set E : V ≃* CFSG.Quasithin.H13.H11M.VH n (AdjoinRoot (quadPoly a)) := e.trans Ψ with hE
  have hcomp : (MulAut.congr E).toMonoidHom =
      (MulAut.congr Ψ).toMonoidHom.comp (MulAut.congr e).toMonoidHom :=
    MonoidHom.ext fun x => MulEquiv.ext fun y => by
      simp [hE, MulAut.congr_apply, MulEquiv.trans_apply]
  have hcomp' : ∀ x, MulAut.congr E x = MulAut.congr Ψ (MulAut.congr e x) :=
    fun x => DFunLike.congr_fun hcomp x
  have hL : (perfectCore M).map (MulAut.congr E).toMonoidHom =
      CFSG.Quasithin.H13.H11M.LH (sigInv_of_card hK) := by
    rw [hcomp, ← Subgroup.map_map, hO]
    exact omega_minus_map ha hn1 hF hK
  have hreal := realizes_minus (sigInv_of_card hK) E hL
  have hLM : perfectCore M ≤ M := perfectCore_le M
  have hMN : M ≤ Subgroup.normalizer (perfectCore M : Set (MulAut V)) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (perfectCore_le M)).mp (perfectCore_normal M)
  have hKc : Nat.card (AdjoinRoot (quadPoly a)) = 2 ^ (2 * n) := by
    rw [hK, ← pow_mul, mul_comm]
  obtain ⟨c1, c2, c3⟩ := CFSG.Quasithin.H13.ch6InH11_holds V (perfectCore M) M n hV2 (by omega)
    hLM hMN ⟨AdjoinRoot (quadPoly a), inferInstance, inferInstance, inferInstance, hKc, hreal⟩
    A hA.1 hA.2.1 hA.2.2
  refine ⟨c1, ?_, c3⟩
  rcases c2 with c2 | ⟨hn2, t, htA, hrk⟩
  · exact Or.inl c2
  · refine Or.inr ⟨hn2, t, htA, ?_⟩
    have hF4 : Nat.card F = 4 := by rw [hF, hn2]; norm_num
    have htM : t ∈ M := hA.1 htA
    have ht2 : t * t = 1 := by
      rw [← sq]
      exact hA.2.2.2 t htA
    have hV : Nat.card V = 2 ^ 8 := by
      have hm : Nat.card (Multiplicative (Fin 4 → F)) = Nat.card (Fin 4 → F) := rfl
      rw [Nat.card_congr e.toEquiv, hm, natCard_fin4_fun hF4]
    have hrk2 : rkIdx (fixV (Subgroup.zpowers t)) = 2 := by rw [hrk, hn2]
    have hH := card_mul_pow_of_rkIdx (fixV (Subgroup.zpowers t)) hV
    rw [hrk2] at hH
    have hHcard : Nat.card (fixV (Subgroup.zpowers t)) = 64 := by omega
    have hfix' : fixV (Subgroup.zpowers (MulAut.congr e t)) =
        (fixV (Subgroup.zpowers t)).map e.toMonoidHom := by
      have := CFSG.Quasithin.fixV_map_congr_equiv e (Subgroup.zpowers t)
      rw [MonoidHom.map_zpowers] at this
      exact this
    have hcard' : Nat.card (fixV (Subgroup.zpowers (MulAut.congr e t))) = 64 := by
      rw [hfix', Subgroup.card_map_of_injective e.injective, hHcard]
    have hT2 : MulAut.congr e t * MulAut.congr e t = 1 := by
      rw [← map_mul, ht2, map_one]
    have htN : MulAut.congr Ψ (MulAut.congr e t) ∈
        CFSG.Quasithin.H13.H11M.NH (sigInv_of_card hK) := by
      rw [← hcomp']
      have h1 : MulAut.congr E t ∈
          (Subgroup.normalizer (perfectCore M : Set (MulAut V))).map
            (MulAut.congr E).toMonoidHom := Subgroup.mem_map_of_mem _ (hMN htM)
      rw [Subgroup.map_equiv_normalizer_eq, hL] at h1
      exact h1
    exact fin4_transvection hF4 _ hT2 (fin4_linear ha hn1 hF hK _ htN hT2) hcard'

end CFSG.Quasithin.H11Proof

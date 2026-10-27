module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenFixHalfCover
import CFSG.ClassicalGroups.Symplectic.StandardForm
import CFSG.Quasithin.Background.B4L3Coord
import CFSG.Quasithin.Background.F918D0
import CFSG.Quasithin.Background.JonesParshallSymplecticBinary
import CFSG.Quasithin.Background.JonesParshallSymplecticField
import CFSG.Quasithin.Vol2.Ch3B513NSelfDual

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup
open scoped Matrix

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

private noncomputable def s16nt_spMap {F L : Type} [Field F] [Field L] (f : F →+* L) (r : ℕ) :
    ↥(StatedSp r F) →* ↥(StatedSp r L) :=
  ((Matrix.GeneralLinearGroup.map f).comp (StatedSp r F).subtype).codRestrict (StatedSp r L)
    fun g => StatedAPI.map_mem_statedSp f g.2

private theorem s16nt_spMap_apply {F L : Type} [Field F] [Field L] (f : F →+* L) (r : ℕ)
    (g : ↥(StatedSp r F)) (i j : Fin r ⊕ Fin r) :
    ((s16nt_spMap f r g : Matrix.GeneralLinearGroup (Fin r ⊕ Fin r) L) :
      Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) L) i j =
      f (((g : Matrix.GeneralLinearGroup (Fin r ⊕ Fin r) F) :
        Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) F) i j) :=
  rfl

private theorem s16nt_spMap_surjective {F L : Type} [Field F] [Field L] (e : F ≃+* L) (r : ℕ) :
    Function.Surjective (s16nt_spMap (e.symm : L →+* F) r) := by
  intro g
  refine ⟨s16nt_spMap (e : F →+* L) r g, ?_⟩
  apply Subtype.ext
  apply Matrix.GeneralLinearGroup.ext
  intro i j
  rw [s16nt_spMap_apply, s16nt_spMap_apply]
  exact e.symm_apply_apply _

private theorem s16nt_map_mulVec {F L : Type} [Field F] [Field L] (e : F ≃+* L) {r : ℕ}
    (A : Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) L) (x : Fin r ⊕ Fin r → F) (i : Fin r ⊕ Fin r) :
    e ((A.map e.symm *ᵥ x) i) = (A *ᵥ fun j => e (x j)) i := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul,
    RingEquiv.apply_symm_apply]

theorem s16nt_cover_sp_binary {K : Type} [Field K] [Finite K] (r : ℕ) (hK : Nat.card K = 2) :
    S16BoundCover (FFModel.nat (StatedSp r K)) 1 := by
  intro W _ _ hW2 H Z hZ hcomm hreal
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card]; exact hK
  let e : K ≃+* ZMod 2 := (ZMod.ringEquivOfPrime K Nat.prime_two hF).symm
  let B := ClassicalGroups.Symplectic.spForm r (ZMod 2)
  let σ : ↥(StatedSp r (ZMod 2)) ≃* ↥(LocalAnalysis.ComponentInitial.bilinIsometryGroup B) :=
    ClassicalGroups.Symplectic.spEquiv
  let θ : ↥(LocalAnalysis.ComponentInitial.bilinIsometryGroup B) →* ↥(StatedSp r K) :=
    (s16nt_spMap (e.symm : ZMod 2 →+* K) r).comp σ.symm.toMonoidHom
  have hθ : Function.Surjective θ := (s16nt_spMap_surjective e r).comp σ.symm.surjective
  have : Finite ↥(StatedSp r (ZMod 2)) := Subtype.finite
  have : Finite ↥(LocalAnalysis.ComponentInitial.bilinIsometryGroup B) :=
    Finite.of_equiv _ σ.toEquiv
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  let Φ : Multiplicative (Fin r ⊕ Fin r → K) ≃* Multiplicative (Fin r ⊕ Fin r → ZMod 2) :=
    AddEquiv.toMultiplicative (AddEquiv.piCongrRight fun _ => e.toAddEquiv)
  let β' : ↥(⊤ : Subgroup W) →* Multiplicative (Fin r ⊕ Fin r → ZMod 2) := Φ.toMonoidHom.comp β
  have hcomm' : XMod.commOf ↥H (⊤ : Subgroup W) = ⊤ := by
    rw [commOf_eq_commSub, ← commV_eq_commSub]; exact hcomm
  have hact : ∀ (γ : ↥(LocalAnalysis.ComponentInitial.bilinIsometryGroup B))
      (x : Fin r ⊕ Fin r → ZMod 2), JonesParshall.binarySymplecticNatural B γ x =
        ((σ.symm γ : Matrix.GeneralLinearGroup (Fin r ⊕ Fin r) (ZMod 2)) :
          Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) (ZMod 2)) *ᵥ x := by
    intro γ x
    have h := ClassicalGroups.Symplectic.spEquiv_app (σ.symm γ) x
    rw [show ClassicalGroups.Symplectic.spEquiv (σ.symm γ) = γ from σ.apply_symm_apply γ] at h
    exact h
  have hβk' : ∀ v : ↥(⊤ : Subgroup W), β' v = 1 ↔ (v : W) ∈ Z := fun v => by
    show Φ (β v) = 1 ↔ (v : W) ∈ Z
    exact (map_eq_one_iff Φ Φ.injective).trans (hβk v)
  have hβe' : ∀ (γ : ↥(LocalAnalysis.ComponentInitial.bilinIsometryGroup B))
      (v : ↥(⊤ : Subgroup W)) (hv : ((π.comp θ γ : ↥H) : MulAut W) (v : W) ∈ (⊤ : Subgroup W)),
      β' ⟨((π.comp θ γ : ↥H) : MulAut W) (v : W), hv⟩ =
        Multiplicative.ofAdd (JonesParshall.binarySymplecticNatural B γ
          (Multiplicative.toAdd (β' v))) := by
    intro γ v hv
    have h1 : β' ⟨((π.comp θ γ : ↥H) : MulAut W) (v : W), hv⟩ =
        Φ ((FFModel.nat (StatedSp r K)).act (θ γ) (β v)) := congrArg Φ (hβe (θ γ) v hv)
    rw [h1, hact]
    apply Multiplicative.toAdd.injective
    funext i
    exact s16nt_map_mulVec e _ _ i
  have hcard := card_le_pow_finrank_H1_dual
    (Γ := ↥(LocalAnalysis.ComponentInitial.bilinIsometryGroup B)) hW2 H ⊤ Z le_top
    (fun z hz x hx => mem_fixV.1 (hZ hz) x hx) (fun x hx v hv => Subgroup.mem_top _) hcomm'
    (π.comp θ) (hπ.1.comp hθ) (JonesParshall.binarySymplecticNatural B) β'
    (Φ.surjective.comp hβs) hβk' hβe'
  exact hcard.trans (Nat.pow_le_pow_right (by norm_num)
    (JonesParshall.finrank_H1_binarySymplecticNatural_dual_le_one
      ClassicalGroups.Symplectic.spForm_isAlt ClassicalGroups.Symplectic.spForm_nondegenerate))

section Rep

variable (r : ℕ) (K : Type) [Field K] [CharP K 2]

noncomputable local instance s16nt_algZ2 : Algebra (ZMod 2) K := ZMod.algebra K 2

private noncomputable def s16nt_natRep :
    Representation (ZMod 2) ↥(StatedSp r K) (Fin r ⊕ Fin r → K) where
  toFun γ := (Matrix.mulVecLin ((γ : Matrix.GeneralLinearGroup (Fin r ⊕ Fin r) K) :
    Matrix (Fin r ⊕ Fin r) (Fin r ⊕ Fin r) K)).restrictScalars (ZMod 2)
  map_one' := by
    ext x i
    simp
  map_mul' γ δ := by
    ext x i
    simp

private theorem s16nt_finrank_H1_dual_le [Finite K] {m : ℕ} (hK : Nat.card K = 2 ^ m)
    (hq : 2 < Nat.card K) :
    Module.finrank (ZMod 2) (JonesParshall.H1 (Representation.dual (s16nt_natRep r K))) ≤ m := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(StatedSp r K) := Subtype.finite
  have hinv : ∀ (γ : ↥(StatedSp r K)) (u x : Fin r ⊕ Fin r → K),
      ClassicalGroups.Symplectic.spForm r K (s16nt_natRep r K γ u) (s16nt_natRep r K γ x) =
        ClassicalGroups.Symplectic.spForm r K u x := fun γ u x =>
    (ClassicalGroups.Symplectic.mem_statedSp_iff_forall _).mp γ.2 u x
  have : Finite ↥(LocalAnalysis.ComponentInitial.bilinIsometryGroup
      (ClassicalGroups.Symplectic.spForm r K)) :=
    Finite.of_equiv _ (ClassicalGroups.Symplectic.spEquiv (m := r) (K := K)).toEquiv
  obtain ⟨k, hkq, hk⟩ := JonesParshall.exists_card_Z1A_eq_mul_le
    (JonesParshall.card_Z1A_spNatA_le hq ClassicalGroups.Symplectic.spForm_isAlt
      (ClassicalGroups.Symplectic.spForm_nondegenerate (m := r) (K := K)))
  have hH1 := B513N.card_H1_dual_of_selfDual K (s16nt_natRep r K)
    (ClassicalGroups.Symplectic.spForm r K) ClassicalGroups.Symplectic.spForm_nondegenerate.1 hinv
    ClassicalGroups.Symplectic.spEquiv (JonesParshall.spNatA _)
    (fun γ x => (ClassicalGroups.Symplectic.spEquiv_app γ x).symm) hk
  have : Finite (Module.Dual (ZMod 2) (Fin r ⊕ Fin r → K)) := by
    have : Module.Finite (ZMod 2) (Fin r ⊕ Fin r → K) := Module.Finite.of_finite
    exact Module.finite_of_finite (ZMod 2)
  have : Finite (↥(StatedSp r K) → Module.Dual (ZMod 2) (Fin r ⊕ Fin r → K)) := Pi.finite
  have : Finite (JonesParshall.H1 (Representation.dual (s16nt_natRep r K))) :=
    Finite.of_surjective _ (Submodule.Quotient.mk_surjective _)
  have h2 := FiniteField.pow_finrank_eq_natCard 2
    (JonesParshall.H1 (Representation.dual (s16nt_natRep r K)))
  rw [hH1] at h2
  rw [← Nat.pow_le_pow_iff_right (by norm_num : 1 < 2), h2, ← hK]
  exact hkq

end Rep

theorem s16nt_cover_sp_of_two_lt {K : Type} [Field K] [Finite K] (r : ℕ) {m : ℕ}
    (hK : Nat.card K = 2 ^ m) (hq : 2 < Nat.card K) :
    S16BoundCover (FFModel.nat (StatedSp r K)) m := by
  intro W _ _ hW2 H Z hZ hcomm hreal
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 ^ m := by rw [← Nat.card_eq_fintype_card]; exact hK
  have : CharP K 2 := charP_of_card_eq_prime_pow hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite ↥(StatedSp r K) := Subtype.finite
  let _ : Algebra (ZMod 2) K := ZMod.algebra K 2
  obtain ⟨π, hπ⟩ := hreal
  obtain ⟨β, hβs, hβk, hβe⟩ := FFModel.RealizesVia.coord rfl rfl hπ
  have hcomm' : XMod.commOf ↥H (⊤ : Subgroup W) = ⊤ := by
    rw [commOf_eq_commSub, ← commV_eq_commSub]; exact hcomm
  have hcard := card_le_pow_finrank_H1_dual (Γ := ↥(StatedSp r K)) hW2 H ⊤ Z le_top
    (fun z hz x hx => mem_fixV.1 (hZ hz) x hx) (fun x hx v hv => Subgroup.mem_top _) hcomm'
    π hπ.1 (s16nt_natRep r K) β hβs hβk (fun γ v hv => hβe γ v hv)
  exact hcard.trans (Nat.pow_le_pow_right (by norm_num) (s16nt_finrank_H1_dual_le r K hK hq))

theorem s16nt_cover_sp {K : Type} [Field K] [Finite K] (r : ℕ) {m : ℕ}
    (hK : Nat.card K = 2 ^ m) : S16BoundCover (FFModel.nat (StatedSp r K)) m := by
  rcases Nat.lt_or_ge 2 (Nat.card K) with hq | hq
  · exact s16nt_cover_sp_of_two_lt r hK hq
  · have hK2 : Nat.card K = 2 := le_antisymm hq Finite.one_lt_card
    have hm : m = 1 := Nat.pow_right_injective le_rfl ((hK.symm.trans hK2).trans (pow_one 2).symm)
    subst hm
    exact s16nt_cover_sp_binary r hK2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end

module

public import CFSG.Quasithin.Background.B5FinSpCore
public import CFSG.Quasithin.Background.B5FinTransport
public import CFSG.Quasithin.Background.B5Inputs
public import CFSG.Quasithin.Background.B4ModelsAction
public import CFSG.Timmesfeld.Transvection.QTwoSp

public section

namespace CFSG.Quasithin

open CFSG.ComponentClassification.PresentationLocal CFSG.Timmesfeld.Transvection.QTwo
  CFSG.ClassicalGroups.Symplectic CFSG.Assembly.LowTwoRank Matrix

namespace B5FinSp

@[expose] noncomputable def omegaEquiv : sympFour ≃* Equiv.Perm (Fin 6) :=
  MulEquiv.ofBijective omegaPerm ⟨omegaPerm_injective, omegaPerm_surjective⟩

theorem omegaEquiv_apply (h : sympFour) : omegaEquiv h = omegaPerm h := rfl

@[expose] noncomputable def rhoEquiv : sympFour ≃* TauCeti.GLSymplectic (Fin 2) (ZMod 2) :=
  (glFourEquiv.subgroupMap sympFour).trans (MulEquiv.subgroupCongr map_sympFour)

theorem coe_rhoEquiv (h : sympFour) :
    ((((rhoEquiv h : TauCeti.GLSymplectic (Fin 2) (ZMod 2)) : GL (Fin 2 ⊕ Fin 2) (ZMod 2))) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) (ZMod 2)) =
      Matrix.reindex fourIdx fourIdx
        (((h : GL (Fin 4) (ZMod 2))) : Matrix (Fin 4) (Fin 4) (ZMod 2)) := rfl

variable {K : Type} [Field K]

@[expose] noncomputable def theta (c : ZMod 2 ≃+* K) : Equiv.Perm (Fin 6) ≃* ↥(StatedSp 2 K) :=
  ((omegaEquiv.symm.trans rhoEquiv).trans (glSympRingEquiv 2 c)).trans
    (MulEquiv.subgroupCongr (statedSp_eq_GLSymplectic (n := 2) (K := K)).symm)

theorem theta_apply (c : ZMod 2 ≃+* K) (σ : Equiv.Perm (Fin 6)) (a b : Fin 2 ⊕ Fin 2) :
    (((theta c σ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
        a b =
      c ((((omegaEquiv.symm σ : sympFour) : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) (fourIdx.symm a) (fourIdx.symm b)) := by
  have h1 := glSympRingEquiv_apply 2 c (rhoEquiv (omegaEquiv.symm σ)) a b
  rw [coe_rhoEquiv] at h1
  exact h1

@[expose] def lfun (c : ZMod 2 ≃+* K) (v : Fin 4 → ZMod 2) : Fin 2 ⊕ Fin 2 → K :=
  fun a => c (v (fourIdx.symm a))

theorem lfun_add (c : ZMod 2 ≃+* K) (v w : Fin 4 → ZMod 2) :
    lfun c (v + w) = lfun c v + lfun c w := by
  funext a
  simp [lfun]

theorem lfun_injective (c : ZMod 2 ≃+* K) : Function.Injective (lfun c) := by
  intro v w h
  funext i
  have := congrFun h (fourIdx i)
  simpa [lfun] using this

theorem lfun_surjective (c : ZMod 2 ≃+* K) : Function.Surjective (lfun c) := by
  intro u
  refine ⟨fun i => c.symm (u (fourIdx i)), ?_⟩
  funext a
  simp [lfun]

@[expose] noncomputable def lhom (c : ZMod 2 ≃+* K) :
    Multiplicative (Fin 4 → ZMod 2) →* Multiplicative (Fin 2 ⊕ Fin 2 → K) where
  toFun w := Multiplicative.ofAdd (lfun c (Multiplicative.toAdd w))
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext a
    simp [lfun]
  map_mul' _ _ := by
    exact congrArg Multiplicative.ofAdd (lfun_add c _ _)

theorem toAdd_lhom (c : ZMod 2 ≃+* K) (w : Multiplicative (Fin 4 → ZMod 2)) :
    Multiplicative.toAdd (lhom c w) = lfun c (Multiplicative.toAdd w) := rfl

theorem lhom_injective (c : ZMod 2 ≃+* K) : Function.Injective (lhom c) := fun _ _ h =>
  Multiplicative.toAdd.injective (lfun_injective c (congrArg Multiplicative.toAdd h))

theorem lhom_surjective (c : ZMod 2 ≃+* K) : Function.Surjective (lhom c) := fun t => by
  obtain ⟨v, hv⟩ := lfun_surjective c (Multiplicative.toAdd t)
  exact ⟨Multiplicative.ofAdd v, Multiplicative.toAdd.injective hv⟩

theorem theta_mulVec_lfun (c : ZMod 2 ≃+* K) (σ : Equiv.Perm (Fin 6)) (v : Fin 4 → ZMod 2) :
    (((theta c σ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K)
        *ᵥ lfun c v =
      lfun c ((((omegaEquiv.symm σ : sympFour) : GL (Fin 4) (ZMod 2)) :
        Matrix (Fin 4) (Fin 4) (ZMod 2)) *ᵥ v) := by
  funext a
  simp only [mulVec, dotProduct, theta_apply, lfun]
  calc ∑ b, c (_) * c (v (fourIdx.symm b))
      = ∑ b, c ((((omegaEquiv.symm σ : sympFour) : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) (fourIdx.symm a) (fourIdx.symm b) *
          v (fourIdx.symm b)) := by simp only [map_mul]
    _ = ∑ b', c ((((omegaEquiv.symm σ : sympFour) : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) (fourIdx.symm a) b' * v b') :=
        Equiv.sum_comp fourIdx.symm
          (fun b' => c ((((omegaEquiv.symm σ : sympFour) : GL (Fin 4) (ZMod 2)) :
            Matrix (Fin 4) (Fin 4) (ZMod 2)) (fourIdx.symm a) b' * v b'))
    _ = c (∑ b', (((omegaEquiv.symm σ : sympFour) : GL (Fin 4) (ZMod 2)) :
          Matrix (Fin 4) (Fin 4) (ZMod 2)) (fourIdx.symm a) b' * v b') := (map_sum c _ _).symm

@[expose] noncomputable def ehat (c : ZMod 2 ≃+* K) :
    ↥(G6.coreMod 6) →* ↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K))) :=
  ((lhom c).comp (chiHom.comp (G6.coreMod 6).subtype)).codRestrict ⊤ fun _ => trivial

theorem coe_ehat (c : ZMod 2 ≃+* K) (m : ↥(G6.coreMod 6)) :
    ((ehat c m : ↥(⊤ : Subgroup (Multiplicative (Fin 2 ⊕ Fin 2 → K)))) :
      Multiplicative (Fin 2 ⊕ Fin 2 → K)) = lhom c (chiHom m.1) := rfl

theorem ehat_surjective (c : ZMod 2 ≃+* K) : Function.Surjective (ehat c) := by
  rintro ⟨t, -⟩
  obtain ⟨w, rfl⟩ := lhom_surjective c t
  obtain ⟨x, hx, rfl⟩ := exists_core_chiHom_eq w
  exact ⟨⟨x, hx⟩, Subtype.ext rfl⟩

theorem symmetricNatural_six_of_binaryNaturalSp4 {V : Type} [CommGroup V]
    {H : Subgroup (MulAut V)} {U Z : Subgroup V} (h : BinaryNaturalSp4 H U Z 1) :
    SymmetricNatural H U Z 6 := by
  obtain ⟨K, hKf, hKfin, hKc, π, hπ⟩ := h
  have : Fintype K := Fintype.ofFinite K
  have hF : Fintype.card K = 2 := by rw [← Nat.card_eq_fintype_card, hKc, pow_one]
  let c : ZMod 2 ≃+* K := ZMod.ringEquivOfPrime K Nat.prime_two hF
  refine ⟨π.comp (theta c).toMonoidHom, ?_⟩
  refine FFModel.RealizesVia.of_surjHom (FFModel.symDn_isActionModel 6) hπ
    (theta c).toMonoidHom (theta c).surjective (ehat c) (ehat_surjective c) ?_ ?_
  · intro σ m hm
    have hmc : m.1 ∈ G6.coreMod 6 := m.2
    have hσ : omegaPerm (omegaEquiv.symm (σ : Equiv.Perm (Fin 6))) = (σ : Equiv.Perm (Fin 6)) :=
      omegaEquiv.apply_symm_apply σ
    have h1 := chiHom_permAct (omegaEquiv.symm (σ : Equiv.Perm (Fin 6))) hmc
    rw [hσ] at h1
    change lhom c (chiHom (G6.permAct 6 σ m.1)) =
      Multiplicative.ofAdd ((((theta c σ : ↥(StatedSp 2 K)) : GL (Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ
        Multiplicative.toAdd (lhom c (chiHom m.1)))
    rw [h1]
    exact congrArg Multiplicative.ofAdd
      (theta_mulVec_lfun c (σ : Equiv.Perm (Fin 6)) (Multiplicative.toAdd (chiHom m.1))).symm
  · intro m
    change lhom c (chiHom m.1) ∈ (⊥ : Subgroup _) ↔ _
    rw [Subgroup.mem_bot, ← map_one (lhom c), (lhom_injective c).eq_iff]
    exact chiHom_eq_one_iff m.2

end B5FinSp

theorem asSp4S6 : AsSp4S6 := fun _ _ _ _ _ h => B5FinSp.symmetricNatural_six_of_binaryNaturalSp4 h

end CFSG.Quasithin

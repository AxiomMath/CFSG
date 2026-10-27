module

public import CFSG.RankThree.Classical2.NegativeExchangedSL3
public import CFSG.Timmesfeld.RankTwo.LevisExtras
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGeneralLinearNative

public section

namespace CFSG.RankThree.Classical2

open Matrix
open scoped MatrixGroups

noncomputable section

variable (k Ω : Type) [Field k] [Fintype k] [Field Ω] [Algebra k Ω]

noncomputable abbrev mapFrobSqFixedSL2 :
    SL(2, frobSqFixedField k Ω) →* SL(2, Ω) :=
  Matrix.SpecialLinearGroup.map (frobSqFixedField k Ω).subtype

theorem mapFrobSqFixedSL2_apply (A : SL(2, frobSqFixedField k Ω)) :
    mapFrobSqFixedSL2 k Ω A =
      Matrix.SpecialLinearGroup.map (n := Fin 2) (frobSqFixedField k Ω).subtype A :=
  rfl

variable {G : Type*} [Group G]

@[expose] noncomputable def negExchangedPairEta
    (f g : SL(2, Ω) →* G) (hcomm : ∀ A B, Commute (f A) (g B)) :
    SL(2, frobSqFixedField k Ω) →* G :=
  let F : SL(2, frobSqFixedField k Ω) →* G := f.comp (mapFrobSqFixedSL2 k Ω)
  let G' : SL(2, frobSqFixedField k Ω) →* G :=
    g.comp ((negFrobSL k Ω 2).comp (mapFrobSqFixedSL2 k Ω))
  (F.noncommCoprod G' fun A B => hcomm (mapFrobSqFixedSL2 k Ω A)
    (negFrobSL k Ω 2 (mapFrobSqFixedSL2 k Ω B))).comp
      ((MonoidHom.id (SL(2, frobSqFixedField k Ω))).prod
        (MonoidHom.id (SL(2, frobSqFixedField k Ω))))

theorem negExchangedPairEta_apply
    (f g : SL(2, Ω) →* G) (hcomm : ∀ A B, Commute (f A) (g B))
    (A : SL(2, frobSqFixedField k Ω)) :
    negExchangedPairEta k Ω f g hcomm A =
      f (mapFrobSqFixedSL2 k Ω A) *
        g (negFrobSL k Ω 2 (mapFrobSqFixedSL2 k Ω A)) :=
  rfl

variable [CharP k 2]

theorem negExchangedPair_mem_fixed_iff
    (f g : SL(2, Ω) →* G) (hf : Function.Injective f) (hg : Function.Injective g)
    (hcomm : ∀ A B, Commute (f A) (g B))
    (theta : G →* G)
    (htheta_f : ∀ A, theta (f A) = g (negFrobSL k Ω 2 A))
    (htheta_g : ∀ A, theta (g A) = f (negFrobSL k Ω 2 A))
    (z : G) :
    z ∈ (f.range ⊔ g.range) ⊓ theta.eqLocus (MonoidHom.id G) ↔
      ∃ A : SL(2, frobSqFixedField k Ω),
        negExchangedPairEta k Ω f g hcomm A = z := by
  have : CharP Ω 2 :=
    charP_of_injective_algebraMap (algebraMap k Ω).injective 2
  have hΦinj : Function.Injective (f.noncommCoprod g hcomm) :=
    CFSG.Timmesfeld.LevisExtras.injective_noncommCoprod (F := Ω) hf hg hcomm
  constructor
  · rintro hz
    obtain ⟨hzsup, hzfix⟩ := Subgroup.mem_inf.1 hz
    change theta z = z at hzfix
    have hΦrange : z ∈ (f.noncommCoprod g hcomm).range := by
      rw [MonoidHom.noncommCoprod_range f g hcomm]
      exact hzsup
    obtain ⟨⟨A, B⟩, hAB⟩ := hΦrange
    have hzAB : f A * g B = z := by
      simpa only [MonoidHom.noncommCoprod_apply] using hAB
    have hfixθ : theta (f A * g B) = f A * g B := by
      simpa only [← hzAB] using hzfix
    have hpair : (negFrobSL k Ω 2 B, negFrobSL k Ω 2 A) = (A, B) := by
      apply hΦinj
      rw [MonoidHom.noncommCoprod_apply, MonoidHom.noncommCoprod_apply]
      rw [map_mul, htheta_f, htheta_g] at hfixθ
      calc
        f (negFrobSL k Ω 2 B) * g (negFrobSL k Ω 2 A)
            = g (negFrobSL k Ω 2 A) * f (negFrobSL k Ω 2 B) :=
              (hcomm (negFrobSL k Ω 2 B) (negFrobSL k Ω 2 A)).eq
        _ = f A * g B := hfixθ
    have hA : A = negFrobSL k Ω 2 B := (congrArg Prod.fst hpair).symm
    have hB : B = negFrobSL k Ω 2 A := (congrArg Prod.snd hpair).symm
    have hττA : negFrobSL k Ω 2 (negFrobSL k Ω 2 A) = A := by
      rw [← hB, ← hA]
    obtain ⟨A', hA'⟩ :=
      (negFrobSL_negFrobSL_eq_self_iff (k := k) (Ω := Ω) (n := 2) A).mp hττA
    refine ⟨A', ?_⟩
    rw [negExchangedPairEta_apply, mapFrobSqFixedSL2_apply, hA', ← hB]
    exact hzAB
  · rintro ⟨A, rfl⟩
    refine Subgroup.mem_inf.2 ⟨?_, ?_⟩
    · exact Subgroup.mul_mem _
        (Subgroup.mem_sup_left (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
        (Subgroup.mem_sup_right (MonoidHom.mem_range.mpr ⟨_, rfl⟩))
    · change theta (negExchangedPairEta k Ω f g hcomm A) =
        negExchangedPairEta k Ω f g hcomm A
      rw [negExchangedPairEta_apply, map_mul, htheta_f, htheta_g]
      have hττ : negFrobSL k Ω 2 (negFrobSL k Ω 2 (mapFrobSqFixedSL2 k Ω A)) =
          mapFrobSqFixedSL2 k Ω A :=
        (negFrobSL_negFrobSL_eq_self_iff (k := k) (Ω := Ω) (n := 2)
          (mapFrobSqFixedSL2 k Ω A)).mpr ⟨A, rfl⟩
      rw [hττ]
      exact (hcomm (mapFrobSqFixedSL2 k Ω A)
        (negFrobSL k Ω 2 (mapFrobSqFixedSL2 k Ω A))).eq.symm

theorem negExchangedPair_fixed_range
    (f g : SL(2, Ω) →* G) (hf : Function.Injective f) (hg : Function.Injective g)
    (hcomm : ∀ A B, Commute (f A) (g B))
    (theta : G →* G)
    (htheta_f : ∀ A, theta (f A) = g (negFrobSL k Ω 2 A))
    (htheta_g : ∀ A, theta (g A) = f (negFrobSL k Ω 2 A)) :
    (f.range ⊔ g.range) ⊓ theta.eqLocus (MonoidHom.id G) =
      (negExchangedPairEta k Ω f g hcomm).range := by
  ext z
  rw [negExchangedPair_mem_fixed_iff k Ω f g hf hg hcomm theta htheta_f htheta_g z,
    MonoidHom.mem_range]

theorem negExchangedPairEta_injective
    (f g : SL(2, Ω) →* G) (hf : Function.Injective f) (hg : Function.Injective g)
    (hcomm : ∀ A B, Commute (f A) (g B)) :
    Function.Injective (negExchangedPairEta k Ω f g hcomm) := by
  have : CharP Ω 2 :=
    charP_of_injective_algebraMap (algebraMap k Ω).injective 2
  have hΦinj : Function.Injective (f.noncommCoprod g hcomm) :=
    CFSG.Timmesfeld.LevisExtras.injective_noncommCoprod (F := Ω) hf hg hcomm
  intro A B hAB
  have hpair : (mapFrobSqFixedSL2 k Ω A,
      negFrobSL k Ω 2 (mapFrobSqFixedSL2 k Ω A)) =
      (mapFrobSqFixedSL2 k Ω B, negFrobSL k Ω 2 (mapFrobSqFixedSL2 k Ω B)) := by
    apply hΦinj
    simpa only [negExchangedPairEta_apply, MonoidHom.noncommCoprod_apply] using hAB
  have hmap : mapFrobSqFixedSL2 k Ω A = mapFrobSqFixedSL2 k Ω B :=
    congrArg Prod.fst hpair
  change Matrix.SpecialLinearGroup.map (n := Fin 2) (frobSqFixedField k Ω).subtype A =
    Matrix.SpecialLinearGroup.map (n := Fin 2) (frobSqFixedField k Ω).subtype B at hmap
  exact (specialLinearGroup_map_injective (n := 2)
    (frobSqFixedField k Ω).subtype.injective) hmap

noncomputable def negExchangedPairEtaEquiv
    (f g : SL(2, Ω) →* G) (hf : Function.Injective f) (hg : Function.Injective g)
    (hcomm : ∀ A B, Commute (f A) (g B)) :
    SL(2, frobSqFixedField k Ω) ≃* (negExchangedPairEta k Ω f g hcomm).range :=
  MonoidHom.ofInjective (negExchangedPairEta_injective k Ω f g hf hg hcomm)

theorem negExchangedPairEta_range_isQuasisimple
    [IsAlgClosure k Ω]
    (f g : SL(2, Ω) →* G) (hf : Function.Injective f) (hg : Function.Injective g)
    (hcomm : ∀ A B, Commute (f A) (g B)) (hk4 : 4 ≤ Nat.card k) :
    CFSG.IsQuasisimple (negExchangedPairEta k Ω f g hcomm).range := by
  have : Finite (frobSqFixedField k Ω) :=
    NegExchangedLayer.finite_frobSqFixedField (k := k) (Ω := Ω)
  have hk4' : 4 ≤ Fintype.card k := by
    simpa only [Nat.card_eq_fintype_card] using hk4
  have hcard : 4 ≤ Nat.card (frobSqFixedField k Ω) := by
    rw [natCard_frobSqFixedField]
    have h2 : 2 ≤ Fintype.card k := by omega
    calc
      4 = 2 * 2 := by norm_num
      _ ≤ Fintype.card k * Fintype.card k := Nat.mul_le_mul h2 h2
      _ = Fintype.card k ^ 2 := by rw [pow_two]
  have hq : CFSG.IsQuasisimple (SL(2, frobSqFixedField k Ω)) :=
    CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 2
      (frobSqFixedField k Ω) le_rfl (Or.inr (by omega)) (Or.inr (by omega))
  let e := negExchangedPairEtaEquiv k Ω f g hf hg hcomm
  exact (CFSG.IsQuasisimple.congr e).mp hq

end

end CFSG.RankThree.Classical2

end

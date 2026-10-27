module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSp6
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailEqClosure
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneLeviMinus
public import CFSG.RankThree.GF2n.Smith81.OrthTensorModel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement Matrix

@[expose] def OmegaMinus6Line (W : Type) [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  ∀ S : Sylow 2 ↥H,
    letI : MulDistribMulAction ↥S W :=
      MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
    let ℓ : Subgroup W := fixedPointSubgroup ↥S W
    let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
    ∀ Tstar : Subgroup (MulAut W),
      Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
      IsPGroup 2 ↥Tstar →
      (S : Subgroup ↥H).map H.subtype ≤ Tstar →
      let Good : Subgroup ↥H → Prop := fun Pstar =>
        IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
        (∀ t ∈ Tstar,
          (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
        ¬ Pstar ≤ Pℓ
      ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
        Pstar ≠ ⊤ ∧ (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥))

section Transport

variable {W V : Type} [CommGroup W] [CommGroup V] [Finite W] [Finite V]

theorem omegaMinus6Line_of_map_congr (H : Subgroup (MulAut W)) (H' : Subgroup (MulAut V))
    (n : ℕ) (e : W ≃* V) (hH' : H' = H.map (CFSG.Quasithin.H.congrHom e))
    (h : OmegaMinus6Line V H' n) : OmegaMinus6Line W H n := by
  letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
  letI : MulAction ↥H W := MulAction.compHom W H.subtype
  letI : MulAction ↥H (Set W) := Set.mulActionSet
  intro S
  letI : MulDistribMulAction ↥S W :=
    MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
  let ℓ : Subgroup W := fixedPointSubgroup ↥S W
  let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
  dsimp only
  intro Tstar hTnorm hT2 hST
  letI : MulDistribMulAction ↥H' V := MulDistribMulAction.compHom V H'.subtype
  letI : MulAction ↥H' V := MulAction.compHom V H'.subtype
  letI : MulAction ↥H' (Set V) := Set.mulActionSet
  let eH : ↥H ≃* ↥H' :=
    ((MulAut.congr e).subgroupMap H).trans (MulEquiv.subgroupCongr hH'.symm)
  let S' : Sylow 2 ↥H' := S.mapSurjective (f := eH.toMonoidHom) eH.surjective
  letI : MulDistribMulAction ↥S' V :=
    MulDistribMulAction.compHom V (H'.subtype.comp (S' : Subgroup ↥H').subtype)
  let ℓ' : Subgroup V := fixedPointSubgroup ↥S' V
  let Pℓ' : Subgroup ↥H' := MulAction.stabilizer ↥H' (ℓ' : Set V)
  let Tstar' : Subgroup (MulAut V) := Tstar.map (CFSG.Quasithin.H.congrHom e)
  have heHcoe : ∀ g : ↥H, (eH g : MulAut V) = MulAut.congr e (g : MulAut W) := by
    intro g
    change ((MulEquiv.subgroupMap (MulAut.congr e) H g : MulAut V)) =
      MulAut.congr e (g : MulAut W)
    rw [MulEquiv.coe_subgroupMap_apply]
  have hcomp : H'.subtype.comp eH.toMonoidHom =
      (CFSG.Quasithin.H.congrHom e).comp H.subtype :=
    MonoidHom.ext fun g => heHcoe g
  have hmapEH : ∀ P : Subgroup ↥H, (P.map eH.toMonoidHom).map eH.symm.toMonoidHom = P := by
    intro P
    rw [Subgroup.map_map]
    convert Subgroup.map_id P using 2
    ext x
    simp
  have hmapEH' : ∀ P : Subgroup ↥H', (P.map eH.symm.toMonoidHom).map eH.toMonoidHom = P := by
    intro P
    rw [Subgroup.map_map]
    convert Subgroup.map_id P using 2
    ext x
    simp
  have hℓ : ℓ = CFSG.Quasithin.fixV ((S : Subgroup ↥H).map H.subtype) := by
    ext w
    constructor
    · intro hw x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      have h := hw ⟨s, hs⟩
      rw [MulAction.compHom_smul_def] at h
      change (s : MulAut W) w = w at h
      exact h
    · intro hw s
      have h := hw (s : MulAut W) (Subgroup.mem_map_of_mem _ s.2)
      rw [MulAction.compHom_smul_def]
      change (s : MulAut W) w = w
      exact h
  have hℓ' : ℓ' = CFSG.Quasithin.fixV ((S' : Subgroup ↥H').map H'.subtype) := by
    ext v
    constructor
    · intro hv x hx
      obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
      have h := hv ⟨s, hs⟩
      rw [MulAction.compHom_smul_def] at h
      change (s : MulAut V) v = v at h
      exact h
    · intro hv s
      have h := hv (s : MulAut V) (Subgroup.mem_map_of_mem _ s.2)
      rw [MulAction.compHom_smul_def]
      change (s : MulAut V) v = v
      exact h
  have hS'coe : (S' : Subgroup ↥H') = (S : Subgroup ↥H).map eH.toMonoidHom :=
    Sylow.coe_mapSurjective _ _
  have hA : ((S : Subgroup ↥H).map eH.toMonoidHom).map H'.subtype =
      ((S : Subgroup ↥H).map H.subtype).map (CFSG.Quasithin.H.congrHom e) := by
    rw [Subgroup.map_map, Subgroup.map_map, hcomp]
  have hfix : ℓ' = ℓ.map e.toMonoidHom := by
    rw [hℓ', hS'coe, hA, hℓ, CFSG.Quasithin.H.fixV_map_congrHom e]
  have hstab : Pℓ' = Pℓ.map eH.toMonoidHom := by
    have hfixset : Equiv.setCongr e.toEquiv (ℓ : Set W) = (ℓ' : Set V) := by
      rw [hfix]
      rfl
    have h := CFSG.ProperTwoGeneratedCore.LocalCriterionNumerator.stabilizer_map_of_equivariant
      eH (Equiv.setCongr e.toEquiv) ?_ (ℓ : Set W)
    · rw [hfixset] at h
      exact h.symm
    · intro g z
      change Equiv.setCongr e.toEquiv ((g : MulAut W) '' z) =
        (eH g : MulAut V) '' (Equiv.setCongr e.toEquiv z)
      rw [heHcoe g]
      ext y
      simp [Equiv.setCongr, MulAut.congr_apply, Set.image_image]
  have hTnorm' : Tstar' ≤ Subgroup.normalizer (H' : Set (MulAut V)) := by
    rw [hH', ← Subgroup.map_equiv_normalizer_eq H (MulAut.congr e)]
    exact Subgroup.map_mono hTnorm
  have hT2' : IsPGroup 2 ↥Tstar' := hT2.map (CFSG.Quasithin.H.congrHom e)
  have hST' : (S' : Subgroup ↥H').map H'.subtype ≤ Tstar' := by
    rw [hS'coe, Subgroup.map_map, hcomp, ← Subgroup.map_map]
    exact Subgroup.map_mono hST
  let Good : Subgroup ↥H → Prop := fun Pstar =>
    IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
    (∀ t ∈ Tstar,
      (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
    ¬ Pstar ≤ Pℓ
  let Good' : Subgroup ↥H' → Prop := fun Pstar =>
    IsParabolicTwo ↥H' Pstar ∧ (S' : Subgroup ↥H') ≤ Pstar ∧
    (∀ t ∈ Tstar',
      (Pstar.map H'.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H'.subtype) ∧
    ¬ Pstar ≤ Pℓ'
  have hconj : ∀ t : MulAut W,
      (MulAut.conj (CFSG.Quasithin.H.congrHom e t)).toMonoidHom.comp
        (CFSG.Quasithin.H.congrHom e) =
      (CFSG.Quasithin.H.congrHom e).comp (MulAut.conj t).toMonoidHom := by
    intro t
    ext x
    simp [MulAut.conj_apply]
  have hgoodmap : ∀ Pstar : Subgroup ↥H, Good Pstar ↔ Good' (Pstar.map eH.toMonoidHom) := by
    intro Pstar
    have hpar : IsParabolicTwo ↥H Pstar ↔ IsParabolicTwo ↥H' (Pstar.map eH.toMonoidHom) :=
      ⟨fun hp => hp.map eH.toMonoidHom eH.surjective, fun hp => by
        have h1 : IsParabolicTwo ↥H ((Pstar.map eH.toMonoidHom).map eH.symm.toMonoidHom) :=
          hp.map eH.symm.toMonoidHom eH.symm.surjective
        rwa [hmapEH] at h1⟩
    have hSle : (S : Subgroup ↥H) ≤ Pstar ↔
        (S' : Subgroup ↥H') ≤ Pstar.map eH.toMonoidHom := by
      rw [hS'coe, Subgroup.map_le_map_iff_of_injective eH.injective]
    have hPℓle : Pstar ≤ Pℓ ↔ Pstar.map eH.toMonoidHom ≤ Pℓ' := by
      rw [hstab, Subgroup.map_le_map_iff_of_injective eH.injective]
    have hA' : (Pstar.map eH.toMonoidHom).map H'.subtype =
        (Pstar.map H.subtype).map (CFSG.Quasithin.H.congrHom e) := by
      rw [Subgroup.map_map, Subgroup.map_map, hcomp]
    have hTinv : (∀ t ∈ Tstar,
        (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ↔
        (∀ t ∈ Tstar',
          ((Pstar.map eH.toMonoidHom).map H'.subtype).map (MulAut.conj t).toMonoidHom =
            (Pstar.map eH.toMonoidHom).map H'.subtype) := by
      constructor
      · rintro hh t' ht'
        obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp ht'
        rw [hA']
        conv_lhs => rw [Subgroup.map_map, hconj t, ← Subgroup.map_map]
        rw [hh t ht]
      · rintro hh t ht
        have h1 := hh (CFSG.Quasithin.H.congrHom e t) (Subgroup.mem_map_of_mem _ ht)
        rw [hA'] at h1
        conv_lhs at h1 => rw [Subgroup.map_map, hconj t, ← Subgroup.map_map]
        exact (Subgroup.map_injective (CFSG.Quasithin.H.congrHom_injective e)).eq_iff.mp h1
    exact and_congr hpar (and_congr hSle (and_congr hTinv (not_congr hPℓle)))
  intro Pstar hmin
  have hgood : Good Pstar := hmin.1
  have hmin' : Minimal Good' (Pstar.map eH.toMonoidHom) := by
    refine ⟨(hgoodmap Pstar).mp hgood, ?_⟩
    intro Q' hQ' hQle
    have hQ : Good (Q'.map eH.symm.toMonoidHom) :=
      (hgoodmap _).mpr (by rwa [hmapEH'])
    have hQle' : Q'.map eH.symm.toMonoidHom ≤ Pstar := by
      have h2 := Subgroup.map_mono (f := eH.symm.toMonoidHom) hQle
      rwa [hmapEH] at h2
    have hle' : Pstar.map eH.toMonoidHom ≤ Q' := by
      have h2 := Subgroup.map_mono (f := eH.toMonoidHom) (hmin.2 hQ hQle')
      rwa [hmapEH'] at h2
    exact hle'
  obtain ⟨hne', hres'⟩ := h S' Tstar' hTnorm' hT2' hST' (Pstar.map eH.toMonoidHom) hmin'
  refine ⟨?_, ?_⟩
  · intro htop
    apply hne'
    rw [htop, Subgroup.map_top_of_surjective _ eH.surjective]
  · rcases hres' with hL2 | ⟨hn, hbot⟩
    · left
      have hHinf : (Hinf Pstar).map eH.toMonoidHom = Hinf (Pstar.map eH.toMonoidHom) :=
        Hinf_map eH.toMonoidHom Pstar
      let eSub : ↥(Hinf Pstar) ≃* ↥(Hinf (Pstar.map eH.toMonoidHom)) :=
        ((Hinf Pstar).equivMapOfInjective eH.toMonoidHom eH.injective).trans
          (MulEquiv.subgroupCongr hHinf)
      obtain ⟨ebar⟩ := nonempty_bar2_mulEquiv_of_equiv eSub
      exact CFSG.Blueprint.LieModel.of_mulEquiv ebar.symm hL2
    · right
      refine ⟨hn, ?_⟩
      have hHinf : (Hinf Pstar).map eH.toMonoidHom = Hinf (Pstar.map eH.toMonoidHom) :=
        Hinf_map eH.toMonoidHom Pstar
      rw [← hHinf] at hbot
      exact (Subgroup.map_eq_bot_iff_of_injective (H := Hinf Pstar)
        (f := eH.toMonoidHom) eH.injective).mp hbot

end Transport

theorem kTab23b_OmegaMinus6_line_of_natural (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hline : IsOmegaMinus ↥H 6 n ∧ NatOmegaMinus H ⊤ ⊥ 6 n)
    (hNat : ∀ (K : Type) [Field K] [Finite K] (b c : K) (m : ℕ), Nat.card K = 2 ^ m →
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      OmegaMinus6Line (CFSG.Quasithin.H.StdMod (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K)
        (CFSG.Quasithin.H.natImage
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c))) m) :
    letI : MulDistribMulAction ↥H W := MulDistribMulAction.compHom W H.subtype
    letI : MulAction ↥H W := MulAction.compHom W H.subtype
    letI : MulAction ↥H (Set W) := Set.mulActionSet
    ∀ S : Sylow 2 ↥H,
      letI : MulDistribMulAction ↥S W :=
        MulDistribMulAction.compHom W (H.subtype.comp (S : Subgroup ↥H).subtype)
      let ℓ : Subgroup W := fixedPointSubgroup ↥S W
      let Pℓ : Subgroup ↥H := MulAction.stabilizer ↥H (ℓ : Set W)
      ∀ Tstar : Subgroup (MulAut W),
        Tstar ≤ Subgroup.normalizer (H : Set (MulAut W)) →
        IsPGroup 2 ↥Tstar →
        (S : Subgroup ↥H).map H.subtype ≤ Tstar →
        let Good : Subgroup ↥H → Prop := fun Pstar =>
          IsParabolicTwo ↥H Pstar ∧ (S : Subgroup ↥H) ≤ Pstar ∧
          (∀ t ∈ Tstar,
            (Pstar.map H.subtype).map (MulAut.conj t).toMonoidHom = Pstar.map H.subtype) ∧
          ¬ Pstar ≤ Pℓ
        ∀ Pstar : Subgroup ↥H, Minimal Good Pstar →
          Pstar ≠ ⊤ ∧ (IsL2 (Bar2 (Hinf Pstar)) n ∨ (n = 1 ∧ Hinf Pstar = ⊥)) := by
  obtain ⟨-, K, hF, hFin, b, c, hK, hirr, hReal⟩ := hline.2
  letI : Field K := hF
  letI : Finite K := hFin
  obtain ⟨π, e, he⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC.exists_natEquiv
      (ι := Fin 2 ⊕ Fin 2 ⊕ Fin 2)
      (Γ := CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c)) (H := H) hReal
  have he' : ∀ (γ : ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c))) (w : W),
      e (((π γ : ↥H) : MulAut W) w) =
        CFSG.Quasithin.natAct (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c)) γ
          (e w) := by
    intro γ w
    have h1 := he γ w
    change e (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd
      (((γ : Matrix.GeneralLinearGroup (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) :
        Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) *ᵥ
        Multiplicative.toAdd (e w))
    rw [← h1, ofAdd_toAdd]
  have hmodel :
      CFSG.Quasithin.H.natImage
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c)) =
        H.map (CFSG.Quasithin.H.congrHom e) :=
    (CFSG.Quasithin.H.map_congrHom_eq_natImage
      (Γ := CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c))
      (H := H) (π := π) π.surjective e he').symm
  exact omegaMinus6Line_of_map_congr H _ n e hmodel (hNat K b c n hK hirr)

namespace OmegaMinus6Tail

section LinearImage

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] noncomputable def linMulAut : (V ≃ₗ[K] V) →* MulAut (Multiplicative V) where
  toFun e :=
    { toFun := fun x => Multiplicative.ofAdd (e (Multiplicative.toAdd x))
      invFun := fun x => Multiplicative.ofAdd (e.symm (Multiplicative.toAdd x))
      left_inv := by intro x; simp
      right_inv := by intro x; simp
      map_mul' := by intro x y; simp [map_add] }
  map_one' := by
    ext x
    simp
  map_mul' := by
    intro e f
    ext x
    simp [map_add]

@[simp]
theorem linMulAut_apply (e : V ≃ₗ[K] V) (x : Multiplicative V) :
    linMulAut e x = Multiplicative.ofAdd (e (Multiplicative.toAdd x)) := rfl

theorem linMulAut_injective : Function.Injective (linMulAut (K := K) (V := V)) := by
  intro e f h
  ext v
  have := congrArg (fun g : MulAut (Multiplicative V) => g (Multiplicative.ofAdd v)) h
  simpa using this

@[expose] def linFixV (A : Subgroup (V ≃ₗ[K] V)) : Subgroup (Multiplicative V) where
  carrier := {x | ∀ g ∈ A, g (Multiplicative.toAdd x) = Multiplicative.toAdd x}
  one_mem' := by
    intro g _
    simp
  mul_mem' := by
    intro x y hx hy g hg
    rw [toAdd_mul, map_add, hx g hg, hy g hg]
  inv_mem' := by
    intro x hx g hg
    have h := hx g hg
    change g (-(Multiplicative.toAdd x)) = -(Multiplicative.toAdd x)
    rw [map_neg, h]

theorem mem_linFixV {A : Subgroup (V ≃ₗ[K] V)} {x : Multiplicative V} :
    x ∈ linFixV A ↔ ∀ g ∈ A, g (Multiplicative.toAdd x) = Multiplicative.toAdd x :=
  Iff.rfl

theorem fixV_map_linMulAut (A : Subgroup (V ≃ₗ[K] V)) :
    CFSG.Quasithin.fixV (A.map linMulAut) = linFixV A := by
  ext x
  constructor
  · intro hx g hg
    have h := hx (linMulAut g) (Subgroup.mem_map_of_mem linMulAut hg)
    rw [linMulAut_apply] at h
    exact Multiplicative.ofAdd.injective h
  · intro hx g hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
    rw [linMulAut_apply, hx a ha, ofAdd_toAdd]

end LinearImage

section TailTwoMinus

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open QuadraticMap CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open CFSG.RankThree.GF2n.Smith81

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

abbrev T2V (K : Type) [Field K] : Type := (Fin 2 ⊕ Fin 2 → K) × (Fin 2 → K)

noncomputable abbrev T2Q (K : Type) [Field K] (b c : K) : QuadraticForm K (T2V K) :=
  quadTail 2 (minusTailForm K b c)

noncomputable abbrev T2G (K : Type) [Field K] (b c : K) : Subgroup (T2V K ≃ₗ[K] T2V K) :=
  orthElementaryGroup (T2Q K b c)

theorem t2q_anisotropic (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (minusTailForm K b c).Anisotropic :=
  anisotropic_minusTailForm hirr

theorem t2q_regular (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (polarBilin (minusTailForm K b c)).Nondegenerate :=
  nondegenerate_minusTailForm hirr

theorem t2q_finrank : Module.finrank K (Fin 2 → K) = 2 := finrank_fin_two_fun

instance t2G_finite (K : Type) [Field K] [Finite K] (b c : K) : Finite ↥(T2G K b c) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite (T2V K) := by infer_instance
  haveI : Finite (T2V K → T2V K) := by infer_instance
  haveI : Finite (T2V K ≃ₗ[K] T2V K) :=
    Finite.of_injective ((↑) : (T2V K ≃ₗ[K] T2V K) → T2V K → T2V K)
      DFunLike.coe_injective
  exact Subtype.finite

def t2a0 (K : Type) [Field K] : Fin 2 → K := Pi.single 1 1

theorem t2a0_ne_zero (K : Type) [Field K] : t2a0 K ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [t2a0] at this

noncomputable abbrev T2U (K : Type) [Field K] (b c : K) : Subgroup ↥(T2G K b c) :=
  (tailUnipotent 2 (minusTailForm K b c)).subgroupOf (T2G K b c)

noncomputable abbrev T2B (K : Type) [Field K] (b c : K) : Subgroup ↥(T2G K b c) :=
  (tailBorel 2 (minusTailForm K b c)).subgroupOf (T2G K b c)

noncomputable abbrev T2P0 (K : Type) [Field K] (b c : K) : Subgroup ↥(T2G K b c) :=
  (tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2)).subgroupOf (T2G K b c)

noncomputable abbrev T2F1 (K : Type) [Field K] : Submodule K (T2V K) :=
  tailFlag K (Fin 2 → K) 2 1

noncomputable abbrev T2F2 (K : Type) [Field K] : Submodule K (T2V K) :=
  tailFlag K (Fin 2 → K) 2 2

theorem T2F2_mem_singularSubspaces (K : Type) [Field K] (b c : K) :
    T2F2 K ∈ CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.singularSubspaces
      (quadTail 2 (minusTailForm K b c)) 2 := by
  refine ⟨?_, ?_⟩
  · rw [T2F2]
    exact finrank_tailFlag (le_refl 2)
  · intro x hx
    exact quadTail_eq_zero_of_mem_tailFlag hx

theorem card_singularSubspaces_two (K : Type) [Field K] [Finite K] [CharP K 2]
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2) :
    Nat.card (CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit.singularSubspaces
      (quadTail 2 (minusTailForm K b c)) 2) = 45 := by
  have h := card_singularSubspaces_tail (K := K) (A := Fin 2 → K) (r := 2)
    (qA := minusTailForm K b c) (t2q_anisotropic (K := K) (b := b) (c := c) hirr)
    (t2q_regular (K := K) (b := b) (c := c) hirr) (k := 2) (le_refl 2)
  rw [hK] at h
  have hIcc : Finset.Icc 1 2 = ({1, 2} : Finset ℕ) := by decide
  rw [hIcc] at h
  norm_num [t2q_finrank, Finset.prod_insert] at h
  exact_mod_cast h

noncomputable abbrev T2H (K : Type) [Field K] (b c : K) :
    Subgroup (MulAut (Multiplicative (T2V K))) :=
  (T2G K b c).map (linMulAut (K := K) (V := T2V K))

@[expose] noncomputable def t2e (K : Type) [Field K] (b c : K) :
    ↥(T2G K b c) ≃* ↥(T2H K b c) :=
  Subgroup.equivMapOfInjective (T2G K b c) (linMulAut (K := K) (V := T2V K)) linMulAut_injective

@[simp]
theorem t2e_apply (K : Type) [Field K] (b c : K) (g : ↥(T2G K b c)) :
    ((t2e K b c g : ↥(T2H K b c)) : MulAut (Multiplicative (T2V K))) =
      linMulAut (g : T2V K ≃ₗ[K] T2V K) := rfl

theorem t2e_map_subtype_comp (K : Type) [Field K] (b c : K) :
    (T2H K b c).subtype.comp (t2e K b c).toMonoidHom =
      (linMulAut (K := K) (V := T2V K)).comp (T2G K b c).subtype := by
  refine MonoidHom.ext fun g => ?_
  refine MulEquiv.ext fun x => ?_
  rfl

theorem t2_map_e_map_subtype (K : Type) [Field K] (b c : K) (A : Subgroup ↥(T2G K b c)) :
    (A.map (t2e K b c).toMonoidHom).map (T2H K b c).subtype =
      (A.map (T2G K b c).subtype).map (linMulAut (K := K) (V := T2V K)) := by
  rw [Subgroup.map_map, t2e_map_subtype_comp, ← Subgroup.map_map]

@[expose] noncomputable def t2OmegaEquiv (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    StatedOmega (StatedQuadMinus 3 K b c) ≃* T2G K b c :=
  tailOmegaEquiv (minusTailIsometry 3 K b c) (coe_quadMinus (n := 3) (K := K) b c)
    (commutator_orthogonalGroup_quadMinus_of_two_le (n := 3) (by norm_num) hirr)

theorem t2G_card (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(T2G K b c) =
      (Nat.card K) ^ 6 * ((Nat.card K) ^ 3 + 1) * ((Nat.card K) ^ 2 - 1) *
        ((Nat.card K) ^ 4 - 1) := by
  set q := Nat.card K
  have hcard : Nat.card ↥(T2G K b c) =
      Nat.card ↥(StatedOmega (StatedQuadMinus 3 K b c)) :=
    Nat.card_congr (t2OmegaEquiv K b c hirr).toEquiv.symm
  rw [hcard]
  have hInt := card_statedOmega_minus_eq (K := K) (m := 3) (by norm_num) hirr
  have hInt' : ((Nat.card ↥(StatedOmega (StatedQuadMinus 3 K b c)) : ℕ) : ℤ) =
      ((q ^ 6 * (q ^ 3 + 1) * (q ^ 2 - 1) * (q ^ 4 - 1) : ℕ) : ℤ) := by
    rw [hInt]
    have hIcc : Finset.Icc 1 (3 - 1) = ({1, 2} : Finset ℕ) := by decide
    rw [hIcc]
    norm_num [q, Finset.prod_insert]
    push_cast
    ring
  exact_mod_cast hInt'

theorem t2U_card (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nat.card ↥(T2U K b c) = (Nat.card K) ^ 6 := by
  change Nat.card ↥((tailUnipotent 2 (minusTailForm K b c)).subgroupOf (T2G K b c)) =
    (Nat.card K) ^ 6
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
    (tailUnipotent_le (r := 2) (qA := minusTailForm K b c))).toEquiv]
  rw [card_tailUnipotent (hani := t2q_anisotropic hirr) (qA := minusTailForm K b c) (r := 2)]
  norm_num [t2q_finrank]

theorem t2G_card_two (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2) :
    Nat.card ↥(T2G K b c) = 25920 := by
  rw [t2G_card K b c hirr, hK]
  norm_num

theorem index_stabilizer_T2F2 (K : Type) [Field K] [Finite K] [CharP K 2]
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2) :
    (MulAction.stabilizer ↥(T2G K b c) (T2F2 K)).index = 45 := by
  have h := index_stabilizer_eq_card (K := K) (A := Fin 2 → K) (r := 2)
    (qA := minusTailForm K b c) (t2q_anisotropic (K := K) (b := b) (c := c) hirr)
    (hA := ⟨t2a0 K, t2a0_ne_zero K⟩) (k := 2) (le_refl 2)
    (T2F2_mem_singularSubspaces (K := K) (b := b) (c := c))
  simpa [card_singularSubspaces_two (K := K) (b := b) (c := c) hirr hK] using h

theorem card_stabilizer_T2F2 (K : Type) [Field K] [Finite K] [CharP K 2]
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2) :
    Nat.card ↥(MulAction.stabilizer ↥(T2G K b c) (T2F2 K)) = 576 := by
  have h := Subgroup.card_mul_index (H := MulAction.stabilizer ↥(T2G K b c) (T2F2 K))
  rw [index_stabilizer_T2F2 (K := K) (b := b) (c := c) hirr hK,
    t2G_card_two (K := K) (b := b) (c := c) hirr hK] at h
  omega

theorem t2U_index (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (T2U K b c).index =
      ((Nat.card K) ^ 3 + 1) * ((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) := by
  have hmul := Subgroup.card_mul_index (T2U K b c)
  rw [t2U_card K b c hirr, t2G_card K b c hirr] at hmul
  have hmul' : Nat.card K ^ 6 * (T2U K b c).index =
      Nat.card K ^ 6 * ((Nat.card K ^ 3 + 1) * (Nat.card K ^ 2 - 1) *
        (Nat.card K ^ 4 - 1)) := by
    rw [hmul]
    ring
  exact Nat.eq_of_mul_eq_mul_left (pow_pos Nat.card_pos 6) hmul'

theorem t2Odd_not_two_dvd (K : Type) [Field K] [Finite K] (h2 : 2 ∣ Nat.card K) :
    ¬ 2 ∣ ((Nat.card K) ^ 3 + 1) * ((Nat.card K) ^ 2 - 1) * ((Nat.card K) ^ 4 - 1) := by
  have hq_even : Even (Nat.card K) := even_iff_two_dvd.mpr h2
  have h1 : Odd ((Nat.card K) ^ 3 + 1) := (hq_even.pow_of_ne_zero (by norm_num)).add_one
  have hqpos : 0 < Nat.card K := Nat.card_pos
  have hq2ge : 1 ≤ (Nat.card K) ^ 2 := Nat.one_le_pow 2 _ hqpos
  have h2' : Odd ((Nat.card K) ^ 2 - 1) :=
    Nat.Even.sub_odd hq2ge (hq_even.pow_of_ne_zero (by norm_num)) odd_one
  have hq4ge : 1 ≤ (Nat.card K) ^ 4 := Nat.one_le_pow 4 _ hqpos
  have h3 : Odd ((Nat.card K) ^ 4 - 1) :=
    Nat.Even.sub_odd hq4ge (hq_even.pow_of_ne_zero (by norm_num)) odd_one
  simpa [mul_assoc] using ((h1.mul h2').mul h3).not_two_dvd_nat

@[expose] noncomputable def t2Sylow (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : Sylow 2 ↥(T2G K b c) :=
  (isPGroup_tailUnipotent (p := 2) (qA := minusTailForm K b c) (r := 2)
    (t2q_anisotropic hirr)).toSylow (by
      rw [t2U_index K b c hirr]
      exact t2Odd_not_two_dvd K (by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        exact dvd_natCard_of_charP (K := K) (p := 2)))

@[simp]
theorem t2Sylow_coe (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (t2Sylow K b c hirr : Subgroup ↥(T2G K b c)) = T2U K b c := by
  rw [t2Sylow, IsPGroup.toSylow_coe]

noncomputable abbrev T2UH (K : Type) [Field K] (b c : K) : Subgroup ↥(T2H K b c) :=
  (T2U K b c).map (t2e K b c).toMonoidHom

noncomputable def T2SH (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : Sylow 2 ↥(T2H K b c) :=
  (t2Sylow K b c hirr).mapSurjective (f := (t2e K b c).toMonoidHom)
    (by simpa using (t2e K b c).surjective)

theorem T2SH_coe (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (T2SH K b c hirr : Subgroup ↥(T2H K b c)) = T2UH K b c := by
  rw [T2SH, Sylow.coe_mapSurjective, t2Sylow_coe]

theorem T2B_eq_normalizer (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    T2B K b c = Subgroup.normalizer (T2U K b c : Set ↥(T2G K b c)) := by
  change (tailBorel 2 (minusTailForm K b c)).subgroupOf (T2G K b c) =
    Subgroup.normalizer (((tailUnipotent 2 (minusTailForm K b c)).subgroupOf
      (T2G K b c)) : Set ↥(T2G K b c))
  exact (normalizer_tailUnipotent (qA := minusTailForm K b c) (r := 2)
    (t2q_anisotropic hirr) ⟨t2a0 K, t2a0_ne_zero K⟩).symm

theorem T2B_le_T2P0 (K : Type) [Field K] (b c : K) :
    T2B K b c ≤ T2P0 K b c := by
  intro x hx
  exact Subgroup.subset_closure (Or.inl (Subgroup.mem_subgroupOf.mp hx))

theorem T2U_le_T2P0 (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    T2U K b c ≤ T2P0 K b c := by
  intro x hx
  exact T2B_le_T2P0 K b c (Subgroup.mem_subgroupOf.mpr
    (tailUnipotent_le_tailBorel (t2q_anisotropic hirr) (Subgroup.mem_subgroupOf.mp hx)))

theorem T2P0_isParabolic (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsParabolicTwo ↥(T2G K b c) (T2P0 K b c) := by
  refine ⟨t2Sylow K b c hirr, ?_⟩
  change Subgroup.normalizer
    (((t2Sylow K b c hirr : Subgroup ↥(T2G K b c)) : Set ↥(T2G K b c))) ≤ T2P0 K b c
  rw [t2Sylow_coe, ← T2B_eq_normalizer K b c hirr]
  exact T2B_le_T2P0 K b c

theorem T2F1_eq_span (K : Type) [Field K] :
    T2F1 K = K ∙ hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 2)) := by
  rw [T2F1, tailFlag]
  congr 1
  ext v
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj0 : j = 0 := by fin_cases j <;> simp at hj ⊢
    subst hj0
    rfl
  · rintro rfl
    exact ⟨0, by simp, rfl⟩

theorem T2F1_fixed_eq (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    {v : T2V K | ∀ u ∈ tailUnipotent 2 (minusTailForm K b c), u v = v} = (T2F1 K : Set (T2V K)) := by
  rw [T2F1_eq_span]
  exact fixed_tailUnipotent_eq (r := 2) (qA := minusTailForm K b c) (by norm_num)
    (t2q_regular hirr) ⟨t2a0 K, t2a0_ne_zero K⟩

noncomputable abbrev T2F1Sub (K : Type) [Field K] : Subgroup (Multiplicative (T2V K)) where
  carrier := {x | Multiplicative.toAdd x ∈ T2F1 K}
  one_mem' := by
    change (0 : T2V K) ∈ T2F1 K
    exact Submodule.zero_mem _
  mul_mem' := by
    intro x y hx hy
    change Multiplicative.toAdd (x * y) ∈ T2F1 K
    rw [toAdd_mul]
    exact Submodule.add_mem _ hx hy
  inv_mem' := by
    intro x hx
    change Multiplicative.toAdd x⁻¹ ∈ T2F1 K
    rw [toAdd_inv]
    exact Submodule.neg_mem _ hx

theorem linFixV_tailUnipotent_eq (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    linFixV (tailUnipotent 2 (minusTailForm K b c)) = T2F1Sub K := by
  ext x
  rw [mem_linFixV]
  change (∀ u ∈ tailUnipotent 2 (minusTailForm K b c),
      u (Multiplicative.toAdd x) = Multiplicative.toAdd x) ↔
    Multiplicative.toAdd x ∈ T2F1 K
  exact Set.ext_iff.mp (T2F1_fixed_eq K b c hirr) _

theorem mem_T2F1Sub_map_iff (K : Type) [Field K] {x : Multiplicative (T2V K)}
    (g : T2V K ≃ₗ[K] T2V K) :
    x ∈ (T2F1Sub K).map (linMulAut g).toMonoidHom ↔
      Multiplicative.toAdd x ∈ (T2F1 K).map (g : T2V K →ₗ[K] T2V K) := by
  constructor
  · rintro ⟨y, hy, hxy⟩
    refine ⟨Multiplicative.toAdd y, hy, ?_⟩
    have h := congrArg Multiplicative.toAdd hxy
    simpa [linMulAut] using h
  · rintro ⟨y, hy, hxy⟩
    refine ⟨Multiplicative.ofAdd y, hy, ?_⟩
    exact (congrArg Multiplicative.ofAdd hxy).trans (ofAdd_toAdd x)

theorem T2F1Sub_map_eq_iff (K : Type) [Field K] (g : T2V K ≃ₗ[K] T2V K) :
    (T2F1Sub K).map (linMulAut g).toMonoidHom = T2F1Sub K ↔
      (T2F1 K).map (g : T2V K →ₗ[K] T2V K) = T2F1 K := by
  constructor
  · intro h
    ext v
    constructor
    · intro hv
      have hv' : Multiplicative.ofAdd v ∈ (T2F1Sub K).map (linMulAut g).toMonoidHom := by
        rw [mem_T2F1Sub_map_iff]
        simpa using hv
      rw [h] at hv'
      exact hv'
    · intro hv
      have hv' : Multiplicative.ofAdd v ∈ T2F1Sub K := hv
      rw [← h] at hv'
      rw [mem_T2F1Sub_map_iff] at hv'
      simpa using hv'
  · intro h
    refine Subgroup.ext fun x => ?_
    rw [mem_T2F1Sub_map_iff (K := K) (x := x) g, h]
    rfl

theorem T2Pℓ0H_eq_stabilizer (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (MulAction.stabilizer ↥(T2G K b c) (T2F1 K)).map (t2e K b c).toMonoidHom =
      MulAction.stabilizer ↥(T2H K b c) (linFixV (tailUnipotent 2 (minusTailForm K b c))) := by
  classical
  rw [linFixV_tailUnipotent_eq K b c hirr]
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    rw [MulAction.mem_stabilizer_iff]
    change (T2F1Sub K).map
      (((t2e K b c g : ↥(T2H K b c)) : MulAut (Multiplicative (T2V K))).toMonoidHom) = T2F1Sub K
    rw [t2e_apply]
    rw [T2F1Sub_map_eq_iff]
    have h := Submodule.mem_stabilizer_submodule_iff_map_eq.mp hg
    change (T2F1 K).map (g : T2V K →ₗ[K] T2V K) = T2F1 K at h
    exact h
  · intro hx
    obtain ⟨g, hg, hxg⟩ := Subgroup.mem_map.mp
      (x.2 : (x : MulAut (Multiplicative (T2V K))) ∈ T2H K b c)
    refine ⟨⟨g, hg⟩, ?_, Subtype.ext hxg⟩
    refine Submodule.mem_stabilizer_submodule_iff_map_eq.2 ?_
    change (T2F1 K).map (g : T2V K →ₗ[K] T2V K) = T2F1 K
    rw [← T2F1Sub_map_eq_iff]
    have hx' : (x : MulAut (Multiplicative (T2V K))) • (T2F1Sub K) = T2F1Sub K := by
      rwa [MulAction.mem_stabilizer_iff] at hx
    rw [← hxg] at hx'
    rw [Subgroup.pointwise_smul_def] at hx'
    change (T2F1Sub K).map (MulEquiv.toMonoidHom (linMulAut g)) = T2F1Sub K at hx'
    exact hx'

theorem tailBorel_le_stabilizer_T2F1 (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K) :
    tailBorel 2 (minusTailForm K b c) ≤
      MulAction.stabilizer (T2V K ≃ₗ[K] T2V K) (T2F1 K) := by
  intro g hg
  exact Submodule.mem_stabilizer_submodule_iff_map_eq.2
    ((mem_tailBorel.1 hg).2 1 (by norm_num) (by norm_num))

theorem tailRankOneParabolic_le_of_borel_le_of_not_le_point (K : Type) [Field K] [Finite K]
    [CharP K 2] (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {M : Subgroup (T2V K ≃ₗ[K] T2V K)} (hMG : M ≤ T2G K b c)
    (hBM : tailBorel 2 (minusTailForm K b c) ≤ M)
    (hnot : ¬ M ≤ MulAction.stabilizer (T2V K ≃ₗ[K] T2V K) (T2F1 K)) :
    tailRankOneParabolic (minusTailForm K b c) (t2a0 K) 0 ≤ M := by
  classical
  have hani := t2q_anisotropic (K := K) (b := b) (c := c) hirr
  have ha0 := t2a0_ne_zero K
  have hgen := tail_eq_closure_of_borel_le (qA := minusTailForm K b c) (r := 2)
    (a₀ := t2a0 K) hani ha0 hMG hBM
  have hn0 : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0 ∈ M := by
    by_contra h
    apply hnot
    rw [hgen, Subgroup.closure_le]
    rintro _ (hb | ⟨i, hi, rfl⟩)
    · exact tailBorel_le_stabilizer_T2F1 K b c hb
    · have hi0 : i ≠ 0 := by rintro rfl; exact h hi
      exact MulAction.mem_stabilizer_iff.2
        ((tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 2)
          (a₀ := t2a0 K) hani ha0 0 i).2 hi0)
  rw [tailRankOneParabolic, Subgroup.closure_le]
  rintro _ (hb | rfl)
  · exact hBM hb
  · exact hn0

theorem T2P0_le_of_borel_le_of_not_le_point (K : Type) [Field K] [Finite K] [CharP K 2]
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {P : Subgroup ↥(T2G K b c)}
    (hB : T2B K b c ≤ P)
    (hnot : ¬ P ≤ MulAction.stabilizer ↥(T2G K b c) (T2F1 K)) :
    T2P0 K b c ≤ P := by
  have hMG : P.map (T2G K b c).subtype ≤ T2G K b c := Subgroup.map_subtype_le _
  have hBM : tailBorel 2 (minusTailForm K b c) ≤ P.map (T2G K b c).subtype := by
    rintro x hx
    let xG : ↥(T2G K b c) := ⟨x, tailBorel_le (qA := minusTailForm K b c) hx⟩
    have hxG : xG ∈ T2B K b c := Subgroup.mem_subgroupOf.mpr hx
    simpa [xG] using Subgroup.mem_map_of_mem (T2G K b c).subtype (hB hxG)
  have hnot' : ¬ P.map (T2G K b c).subtype ≤
      MulAction.stabilizer (T2V K ≃ₗ[K] T2V K) (T2F1 K) := by
    intro hle
    apply hnot
    intro p hp
    exact hle (Subgroup.mem_map_of_mem (T2G K b c).subtype hp)
  have hP0 : tailRankOneParabolic (minusTailForm K b c) (t2a0 K) 0 ≤
      P.map (T2G K b c).subtype :=
    tailRankOneParabolic_le_of_borel_le_of_not_le_point K b c hirr hMG hBM hnot'
  intro x hx
  obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp (hP0 hx)
  have hpx' : p = x := Subtype.ext hpx
  simpa [hpx'] using hp

theorem T2P0_ne_top (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    T2P0 K b c ≠ ⊤ := by
  intro htop
  have hani := t2q_anisotropic (K := K) (b := b) (c := c) hirr
  have ha0 := t2a0_ne_zero K
  have hn1G : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 1 ∈ T2G K b c :=
    tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t2a0 K) 1
  have hn1 : (⟨tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 1, hn1G⟩ :
      ↥(T2G K b c)) ∈ T2P0 K b c := by
    rw [htop]
    exact Subgroup.mem_top _
  have hP0stab : tailRankOneParabolic (minusTailForm K b c) (t2a0 K) 0 ≤
      MulAction.stabilizer (T2V K ≃ₗ[K] T2V K) (T2F2 K) := by
    rw [tailRankOneParabolic, Subgroup.closure_le]
    rintro _ (hb | rfl)
    · exact Submodule.mem_stabilizer_submodule_iff_map_eq.2
        ((mem_tailBorel.1 hb).2 2 (by norm_num) (by norm_num))
    · exact MulAction.mem_stabilizer_iff.2
        ((tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 2)
          (a₀ := t2a0 K) hani ha0 1 0).2 (by decide))
  have hfix : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 1 •
      T2F2 K = T2F2 K :=
    MulAction.mem_stabilizer_iff.1 (hP0stab (Subgroup.mem_subgroupOf.mp hn1))
  have hmove := (tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 2)
    (a₀ := t2a0 K) hani ha0 1 1).1 hfix
  exact hmove rfl

noncomputable abbrev T2P0H (K : Type) [Field K] (b c : K) : Subgroup ↥(T2H K b c) :=
  (T2P0 K b c).map (t2e K b c).toMonoidHom

private theorem hinf_T2P0H_map_subtype (K : Type) [Field K] [Finite K] [CharP K 2]
    (b c : K) :
    (Hinf (T2P0H K b c)).map (T2H K b c).subtype =
      (Hinf (tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2))).map
        (linMulAut (K := K) (V := T2V K)) := by
  have hP : tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2) ≤ T2G K b c := by
    rw [tailRankOneParabolic, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact tailBorel_le (r := 2) (qA := minusTailForm K b c) hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t2a0 K) (0 : Fin 2)
  have hHinfP : Hinf (tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2)) ≤
      T2G K b c := by
    rw [Hinf_eq_perfectCore]
    exact (CFSG.Quasithin.perfectCore_le _).trans hP
  have hsubOf : Hinf (T2P0 K b c) =
      (Hinf (tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2))).subgroupOf
        (T2G K b c) := by
    rw [T2P0]
    refine Subgroup.map_subtype_inj.mp ?_
    rw [Hinf_map (T2G K b c).subtype
        ((tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2)).subgroupOf
          (T2G K b c)),
      Subgroup.map_subgroupOf_eq_of_le hP,
      Subgroup.map_subgroupOf_eq_of_le hHinfP]
  have h1 : Hinf (T2P0H K b c) =
      (Hinf (T2P0 K b c)).map (t2e K b c).toMonoidHom := by
    rw [T2P0H, ← Hinf_map (t2e K b c).toMonoidHom (T2P0 K b c)]
  rw [h1, Subgroup.map_map, t2e_map_subtype_comp, hsubOf, ← Subgroup.map_map,
    Subgroup.map_subgroupOf_eq_of_le hHinfP]

theorem isL2_bar2_hinf_T2P0H_of_tail {K : Type} [Field K] [Finite K] [CharP K 2]
    (b c : K) {n : ℕ}
    (h : IsL2 (Bar2 (Hinf (tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2)))) n) :
    IsL2 (Bar2 (Hinf (T2P0H K b c))) n := by
  have hsub := hinf_T2P0H_map_subtype K b c
  let eL : ↥(Hinf (tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2))) ≃*
      ↥((Hinf (tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2))).map
        (linMulAut (K := K) (V := T2V K))) :=
    (Hinf (tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2))).equivMapOfInjective
      (linMulAut (K := K) (V := T2V K)) linMulAut_injective
  let eR : ↥(Hinf (T2P0H K b c)) ≃*
      ↥((Hinf (T2P0H K b c)).map (T2H K b c).subtype) :=
    (Hinf (T2P0H K b c)).equivMapOfInjective (T2H K b c).subtype (T2H K b c).subtype_injective
  let e : ↥(Hinf (tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2))) ≃*
      ↥(Hinf (T2P0H K b c)) :=
    eL.trans ((MulEquiv.subgroupCongr hsub).symm.trans eR.symm)
  obtain ⟨ebar⟩ := nonempty_bar2_mulEquiv_of_equiv e
  exact CFSG.Blueprint.LieModel.of_mulEquiv ebar h

theorem hinf_T2P0H_eq_bot_of_tail {K : Type} [Field K] [Finite K] [CharP K 2]
    (b c : K)
    (h : Hinf (tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2)) = ⊥) :
    Hinf (T2P0H K b c) = ⊥ := by
  have hbot : (Hinf (T2P0H K b c)).map (T2H K b c).subtype = ⊥ := by
    rw [hinf_T2P0H_map_subtype K b c, h, Subgroup.map_bot]
  exact (Subgroup.map_eq_bot_iff_of_injective (H := Hinf (T2P0H K b c))
    (f := (T2H K b c).subtype) (T2H K b c).subtype_injective).mp hbot

theorem T2P0H_res_of_surj {K : Type} [Field K] [Finite K] [CharP K 2]
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {n : ℕ} (hn : 2 ≤ n)
    (hK : Nat.card K = 2 ^ n)
    (hsurj : TailRankOneSL2Surjection (qA := minusTailForm K b c) (r := 2)
      (t2q_anisotropic (K := K) (b := b) (c := c) hirr) (a₀ := t2a0 K) (t2a0_ne_zero K)
      (0 : Fin 2)) :
    IsL2 (Bar2 (Hinf (T2P0H K b c))) n :=
  isL2_bar2_hinf_T2P0H_of_tail (K := K) b c
    (isL2_rankOneParabolic_tail_of_sl2Surjection (K := K) (A := Fin 2 → K) (r := 2)
      (qA := minusTailForm K b c)
      (t2q_anisotropic (K := K) (b := b) (c := c) hirr) (a₀ := t2a0 K) (t2a0_ne_zero K)
      (i := 0) (by omega) hn hK hsurj)

noncomputable abbrev T2BH (K : Type) [Field K] (b c : K) : Subgroup ↥(T2H K b c) :=
  (T2B K b c).map (t2e K b c).toMonoidHom

noncomputable abbrev T2Pℓ0H (K : Type) [Field K] (b c : K) : Subgroup ↥(T2H K b c) :=
  (MulAction.stabilizer ↥(T2G K b c) (T2F1 K)).map (t2e K b c).toMonoidHom

theorem T2BH_eq_normalizer (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    T2BH K b c = Subgroup.normalizer (T2UH K b c : Set ↥(T2H K b c)) := by
  rw [T2BH, T2UH, ← Subgroup.map_equiv_normalizer_eq (T2U K b c) (t2e K b c),
    T2B_eq_normalizer K b c hirr]

theorem T2UH_map_subtype (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K) :
    (T2UH K b c).map (T2H K b c).subtype =
      (tailUnipotent 2 (minusTailForm K b c)).map (linMulAut (K := K) (V := T2V K)) := by
  rw [T2UH, t2_map_e_map_subtype, Subgroup.map_subgroupOf_eq_of_le
    (tailUnipotent_le (r := 2) (qA := minusTailForm K b c))]

theorem T2P0H_le_of_borel_le_of_not_le_point (K : Type) [Field K] [Finite K] [CharP K 2]
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {P : Subgroup ↥(T2H K b c)}
    (hB : T2BH K b c ≤ P)
    (hnot : ¬ P ≤ T2Pℓ0H K b c) :
    T2P0H K b c ≤ P := by
  classical
  let Pg : Subgroup ↥(T2G K b c) := P.map (t2e K b c).symm.toMonoidHom
  have hBg : T2B K b c ≤ Pg := by
    intro x hx
    have hxH : t2e K b c x ∈ T2BH K b c := Subgroup.mem_map_of_mem _ hx
    have hxP : t2e K b c x ∈ P := hB hxH
    rw [← (t2e K b c).symm_apply_apply x]
    exact Subgroup.mem_map_of_mem _ hxP
  have hnotg : ¬ Pg ≤ MulAction.stabilizer ↥(T2G K b c) (T2F1 K) := by
    intro hle
    apply hnot
    have hmap := Subgroup.map_mono (f := (t2e K b c).toMonoidHom) hle
    rw [Subgroup.map_map] at hmap
    have hcomp : ((t2e K b c).toMonoidHom.comp (t2e K b c).symm.toMonoidHom) =
        MonoidHom.id ↥(T2H K b c) := by
      refine MonoidHom.ext fun z => ?_
      exact (t2e K b c).apply_symm_apply z
    rw [hcomp, Subgroup.map_id] at hmap
    exact hmap
  have hP0 : T2P0 K b c ≤ Pg :=
    T2P0_le_of_borel_le_of_not_le_point K b c hirr hBg hnotg
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
  have hyPg : y ∈ Pg := hP0 hy
  obtain ⟨p, hp, hyp⟩ := Subgroup.mem_map.mp hyPg
  rw [← hxy, ← hyp]
  simpa using hp

noncomputable abbrev T2PℓH (K : Type) [Field K] (b c : K) (h : ↥(T2H K b c)) :
    Subgroup ↥(T2H K b c) :=
  (T2Pℓ0H K b c).map (MulAut.conj h).toMonoidHom

theorem T2P0H_map_conj_le_of_borel_le_of_not_le_point (K : Type) [Field K] [Finite K]
    [CharP K 2] (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h : ↥(T2H K b c)) {P : Subgroup ↥(T2H K b c)}
    (hB : (T2BH K b c).map (MulAut.conj h).toMonoidHom ≤ P)
    (hnot : ¬ P ≤ T2PℓH K b c h) :
    (T2P0H K b c).map (MulAut.conj h).toMonoidHom ≤ P := by
  classical
  let P' : Subgroup ↥(T2H K b c) := P.map (MulAut.conj h⁻¹).toMonoidHom
  have hcomp : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
      MonoidHom.id ↥(T2H K b c) := by
    refine MonoidHom.ext fun x => ?_
    simp [MulAut.conj_apply, mul_assoc]
  have hcomp' : ((MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom) =
      MonoidHom.id ↥(T2H K b c) := by
    refine MonoidHom.ext fun x => ?_
    simp [MulAut.conj_apply, mul_assoc]
  have hB' : T2BH K b c ≤ P' := by
    intro x hx
    have hfx : (MulAut.conj h).toMonoidHom x ∈ P :=
      hB (Subgroup.mem_map_of_mem (f := (MulAut.conj h).toMonoidHom) hx)
    have hxeq : x = (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom x) := by
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      group
    rw [hxeq]
    exact Subgroup.mem_map_of_mem (f := (MulAut.conj h⁻¹).toMonoidHom) hfx
  have hnot' : ¬ P' ≤ T2Pℓ0H K b c := by
    intro hle
    have h2 : P ≤ T2PℓH K b c h := by
      change P ≤ (T2Pℓ0H K b c).map (MulAut.conj h).toMonoidHom
      have h3 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hle
      rw [Subgroup.map_map, hcomp', Subgroup.map_id] at h3
      exact h3
    exact hnot h2
  have hP0' : T2P0H K b c ≤ P' :=
    T2P0H_le_of_borel_le_of_not_le_point K b c hirr hB' hnot'
  have h2 : (T2P0H K b c).map (MulAut.conj h).toMonoidHom ≤ P := by
    have h3 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hP0'
    have h4 : P'.map (MulAut.conj h).toMonoidHom = P := by
      change (P.map (MulAut.conj h⁻¹).toMonoidHom).map
        (MulAut.conj h).toMonoidHom = P
      rw [Subgroup.map_map, hcomp', Subgroup.map_id]
    rwa [h4] at h3
  exact h2

noncomputable abbrev T2Pℓ0 (K : Type) [Field K] (b c : K) : Subgroup ↥(T2G K b c) :=
  MulAction.stabilizer ↥(T2G K b c) (T2F1 K)

theorem T2P0_not_le_T2Pℓ0 (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ T2P0 K b c ≤ T2Pℓ0 K b c := by
  intro hle
  have hani := t2q_anisotropic (K := K) (b := b) (c := c) hirr
  have ha0 := t2a0_ne_zero K
  have hn0P : (⟨tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0,
      tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t2a0 K) 0⟩ :
        ↥(T2G K b c)) ∈ T2P0 K b c :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (Or.inr rfl))
  have hn0Pℓ := hle hn0P
  rw [T2Pℓ0] at hn0Pℓ
  have hfix := MulAction.mem_stabilizer_iff.1 hn0Pℓ
  have hfix' : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0 •
      T2F1 K = T2F1 K := hfix
  exact ((tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 2)
    (a₀ := t2a0 K) hani ha0 0 0).1 hfix') rfl

theorem T2P0H_not_le_T2Pℓ0H (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ T2P0H K b c ≤ T2Pℓ0H K b c := by
  intro hle
  apply T2P0_not_le_T2Pℓ0 (K := K) (b := b) (c := c) hirr
  have h1 := Subgroup.map_mono (f := (t2e K b c).symm.toMonoidHom) hle
  rw [T2P0H, T2Pℓ0H, Subgroup.map_map, Subgroup.map_map] at h1
  have hcomp : ((t2e K b c).symm.toMonoidHom.comp (t2e K b c).toMonoidHom) =
      MonoidHom.id ↥(T2G K b c) := by
    refine MonoidHom.ext fun z => ?_
    exact (t2e K b c).symm_apply_apply z
  rw [hcomp, Subgroup.map_id] at h1
  simpa [T2Pℓ0] using h1

theorem t2e_symm_comp_toMonoidHom (K : Type) [Field K] (b c : K) :
    ((t2e K b c).symm.toMonoidHom.comp (t2e K b c).toMonoidHom) =
      MonoidHom.id ↥(T2G K b c) := by
  refine MonoidHom.ext fun z => ?_
  exact (t2e K b c).symm_apply_apply z

theorem T2P0H_ne_top (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    T2P0H K b c ≠ ⊤ := by
  intro htop
  apply T2P0_ne_top K b c hirr
  have h2 := congrArg (fun X : Subgroup ↥(T2H K b c) =>
    X.map (t2e K b c).symm.toMonoidHom) htop
  rw [T2P0H, Subgroup.map_map, t2e_symm_comp_toMonoidHom, Subgroup.map_id,
    Subgroup.map_top_of_surjective _ (t2e K b c).symm.surjective] at h2
  exact h2

theorem closure_tailBorel_weyl_top (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Subgroup.closure ((tailBorel 2 (minusTailForm K b c) :
        Set (T2V K ≃ₗ[K] T2V K)) ∪
      {tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0,
        tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 1}) = T2G K b c := by
  classical
  have h := tail_eq_closure_of_borel_le (qA := minusTailForm K b c) (r := 2)
    (a₀ := t2a0 K) (t2q_anisotropic hirr) (t2a0_ne_zero K)
    (le_refl (T2G K b c)) (tailBorel_le (r := 2) (qA := minusTailForm K b c))
  have himage : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) ''
      {i : Fin 2 | tailWeylElt 2 (minusTailForm K b c) (t2a0 K) i ∈ T2G K b c} =
      {tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0,
        tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 1} := by
    ext x
    constructor
    · rintro ⟨i, -, rfl⟩
      fin_cases i <;> simp
    · rintro (rfl | rfl)
      · exact ⟨0, tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t2a0 K) 0, rfl⟩
      · exact ⟨1, tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t2a0 K) 1, rfl⟩
  rw [himage] at h
  exact h.symm

theorem tailP0_eq_of_borel_le_of_ne_top_of_not_le_point (K : Type) [Field K] [Finite K]
    [CharP K 2] (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {M : Subgroup (T2V K ≃ₗ[K] T2V K)} (hMG : M ≤ T2G K b c)
    (hBM : tailBorel 2 (minusTailForm K b c) ≤ M) (hne : M ≠ T2G K b c)
    (hnot : ¬ M ≤ MulAction.stabilizer (T2V K ≃ₗ[K] T2V K) (T2F1 K)) :
    M = tailRankOneParabolic (minusTailForm K b c) (t2a0 K) 0 := by
  classical
  have hP0le : tailRankOneParabolic (minusTailForm K b c) (t2a0 K) 0 ≤ M :=
    tailRankOneParabolic_le_of_borel_le_of_not_le_point K b c hirr hMG hBM hnot
  have hn0M : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0 ∈ M :=
    hP0le (Subgroup.subset_closure (Or.inr rfl))
  have hn1M : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 1 ∉ M := by
    intro hn1
    apply hne
    have htop : Subgroup.closure ((tailBorel 2 (minusTailForm K b c) :
        Set (T2V K ≃ₗ[K] T2V K)) ∪
        {tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0,
          tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 1}) ≤ M := by
      refine (Subgroup.closure_le M).2 ?_
      rintro x (hx | hx)
      · exact hBM hx
      · rcases hx with rfl | rfl
        · exact hn0M
        · exact hn1
    rw [closure_tailBorel_weyl_top K b c hirr] at htop
    exact (hne (le_antisymm hMG htop)).elim
  have hgen := tail_eq_closure_of_borel_le (qA := minusTailForm K b c) (r := 2)
    (a₀ := t2a0 K) (t2q_anisotropic hirr) (t2a0_ne_zero K) hMG hBM
  have hset : {i : Fin 2 | tailWeylElt 2 (minusTailForm K b c) (t2a0 K) i ∈ M} = {0} := by
    ext i
    fin_cases i
    · simp [hn0M]
    · simp [hn1M]
  rw [hgen, hset]
  congr 1
  ext x
  simp

theorem T2P0_eq_of_borel_le_of_ne_top_of_not_le_point (K : Type) [Field K] [Finite K]
    [CharP K 2] (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {M : Subgroup ↥(T2G K b c)} (hBM : T2B K b c ≤ M) (hne : M ≠ ⊤)
    (hnot : ¬ M ≤ T2Pℓ0 K b c) : M = T2P0 K b c := by
  classical
  let Mamb : Subgroup (T2V K ≃ₗ[K] T2V K) := M.map (T2G K b c).subtype
  have hMambG : Mamb ≤ T2G K b c := Subgroup.map_subtype_le _
  have hBMamb : tailBorel 2 (minusTailForm K b c) ≤ Mamb := by
    intro x hx
    let xG : ↥(T2G K b c) := ⟨x, tailBorel_le (qA := minusTailForm K b c) hx⟩
    have hxG : xG ∈ T2B K b c := Subgroup.mem_subgroupOf.mpr hx
    change x ∈ M.map (T2G K b c).subtype
    exact Subgroup.mem_map_of_mem (T2G K b c).subtype (hBM hxG)
  have hneAmb : Mamb ≠ T2G K b c := by
    intro htop
    apply hne
    have h1 : Mamb.subgroupOf (T2G K b c) = M := by
      ext x
      constructor
      · intro hx
        exact (Subgroup.mem_map_iff_mem (T2G K b c).subtype_injective).mp hx
      · intro hx
        exact Subgroup.mem_map_of_mem _ hx
    rw [← h1, htop, Subgroup.subgroupOf_self]
  have hnotAmb : ¬ Mamb ≤ MulAction.stabilizer (T2V K ≃ₗ[K] T2V K) (T2F1 K) := by
    intro hle
    apply hnot
    intro x hx
    exact hle (Subgroup.mem_map_of_mem _ hx)
  have hkey := tailP0_eq_of_borel_le_of_ne_top_of_not_le_point K b c hirr
    hMambG hBMamb hneAmb hnotAmb
  have hM : Mamb.subgroupOf (T2G K b c) = M := by
    ext x
    constructor
    · intro hx
      exact (Subgroup.mem_map_iff_mem (T2G K b c).subtype_injective).mp hx
    · intro hx
      exact Subgroup.mem_map_of_mem _ hx
  have h1 : Mamb.subgroupOf (T2G K b c) =
      (tailRankOneParabolic (minusTailForm K b c) (t2a0 K) 0).subgroupOf (T2G K b c) :=
    congrArg (fun X => X.subgroupOf (T2G K b c)) hkey
  rw [hM] at h1
  simpa [T2P0] using h1

theorem T2P0H_eq_of_borel_le_of_ne_top_of_not_le_point (K : Type) [Field K] [Finite K]
    [CharP K 2] (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {M : Subgroup ↥(T2H K b c)} (hBM : T2BH K b c ≤ M) (hne : M ≠ ⊤)
    (hnot : ¬ M ≤ T2Pℓ0H K b c) : M = T2P0H K b c := by
  classical
  let Mg : Subgroup ↥(T2G K b c) := M.map (t2e K b c).symm.toMonoidHom
  have hBg : T2B K b c ≤ Mg := by
    intro x hx
    have hxH : t2e K b c x ∈ T2BH K b c := Subgroup.mem_map_of_mem _ hx
    have hxM : t2e K b c x ∈ M := hBM hxH
    rw [← (t2e K b c).symm_apply_apply x]
    exact Subgroup.mem_map_of_mem _ hxM
  have hneg : Mg ≠ ⊤ := by
    intro htop
    apply hne
    have h1 := congrArg (fun X : Subgroup ↥(T2G K b c) =>
      X.map (t2e K b c).toMonoidHom) htop
    rw [Subgroup.map_top_of_surjective _ (t2e K b c).surjective] at h1
    have h2 : (M.map (t2e K b c).symm.toMonoidHom).map (t2e K b c).toMonoidHom = M := by
      rw [Subgroup.map_map]
      have hcomp : ((t2e K b c).toMonoidHom.comp (t2e K b c).symm.toMonoidHom) =
          MonoidHom.id ↥(T2H K b c) := by
        refine MonoidHom.ext fun z => ?_
        exact (t2e K b c).apply_symm_apply z
      rw [hcomp, Subgroup.map_id]
    rwa [h2] at h1
  have hnotg : ¬ Mg ≤ T2Pℓ0 K b c := by
    intro hle
    apply hnot
    have h1 := Subgroup.map_mono (f := (t2e K b c).toMonoidHom) hle
    rw [Subgroup.map_map] at h1
    have hcomp : ((t2e K b c).toMonoidHom.comp (t2e K b c).symm.toMonoidHom) =
        MonoidHom.id ↥(T2H K b c) := by
      refine MonoidHom.ext fun z => ?_
      exact (t2e K b c).apply_symm_apply z
    rw [hcomp, Subgroup.map_id] at h1
    exact h1
  have hkey := T2P0_eq_of_borel_le_of_ne_top_of_not_le_point K b c hirr hBg hneg hnotg
  have h1 : Mg.map (t2e K b c).toMonoidHom = M := by
    rw [Subgroup.map_map]
    have hcomp : ((t2e K b c).toMonoidHom.comp (t2e K b c).symm.toMonoidHom) =
        MonoidHom.id ↥(T2H K b c) := by
      refine MonoidHom.ext fun z => ?_
      exact (t2e K b c).apply_symm_apply z
    rw [hcomp, Subgroup.map_id]
  rw [← h1, hkey, T2P0H]

theorem T2BH_le_T2P0H (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K) :
    T2BH K b c ≤ T2P0H K b c := by
  rw [T2BH, T2P0H]
  exact Subgroup.map_mono (f := (t2e K b c).toMonoidHom) (T2B_le_T2P0 K b c)

theorem T2P0H_map_conj_eq_of_borel_le_of_ne_top_of_not_le_point (K : Type) [Field K]
    [Finite K] [CharP K 2] (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (h : ↥(T2H K b c)) {M : Subgroup ↥(T2H K b c)}
    (hB : (T2BH K b c).map (MulAut.conj h).toMonoidHom ≤ M) (hne : M ≠ ⊤)
    (hnot : ¬ M ≤ T2PℓH K b c h) :
    M = (T2P0H K b c).map (MulAut.conj h).toMonoidHom := by
  classical
  let M' : Subgroup ↥(T2H K b c) := M.map (MulAut.conj h⁻¹).toMonoidHom
  have hcomp : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
      MonoidHom.id ↥(T2H K b c) := by
    refine MonoidHom.ext fun z => ?_
    simp [MulAut.conj_apply, mul_assoc]
  have hcomp' : ((MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom) =
      MonoidHom.id ↥(T2H K b c) := by
    refine MonoidHom.ext fun z => ?_
    simp [MulAut.conj_apply, mul_assoc]
  have hB' : T2BH K b c ≤ M' := by
    intro x hx
    have hfx : (MulAut.conj h).toMonoidHom x ∈ M :=
      hB (Subgroup.mem_map_of_mem (f := (MulAut.conj h).toMonoidHom) hx)
    have hxeq : x = (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom x) := by
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      group
    rw [hxeq]
    exact Subgroup.mem_map_of_mem (f := (MulAut.conj h⁻¹).toMonoidHom) hfx
  have hne' : M' ≠ ⊤ := by
    intro htop
    apply hne
    have h2 : M = M'.map (MulAut.conj h).toMonoidHom := by
      dsimp only [M']
      rw [Subgroup.map_map, hcomp', Subgroup.map_id]
    rw [h2, htop, Subgroup.map_top_of_surjective _ (MulAut.conj h).surjective]
  have hnot' : ¬ M' ≤ T2Pℓ0H K b c := by
    intro hle
    apply hnot
    dsimp only [T2PℓH]
    have h1 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hle
    rw [Subgroup.map_map, hcomp', Subgroup.map_id] at h1
    exact h1
  have hkey := T2P0H_eq_of_borel_le_of_ne_top_of_not_le_point K b c hirr hB' hne' hnot'
  have hM' : M'.map (MulAut.conj h).toMonoidHom = M := by
    dsimp only [M']
    rw [Subgroup.map_map, hcomp', Subgroup.map_id]
  rw [← hM', hkey]

theorem T2P0_card (K : Type) [Field K] [Finite K] [CharP K 2]
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2) :
    Nat.card ↥(T2P0 K b c) = 576 := by
  classical
  have hani := t2q_anisotropic (K := K) (b := b) (c := c) hirr
  have ha0 := t2a0_ne_zero K
  let M : Subgroup (T2V K ≃ₗ[K] T2V K) :=
    (MulAction.stabilizer ↥(T2G K b c) (T2F2 K)).map (T2G K b c).subtype
  have hMcard : Nat.card ↥M = 576 := by
    dsimp [M]
    rw [Subgroup.card_map_of_injective (T2G K b c).subtype_injective]
    exact card_stabilizer_T2F2 (K := K) (b := b) (c := c) hirr hK
  have hMG : M ≤ T2G K b c := by
    dsimp [M]
    exact Subgroup.map_subtype_le _
  have hBM : tailBorel 2 (minusTailForm K b c) ≤ M := by
    intro x hx
    have hxG : x ∈ T2G K b c := tailBorel_le (r := 2) (qA := minusTailForm K b c) hx
    have hxstab : (⟨x, hxG⟩ : ↥(T2G K b c)) ∈
        MulAction.stabilizer ↥(T2G K b c) (T2F2 K) := by
      rw [MulAction.mem_stabilizer_iff]
      exact (mem_tailBorel.1 hx).2 2 (by norm_num) (by norm_num)
    exact Subgroup.mem_map_of_mem (f := (T2G K b c).subtype) hxstab
  have hne : M ≠ T2G K b c := by
    intro h
    rw [h] at hMcard
    have := t2G_card_two (K := K) (b := b) (c := c) hirr hK
    omega
  have hnot : ¬ M ≤ MulAction.stabilizer (T2V K ≃ₗ[K] T2V K) (T2F1 K) := by
    intro hle
    have hn0G : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0 ∈ T2G K b c :=
      tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t2a0 K) 0
    have hn0stab : (⟨tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0, hn0G⟩ :
        ↥(T2G K b c)) ∈ MulAction.stabilizer ↥(T2G K b c) (T2F2 K) := by
      rw [MulAction.mem_stabilizer_iff]
      exact (tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 2)
        (a₀ := t2a0 K) hani ha0 1 0).2 (by decide)
    have hn0M : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0 ∈ M :=
      Subgroup.mem_map_of_mem (f := (T2G K b c).subtype) hn0stab
    have hfix1 : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0 ∈
        MulAction.stabilizer (T2V K ≃ₗ[K] T2V K) (T2F1 K) := hle hn0M
    have hfix1' : tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0 • T2F1 K = T2F1 K := by
      simpa using hfix1
    have hmove : ¬ tailWeylElt 2 (minusTailForm K b c) (t2a0 K) 0 • T2F1 K = T2F1 K := by
      intro h
      exact (tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 2)
        (a₀ := t2a0 K) hani ha0 0 0).1 h rfl
    exact hmove hfix1'
  have hM : M = tailRankOneParabolic (minusTailForm K b c) (t2a0 K) 0 :=
    tailP0_eq_of_borel_le_of_ne_top_of_not_le_point K b c hirr hMG hBM hne hnot
  have hPle : tailRankOneParabolic (minusTailForm K b c) (t2a0 K) 0 ≤ T2G K b c := by
    rw [tailRankOneParabolic, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact tailBorel_le (r := 2) (qA := minusTailForm K b c) hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t2a0 K) 0
  rw [T2P0]
  rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv]
  rw [← hM]
  exact hMcard

theorem isSolvable_tailRankOneParabolic_F2 (K : Type) [Field K] [Finite K] [CharP K 2]
    (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (hK : Nat.card K = 2) :
    Group.IsSolvable ↥(tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2)) := by
  have hPle : tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2) ≤ T2G K b c := by
    rw [tailRankOneParabolic, Subgroup.closure_le]
    rintro x (hx | hx)
    · exact tailBorel_le (r := 2) (qA := minusTailForm K b c) hx
    · rw [Set.mem_singleton_iff] at hx
      rw [hx]
      exact tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t2a0 K) 0
  have hcard576 : Nat.card ↥(tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2)) = 576 := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hPle).toEquiv]
    exact T2P0_card (K := K) (b := b) (c := c) hirr hK
  letI : Fintype ↥(tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2)) := Fintype.ofFinite _
  have hcard : Fintype.card ↥(tailRankOneParabolic (minusTailForm K b c) (t2a0 K) (0 : Fin 2)) =
      2 ^ 6 * 3 ^ 2 := by
    rw [← Nat.card_eq_fintype_card, hcard576]
    norm_num
  exact Burnside.finite_group_isSolvable_of_card_eq_prime_pow_mul_prime_pow
    Nat.prime_two Nat.prime_three (by norm_num) hcard

theorem T2H_line (K : Type) [Field K] [Finite K] [CharP K 2] (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (n : ℕ)
    (hres : IsL2 (Bar2 (Hinf (T2P0H K b c))) n ∨
      (n = 1 ∧ Hinf (T2P0H K b c) = ⊥)) :
    OmegaMinus6Line (Multiplicative (T2V K)) (T2H K b c) n := by
  classical
  letI : MulDistribMulAction ↥(T2H K b c) (Multiplicative (T2V K)) :=
    MulDistribMulAction.compHom _ (T2H K b c).subtype
  letI : MulAction ↥(T2H K b c) (Multiplicative (T2V K)) := MulDistribMulAction.toMulAction
  letI : MulAction ↥(T2H K b c) (Set (Multiplicative (T2V K))) := Set.mulActionSet
  intro S
  letI : MulDistribMulAction ↥S (Multiplicative (T2V K)) :=
    MulDistribMulAction.compHom _ ((T2H K b c).subtype.comp (S : Subgroup ↥(T2H K b c)).subtype)
  let ℓ : Subgroup (Multiplicative (T2V K)) := fixedPointSubgroup ↥S _
  let Pℓ : Subgroup ↥(T2H K b c) :=
    MulAction.stabilizer ↥(T2H K b c) (ℓ : Set (Multiplicative (T2V K)))
  dsimp only
  intro Tstar hTnorm hT2 hST
  intro Pstar hmin
  have hSylS : CFSG.QuasithinUnique.IsSylowTwoOf (S : Subgroup ↥(T2H K b c)) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow S
  have hSylStd : CFSG.QuasithinUnique.IsSylowTwoOf
      (T2SH K b c hirr : Subgroup ↥(T2H K b c)) ⊤ :=
    CFSG.QuasithinUnique.isSylowTwoOf_top_of_sylow _
  obtain ⟨h, -, hconj⟩ :=
    CFSG.QuasithinUnique.IsSylowTwoOf.exists_conj hSylStd hSylS
  let SH : Subgroup (MulAut (Multiplicative (T2V K))) :=
    (S : Subgroup ↥(T2H K b c)).map (T2H K b c).subtype
  have hcomp : (T2H K b c).subtype.comp (MulAut.conj h).toMonoidHom =
      (MulAut.conj ((h : ↥(T2H K b c)) : MulAut (Multiplicative (T2V K)))).toMonoidHom.comp
        (T2H K b c).subtype := rfl
  have hSH : SH = ((T2UH K b c).map (T2H K b c).subtype).map
      (MulAut.conj ((h : ↥(T2H K b c)) : MulAut (Multiplicative (T2V K)))).toMonoidHom := by
    dsimp [SH]
    rw [hconj, T2SH_coe, Subgroup.map_map, hcomp, ← Subgroup.map_map]
    rfl
  have hfixV : ℓ = CFSG.Quasithin.fixV SH := by
    dsimp [ℓ, SH]
    rw [fixedPointSubgroup_sylow_map S, fixedPointSubgroup_eq_fixV]
  have hℓ : ℓ = (linFixV (tailUnipotent 2 (minusTailForm K b c))).map
      ((h : ↥(T2H K b c)) : MulAut (Multiplicative (T2V K))).toMonoidHom := by
    rw [hfixV, hSH, fixV_map_conj, T2UH_map_subtype, fixV_map_linMulAut]
  have hPℓ : Pℓ = (T2Pℓ0H K b c).map (MulAut.conj h).toMonoidHom := by
    have hstab := stabilizer_map_conj_subgroup (T2H K b c) h
      (linFixV (tailUnipotent 2 (minusTailForm K b c)))
    have hbridge : MulAction.stabilizer ↥(T2H K b c)
        (linFixV (tailUnipotent 2 (minusTailForm K b c)) :
          Subgroup (Multiplicative (T2V K))) =
      MulAction.stabilizer ↥(T2H K b c)
        (↑(linFixV (tailUnipotent 2 (minusTailForm K b c))) :
          Set (Multiplicative (T2V K))) := by
      ext g
      rw [MulAction.mem_stabilizer_iff, MulAction.mem_stabilizer_iff]
      constructor
      · intro hg
        rwa [← Subgroup.coe_pointwise_smul, SetLike.coe_set_eq]
      · intro hg
        rwa [← Subgroup.coe_pointwise_smul, SetLike.coe_set_eq] at hg
    have hstabL : MulAction.stabilizer ↥(T2H K b c)
        (↑(linFixV (tailUnipotent 2 (minusTailForm K b c))) :
          Set (Multiplicative (T2V K))) = T2Pℓ0H K b c := by
      rw [← hbridge]
      exact (T2Pℓ0H_eq_stabilizer K b c hirr).symm
    dsimp [Pℓ]
    rw [hℓ, hstab, hstabL]
    rfl
  have hB : Subgroup.normalizer (((S : Subgroup ↥(T2H K b c))) :
        Set ↥(T2H K b c)) =
      (T2BH K b c).map (MulAut.conj h).toMonoidHom := by
    have hSset : (((S : Subgroup ↥(T2H K b c))) : Set ↥(T2H K b c)) =
        ((T2UH K b c).map (MulAut.conj h).toMonoidHom : Set ↥(T2H K b c)) := by
      have h1 : (S : Subgroup ↥(T2H K b c)) =
          (T2UH K b c).map (MulAut.conj h).toMonoidHom := by
        rw [hconj, T2SH_coe]
      exact congrArg (fun X : Subgroup ↥(T2H K b c) => (X : Set ↥(T2H K b c))) h1
    rw [hSset, ← Subgroup.map_equiv_normalizer_eq (T2UH K b c) (MulAut.conj h),
      T2BH_eq_normalizer K b c hirr]
  have hBP : Subgroup.normalizer (((S : Subgroup ↥(T2H K b c))) :
        Set ↥(T2H K b c)) ≤ Pstar :=
    hmin.1.1.normalizer_le S hmin.1.2.1
  have hBle : (T2BH K b c).map (MulAut.conj h).toMonoidHom ≤ Pstar := by
    rwa [← hB]
  have hnotPℓ : ¬ Pstar ≤ (T2Pℓ0H K b c).map (MulAut.conj h).toMonoidHom := by
    rw [← hPℓ]
    exact hmin.1.2.2.2
  have hQle : (T2P0H K b c).map (MulAut.conj h).toMonoidHom ≤ Pstar :=
    T2P0H_map_conj_le_of_borel_le_of_not_le_point K b c hirr h hBle hnotPℓ
  have hTstarH : Tstar ⊓ (T2H K b c) = SH := by
    have hX2 : IsPGroup 2 ↥(Tstar ⊓ (T2H K b c)) := by
      intro x
      obtain ⟨k, hk⟩ := hT2 ⟨(x : MulAut (Multiplicative (T2V K))), x.2.1⟩
      exact ⟨k, Subtype.ext (by simpa using congrArg Subtype.val hk)⟩
    have hX2sub : IsPGroup 2 ((Tstar ⊓ (T2H K b c)).subgroupOf (T2H K b c)) :=
      hX2.of_equiv (Subgroup.subgroupOfEquivOfLe inf_le_right).symm
    have hSX : (S : Subgroup ↥(T2H K b c)) ≤
        (Tstar ⊓ (T2H K b c)).subgroupOf (T2H K b c) := by
      intro x hx
      exact ⟨hST (Subgroup.mem_map_of_mem (T2H K b c).subtype hx), x.2⟩
    have hEq : (Tstar ⊓ (T2H K b c)).subgroupOf (T2H K b c) =
        (S : Subgroup ↥(T2H K b c)) := S.is_maximal' hX2sub hSX
    have h1 := congrArg (fun X : Subgroup ↥(T2H K b c) => X.map (T2H K b c).subtype) hEq
    rw [Subgroup.map_subgroupOf_eq_of_le inf_le_right] at h1
    simpa [SH] using h1
  have hSH_normal : ∀ t ∈ Tstar,
      SH.map (MulAut.conj t).toMonoidHom = SH := by
    intro t ht
    have hle : SH.map (MulAut.conj t).toMonoidHom ≤ SH := by
      rintro x ⟨s, hs, rfl⟩
      obtain ⟨s0, hs0, rfl⟩ := Subgroup.mem_map.mp hs
      have htH : t * (s0 : MulAut (Multiplicative (T2V K))) * t⁻¹ ∈ T2H K b c :=
        ((Subgroup.mem_normalizer_iff.mp (hTnorm ht)) _).mp s0.2
      have hmem : t * (s0 : MulAut (Multiplicative (T2V K))) * t⁻¹ ∈
          Tstar ⊓ (T2H K b c) :=
        ⟨Tstar.mul_mem (Tstar.mul_mem ht
          (hST (Subgroup.mem_map_of_mem (T2H K b c).subtype hs0))) (Tstar.inv_mem ht), htH⟩
      rwa [hTstarH] at hmem
    exact Subgroup.eq_of_le_of_card_ge hle (by
      rw [Subgroup.card_map_of_injective (f := (MulAut.conj t).toMonoidHom)
        (MulAut.conj t).injective])
  have hℓ_t : ∀ t ∈ Tstar, ℓ.map t.toMonoidHom = ℓ := by
    intro t ht
    rw [hfixV, ← fixV_map_conj SH t, hSH_normal t ht]
  have hPℓ_t : ∀ t ∈ Tstar,
      (Pℓ.map (T2H K b c).subtype).map (MulAut.conj t).toMonoidHom =
        Pℓ.map (T2H K b c).subtype := by
    intro t ht
    have h := map_subtype_stabilizer_conj_normalizer t (hTnorm ht) ℓ
    rw [h, hℓ_t t ht]
  have hB_t : ∀ t ∈ Tstar,
      ((Subgroup.normalizer (((S : Subgroup ↥(T2H K b c))) : Set ↥(T2H K b c))).map
        (T2H K b c).subtype).map (MulAut.conj t).toMonoidHom =
      (Subgroup.normalizer (((S : Subgroup ↥(T2H K b c))) : Set ↥(T2H K b c))).map
        (T2H K b c).subtype := by
    intro t ht
    have hNB : (Subgroup.normalizer (((S : Subgroup ↥(T2H K b c))) :
        Set ↥(T2H K b c))).map (T2H K b c).subtype =
        Subgroup.normalizer (((S : Subgroup ↥(T2H K b c))).map (T2H K b c).subtype) ⊓
          (T2H K b c) :=
      map_subtype_normalizer_eq_inf (T2H K b c) (S : Subgroup ↥(T2H K b c))
    have hHt : (T2H K b c).map (MulAut.conj t).toMonoidHom = T2H K b c :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hTnorm ht)
    rw [hNB, Subgroup.map_inf_eq _ _ _ (MulAut.conj t).injective,
      Subgroup.map_equiv_normalizer_eq SH (MulAut.conj t), hSH_normal t ht, hHt]
  let Q : Subgroup ↥(T2H K b c) := (T2P0H K b c).map (MulAut.conj h).toMonoidHom
  have hQnotPℓ : ¬ Q ≤ Pℓ := by
    rw [hPℓ]
    intro hle
    exact T2P0H_not_le_T2Pℓ0H K b c hirr
      ((Subgroup.map_le_map_iff_of_injective (f := (MulAut.conj h).toMonoidHom)
        (MulAut.conj h).injective).mp hle)
  have hQ_t : ∀ t ∈ Tstar,
      (Q.map (T2H K b c).subtype).map (MulAut.conj t).toMonoidHom =
        Q.map (T2H K b c).subtype := by
    intro t ht
    let Mamb : Subgroup (MulAut (Multiplicative (T2V K))) :=
      (Q.map (T2H K b c).subtype).map (MulAut.conj t).toMonoidHom
    have hMambH : Mamb ≤ T2H K b c := by
      rintro _ ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.mp (hTnorm ht) y).mp (Subgroup.map_subtype_le Q hy)
    let M : Subgroup ↥(T2H K b c) := Mamb.subgroupOf (T2H K b c)
    have hMmap : M.map (T2H K b c).subtype = Mamb :=
      Subgroup.map_subgroupOf_eq_of_le hMambH
    have hBM : (T2BH K b c).map (MulAut.conj h).toMonoidHom ≤ M := by
      have hB_le_Q : (T2BH K b c).map (MulAut.conj h).toMonoidHom ≤ Q := by
        dsimp [Q]
        exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) (T2BH_le_T2P0H K b c)
      have h1 : ((T2BH K b c).map (MulAut.conj h).toMonoidHom).map
          (T2H K b c).subtype ≤ Mamb := by
        have h2 := Subgroup.map_mono (f := (MulAut.conj t).toMonoidHom)
          (Subgroup.map_mono (f := (T2H K b c).subtype) hB_le_Q)
        rw [← hB, hB_t t ht, hB] at h2
        exact h2
      intro x hx
      exact h1 (Subgroup.mem_map_of_mem _ hx)
    have htopH : (⊤ : Subgroup ↥(T2H K b c)).map (T2H K b c).subtype = T2H K b c := by
      rw [← MonoidHom.range_eq_map, Subgroup.range_subtype]
    have hMne : M ≠ ⊤ := by
      intro htop
      have htop' : Mamb = T2H K b c := by
        rw [← hMmap, htop, htopH]
      have hQamb : Q.map (T2H K b c).subtype = T2H K b c := by
        have h1 := congrArg (fun X : Subgroup (MulAut (Multiplicative (T2V K))) =>
          X.map (MulAut.conj t⁻¹).toMonoidHom) htop'
        dsimp only [Mamb] at h1
        rw [Subgroup.map_map, show ((MulAut.conj t⁻¹).toMonoidHom.comp
          (MulAut.conj t).toMonoidHom) = MonoidHom.id _ from by
            refine MonoidHom.ext fun z => ?_
            simp [MulAut.conj_apply, mul_assoc], Subgroup.map_id] at h1
        have htH : (T2H K b c).map (MulAut.conj t⁻¹) = T2H K b c :=
          (Subgroup.mem_normalizer_iff_map_conj_eq (H := T2H K b c) (g := t⁻¹)).mp
            (hTnorm (Tstar.inv_mem ht))
        rw [MulEquiv.toMonoidHom_eq_coe] at h1
        exact h1.trans htH
      have hQtop : Q = ⊤ := by
        apply Subgroup.map_injective (f := (T2H K b c).subtype) (T2H K b c).subtype_injective
        rw [hQamb, htopH]
      apply T2P0H_ne_top K b c hirr
      rw [show Q = (T2P0H K b c).map (MulAut.conj h).toMonoidHom from rfl] at hQtop
      have h2 := congrArg (fun X : Subgroup ↥(T2H K b c) =>
        X.map (MulAut.conj h⁻¹).toMonoidHom) hQtop
      rw [Subgroup.map_top_of_surjective _ (MulAut.conj h⁻¹).surjective] at h2
      rwa [show ((T2P0H K b c).map (MulAut.conj h).toMonoidHom).map
        (MulAut.conj h⁻¹).toMonoidHom = T2P0H K b c from by
          rw [Subgroup.map_map]
          have hc : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
              MonoidHom.id ↥(T2H K b c) := by
            refine MonoidHom.ext fun z => ?_
            simp [MulAut.conj_apply, mul_assoc]
          rw [hc, Subgroup.map_id]] at h2
    have hMnot : ¬ M ≤ T2PℓH K b c h := by
      intro hle
      apply hQnotPℓ
      have hle' : M ≤ Pℓ := by
        rw [hPℓ]
        exact hle
      have h1 : Mamb ≤ Pℓ.map (T2H K b c).subtype := by
        rw [← hMmap]
        exact Subgroup.map_mono (f := (T2H K b c).subtype) hle'
      have h2 : Q.map (T2H K b c).subtype ≤ Pℓ.map (T2H K b c).subtype := by
        have h2' := Subgroup.map_mono (f := (MulAut.conj t⁻¹).toMonoidHom) h1
        rw [show Mamb = (Q.map (T2H K b c).subtype).map
            (MulAut.conj t).toMonoidHom from rfl, Subgroup.map_map,
          show ((MulAut.conj t⁻¹).toMonoidHom.comp (MulAut.conj t).toMonoidHom) =
            MonoidHom.id _ from by
            refine MonoidHom.ext fun z => ?_
            simp [MulAut.conj_apply, mul_assoc], Subgroup.map_id] at h2'
        rwa [hPℓ_t t⁻¹ (Tstar.inv_mem ht)] at h2'
      exact (Subgroup.map_le_map_iff_of_injective (f := (T2H K b c).subtype)
        (T2H K b c).subtype_injective).mp h2
    have hMeq : M = Q :=
      T2P0H_map_conj_eq_of_borel_le_of_ne_top_of_not_le_point K b c hirr h hBM hMne hMnot
    have hfin : M.map (T2H K b c).subtype = Q.map (T2H K b c).subtype := by rw [hMeq]
    rw [hMmap] at hfin
    exact hfin
  have hQpar : IsParabolicTwo ↥(T2H K b c) Q := by
    have h0 : IsParabolicTwo ↥(T2H K b c) (T2P0H K b c) := by
      have h1 : IsParabolicTwo ↥(T2G K b c) (T2P0 K b c) := T2P0_isParabolic K b c hirr
      have h2 := h1.map (t2e K b c).toMonoidHom (t2e K b c).surjective
      rwa [T2P0H]
    exact h0.map (MulAut.conj h).toMonoidHom (MulAut.conj h).surjective
  have hSQ : (S : Subgroup ↥(T2H K b c)) ≤ Q := by
    rw [hconj]
    exact Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom)
      (Subgroup.map_mono (f := (t2e K b c).toMonoidHom) (T2U_le_T2P0 K b c hirr))
  have hQgood : (IsParabolicTwo ↥(T2H K b c) Q ∧ (S : Subgroup ↥(T2H K b c)) ≤ Q ∧
      (∀ t ∈ Tstar, (Q.map (T2H K b c).subtype).map (MulAut.conj t).toMonoidHom =
        Q.map (T2H K b c).subtype) ∧ ¬ Q ≤ Pℓ) :=
    ⟨hQpar, hSQ, hQ_t, hQnotPℓ⟩
  have hPle : Pstar ≤ Q := hmin.2 hQgood hQle
  have hPeq : Pstar = Q := le_antisymm hPle hQle
  have hQne : Q ≠ ⊤ := by
    intro hQtop
    apply T2P0H_ne_top K b c hirr
    have h2 := congrArg (fun X : Subgroup ↥(T2H K b c) =>
      X.map (MulAut.conj h⁻¹).toMonoidHom) hQtop
    rw [Subgroup.map_top_of_surjective _ (MulAut.conj h⁻¹).surjective] at h2
    rwa [show Q.map (MulAut.conj h⁻¹).toMonoidHom = T2P0H K b c from by
      dsimp [Q]
      rw [Subgroup.map_map]
      have hc : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
          MonoidHom.id ↥(T2H K b c) := by
        refine MonoidHom.ext fun z => ?_
        simp [MulAut.conj_apply, mul_assoc]
      change (T2P0H K b c).map
        (((MulAut.conj h⁻¹).toMonoidHom).comp ((MulAut.conj h).toMonoidHom)) = T2P0H K b c
      rw [hc, Subgroup.map_id]] at h2
  refine ⟨?_, ?_⟩
  · rw [hPeq]
    exact hQne
  · rw [hPeq]
    rcases hres with hL2 | ⟨hn, hbot⟩
    · left
      exact isL2_bar2_hinf_map_equiv (MulAut.conj h) (T2P0H K b c) hL2
    · right
      exact ⟨hn, Hinf_map_eq_bot (MulAut.conj h) (T2P0H K b c) hbot⟩

end TailTwoMinus

end OmegaMinus6Tail

section FinalLine

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open OmegaMinus6Tail

theorem omegaMinus6NaturalLine
    (hsurj : ∀ (K : Type) [Field K] [Finite K] (b c : K) (a : Fin 2 → K) (n : ℕ),
      2 ≤ n → Nat.card K = 2 ^ n → a ≠ 0 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∃ f : ↥(Hinf (tailRankOneParabolic (minusTailForm K b c) a (0 : Fin 2))) →*
          Matrix.SpecialLinearGroup (Fin 2) K, Function.Surjective f ∧ IsPGroup 2 f.ker)
 :
    ∀ (K : Type) [Field K] [Finite K] (b c : K) (m : ℕ), Nat.card K = 2 ^ m →
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      OmegaMinus6Line (CFSG.Quasithin.H.StdMod (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K)
        (CFSG.Quasithin.H.natImage
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c))) m := by
  intro K hF hFin b c m hK hirr
  letI : Field K := hF
  letI : Finite K := hFin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (f := m) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  have hmpos : 0 < m := by
    rcases Nat.eq_zero_or_pos m with rfl | h
    · rw [pow_zero] at hK
      have := Finite.one_lt_card (α := K)
      omega
    · exact h
  have hres : IsL2 (Bar2 (Hinf (T2P0H K b c))) m ∨
      (m = 1 ∧ Hinf (T2P0H K b c) = ⊥) := by
    by_cases hm : 2 ≤ m
    · exact Or.inl (T2P0H_res_of_surj (K := K) b c hirr hm hK
        (hsurj K b c (t2a0 K) m hm hK (t2a0_ne_zero K) hirr))
    · have hm1 : m = 1 := by omega
      have hK2 : Nat.card K = 2 := by rw [hK, hm1, pow_one]
      exact Or.inr ⟨hm1, hinf_T2P0H_eq_bot_of_tail (K := K) b c
        (hinf_rankOneParabolic_tail_eq_bot_of_solvable (r := 2) (qA := minusTailForm K b c)
          (a₀ := t2a0 K) (i := 0)
          (isSolvable_tailRankOneParabolic_F2 (K := K) (b := b) (c := c) hirr hK2))⟩
  set Γ : Subgroup (GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) :=
    CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c) with hΓ
  set ψ : T2V K ≃ₗ[K] (Fin 2 ⊕ Fin 2 ⊕ Fin 2 → K) :=
    (minusTailIsometry 3 K b c).toLinearEquiv with hψ
  let e : Multiplicative (T2V K) ≃* CFSG.Quasithin.H.StdMod (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K :=
    AddEquiv.toMultiplicative ψ.toAddEquiv
  let H : Subgroup (MulAut (Multiplicative (T2V K))) := T2H K b c
  let π : ↥Γ →* ↥H :=
    (t2e K b c).toMonoidHom.comp (t2OmegaEquiv K b c hirr).toMonoidHom
  have hπ : Function.Surjective π := by
    intro x
    obtain ⟨g, rfl⟩ := (t2e K b c).surjective x
    obtain ⟨γ, rfl⟩ := (t2OmegaEquiv K b c hirr).surjective g
    exact ⟨γ, rfl⟩
  have he : ∀ (γ : ↥Γ) (v : Multiplicative (T2V K)),
      e (((π γ : ↥H) : MulAut (Multiplicative (T2V K))) v) = natAct Γ γ (e v) := by
    intro γ v
    have hπγ : ((π γ : ↥H) : MulAut (Multiplicative (T2V K))) =
        linMulAut ((t2OmegaEquiv K b c hirr γ).val) := rfl
    have hev : e v = Multiplicative.ofAdd (ψ (Multiplicative.toAdd v)) := rfl
    rw [hπγ, hev]
    change ψ ((t2OmegaEquiv K b c hirr γ).val (Multiplicative.toAdd v)) =
      (((γ : GL (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) : Matrix (Fin 2 ⊕ Fin 2 ⊕ Fin 2)
        (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K) *ᵥ ψ (Multiplicative.toAdd v))
    have hg : (t2OmegaEquiv K b c hirr γ).val (Multiplicative.toAdd v) =
        ψ.symm (CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K γ.val
          (ψ (Multiplicative.toAdd v))) :=
      tailOmegaEquiv_apply _ _ _ _ _
    rw [hg, LinearEquiv.apply_symm_apply, CFSG.ClassicalGroups.Orthogonal.toLinEquiv_apply]
  have hmap : H.map (CFSG.Quasithin.H.congrHom e) = CFSG.Quasithin.H.natImage Γ :=
    CFSG.Quasithin.H.map_congrHom_eq_natImage Γ hπ e he
  have hH' : H = (CFSG.Quasithin.H.natImage Γ).map
      (CFSG.Quasithin.H.congrHom e.symm) := by
    rw [← hmap, Subgroup.map_map]
    have hcomp : (CFSG.Quasithin.H.congrHom e.symm).comp
        (CFSG.Quasithin.H.congrHom e) = MonoidHom.id _ := by
      refine MonoidHom.ext fun x => MulEquiv.ext fun y => ?_
      simp [CFSG.Quasithin.H.congrHom_apply]
    rw [hcomp, Subgroup.map_id]
  exact omegaMinus6Line_of_map_congr (CFSG.Quasithin.H.natImage Γ) (T2H K b c) m e.symm
    hH' (T2H_line K b c hirr m hres)

theorem hsurj_holds :
    ∀ (K : Type) [Field K] [Finite K] (b c : K) (a : Fin 2 → K) (n : ℕ),
      2 ≤ n → Nat.card K = 2 ^ n → a ≠ 0 → (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      ∃ f : ↥(Hinf (tailRankOneParabolic (minusTailForm K b c) a (0 : Fin 2))) →*
          Matrix.SpecialLinearGroup (Fin 2) K, Function.Surjective f ∧ IsPGroup 2 f.ker := by
  intro K hF hFin b c a n hn hK ha hirr
  haveI : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    exact charP_of_card_eq_prime_pow (f := n) (by rw [← Nat.card_eq_fintype_card]; exact hK)
  exact tailRankOneSL2Surjection_minus (b := b) (c := c) hirr
    (i := (0 : Fin 2)) (by decide) (a₀ := a) ha hn hK

theorem omegaMinus6NaturalLine_holds :
    ∀ (K : Type) [Field K] [Finite K] (b c : K) (m : ℕ), Nat.card K = 2 ^ m →
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      OmegaMinus6Line (CFSG.Quasithin.H.StdMod (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K)
        (CFSG.Quasithin.H.natImage
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c))) m :=
  omegaMinus6NaturalLine hsurj_holds

end FinalLine

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

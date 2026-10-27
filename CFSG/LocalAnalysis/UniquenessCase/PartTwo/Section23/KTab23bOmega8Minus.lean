module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23bSL3
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailEqClosure
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalTailRankOneIsL2
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement Matrix

@[expose] def OmegaMinus8Line (W : Type) [CommGroup W] (H : Subgroup (MulAut W)) (n : ℕ) : Prop :=
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

theorem omegaMinus8Line_of_map_congr (H : Subgroup (MulAut W)) (H' : Subgroup (MulAut V))
    (n : ℕ) (e : W ≃* V) (hH' : H' = H.map (CFSG.Quasithin.H.congrHom e))
    (h : OmegaMinus8Line V H' n) : OmegaMinus8Line W H n := by
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

section LinearImage

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def linMulAut8 : (V ≃ₗ[K] V) →* MulAut (Multiplicative V) where
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
theorem linMulAut8_apply (e : V ≃ₗ[K] V) (x : Multiplicative V) :
    linMulAut8 e x = Multiplicative.ofAdd (e (Multiplicative.toAdd x)) := rfl

theorem linMulAut8_apply_ofAdd (e : V ≃ₗ[K] V) (v : V) :
    linMulAut8 e (Multiplicative.ofAdd v) = Multiplicative.ofAdd (e v) := rfl

theorem linMulAut8_injective : Function.Injective (linMulAut8 (K := K) (V := V)) := by
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

theorem fixV_map_linMulAut8 (A : Subgroup (V ≃ₗ[K] V)) :
    CFSG.Quasithin.fixV (A.map linMulAut8) = linFixV A := by
  ext x
  constructor
  · intro hx g hg
    have h := hx (linMulAut8 g) (Subgroup.mem_map_of_mem linMulAut8 hg)
    rw [linMulAut8_apply] at h
    exact Multiplicative.ofAdd.injective h
  · intro hx g hg
    obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
    rw [linMulAut8_apply, hx a ha, ofAdd_toAdd]

end LinearImage

section TailThreeMinus

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail
open QuadraticMap CFSG.ClassicalGroups.Orthogonal

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

abbrev T3V (K : Type) [Field K] : Type := (Fin 3 ⊕ Fin 3 → K) × (Fin 2 → K)

noncomputable abbrev T3Q (K : Type) [Field K] (b c : K) : QuadraticForm K (T3V K) :=
  quadTail 3 (minusTailForm K b c)

noncomputable abbrev T3G (K : Type) [Field K] (b c : K) : Subgroup (T3V K ≃ₗ[K] T3V K) :=
  orthElementaryGroup (T3Q K b c)

theorem t3q_anisotropic (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (minusTailForm K b c).Anisotropic :=
  anisotropic_minusTailForm hirr

theorem t3q_regular (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (polarBilin (minusTailForm K b c)).Nondegenerate :=
  nondegenerate_minusTailForm hirr

theorem t3q_finrank : Module.finrank K (Fin 2 → K) = 2 := finrank_fin_two_fun

instance t3G_finite (K : Type) [Field K] [Finite K] (b c : K) : Finite ↥(T3G K b c) := by
  haveI : Fintype K := Fintype.ofFinite K
  haveI : Finite (T3V K) := by infer_instance
  haveI : Finite (T3V K → T3V K) := by infer_instance
  haveI : Finite (T3V K ≃ₗ[K] T3V K) :=
    Finite.of_injective ((↑) : (T3V K ≃ₗ[K] T3V K) → T3V K → T3V K)
      DFunLike.coe_injective
  exact Subtype.finite

noncomputable def t3Sylow (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Sylow 2 ↥(T3G K b c) :=
  (isPGroup_tailUnipotent (p := 2) (qA := minusTailForm K b c) (r := 3)
    (t3q_anisotropic hirr)).toSylow
    (not_dvd_index_tailUnipotent (p := 2) (qA := minusTailForm K b c) (r := 3)
      (by norm_num) (t3q_anisotropic hirr) (t3q_regular hirr) (Or.inr t3q_finrank))

@[simp]
theorem t3Sylow_coe (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (t3Sylow (K := K) (b := b) (c := c) hirr : Subgroup ↥(T3G K b c)) =
      (tailUnipotent 3 (minusTailForm K b c)).subgroupOf (T3G K b c) := by
  rw [t3Sylow, IsPGroup.toSylow_coe]

noncomputable abbrev t3U (K : Type) [Field K] (b c : K) : Subgroup ↥(T3G K b c) :=
  (tailUnipotent 3 (minusTailForm K b c)).subgroupOf (T3G K b c)

noncomputable abbrev t3B (K : Type) [Field K] (b c : K) : Subgroup ↥(T3G K b c) :=
  (tailBorel 3 (minusTailForm K b c)).subgroupOf (T3G K b c)

def t3a0 (K : Type) [Field K] : Fin 2 → K := Pi.single 1 1

theorem t3a0_ne_zero (K : Type) [Field K] : t3a0 K ≠ 0 := by
  intro h
  have := congrFun h 1
  simp [t3a0] at this

noncomputable abbrev t3P0 (K : Type) [Field K] (b c : K) : Subgroup ↥(T3G K b c) :=
  (tailRankOneParabolic (minusTailForm K b c) (t3a0 K) (0 : Fin 3)).subgroupOf (T3G K b c)

noncomputable abbrev t3F1 (K : Type) [Field K] : Submodule K (T3V K) :=
  tailFlag K (Fin 2 → K) 3 1

theorem tailBorel_le_stabilizer_t3F1 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    tailBorel 3 (minusTailForm K b c) ≤
      MulAction.stabilizer (T3V K ≃ₗ[K] T3V K) (t3F1 K) := by
  intro g hg
  exact Submodule.mem_stabilizer_submodule_iff_map_eq.2
    ((mem_tailBorel.1 hg).2 1 (by norm_num) (by norm_num))

theorem tailRankOneParabolic_le_of_borel_le_of_not_le_point
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {M : Subgroup (T3V K ≃ₗ[K] T3V K)}
    (hMG : M ≤ T3G K b c)
    (hBM : tailBorel 3 (minusTailForm K b c) ≤ M)
    (hnot : ¬ M ≤ MulAction.stabilizer (T3V K ≃ₗ[K] T3V K) (t3F1 K)) :
    tailRankOneParabolic (minusTailForm K b c) (t3a0 K) 0 ≤ M := by
  classical
  have hani := t3q_anisotropic (K := K) (b := b) (c := c) hirr
  have ha0 := t3a0_ne_zero K
  have hgen := tail_eq_closure_of_borel_le (qA := minusTailForm K b c) (r := 3)
    (a₀ := t3a0 K) hani ha0 hMG hBM
  have hn0 : tailWeylElt 3 (minusTailForm K b c) (t3a0 K) 0 ∈ M := by
    by_contra h
    apply hnot
    rw [hgen, Subgroup.closure_le]
    rintro _ (hb | ⟨i, hi, rfl⟩)
    · exact tailBorel_le_stabilizer_t3F1 (K := K) (b := b) (c := c) hirr hb
    · have hi0 : i ≠ 0 := by rintro rfl; exact h hi
      exact MulAction.mem_stabilizer_iff.2
        ((tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 3)
          (a₀ := t3a0 K) hani ha0 0 i).2 hi0)
  rw [tailRankOneParabolic, Subgroup.closure_le]
  rintro _ (hb | rfl)
  · exact hBM hb
  · exact hn0

theorem t3B_eq_normalizer (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    t3B K b c = Subgroup.normalizer (t3U K b c : Set ↥(T3G K b c)) := by
  change (tailBorel 3 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 3 (minusTailForm K b c))) =
    Subgroup.normalizer (((tailUnipotent 3 (minusTailForm K b c)).subgroupOf
      (orthElementaryGroup (quadTail 3 (minusTailForm K b c)))) :
        Set ↥(orthElementaryGroup (quadTail 3 (minusTailForm K b c))))
  exact (normalizer_tailUnipotent (qA := minusTailForm K b c) (r := 3)
    (t3q_anisotropic hirr) ⟨t3a0 K, t3a0_ne_zero K⟩).symm

theorem t3B_le_t3P0 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    t3B K b c ≤ t3P0 K b c := by
  intro x hx
  exact Subgroup.subset_closure (Or.inl (Subgroup.mem_subgroupOf.mp hx))

theorem t3U_le_t3P0 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    t3U K b c ≤ t3P0 K b c :=
  fun x hx => t3B_le_t3P0 hirr (tailUnipotent_le_tailBorel (t3q_anisotropic hirr)
    (Subgroup.mem_subgroupOf.mp hx))

theorem t3P0_isParabolic (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    IsParabolicTwo ↥(T3G K b c) (t3P0 K b c) := by
  refine ⟨t3Sylow (K := K) (b := b) (c := c) hirr, ?_⟩
  change Subgroup.normalizer
    (((t3Sylow (K := K) (b := b) (c := c) hirr : Subgroup ↥(T3G K b c)) :
      Set ↥(T3G K b c))) ≤ t3P0 K b c
  rw [t3Sylow_coe, ← t3B_eq_normalizer hirr]
  exact t3B_le_t3P0 hirr

theorem t3P0_le_of_borel_le_of_not_le_point
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {P : Subgroup ↥(T3G K b c)}
    (hB : t3B K b c ≤ P)
    (hnot : ¬ P ≤ MulAction.stabilizer ↥(T3G K b c) (t3F1 K)) :
    t3P0 K b c ≤ P := by
  have hMG : P.map (T3G K b c).subtype ≤ T3G K b c := Subgroup.map_subtype_le _
  have hBM : tailBorel 3 (minusTailForm K b c) ≤ P.map (T3G K b c).subtype := by
    rintro x hx
    let xG : ↥(T3G K b c) := ⟨x, tailBorel_le (qA := minusTailForm K b c) hx⟩
    have hxG : xG ∈ t3B K b c := Subgroup.mem_subgroupOf.mpr hx
    simpa [xG] using Subgroup.mem_map_of_mem (T3G K b c).subtype (hB hxG)
  have hnot' : ¬ P.map (T3G K b c).subtype ≤
      MulAction.stabilizer (T3V K ≃ₗ[K] T3V K) (t3F1 K) := by
    intro hle
    apply hnot
    intro p hp
    exact hle (Subgroup.mem_map_of_mem (T3G K b c).subtype hp)
  have hP0 : tailRankOneParabolic (minusTailForm K b c) (t3a0 K) 0 ≤
      P.map (T3G K b c).subtype :=
    tailRankOneParabolic_le_of_borel_le_of_not_le_point (K := K) (b := b) (c := c) hirr
      hMG hBM hnot'
  intro x hx
  obtain ⟨p, hp, hpx⟩ := Subgroup.mem_map.mp (hP0 hx)
  have hpx' : p = x := Subtype.ext hpx
  simpa [hpx'] using hp

noncomputable abbrev t3Pℓ0 (K : Type) [Field K] (b c : K) : Subgroup ↥(T3G K b c) :=
  MulAction.stabilizer ↥(T3G K b c) (t3F1 K)

noncomputable abbrev t3Pℓ (K : Type) [Field K] (b c : K) (h : ↥(T3G K b c)) :
    Subgroup ↥(T3G K b c) :=
  (t3Pℓ0 K b c).map (MulAut.conj h).toMonoidHom

noncomputable abbrev T3H (K : Type) [Field K] (b c : K) :
    Subgroup (MulAut (Multiplicative (T3V K))) :=
  (T3G K b c).map linMulAut8

@[expose] noncomputable def t3e (K : Type) [Field K] (b c : K) :
    ↥(T3G K b c) ≃* ↥(T3H K b c) :=
  Subgroup.equivMapOfInjective (T3G K b c) linMulAut8 linMulAut8_injective

@[simp]
theorem t3e_apply (g : ↥(T3G K b c)) :
    ((t3e K b c g : ↥(T3H K b c)) : MulAut (Multiplicative (T3V K))) =
      linMulAut8 (g : T3V K ≃ₗ[K] T3V K) := rfl

theorem t3e_map_subtype_comp :
    (T3H K b c).subtype.comp (t3e K b c).toMonoidHom =
      linMulAut8.comp (T3G K b c).subtype := by
  refine MonoidHom.ext fun g => ?_
  refine MulEquiv.ext fun x => ?_
  change Multiplicative.ofAdd ((g : T3V K ≃ₗ[K] T3V K) (Multiplicative.toAdd x)) =
    Multiplicative.ofAdd ((g : T3V K ≃ₗ[K] T3V K) (Multiplicative.toAdd x))
  rfl

theorem t3_map_e_map_subtype (A : Subgroup ↥(T3G K b c)) :
    (A.map (t3e K b c).toMonoidHom).map (T3H K b c).subtype =
      (A.map (T3G K b c).subtype).map linMulAut8 := by
  rw [Subgroup.map_map, t3e_map_subtype_comp, ← Subgroup.map_map]

noncomputable abbrev t3F1Sub (K : Type) [Field K] :
    Subgroup (Multiplicative (T3V K)) where
  carrier := {x : Multiplicative (T3V K) | Multiplicative.toAdd x ∈ t3F1 K}
  one_mem' := by
    change (0 : T3V K) ∈ t3F1 K
    exact Submodule.zero_mem _
  mul_mem' := by
    intro x y hx hy
    change Multiplicative.toAdd (x * y) ∈ t3F1 K
    rw [toAdd_mul]
    exact Submodule.add_mem _ hx hy
  inv_mem' := by
    intro x hx
    change Multiplicative.toAdd x⁻¹ ∈ t3F1 K
    rw [toAdd_inv]
    exact Submodule.neg_mem _ hx

theorem t3F1_eq_span :
    t3F1 K = K ∙ hypVec K (Fin 2 → K) (Sum.inl (0 : Fin 3)) := by
  rw [t3F1, tailFlag]
  congr 1
  ext v
  simp only [Set.mem_image, Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · rintro ⟨j, hj, rfl⟩
    have hj0 : j = 0 := by
      fin_cases j <;> simp at hj ⊢
    subst hj0
    rfl
  · rintro rfl
    exact ⟨0, by simp, rfl⟩

theorem t3F1_fixed_eq (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    {v : T3V K | ∀ u ∈ tailUnipotent 3 (minusTailForm K b c), u v = v} =
      (t3F1 K : Set (T3V K)) := by
  rw [t3F1_eq_span]
  exact fixed_tailUnipotent_eq (r := 3) (qA := minusTailForm K b c) (by norm_num)
    (t3q_regular hirr) ⟨t3a0 K, t3a0_ne_zero K⟩

theorem linFixV_tailUnipotent_eq (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    linFixV (tailUnipotent 3 (minusTailForm K b c)) = t3F1Sub K := by
  ext x
  rw [mem_linFixV]
  change (∀ u ∈ tailUnipotent 3 (minusTailForm K b c),
      u (Multiplicative.toAdd x) = Multiplicative.toAdd x) ↔
    Multiplicative.toAdd x ∈ t3F1 K
  exact Set.ext_iff.mp (t3F1_fixed_eq (K := K) (b := b) (c := c) hirr) _

noncomputable abbrev t3UH (K : Type) [Field K] (b c : K) : Subgroup ↥(T3H K b c) :=
  (t3U K b c).map (t3e K b c).toMonoidHom

noncomputable abbrev t3BH (K : Type) [Field K] (b c : K) : Subgroup ↥(T3H K b c) :=
  (t3B K b c).map (t3e K b c).toMonoidHom

noncomputable abbrev t3P0H (K : Type) [Field K] (b c : K) : Subgroup ↥(T3H K b c) :=
  (t3P0 K b c).map (t3e K b c).toMonoidHom

noncomputable abbrev t3Pℓ0H (K : Type) [Field K] (b c : K) : Subgroup ↥(T3H K b c) :=
  (t3Pℓ0 K b c).map (t3e K b c).toMonoidHom

theorem t3UH_map_subtype (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (t3UH K b c).map (T3H K b c).subtype =
      (tailUnipotent 3 (minusTailForm K b c)).map linMulAut8 := by
  rw [t3UH, t3_map_e_map_subtype]
  congr 1
  exact Subgroup.map_subgroupOf_eq_of_le (tailUnipotent_le (r := 3))

theorem mem_t3F1Sub_map_iff (g : T3V K ≃ₗ[K] T3V K) (v : T3V K) :
    Multiplicative.ofAdd v ∈ (t3F1Sub K).map (linMulAut8 g).toMonoidHom ↔
      v ∈ (t3F1 K).map g.toLinearMap := by
  constructor
  · rintro ⟨u, hu, hgu⟩
    refine ⟨Multiplicative.toAdd u, hu, ?_⟩
    have := congrArg Multiplicative.toAdd hgu
    simpa [linMulAut8_apply] using this
  · rintro ⟨w, hw, rfl⟩
    exact ⟨Multiplicative.ofAdd w, hw, by simp [linMulAut8_apply]⟩

theorem t3F1Sub_map_eq_iff (g : T3V K ≃ₗ[K] T3V K) :
    (t3F1Sub K).map (linMulAut8 g).toMonoidHom = t3F1Sub K ↔
      (t3F1 K).map g.toLinearMap = t3F1 K := by
  constructor
  · intro h
    ext v
    rw [← mem_t3F1Sub_map_iff, h]
    rfl
  · intro h
    refine Subgroup.ext fun x => ?_
    rw [← ofAdd_toAdd x]
    rw [mem_t3F1Sub_map_iff, h]
    rfl

theorem mem_stabilizer_linFixV_iff (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (g : T3V K ≃ₗ[K] T3V K) :
    linMulAut8 g ∈ MulAction.stabilizer (MulAut (Multiplicative (T3V K)))
        (linFixV (tailUnipotent 3 (minusTailForm K b c))) ↔
      g ∈ MulAction.stabilizer (T3V K ≃ₗ[K] T3V K) (t3F1 K) := by
  rw [MulAction.mem_stabilizer_iff]
  change ((linFixV (tailUnipotent 3 (minusTailForm K b c))).map
      (linMulAut8 g).toMonoidHom = linFixV (tailUnipotent 3 (minusTailForm K b c))) ↔
    g ∈ MulAction.stabilizer (T3V K ≃ₗ[K] T3V K) (t3F1 K)
  rw [linFixV_tailUnipotent_eq (K := K) (b := b) (c := c) hirr,
    t3F1Sub_map_eq_iff]
  constructor
  · intro h
    rw [Submodule.mem_stabilizer_submodule_iff_map_eq]
    exact h
  · intro h
    rw [Submodule.mem_stabilizer_submodule_iff_map_eq] at h
    exact h

theorem t3BH_eq_normalizer (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    t3BH K b c =
      Subgroup.normalizer (t3UH K b c : Set ↥(T3H K b c)) := by
  rw [t3BH, t3UH, ← Subgroup.map_equiv_normalizer_eq (t3U K b c) (t3e K b c),
    t3B_eq_normalizer hirr]

theorem t3e_symm_comp_toMonoidHom :
    ((t3e K b c).symm.toMonoidHom.comp (t3e K b c).toMonoidHom) =
      MonoidHom.id ↥(T3G K b c) := by
  refine MonoidHom.ext fun x => ?_
  simp

theorem t3e_comp_symm_toMonoidHom :
    ((t3e K b c).toMonoidHom.comp (t3e K b c).symm.toMonoidHom) =
      MonoidHom.id ↥(T3H K b c) := by
  refine MonoidHom.ext fun x => ?_
  simp

theorem t3P0H_le_of_borel_le_of_not_le_point
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {P : Subgroup ↥(T3H K b c)}
    (hB : t3BH K b c ≤ P)
    (hnot : ¬ P ≤ t3Pℓ0H K b c) :
    t3P0H K b c ≤ P := by
  classical
  let Pg : Subgroup ↥(T3G K b c) := P.map (t3e K b c).symm.toMonoidHom
  have hBg : t3B K b c ≤ Pg := by
    intro x hx
    have hxH : t3e K b c x ∈ t3BH K b c := Subgroup.mem_map_of_mem _ hx
    have hxP : t3e K b c x ∈ P := hB hxH
    rw [← (t3e K b c).symm_apply_apply x]
    exact Subgroup.mem_map_of_mem _ hxP
  have hnotg : ¬ Pg ≤ t3Pℓ0 K b c := by
    intro hle
    apply hnot
    have hmap := Subgroup.map_mono (f := (t3e K b c).toMonoidHom) hle
    rw [Subgroup.map_map, t3e_comp_symm_toMonoidHom, Subgroup.map_id] at hmap
    exact hmap
  have hP0 : t3P0 K b c ≤ Pg :=
    t3P0_le_of_borel_le_of_not_le_point (K := K) (b := b) (c := c) hirr hBg hnotg
  intro x hx
  obtain ⟨y, hy, hxy⟩ := Subgroup.mem_map.mp hx
  have hyPg : y ∈ Pg := hP0 hy
  obtain ⟨p, hp, hyp⟩ := Subgroup.mem_map.mp hyPg
  rw [← hxy, ← hyp]
  simpa using hp

theorem t3Pℓ0H_eq_stabilizer (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    t3Pℓ0H K b c =
      MulAction.stabilizer ↥(T3H K b c)
        (linFixV (tailUnipotent 3 (minusTailForm K b c))) := by
  classical
  ext x
  constructor
  · rintro ⟨g, hg, rfl⟩
    have hg' : (g : T3V K ≃ₗ[K] T3V K) ∈
        MulAction.stabilizer (T3V K ≃ₗ[K] T3V K) (t3F1 K) := by
      rwa [t3Pℓ0] at hg
    exact (mem_stabilizer_linFixV_iff (K := K) (b := b) (c := c) hirr
      (g : T3V K ≃ₗ[K] T3V K)).2 hg'
  · intro hx
    obtain ⟨g, hg, hxg⟩ := Subgroup.mem_map.mp (x.2 : (x : MulAut (Multiplicative (T3V K))) ∈ T3H K b c)
    refine ⟨⟨g, hg⟩, ?_, Subtype.ext hxg⟩
    rw [t3Pℓ0]
    refine Submodule.mem_stabilizer_submodule_iff_map_eq.2 ?_
    have hx_amb : (x : MulAut (Multiplicative (T3V K))) ∈
        MulAction.stabilizer (MulAut (Multiplicative (T3V K)))
          (linFixV (tailUnipotent 3 (minusTailForm K b c))) := by
      rw [MulAction.mem_stabilizer_iff] at hx ⊢
      exact hx
    have hx' : linMulAut8 g ∈ MulAction.stabilizer (MulAut (Multiplicative (T3V K)))
        (linFixV (tailUnipotent 3 (minusTailForm K b c))) := by
      rwa [hxg]
    exact (mem_stabilizer_linFixV_iff (K := K) (b := b) (c := c) hirr
      (g : T3V K ≃ₗ[K] T3V K)).1 hx'

noncomputable abbrev t3PℓH (K : Type) [Field K] (b c : K) (h : ↥(T3H K b c)) :
    Subgroup ↥(T3H K b c) :=
  (t3Pℓ0H K b c).map (MulAut.conj h).toMonoidHom

theorem t3P0H_map_conj_le_of_borel_le_of_not_le_point
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) (h : ↥(T3H K b c))
    {P : Subgroup ↥(T3H K b c)}
    (hB : (t3BH K b c).map (MulAut.conj h).toMonoidHom ≤ P)
    (hnot : ¬ P ≤ t3PℓH K b c h) :
    (t3P0H K b c).map (MulAut.conj h).toMonoidHom ≤ P := by
  classical
  let P' : Subgroup ↥(T3H K b c) := P.map (MulAut.conj h⁻¹).toMonoidHom
  have hcomp : ((MulAut.conj h⁻¹).toMonoidHom.comp (MulAut.conj h).toMonoidHom) =
      MonoidHom.id ↥(T3H K b c) := by
    refine MonoidHom.ext fun x => ?_
    simp [MulAut.conj_apply, mul_assoc]
  have hcomp' : ((MulAut.conj h).toMonoidHom.comp (MulAut.conj h⁻¹).toMonoidHom) =
      MonoidHom.id ↥(T3H K b c) := by
    refine MonoidHom.ext fun x => ?_
    simp [MulAut.conj_apply, mul_assoc]
  have hB' : t3BH K b c ≤ P' := by
    intro x hx
    have hfx : (MulAut.conj h).toMonoidHom x ∈ P :=
      hB (Subgroup.mem_map_of_mem (f := (MulAut.conj h).toMonoidHom) hx)
    have hxeq : x = (MulAut.conj h⁻¹).toMonoidHom ((MulAut.conj h).toMonoidHom x) := by
      simp only [MulAut.conj_apply, MulEquiv.coe_toMonoidHom]
      group
    rw [hxeq]
    exact Subgroup.mem_map_of_mem (f := (MulAut.conj h⁻¹).toMonoidHom) hfx
  have hnot' : ¬ P' ≤ t3Pℓ0H K b c := by
    intro hle
    have h2 : P ≤ t3PℓH K b c h := by
      have h3 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hle
      rw [Subgroup.map_map, hcomp', Subgroup.map_id] at h3
      exact h3
    exact hnot h2
  have hP0' : t3P0H K b c ≤ P' :=
    t3P0H_le_of_borel_le_of_not_le_point (K := K) (b := b) (c := c) hirr hB' hnot'
  have h2 : (t3P0H K b c).map (MulAut.conj h).toMonoidHom ≤ P := by
    have h3 := Subgroup.map_mono (f := (MulAut.conj h).toMonoidHom) hP0'
    have h4 : P'.map (MulAut.conj h).toMonoidHom = P := by
      change (P.map (MulAut.conj h⁻¹).toMonoidHom).map
        (MulAut.conj h).toMonoidHom = P
      rw [Subgroup.map_map, hcomp', Subgroup.map_id]
    rwa [h4] at h3
  exact h2

noncomputable def t3SH (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Sylow 2 ↥(T3H K b c) :=
  (t3Sylow (K := K) (b := b) (c := c) hirr).mapSurjective
    (f := (t3e K b c).toMonoidHom) (by simpa using (t3e K b c).surjective)

theorem t3SH_coe (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (t3SH (K := K) (b := b) (c := c) hirr : Subgroup ↥(T3H K b c)) =
      t3UH K b c := by
  rw [t3SH, Sylow.coe_mapSurjective, t3Sylow_coe]

theorem t3P0_ne_top (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    t3P0 K b c ≠ ⊤ := by
  intro htop
  have hani := t3q_anisotropic (K := K) (b := b) (c := c) hirr
  have ha0 := t3a0_ne_zero K
  have hn2G : tailWeylElt 3 (minusTailForm K b c) (t3a0 K) 2 ∈ T3G K b c :=
    tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t3a0 K) 2
  have hn2 : (⟨tailWeylElt 3 (minusTailForm K b c) (t3a0 K) 2, hn2G⟩ :
      ↥(T3G K b c)) ∈ t3P0 K b c := by
    rw [htop]
    exact Subgroup.mem_top _
  have hmem : tailWeylElt 3 (minusTailForm K b c) (t3a0 K) 2 ∈
      tailRankOneParabolic (minusTailForm K b c) (t3a0 K) 0 := hn2
  have hP0stab : tailRankOneParabolic (minusTailForm K b c) (t3a0 K) 0 ≤
      MulAction.stabilizer (T3V K ≃ₗ[K] T3V K)
        (tailFlag K (Fin 2 → K) 3 3) := by
    rw [tailRankOneParabolic, Subgroup.closure_le]
    rintro _ (hb | rfl)
    · refine Submodule.mem_stabilizer_submodule_iff_map_eq.2 ?_
      exact (mem_tailBorel.1 hb).2 3 (by norm_num) (by norm_num)
    · exact MulAction.mem_stabilizer_iff.2
        ((tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 3)
          (a₀ := t3a0 K) hani ha0 2 0).2 (by decide))
  have hfix : tailWeylElt 3 (minusTailForm K b c) (t3a0 K) 2 •
      tailFlag K (Fin 2 → K) 3 3 = tailFlag K (Fin 2 → K) 3 3 :=
    MulAction.mem_stabilizer_iff.1 (hP0stab hmem)
  have hmove := (tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 3)
    (a₀ := t3a0 K) hani ha0 2 2).1 hfix
  exact hmove rfl

theorem t3P0_not_le_t3Pℓ0 (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ t3P0 K b c ≤ t3Pℓ0 K b c := by
  intro hle
  have hani := t3q_anisotropic (K := K) (b := b) (c := c) hirr
  have ha0 := t3a0_ne_zero K
  have hn0P : (⟨tailWeylElt 3 (minusTailForm K b c) (t3a0 K) 0,
      tailWeylElt_mem (qA := minusTailForm K b c) (a₀ := t3a0 K) 0⟩ :
        ↥(T3G K b c)) ∈ t3P0 K b c :=
    Subgroup.mem_subgroupOf.mpr (Subgroup.subset_closure (Or.inr rfl))
  have hn0Pℓ := hle hn0P
  rw [t3Pℓ0] at hn0Pℓ
  have hfix := MulAction.mem_stabilizer_iff.1 hn0Pℓ
  have hfix' : tailWeylElt 3 (minusTailForm K b c) (t3a0 K) 0 •
      t3F1 K = t3F1 K := hfix
  exact ((tailWeylElt_smul_tailFlag (qA := minusTailForm K b c) (r := 3)
    (a₀ := t3a0 K) hani ha0 0 0).1 hfix') rfl

theorem t3P0H_not_le_t3Pℓ0H (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    ¬ t3P0H K b c ≤ t3Pℓ0H K b c := by
  intro hle
  apply t3P0_not_le_t3Pℓ0 (K := K) (b := b) (c := c) hirr
  have h1 := Subgroup.map_mono (f := (t3e K b c).symm.toMonoidHom) hle
  rw [t3P0H, t3Pℓ0H, Subgroup.map_map, Subgroup.map_map,
    t3e_symm_comp_toMonoidHom, Subgroup.map_id] at h1
  simpa using h1

end TailThreeMinus

theorem kTab23b_OmegaMinus8_line_of_natural (W : Type) [CommGroup W] [Finite W]
    (H : Subgroup (MulAut W)) (n : ℕ)
    (hnat : IsNaturalClassicalModule H n) (hperf : ⁅H, H⁆ = H)
    (hline : IsOmega8m ↥H n ∧ NatOmegaMinus H ⊤ ⊥ 8 n)
    (hNat : ∀ (K : Type) [Field K] [Finite K] (b c : K) (m : ℕ), Nat.card K = 2 ^ m →
      (∀ s : K, s ^ 2 + b * s + c ≠ 0) →
      OmegaMinus8Line (CFSG.Quasithin.H.StdMod (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K)
        (CFSG.Quasithin.H.natImage
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))) m) :
    OmegaMinus8Line W H n := by
  obtain ⟨-, K, hF, hFin, b, c, hK, hirr, hReal⟩ := hline.2
  letI : Field K := hF
  letI : Finite K := hFin
  obtain ⟨π, e, he⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KTabC.exists_natEquiv
      (ι := Fin 3 ⊕ Fin 3 ⊕ Fin 2)
      (Γ := CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) (H := H) hReal
  have he' : ∀ (γ : ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))) (w : W),
      e (((π γ : ↥H) : MulAut W) w) =
        CFSG.Quasithin.natAct (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) γ
          (e w) := by
    intro γ w
    have h1 := he γ w
    change e (((π γ : ↥H) : MulAut W) w) = Multiplicative.ofAdd
      (((γ : Matrix.GeneralLinearGroup (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) :
        Matrix (Fin 3 ⊕ Fin 3 ⊕ Fin 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2) K) *ᵥ
        Multiplicative.toAdd (e w))
    rw [← h1, ofAdd_toAdd]
  have hmodel :
      CFSG.Quasithin.H.natImage
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c)) =
        H.map (CFSG.Quasithin.H.congrHom e) :=
    (CFSG.Quasithin.H.map_congrHom_eq_natImage
      (Γ := CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 K b c))
      (H := H) (π := π) π.surjective e he').symm
  exact omegaMinus8Line_of_map_congr H _ n e hmodel (hNat K b c n hK hirr)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

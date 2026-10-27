module

public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmDefs
public import CFSG.LocalAnalysis.StandardType.GGA8NbrOmFrameCore
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSp
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelSpCompBlock
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmCompClass
public import CFSG.LocalAnalysis.StandardType.GGSixStepTwoCoordModelOmCompZero
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinateRegular

public section

namespace CFSG.StandardType

open Polynomial Module Multiplicative CFSG.Assembly CFSG.RankThree.PartOne.KCPrimary
  CFSG.RankThree.PartOne.KCOrthogonal SevOm CoordOm
open CFSG.RankThree.Classical2 (orthDerived)
open CFSG.LieType.Universal

namespace A8Coord

private theorem om4_card_ge_of_two {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
    {Q : QuadraticForm K V} {p : ℕ} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    [Fact p.Prime] (F : SevOm.Frame Q p A r) {H : Subgroup (V ≃ₗ[K] V)}
    [Finite H] {v₁ v₂ : Fin r → ZMod p} (h₁ : F.ι (ofAdd v₁) ∈ H) (h₂ : F.ι (ofAdd v₂) ∈ H)
    {k₁ k₂ : Fin r} (hv₁ : v₁ k₁ ≠ 0) (hv₂ : v₂ k₂ ≠ 0) (h12 : v₁ k₂ = 0) :
    p ^ 2 ≤ Nat.card H := by
  have hmem : ∀ a : ZMod p × ZMod p, F.ι (ofAdd (a.1 • v₁ + a.2 • v₂)) ∈ H := by
    intro a
    rw [ofAdd_add, map_mul]
    exact H.mul_mem (StepTwoToral.ofAdd_smul_mem h₁ _) (StepTwoToral.ofAdd_smul_mem h₂ _)
  have hinj : Function.Injective fun a : ZMod p × ZMod p => (⟨_, hmem a⟩ : H) := by
    intro a b hab
    have h0 : a.1 • v₁ + a.2 • v₂ = b.1 • v₁ + b.2 • v₂ :=
      ofAdd.injective (F.inj (congrArg Subtype.val hab))
    have e2 := congrFun h0 k₂
    have e1 := congrFun h0 k₁
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, h12, mul_zero, zero_add] at e2
    have hb : a.2 = b.2 := mul_right_cancel₀ hv₂ e2
    rw [hb] at e1
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, add_left_inj] at e1
    exact Prod.ext (mul_right_cancel₀ hv₁ e1) hb
  have hcard : Nat.card (ZMod p × ZMod p) = p ^ 2 := by
    rw [Nat.card_prod, Nat.card_zmod]
    ring
  have h := Nat.card_le_card_of_injective _ hinj
  rwa [hcard] at h

private theorem om4_zero_class {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q p A r) {β : Fin r → ZMod p} (hβ0 : β ≠ 0)
    (hh1 : (X - 1 : K[X]) ∈ primaryFactors (F.ι (ofAdd β)).toLinearMap)
    {L : Subgroup (V ≃ₗ[K] V)} (hLF : L ≤ supportedBlock Q (F.ι (ofAdd β)) (X - 1))
    (hcardL : Nat.card (A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p) :
    ∃ j, β j ≠ 0 ∧ ∀ i, i ≠ j → β i = 0 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  set x := F.ι (ofAdd β) with hxdef
  have hx : OddOrderIsometry Q p x := F.oddOrderIsometry hQ hp2 hp hAΩ (ofAdd β)
  have hxA : x ∈ A := F.mem _
  have hAc : ∀ y ∈ A, y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (frame_comm F hy hxA)
  have hsingle : ∀ i, β i ≠ 0 →
      F.ι (ofAdd (Pi.single i 1)) ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := by
    intro i hi
    refine Subgroup.mem_inf.mpr ⟨F.mem _, Subgroup.mem_centralizer_iff.mpr fun g hg =>
      commute_of_triv hx hh1 (hLF hg) (hAc _ (F.mem _)) fun v hv => ?_⟩
    rw [orbitSpace_X_sub_one] at hv
    refine (F.fix _ v).mpr fun i' hi' u hu => ?_
    have : i' = i := by
      by_contra hne
      exact hi' (by rw [toAdd_ofAdd, Pi.single_eq_of_ne hne])
    subst this
    exact (F.fix (ofAdd β) v).mp (mem_fixedSpace.mp hv) i' hi u hu
  obtain ⟨j, hj⟩ : ∃ j, β j ≠ 0 := by
    by_contra h
    push Not at h
    exact hβ0 (funext h)
  refine ⟨j, hj, fun i hij => ?_⟩
  by_contra hi
  have h2 := om4_card_ge_of_two F (hsingle j hj) (hsingle i hi) (k₁ := j) (k₂ := i) (by simp)
    (by simp) (by simp [Ne.symm hij])
  exact absurd (h2.trans hcardL) (not_le.mpr (by
    have := hp.one_lt
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right this (by norm_num)))

private theorem om4_finrank_fixedSpace_single {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate)
    (F : SevOm.Frame Q p A r) {β : Fin r → ZMod p} {j : Fin r} (hj : β j ≠ 0)
    (hz : ∀ i, i ≠ j → β i = 0) :
    finrank K (fixedSpace (F.ι (ofAdd β))) + finrank K (F.U j) = finrank K V := by
  have heq : fixedSpace (F.ι (ofAdd β)) =
      LinearMap.BilinForm.orthogonal (QuadraticMap.polarBilin Q) (F.U j) := by
    ext v
    rw [mem_fixedSpace, LinearMap.BilinForm.mem_orthogonal_iff, F.fix]
    constructor
    · intro h u hu
      exact h j hj u hu
    · intro h i hi u hu
      have hij : i = j := by
        by_contra hne
        exact hi (hz i hne)
      subst hij
      exact h u hu
  rw [heq, LinearMap.BilinForm.finrank_orthogonal hQ, Nat.sub_add_cancel (Submodule.finrank_le _)]

private theorem om4_zeta_pow_eq_iff {K : Type} [Field K] {p : ℕ} {ζ : Kˣ}
    (hζ : orderOf ζ = p) (m n : ℕ) :
    (ζ : K) ^ m = (ζ : K) ^ n ↔ (m : ZMod p) = n := by
  rw [← Units.val_pow_eq_pow_val, ← Units.val_pow_eq_pow_val, Units.val_inj,
    pow_eq_pow_iff_modEq, hζ, ZMod.natCast_eq_natCast_iff]

private theorem om4_class_full {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime) (hp2 : p ≠ 2)
    (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q p A r) {ζ : Kˣ} (hζ : orderOf ζ = p)
    (hal : CoordOm.FrameAligned F ζ) (hdim : ∀ i, finrank K (F.U i) = 2) (β : Fin r → ZMod p)
    {k : ℕ} (hk : (k : ZMod p) ≠ 0)
    (hh : X - C ((ζ : K) ^ k) ∈ primaryFactors (F.ι (ofAdd β)).toLinearMap)
    {L : Subgroup (V ≃ₗ[K] V)} (hLB : L ≤ supportedBlock Q (F.ι (ofAdd β)) (X - C ((ζ : K) ^ k)))
    (hcardL : Nat.card (A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) : Subgroup _) ≤ p) :
    ∀ i, β i = k ∨ β i = -k := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  have : Finite (V ≃ₗ[K] V) := by
    have : Finite V := Module.finite_of_finite K
    exact Finite.of_injective (fun e : V ≃ₗ[K] V => (e : V → V))
      fun _ _ he => LinearEquiv.ext (congrFun he)
  set h : K[X] := X - C ((ζ : K) ^ k) with hhdef
  set x := F.ι (ofAdd β) with hxdef
  have hx : OddOrderIsometry Q p x := F.oddOrderIsometry hQ hp2 hp hAΩ (ofAdd β)
  have hxA : x ∈ A := F.mem _
  have hX : h ≠ X - 1 := by
    intro he
    have h1 : (ζ : K) ^ k = (ζ : K) ^ 0 := by
      have := congrArg (eval 0) he
      simp only [hhdef, eval_sub, eval_X, eval_C, eval_one, zero_sub, neg_inj] at this
      rw [pow_zero]
      exact this
    exact hk (by simpa using (om4_zeta_pow_eq_iff hζ k 0).mp h1)
  have hAc : ∀ y ∈ A, y ∈ Subgroup.centralizer ({x} : Set (V ≃ₗ[K] V)) := fun y hy =>
    Subgroup.mem_centralizer_singleton_iff.mpr (frame_comm F hy hxA)
  have hdich := fun i => omf_piece_dichotomy (k := k) hp hp2 hAΩ F hζ hal hdim β i
  have hoff : ∀ t : Multiplicative (Fin r → ZMod p),
      (∀ j, toAdd t j ≠ 0 → F.U j ≤ othersSpace x.toLinearMap h) →
        F.ι t ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := fun t ht =>
    Subgroup.mem_inf.mpr ⟨F.mem t, Subgroup.mem_centralizer_iff.mpr fun g hg =>
      commute_of_triv hx hh (hLB hg) (hAc _ (F.mem t)) (frame_triv_orbit F hx hh ht)⟩
  by_contra hno
  push Not at hno
  obtain ⟨k₀, hk₀⟩ := hno
  have hk₀' : ¬ (β k₀ = k ∨ β k₀ = -k) := by
    rintro (h1 | h1)
    · exact hk₀.1 h1
    · exact hk₀.2 h1
  have hsingle : F.ι (ofAdd (Pi.single k₀ 1)) ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := by
    refine hoff _ fun j hj => ?_
    have hjk : j = k₀ := by
      by_contra hne
      exact hj (by rw [toAdd_ofAdd, Pi.single_eq_of_ne hne])
    rw [hjk]
    exact (hdich k₀).2 hk₀'
  set t : Fin r → ZMod p := fun i => if β i = k ∨ β i = -k then β i else 0 with htdef
  have hy : F.ι (ofAdd (t - β)) ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := by
    refine hoff _ fun j hj => ?_
    have hPj : ¬ (β j = k ∨ β j = -k) := by
      intro hP
      apply hj
      rw [toAdd_ofAdd, Pi.sub_apply, htdef]
      simp only [hP, ite_true, sub_self]
    exact (hdich j).2 hPj
  have hxL : x ∈ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := by
    refine Subgroup.mem_centralizer_iff.mpr fun g hg => ?_
    have hgc := (Subgroup.mem_inf.mp (mem_supportedBlock.mp (hLB hg)).1).2
    exact Subgroup.mem_centralizer_singleton_iff.mp hgc
  have htx : F.ι (ofAdd t) = x * F.ι (ofAdd (t - β)) := by
    rw [hxdef, ← map_mul, ← ofAdd_add, add_sub_cancel]
  have ht : F.ι (ofAdd t) ∈ A ⊓ Subgroup.centralizer (L : Set (V ≃ₗ[K] V)) := by
    refine Subgroup.mem_inf.mpr ⟨F.mem _, ?_⟩
    rw [htx]
    exact Subgroup.mul_mem _ hxL (Subgroup.mem_inf.mp hy).2
  obtain ⟨i₀, hi₀⟩ : ∃ i₀, β i₀ = k ∨ β i₀ = -k := by
    by_contra hS
    push Not at hS
    have ht0 : t = 0 := funext fun i => by
      simp only [htdef]
      rw [if_neg (by rintro (h1 | h1); exacts [(hS i).1 h1, (hS i).2 h1])]
      rfl
    obtain ⟨u, hu, hu0⟩ :=
      (Submodule.ne_bot_iff _).mp (primaryComponent_ne_bot hx.squarefree_minpoly hh)
    have huo : u ∈ orbitSpace x.toLinearMap h := Submodule.mem_sup_left hu
    have hyu : F.ι (ofAdd (t - β)) u = u := frame_triv_orbit F hx hh (fun j hj => by
      have hPj : ¬ (β j = k ∨ β j = -k) := by
        intro hP
        apply hj
        rw [toAdd_ofAdd, Pi.sub_apply, htdef]
        simp only [hP, ite_true, sub_self]
      exact (hdich j).2 hPj) u huo
    have hfix : x u = u := by
      have h1 : F.ι (ofAdd t) u = u := by rw [ht0, ofAdd_zero, map_one]; rfl
      rw [htx, LinearEquiv.mul_apply, hyu] at h1
      exact h1
    exact hu0 (eq_zero_of_fix_orbit hx hp hp2 hh hX huo hfix)
  have hti₀ : t i₀ ≠ 0 := by
    simp only [htdef, hi₀, ite_true]
    rcases hi₀ with h1 | h1 <;> rw [h1]
    · exact hk
    · exact neg_ne_zero.mpr hk
  have hne : i₀ ≠ k₀ := fun e => hk₀' (e ▸ hi₀)
  have h2 := om4_card_ge_of_two F hsingle ht (k₁ := k₀) (k₂ := i₀) (by simp) hti₀
    (by simp [hne])
  exact absurd (h2.trans hcardL) (not_le.mpr (by
    have := hp.one_lt
    calc p = p ^ 1 := (pow_one p).symm
      _ < p ^ 2 := Nat.pow_lt_pow_right this (by norm_num)))

private theorem om4_compShape_three {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type}
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {Q : QuadraticForm K V} {p : ℕ}
    {A : Subgroup (V ≃ₗ[K] V)}
    (hQ : (QuadraticMap.polarBilin Q).Nondegenerate) (hp : p.Prime)
    (hp2 : p ≠ 2) (hV : finrank K V = 8) (hAΩ : A ≤ orthDerived Q) (F : SevOm.Frame Q p A 3)
    {ζ : Kˣ} (hζ : orderOf ζ = p) (hdim : ∀ i, finrank K (F.U i) = 2)
    (hal : CoordOm.FrameAligned F ζ)
    {β : Fin 3 → ZMod p} (hβ0 : β ≠ 0) (hβal : CoordSp.SpAligned β)
    {J : Subgroup (V ≃ₗ[K] V)}
    (hJ : CFSG.Assembly.IsComponentOf J (orthDerived Q ⊓ Subgroup.centralizer {F.ι (ofAdd β)}))
    (hcent : Nat.card (A ⊓ Subgroup.centralizer (J : Set (V ≃ₗ[K] V)) :
      Subgroup (V ≃ₗ[K] V)) ≤ p) :
    (∃ j : Fin 3, β j ≠ 0 ∧ (∀ i, i ≠ j → β i = 0) ∧
        finrank K (fixedSpace (F.ι (ofAdd β))) = 6 ∧
        J ≤ supportedBlock Q (F.ι (ofAdd β)) (X - 1) ∧
        ∀ u ∈ supportedBlock Q (F.ι (ofAdd β)) (X - 1), u ^ p = 1 → u ∈ J) ∨
    (∃ c : ZMod p, c ≠ 0 ∧ (∀ i, β i = c) ∧
        ∃ h ∈ primaryFactors (F.ι (ofAdd β)).toLinearMap, h ≠ X - 1 ∧
          J = specialBlock Q (F.ι (ofAdd β)) h ∧
          primaryMultiplicity (F.ι (ofAdd β)).toLinearMap h = 3) := by
  have : NeZero p := ⟨hp.ne_zero⟩
  have hx : OddOrderIsometry Q p (F.ι (ofAdd β)) := F.oddOrderIsometry hQ hp2 hp hAΩ (ofAdd β)
  have hL' := isComponentOf_isometryCentralizer hJ
  obtain ⟨h, hh, hLF⟩ := exists_le_supportedBlock hx hL'
  by_cases hX : h = X - 1
  · subst hX
    obtain ⟨j, hj, hz⟩ := om4_zero_class hQ hp hp2 hAΩ F hβ0 hh hLF hcent
    have h6 : finrank K (fixedSpace (F.ι (ofAdd β))) = 6 := by
      have := om4_finrank_fixedSpace_single hQ F hj hz
      rw [hdim j, hV] at this
      omega
    obtain ⟨-, hcase⟩ := fixed_case hx hp hp2 hL' hLF
    left
    refine ⟨j, hj, hz, h6, hLF, ?_⟩
    rcases hcase with h4 | hall
    · omega
    · exact hall
  · right
    obtain ⟨k, hkp, rfl⟩ := omf_exists_eq_X_sub_C hx hp.ne_zero hζ hh
    have hk : (k : ZMod p) ≠ 0 := by
      intro h0
      have hk0 : k = 0 := by
        have := ZMod.val_natCast_of_lt hkp
        rw [h0, ZMod.val_zero] at this
        exact this.symm
      subst hk0
      exact hX (by rw [pow_zero, C_1])
    have hJeq := free_case hx hp hp2 hh hX hL' hLF
    have hpm := om4_class_full hQ hp hp2 hAΩ F hζ hal hdim β hk hh hLF hcent
    obtain ⟨c', hc', hconst⟩ := omf_const_of_spAligned hβal hk hpm
    exact ⟨c', hc', hconst, _, hh, hX, hJeq,
      omf_primaryMultiplicity_eq_three hQ hp hp2 hAΩ F hζ hal hdim hV hc' hconst hh hX⟩

theorem omCompShape {A : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)} (hAΩ : A ≤ omΩ)
    (F : SevOm.Frame omQ 7 A 3) (ζ : (GaloisField 2 3)ˣ) (hζ : orderOf ζ = 7)
    (hdim : ∀ i, finrank (GaloisField 2 3) (F.U i) = 2) (hal : CoordOm.FrameAligned F ζ)
    (hmoves : CoordOm.FrameMovesAll F (CoordSp.signs 7))
    {β : Fin 3 → ZMod 7} (hβ0 : β ≠ 0) (hβal : CoordSp.SpAligned β)
    {J : Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)}
    (hJ : IsComponentOf J (omΩ ⊓ Subgroup.centralizer {F.ι (ofAdd β)}))
    (hcent : Nat.card (A ⊓ Subgroup.centralizer (J : Set (OmV ≃ₗ[GaloisField 2 3] OmV)) :
      Subgroup (OmV ≃ₗ[GaloisField 2 3] OmV)) ≤ 7) :
    (∃ j : Fin 3, β j ≠ 0 ∧ (∀ i, i ≠ j → β i = 0) ∧
        finrank (GaloisField 2 3) (fixedSpace (F.ι (ofAdd β))) = 6 ∧
        J ≤ supportedBlock omQ (F.ι (ofAdd β)) (X - 1) ∧
        ∀ u ∈ supportedBlock omQ (F.ι (ofAdd β)) (X - 1), u ^ 7 = 1 → u ∈ J) ∨
    (∃ c : ZMod 7, c ≠ 0 ∧ (∀ i, β i = c) ∧
        ∃ h ∈ primaryFactors (F.ι (ofAdd β)).toLinearMap, h ≠ X - 1 ∧
          J = specialBlock omQ (F.ι (ofAdd β)) h ∧
          primaryMultiplicity (F.ι (ofAdd β)).toLinearMap h = 3) := by
  haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
  have hQ : (QuadraticMap.polarBilin omQ).Nondegenerate :=
    (CFSG.ComponentClassification.CatalogueBOrthogonalPointData.regular_coordinateQuadMinus
      4 (GaloisField 2 3) (minusCoeffs 2 3).1 (minusCoeffs 2 3).2 (by norm_num)
      (minusCoeffs_irr 2 3)).1
  have hV : finrank (GaloisField 2 3) OmV = 8 := by
    simp only [OmV, Module.finrank_fin_fun]
  exact om4_compShape_three hQ (Fact.out) (by norm_num) hV hAΩ F hζ hdim hal hβ0 hβal hJ hcent

end A8Coord

end CFSG.StandardType

end

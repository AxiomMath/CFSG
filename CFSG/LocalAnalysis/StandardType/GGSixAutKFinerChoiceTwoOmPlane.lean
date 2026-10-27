module

public import CFSG.LocalAnalysis.StandardType.GGSixSeventeenWitOmMain
public import CFSG.LocalAnalysis.StandardType.GGSixAutKFinerChoiceTwoCent
public import CFSG.RankThree.PartOne.S11d.OrthCyclic
public import CFSG.RankThree.PartOne.S11d.LieCentralizerBlock
public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.RankThree.PartOne.S9.Sylow.ExclusionBasic
public import CFSG.RankThree.Theta.ThreeComponentOrbitCover

public section

namespace CFSG.StandardType

namespace ChoiceTwoOm

open Module Multiplicative SevOm QuadraticMap

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Polar

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}

theorem polar_map_of_isom {g : V ≃ₗ[K] V} (hg : ∀ v, Q (g v) = Q v) (x y : V) :
    polar Q (g x) (g y) = polar Q x y := by
  simp only [QuadraticMap.polar, ← map_add, hg]

variable [CharP K 2]

theorem polar_self_eq_zero (x : V) : polar Q x x = 0 := by
  rw [QuadraticMap.polar_self, two_nsmul, CharTwo.add_self_eq_zero]

theorem eq_add_of_add_add_eq_zero (K : Type) [Field K] [CharP K 2] [Module K V] {a b c : V}
    (h : a + b + c = 0) : a = b + c := by
  have h2 : (a + b + c) + (b + c) = a := by
    rw [add_assoc a, add_assoc, ChoiceTwo.add_self_eq_zero_of_charTwo (K := K), add_zero]
  rw [h, zero_add] at h2
  exact h2.symm

end Polar

section Gen

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

@[expose] noncomputable def gen (F : Frame Q 3 A r) (i : Fin r) : V ≃ₗ[K] V :=
  F.ι (ofAdd (Pi.single i 1))

theorem ofAdd_single_eq_pow (i : Fin r) (a : ZMod 3) :
    (ofAdd (Pi.single i a) : Multiplicative (Fin r → ZMod 3)) =
      ofAdd (Pi.single i (1 : ZMod 3)) ^ a.val := by
  apply toAdd.injective
  rw [toAdd_pow, toAdd_ofAdd, toAdd_ofAdd]
  funext l
  by_cases h : l = i
  · subst h
    rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, nsmul_eq_mul, mul_one,
      ZMod.natCast_zmod_val]
  · rw [Pi.smul_apply, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, smul_zero]

theorem toAdd_single_ne (i : Fin r) :
    toAdd (ofAdd (Pi.single i (1 : ZMod 3)) : Multiplicative (Fin r → ZMod 3)) i ≠ 0 := by
  rw [toAdd_ofAdd, Pi.single_eq_same]
  exact one_ne_zero

theorem toAdd_single_of_ne {i j : Fin r} (h : j ≠ i) :
    toAdd (ofAdd (Pi.single i (1 : ZMod 3)) : Multiplicative (Fin r → ZMod 3)) j = 0 := by
  rw [toAdd_ofAdd, Pi.single_eq_of_ne h]

theorem act_piece (F : Frame Q 3 A r) (s : Multiplicative (Fin r → ZMod 3)) {i : Fin r}
    {u : V} (hu : u ∈ F.U i) : F.ι s u = (gen F i ^ (toAdd s i).val) u := by
  have hs : s = ofAdd (Pi.single i (toAdd s i)) * ofAdd (toAdd s - Pi.single i (toAdd s i)) := by
    apply toAdd.injective
    rw [toAdd_mul, toAdd_ofAdd, toAdd_ofAdd, add_sub_cancel]
  have h0 : toAdd (ofAdd (toAdd s - Pi.single i (toAdd s i)) :
      Multiplicative (Fin r → ZMod 3)) i = 0 := by
    rw [toAdd_ofAdd, Pi.sub_apply, Pi.single_eq_same, sub_self]
  conv_lhs => rw [hs]
  rw [map_mul, LinearEquiv.mul_apply, F.triv _ i h0 u hu, ofAdd_single_eq_pow, map_pow]
  rfl

theorem gen_mem (F : Frame Q 3 A r) (i : Fin r) {j : Fin r} {u : V} (hu : u ∈ F.U j) :
    gen F i u ∈ F.U j :=
  F.mapsTo _ j u hu

theorem gen_mem_A (F : Frame Q 3 A r) (i : Fin r) : gen F i ∈ A := F.mem _

theorem gen_gen_gen (F : Frame Q 3 A r) (i : Fin r) (v : V) :
    gen F i (gen F i (gen F i v)) = v := by
  have h := congrArg (fun g : V ≃ₗ[K] V => g v) (F.pow_p (ofAdd (Pi.single i (1 : ZMod 3))))
  simpa [pow_succ, LinearEquiv.mul_apply, gen] using h

theorem gen_of_mem_ne (F : Frame Q 3 A r) {i j : Fin r} (hji : j ≠ i) {u : V}
    (hu : u ∈ F.U j) : gen F i u = u :=
  F.triv _ j (toAdd_single_of_ne hji) u hu

theorem eq_zero_of_gen_eq (F : Frame Q 3 A r) {i : Fin r} {u : V} (hu : u ∈ F.U i)
    (h : gen F i u = u) : u = 0 :=
  F.fpf _ i (toAdd_single_ne i) u hu h

theorem gen_sq_add (F : Frame Q 3 A r) (i : Fin r) {u : V} (hu : u ∈ F.U i) :
    gen F i (gen F i u) + gen F i u + u = 0 := by
  have hvU : gen F i (gen F i u) + gen F i u + u ∈ F.U i :=
    add_mem (add_mem (gen_mem F i (gen_mem F i hu)) (gen_mem F i hu)) hu
  refine eq_zero_of_gen_eq F hvU ?_
  rw [map_add, map_add, gen_gen_gen]
  abel

theorem exists_Q_ne_zero (F : Frame Q 3 A r) (i : Fin r) : ∃ u ∈ F.U i, Q u ≠ 0 := by
  by_contra h
  push Not at h
  obtain ⟨u, hu, hu0⟩ := (Submodule.ne_bot_iff _).mp (F.ne_bot i)
  apply hu0
  refine F.nondeg i u hu fun v hv => ?_
  rw [QuadraticMap.polar, h _ (add_mem hv hu), h v hv, h u hu, sub_zero, sub_zero]

variable [CharP K 2]

theorem gen_gen (F : Frame Q 3 A r) (i : Fin r) {u : V} (hu : u ∈ F.U i) :
    gen F i (gen F i u) = gen F i u + u :=
  eq_add_of_add_add_eq_zero K (gen_sq_add F i hu)

theorem polar_gen (F : Frame Q 3 A r) (hAQ : ∀ a ∈ A, ∀ v, Q (a v) = Q v) {i : Fin r} {u : V}
    (hu : u ∈ F.U i) (hQu : Q u = 1) : polar Q u (gen F i u) = 1 := by
  have hy : ∀ v, Q (gen F i v) = Q v := hAQ _ (gen_mem_A F i)
  have h1 : u + gen F i u = gen F i (gen F i u) := by rw [gen_gen F i hu, add_comm]
  rw [QuadraticMap.polar, h1, hy, hy, hQu, sub_self, zero_sub, CharTwo.neg_eq]

end Gen

section Proj

variable {K : Type} [Field K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  {Q : QuadraticForm K V}

@[expose] noncomputable def proj (Q : QuadraticForm K V) (u w : V) : V →ₗ[K] V :=
  ((polarBilin Q).flip w).smulRight u + ((polarBilin Q).flip u).smulRight w

omit [CharP K 2] in
theorem proj_apply (u w v : V) : proj Q u w v = polar Q v w • u + polar Q v u • w := by
  simp [proj, LinearMap.smulRight_apply]

variable {u w : V}

theorem proj_comb (huw : polar Q u w = 1) (a b : K) :
    proj Q u w (a • u + b • w) = a • u + b • w := by
  rw [proj_apply, polar_add_left, polar_add_left, polar_smul_left, polar_smul_left,
    polar_smul_left, polar_smul_left, polar_self_eq_zero, polar_self_eq_zero, huw,
    polar_comm Q w u, huw]
  simp

theorem proj_u (huw : polar Q u w = 1) : proj Q u w u = u := by
  simpa using proj_comb huw 1 0

theorem proj_w (huw : polar Q u w = 1) : proj Q u w w = w := by
  simpa using proj_comb huw 0 1

omit [CharP K 2] in
theorem proj_of_perp {v : V} (h1 : polar Q v w = 0) (h2 : polar Q v u = 0) :
    proj Q u w v = 0 := by
  rw [proj_apply, h1, h2, zero_smul, zero_smul, add_zero]

theorem polar_sub_proj_u (huw : polar Q u w = 1) (v : V) :
    polar Q (v - proj Q u w v) u = 0 := by
  rw [polar_sub_left, proj_apply, polar_add_left, polar_smul_left, polar_smul_left,
    polar_self_eq_zero, polar_comm Q w u, huw]
  simp

theorem polar_sub_proj_w (huw : polar Q u w = 1) (v : V) :
    polar Q (v - proj Q u w v) w = 0 := by
  rw [polar_sub_left, proj_apply, polar_add_left, polar_smul_left, polar_smul_left,
    polar_self_eq_zero, huw]
  simp

theorem proj_proj (huw : polar Q u w = 1) (v : V) :
    proj Q u w (proj Q u w v) = proj Q u w v := by
  have h := proj_comb huw (polar Q v w) (polar Q v u)
  rwa [← proj_apply] at h

omit [CharP K 2] in
theorem polar_comb_of_perp {x : V} (h1 : polar Q x u = 0) (h2 : polar Q x w = 0) (a b : K) :
    polar Q x (a • u + b • w) = 0 := by
  rw [polar_add_right, polar_smul_right, polar_smul_right, h1, h2, smul_zero, smul_zero,
    add_zero]

variable {y : V ≃ₗ[K] V}

omit [CharP K 2] in
theorem y_comb (hyu : y u = w) (hyw : y w = u + w) (a b : K) :
    y (a • u + b • w) = b • u + (a + b) • w := by
  rw [map_add, map_smul, map_smul, hyu, hyw, smul_add, add_smul]
  abel

theorem y_u_add_w (hyu : y u = w) (hyw : y w = u + w) : y (u + w) = u := by
  rw [map_add, hyu, hyw, add_comm u w, ← add_assoc,
    ChoiceTwo.add_self_eq_zero_of_charTwo (K := K), zero_add]

theorem proj_y (hy : ∀ v, Q (y v) = Q v) (hyu : y u = w) (hyw : y w = u + w) (v : V) :
    proj Q u w (y v) = y (proj Q u w v) := by
  rw [proj_apply, proj_apply, y_comb hyu hyw]
  have e1 : polar Q (y v) w = polar Q v u := by
    rw [← hyu]
    exact polar_map_of_isom hy v u
  have e2 : polar Q (y v) u = polar Q v u + polar Q v w := by
    conv_lhs => rw [← y_u_add_w hyu hyw]
    rw [polar_map_of_isom hy, polar_add_right]
  rw [e1, e2, add_comm (polar Q v u)]

@[expose] noncomputable def rotL (Q : QuadraticForm K V) (u w : V) (y : V ≃ₗ[K] V) :
    V →ₗ[K] V :=
  LinearMap.id - proj Q u w + proj Q u w ∘ₗ y.toLinearMap

omit [CharP K 2] in
theorem rotL_apply (v : V) : rotL Q u w y v = v - proj Q u w v + proj Q u w (y v) := rfl

theorem rotL_apply' (hy : ∀ v, Q (y v) = Q v) (hyu : y u = w) (hyw : y w = u + w) (v : V) :
    rotL Q u w y v = (v - proj Q u w v) + y (proj Q u w v) := by
  rw [rotL_apply, proj_y hy hyu hyw]

variable (huw : polar Q u w = 1) (hy : ∀ v, Q (y v) = Q v) (hyu : y u = w) (hyw : y w = u + w)
include huw hy hyu hyw

theorem proj_rotL (v : V) : proj Q u w (rotL Q u w y v) = y (proj Q u w v) := by
  rw [rotL_apply' hy hyu hyw, map_add, map_sub, proj_proj huw, sub_self, zero_add, proj_y hy hyu hyw,
    proj_proj huw]

theorem sub_proj_rotL (v : V) :
    rotL Q u w y v - proj Q u w (rotL Q u w y v) = v - proj Q u w v := by
  rw [proj_rotL huw hy hyu hyw, rotL_apply' hy hyu hyw]
  abel

theorem rotL_three (hy3 : ∀ v, y (y (y v)) = v) (v : V) :
    rotL Q u w y (rotL Q u w y (rotL Q u w y v)) = v := by
  rw [rotL_apply' hy hyu hyw (rotL Q u w y (rotL Q u w y v)),
    sub_proj_rotL huw hy hyu hyw, sub_proj_rotL huw hy hyu hyw, proj_rotL huw hy hyu hyw,
    proj_rotL huw hy hyu hyw, hy3]
  abel

theorem Q_rotL (v : V) : Q (rotL Q u w y v) = Q v := by
  have hq1 := polar_sub_proj_u huw v
  have hq2 := polar_sub_proj_w huw v
  have hp : proj Q u w v = polar Q v w • u + polar Q v u • w := proj_apply u w v
  have h1 : polar Q (v - proj Q u w v) (y (proj Q u w v)) = 0 := by
    rw [hp, y_comb hyu hyw]
    exact polar_comb_of_perp hq1 hq2 _ _
  have h2 : polar Q (v - proj Q u w v) (proj Q u w v) = 0 := by
    rw [hp]
    exact polar_comb_of_perp hq1 hq2 _ _
  have h3 : Q v = Q (v - proj Q u w v) + Q (proj Q u w v) := by
    conv_lhs => rw [show v = (v - proj Q u w v) + proj Q u w v by abel]
    rw [QuadraticMap.map_add (⇑Q), h2, add_zero]
  rw [rotL_apply' hy hyu hyw, QuadraticMap.map_add (⇑Q), h1, add_zero, hy, h3]

end Proj

section Plane

variable {K : Type} [Field K] [Finite K] [CharP K 2] {V : Type} [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] {Q : QuadraticForm K V} {A : Subgroup (V ≃ₗ[K] V)} {r : ℕ}

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem mem_of_single {H : Subgroup (Multiplicative (Fin r → ZMod 3))}
    (h : ∀ j, (ofAdd (Pi.single j (1 : ZMod 3)) : Multiplicative (Fin r → ZMod 3)) ∈ H)
    (s : Multiplicative (Fin r → ZMod 3)) : s ∈ H := by
  have hs : s = ∏ j, (ofAdd (Pi.single j (1 : ZMod 3)) : Multiplicative (Fin r → ZMod 3)) ^
      (toAdd s j).val := by
    simp only [← ofAdd_single_eq_pow]
    apply toAdd.injective
    rw [toAdd_prod]
    simp only [toAdd_ofAdd]
    exact (Finset.univ_sum_single (toAdd s)).symm
  rw [hs]
  exact Subgroup.prod_mem _ fun j _ => Subgroup.pow_mem _ (h j) _

omit [Finite K] [CharP K 2] [FiniteDimensional K V] in
theorem commute_of_gen (F : Frame Q 3 A r) {z : V ≃ₗ[K] V} (hz : ∀ j, z * gen F j = gen F j * z)
    {c : V ≃ₗ[K] V} (hc : c ∈ A) : z * c = c * z := by
  obtain ⟨s, rfl⟩ := F.exists_eq hc
  have hH : s ∈ (Subgroup.centralizer ({z} : Set (V ≃ₗ[K] V))).comap F.ι :=
    mem_of_single (fun j => by
      rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff]
      exact (hz j).symm) s
  rw [Subgroup.mem_comap, Subgroup.mem_centralizer_singleton_iff] at hH
  exact hH.symm

theorem exists_plane (hK : Nat.card K = 2) (hQ : (polarBilin Q).Nondegenerate)
    (hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    (hAΩ : A ≤ CFSG.RankThree.Classical2.orthDerived Q) (F : Frame Q 3 A r)
    (hmax : ∀ g ∈ CFSG.RankThree.Classical2.orthDerived Q, g ^ 3 = 1 →
      (∀ c ∈ A, g * c = c * g) → g ∈ A) (i : Fin r) :
    ∃ u ∈ F.U i, Q u = 1 ∧ polar Q u (gen F i u) = 1 ∧
      ∀ x ∈ F.U i, proj Q u (gen F i u) x = x := by
  have hAQ : ∀ a ∈ A, ∀ v, Q (a v) = Q v := fun a ha =>
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
      (CFSG.RankThree.PartOne.KCOrthogonal.orthDerived_le_orthogonalGroup (hAΩ ha))
  obtain ⟨u, hu, hQu0⟩ := exists_Q_ne_zero F i
  have hQu : Q u = 1 := (ChoiceTwo.eq_zero_or_eq_one hK (Q u)).resolve_left hQu0
  set y := gen F i with hydef
  set w := y u with hwdef
  have hyu : y u = w := rfl
  have hyw : y w = u + w := by rw [hwdef, hydef, gen_gen F i hu, add_comm]
  have huw : polar Q u w = 1 := polar_gen F hAQ hu hQu
  have hy : ∀ v, Q (y v) = Q v := hAQ _ (gen_mem_A F i)
  have hy3 : ∀ v, y (y (y v)) = v := gen_gen_gen F i
  have hwU : w ∈ F.U i := gen_mem F i hu
  refine ⟨u, hu, hQu, huw, ?_⟩
  have h3 : ∀ v, rotL Q u w y (rotL Q u w y (rotL Q u w y v)) = v :=
    rotL_three huw hy hyu hyw hy3
  set z : V ≃ₗ[K] V := LinearEquiv.ofLinearMap (rotL Q u w y) (rotL Q u w y ∘ₗ rotL Q u w y)
    (LinearMap.ext fun v => h3 v) (LinearMap.ext fun v => h3 v) with hz
  have hzv : ∀ v, z v = rotL Q u w y v := fun v => rfl
  have hzO : z ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
    TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mpr fun v => Q_rotL huw hy hyu hyw v
  have hz3 : z ^ 3 = 1 := LinearEquiv.ext fun v => by
    simpa [pow_succ, LinearEquiv.mul_apply, hzv] using h3 v
  have hzΩ : z ∈ CFSG.RankThree.Classical2.orthDerived Q :=
    CFSG.RankThree.PartOne.mem_orthDerived_of_pow_eq_one hQ hT (by decide) hzO hz3
  have hprojU : ∀ v, proj Q u w v ∈ F.U i := fun v => by
    rw [proj_apply]
    exact add_mem (Submodule.smul_mem _ _ hu) (Submodule.smul_mem _ _ hwU)
  have hcomm_gen : ∀ j, z * gen F j = gen F j * z := by
    intro j
    refine LinearEquiv.ext fun v => ?_
    rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hzv, hzv]
    by_cases hji : j = i
    · subst hji
      rw [← hydef]
      simp only [rotL_apply, map_add, map_sub, proj_y hy hyu hyw]
    · have hge : ∀ x ∈ F.U i, gen F j x = x := fun x hx => gen_of_mem_ne F (Ne.symm hji) hx
      have hgQ : ∀ v, Q (gen F j v) = Q v := hAQ _ (gen_mem_A F j)
      have hpe : ∀ v, proj Q u w (gen F j v) = proj Q u w v := by
        intro v
        have e1 := polar_map_of_isom hgQ v w
        have e2 := polar_map_of_isom hgQ v u
        rw [hge w hwU] at e1
        rw [hge u hu] at e2
        rw [proj_apply, proj_apply, e1, e2]
      have hep : ∀ v, gen F j (proj Q u w v) = proj Q u w v := fun v => hge _ (hprojU v)
      have hcm : gen F i * gen F j = gen F j * gen F i := by
        unfold gen
        rw [← map_mul F.ι, ← map_mul F.ι, mul_comm]
      have hyc : y (gen F j v) = gen F j (y v) := by
        have := congrArg (fun g : V ≃ₗ[K] V => g v) hcm
        simpa [LinearEquiv.mul_apply] using this
      rw [rotL_apply, rotL_apply, hpe, hyc, hpe, map_add, map_sub, hep, hep]
  have hzc : ∀ c ∈ A, z * c = c * z := fun c hc => commute_of_gen F hcomm_gen hc
  have hzA : z ∈ A := hmax z hzΩ hz3 hzc
  obtain ⟨s₁, hs₁⟩ := F.exists_eq hzA
  have hzu : z u = w := by
    rw [hzv, rotL_apply, proj_u huw, sub_self, zero_add, hyu, proj_w huw]
  have hs₁i : toAdd s₁ i ≠ 0 := by
    intro h0
    have h1 := F.triv s₁ i h0 u hu
    rw [hs₁, hzu] at h1
    have h2 : u = 0 := eq_zero_of_gen_eq F hu h1
    rw [h2, QuadraticMap.map_zero] at hQu
    exact zero_ne_one hQu
  intro x hx
  have hq : x - proj Q u w x ∈ F.U i := sub_mem hx (hprojU x)
  have hp0 : proj Q u w (x - proj Q u w x) = 0 :=
    proj_of_perp (polar_sub_proj_w huw x) (polar_sub_proj_u huw x)
  have hzq : F.ι s₁ (x - proj Q u w x) = x - proj Q u w x := by
    rw [hs₁, hzv, rotL_apply, hp0, proj_y hy hyu hyw, hp0, map_zero, sub_zero, add_zero]
  have := F.fpf s₁ i hs₁i _ hq hzq
  exact (sub_eq_zero.mp this).symm

end Plane

end ChoiceTwoOm

end CFSG.StandardType

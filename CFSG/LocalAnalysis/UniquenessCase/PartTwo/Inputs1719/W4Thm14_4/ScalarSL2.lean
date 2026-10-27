module

public import CFSG.Quasithin.Background.HStandard
import CFSG.Quasithin.Background.HSL3Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.H
open scoped Matrix

theorem exists_sum_statedSL_two_eq_smul_one {K : Type} [Field K] [CharP K 2] {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    ∃ a : Fin 5 → ↥(StatedSL 2 K),
      ∑ i, (((a i : ↥(StatedSL 2 K)) : GL (Fin 2) K) : Matrix (Fin 2) (Fin 2) K) = ω • 1 := by
  have hω3 : ω ^ 3 = 1 := by
    have h : ω ^ 3 - 1 = (ω - 1) * (ω ^ 2 + ω + 1) := by ring
    rw [hω, mul_zero, sub_eq_zero] at h
    exact h
  have hωmul : ω * ω ^ 2 = 1 := by
    rw [← pow_succ']
    exact hω3
  have hω2 : ω ^ 2 = ω + 1 := by
    have h : ω ^ 2 = -(ω + 1) := by linear_combination hω
    rw [h, CharTwo.neg_eq]
  let D : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![ω, 0; 0, ω ^ 2] (by
      rw [Matrix.det_fin_two]
      simp [hωmul])
  have hD : (D : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.det_fin_two]
    simp [hωmul]
  let U : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 1; 0, 1] (by
      rw [Matrix.det_fin_two]; simp)
  have hU : (U : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.det_fin_two]
    simp
  let U' : GL (Fin 2) K :=
    Matrix.GeneralLinearGroup.mkOfDetNeZero !![1, 0; 1, 1] (by
      rw [Matrix.det_fin_two]; simp)
  have hU' : (U' : Matrix (Fin 2) (Fin 2) K).det = 1 := by
    rw [Matrix.GeneralLinearGroup.val_mkOfDetNeZero, Matrix.det_fin_two]
    simp
  refine ⟨![⟨D, CFSG.Open.StatedAPI.mem_statedSL_of_det hD⟩,
    ⟨1, CFSG.Open.StatedAPI.mem_statedSL_of_det (by simp)⟩,
    ⟨U, CFSG.Open.StatedAPI.mem_statedSL_of_det hU⟩,
    ⟨U', CFSG.Open.StatedAPI.mem_statedSL_of_det hU'⟩,
    ⟨U' * U, Subgroup.mul_mem _
      (CFSG.Open.StatedAPI.mem_statedSL_of_det hU')
      (CFSG.Open.StatedAPI.mem_statedSL_of_det hU)⟩], ?_⟩
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Fin.sum_univ_succ, D, U, U',
      Matrix.GeneralLinearGroup.val_mkOfDetNeZero, hω2, CharTwo.add_self_eq_zero, add_assoc]

@[expose] def prodAct {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {Γ : Type} [Group Γ]
    (π : Γ →* ↥L) {n : ℕ} (a : Fin n → Γ) : V →* V where
  toFun v := ∏ i, ((π (a i) : ↥L) : MulAut V) v
  map_one' := by simp
  map_mul' v w := by simp [Finset.prod_mul_distrib]

theorem prodAct_apply {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} {Γ : Type} [Group Γ]
    (π : Γ →* ↥L) {n : ℕ} (a : Fin n → Γ) (v : V) :
    prodAct π a v = ∏ i, ((π (a i) : ↥L) : MulAut V) v := rfl

theorem prodAct_mem_and_toAdd {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} (Γ : Subgroup (GL ι K))
    {J : Subgroup V} {π : ↥Γ →* ↥L} (hJ : ∀ x ∈ L, ∀ u ∈ J, x u ∈ J)
    (e : ↥J ≃* StdMod ι K)
    (he : ∀ (γ : ↥Γ) (u : ↥J) (hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ J),
      e ⟨((π γ : ↥L) : MulAut V) (u : V), hu⟩ = natAct Γ γ (e u))
    {n : ℕ} (a : Fin n → ↥Γ) (u : ↥J) :
    ∃ hu : prodAct π a (u : V) ∈ J, Multiplicative.toAdd (e ⟨prodAct π a (u : V), hu⟩) =
      (∑ i, (((a i : ↥Γ) : GL ι K) : Matrix ι ι K)) *ᵥ Multiplicative.toAdd (e u) := by
  classical
  have hmem : ∀ i, ((π (a i) : ↥L) : MulAut V) (u : V) ∈ J := fun i => hJ _ (π (a i)).2 _ u.2
  set x : Fin n → ↥J := fun i => ⟨((π (a i) : ↥L) : MulAut V) (u : V), hmem i⟩ with hxdef
  have hu : prodAct π a (u : V) ∈ J := by
    rw [prodAct_apply]
    simpa using Subgroup.prod_mem J (fun i _ => hmem i)
  refine ⟨hu, ?_⟩
  have h1 : (⟨prodAct π a (u : V), hu⟩ : ↥J) = ∏ i, x i := by
    apply Subtype.ext
    simp [prodAct_apply, x]
  calc Multiplicative.toAdd (e ⟨prodAct π a (u : V), hu⟩)
      = Multiplicative.toAdd (e (∏ i, x i)) := by rw [h1]
    _ = Multiplicative.toAdd (∏ i, e (x i)) := by rw [map_prod]
    _ = Multiplicative.toAdd (∏ i, natAct Γ (a i) (e u)) := by
          congr 1
          exact Finset.prod_congr rfl fun i _ => he (a i) _ (hmem i)
    _ = ∑ i, Multiplicative.toAdd (natAct Γ (a i) (e u)) := by simp
    _ = ∑ i, (((a i : ↥Γ) : GL ι K) : Matrix ι ι K) *ᵥ Multiplicative.toAdd (e u) := by
          refine Finset.sum_congr rfl fun i _ => ?_
          simp [natAct]
    _ = (∑ i, (((a i : ↥Γ) : GL ι K) : Matrix ι ι K)) *ᵥ Multiplicative.toAdd (e u) := by
          rw [Matrix.sum_mulVec]

private theorem prodAct_eq_smul_of_sum_eq_smul {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (Γ : Subgroup (GL ι K)) {J : Subgroup V} {π : ↥Γ →* ↥L}
    (hJ : ∀ x ∈ L, ∀ u ∈ J, x u ∈ J) (e : ↥J ≃* StdMod ι K)
    (he : ∀ (γ : ↥Γ) (u : ↥J) (hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ J),
      e ⟨((π γ : ↥L) : MulAut V) (u : V), hu⟩ = natAct Γ γ (e u))
    {n : ℕ} (a : Fin n → ↥Γ) {ω : K}
    (ha : ∑ i, (((a i : ↥Γ) : GL ι K) : Matrix ι ι K) = ω • 1) (u : ↥J) :
    ∃ hu : prodAct π a (u : V) ∈ J,
      e ⟨prodAct π a (u : V), hu⟩ = Multiplicative.ofAdd (ω • Multiplicative.toAdd (e u)) := by
  obtain ⟨hu, h⟩ := prodAct_mem_and_toAdd Γ hJ e he a u
  refine ⟨hu, ?_⟩
  apply Multiplicative.toAdd.injective
  rw [h, ha, toAdd_ofAdd, Matrix.smul_mulVec, Matrix.one_mulVec]

private theorem prodAct_mul_self_mul_self_of_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (Γ : Subgroup (GL ι K)) {J : Subgroup V} {π : ↥Γ →* ↥L}
    (hJ : ∀ x ∈ L, ∀ u ∈ J, x u ∈ J) (e : ↥J ≃* StdMod ι K)
    (he : ∀ (γ : ↥Γ) (u : ↥J) (hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ J),
      e ⟨((π γ : ↥L) : MulAut V) (u : V), hu⟩ = natAct Γ γ (e u))
    {n : ℕ} (a : Fin n → ↥Γ) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (ha : ∑ i, (((a i : ↥Γ) : GL ι K) : Matrix ι ι K) = ω • 1) (u : ↥J) :
    prodAct π a (prodAct π a (u : V)) * prodAct π a (u : V) * (u : V) = 1 := by
  obtain ⟨hu1, he1⟩ := prodAct_eq_smul_of_sum_eq_smul Γ hJ e he a ha u
  obtain ⟨hu2, he2⟩ := prodAct_eq_smul_of_sum_eq_smul Γ hJ e he a ha
    (⟨prodAct π a (u : V), hu1⟩ : ↥J)
  have hmem3 : prodAct π a (prodAct π a (u : V)) * prodAct π a (u : V) * (u : V) ∈ J :=
    J.mul_mem (J.mul_mem hu2 hu1) u.2
  have hsub : (⟨_, hmem3⟩ : ↥J) = ⟨prodAct π a (prodAct π a (u : V)), hu2⟩ *
      ⟨prodAct π a (u : V), hu1⟩ * u := by
    apply Subtype.ext
    simp
  have key : e ⟨_, hmem3⟩ = 1 := by
    rw [hsub, map_mul, map_mul, he2, he1]
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_one, toAdd_ofAdd]
    rw [show ω • (ω • Multiplicative.toAdd (e u)) + ω • Multiplicative.toAdd (e u) +
        Multiplicative.toAdd (e u) = (ω ^ 2 + ω + 1) • Multiplicative.toAdd (e u) by
      module, hω, zero_smul]
  have hone : (⟨_, hmem3⟩ : ↥J) = 1 := by
    apply e.injective
    rw [key, map_one]
  simpa using congrArg Subtype.val hone

private theorem prodAct_comm_of_mem {ι : Type} [Fintype ι] [DecidableEq ι]
    {K : Type} [Field K] {V : Type} [CommGroup V] {L : Subgroup (MulAut V)}
    (Γ : Subgroup (GL ι K)) {J : Subgroup V} {π : ↥Γ →* ↥L}
    (hπ : Function.Surjective π) (hJ : ∀ x ∈ L, ∀ u ∈ J, x u ∈ J)
    (e : ↥J ≃* StdMod ι K)
    (he : ∀ (γ : ↥Γ) (u : ↥J) (hu : ((π γ : ↥L) : MulAut V) (u : V) ∈ J),
      e ⟨((π γ : ↥L) : MulAut V) (u : V), hu⟩ = natAct Γ γ (e u))
    {n : ℕ} (a : Fin n → ↥Γ) {ω : K}
    (ha : ∑ i, (((a i : ↥Γ) : GL ι K) : Matrix ι ι K) = ω • 1)
    {x : MulAut V} (hx : x ∈ L) (u : ↥J) :
    prodAct π a (x (u : V)) = x (prodAct π a (u : V)) := by
  obtain ⟨γ, hγ⟩ := hπ ⟨x, hx⟩
  obtain rfl : x = ((π γ : ↥L) : MulAut V) := by
    simpa using (congrArg (fun y : ↥L => (y : MulAut V)) hγ).symm
  obtain ⟨hu1, he1⟩ := prodAct_eq_smul_of_sum_eq_smul Γ hJ e he a ha u
  have hxu : ((π γ : ↥L) : MulAut V) (u : V) ∈ J := hJ _ (π γ).2 _ u.2
  have hxPu : ((π γ : ↥L) : MulAut V) (prodAct π a (u : V)) ∈ J := hJ _ (π γ).2 _ hu1
  obtain ⟨hu2, he2⟩ := prodAct_eq_smul_of_sum_eq_smul Γ hJ e he a ha (⟨_, hxu⟩ : ↥J)
  have hone : (⟨prodAct π a (((π γ : ↥L) : MulAut V) (u : V)), hu2⟩ : ↥J) =
      ⟨((π γ : ↥L) : MulAut V) (prodAct π a (u : V)), hxPu⟩ := by
    apply e.injective
    rw [he2, he γ u hxu, he γ (⟨prodAct π a (u : V), hu1⟩ : ↥J) hxPu, he1]
    apply Multiplicative.toAdd.injective
    simp only [natAct, toAdd_ofAdd, Matrix.mulVec_smul]
  simpa using congrArg Subtype.val hone

theorem prodAct_rel_of_iSup {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]
    {V : Type} [CommGroup V] {L : Subgroup (MulAut V)} (Γ : Subgroup (GL ι K))
    {π : ↥Γ →* ↥L} (hπ : Function.Surjective π) (𝒮 : Set (Subgroup V))
    (hsup : ⨆ J ∈ 𝒮, J = ⊤) (hreal : ∀ J ∈ 𝒮, (FFModel.nat Γ).RealizesVia L J ⊥ π)
    {ω : K} (hω : ω ^ 2 + ω + 1 = 0) {n : ℕ} {a : Fin n → ↥Γ}
    (ha : ∑ i, (((a i : ↥Γ) : GL ι K) : Matrix ι ι K) = ω • 1) :
    (∀ v : V, prodAct π a (prodAct π a v) * prodAct π a v * v = 1) ∧
      ∀ x ∈ L, ∀ v : V, prodAct π a (x v) = x (prodAct π a v) := by
  have hkey : ∀ J ∈ 𝒮, ∀ u : ↥J,
      prodAct π a (prodAct π a (u : V)) * prodAct π a (u : V) * (u : V) = 1 := by
    intro J hJ u
    obtain ⟨e, he⟩ := CFSG.Quasithin.H.SL3Pair.exists_mulEquiv_of_realizesVia_sub Γ (hreal J hJ)
    have hstab : ∀ x ∈ L, ∀ u ∈ J, x u ∈ J :=
      fun x hx u hu => (hreal J hJ).2.2.2.1 ⟨x, hx⟩ u hu
    exact prodAct_mul_self_mul_self_of_mem Γ hstab e he a hω ha u
  have hkey2 : ∀ J ∈ 𝒮, ∀ (x : MulAut V), x ∈ L → ∀ u : ↥J,
      prodAct π a (x (u : V)) = x (prodAct π a (u : V)) := by
    intro J hJ x hx u
    obtain ⟨e, he⟩ := CFSG.Quasithin.H.SL3Pair.exists_mulEquiv_of_realizesVia_sub Γ (hreal J hJ)
    have hstab : ∀ x ∈ L, ∀ u ∈ J, x u ∈ J :=
      fun x hx u hu => (hreal J hJ).2.2.2.1 ⟨x, hx⟩ u hu
    exact prodAct_comm_of_mem Γ hπ hstab e he a ha hx u
  refine ⟨?_, ?_⟩
  · let f : V →* V := (prodAct π a).comp (prodAct π a) * prodAct π a * MonoidHom.id V
    have hf : ∀ v, f v = prodAct π a (prodAct π a v) * prodAct π a v * v := fun v => by
      simp [f]
    have hle : (⨆ J ∈ 𝒮, J) ≤ f.ker := iSup₂_le fun J hJ => by
      intro u hu
      rw [MonoidHom.mem_ker, hf]
      exact hkey J hJ ⟨u, hu⟩
    have htop : f.ker = ⊤ := top_le_iff.mp (hsup ▸ hle)
    intro v
    have hv : f v = 1 := MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top v)
    rwa [hf] at hv
  · intro x hx v
    let g : V →* V := (prodAct π a).comp x.toMonoidHom * (x.toMonoidHom.comp (prodAct π a))⁻¹
    have hg : ∀ v, g v = prodAct π a (x v) * (x (prodAct π a v))⁻¹ := fun v => by
      simp [g]
    have hle : (⨆ J ∈ 𝒮, J) ≤ g.ker := iSup₂_le fun J hJ => by
      intro u hu
      rw [MonoidHom.mem_ker, hg, mul_inv_eq_one]
      exact hkey2 J hJ x hx ⟨u, hu⟩
    have htop : g.ker = ⊤ := top_le_iff.mp (hsup ▸ hle)
    have hv : g v = 1 := MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top v)
    rw [hg] at hv
    exact mul_inv_eq_one.mp hv

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

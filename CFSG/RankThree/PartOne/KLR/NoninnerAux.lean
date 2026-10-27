module

public import CFSG.GroupTheory.LocalCores.FittingNormal
public import CFSG.RankThree.Chevalley.SteinbergBTNoninnerLocalCore
public import CFSG.Open.SignalizerFunctorDefs

public section

namespace CFSG.RankThree.PartOne.KLR

open CFSG.LocalCores CFSG.RankThree.LocalRank CFSG.RankThree.Chevalley

theorem eq_one_of_centralizes_generalizedFitting {C : Type*} [Group C] [Finite C]
    (hS : IsSimpleGroup (CFSG.generalizedFitting C))
    (hnc : ¬ IsMulCommutative (CFSG.generalizedFitting C)) {z : C}
    (hz : ∀ f ∈ CFSG.generalizedFitting C, z * f = f * z) : z = 1 := by
  classical
  have := hS
  have hFn : (CFSG.generalizedFitting C).Normal := generalized_fitting_characteristic.2
  set Z : Subgroup C := Subgroup.centralizer (CFSG.generalizedFitting C : Set C) with hZ
  have hZn : Z.Normal := Subgroup.normal_centralizer
  by_contra hz1
  have hZne : Z ≠ ⊥ := by
    intro h
    have : z ∈ Z := by
      rw [hZ, Subgroup.mem_centralizer_iff]
      intro f hf
      exact (hz f hf).symm
    rw [h, Subgroup.mem_bot] at this
    exact hz1 this
  obtain ⟨N, ⟨hNn, hNne, hNZ⟩, hNmin⟩ :=
    (Set.toFinite {M : Subgroup C | M.Normal ∧ M ≠ ⊥ ∧ M ≤ Z}).exists_minimal
      ⟨Z, hZn, hZne, le_rfl⟩
  have hmin : ∀ M : Subgroup C, M.Normal → M ≤ N → M = ⊥ ∨ M = N := by
    intro M hM hMN
    by_cases hM1 : M = ⊥
    · exact Or.inl hM1
    · exact Or.inr (le_antisymm hMN (hNmin ⟨hM, hM1, hMN.trans hNZ⟩ hMN))
  have hNF : N ≤ CFSG.generalizedFitting C :=
    generalized_fitting_minimal_normal.1 N hNn hNne hmin
  obtain ⟨n, hnN, hn1⟩ : ∃ n ∈ N, n ≠ 1 := by
    by_contra h
    push Not at h
    exact hNne (eq_bot_iff.2 fun n hn => Subgroup.mem_bot.2 (h n hn))
  have hnZ : n ∈ Z := hNZ hnN
  have hnF : n ∈ CFSG.generalizedFitting C := hNF hnN
  have hcen : (⟨n, hnF⟩ : CFSG.generalizedFitting C) ∈
      Subgroup.center (CFSG.generalizedFitting C) := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := Subgroup.mem_centralizer_iff.1 hnZ g g.2
    exact Subtype.ext this
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    (Subgroup.center (CFSG.generalizedFitting C)) with h | h
  · rw [h, Subgroup.mem_bot] at hcen
    exact hn1 (congrArg Subtype.val hcen)
  · apply hnc
    refine ⟨⟨fun x y => ?_⟩⟩
    have hx : x ∈ Subgroup.center (CFSG.generalizedFitting C) := by rw [h]; trivial
    exact (Subgroup.mem_center_iff.1 hx y).symm

section Fixed

variable {Γ : Type*} [Group Γ] [Finite Γ] (δ : MulAut Γ)

open CFSG.Open

@[expose] noncomputable def fixedFStar : Subgroup Γ :=
  (CFSG.generalizedFitting ↥(signalizerFixedSubgroup δ)).map (signalizerFixedSubgroup δ).subtype

variable {δ}

omit [Finite Γ] in
theorem fixedFStar_le_fixed : fixedFStar δ ≤ signalizerFixedSubgroup δ :=
  Subgroup.map_subtype_le _

omit [Finite Γ] in
theorem map_mem_fixed_of_commute {u : MulAut Γ} (hu : u * δ = δ * u) {c : Γ}
    (hc : c ∈ signalizerFixedSubgroup δ) : u c ∈ signalizerFixedSubgroup δ := by
  show δ (u c) = u c
  have h1 := congrArg (fun w : MulAut Γ => w c) hu
  simp only [MulAut.mul_apply] at h1
  have h2 : δ c = c := hc
  rw [h2] at h1
  exact h1.symm

omit [Finite Γ] in
theorem map_mem_fixedFStar {u : MulAut Γ} (hu : u * δ = δ * u) {f : Γ}
    (hf : f ∈ fixedFStar δ) : u f ∈ fixedFStar δ := by
  classical
  obtain ⟨c, hc, rfl⟩ := hf
  have hu' : u⁻¹ * δ = δ * u⁻¹ := (Commute.inv_left (show Commute u δ from hu)).eq
  have hmapeq : (signalizerFixedSubgroup δ).map (u : Γ ≃* Γ).toMonoidHom =
      signalizerFixedSubgroup δ := by
    refine le_antisymm ?_ ?_
    · rintro _ ⟨y, hy, rfl⟩
      exact map_mem_fixed_of_commute hu hy
    · intro y hy
      exact ⟨u⁻¹ y, map_mem_fixed_of_commute hu' hy, by simp⟩
  let φ : MulAut ↥(signalizerFixedSubgroup δ) :=
    (MulEquiv.subgroupMap (u : Γ ≃* Γ) (signalizerFixedSubgroup δ)).trans
      (MulEquiv.subgroupCongr hmapeq)
  have hφ : (CFSG.generalizedFitting ↥(signalizerFixedSubgroup δ)).map φ.toMonoidHom =
      CFSG.generalizedFitting ↥(signalizerFixedSubgroup δ) :=
    Subgroup.characteristic_iff_map_eq.mp generalized_fitting_characteristic.1 φ
  have hmem : φ c ∈ CFSG.generalizedFitting ↥(signalizerFixedSubgroup δ) := by
    rw [← hφ]
    exact ⟨c, hc, rfl⟩
  exact ⟨φ c, hmem, rfl⟩

end Fixed

section Stabilizer

open CFSG.Open

theorem mulAut_mul_conj_mul_inv_aux {Γ : Type*} [Group Γ] (s : MulAut Γ) (y : Γ) :
    s * MulAut.conj y * s⁻¹ = MulAut.conj (s y) :=
  MulEquiv.ext fun u => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem mem_zpowers_of_fixes_fstar {Γ A : Type*} [Group Γ] [Finite Γ] [Group A]
    (hZ : Subgroup.center Γ = ⊥) (hA : ∀ u v : A, u * v = v * u) (φ : A →* MulAut Γ)
    (hNF : ∀ α : MulAut Γ, ∃ (x : Γ) (τ : A), α = MulAut.conj x * φ τ) (σ : A)
    (hS : IsSimpleGroup (CFSG.generalizedFitting ↥(signalizerFixedSubgroup (φ σ))))
    (hnc : ¬ IsMulCommutative (CFSG.generalizedFitting ↥(signalizerFixedSubgroup (φ σ))))
    (hres : ∀ (x : Γ) (τ : A), x ∈ signalizerFixedSubgroup (φ σ) →
      (∀ j ∈ signalizerFixedSubgroup (φ σ), x * φ τ j * x⁻¹ = j) → τ ∈ Subgroup.zpowers σ)
    {u : MulAut Γ} (hu : u * φ σ = φ σ * u) (hfix : ∀ f ∈ fixedFStar (φ σ), u f = f) :
    u ∈ Subgroup.zpowers (φ σ) := by
  classical
  have hconjinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) := by
    intro g g' e
    have hc : g'⁻¹ * g ∈ Subgroup.center Γ := Subgroup.mem_center_iff.2 fun x => by
      have h1 := congrArg (fun α : MulAut Γ => α x) e
      simp only [MulAut.conj_apply] at h1
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
        _ = g'⁻¹ * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  obtain ⟨y, τ, huyτ⟩ := hNF u
  have hcomm : φ τ * φ σ = φ σ * φ τ := by rw [← map_mul, ← map_mul, hA]
  have hyδ : φ σ y = y := by
    have h3 : MulAut.conj y * φ σ = φ σ * MulAut.conj y := by
      have h4 : MulAut.conj y * φ σ * φ τ = φ σ * MulAut.conj y * φ τ := by
        have := hu
        rw [huyτ] at this
        calc MulAut.conj y * φ σ * φ τ = MulAut.conj y * (φ σ * φ τ) := by rw [mul_assoc]
          _ = MulAut.conj y * (φ τ * φ σ) := by rw [hcomm]
          _ = MulAut.conj y * φ τ * φ σ := by rw [mul_assoc]
          _ = φ σ * (MulAut.conj y * φ τ) := this
          _ = φ σ * MulAut.conj y * φ τ := by rw [mul_assoc]
      exact mul_right_cancel h4
    have h5 := mulAut_mul_conj_mul_inv_aux (φ σ) y
    rw [← h3, mul_inv_cancel_right] at h5
    exact hconjinj h5.symm
  have hyC : y ∈ signalizerFixedSubgroup (φ σ) := hyδ
  have huC : ∀ j ∈ signalizerFixedSubgroup (φ σ), u j = j := by
    intro j hj
    have hjC : (⟨j, hj⟩ : ↥(signalizerFixedSubgroup (φ σ))) ∈
        (signalizerFixedSubgroup (φ σ)).subgroupOf (signalizerFixedSubgroup (φ σ)) := hj
    set z : ↥(signalizerFixedSubgroup (φ σ)) :=
      (⟨j, hj⟩ : ↥(signalizerFixedSubgroup (φ σ)))⁻¹ *
        ⟨u j, map_mem_fixed_of_commute hu hj⟩ with hz
    have hz1 : z = 1 := by
      refine eq_one_of_centralizes_generalizedFitting hS hnc fun f hf => ?_
      apply Subtype.ext
      have hfΓ : (f : Γ) ∈ fixedFStar (φ σ) := ⟨f, hf, rfl⟩
      have hnorm := (generalized_fitting_characteristic.2 :
        (CFSG.generalizedFitting ↥(signalizerFixedSubgroup (φ σ))).Normal).conj_mem f hf ⟨j, hj⟩
      have hjf : j * (f : Γ) * j⁻¹ ∈ fixedFStar (φ σ) := ⟨_, hnorm, rfl⟩
      have h1 := hfix _ hjf
      rw [map_mul, map_mul, map_inv, hfix _ hfΓ] at h1
      change j⁻¹ * u j * (f : Γ) = (f : Γ) * (j⁻¹ * u j)
      calc j⁻¹ * u j * (f : Γ) = j⁻¹ * (u j * (f : Γ) * (u j)⁻¹) * u j := by group
        _ = j⁻¹ * (j * (f : Γ) * j⁻¹) * u j := by rw [h1]
        _ = (f : Γ) * (j⁻¹ * u j) := by group
    have := congrArg Subtype.val hz1
    change j⁻¹ * u j = 1 at this
    exact (inv_injective (mul_eq_one_iff_eq_inv.1 this)).symm
  have hfixτ : ∀ j ∈ signalizerFixedSubgroup (φ σ), y * φ τ j * y⁻¹ = j := by
    intro j hj
    have := huC j hj
    rw [huyτ, MulAut.mul_apply, MulAut.conj_apply] at this
    exact this
  have hτ : τ ∈ Subgroup.zpowers σ := hres y τ hyC hfixτ
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.1 hτ
  have hφτ : φ τ = φ σ ^ n := by rw [← hn, map_zpow]
  have hτC : ∀ j ∈ signalizerFixedSubgroup (φ σ), φ τ j = j := by
    intro j hj
    have hstab : φ σ ∈ MulAction.stabilizer (MulAut Γ) j := by
      rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]
      exact hj
    have := zpow_mem hstab n
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at this
    rw [hφτ]
    exact this
  have hy1 : y = 1 := by
    have h1 : (⟨y, hyC⟩ : ↥(signalizerFixedSubgroup (φ σ))) = 1 := by
      refine eq_one_of_centralizes_generalizedFitting hS hnc fun f hf => ?_
      apply Subtype.ext
      have := hfixτ f f.2
      rw [hτC f f.2] at this
      change y * (f : Γ) = (f : Γ) * y
      calc y * (f : Γ) = y * (f : Γ) * y⁻¹ * y := by group
        _ = (f : Γ) * y := by rw [this]
    exact congrArg Subtype.val h1
  rw [huyτ, hy1, map_one, one_mul, hφτ]
  exact Subgroup.zpow_mem_zpowers _ n

theorem aschbacherSolvableCore_eq_bot_of_fieldActor {Γ A : Type*} [Group Γ] [Finite Γ] [Group A]
    {p : ℕ} (hp : p.Prime) (hZ : Subgroup.center Γ = ⊥) (hA : ∀ u v : A, u * v = v * u)
    (φ : A →* MulAut Γ) (hNF : ∀ α : MulAut Γ, ∃ (x : Γ) (τ : A), α = MulAut.conj x * φ τ)
    (σ : A)
    (hS : IsSimpleGroup (CFSG.generalizedFitting ↥(signalizerFixedSubgroup (φ σ))))
    (hnc : ¬ IsMulCommutative (CFSG.generalizedFitting ↥(signalizerFixedSubgroup (φ σ))))
    (hres : ∀ (x : Γ) (τ : A), x ∈ signalizerFixedSubgroup (φ σ) →
      (∀ j ∈ signalizerFixedSubgroup (φ σ), x * φ τ j * x⁻¹ = j) → τ ∈ Subgroup.zpowers σ)
    {B : Subgroup (MulAut Γ)} (hB : (MulAut.conj : Γ →* MulAut Γ).range ≤ B) (α : B) (g : Γ)
    (hg : (α : MulAut Γ) = MulAut.conj g * φ σ * (MulAut.conj g)⁻¹) (hαp : orderOf α = p) :
    aschbacherSolvableCore p (Subgroup.centralizer {α} : Subgroup B) = ⊥ := by
  classical
  have hconjinj : Function.Injective (MulAut.conj : Γ →* MulAut Γ) := by
    intro g g' e
    have hc : g'⁻¹ * g ∈ Subgroup.center Γ := Subgroup.mem_center_iff.2 fun x => by
      have h1 := congrArg (fun α : MulAut Γ => α x) e
      simp only [MulAut.conj_apply] at h1
      calc x * (g'⁻¹ * g) = g'⁻¹ * (g' * x * g'⁻¹) * g := by group
        _ = g'⁻¹ * (g * x * g⁻¹) * g := by rw [h1]
        _ = g'⁻¹ * g * x := by group
    rw [hZ, Subgroup.mem_bot] at hc
    exact (inv_mul_eq_one.1 hc).symm
  have hconjδ : ∀ f : Γ, φ σ f = f → MulAut.conj f * φ σ = φ σ * MulAut.conj f := by
    intro f hf
    have h := mulAut_mul_conj_mul_inv_aux (φ σ) f
    rw [hf] at h
    exact (mul_inv_eq_iff_eq_mul.1 h).symm
  have hNa : (fixedFStar (φ σ)).map (MulAut.conj : Γ →* MulAut Γ) ≤
      Subgroup.centralizer ({φ σ} : Set (MulAut Γ)) := by
    rintro _ ⟨f, hf, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2 (hconjδ f (fixedFStar_le_fixed hf))
  have hNnormal : (((fixedFStar (φ σ)).map (MulAut.conj : Γ →* MulAut Γ)).subgroupOf
      (Subgroup.centralizer ({φ σ} : Set (MulAut Γ)))).Normal := by
    refine ⟨fun n hn u => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    obtain ⟨f, hf, hfn⟩ := hn
    have huδ : (u : MulAut Γ) * φ σ = φ σ * u := Subgroup.mem_centralizer_singleton_iff.1 u.2
    refine ⟨(u : MulAut Γ) f, map_mem_fixedFStar huδ hf, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [← hfn]
    exact (mulAut_mul_conj_mul_inv_aux (u : MulAut Γ) f).symm
  have : IsSimpleGroup (CFSG.generalizedFitting ↥(signalizerFixedSubgroup (φ σ))) := hS
  let eN : ↥(CFSG.generalizedFitting ↥(signalizerFixedSubgroup (φ σ))) ≃*
      ↥((fixedFStar (φ σ)).map (MulAut.conj : Γ →* MulAut Γ)) :=
    (Subgroup.equivMapOfInjective _ (signalizerFixedSubgroup (φ σ)).subtype
      (signalizerFixedSubgroup (φ σ)).subtype_injective).trans
      (Subgroup.equivMapOfInjective (fixedFStar (φ σ)) (MulAut.conj : Γ →* MulAut Γ) hconjinj)
  have hsimple : IsSimpleGroup ↥((fixedFStar (φ σ)).map (MulAut.conj : Γ →* MulAut Γ)) :=
    eN.symm.isSimpleGroup
  have hncN : ¬ ∀ x y : ↥((fixedFStar (φ σ)).map (MulAut.conj : Γ →* MulAut Γ)),
      x * y = y * x := by
    intro h
    apply hnc
    refine ⟨⟨fun x y => ?_⟩⟩
    apply eN.injective
    rw [map_mul, map_mul]
    exact h _ _
  have hδα : (MulAut.conj g)⁻¹ * (α : MulAut Γ) * ((MulAut.conj g)⁻¹)⁻¹ = φ σ := by
    rw [hg]
    group
  have hNB : ∀ n ∈ (fixedFStar (φ σ)).map (MulAut.conj : Γ →* MulAut Γ),
      ((MulAut.conj g)⁻¹)⁻¹ * n * (MulAut.conj g)⁻¹ ∈ B := by
    intro n hn
    obtain ⟨f, -, rfl⟩ := hn
    have h1 : MulAut.conj g ∈ B := hB ⟨g, rfl⟩
    have h2 : MulAut.conj f ∈ B := hB ⟨f, rfl⟩
    rw [inv_inv]
    exact B.mul_mem (B.mul_mem h1 h2) (B.inv_mem h1)
  have hcent : Subgroup.centralizer ({φ σ} : Set (MulAut Γ)) ⊓
      Subgroup.centralizer (((fixedFStar (φ σ)).map (MulAut.conj : Γ →* MulAut Γ) :
        Subgroup (MulAut Γ)) : Set (MulAut Γ)) ≤ Subgroup.zpowers (φ σ) := by
    intro u hu
    obtain ⟨hu1, hu2⟩ := Subgroup.mem_inf.1 hu
    refine mem_zpowers_of_fixes_fstar hZ hA φ hNF σ hS hnc hres
      (Subgroup.mem_centralizer_singleton_iff.1 hu1) fun f hf => ?_
    have h1 := Subgroup.mem_centralizer_iff.1 hu2 (MulAut.conj f) ⟨f, hf, rfl⟩
    have h2 : u * MulAut.conj f * u⁻¹ = MulAut.conj f := by
      calc u * MulAut.conj f * u⁻¹ = (MulAut.conj f * u) * u⁻¹ := by rw [h1]
        _ = MulAut.conj f := by group
    rw [mulAut_mul_conj_mul_inv_aux] at h2
    exact hconjinj h2
  exact aschbacherSolvableCore_centralizer_eq_bot_of_conj hp α hαp (MulAut.conj g)⁻¹ _ hNB
    (by rw [hδα]; exact hNa) (by rw [hδα]; exact hNnormal) hsimple hncN
    (by rw [hδα]; exact hcent)

end Stabilizer

end CFSG.RankThree.PartOne.KLR

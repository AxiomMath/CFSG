module

public import CFSG.RankThree.Lattice.SteinbergBIE6EvenRoots
public import CFSG.LieType.AlgebraicGroups.ToralTwistSemilinearDatum
public import CFSG.RankThree.Chevalley.EvenPinnedRootSL2
public import CFSG.RankThree.Lattice.SteinbergBIGenFixedRootData

public noncomputable section

namespace CFSG.RankThree.Lattice

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.RankThree.E6 CFSG.LieType.AlgebraicGroups

open _root_.Classical in
@[expose] def supportChar (S : Set (Fin Tag.E6.rank)) :
    Multiplicative (Fin Tag.E6.rank → ℤ) →* Multiplicative (Fin Tag.E6.rank → ℤ) where
  toFun x := Multiplicative.ofAdd fun i => if i ∈ S then 0 else Multiplicative.toAdd x i
  map_one' := by
    rw [ofAdd_eq_one]
    funext i
    split_ifs <;> rfl
  map_mul' x y := by
    rw [← ofAdd_add]
    congr 1
    funext i
    simp only [toAdd_mul, Pi.add_apply]
    split_ifs <;> simp

theorem supportChar_eq_one_iff (S : Set (Fin Tag.E6.rank)) (α : Fin Tag.E6.rank → ℤ) :
    supportChar S (Multiplicative.ofAdd α) = 1 ↔ ∀ i ∉ S, α i = 0 := by
  classical
  change Multiplicative.ofAdd _ = 1 ↔ _
  rw [ofAdd_eq_one, funext_iff]
  refine forall_congr' fun i => ?_
  by_cases hi : i ∈ S <;> simp [hi]

theorem kernelRoots_supportChar (S : Set (Fin Tag.E6.rank)) :
    kernelRoots (supportChar S) = parabolicRoots Tag.E6 S := by
  ext α
  exact and_congr_right' (supportChar_eq_one_iff S α)

theorem iform_single_left_eq (j : Fin Tag.E6.rank) (α : Fin Tag.E6.rank → ℤ) :
    iform (Pi.single j 1) α = ∑ k, Tag.E6.symmetrizedCartan j k * α k := by
  rw [iform, Finset.sum_eq_single j]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

theorem iform_self_eq_sum (α : Fin Tag.E6.rank → ℤ) :
    iform α α = ∑ j, α j * iform (Pi.single j 1) α := by
  rw [iform]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [iform_single_left_eq, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem exists_iform_single_ne_zero {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ∃ j, α j ≠ 0 ∧ iform (Pi.single j 1) α ≠ 0 := by
  by_contra h
  push Not at h
  have e := iform_self_eq_sum α
  rw [iform_self_E6 hα, Finset.sum_eq_zero fun j _ => by
    by_cases hj : α j = 0
    · rw [hj, zero_mul]
    · rw [h j hj, mul_zero]] at e
  omega

namespace E6EvenFixedRootDatum

variable {Ω : Type} [Field Ω] [CharP Ω 2] [IsAlgClosed Ω] (D : E6EvenFixedRootDatum Ω)

@[expose] def chi :
    Multiplicative (Fin Tag.E6.rank → ℤ) →* Multiplicative (Fin Tag.E6.rank → ℤ) :=
  supportChar D.support

theorem kernelRoots_chi : kernelRoots D.chi = D.Ξ := by
  rw [chi, kernelRoots_supportChar, D.Ξ_eq_parabolicRoots]

@[expose] def deltaHom : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) :=
  AddMonoidHom.mk' D.δ D.δ_add

@[expose] def theta : (Fin Tag.E6.rank → ℝ) →ₗ[ℝ] (Fin Tag.E6.rank → ℝ) :=
  latticeRealExt D.deltaHom

theorem theta_toReal (v : Fin Tag.E6.rank → ℤ) : D.theta (toReal v) = toReal (D.δ v) :=
  latticeRealExt_toReal _ v

theorem theta_pow_toReal (m : ℕ) (v : Fin Tag.E6.rank → ℤ) :
    (D.theta ^ m) (toReal v) = toReal (D.δ^[m] v) :=
  latticeRealExt_pow_toReal _ m v

theorem δ_injective : Function.Injective D.δ := fun x y h => by
  rw [← D.δ_δ x, h, D.δ_δ]

theorem iterate_δ (m : ℕ) (x : Fin Tag.E6.rank → ℤ) : D.δ^[m] x = x ∨ D.δ^[m] x = D.δ x := by
  induction m with
  | zero => exact Or.inl rfl
  | succ m ih =>
    rw [Function.iterate_succ_apply']
    rcases ih with h | h
    · rw [h]
      exact Or.inr rfl
    · rw [h, D.δ_δ]
      exact Or.inl rfl

theorem thetaOrbit_eq_iterate (α : Fin Tag.E6.rank → ℤ) :
    thetaOrbit D.theta α = {β | ∃ k : ℕ, β = D.δ^[k] α} := by
  ext β
  simp only [thetaOrbit, Set.mem_ofPred_eq, D.theta_pow_toReal]
  exact exists_congr fun m => ⟨fun h => (toReal_injective h).symm, fun h => by rw [h]⟩

theorem thetaOrbit_eq (α : Fin Tag.E6.rank → ℤ) : thetaOrbit D.theta α = {α, D.δ α} := by
  rw [thetaOrbit_eq_iterate]
  ext β
  simp only [Set.mem_ofPred_eq, Set.mem_insert_iff, Set.mem_singleton_iff]
  constructor
  · rintro ⟨m, rfl⟩
    exact D.iterate_δ m α
  · rintro (rfl | rfl)
    · exact ⟨0, rfl⟩
    · exact ⟨1, rfl⟩

theorem simpleOrbit_eq_thetaOrbit (j : Fin Tag.E6.rank) :
    D.simpleOrbit j = thetaOrbit D.theta (Pi.single j 1) := by
  rw [thetaOrbit_eq_iterate]
  rfl

theorem image_δ_Ξ : D.δ '' D.Ξ = D.Ξ := by
  refine Set.Subset.antisymm ?_ fun α hα => ⟨D.δ α, D.δ_mem_Ξ hα, D.δ_δ α⟩
  rintro _ ⟨α, hα, rfl⟩
  exact D.δ_mem_Ξ hα

theorem single_mem_kernelRoots {j : Fin Tag.E6.rank} (hj : j ∈ D.support) :
    Pi.single j 1 ∈ kernelRoots D.chi := by
  rw [D.kernelRoots_chi]
  exact hj

theorem mem_support_of_ne_zero {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ D.Ξ) {j : Fin Tag.E6.rank}
    (hj : α j ≠ 0) : j ∈ D.support := by
  rw [D.Ξ_eq_parabolicRoots] at hα
  by_contra h
  exact hj (hα.2 j h)

theorem mem_support_iff_component {j : Fin Tag.E6.rank} :
    j ∈ D.support ↔ j ∈ e6JComponent (e6QpSupport D.qpIndex) D.i₀ ∨
      j ∈ e6JComponent (e6QpSupport D.qpIndex) (e6QpPerm D.qpIndex D.i₀) := by
  change Pi.single j 1 ∈ D.Ξ ↔ _
  rw [D.Ξ_eq, e6Xi_eq D.qpIndex D.i₀_mem', Set.mem_union, single_mem_parabolicRoots_iff,
    single_mem_parabolicRoots_iff]

theorem mem_unionSimpleRoots_iff {β : Fin Tag.E6.rank → ℤ} :
    β ∈ unionSimpleRoots D.chi Set.univ ↔ ∃ j ∈ D.support, β = Pi.single j 1 := by
  constructor
  · rintro ⟨i, -, hβ⟩
    obtain ⟨hβr, ⟨⟨hβK, hβc⟩, hβpos⟩, hβmin⟩ := mem_simpleRoots.1 hβ
    by_cases h1 : height β = 1
    · obtain ⟨j, rfl⟩ := eq_single_of_height_eq_one hβr h1
      refine ⟨j, ?_, rfl⟩
      rw [mem_support_iff, ← D.kernelRoots_chi]
      exact hβK
    · exfalso
      obtain ⟨j, hγ⟩ := exists_root_sub_single hβr (by omega)
      set γ := β - Pi.single j 1 with hγdef
      have hβγ : β = γ + Pi.single j 1 := by rw [hγdef, sub_add_cancel]
      have hγpos : 0 < height γ := by
        rw [hγdef, height_sub, height_single]
        omega
      have hγj : iform γ (Pi.single j 1) = -1 := by
        have e := iform_self_E6 hβr
        rw [hβγ, iform_add_left, iform_add_right, iform_add_right, iform_self_E6 hγ,
          iform_comm (Pi.single j 1) γ, show iform (Pi.single j 1 : Fin Tag.E6.rank → ℤ)
            (Pi.single j 1) = 2 from iform_self_E6 (isRoot_single Tag.E6 j)] at e
        omega
      have hβΞ : β ∈ D.Ξ := D.kernelRoots_chi ▸ hβK
      have hjβ : β j ≠ 0 := by
        have e : β j = γ j + 1 := by rw [hβγ]; simp
        have hnn := (IsRoot.height_pos_iff hγ).1 hγpos j
        omega
      have hjS := D.mem_support_of_ne_zero hβΞ hjβ
      have hjK := D.single_mem_kernelRoots hjS
      have hγK : γ ∈ kernelRoots D.chi := by
        rw [D.kernelRoots_chi, D.Ξ_eq_parabolicRoots]
        refine ⟨hγ, fun i hi => ?_⟩
        have hij : i ≠ j := fun e => hi (e ▸ hjS)
        have hβi : β i = 0 := by
          rw [D.Ξ_eq_parabolicRoots] at hβΞ
          exact hβΞ.2 i hi
        rw [hγdef, Pi.sub_apply, hβi, Pi.single_apply,
          ite_eq_right_iff.2 (fun h => absurd h hij), sub_zero]
      have hγc : (⟦⟨γ, hγK⟩⟧ : KernelComponent D.chi) = i := by
        refine (mk_eq_of_iform_ne_zero (β := ⟨β, hβK⟩) ?_).trans hβc
        change iform γ β ≠ 0
        rw [hβγ, iform_add_right, iform_self_E6 hγ, hγj]
        omega
      have hjc : (⟦⟨Pi.single j 1, hjK⟩⟧ : KernelComponent D.chi) = i := by
        refine (mk_eq_of_iform_ne_zero (β := ⟨β, hβK⟩) ?_).trans hβc
        change iform (Pi.single j 1) β ≠ 0
        rw [hβγ, iform_add_right, iform_comm, hγj, show iform (Pi.single j 1 : Fin Tag.E6.rank → ℤ)
          (Pi.single j 1) = 2 from iform_self_E6 (isRoot_single Tag.E6 j)]
        omega
      exact hβmin γ ⟨⟨hγK, hγc⟩, hγpos⟩ (Pi.single j 1) ⟨⟨hjK, hjc⟩, by rw [height_single]; omega⟩
        hβγ
  · rintro ⟨j, hj, rfl⟩
    have hjK := D.single_mem_kernelRoots hj
    refine ⟨⟦⟨_, hjK⟩⟧, Set.mem_univ _, mem_simpleRoots.2 ⟨isRoot_single _ _,
      ⟨⟨hjK, rfl⟩, by rw [height_single]; omega⟩, ?_⟩⟩
    rintro γ ⟨-, hγ⟩ δ' ⟨-, hδ⟩ e
    have h := congrArg height e
    rw [height_add, height_single] at h
    omega

theorem image_δ_unionSimpleRoots :
    D.deltaHom '' unionSimpleRoots D.chi Set.univ = unionSimpleRoots D.chi Set.univ := by
  ext β
  simp only [Set.mem_image, D.mem_unionSimpleRoots_iff]
  constructor
  · rintro ⟨_, ⟨j, hj, rfl⟩, rfl⟩
    exact ⟨_, D.perm_mem_support hj, D.δ_single hj⟩
  · rintro ⟨j, hj, rfl⟩
    refine ⟨_, ⟨_, D.perm_mem_support hj, rfl⟩, ?_⟩
    change D.δ _ = _
    rw [← D.δ_single hj, D.δ_δ]

theorem exists_single_mk_eq {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ kernelRoots D.chi) :
    ∃ j ∈ D.support, ∃ hj : Pi.single j 1 ∈ kernelRoots D.chi,
      (⟦⟨α, hα⟩⟧ : KernelComponent D.chi) = ⟦⟨Pi.single j 1, hj⟩⟧ := by
  obtain ⟨j, hj, hne⟩ := exists_iform_single_ne_zero hα.1
  have hjS := D.mem_support_of_ne_zero (D.kernelRoots_chi ▸ hα) hj
  exact ⟨j, hjS, D.single_mem_kernelRoots hjS, mk_eq_of_iform_ne_zero (by
    change iform α (Pi.single j 1) ≠ 0
    rw [iform_comm]
    exact hne)⟩

theorem mk_single_eq_of_reflTransGen {a b : Fin Tag.E6.rank}
    (hab : Relation.ReflTransGen (e6JAdj (e6QpSupport D.qpIndex)) a b)
    (hsub : ∀ c, Relation.ReflTransGen (e6JAdj (e6QpSupport D.qpIndex)) a c → c ∈ D.support)
    (ha : Pi.single a 1 ∈ kernelRoots D.chi) :
    ∀ hb : Pi.single b 1 ∈ kernelRoots D.chi,
      (⟦⟨Pi.single a 1, ha⟩⟧ : KernelComponent D.chi) = ⟦⟨Pi.single b 1, hb⟩⟧ := by
  induction hab with
  | refl => exact fun _ => rfl
  | tail hac hcd ih =>
    intro hd
    refine (ih (D.single_mem_kernelRoots (hsub _ hac))).trans (mk_eq_of_iform_ne_zero ?_)
    change iform (Pi.single _ 1) (Pi.single _ 1) ≠ 0
    rw [iform_single_single_E6']
    exact hcd.2.2.2

theorem isThetaOrbit_univ : ∃ i₀ : KernelComponent D.chi,
    (Set.univ : Set (KernelComponent D.chi)) = {i | ∃ m : ℕ, ∃ α ∈ componentRoots D.chi i₀,
      ∃ β ∈ componentRoots D.chi i, (D.theta ^ m) (toReal α) = toReal β} := by
  have hC : ∀ c, Relation.ReflTransGen (e6JAdj (e6QpSupport D.qpIndex)) D.i₀ c →
      c ∈ D.support := fun c h => D.mem_support_iff_component.2 (Or.inl h)
  have hC' : ∀ c, Relation.ReflTransGen (e6JAdj (e6QpSupport D.qpIndex))
      (e6QpPerm D.qpIndex D.i₀) c → c ∈ D.support :=
    fun c h => D.mem_support_iff_component.2 (Or.inr h)
  have hi₀S : D.i₀ ∈ D.support := hC _ Relation.ReflTransGen.refl
  have hπS : e6QpPerm D.qpIndex D.i₀ ∈ D.support := hC' _ Relation.ReflTransGen.refl
  have hi₀K := D.single_mem_kernelRoots hi₀S
  have hπK := D.single_mem_kernelRoots hπS
  refine ⟨⟦⟨_, hi₀K⟩⟧, (Set.eq_univ_of_forall fun i => ?_).symm⟩
  obtain ⟨⟨γ, hγ⟩, rfl⟩ := Quotient.exists_rep i
  obtain ⟨j, hjS, hjK, hγj⟩ := D.exists_single_mk_eq hγ
  rcases D.mem_support_iff_component.1 hjS with hj | hj
  · have e := (D.mk_single_eq_of_reflTransGen hj hC hi₀K hjK).trans hγj.symm
    exact ⟨0, _, ⟨hi₀K, rfl⟩, _, ⟨hi₀K, e⟩, by rw [pow_zero, Module.End.one_apply]⟩
  · have e := (D.mk_single_eq_of_reflTransGen hj hC' hπK hjK).trans hγj.symm
    exact ⟨1, _, ⟨hi₀K, rfl⟩, _, ⟨hπK, e⟩, by rw [pow_one, D.theta_toReal, D.δ_single hi₀S]⟩

theorem orbit_orthogonal' {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ kernelRoots D.chi)
    {β γ : Fin Tag.E6.rank → ℤ} (hβ : β ∈ thetaOrbit D.theta α) (hγ : γ ∈ thetaOrbit D.theta α)
    (hne : β ≠ γ) : iform β γ = 0 := by
  have hαΞ : α ∈ D.Ξ := D.kernelRoots_chi ▸ hα
  rw [thetaOrbit_eq] at hβ hγ
  rcases hβ with rfl | rfl <;> rcases hγ with rfl | rfl
  · exact absurd rfl hne
  · exact D.iform_δ_eq_zero hαΞ (Ne.symm hne)
  · rw [iform_comm]
    exact D.iform_δ_eq_zero hαΞ hne
  · exact absurd rfl hne

theorem orbit_reflection' {α : Fin Tag.E6.rank → ℤ} (hα : α ∈ kernelRoots D.chi) :
    ∃ w ∈ Subgroup.closure ((fun β => setReflection (thetaOrbit D.theta β)) ''
      unionSimpleRoots D.chi Set.univ),
      ∃ β ∈ unionSimpleRoots D.chi Set.univ,
        (fun γ => w • γ) '' thetaOrbit D.theta α = thetaOrbit D.theta β := by
  have hαΞ : α ∈ e6Xi (e6QpSupport D.qpIndex) D.i₀ := by
    rw [← D.Ξ_eq, ← D.kernelRoots_chi]
    exact hα
  obtain ⟨w, hw, O, hO, hwO⟩ := exists_smul_e6Orbit_eq D.qpIndex D.i₀_mem' D.orth hαΞ
  obtain ⟨j, hj, rfl⟩ := hO
  have hjS : j ∈ D.support := by
    rw [mem_support_iff, D.Ξ_eq]
    exact hj
  have hjΔ : Pi.single j 1 ∈ unionSimpleRoots D.chi Set.univ :=
    D.mem_unionSimpleRoots_iff.2 ⟨j, hjS, rfl⟩
  have hsimple : ∀ i, Pi.single i 1 ∈ e6Xi (e6QpSupport D.qpIndex) D.i₀ →
      e6SimpleOrbit (e6QpSupport D.qpIndex) i = thetaOrbit D.theta (Pi.single i 1) := by
    intro i _
    rw [thetaOrbit_eq_iterate, D.δ_eq]
    rfl
  have hle : e6RelWeyl (e6QpSupport D.qpIndex) D.i₀ ≤ Subgroup.closure
      ((fun β => setReflection (thetaOrbit D.theta β)) '' unionSimpleRoots D.chi Set.univ) := by
    refine Subgroup.closure_mono ?_
    rintro _ ⟨_, ⟨i, hi, rfl⟩, rfl⟩
    have hiS : i ∈ D.support := by
      rw [mem_support_iff, D.Ξ_eq]
      exact hi
    exact ⟨Pi.single i 1, D.mem_unionSimpleRoots_iff.2 ⟨i, hiS, rfl⟩, by rw [hsimple i hi]⟩
  have hroot : e6RootOrbit (e6QpSupport D.qpIndex) α = thetaOrbit D.theta α := by
    rw [thetaOrbit_eq_iterate, D.δ_eq]
    rfl
  refine ⟨w⁻¹, hle (inv_mem hw), _, hjΔ, ?_⟩
  rw [← hroot, ← hwO, Set.image_image, ← hsimple j hj]
  simp only [inv_smul_smul, Set.image_id']

@[expose] def psiAut : MulAut (ModGL Tag.E6 Ω) :=
  (exactEntrywiseAut Tag.E6 (iterateFrobeniusEquiv Ω 2 D.f)).trans (MulAut.conj D.psiRep)

theorem psiAut_apply (g : ModGL Tag.E6 Ω) : D.psiAut g = D.psi g :=
  rfl

theorem psi_eq_frobTwistGL : D.psi = frobTwistGL Tag.E6 Ω 2 D.f D.psiRep :=
  rfl

theorem psiRep_mem_adjointGroup : D.psiRep ∈ adjointGroup Tag.E6 Ω :=
  mul_mem (canonicalRep_mem_adjointGroup _ Ω _) (canonicalRep_mem_adjointGroup _ Ω _)

theorem psiRep_mem_normalizer :
    D.psiRep ∈ Subgroup.normalizer (torusGroup Tag.E6 Ω : Set (ModGL Tag.E6 Ω)) :=
  mul_mem (mem_normalizer_torusGroup_of_mem_monomialSubgroup
    (canonicalRep_mem_monomialSubgroup Ω _))
    (mem_normalizer_torusGroup_of_mem_monomialSubgroup (canonicalRep_mem_monomialSubgroup Ω _))

theorem map_psiAut_adjointGroup :
    (adjointGroup Tag.E6 Ω).map D.psiAut.toMonoidHom = adjointGroup Tag.E6 Ω := by
  have e : D.psiAut.toMonoidHom = (MulAut.conj D.psiRep).toMonoidHom.comp
      (exactEntrywiseAut Tag.E6 (iterateFrobeniusEquiv Ω 2 D.f)).toMonoidHom := rfl
  rw [e, ← Subgroup.map_map, map_exactEntrywiseAut _ (Or.inl rfl),
    map_conj_eq_of_mem_normalizer (Subgroup.le_normalizer D.psiRep_mem_adjointGroup)]

@[expose] def psiC : MulAut (adjointGroup Tag.E6 Ω) :=
  ((adjointGroup Tag.E6 Ω).equivMapOfInjective D.psiAut.toMonoidHom D.psiAut.injective).trans
    (MulEquiv.subgroupCongr D.map_psiAut_adjointGroup)

theorem coe_psiC (x : adjointGroup Tag.E6 Ω) : (D.psiC x : ModGL Tag.E6 Ω) = D.psi x :=
  rfl

omit [IsAlgClosed Ω] in
theorem canonicalRep_conj_pinnedX (w : WeylGroup Tag.E6) {γ : Fin Tag.E6.rank → ℤ}
    (hγ : IsRoot Tag.E6 γ) (c : Ω) :
    canonicalRep (coxeterSystem Tag.E6) Ω w * pinnedX Tag.E6 Ω γ c *
        (canonicalRep (coxeterSystem Tag.E6) Ω w)⁻¹ = pinnedX Tag.E6 Ω (w • γ) c := by
  obtain ⟨ω, hω, rfl⟩ := (coxeterSystem Tag.E6).exists_isReduced w
  rw [canonicalRep_wordProd hω]
  exact CFSG.RankThree.Chevalley.list_prod_weylElt_conj_pinnedX_of_charTwo ω hγ c

theorem psiRep_conj_pinnedX {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (c : Ω) :
    D.psiRep * pinnedX Tag.E6 Ω γ c * D.psiRep⁻¹ = pinnedX Tag.E6 Ω (D.δ γ) c := by
  have h0 := canonicalRep_conj_pinnedX e6W0 hγ c
  have h1 := canonicalRep_conj_pinnedX D.wJ (IsRoot.smul hγ e6W0) c
  calc D.psiRep * pinnedX Tag.E6 Ω γ c * D.psiRep⁻¹
      = canonicalRep (coxeterSystem Tag.E6) Ω D.wJ * (canonicalRep (coxeterSystem Tag.E6) Ω e6W0 *
          pinnedX Tag.E6 Ω γ c * (canonicalRep (coxeterSystem Tag.E6) Ω e6W0)⁻¹) *
          (canonicalRep (coxeterSystem Tag.E6) Ω D.wJ)⁻¹ := by
        rw [psiRep, _root_.mul_inv_rev]
        group
    _ = pinnedX Tag.E6 Ω (D.wJ • e6W0 • γ) c := by rw [h0, h1]
    _ = pinnedX Tag.E6 Ω (D.δ γ) c := by
        rw [e6W0_smul, smul_neg]
        rfl

theorem isRoot_δ {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) : IsRoot Tag.E6 (D.δ γ) :=
  isRoot_e6Delta D.J hγ

theorem psi_pinnedX {γ : Fin Tag.E6.rank → ℤ} (hγ : IsRoot Tag.E6 γ) (c : Ω) :
    D.psi (pinnedX Tag.E6 Ω γ c) = pinnedX Tag.E6 Ω (D.δ γ) (iterateFrobenius Ω 2 D.f c) := by
  rw [psi_eq_frobTwistGL, frobTwistGL_apply, entrywiseFrobGL_pinnedX, D.psiRep_conj_pinnedX hγ]

theorem psi_rootSL2 {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot Tag.E6 β) (A : SL2 Ω) :
    D.psi (rootSL2 Tag.E6 Ω β A) = rootSL2 Tag.E6 Ω (D.δ β)
      (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 D.f) A) := by
  have hδβ := D.isRoot_δ hβ
  have h : D.psi.comp (rootSL2 Tag.E6 Ω β) = (rootSL2 Tag.E6 Ω (D.δ β)).comp
      (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 D.f)) :=
    MonoidHom.eq_of_eqOn_dense CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower
      fun g hg => by
      rcases hg with ⟨c, rfl⟩ | ⟨c, rfl⟩
      · change D.psi (rootSL2 Tag.E6 Ω β (uSL c)) = rootSL2 Tag.E6 Ω (D.δ β)
          (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 D.f) (uSL c))
        rw [CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hβ, map_uSL,
          CFSG.RankThree.Chevalley.rootSL2_uSL_of_charTwo hδβ, D.psi_pinnedX hβ]
      · change D.psi (rootSL2 Tag.E6 Ω β (vSL c)) = rootSL2 Tag.E6 Ω (D.δ β)
          (Matrix.SpecialLinearGroup.map (iterateFrobenius Ω 2 D.f) (vSL c))
        rw [CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hβ, map_vSL,
          CFSG.RankThree.Chevalley.rootSL2_vSL_of_charTwo hδβ, D.psi_pinnedX (IsRoot.neg hβ),
          D.δ_neg]
  exact DFunLike.congr_fun h A

theorem map_torusGroup_psiC :
    ((torusGroup Tag.E6 Ω).subgroupOf (adjointGroup Tag.E6 Ω)).map D.psiC.toMonoidHom =
      (torusGroup Tag.E6 Ω).subgroupOf (adjointGroup Tag.E6 Ω) :=
  map_subgroupOf_adjointGroup D.coe_psiC torusGroup_le_adjointGroup
    (map_frobTwistGL_torusGroup 2 D.f D.psiRep_mem_normalizer)

theorem map_rootSubgroup_psiC {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot Tag.E6 α) :
    ((rootSubgroup Tag.E6 Ω α).subgroupOf (adjointGroup Tag.E6 Ω)).map D.psiC.toMonoidHom =
      (rootSubgroup Tag.E6 Ω (D.δ α)).subgroupOf (adjointGroup Tag.E6 Ω) :=
  map_subgroupOf_adjointGroup D.coe_psiC (rootSubgroup_le_adjointGroup α)
    (map_frobTwistGL_rootSubgroup_of_conj 2 D.f
      (fun γ hγ => ⟨1, fun c => by rw [Units.val_one, one_mul, D.psiRep_conj_pinnedX hγ]⟩) hα)

@[expose] def gen : GenFixedRootDatum Tag.E6 2 Ω (Multiplicative (Fin Tag.E6.rank → ℤ)) where
  simplyLaced := Or.inr (Or.inl rfl)
  e := D.f
  one_le_e := by have := D.two_le_f; omega
  χ := D.chi
  θ := D.theta
  isometry := latticeRealExt_isometry _ D.iform_δ
  bijOn_kernelRoots := by
    rw [D.kernelRoots_chi]
    exact bijOn_latticeRealExt D.δ_injective D.image_δ_Ξ
  bijOn_simpleRoots := bijOn_latticeRealExt D.δ_injective D.image_δ_unionSimpleRoots
  orbit_orthogonal := fun _ hα _ hβ _ hγ hne => D.orbit_orthogonal' hα hβ hγ hne
  orbit_reflection := fun _ hα => D.orbit_reflection' hα
  F := D.psiC
  map_torusGroup := D.map_torusGroup_psiC
  map_rootSubgroup := fun α hα α' h => by
    have e : α' = D.δ α := toReal_injective (h.symm.trans (D.theta_toReal α))
    subst e
    exact D.map_rootSubgroup_psiC hα.1
  map_rootSL2 := fun β hβ β' h A x hx => by
    have e : β' = D.δ β := toReal_injective (h.symm.trans (D.theta_toReal β))
    subst e
    obtain ⟨j, -, rfl⟩ := D.mem_unionSimpleRoots_iff.1 hβ
    rw [D.coe_psiC, hx]
    exact D.psi_rootSL2 (isRoot_single _ _) A
  J := Set.univ
  isThetaOrbit := D.isThetaOrbit_univ

end E6EvenFixedRootDatum

end CFSG.RankThree.Lattice

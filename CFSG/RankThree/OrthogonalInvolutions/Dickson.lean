module

public import CFSG.RankThree.OrthogonalInvolutions.Basic
public import CFSG.LieType.BorelTits.Families

public section

namespace CFSG.RankThree.OrthogonalInvolutions

open Module QuadraticMap CFSG.LieType.BorelTits

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

variable (K V) in
abbrev diagonalSubmodule : Submodule K (V × V) :=
  LinearMap.range (LinearMap.id.prod LinearMap.id : V →ₗ[K] V × V)

theorem inf_map_prodMap_diagonal (g : V →ₗ[K] V) :
    diagonalSubmodule K V ⊓ (diagonalSubmodule K V).map (g.prodMap LinearMap.id) =
      (LinearMap.ker (g - 1)).map (LinearMap.id.prod LinearMap.id : V →ₗ[K] V × V) := by
  ext p
  simp only [Submodule.mem_inf, LinearMap.mem_range, Submodule.mem_map, LinearMap.mem_ker,
    LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero]
  constructor
  · rintro ⟨⟨v, rfl⟩, ⟨_, ⟨w, rfl⟩, hw⟩⟩
    have h1 : g w = v := by simpa using congrArg Prod.fst hw
    have h2 : w = v := by simpa using congrArg Prod.snd hw
    subst h2
    exact ⟨w, h1, rfl⟩
  · rintro ⟨w, hw, rfl⟩
    refine ⟨⟨w, rfl⟩, ⟨(w, w), ⟨w, rfl⟩, ?_⟩⟩
    simp [hw]

theorem dicksonInvariant_diagonal [FiniteDimensional K V] (g : V ≃ₗ[K] V) :
    dicksonInvariant (diagonalSubmodule K V) ((g : V →ₗ[K] V).prodMap LinearMap.id) =
      (finrank K (commSpace g) : ZMod 2) := by
  have hinj : Function.Injective (LinearMap.id.prod LinearMap.id : V →ₗ[K] V × V) :=
    fun v w h => congrArg Prod.fst h
  have h1 : finrank K (diagonalSubmodule K V) = finrank K V := LinearMap.finrank_range_of_inj hinj
  have h2 : finrank K ↥(diagonalSubmodule K V ⊓
      (diagonalSubmodule K V).map ((g : V →ₗ[K] V).prodMap LinearMap.id)) =
      finrank K (fixSpace g) := by
    rw [inf_map_prodMap_diagonal]
    exact (Submodule.equivMapOfInjective _ hinj _).finrank_eq.symm
  have h3 := finrank_commSpace_add_finrank_fixSpace g
  rw [dicksonInvariant, h1, h2]
  congr 1
  omega

theorem natCast_finrank_commSpace_mul [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {g h : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (finrank K (commSpace (g * h)) : ZMod 2) =
      finrank K (commSpace g) + finrank K (commSpace h) := by
  have hΔ := (toQuadForm Q hQ).isLagrangian_prodNeg_diagonal
  have hG := QuadForm.prodNeg_Q_prodMap (toQuadForm_Q_apply hQ hg)
  have hH := QuadForm.prodNeg_Q_prodMap (toQuadForm_Q_apply hQ hh)
  have key := QuadForm.dicksonInvariant_mul hΔ hG hH
  have e : (LinearMap.id * LinearMap.id : V →ₗ[K] V) = LinearMap.id := LinearMap.id_comp _
  rw [LinearMap.prodMap_mul, e, ← LinearEquiv.coe_toLinearMap_mul] at key
  rw [← dicksonInvariant_diagonal, ← dicksonInvariant_diagonal, ← dicksonInvariant_diagonal]
  exact key

theorem natCast_finrank_commSpace_one :
    (finrank K (commSpace (1 : V ≃ₗ[K] V)) : ZMod 2) = 0 := by
  have : commSpace (1 : V ≃ₗ[K] V) = ⊥ := by
    rw [commSpace, LinearEquiv.coe_toLinearMap_one, ← Module.End.one_eq_id, sub_self,
      LinearMap.range_zero]
  rw [this, finrank_bot, Nat.cast_zero]

theorem natCast_finrank_commSpace_inv [FiniteDimensional K V] [CharP K 2]
    {Q : QuadraticForm K V} (hQ : Q.polarBilin.Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    (finrank K (commSpace g⁻¹) : ZMod 2) = finrank K (commSpace g) := by
  have h := natCast_finrank_commSpace_mul hQ hg (inv_mem hg)
  rw [mul_inv_cancel, natCast_finrank_commSpace_one] at h
  have h2 : ((finrank K (commSpace g) : ℕ) : ZMod 2) + finrank K (commSpace g) = 0 :=
    CharTwo.add_self_eq_zero _
  linear_combination -h - h2

@[expose] def omegaGroup [FiniteDimensional K V] [CharP K 2] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) : Subgroup (V ≃ₗ[K] V) where
  carrier := {g | g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ Even (finrank K (commSpace g))}
  mul_mem' := by
    rintro g h ⟨hg, hge⟩ ⟨hh, hhe⟩
    refine ⟨mul_mem hg hh, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_mul hQ hg hh,
      ZMod.natCast_eq_zero_iff_even.mpr hge, ZMod.natCast_eq_zero_iff_even.mpr hhe, add_zero]
  one_mem' := ⟨one_mem _, by
    rw [← ZMod.natCast_eq_zero_iff_even]
    exact natCast_finrank_commSpace_one⟩
  inv_mem' := by
    rintro g ⟨hg, hge⟩
    refine ⟨inv_mem hg, ?_⟩
    rw [← ZMod.natCast_eq_zero_iff_even, natCast_finrank_commSpace_inv hQ hg,
      ZMod.natCast_eq_zero_iff_even]
    exact hge

theorem mem_omegaGroup [FiniteDimensional K V] [CharP K 2] {Q : QuadraticForm K V}
    {hQ : Q.polarBilin.Nondegenerate} {g : V ≃ₗ[K] V} :
    g ∈ omegaGroup Q hQ ↔
      g ∈ TauCeti.QuadraticMap.orthogonalGroup Q ∧ Even (finrank K (commSpace g)) :=
  Iff.rfl

theorem omegaGroup_le [FiniteDimensional K V] [CharP K 2] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) :
    omegaGroup Q hQ ≤ TauCeti.QuadraticMap.orthogonalGroup Q :=
  fun _ hg => hg.1

@[expose] noncomputable def dicksonHom [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) :
    TauCeti.QuadraticMap.orthogonalGroup Q →* Multiplicative (ZMod 2) where
  toFun g := Multiplicative.ofAdd (finrank K (commSpace (g : V ≃ₗ[K] V)) : ZMod 2)
  map_one' := by
    rw [OneMemClass.coe_one, natCast_finrank_commSpace_one, ofAdd_zero]
  map_mul' g h := by
    rw [Subgroup.coe_mul, natCast_finrank_commSpace_mul hQ g.2 h.2, ofAdd_add]

theorem dicksonHom_apply [FiniteDimensional K V] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) (g : TauCeti.QuadraticMap.orthogonalGroup Q) :
    dicksonHom Q hQ g =
      Multiplicative.ofAdd (finrank K (commSpace (g : V ≃ₗ[K] V)) : ZMod 2) :=
  rfl

theorem dicksonHom_ker [FiniteDimensional K V] [CharP K 2] (Q : QuadraticForm K V)
    (hQ : Q.polarBilin.Nondegenerate) :
    (dicksonHom Q hQ).ker =
      (omegaGroup Q hQ).subgroupOf (TauCeti.QuadraticMap.orthogonalGroup Q) := by
  ext g
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, mem_omegaGroup, dicksonHom_apply,
    ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff, ZMod.natCast_eq_zero_iff_even]
  exact ⟨fun h => ⟨g.2, h⟩, fun h => h.2⟩

theorem exists_map_ne_zero [Nontrivial V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) : ∃ a, Q a ≠ 0 := by
  by_contra! h
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  apply hv
  refine hQ.1 v fun w => ?_
  rw [polarBilin_apply_apply, polar, h, h, h, sub_zero, sub_zero]

theorem finrank_commSpace_reflection [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) (a : V) [Invertible (Q a)] :
    finrank K (commSpace (TauCeti.QuadraticMap.reflection Q a)) = 1 := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact (isUnit_of_invertible (Q 0)).ne_zero (map_zero Q)
  have hle : commSpace (TauCeti.QuadraticMap.reflection Q a) ≤ K ∙ a := by
    intro x hx
    obtain ⟨v, rfl⟩ := mem_commSpace.mp hx
    rw [TauCeti.QuadraticMap.reflection_apply, sub_sub_cancel_left, Submodule.mem_span_singleton]
    exact ⟨-(⅟(Q a) * polar Q a v), by rw [neg_smul]⟩
  have hne : TauCeti.QuadraticMap.reflection Q a ≠ 1 := by
    intro h1
    obtain ⟨w, hw⟩ : ∃ w, polar Q a w ≠ 0 := by
      by_contra! h
      exact ha (hQ.1 a fun w => by rw [polarBilin_apply_apply]; exact h w)
    have h2 := LinearEquiv.congr_fun h1 w
    rw [TauCeti.QuadraticMap.reflection_apply, LinearEquiv.coe_one, id, sub_eq_self,
      smul_eq_zero] at h2
    have hQa : Q a ≠ 0 := Invertible.ne_zero (Q a)
    rcases h2 with h2 | h2
    · exact mul_ne_zero (by rw [invOf_eq_inv]; exact inv_ne_zero hQa) hw h2
    · exact ha h2
  have h1 := Submodule.finrank_mono hle
  rw [finrank_span_singleton ha] at h1
  have h2 := one_le_finrank_commSpace hne
  omega

theorem relIndex_omegaGroup [FiniteDimensional K V] [CharP K 2] [Nontrivial V]
    (Q : QuadraticForm K V) (hQ : Q.polarBilin.Nondegenerate) :
    (omegaGroup Q hQ).relIndex (TauCeti.QuadraticMap.orthogonalGroup Q) = 2 := by
  rw [Subgroup.relIndex, Subgroup.index_eq_two_iff]
  obtain ⟨a, ha⟩ := exists_map_ne_zero hQ
  let _ : Invertible (Q a) := invertibleOfNonzero ha
  have hrO := TauCeti.QuadraticMap.reflection_mem_orthogonalGroup Q a
  refine ⟨⟨TauCeti.QuadraticMap.reflection Q a, hrO⟩, fun b => ?_⟩
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.coe_mul, mem_omegaGroup,
    mem_omegaGroup]
  have hmul := natCast_finrank_commSpace_mul hQ b.2 hrO
  rw [finrank_commSpace_reflection hQ a, Nat.cast_one] at hmul
  simp only [b.2, mul_mem b.2 hrO, true_and]
  rw [xor_iff_iff_not, ← ZMod.natCast_eq_zero_iff_even, hmul, ← Nat.cast_one, ← Nat.cast_add,
    ZMod.natCast_eq_zero_iff_even, Nat.even_add_one]

theorem map_prodMap_prod (f g : V →ₗ[K] V) (U U' : Submodule K V) :
    (U.prod U').map (f.prodMap g) = (U.map f).prod (U'.map g) := by
  ext ⟨x, y⟩
  simp only [Submodule.mem_map, Submodule.mem_prod, Prod.exists, LinearMap.prodMap_apply,
    Prod.mk.injEq]
  constructor
  · rintro ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩
    exact ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
  · rintro ⟨⟨a, ha, rfl⟩, ⟨b, hb, rfl⟩⟩
    exact ⟨a, b, ⟨ha, hb⟩, rfl, rfl⟩

theorem finrank_prod_submodule [FiniteDimensional K V] (U U' : Submodule K V) :
    finrank K (U.prod U') = finrank K U + finrank K U' := by
  rw [(Submodule.prodEquiv U U').finrank_eq, Module.finrank_prod]

theorem natCast_finrank_sub_finrank_inf_map [FiniteDimensional K V] {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {U : Submodule K V} (hU : ∀ x ∈ U, Q x = 0)
    (hUdim : 2 * finrank K U = finrank K V) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    ((finrank K U - finrank K ↥(U ⊓ U.map (g : V →ₗ[K] V)) : ℕ) : ZMod 2) =
      finrank K (commSpace g) := by
  have hΔ := (toQuadForm Q hQ).isLagrangian_prodNeg_diagonal
  have hX : (toQuadForm Q hQ).prodNeg.IsLagrangian (U.prod U) := by
    refine ⟨fun p hp => ?_, ?_⟩
    · rw [Submodule.mem_prod] at hp
      simp [hU _ hp.1, hU _ hp.2]
    · rw [finrank_prod_submodule, Module.finrank_prod]
      omega
  have hG := QuadForm.prodNeg_Q_prodMap (toQuadForm_Q_apply hQ hg)
  have key := QuadForm.dicksonInvariant_eq hΔ hX hG
  rw [dicksonInvariant_diagonal] at key
  rw [key, dicksonInvariant, map_prodMap_prod, Submodule.map_id, Submodule.prod_inf_prod,
    inf_idem, finrank_prod_submodule, finrank_prod_submodule]
  congr 1
  omega

end CFSG.RankThree.OrthogonalInvolutions

module

public import CFSG.Timmesfeld.Transvection.PresSUClass
public import CFSG.Timmesfeld.Transvection.PresHalfSpace
public import CFSG.LieType.Universal.Unitary.Extras.Commutator
import all CFSG.LieType.Universal.Unitary.Roots

public section

namespace CFSG.Timmesfeld.Transvection

open Matrix CFSG.LieType CFSG.LieType.Steinberg CFSG.LieType.Universal
  CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.RootSystem CFSG.LieType.BorelTits CFSG.Timmesfeld.Transvection.Pres
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open CFSG.LieType.Universal.Symplectic (stdVec)
open scoped commutatorElement

variable {m : ℕ}

theorem mem_roots_iff_su (he : Even m) (γ : Fin (m / 2) → ℤ) :
    γ ∈ roots (isFiniteType_cartan m) (divisible m) ↔
      toStd m γ ∈ Set.range (stdVec (n := m / 2)) := by
  rw [roots_eq]
  constructor
  · rintro (⟨i, j, hij, hi, hj, hji, h⟩ | ⟨i, hi, h⟩ | ⟨hodd, -⟩)
    · obtain ⟨a, rfl⟩ := exists_crd_eq he i
      obtain ⟨b, rfl⟩ := exists_crd_eq he j
      have hb : Sum.swap b ≠ Sum.swap a := fun e => hij (by
        have := congrArg Sum.swap e
        rw [Sum.swap_swap, Sum.swap_swap] at this
        rw [this])
      refine ⟨rtIdx a (Sum.swap b), ?_⟩
      rw [stdVec_rtIdx hb, h, weight_crd, weight_crd, rt, CFSG.LieType.Steinberg.Sp.wt_swap,
        sub_eq_add_neg]
    · obtain ⟨a, rfl⟩ := exists_crd_eq he i
      refine ⟨rtIdx a a, ?_⟩
      rw [stdVec_rtIdx (swap_ne_self a).symm, h, weight_crd, rt, two_nsmul]
    · exact absurd he hodd
  · rintro ⟨t, ht⟩
    obtain ⟨a, b, hab, hrt⟩ := exists_rt_eq t
    by_cases hba : b = a
    · subst hba
      exact Or.inr (Or.inl ⟨crd b, crd_ne_rev b, by rw [← ht, ← hrt, weight_crd, rt, two_nsmul]⟩)
    · have hidx : idx a ≠ idx b := idx_ne_of_ne hba hab
      refine Or.inl ⟨crd a, crd (Sum.swap b), crd_ne_crd_swap hidx, crd_ne_rev a, crd_ne_rev _,
        ?_, ?_⟩
      · rw [crd_swap b, Ne, Fin.rev_inj]
        exact fun e => hba (crd_injective e)
      · rw [← ht, ← hrt, weight_crd, weight_crd, rt, CFSG.LieType.Steinberg.Sp.wt_swap,
          sub_neg_eq_add]

section Psi

variable {F : Type*} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) [CharP F 2]
  {G : Type*} [Group G] (R : SURelations (m / 2) σ G)

theorem mat_suElt_apply {a b : Fin (m / 2) ⊕ Fin (m / 2)} (h : idx a ≠ idx b) (c : F) :
    mat σ m (suElt σ hσ a b c) (crd a) (crd (Sum.swap b)) = c := by
  rw [mat_suElt_two hσ h]
  have h1 : crd a ≠ crd (Sum.swap b) := crd_ne_crd_swap h
  have h2 : crd b ≠ crd a := fun e => ne_of_idx_ne h (crd_injective e)
  simp [Matrix.add_apply, h1, h2]

theorem mat_suElt_apply' {a b : Fin (m / 2) ⊕ Fin (m / 2)} (h : idx a ≠ idx b) (c : F) :
    mat σ m (suElt σ hσ a b c) (crd b) (crd (Sum.swap a)) = σ c := by
  rw [mat_suElt_two hσ h]
  have h1 : crd b ≠ crd (Sum.swap a) := crd_ne_crd_swap h.symm
  have h2 : crd a ≠ crd b := fun e => ne_of_idx_ne h (crd_injective e).symm
  simp [Matrix.add_apply, h1, h2]

omit [CharP F 2] in
theorem mat_suLong_apply (a : Fin (m / 2) ⊕ Fin (m / 2)) {c : F} (h : c + σ c = 0) :
    mat σ m (suLong σ a c) (crd a) (crd (Sum.swap a)) = c := by
  rw [mat_suLong a h]
  have h1 : crd a ≠ crd (Sum.swap a) := by rw [crd_swap]; exact crd_ne_rev a
  simp [Matrix.add_apply, h1]

@[expose] noncomputable def shortPsi (he : Even m) {a b : Fin (m / 2) ⊕ Fin (m / 2)}
    (hab : idx a ≠ idx b) {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a b) :
    rootGroup σ hσ m γ →* G where
  toFun g := R.ξ a b (mat σ m g (crd a) (crd (Sum.swap b)))
  map_one' := by
    rw [OneMemClass.coe_one, map_one, Matrix.one_apply_ne (crd_ne_crd_swap hab), R.map_zero hab]
  map_mul' g g' := by
    obtain ⟨c, hc⟩ := (mem_rootGroup_iff_suElt hσ he hab hγ g).1 g.2
    obtain ⟨d, hd⟩ := (mem_rootGroup_iff_suElt hσ he hab hγ g').1 g'.2
    rw [Subgroup.coe_mul, ← hc, ← hd, ← suElt_add, mat_suElt_apply hσ hab,
      mat_suElt_apply hσ hab, mat_suElt_apply hσ hab, R.add a b hab]

theorem shortPsi_apply (he : Even m) {a b : Fin (m / 2) ⊕ Fin (m / 2)} (hab : idx a ≠ idx b)
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a b) (g : rootGroup σ hσ m γ) :
    shortPsi hσ R he hab hγ g = R.ξ a b (mat σ m g (crd a) (crd (Sum.swap b))) := rfl

@[expose] noncomputable def longPsi (he : Even m) (a : Fin (m / 2) ⊕ Fin (m / 2))
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a a) : rootGroup σ hσ m γ →* G where
  toFun g := R.ξL a (mat σ m g (crd a) (crd (Sum.swap a)))
  map_one' := by
    rw [OneMemClass.coe_one, map_one,
      Matrix.one_apply_ne (by rw [crd_swap]; exact crd_ne_rev a), R.mapL_zero]
  map_mul' g g' := by
    obtain ⟨c, hc0, hc⟩ := (mem_rootGroup_iff_suLong hσ he a hγ g).1 g.2
    obtain ⟨d, hd0, hd⟩ := (mem_rootGroup_iff_suLong hσ he a hγ g').1 g'.2
    rw [Subgroup.coe_mul, ← hc, ← hd, ← suLong_add a hc0 hd0,
      mat_suLong_apply a (by rw [map_add, add_add_add_comm, hc0, hd0, add_zero]),
      mat_suLong_apply a hc0, mat_suLong_apply a hd0,
      R.addL a c d (add_map_eq_zero_iff.1 hc0) (add_map_eq_zero_iff.1 hd0)]

theorem longPsi_apply (he : Even m) (a : Fin (m / 2) ⊕ Fin (m / 2)) {γ : Fin (m / 2) → ℤ}
    (hγ : toStd m γ = rt a a) (g : rootGroup σ hσ m γ) :
    longPsi hσ R he a hγ g = R.ξL a (mat σ m g (crd a) (crd (Sum.swap a))) := rfl

open Classical in
@[expose] noncomputable def suPsi (he : Even m) (γ : Fin (m / 2) → ℤ) :
    rootGroup σ hσ m γ →* G :=
  if h : ∃ t, stdVec t = toStd m γ then
    if hl : (sp h.choose).2 = (sp h.choose).1 then
      longPsi hσ R he (sp h.choose).1
        ((h.choose_spec.symm.trans (rt_sp h.choose).symm).trans (by rw [hl]))
    else
      shortPsi hσ R he (idx_ne_of_ne hl (sp_ne h.choose))
        (h.choose_spec.symm.trans (rt_sp h.choose).symm)
  else 1

theorem eval_mem_rootGroup {a b : Fin (m / 2) ⊕ Fin (m / 2)} {c : F} (hv : RElValid σ (a, b, c))
    {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a b) :
    (suRelationsModel hσ m).eval (a, b, c) ∈ rootGroup σ hσ m γ := by
  by_cases hba : b = a
  · subst hba
    rw [SURelations.eval_long, suRelationsModel_ξL]
    exact suLong_mem hσ b hγ c
  · rw [SURelations.eval_short _ hba, suRelationsModel_ξ]
    exact suElt_mem hσ (idx_ne_of_ne hba hv.1) hγ c

theorem suPsi_eval (he : Even m) {a b : Fin (m / 2) ⊕ Fin (m / 2)} {c : F}
    (hv : RElValid σ (a, b, c)) {γ : Fin (m / 2) → ℤ} (hγ : toStd m γ = rt a b) :
    suPsi hσ R he γ ⟨_, eval_mem_rootGroup hσ hv hγ⟩ = R.eval (a, b, c) := by
  have h : ∃ t, stdVec t = toStd m γ := ⟨rtIdx a b, (stdVec_rtIdx hv.1).trans hγ.symm⟩
  have hsp := eq_sp_of_rt_eq (hγ.symm.trans h.choose_spec.symm)
  rw [suPsi, dite_eq_left h]
  by_cases hba : b = a
  · subst hba
    have hc : c + σ c = 0 := add_map_eq_zero_iff.2 (hv.2 rfl)
    have e : sp h.choose = (b, b) := by rcases hsp with e | e <;> exact e.symm
    rw [dite_eq_left (by rw [e]), longPsi_apply]
    simp only [e]
    rw [SURelations.eval_long, SURelations.eval_long, suRelationsModel_ξL, mat_suLong_apply b hc]
  · have hidx : idx a ≠ idx b := idx_ne_of_ne hba hv.1
    have hl : ¬(sp h.choose).2 = (sp h.choose).1 := by
      rcases hsp with e | e <;> rw [← e] <;> simp only
      · exact hba
      · exact Ne.symm hba
    rw [dite_eq_right hl, shortPsi_apply]
    rcases hsp with e | e
    · simp only [← e]
      rw [SURelations.eval_short _ hba, SURelations.eval_short _ hba, suRelationsModel_ξ,
        mat_suElt_apply hσ hidx]
    · simp only [← e]
      rw [SURelations.eval_short _ hba, SURelations.eval_short _ hba, suRelationsModel_ξ,
        mat_suElt_apply' hσ hidx, R.swap a b hidx, hσ]

theorem evalO_mem_rootGroup
    {o : Option ((Fin (m / 2) ⊕ Fin (m / 2)) × (Fin (m / 2) ⊕ Fin (m / 2)) × F)}
    {γ : Fin (m / 2) → ℤ} (ho : ∀ e ∈ o, RElValid σ e ∧ rt e.1 e.2.1 = toStd m γ) :
    (suRelationsModel hσ m).evalO o ∈ rootGroup σ hσ m γ := by
  rcases o with _ | ⟨a, b, c⟩
  · exact one_mem _
  · obtain ⟨hv, hrt⟩ := ho _ rfl
    exact eval_mem_rootGroup hσ hv hrt.symm

theorem suPsi_evalO (he : Even m)
    {o : Option ((Fin (m / 2) ⊕ Fin (m / 2)) × (Fin (m / 2) ⊕ Fin (m / 2)) × F)}
    {γ : Fin (m / 2) → ℤ} (ho : ∀ e ∈ o, RElValid σ e ∧ rt e.1 e.2.1 = toStd m γ) :
    suPsi hσ R he γ ⟨_, evalO_mem_rootGroup hσ ho⟩ = R.evalO o := by
  rcases o with _ | ⟨a, b, c⟩
  · exact map_one _
  · obtain ⟨hv, hrt⟩ := ho _ rfl
    exact suPsi_eval hσ R he hv hrt.symm

theorem exists_eval_eq (he : Even m) {γ : Fin (m / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan m) (divisible m)) (g : rootGroup σ hσ m γ) :
    ∃ a b c, RElValid σ (a, b, c) ∧ toStd m γ = rt a b ∧
      (suRelationsModel hσ m).eval (a, b, c) = g := by
  obtain ⟨t, ht⟩ := (mem_roots_iff_su he γ).1 hγ
  obtain ⟨a, b, hab, hrt⟩ := exists_rt_eq t
  have hγ' : toStd m γ = rt a b := ht.symm.trans hrt.symm
  by_cases hba : b = a
  · subst hba
    obtain ⟨c, hc0, hc⟩ := (mem_rootGroup_iff_suLong hσ he b hγ' g).1 g.2
    exact ⟨b, b, c, relValid_long b (add_map_eq_zero_iff.1 hc0), hγ',
      by rw [SURelations.eval_long, suRelationsModel_ξL, hc]⟩
  · have hidx : idx a ≠ idx b := idx_ne_of_ne hba hab
    obtain ⟨c, hc⟩ := (mem_rootGroup_iff_suElt hσ he hidx hγ' g).1 g.2
    exact ⟨a, b, c, relValid_short hidx c, hγ',
      by rw [SURelations.eval_short _ hba, suRelationsModel_ξ, hc]⟩

theorem commCompat_suPsi (he : Even m) :
    CommCompat (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m))
      (rootGroup σ hσ m) (suPsi hσ R he) := by
  intro γ hγ δ hδ _ hγδ s t
  obtain ⟨a, b, s', hu, hγa, hs⟩ := exists_eval_eq hσ he hγ s
  obtain ⟨c, d, t', hv, hδc, ht⟩ := exists_eval_eq hσ he hδ t
  have hne : rt a b + rt c d ≠ 0 := by
    rw [← hγa, ← hδc, ← toStd_add']
    intro h0
    exact hγδ (toStd_injective m (h0.trans toStd_zero'.symm))
  obtain ⟨h1, h2, h3, hM⟩ := (suRelationsModel hσ m).comm_eval hσ hu hv hne
  obtain ⟨-, -, -, hG⟩ := R.comm_eval hσ hu hv hne
  set o := commData σ a b c d s' t'
  have e1 : rt a b + rt c d = toStd m (γ + δ) := by rw [toStd_add', hγa, hδc]
  have e2 : 2 • rt a b + rt c d = toStd m (2 • γ + δ) := by rw [toStd_add', toStd_nsmul, hγa, hδc]
  have e3 : rt a b + 2 • rt c d = toStd m (γ + 2 • δ) := by rw [toStd_add', toStd_nsmul, hγa, hδc]
  have ho1 : ∀ e ∈ o.1, RElValid σ e ∧ rt e.1 e.2.1 = toStd m (γ + δ) := fun e he =>
    ⟨(h1 e he).1, (h1 e he).2.trans e1⟩
  have ho2 : ∀ e ∈ o.2.1, RElValid σ e ∧ rt e.1 e.2.1 = toStd m (2 • γ + δ) := fun e he =>
    ⟨(h2 e he).1, (h2 e he).2.trans e2⟩
  have ho3 : ∀ e ∈ o.2.2, RElValid σ e ∧ rt e.1 e.2.1 = toStd m (γ + 2 • δ) := fun e he =>
    ⟨(h3 e he).1, (h3 e he).2.trans e3⟩
  have htriv : ∀ {v : Fin (m / 2) → ℤ} {o' : Option _},
      (∀ e ∈ o', RElValid σ e ∧ rt e.1 e.2.1 = toStd m v) →
      v ∉ roots (isFiniteType_cartan m) (divisible m) →
      (suRelationsModel hσ m).evalO o' = 1 := by
    intro v o' ho' hv'
    rcases o' with _ | ⟨e₁, e₂, e₃⟩
    · rfl
    · exfalso
      obtain ⟨hval, hrt⟩ := ho' _ rfl
      exact hv' ((mem_roots_iff_su he v).2 (hrt ▸ rt_mem hval.1))
  refine ⟨⟨_, evalO_mem_rootGroup hσ ho1⟩, ⟨_, evalO_mem_rootGroup hσ ho2⟩,
    ⟨_, evalO_mem_rootGroup hσ ho3⟩, ?_, fun h => htriv ho1 h, fun h => htriv ho2 h,
    fun h => htriv ho3 h, ?_⟩
  · rw [← hs, ← ht]
    exact hM
  · have hs' : s = ⟨_, eval_mem_rootGroup hσ hu hγa⟩ := Subtype.ext hs.symm
    have ht' : t = ⟨_, eval_mem_rootGroup hσ hv hδc⟩ := Subtype.ext ht.symm
    rw [hs', ht', suPsi_eval hσ R he hu hγa, suPsi_eval hσ R he hv hδc, suPsi_evalO hσ R he ho1,
      suPsi_evalO hσ R he ho2, suPsi_evalO hσ R he ho3]
    exact hG

end Psi

section HalfSpace

variable {F : Type*} [Field F] [Finite F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c) [CharP F 2]
  {G : Type*} [Group G] (R : SURelations (m / 2) σ G)

omit [Finite F] in
theorem one_mem_traceZero : (1 : F) ∈ traceZero σ := by
  rw [mem_traceZero, map_one, CharTwo.add_self_eq_zero]

omit [Finite F] in
theorem levelWeyl_conj_mem' (i : Fin (m / 2)) {γ : Fin (m / 2) → ℤ} {x : SU σ m}
    (hx : x ∈ rootGroup σ hσ m γ) :
    levelWeyl hσ ⟨1, one_mem_traceZero⟩ i * x * (levelWeyl hσ ⟨1, one_mem_traceZero⟩ i)⁻¹ ∈
      rootGroup σ hσ m ((RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)).refl i γ) := by
  have h := levelWeyl_conj_mem hσ (ζ := ⟨1, one_mem_traceZero⟩) one_ne_zero i γ x hx
  rwa [weylAction_simple] at h

theorem ne_two_smul_of_even (he : Even m) {γ δ : Fin (m / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan m) (divisible m))
    (hδ : δ ∈ roots (isFiniteType_cartan m) (divisible m)) : γ ≠ 2 • δ := by
  rintro rfl
  obtain ⟨t, ht⟩ := (mem_roots_iff_su he _).1 hγ
  obtain ⟨t', ht'⟩ := (mem_roots_iff_su he _).1 hδ
  have h1 := CFSG.LieType.Universal.Symplectic.SpExtras.dot_stdVec t
  have h2 := CFSG.LieType.Universal.Symplectic.SpExtras.dot_stdVec t'
  rw [ht, toStd_nsmul, ← ht', smul_dotProduct, dotProduct_smul, smul_smul] at h1
  simp only [nsmul_eq_mul] at h1
  push_cast at h1
  omega

omit [Finite F] [CharP F 2] in
theorem rootGroup_mul_comm (he : Even m) {γ : Fin (m / 2) → ℤ}
    (hγ : γ ∈ roots (isFiniteType_cartan m) (divisible m)) {x y : SU σ m}
    (hx : x ∈ rootGroup σ hσ m γ) (hy : y ∈ rootGroup σ hσ m γ) : x * y = y * x := by
  obtain ⟨t, ht⟩ := (mem_roots_iff_su he γ).1 hγ
  obtain ⟨a, b, hab, hrt⟩ := exists_rt_eq t
  have hγ' : toStd m γ = rt a b := ht.symm.trans hrt.symm
  by_cases hba : b = a
  · subst hba
    obtain ⟨c, hc0, rfl⟩ := (mem_rootGroup_iff_suLong hσ he b hγ' x).1 hx
    obtain ⟨d, hd0, rfl⟩ := (mem_rootGroup_iff_suLong hσ he b hγ' y).1 hy
    rw [← suLong_add b hc0 hd0, ← suLong_add b hd0 hc0, add_comm]
  · have hidx : idx a ≠ idx b := idx_ne_of_ne hba hab
    obtain ⟨c, rfl⟩ := (mem_rootGroup_iff_suElt hσ he hidx hγ' x).1 hx
    obtain ⟨d, rfl⟩ := (mem_rootGroup_iff_suElt hσ he hidx hγ' y).1 hy
    rw [← suElt_add, ← suElt_add, add_comm]

theorem extendsToHom_halfSpace_su (he : Even m) (f : (Fin (m / 2) → ℤ) →+ ℤ) :
    ExtendsToHom (rootGroup σ hσ m)
      (halfSpace (RootSystem.ofCartan (isFiniteType_cartan m) (divisible m)) f)
      (fun γ x => suPsi hσ R he γ x) :=
  extendsToHom_halfSpace (levelWeyl hσ ⟨1, one_mem_traceZero⟩)
    (fun i _ _ _ hx => levelWeyl_conj_mem' hσ i hx)
    (fun L hL hmem hsort => prodInjective_of hσ 1 one_ne_zero L hL (fun γ hγ => (hmem γ hγ).1)
      (fun γ hγ δ hδ => ne_two_smul_of_even he (hmem γ hγ).1 hδ)
      (fun γ hγ => by have := (hmem γ hγ).2; omega)
      (hsort.imp fun h => by simpa using h))
    (fun γ hγ _ hx _ hy => rootGroup_mul_comm hσ he hγ hx hy) (suPsi hσ R he)
    (commCompat_suPsi hσ R he) f

end HalfSpace

end CFSG.Timmesfeld.Transvection

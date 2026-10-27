module

public import CFSG.Sporadic.Th.Recog.Swap
public import CFSG.Sporadic.Th.Recog.EightDim
public import CFSG.GroupTheory.TwoElementSquare
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Wielandt

public section

open scoped commutatorElement

namespace CFSG.Sporadic.Th.Recog

open CFSG

local instance (priority := high) : AddCommGroup (ZMod 2) :=
  Ring.toAddCommGroup

variable {G : Type} [Group G] [Finite G]

abbrev fiveClosure (u v : G) : Subgroup G :=
  Subgroup.closure {x : G | x * u = u * x ∧ x * v = v * x ∧ orderOf x = 5}

theorem fiveClosure_comm (u v : G) : fiveClosure u v = fiveClosure v u := by
  unfold fiveClosure
  congr 1
  ext x
  constructor <;> rintro ⟨h1, h2, h3⟩ <;> exact ⟨h2, h1, h3⟩

theorem fiveClosure_map_conj (u v y : G) :
    (fiveClosure u v).map (MulAut.conj y).toMonoidHom =
      fiveClosure (y * u * y⁻¹) (y * v * y⁻¹) := by
  unfold fiveClosure
  rw [MonoidHom.map_closure]
  congr 1
  ext x
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z ∈ {x : G | x * u = u * x ∧ x * v = v * x ∧ orderOf x = 5} := hz
    refine ⟨?_, ?_, ?_⟩
    · change (MulAut.conj y) z * (MulAut.conj y) u = (MulAut.conj y) u * (MulAut.conj y) z
      rw [← map_mul, ← map_mul, hz'.1]
    · change (MulAut.conj y) z * (MulAut.conj y) v = (MulAut.conj y) v * (MulAut.conj y) z
      rw [← map_mul, ← map_mul, hz'.2.1]
    · rw [orderOf_injective (MulAut.conj y).toMonoidHom (MulAut.conj y).injective z,
        hz'.2.2]
  · intro hx
    have hx' : x ∈ {x : G | x * (y * u * y⁻¹) = (y * u * y⁻¹) * x ∧
        x * (y * v * y⁻¹) = (y * v * y⁻¹) * x ∧ orderOf x = 5} := hx
    refine ⟨(MulAut.conj y).symm x, ?_, ?_⟩
    · refine ⟨?_, ?_, ?_⟩
      · apply (MulAut.conj y).injective
        change (MulAut.conj y) ((MulAut.conj y).symm x * u) =
          (MulAut.conj y) (u * (MulAut.conj y).symm x)
        rw [map_mul, map_mul, (MulAut.conj y).apply_symm_apply]
        exact hx'.1
      · apply (MulAut.conj y).injective
        change (MulAut.conj y) ((MulAut.conj y).symm x * v) =
          (MulAut.conj y) (v * (MulAut.conj y).symm x)
        rw [map_mul, map_mul, (MulAut.conj y).apply_symm_apply]
        exact hx'.2.1
      · have hsc : SemiconjBy y⁻¹ x ((MulAut.conj y).symm x) := by
          dsimp [SemiconjBy]
          group
        rw [← SemiconjBy.orderOf_eq y⁻¹ hsc, hx'.2.2]
    · exact (MulAut.conj y).apply_symm_apply x

abbrev K (S : ThSetting G) (w : G) : Subgroup G := fiveClosure S.z w

theorem K_le_H (S : ThSetting G) (w : G) : K S w ≤ S.H := by
  unfold K fiveClosure
  rw [Subgroup.closure_le]
  intro x hx
  change x ∈ Subgroup.centralizer ({S.z} : Set G)
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact hx.1

noncomputable def thetaK (S : ThSetting G) (w : G) :
    fiveClosure S.z w →* alternatingGroup (Fin 9) :=
  S.θ.comp (Subgroup.inclusion (K_le_H S w))

noncomputable def twoCore (K : Subgroup G) : Subgroup G :=
  (CFSG.pCore 2 K).map K.subtype

noncomputable def e9v (i : Fin 9) : V8 :=
  if h : (i : ℕ) < 8 then Pi.single ⟨i, h⟩ 1 else 0

noncomputable def pairVec (a b : Fin 9) : V8 := e9v a + e9v b

theorem ext9_pairVec (a b : Fin 9) :
    ext9 (pairVec a b) = Pi.single a 1 + Pi.single b 1 := by
  fin_cases a <;> fin_cases b <;> decide +kernel

theorem rho8p_pairVec (σ : alternatingGroup (Fin 9)) (a b : Fin 9) :
    rho8p σ (pairVec a b) = pairVec ((σ : Equiv.Perm (Fin 9)) a) ((σ : Equiv.Perm (Fin 9)) b) := by
  apply ext9_injective
  rw [ext9_rho8p, ext9_pairVec, ext9_pairVec]
  funext j
  fin_cases j <;> simp [Pi.single_apply, Equiv.symm_apply_eq]

noncomputable def formB (S : ThSetting G) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8) :
    LinearMap.BilinForm (ZMod 2) V8 :=
  LinearMap.BilinForm.comp S.toSetting.q.polarBilin
    (e.symm : V8 →ₗ[ZMod 2] S.toSetting.Qt)
    (e.symm : V8 →ₗ[ZMod 2] S.toSetting.Qt)

theorem formB_alt (S : ThSetting G) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8) (v : V8) :
    formB S e v v = 0 := by
  change (S.toSetting.q.polarBilin (e.symm v)) (e.symm v) = 0
  exact S.toSetting.polarBilin_isAlt (x := e.symm v)

theorem formB_invariant (S : ThSetting G) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    (σ : alternatingGroup (Fin 9)) (v w : V8) :
    formB S e (rho8p σ v) (rho8p σ w) = formB S e v w := by
  have hmem : S.rho σ ∈ S.toSetting.O := by
    obtain ⟨h, rfl⟩ := S.θ_surj σ
    rw [S.rho_θ h]
    exact (S.toSetting.ρ (S.toSettingE h)).2
  have hsymm : ∀ x : V8, e.symm (rho8p σ x) = S.rho σ (e.symm x) := by
    intro x
    apply LinearEquiv.injective e
    rw [LinearEquiv.apply_symm_apply, he σ (e.symm x), LinearEquiv.apply_symm_apply]
  change (S.toSetting.q.polarBilin (e.symm (rho8p σ v))) (e.symm (rho8p σ w)) =
    (S.toSetting.q.polarBilin (e.symm v)) (e.symm w)
  rw [hsymm v, hsymm w, QuadraticMap.polarBilin_apply_apply,
    QuadraticMap.polarBilin_apply_apply]
  exact TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hmem _ _

theorem formB_exists_ne_zero (S : ThSetting G) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8) :
    ∃ v w : V8, formB S e v w ≠ 0 := by
  by_contra h
  push Not at h
  have hzero : formB S e = 0 := LinearMap.BilinForm.ext h
  have hqzero : S.toSetting.q.polarBilin =
      (0 : LinearMap.BilinForm (ZMod 2) S.toSetting.Qt) := by
    refine LinearMap.BilinForm.ext ?_
    intro u v
    have := LinearMap.BilinForm.ext_iff.mp hzero (e u) (e v)
    simpa [formB, LinearMap.BilinForm.comp_apply] using this
  have hcard : Nat.card S.toSetting.Qt = 2 ^ 8 := by
    rw [S.toSetting.card_Qt, S.finrank_Qt]
  haveI : Nontrivial S.toSetting.Qt := by
    have h256 : 1 < Nat.card S.toSetting.Qt := by rw [hcard]; norm_num
    rw [← not_subsingleton_iff_nontrivial]
    intro hs
    have h1 : Nat.card S.toSetting.Qt = 1 := Nat.card_eq_one_iff_unique.mpr ⟨hs, inferInstance⟩
    omega
  obtain ⟨u, hu⟩ := exists_ne (0 : S.toSetting.Qt)
  have hleft := S.toSetting.q_nondegenerate.1 u
  apply hu
  apply hleft
  intro v
  rw [hqzero]
  rfl

theorem exists_alternating_triple_map {a b c a' b' c' : Fin 9}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hab' : a' ≠ b') (hbc' : b' ≠ c') (hac' : a' ≠ c') :
    ∃ σ : alternatingGroup (Fin 9), (σ : Equiv.Perm (Fin 9)) a = a' ∧
      (σ : Equiv.Perm (Fin 9)) b = b' ∧ (σ : Equiv.Perm (Fin 9)) c = c' := by
  haveI h3 : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 9)) (Fin 9) 3 := by
    haveI : MulAction.IsMultiplyPretransitive (alternatingGroup (Fin 9)) (Fin 9)
        (Nat.card (Fin 9) - 2) :=
      alternatingGroup.isMultiplyPretransitive (α := Fin 9)
    exact MulAction.isMultiplyPretransitive_of_le (G := alternatingGroup (Fin 9)) (α := Fin 9)
      (m := 3) (n := Nat.card (Fin 9) - 2) (by norm_num) (by norm_num)
  let x : Fin 3 ↪ Fin 9 := ⟨![a, b, c], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  let y : Fin 3 ↪ Fin 9 := ⟨![a', b', c'], by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all⟩
  obtain ⟨σ, hσ⟩ := (MulAction.isMultiplyPretransitive_iff.mp h3 x y)
  refine ⟨σ, ?_, ?_, ?_⟩
  · have hx0 : (x : Fin 3 → Fin 9) 0 = a := rfl
    have hy0 : (y : Fin 3 → Fin 9) 0 = a' := rfl
    have h := congrArg (fun f : Fin 3 ↪ Fin 9 => (f : Fin 3 → Fin 9) 0) hσ
    simpa [hx0, hy0, Subgroup.smul_def, Equiv.Perm.smul_def] using h
  · have hx1 : (x : Fin 3 → Fin 9) 1 = b := rfl
    have hy1 : (y : Fin 3 → Fin 9) 1 = b' := rfl
    have h := congrArg (fun f : Fin 3 ↪ Fin 9 => (f : Fin 3 → Fin 9) 1) hσ
    simpa [hx1, hy1, Subgroup.smul_def, Equiv.Perm.smul_def] using h
  · have hx2 : (x : Fin 3 → Fin 9) 2 = c := rfl
    have hy2 : (y : Fin 3 → Fin 9) 2 = c' := rfl
    have h := congrArg (fun f : Fin 3 ↪ Fin 9 => (f : Fin 3 → Fin 9) 2) hσ
    simpa [hx2, hy2, Subgroup.smul_def, Equiv.Perm.smul_def] using h

theorem formB_pairVec_shared_eq (S : ThSetting G) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {a b c a' b' c' : Fin 9}
    (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c)
    (hab' : a' ≠ b') (hbc' : b' ≠ c') (hac' : a' ≠ c') :
    formB S e (pairVec a b) (pairVec b c) =
      formB S e (pairVec a' b') (pairVec b' c') := by
  obtain ⟨σ, ha, hb, hc⟩ := exists_alternating_triple_map hab hbc hac hab' hbc' hac'
  rw [← formB_invariant S e he σ (pairVec a b) (pairVec b c)]
  rw [rho8p_pairVec, rho8p_pairVec, ha, hb, hc]

theorem span_pairVec_last :
    Submodule.span (ZMod 2)
      (Set.range (fun i : Fin 8 => pairVec (Fin.castSucc i) (Fin.last 8))) = ⊤ := by
  rw [Submodule.eq_top_iff']
  intro v
  have hv : v = ∑ i : Fin 8, v i • Pi.single i 1 := by
    funext j
    rw [Finset.sum_apply]
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne (Ne.symm hb)]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hv]
  refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  refine ⟨i, ?_⟩
  simp [pairVec, e9v]

theorem formB_pairVec_shared_eq_one (S : ThSetting G) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {a b c : Fin 9} (hab : a ≠ b) (hbc : b ≠ c) (hac : a ≠ c) :
    formB S e (pairVec a b) (pairVec b c) = 1 := by
  have hα := formB_pairVec_shared_eq (S := S) (e := e) (he := he)
    (a := a) (b := b) (c := c) (a' := 0) (b' := 1) (c' := 2)
    hab hbc hac (by decide) (by decide) (by decide)
  rw [hα]
  by_contra hne
  have hzeroα : formB S e (pairVec 0 1) (pairVec 1 2) = 0 := by
    rcases CFSG.Certificates.ExtraspecialNF.zmod_two_cases
      (formB S e (pairVec 0 1) (pairVec 1 2)) with h | h
    · exact h
    · exact absurd h hne
  have hbasis : ∀ i j : Fin 8,
      formB S e (pairVec (Fin.castSucc i) (Fin.last 8))
        (pairVec (Fin.castSucc j) (Fin.last 8)) = 0 := by
    intro i j
    by_cases hij : i = j
    · subst hij
      exact formB_alt S e _
    · have hi : Fin.castSucc i ≠ Fin.last 8 := Fin.castSucc_ne_last i
      have hj : Fin.last 8 ≠ Fin.castSucc j := (Fin.castSucc_ne_last j).symm
      have hij' : Fin.castSucc i ≠ Fin.castSucc j := by
        intro h; exact hij (Fin.castSucc_injective 8 h)
      have h := formB_pairVec_shared_eq (S := S) (e := e) (he := he)
        (a := Fin.castSucc i) (b := Fin.last 8) (c := Fin.castSucc j)
        (a' := 0) (b' := 1) (c' := 2)
        hi hj hij' (by decide) (by decide) (by decide)
      rw [hzeroα] at h
      simpa [pairVec, add_comm] using h
  have hzeroB : formB S e = 0 := by
    apply LinearMap.BilinForm.ext
    intro v w
    have hv : v ∈ Submodule.span (ZMod 2)
        (Set.range (fun i : Fin 8 => pairVec (Fin.castSucc i) (Fin.last 8))) := by
      rw [span_pairVec_last]; trivial
    have hw : w ∈ Submodule.span (ZMod 2)
        (Set.range (fun i : Fin 8 => pairVec (Fin.castSucc i) (Fin.last 8))) := by
      rw [span_pairVec_last]; trivial
    revert w
    refine Submodule.span_induction (p := fun x _ => ∀ w ∈ Submodule.span (ZMod 2)
      (Set.range (fun i : Fin 8 => pairVec (Fin.castSucc i) (Fin.last 8))),
        formB S e x w = 0) ?_ ?_ ?_ ?_ hv
    · intro x hx w hw
      obtain ⟨i, rfl⟩ := hx
      refine Submodule.span_induction
        (p := fun y _ => formB S e (pairVec (Fin.castSucc i) (Fin.last 8)) y = 0)
        ?_ ?_ ?_ ?_ hw
      · intro y hy
        obtain ⟨j, rfl⟩ := hy
        exact hbasis i j
      · simp
      · intro y z _ _ hy hz
        rw [map_add, hy, hz, add_zero]
      · intro c y _ hy
        rw [map_smul, hy, smul_zero]
    · intro w hw
      simp
    · intro x y _ _ hx hy w hw
      rw [map_add, LinearMap.add_apply, hx w hw, hy w hw, add_zero]
    · intro c x _ hx w hw
      rw [map_smul, LinearMap.smul_apply, hx w hw, smul_zero]
  obtain ⟨v, w, hvw⟩ := formB_exists_ne_zero S e
  exact hvw (by rw [hzeroB]; rfl)

noncomputable def T (S : ThSetting G) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8) (w : G) :
    Finset (Fin 9) := supp9 (e (S.toSetting.cl w))

theorem T_even_nonempty (S : ThSetting G) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z) :
    Even (T S e w).card ∧ (T S e w).Nonempty := by
  have hwQG : w ∈ S.toSetting.QG := by rw [S.toSetting_QG]; exact hw
  have hcl : S.toSetting.cl w ≠ 0 := by
    intro h
    rcases (S.toSetting.cl_eq_zero_iff hwQG).mp h with h1 | h1
    · exact hwz (h1 ▸ Subgroup.one_mem _)
    · exact hwz (h1 ▸ Subgroup.mem_zpowers S.z)
  refine ⟨even_card_supp9 _, ?_⟩
  exact supp9_nonempty (x := e (S.toSetting.cl w)) (by
    intro hzero
    exact hcl (LinearEquiv.injective e (hzero.trans (map_zero e).symm)))

theorem thetaK_generator_stabilizes_T (S : ThSetting G)
    (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {w : G} (hw : w ∈ S.Q)
    {y : G} (hy : y ∈ ({x : G | x * S.z = S.z * x ∧ x * w = w * x ∧ orderOf x = 5} : Set G)) :
    ∀ j, ((thetaK S w ⟨y, Subgroup.subset_closure hy⟩ : alternatingGroup (Fin 9)) :
        Equiv.Perm (Fin 9)) j ∈ T S e w ↔ j ∈ T S e w := by
  have hyH : y ∈ S.H := K_le_H S w (Subgroup.subset_closure hy)
  have hyw : y * w = w * y := hy.2.1
  have hyw' : y * w * y⁻¹ = w := by rw [hyw]; group
  have hwQG : w ∈ S.toSetting.QG := by rw [S.toSetting_QG]; exact hw
  have hρ : ((S.toSetting.ρ (S.toSettingE ⟨y, hyH⟩) : S.toSetting.O) :
      S.toSetting.Qt ≃ₗ[ZMod 2] S.toSetting.Qt) (S.toSetting.cl w) = S.toSetting.cl w := by
    rw [S.toSetting.ρ_cl (S.toSettingE ⟨y, hyH⟩) hwQG]
    rw [show (((S.toSettingE ⟨y, hyH⟩ : S.toSetting.M) : G) * w *
      ((S.toSettingE ⟨y, hyH⟩ : S.toSetting.M) : G)⁻¹) = y * w * y⁻¹ from rfl, hyw']
  have htheta : thetaK S w ⟨y, Subgroup.subset_closure hy⟩ = S.θ ⟨y, hyH⟩ := by
    rw [thetaK, MonoidHom.comp_apply]
    congr 1
  have hfix : S.rho (S.θ ⟨y, hyH⟩) (S.toSetting.cl w) = S.toSetting.cl w := by
    rw [S.rho_θ ⟨y, hyH⟩]
    exact hρ
  have hfix' : rho8p (S.θ ⟨y, hyH⟩) (e (S.toSetting.cl w)) = e (S.toSetting.cl w) := by
    rw [← he]
    exact congrArg e hfix
  have hsupp := (rho8p_eq_self_iff (S.θ ⟨y, hyH⟩) (e (S.toSetting.cl w))).mp hfix'
  rw [htheta]
  simpa [T] using hsupp

theorem thetaK_generator_mem_fixingSubgroup (S : ThSetting G)
    (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z)
    {y : G} (hy : y ∈ ({x : G | x * S.z = S.z * x ∧ x * w = w * x ∧ orderOf x = 5} : Set G)) :
    thetaK S w ⟨y, Subgroup.subset_closure hy⟩ ∈ fixingSubgroup (omegaOf (T S e w)) := by
  by_cases h1 : thetaK S w ⟨y, Subgroup.subset_closure hy⟩ = 1
  · rw [h1]
    exact (fixingSubgroup _).one_mem
  · have hT := T_even_nonempty S e hw hwz
    have hsupp := thetaK_generator_stabilizes_T S e he hw hy
    have hord_sub : orderOf (⟨y, Subgroup.subset_closure hy⟩ : fiveClosure S.z w) = 5 := by
      rw [← Subgroup.orderOf_coe]
      exact hy.2.2
    have hdvd : orderOf (thetaK S w ⟨y, Subgroup.subset_closure hy⟩) ∣ 5 := by
      simpa [hord_sub] using orderOf_map_dvd (thetaK S w) ⟨y, Subgroup.subset_closure hy⟩
    have hord5 : orderOf (thetaK S w ⟨y, Subgroup.subset_closure hy⟩) = 5 := by
      rcases Nat.dvd_prime (by decide : Nat.Prime 5) |>.mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) h1
      · exact h
    have hsuppΩ := support_subset_omegaOf (T := T S e w) hord5 hsupp
    rw [mem_fixingSubgroup]
    intro j hj
    by_contra hne
    exact hj (hsuppΩ (Equiv.Perm.mem_support.mpr hne))

theorem thetaK_range_le_fixingSubgroup (S : ThSetting G)
    (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z) :
    (thetaK S w).range ≤ fixingSubgroup (omegaOf (T S e w)) := by
  rintro σ ⟨x, rfl⟩
  have hgen : ∀ y : G, ∀ hy : y ∈ ({x : G | x * S.z = S.z * x ∧ x * w = w * x ∧
      orderOf x = 5} : Set G),
      thetaK S w ⟨y, Subgroup.subset_closure hy⟩ ∈ fixingSubgroup (omegaOf (T S e w)) := by
    intro y hy
    exact thetaK_generator_mem_fixingSubgroup S e he hw hwz hy
  have hx : thetaK S w x ∈ fixingSubgroup (omegaOf (T S e w)) := by
    refine Subgroup.closure_induction (p := fun y hy =>
      thetaK S w ⟨y, hy⟩ ∈ fixingSubgroup (omegaOf (T S e w)))
      (fun y hy => hgen y hy) ?_ ?_ ?_ x.2
    · change thetaK S w (1 : fiveClosure S.z w) ∈ fixingSubgroup (omegaOf (T S e w))
      rw [map_one]
      exact (fixingSubgroup (omegaOf (T S e w))).one_mem
    · intro y z hy hz ihy ihz
      have hyz : y * z ∈ fiveClosure S.z w := Subgroup.mul_mem _ hy hz
      have hprod : (⟨y, hy⟩ : fiveClosure S.z w) * ⟨z, hz⟩ = ⟨y * z, hyz⟩ :=
        Subtype.ext rfl
      change thetaK S w ⟨y * z, hyz⟩ ∈ fixingSubgroup (omegaOf (T S e w))
      rw [← hprod, map_mul]
      exact mul_mem ihy ihz
    · intro y hy ihy
      have hyinv : y⁻¹ ∈ fiveClosure S.z w := Subgroup.inv_mem _ hy
      have hinv : (⟨y, hy⟩ : fiveClosure S.z w)⁻¹ = ⟨y⁻¹, hyinv⟩ := Subtype.ext rfl
      change thetaK S w ⟨y⁻¹, hyinv⟩ ∈ fixingSubgroup (omegaOf (T S e w))
      rw [← hinv, map_inv]
      exact inv_mem ihy
  exact hx

theorem thetaK_ker (S : ThSetting G) (w : G) :
    (thetaK S w).ker = S.Q.subgroupOf (fiveClosure S.z w) := by
  ext x
  rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
  constructor
  · intro h
    have hx : (Subgroup.inclusion (K_le_H S w) x) ∈ S.θ.ker := MonoidHom.mem_ker.mpr h
    rw [S.θ_ker] at hx
    exact Subgroup.mem_subgroupOf.mp hx
  · intro hx
    have hx' : (Subgroup.inclusion (K_le_H S w) x) ∈ S.θ.ker := by
      rw [S.θ_ker]
      exact Subgroup.mem_subgroupOf.mpr hx
    exact MonoidHom.mem_ker.mp hx'

theorem conj_eq_self_of_orderOf_eq_five {x w z : G} (hx : orderOf x = 5)
    (hz2 : z * z = 1) (hz1 : z ≠ 1) (hxz : x * z = z * x)
    (h : x * w * x⁻¹ = w ∨ x * w * x⁻¹ = w * z) : x * w * x⁻¹ = w := by
  rcases h with h | h
  · exact h
  · exfalso
    have hx5 : x ^ 5 = 1 := by
      rw [← hx, pow_orderOf_eq_one]
    have hx6 : x ^ 6 = x := by
      calc x ^ 6 = x ^ 5 * x := by rw [pow_succ]
        _ = x := by rw [hx5, one_mul]
    have hxz' : x * z * x⁻¹ = z := by rw [hxz]; group
    have hx2 : x ^ 2 * w * (x ^ 2)⁻¹ = w := by
      rw [pow_two]
      calc (x * x) * w * (x * x)⁻¹ = x * (x * w * x⁻¹) * x⁻¹ := by group
        _ = x * (w * z) * x⁻¹ := by rw [h]
        _ = (x * w * x⁻¹) * (x * z * x⁻¹) := by group
        _ = (w * z) * z := by rw [h, hxz']
        _ = w := by rw [mul_assoc, hz2, mul_one]
    have hx2pow : ∀ n : ℕ, (x ^ 2) ^ n * w * ((x ^ 2) ^ n)⁻¹ = w := by
      intro n
      induction n with
      | zero => simp
      | succ n ih =>
          calc (x ^ 2) ^ (n + 1) * w * ((x ^ 2) ^ (n + 1))⁻¹
              = (x ^ 2) ^ n * ((x ^ 2) * w * (x ^ 2)⁻¹) * ((x ^ 2) ^ n)⁻¹ := by group
            _ = (x ^ 2) ^ n * w * ((x ^ 2) ^ n)⁻¹ := by rw [hx2]
            _ = w := ih
    have hx2_3 : (x ^ 2) ^ 3 = x := by
      rw [← pow_mul]
      norm_num
      exact hx6
    have hxw : x * w * x⁻¹ = w := by
      have := hx2pow 3
      rwa [hx2_3] at this
    have hwz : w * z = w := h.symm.trans hxw
    have hz : z = 1 := by
      apply mul_left_cancel (a := w)
      rwa [mul_one]
    exact hz1 hz

theorem exists_lift_orderOf_eq_five (S : ThSetting G)
    (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z)
    {σ : alternatingGroup (Fin 9)} (hσ : orderOf σ = 5)
    (hσT : ∀ j, (σ : Equiv.Perm (Fin 9)) j ∈ T S e w ↔ j ∈ T S e w) :
    ∃ (x : G) (hx : x ∈ fiveClosure S.z w), x * w = w * x ∧ orderOf x = 5 ∧
      S.θ ⟨x, K_le_H S w hx⟩ = σ := by
  classical
  let P : Subgroup (alternatingGroup (Fin 9)) := Subgroup.zpowers σ
  let E : Subgroup S.H := P.comap S.θ
  let φ : E →* P :=
    { toFun := fun x => ⟨S.θ x.1, x.2⟩
      map_one' := Subtype.ext (map_one S.θ)
      map_mul' := fun x y => Subtype.ext (map_mul S.θ x.1 y.1) }
  have hφsurj : Function.Surjective φ := by
    intro p
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp p.2
    obtain ⟨h, hh⟩ := S.θ_surj σ
    refine ⟨⟨h ^ n, ?_⟩, ?_⟩
    ·
      change S.θ (h ^ n) ∈ Subgroup.zpowers σ
      rw [map_zpow, hh]
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, rfl⟩
    ·
      apply Subtype.ext
      simp only [φ, MonoidHom.coe_mk, OneHom.coe_mk, map_zpow, hh]
      exact hn
  have hker : IsPGroup 2 φ.ker := by
    let ψ : φ.ker →* S.Q :=
      { toFun := fun x => ⟨x.1.1.1, by
          have hx : S.θ x.1.1 = 1 := by
            have h := congrArg Subtype.val (MonoidHom.mem_ker.mp x.2)
            simpa [φ] using h
          have hxmem : x.1.1 ∈ S.θ.ker := MonoidHom.mem_ker.mpr hx
          rw [S.θ_ker] at hxmem
          exact Subgroup.mem_subgroupOf.mp hxmem⟩
        map_one' := Subtype.ext rfl
        map_mul' := fun x y => Subtype.ext rfl }
    have hψinj : Function.Injective ψ := by
      intro x y hxy
      apply Subtype.ext
      apply Subtype.ext
      simpa [ψ] using congrArg (fun z : S.Q => (z : G)) hxy
    exact IsPGroup.of_injective S.ext.1 ψ hψinj
  have hcop : Nat.Coprime 2 (Nat.card P) := by
    rw [show Nat.card P = orderOf σ from Nat.card_zpowers σ, hσ]
    norm_num
  obtain ⟨sec, hsec⟩ := CFSG.Wielandt.exists_monoidHom_rightInverse_of_surjective_isPGroup_ker
    φ hφsurj hker hcop
  let p : P := ⟨σ, Subgroup.mem_zpowers σ⟩
  let xE : E := sec p
  let x : S.H := xE.1
  have hθx : S.θ x = σ := by
    have h := hsec p
    change φ (sec p) = p at h
    change S.θ x = σ
    exact congrArg Subtype.val h
  have hsecinj : Function.Injective sec := Function.LeftInverse.injective (hsec)
  have hxordP : orderOf (sec p) = 5 := by
    have hp : orderOf p = 5 := by
      rw [show p = ⟨σ, Subgroup.mem_zpowers σ⟩ from rfl, ← Subgroup.orderOf_coe, hσ]
    rw [orderOf_injective sec hsecinj p, hp]
  have hxordE : orderOf xE = 5 := by
    simpa [xE] using hxordP
  have hxord : orderOf x = 5 := by
    change orderOf (↑xE : S.H) = 5
    rw [Subgroup.orderOf_coe]
    exact hxordE
  have hxH : (x : G) ∈ S.H := x.2
  have hxcl : S.toSetting.cl ((x : G) * w * (x : G)⁻¹) = S.toSetting.cl w := by
    have hwQG : w ∈ S.toSetting.QG := by rw [S.toSetting_QG]; exact hw
    have hfixρ : ((S.toSetting.ρ (S.toSettingE x) : S.toSetting.O) :
        S.toSetting.Qt ≃ₗ[ZMod 2] S.toSetting.Qt) (S.toSetting.cl w) = S.toSetting.cl w := by
      have hfix : S.rho σ (S.toSetting.cl w) = S.toSetting.cl w := by
        have hfix' : rho8p σ (e (S.toSetting.cl w)) = e (S.toSetting.cl w) := by
          rw [rho8p_eq_self_iff]
          simpa [T] using hσT
        have h := congrArg e.symm hfix'
        have hsymm : e.symm (rho8p σ (e (S.toSetting.cl w))) =
            S.rho σ (S.toSetting.cl w) := by
          have h' := congrArg e.symm (he σ (e.symm (e (S.toSetting.cl w))))
          simpa [LinearEquiv.apply_symm_apply] using h'.symm
        rw [hsymm] at h
        simpa using h
      rw [← hθx, S.rho_θ x] at hfix
      exact hfix
    rw [S.toSetting.ρ_cl (S.toSettingE x) hwQG] at hfixρ
    have hcoe : ((S.toSettingE x : S.toSetting.M) : G) = (x : G) := rfl
    rw [hcoe] at hfixρ
    exact hfixρ
  have hxw : (x : G) * w * (x : G)⁻¹ = w := by
    have hwQG : w ∈ S.toSetting.QG := by rw [S.toSetting_QG]; exact hw
    have hconjQG : (x : G) * w * (x : G)⁻¹ ∈ S.toSetting.QG := by
      rw [S.toSetting_QG]
      have hwQH : (⟨w, S.Q_le_H hw⟩ : S.H) ∈ S.Q.subgroupOf S.H :=
        Subgroup.mem_subgroupOf.mpr hw
      have hconj := S.Q_normal.conj_mem (⟨w, S.Q_le_H hw⟩ : S.H) hwQH x
      exact Subgroup.mem_subgroupOf.mp hconj
    rcases (S.toSetting.cl_eq_cl_iff hwQG hconjQG).mp hxcl.symm with h | h
    · exact h
    · exact absurd h (by
        intro h
        have hxodd : orderOf ((x : S.H) : G) = 5 := by
          rw [Subgroup.orderOf_coe]
          exact hxord
        have hz2 : S.z * S.z = 1 := by rw [← pow_two, ← S.ord_z, pow_orderOf_eq_one]
        have hz1 : S.z ≠ 1 := by
          intro h1
          have := S.ord_z
          rw [h1, orderOf_one] at this
          norm_num at this
        have hxz : (x : G) * S.z = S.z * (x : G) :=
          Subgroup.mem_centralizer_singleton_iff.mp hxH
        have hconj := conj_eq_self_of_orderOf_eq_five hxodd hz2 hz1 hxz (Or.inr h)
        rw [hconj] at h
        have hwz : w * S.z = w := h.symm
        have hz : S.z = 1 := by
          apply mul_left_cancel (a := w)
          simpa using hwz
        exact hz1 hz)
  have hxw_comm : (x : G) * w = w * (x : G) := by
    have := congrArg (fun t : G => t * (x : G)) hxw
    simpa [mul_assoc] using this
  have hxordG : orderOf ((x : S.H) : G) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hxord
  have hxK : ((x : S.H) : G) ∈ fiveClosure S.z w := by
    rw [Subgroup.mem_closure]
    intro K hK
    exact hK ⟨Subgroup.mem_centralizer_singleton_iff.mp hxH, hxw_comm, hxordG⟩
  refine ⟨((x : S.H) : G), hxK, hxw_comm, hxordG, ?_⟩
  exact hθx

theorem thetaK_range_ge_fixingSubgroup (S : ThSetting G)
    (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z) :
    fixingSubgroup (omegaOf (T S e w)) ≤ (thetaK S w).range := by
  have hT := T_even_nonempty S e hw hwz
  rw [← closure_fiveCycles_stabilizer_eq_fixingSubgroup hT.1 hT.2]
  rw [Subgroup.closure_le]
  rintro σ ⟨hσ5, hσT⟩
  obtain ⟨x, hxK, hxw, hxord, hθx⟩ := exists_lift_orderOf_eq_five S e he hw hwz hσ5 hσT
  exact ⟨⟨x, hxK⟩, hθx⟩

theorem thetaK_range_eq_fixingSubgroup (S : ThSetting G)
    (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z) :
    (thetaK S w).range = fixingSubgroup (omegaOf (T S e w)) :=
  le_antisymm (thetaK_range_le_fixingSubgroup S e he hw hwz)
    (thetaK_range_ge_fixingSubgroup S e he hw hwz)

noncomputable def fixingSubgroupEquiv (Ω : Finset (Fin 9)) :
    fixingSubgroup Ω ≃* alternatingGroup Ω :=
  (MulEquiv.subgroupCongr (fixingSubgroup_eq_map Ω)).trans
    ((Subgroup.equivMapOfInjective (⊤ : Subgroup (alternatingGroup Ω)) (altEmbed Ω)
      (altEmbed_injective Ω)).symm.trans Subgroup.topEquiv)

theorem fixingSubgroup_isSimple {Ω : Finset (Fin 9)} (h5 : 5 ≤ Ω.card) :
    IsSimpleGroup (fixingSubgroup Ω) := by
  haveI : IsSimpleGroup (alternatingGroup Ω) :=
    alternatingGroup.isSimpleGroup (α := Ω) (by simpa using h5)
  exact MulEquiv.isSimpleGroup (fixingSubgroupEquiv Ω)

theorem fixingSubgroup_nonabelian {Ω : Finset (Fin 9)} (h5 : 5 ≤ Ω.card) :
    ∃ a b : fixingSubgroup Ω, a * b ≠ b * a := by
  have hcard : 5 ≤ Nat.card Ω := by simpa using h5
  have hnt : Nontrivial (alternatingGroup Ω) :=
    alternatingGroup.nontrivial_of_three_le_card (by omega)
  have hcenter : Subgroup.center (alternatingGroup Ω) = ⊥ :=
    alternatingGroup.center_eq_bot (by omega)
  have hnab : ∃ a b : alternatingGroup Ω, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have htop : Subgroup.center (alternatingGroup Ω) = ⊤ :=
      eq_top_iff.mpr fun x _ => Subgroup.mem_center_iff.mpr fun g => h g x
    rw [hcenter] at htop
    exact (bot_ne_top : (⊥ : Subgroup (alternatingGroup Ω)) ≠ ⊤) htop
  obtain ⟨a, b, hab⟩ := hnab
  refine ⟨(fixingSubgroupEquiv Ω).symm a, (fixingSubgroupEquiv Ω).symm b, ?_⟩
  intro h
  apply hab
  simpa using congrArg (fixingSubgroupEquiv Ω) h

theorem inf_le_twoCore (S : ThSetting G) (w : G) :
    K S w ⊓ S.Q ≤ twoCore (K S w) := by
  intro x hx
  have hxK : x ∈ K S w := hx.1
  have hxQ : x ∈ S.Q := hx.2
  have hEq : (K S w ⊓ S.Q).subgroupOf (K S w) = S.Q.subgroupOf (K S w) := by
    ext y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · rintro ⟨-, h⟩; exact h
    · intro h; exact ⟨y.2, h⟩
  have hN : ((K S w ⊓ S.Q).subgroupOf (K S w)).Normal := by
    rw [hEq]
    refine Subgroup.Normal.mk ?_
    intro x hx g
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxH : (⟨x, S.Q_le_H hx⟩ : S.H) ∈ S.Q.subgroupOf S.H :=
      Subgroup.mem_subgroupOf.mpr hx
    have hconj := S.Q_normal.conj_mem (⟨x, S.Q_le_H hx⟩ : S.H) hxH
      (⟨(g : G), K_le_H S w g.2⟩ : S.H)
    exact Subgroup.mem_subgroupOf.mp hconj
  have hP' : IsPGroup 2 ↥(K S w ⊓ S.Q) := S.ext.1.to_le inf_le_right
  have hP : IsPGroup 2 ((K S w ⊓ S.Q).subgroupOf (K S w)) :=
    IsPGroup.of_equiv hP' (Subgroup.subgroupOfEquivOfLe inf_le_left).symm
  have hmem : ((K S w ⊓ S.Q).subgroupOf (K S w)) ∈
      {N : Subgroup (K S w) | N.Normal ∧ IsPGroup 2 N} := ⟨hN, hP⟩
  have hx' : (⟨x, hxK⟩ : K S w) ∈ (K S w ⊓ S.Q).subgroupOf (K S w) :=
    Subgroup.mem_subgroupOf.mpr ⟨hxK, hxQ⟩
  have hpcore : (⟨x, hxK⟩ : K S w) ∈ CFSG.pCore 2 (K S w) :=
    Subgroup.mem_sSup_of_mem hmem hx'
  exact Subgroup.mem_map_of_mem (K S w).subtype hpcore

theorem twoCore_le_inf (S : ThSetting G) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z) :
    twoCore (K S w) ≤ K S w ⊓ S.Q := by
  intro x hx
  rcases Subgroup.mem_map.mp hx with ⟨xK, hxcore, rfl⟩
  have hxK : (xK : G) ∈ K S w := xK.2
  refine ⟨hxK, ?_⟩
  have hT := T_even_nonempty S e hw hwz
  have hΩ5 : 5 ≤ (omegaOf (T S e w)).card := (card_omegaOf hT.1 hT.2).1
  have hrange := thetaK_range_eq_fixingSubgroup S e he hw hwz
  let N : Subgroup (K S w) := CFSG.pCore 2 (K S w)
  let M : Subgroup (alternatingGroup (Fin 9)) := N.map (thetaK S w)
  have hMle : M ≤ fixingSubgroup (omegaOf (T S e w)) := by
    rw [← hrange]
    exact Subgroup.map_le_range (thetaK S w) N
  have hMnorm : (M.subgroupOf (fixingSubgroup (omegaOf (T S e w)))).Normal := by
    refine Subgroup.Normal.mk ?_
    intro m hm g
    rw [Subgroup.mem_subgroupOf]
    change (g : alternatingGroup (Fin 9)) * (m : alternatingGroup (Fin 9)) *
      (g : alternatingGroup (Fin 9))⁻¹ ∈ M
    have hg : (g : alternatingGroup (Fin 9)) ∈ (thetaK S w).range := by
      rw [hrange]
      exact g.2
    obtain ⟨y, hy⟩ := hg
    obtain ⟨n, hnN, hn⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hm)
    have hyN : y * n * y⁻¹ ∈ N := CFSG.pCore_normal.conj_mem n hnN y
    rw [← hy, ← hn]
    rw [show thetaK S w y * thetaK S w n * (thetaK S w y)⁻¹ =
      thetaK S w (y * n * y⁻¹) by simp [map_mul]]
    exact Subgroup.mem_map_of_mem (thetaK S w) hyN
  have hMp : IsPGroup 2 ↥M := by
    change IsPGroup 2 ↥(N.map (thetaK S w))
    exact CFSG.pCore_isPGroup.map (thetaK S w)
  have hMp' : IsPGroup 2 ↥(M.subgroupOf (fixingSubgroup (omegaOf (T S e w)))) :=
    IsPGroup.of_equiv hMp (Subgroup.subgroupOfEquivOfLe hMle).symm
  haveI : IsSimpleGroup (fixingSubgroup (omegaOf (T S e w))) :=
    fixingSubgroup_isSimple hΩ5
  have hbot := CFSG.eq_bot_of_normal_isPGroup_of_isSimpleGroup
    (fixingSubgroup_nonabelian hΩ5) hMp'
  have hMbot : M = ⊥ := by
    have hmap := Subgroup.map_subgroupOf_eq_of_le hMle
    rw [hbot] at hmap
    simpa using hmap.symm
  have hxker : xK ∈ (thetaK S w).ker := by
    have hxmem : thetaK S w xK ∈ M := Subgroup.mem_map_of_mem _ hxcore
    rw [hMbot] at hxmem
    exact hxmem
  rw [thetaK_ker] at hxker
  exact Subgroup.mem_subgroupOf.mp hxker

theorem twoCore_eq_inf (S : ThSetting G) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z) :
    twoCore (K S w) = K S w ⊓ S.Q :=
  le_antisymm (twoCore_le_inf S e he hw hwz) (inf_le_twoCore S w)

theorem commutator_mem_Q (S : ThSetting G) {x : G} (hx : x ∈ S.H) (q : S.Q) :
    ⁅(q : G), x⁆ ∈ S.Q := by
  have hqinv : (q : G)⁻¹ ∈ S.Q := S.Q.inv_mem q.2
  have hconjH : (⟨x, hx⟩ : S.H) * (⟨(q : G)⁻¹, S.Q_le_H hqinv⟩ : S.H) *
      (⟨x, hx⟩ : S.H)⁻¹ ∈ S.Q.subgroupOf S.H :=
    S.Q_normal.conj_mem _ (Subgroup.mem_subgroupOf.mpr hqinv) (⟨x, hx⟩ : S.H)
  have hconj : x * (q : G)⁻¹ * x⁻¹ ∈ S.Q := Subgroup.mem_subgroupOf.mp hconjH
  have heq : ⁅(q : G), x⁆ = (q : G) * (x * (q : G)⁻¹ * x⁻¹) := by
    rw [commutatorElement_def]; group
  rw [heq]
  exact S.Q.mul_mem q.2 hconj

theorem conj_mem_or_mul_z (S : ThSetting G) {q : S.Q} {w : G} (hw : w ∈ S.Q) :
    (q : G) * w * (q : G)⁻¹ = w ∨ (q : G) * w * (q : G)⁻¹ = w * S.z := by
  have hqH : (q : G) ∈ S.H := S.Q_le_H q.2
  have hwQG : w ∈ S.toSetting.QG := by rw [S.toSetting_QG]; exact hw
  have hconjQG : (q : G) * w * (q : G)⁻¹ ∈ S.toSetting.QG := by
    rw [S.toSetting_QG]
    have hwQH : (⟨w, S.Q_le_H hw⟩ : S.H) ∈ S.Q.subgroupOf S.H :=
      Subgroup.mem_subgroupOf.mpr hw
    have hconj := S.Q_normal.conj_mem (⟨w, S.Q_le_H hw⟩ : S.H) hwQH
      (⟨(q : G), hqH⟩ : S.H)
    exact Subgroup.mem_subgroupOf.mp hconj
  have hcl : S.toSetting.cl ((q : G) * w * (q : G)⁻¹) = S.toSetting.cl w := by
    have hρ : ((S.toSetting.ρ (S.toSettingE ⟨(q : G), hqH⟩) : S.toSetting.O) :
        S.toSetting.Qt ≃ₗ[ZMod 2] S.toSetting.Qt) (S.toSetting.cl w) = S.toSetting.cl w := by
      rw [S.toSetting.ρ_eq_one_of_mem_Q]
      · rfl
      · rw [S.toSetting_Q_eq]
        exact Subgroup.mem_subgroupOf.mpr q.2
    rw [S.toSetting.ρ_cl (S.toSettingE ⟨(q : G), hqH⟩) hwQG] at hρ
    have hcoe : ((S.toSettingE ⟨(q : G), hqH⟩ : S.toSetting.M) : G) = (q : G) := rfl
    rw [hcoe] at hρ
    exact hρ
  rcases (S.toSetting.cl_eq_cl_iff hwQG hconjQG).mp hcl.symm with h | h
  · exact Or.inl h
  · exact Or.inr h

theorem commutator_mem_K (S : ThSetting G) {w : G} (hw : w ∈ S.Q)
    {x : G} (hxK : x ∈ K S w) (hxw : x * w = w * x) (hxord : orderOf x = 5)
    (q : S.Q) : ⁅(q : G), x⁆ ∈ K S w := by
  have hxH : x ∈ S.H := K_le_H S w hxK
  have hqH : (q : G) ∈ S.H := S.Q_le_H q.2
  let c : G := (q : G) * x * (q : G)⁻¹
  have hcH : c ∈ S.H := S.H.mul_mem (S.H.mul_mem hqH hxH) (S.H.inv_mem hqH)
  have hcord : orderOf c = 5 := by
    have hsc : SemiconjBy (q : G) x c := by
      dsimp [SemiconjBy, c]
      group
    rw [← SemiconjBy.orderOf_eq (q : G) hsc]
    exact hxord
  have hcw : c * w = w * c := by
    have hc_conj : c * ((q : G) * w * (q : G)⁻¹) = ((q : G) * w * (q : G)⁻¹) * c := by
      dsimp [c]
      calc ((q : G) * x * (q : G)⁻¹) * ((q : G) * w * (q : G)⁻¹)
          = (q : G) * (x * w) * (q : G)⁻¹ := by group
        _ = (q : G) * (w * x) * (q : G)⁻¹ := by rw [hxw]
        _ = ((q : G) * w * (q : G)⁻¹) * ((q : G) * x * (q : G)⁻¹) := by group
    rcases conj_mem_or_mul_z S hw (q := q) with h | h
    · rwa [h] at hc_conj
    · have hc_z : c * S.z = S.z * c :=
        Subgroup.mem_centralizer_singleton_iff.mp hcH
      have hc_wz : c * (w * S.z) = (w * S.z) * c := by rwa [← h]
      have hcancel : c * w * S.z = w * c * S.z := by
        calc c * w * S.z = c * (w * S.z) := by group
          _ = (w * S.z) * c := hc_wz
          _ = w * (S.z * c) := by group
          _ = w * (c * S.z) := by rw [hc_z]
          _ = w * c * S.z := by group
      exact mul_right_cancel hcancel
  have hcK : c ∈ K S w := by
    rw [Subgroup.mem_closure]
    intro K hK
    exact hK ⟨Subgroup.mem_centralizer_singleton_iff.mp hcH, hcw, hcord⟩
  have hxinv : x⁻¹ ∈ K S w := (K S w).inv_mem hxK
  have heq : ⁅(q : G), x⁆ = c * x⁻¹ := by
    rw [commutatorElement_def]
  rw [heq]
  exact (K S w).mul_mem hcK hxinv

theorem cl_commutator (S : ThSetting G) {x : G} (hx : x ∈ S.H) (q : S.Q) :
    S.toSetting.cl ⁅(q : G), x⁆ =
      ((S.toSetting.ρ (S.toSettingE ⟨x, hx⟩) : S.toSetting.O) :
        S.toSetting.Qt ≃ₗ[ZMod 2] S.toSetting.Qt) (S.toSetting.cl (q : G)) +
        S.toSetting.cl (q : G) := by
  have hqQG : (q : G) ∈ S.toSetting.QG := by rw [S.toSetting_QG]; exact q.2
  have hqinvH : (q : G)⁻¹ ∈ S.H := S.H.inv_mem (S.Q_le_H q.2)
  have hconjQG : x * (q : G)⁻¹ * x⁻¹ ∈ S.toSetting.QG := by
    rw [S.toSetting_QG]
    have hqinvQ : (q : G)⁻¹ ∈ S.Q := S.Q.inv_mem q.2
    have hconj := S.Q_normal.conj_mem (⟨(q : G)⁻¹, S.Q_le_H hqinvQ⟩ : S.H)
      (Subgroup.mem_subgroupOf.mpr hqinvQ) (⟨x, hx⟩ : S.H)
    exact Subgroup.mem_subgroupOf.mp hconj
  have hdecomp : ⁅(q : G), x⁆ = (q : G) * (x * (q : G)⁻¹ * x⁻¹) := by
    rw [commutatorElement_def]; group
  calc S.toSetting.cl ⁅(q : G), x⁆
      = S.toSetting.cl (q : G) + S.toSetting.cl (x * (q : G)⁻¹ * x⁻¹) := by
        rw [hdecomp, S.toSetting.cl_mul hqQG hconjQG]
    _ = S.toSetting.cl (q : G) +
        ((S.toSetting.ρ (S.toSettingE ⟨x, hx⟩) : S.toSetting.O) :
          S.toSetting.Qt ≃ₗ[ZMod 2] S.toSetting.Qt) (S.toSetting.cl (q : G)) := by
        have hρ := S.toSetting.ρ_cl (S.toSettingE ⟨x, hx⟩) (S.toSetting.QG.inv_mem hqQG)
        rw [← S.toSetting.cl_inv hqQG]
        congr 1
        exact hρ.symm
    _ = ((S.toSetting.ρ (S.toSettingE ⟨x, hx⟩) : S.toSetting.O) :
          S.toSetting.Qt ≃ₗ[ZMod 2] S.toSetting.Qt) (S.toSetting.cl (q : G)) +
        S.toSetting.cl (q : G) := add_comm _ _

theorem fixingSubgroup_stabilizes {Ω : Finset (Fin 9)} (σ : fixingSubgroup Ω) :
    ∀ j, (σ : Equiv.Perm (Fin 9)) j ∈ Ω ↔ j ∈ Ω := by
  intro j
  constructor
  · intro hj
    by_contra hnot
    have hfix : (σ : Equiv.Perm (Fin 9)) j = j := σ.2 j hnot
    rw [hfix] at hj
    exact hnot hj
  · intro hj
    by_contra hnot
    have hfix : (σ : Equiv.Perm (Fin 9)) ((σ : Equiv.Perm (Fin 9)) j) =
        (σ : Equiv.Perm (Fin 9)) j := σ.2 ((σ : Equiv.Perm (Fin 9)) j) hnot
    have hsj : (σ : Equiv.Perm (Fin 9)) j = j :=
      (σ : Equiv.Perm (Fin 9)).injective hfix
    rw [← hsj] at hj
    exact hnot hj

theorem fixingSubgroup_stabilizes_T {T : Finset (Fin 9)}
    (σ : fixingSubgroup (omegaOf T)) :
    ∀ j, (σ : Equiv.Perm (Fin 9)) j ∈ T ↔ j ∈ T := by
  have hΩ := fixingSubgroup_stabilizes σ
  have hpart : omegaOf T = T ∨ omegaOf T = Tᶜ := by
    unfold omegaOf
    split_ifs with h
    · exact Or.inl rfl
    · exact Or.inr rfl
  rcases hpart with h | h
  · simpa [h] using hΩ
  · intro j
    have h1 : (σ : Equiv.Perm (Fin 9)) j ∈ Tᶜ ↔ j ∈ Tᶜ := by
      simpa [h] using hΩ j
    simpa [Finset.mem_compl] using not_congr h1

theorem exists_orderOf_eq_five_fixingSubgroup (S : ThSetting G)
    (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z) :
    ∃ σ : fixingSubgroup (omegaOf (T S e w)), orderOf σ = 5 := by
  have hT := T_even_nonempty S e hw hwz
  have hΩ := card_omegaOf hT.1 hT.2
  let Ω := omegaOf (T S e w)
  have hΩ5 : 5 ≤ Ω.card := hΩ.1
  have hΩ8 : Ω.card ≤ 8 := hΩ.2
  haveI : Nontrivial Ω := by
    have hlt : 1 < Fintype.card Ω := by
      rw [Fintype.card_coe]
      omega
    obtain ⟨a, b, hab⟩ := Fintype.one_lt_card_iff.mp hlt
    exact ⟨a, b, hab⟩
  have hdvd : 5 ∣ Fintype.card (alternatingGroup Ω) := by
    rw [← Nat.card_eq_fintype_card, nat_card_alternatingGroup, Nat.card_eq_fintype_card,
      Fintype.card_coe]
    interval_cases hc : Ω.card <;> norm_num [Nat.factorial]
  haveI : Fact (Nat.Prime 5) := ⟨by decide⟩
  obtain ⟨τ, hτ⟩ := exists_prime_orderOf_dvd_card 5 hdvd
  refine ⟨(fixingSubgroupEquiv Ω).symm τ, ?_⟩
  have h : orderOf τ = orderOf ((fixingSubgroupEquiv Ω).symm τ) := by
    simpa using orderOf_injective
      (fixingSubgroupEquiv Ω : fixingSubgroup Ω →* alternatingGroup Ω)
      (fixingSubgroupEquiv Ω).injective ((fixingSubgroupEquiv Ω).symm τ)
  exact h.symm.trans hτ

theorem pairVec_eq_add_rho8p (σ : alternatingGroup (Fin 9)) {a b p : Fin 9}
    (ha : (σ : Equiv.Perm (Fin 9)) a = b) (hp : (σ : Equiv.Perm (Fin 9)) p = p)
    (hab : a ≠ b) (hpa : p ≠ a) (hpb : p ≠ b) :
    pairVec a b = e9v a + e9v p + rho8p σ (e9v a + e9v p) := by
  apply ext9_injective
  have h1 : ext9 (e9v a) + ext9 (e9v p) = Pi.single a 1 + Pi.single p 1 := by
    rw [← ext9_add, ← pairVec, ext9_pairVec]
  have h2 : ext9 (e9v a + e9v p) = Pi.single a 1 + Pi.single p 1 := by
    rw [ext9_add, h1]
  rw [ext9_add, ext9_add, h1, ext9_rho8p, h2, ext9_pairVec]
  funext j
  by_cases hja : j = a <;> by_cases hjb : j = b <;> by_cases hjp : j = p <;>
    simp [Pi.add_apply, Pi.single_apply, Equiv.symm_apply_eq, ha, hp, hja, hjb, hjp,
      hab, hab.symm, hpa, hpa.symm, hpb, hpb.symm] <;> decide

theorem five_cycle_data (σ : alternatingGroup (Fin 9)) (hσ : orderOf σ = 5) :
    ∃ a b c p : Fin 9, a ≠ b ∧ b ≠ c ∧ a ≠ c ∧
      (σ : Equiv.Perm (Fin 9)) a = b ∧ (σ : Equiv.Perm (Fin 9)) b = c ∧
      (σ : Equiv.Perm (Fin 9)) p = p ∧ p ≠ a ∧ p ≠ b ∧ p ≠ c := by
  have hσperm : orderOf ((σ : alternatingGroup (Fin 9)) : Equiv.Perm (Fin 9)) = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hσ
  have hcyc : (σ : Equiv.Perm (Fin 9)).IsCycle := isCycle_of_orderOf_eq_five hσperm
  have hcard : (σ : Equiv.Perm (Fin 9)).support.card = 5 := by
    rw [← Equiv.Perm.IsCycle.orderOf hcyc, hσperm]
  obtain ⟨a, ha⟩ := Finset.card_pos.mp (by rw [hcard]; norm_num)
  let b : Fin 9 := (σ : Equiv.Perm (Fin 9)) a
  let c : Fin 9 := (σ : Equiv.Perm (Fin 9)) b
  have hab : a ≠ b := by
    intro h
    exact (Equiv.Perm.mem_support.mp ha) (by simpa [b] using h.symm)
  have hb_supp : b ∈ (σ : Equiv.Perm (Fin 9)).support := by
    have h := (Equiv.Perm.zpow_apply_mem_support (f := (σ : Equiv.Perm (Fin 9)))
      (n := 1) (x := a)).mpr ha
    simpa [b] using h
  have hbc : b ≠ c := by
    intro h
    have hb : (σ : Equiv.Perm (Fin 9)) b = b := by
      simpa [c] using h.symm
    exact (Equiv.Perm.mem_support.mp hb_supp) hb
  have hcycOn : (σ : Equiv.Perm (Fin 9)).IsCycleOn
      ((σ : Equiv.Perm (Fin 9)).support : Finset (Fin 9)) := by
    simpa [Equiv.Perm.support] using hcyc.isCycleOn
  have hac : a ≠ c := by
    intro h
    have h2 : ((σ : Equiv.Perm (Fin 9)) ^ 2) a = a := by
      rw [pow_two]
      exact h.symm
    have hdvd : ((σ : Equiv.Perm (Fin 9)).support.card : ℤ) ∣ 2 :=
      (hcycOn.zpow_apply_eq ha (n := 2)).mp h2
    rw [hcard] at hdvd
    norm_num at hdvd
  have hlt : (σ : Equiv.Perm (Fin 9)).support.card < (Finset.univ : Finset (Fin 9)).card := by
    rw [hcard, Finset.card_univ, Fintype.card_fin]
    norm_num
  obtain ⟨p, -, hp_not⟩ :=
    Finset.exists_mem_notMem_of_card_lt_card (s := (σ : Equiv.Perm (Fin 9)).support)
      (t := (Finset.univ : Finset (Fin 9))) hlt
  have hp : (σ : Equiv.Perm (Fin 9)) p = p := by
    by_contra h
    exact hp_not (Equiv.Perm.mem_support.mpr h)
  refine ⟨a, b, c, p, hab, hbc, hac, rfl, rfl, hp, ?_, ?_, ?_⟩
  · intro h; exact hp_not (h ▸ ha)
  · intro h; exact hp_not (h ▸ hb_supp)
  · intro h
    have hc_supp : c ∈ (σ : Equiv.Perm (Fin 9)).support := by
      have h := (Equiv.Perm.zpow_apply_mem_support (f := (σ : Equiv.Perm (Fin 9)))
        (n := 1) (x := b)).mpr hb_supp
      simpa [c] using h
    exact hp_not (h ▸ hc_supp)

theorem exists_noncommuting_commutators (S : ThSetting G)
    (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z)
    {x : G} (hxK : x ∈ K S w) (hxw : x * w = w * x) (hxord : orderOf x = 5)
    (hxθ : S.θ ⟨x, K_le_H S w hxK⟩ ≠ 1) :
    ∃ q1 q2 : S.Q, ⁅(q1 : G), x⁆ * ⁅(q2 : G), x⁆ ≠
      ⁅(q2 : G), x⁆ * ⁅(q1 : G), x⁆ := by
  classical
  let σ : alternatingGroup (Fin 9) := S.θ ⟨x, K_le_H S w hxK⟩
  have hxH : x ∈ S.H := K_le_H S w hxK
  have hσ5 : orderOf σ = 5 := by
    have hdvd : orderOf σ ∣ 5 := by
      have h := orderOf_map_dvd S.θ ⟨x, K_le_H S w hxK⟩
      rw [← Subgroup.orderOf_coe ⟨x, K_le_H S w hxK⟩, hxord] at h
      simpa [σ] using h
    rcases Nat.dvd_prime (by decide : Nat.Prime 5) |>.mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hxθ
    · exact h
  have hgen : x ∈ ({y : G | y * S.z = S.z * y ∧ y * w = w * y ∧ orderOf y = 5} : Set G) :=
    ⟨Subgroup.mem_centralizer_singleton_iff.mp hxH, hxw, hxord⟩
  have hsupp := thetaK_generator_stabilizes_T S e he hw hgen
  have htheta : thetaK S w ⟨x, Subgroup.subset_closure hgen⟩ = σ := by
    rw [thetaK, MonoidHom.comp_apply]
    congr 1
  have hσT : ∀ j, (σ : Equiv.Perm (Fin 9)) j ∈ T S e w ↔ j ∈ T S e w := by
    intro j
    rw [← htheta]
    exact hsupp j
  obtain ⟨a, b, c, p, hab, hbc, hac, ha, hb, hp, hpa, hpb, hpc⟩ :=
    five_cycle_data σ hσ5
  have hB : formB S e (pairVec a b) (pairVec b c) = 1 :=
    formB_pairVec_shared_eq_one S e he hab hbc hac
  have hu : pairVec a b = e9v a + e9v p + rho8p σ (e9v a + e9v p) :=
    pairVec_eq_add_rho8p σ ha hp hab hpa hpb
  have hv : pairVec b c = e9v b + e9v p + rho8p σ (e9v b + e9v p) := by
    have hpb' : p ≠ b := hpb
    have hpc' : p ≠ c := hpc
    exact pairVec_eq_add_rho8p σ hb hp hbc hpb' hpc'
  let w1 : S.toSetting.Qt := e.symm (e9v a + e9v p)
  let w2 : S.toSetting.Qt := e.symm (e9v b + e9v p)
  have h1 : e ((S.rho σ) w1 + w1) = pairVec a b := by
    rw [map_add, he σ w1, LinearEquiv.apply_symm_apply]
    rw [hu]
    abel
  have h2 : e ((S.rho σ) w2 + w2) = pairVec b c := by
    rw [map_add, he σ w2, LinearEquiv.apply_symm_apply]
    rw [hv]
    abel
  obtain ⟨q1G, hq1QG, hq1cl⟩ := S.toSetting.exists_cl w1
  let q1 : S.Q := ⟨q1G, by rwa [S.toSetting_QG] at hq1QG⟩
  have hq1cl' : S.toSetting.cl (q1 : G) = w1 := by simpa [q1] using hq1cl
  obtain ⟨q2G, hq2QG, hq2cl⟩ := S.toSetting.exists_cl w2
  let q2 : S.Q := ⟨q2G, by rwa [S.toSetting_QG] at hq2QG⟩
  have hq2cl' : S.toSetting.cl (q2 : G) = w2 := by simpa [q2] using hq2cl
  have hcl1 : S.toSetting.cl ⁅(q1 : G), x⁆ = (S.rho σ) w1 + w1 := by
    rw [cl_commutator S hxH q1, hq1cl']
    congr 1
    rw [← S.rho_θ ⟨x, hxH⟩]
  have hcl2 : S.toSetting.cl ⁅(q2 : G), x⁆ = (S.rho σ) w2 + w2 := by
    rw [cl_commutator S hxH q2, hq2cl']
    congr 1
    rw [← S.rho_θ ⟨x, hxH⟩]
  have he1 : e (S.toSetting.cl ⁅(q1 : G), x⁆) = pairVec a b := by
    rw [hcl1, h1]
  have he2 : e (S.toSetting.cl ⁅(q2 : G), x⁆) = pairVec b c := by
    rw [hcl2, h2]
  have hq1Q : ⁅(q1 : G), x⁆ ∈ S.Q := commutator_mem_Q S hxH q1
  have hq2Q : ⁅(q2 : G), x⁆ ∈ S.Q := commutator_mem_Q S hxH q2
  have hq1QG' : ⁅(q1 : G), x⁆ ∈ S.toSetting.QG := by rw [S.toSetting_QG]; exact hq1Q
  have hq2QG' : ⁅(q2 : G), x⁆ ∈ S.toSetting.QG := by rw [S.toSetting_QG]; exact hq2Q
  have hpolar : QuadraticMap.polar (⇑S.toSetting.q)
      (S.toSetting.cl ⁅(q1 : G), x⁆) (S.toSetting.cl ⁅(q2 : G), x⁆) = 1 := by
    have h := hB
    change QuadraticMap.polar (⇑S.toSetting.q) (e.symm (pairVec a b))
      (e.symm (pairVec b c)) = 1 at h
    have h1' : e.symm (pairVec a b) = S.toSetting.cl ⁅(q1 : G), x⁆ := by
      apply LinearEquiv.injective e
      rw [LinearEquiv.apply_symm_apply, he1]
    have h2' : e.symm (pairVec b c) = S.toSetting.cl ⁅(q2 : G), x⁆ := by
      apply LinearEquiv.injective e
      rw [LinearEquiv.apply_symm_apply, he2]
    have hpolar' : QuadraticMap.polar (⇑S.toSetting.q) (e.symm (pairVec a b))
        (e.symm (pairVec b c)) =
        QuadraticMap.polar (⇑S.toSetting.q) (S.toSetting.cl ⁅(q1 : G), x⁆)
          (S.toSetting.cl ⁅(q2 : G), x⁆) := by
      rw [h1', h2']
    rw [← hpolar']
    exact h
  refine ⟨q1, q2, ?_⟩
  intro hcomm
  have hzero : QuadraticMap.polar (⇑S.toSetting.q)
      (S.toSetting.cl ⁅(q1 : G), x⁆) (S.toSetting.cl ⁅(q2 : G), x⁆) = 0 :=
    (S.toSetting.polar_cl_eq_zero_iff hq1QG' hq2QG').mpr hcomm
  rw [hpolar] at hzero
  exact zero_ne_one hzero.symm

theorem exists_K_order_five_nontrivial (S : ThSetting G)
    (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z) :
    ∃ (x : G) (hx : x ∈ K S w), x * w = w * x ∧ orderOf x = 5 ∧
      S.θ ⟨x, K_le_H S w hx⟩ ≠ 1 := by
  obtain ⟨σ, hσ⟩ := exists_orderOf_eq_five_fixingSubgroup S e hw hwz
  let τ : alternatingGroup (Fin 9) := σ
  have hτ5 : orderOf τ = 5 := by
    rw [Subgroup.orderOf_coe]
    exact hσ
  have hτT : ∀ j, (τ : Equiv.Perm (Fin 9)) j ∈ T S e w ↔ j ∈ T S e w :=
    fixingSubgroup_stabilizes_T σ
  obtain ⟨x, hxK, hxw, hxord, hθx⟩ :=
    exists_lift_orderOf_eq_five S e he hw hwz hτ5 hτT
  refine ⟨x, hxK, hxw, hxord, ?_⟩
  rw [hθx]
  intro h1
  rw [h1, orderOf_one] at hτ5
  norm_num at hτ5

theorem commutator_Q_eq_zpowers (S : ThSetting G) :
    ⁅S.Q, S.Q⁆ = Subgroup.zpowers S.z := by
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro q1 hq1 q2 hq2
    have hq1QG : (q1 : G) ∈ S.toSetting.QG := by rw [S.toSetting_QG]; exact hq1
    have hq2QG : (q2 : G) ∈ S.toSetting.QG := by rw [S.toSetting_QG]; exact hq2
    rcases S.toSetting.commutator_eq_one_or_z hq1QG hq2QG with h | h
    · rw [commutatorElement_def, h]; exact Subgroup.one_mem _
    · rw [commutatorElement_def, h]; exact Subgroup.mem_zpowers S.z
  · let zQ : S.Q := ⟨S.z, S.z_mem_Q⟩
    have hzQ_center : zQ ∈ Subgroup.center S.Q := by
      rw [Subgroup.mem_center_iff]
      intro q
      apply Subtype.ext
      exact S.toSetting.z_comm_QG (by rw [S.toSetting_QG]; exact q.2)
    have hzQ_comm : zQ ∈ commutator S.Q := by
      rw [S.ext.2.1]
      exact hzQ_center
    have hmap : (commutator S.Q).map S.Q.subtype = ⁅S.Q, S.Q⁆ := by
      rw [commutator_def, Subgroup.map_commutator]
      congr 1 <;> rw [Subgroup.map_top, Subgroup.range_subtype]
    rw [← hmap]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_map_of_mem S.Q.subtype hzQ_comm)

theorem commutator_inf_eq_zpowers (S : ThSetting G)
    (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v))
    {w : G} (hw : w ∈ S.Q) (hwz : w ∉ Subgroup.zpowers S.z) :
    ⁅K S w ⊓ S.Q, K S w ⊓ S.Q⁆ = Subgroup.zpowers S.z := by
  have hle : ⁅K S w ⊓ S.Q, K S w ⊓ S.Q⁆ ≤ Subgroup.zpowers S.z := by
    calc ⁅K S w ⊓ S.Q, K S w ⊓ S.Q⁆ ≤ ⁅S.Q, S.Q⁆ :=
          Subgroup.commutator_mono inf_le_right inf_le_right
      _ = Subgroup.zpowers S.z := commutator_Q_eq_zpowers S
  obtain ⟨x, hxK, hxw, hxord, hxθ⟩ := exists_K_order_five_nontrivial S e he hw hwz
  obtain ⟨q1, q2, hnc⟩ := exists_noncommuting_commutators S e he hw hwz hxK hxw hxord hxθ
  have hq1K : ⁅(q1 : G), x⁆ ∈ K S w := commutator_mem_K S hw hxK hxw hxord q1
  have hq2K : ⁅(q2 : G), x⁆ ∈ K S w := commutator_mem_K S hw hxK hxw hxord q2
  have hq1Q : ⁅(q1 : G), x⁆ ∈ S.Q := commutator_mem_Q S (K_le_H S w hxK) q1
  have hq2Q : ⁅(q2 : G), x⁆ ∈ S.Q := commutator_mem_Q S (K_le_H S w hxK) q2
  have hne : ⁅K S w ⊓ S.Q, K S w ⊓ S.Q⁆ ≠ ⊥ := by
    intro hbot
    have hmem : ⁅⁅(q1 : G), x⁆, ⁅(q2 : G), x⁆⁆ ∈ ⁅K S w ⊓ S.Q, K S w ⊓ S.Q⁆ :=
      Subgroup.commutator_mem_commutator ⟨hq1K, hq1Q⟩ ⟨hq2K, hq2Q⟩
    rw [hbot] at hmem
    have h1 : ⁅⁅(q1 : G), x⁆, ⁅(q2 : G), x⁆⁆ = 1 := by simpa using hmem
    exact hnc ((commutatorElement_eq_one_iff_mul_comm).mp h1)
  have hcard_le : Nat.card ↥⁅K S w ⊓ S.Q, K S w ⊓ S.Q⁆ ≤ 2 := by
    calc Nat.card ↥⁅K S w ⊓ S.Q, K S w ⊓ S.Q⁆
        ≤ Nat.card ↥(Subgroup.zpowers S.z) := Subgroup.card_le_of_le hle
      _ = 2 := by rw [Nat.card_zpowers, S.ord_z]
  have hcard_gt : 1 < Nat.card ↥⁅K S w ⊓ S.Q, K S w ⊓ S.Q⁆ := by
    rw [Nat.one_lt_iff_ne_zero_and_ne_one]
    refine ⟨Nat.card_pos.ne', ?_⟩
    intro h1
    exact hne (Subgroup.card_eq_one.mp h1)
  have hcard : Nat.card ↥⁅K S w ⊓ S.Q, K S w ⊓ S.Q⁆ =
      Nat.card ↥(Subgroup.zpowers S.z) := by
    rw [show Nat.card ↥(Subgroup.zpowers S.z) = 2 by rw [Nat.card_zpowers, S.ord_z]]
    omega
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [hcard])

theorem twoCore_map_conj (K : Subgroup G) (y : G) :
    (twoCore K).map (MulAut.conj y).toMonoidHom =
      twoCore (K.map (MulAut.conj y).toMonoidHom) := by
  let e : K ≃* K.map (MulAut.conj y).toMonoidHom :=
    Subgroup.equivMapOfInjective K (MulAut.conj y).toMonoidHom (MulAut.conj y).injective
  have h := CFSG.pCore_map_iso 2 e
  ext x
  constructor
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨kG, hkG, rfl⟩
    rcases Subgroup.mem_map.mp hkG with ⟨k, hk, rfl⟩
    have hk' : e k ∈ CFSG.pCore 2 (K.map (MulAut.conj y).toMonoidHom) := by
      rw [← h]
      exact Subgroup.mem_map_of_mem e.toMonoidHom hk
    exact Subgroup.mem_map_of_mem (K.map (MulAut.conj y).toMonoidHom).subtype hk'
  · intro hx
    rcases Subgroup.mem_map.mp hx with ⟨k', hk', hk'_eq⟩
    have hk'' : k' ∈ (CFSG.pCore 2 K).map e.toMonoidHom := by
      rw [h]
      exact hk'
    rcases Subgroup.mem_map.mp hk'' with ⟨k, hk, hk_eq⟩
    refine Subgroup.mem_map.mpr ⟨(k : G), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem K.subtype hk
    · rw [← hk'_eq, ← hk_eq]
      rfl

theorem not_rho8p (S : ThSetting G) (e : S.toSetting.Qt ≃ₗ[ZMod 2] V8)
    (he : ∀ g v, e (S.rho g v) = rho8p g (e v)) : False := by
  obtain ⟨y, hy1, hy2, hy3⟩ := S.exists_conj_Q
  let k : G := y * S.z * y⁻¹
  have hkQ : k ∈ S.Q := hy2
  have hkz : k ≠ S.z := hy3
  have hzsq : S.z * S.z = 1 := by
    rw [← pow_two, ← S.ord_z, pow_orderOf_eq_one]
  have hk1 : k ≠ 1 := by
    intro h1
    have hz1 : S.z = 1 := by
      calc S.z = y⁻¹ * k * y := by dsimp [k]; group
        _ = 1 := by rw [h1]; group
    have hzord := S.ord_z
    rw [hz1, orderOf_one] at hzord
    norm_num at hzord
  have hk_not : k ∉ Subgroup.zpowers S.z := by
    intro h
    rcases (CFSG.LargeExtraspecial.Setting.mem_zpowers_iff_of_mul_self hzsq).mp h with h1 | h1
    · exact hk1 h1
    · exact hkz h1
  have hh0_1 : S.h₀ ≠ 1 := by
    intro h1
    have hord := S.orderOf_h₀
    rw [h1, orderOf_one] at hord
    norm_num at hord
  have hh0_not : S.h₀ ∉ Subgroup.zpowers S.z := by
    intro h
    rcases (CFSG.LargeExtraspecial.Setting.mem_zpowers_iff_of_mul_self hzsq).mp h with h1 | h1
    · exact hh0_1 h1
    · exact S.h₀_ne_z h1
  have hO2h0 : twoCore (K S S.h₀) = K S S.h₀ ⊓ S.Q :=
    twoCore_eq_inf S e he S.h₀_mem_Q hh0_not
  have hderh0 : ⁅K S S.h₀ ⊓ S.Q, K S S.h₀ ⊓ S.Q⁆ = Subgroup.zpowers S.z :=
    commutator_inf_eq_zpowers S e he S.h₀_mem_Q hh0_not
  have hO2k : twoCore (K S k) = K S k ⊓ S.Q :=
    twoCore_eq_inf S e he hkQ hk_not
  have hderk : ⁅K S k ⊓ S.Q, K S k ⊓ S.Q⁆ = Subgroup.zpowers S.z :=
    commutator_inf_eq_zpowers S e he hkQ hk_not
  have hKmap : (K S S.h₀).map (MulAut.conj y).toMonoidHom = K S k := by
    calc (K S S.h₀).map (MulAut.conj y).toMonoidHom
        = fiveClosure (y * S.z * y⁻¹) (y * S.h₀ * y⁻¹) := by
          rw [show K S S.h₀ = fiveClosure S.z S.h₀ from rfl, fiveClosure_map_conj]
      _ = fiveClosure k S.z := by rw [hy1]
      _ = fiveClosure S.z k := fiveClosure_comm k S.z
      _ = K S k := rfl
  have hO2map : (twoCore (K S S.h₀)).map (MulAut.conj y).toMonoidHom =
      twoCore (K S k) := by
    rw [twoCore_map_conj, hKmap]
  have hder_map : (⁅twoCore (K S S.h₀), twoCore (K S S.h₀)⁆).map
      (MulAut.conj y).toMonoidHom = ⁅twoCore (K S k), twoCore (K S k)⁆ := by
    rw [Subgroup.map_commutator, hO2map]
  have hderh0' : ⁅twoCore (K S S.h₀), twoCore (K S S.h₀)⁆ = Subgroup.zpowers S.z := by
    rw [hO2h0, hderh0]
  have hderk' : ⁅twoCore (K S k), twoCore (K S k)⁆ = Subgroup.zpowers S.z := by
    rw [hO2k, hderk]
  have hmapz : (Subgroup.zpowers S.z).map (MulAut.conj y).toMonoidHom =
      Subgroup.zpowers S.z := by
    calc (Subgroup.zpowers S.z).map (MulAut.conj y).toMonoidHom
        = (⁅twoCore (K S S.h₀), twoCore (K S S.h₀)⁆).map
            (MulAut.conj y).toMonoidHom := by rw [hderh0']
      _ = ⁅twoCore (K S k), twoCore (K S k)⁆ := hder_map
      _ = Subgroup.zpowers S.z := hderk'
  have hmapz' : (Subgroup.zpowers S.z).map (MulAut.conj y).toMonoidHom =
      Subgroup.zpowers k := by
    simpa [k] using MonoidHom.map_zpowers (MulAut.conj y).toMonoidHom S.z
  have hzp : Subgroup.zpowers k = Subgroup.zpowers S.z := hmapz'.symm.trans hmapz
  have hk_mem : k ∈ Subgroup.zpowers S.z := by
    rw [← hzp]
    exact Subgroup.mem_zpowers k
  exact hk_not hk_mem

end CFSG.Sporadic.Th.Recog

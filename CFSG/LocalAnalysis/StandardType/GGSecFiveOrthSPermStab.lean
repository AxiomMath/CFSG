module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthSPerm

public section

namespace CFSG.StandardType.OrthF3

@[expose] noncomputable def ggOrthStabSP {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (j : Fin n) : Subgroup (V ≃ₗ[ZMod 3] V) :=
  ggOrthSignedPerms f ⊓ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) (f j)

private lemma ct_s2_witness {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (g : ↥(ggOrthSignedPerms f)) :
    ∃ (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3),
      (∀ i, ε i = 1 ∨ ε i = -1) ∧ ∀ i, (g : V ≃ₗ[ZMod 3] V) (f i) = ε i • f (π i) := by
  simpa [ggOrthSignedPerms] using g.2

private lemma ct_s2_pm_ne_zero {s : ZMod 3} (h : s = 1 ∨ s = -1) : s ≠ 0 := by
  rcases h with rfl | rfl <;> decide

private noncomputable def ct_s2_perm {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (g : ↥(ggOrthSignedPerms f)) : Equiv.Perm (Fin n) :=
  Classical.choose (ct_s2_witness f g)

private noncomputable def ct_s2_sign {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (g : ↥(ggOrthSignedPerms f)) : Fin n → ZMod 3 :=
  Classical.choose (Classical.choose_spec (ct_s2_witness f g))

private lemma ct_s2_sign_spec {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (g : ↥(ggOrthSignedPerms f)) :
    ∀ i, ct_s2_sign f g i = 1 ∨ ct_s2_sign f g i = -1 :=
  (Classical.choose_spec (Classical.choose_spec (ct_s2_witness f g))).1

private lemma ct_s2_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (g : ↥(ggOrthSignedPerms f)) (i : Fin n) :
    (g : V ≃ₗ[ZMod 3] V) (f i) = ct_s2_sign f g i • f (ct_s2_perm f g i) :=
  (Classical.choose_spec (Classical.choose_spec (ct_s2_witness f g))).2 i

private lemma ct_s2_index_eq {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) {a b : Fin n} {sa sb : ZMod 3}
    (ha : sa = 1 ∨ sa = -1) (h : sa • f a = sb • f b) : a = b := by
  have hc : f.repr (sa • f a) = f.repr (sb • f b) := congrArg f.repr h
  rw [map_smul, map_smul, Module.Basis.repr_self, Module.Basis.repr_self] at hc
  have hca := congrArg (fun v : Fin n →₀ ZMod 3 => v a) hc
  simp only [Finsupp.smul_apply, smul_eq_mul, Finsupp.single_eq_same] at hca
  by_contra hne
  rw [Finsupp.single_eq_of_ne hne, mul_zero, mul_one] at hca
  exact ct_s2_pm_ne_zero ha hca

private lemma ct_s2_perm_eq_of_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (g : ↥(ggOrthSignedPerms f)) {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod 3} (_hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (h : ∀ i, (g : V ≃ₗ[ZMod 3] V) (f i) = ε i • f (π i)) :
    ct_s2_perm f g = π := by
  apply Equiv.ext
  intro i
  exact ct_s2_index_eq f (ct_s2_sign_spec f g i) (by rw [← ct_s2_apply f g i, h i])

private noncomputable def ct_s2_signed {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) : V ≃ₗ[ZMod 3] V :=
  f.equiv (f.unitsSMul fun k => Units.mk0 (ε (π.symm k)) (ct_s2_pm_ne_zero (hε (π.symm k)))) π

private lemma ct_s2_signed_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) (i : Fin n) :
    ct_s2_signed f π ε hε (f i) = ε i • f (π i) := by
  simp only [ct_s2_signed, Module.Basis.equiv_apply, Module.Basis.unitsSMul_apply,
    Units.smul_def, Equiv.symm_apply_apply]
  rfl

private lemma ct_s2_signed_mem {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ct_s2_signed f π ε hε ∈ ggOrthSignedPerms f := by
  refine ⟨π, ε, hε, fun i => ?_⟩
  exact ct_s2_signed_apply f π ε hε i

private lemma ct_s2_perm_signed {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ct_s2_perm f ⟨ct_s2_signed f π ε hε, ct_s2_signed_mem f π ε hε⟩ = π :=
  ct_s2_perm_eq_of_apply (f := f) (g := ⟨ct_s2_signed f π ε hε, ct_s2_signed_mem f π ε hε⟩)
    hε (fun i => ct_s2_signed_apply f π ε hε i)

private lemma ct_s2_sign_signed {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (π : Equiv.Perm (Fin n)) (ε : Fin n → ZMod 3)
    (hε : ∀ i, ε i = 1 ∨ ε i = -1) :
    ct_s2_sign f ⟨ct_s2_signed f π ε hε, ct_s2_signed_mem f π ε hε⟩ = ε := by
  funext i
  have h := ct_s2_apply f ⟨ct_s2_signed f π ε hε, ct_s2_signed_mem f π ε hε⟩ i
  rw [ct_s2_perm_signed f π ε hε, ct_s2_signed_apply f π ε hε i] at h
  have hc : f.repr (ε i • f (π i)) =
      f.repr (ct_s2_sign f ⟨ct_s2_signed f π ε hε, ct_s2_signed_mem f π ε hε⟩ i • f (π i)) :=
    congrArg f.repr h
  have hca := congrArg (fun v : Fin n →₀ ZMod 3 => v (π i)) hc
  simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_eq_same, mul_one] using hca.symm

private lemma ct_s2_inv_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (g : ↥(ggOrthSignedPerms f)) (k : Fin n) :
    (g : V ≃ₗ[ZMod 3] V)⁻¹ (f k) =
      (ct_s2_sign f g ((ct_s2_perm f g).symm k))⁻¹ • f ((ct_s2_perm f g).symm k) := by
  set m := (ct_s2_perm f g).symm k
  have h : (g : V ≃ₗ[ZMod 3] V) (f m) = ct_s2_sign f g m • f k := by
    rw [ct_s2_apply f g m]
    congr 1
    rw [Equiv.apply_symm_apply]
  have key : (ct_s2_sign f g m)⁻¹ • f m = (g : V ≃ₗ[ZMod 3] V)⁻¹ (f k) := by
    calc (ct_s2_sign f g m)⁻¹ • f m
        = (ct_s2_sign f g m)⁻¹ • ((g : V ≃ₗ[ZMod 3] V)⁻¹ ((g : V ≃ₗ[ZMod 3] V) (f m))) := by
          congr 1
          exact (LinearEquiv.symm_apply_apply (g : V ≃ₗ[ZMod 3] V) (f m)).symm
      _ = (ct_s2_sign f g m)⁻¹ • ((g : V ≃ₗ[ZMod 3] V)⁻¹ (ct_s2_sign f g m • f k)) := by
          rw [h]
      _ = (ct_s2_sign f g m)⁻¹ • (ct_s2_sign f g m • (g : V ≃ₗ[ZMod 3] V)⁻¹ (f k)) := by
          rw [map_smul]
      _ = ((ct_s2_sign f g m)⁻¹ * ct_s2_sign f g m) • (g : V ≃ₗ[ZMod 3] V)⁻¹ (f k) := by
          rw [smul_smul]
      _ = (g : V ≃ₗ[ZMod 3] V)⁻¹ (f k) := by
          rw [inv_mul_cancel₀ (ct_s2_pm_ne_zero (ct_s2_sign_spec f g m)), one_smul]
  exact key.symm

private lemma ct_s2_conj_signChange {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (g : ↥(ggOrthSignedPerms f)) (i : Fin n) :
    (g : V ≃ₗ[ZMod 3] V) * ggOrthSignChange f i * (g : V ≃ₗ[ZMod 3] V)⁻¹ =
      ggOrthSignChange f (ct_s2_perm f g i) := by
  apply f.ext'
  intro k
  change (g : V ≃ₗ[ZMod 3] V) (ggOrthSignChange f i ((g : V ≃ₗ[ZMod 3] V)⁻¹ (f k))) =
    ggOrthSignChange f (ct_s2_perm f g i) (f k)
  by_cases hk : k = ct_s2_perm f g i
  · subst hk
    have hinv : (g : V ≃ₗ[ZMod 3] V)⁻¹ (f (ct_s2_perm f g i)) =
        (ct_s2_sign f g i)⁻¹ • f i := by
      rw [ct_s2_inv_apply f g (ct_s2_perm f g i), Equiv.symm_apply_apply]
    rw [hinv, map_smul, ggOrthSignChange_apply_self, ggOrthSignChange_apply_self]
    rw [map_smul, map_neg, ct_s2_apply f g i, smul_neg, smul_smul,
      inv_mul_cancel₀ (ct_s2_pm_ne_zero (ct_s2_sign_spec f g i)), one_smul]
  · rw [ggOrthSignChange_apply_of_ne f hk]
    have hm : (ct_s2_perm f g).symm k ≠ i := by
      intro hmi
      exact hk (by rw [← hmi, Equiv.apply_symm_apply])
    rw [ct_s2_inv_apply f g k, map_smul,
      ggOrthSignChange_apply_of_ne f hm, map_smul, ct_s2_apply f g ((ct_s2_perm f g).symm k)]
    rw [smul_smul, inv_mul_cancel₀ (ct_s2_pm_ne_zero (ct_s2_sign_spec f g _)), one_smul]
    congr 1
    exact Equiv.apply_symm_apply (ct_s2_perm f g) k

private lemma ct_s2_coord_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (a : ↥(ggOrthSignedPerms f)) (j : Fin n) :
    (f.coord (ct_s2_perm f a j)).comp (a : V →ₗ[ZMod 3] V) =
      ct_s2_sign f a j • f.coord j := by
  apply f.ext
  intro i
  rw [LinearMap.comp_apply, LinearEquiv.coe_coe, ct_s2_apply f a i, map_smul,
    LinearMap.smul_apply, smul_eq_mul]
  simp only [Module.Basis.coord_apply, Module.Basis.repr_self,
    smul_eq_mul, Finsupp.single_apply]
  by_cases h : i = j
  · subst h
    simp
  · have hπ : ct_s2_perm f a i ≠ ct_s2_perm f a j :=
      fun hh => h ((ct_s2_perm f a).injective hh)
    simp [h, hπ]

private lemma ct_s2_coord_perm {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (a : ↥(ggOrthSignedPerms f)) {u : V}
    (hu : (a : V ≃ₗ[ZMod 3] V) u = u) (j : Fin n) :
    f.repr u (ct_s2_perm f a j) = ct_s2_sign f a j * f.repr u j := by
  have h := LinearMap.congr_fun (ct_s2_coord_apply f a j) u
  rw [LinearMap.comp_apply, LinearMap.smul_apply, smul_eq_mul] at h
  rw [show (a : V →ₗ[ZMod 3] V) u = u from hu] at h
  simpa only [Module.Basis.coord_apply] using h

private lemma ct_s2_stabSP_iff {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Module.Basis (Fin 5) (ZMod 3) V) (j : Fin 5) (g : ↥(ggOrthSignedPerms f)) :
    (g : V ≃ₗ[ZMod 3] V) ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) (f j) ↔
      ct_s2_perm f g j = j ∧ ct_s2_sign f g j = 1 := by
  rw [MulAction.mem_stabilizer_iff]
  constructor
  · intro h
    have hh : (g : V ≃ₗ[ZMod 3] V) (f j) = f j := by simpa [LinearEquiv.smul_def] using h
    have h1 : ct_s2_sign f g j • f (ct_s2_perm f g j) = (1 : ZMod 3) • f j :=
      (ct_s2_apply f g j).symm.trans (hh.trans (one_smul (ZMod 3) (f j)).symm)
    have hp : ct_s2_perm f g j = j := ct_s2_index_eq f (ct_s2_sign_spec f g j) h1
    refine ⟨hp, ?_⟩
    rw [hp] at h1
    have hs : (ct_s2_sign f g j - 1) • f j = 0 := by
      rw [sub_smul, h1, one_smul, sub_self]
    exact sub_eq_zero.mp ((smul_eq_zero.mp hs).resolve_right (Module.Basis.ne_zero f j))
  · rintro ⟨hp, hε⟩
    rw [LinearEquiv.smul_def, ct_s2_apply f g j, hp, hε, one_smul]

private noncomputable def ct_s2_toSigned {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Module.Basis (Fin 5) (ZMod 3) V) (j : Fin 5) (g : ↥(ggOrthStabSP f j)) :
    ↥(ggOrthSignedPerms f) :=
  ⟨(g : V ≃ₗ[ZMod 3] V), (Subgroup.mem_inf.mp (by
    simpa only [ggOrthStabSP] using g.2)).1⟩

private lemma ct_s2_toSigned_mem_stab {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Module.Basis (Fin 5) (ZMod 3) V) (j : Fin 5) (g : ↥(ggOrthStabSP f j)) :
    (ct_s2_toSigned f j g : V ≃ₗ[ZMod 3] V) ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) (f j) :=
  (Subgroup.mem_inf.mp (by simpa only [ggOrthStabSP, ct_s2_toSigned] using g.2)).2

private lemma ct_s2_sign_eq_of_apply {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) (g : ↥(ggOrthSignedPerms f)) {π : Equiv.Perm (Fin n)}
    {ε : Fin n → ZMod 3} (hε : ∀ i, ε i = 1 ∨ ε i = -1)
    (h : ∀ i, (g : V ≃ₗ[ZMod 3] V) (f i) = ε i • f (π i)) :
    ct_s2_sign f g = ε := by
  have hp := ct_s2_perm_eq_of_apply f g hε h
  funext i
  have h1 : ct_s2_sign f g i • f (ct_s2_perm f g i) = ε i • f (π i) := by
    rw [← ct_s2_apply f g i, h i]
  rw [hp] at h1
  have hc : f.repr (ct_s2_sign f g i • f (π i)) = f.repr (ε i • f (π i)) := congrArg f.repr h1
  have hca := congrArg (fun v : Fin n →₀ ZMod 3 => v (π i)) hc
  simpa only [map_smul, Module.Basis.repr_self, Finsupp.smul_apply, smul_eq_mul,
    Finsupp.single_eq_same, mul_one] using hca

private noncomputable def ct_s2_ofPair {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Module.Basis (Fin 5) (ZMod 3) V) (j : Fin 5)
    (p : {π : Equiv.Perm (Fin 5) // π j = j} ×
      {ε : Fin 5 → ZMod 3 // (∀ i, ε i = 1 ∨ ε i = -1) ∧ ε j = 1}) :
    ↥(ggOrthStabSP f j) :=
  let e := p.2.1
  let he := p.2.2.1
  let g₀ := ct_s2_signed f p.1.1 e he
  let hmem := ct_s2_signed_mem f p.1.1 e he
  ⟨g₀, by
    show g₀ ∈ ggOrthStabSP f j
    rw [ggOrthStabSP]
    refine Subgroup.mem_inf.mpr ⟨hmem, ?_⟩
    rw [ct_s2_stabSP_iff f j ⟨g₀, hmem⟩]
    exact ⟨by rw [ct_s2_perm_signed f p.1.1 e he]; exact p.1.2,
      by rw [ct_s2_sign_signed f p.1.1 e he]; exact p.2.2.2⟩⟩

private noncomputable def ct_s2_stabEquiv {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Module.Basis (Fin 5) (ZMod 3) V) (j : Fin 5) :
    ↥(ggOrthStabSP f j) ≃
      ({π : Equiv.Perm (Fin 5) // π j = j} ×
        {ε : Fin 5 → ZMod 3 // (∀ i, ε i = 1 ∨ ε i = -1) ∧ ε j = 1}) where
  toFun g :=
    have hstab : (ct_s2_toSigned f j g : V ≃ₗ[ZMod 3] V) ∈
        MulAction.stabilizer (V ≃ₗ[ZMod 3] V) (f j) :=
      ct_s2_toSigned_mem_stab f j g
    have h := (ct_s2_stabSP_iff f j (ct_s2_toSigned f j g)).mp hstab
    (⟨ct_s2_perm f (ct_s2_toSigned f j g), h.1⟩,
      ⟨ct_s2_sign f (ct_s2_toSigned f j g), ct_s2_sign_spec f (ct_s2_toSigned f j g), h.2⟩)
  invFun := ct_s2_ofPair f j
  left_inv g := by
    apply Subtype.ext
    apply f.ext'
    intro i
    show ct_s2_signed f (ct_s2_perm f (ct_s2_toSigned f j g))
        (ct_s2_sign f (ct_s2_toSigned f j g))
        (ct_s2_sign_spec f (ct_s2_toSigned f j g)) (f i) =
      (ct_s2_toSigned f j g : V ≃ₗ[ZMod 3] V) (f i)
    rw [ct_s2_signed_apply, ct_s2_apply]
  right_inv p := by
    apply Prod.ext
    · apply Subtype.ext
      exact ct_s2_perm_eq_of_apply (f := f) (g := ct_s2_toSigned f j (ct_s2_ofPair f j p))
        (π := p.1.1) (ε := p.2.1) p.2.2.1
        (fun i => ct_s2_signed_apply f p.1.1 p.2.1 p.2.2.1 i)
    · apply Subtype.ext
      exact ct_s2_sign_eq_of_apply (f := f) (g := ct_s2_toSigned f j (ct_s2_ofPair f j p))
        (π := p.1.1) (ε := p.2.1) p.2.2.1
        (fun i => ct_s2_signed_apply f p.1.1 p.2.1 p.2.2.1 i)

theorem card_ggOrthStabSP {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Module.Basis (Fin 5) (ZMod 3) V) (j : Fin 5) : Nat.card ↥(ggOrthStabSP f j) = 384 := by
  rw [Nat.card_congr (ct_s2_stabEquiv f j), Nat.card_prod]
  have h1 : Nat.card {π : Equiv.Perm (Fin 5) // π j = j} = 24 := by
    rw [Nat.card_eq_fintype_card]
    fin_cases j <;> decide
  have h2 : Nat.card {ε : Fin 5 → ZMod 3 // (∀ i, ε i = 1 ∨ ε i = -1) ∧ ε j = 1} = 16 := by
    rw [Nat.card_eq_fintype_card]
    fin_cases j <;> decide
  rw [h1, h2]

theorem ggOrthSignChange_mem_stabSP {V : Type} [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ}
    (f : Module.Basis (Fin n) (ZMod 3) V) {i j : Fin n} (h : i ≠ j) :
    ggOrthSignChange f i ∈ ggOrthStabSP f j := by
  rw [ggOrthStabSP, Subgroup.mem_inf]
  refine ⟨ggOrthSignChange_mem f i, ?_⟩
  rw [MulAction.mem_stabilizer_iff]
  simpa [LinearEquiv.smul_def] using ggOrthSignChange_apply_of_ne f (Ne.symm h)

private lemma ct_s2_conj_eq_signChange {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Module.Basis (Fin 5) (ZMod 3) V) {i j : Fin 5} (h : i ≠ j)
    (c : ↥(ggOrthStabSP f j)) :
    ∃ k : Fin 5, k ≠ j ∧
      (c : V ≃ₗ[ZMod 3] V) * ggOrthSignChange f i * (c : V ≃ₗ[ZMod 3] V)⁻¹ =
        ggOrthSignChange f k := by
  let c' : ↥(ggOrthSignedPerms f) := ⟨(c : V ≃ₗ[ZMod 3] V), (Subgroup.mem_inf.mp c.2).1⟩
  have hstab : (c' : V ≃ₗ[ZMod 3] V) ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) (f j) :=
    (Subgroup.mem_inf.mp c.2).2
  have hpj : ct_s2_perm f c' j = j := ((ct_s2_stabSP_iff f j c').mp hstab).1
  refine ⟨ct_s2_perm f c' i, ?_, ?_⟩
  · intro hk
    exact h ((ct_s2_perm f c').injective (by rw [hk, hpj]))
  · exact ct_s2_conj_signChange f c' i

theorem card_conj_ggOrthSignChange {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Module.Basis (Fin 5) (ZMod 3) V) {i j : Fin 5} (h : i ≠ j) (φ : ↥(ggOrthStabSP f j))
    (hφ : (φ : V ≃ₗ[ZMod 3] V) = ggOrthSignChange f i) :
    Nat.card {ψ : ↥(ggOrthStabSP f j) // IsConj φ ψ} = 4 := by
  classical
  let F : {k : Fin 5 // k ≠ j} → {ψ : ↥(ggOrthStabSP f j) // IsConj φ ψ} := fun k =>
    ⟨⟨ggOrthSignChange f k.1, ggOrthSignChange_mem_stabSP f k.2⟩, by
      let c := ct_s2_signed f (Equiv.swap i k.1) (fun _ => (1 : ZMod 3)) (fun _ => Or.inl rfl)
      have hmemSP : c ∈ ggOrthSignedPerms f :=
        ct_s2_signed_mem f (Equiv.swap i k.1) (fun _ => (1 : ZMod 3)) (fun _ => Or.inl rfl)
      have hperm : ct_s2_perm f ⟨c, hmemSP⟩ = Equiv.swap i k.1 :=
        ct_s2_perm_signed f (Equiv.swap i k.1) (fun _ => (1 : ZMod 3)) (fun _ => Or.inl rfl)
      have hsign : ct_s2_sign f ⟨c, hmemSP⟩ = fun _ => (1 : ZMod 3) :=
        ct_s2_sign_signed f (Equiv.swap i k.1) (fun _ => (1 : ZMod 3)) (fun _ => Or.inl rfl)
      have hstab : c ∈ MulAction.stabilizer (V ≃ₗ[ZMod 3] V) (f j) := by
        rw [ct_s2_stabSP_iff f j ⟨c, hmemSP⟩]
        refine ⟨?_, ?_⟩
        · rw [hperm]
          exact Equiv.swap_apply_of_ne_of_ne (Ne.symm h) (Ne.symm k.2)
        · rw [hsign]
      let cStab : ↥(ggOrthStabSP f j) := ⟨c, Subgroup.mem_inf.mpr ⟨hmemSP, hstab⟩⟩
      refine isConj_iff.mpr ⟨cStab, ?_⟩
      apply Subtype.ext
      show (cStab : V ≃ₗ[ZMod 3] V) * (φ : V ≃ₗ[ZMod 3] V) *
          (cStab : V ≃ₗ[ZMod 3] V)⁻¹ = ggOrthSignChange f k.1
      rw [hφ]
      have hconj := ct_s2_conj_signChange f ⟨c, hmemSP⟩ i
      rw [hperm, Equiv.swap_apply_left] at hconj
      simpa using hconj⟩
  have hinj : Function.Injective F := by
    intro k k' hkk'
    have hval : ggOrthSignChange f k.1 = ggOrthSignChange f k'.1 :=
      congrArg (fun x => ((x.1 : ↥(ggOrthStabSP f j)) : V ≃ₗ[ZMod 3] V)) hkk'
    by_contra hne
    have hkne : k.1 ≠ k'.1 := fun hh => hne (Subtype.ext hh)
    have h := congrArg (fun e : V ≃ₗ[ZMod 3] V => e (f k.1)) hval
    rw [ggOrthSignChange_apply_self f k.1,
      ggOrthSignChange_apply_of_ne f (i := k'.1) (j := k.1) hkne] at h
    have hc : (-1 : ZMod 3) = 1 := by
      simpa only [map_neg, Module.Basis.repr_self, Finsupp.neg_apply, Finsupp.single_eq_same]
        using congrArg (fun x => f.repr x k.1) h
    exact absurd hc (by decide)
  have hsurj : Function.Surjective F := by
    rintro ⟨ψ, hψ⟩
    rw [isConj_iff] at hψ
    obtain ⟨c, hc⟩ := hψ
    have hc' : (c : V ≃ₗ[ZMod 3] V) * (φ : V ≃ₗ[ZMod 3] V) * (c : V ≃ₗ[ZMod 3] V)⁻¹ =
        (ψ : V ≃ₗ[ZMod 3] V) := by
      have h := congrArg (fun x : ↥(ggOrthStabSP f j) => (x : V ≃ₗ[ZMod 3] V)) hc
      simpa using h
    rw [hφ] at hc'
    obtain ⟨k, hk, hk_eq⟩ := ct_s2_conj_eq_signChange f h c
    refine ⟨⟨k, hk⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    exact hk_eq.symm.trans hc'
  have hbij : Function.Bijective F := ⟨hinj, hsurj⟩
  rw [← Nat.card_congr (Equiv.ofBijective F hbij)]
  rw [Nat.card_eq_fintype_card]
  fin_cases j <;> decide

private lemma ct_s2_zmod3_ne_zero_eq_pm : ∀ c : ZMod 3, c ≠ 0 → c = 1 ∨ c = -1 := by decide

private noncomputable def ct_s2_setStabInj (S : Finset (Fin 5)) :
    {π : Equiv.Perm (Fin 5) // ∀ i, i ∈ S ↔ π i ∈ S} →
      Equiv.Perm {i : Fin 5 // i ∈ S} × Equiv.Perm {i : Fin 5 // i ∉ S} :=
  fun π => (π.1.subtypePerm (fun i => (π.2 i).symm),
    π.1.subtypePerm (fun i => (not_iff_not.mpr (π.2 i)).symm))

private lemma ct_s2_setStabInj_injective (S : Finset (Fin 5)) :
    Function.Injective (ct_s2_setStabInj S) := by
  intro x y hxy
  apply Subtype.ext
  apply Equiv.ext
  intro i
  by_cases hi : i ∈ S
  · have h := congrArg (fun z => ((z.1 ⟨i, hi⟩ : {i : Fin 5 // i ∈ S}) : Fin 5)) hxy
    simpa [ct_s2_setStabInj] using h
  · have h := congrArg (fun z => ((z.2 ⟨i, hi⟩ : {i : Fin 5 // i ∉ S}) : Fin 5)) hxy
    simpa [ct_s2_setStabInj] using h

private lemma ct_s2_card_setStab_le (S : Finset (Fin 5)) :
    Nat.card {π : Equiv.Perm (Fin 5) // ∀ i, i ∈ S ↔ π i ∈ S} ≤
      S.card.factorial * (5 - S.card).factorial := by
  have hαf : Fintype.card {i : Fin 5 // i ∈ S} = S.card := by
    rw [Fintype.card_subtype]; simp
  have hβf : Fintype.card {i : Fin 5 // i ∉ S} = 5 - S.card := by
    rw [Fintype.card_subtype_compl (fun i => i ∈ S), Fintype.card_fin, hαf]
  have hα : Nat.card {i : Fin 5 // i ∈ S} = S.card := by
    rw [Nat.card_eq_fintype_card, hαf]
  have hβ : Nat.card {i : Fin 5 // i ∉ S} = 5 - S.card := by
    rw [Nat.card_eq_fintype_card, hβf]
  have hpα : Nat.card (Equiv.Perm {i : Fin 5 // i ∈ S}) = S.card.factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hαf]
  have hpβ : Nat.card (Equiv.Perm {i : Fin 5 // i ∉ S}) = (5 - S.card).factorial := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, hβf]
  have h := Nat.card_le_card_of_injective (ct_s2_setStabInj S) (ct_s2_setStabInj_injective S)
  refine h.trans ?_
  rw [Nat.card_prod, hpα, hpβ]

private lemma ct_s2_card_compl_signs (S : Finset (Fin 5)) :
    Nat.card ({i : Fin 5 // i ∉ S} → (ZMod 3)ˣ) = 2 ^ (5 - S.card) := by
  rw [Nat.card_fun]
  congr 1
  · rw [Nat.card_eq_fintype_card]; decide
  · rw [Nat.card_eq_fintype_card, Fintype.card_subtype_compl (fun i => i ∈ S),
      Fintype.card_fin]
    have hαf : Fintype.card {i : Fin 5 // i ∈ S} = S.card := by
      rw [Fintype.card_subtype]; simp
    rw [hαf]

private noncomputable def ct_s2_AtoProd {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Module.Basis (Fin 5) (ZMod 3) V) {A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hA : A ≤ ggOrthSignedPerms f) {u : V} (hfix : ∀ a ∈ A, a u = u) (S : Finset (Fin 5))
    (hS : ∀ i, i ∈ S ↔ f.repr u i ≠ 0) :
    ↥A → ({π : Equiv.Perm (Fin 5) // ∀ i, i ∈ S ↔ π i ∈ S} ×
      ({i : Fin 5 // i ∉ S} → (ZMod 3)ˣ)) := fun a =>
  let a' : ↥(ggOrthSignedPerms f) := ⟨a.1, hA a.2⟩
  have hc := ct_s2_coord_perm f a' (hfix a a.2)
  (⟨ct_s2_perm f a', fun i => by
      rw [hS i, hS (ct_s2_perm f a' i), hc i, mul_ne_zero_iff]
      exact ⟨fun h => ⟨ct_s2_pm_ne_zero (ct_s2_sign_spec f a' i), h⟩, fun h => h.2⟩⟩,
    fun i => Units.mk0 (ct_s2_sign f a' i.1)
      (ct_s2_pm_ne_zero (ct_s2_sign_spec f a' i.1)))

private lemma ct_s2_AtoProd_injective {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Module.Basis (Fin 5) (ZMod 3) V) {A : Subgroup (V ≃ₗ[ZMod 3] V)}
    (hA : A ≤ ggOrthSignedPerms f) {u : V} (hfix : ∀ a ∈ A, a u = u) (S : Finset (Fin 5))
    (hS : ∀ i, i ∈ S ↔ f.repr u i ≠ 0) :
    Function.Injective (ct_s2_AtoProd f hA hfix S hS) := by
  intro a b hab
  let a' : ↥(ggOrthSignedPerms f) := ⟨a.1, hA a.2⟩
  let b' : ↥(ggOrthSignedPerms f) := ⟨b.1, hA b.2⟩
  have hperm : ct_s2_perm f a' = ct_s2_perm f b' :=
    congrArg (fun x => x.1.1) hab
  have hsign_off : ∀ i (hi : i ∉ S), ct_s2_sign f a' i = ct_s2_sign f b' i := by
    intro i hi
    have h := congrArg (fun x => ((x.2 ⟨i, hi⟩ : (ZMod 3)ˣ) : ZMod 3)) hab
    simpa only [ct_s2_AtoProd, Units.val_mk0] using h
  have hsign : ct_s2_sign f a' = ct_s2_sign f b' := by
    funext i
    by_cases hi : i ∈ S
    · have hca := ct_s2_coord_perm f a' (hfix a a.2) i
      have hcb := ct_s2_coord_perm f b' (hfix b b.2) i
      rw [← hperm] at hcb
      have hci : f.repr u i ≠ 0 := (hS i).mp hi
      have heq : ct_s2_sign f a' i * f.repr u i = ct_s2_sign f b' i * f.repr u i := by
        rw [← hca, ← hcb]
      exact mul_right_cancel₀ hci heq
    · exact hsign_off i hi
  apply Subtype.ext
  show (a' : V ≃ₗ[ZMod 3] V) = (b' : V ≃ₗ[ZMod 3] V)
  apply f.ext'
  intro i
  rw [ct_s2_apply f a' i, ct_s2_apply f b' i, hperm, hsign]

theorem ggOrthSP_exists_eq_pm_basis_of_fixed {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (f : Module.Basis (Fin 5) (ZMod 3) V) {A : Subgroup (V ≃ₗ[ZMod 3] V)} (hA : A ≤ ggOrthSignedPerms f)
    (hcard : 120 < Nat.card ↥A) {u : V} (hu : u ≠ 0) (hfix : ∀ a ∈ A, a u = u) :
    ∃ j : Fin 5, u = f j ∨ u = -f j := by
  classical
  let S : Finset (Fin 5) := Finset.univ.filter (fun i => f.repr u i ≠ 0)
  have hS : ∀ i, i ∈ S ↔ f.repr u i ≠ 0 := by
    intro i; simp [S]
  have hspos : 0 < S.card := by
    rw [Finset.card_pos]
    by_contra hemp
    have : u = 0 := by
      rw [← Module.Basis.sum_repr f u]
      apply Finset.sum_eq_zero
      intro i _
      have hci : f.repr u i = 0 := by
        by_contra hc
        exact hemp ⟨i, (hS i).mpr hc⟩
      rw [hci, zero_smul]
    exact hu this
  by_cases h1 : S.card = 1
  · obtain ⟨j, hSsing⟩ := Finset.card_eq_one.mp h1
    have hcsj : f.repr u j ≠ 0 := (hS j).mp (by rw [hSsing]; simp)
    have hu_eq : u = f.repr u j • f j := by
      conv_lhs => rw [← Module.Basis.sum_repr f u]
      refine Finset.sum_eq_single j ?_ ?_
      · intro i _ hi
        have hci : f.repr u i = 0 := by
          by_contra hc
          have his : i ∈ S := (hS i).mpr hc
          rw [hSsing] at his
          exact hi (by simpa using his)
        rw [hci, zero_smul]
      · intro hj; exact absurd (Finset.mem_univ j) hj
    rcases ct_s2_zmod3_ne_zero_eq_pm (f.repr u j) hcsj with hc | hc
    · exact ⟨j, Or.inl (by rw [hu_eq, hc, one_smul])⟩
    · exact ⟨j, Or.inr (by rw [hu_eq, hc, neg_one_smul])⟩
  · have hs2 : 2 ≤ S.card := by omega
    have hbound : Nat.card ↥A ≤ 120 := by
      let T := ({π : Equiv.Perm (Fin 5) // ∀ i, i ∈ S ↔ π i ∈ S} ×
          ({i : Fin 5 // i ∉ S} → (ZMod 3)ˣ))
      have hle := Nat.card_le_card_of_injective (ct_s2_AtoProd f hA hfix S hS)
        (ct_s2_AtoProd_injective f hA hfix S hS)
      have hT1 := ct_s2_card_setStab_le S
      have hT2 := ct_s2_card_compl_signs S
      have hSle : S.card ≤ 5 := by simpa using Finset.card_le_univ S
      calc Nat.card ↥A ≤ Nat.card T := hle
        _ = Nat.card {π : Equiv.Perm (Fin 5) // ∀ i, i ∈ S ↔ π i ∈ S} *
              Nat.card ({i : Fin 5 // i ∉ S} → (ZMod 3)ˣ) := by
            dsimp only [T]; rw [Nat.card_prod]
        _ ≤ (S.card.factorial * (5 - S.card).factorial) * 2 ^ (5 - S.card) :=
            Nat.mul_le_mul hT1 (le_of_eq hT2)
        _ ≤ 120 := by
            have hcases : S.card = 2 ∨ S.card = 3 ∨ S.card = 4 ∨ S.card = 5 := by omega
            rcases hcases with h | h | h | h <;> rw [h] <;> decide
    exact absurd hbound (not_le.mpr hcard)

end CFSG.StandardType.OrthF3

end

module

public import CFSG.Quasithin.Recognition.Stroth.WeissDelta.LocalFacts

public section

open scoped Pointwise commutatorElement

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.Stroth CFSG.Geometry.GeneralizedPolygons
  CFSG.GH74.GLS.SP CFSG.GH74.BNPair CFSG.QuasithinUnique
  CFSG.Quasithin.H13.F431.TwoF4 CFSG.Quasithin.H13.F431.Un
  CFSG.LieType.Ree.ReeTag CFSG.LieType.Universal.Unitary CFSG.LieType.BorelTits

namespace CFSG.Quasithin.Stroth.WeissDelta

variable {V : Type} {Γ : SimpleGraph V} {H : Type} [Group H] [MulAction H V] [GraphAction H Γ]

variable (H) in
@[expose] noncomputable def localGroup (Γ : SimpleGraph V) [GraphAction H Γ] (z : V) :
    Subgroup (Equiv.Perm {w : V // Γ.Adj z w}) :=
  (localPermHom (H := H) Γ z).range

variable (H) in
@[expose] def IsLocalL2 (Γ : SimpleGraph V) [GraphAction H Γ] (z : V) (m : ℕ) : Prop :=
  Nat.card {w : V // Γ.Adj z w} = 2 ^ m + 1 ∧
    MulAction.IsMultiplyPretransitive ↥(localGroup H Γ z) {w : V // Γ.Adj z w} 2 ∧
    ∃ N : Subgroup ↥(localGroup H Γ z), N.Normal ∧
      Nonempty (↥N ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 m))

variable (H) in
@[expose] def IsLocalSz (Γ : SimpleGraph V) [GraphAction H Γ] (z : V) (a : ℕ) : Prop :=
  Nat.card {w : V // Γ.Adj z w} = 2 ^ (2 * (2 * a + 1)) + 1 ∧
    MulAction.IsMultiplyPretransitive ↥(localGroup H Γ z) {w : V // Γ.Adj z w} 2 ∧
    ∃ N : Subgroup ↥(localGroup H Γ z), N.Normal ∧ Nonempty (↥N ≃* Sz a)

variable (H) in
@[expose] def IsLocalU3 (Γ : SimpleGraph V) [GraphAction H Γ] (z : V) (k : ℕ) (F : Type)
    [Field F] : Prop :=
  Nat.card {w : V // Γ.Adj z w} = 2 ^ (3 * k) + 1 ∧
    MulAction.IsMultiplyPretransitive ↥(localGroup H Γ z) {w : V // Γ.Adj z w} 2 ∧
    ∃ N : Subgroup ↥(localGroup H Γ z), N.Normal ∧
      Nonempty (↥N ≃* StatedProj (StatedSU 3 (2 ^ k) F))

private noncomputable def neighborEquiv (g : H) (z : V) :
    {w : V // Γ.Adj z w} ≃ {w : V // Γ.Adj (g • z) w} where
  toFun w := ⟨g • w.1, (GraphAction.adj_smul g z w.1).mpr w.2⟩
  invFun w := ⟨g⁻¹ • w.1, by
    have h : Γ.Adj (g⁻¹ • (g • z)) (g⁻¹ • w.1) :=
      (GraphAction.adj_smul g⁻¹ (g • z) w.1).mpr w.2
    simpa using h⟩
  left_inv w := Subtype.ext (by simp)
  right_inv w := Subtype.ext (by simp)

theorem localPermHom_apply (z : V) (x : ↥(MulAction.stabilizer H z))
    (w : {w : V // Γ.Adj z w}) :
    (localPermHom (H := H) Γ z x) w =
      (⟨(x : H) • w.1, by
        have h := (GraphAction.adj_smul (x : H) z w.1).mpr w.2
        rwa [MulAction.mem_stabilizer_iff.mp x.2] at h⟩ : {w : V // Γ.Adj z w}) :=
  rfl

private theorem localPermHom_conj (g : H) (z : V)
    (x : ↥(MulAction.stabilizer H z)) :
    localPermHom (H := H) Γ (g • z)
        (MulAction.stabilizerEquivStabilizer (rfl : g • z = g • z) x) =
      (neighborEquiv (H := H) (Γ := Γ) g z).permCongrHom
        (localPermHom (H := H) Γ z x) := by
  ext w
  rw [Equiv.permCongrHom_coe, Equiv.permCongr_apply]
  rw [localPermHom_apply, localPermHom_apply]
  simp [neighborEquiv, MulAction.stabilizerEquivStabilizer_apply, Equiv.Perm.smul_def,
    mul_smul, MulAut.conj_apply]

private theorem localGroup_smul (g : H) (z : V) :
    localGroup H Γ (g • z) =
      (localGroup H Γ z).map
        ((neighborEquiv (H := H) (Γ := Γ) g z).permCongrHom.toMonoidHom) := by
  let e := neighborEquiv (H := H) (Γ := Γ) g z
  let cg : ↥(MulAction.stabilizer H z) ≃* ↥(MulAction.stabilizer H (g • z)) :=
    MulAction.stabilizerEquivStabilizer (rfl : g • z = g • z)
  let f : Equiv.Perm {w : V // Γ.Adj z w} →* Equiv.Perm {w : V // Γ.Adj (g • z) w} :=
    e.permCongrHom.toMonoidHom
  ext p
  constructor
  · intro hp
    rcases hp with ⟨a, rfl⟩
    refine Subgroup.mem_map.mpr ⟨localPermHom (H := H) Γ z (cg.symm a),
      ⟨cg.symm a, rfl⟩, ?_⟩
    have h : localPermHom (H := H) Γ (g • z) (cg (cg.symm a)) =
        e.permCongrHom (localPermHom (H := H) Γ z (cg.symm a)) := by
      simpa [cg] using localPermHom_conj (H := H) (Γ := Γ) g z (cg.symm a)
    rw [MulEquiv.apply_symm_apply] at h
    simpa using h.symm
  · intro hp
    rcases Subgroup.mem_map.mp hp with ⟨q, hq, hqp⟩
    rcases hq with ⟨x, rfl⟩
    refine ⟨cg x, ?_⟩
    have h : localPermHom (H := H) Γ (g • z) (cg x) =
        e.permCongrHom (localPermHom (H := H) Γ z x) := by
      simpa [cg] using localPermHom_conj (H := H) (Γ := Γ) g z x
    rw [h]
    simpa [f] using hqp

private noncomputable def localGroupConj (g : H) (z : V) :
    ↥(localGroup H Γ z) ≃* ↥(localGroup H Γ (g • z)) :=
  (MulEquiv.subgroupMap ((neighborEquiv (H := H) (Γ := Γ) g z).permCongrHom)
    (localGroup H Γ z)).trans
    (MulEquiv.subgroupCongr (localGroup_smul (H := H) (Γ := Γ) g z).symm)

private theorem localGroupConj_coe (g : H) (z : V) (x : ↥(localGroup H Γ z)) :
    ((localGroupConj (H := H) (Γ := Γ) g z x :
        ↥(localGroup H Γ (g • z))) : Equiv.Perm _) =
      (neighborEquiv (H := H) (Γ := Γ) g z).permCongrHom (x : Equiv.Perm _) :=
  rfl

private theorem card_neighbor_smul (g : H) (z : V) :
    Nat.card {w : V // Γ.Adj (g • z) w} = Nat.card {w : V // Γ.Adj z w} :=
  (Nat.card_congr (neighborEquiv (H := H) (Γ := Γ) g z)).symm

private theorem isMultiplyPretransitive_smul {z : V}
    (h2 : MulAction.IsMultiplyPretransitive ↥(localGroup H Γ z) {w : V // Γ.Adj z w} 2)
    (g : H) :
    MulAction.IsMultiplyPretransitive ↥(localGroup H Γ (g • z))
      {w : V // Γ.Adj (g • z) w} 2 := by
  rw [MulAction.is_two_pretransitive_iff] at h2 ⊢
  intro a b c d hab hcd
  let e := neighborEquiv (H := H) (Γ := Γ) g z
  have hab' : e.symm a ≠ e.symm b := by
    intro h
    exact hab (by simpa using congrArg e h)
  have hcd' : e.symm c ≠ e.symm d := by
    intro h
    exact hcd (by simpa using congrArg e h)
  obtain ⟨x, hx1, hx2⟩ := h2 hab' hcd'
  refine ⟨localGroupConj (H := H) (Γ := Γ) g z x, ?_, ?_⟩
  · rw [Subgroup.smul_def, Equiv.Perm.smul_def, localGroupConj_coe,
      Equiv.permCongrHom_coe, Equiv.permCongr_apply]
    have hx1' : (x : Equiv.Perm _) (e.symm a) = e.symm c := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hx1
    calc
      e ((x : Equiv.Perm _) (e.symm a)) = e (e.symm c) := by rw [hx1']
      _ = c := by simp
  · rw [Subgroup.smul_def, Equiv.Perm.smul_def, localGroupConj_coe,
      Equiv.permCongrHom_coe, Equiv.permCongr_apply]
    have hx2' : (x : Equiv.Perm _) (e.symm b) = e.symm d := by
      simpa [Subgroup.smul_def, Equiv.Perm.smul_def] using hx2
    calc
      e ((x : Equiv.Perm _) (e.symm b)) = e (e.symm d) := by rw [hx2']
      _ = d := by simp

theorem isLocalL2_smul {z : V} {m : ℕ} (h : IsLocalL2 H Γ z m) (g : H) :
    IsLocalL2 H Γ (g • z) m := by
  obtain ⟨hcard, h2, N, hN, hNiso⟩ := h
  refine ⟨?_, isMultiplyPretransitive_smul h2 g, ?_⟩
  · rw [card_neighbor_smul]
    exact hcard
  · refine ⟨N.map (localGroupConj (H := H) (Γ := Γ) g z).toMonoidHom, ?_, ?_⟩
    · exact hN.map _ (localGroupConj (H := H) (Γ := Γ) g z).surjective
    · obtain ⟨eN⟩ := hNiso
      exact ⟨(MulEquiv.subgroupMap (localGroupConj (H := H) (Γ := Γ) g z) N).symm.trans eN⟩

theorem isLocalSz_smul {z : V} {a : ℕ} (h : IsLocalSz H Γ z a) (g : H) :
    IsLocalSz H Γ (g • z) a := by
  obtain ⟨hcard, h2, N, hN, hNiso⟩ := h
  refine ⟨?_, isMultiplyPretransitive_smul h2 g, ?_⟩
  · rw [card_neighbor_smul]
    exact hcard
  · refine ⟨N.map (localGroupConj (H := H) (Γ := Γ) g z).toMonoidHom, ?_, ?_⟩
    · exact hN.map _ (localGroupConj (H := H) (Γ := Γ) g z).surjective
    · obtain ⟨eN⟩ := hNiso
      exact ⟨(MulEquiv.subgroupMap (localGroupConj (H := H) (Γ := Γ) g z) N).symm.trans eN⟩

theorem isLocalU3_smul {z : V} {k : ℕ} {F : Type} [Field F] (h : IsLocalU3 H Γ z k F)
    (g : H) : IsLocalU3 H Γ (g • z) k F := by
  obtain ⟨hcard, h2, N, hN, hNiso⟩ := h
  refine ⟨?_, isMultiplyPretransitive_smul h2 g, ?_⟩
  · rw [card_neighbor_smul]
    exact hcard
  · refine ⟨N.map (localGroupConj (H := H) (Γ := Γ) g z).toMonoidHom, ?_, ?_⟩
    · exact hN.map _ (localGroupConj (H := H) (Γ := Γ) g z).surjective
    · obtain ⟨eN⟩ := hNiso
      exact ⟨(MulEquiv.subgroupMap (localGroupConj (H := H) (Γ := Γ) g z) N).symm.trans eN⟩

structure RootFacts (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V) [GraphAction H Γ]
    (n : ℕ) (z : V) : Prop where
  le_root : ∀ q : GPath Γ n, q.NoBack → q n = z → ∀ ω', Γ.Adj z ω' → ω' ≠ q (n - 1) →
    ∀ Q : Subgroup H, Q ≤ MulAction.stabilizer H z ⊓ MulAction.stabilizer H (q (n - 1)) →
    IsPGroup 2 Q →
    (∀ t ∈ socTorus H Γ z (q (n - 1)) ω', ∀ x ∈ Q,
      t * x * t⁻¹ ∈ Q ⊔ fixingSubgroup H (Γ.neighborSet z)) →
    Q ≤ pathRootGroup H Γ q ⊔ fixingSubgroup H (Γ.neighborSet z)
  socle_le : ∀ q q' : GPath Γ n, q.NoBack → q'.NoBack → q n = z → q' n = z →
    q (n - 1) ≠ q' (n - 1) →
    socleAt H Γ z ≤ pathRootGroup H Γ q ⊔ pathRootGroup H Γ q' ⊔
      fixingSubgroup H (Γ.neighborSet z)

structure TransitiveFacts (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (z : V) : Prop where
  transitive : ∀ ω ω', Γ.Adj z ω → Γ.Adj z ω' → ω ≠ ω' → ∀ P : Subgroup H,
    P ≤ MulAction.stabilizer H z ⊓ MulAction.stabilizer H ω → IsPGroup 2 P →
    ¬ P ≤ fixingSubgroup H (Γ.neighborSet z) →
    (∀ t ∈ socTorus H Γ z ω ω', ∀ x ∈ P,
      t * x * t⁻¹ ∈ P ⊔ fixingSubgroup H (Γ.neighborSet z)) →
    ∀ α β, Γ.Adj z α → Γ.Adj z β → α ≠ ω → β ≠ ω → ∃ r ∈ P, r • α = β

variable (H) in
@[expose] def IsTorusNormalAt (Γ : SimpleGraph V) (z ω : V) (Z : Subgroup H) : Prop :=
  ∃ ω', Γ.Adj z ω' ∧ ω' ≠ ω ∧ ∀ t ∈ socTorus H Γ z ω ω', ∀ x ∈ Z,
    t * x * t⁻¹ ∈ Z ⊔ fixingSubgroup H (Γ.neighborSet z)

variable (H) in
@[expose] def IsRootAt (Γ : SimpleGraph V) (z ω : V) (R : Subgroup H) : Prop :=
  R ≤ MulAction.stabilizer H z ⊓ MulAction.stabilizer H ω ∧ IsPGroup 2 R ∧
    (∀ α β, Γ.Adj z α → Γ.Adj z β → α ≠ ω → β ≠ ω → ∃ r ∈ R, r • α = β) ∧
    IsTorusNormalAt H Γ z ω R

structure CenterFacts (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (z : V) (e : ℕ) : Prop where
  le_of_ne_bot : ∀ ω, Γ.Adj z ω → ∀ R Z Z' : Subgroup H, IsRootAt H Γ z ω R →
    Z ≤ MulAction.stabilizer H z ⊓ MulAction.stabilizer H ω →
    Z' ≤ MulAction.stabilizer H z ⊓ MulAction.stabilizer H ω →
    IsTorusNormalAt H Γ z ω Z → IsTorusNormalAt H Γ z ω Z' →
    ⁅R, Z⁆ ≤ fixingSubgroup H (Γ.neighborSet z) → ⁅R, Z'⁆ ≤ fixingSubgroup H (Γ.neighborSet z) →
    ¬ Z' ≤ fixingSubgroup H (Γ.neighborSet z) → Z ≤ Z' ⊔ fixingSubgroup H (Γ.neighborSet z)
  centralizer : ∀ ω ω', Γ.Adj z ω → Γ.Adj z ω' → ω ≠ ω' → ∀ R Z : Subgroup H,
    IsRootAt H Γ z ω R → Z ≤ MulAction.stabilizer H z ⊓ MulAction.stabilizer H ω →
    IsTorusNormalAt H Γ z ω Z → ⁅R, Z⁆ ≤ fixingSubgroup H (Γ.neighborSet z) →
    ¬ Z ≤ fixingSubgroup H (Γ.neighborSet z) →
    ∀ g ∈ MulAction.stabilizer H z ⊓ MulAction.stabilizer H ω ⊓ MulAction.stabilizer H ω',
      Odd (orderOf g) → ⁅Subgroup.zpowers g, Z⁆ ≤ fixingSubgroup H (Γ.neighborSet z) →
        g ^ e ∈ fixingSubgroup H (Γ.neighborSet z)

structure UnitaryFacts (H : Type) [Group H] [MulAction H V] (Γ : SimpleGraph V)
    [GraphAction H Γ] (z : V) (q : ℕ) : Prop where
  fix_two : ∀ w y, Γ.Adj z w → Γ.Adj z y → w ≠ y → ∀ t ∈ socTorus H Γ z w y,
    t ^ (q + 1) ∉ fixingSubgroup H (Γ.neighborSet z) →
      ∀ u, Γ.Adj z u → t • u = u → u = w ∨ u = y
  pow_card : ∀ w y, Γ.Adj z w → Γ.Adj z y → w ≠ y → ∀ t ∈ socTorus H Γ z w y,
    t ^ (q ^ 2 - 1) ∈ fixingSubgroup H (Γ.neighborSet z)
  exists_pow : ∀ w y, Γ.Adj z w → Γ.Adj z y → w ≠ y → ∃ t ∈ socTorus H Γ z w y,
    (t ^ (q + 1)) ^ (q + 1) ∉ fixingSubgroup H (Γ.neighborSet z)

theorem localPermHom_ker {z : V} :
    (localPermHom (H := H) Γ z).ker =
      (fixingSubgroup H (Γ.neighborSet z)).subgroupOf (MulAction.stabilizer H z) := by
  ext x
  constructor
  · intro hx
    rw [MonoidHom.mem_ker] at hx
    rw [Subgroup.mem_subgroupOf, mem_fixingSubgroup_iff]
    intro w hw
    have hxw : localPermHom (H := H) Γ z x (⟨w, hw⟩ : {w : V // Γ.Adj z w}) = ⟨w, hw⟩ := by
      rw [hx]
      simp
    have hco := congrArg Subtype.val hxw
    rwa [localPermHom_apply] at hco
  · intro hx
    rw [MonoidHom.mem_ker]
    ext w
    rw [show (1 : Equiv.Perm {w : V // Γ.Adj z w}) w = w from rfl]
    rw [localPermHom_apply]
    exact (mem_fixingSubgroup_iff H).mp (Subgroup.mem_subgroupOf.mp hx) w.1 w.2

theorem RootFacts.exists_odd_torus [Finite H] {n : ℕ} (hn : 3 ≤ n) {z : V}
    (hR : RootFacts H Γ n z) (hL : LocalFacts H Γ z)
    (h3 : ∀ w w', Γ.Adj z w → Γ.Adj z w' → ∃ u, Γ.Adj z u ∧ u ≠ w ∧ u ≠ w')
    {q q' : GPath Γ n} (hq : q.NoBack) (hq' : q'.NoBack) (hqz : q n = z) (hq'z : q' n = z)
    (hne : q (n - 1) ≠ q' (n - 1)) :
    ∃ b ∈ pathRootGroup H Γ q ⊔ pathRootGroup H Γ q', b • q (n - 1) = q (n - 1) ∧
      b • q' (n - 1) = q' (n - 1) ∧ Odd (orderOf b) ∧
      b ∉ fixingSubgroup H (Γ.neighborSet z) := by
  classical
  let Gz := MulAction.stabilizer H z
  let F := fixingSubgroup H (Γ.neighborSet z)
  let U := pathRootGroup H Γ q
  let U' := pathRootGroup H Γ q'
  let ω := q (n - 1)
  let ω' := q' (n - 1)
  have hFGz : F ≤ Gz := hL.kernel_le
  have hzω : Γ.Adj z ω := by
    have h := q.adj (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega, hqz] at h
    exact h.symm
  have hzω' : Γ.Adj z ω' := by
    have h := q'.adj (n - 1) (by omega)
    rw [show n - 1 + 1 = n by omega, hq'z] at h
    exact h.symm
  have hne' : ω ≠ ω' := hne
  have hnot : ¬ socTorus H Γ z ω ω' ≤ F := by
    intro hle
    obtain ⟨u, hzu, huw, huw'⟩ := h3 ω ω' hzω hzω'
    have hfix : ∀ t ∈ socTorus H Γ z ω ω', t • u = u :=
      fun t ht => (mem_fixingSubgroup_iff H).mp (hle ht) u hzu
    rcases hL.torusFix ω ω' u hzω hzω' hne' hzu hfix with h | h
    · exact huw h
    · exact huw' h
  obtain ⟨t, htT, htod, htgen⟩ :=
    hL.torusGen ω ω' hzω hzω' hne' (socTorus H Γ z ω ω') le_rfl le_sup_left
  have htF : t ∉ F := by
    intro htF
    apply hnot
    intro x hx
    have hclosure : Subgroup.closure {t} ≤ F :=
      (Subgroup.closure_le F).mpr (by
        intro y hy
        rw [Set.mem_singleton_iff] at hy
        subst hy
        exact htF)
    exact (sup_le hclosure le_rfl) (htgen hx)
  have hSsocle : socleAt H Γ z ≤ Gz := socleAt_le_stabilizer hL.kernel_le
  have htSoc : t ∈ socleAt H Γ z := htT.1.1
  have htGz : t ∈ Gz := hSsocle htSoc
  have htU : t ∈ U ⊔ U' ⊔ F := hR.socle_le q q' hq hq' hqz hq'z hne' htSoc
  have hUleGz : U ≤ Gz := by
    intro x hx
    rw [MulAction.mem_stabilizer_iff]
    have hfix := smul_path_eq_self_of_mem_pathRootGroup hn hx n le_rfl
    rwa [hqz] at hfix
  have hU'leGz : U' ≤ Gz := by
    intro x hx
    rw [MulAction.mem_stabilizer_iff]
    have hfix := smul_path_eq_self_of_mem_pathRootGroup hn hx n le_rfl
    rwa [hq'z] at hfix
  let tGz : Gz := ⟨t, htGz⟩
  have htSub : tGz ∈ (U ⊔ U' ⊔ F).subgroupOf Gz := by
    rw [Subgroup.mem_subgroupOf]
    exact htU
  have hsub : (U ⊔ U' ⊔ F).subgroupOf Gz =
      (U.subgroupOf Gz ⊔ U'.subgroupOf Gz) ⊔ F.subgroupOf Gz := by
    rw [Subgroup.subgroupOf_sup (sup_le hUleGz hU'leGz) hFGz,
      Subgroup.subgroupOf_sup hUleGz hU'leGz]
  rw [hsub] at htSub
  have hFnormal : (F.subgroupOf Gz).Normal := by
    rw [← localPermHom_ker]
    infer_instance
  haveI := hFnormal
  obtain ⟨aGz, haGz, kGz, hkGz, hak⟩ := Subgroup.mem_sup_of_normal_right.mp htSub
  let a : H := (aGz : H)
  let k : H := (kGz : H)
  have hakH : a * k = t := by
    have := congrArg (fun x : Gz => (x : H)) hak
    simpa [a, k, tGz] using this
  have haU : a ∈ U ⊔ U' := by
    have haSub : aGz ∈ (U ⊔ U').subgroupOf Gz := by
      rw [Subgroup.subgroupOf_sup hUleGz hU'leGz]
      exact haGz
    exact Subgroup.mem_subgroupOf.mp haSub
  have hkF : k ∈ F := Subgroup.mem_subgroupOf.mp hkGz
  have haGz' : a ∈ Gz := (sup_le hUleGz hU'leGz) haU
  have htfixω : t • ω = ω := MulAction.mem_stabilizer_iff.mp htT.1.2
  have htfixω' : t • ω' = ω' := MulAction.mem_stabilizer_iff.mp htT.2
  have hkfixω : k • ω = ω := (mem_fixingSubgroup_iff H).mp hkF ω hzω
  have hkfixω' : k • ω' = ω' := (mem_fixingSubgroup_iff H).mp hkF ω' hzω'
  have ha_eq : a = t * k⁻¹ := by
    rw [← hakH]
    group
  have hkinvω : k⁻¹ • ω = ω := by
    calc k⁻¹ • ω = k⁻¹ • (k • ω) := by rw [hkfixω]
      _ = ω := inv_smul_smul k ω
  have hkinvω' : k⁻¹ • ω' = ω' := by
    calc k⁻¹ • ω' = k⁻¹ • (k • ω') := by rw [hkfixω']
      _ = ω' := inv_smul_smul k ω'
  have haω : a • ω = ω := by
    rw [ha_eq, mul_smul, hkinvω, htfixω]
  have haω' : a • ω' = ω' := by
    rw [ha_eq, mul_smul, hkinvω', htfixω']
  have hπa_eq : localPermHom (H := H) Γ z aGz = localPermHom (H := H) Γ z tGz := by
    have h := congrArg (localPermHom (H := H) Γ z) hak
    rw [map_mul] at h
    have hkker : localPermHom (H := H) Γ z kGz = 1 := by
      rw [← MonoidHom.mem_ker, localPermHom_ker]
      exact hkGz
    rw [hkker, mul_one] at h
    exact h
  have hφa_odd : Odd (orderOf (localPermHom (H := H) Γ z aGz)) := by
    rw [hπa_eq]
    refine htod.of_dvd_nat ?_
    rw [show orderOf t = orderOf tGz from Subgroup.orderOf_coe tGz]
    exact orderOf_map_dvd _ _
  obtain ⟨m, hmodd, hmimg⟩ :=
    exists_odd_pow_map_eq (localPermHom (H := H) Γ z) aGz hφa_odd
  let b : H := ((aGz ^ m : Gz) : H)
  have hb_eq : b = a ^ m := by
    simp [b, a, Subgroup.coe_pow]
  have hbU : b ∈ U ⊔ U' := by
    have h := Subgroup.pow_mem (U ⊔ U') haU m
    simpa [b, a, Subgroup.coe_pow] using h
  have hbzp : a ^ m ∈ Subgroup.zpowers a := by
    simpa using Subgroup.zpow_mem (Subgroup.zpowers a) (Subgroup.mem_zpowers a) (m : ℤ)
  have hbω : b • ω = ω := by
    rw [hb_eq]
    exact smul_eq_self_of_mem_zpowers hbzp haω
  have hbω' : b • ω' = ω' := by
    rw [hb_eq]
    exact smul_eq_self_of_mem_zpowers hbzp haω'
  have hbGz : b ∈ Gz := by
    simpa [b] using (aGz ^ m).2
  have hπt_ne : localPermHom (H := H) Γ z tGz ≠ 1 := by
    intro h
    apply htF
    have hmem : tGz ∈ (localPermHom (H := H) Γ z).ker := MonoidHom.mem_ker.mpr h
    rw [localPermHom_ker] at hmem
    exact Subgroup.mem_subgroupOf.mp hmem
  have hbF : b ∉ F := by
    intro hbF
    have hker : (⟨b, hbGz⟩ : Gz) ∈ (localPermHom (H := H) Γ z).ker := by
      rw [localPermHom_ker]
      exact Subgroup.mem_subgroupOf.mpr hbF
    have h1 : localPermHom (H := H) Γ z (⟨b, hbGz⟩ : Gz) = 1 := MonoidHom.mem_ker.mp hker
    have hb_eq' : (⟨b, hbGz⟩ : Gz) = aGz ^ m := Subtype.ext rfl
    rw [hb_eq', hmimg] at h1
    exact hπt_ne (hπa_eq.symm.trans h1)
  have hbodd : Odd (orderOf b) := by
    have hcoe : orderOf b = orderOf (aGz ^ m) := Subgroup.orderOf_coe (aGz ^ m)
    rwa [hcoe]
  exact ⟨b, hbU, hbω, hbω', hbodd, hbF⟩

end CFSG.Quasithin.Stroth.WeissDelta

end

module

public import CFSG.RankThree.PartTwo.Sec3.ThreeSpaceTransvections
public import CFSG.GH74.GLS.Basic
public import CFSG.GroupTheory.BaerSuzuki

public section

namespace CFSG.RankThree.PartTwo.Sec3

open Module CFSG.RankThree.Classical
open scoped MatrixGroups

variable {V : Type*} [AddCommGroup V] [Module (ZMod 3) V]

theorem zmod3_pow_three_pow (d : ZMod 3) (n : ℕ) : d ^ (3 ^ n) = d := by
  induction n with
  | zero => rw [pow_zero, pow_one]
  | succ n ih => rw [pow_succ, pow_mul, ih]; exact ZMod.pow_card d

theorem range_sub_one_eq_span {r : V ≃ₗ[ZMod 3] V} {v : V} {f : Dual (ZMod 3) V}
    (hr : IsTransvectionWith r v f) :
    LinearMap.range ((r : V →ₗ[ZMod 3] V) - 1) = Submodule.span (ZMod 3) {v} := by
  apply le_antisymm
  · rintro _ ⟨x, rfl⟩
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, hr.2.2.2, Module.End.one_apply,
      add_sub_cancel_left]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · rw [Submodule.span_singleton_le_iff_mem]
    obtain ⟨x, hx⟩ : ∃ x, f x ≠ 0 := by
      by_contra! h
      exact hr.2.1 (LinearMap.ext h)
    refine ⟨(f x)⁻¹ • x, ?_⟩
    rw [LinearMap.sub_apply, LinearEquiv.coe_coe, hr.2.2.2, Module.End.one_apply,
      add_sub_cancel_left, map_smul, smul_eq_mul, inv_mul_cancel₀ hx, one_smul]

theorem pow_three_eq_one_of_isTransvectionWith {r : V ≃ₗ[ZMod 3] V} {v : V}
    {f : Dual (ZMod 3) V} (hr : IsTransvectionWith r v f) : r ^ 3 = 1 := by
  ext x
  rw [hr.pow_apply, show ((3 : ℕ) : ZMod 3) = 0 from rfl, zero_mul, zero_smul, add_zero,
    LinearEquiv.coe_one, id]

theorem orderOf_eq_three_of_isTransvectionWith {r : V ≃ₗ[ZMod 3] V} {v : V}
    {f : Dual (ZMod 3) V} (hr : IsTransvectionWith r v f) : orderOf r = 3 :=
  orderOf_eq_prime (pow_three_eq_one_of_isTransvectionWith hr) (ne_one_of_isTransvectionWith hr)

theorem mapsTo_span_of_conj_mem {r : V ≃ₗ[ZMod 3] V} {v : V} {f : Dual (ZMod 3) V}
    (hr : IsTransvectionWith r v f) {g : V ≃ₗ[ZMod 3] V}
    (hg : g * r * g⁻¹ ∈ Subgroup.zpowers r) :
    ∀ y ∈ Submodule.span (ZMod 3) {v}, g y ∈ Submodule.span (ZMod 3) {v} := by
  have hfin : IsOfFinOrder r :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, pow_three_eq_one_of_isTransvectionWith hr⟩
  obtain ⟨n, hn⟩ := (hfin.mem_powers_iff_mem_zpowers).mpr hg
  have hconj := hr.conj g
  obtain ⟨y₀, hy₀⟩ : ∃ y, f y ≠ 0 := by
    by_contra! h
    exact hr.2.1 (LinearMap.ext h)
  have h1 := congrArg (fun t : V ≃ₗ[ZMod 3] V => t (g y₀)) hn
  simp only at h1
  rw [hr.pow_apply, hconj.2.2.2] at h1
  have hgy : (f.comp (g.symm : V →ₗ[ZMod 3] V)) (g y₀) = f y₀ := by
    simp
  rw [hgy, add_right_inj] at h1
  have hgv : g v ∈ Submodule.span (ZMod 3) {v} := by
    have : g v = (f y₀)⁻¹ • (((n : ZMod 3) * f (g y₀)) • v) := by
      rw [h1, smul_smul, inv_mul_cancel₀ hy₀, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v))
  intro y hy
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
  rw [map_smul]
  exact Submodule.smul_mem _ _ hgv

theorem mem_fixingSubgroup_span_iff {g : V ≃ₗ[ZMod 3] V} {v : V} :
    g ∈ fixingSubgroup (V ≃ₗ[ZMod 3] V)
        ((Submodule.span (ZMod 3) {v} : Submodule (ZMod 3) V) : Set V) ↔ g v = v := by
  rw [mem_fixingSubgroup_iff]
  constructor
  · intro h
    exact h v (Submodule.mem_span_singleton_self v)
  · intro h y hy
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hy
    rw [LinearEquiv.smul_def, map_smul, h]

theorem apply_eq_of_mem_closure {S : Set (V ≃ₗ[ZMod 3] V)} {v : V} (hS : ∀ s ∈ S, s v = v)
    {s : V ≃ₗ[ZMod 3] V} (hs : s ∈ Subgroup.closure S) : s v = v :=
  ((Subgroup.closure_le (MulAction.stabilizer (V ≃ₗ[ZMod 3] V) v)).mpr
    (fun t ht => (hS t ht : t • v = v)) hs : s • v = v)

theorem sub_mem_of_mapsTo_of_fix {P L : Submodule (ZMod 3) V} (hPL : IsCompl P L)
    {x : V ≃ₗ[ZMod 3] V} (hxP : ∀ p ∈ P, x p ∈ P) (hxL : ∀ l ∈ L, x l = l) (u : V) :
    x u - u ∈ P := by
  have hu : u ∈ P ⊔ L := by rw [hPL.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp hu
  have : x (p + l) - (p + l) = x p - p := by rw [map_add, hxL l hl]; abel
  rw [this]
  exact P.sub_mem (hxP p hp) hp

theorem eq_of_isSylowOf {G' : Type*} [Group G'] {p : ℕ} {P K R : Subgroup G'}
    (h : CFSG.ABGLocalTools.IsSylowOf p P K) (hRK : R ≤ K) (hR : IsPGroup p R) (hPR : P ≤ R) :
    R = P := by
  obtain ⟨Q, hQ⟩ := h.exists_sylow_eq_subgroupOf
  have h1 : (Q : Subgroup K) ≤ R.subgroupOf K := hQ ▸ Subgroup.comap_mono hPR
  have h2 : R.subgroupOf K = Q := Q.is_maximal' (hR.comap_subtype (K := K)) h1
  calc R = (R.subgroupOf K).map K.subtype := (Subgroup.map_subgroupOf_eq_of_le hRK).symm
    _ = (P.subgroupOf K).map K.subtype := by rw [h2, hQ]
    _ = P := Subgroup.map_subgroupOf_eq_of_le h.le

theorem exists_conj_mem_of_lt {G' : Type*} [Group G'] [Finite G'] {p : ℕ} [Fact p.Prime]
    {H Q : Subgroup G'} (hQ : IsPGroup p Q) (hHQ : H < Q) :
    ∃ q ∈ Q, q ∉ H ∧ ∀ h ∈ H, q * h * q⁻¹ ∈ H := by
  have : Group.IsNilpotent Q := hQ.isNilpotent
  have hlt : H.subgroupOf Q < ⊤ := by
    rw [lt_top_iff_ne_top]
    intro htop
    apply hHQ.not_ge
    intro q hq
    have : (⟨q, hq⟩ : Q) ∈ H.subgroupOf Q := htop ▸ Subgroup.mem_top _
    exact this
  obtain ⟨q, hqN, hqH⟩ :=
    IsConcreteLE.exists_of_lt (Group.normalizerCondition_of_isNilpotent _ hlt)
  refine ⟨q, q.2, hqH, fun h hh => ?_⟩
  have := (Subgroup.mem_normalizer_iff.mp hqN ⟨h, hHQ.le hh⟩).mp hh
  simpa [Subgroup.mem_subgroupOf] using this

variable [FiniteDimensional (ZMod 3) V]

theorem finite_linearEquiv : Finite (V ≃ₗ[ZMod 3] V) := by
  have : Finite V := Module.finite_of_finite (ZMod 3)
  exact Finite.of_injective (fun e : V ≃ₗ[ZMod 3] V => (e : V → V)) DFunLike.coe_injective

theorem sub_mem_of_mapsTo_of_pow {P L : Submodule (ZMod 3) V} (hPL : IsCompl P L)
    (hL : finrank (ZMod 3) L = 1) {y : V ≃ₗ[ZMod 3] V} (hyP : ∀ p ∈ P, y p ∈ P) {k : ℕ}
    (hy : y ^ (3 ^ k) = 1) (z : V) : y z - z ∈ P := by
  obtain ⟨l₀, hl₀, rfl⟩ := exists_eq_span_of_finrank_eq_one hL
  have hyl : y l₀ ∈ P ⊔ Submodule.span (ZMod 3) {l₀} := by
    rw [hPL.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨p₀, hp₀, l₁, hl₁, hdec⟩ := Submodule.mem_sup.mp hyl
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hl₁
  have hpow : ∀ n : ℕ, (y ^ n) l₀ - c ^ n • l₀ ∈ P := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      have : (y ^ (n + 1)) l₀ - c ^ (n + 1) • l₀ =
          y ((y ^ n) l₀ - c ^ n • l₀) + c ^ n • p₀ := by
        rw [pow_succ', LinearEquiv.mul_apply, map_sub, map_smul, ← hdec]
        module
      rw [this]
      exact P.add_mem (hyP _ ih) (P.smul_mem _ hp₀)
  have h3 := hpow (3 ^ k)
  rw [hy, LinearEquiv.coe_one, id] at h3
  rw [zmod3_pow_three_pow] at h3
  have hmem : (1 - c) • l₀ ∈ P := by rw [sub_smul, one_smul]; exact h3
  have hzero : (1 - c) • l₀ = 0 :=
    Submodule.disjoint_def.mp hPL.disjoint _ hmem
      (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self l₀))
  have hc : c = 1 := by
    rcases smul_eq_zero.mp hzero with h | h
    · exact (sub_eq_zero.mp h).symm
    · exact absurd h hl₀
  have hyl₀ : y l₀ - l₀ ∈ P := by
    rw [← hdec, hc, one_smul, add_sub_cancel_right]
    exact hp₀
  have hz : z ∈ P ⊔ Submodule.span (ZMod 3) {l₀} := by
    rw [hPL.sup_eq_top]; exact Submodule.mem_top
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp hz
  obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hl
  have : y (p + a • l₀) - (p + a • l₀) = (y p - p) + a • (y l₀ - l₀) := by
    rw [map_add, map_smul, smul_sub]; abel
  rw [this]
  exact P.add_mem (P.sub_mem (hyP p hp) hp) (P.smul_mem _ hyl₀)

omit [FiniteDimensional (ZMod 3) V] in
theorem det_projection_comp_eq_one {P L : Submodule (ZMod 3) V} (hPL : IsCompl P L)
    {y : V ≃ₗ[ZMod 3] V} (hyL : ∀ l ∈ L, y l = l) {k : ℕ} (hy : y ^ (3 ^ k) = 1) :
    LinearMap.det ((P.projectionOnto L hPL).comp ((y : V →ₗ[ZMod 3] V).comp P.subtype)) = 1 := by
  set φ := (P.projectionOnto L hPL).comp ((y : V →ₗ[ZMod 3] V).comp P.subtype) with hφdef
  have hπ : ∀ z : V, P.projectionOnto L hPL (y (P.projection L hPL z)) =
      P.projectionOnto L hPL (y z) := by
    intro z
    have hzl : z - P.projection L hPL z ∈ L := by
      have h := Submodule.projection_add_projection_eq_self hPL z
      have : z - P.projection L hPL z = L.projection P hPL.symm z := by
        rw [sub_eq_iff_eq_add']
        exact h.symm
      rw [this]
      exact Submodule.projection_apply_mem hPL.symm z
    have : y z = y (P.projection L hPL z) + (z - P.projection L hPL z) := by
      rw [← hyL _ hzl, ← map_add, add_sub_cancel]
    rw [this, map_add, (Submodule.projectionOnto_apply_eq_zero_iff hPL).mpr hzl, add_zero]
  have hpow : ∀ n : ℕ, ∀ p : P, (φ ^ n) p = P.projectionOnto L hPL ((y ^ n) p) := by
    intro n
    induction n with
    | zero =>
      intro p
      simp
    | succ n ih =>
      intro p
      rw [pow_succ', Module.End.mul_apply, ih, hφdef, LinearMap.comp_apply, LinearMap.comp_apply,
        Submodule.subtype_apply]
      have := hπ ((y ^ n) p)
      rw [Submodule.projection, LinearMap.comp_apply] at this
      refine this.trans ?_
      rw [pow_succ', LinearEquiv.mul_apply]
  have hφ1 : φ ^ (3 ^ k) = 1 := by
    ext p
    rw [hpow, hy, LinearEquiv.coe_one, id, Submodule.projectionOnto_apply_left]
    rfl
  have hd := congrArg LinearMap.det hφ1
  rw [map_pow, map_one] at hd
  rw [zmod3_pow_three_pow] at hd
  exact hd

omit [FiniteDimensional (ZMod 3) V] in
theorem det_restrict_eq_one_of_pow {y : V ≃ₗ[ZMod 3] V} {P : Submodule (ZMod 3) V}
    (hyP : ∀ p ∈ P, y p ∈ P) {k : ℕ} (hy : y ^ (3 ^ k) = 1) :
    LinearMap.det ((y : V →ₗ[ZMod 3] V).restrict hyP) = 1 := by
  set φ := (y : V →ₗ[ZMod 3] V).restrict hyP with hφdef
  have hpow : ∀ n : ℕ, ∀ p : P, ((φ ^ n) p : V) = (y ^ n) p := by
    intro n
    induction n with
    | zero => intro p; simp
    | succ n ih =>
      intro p
      rw [pow_succ', Module.End.mul_apply]
      change y ((φ ^ n) p : V) = (y ^ (n + 1)) p
      rw [ih, pow_succ', LinearEquiv.mul_apply]
  have h1 : φ ^ (3 ^ k) = 1 := by
    ext p
    rw [hpow, hy]
    rfl
  have hd := congrArg LinearMap.det h1
  rw [map_pow, map_one, zmod3_pow_three_pow] at hd
  exact hd

theorem exists_transvection_same_center (hV : finrank (ZMod 3) V = 3) {r : V ≃ₗ[ZMod 3] V}
    {v : V} {f : Dual (ZMod 3) V} (hr : IsTransvectionWith r v f) :
    ∃ (s : V ≃ₗ[ZMod 3] V) (h : Dual (ZMod 3) V), IsTransvectionWith s v h ∧
      s ∉ Subgroup.zpowers r := by
  classical
  obtain ⟨x₀, hx₀⟩ : ∃ x, f x ≠ 0 := by
    by_contra! h
    exact hr.2.1 (LinearMap.ext h)
  set p := Submodule.span (ZMod 3) ({v, x₀} : Set V) with hpdef
  have hp : p ≠ ⊤ := by
    intro htop
    have h1 : finrank (ZMod 3) p ≤ 2 := by
      have h := finrank_span_finset_le_card (R := ZMod 3) ({v, x₀} : Finset V)
      rw [Finset.coe_insert, Finset.coe_singleton] at h
      exact h.trans (Finset.card_le_two)
    rw [htop, finrank_top, hV] at h1
    omega
  obtain ⟨y, hy⟩ : ∃ y, y ∉ p := by
    by_contra! h
    exact hp (eq_top_iff.mpr fun y _ => h y)
  obtain ⟨h, hhy, hhp⟩ := Submodule.exists_dual_map_eq_bot_of_notMem hy inferInstance
  have hmem : ∀ x ∈ p, h x = 0 := fun x hx => by
    have : h x ∈ p.map h := Submodule.mem_map_of_mem hx
    rwa [hhp, Submodule.mem_bot] at this
  have hhv : h v = 0 := hmem v (Submodule.subset_span (by simp))
  have hhx : h x₀ = 0 := hmem x₀ (Submodule.subset_span (by simp))
  have hs : IsTransvectionWith (LinearEquiv.transvection hhv) v h :=
    ⟨hr.1, fun h0 => hhy (by rw [h0]; rfl), hhv, fun x => LinearEquiv.transvection.apply _ _⟩
  refine ⟨LinearEquiv.transvection hhv, h, hs, fun hmem' => ?_⟩
  have hfin : IsOfFinOrder r :=
    isOfFinOrder_iff_pow_eq_one.mpr ⟨3, by norm_num, pow_three_eq_one_of_isTransvectionWith hr⟩
  obtain ⟨n, hn⟩ := (hfin.mem_powers_iff_mem_zpowers).mpr hmem'
  have h1 := congrArg (fun t : V ≃ₗ[ZMod 3] V => t x₀) hn
  simp only at h1
  rw [hr.pow_apply, hs.2.2.2, hhx, zero_smul, add_zero, add_eq_left, smul_eq_zero] at h1
  have hn0 : (n : ZMod 3) = 0 := by
    rcases h1 with h1 | h1
    · exact (mul_eq_zero.mp h1).resolve_right hx₀
    · exact absurd h1 hr.1
  apply ne_one_of_isTransvectionWith hs
  rw [← hn]
  ext x
  rw [hr.pow_apply, hn0, zero_mul, zero_smul, add_zero, LinearEquiv.coe_one, id]

section PairFacts

variable {t₁ t₂ : V ≃ₗ[ZMod 3] V} {v w : V} {f g : Dual (ZMod 3) V}
  (h₁ : IsTransvectionWith t₁ v f) (h₂ : IsTransvectionWith t₂ w g) (hfw : f w ≠ 0)
  (hgv : g v ≠ 0)
include h₁ h₂ hfw hgv

theorem finrank_pair (hV : finrank (ZMod 3) V = 3) :
    finrank (ZMod 3) (Submodule.span (ZMod 3) {v, w}) = 2 ∧
      finrank (ZMod 3) ↥(LinearMap.ker f ⊓ LinearMap.ker g) = 1 := by
  have hvw := linearIndependent_pair_of_transvections h₁ hfw h₁.1
  have hP : finrank (ZMod 3) (Submodule.span (ZMod 3) {v, w}) = 2 := by
    have hset : Set.range ![v, w] = ({v, w} : Set V) := by
      ext x
      simp only [Set.mem_range, Fin.exists_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one,
        Set.mem_insert_iff, Set.mem_singleton_iff]
      exact ⟨fun h => h.imp Eq.symm Eq.symm, fun h => h.imp Eq.symm Eq.symm⟩
    have := finrank_span_eq_card hvw
    rw [hset] at this
    rw [this]
    rfl
  have hsum := Submodule.finrank_add_eq_of_isCompl
    (isCompl_span_pair_ker_inf_ker h₁.2.2.1 h₂.2.2.1 hfw hgv)
  exact ⟨hP, by omega⟩

theorem exists_neg_mem_pair (hV : finrank (ZMod 3) V = 3) :
    ∃ z ∈ Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)),
      (∀ p ∈ Submodule.span (ZMod 3) {v, w}, z p = -p) ∧
        ∀ l ∈ LinearMap.ker f ⊓ LinearMap.ker g, z l = l := by
  have hP := (finrank_pair h₁ h₂ hfw hgv hV).1
  have hdet : LinearMap.det (-LinearMap.id : Submodule.span (ZMod 3) {v, w} →ₗ[ZMod 3]
      Submodule.span (ZMod 3) {v, w}) = 1 := by
    rw [← neg_one_smul (ZMod 3) (LinearMap.id : Submodule.span (ZMod 3) {v, w} →ₗ[ZMod 3]
      Submodule.span (ZMod 3) {v, w}), LinearMap.det_smul, LinearMap.det_id, hP]
    decide
  obtain ⟨z, hz, hzP, hzL⟩ := exists_mem_of_det_eq_one
    (H := Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V))) h₁ h₂
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hfw hgv _ hdet
  exact ⟨z, hz, fun p hp => by simpa using hzP ⟨p, hp⟩, hzL⟩

theorem invariant_subspaces_pair (hV : finrank (ZMod 3) V = 3) {Y : Submodule (ZMod 3) V}
    (hY : ∀ x ∈ Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)), ∀ y ∈ Y, x y ∈ Y) :
    Y = ⊥ ∨ Y = Submodule.span (ZMod 3) {v, w} ∨ Y = LinearMap.ker f ⊓ LinearMap.ker g ∨
      Y = ⊤ := by
  set P := Submodule.span (ZMod 3) {v, w} with hPdef
  set L := LinearMap.ker f ⊓ LinearMap.ker g with hLdef
  have hPL : IsCompl P L := isCompl_span_pair_ker_inf_ker h₁.2.2.1 h₂.2.2.1 hfw hgv
  obtain ⟨hP2, hL1⟩ : finrank (ZMod 3) P = 2 ∧ finrank (ZMod 3) L = 1 :=
    finrank_pair h₁ h₂ hfw hgv hV
  have ht₁X : t₁ ∈ Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)) :=
    Subgroup.subset_closure (by simp)
  have ht₂X : t₂ ∈ Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)) :=
    Subgroup.subset_closure (by simp)
  obtain ⟨z, hzX, hzP, hzL⟩ := exists_neg_mem_pair h₁ h₂ hfw hgv hV
  have hdec : Y = Y ⊓ P ⊔ Y ⊓ L := by
    refine le_antisymm (fun y hy => ?_) (sup_le inf_le_left inf_le_left)
    have hyPL : y ∈ P ⊔ L := by rw [hPL.sup_eq_top]; exact Submodule.mem_top
    obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp hyPL
    have hzy : z (p + l) ∈ Y := hY z hzX _ hy
    rw [map_add, hzP p hp, hzL l hl] at hzy
    have hpY : p ∈ Y := by
      have h1 : p + l - (-p + l) ∈ Y := Y.sub_mem hy hzy
      have h3 : p + p + p = 0 := by
        have := zmod3_three_smul p
        rwa [succ_nsmul, succ_nsmul, one_nsmul] at this
      have h2 : p + l - (-p + l) = p + p := by abel
      rw [h2, eq_neg_of_add_eq_zero_left h3] at h1
      simpa using Y.neg_mem h1
    have hlY : l ∈ Y := by
      have := Y.sub_mem hy hpY
      rwa [add_sub_cancel_left] at this
    exact Submodule.mem_sup.mpr ⟨p, Submodule.mem_inf.mpr ⟨hpY, hp⟩, l,
      Submodule.mem_inf.mpr ⟨hlY, hl⟩, rfl⟩
  have hYP : Y ⊓ P = ⊥ ∨ Y ⊓ P = P := by
    have hle : Y ⊓ P ≤ P := inf_le_right
    have hfin := Submodule.finrank_mono hle
    rw [hP2] at hfin
    rcases Nat.lt_or_ge (finrank (ZMod 3) ↥(Y ⊓ P)) 1 with h | h
    · left
      exact Submodule.finrank_eq_zero.mp (by omega)
    rcases h.lt_or_eq with h' | h'
    · right
      exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
    · exfalso
      obtain ⟨y₀, hy₀, hY₀⟩ := exists_eq_span_of_finrank_eq_one h'.symm
      have hy₀mem : y₀ ∈ Y ⊓ P := hY₀ ▸ Submodule.mem_span_singleton_self y₀
      have hinv : ∀ {t : V ≃ₗ[ZMod 3] V}, t ∈ Subgroup.closure ({t₁, t₂} : Set _) →
          t y₀ ∈ Submodule.span (ZMod 3) {y₀} := by
        intro t ht
        rw [← hY₀]
        refine Submodule.mem_inf.mpr ⟨hY t ht _ (Submodule.mem_inf.mp hy₀mem).1, ?_⟩
        exact (pair_mapsTo_and_fix h₁ h₂ ht).1 _ (Submodule.mem_inf.mp hy₀mem).2
      have hf : f y₀ = 0 := by
        have h := apply_eq_self_of_isTransvectionWith_of_mem h₁ (hinv ht₁X)
        rw [h₁.2.2.2, add_eq_left, smul_eq_zero] at h
        exact h.resolve_right h₁.1
      have hg : g y₀ = 0 := by
        have h := apply_eq_self_of_isTransvectionWith_of_mem h₂ (hinv ht₂X)
        rw [h₂.2.2.2, add_eq_left, smul_eq_zero] at h
        exact h.resolve_right h₂.1
      have hy₀L : y₀ ∈ L := Submodule.mem_inf.mpr ⟨hf, hg⟩
      exact hy₀ (Submodule.disjoint_def.mp hPL.disjoint _ (Submodule.mem_inf.mp hy₀mem).2 hy₀L)
  have hYL : Y ⊓ L = ⊥ ∨ Y ⊓ L = L := by
    have hle : Y ⊓ L ≤ L := inf_le_right
    have hfin := Submodule.finrank_mono hle
    rw [hL1] at hfin
    rcases Nat.lt_or_ge (finrank (ZMod 3) ↥(Y ⊓ L)) 1 with h | h
    · left
      exact Submodule.finrank_eq_zero.mp (by omega)
    · right
      exact Submodule.eq_of_le_of_finrank_eq hle (by omega)
  rcases hYP with h | h <;> rcases hYL with h' | h'
  · left
    rw [hdec, h, h', bot_sup_eq]
  · right; right; left
    rw [hdec, h, h', bot_sup_eq]
  · right; left
    rw [hdec, h, h', sup_bot_eq]
  · right; right; right
    rw [hdec, h, h', hPL.sup_eq_top]

theorem mem_pair_of_pow_of_mapsTo_span (hV : finrank (ZMod 3) V = 3)
    (G : Subgroup (V ≃ₗ[ZMod 3] V)) (hGP : ∀ x ∈ G, ∀ p ∈ Submodule.span (ZMod 3) {v, w},
      x p ∈ Submodule.span (ZMod 3) {v, w})
    (hXG : Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)) ≤ G)
    (hcore : ∀ k : G, k ∈ CFSG.pCore 3 G → k = 1) {y : V ≃ₗ[ZMod 3] V} (hyG : y ∈ G) {k : ℕ}
    (hy : y ^ (3 ^ k) = 1) : y ∈ Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)) := by
  set P := Submodule.span (ZMod 3) {v, w}
  set L := LinearMap.ker f ⊓ LinearMap.ker g
  have hPL : IsCompl P L := isCompl_span_pair_ker_inf_ker h₁.2.2.1 h₂.2.2.1 hfw hgv
  have hL1 : finrank (ZMod 3) L = 1 := (finrank_pair h₁ h₂ hfw hgv hV).2
  have hyP := hGP y hyG
  obtain ⟨x, hxX, hxP, hxL⟩ := exists_mem_of_det_eq_one
    (H := Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V))) h₁ h₂
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hfw hgv
    ((y : V →ₗ[ZMod 3] V).restrict hyP) (det_restrict_eq_one_of_pow hyP hy)
  have hxP' : ∀ p ∈ P, x p = y p := fun p hp => hxP ⟨p, hp⟩
  have hxPm := (pair_mapsTo_and_fix h₁ h₂ hxX).1
  have hxinvP := inv_mapsTo hxPm
  have hxinvL : ∀ l ∈ L, x⁻¹ l = l := fun l hl => by
    change x.symm l = l
    rw [LinearEquiv.symm_apply_eq, hxL l hl]
  have hflag : IsFlagUnipotent ⊥ P (x⁻¹ * y) := by
    refine ⟨fun z => ?_, fun z hz => ?_, fun z hz => ?_⟩
    · have h1 := sub_mem_of_mapsTo_of_pow hPL hL1 hyP hy z
      have h2 := sub_mem_of_mapsTo_of_fix hPL hxinvP hxinvL z
      have : (x⁻¹ * y) z - z = x⁻¹ (y z - z) + (x⁻¹ z - z) := by
        rw [LinearEquiv.mul_apply, map_sub]; abel
      rw [this]
      exact P.add_mem (hxinvP _ h1) h2
    · rw [LinearEquiv.mul_apply, ← hxP' z hz]
      change x.symm (x z) - z ∈ ⊥
      rw [LinearEquiv.symm_apply_apply, sub_self]
      exact Submodule.zero_mem _
    · rw [Submodule.mem_bot] at hz
      rw [hz, map_zero]
  have hkG : x⁻¹ * y ∈ G := G.mul_mem (G.inv_mem (hXG hxX)) hyG
  have hk1 := hcore ⟨x⁻¹ * y, hkG⟩ (mem_pCore_of_isFlagUnipotent G bot_le
    (fun g _ z hz => by rw [Submodule.mem_bot] at hz ⊢; rw [hz, map_zero]) hGP hflag)
  have : x⁻¹ * y = 1 := congrArg Subtype.val hk1
  rw [inv_mul_eq_one] at this
  rw [← this]
  exact hxX

theorem mem_pair_of_pow_of_mapsTo_ker (hV : finrank (ZMod 3) V = 3)
    (G : Subgroup (V ≃ₗ[ZMod 3] V)) (hGL : ∀ x ∈ G, ∀ l ∈ LinearMap.ker f ⊓ LinearMap.ker g,
      x l ∈ LinearMap.ker f ⊓ LinearMap.ker g)
    (hXG : Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)) ≤ G)
    (hcore : ∀ k : G, k ∈ CFSG.pCore 3 G → k = 1) {y : V ≃ₗ[ZMod 3] V} (hyG : y ∈ G) {k : ℕ}
    (hy : y ^ (3 ^ k) = 1) : y ∈ Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V)) := by
  set P := Submodule.span (ZMod 3) {v, w}
  set L := LinearMap.ker f ⊓ LinearMap.ker g
  have hPL : IsCompl P L := isCompl_span_pair_ker_inf_ker h₁.2.2.1 h₂.2.2.1 hfw hgv
  have hL1 : finrank (ZMod 3) L = 1 := (finrank_pair h₁ h₂ hfw hgv hV).2
  have hyL : ∀ l ∈ L, y l = l := by
    obtain ⟨l₀, -, hl₀⟩ := exists_eq_span_of_finrank_eq_one hL1
    have hl₀L : l₀ ∈ L := by rw [hl₀]; exact Submodule.mem_span_singleton_self l₀
    have hyl₀ : y l₀ = l₀ := by
      refine apply_eq_self_of_map_eq hy ?_
      rw [← hl₀]
      exact hGL y hyG l₀ hl₀L
    intro l hl
    rw [hl₀] at hl
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hl
    rw [map_smul, hyl₀]
  set φ := (P.projectionOnto L hPL).comp ((y : V →ₗ[ZMod 3] V).comp P.subtype) with hφdef
  obtain ⟨x, hxX, hxP, hxL⟩ := exists_mem_of_det_eq_one
    (H := Subgroup.closure ({t₁, t₂} : Set (V ≃ₗ[ZMod 3] V))) h₁ h₂
    (Subgroup.subset_closure (by simp)) (Subgroup.subset_closure (by simp)) hfw hgv
    φ (det_projection_comp_eq_one hPL hyL hy)
  have hxinvL : ∀ l ∈ L, x⁻¹ l = l := fun l hl => by
    change x.symm l = l
    rw [LinearEquiv.symm_apply_eq, hxL l hl]
  have hflag : IsFlagUnipotent ⊥ L (x⁻¹ * y) := by
    refine ⟨fun z => ?_, fun z hz => ?_, fun z hz => ?_⟩
    · have hz : z ∈ P ⊔ L := by rw [hPL.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.mp hz
      have hφp : (φ ⟨p, hp⟩ : V) = P.projection L hPL (y p) := rfl
      have hdiff : y p - (φ ⟨p, hp⟩ : V) ∈ L := by
        rw [hφp]
        have h := Submodule.projection_add_projection_eq_self hPL (y p)
        have : y p - P.projection L hPL (y p) = L.projection P hPL.symm (y p) := by
          rw [sub_eq_iff_eq_add']
          exact h.symm
        rw [this]
        exact Submodule.projection_apply_mem hPL.symm _
      have hxp : x⁻¹ (φ ⟨p, hp⟩ : V) = p := by
        rw [← hxP ⟨p, hp⟩]
        change x.symm (x p) = p
        rw [LinearEquiv.symm_apply_apply]
      have : (x⁻¹ * y) (p + l) - (p + l) = x⁻¹ (y p - (φ ⟨p, hp⟩ : V)) := by
        rw [LinearEquiv.mul_apply, map_add, hyL l hl, map_add, hxinvL l hl, map_sub, hxp]
        abel
      rw [this, hxinvL _ hdiff]
      exact hdiff
    · rw [LinearEquiv.mul_apply, hyL z hz, hxinvL z hz, sub_self]
      exact Submodule.zero_mem _
    · rw [Submodule.mem_bot] at hz
      rw [hz, map_zero]
  have hkG : x⁻¹ * y ∈ G := G.mul_mem (G.inv_mem (hXG hxX)) hyG
  have hk1 := hcore ⟨x⁻¹ * y, hkG⟩ (mem_pCore_of_isFlagUnipotent G bot_le
    (fun g _ z hz => by rw [Submodule.mem_bot] at hz ⊢; rw [hz, map_zero]) hGL hflag)
  have : x⁻¹ * y = 1 := congrArg Subtype.val hk1
  rw [inv_mul_eq_one] at this
  rw [← this]
  exact hxX

end PairFacts

theorem rank3II_3_14 (hV : finrank (ZMod 3) V = 3) (G : Subgroup (V ≃ₗ[ZMod 3] V))
    {r : V ≃ₗ[ZMod 3] V} (hrG : r ∈ G) (hr : ∃ v f, IsTransvectionWith r v f)
    {U : Submodule (ZMod 3) V} (hU : U = LinearMap.range ((r : V →ₗ[ZMod 3] V) - 1))
    (hsyl : CFSG.ABGLocalTools.IsSylowOf 3 (Subgroup.zpowers r)
      (G ⊓ fixingSubgroup (V ≃ₗ[ZMod 3] V) (U : Set V))) :
    (∀ g ∈ G, U.map (g : V →ₗ[ZMod 3] V) = U) ∨
      Nonempty (CFSG.GH74.GLS.oPrimeResidual 3 G ≃* SL(2, ZMod 3)) := by
  classical
  have : Finite (V ≃ₗ[ZMod 3] V) := finite_linearEquiv
  obtain ⟨v, f, hrt⟩ := hr
  have hUv : U = Submodule.span (ZMod 3) {v} := hU.trans (range_sub_one_eq_span hrt)
  by_cases hN : ∀ g ∈ G, U.map (g : V →ₗ[ZMod 3] V) = U
  · exact Or.inl hN
  right
  obtain ⟨g₀, hg₀G, hg₀U⟩ : ∃ g ∈ G, U.map (g : V →ₗ[ZMod 3] V) ≠ U := by
    by_contra! h
    exact hN h
  set C := G ⊓ fixingSubgroup (V ≃ₗ[ZMod 3] V) (U : Set V) with hCdef
  have hrord : orderOf r = 3 := orderOf_eq_three_of_isTransvectionWith hrt
  have hr3 : IsPGroup 3 (Subgroup.zpowers r) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hrord, pow_one])
  have hnorm : ∀ g : V ≃ₗ[ZMod 3] V, g * r * g⁻¹ ∈ Subgroup.zpowers r →
      U.map (g : V →ₗ[ZMod 3] V) = U := fun g hg => by
    rw [hUv]
    exact map_eq_of_mapsTo (mapsTo_span_of_conj_mem hrt hg)
  have hmemC : ∀ g ∈ G, (∃ k : ℕ, g ^ (3 ^ k) = 1) → g * r * g⁻¹ ∈ Subgroup.zpowers r →
      g ∈ C := by
    rintro g hg ⟨k, hk⟩ hgr
    refine Subgroup.mem_inf.mpr ⟨hg, ?_⟩
    rw [hUv, mem_fixingSubgroup_span_iff]
    exact apply_eq_self_of_map_eq hk
      (mapsTo_span_of_conj_mem hrt hgr v (Submodule.mem_span_singleton_self v))
  have hmax : ∀ Q : Subgroup (V ≃ₗ[ZMod 3] V), Q ≤ G → IsPGroup 3 Q →
      Subgroup.zpowers r ≤ Q → Q = Subgroup.zpowers r := by
    intro Q hQG hQ hrQ
    by_contra hne
    have hlt : Subgroup.zpowers r < Q := lt_of_le_of_ne hrQ (Ne.symm hne)
    obtain ⟨n, hnQ, hnr, hnN⟩ := exists_conj_mem_of_lt hQ hlt
    have hn3 : ∃ k : ℕ, n ^ (3 ^ k) = 1 := by
      obtain ⟨k, hk⟩ := hQ ⟨n, hnQ⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
    have hnC : n ∈ C := hmemC n (hQG hnQ) hn3 (hnN r (Subgroup.mem_zpowers r))
    have hRC : Subgroup.zpowers r ⊔ Subgroup.zpowers n ≤ C :=
      sup_le hsyl.le (Subgroup.zpowers_le.mpr hnC)
    have hRp : IsPGroup 3 (Subgroup.zpowers r ⊔ Subgroup.zpowers n : Subgroup _) :=
      hQ.to_le (sup_le hrQ (Subgroup.zpowers_le.mpr hnQ))
    have heq := eq_of_isSylowOf hsyl hRC hRp le_sup_left
    exact hnr (heq ▸ (le_sup_right : Subgroup.zpowers n ≤ _) (Subgroup.mem_zpowers n))
  obtain ⟨P₀, hP₀⟩ := IsPGroup.exists_le_sylow (p := 3)
    (hr3.comap_subtype (K := G) : IsPGroup 3 ((Subgroup.zpowers r).subgroupOf G))
  have hP₀eq : (P₀ : Subgroup G).map G.subtype = Subgroup.zpowers r := by
    refine hmax _ (Subgroup.map_subtype_le _) (P₀.isPGroup'.map _) ?_
    rw [← Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr hrG)]
    exact Subgroup.map_mono hP₀
  have hcore : ∀ k : G, k ∈ CFSG.pCore 3 G → k = 1 := by
    intro k hk
    have hkr : ∀ k' : G, k' ∈ CFSG.pCore 3 G → (k' : V ≃ₗ[ZMod 3] V) ∈ Subgroup.zpowers r :=
      fun k' hk' => hP₀eq ▸ Subgroup.mem_map_of_mem _
        (IsPGroup.le_sylow_of_normal CFSG.pCore_isPGroup P₀ hk')
    by_contra hk1
    have hk1' : (k : V ≃ₗ[ZMod 3] V) ≠ 1 := fun h => hk1 (Subtype.ext h)
    have hkord : orderOf (k : V ≃ₗ[ZMod 3] V) = 3 := by
      have hdvd : orderOf (k : V ≃ₗ[ZMod 3] V) ∣ 3 := by
        have := orderOf_dvd_of_mem_zpowers (hkr k hk)
        rwa [hrord] at this
      rcases (Nat.dvd_prime Nat.prime_three).mp hdvd with h | h
      · exact absurd (orderOf_eq_one_iff.mp h) hk1'
      · exact h
    have heq : Subgroup.zpowers (k : V ≃ₗ[ZMod 3] V) = Subgroup.zpowers r :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr (hkr k hk))
        (by rw [Nat.card_zpowers, Nat.card_zpowers, hkord, hrord])
    obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp (heq ▸ Subgroup.mem_zpowers r)
    have hrcore : (⟨r, hrG⟩ : G) ∈ CFSG.pCore 3 G := by
      have : (⟨r, hrG⟩ : G) = k ^ m := Subtype.ext (by rw [Subgroup.coe_zpow, hm])
      rw [this]
      exact Subgroup.zpow_mem _ hk m
    apply hg₀U
    apply hnorm
    have hconj : (⟨g₀, hg₀G⟩ * ⟨r, hrG⟩ * (⟨g₀, hg₀G⟩ : G)⁻¹ : G) ∈ CFSG.pCore 3 G :=
      CFSG.pCore_normal.conj_mem _ hrcore _
    exact hkr _ hconj
  have hrnot : (⟨r, hrG⟩ : G) ∉ CFSG.pCore 3 G := fun h =>
    ne_one_of_isTransvectionWith hrt (congrArg Subtype.val (hcore _ h))
  rw [CFSG.BaerSuzuki.baer_suzuki_iff] at hrnot
  obtain ⟨g, hg⟩ : ∃ g : G, ¬ IsPGroup 3
      (Subgroup.closure ({⟨r, hrG⟩, g * ⟨r, hrG⟩ * g⁻¹} : Set G)) := by
    by_contra! h
    exact hrnot h
  set r' : V ≃ₗ[ZMod 3] V := (g : V ≃ₗ[ZMod 3] V) * r * (g : V ≃ₗ[ZMod 3] V)⁻¹ with hr'def
  have hr'G : r' ∈ G := G.mul_mem (G.mul_mem g.2 hrG) (G.inv_mem g.2)
  have hr't := hrt.conj (g : V ≃ₗ[ZMod 3] V)
  have hnp : ¬ IsPGroup 3 (Subgroup.closure ({r, r'} : Set (V ≃ₗ[ZMod 3] V))) := by
    intro hp
    apply hg
    have hmap : (Subgroup.closure ({⟨r, hrG⟩, g * ⟨r, hrG⟩ * g⁻¹} : Set G)).map G.subtype =
        Subgroup.closure ({r, r'} : Set (V ≃ₗ[ZMod 3] V)) := by
      rw [MonoidHom.map_closure, Set.image_pair]
      rfl
    rw [← hmap] at hp
    exact hp.of_equiv (Subgroup.equivMapOfInjective _ _ G.subtype_injective).symm
  have hfg : f ((g : V ≃ₗ[ZMod 3] V) v) *
      (f.comp ((g : V ≃ₗ[ZMod 3] V).symm : V →ₗ[ZMod 3] V)) v ≠ 0 := fun h0 =>
    hnp (isPGroup_closure_pair_of_mul_eq_zero hrt hr't h0)
  have hfw := left_ne_zero_of_mul hfg
  have hgv := right_ne_zero_of_mul hfg
  set X := Subgroup.closure ({r, r'} : Set (V ≃ₗ[ZMod 3] V)) with hXdef
  have hXG : X ≤ G := by
    rw [hXdef, Subgroup.closure_le]
    rintro x (rfl | rfl)
    · exact hrG
    · exact hr'G
  obtain ⟨e⟩ := nonempty_pair_mulEquiv hrt hr't hfw hgv
  obtain ⟨Y, hY0, hYtop, hYG⟩ : ∃ Y : Submodule (ZMod 3) V, Y ≠ ⊥ ∧ Y ≠ ⊤ ∧
      ∀ x ∈ G, ∀ y ∈ Y, x y ∈ Y := by
    by_contra! hirr
    have hirr' : ∀ W : Submodule (ZMod 3) V, (∀ x ∈ G, ∀ y ∈ W, x y ∈ W) → W = ⊥ ∨ W = ⊤ := by
      intro W hW
      by_contra h
      rw [not_or] at h
      exact (hirr W h.1 h.2).elim fun x hx => by
        obtain ⟨hxG, y, hyW, hy⟩ := hx
        exact hy (hW x hxG y hyW)
    have hSL := det_eq_one_mem_of_irreducible hV G hirr' hrG hrt
    obtain ⟨s, h, hst, hsr⟩ := exists_transvection_same_center hV hrt
    have hsG : s ∈ G := hSL s (det_eq_one_of_isTransvectionWith hst)
    have hsC : s ∈ C := by
      refine Subgroup.mem_inf.mpr ⟨hsG, ?_⟩
      rw [hUv, mem_fixingSubgroup_span_iff, hst.2.2.2, hst.2.2.1, zero_smul, add_zero]
    have hcomm : r * s = s * r := by
      ext x
      rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, hst.2.2.2 x, hrt.2.2.2 x, hrt.2.2.2,
        hst.2.2.2]
      simp only [map_add, map_smul, hrt.2.2.1, hst.2.2.1, smul_eq_mul, mul_zero, add_zero]
      abel
    have hs3 : IsPGroup 3 (Subgroup.zpowers s) :=
      IsPGroup.of_card (n := 1)
        (by rw [Nat.card_zpowers, orderOf_eq_three_of_isTransvectionWith hst, pow_one])
    have hRp : IsPGroup 3 (Subgroup.zpowers r ⊔ Subgroup.zpowers s : Subgroup _) := by
      refine IsPGroup.to_sup_of_normal_right' hr3 hs3 ?_
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro t
      constructor
      · intro ht
        obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.mp ht
        rw [show r * s ^ m * r⁻¹ = s ^ m by
          rw [(Commute.zpow_right hcomm m).eq, mul_inv_cancel_right]]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers s) m
      · intro ht
        have : t = r⁻¹ * (r * t * r⁻¹) * r := by group
        rw [this]
        obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp ht
        rw [← hm, show r⁻¹ * s ^ m * r = s ^ m by
          rw [mul_assoc, ← (Commute.zpow_right hcomm m).eq, inv_mul_cancel_left]]
        exact Subgroup.zpow_mem _ (Subgroup.mem_zpowers s) m
    have hRC : Subgroup.zpowers r ⊔ Subgroup.zpowers s ≤ C :=
      sup_le hsyl.le (Subgroup.zpowers_le.mpr hsC)
    have heq := eq_of_isSylowOf hsyl hRC hRp le_sup_left
    exact hsr (heq ▸ (le_sup_right : Subgroup.zpowers s ≤ _) (Subgroup.mem_zpowers s))
  set P := Submodule.span (ZMod 3) {v, (g : V ≃ₗ[ZMod 3] V) v} with hPdef
  set L := LinearMap.ker f ⊓ LinearMap.ker (f.comp ((g : V ≃ₗ[ZMod 3] V).symm : V →ₗ[ZMod 3] V))
    with hLdef
  have hYX : ∀ x ∈ X, ∀ y ∈ Y, x y ∈ Y := fun x hx => hYG x (hXG hx)
  have h3el : ∀ y : G, (∃ k : ℕ, y ^ (3 ^ k) = 1) → (y : V ≃ₗ[ZMod 3] V) ∈ X := by
    rintro y ⟨k, hk⟩
    have hk' : (y : V ≃ₗ[ZMod 3] V) ^ (3 ^ k) = 1 := by
      rw [← Subgroup.coe_pow, hk]; rfl
    rcases invariant_subspaces_pair hrt hr't hfw hgv hV hYX with h | h | h | h
    · exact absurd h hY0
    · exact mem_pair_of_pow_of_mapsTo_span hrt hr't hfw hgv hV G (h ▸ hYG) hXG hcore y.2 hk'
    · exact mem_pair_of_pow_of_mapsTo_ker hrt hr't hfw hgv hV G (h ▸ hYG) hXG hcore y.2 hk'
    · exact absurd h hYtop
  have hO : CFSG.GH74.GLS.oPrimeResidual 3 G = X.subgroupOf G := by
    apply le_antisymm
    · rw [CFSG.GH74.GLS.oPrimeResidual, Subgroup.closure_le]
      intro y hy
      exact h3el y hy
    · have hle : X ≤ (CFSG.GH74.GLS.oPrimeResidual 3 G).map G.subtype := by
        rw [hXdef, Subgroup.closure_le]
        intro x hx
        have hrO : (⟨r, hrG⟩ : G) ∈ CFSG.GH74.GLS.oPrimeResidual 3 G :=
          Subgroup.subset_closure ⟨1, Subtype.ext (by
            rw [pow_one, Subgroup.coe_pow, pow_three_eq_one_of_isTransvectionWith hrt]; rfl)⟩
        have hr'O : (⟨r', hr'G⟩ : G) ∈ CFSG.GH74.GLS.oPrimeResidual 3 G :=
          Subgroup.subset_closure ⟨1, Subtype.ext (by
            rw [pow_one, Subgroup.coe_pow, pow_three_eq_one_of_isTransvectionWith hr't]; rfl)⟩
        rcases hx with hx | hx
        · exact ⟨⟨r, hrG⟩, hrO, hx.symm⟩
        · rw [Set.mem_singleton_iff] at hx
          exact ⟨⟨r', hr'G⟩, hr'O, hx.symm⟩
      intro x hx
      have := hle hx
      obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp this
      have : y = x := Subtype.ext hyx
      rw [← this]
      exact hy
  exact ⟨(MulEquiv.subgroupCongr hO).trans ((Subgroup.subgroupOfEquivOfLe hXG).trans e)⟩

end CFSG.RankThree.PartTwo.Sec3

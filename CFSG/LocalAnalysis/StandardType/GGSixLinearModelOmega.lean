module

public import CFSG.LocalAnalysis.StandardType.GGLinearTorusCompBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly Matrix

namespace LinModel

variable {m : ℕ} {F : Type} [Field F] {G : Type*} [Group G]

theorem mem_normalizer_of_mem_ggInducedPairs
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {g : G} {A : GL (Fin (m + 1)) F}
    (h : (g, A) ∈ LinFusion.ggInducedPairs ψ) :
    g ∈ Subgroup.normalizer (ψ.range : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · rintro ⟨u, rfl⟩
    exact ⟨_, (LinFusion.mem_ggInducedPairs.mp h u).symm⟩
  · rintro ⟨v, hv⟩
    have h' := (LinFusion.ggInducedPairs ψ).inv_mem h
    rw [Prod.inv_mk] at h'
    refine ⟨InnerDiagA.conjSL A⁻¹ v, ?_⟩
    rw [← LinFusion.mem_ggInducedPairs.mp h' v, hv]
    group

theorem mem_ggInducedPairs_comp_conjSL_inv
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {g : G} {A : GL (Fin (m + 1)) F}
    (h : (g, A) ∈ LinFusion.ggInducedPairs ψ) (P : GL (Fin (m + 1)) F) :
    (g, P * A * P⁻¹) ∈ LinFusion.ggInducedPairs (ψ.comp (InnerDiagA.conjSL P⁻¹)) := by
  intro u
  show g * ψ (InnerDiagA.conjSL P⁻¹ u) * g⁻¹ =
    ψ (InnerDiagA.conjSL P⁻¹ (InnerDiagA.conjSL (P * A * P⁻¹) u))
  rw [LinFusion.mem_ggInducedPairs.mp h, ← LinFusion.conjSL_mul, ← LinFusion.conjSL_mul,
    show P⁻¹ * (P * A * P⁻¹) = A * P⁻¹ by group]

theorem map_toGL_mem_ggInducedPairs (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (s : Matrix.SpecialLinearGroup (Fin (m + 1)) F) :
    (ψ s, Matrix.SpecialLinearGroup.toGL s) ∈ LinFusion.ggInducedPairs ψ := by
  intro u
  rw [LinFusion.conjSL_toGL, map_mul, map_mul, map_inv]

theorem scalar_mul_mem_ggInducedPairs {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    {g : G} {A : GL (Fin (m + 1)) F} (h : (g, A) ∈ LinFusion.ggInducedPairs ψ) (c : Fˣ) :
    (g, GeneralLinearGroup.scalar (Fin (m + 1)) c * A) ∈ LinFusion.ggInducedPairs ψ := by
  have h1 := (LinFusion.ggInducedPairs ψ).mul_mem (LinTorus.one_scalar_mem_ggInducedPairs ψ c) h
  rwa [Prod.mk_mul_mk, one_mul] at h1

theorem diagGL_pow (d : Fin (m + 1) → Fˣ) (k : ℕ) :
    InnerDiagA.diagGL (d ^ k) = InnerDiagA.diagGL d ^ k := by
  induction k with
  | zero => rw [pow_zero, pow_zero, LinFusion.diagGL_one]
  | succ k ih => rw [pow_succ, pow_succ, LinFusion.diagGL_mul, ih]

theorem diagGL_apply (d : Fin (m + 1) → Fˣ) (i j : Fin (m + 1)) :
    ((InnerDiagA.diagGL d : GL (Fin (m + 1)) F) : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i j =
      if i = j then (d i : F) else 0 := by
  rw [InnerDiagA.coe_diagGL, diagonal_apply]

theorem scalar_mul_diagGL (c : Fˣ) (d : Fin (m + 1) → Fˣ) :
    GeneralLinearGroup.scalar (Fin (m + 1)) c * InnerDiagA.diagGL d =
      InnerDiagA.diagGL (fun i => c * d i) := by
  apply Units.ext
  rw [Units.val_mul, GeneralLinearGroup.coe_scalar, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL]
  ext i j
  rw [Matrix.scalar_apply, diagonal_mul_diagonal]
  simp

theorem eq_of_diagGL_eq_scalar_mul {d e : Fin (m + 1) → Fˣ} {c : Fˣ}
    (h : InnerDiagA.diagGL e = GeneralLinearGroup.scalar (Fin (m + 1)) c * InnerDiagA.diagGL d)
    (h0 : d 0 = e 0) : d = e := by
  rw [scalar_mul_diagGL] at h
  have hentry : ∀ i, e i = c * d i := fun i => by
    have := congrArg (fun A : GL (Fin (m + 1)) F =>
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) F) i i) h
    simp only [diagGL_apply] at this
    exact Units.ext (by rw [Units.val_mul]; exact this)
  have hc : c = 1 := by
    have := hentry 0
    rw [h0] at this
    exact (mul_eq_right.mp this.symm)
  funext i
  rw [hentry i, hc, one_mul]

@[expose] noncomputable def diagSL (d : Fin (m + 1) → Fˣ) (hd : ∏ i, d i = 1) :
    Matrix.SpecialLinearGroup (Fin (m + 1)) F :=
  ⟨diagonal fun i => (d i : F), by
    rw [det_diagonal, ← Units.coe_prod, hd, Units.val_one]⟩

theorem toGL_diagSL (d : Fin (m + 1) → Fˣ) (hd : ∏ i, d i = 1) :
    Matrix.SpecialLinearGroup.toGL (diagSL d hd) = InnerDiagA.diagGL d :=
  Units.ext rfl

theorem exists_mem_of_prod_eq_one (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (d : Fin (m + 1) → Fˣ) (hd : ∏ i, d i = 1) :
    (ψ (diagSL d hd), InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ := by
  rw [← toGL_diagSL d hd]
  exact map_toGL_mem_ggInducedPairs ψ _

theorem exists_mem_of_scalar (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G)
    (d : Fin (m + 1) → Fˣ) (c : Fˣ) (hd : ∏ i, c * d i = 1) :
    ∃ g ∈ ψ.range, (g, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ := by
  refine ⟨ψ (diagSL (fun i => c * d i) hd), ⟨_, rfl⟩, ?_⟩
  have h := scalar_mul_mem_ggInducedPairs (exists_mem_of_prod_eq_one ψ _ hd) c⁻¹
  rwa [← scalar_mul_diagGL, ← mul_assoc, ← map_mul, inv_mul_cancel, map_one, one_mul] at h


theorem exists_mem_of_det [Finite F] {p : ℕ} [Fact p.Prime] (hmp : m + 1 = p)
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {g₀ : G} {A₀ : GL (Fin (m + 1)) F}
    (h₀ : (g₀, A₀) ∈ LinFusion.ggInducedPairs ψ)
    (hdet : ¬ ∃ c : Fˣ, c ^ p = GeneralLinearGroup.det A₀) (A : GL (Fin (m + 1)) F) :
    ∃ g : G, (g, A) ∈ LinFusion.ggInducedPairs ψ := by
  set x : TypeA.PGLTor.PowQuot F p := QuotientGroup.mk (GeneralLinearGroup.det A₀) with hx
  have hx1 : x ≠ 1 := fun h => hdet (TypeA.PGLTor.powQuot_mk_eq_one_iff.mp h)
  have hxp : x ^ p = 1 := by
    rw [hx, ← QuotientGroup.mk_pow, TypeA.PGLTor.powQuot_mk_eq_one_iff]
    exact ⟨_, rfl⟩
  have hord : orderOf x = p := orderOf_eq_prime hxp hx1
  have : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have htop : Subgroup.zpowers x = ⊤ := by
    apply Subgroup.eq_top_of_le_card
    rw [Nat.card_zpowers, hord]
    exact TypeA.PGLTor.card_powQuot_le
  have hmem : (QuotientGroup.mk (GeneralLinearGroup.det A) : TypeA.PGLTor.PowQuot F p) ∈
      Subgroup.zpowers x := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  rw [hx, ← QuotientGroup.mk_zpow, QuotientGroup.eq] at hk
  obtain ⟨c, hc⟩ := hk
  have hc' : c ^ p = (GeneralLinearGroup.det A₀ ^ k)⁻¹ * GeneralLinearGroup.det A := hc
  have hdetA : GeneralLinearGroup.det A = GeneralLinearGroup.det A₀ ^ k * c ^ p := by
    rw [hc']
    group
  set S : GL (Fin (m + 1)) F := GeneralLinearGroup.scalar (Fin (m + 1)) c⁻¹ * A * A₀ ^ (-k)
    with hS
  have hscal : ∀ u : Fˣ, GeneralLinearGroup.det (GeneralLinearGroup.scalar (Fin (m + 1)) u) =
      u ^ p := fun u => by
    apply Units.ext
    rw [GeneralLinearGroup.val_det_apply, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      det_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, hmp, Units.val_pow_eq_pow_val]
  have hSdet : GeneralLinearGroup.det S = 1 := by
    rw [hS, map_mul, map_mul, map_zpow, hscal, hdetA,
      mul_comm (GeneralLinearGroup.det A₀ ^ k) (c ^ p)]
    group
  set s : Matrix.SpecialLinearGroup (Fin (m + 1)) F := ⟨(S : Matrix (Fin (m + 1)) (Fin (m + 1)) F),
    by rw [← GeneralLinearGroup.val_det_apply, hSdet, Units.val_one]⟩ with hs
  have hsS : Matrix.SpecialLinearGroup.toGL s = S := Units.ext rfl
  refine ⟨ψ s * g₀ ^ k, ?_⟩
  have h1 := (LinFusion.ggInducedPairs ψ).mul_mem (map_toGL_mem_ggInducedPairs ψ s)
    ((LinFusion.ggInducedPairs ψ).zpow_mem h₀ k)
  rw [Prod.pow_mk, Prod.mk_mul_mk, hsS] at h1
  have h2 := scalar_mul_mem_ggInducedPairs h1 c
  have hA : GeneralLinearGroup.scalar (Fin (m + 1)) c * (S * A₀ ^ k) = A := by
    rw [hS, ← mul_assoc, ← mul_assoc, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul,
      mul_assoc, ← _root_.zpow_add, neg_add_cancel, zpow_zero, mul_one]
  rwa [hA] at h2

theorem mul_comm_of_mem_diag {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {g h : G} {d e : Fin (m + 1) → Fˣ}
    (hg : (g, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ)
    (hh : (h, InnerDiagA.diagGL e) ∈ LinFusion.ggInducedPairs ψ) : g * h = h * g := by
  have hc := (LinFusion.ggInducedPairs ψ).mul_mem ((LinFusion.ggInducedPairs ψ).mul_mem hg hh)
    ((LinFusion.ggInducedPairs ψ).inv_mem ((LinFusion.ggInducedPairs ψ).mul_mem hh hg))
  rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.inv_mk, Prod.mk_mul_mk,
    LinFusion.diagGL_mul_comm d e, mul_inv_cancel] at hc
  have h2 := LinFusion.mem_centralizer_of_mem_ggInducedPairs_one hc
  rw [hC, Subgroup.mem_bot, mul_inv_eq_one] at h2
  exact h2

variable (p : ℕ) (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G) in
@[expose] def rootTorus : Subgroup G where
  carrier := {g | ∃ d : Fin (m + 1) → Fˣ, (∀ i, d i ^ p = 1) ∧
    (g, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ}
  one_mem' := ⟨1, fun _ => one_pow _, by
    rw [LinFusion.diagGL_one]
    exact (LinFusion.ggInducedPairs ψ).one_mem⟩
  mul_mem' := by
    rintro g h ⟨d, hd, hgd⟩ ⟨e, he, hhe⟩
    refine ⟨d * e, fun i => by rw [Pi.mul_apply, mul_pow, hd, he, one_mul], ?_⟩
    rw [LinFusion.diagGL_mul]
    exact (LinFusion.ggInducedPairs ψ).mul_mem hgd hhe
  inv_mem' := by
    rintro g ⟨d, hd, hgd⟩
    refine ⟨d⁻¹, fun i => by rw [Pi.inv_apply, inv_pow, hd, inv_one], ?_⟩
    rw [LinFusion.diagGL_inv]
    exact (LinFusion.ggInducedPairs ψ).inv_mem hgd

theorem mem_rootTorus {p : ℕ} {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G} {g : G} :
    g ∈ rootTorus p ψ ↔ ∃ d : Fin (m + 1) → Fˣ, (∀ i, d i ^ p = 1) ∧
      (g, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ :=
  Iff.rfl

theorem isElemAbelian_rootTorus {p : ℕ} {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) : IsElemAbelian p (rootTorus p ψ) := by
  refine ⟨⟨⟨fun ⟨g, hg⟩ ⟨h, hh⟩ => Subtype.ext ?_⟩⟩, fun g hg => ?_⟩
  · obtain ⟨d, -, hd⟩ := hg
    obtain ⟨e, -, he⟩ := hh
    exact mul_comm_of_mem_diag hC hd he
  · obtain ⟨d, hdp, hd⟩ := hg
    have h1 := (LinFusion.ggInducedPairs ψ).pow_mem hd p
    rw [Prod.pow_mk, ← diagGL_pow, show d ^ p = 1 from funext hdp, LinFusion.diagGL_one] at h1
    have h2 := LinFusion.mem_centralizer_of_mem_ggInducedPairs_one h1
    rwa [hC, Subgroup.mem_bot] at h2

theorem rootTorus_le_normalizer (p : ℕ) (ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G) :
    rootTorus p ψ ≤ Subgroup.normalizer (ψ.range : Set G) := fun _ ⟨_, _, hd⟩ =>
  mem_normalizer_of_mem_ggInducedPairs hd

theorem rootTorus_le {p : ℕ} {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hC : Subgroup.centralizer (ψ.range : Set G) = ⊥) {Bs : Subgroup G}
    (hBs : ∀ b ∈ Bs, ∃ d : Fin (m + 1) → Fˣ,
      (b, InnerDiagA.diagGL d) ∈ LinFusion.ggInducedPairs ψ)
    (hom : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs) :
    rootTorus p ψ ≤ Bs := by
  intro g hg
  refine hom g ?_ ((isElemAbelian_rootTorus hC).2 g hg)
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  obtain ⟨d, -, hd⟩ := hg
  obtain ⟨e, he⟩ := hBs b hb
  exact mul_comm_of_mem_diag hC he hd

theorem pow_val_add {p : ℕ} [NeZero p] {ω : Fˣ} (hω : ω ^ p = 1) (a b : ZMod p) :
    ω ^ (a + b).val = ω ^ a.val * ω ^ b.val := by
  rw [ZMod.val_add, ← pow_add]
  conv_rhs => rw [← Nat.div_add_mod (a.val + b.val) p, pow_add, pow_mul, hω, one_pow, one_mul]

theorem card_le_card_rootTorus [CharP F 2] [Finite G] {p : ℕ} [NeZero p]
    {ψ : Matrix.SpecialLinearGroup (Fin (m + 1)) F →* G}
    (hker : ψ.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin (m + 1)) F))
    {ω : Fˣ} (hω : IsPrimitiveRoot ω p) {X : Type*} (a : X → Fin (m + 1) → ZMod p)
    (ha0 : ∀ x, a x 0 = 0) (hainj : Function.Injective a)
    (hreal : ∀ x, ∃ g : G, (g, InnerDiagA.diagGL (fun i => ω ^ (a x i).val)) ∈
      LinFusion.ggInducedPairs ψ) :
    Nat.card X ≤ Nat.card (rootTorus p ψ) := by
  choose g hg using hreal
  have hmem : ∀ x, g x ∈ rootTorus p ψ := fun x =>
    ⟨_, fun i => by rw [← pow_mul, mul_comm, pow_mul, hω.pow_eq_one, one_pow], hg x⟩
  refine Nat.card_le_card_of_injective (fun x => ⟨g x, hmem x⟩) fun x y hxy => ?_
  have hgxy : g x = g y := congrArg Subtype.val hxy
  have hy := hg y
  rw [← hgxy] at hy
  obtain ⟨c, hc⟩ := LinTorus.exists_scalar_mul_of_mem_ggInducedPairs hker (hg x) hy
  have hd := eq_of_diagGL_eq_scalar_mul hc (by rw [ha0, ha0])
  apply hainj
  funext i
  have hi := congrFun hd i
  exact ZMod.val_injective p (hω.pow_inj (ZMod.val_lt _) (ZMod.val_lt _) hi)

end LinModel

end CFSG.StandardType

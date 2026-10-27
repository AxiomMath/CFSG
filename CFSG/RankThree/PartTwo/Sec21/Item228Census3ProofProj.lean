module

public import CFSG.RankThree.PartTwo.Sec21.Item228Census3ProofTools
public import CFSG.Assembly.RankThreeEvenDefs
import CFSG.GroupTheory.PerfectResidualNodes
import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG Matrix
open CFSG.Assembly.RankThreeEven (projImage projSL)

namespace Item228Census3Proof

theorem inSubgroup_perfectResidual_map {G H : Type*} [Group G] [Group H] [Finite G] [Finite H]
    (φ : G →* H) (C : Subgroup G) :
    inSubgroup perfectResidual (C.map φ) = (inSubgroup perfectResidual C).map φ := by
  have h := (CFSG.perfect_residual_transport (φ.comp C.subtype)).1
  have hr : (φ.comp C.subtype).range = C.map φ := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have h' : (perfectResidual C).map (φ.comp C.subtype) =
      inSubgroup perfectResidual (C.map φ) := by
    rw [← hr]
    exact h
  rw [← h', inSubgroup, Subgroup.map_map]

theorem commutator_range_of_isPerfect {X H : Type*} [Group X] [Group H] (hX : Group.IsPerfect X)
    (φ : X →* H) : ⁅φ.range, φ.range⁆ = φ.range := by
  rw [MonoidHom.range_eq_map, ← Subgroup.map_commutator, ← commutator_def, hX.commutator_eq_top]

variable {ι : Type} [Fintype ι] [DecidableEq ι] {K : Type} [Field K]

@[expose] noncomputable def projRestrict (G : Subgroup (GL ι K)) : G →* projImage G :=
  (ProjGenLinGroup.mk.comp G.subtype).codRestrict (projImage G) fun g => ⟨g, g.2, rfl⟩

theorem coe_projRestrict (G : Subgroup (GL ι K)) (g : G) :
    ((projRestrict G g : projImage G) : ProjGenLinGroup ι K) = ProjGenLinGroup.mk (g : GL ι K) :=
  rfl

theorem projRestrict_surjective (G : Subgroup (GL ι K)) : Function.Surjective (projRestrict G) := by
  rintro ⟨_, g, hg, rfl⟩
  exact ⟨⟨g, hg⟩, rfl⟩

theorem projRestrict_eq_iff (G : Subgroup (GL ι K)) {g h : G} :
    projRestrict G g = projRestrict G h ↔
      ∃ u : Kˣ, (g : GL ι K) * GeneralLinearGroup.scalar ι u = h := by
  rw [← Subtype.coe_inj, coe_projRestrict, coe_projRestrict, ProjGenLinGroup.mk_eq_mk_iff]

theorem projRestrict_eq_one_iff (G : Subgroup (GL ι K)) {g : G} :
    projRestrict G g = 1 ↔ ∃ u : Kˣ, GeneralLinearGroup.scalar ι u = (g : GL ι K) := by
  rw [← (projRestrict G).map_one, projRestrict_eq_iff]
  constructor
  · rintro ⟨u, hu⟩
    refine ⟨u⁻¹, ?_⟩
    rw [map_inv]
    exact (eq_inv_of_mul_eq_one_left hu).symm
  · rintro ⟨u, hu⟩
    refine ⟨u⁻¹, ?_⟩
    rw [← hu, ← map_mul, mul_inv_cancel, map_one, Subgroup.coe_one]

theorem scalar_eq_one_iff [Nonempty ι] {u : Kˣ} : GeneralLinearGroup.scalar ι u = 1 ↔ u = 1 := by
  constructor
  · intro h
    obtain ⟨i⟩ := ‹Nonempty ι›
    have := congrArg (fun x : GL ι K => (x : Matrix ι ι K) i i) h
    simp only [GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, Units.val_one,
      Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at this
    exact Units.ext this
  · rintro rfl
    exact map_one _

theorem exists_lift_cube (G : Subgroup (GL ι K))
    (hZ : ∀ u : Kˣ, GeneralLinearGroup.scalar ι u ∈ G → u ^ 4 = 1) (y : projImage G)
    (hy : orderOf y = 3) : ∃ A : G, projRestrict G A = y ∧ A ^ 3 = 1 ∧ A ≠ 1 := by
  obtain ⟨A₀, rfl⟩ := projRestrict_surjective G y
  have hy3 : projRestrict G (A₀ ^ 3) = 1 := by rw [map_pow, ← hy, pow_orderOf_eq_one]
  obtain ⟨u, hu⟩ := (projRestrict_eq_one_iff G).mp hy3
  have hu4 : u ^ 4 = 1 := hZ u (hu ▸ (A₀ ^ 3).2)
  refine ⟨A₀ ^ 4, ?_, ?_, ?_⟩
  · rw [map_pow, show (4 : ℕ) = 3 + 1 from rfl, pow_succ, ← hy, pow_orderOf_eq_one, one_mul]
  · apply Subtype.ext
    rw [← pow_mul, show 4 * 3 = 3 * 4 from rfl, pow_mul, Subgroup.coe_pow, ← hu,
      Subgroup.coe_one, ← map_pow, hu4, map_one]
  · intro h1
    have : projRestrict G (A₀ ^ 4) = 1 := by rw [h1, map_one]
    rw [map_pow, show (4 : ℕ) = 3 + 1 from rfl, pow_succ, ← hy, pow_orderOf_eq_one, one_mul] at this
    rw [this, orderOf_one] at hy
    norm_num at hy

theorem centralizer_projRestrict [Nonempty ι] (G : Subgroup (GL ι K)) (A : G) (hA3 : A ^ 3 = 1)
    (hZ : ∀ u : Kˣ, GeneralLinearGroup.scalar ι u ∈ G → u ^ 3 = 1 → u = 1) :
    Subgroup.centralizer ({projRestrict G A} : Set (projImage G)) =
      (Subgroup.centralizer ({A} : Set G)).map (projRestrict G) := by
  apply le_antisymm
  · intro y hy
    obtain ⟨g, rfl⟩ := projRestrict_surjective G y
    rw [Subgroup.mem_centralizer_singleton_iff] at hy
    refine ⟨g, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff]
    have h1 : projRestrict G A = projRestrict G (g * A * g⁻¹) := by
      rw [map_mul, map_mul, hy, mul_assoc, ← map_mul, mul_inv_cancel, map_one, mul_one]
    obtain ⟨u, hu⟩ := (projRestrict_eq_iff G).mp h1
    have hsc : GeneralLinearGroup.scalar ι u ∈ G := by
      have : GeneralLinearGroup.scalar ι u = (A : GL ι K)⁻¹ * (g * A * g⁻¹ : G) := by
        rw [← hu, inv_mul_cancel_left]
      rw [this]
      exact G.mul_mem (G.inv_mem A.2) (g * A * g⁻¹).2
    have hcomm : ∀ x : GL ι K, Commute x (GeneralLinearGroup.scalar ι u) := fun x =>
      Subgroup.mem_center_iff.mp (by
        rw [GeneralLinearGroup.center_eq_range_scalar]; exact ⟨u, rfl⟩) x
    have hu3 : u ^ 3 = 1 := by
      have e1 : ((g * A * g⁻¹ : G) : GL ι K) ^ 3 = 1 := by
        rw [← Subgroup.coe_pow, conj_pow, hA3, mul_one, mul_inv_cancel, Subgroup.coe_one]
      rw [← hu, (hcomm (A : GL ι K)).mul_pow, ← Subgroup.coe_pow, hA3, Subgroup.coe_one,
        one_mul, ← map_pow] at e1
      exact scalar_eq_one_iff.mp e1
    have hu1 : u = 1 := hZ u hsc hu3
    rw [hu1, map_one, mul_one] at hu
    have : g * A * g⁻¹ = A := Subtype.ext hu.symm
    rw [mul_inv_eq_iff_eq_mul] at this
    exact this
  · rintro _ ⟨g, hg, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_centralizer_singleton_iff] at hg
    rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul, hg]

@[expose] def IsCentData (G : Subgroup (GL ι K)) (A : GL ι K) {X : Type*} [Group X]
    (φ : X →* GL ι K) : Prop :=
  (∀ x, φ x ∈ G) ∧ (∀ x, φ x * A = A * φ x) ∧
    ∀ g ∈ G, ∀ h ∈ G, g * A = A * g → h * A = A * h → ∃ x, φ x = g * h * g⁻¹ * h⁻¹

theorem IsCentData.conj {G G' : Subgroup (GL ι K)} {A D P : GL ι K} {X : Type*} [Group X]
    {φ : X →* GL ι K} (h : IsCentData G' D φ) (hP : ∀ g, g ∈ G ↔ P * g * P⁻¹ ∈ G')
    (hD : D = P * A * P⁻¹) : IsCentData G A ((MulAut.conj P⁻¹).toMonoidHom.comp φ) := by
  obtain ⟨hmem, hcomm, hcom⟩ := h
  have hc : ∀ x, ((MulAut.conj P⁻¹).toMonoidHom.comp φ) x = P⁻¹ * φ x * P := fun x => by
    simp
  refine ⟨fun x => ?_, fun x => ?_, fun g hg k hk hgA hkA => ?_⟩
  · rw [hc, hP]
    have e : P * (P⁻¹ * φ x * P) * P⁻¹ = φ x := by group
    rw [e]
    exact hmem x
  · rw [hc]
    have e := hcomm x
    rw [hD] at e
    calc P⁻¹ * φ x * P * A = P⁻¹ * (φ x * (P * A * P⁻¹)) * P := by group
      _ = P⁻¹ * ((P * A * P⁻¹) * φ x) * P := by rw [e]
      _ = A * (P⁻¹ * φ x * P) := by group
  · have hg' : P * g * P⁻¹ * D = D * (P * g * P⁻¹) := by
      rw [hD]
      calc P * g * P⁻¹ * (P * A * P⁻¹) = P * (g * A) * P⁻¹ := by group
        _ = P * (A * g) * P⁻¹ := by rw [hgA]
        _ = P * A * P⁻¹ * (P * g * P⁻¹) := by group
    have hk' : P * k * P⁻¹ * D = D * (P * k * P⁻¹) := by
      rw [hD]
      calc P * k * P⁻¹ * (P * A * P⁻¹) = P * (k * A) * P⁻¹ := by group
        _ = P * (A * k) * P⁻¹ := by rw [hkA]
        _ = P * A * P⁻¹ * (P * k * P⁻¹) := by group
    obtain ⟨x, hx⟩ := hcom _ ((hP g).mp hg) _ ((hP k).mp hk) hg' hk'
    refine ⟨x, ?_⟩
    rw [hc, hx]
    group

theorem map_center_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    (Subgroup.center X).map (e : X →* Y) = Subgroup.center Y := by
  ext y
  constructor
  · rintro ⟨x, hx, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_center_iff] at hx
    rw [Subgroup.mem_center_iff]
    intro z
    obtain ⟨w, rfl⟩ := e.surjective z
    change e w * e x = e x * e w
    rw [← map_mul, ← map_mul, hx w]
  · intro hy
    refine ⟨e.symm y, ?_, by simp⟩
    rw [Subgroup.mem_center_iff] at hy
    rw [SetLike.mem_coe, Subgroup.mem_center_iff]
    intro z
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact hy (e z)

theorem ker_projRestrict_comp (G : Subgroup (GL ι K)) {X : Type*} [Group X] (φ : X →* GL ι K)
    (hφ : ∀ x, φ x ∈ G) :
    ((projRestrict G).comp (φ.codRestrict G hφ)).ker = (ProjGenLinGroup.mk.comp φ).ker := by
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.mem_ker, ← Subtype.coe_inj]
  rfl

theorem ker_mk_conj {X : Type*} [Group X] (φ : X →* GL ι K) (Q : GL ι K) :
    (ProjGenLinGroup.mk.comp ((MulAut.conj Q).toMonoidHom.comp φ)).ker =
      (ProjGenLinGroup.mk.comp φ).ker := by
  ext x
  simp only [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulAut.conj_apply, map_mul, map_inv]
  constructor
  · intro h
    have : ProjGenLinGroup.mk (φ x) = (ProjGenLinGroup.mk Q)⁻¹ *
        (ProjGenLinGroup.mk Q * ProjGenLinGroup.mk (φ x) * (ProjGenLinGroup.mk Q)⁻¹) *
        ProjGenLinGroup.mk Q := by group
    rw [this, h, mul_one, inv_mul_cancel]
  · intro h
    rw [h, mul_one, mul_inv_cancel]

section Residual

variable [Finite K] [Nonempty ι]

omit [Nonempty ι] in
theorem finite_projGenLinGroup : Finite (ProjGenLinGroup ι K) :=
  Finite.of_surjective _ ProjGenLinGroup.mk_surjective

omit [Nonempty ι] in
theorem finite_projImage (G : Subgroup (GL ι K)) : Finite (projImage G) := by
  have := finite_projGenLinGroup (ι := ι) (K := K)
  exact Subtype.finite

theorem perfectResidual_centralizer_eq_range (G : Subgroup (GL ι K)) (A : G) (hA3 : A ^ 3 = 1)
    (hZ : ∀ u : Kˣ, GeneralLinearGroup.scalar ι u ∈ G → u ^ 3 = 1 → u = 1)
    {X : Type*} [Group X] [Group.IsPerfect X] (φ : X →* GL ι K) (hφ : IsCentData G A φ) :
    inSubgroup perfectResidual (Subgroup.centralizer ({projRestrict G A} : Set (projImage G))) =
      ((projRestrict G).comp (φ.codRestrict G hφ.1)).range := by
  have := finite_projImage G
  set ψ : X →* G := φ.codRestrict G hφ.1 with hψ
  have hB : inSubgroup perfectResidual (Subgroup.centralizer ({A} : Set G)) = ψ.range := by
    refine inSubgroup_perfectResidual_eq_of_commutator ?_ (commutator_range_of_isPerfect
      inferInstance ψ) ?_
    · rintro _ ⟨x, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact Subtype.ext (hφ.2.1 x)
    · intro g hg k hk
      rw [Subgroup.mem_centralizer_singleton_iff] at hg hk
      obtain ⟨x, hx⟩ := hφ.2.2 g g.2 k k.2 (congrArg Subtype.val hg) (congrArg Subtype.val hk)
      exact ⟨x, Subtype.ext hx⟩
  rw [centralizer_projRestrict G A hA3 hZ, inSubgroup_perfectResidual_map, hB,
    MonoidHom.range_comp]

theorem nonempty_perfectResidual_equiv_of_ker_bot (G : Subgroup (GL ι K)) (A : G)
    (hA3 : A ^ 3 = 1) (hZ : ∀ u : Kˣ, GeneralLinearGroup.scalar ι u ∈ G → u ^ 3 = 1 → u = 1)
    {X : Type*} [Group X] [Group.IsPerfect X] (φ : X →* GL ι K) (hφ : IsCentData G A φ)
    (hker : (ProjGenLinGroup.mk.comp φ).ker = ⊥) :
    Nonempty (inSubgroup perfectResidual
      (Subgroup.centralizer ({projRestrict G A} : Set (projImage G))) ≃* X) := by
  rw [perfectResidual_centralizer_eq_range G A hA3 hZ φ hφ]
  have hinj : Function.Injective ((projRestrict G).comp (φ.codRestrict G hφ.1)) := by
    rw [← MonoidHom.ker_eq_bot_iff, ker_projRestrict_comp, hker]
  exact ⟨(MonoidHom.ofInjective hinj).symm⟩

theorem nonempty_perfectResidual_equiv_projSL (G : Subgroup (GL ι K)) (A : G)
    (hA3 : A ^ 3 = 1) (hZ : ∀ u : Kˣ, GeneralLinearGroup.scalar ι u ∈ G → u ^ 3 = 1 → u = 1)
    {X : Type*} [Group X] [Group.IsPerfect X] (φ : X →* GL ι K) (hφ : IsCentData G A φ)
    (hker : (ProjGenLinGroup.mk.comp φ).ker = Subgroup.center X) {F : Type} [Field F]
    (e : X ≃* SpecialLinearGroup (Fin 2) F) :
    Nonempty (inSubgroup perfectResidual
      (Subgroup.centralizer ({projRestrict G A} : Set (projImage G))) ≃* projSL 2 F) := by
  rw [perfectResidual_centralizer_eq_range G A hA3 hZ φ hφ]
  set f := (projRestrict G).comp (φ.codRestrict G hφ.1)
  have hk : f.ker = Subgroup.center X := by rw [ker_projRestrict_comp, hker]
  have e1 : X ⧸ f.ker ≃* SpecialLinearGroup (Fin 2) F ⧸
      Subgroup.center (SpecialLinearGroup (Fin 2) F) :=
    QuotientGroup.congr _ _ e (by rw [hk, map_center_equiv])
  exact ⟨(QuotientGroup.quotientKerEquivRange f).symm.trans
    (e1.trans (Sec4.projSLEquivPSL F).symm)⟩

end Residual

end Item228Census3Proof

end CFSG.RankThree.PartTwo.Sec21

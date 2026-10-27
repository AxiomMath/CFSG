module

import CFSG.GroupTheory.Fitting.MulEquiv
public import CFSG.RankThree.GF2n.Stroth80.Swap

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

abbrev Mbar (M Q : Subgroup G) := ↥M ⧸ Q.subgroupOf M

theorem Ctx.normal_Q_in_M (hc : Ctx M Q Z B) : (Q.subgroupOf M).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer hc.hyp.Q_normal.2

theorem Ctx.LB_le_M (hc : Ctx M Q Z B) : LB M Q B ≤ M :=
  sup_le hc.hyp.Q_normal.1 inf_le_right

theorem Rt_le_M {L : Subgroup G} (hL : L ≤ M) (t : G) : Rt M L t ≤ M := by
  refine iSup₂_le fun m hm => iSup_le fun _ => ?_
  intro x hx
  rw [mem_conjSubgroup] at hx
  have := hL hx
  have h2 : m * (m⁻¹ * x * m) * m⁻¹ ∈ M := M.mul_mem (M.mul_mem hm this) (M.inv_mem hm)
  rwa [show m * (m⁻¹ * x * m) * m⁻¹ = x by group] at h2

theorem QB_conj (g : G) (B : Subgroup G) : QB (conjSubgroup g B) = conjSubgroup g (QB B) := by
  unfold QB
  have hN : Subgroup.normalizer ((conjSubgroup g B : Subgroup G) : Set G) =
      conjSubgroup g (Subgroup.normalizer (B : Set G)) :=
    (Subgroup.map_normalizer_eq_of_bijective (f := (MulAut.conj g).toMonoidHom) B
      (MulAut.conj g).bijective).symm
  rw [hN]
  set N := Subgroup.normalizer (B : Set G)
  let e : ↥N ≃* ↥(conjSubgroup g N) := MulEquiv.subgroupMap (MulAut.conj g) N
  have key := CFSG.WholeGroup.generalizedFitting_map_mulEquiv e
  show (generalizedFitting ↥(conjSubgroup g N)).map (conjSubgroup g N).subtype =
    ((generalizedFitting ↥N).map N.subtype).map (MulAut.conj g).toMonoidHom
  rw [← key, Subgroup.map_map, Subgroup.map_map]
  congr 1 <;> ext x <;> rfl

theorem Ctx.conj_Q_eq (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) : conjSubgroup m Q = Q :=
  conjSubgroup_eq_self_iff.mpr (hc.hyp.Q_normal.2 hm)

theorem Ctx.conj_Z_eq (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) : conjSubgroup m Z = Z :=
  conjSubgroup_eq_self_iff.mpr (hc.hyp.Z_normal.2 hm)

theorem Ctx.conj_M_eq (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) : conjSubgroup m M = M := by
  rw [conjSubgroup_eq_self_iff]
  exact (Subgroup.mem_normalizer_iff.mpr fun x => by
    constructor
    · intro hx; exact M.mul_mem (M.mul_mem hm hx) (M.inv_mem hm)
    · intro hx
      have := M.mul_mem (M.mul_mem (M.inv_mem hm) hx) hm
      simpa [mul_assoc] using this)

theorem Ctx.conj_of_mem (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
    Ctx M Q Z (conjSubgroup m B) where
  hyp := hc.hyp
  conj := by
    obtain ⟨g, hg⟩ := hc.conj
    exact ⟨m * g, by rw [hg, conjSubgroup_mul]⟩
  le := by
    rw [← hc.conj_Q_eq hm]
    exact Subgroup.map_mono hc.le
  ne := by
    intro h
    apply hc.ne
    have : conjSubgroup m⁻¹ (conjSubgroup m B) = conjSubgroup m⁻¹ Z := by rw [h]
    rwa [← conjSubgroup_mul, inv_mul_cancel, conjSubgroup_one, hc.conj_Z_eq (M.inv_mem hm)]
      at this

theorem Ctx.LB_conj (hc : Ctx M Q Z B) {m : G} (hm : m ∈ M) :
    LB M Q (conjSubgroup m B) = conjSubgroup m (LB M Q B) := by
  unfold LB
  rw [QB_conj, conjSubgroup_sup', conjSubgroup_inf, hc.conj_Q_eq hm, hc.conj_M_eq hm]

@[expose] def CNtGrp (M L B Z : Subgroup G) (t : G) (hL : L ≤ M)
    (hZ : M ≤ Subgroup.normalizer (Z : Set G)) : Subgroup G where
  carrier := CNt M L B Z t
  mul_mem' := by
    rintro a b ⟨ha, hav⟩ ⟨hb, hbv⟩
    refine ⟨Subgroup.mul_mem _ ha hb, fun v hv => ?_⟩
    have haM : a ∈ M := Rt_le_M hL t ha
    have h1 : ⁅a * b, v⁆ = a * ⁅b, v⁆ * a⁻¹ * ⁅a, v⁆ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    refine Z.mul_mem ?_ (hav v hv)
    have := (Subgroup.mem_normalizer_iff.mp (hZ haM) _).mp (hbv v hv)
    simpa using this
  one_mem' := ⟨Subgroup.one_mem _, fun v _ => by simp [commutatorElement_def]⟩
  inv_mem' := by
    rintro a ⟨ha, hav⟩
    refine ⟨Subgroup.inv_mem _ ha, fun v hv => ?_⟩
    have haM : a ∈ M := Rt_le_M hL t ha
    have h1 : ⁅a⁻¹, v⁆ = (a⁻¹ * ⁅a, v⁆ * a)⁻¹ := by
      simp only [commutatorElement_def]; group
    rw [h1]
    refine Z.inv_mem ?_
    have := (Subgroup.mem_normalizer_iff.mp (hZ (M.inv_mem haM)) _).mp (hav v hv)
    simpa using this

@[expose] def GenByB (M Q B : Subgroup G) : Prop :=
  Q = ⨆ (m : G) (_ : m ∈ M), conjSubgroup m B

theorem GenByB.conj_of_mem {M Q B : Subgroup G} (h : GenByB M Q B) {m : G} (hm : m ∈ M) :
    GenByB M Q (conjSubgroup m B) := by
  unfold GenByB at h ⊢
  rw [h]
  refine le_antisymm (iSup₂_le fun m' hm' => ?_) (iSup₂_le fun m' hm' => ?_)
  · have : conjSubgroup m' B = conjSubgroup (m' * m⁻¹) (conjSubgroup m B) := by
      rw [← conjSubgroup_mul]; congr 1; group
    rw [this]
    exact le_iSup₂_of_le (m' * m⁻¹) (M.mul_mem hm' (M.inv_mem hm)) le_rfl
  · rw [← conjSubgroup_mul]
    exact le_iSup₂_of_le (m' * m) (M.mul_mem hm' hm) le_rfl

@[expose] def Conc34 (M Q Z B : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≤ Q ⊓ Subgroup.centralizer (B : Set G) →
    (∀ x ∈ X, ∀ t ∈ LB M Q B, ⁅t, x⁆ ∈ (B ⊔ Z : Subgroup G)) → X ≤ Q ⊓ QB B

@[expose] def Ctx.CN (hc : Ctx M Q Z B) (t : G) : Subgroup G :=
  CNtGrp M (LB M Q B) B Z t hc.LB_le_M hc.hyp.Z_normal.2

@[expose] def NaturalRep {ι : Type} [Fintype ι] [DecidableEq ι] (K : Type) [Field K]
    (X : Subgroup (GL ι K)) (R V Z N : Subgroup G) : Prop :=
  ∃ φ : R →* GL ι K, φ.range = X ∧ φ.ker = N.subgroupOf R ∧
    SectionAct K R V Z φ (fun g => (g : Matrix ι ι K))

end CFSG.RankThree.GF2n.Stroth80

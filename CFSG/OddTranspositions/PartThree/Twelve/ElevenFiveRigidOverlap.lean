module

public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveOverlap
public import CFSG.OddTranspositions.PartThree.Twelve.ElevenFiveNorm

public section

namespace CFSG.OddTranspositions.PartThree

open CFSG.Timmesfeld.Bridge Matrix

variable {G G' : Type} [Group G] [Group G']

theorem mem_fiveReflectionsIn_fiveOrth_span_iff {k : ℕ} {ε π : Bool}
    {a : Fin (k + 1) → ZMod 5}
    {g : GL (Fin (k + 1)) (ZMod 5)} :
    g ∈ fiveReflectionsIn k ε π (fiveOrth k ε (Submodule.span (ZMod 5) {a})) ↔
      g ∈ fiveReflections k ε π ∧
        (g : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a = a := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  constructor
  · rintro ⟨v, hv, hv0, hvπ, hg⟩
    have hav : fiveForm k ε a v = 0 := by
      have h := (mem_fiveOrth (k := k) (ε := ε)
        (U := Submodule.span (ZMod 5) {a})).1 hv a
        (Submodule.mem_span_singleton_self a)
      rwa [fiveForm_comm] at h
    refine ⟨⟨v, hv0, hvπ, hg⟩, ?_⟩
    rw [hg a, hav]
    simp
  · rintro ⟨⟨v, hv0, hvπ, hg⟩, hga⟩
    have hav : fiveForm k ε a v = 0 := by
      have hvne : v ≠ 0 := fun h0 => hv0 (by rw [h0]; simp [fiveForm])
      have hcv : (2 * fiveForm k ε a v * (fiveForm k ε v v)⁻¹) • v = 0 := by
        have h := hg a
        rw [hga] at h
        exact sub_eq_self.mp h.symm
      have hcoef : (2 : ZMod 5) * fiveForm k ε a v * (fiveForm k ε v v)⁻¹ = 0 := by
        rcases smul_eq_zero.mp hcv with h | h
        · exact h
        · exact absurd h hvne
      have h2ne : (2 : ZMod 5) ≠ 0 := fun h2 =>
        (by decide : ¬(5 : ℕ) ∣ 2) ((ZMod.natCast_eq_zero_iff 2 5).mp h2)
      rcases mul_eq_zero.mp hcoef with h | h
      · rcases mul_eq_zero.mp h with h | h
        · exact absurd h h2ne
        · exact h
      · exact absurd h (inv_ne_zero hv0)
    refine ⟨v, ?_, hv0, hvπ, hg⟩
    rw [mem_fiveOrth]
    intro u hu
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    rw [fiveForm_comm, fiveForm_smul_left, hav, mul_zero]

theorem mem_commSet_inter_iff_of_fiveLocalModel {D : Set G} {v : G} {k : ℕ} {ε π : Bool}
    (cv : FiveLocalModel D v k ε π) {u : G} (hu : u ∈ commSet D v)
    {a : Fin (k + 1) → ZMod 5} (ha0 : fiveForm k ε a a ≠ 0)
    (ha : (cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ : GL (Fin (k + 1)) (ZMod 5)) =
      fiveReflOf k ε a)
    (y : Subgroup.closure (commSet D v)) :
    (y : G) ∈ commSet D u ∩ commSet D v ↔
      (cv.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) ∈
        fiveReflectionsIn k ε π (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
  constructor
  · intro hy
    have hyv : (y : G) ∈ commSet D v := hy.2
    have h1 : ((cv.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ a = a :=
      (mem_commSet_iff_of_fiveLocalModel cv hu hyv ha0 ha).1 hy.1
    have h2 : (cv.toMulEquiv y : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π :=
      (cv.mem_iff y).1 hyv
    exact (mem_fiveReflectionsIn_fiveOrth_span_iff).2 ⟨h2, h1⟩
  · intro hg
    obtain ⟨h2, h1⟩ := (mem_fiveReflectionsIn_fiveOrth_span_iff).1 hg
    have hyv : (y : G) ∈ commSet D v := (cv.mem_iff y).2 h2
    exact ⟨(mem_commSet_iff_of_fiveLocalModel cv hu hyv ha0 ha).2 h1, hyv⟩

theorem exists_iso_closure_inter_fiveOrth {D : Set G} {v : G} {k : ℕ} {ε π : Bool}
    (cv : FiveLocalModel D v k ε π) {u : G} (hu : u ∈ commSet D v)
    {a : Fin (k + 1) → ZMod 5} (ha0 : fiveForm k ε a a ≠ 0)
    (ha : (cv.toMulEquiv ⟨u, Subgroup.subset_closure hu⟩ : GL (Fin (k + 1)) (ZMod 5)) =
      fiveReflOf k ε a) :
    ∃ e : Subgroup.closure (commSet D u ∩ commSet D v) ≃*
        fiveReflectionGroupIn k ε π (fiveOrth k ε (Submodule.span (ZMod 5) {a})),
      (∀ y : Subgroup.closure (commSet D u ∩ commSet D v),
        (e y : GL (Fin (k + 1)) (ZMod 5)) =
          cv.toMulEquiv ⟨y.1, Subgroup.closure_mono Set.inter_subset_right y.2⟩) ∧
      (∀ y : Subgroup.closure (commSet D u ∩ commSet D v),
        (y : G) ∈ commSet D u ∩ commSet D v ↔
          (e y : GL (Fin (k + 1)) (ZMod 5)) ∈
            fiveReflectionsIn k ε π (fiveOrth k ε (Submodule.span (ZMod 5) {a}))) := by
  classical
  let A : Subgroup G := Subgroup.closure (commSet D v)
  let S : Set G := commSet D u ∩ commSet D v
  let R : Subgroup G := Subgroup.closure S
  let W : Submodule (ZMod 5) (Fin (k + 1) → ZMod 5) :=
    fiveOrth k ε (Submodule.span (ZMod 5) {a})
  have hSA : S ⊆ A := fun x hx => Subgroup.subset_closure (Set.inter_subset_right hx)
  have hRA : R ≤ A := Subgroup.closure_mono Set.inter_subset_right
  have hleF : fiveReflectionsIn k ε π W ⊆ fiveReflections k ε π :=
    fun g hg => ((mem_fiveReflectionsIn_fiveOrth_span_iff).1 hg).1
  have hleG : fiveReflectionsIn k ε π W ⊆ fiveReflectionGroup k ε π :=
    fun g hg => Subgroup.subset_closure (hleF hg)
  have hle : fiveReflectionGroupIn k ε π W ≤ fiveReflectionGroup k ε π :=
    Subgroup.closure_mono hleF
  have himg : ⇑(cv.toMulEquiv : A →* fiveReflectionGroup k ε π) '' (A.subtype ⁻¹' S) =
      ⇑(fiveReflectionGroup k ε π).subtype ⁻¹' fiveReflectionsIn k ε π W := by
    ext g
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (mem_commSet_inter_iff_of_fiveLocalModel cv hu ha0 ha y).1 hy
    · intro hg
      refine ⟨cv.toMulEquiv.symm g, ?_, by simp⟩
      change ((cv.toMulEquiv.symm g : A) : G) ∈ S
      rw [mem_commSet_inter_iff_of_fiveLocalModel cv hu ha0 ha]
      simpa using hg
  have hmap : (R.subgroupOf A).map (cv.toMulEquiv : A →* fiveReflectionGroup k ε π) =
      (fiveReflectionGroupIn k ε π W).subgroupOf (fiveReflectionGroup k ε π) := by
    rw [Subgroup.closure_subgroupOf hSA, MonoidHom.map_closure, himg,
      ← Subgroup.closure_subgroupOf hleG]
    rfl
  let e1 : R ≃* fiveReflectionGroupIn k ε π W :=
    (Subgroup.subgroupOfEquivOfLe hRA).symm.trans
      (((cv.toMulEquiv.subgroupMap (R.subgroupOf A)).trans
        (MulEquiv.subgroupCongr hmap)).trans (Subgroup.subgroupOfEquivOfLe hle))
  have hval : ∀ y : R, (e1 y : GL (Fin (k + 1)) (ZMod 5)) =
      (cv.toMulEquiv ⟨y.1, hRA y.2⟩ : GL (Fin (k + 1)) (ZMod 5)) := by
    intro y
    simp only [e1, MulEquiv.trans_apply]
    rfl
  refine ⟨e1, hval, ?_⟩
  intro y
  rw [hval y]
  exact mem_commSet_inter_iff_of_fiveLocalModel cv hu ha0 ha ⟨y.1, hRA y.2⟩

theorem exists_iso_closure_inter_commSet {D : Set G} {D' : Set G'} {u v : G} {u' v' : G'}
    (θ : LocalIso D u D' u') (hv : v ∈ commSet D u)
    (hθv : θ.app v = v') :
    ∃ e : Subgroup.closure (commSet D u ∩ commSet D v) ≃*
        Subgroup.closure (commSet D' u' ∩ commSet D' v'),
      (∀ y : Subgroup.closure (commSet D u ∩ commSet D v),
        (e y : G') = θ.toMulEquiv ⟨y.1, Subgroup.closure_mono Set.inter_subset_left y.2⟩) ∧
      (∀ y : Subgroup.closure (commSet D u ∩ commSet D v),
        (y : G) ∈ commSet D u ∩ commSet D v ↔
          (e y : G') ∈ commSet D' u' ∩ commSet D' v') := by
  classical
  let B : Subgroup G := Subgroup.closure (commSet D u)
  let B' : Subgroup G' := Subgroup.closure (commSet D' u')
  let S : Set G := commSet D u ∩ commSet D v
  let S' : Set G' := commSet D' u' ∩ commSet D' v'
  let R : Subgroup G := Subgroup.closure S
  let R' : Subgroup G' := Subgroup.closure S'
  have hSB : S ⊆ B := fun x hx => Subgroup.subset_closure (Set.inter_subset_left hx)
  have hS'B' : S' ⊆ B' := fun x hx => Subgroup.subset_closure (Set.inter_subset_left hx)
  have hRB : R ≤ B := Subgroup.closure_mono Set.inter_subset_left
  have hR'B' : R' ≤ B' := Subgroup.closure_mono Set.inter_subset_left
  have hvB : v ∈ B := Subgroup.subset_closure hv
  have hgen : ∀ y : B, (y : G) ∈ S ↔ (θ.toMulEquiv y : G') ∈ S' := by
    intro y
    have hycomm : (y : G) ∈ commSet D u ↔ (θ.toMulEquiv y : G') ∈ commSet D' u' :=
      θ.mem_iff y
    constructor
    · intro hy
      have hz1 : (θ.toMulEquiv y : G') ∈ commSet D' u' := hycomm.1 hy.1
      have hcz : Commute (θ.toMulEquiv y : G') v' := by
        have h1 : Commute (θ.app (y : G)) (θ.app v) :=
          (θ.commute_iff y.2 hvB).2 hy.2.2.1
        rwa [LocalIso.app_of_mem θ y.2, hθv] at h1
      have hnez : (θ.toMulEquiv y : G') ≠ v' := by
        rw [← LocalIso.app_of_mem θ y.2, ← hθv]
        intro h
        exact hy.2.2.2 (θ.app_injOn y.2 hvB h)
      exact ⟨hz1, hz1.1, hcz, hnez⟩
    · intro hz
      have hyu : (y : G) ∈ commSet D u := hycomm.2 hz.1
      have hcomm : Commute (y : G) v := by
        have h1 : Commute (θ.app (y : G)) (θ.app v) := by
          rw [LocalIso.app_of_mem θ y.2, hθv]
          exact hz.2.2.1
        exact (θ.commute_iff y.2 hvB).1 h1
      have hne : (y : G) ≠ v := by
        intro h
        apply hz.2.2.2
        rw [← LocalIso.app_of_mem θ y.2, h]
        exact hθv
      exact ⟨hyu, hyu.1, hcomm, hne⟩
  have himg : ⇑(θ.toMulEquiv : B →* B') '' (B.subtype ⁻¹' S) = B'.subtype ⁻¹' S' := by
    ext z
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (hgen y).1 hy
    · intro hz
      refine ⟨θ.toMulEquiv.symm z, ?_, by simp⟩
      change ((θ.toMulEquiv.symm z : B) : G) ∈ S
      rw [hgen, MulEquiv.apply_symm_apply]
      exact hz
  have hmap : (R.subgroupOf B).map
        (θ.toMulEquiv : B →* B') = R'.subgroupOf B' := by
    change (R.subgroupOf B).map (θ.toMulEquiv : B →* B') =
      (Subgroup.closure S').subgroupOf B'
    rw [Subgroup.closure_subgroupOf hSB, MonoidHom.map_closure, himg,
      ← Subgroup.closure_subgroupOf hS'B']
  let e : R ≃* R' :=
    (Subgroup.subgroupOfEquivOfLe hRB).symm.trans
      (((θ.toMulEquiv.subgroupMap (R.subgroupOf B)).trans
        (MulEquiv.subgroupCongr hmap)).trans (Subgroup.subgroupOfEquivOfLe hR'B'))
  have hval : ∀ y : R, (e y : G') = θ.toMulEquiv ⟨y.1, hRB y.2⟩ := by
    intro y
    simp only [e, MulEquiv.trans_apply]
    rfl
  refine ⟨e, hval, ?_⟩
  intro y
  rw [hval y]
  exact hgen ⟨y.1, hRB y.2⟩

theorem fiveOrth_fiveOrth_span_singleton {k : ℕ} {ε : Bool} {a : Fin (k + 1) → ZMod 5}
    (ha0 : fiveForm k ε a a ≠ 0) :
    fiveOrth k ε (fiveOrth k ε (Submodule.span (ZMod 5) {a})) =
      Submodule.span (ZMod 5) {a} := by
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hnd : IsFiveNondeg k ε (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
    have h := isFiveNondeg_inf_fiveOrth (k := k) (ε := ε) (W := ⊤)
      (U := Submodule.span (ZMod 5) {a}) (isFiveNondeg_top k ε)
      (isFiveNondeg_span_singleton ha0) le_top
    rwa [top_inf_eq] at h
  have hle : Submodule.span (ZMod 5) {a} ≤
      fiveOrth k ε (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
    rw [Submodule.span_le]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    rw [hx]
    change a ∈ fiveOrth k ε (fiveOrth k ε (Submodule.span (ZMod 5) {a}))
    rw [mem_fiveOrth]
    intro u hu
    have h := (mem_fiveOrth (k := k) (ε := ε)
      (U := Submodule.span (ZMod 5) {a})).1 hu a (Submodule.mem_span_singleton_self a)
    rwa [fiveForm_comm] at h
  refine le_antisymm ?_ hle
  intro x hx
  set c : ZMod 5 := fiveForm k ε x a * (fiveForm k ε a a)⁻¹ with hcdef
  have hw1 : x - c • a ∈ fiveOrth k ε (Submodule.span (ZMod 5) {a}) := by
    rw [mem_fiveOrth]
    intro u hu
    obtain ⟨d, rfl⟩ := Submodule.mem_span_singleton.mp hu
    have hxw : x - c • a = x + (-c) • a := by
      rw [sub_eq_add_neg]
      congr 1
      exact (@neg_smul (ZMod 5) (Fin (k + 1) → ZMod 5) _ _
        (inferInstance : Module (ZMod 5) (Fin (k + 1) → ZMod 5)) c a).symm
    rw [hxw, fiveForm_add_left, fiveForm_smul_left, fiveForm_smul_right, fiveForm_smul_right]
    rw [hcdef]
    field_simp [ha0]
    ring
  have hw2 : x - c • a ∈ fiveOrth k ε (fiveOrth k ε (Submodule.span (ZMod 5) {a})) :=
    Submodule.sub_mem _ hx
      (Submodule.smul_mem _ _ (hle (Submodule.mem_span_singleton_self a)))
  have hw0 : x - c • a = 0 :=
    (isFiveNondeg_iff.1 hnd) (x - c • a) hw1 ((mem_fiveOrth (k := k) (ε := ε)
      (U := fiveOrth k ε (Submodule.span (ZMod 5) {a}))).1 hw2)
  rw [sub_eq_zero.mp hw0]
  exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a)

theorem isFiveNondeg_fiveOrth_span_singleton {k : ℕ} {ε : Bool} {a : Fin (k + 1) → ZMod 5}
    (ha0 : fiveForm k ε a a ≠ 0) :
    IsFiveNondeg k ε (fiveOrth k ε (Submodule.span (ZMod 5) {a})) := by
  have h := isFiveNondeg_inf_fiveOrth (k := k) (ε := ε) (W := ⊤)
    (U := Submodule.span (ZMod 5) {a}) (isFiveNondeg_top k ε)
    (isFiveNondeg_span_singleton ha0) le_top
  rwa [top_inf_eq] at h

theorem fiveForm_mulVec_inv {k : ℕ} {ε : Bool} {M : GL (Fin (k + 1)) (ZMod 5)}
    (hM : ∀ x y, fiveForm k ε ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y)
    (x y : Fin (k + 1) → ZMod 5) :
    fiveForm k ε (((M⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      (((M⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
        Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y := by
  rw [← hM (((M⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
    (((M⁻¹ : GL (Fin (k + 1)) (ZMod 5)) :
      Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y)]
  simp only [Matrix.mulVec_mulVec, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.GeneralLinearGroup.coe_one, Matrix.one_mulVec]

theorem conj_mem_fiveReflectionGroup {k : ℕ} {ε π : Bool} {M : GL (Fin (k + 1)) (ZMod 5)}
    (hM : ∀ x y, fiveForm k ε ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y)
    {g : GL (Fin (k + 1)) (ZMod 5)} (hg : g ∈ fiveReflectionGroup k ε π) :
    M * g * M⁻¹ ∈ fiveReflectionGroup k ε π := by
  induction hg using Subgroup.closure_induction with
  | mem r hr => exact Subgroup.subset_closure (conj_mem_fiveReflections hM hr)
  | one => simp
  | mul a b _ _ iha ihb =>
      rw [show M * (a * b) * M⁻¹ = (M * a * M⁻¹) * (M * b * M⁻¹) by group]
      exact Subgroup.mul_mem _ iha ihb
  | inv a _ iha =>
      rw [show M * a⁻¹ * M⁻¹ = (M * a * M⁻¹)⁻¹ by group]
      exact Subgroup.inv_mem _ iha

@[expose] noncomputable def conjMulEquiv_fiveReflectionGroup {k : ℕ} {ε π : Bool}
    (M : GL (Fin (k + 1)) (ZMod 5))
    (hM : ∀ x y, fiveForm k ε ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y) :
    fiveReflectionGroup k ε π ≃* fiveReflectionGroup k ε π where
  toFun g := ⟨M * (g : GL (Fin (k + 1)) (ZMod 5)) * M⁻¹, conj_mem_fiveReflectionGroup hM g.2⟩
  invFun g := ⟨M⁻¹ * (g : GL (Fin (k + 1)) (ZMod 5)) * M, by
    simpa only [inv_inv] using
      conj_mem_fiveReflectionGroup (M := M⁻¹) (fiveForm_mulVec_inv hM) g.2⟩
  left_inv g := by ext; group
  right_inv g := by ext; group
  map_mul' g h := by
    apply Subtype.ext
    simp only [Subgroup.coe_mul]
    group

@[simp] theorem conjMulEquiv_fiveReflectionGroup_apply {k : ℕ} {ε π : Bool}
    {M : GL (Fin (k + 1)) (ZMod 5)}
    (hM : ∀ x y, fiveForm k ε ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y)
    (g : fiveReflectionGroup k ε π) :
    (conjMulEquiv_fiveReflectionGroup M hM g : GL (Fin (k + 1)) (ZMod 5)) =
      M * (g : GL (Fin (k + 1)) (ZMod 5)) * M⁻¹ :=
  rfl

theorem conjMulEquiv_fiveReflectionGroup_mem_fiveReflections {k : ℕ} {ε π : Bool}
    {M : GL (Fin (k + 1)) (ZMod 5)}
    (hM : ∀ x y, fiveForm k ε ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ x)
      ((M : Matrix (Fin (k + 1)) (Fin (k + 1)) (ZMod 5)) *ᵥ y) = fiveForm k ε x y)
    (g : fiveReflectionGroup k ε π) :
    ((conjMulEquiv_fiveReflectionGroup M hM g : fiveReflectionGroup k ε π) :
        GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π ↔
      (g : GL (Fin (k + 1)) (ZMod 5)) ∈ fiveReflections k ε π := by
  constructor
  · intro h
    have h2 : M⁻¹ * (M * (g : GL (Fin (k + 1)) (ZMod 5)) * M⁻¹) * M ∈
        fiveReflections k ε π := conj_mem_fiveReflections (fiveForm_mulVec_inv hM) h
    rwa [show M⁻¹ * (M * (g : GL (Fin (k + 1)) (ZMod 5)) * M⁻¹) * M =
      (g : GL (Fin (k + 1)) (ZMod 5)) by group] at h2
  · intro h
    exact conj_mem_fiveReflections hM h

end CFSG.OddTranspositions.PartThree

end

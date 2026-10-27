module

public import CFSG.LocalAnalysis.StandardType.GGNbrGraphD4SmallProof
public import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTwE6

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

section Induced

@[expose] noncomputable def ggInducedAut {X : Type*} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) : MulAut X →* MulAut R :=
  (MulAut.congr θ).toMonoidHom.comp (centerQuotAut X)

theorem ggInducedAut_apply {X : Type*} [Group X] {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (a : MulAut X) (x : X) :
    ggInducedAut θ a (θ (x : X ⧸ Subgroup.center X)) = θ ((a x : X) : X ⧸ Subgroup.center X) := by
  simp [ggInducedAut, MulAut.congr_apply]

theorem ggLAut_eq_ggInducedAut {G : Type*} [Group G] (L : Subgroup G) {R : Type} [Group R]
    (θ : L ⧸ Subgroup.center L ≃* R) (g : Subgroup.normalizer (L : Set G)) :
    ggLAut L θ g = ggInducedAut θ (L.normalizerMonoidHom g) :=
  rfl

theorem ggInducedAut_injective_of_perfect {X : Type*} [Group X] {R : Type} [Group R]
    (hX : commutator X = ⊤) (θ : X ⧸ Subgroup.center X ≃* R) :
    Function.Injective (ggInducedAut θ) := by
  rw [injective_iff_map_eq_one]
  intro a ha
  have hz : ∀ l : X, a l * l⁻¹ ∈ Subgroup.center X := by
    intro l
    have h1 := congrArg (fun φ => φ (θ (l : X ⧸ Subgroup.center X))) ha
    simp only [ggInducedAut_apply, MulAut.one_apply] at h1
    have h2 : l⁻¹ * a l ∈ Subgroup.center X := by
      have := inv_mem (QuotientGroup.eq.mp (θ.injective h1))
      simpa [mul_inv_rev] using this
    have h3 : a l * l⁻¹ = l⁻¹ * a l := by
      have := (Subgroup.mem_center_iff.mp h2) l
      calc a l * l⁻¹ = (l * (l⁻¹ * a l)) * l⁻¹ := by group
        _ = ((l⁻¹ * a l) * l) * l⁻¹ := by rw [this]
        _ = l⁻¹ * a l := by group
    rw [h3]
    exact h2
  let f : X →* X :=
    { toFun := fun l => a l * l⁻¹
      map_one' := by simp
      map_mul' := fun p q => by
        have h := (Subgroup.mem_center_iff.mp (hz q)) p⁻¹
        simp only [map_mul, mul_inv_rev]
        calc a p * a q * (q⁻¹ * p⁻¹) = a p * ((a q * q⁻¹) * p⁻¹) := by group
          _ = a p * (p⁻¹ * (a q * q⁻¹)) := by rw [h]
          _ = a p * p⁻¹ * (a q * q⁻¹) := by group }
  have hker : commutator X ≤ f.ker := by
    rw [commutator_def, Subgroup.commutator_le]
    intro p _ q _
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hz q)) (f p)
  ext l
  have h1 : f l = 1 := hker (by rw [hX]; exact Subgroup.mem_top _)
  have h2 : a l = l := mul_inv_eq_one.mp h1
  simpa using h2

@[expose] def GGInducedInn {X : Type*} [Group X] (A : Subgroup (MulAut X)) {R : Type} [Group R]
    (θ : X ⧸ Subgroup.center X ≃* R) (I : Set (MulAut R)) : Prop :=
  ∀ a ∈ A, ggInducedAut θ a ∈ I

@[expose] def GGInnField {R : Type} [Group R] (I F : Set (MulAut R)) (φ : MulAut R) : Prop :=
  ∃ u ∈ I, ∃ f ∈ Subgroup.closure F, φ = u * f

end Induced

section AutsOf

variable {G : Type*} [Group G]

@[expose] noncomputable def ggAutsOf (X S : Subgroup G) (h : S ≤ Subgroup.normalizer (X : Set G)) :
    Subgroup (MulAut ↥X) :=
  (X.normalizerMonoidHom.comp (Subgroup.inclusion h)).range

theorem mem_ggAutsOf {X S : Subgroup G} (h : S ≤ Subgroup.normalizer (X : Set G))
    {a : MulAut ↥X} :
    a ∈ ggAutsOf X S h ↔ ∃ (s : G) (hs : s ∈ S), X.normalizerMonoidHom ⟨s, h hs⟩ = a := by
  constructor
  · rintro ⟨s, rfl⟩
    exact ⟨s, s.2, rfl⟩
  · rintro ⟨s, hs, rfl⟩
    exact ⟨⟨s, hs⟩, rfl⟩

theorem normalizerMonoidHom_apply_coe {X : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (X : Set G)) (k : ↥X) :
    ((X.normalizerMonoidHom ⟨s, hs⟩ k : ↥X) : G) = s * k * s⁻¹ :=
  rfl

end AutsOf

section Local

@[expose] def GGAutLocal {X : Type*} [Group X] (A : Subgroup (MulAut X)) (σ : MulAut X)
    (J : Subgroup X) : Prop :=
  IsElemAbelian 3 A ∧ σ ∈ A ∧ σ ≠ 1 ∧ IsComponentOf J (ggAutFixedSubgroup σ) ∧
    ∀ a ∈ A, ∀ j ∈ J, a j ∈ J

@[expose] def GGKLocal {X : Type*} [Group X] (A : Subgroup (MulAut X)) (σ : MulAut X)
    (J : Subgroup X) : Prop :=
  GGAutLocal A σ J ∧ ∀ a ∈ A, (∀ j ∈ J, a j = j) → a ∈ Subgroup.zpowers σ

end Local

section Induce

@[expose] def GGAutsInduceOn {X : Type*} [Group X] (A : Subgroup (MulAut X)) (J : Subgroup X)
    {R : Type} [Group R] (θ' : ↥J ⧸ Subgroup.center ↥J ≃* R) (I : Set (MulAut R)) : Prop :=
  ∀ a ∈ A, ∃ φ ∈ I, LargeEvenInduces θ' (fun j j' : ↥J => a (j : X) = (j' : X)) φ

@[expose] def GGConjInducesOn {G : Type*} [Group G] (S J : Subgroup G) {R : Type} [Group R]
    (θ : ↥J ⧸ Subgroup.center ↥J ≃* R) (I : Set (MulAut R)) : Prop :=
  ∀ s ∈ S, ∃ φ ∈ I, LargeEvenInduces θ (fun j j' : ↥J => (j' : G) = s * j * s⁻¹) φ

@[expose] def GGAutsFixedInCenter {X : Type*} [Group X] (A : Subgroup (MulAut X))
    (J : Subgroup X) : Prop :=
  ∀ j : ↥J, (∀ a ∈ A, a (j : X) = j) → j ∈ Subgroup.center ↥J

@[expose] def GGConjFixedInCenter {G : Type*} [Group G] (S J : Subgroup G) : Prop :=
  ∀ j : ↥J, (∀ s ∈ S, s * (j : G) * s⁻¹ = j) → j ∈ Subgroup.center ↥J

end Induce

section Transport

@[expose] def centerQuotCongr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    X ⧸ Subgroup.center X ≃* Y ⧸ Subgroup.center Y :=
  QuotientGroup.congr (Subgroup.center X) (Subgroup.center Y) e (Subgroup.map_center_eq e)

theorem centerQuotCongr_mk {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    centerQuotCongr e (x : X ⧸ Subgroup.center X) = ((e x : Y) : Y ⧸ Subgroup.center Y) :=
  rfl

theorem centerQuotCongr_symm {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) :
    centerQuotCongr e.symm = (centerQuotCongr e).symm := by
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    apply (centerQuotCongr e).injective
    rw [MulEquiv.apply_symm_apply]
    change ((e (e.symm y) : Y) : Y ⧸ Subgroup.center Y) = _
    rw [MulEquiv.apply_symm_apply]

theorem centerQuotCongr_trans_symm_trans {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {R : Type} [Group R] (θ : X ⧸ Subgroup.center X ≃* R) :
    (centerQuotCongr e).trans ((centerQuotCongr e).symm.trans θ) = θ := by
  ext q
  simp

theorem centerQuotCongr_symm_trans_trans {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {R : Type} [Group R] (θ : Y ⧸ Subgroup.center Y ≃* R) :
    (centerQuotCongr e).symm.trans ((centerQuotCongr e).trans θ) = θ := by
  ext q
  simp

theorem largeEvenMarking_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {P : LargeEvenMarkProp X} {P' : LargeEvenMarkProp Y}
    (hPP' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : Y ⧸ Subgroup.center Y ≃* R), P' lab R I F θ →
        P lab R I F ((centerQuotCongr e).trans θ))
    (h : LargeEvenMarking Y P') : LargeEvenMarking X P := by
  obtain ⟨hY, lab, hlab, hraw⟩ := h
  have hperf : Group.IsPerfect Y := ⟨hY⟩
  have hX : commutator X = ⊤ :=
    (Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective).commutator_eq_top
  refine ⟨hX, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, hθ⟩
  exact ⟨hs, hna, (centerQuotCongr e).trans θ, hPP' lab R I F θ hθ⟩

theorem ggMarkingAll_congr {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y)
    {Q : LargeEvenMarkProp X} {Q' : LargeEvenMarkProp Y}
    (hQQ' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : Y ⧸ Subgroup.center Y ≃* R), Q lab R I F ((centerQuotCongr e).trans θ) →
        Q' lab R I F θ)
    (h : GGMarkingAll Q) : GGMarkingAll Q' := by
  intro P hP
  have hP' : LargeEvenMarking X
      (fun lab R _ I F θX => P lab R I F ((centerQuotCongr e).symm.trans θX)) :=
    largeEvenMarking_congr e (fun lab R _ I F θ hθ => by
      rw [centerQuotCongr_symm_trans_trans]
      exact hθ) hP
  refine largeEvenMarking_congr e.symm (fun lab R _ I F θX hθX => ?_) (h _ hP')
  rw [centerQuotCongr_symm]
  refine ⟨hθX.1, hQQ' lab R I F _ ?_⟩
  rw [centerQuotCongr_trans_symm_trans]
  exact hθX.2

end Transport

section MarkingAll

variable {X : Type*} [Group X]

theorem ggMarkingAll_imp {Q : LargeEvenMarkProp X} (H : Prop) (h : H → GGMarkingAll Q) :
    GGMarkingAll (fun lab R _ I F θ => H → Q lab R I F θ) := by
  intro P hP
  by_cases hH : H
  · exact largeEvenMarking_mono (fun lab R _ I F θ hPQ => ⟨hPQ.1, fun _ => hPQ.2⟩) (h hH P hP)
  · exact largeEvenMarking_mono (fun lab R _ I F θ hP' => ⟨hP', fun hh => absurd hh hH⟩) hP

theorem ggMarkingAll_and {Q₁ Q₂ : LargeEvenMarkProp X} (h₁ : GGMarkingAll Q₁)
    (h₂ : GGMarkingAll Q₂) :
    GGMarkingAll (fun lab R _ I F θ => Q₁ lab R I F θ ∧ Q₂ lab R I F θ) := by
  intro P hP
  exact largeEvenMarking_mono (fun lab R _ I F θ hh => ⟨hh.1.1, hh.1.2, hh.2⟩) (h₂ _ (h₁ P hP))

theorem ggMarkingAll_mono {Q Q' : LargeEvenMarkProp X}
    (hQQ' : ∀ (lab : LargeEvenLabel) (R : Type) [Group R] (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), Q lab R I F θ → Q' lab R I F θ)
    (h : GGMarkingAll Q) : GGMarkingAll Q' := fun P hP =>
  largeEvenMarking_mono (fun lab R _ I F θ hh => ⟨hh.1, hQQ' lab R I F θ hh.2⟩) (h P hP)

theorem ggMarkingAll_apply {Q : LargeEvenMarkProp X} {P : LargeEvenMarkProp X}
    (h : GGMarkingAll Q) (hP : LargeEvenMarking X P) :
    LargeEvenMarking X fun lab R _ I F θ => P lab R I F θ ∧ Q lab R I F θ :=
  h P hP

theorem largeEvenMarking_exists' {P : LargeEvenMarkProp X} (h : LargeEvenMarking X P) :
    commutator X = ⊤ ∧ ∃ (lab : LargeEvenLabel) (R : Type) (_ : Group R) (I F : Set (MulAut R))
      (θ : X ⧸ Subgroup.center X ≃* R), LargeEvenInLambda2 lab ∧ P lab R I F θ := by
  obtain ⟨hX, lab, hlab, hraw⟩ := h
  obtain ⟨R, _, I, F, -, -, θ, hθ⟩ := largeEvenRawDatum_exists hraw
  exact ⟨hX, lab, R, inferInstance, I, F, θ, hlab, hθ⟩

end MarkingAll

section Compare

theorem largeEvenInduces_congr_equiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) {R : Type}
    [Group R] (θ : Y ⧸ Subgroup.center Y ≃* R) (relX : X → X → Prop) (relY : Y → Y → Prop)
    (hrel : ∀ x x', relX x x' ↔ relY (e x) (e x')) (φ : MulAut R) :
    LargeEvenInduces ((centerQuotCongr e).trans θ) relX φ ↔ LargeEvenInduces θ relY φ := by
  constructor
  · intro h y y' hy
    obtain ⟨x, rfl⟩ := e.surjective y
    obtain ⟨x', rfl⟩ := e.surjective y'
    exact h x x' ((hrel x x').2 hy)
  · intro h x x' hx
    exact h (e x) (e x') ((hrel x x').1 hx)

theorem ggAutsInduceOn_iff {G : Type*} [Group G] {X S J : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (X : Set G)) (hJX : J ≤ X) {R : Type} [Group R]
    (θ : ↥(J.subgroupOf X) ⧸ Subgroup.center ↥(J.subgroupOf X) ≃* R) (I : Set (MulAut R)) :
    GGAutsInduceOn (ggAutsOf X S hS) (J.subgroupOf X) θ I ↔
      GGConjInducesOn S J
        ((centerQuotCongr (Subgroup.subgroupOfEquivOfLe hJX)).symm.trans θ) I := by
  set e := Subgroup.subgroupOfEquivOfLe hJX with he
  have hθ : (centerQuotCongr e).trans ((centerQuotCongr e).symm.trans θ) = θ :=
    centerQuotCongr_trans_symm_trans e θ
  have key : ∀ (s : G) (hs : s ∈ S) (φ : MulAut R),
      LargeEvenInduces θ (fun j j' : ↥(J.subgroupOf X) =>
        (X.normalizerMonoidHom ⟨s, hS hs⟩ (j : ↥X) : ↥X) = (j' : ↥X)) φ ↔
      LargeEvenInduces ((centerQuotCongr e).symm.trans θ)
        (fun j j' : ↥J => (j' : G) = s * j * s⁻¹) φ := by
    intro s hs φ
    have := largeEvenInduces_congr_equiv e ((centerQuotCongr e).symm.trans θ)
      (fun j j' : ↥(J.subgroupOf X) => (X.normalizerMonoidHom ⟨s, hS hs⟩ (j : ↥X) : ↥X) = (j' : ↥X))
      (fun j j' : ↥J => (j' : G) = s * j * s⁻¹) (fun j j' => by
        constructor
        · intro h
          have := congrArg Subtype.val h
          rw [normalizerMonoidHom_apply_coe] at this
          exact this.symm
        · intro h
          apply Subtype.ext
          rw [normalizerMonoidHom_apply_coe]
          exact h.symm) φ
    rwa [hθ] at this
  constructor
  · intro h s hs
    obtain ⟨φ, hφ, hind⟩ := h _ ((mem_ggAutsOf hS).2 ⟨s, hs, rfl⟩)
    exact ⟨φ, hφ, (key s hs φ).1 hind⟩
  · intro h a ha
    obtain ⟨s, hs, rfl⟩ := (mem_ggAutsOf hS).1 ha
    obtain ⟨φ, hφ, hind⟩ := h s hs
    exact ⟨φ, hφ, (key s hs φ).2 hind⟩

theorem mem_center_iff_of_mulEquiv {X Y : Type*} [Group X] [Group Y] (e : X ≃* Y) (x : X) :
    e x ∈ Subgroup.center Y ↔ x ∈ Subgroup.center X := by
  rw [Subgroup.mem_center_iff, Subgroup.mem_center_iff]
  constructor
  · intro h z
    apply e.injective
    rw [map_mul, map_mul]
    exact h (e z)
  · intro h z
    obtain ⟨w, rfl⟩ := e.surjective z
    rw [← map_mul, ← map_mul, h w]

theorem ggAutsFixedInCenter_iff {G : Type*} [Group G] {X S J : Subgroup G}
    (hS : S ≤ Subgroup.normalizer (X : Set G)) (hJX : J ≤ X) :
    GGAutsFixedInCenter (ggAutsOf X S hS) (J.subgroupOf X) ↔ GGConjFixedInCenter S J := by
  set e := Subgroup.subgroupOfEquivOfLe hJX with he
  have hfix : ∀ (j : ↥(J.subgroupOf X)),
      (∀ a ∈ ggAutsOf X S hS, a (j : ↥X) = j) ↔
        ∀ s ∈ S, s * ((e j : ↥J) : G) * s⁻¹ = (e j : G) := by
    intro j
    constructor
    · intro h s hs
      have := congrArg Subtype.val (h _ ((mem_ggAutsOf hS).2 ⟨s, hs, rfl⟩))
      rw [normalizerMonoidHom_apply_coe] at this
      exact this
    · intro h a ha
      obtain ⟨s, hs, rfl⟩ := (mem_ggAutsOf hS).1 ha
      apply Subtype.ext
      rw [normalizerMonoidHom_apply_coe]
      exact h s hs
  constructor
  · intro h j hj
    obtain ⟨j', rfl⟩ := e.surjective j
    exact (mem_center_iff_of_mulEquiv e j').2 (h j' ((hfix j').2 hj))
  · intro h j hj
    exact (mem_center_iff_of_mulEquiv e j).1 (h (e j) ((hfix j).1 hj))

end Compare

section AutsOfLemmas

variable {G : Type*} [Group G]

theorem normalizerMonoidHom_eq_one_iff {X : Subgroup G} {s : G}
    (hs : s ∈ Subgroup.normalizer (X : Set G)) :
    X.normalizerMonoidHom ⟨s, hs⟩ = 1 ↔ s ∈ Subgroup.centralizer (X : Set G) := by
  constructor
  · intro h
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h' := congrArg (fun a : MulAut ↥X => ((a ⟨k, hk⟩ : ↥X) : G)) h
    simp only [normalizerMonoidHom_apply_coe, MulAut.one_apply] at h'
    calc k * s = (s * k * s⁻¹) * s := by rw [h']
      _ = s * k := by group
  · intro h
    ext k
    rw [normalizerMonoidHom_apply_coe, MulAut.one_apply]
    have := Subgroup.mem_centralizer_iff.mp h (k : G) k.2
    calc s * (k : G) * s⁻¹ = (k : G) * s * s⁻¹ := by rw [this]
      _ = k := by group

theorem ggAutFixedSubgroup_normalizerMonoidHom {X : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    ggAutFixedSubgroup (X.normalizerMonoidHom ⟨g, hg⟩) =
      (X ⊓ Subgroup.centralizer ({g} : Set G)).subgroupOf X := by
  ext k
  rw [mem_ggAutFixedSubgroup, Subgroup.mem_subgroupOf, Subgroup.mem_inf,
    Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    have h' := congrArg Subtype.val h
    rw [normalizerMonoidHom_apply_coe] at h'
    refine ⟨k.2, ?_⟩
    calc (k : G) * g = (g * k * g⁻¹) * g := by rw [h']
      _ = g * k := by group
  · rintro ⟨-, h⟩
    apply Subtype.ext
    rw [normalizerMonoidHom_apply_coe]
    calc g * (k : G) * g⁻¹ = (k : G) * g * g⁻¹ := by rw [h]
      _ = k := by group

theorem isComponentOf_subgroupOf_ggAutFixed {X J : Subgroup G} {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) (hJX : J ≤ X)
    (hJ : IsComponentOf J (X ⊓ Subgroup.centralizer ({g} : Set G))) :
    IsComponentOf (J.subgroupOf X)
      (ggAutFixedSubgroup (X.normalizerMonoidHom ⟨g, hg⟩)) := by
  rw [ggAutFixedSubgroup_normalizerMonoidHom hg]
  refine ⟨Subgroup.comap_mono hJ.1, hJ.2.1.comap X.subtype, ?_⟩
  exact CFSG.Assembly.IsQuasisimple.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJX) hJ.2.2

theorem ggAutsOf_apply_mem {X S J : Subgroup G} (h : S ≤ Subgroup.normalizer (X : Set G))
    (hSJ : S ≤ Subgroup.normalizer (J : Set G)) :
    ∀ a ∈ ggAutsOf X S h, ∀ j ∈ J.subgroupOf X, a j ∈ J.subgroupOf X := by
  intro a ha j hj
  obtain ⟨s, hs, rfl⟩ := (mem_ggAutsOf h).1 ha
  rw [Subgroup.mem_subgroupOf] at hj ⊢
  rw [normalizerMonoidHom_apply_coe]
  exact (Subgroup.mem_normalizer_iff.mp (hSJ hs) _).mp hj

theorem isElemAbelian_ggAutsOf {X S : Subgroup G} (h : S ≤ Subgroup.normalizer (X : Set G))
    (hS : IsElemAbelian 3 S) : IsElemAbelian 3 (ggAutsOf X S h) :=
  isElemAbelian_range_of_comm (fun a b => hS.1.is_comm.comm a b)
    (fun a => Subtype.ext (by simpa using hS.2 a a.2)) _

theorem card_ggAutsOf_mul_card {X S : Subgroup G} (h : S ≤ Subgroup.normalizer (X : Set G)) :
    Nat.card (ggAutsOf X S h) * Nat.card ↥(S ⊓ Subgroup.centralizer (X : Set G)) =
      Nat.card S := by
  set f : ↥S →* MulAut ↥X := X.normalizerMonoidHom.comp (Subgroup.inclusion h) with hf
  have hker : f.ker = (S ⊓ Subgroup.centralizer (X : Set G)).subgroupOf S := by
    ext s
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    have := normalizerMonoidHom_eq_one_iff (X := X) (h s.2)
    constructor
    · intro hs
      exact ⟨s.2, this.1 hs⟩
    · intro hs
      exact this.2 hs.2
  have h1 := Subgroup.card_ker_mul_card_range f
  have h2 : Nat.card f.ker = Nat.card ↥(S ⊓ Subgroup.centralizer (X : Set G)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [h2] at h1
  rw [mul_comm]
  exact h1

end AutsOfLemmas

end CFSG.StandardType

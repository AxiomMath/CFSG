module

public import CFSG.Quasithin.Background.RonanE111Defs
public import CFSG.Quasithin.Vol2.Ch12Sec6P31SecAS

public section

namespace CFSG.Quasithin.H13.P31Sec

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.RonanE111

section Conj

variable {Q : Type} [Group Q]

@[expose] def conjOn (M : Subgroup Q) {g : Q} (hg : g ∈ Subgroup.normalizer (M : Set Q)) : ↥M ≃* ↥M where
  toFun m := ⟨g * (m : Q) * g⁻¹, (Subgroup.mem_normalizer_iff.1 hg (m : Q)).1 m.2⟩
  invFun m := ⟨g⁻¹ * (m : Q) * g, by
    have h := (Subgroup.mem_normalizer_iff.1 hg (g⁻¹ * (m : Q) * g)).2 (by
      have : g * (g⁻¹ * (m : Q) * g) * g⁻¹ = (m : Q) := by group
      rw [this]
      exact m.2)
    exact h⟩
  left_inv m := by
    apply Subtype.ext
    show g⁻¹ * (g * (m : Q) * g⁻¹) * g = (m : Q)
    group
  right_inv m := by
    apply Subtype.ext
    show g * (g⁻¹ * (m : Q) * g) * g⁻¹ = (m : Q)
    group
  map_mul' a b := by
    apply Subtype.ext
    show g * ((a : Q) * (b : Q)) * g⁻¹ = g * (a : Q) * g⁻¹ * (g * (b : Q) * g⁻¹)
    group

theorem coe_conjOn (M : Subgroup Q) {g : Q} (hg : g ∈ Subgroup.normalizer (M : Set Q)) (m : ↥M) :
    ((conjOn M hg m : ↥M) : Q) = g * (m : Q) * g⁻¹ := rfl

end Conj

section Action

variable {Q : Type} [Group Q] (M N : Subgroup Q) [hN : (N.subgroupOf M).Normal]

abbrev secB : Subgroup Q := Subgroup.normalizer (M : Set Q) ⊓ Subgroup.normalizer (N : Set Q)

variable {M N}

theorem mem_normalizer_self {m : Q} (hm : m ∈ M) : m ∈ Subgroup.normalizer (M : Set Q) :=
  Subgroup.le_normalizer hm

theorem le_normalizer_of_normal (hNM : N ≤ M) : M ≤ Subgroup.normalizer (N : Set Q) := by
  intro m hm
  rw [Subgroup.mem_normalizer_iff]
  intro x
  constructor
  · intro hx
    exact hN.conj_mem (⟨x, hNM hx⟩ : ↥M) (show (⟨x, hNM hx⟩ : ↥M) ∈ N.subgroupOf M from hx)
      ⟨m, hm⟩
  · intro hx
    have h2 : (⟨m * x * m⁻¹, hNM hx⟩ : ↥M) ∈ N.subgroupOf M := hx
    have h3 : ((⟨m⁻¹, M.inv_mem hm⟩ : ↥M) * (⟨m * x * m⁻¹, hNM hx⟩ : ↥M) *
        (⟨m⁻¹, M.inv_mem hm⟩ : ↥M)⁻¹ : ↥M) ∈ N.subgroupOf M :=
      hN.conj_mem _ h2 (⟨m⁻¹, M.inv_mem hm⟩ : ↥M)
    have h4 : (m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ : Q) ∈ N := h3
    have h5 : (m⁻¹ * (m * x * m⁻¹) * (m⁻¹)⁻¹ : Q) = x := by group
    rwa [h5] at h4

theorem le_secB_of_le (hNM : N ≤ M) : M ≤ secB M N :=
  fun _ hm => ⟨mem_normalizer_self hm, le_normalizer_of_normal hNM hm⟩

@[expose] noncomputable def secAct {g : Q} (hg : g ∈ secB M N) : MulAut (↥M ⧸ N.subgroupOf M) :=
  QuotientGroup.congr (N.subgroupOf M) (N.subgroupOf M) (conjOn M hg.1) (by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact (Subgroup.mem_normalizer_iff.1 hg.2 (y : Q)).1 hy
    · intro hx
      refine ⟨(conjOn M hg.1).symm x, ?_, (conjOn M hg.1).apply_symm_apply x⟩
      have h : (g⁻¹ * (x : Q) * g) ∈ N := by
        refine (Subgroup.mem_normalizer_iff.1 hg.2 (g⁻¹ * (x : Q) * g)).2 ?_
        have : g * (g⁻¹ * (x : Q) * g) * g⁻¹ = (x : Q) := by group
        rw [this]
        exact hx
      exact h)

theorem secAct_mk {g : Q} (hg : g ∈ secB M N) (m : ↥M) :
    secAct hg (QuotientGroup.mk m) = QuotientGroup.mk (conjOn M hg.1 m) :=
  QuotientGroup.congr_mk _ _ _ _ m

@[expose] noncomputable def secActHom : ↥(secB M N) →* MulAut (↥M ⧸ N.subgroupOf M) where
  toFun g := secAct g.2
  map_one' := by
    refine MulEquiv.ext fun w => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
    rw [secAct_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (by simp [coe_conjOn]))
  map_mul' g h := by
    refine MulEquiv.ext fun w => ?_
    obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
    change secAct (g * h).2 (QuotientGroup.mk m) =
      secAct g.2 (secAct h.2 (QuotientGroup.mk m))
    rw [secAct_mk, secAct_mk, secAct_mk]
    exact congrArg QuotientGroup.mk (Subtype.ext (by simp [coe_conjOn, mul_assoc]))

theorem secActHom_apply (g : ↥(secB M N)) : secActHom g = secAct g.2 := rfl

theorem induces_secAct {g : Q} (hg : g ∈ secB M N) : Induces M N g (secAct hg) :=
  fun m => ⟨conjOn M hg.1 m, rfl, secAct_mk hg m⟩

theorem eq_secAct_of_induces {g : Q} (hg : g ∈ secB M N) {α : MulAut (↥M ⧸ N.subgroupOf M)}
    (h : Induces M N g α) : α = secAct hg := by
  refine MulEquiv.ext fun w => ?_
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
  obtain ⟨m', hm', hα⟩ := h m
  rw [hα, secAct_mk]
  exact congrArg QuotientGroup.mk (Subtype.ext hm')

theorem secAct_of_mem {m : Q} (hm : m ∈ M) (hmB : m ∈ secB M N) :
    secAct hmB = MulAut.conj (QuotientGroup.mk (⟨m, hm⟩ : ↥M) : ↥M ⧸ N.subgroupOf M) := by
  refine MulEquiv.ext fun w => ?_
  obtain ⟨m₂, rfl⟩ := QuotientGroup.mk_surjective w
  rw [secAct_mk, MulAut.conj_apply, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
    ← QuotientGroup.mk_mul]
  exact congrArg QuotientGroup.mk (Subtype.ext (by simp [coe_conjOn]))

end Action

section Decomposition

variable {Q : Type} [Group Q]

@[expose] def innGroup (W : Type) [Group W] : Subgroup (MulAut W) := (MulAut.conj : W →* MulAut W).range

@[expose] noncomputable def secP (T M N : Subgroup Q) [(N.subgroupOf M).Normal] :
    Subgroup (MulAut (↥M ⧸ N.subgroupOf M)) :=
  ((T ⊓ Subgroup.normalizer (M : Set Q) ⊓ Subgroup.normalizer (N : Set Q)).subgroupOf
    (secB M N)).map secActHom

variable {T M N : Subgroup Q} [hN : (N.subgroupOf M).Normal]

theorem le_secB_inf : T ⊓ Subgroup.normalizer (M : Set Q) ⊓ Subgroup.normalizer (N : Set Q) ≤
    secB M N := fun _ hx => ⟨hx.1.2, hx.2⟩

theorem secP_le_innAutInduced (hNM : N ≤ M) : secP T M N ≤ innAutInduced T M N := by
  rintro α ⟨x, hx, rfl⟩
  have hx' : (x : Q) ∈ T ⊓ Subgroup.normalizer (M : Set Q) ⊓ Subgroup.normalizer (N : Set Q) :=
    Subgroup.mem_subgroupOf.1 hx
  have hxM : (x : Q) ∈ M ⊔ (T ⊓ Subgroup.normalizer (M : Set Q) ⊓ Subgroup.normalizer (N : Set Q)) :=
    Subgroup.mem_sup_right hx'
  exact Subgroup.subset_closure ⟨(x : Q), hxM, induces_secAct x.2⟩

theorem innGroup_le_innAutInduced (hNM : N ≤ M) :
    innGroup (↥M ⧸ N.subgroupOf M) ≤ innAutInduced T M N := by
  rintro α ⟨w, rfl⟩
  obtain ⟨m, rfl⟩ := QuotientGroup.mk_surjective w
  have hmB : (m : Q) ∈ secB M N := le_secB_of_le hNM m.2
  rw [← secAct_of_mem m.2 hmB]
  exact Subgroup.subset_closure ⟨(m : Q), Subgroup.mem_sup_left m.2, induces_secAct hmB⟩

theorem innAutInduced_eq_sup (hNM : N ≤ M) :
    innAutInduced T M N = innGroup (↥M ⧸ N.subgroupOf M) ⊔ secP T M N := by
  have hMB : M ≤ secB M N := le_secB_of_le hNM
  have hPB : T ⊓ Subgroup.normalizer (M : Set Q) ⊓ Subgroup.normalizer (N : Set Q) ≤
      secB M N := le_secB_inf
  apply le_antisymm
  · refine (Subgroup.closure_le _).2 ?_
    rintro α ⟨g, hg, hind⟩
    have hgB : g ∈ secB M N := (sup_le hMB hPB) hg
    have hsub : (M ⊔ (T ⊓ Subgroup.normalizer (M : Set Q) ⊓
        Subgroup.normalizer (N : Set Q))).subgroupOf (secB M N) ≤
        (innGroup (↥M ⧸ N.subgroupOf M) ⊔ secP T M N).comap secActHom := by
      rw [Subgroup.subgroupOf_sup hMB hPB]
      refine sup_le ?_ ?_
      · rintro ⟨x, hxB⟩ hx
        have hxM : x ∈ M := hx
        have : secActHom (⟨x, hxB⟩ : ↥(secB M N)) ∈ innGroup (↥M ⧸ N.subgroupOf M) :=
          ⟨QuotientGroup.mk (⟨x, hxM⟩ : ↥M), (secAct_of_mem hxM hxB).symm⟩
        exact Subgroup.mem_sup_left this
      · intro x hx
        have : secActHom x ∈ secP T M N := ⟨x, hx, rfl⟩
        exact Subgroup.mem_sup_right this
    have h1 : secActHom (⟨g, hgB⟩ : ↥(secB M N)) ∈
        innGroup (↥M ⧸ N.subgroupOf M) ⊔ secP T M N := hsub (Subgroup.mem_subgroupOf.2 hg)
    rw [secActHom_apply] at h1
    rw [eq_secAct_of_induces hgB hind]
    exact h1
  · exact sup_le (innGroup_le_innAutInduced hNM) (secP_le_innAutInduced hNM)

end Decomposition

section Inner

variable {W : Type} [Group W]

instance normal_innGroup : (innGroup W).Normal :=
  ⟨by
    rintro _ ⟨w, rfl⟩ α
    refine ⟨α w, ?_⟩
    refine MulEquiv.ext fun x => ?_
    simp only [MulAut.conj_apply, MulAut.mul_apply, MulAut.inv_apply]
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply, map_inv]⟩

theorem conj_injective (hZ : Subgroup.center W = ⊥) :
    Function.Injective (MulAut.conj : W →* MulAut W) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro w hw
  have h : ∀ x : W, w * x * w⁻¹ = x := fun x => by
    have := congrArg (fun f : MulAut W => f x) (MonoidHom.mem_ker.1 hw)
    simpa using this
  have hc : w ∈ Subgroup.center W := by
    rw [Subgroup.mem_center_iff]
    intro g
    have := h g
    calc g * w = w * g * w⁻¹ * w := by rw [this]
      _ = w * g := by group
  rw [hZ] at hc
  exact hc

noncomputable def innEquiv (hZ : Subgroup.center W = ⊥) : W ≃* ↥(innGroup W) :=
  MonoidHom.ofInjective (conj_injective hZ)

theorem centralizer_innGroup (hZ : Subgroup.center W = ⊥) :
    Subgroup.centralizer (innGroup W : Set (MulAut W)) = ⊥ := by
  rw [eq_bot_iff]
  intro α hα
  rw [Subgroup.mem_bot]
  refine MulEquiv.ext fun w => ?_
  have hcomm : ∀ x : W, w * α x * w⁻¹ = α w * α x * (α w)⁻¹ := fun x => by
    have h := congrArg (fun f : MulAut W => f x)
      (Subgroup.mem_centralizer_iff.1 hα (MulAut.conj w) ⟨w, rfl⟩)
    simpa [MulAut.conj_apply] using h
  have hmem : (α w)⁻¹ * w ∈ Subgroup.center W := by
    rw [Subgroup.mem_center_iff]
    intro y
    obtain ⟨x, rfl⟩ := α.surjective y
    have h := hcomm x
    calc α x * ((α w)⁻¹ * w) = (α w)⁻¹ * (α w * α x * (α w)⁻¹) * w := by group
      _ = (α w)⁻¹ * (w * α x * w⁻¹) * w := by rw [h]
      _ = (α w)⁻¹ * w * α x := by group
  rw [hZ, Subgroup.mem_bot] at hmem
  have : α w = w := by
    have h2 : α w = w * ((α w)⁻¹ * w)⁻¹ := by group
    rw [hmem] at h2
    simpa using h2
  simpa using this

end Inner

section Ambient

variable {A : Type} [Group A] [Finite A]

theorem ambient_bound {S : Type} [Group S] {ν : ℕ∞} (hE : EBound S ν) (I P : Subgroup A)
    [hIn : I.Normal] (hI : IsSimpleGroup ↥I) (hnab : ∃ x y : ↥I, x * y ≠ y * x)
    (hC : Subgroup.centralizer (I : Set A) = ⊥) (hP : IsPGroup 2 ↥P) (e : ↥I ≃* S)
    (hK : CFSG.SectionRank.IsKGroupCat ↥I)
    (hrk : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup ↥I) ≤ 2) :
    E1.nParam (I ⊔ P) ≤ ν := by
  have hIX : I ≤ I ⊔ P := le_sup_left
  have hPX : P ≤ I ⊔ P := le_sup_right
  rw [E1.nParam_subgroupOf (I ⊔ P)]
  let eI : ↥(I.subgroupOf (I ⊔ P)) ≃* ↥I := Subgroup.subgroupOfEquivOfLe hIX
  refine almostSimple_bound (I := I.subgroupOf (I ⊔ P)) (P := P.subgroupOf (I ⊔ P)) hE ?_ ?_ ?_ ?_ ?_
    (eI.trans e) ?_ ?_
  · haveI := hI
    exact eI.isSimpleGroup
  · obtain ⟨x, y, hxy⟩ := hnab
    exact ⟨eI.symm x, eI.symm y, fun h => hxy (eI.symm.injective (by rw [map_mul, map_mul, h]))⟩
  · rw [eq_bot_iff]
    intro x hx
    have hxA : (x : A) ∈ Subgroup.centralizer (I : Set A) := by
      rw [Subgroup.mem_centralizer_iff]
      intro i hi
      have := Subgroup.mem_centralizer_iff.1 hx ⟨i, hIX hi⟩ (Subgroup.mem_subgroupOf.2 hi)
      exact congrArg Subtype.val this
    rw [hC, Subgroup.mem_bot] at hxA
    exact Subgroup.mem_bot.2 (Subtype.ext hxA)
  · exact hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPX).symm
  · rw [← Subgroup.subgroupOf_sup hIX hPX]
    exact Subgroup.subgroupOf_self _
  · exact CFSG.SectionRank.IsKGroupCat.of_mulEquiv hK eI
  · intro p hp hp2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt eI]
    exact hrk p hp hp2

end Ambient

section SectionBound

variable {Q : Type} [Group Q] [Finite Q]

theorem sectionBound {S : Type} [Group S] [Finite S] {ν : ℕ∞} (hE : EBound S ν)
    (hKQ : CFSG.SectionRank.IsKGroupCat Q)
    (hrk : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup S) ≤ 2)
    {T M N : Subgroup Q} [hN : (N.subgroupOf M).Normal] (hT : IsPGroup 2 ↥T) (hNM : N ≤ M)
    (hsimple : IsSimpleGroup (↥M ⧸ N.subgroupOf M))
    (hnab : ∃ a b : ↥M ⧸ N.subgroupOf M, a * b ≠ b * a) (e : (↥M ⧸ N.subgroupOf M) ≃* S) :
    E1.nParam (innAutInduced T M N) ≤ ν := by
  rw [innAutInduced_eq_sup hNM]
  have hZ : Subgroup.center (↥M ⧸ N.subgroupOf M) = ⊥ :=
    (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup hnab).2
  let eInn : (↥M ⧸ N.subgroupOf M) ≃* ↥(innGroup (↥M ⧸ N.subgroupOf M)) := innEquiv hZ
  have hW : CFSG.SectionRank.IsKGroupCat (↥M ⧸ N.subgroupOf M) :=
    (hKQ.subgroup M).quotient (N.subgroupOf M)
  have hP : IsPGroup 2 ↥(secP T M N) := by
    refine IsPGroup.map ?_ secActHom
    have hP₁ : IsPGroup 2 ↥(T ⊓ Subgroup.normalizer (M : Set Q) ⊓ Subgroup.normalizer (N : Set Q)) :=
      hT.to_le (fun x hx => hx.1.1)
    exact hP₁.of_equiv (Subgroup.subgroupOfEquivOfLe le_secB_inf).symm
  haveI : IsSimpleGroup ↥(innGroup (↥M ⧸ N.subgroupOf M)) := by
    haveI := hsimple
    exact eInn.symm.isSimpleGroup
  refine ambient_bound hE (innGroup (↥M ⧸ N.subgroupOf M)) (secP T M N) inferInstance ?_
    (centralizer_innGroup hZ) hP (eInn.symm.trans e) (CFSG.SectionRank.IsKGroupCat.of_mulEquiv hW
      eInn.symm) ?_
  · obtain ⟨a, b, hab⟩ := hnab
    exact ⟨eInn a, eInn b, fun h => hab (eInn.injective (by rw [map_mul, map_mul, h]))⟩
  · intro p hp hp2
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt (eInn.symm.trans e)]
    exact hrk p hp hp2

end SectionBound

end CFSG.Quasithin.H13.P31Sec

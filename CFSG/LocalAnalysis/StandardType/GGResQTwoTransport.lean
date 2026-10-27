module

public import CFSG.LocalAnalysis.StandardType.GGResQTwoCell
public import CFSG.LocalAnalysis.StandardType.GGResQTwoKernel
public import CFSG.LocalAnalysis.StandardType.GGResQTwoCellData
public import CFSG.LocalAnalysis.StandardType.GGResIDispatch
public import CFSG.LocalAnalysis.StandardType.GGResIStdFork
public import CFSG.LocalAnalysis.StandardType.GGResIO2bExcl
public import CFSG.LocalAnalysis.StandardType.GGResICellSound
public import CFSG.LocalAnalysis.StandardType.GGResITransport
public import CFSG.LocalAnalysis.StandardType.GGResIQEight
public import CFSG.LocalAnalysis.StandardType.GGResLeaf
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelProof
public import CFSG.LocalAnalysis.StandardType.GGE6DepPerpDefs
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyQSplit
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyRefl
public import CFSG.LocalAnalysis.StandardType.GGRCTransfer

public section

namespace CFSG.StandardType

open CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {V : Type} [AddCommGroup V] [Module (ZMod 3) V]

theorem GGReflClosed.reindex {Λ Λ' : Type} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {s : Λ → V ≃ₗ[ZMod 3] V} (e : Λ' ≃ Λ)
    (h : GGReflClosed s) : GGReflClosed (fun i => s (e i)) := by
  have hrange : Set.range (fun i => s (e i)) = Set.range s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e i, rfl⟩
    · rintro ⟨i, rfl⟩
      exact ⟨e.symm i, by simp⟩
  have hconj : ggReflConj (fun i => s (e i)) = ggReflConj s := by
    ext r
    constructor
    · rintro ⟨u, hu, i, rfl⟩
      exact ⟨u, by rwa [hrange] at hu, e i, rfl⟩
    · rintro ⟨u, hu, i, rfl⟩
      exact ⟨u, by rwa [← hrange] at hu, e.symm i, by simp⟩
  intro r hr hr2 hr1 hrank
  rw [hconj]
  exact h r (by rwa [hrange] at hr) hr2 hr1 hrank

theorem ggResQTwoLSide_mem {n : ℕ} {i : Fin (n + 1)} :
    i ∈ ggResQTwoLSide n ↔ i.val < n := by
  unfold ggResQTwoLSide
  simp only [List.mem_map, List.mem_finRange]
  constructor
  · rintro ⟨j, -, rfl⟩
    simp
  · intro h
    exact ⟨⟨i.val, h⟩, by simp, by simp⟩

@[expose] noncomputable def ggResQTwoLSideEquiv (n : ℕ) :
    Fin n ≃ {i : Fin (n + 1) // i ∈ ggResQTwoLSide n} where
  toFun j := ⟨j.castSucc, by simp [ggResQTwoLSide]⟩
  invFun i := ⟨i.1.val, ggResQTwoLSide_mem.mp i.2⟩
  left_inv j := by simp
  right_inv i := by ext; simp

theorem ggResQTwoKSide_mem {n : ℕ} {ib : Fin n} {i : Fin (n + 1)} :
    i ∈ ggResQTwoKSide n ib ↔ i ≠ ib.castSucc := by
  unfold ggResQTwoKSide
  simp only [List.mem_filter, List.mem_finRange, true_and, decide_eq_true_eq]

@[expose] noncomputable def ggResQTwoKSideEquiv (n : ℕ) (ib : Fin n) :
    Option {j : Fin n // j ≠ ib} ≃ {i : Fin (n + 1) // i ∈ ggResQTwoKSide n ib} :=
  Equiv.ofBijective
    (fun o =>
      match o with
      | none => ⟨Fin.last n, by
          rw [ggResQTwoKSide_mem]
          exact (Fin.castSucc_lt_last ib).ne'⟩
      | some j => ⟨j.1.castSucc, by
          rw [ggResQTwoKSide_mem]
          exact fun h => j.2 (Fin.castSucc_injective n h)⟩)
    ⟨by
      intro o o' h
      cases o with
      | none =>
          cases o' with
          | none => rfl
          | some j =>
              exfalso
              have hv : (Fin.last n : Fin (n + 1)) = j.1.castSucc := congrArg Subtype.val h
              exact (Fin.castSucc_lt_last j.1).ne' hv
      | some j =>
          cases o' with
          | none =>
              exfalso
              have hv : j.1.castSucc = (Fin.last n : Fin (n + 1)) := congrArg Subtype.val h
              exact (Fin.castSucc_lt_last j.1).ne hv
          | some j' =>
              have hv : j.1.castSucc = j'.1.castSucc := congrArg Subtype.val h
              have hjj : j = j' := Subtype.ext (Fin.castSucc_injective n hv)
              subst hjj
              rfl,
      by
        intro i
        rcases Fin.eq_castSucc_or_eq_last i.1 with ⟨j, hj⟩ | hj
        · by_cases h : j = ib
          · exfalso
            have hi : i.1 ∈ ggResQTwoKSide n ib := i.2
            rw [hj, h] at hi
            exact (ggResQTwoKSide_mem.mp hi) rfl
          · refine ⟨some ⟨j, h⟩, ?_⟩
            apply Subtype.ext
            simp [hj]
        · refine ⟨none, ?_⟩
          apply Subtype.ext
          simp [hj]⟩

@[expose] def ggResQTwoKFullFun {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) {b : Λ}
    {ib : Fin n} (hib : e ib = b) :
    Option {j : Λ // j ≠ b} → {i : Fin (n + 1) // i ∈ ggResQTwoKSide n ib}
  | none => ⟨Fin.last n, by
      rw [ggResQTwoKSide_mem]
      exact (Fin.castSucc_lt_last ib).ne'⟩
  | some j => ⟨(e.symm j.1).castSucc, by
      rw [ggResQTwoKSide_mem]
      exact fun h => j.2 (by
        have h' : e.symm j.1 = ib := Fin.castSucc_injective n h
        calc j.1 = e (e.symm j.1) := (e.apply_symm_apply j.1).symm
          _ = e ib := by rw [h']
          _ = b := hib)⟩

theorem ggResQTwoKFullFun_bijective {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) {b : Λ}
    {ib : Fin n} (hib : e ib = b) : Function.Bijective (ggResQTwoKFullFun e hib) := by
  constructor
  · intro o o' h
    cases o with
    | none =>
        cases o' with
        | none => rfl
        | some j =>
            exfalso
            have hv : (Fin.last n : Fin (n + 1)) = (e.symm j.1).castSucc :=
              congrArg Subtype.val h
            exact (Fin.castSucc_lt_last (e.symm j.1)).ne' hv
    | some j =>
        cases o' with
        | none =>
            exfalso
            have hv : (e.symm j.1).castSucc = (Fin.last n : Fin (n + 1)) :=
              congrArg Subtype.val h
            exact (Fin.castSucc_lt_last (e.symm j.1)).ne hv
        | some j' =>
            have hv : (e.symm j.1).castSucc = (e.symm j'.1).castSucc :=
              congrArg Subtype.val h
            have hsymm : e.symm j.1 = e.symm j'.1 := Fin.castSucc_injective n hv
            have hjj : j = j' := Subtype.ext (e.symm.injective hsymm)
            subst hjj
            rfl
  · intro i
    rcases Fin.eq_castSucc_or_eq_last i.1 with ⟨j, hj⟩ | hj
    · by_cases h : j = ib
      · exfalso
        have hi : i.1 ∈ ggResQTwoKSide n ib := i.2
        rw [hj, h] at hi
        exact (ggResQTwoKSide_mem.mp hi) rfl
      · have hne : e j ≠ b := by
          intro he
          exact h (e.injective (he.trans hib.symm))
        refine ⟨some ⟨e j, hne⟩, ?_⟩
        apply Subtype.ext
        simp [ggResQTwoKFullFun, hj, e.symm_apply_apply]
    · refine ⟨none, ?_⟩
      apply Subtype.ext
      simp [ggResQTwoKFullFun, hj]

@[expose] noncomputable def ggResQTwoKFullEquiv {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) {b : Λ}
    {ib : Fin n} (hib : e ib = b) :
    Option {j : Λ // j ≠ b} ≃ {i : Fin (n + 1) // i ∈ ggResQTwoKSide n ib} :=
  Equiv.ofBijective (ggResQTwoKFullFun e hib) (ggResQTwoKFullFun_bijective e hib)

@[simp] lemma ggResQTwoKFullEquiv_none {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) {b : Λ}
    {ib : Fin n} (hib : e ib = b) :
    ggResQTwoKFullEquiv e hib none =
      (⟨Fin.last n, by
        rw [ggResQTwoKSide_mem]
        exact (Fin.castSucc_lt_last ib).ne'⟩ :
        {i : Fin (n + 1) // i ∈ ggResQTwoKSide n ib}) := by
  rw [ggResQTwoKFullEquiv, Equiv.ofBijective_apply]
  rfl

@[simp] lemma ggResQTwoKFullEquiv_some {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) {b : Λ}
    {ib : Fin n} (hib : e ib = b) (j : {j : Λ // j ≠ b}) :
    ggResQTwoKFullEquiv e hib (some j) =
      (⟨(e.symm j.1).castSucc, by
        rw [ggResQTwoKSide_mem]
        exact fun h => j.2 (by
          have h' : e.symm j.1 = ib := Fin.castSucc_injective n h
          calc j.1 = e (e.symm j.1) := (e.apply_symm_apply j.1).symm
            _ = e ib := by rw [h']
            _ = b := hib)⟩ :
        {i : Fin (n + 1) // i ∈ ggResQTwoKSide n ib}) := by
  rw [ggResQTwoKFullEquiv, Equiv.ofBijective_apply]
  rfl

lemma ggResQTwoKFullEquiv_map {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) {b : Λ}
    {ib : Fin n} (hib : e ib = b) (o : Option {j : Λ // j ≠ b}) :
    ggResIIIdx e ((ggResQTwoKFullEquiv e hib o).1) = o.map Subtype.val := by
  cases o with
  | none => simp [ggResIIIdx_last]
  | some j => simp [ggResIIIdx_castSucc, e.apply_symm_apply]

lemma ggResQTwoKFullEquiv_symm_map {Λ : Type} {n : ℕ} (e : Fin n ≃ Λ) {b : Λ}
    {ib : Fin n} (hib : e ib = b) (i : {i : Fin (n + 1) // i ∈ ggResQTwoKSide n ib}) :
    ((ggResQTwoKFullEquiv e hib).symm i).map Subtype.val = ggResIIIdx e i.1 := by
  rcases Fin.eq_castSucc_or_eq_last i.1 with ⟨j, hj⟩ | hj
  · by_cases h : j = ib
    · exfalso
      have hi : i.1 ∈ ggResQTwoKSide n ib := i.2
      rw [hj, h] at hi
      exact (ggResQTwoKSide_mem.mp hi) rfl
    · have hne : e j ≠ b := by
        intro he
        exact h (e.injective (he.trans hib.symm))
      have hval : ggResQTwoKFullEquiv e hib (some ⟨e j, hne⟩) = i := by
        apply Subtype.ext
        simp [hj, e.symm_apply_apply]
      have hs : (ggResQTwoKFullEquiv e hib).symm i = some ⟨e j, hne⟩ :=
        (Equiv.symm_apply_eq (e := ggResQTwoKFullEquiv e hib)).mpr hval.symm
      rw [hs]
      simp [hj]
  · have hval : ggResQTwoKFullEquiv e hib none = i := by
      apply Subtype.ext
      simp [hj]
    have hs : (ggResQTwoKFullEquiv e hib).symm i = none :=
      (Equiv.symm_apply_eq (e := ggResQTwoKFullEquiv e hib)).mpr hval.symm
    rw [hs]
    simp [hj]

structure GGResQTwoSidePremises {n : ℕ}
    (g : Fin (n + 1) → V ≃ₗ[ZMod 3] V)
    (α : Fin (n + 1) → Module.Dual (ZMod 3) V) (x : V)
    (side : List (Fin (n + 1))) : Prop where
  hxline : ∀ w : V, (∀ i, i ∈ side → α i w = 0) →
    w ∈ Submodule.span (ZMod 3) {x}
  hRC : GGReflClosed (fun i : {i : Fin (n + 1) // i ∈ side} => g i.1)
  hfixnorm : ∀ t : V ≃ₗ[ZMod 3] V, t ∈ Subgroup.closure (Set.range g) → t x = x →
    t ∈ Subgroup.normalizer
      (Subgroup.closure (Set.range fun i : {i : Fin (n + 1) // i ∈ side} => g i.1) :
        Set (V ≃ₗ[ZMod 3] V))

@[expose] def GGResQTwoTransvection {n : ℕ} (g : Fin (n + 1) → V ≃ₗ[ZMod 3] V) : Prop :=
  ∃ t ∈ Subgroup.closure (Set.range g),
    Module.finrank (ZMod 3) (ggLinMove t) = 1 ∧ ∀ w, t (t w - w) = t w - w

theorem ggResQTwoReuse_exit {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n}
    {e₁ e₂ : ℤ} {u v : ZMod 3} {g : Fin (n + 1) → V ≃ₗ[ZMod 3] V}
    {h : Fin (n + 1) → V} {α : Fin (n + 1) → Module.Dual (ZMod 3) V} {x : V}
    (hg : ∀ k w, g k w = w - α k w • h k) (h2 : ∀ k, α k (h k) = 2)
    (hT : GGFTable (RingHom.id (ZMod 3))
      (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h 0 α)
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (hind : LinearIndependent (ZMod 3) h)
    (hfix : ∀ w : V, (∀ i : Fin n, α i.castSucc w = 0) →
      w ∈ Submodule.span (ZMod 3) {x})
    (w : GGCellWitI n) (hreuse : ggResQTwoReuseOk w = true)
    (hchk : ggCellWitCheckI 3 C ib ic e₁ e₂ u v w = true) :
    GGResQTwoTransvection g ∨ (u = 0 ∧ GGResIStdShapeI C ib ic e₁ e₂) ∨
      GGResIO2bI 3 C ib ic e₁ e₂ u v ∨
      ZS.LinWeyl 3 (Subgroup.closure (Set.range g)) := by
  cases w with
  | tv t₁ t₂ l₀ z =>
    simp only [ggResQTwoReuseOk, ggCellWitCheckI, Bool.and_eq_true, List.all_eq_true,
      List.mem_finRange, true_implies, decide_eq_true_eq] at hreuse hchk
    obtain ⟨⟨⟨hmin, hn₁⟩, hn₂⟩, hnY⟩ := hchk
    exact Or.inl (ggF_tvH (φ := RingHom.id (ZMod 3)) (by decide) hT hg h2 t₁ t₂ l₀
      (ggFUnit z) hmin hn₁ hn₂ hnY)
  | tvk t₁ t₂ o₀ l =>
    simp only [ggResQTwoReuseOk, ggCellWitCheckI, Bool.and_eq_true, List.all_eq_true,
      List.mem_finRange, true_implies, decide_eq_true_eq] at hreuse hchk
    obtain ⟨⟨⟨hmin, hn₁⟩, hn₂⟩, hnC⟩ := hchk
    exact Or.inl (ggF_tvkV (φ := RingHom.id (ZMod 3)) (by decide) hT hg h2 hspan hind
      t₁ t₂ o₀ l hmin hn₁ hn₂ hnC)
  | wstar typ ts d lam gw =>
    simp only [ggResQTwoReuseOk, ggCellWitCheckI, Bool.and_eq_true, List.all_eq_true,
      List.mem_finRange, true_implies, decide_eq_true_eq] at hreuse hchk
    obtain ⟨⟨⟨⟨hok, hgen⟩, hd⟩, hpair⟩, hlam⟩ := hchk
    refine Or.inr (Or.inr (Or.inr ?_))
    refine ggResI_wstar_of (φ := RingHom.id (ZMod 3)) (by decide) hg h2 hT hind hok
      (fun i => ts.getD i.val (0, [])) ?_ (fun i => (d.getD i.val 0 : ZMod 3)) hd hpair
      (fun o i => ((lam.getD o.val []).getD i.val 0 : ZMod 3)) 1 one_ne_zero hlam
    intro k
    obtain ⟨hm, hk⟩ := hgen k
    have hk' := ggFMat_eq hT hg hspan hk
    rw [List.map_singleton, List.prod_singleton] at hk'
    rw [hk']
    have key : ∀ L : List ℕ, (∀ m ∈ L, m < n + 1) →
        ((L.flatMap fun m => ggConjWord (ts.getD m (0, []))).map g).prod ∈
          Subgroup.closure (Set.range fun i : Fin (n + 1) =>
            ((ts.getD i.val (0, [])).2.map g).prod * g (ts.getD i.val (0, [])).1 *
              (((ts.getD i.val (0, [])).2.map g).prod)⁻¹) := by
      intro L hL
      induction L with
      | nil => exact Subgroup.one_mem _
      | cons m L ih =>
        rw [List.flatMap_cons, List.map_append, List.prod_append]
        refine Subgroup.mul_mem _ ?_ (ih fun m' hm' => hL m' (List.mem_cons_of_mem _ hm'))
        rw [ggF_conjWord_prod hg h2]
        exact Subgroup.subset_closure ⟨⟨m, hL m List.mem_cons_self⟩, rfl⟩
    exact key _ hm
  | std typ σ =>
    simp only [ggResQTwoReuseOk, ggCellWitCheckI, Bool.and_eq_true, List.all_eq_true,
      List.mem_finRange, true_implies, decide_eq_true_eq] at hreuse hchk
    obtain ⟨⟨⟨⟨hu, hok⟩, hlen⟩, hnd⟩, hgl⟩ := hchk
    exact Or.inr (Or.inl ⟨hu, ggResI_stdShape_of hok hlen hnd hgl⟩)
  | nospan z₁ z₂ l₁ l₂ =>
    simp only [ggResQTwoReuseOk, ggCellWitCheckI, Bool.and_eq_true, List.all_eq_true,
      List.mem_finRange, true_implies, decide_eq_true_eq] at hreuse hchk
    obtain ⟨hz, hmin⟩ := hchk
    exact (ggResI_false_of_nospan hT hind hfix (fun i => (hz i).1) (fun i => (hz i).2)
      hmin).elim
  | o2b =>
    simp only [ggResQTwoReuseOk, ggCellWitCheckI] at hreuse hchk
    exact Or.inr (Or.inr (Or.inl (ggResIO2bI_of hchk)))
  | tri _ _ => simp [ggResQTwoReuseOk] at hreuse
  | triple _ _ => simp [ggResQTwoReuseOk] at hreuse
  | gram _ _ => simp [ggResQTwoReuseOk] at hreuse
  | q8 _ _ _ _ => simp [ggResQTwoReuseOk] at hreuse
  | line _ _ _ _ _ _ _ _ => simp [ggResQTwoReuseOk] at hreuse
  | o2a _ _ _ _ _ _ _ _ => simp [ggResQTwoReuseOk] at hreuse

theorem ggResQTwoCell_exit {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n}
    {e₁ e₂ : ℤ} {u v : ZMod 3} {g : Fin (n + 1) → V ≃ₗ[ZMod 3] V}
    {h : Fin (n + 1) → V} {α : Fin (n + 1) → Module.Dual (ZMod 3) V} {xv yv : V}
    (hT : GGFTable (RingHom.id (ZMod 3))
      (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h 0 α)
    (hg : ∀ k w, g k w = w - α k w • h k) (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤)
    (hind : LinearIndependent (ZMod 3) h) (hα2 : ∀ k, α k (h k) = 2)
    (hfix : ∀ w : V, (∀ i : Fin n, α i.castSucc w = 0) →
      w ∈ Submodule.span (ZMod 3) {xv})
    (hker : ∀ w : V, (∀ i : Fin (n + 1), α i w = 0) → w = 0)
    (w : GGResQTwoCell n)
    (hsideOK : ggResQTwoCellSideOK ib w)
    (hsideL : GGResQTwoSidePremises g α xv (ggResQTwoLSide n))
    (hsideK : GGResQTwoSidePremises g α yv (ggResQTwoKSide n ib))
    (hchk : ggResQTwoCellCheck C ib ic e₁ e₂ u v w = true) :
    (∃ tag, GGResQTwoResidualShape tag n C ib ic e₁ e₂ u v) ∨
      ZS.LinWeyl 3 (Subgroup.closure (Set.range g)) ∨
      GGResQTwoTransvection g ∨
      (u = 0 ∧ GGResIStdShapeI C ib ic e₁ e₂) ∨
      GGResIO2bI 3 C ib ic e₁ e₂ u v := by
  cases w with
  | reuse w =>
    simp only [ggResQTwoCellCheck, Bool.and_eq_true] at hchk
    rcases ggResQTwoReuse_exit hg hα2 hT hspan hind hfix w
      (by simpa using hchk.1) hchk.2 with htv | hstd | ho2b | hweyl
    · exact Or.inr (Or.inr (Or.inl htv))
    · exact Or.inr (Or.inr (Or.inr (Or.inl hstd)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ho2b)))
    · exact Or.inr (Or.inl hweyl)
  | commonKernel z =>
    exact (ggResQTwoCell_commonKernel_false hT hind hker hchk).elim
  | norm side x₀ R τ k =>
    rcases hsideOK with hL | hK
    · rw [hL] at hchk
      exact (ggResQTwoCell_norm_false hT hg hspan hind hα2 hsideL.hxline hsideL.hRC
        hsideL.hfixnorm hchk).elim
    · rw [hK] at hchk
      exact (ggResQTwoCell_norm_false hT hg hspan hind hα2 (x := yv) hsideK.hxline
        hsideK.hRC hsideK.hfixnorm hchk).elim
  | residual tag =>
    refine Or.inl ⟨tag, ?_⟩
    simpa only [ggResQTwoCellCheck] using
      (ggResQTwoResidualShapeCheck_spec tag n C ib ic e₁ e₂ u v).mp hchk

@[expose] def GGResQTwoResidualCell {Λ : Type} (b : Λ) (CL : Matrix Λ Λ ℤ)
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ)
    (u v : ZMod 3) : Prop :=
  ∃ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ)
    (e : Fin n ≃ Λ) (tag : GGResQTwoResidual),
    (∀ i j, CL (e i) (e j) = C i j) ∧ e ib = b ∧
    (∀ (j : Fin n) (hj : e j ≠ b),
      CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0) ∧
    (∀ (j : Fin n) (hj : e j ≠ b),
      CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0) ∧
    CK none none = 2 ∧
    GGResQTwoResidualShape tag n C ib ic e₁ e₂ u v

@[expose] def GGResQTwoResidualCellTag {Λ : Type} (tag : GGResQTwoResidual) (b : Λ)
    (CL : Matrix Λ Λ ℤ)
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ)
    (u v : ZMod 3) : Prop :=
  ∃ (n : ℕ) (C : Matrix (Fin n) (Fin n) ℤ) (ib ic : Fin n) (e₁ e₂ : ℤ)
    (e : Fin n ≃ Λ),
    (∀ i j, CL (e i) (e j) = C i j) ∧ e ib = b ∧
    (∀ (j : Fin n) (hj : e j ≠ b),
      CK none (some ⟨e j, hj⟩) = if j = ic then e₁ else 0) ∧
    (∀ (j : Fin n) (hj : e j ≠ b),
      CK (some ⟨e j, hj⟩) none = if j = ic then e₂ else 0) ∧
    CK none none = 2 ∧
    GGResQTwoResidualShape tag n C ib ic e₁ e₂ u v

@[expose] def GGResQTwoResidualCellB2 {Λ : Type} (b : Λ) (CL : Matrix Λ Λ ℤ)
    (CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ)
    (u v : ZMod 3) : Prop :=
  GGResQTwoResidualCellTag .B3b0c2 b CL CK u v ∨
    GGResQTwoResidualCellTag .C3b0c2 b CL CK u v

theorem GGResQTwoResidualCellTag.toCell {Λ : Type} {tag : GGResQTwoResidual} {b : Λ}
    {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {u v : ZMod 3}
    (h : GGResQTwoResidualCellTag tag b CL CK u v) :
    GGResQTwoResidualCell b CL CK u v := by
  obtain ⟨n, C, ib, ic, e₁, e₂, e, hCe, hib, hrow, hcol, hCKaa, hshape⟩ := h
  exact ⟨n, C, ib, ic, e₁, e₂, e, tag, hCe, hib, hrow, hcol, hCKaa, hshape⟩

theorem GGResQTwoResidualCellB2.toCell {Λ : Type} {b : Λ} {CL : Matrix Λ Λ ℤ}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ} {u v : ZMod 3}
    (h : GGResQTwoResidualCellB2 b CL CK u v) :
    GGResQTwoResidualCell b CL CK u v := by
  rcases h with h | h
  · exact h.toCell
  · exact h.toCell

@[expose] noncomputable def ggResQTwoG {G : Type} [Group G] {Bs : Subgroup G} {Λ : Type} {V : Type}
    [AddCommGroup V] [Module (ZMod 3) V] {n : ℕ} (ι : Additive ↥Bs ≃+ V)
    (φ : Option Λ → MulAut ↥Bs) (e : Fin n ≃ Λ) : Fin (n + 1) → V ≃ₗ[ZMod 3] V :=
  fun i => ggLin (p := 3) ι (φ (ggResIIIdx e i))

@[expose] def ggResQTwoAlpha {Λ : Type} {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {n : ℕ} (α : Option Λ → Module.Dual (ZMod 3) V) (e : Fin n ≃ Λ) :
    Fin (n + 1) → Module.Dual (ZMod 3) V :=
  fun i => α (ggResIIIdx e i)

@[expose] def ggResQTwoCarrierIdx (ib : Fin 3) : Fin 4 → Fin 4 :=
  if ib = 0 then ![1, 2, 0, 3] else if ib = 1 then ![0, 2, 1, 3] else ![0, 1, 2, 3]

@[expose] def ggResQTwoCarrierPoint {Λ : Type} (e : Fin 3 ≃ Λ) (ib : Fin 3) : Fin 4 → Option Λ :=
  fun k => ggResIIIdx e (ggResQTwoCarrierIdx ib k)

theorem ggResQTwoCarrierIdx_injective (ib : Fin 3) :
    Function.Injective (ggResQTwoCarrierIdx ib) := by
  fin_cases ib <;> decide

theorem ggResQTwoCarrierPoint_injective {Λ : Type} (e : Fin 3 ≃ Λ) (ib : Fin 3) :
    Function.Injective (ggResQTwoCarrierPoint e ib) :=
  (ggResIIIdx_injective e).comp (ggResQTwoCarrierIdx_injective ib)

noncomputable def ggResQTwoCarrierBasis {Λ : Type} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {e : Fin 3 ≃ Λ} (ib : Fin 3) (h : Option Λ → V)
    (hsel : LinearIndependent (ZMod 3) h)
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤) :
    Module.Basis (Fin 4) (ZMod 3) V :=
  Module.Basis.mk (hsel.comp (ggResQTwoCarrierPoint e ib) (ggResQTwoCarrierPoint_injective e ib))
    (by
      have hcarrier_surj : Function.Surjective (ggResQTwoCarrierIdx ib) :=
        Finite.injective_iff_surjective.mp (ggResQTwoCarrierIdx_injective ib)
      have hpoint_surj : Function.Surjective (ggResQTwoCarrierPoint e ib) :=
        (ggResIIIdx_surjective e).comp hcarrier_surj
      rw [hpoint_surj.range_comp h, hspan])

@[simp] theorem ggResQTwoCarrierBasis_apply {Λ : Type} {V : Type} [AddCommGroup V]
    [Module (ZMod 3) V] {e : Fin 3 ≃ Λ} (ib : Fin 3) (h : Option Λ → V)
    (hsel : LinearIndependent (ZMod 3) h)
    (hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤) (k : Fin 4) :
    ggResQTwoCarrierBasis (e := e) ib h hsel hspan k = h (ggResQTwoCarrierPoint e ib k) := by
  rw [ggResQTwoCarrierBasis, Module.Basis.mk_apply]
  rfl

theorem ggResQTwoCellAt_exists {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} {ib ic : Fin n}
    {e₁ e₂ : ℤ} {wits : List (ℕ × ℕ × GGResQTwoCell n)} {u v : ZMod 3}
    (h : ggResQTwoCellAt C ib ic e₁ e₂ wits u v = true) :
    ∃ w ∈ wits, w.1 = u.val ∧ w.2.1 = v.val ∧
      ggResQTwoCellCheck C ib ic e₁ e₂ u v w.2.2 = true := by
  unfold ggResQTwoCellAt at h
  split at h
  · rename_i w hw
    have hp := List.find?_some hw
    simp only [Bool.and_eq_true, beq_iff_eq] at hp
    exact ⟨w, List.mem_of_find?_eq_some hw, hp.1, hp.2, h⟩
  · exact Bool.noConfusion h

theorem ggResQTwoSidePremises_L
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod 3) V}
    (hH : GGResHyp 3 B Bs x L D J y K) (hxBs : x ∈ Bs)
    (hWL : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hφ : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod 3))
    (hsel : LinearIndependent (ZMod 3) h)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hFix : GGTBFixInput) (ha₀ : GGLNoncyclicInput)
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = C i j) :
    GGResQTwoSidePremises (ggResQTwoG ι φ e) (ggResQTwoAlpha α e)
      (ggResVec ι x hxBs) (ggResQTwoLSide n) := by
  classical
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let eL := ggResQTwoLSideEquiv n
  let S := {i : Fin (n + 1) // i ∈ ggResQTwoLSide n}
  let es : S ≃ Λ := eL.symm.trans e
  let Cside : Matrix S S ℤ := fun i j => C (eL.symm i) (eL.symm j)
  let Mside : CoxeterMatrix S := ML.reindex es.symm
  let hside : S → V := fun i => h (some (es i))
  let αside : S → Module.Dual (ZMod 3) V := fun i => α (some (es i))
  let sside : S → V ≃ₗ[ZMod 3] V := fun i => ggLin (p := 3) ι (φ (some (es i)))
  have hCside : GGIntCartan Mside Cside := by
    have h := hCL.reindex es.symm
    convert h using 2
    ext i j
    change C (eL.symm i) (eL.symm j) = CL (e (eL.symm i)) (e (eL.symm j))
    rw [← hCe]
  have hFTside : TauCeti.IsFiniteType Cside :=
    isFiniteType_of_ggIsWeylMatrixFixed (l05nDP4_weyl_reindex hWL es.symm) hCside
  have hpair : ∀ i j : S, αside i (hside j) = (Cside i j : ZMod 3) := by
    intro i j
    simp only [αside, hside, Cside, es, Equiv.trans_apply]
    rw [hL, hCe]
  have hinj : Function.Injective (fun i : S => some (es i) : S → Option Λ) := by
    intro i j hij
    exact es.injective (Option.some.inj hij)
  have hindside : LinearIndependent (ZMod 3) hside :=
    hsel.comp (fun i : S => some (es i)) hinj
  have hs : ∀ i v, sside i v = v - αside i v • hside i := fun i v => hφ _ _
  have hRCside : GGReflClosed sside :=
    ggReflClosed_of_indep (by decide : (3 : ℕ) ≠ 2) hFTside hCside hside αside hpair
      hindside sside hs
  have hval : ∀ i : S, i.1 = (eL.symm i).castSucc := by
    intro i
    exact congrArg Subtype.val (eL.apply_symm_apply i).symm
  have hfam : (fun i : S => ggResQTwoG ι φ e i.1) = sside := by
    funext i
    simp only [ggResQTwoG, hval i, ggResIIIdx_castSucc, sside, es, Equiv.trans_apply]
  have hfixspan := ggResI_fixSpan hFix hH hxBs ι hφ hAL
  refine ⟨?_, ?_, ?_⟩
  ·
    intro w hw
    apply hfixspan w
    intro i
    have hwj := hw (e.symm i).castSucc (by simp [ggResQTwoLSide])
    simpa [ggResQTwoAlpha, ggResIIIdx_castSucc, e.apply_symm_apply] using hwj
  ·
    rw [hfam]
    exact hRCside
  ·
    intro t ht htx
    have hrange_g : Set.range (ggResQTwoG ι φ e) =
        Set.range (fun o : Option Λ => ggLin (p := 3) ι (φ o)) := by
      ext u
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨ggResIIIdx e i, rfl⟩
      · rintro ⟨o, rfl⟩
        obtain ⟨i, rfl⟩ := ggResIIIdx_surjective e o
        exact ⟨i, rfl⟩
    have hclosure_g : Subgroup.closure (Set.range (ggResQTwoG ι φ e)) =
        (Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι) := by
      rw [hrange_g, MonoidHom.map_closure, ← Set.range_comp]
      rfl
    have ht' : t ∈ (Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι) := by
      rw [← hclosure_g]
      exact ht
    obtain ⟨φt, hφt, hlin⟩ := Subgroup.mem_map.mp ht'
    have hφt_top : φt ∈ ggAutomizer ⊤ Bs := by
      have hle : Subgroup.closure (Set.range φ) ≤ ggAutomizer ⊤ Bs := by
        refine (Subgroup.closure_le (ggAutomizer ⊤ Bs)).mpr ?_
        intro f hf
        rcases hf with ⟨o, rfl⟩
        cases o with
        | none =>
            exact ggAutomizer_mono Bs le_top (by
              rw [hAK]
              exact Subgroup.subset_closure (Or.inr (by simp)))
        | some i =>
            exact ggAutomizer_mono Bs le_top (by
              rw [hAL]
              exact Subgroup.subset_closure ⟨i, rfl⟩)
      exact hle hφt
    have hfixφ : φt ⟨x, hxBs⟩ = ⟨x, hxBs⟩ := by
      rw [ggLin_fix_iff (p := 3) ι φt ⟨x, hxBs⟩]
      change ggLin (p := 3) ι φt (ggResVec ι x hxBs) = ggResVec ι x hxBs
      rw [hlin]
      exact htx
    have htN : φt ∈ Subgroup.normalizer (ggAutomizer L Bs) :=
      ggAutomizer_fixes_mem_normalizer ha₀ hH.1 hxBs hφt_top hfixφ
    have hlinN : ggLin (p := 3) ι φt ∈
        Subgroup.normalizer ((ggAutomizer L Bs).map (ggLin (p := 3) ι)) :=
      Subgroup.le_normalizer_map (ggLin (p := 3) ι) ⟨φt, htN, rfl⟩
    have hmapL : (ggAutomizer L Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure (Set.range sside) := by
      rw [hAL, MonoidHom.map_closure, ← Set.range_comp]
      congr 1
      ext t
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨es.symm i, by simp [sside]⟩
      · rintro ⟨i, rfl⟩
        exact ⟨es i, by simp [sside]⟩
    rw [hmapL, hlin] at hlinN
    rwa [← hfam] at hlinN

theorem ggResQTwoSidePremises_K
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod 3) V}
    (hH : GGResHyp 3 B Bs x L D J y K) (hyBs : y ∈ Bs)
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (hφ : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod 3))
    (hsel : LinearIndependent (ZMod 3) h)
    (hα : LinearIndependent (ZMod 3) α)
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hFix : GGTBFixInput)
    {n : ℕ} (e : Fin n ≃ Λ)
    {ib : Fin n} (hib : e ib = b) :
    GGResQTwoSidePremises (ggResQTwoG ι φ e) (ggResQTwoAlpha α e)
      (ggResVec ι y hyBs) (ggResQTwoKSide n ib) := by
  classical
  have : Finite V := Finite.of_equiv (Additive ↥Bs) ι.toEquiv
  let S := {i : Fin (n + 1) // i ∈ ggResQTwoKSide n ib}
  let eK := ggResQTwoKFullEquiv e hib
  let es : S ≃ Option {j : Λ // j ≠ b} := eK.symm
  let Cside : Matrix S S ℤ := fun i j => CK (es i) (es j)
  let Mside : CoxeterMatrix S := MK.reindex es.symm
  let hside : S → V := fun i => h ((es i).map Subtype.val)
  let αside : S → Module.Dual (ZMod 3) V := fun i => α ((es i).map Subtype.val)
  let sside : S → V ≃ₗ[ZMod 3] V := fun i => ggLin (p := 3) ι (φ ((es i).map Subtype.val))
  have hCside : GGIntCartan Mside Cside := by
    have h := hCK.reindex es.symm
    convert h using 2
    ext i j
    simp only [Cside, Matrix.reindex_apply, Matrix.submatrix_apply, es, Equiv.symm_symm]
  have hFTside : TauCeti.IsFiniteType Cside :=
    isFiniteType_of_ggIsWeylMatrixFixed (l05nDP4_weyl_reindex hWK es.symm) hCside
  have hpair : ∀ i j : S, αside i (hside j) = (Cside i j : ZMod 3) := by
    intro i j
    simp only [αside, hside, Cside, es]
    rw [hK]
  have hinjOpt : Function.Injective
      (fun o : Option {j : Λ // j ≠ b} => o.map Subtype.val) := by
    intro o o' h
    cases o with
    | none => cases o' <;> simp_all
    | some j =>
        cases o' with
        | none => simp_all
        | some j' =>
            have h' : j = j' := Subtype.ext (by simpa using h)
            subst h'
            rfl
  have hinj : Function.Injective (fun i : S => (es i).map Subtype.val) :=
    hinjOpt.comp es.injective
  have hindside : LinearIndependent (ZMod 3) hside :=
    hsel.comp (fun i : S => (es i).map Subtype.val) hinj
  have hs : ∀ i v, sside i v = v - αside i v • hside i := fun i v => hφ _ _
  have hRCside : GGReflClosed sside :=
    ggReflClosed_of_indep (by decide : (3 : ℕ) ≠ 2) hFTside hCside hside αside hpair
      hindside sside hs
  have hfam : (fun i : S => ggResQTwoG ι φ e i.1) = sside := by
    funext i
    simp only [ggResQTwoG, sside]
    rw [ggResQTwoKFullEquiv_symm_map e hib i]
  have hfixK := ggResQTwo_mem_span_y_of_fixK hH hFix hφ hrefl hAL hAK hsel hα
  refine ⟨?_, ?_, ?_⟩
  ·
    intro w hw
    apply hfixK w
    intro o
    have hi := hw (eK o).1 (eK o).2
    change α (ggResIIIdx e ((eK o).1)) w = 0 at hi
    rw [ggResQTwoKFullEquiv_map e hib o] at hi
    exact hi
  ·
    rw [hfam]
    exact hRCside
  ·
    intro t ht hty
    have hrange_g : Set.range (ggResQTwoG ι φ e) =
        Set.range (fun o : Option Λ => ggLin (p := 3) ι (φ o)) := by
      ext u
      constructor
      · rintro ⟨i, rfl⟩
        exact ⟨ggResIIIdx e i, rfl⟩
      · rintro ⟨o, rfl⟩
        obtain ⟨i, rfl⟩ := ggResIIIdx_surjective e o
        exact ⟨i, rfl⟩
    have hclosure_g : Subgroup.closure (Set.range (ggResQTwoG ι φ e)) =
        (Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι) := by
      rw [hrange_g, MonoidHom.map_closure, ← Set.range_comp]
      rfl
    have ht' : t ∈ (Subgroup.closure (Set.range φ)).map (ggLin (p := 3) ι) := by
      rw [← hclosure_g]
      exact ht
    obtain ⟨φt, hφt, hlin⟩ := Subgroup.mem_map.mp ht'
    have hφt_top : φt ∈ ggAutomizer ⊤ Bs := by
      have hle : Subgroup.closure (Set.range φ) ≤ ggAutomizer ⊤ Bs := by
        refine (Subgroup.closure_le (ggAutomizer ⊤ Bs)).mpr ?_
        intro f hf
        rcases hf with ⟨o, rfl⟩
        cases o with
        | none =>
            exact ggAutomizer_mono Bs le_top (by
              rw [hAK]
              exact Subgroup.subset_closure (Or.inr (by simp)))
        | some i =>
            exact ggAutomizer_mono Bs le_top (by
              rw [hAL]
              exact Subgroup.subset_closure ⟨i, rfl⟩)
      exact hle hφt
    have hfixφ : φt ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := by
      rw [ggLin_fix_iff (p := 3) ι φt ⟨y, hyBs⟩]
      change ggLin (p := 3) ι φt (ggResVec ι y hyBs) = ggResVec ι y hyBs
      rw [hlin]
      exact hty
    have hCent : Bs ⊓ Subgroup.centralizer (K : Set G) ≤ Subgroup.zpowers y :=
      ggResQTwo_inf_centralizer_le_zpowers hH hFix hφ hrefl hAL hAK hsel hα
    have htN : φt ∈ Subgroup.normalizer (ggAutomizer K Bs) :=
      ggResQTwo_mem_normalizer_automizer_K hH hCent hrefl hAK hφt_top hfixφ
    have hlinN : ggLin (p := 3) ι φt ∈
        Subgroup.normalizer ((ggAutomizer K Bs).map (ggLin (p := 3) ι)) :=
      Subgroup.le_normalizer_map (ggLin (p := 3) ι) ⟨φt, htN, rfl⟩
    have hmapK : (ggAutomizer K Bs).map (ggLin (p := 3) ι) =
        Subgroup.closure (Set.range sside) := by
      rw [hAK, MonoidHom.map_closure]
      congr 1
      ext u
      constructor
      · rintro ⟨ψ, hψ, rfl⟩
        rcases hψ with ⟨j, rfl⟩ | rfl
        · refine ⟨eK (some j), ?_⟩
          simp [sside, es]
        · refine ⟨eK none, ?_⟩
          simp [sside, es]
      · rintro ⟨i, rfl⟩
        refine ⟨φ ((es i).map Subtype.val), ?_, rfl⟩
        cases es i with
        | none => exact Or.inr rfl
        | some j => exact Or.inl ⟨j, rfl⟩
    rw [hmapK, hlin] at hlinN
    rwa [← hfam] at hlinN

theorem ggResQTwo_actual_core
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ}
    {ML : CoxeterMatrix Λ} {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {ι : Additive ↥Bs ≃+ V} {φ : Option Λ → MulAut ↥Bs}
    {h : Option Λ → V} {α : Option Λ → Module.Dual (ZMod 3) V}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hxBs : x ∈ Bs) (hyBs : y ∈ Bs)
    (hWL : GGIsWeylMatrix ML) (hCL : GGIntCartan ML CL)
    (hWK : GGIsWeylMatrix MK) (hCK : GGIntCartan MK CK)
    (htyp : ggTypRankLt 8 ML MK)
    (hφ : ∀ o w, ggLin (p := 3) ι (φ o) w = w - α o w • h o)
    (hrefl : ∀ o, GGIsReflection 3 (φ o))
    (hL : ∀ i j : Λ, α (some i) (h (some j)) = (CL i j : ZMod 3))
    (hK : ∀ o o' : Option {i : Λ // i ≠ b},
      α (o.map Subtype.val) (h (o'.map Subtype.val)) = (CK o o' : ZMod 3))
    (hsel : LinearIndependent (ZMod 3) h)
    (hsome : ∃ j : Λ, α none (h (some j)) ≠ 0)
    (fL : ML.Group ≃* ↥(ggAutomizer L Bs))
    (hfL : ∀ i, (fL (ML.simple i) : MulAut ↥Bs) = φ (some i))
    (fK : MK.Group ≃* ↥(ggAutomizer K Bs))
    (hfK : ∀ o, (fK (MK.simple o) : MulAut ↥Bs) = φ (o.map Subtype.val))
    (hAL : ggAutomizer L Bs = Subgroup.closure (Set.range fun i : Λ => φ (some i)))
    (hAK : ggAutomizer K Bs = Subgroup.closure
      (Set.range (fun j : {j : Λ // j ≠ b} => φ (some j)) ∪ {φ none}))
    (hdel : GGDeletedConnected ML b)
    (hJ : ggAutomizer J Bs = Subgroup.closure
      (Set.range fun j : {j : Λ // j ≠ b} => φ (some j)))
    (hFork : ¬ GGCoxeterForkDatum 3 Bs L K)
    (hStd : ¬ GGCoxeterStdDatum 3 Bs L K)
    (_hE6 : ¬ GGE6DepPerpCfg 3 Bs L K)
    (_hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hFix : GGTBFixInput) (ha₀ : GGLNoncyclicInput)
    {n : ℕ} {C : Matrix (Fin n) (Fin n) ℤ} (e : Fin n ≃ Λ)
    (hCe : ∀ i j, CL (e i) (e j) = C i j)
    {ib : Fin n} (hib : e ib = b) (j₀ : Fin n) (hj₀ : j₀ ≠ ib)
    (pt : Fin n → Fin n → List (Fin n))
    (hcyc : ∀ j₁ j₂ : Fin n, j₁ ≠ ib → j₂ ≠ ib → j₁ ≠ j₂ →
      ggCycleOK C ib j₁ j₂ (pt j₁ j₂))
    (shapes : List (Fin n × ℤ × ℤ)) (vecs : List (Fin n × ℤ × ℤ × List ℕ))
    (hcand : ∀ ic : Fin n, ic ≠ ib → ∀ pr ∈ ggCartanPairsNZ,
      ggCandB C ib ic pr.1 pr.2 shapes vecs = true)
    (wits : Fin n × ℤ × ℤ → List (ℕ × ℕ × GGResQTwoCell n))
    (hcover : GGResQTwoShapeCoverage C ib shapes wits)
    (hsideOK : ∀ (s : Fin n × ℤ × ℤ) (_hs : s ∈ shapes)
      (w : ℕ × ℕ × GGResQTwoCell n), w ∈ wits s →
        ggResQTwoCellSideOK ib w.2.2)
    :
    GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8) GGResQTwoResidualCell ∨
      GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have hp2 : (3 : ℕ) ≠ 2 := by decide
  obtain ⟨-, -, -, hLx, -⟩ := hH.1.tableB_facts
  let g : Option Λ → (V ≃ₗ[ZMod 3] V) := fun o => ggLin (p := 3) ι (φ o)
  let xv : V := ι (Additive.ofMul ⟨x, hxBs⟩)
  have hx0 : xv ≠ 0 := by
    intro h0
    have hx1 : x ≠ 1 := hH.1.1.2.2.2.2.2.2.1.2.2.1
    have hxeq : (⟨x, hxBs⟩ : ↥Bs) = 1 :=
      Additive.ofMul.injective (ι.injective (h0.trans (map_zero ι).symm))
    exact hx1 (congrArg Subtype.val hxeq)
  have hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤ :=
    ggResI_span_top hFix hH ι hφ hAL hsel
  have hfixspan := ggResI_fixSpan hFix hH hxBs ι hφ hAL
  have hα2 : ∀ o : Option Λ, α o (h o) = 2 := by
    intro o
    cases o with
    | none =>
      have h1 := hK none none
      rw [hCK.1 none] at h1
      simpa using h1
    | some i =>
      have h1 := hL i i
      rw [hCL.1 i] at h1
      simpa using h1
  have hxfix : ∀ i : Λ, α (some i) xv = 0 := by
    intro i
    have hmem : φ (some i) ∈ ggAutomizer L Bs := by
      rw [hAL]; exact Subgroup.subset_closure ⟨i, rfl⟩
    exact ggResI_alpha_eq_zero hp2 (hφ (some i)) (hα2 (some i))
      ((ggLin_fix_iff ι (φ (some i)) _).mp (ggResI_automizer_fix hxBs hLx _ hmem))
  have hnf : ¬ GGResIForkShape b CL CK := fun hf =>
    hFork (ggResI_forkDatum hWL hCL hCK hφ hL hK hsel hAL hAK hf)
  have hAV : (ggAutomizer L Bs ⊔ ggAutomizer K Bs).map (ggLin (p := 3) ι) =
      Subgroup.closure (Set.range (fun o => ggLin (p := 3) ι (φ o))) :=
    ggResI_map_sup ι (ggResI_sup_eq_closure hAL hAK)
  let H : GGResIHyp 3 b ML CL MK CK g h α xv :=
    { hp2 := hp2, hWL := hWL, hCL := hCL, hWK := hWK, hCK := hCK, hconn := hdel, hnf := hnf,
      hg := hφ, hL := hL, hK := hK, hind := hsel, hspan := hspan, hxL := hxfix,
      hfix := hfixspan, hx0 := hx0 }
  refine ggResI_dispatch_elim H e hCe hib j₀ hj₀ pt hcyc shapes vecs hcand ?_
  intro ic e₁ e₂ hic hpair hmem hrow hcol
  have hbc : ib ≠ ic := Ne.symm hic
  let ι' : Fin (n + 1) → Option Λ := ggResIIIdx e
  let g' : Fin (n + 1) → (V ≃ₗ[ZMod 3] V) := ggResQTwoG ι φ e
  let h' : Fin (n + 1) → V := fun i => h (ι' i)
  let α' : Fin (n + 1) → Module.Dual (ZMod 3) V := ggResQTwoAlpha α e
  let u : ZMod 3 := α none (h (some b))
  let v : ZMod 3 := α (some b) (h none)
  have hne : ∀ j : Fin n, j ≠ ib → e j ≠ b := fun j hj he =>
    hj (e.injective (he.trans hib.symm))
  have hT : GGFTable (RingHom.id (ZMod 3))
      (ggStdTableI (Int.cast) C ib ic e₁ e₂ u v) h' 0 α' := by
    dsimp only [h', α', ι', g', ggResQTwoG, ggResQTwoAlpha, u, v]
    exact ggResI_stdTable_transport e hCe hib hbc hrow hcol (hCK.1 none) hL hK
  have hg' : ∀ k w, g' k w = w - α' k w • h' k := fun k w => hφ _ w
  have hα2' : ∀ k, α' k (h' k) = 2 := by
    intro k
    induction k using Fin.lastCases with
    | last =>
      have h1 := hT.1 (Fin.last n) (Fin.last n)
      simpa [α', h', ι', ggResQTwoAlpha, ggResIIIdx_last, ggStdTableI, ggStdEntryI] using h1
    | cast i =>
      have h1 := hL (e i) (e i)
      rw [hCL.1 (e i)] at h1
      simpa [α', h', ι', ggResQTwoAlpha, ggResIIIdx_castSucc] using h1
  have hrange_h : Set.range h' = Set.range h := by
    ext w
    constructor
    · rintro ⟨k, rfl⟩
      exact ⟨ι' k, rfl⟩
    · rintro ⟨o, rfl⟩
      obtain ⟨k, hk⟩ := ggResIIIdx_surjective e o
      exact ⟨k, by simp [h', ι', hk]⟩
  have hspan' : Submodule.span (ZMod 3) (Set.range h') = ⊤ := by
    rw [hrange_h, hspan]
  have hind' : LinearIndependent (ZMod 3) h' := hsel.comp (ggResIIdxEquiv e) (ggResIIdxEquiv e).injective
  have hfix' : ∀ w : V, (∀ i : Fin n, α' i.castSucc w = 0) →
      w ∈ Submodule.span (ZMod 3) {xv} := by
    intro w hw
    exact hfixspan w fun i => by simpa [α', ι', ggResQTwoAlpha] using hw (e.symm i)
  have hno : α none (ggResVec ι x hxBs) ≠ 0 :=
    ggResQTwo_alpha_none_x_ne_zero hH ha₀ hxBs hφ hrefl hAL hAK hsel hsome
  have hα : LinearIndependent (ZMod 3) α :=
    ggResQTwo_linearIndependent_roots hH hFix ha₀ hxBs hφ hrefl hAL hAK hsel hsome
  have hker' : ∀ w : V, (∀ i : Fin (n + 1), α' i w = 0) → w = 0 := by
    intro w hw
    have hwAll : ∀ o : Option Λ, α o w = 0 := by
      intro o
      obtain ⟨i, rfl⟩ := ggResIIIdx_surjective e o
      exact hw i
    have hwspan : w ∈ (Submodule.span (ZMod 3) (Set.range α)).dualCoannihilator := by
      rw [Submodule.mem_dualCoannihilator]
      intro f hf
      exact Submodule.span_induction (p := fun f _ => f w = 0)
        (fun f hf => by rcases hf with ⟨o, rfl⟩; exact hwAll o)
        (by simp) (fun f g _ _ ihf ihg => by simp [ihf, ihg])
        (fun c f _ ihf => by simp [ihf]) hf
    have hbot := ggResQTwo_ker_roots_eq_bot hH hFix hxBs hφ hAL hno
    rw [hbot] at hwspan
    simpa using hwspan
  have hrange_g : Set.range g' = Set.range (fun o : Option Λ => ggLin (p := 3) ι (φ o)) := by
    ext t
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨ι' i, rfl⟩
    · rintro ⟨o, rfl⟩
      obtain ⟨i, rfl⟩ := ggResIIIdx_surjective e o
      exact ⟨i, rfl⟩
  have hsideL' : GGResQTwoSidePremises g' α' xv (ggResQTwoLSide n) :=
    ggResQTwoSidePremises_L hH hxBs hWL hCL hφ hL hsel hAL hAK hFix ha₀ e hCe
  have hsideK' : GGResQTwoSidePremises g' α' (ggResVec ι y hyBs)
      (ggResQTwoKSide n ib) :=
    ggResQTwoSidePremises_K hH hyBs hWK hCK hφ hrefl hK hsel hα hAL hAK hFix e hib
  have hselcell := hcover (ic, e₁, e₂) hmem u v
  obtain ⟨w, hwmem, -, -, hwchk⟩ := ggResQTwoCellAt_exists hselcell
  have hsideW := hsideOK (ic, e₁, e₂) hmem w hwmem
  have hcell := ggResQTwoCell_exit (xv := xv) (yv := ggResVec ι y hyBs)
    hT hg' hspan' hind' hα2' hfix' hker' w.2.2 hsideW hsideL' hsideK' hwchk
  rcases hcell with hres | hweyl | htv | hstd | ho2b
  · left
    obtain ⟨tag, htag⟩ := hres
    exact ⟨Λ, inferInstance, inferInstance, b, ML, CL, MK, CK, V, inferInstance, inferInstance,
      ι, φ, h, α, hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩,
      ⟨fK, hfK⟩, hAL, hAK, hdel, hJ,
      ⟨n, C, ib, ic, e₁, e₂, e, tag, hCe, hib, hrow, hcol, hCK.1 none, htag⟩⟩
  · right
    have hweyl' : ZS.LinWeyl 3 (Subgroup.closure (Set.range (fun o : Option Λ =>
        ggLin (p := 3) ι (φ o)))) := by
      rwa [hrange_g] at hweyl
    rw [← hAV] at hweyl'
    exact ggRC_weylReflGroup_of_linWeyl ι _ hweyl'
  · exfalso
    obtain ⟨t, ht, htv⟩ := htv
    have ht' : t ∈ Subgroup.closure (Set.range (fun o : Option Λ =>
        ggLin (p := 3) ι (φ o))) := by
      rwa [hrange_g] at ht
    exact ggResI_false_of_transvection hH.2.2.2.1 ι (ggResI_sup_eq_closure hAL hAK) ht' htv
  · exfalso
    obtain ⟨M₀, hW₀, hC₀⟩ :=
      ggResI_std_back e hCe hib hbc hrow hcol (hCK.1 none) hstd.2
    exact (hStd (ggResI_stdDatum hφ hL hK hsel hAL hAK hstd.1 hW₀ hC₀)).elim
  · exfalso
    have hcellb := ggResI_o2b_back e hCe hib hrow hcol ho2b
    exact (ggResI_o2b_excl hFix G 3 B Bs x L D J y K hH
      ⟨Λ, inferInstance, inferInstance, b, ML, CL, MK, CK, V, inferInstance, inferInstance,
        ι, φ, h, α, hWL, hCL, hWK, hCK, htyp, hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩,
        ⟨fK, hfK⟩, hAL, hAK, hdel, hJ, hcellb⟩).elim

structure GGResQTwoFinite {Λ : Type} [Fintype Λ] [DecidableEq Λ] (b : Λ)
    (CL : Matrix Λ Λ ℤ) where
  n : ℕ
  C : Matrix (Fin n) (Fin n) ℤ
  e : Fin n ≃ Λ
  hCe : ∀ i j, CL (e i) (e j) = C i j
  ib : Fin n
  hib : e ib = b
  j₀ : Fin n
  hj₀ : j₀ ≠ ib
  pt : Fin n → Fin n → List (Fin n)
  hcyc : ∀ j₁ j₂ : Fin n, j₁ ≠ ib → j₂ ≠ ib → j₁ ≠ j₂ →
    ggCycleOK C ib j₁ j₂ (pt j₁ j₂)
  shapes : List (Fin n × ℤ × ℤ)
  vecs : List (Fin n × ℤ × ℤ × List ℕ)
  hcand : ∀ ic : Fin n, ic ≠ ib → ∀ pr ∈ ggCartanPairsNZ,
    ggCandB C ib ic pr.1 pr.2 shapes vecs = true
  wits : Fin n × ℤ × ℤ → List (ℕ × ℕ × GGResQTwoCell n)
  hcover : GGResQTwoShapeCoverage C ib shapes wits
  hsideOK : ∀ (s : Fin n × ℤ × ℤ) (_hs : s ∈ shapes)
    (w : ℕ × ℕ × GGResQTwoCell n), w ∈ wits s →
      ggResQTwoCellSideOK ib w.2.2
  hshapeNZ : ∀ s ∈ shapes, ((s.2.1 : ℤ) : ZMod 3) ≠ 0

theorem GGResQTwoFinite.exists_alpha_none_ne_zero
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] {b : Λ} {ML : CoxeterMatrix Λ}
    {CL : Matrix Λ Λ ℤ}
    {MK : CoxeterMatrix (Option {i : Λ // i ≠ b})}
    {CK : Matrix (Option {i : Λ // i ≠ b}) (Option {i : Λ // i ≠ b}) ℤ}
    {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    {g : Option Λ → V ≃ₗ[ZMod 3] V} {h : Option Λ → V}
    {α : Option Λ → Module.Dual (ZMod 3) V} {x : V}
    (D : GGResQTwoFinite b CL) (H : GGResIHyp 3 b ML CL MK CK g h α x) :
    ∃ j : Λ, α none (h (some j)) ≠ 0 := by
  obtain ⟨ic, e₁, e₂, hic, -, hmem, hrow, -⟩ :=
    ggResI_dispatch_shape H D.e D.hCe D.hib D.j₀ D.hj₀ D.pt D.hcyc D.shapes D.vecs D.hcand
  refine ⟨D.e ic, ?_⟩
  have hne : D.e ic ≠ b := fun he => hic (D.e.injective (he.trans D.hib.symm))
  have hrow' : CK none (some ⟨D.e ic, hne⟩) = e₁ := by
    simpa using hrow ic hne
  have hKrow := H.hK none (some ⟨D.e ic, hne⟩)
  rw [hrow'] at hKrow
  have hKrow' : α none (h (some (D.e ic))) = (e₁ : ZMod 3) := by
    simpa using hKrow
  rw [hKrow']
  exact D.hshapeNZ (ic, e₁, e₂) hmem

theorem ggResQTwo_actual
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    {y : G} {K : Subgroup G}
    (hH : GGResHyp 3 B Bs x L D J y K)
    (hLD : GGResLeviDatum 3 Bs L J K ggSelI (ggTypRankLt 8))
    (hFork : ¬ GGCoxeterForkDatum 3 Bs L K)
    (hStd : ¬ GGCoxeterStdDatum 3 Bs L K)
    (hE6 : ¬ GGE6DepPerpCfg 3 Bs L K)
    (hq : GGInnerDiagOnLabel GGLabQTwo 3 Bs L)
    (hFix : GGTBFixInput) (ha₀ : GGLNoncyclicInput)
    (hdata : ∀ {Λ : Type} [Fintype Λ] [DecidableEq Λ] (b : Λ) (ML : CoxeterMatrix Λ)
      (CL : Matrix Λ Λ ℤ), GGIsWeylMatrix ML → GGIntCartan ML CL →
      3 ≤ Nat.card Λ → Nat.card Λ < 8 → GGDeletedConnected ML b →
      Nonempty (GGResQTwoFinite b CL)) :
    GGResLeviDatumCell 3 Bs L J K ggSelI (ggTypRankLt 8) GGResQTwoResidualCell ∨
      GGWeylReflectionGroup 3 (ggAutomizer L Bs ⊔ ggAutomizer K Bs) := by
  classical
  have hxBs : x ∈ Bs := hH.1.tableB_facts.2.2.1
  have hyBs : y ∈ Bs := hH.1.2.1.1 (hH.2.2.2.2.1.1.2.1)
  obtain ⟨Λ, i1, i2, b, ML, CL, MK, CK, V, i3, i4, ι, φ, h, α, hWL, hCL, hWK, hCK, htyp,
    hφ, hrefl, hL, hK, hsel, ⟨fL, hfL⟩, ⟨fK, hfK⟩, hAL, hAK, hdel, hJ⟩ := hLD
  have hspan : Submodule.span (ZMod 3) (Set.range h) = ⊤ :=
    ggResI_span_top hFix hH ι hφ hAL hsel
  have hdim : Module.finrank (ZMod 3) V = Fintype.card Λ + 1 :=
    ggResI_finrank hspan hsel
  have h3 : 3 ≤ Nat.card Λ := by
    rw [Nat.card_eq_fintype_card]
    exact ggResI_three_le_card hH ι hdim
  have h8 : Nat.card Λ < 8 := htyp
  let D : GGResQTwoFinite b CL := Classical.choice (hdata b ML CL hWL hCL h3 h8 hdel)
  obtain ⟨-, -, -, hLx, -⟩ := hH.1.tableB_facts
  let g : Option Λ → (V ≃ₗ[ZMod 3] V) := fun o => ggLin (p := 3) ι (φ o)
  let xv : V := ggResVec ι x hxBs
  have hx0 : xv ≠ 0 := by
    intro h0
    have hx1 : x ≠ 1 := hH.1.1.2.2.2.2.2.2.1.2.2.1
    have hxeq : (⟨x, hxBs⟩ : ↥Bs) = 1 :=
      Additive.ofMul.injective (ι.injective (h0.trans (map_zero ι).symm))
    exact hx1 (congrArg Subtype.val hxeq)
  have hfixspan := ggResI_fixSpan hFix hH hxBs ι hφ hAL
  have hα2 : ∀ o : Option Λ, α o (h o) = 2 := by
    intro o
    cases o with
    | none =>
      have h1 := hK none none
      rw [hCK.1 none] at h1
      simpa using h1
    | some i =>
      have h1 := hL i i
      rw [hCL.1 i] at h1
      simpa using h1
  have hxfix : ∀ i : Λ, α (some i) xv = 0 := by
    intro i
    have hmem : φ (some i) ∈ ggAutomizer L Bs := by
      rw [hAL]; exact Subgroup.subset_closure ⟨i, rfl⟩
    exact ggResI_alpha_eq_zero (by decide : (3 : ℕ) ≠ 2) (hφ (some i)) (hα2 (some i))
      ((ggLin_fix_iff ι (φ (some i)) _).mp (ggResI_automizer_fix hxBs hLx _ hmem))
  have hnf : ¬ GGResIForkShape b CL CK := fun hf =>
    hFork (ggResI_forkDatum hWL hCL hCK hφ hL hK hsel hAL hAK hf)
  let H : GGResIHyp 3 b ML CL MK CK g h α xv :=
    { hp2 := by decide, hWL := hWL, hCL := hCL, hWK := hWK, hCK := hCK, hconn := hdel,
      hnf := hnf, hg := hφ, hL := hL, hK := hK, hind := hsel, hspan := hspan, hxL := hxfix,
      hfix := hfixspan, hx0 := hx0 }
  have hsome : ∃ j : Λ, α none (h (some j)) ≠ 0 :=
    D.exists_alpha_none_ne_zero H
  exact ggResQTwo_actual_core hH hxBs hyBs hWL hCL hWK hCK htyp hφ hrefl hL hK hsel hsome
    fL hfL fK hfK hAL hAK hdel hJ hFork hStd hE6 hq hFix ha₀
    D.e D.hCe D.hib D.j₀ D.hj₀ D.pt D.hcyc D.shapes D.vecs D.hcand D.wits D.hcover D.hsideOK


end CFSG.StandardType

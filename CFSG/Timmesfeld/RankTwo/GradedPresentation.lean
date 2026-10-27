module

public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Volume.Basic
public import Mathlib.GroupTheory.PresentedGroup
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.Inclusion.Extension.Core.Core
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Hypotheses
public import Mathlib.Tactic.Inclusion.Extension.IntervalDyadicReal.Rational
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.Timmesfeld.GradedPresentation

open scoped commutatorElement

variable {ι : Type*} {F : ι → Type*} [∀ γ, AddGroup (F γ)]

@[expose] def rels (cm : ∀ α (_ : F α) β (_ : F β), FreeGroup (Σ γ, F γ)) :
    Set (FreeGroup (Σ γ, F γ)) :=
  {r | ∃ (γ : ι) (c d : F γ), r = FreeGroup.of (⟨γ, c + d⟩ : Σ γ, F γ) *
    (FreeGroup.of (⟨γ, c⟩ : Σ γ, F γ) * FreeGroup.of (⟨γ, d⟩ : Σ γ, F γ))⁻¹} ∪
  {r | ∃ (α : ι) (s : F α) (β : ι) (t : F β), r = ⁅FreeGroup.of (⟨α, s⟩ : Σ γ, F γ),
    FreeGroup.of (⟨β, t⟩ : Σ γ, F γ)⁆ * (cm α s β t)⁻¹}

variable {cm : ∀ α (_ : F α) β (_ : F β), FreeGroup (Σ γ, F γ)}

section Relations

variable {H : Type*} [Group H] {f : (Σ γ, F γ) → H}

theorem map_add (hf : ∀ r ∈ rels cm, FreeGroup.lift f r = 1) (γ : ι) (c d : F γ) :
    f ⟨γ, c + d⟩ = f ⟨γ, c⟩ * f ⟨γ, d⟩ := by
  have := hf _ (Or.inl ⟨γ, c, d, rfl⟩)
  simp only [map_mul, map_inv, FreeGroup.lift_apply_of] at this
  exact mul_inv_eq_one.1 this

theorem map_zero (hf : ∀ r ∈ rels cm, FreeGroup.lift f r = 1) (γ : ι) : f ⟨γ, 0⟩ = 1 := by
  have := map_add hf γ 0 0
  rw [add_zero] at this
  exact left_eq_mul.1 this

theorem map_neg (hf : ∀ r ∈ rels cm, FreeGroup.lift f r = 1) (γ : ι) (c : F γ) :
    f ⟨γ, -c⟩ = (f ⟨γ, c⟩)⁻¹ := by
  have := map_add hf γ c (-c)
  rw [add_neg_cancel, map_zero hf] at this
  exact (inv_eq_of_mul_eq_one_right this.symm).symm

theorem map_commutator (hf : ∀ r ∈ rels cm, FreeGroup.lift f r = 1) (α : ι) (s : F α) (β : ι)
    (t : F β) : ⁅f ⟨α, s⟩, f ⟨β, t⟩⁆ = FreeGroup.lift f (cm α s β t) := by
  have := hf _ (Or.inr ⟨α, s, β, t, rfl⟩)
  simp only [map_mul, map_inv, map_commutatorElement, FreeGroup.lift_apply_of] at this
  exact mul_inv_eq_one.1 this

end Relations

variable (ht : ι → ℕ)

abbrev above (m : ℕ) : Subgroup (FreeGroup (Σ γ, F γ)) :=
  Subgroup.closure (FreeGroup.of '' {g : Σ γ, F γ | m < ht g.1})

section Filtration

variable {cm : ∀ α (_ : F α) β (_ : F β), FreeGroup (Σ γ, F γ)} {ht}
  (hgr : ∀ α s β t, cm α s β t ∈ above ht (max (ht α) (ht β)))

abbrev gen (cm : ∀ α (_ : F α) β (_ : F β), FreeGroup (Σ γ, F γ)) (g : Σ γ, F γ) :
    PresentedGroup (rels cm) :=
  PresentedGroup.of g

abbrev N (cm : ∀ α (_ : F α) β (_ : F β), FreeGroup (Σ γ, F γ)) (ht : ι → ℕ) (h : ℕ) :
    Subgroup (PresentedGroup (rels cm)) :=
  Subgroup.closure (gen cm '' {g | h ≤ ht g.1})

theorem relsP : ∀ r ∈ rels cm, FreeGroup.lift (gen cm) r = 1 := by
  intro r hr
  have : FreeGroup.lift (gen cm) r = PresentedGroup.mk (rels cm) r := by
    congr 1
    ext g
    simp [gen, PresentedGroup.of]
  rw [this]
  exact PresentedGroup.one_of_mem hr

theorem lift_mem_N {m : ℕ} {w : FreeGroup (Σ γ, F γ)} (hw : w ∈ above ht m) :
    FreeGroup.lift (gen cm) w ∈ N cm ht (m + 1) := by
  have : (above ht m).map (FreeGroup.lift (gen cm)) ≤ N cm ht (m + 1) := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨g, hg, rfl⟩, rfl⟩
    exact Subgroup.subset_closure ⟨g, Nat.succ_le_of_lt hg, by simp [gen]⟩
  exact this ⟨w, hw, rfl⟩

theorem N_succ_le (h : ℕ) : N cm ht (h + 1) ≤ N cm ht h :=
  Subgroup.closure_mono fun _ ⟨g, hg, e⟩ => ⟨g, le_of_lt (Nat.lt_of_succ_le hg), e⟩

include hgr in
theorem commutator_mem {h : ℕ} {a b : Σ γ, F γ} (ha : h ≤ ht a.1) (hb : h ≤ ht b.1) :
    ⁅gen cm a, gen cm b⁆ ∈ N cm ht (h + 1) := by
  obtain ⟨α, s⟩ := a
  obtain ⟨β, t⟩ := b
  rw [map_commutator relsP α s β t]
  refine Subgroup.closure_mono ?_ (lift_mem_N (cm := cm) (hgr α s β t))
  rintro _ ⟨g, hg, rfl⟩
  exact ⟨g, le_trans (Nat.succ_le_succ (le_trans ha (le_max_left _ _))) hg, rfl⟩

include hgr in
theorem conj_mem {h : ℕ} {a : Σ γ, F γ} (ha : h ≤ ht a.1) {n : PresentedGroup (rels cm)}
    (hn : n ∈ N cm ht (h + 1)) : gen cm a * n * (gen cm a)⁻¹ ∈ N cm ht (h + 1) := by
  have hle : (N cm ht (h + 1)).map (MulAut.conj (gen cm a)).toMonoidHom ≤ N cm ht (h + 1) := by
    rw [MonoidHom.map_closure, Subgroup.closure_le]
    rintro _ ⟨_, ⟨b, hb, rfl⟩, rfl⟩
    change gen cm a * gen cm b * (gen cm a)⁻¹ ∈ N cm ht (h + 1)
    have hc := commutator_mem hgr ha (le_trans (Nat.le_succ h) hb)
    have e : gen cm a * gen cm b * (gen cm a)⁻¹ = ⁅gen cm a, gen cm b⁆ * gen cm b := by
      rw [commutatorElement_def]; group
    rw [e]
    exact (N cm ht (h + 1)).mul_mem hc (Subgroup.subset_closure ⟨b, hb, rfl⟩)
  exact hle ⟨n, hn, rfl⟩

include hgr in
theorem le_normalizer (h : ℕ) : N cm ht h ≤ Subgroup.normalizer (N cm ht (h + 1) : Set _) := by
  rw [Subgroup.closure_le]
  rintro _ ⟨a, ha, rfl⟩
  rw [SetLike.mem_coe, Subgroup.mem_normalizer_iff]
  intro n
  refine ⟨conj_mem hgr ha, fun hn => ?_⟩
  have hinv : (gen cm a)⁻¹ = gen cm ⟨a.1, -a.2⟩ := (map_neg relsP a.1 a.2).symm
  have := conj_mem hgr (a := ⟨a.1, -a.2⟩) ha hn
  rw [← hinv, inv_inv] at this
  simpa [mul_assoc] using this

end Filtration

section Card

variable [Fintype ι] [DecidableEq ι] [∀ γ, Fintype (F γ)]
  {cm : ∀ α (_ : F α) β (_ : F β), FreeGroup (Σ γ, F γ)} {ht}
  (hgr : ∀ α s β t, cm α s β t ∈ above ht (max (ht α) (ht β)))

omit [Fintype ι] [DecidableEq ι] [∀ γ, Fintype (F γ)] in
include hgr in
theorem normal_subgroupOf (h : ℕ) : ((N cm ht (h + 1)).subgroupOf (N cm ht h)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer (N_succ_le h)).2 (le_normalizer hgr h)

omit [DecidableEq ι] in
include hgr in
theorem card_quotient_le (h : ℕ) :
    Finite (↥(N cm ht h) ⧸ (N cm ht (h + 1)).subgroupOf (N cm ht h)) ∧
      Nat.card (↥(N cm ht h) ⧸ (N cm ht (h + 1)).subgroupOf (N cm ht h)) ≤
        ∏ γ ∈ Finset.univ.filter (fun γ => ht γ = h), Nat.card (F γ) := by
  have := normal_subgroupOf hgr h
  set Nh := N cm ht h
  set Nh1 := (N cm ht (h + 1)).subgroupOf Nh
  set mk := QuotientGroup.mk' Nh1
  have memN : ∀ g : Σ γ, F γ, h ≤ ht g.1 → gen cm g ∈ Nh := fun g hg =>
    Subgroup.subset_closure ⟨g, hg, rfl⟩
  let ψ : ∀ γ : {γ // ht γ = h}, Multiplicative (F γ.1) →* _ ⧸ Nh1 := fun γ =>
    { toFun := fun c => mk ⟨gen cm ⟨γ.1, c.toAdd⟩, memN _ γ.2.ge⟩
      map_one' := by
        have : gen cm ⟨γ.1, (1 : Multiplicative (F γ.1)).toAdd⟩ = 1 := map_zero relsP γ.1
        simp only [this]
        rfl
      map_mul' := fun c d => by
        rw [← map_mul]
        congr 1
        exact Subtype.ext (map_add relsP γ.1 c.toAdd d.toAdd) }
  have hψ : ∀ (γ : {γ // ht γ = h}) c, ψ γ c = mk ⟨gen cm ⟨γ.1, c.toAdd⟩, memN _ γ.2.ge⟩ :=
    fun _ _ => rfl
  have hcomm_mk : ∀ a b : Σ γ, F γ, ∀ (ha : h ≤ ht a.1) (hb : h ≤ ht b.1),
      Commute (mk ⟨gen cm a, memN a ha⟩) (mk ⟨gen cm b, memN b hb⟩) := by
    intro a b ha hb
    have hc : ⁅(⟨gen cm a, memN a ha⟩ : Nh), ⟨gen cm b, memN b hb⟩⁆ ∈ Nh1 := by
      rw [Subgroup.mem_subgroupOf]
      exact commutator_mem hgr ha hb
    have : mk ⁅(⟨gen cm a, memN a ha⟩ : Nh), ⟨gen cm b, memN b hb⟩⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).2 hc
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at this
    exact this
  have hcomm : Pairwise fun i j => ∀ (x : Multiplicative (F i.1)) (y : Multiplicative (F j.1)),
      Commute (ψ i x) (ψ j y) := fun i j _ x y => by
    rw [hψ, hψ]
    exact hcomm_mk _ _ i.2.ge j.2.ge
  set Ψ := MonoidHom.noncommPiCoprod ψ hcomm
  have hsurj : Function.Surjective Ψ := by
    rw [← MonoidHom.range_eq_top, MonoidHom.noncommPiCoprod_range, eq_top_iff]
    have htop : (⊤ : Subgroup Nh) =
        Subgroup.closure (((↑) : Nh → PresentedGroup (rels cm)) ⁻¹' (gen cm '' {g | h ≤ ht g.1})) :=
      Subgroup.closure_closure_coe_preimage.symm
    rintro q -
    obtain ⟨n, rfl⟩ := QuotientGroup.mk'_surjective Nh1 q
    have hn : n ∈ Subgroup.closure
        (((↑) : Nh → PresentedGroup (rels cm)) ⁻¹' (gen cm '' {g | h ≤ ht g.1})) :=
      htop ▸ Subgroup.mem_top n
    have hmap : (Subgroup.closure (((↑) : Nh → PresentedGroup (rels cm)) ⁻¹'
        (gen cm '' {g | h ≤ ht g.1}))).map mk ≤ ⨆ i, (ψ i).range := by
      rw [MonoidHom.map_closure, Subgroup.closure_le]
      rintro _ ⟨⟨n', hn'N⟩, ⟨g, hg, hgn⟩, rfl⟩
      simp only at hgn
      subst hgn
      rcases Nat.lt_or_eq_of_le (show h ≤ ht g.1 from hg) with hlt | heq
      · have : mk ⟨gen cm g, hn'N⟩ = 1 := by
          rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
          exact Subgroup.subset_closure ⟨g, Nat.succ_le_of_lt hlt, rfl⟩
        rw [SetLike.mem_coe, this]
        exact one_mem _
      · refine Subgroup.mem_iSup_of_mem ⟨g.1, heq.symm⟩ ⟨Multiplicative.ofAdd g.2, ?_⟩
        rw [hψ]
        rfl
    exact hmap ⟨n, hn, rfl⟩
  have hfin : Finite (∀ γ : {γ // ht γ = h}, Multiplicative (F γ.1)) := inferInstance
  refine ⟨Finite.of_surjective Ψ hsurj, ?_⟩
  calc Nat.card (_ ⧸ Nh1) ≤ Nat.card (∀ γ : {γ // ht γ = h}, Multiplicative (F γ.1)) :=
        Nat.card_le_card_of_surjective Ψ hsurj
    _ = ∏ γ : {γ // ht γ = h}, Nat.card (F γ.1) := by
        rw [Nat.card_pi]
        rfl
    _ = ∏ γ ∈ Finset.univ.filter (fun γ => ht γ = h), Nat.card (F γ) :=
        (Finset.prod_subtype (Finset.univ.filter (fun γ => ht γ = h)) (fun γ => by simp)
          (fun γ => Nat.card (F γ))).symm

include hgr in
theorem finite_and_card_le (h : ℕ) :
    Finite (N cm ht h) ∧
      Nat.card (N cm ht h) ≤ ∏ γ ∈ Finset.univ.filter (fun γ => h ≤ ht γ), Nat.card (F γ) := by
  set H₀ := Finset.univ.sup ht
  suffices key : ∀ k h, H₀ + 1 ≤ h + k → Finite (N cm ht h) ∧
      Nat.card (N cm ht h) ≤ ∏ γ ∈ Finset.univ.filter (fun γ => h ≤ ht γ), Nat.card (F γ) from
    key (H₀ + 1) h (by omega)
  intro k
  induction k with
  | zero =>
    intro h hh
    have hbot : N cm ht h = ⊥ := by
      rw [Subgroup.closure_eq_bot_iff]
      rintro _ ⟨g, hg, rfl⟩
      exfalso
      have := Finset.le_sup (f := ht) (Finset.mem_univ g.1)
      change h ≤ ht g.1 at hg
      omega
    rw [hbot]
    refine ⟨inferInstance, ?_⟩
    rw [Subgroup.card_bot]
    exact Nat.one_le_iff_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun γ _ => Nat.card_pos.ne')
  | succ k ih =>
    intro h hh
    obtain ⟨hfin1, hcard1⟩ := ih (h + 1) (by omega)
    obtain ⟨hfinQ, hcardQ⟩ := card_quotient_le hgr h
    have e := Subgroup.subgroupOfEquivOfLe (N_succ_le (cm := cm) (ht := ht) h)
    have : Finite ((N cm ht (h + 1)).subgroupOf (N cm ht h)) := Finite.of_equiv _ e.symm.toEquiv
    refine ⟨Finite.of_subgroup_quotient ((N cm ht (h + 1)).subgroupOf (N cm ht h)), ?_⟩
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup
      ((N cm ht (h + 1)).subgroupOf (N cm ht h)), Nat.card_congr e.toEquiv]
    have hsplit : Finset.univ.filter (fun γ => h ≤ ht γ) =
        Finset.univ.filter (fun γ => ht γ = h) ∪ Finset.univ.filter (fun γ => h + 1 ≤ ht γ) := by
      ext γ
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
      omega
    have hdisj : Disjoint (Finset.univ.filter (fun γ => ht γ = h))
        (Finset.univ.filter (fun γ => h + 1 ≤ ht γ)) := by
      rw [Finset.disjoint_filter]
      intro γ _ h1 h2
      omega
    rw [hsplit, Finset.prod_union hdisj]
    exact Nat.mul_le_mul hcardQ hcard1

include hgr in
theorem card_le : Finite (PresentedGroup (rels cm)) ∧
    Nat.card (PresentedGroup (rels cm)) ≤ ∏ γ, Nat.card (F γ) := by
  have hset : gen cm '' {g : Σ γ, F γ | 0 ≤ ht g.1} =
      Set.range (PresentedGroup.of (rels := rels cm)) := by
    ext p
    constructor
    · rintro ⟨g, -, rfl⟩
      exact ⟨g, rfl⟩
    · rintro ⟨g, rfl⟩
      exact ⟨g, Nat.zero_le _, rfl⟩
  have htop : N cm ht 0 = ⊤ := by
    show Subgroup.closure (gen cm '' {g | 0 ≤ ht g.1}) = ⊤
    rw [hset]
    exact PresentedGroup.closure_range_of _
  obtain ⟨hfin, hcard⟩ := finite_and_card_le hgr 0
  have hf : Finset.univ.filter (fun γ => 0 ≤ ht γ) = Finset.univ := by
    ext γ
    simp
  rw [hf] at hcard
  have e := (MulEquiv.subgroupCongr htop).trans Subgroup.topEquiv
  exact ⟨Finite.of_equiv _ e.toEquiv, (Nat.card_congr e.toEquiv).symm.le.trans hcard⟩

include hgr in
theorem exists_hom {K G : Type*} [Group K] [Group G] (x : (Σ γ, F γ) → K)
    (φ : (Σ γ, F γ) → G) (hx : ∀ r ∈ rels cm, FreeGroup.lift x r = 1)
    (hφ : ∀ r ∈ rels cm, FreeGroup.lift φ r = 1) (L : List ι)
    (hinj : Function.Injective fun c : (∀ γ, F γ) => (L.map fun γ => x ⟨γ, c γ⟩).prod) :
    ∃ θ : Subgroup.closure (Set.range x) →* G,
      ∀ g, θ ⟨x g, Subgroup.subset_closure ⟨g, rfl⟩⟩ = φ g := by
  obtain ⟨hfinP, hcardP⟩ := card_le hgr
  set πK := PresentedGroup.toGroup hx
  have hrange : πK.range = Subgroup.closure (Set.range x) := by
    rw [MonoidHom.range_eq_map, ← PresentedGroup.closure_range_of, MonoidHom.map_closure,
      ← Set.range_comp]
    congr 1
    ext k
    simp [πK, PresentedGroup.toGroup.of]
  have hprod : ∀ c : (∀ γ, F γ), (L.map fun γ => x ⟨γ, c γ⟩).prod ∈ πK.range := by
    intro c
    refine πK.range.list_prod_mem fun y hy => ?_
    obtain ⟨γ, -, rfl⟩ := List.mem_map.1 hy
    rw [hrange]
    exact Subgroup.subset_closure ⟨_, rfl⟩
  have : Finite πK.range := Finite.of_surjective _ πK.rangeRestrict_surjective
  have hle : Nat.card (∀ γ, F γ) ≤ Nat.card πK.range :=
    Nat.card_le_card_of_injective (fun c => ⟨_, hprod c⟩) fun c d e =>
      hinj (congrArg Subtype.val e)
  rw [Nat.card_pi] at hle
  have hbij : Function.Bijective πK.rangeRestrict :=
    πK.rangeRestrict_surjective.bijective_of_nat_card_le (hcardP.trans hle)
  set e := MulEquiv.ofBijective πK.rangeRestrict hbij
  refine ⟨(PresentedGroup.toGroup hφ).comp
    (e.symm.toMonoidHom.comp (MulEquiv.subgroupCongr hrange.symm).toMonoidHom), fun g => ?_⟩
  have he : e (PresentedGroup.of g) = ⟨x g, ⟨PresentedGroup.of g, PresentedGroup.toGroup.of hx⟩⟩ :=
    Subtype.ext (PresentedGroup.toGroup.of hx)
  simp only [MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom]
  have : (MulEquiv.subgroupCongr hrange.symm) ⟨x g, Subgroup.subset_closure ⟨g, rfl⟩⟩ =
      ⟨x g, ⟨PresentedGroup.of g, PresentedGroup.toGroup.of hx⟩⟩ := rfl
  rw [this, ← he, MulEquiv.symm_apply_apply, PresentedGroup.toGroup.of]

end Card

end CFSG.Timmesfeld.GradedPresentation

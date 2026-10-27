module

public import CFSG.RankThree.PartOne.KC.UnitaryPlaneLines
public import CFSG.RankThree.PartOne.KC.UnitaryPlaneOrthogonal
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.RankThree.PartOne.KCUnitaryPlane

open CFSG.LocalAnalysis.ComponentInitial

variable {K : Type*} [Field K] {σ : K →+* K} {V : Type*} [AddCommGroup V] [Module K V]
  {B : V →ₛₗ[σ] V →ₗ[K] K} {P : Type*} [Group P] [Fintype P] {p : ℕ}
  (ρ : P →* LinearMap.GeneralLinearGroup K V)

@[expose] noncomputable def projTop : Module.End K V := avgOp ρ ⊤

@[expose] noncomputable def projLine (L : Subgroup P) : Module.End K V := avgOp ρ L - avgOp ρ ⊤

@[expose] def lineSpace (B : V →ₛₗ[σ] V →ₗ[K] K) (L : Subgroup P) : Submodule K V :=
  fixedSpace ρ L ⊓ (fixedSpace ρ ⊤).orthogonalBilin B

section Facts

variable (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
include hP hpK

omit [Fintype P] hP in
theorem natCard_cast_line {L : Subgroup P} (hL : Nat.card L = p) : ((Nat.card L : ℕ) : K) ≠ 0 := by
  rw [hL]
  exact hpK

omit [Fintype P] in
theorem natCard_cast_top : ((Nat.card (⊤ : Subgroup P) : ℕ) : K) ≠ 0 := by
  rw [Subgroup.card_top, hP.card]
  push_cast
  exact pow_ne_zero 2 hpK

omit hP in
theorem avgOp_mul_top {L : Subgroup P} (hL : Nat.card L = p) :
    avgOp ρ L * avgOp ρ ⊤ = avgOp ρ ⊤ :=
  avgOp_mul_avgOp_of_le' ρ le_top (natCard_cast_line hpK hL)

omit hP in
theorem top_mul_avgOp {L : Subgroup P} (hL : Nat.card L = p) :
    avgOp ρ ⊤ * avgOp ρ L = avgOp ρ ⊤ :=
  avgOp_mul_avgOp_of_le ρ le_top (natCard_cast_line hpK hL)

theorem avgOp_top_mul_self : avgOp ρ ⊤ * avgOp ρ ⊤ = avgOp ρ ⊤ :=
  avgOp_mul_avgOp ρ (natCard_cast_top hP hpK)

theorem avgOp_mul_avgOp_of_ne {L M : Subgroup P} (hL : Nat.card L = p) (hM : Nat.card M = p)
    (hne : L ≠ M) : avgOp ρ L * avgOp ρ M = avgOp ρ ⊤ := by
  unfold avgOp
  rw [smul_mul_smul_comm, hP.sumOp_mul_sumOp_of_ne ρ hL hM hne]
  congr 1
  rw [hL, hM, Subgroup.card_top, hP.card]
  have : (p : K) ≠ 0 := hpK
  push_cast
  field_simp

theorem sum_lines_avgOp : ∑ L ∈ lines p P, avgOp ρ L = 1 + (p : K) • avgOp ρ ⊤ := by
  have h1 : ∀ L ∈ lines p P, avgOp ρ L = (p : K)⁻¹ • sumOp ρ L := fun L hL => by
    unfold avgOp
    rw [mem_lines.mp hL]
  rw [Finset.sum_congr rfl h1, ← Finset.smul_sum, hP.sum_lines_sumOp ρ, smul_add, smul_smul,
    inv_mul_cancel₀ hpK, one_smul]
  congr 1
  unfold avgOp
  rw [smul_smul, Subgroup.card_top, hP.card]
  congr 1
  push_cast
  field_simp

theorem projLine_mul_projLine_of_ne {L M : Subgroup P} (hL : Nat.card L = p) (hM : Nat.card M = p)
    (hne : L ≠ M) : projLine ρ L * projLine ρ M = 0 := by
  unfold projLine
  rw [sub_mul, mul_sub, mul_sub, avgOp_mul_avgOp_of_ne ρ hP hpK hL hM hne,
    avgOp_mul_top ρ hpK hL, top_mul_avgOp ρ hpK hM, avgOp_top_mul_self ρ hP hpK]
  abel

theorem projLine_mul_self {L : Subgroup P} (hL : Nat.card L = p) :
    projLine ρ L * projLine ρ L = projLine ρ L := by
  unfold projLine
  rw [sub_mul, mul_sub, mul_sub, avgOp_mul_avgOp ρ (natCard_cast_line hpK hL),
    avgOp_mul_top ρ hpK hL, top_mul_avgOp ρ hpK hL, avgOp_top_mul_self ρ hP hpK]
  abel

theorem projLine_mul_projTop {L : Subgroup P} (hL : Nat.card L = p) :
    projLine ρ L * projTop ρ = 0 := by
  unfold projLine projTop
  rw [sub_mul, avgOp_mul_top ρ hpK hL, avgOp_top_mul_self ρ hP hpK, sub_self]

theorem projTop_mul_projLine {L : Subgroup P} (hL : Nat.card L = p) :
    projTop ρ * projLine ρ L = 0 := by
  unfold projLine projTop
  rw [mul_sub, top_mul_avgOp ρ hpK hL, avgOp_top_mul_self ρ hP hpK, sub_self]

theorem projTop_mul_self : projTop ρ * projTop ρ = projTop ρ := avgOp_top_mul_self ρ hP hpK

theorem sum_projLine_add_projTop : ∑ L ∈ lines p P, projLine ρ L + projTop ρ = 1 := by
  unfold projLine projTop
  rw [Finset.sum_sub_distrib, sum_lines_avgOp ρ hP hpK, Finset.sum_const, hP.card_lines,
    Nat.cast_smul_eq_nsmul K p, add_smul, one_smul]
  abel

end Facts


section Geometry

theorem isSelfAdj_projTop (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) : IsSelfAdj B (projTop ρ) :=
  avgOp_selfAdj ρ hρ ⊤

theorem isSelfAdj_projLine (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (L : Subgroup P) :
    IsSelfAdj B (projLine ρ L) := by
  intro v w
  unfold projLine
  simp only [LinearMap.sub_apply, map_sub, avgOp_selfAdj ρ hρ L v w, avgOp_selfAdj ρ hρ ⊤ v w]

theorem range_projTop (hP : IsPlane p P) (hpK : (p : K) ≠ 0) :
    LinearMap.range (projTop ρ) = fixedSpace ρ ⊤ :=
  range_avgOp ρ (natCard_cast_top hP hpK)

theorem range_projLine (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {L : Subgroup P} (hL : Nat.card L = p) :
    LinearMap.range (projLine ρ L) = lineSpace ρ B L := by
  ext v
  constructor
  · rintro ⟨u, rfl⟩
    refine ⟨?_, ?_⟩
    · intro y hy
      have h1 : act ρ y * projLine ρ L = projLine ρ L := by
        unfold projLine
        rw [mul_sub, act_mul_avgOp ρ hy, act_mul_avgOp ρ (Subgroup.mem_top y)]
      simpa using congrArg (fun f : Module.End K V => f u) h1
    · intro w hw
      have hw' : projTop ρ w = w :=
        avgOp_apply_of_mem_fixedSpace ρ (natCard_cast_top hP hpK) hw
      have h0 : projTop ρ (projLine ρ L u) = 0 := by
        simpa using congrArg (fun f : Module.End K V => f u) (projTop_mul_projLine ρ hP hpK hL)
      rw [← hw', isSelfAdj_projTop ρ hρ w, h0, map_zero]
  · rintro ⟨hv1, hv2⟩
    have h1 : avgOp ρ L v = v :=
      avgOp_apply_of_mem_fixedSpace ρ (natCard_cast_line hpK hL) hv1
    have h2 : projTop ρ v = 0 := by
      apply hBl
      intro w
      rw [isSelfAdj_projTop ρ hρ v w]
      have hz : B (projTop ρ w) v = 0 := hv2 _ (by
        rw [← range_projTop ρ hP hpK]
        exact LinearMap.mem_range_self _ w)
      rw [← (LinearMap.isSymm_def.mp hB) (projTop ρ w) v, hz, map_zero]
    refine ⟨v, ?_⟩
    unfold projLine
    rw [LinearMap.sub_apply, h1]
    change v - projTop ρ v = v
    rw [h2, sub_zero]

omit [Fintype P] in
theorem orth_top_line (hB : B.IsSymm) {L : Subgroup P} {u w : V} (hu : u ∈ fixedSpace ρ ⊤)
    (hw : w ∈ lineSpace ρ B L) : B u w = 0 ∧ B w u = 0 := by
  have h1 : B u w = 0 := hw.2 u hu
  exact ⟨h1, by rw [← (LinearMap.isSymm_def.mp hB) u w, h1, map_zero]⟩

theorem orth_line_line (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {L M : Subgroup P} (hL : Nat.card L = p) (hM : Nat.card M = p) (hne : L ≠ M) {u w : V}
    (hu : u ∈ lineSpace ρ B L) (hw : w ∈ lineSpace ρ B M) : B u w = 0 := by
  rw [← range_projLine ρ hP hpK hρ hB hBl hL] at hu
  rw [← range_projLine ρ hP hpK hρ hB hBl hM] at hw
  obtain ⟨u', rfl⟩ := hu
  obtain ⟨w', rfl⟩ := hw
  rw [isSelfAdj_projLine ρ hρ L u' (projLine ρ M w')]
  have : projLine ρ L (projLine ρ M w') = 0 := by
    simpa using congrArg (fun f : Module.End K V => f w')
      (projLine_mul_projLine_of_ne ρ hP hpK hL hM hne)
  rw [this, map_zero]

theorem sup_eq_top (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft) :
    fixedSpace ρ ⊤ ⊔ ⨆ L ∈ lines p P, lineSpace ρ B L = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have h := congrArg (fun f : Module.End K V => f v) (sum_projLine_add_projTop ρ hP hpK)
  simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.one_apply] at h
  rw [← h, add_comm]
  refine Submodule.add_mem_sup ?_ ?_
  · exact avgOp_apply_mem_fixedSpace ρ ⊤ v
  · refine Submodule.sum_mem _ fun L hL => ?_
    refine Submodule.mem_iSup_of_mem L (Submodule.mem_iSup_of_mem hL ?_)
    rw [← range_projLine ρ hP hpK hρ hB hBl (mem_lines.mp hL)]
    exact LinearMap.mem_range_self _ v

theorem separatingLeft_fixedTop (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft) :
    (B.domRestrict₁₂ (fixedSpace ρ ⊤) (fixedSpace ρ ⊤)).SeparatingLeft := by
  rw [← range_projTop ρ hP hpK]
  exact separatingLeft_range hB hBl (isSelfAdj_projTop ρ hρ) (projTop_mul_self ρ hP hpK)

theorem separatingLeft_lineSpace (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {L : Subgroup P} (hL : Nat.card L = p) :
    (B.domRestrict₁₂ (lineSpace ρ B L) (lineSpace ρ B L)).SeparatingLeft := by
  rw [← range_projLine ρ hP hpK hρ hB hBl hL]
  exact separatingLeft_range hB hBl (isSelfAdj_projLine ρ hρ L) (projLine_mul_self ρ hP hpK hL)

@[expose] def stabSubgroup (v : V) : Subgroup P where
  carrier := {y | act ρ y v = v}
  mul_mem' := fun {a b} ha hb => by
    show act ρ (a * b) v = v
    rw [act_mul, Module.End.mul_apply, show act ρ b v = v from hb, show act ρ a v = v from ha]
  one_mem' := by
    show act ρ 1 v = v
    rw [act_one]
    rfl
  inv_mem' := fun {a} ha => by
    show act ρ a⁻¹ v = v
    have h : act ρ a v = v := ha
    conv_lhs => rw [← h]
    have := act_inv_apply ρ a⁻¹ v
    rwa [inv_inv] at this

omit [Fintype P] in
theorem mem_stabSubgroup {v : V} {y : P} : y ∈ stabSubgroup ρ v ↔ act ρ y v = v := Iff.rfl

theorem fixedSpace_of_apply_eq (hP : IsPlane p P) {L : Subgroup P} (hL : Nat.card L = p) {x : P}
    (hxL : x ∈ L) (hx1 : x ≠ 1) {v : V} (hv : act ρ x v = v) : v ∈ fixedSpace ρ L := by
  intro y hy
  have h1 : Subgroup.zpowers x = L := hP.zpowers_eq hL hxL hx1
  have h2 : Subgroup.zpowers x ≤ stabSubgroup ρ v := by
    rw [Subgroup.zpowers_le]
    exact hv
  have : y ∈ stabSubgroup ρ v := h2 (h1 ▸ hy)
  exact this

theorem ker_act_sub_one_eq (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    {L : Subgroup P} (hL : Nat.card L = p) {x : P} (hxL : x ∈ L) (hx1 : x ≠ 1) :
    LinearMap.ker (act ρ x - 1) = fixedSpace ρ ⊤ ⊔ lineSpace ρ B L := by
  apply le_antisymm
  · intro v hv
    have hv' : act ρ x v = v := by
      have := LinearMap.mem_ker.mp hv
      simpa [sub_eq_zero] using this
    have hvL : v ∈ fixedSpace ρ L := fixedSpace_of_apply_eq ρ hP hL hxL hx1 hv'
    have h1 : avgOp ρ L v = v := avgOp_apply_of_mem_fixedSpace ρ (natCard_cast_line hpK hL) hvL
    have hsplit : v = projTop ρ v + projLine ρ L v := by
      unfold projLine projTop
      rw [LinearMap.sub_apply, h1]
      change v = avgOp ρ ⊤ v + (v - avgOp ρ ⊤ v)
      abel
    rw [hsplit]
    refine Submodule.add_mem_sup (avgOp_apply_mem_fixedSpace ρ ⊤ v) ?_
    rw [← range_projLine ρ hP hpK hρ hB hBl hL]
    exact LinearMap.mem_range_self _ v
  · refine sup_le ?_ ?_
    · intro v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hv x (Subgroup.mem_top x)]
      simp
    · intro v hv
      rw [LinearMap.mem_ker, LinearMap.sub_apply, hv.1 x hxL]
      simp

theorem exists_two_active (hP : IsPlane p P) (hpK : (p : K) ≠ 0)
    (hρ : ∀ x : P, ρ x ∈ sesqUnitaryGroup B) (hB : B.IsSymm) (hBl : B.SeparatingLeft)
    (hinj : Function.Injective ρ) :
    ∃ L ∈ lines p P, ∃ M ∈ lines p P, L ≠ M ∧ lineSpace ρ B L ≠ ⊥ ∧ lineSpace ρ B M ≠ ⊥ := by
  by_contra hcon
  have hcon' : ∀ L ∈ lines p P, ∀ M ∈ lines p P, L ≠ M → lineSpace ρ B L ≠ ⊥ →
      lineSpace ρ B M = ⊥ := by
    intro L hL M hM hLM hLne
    by_contra hMne
    exact hcon ⟨L, hL, M, hM, hLM, hLne, hMne⟩
  have hex : ∃ L₀ ∈ lines p P, ∀ M ∈ lines p P, M ≠ L₀ → lineSpace ρ B M = ⊥ := by
    by_cases h : ∃ L₁ ∈ lines p P, lineSpace ρ B L₁ ≠ ⊥
    · obtain ⟨L₁, hL₁, hne⟩ := h
      exact ⟨L₁, hL₁, fun M hM hML => hcon' L₁ hL₁ M hM (Ne.symm hML) hne⟩
    · have h' : ∀ L ∈ lines p P, lineSpace ρ B L = ⊥ := fun L hL => by
        by_contra hne
        exact h ⟨L, hL, hne⟩
      have hnt : ∃ y : P, y ≠ 1 := by
        by_contra hall
        have hall' : ∀ y : P, y = 1 := fun y => by
          by_contra hy
          exact hall ⟨y, hy⟩
        have h1 : Nat.card P = 1 := by
          rw [Nat.card_eq_one_iff_unique]
          exact ⟨⟨fun a b => (hall' a).trans (hall' b).symm⟩, ⟨1⟩⟩
        rw [hP.card] at h1
        have h2 := hP.prime.two_le
        have : 2 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left h2 2
        omega
      obtain ⟨y, hy⟩ := hnt
      exact ⟨Subgroup.zpowers y, hP.zpowers_mem_lines hy, fun M hM _ => h' M hM⟩
  obtain ⟨L₀, hL₀, hrest⟩ := hex
  have hL₀c : Nat.card L₀ = p := mem_lines.mp hL₀
  have hx : ∃ x ∈ L₀, x ≠ 1 := by
    by_contra hall
    have hall' : ∀ x ∈ L₀, x = 1 := fun x hx => by
      by_contra hx1
      exact hall ⟨x, hx, hx1⟩
    have h1 : Nat.card L₀ = 1 := by
      rw [Nat.card_eq_one_iff_unique]
      exact ⟨⟨fun a b => Subtype.ext ((hall' a a.2).trans (hall' b b.2).symm)⟩, ⟨1⟩⟩
    rw [hL₀c] at h1
    exact hP.prime.one_lt.ne' h1
  obtain ⟨x, hxL, hx1⟩ := hx
  have htriv : act ρ x = 1 := by
    ext v
    have h := congrArg (fun f : Module.End K V => f v) (sum_projLine_add_projTop ρ hP hpK)
    simp only [LinearMap.add_apply, LinearMap.sum_apply, Module.End.one_apply] at h
    rw [Finset.sum_eq_single L₀ (fun M hM hML => by
      have h0 : lineSpace ρ B M = ⊥ := hrest M hM hML
      rw [← range_projLine ρ hP hpK hρ hB hBl (mem_lines.mp hM), LinearMap.range_eq_bot] at h0
      simpa using congrArg (fun f : Module.End K V => f v) h0) (fun hn => absurd hL₀ hn)] at h
    have hv1 : projLine ρ L₀ v ∈ fixedSpace ρ L₀ := by
      have : projLine ρ L₀ v ∈ lineSpace ρ B L₀ := by
        rw [← range_projLine ρ hP hpK hρ hB hBl hL₀c]
        exact LinearMap.mem_range_self _ v
      exact this.1
    have hv2 : projTop ρ v ∈ fixedSpace ρ L₀ := fun y hy =>
      avgOp_apply_mem_fixedSpace ρ ⊤ v y (Subgroup.mem_top y)
    have hv : v ∈ fixedSpace ρ L₀ := h ▸ Submodule.add_mem _ hv1 hv2
    simpa using hv x hxL
  apply hx1
  apply hinj
  rw [map_one]
  exact Units.ext htriv

end Geometry


end CFSG.RankThree.PartOne.KCUnitaryPlane

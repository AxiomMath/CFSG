module

public import CFSG.Monster.B.Geometry.PolarCoxeter
public import CFSG.LieType.Chevalley.C2E6FieldExtensionResidue
public import CFSG.Monster.B.E6.StdF4Weyl

public noncomputable section

namespace CFSG.Monster.B.E6.StdF4

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.C2E6Overlap CFSG.LieType.Chevalley.C2E6Std.FieldExtension
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.Classical

section Split

variable {ι : Type*} {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W} (hδ : IsWeylDistanceBuilding cs δ)
include hδ

theorem exists_dist_wordProd
    (a c : C) {ω : List ι} (hω : cs.IsReduced ω) :
    ∃ b, δ c b = cs.wordProd ω ∧ δ a b = δ a c * cs.wordProd ω := by
  induction ω using List.reverseRecOn with
  | nil => exact ⟨c, by rw [cs.wordProd_nil]; exact (hδ.eq_one_iff c c).2 rfl,
      by rw [cs.wordProd_nil, mul_one]⟩
  | append_singleton ω i ih =>
    obtain ⟨b', hcb', hab'⟩ := ih (isReduced_of_isReduced_concat hω)
    obtain ⟨b, hb'b, hab⟩ := hδ.exists_simple a b' i
    refine ⟨b, ?_, ?_⟩
    · have hl := length_mul_simple_of_isReduced_concat hω
      rw [← hcb'] at hl
      rw [(hδ.mul_simple c b' b i hb'b).2 hl, hcb', cs.wordProd_append, cs.wordProd_singleton]
    · rw [hab, hab', cs.wordProd_append, cs.wordProd_singleton, mul_assoc]

theorem exists_dist_eq_of_dist_eq_mul
    {a c : C} {x y : W} (h : δ a c = x * y) :
    ∃ b, δ a b = x ∧ δ b c = y := by
  obtain ⟨ω, hω, hy⟩ := cs.exists_isReduced y⁻¹
  obtain ⟨b, hcb, hab⟩ := exists_dist_wordProd hδ a c hω
  refine ⟨b, ?_, ?_⟩
  · rw [hab, ← hy, h, mul_inv_cancel_right]
  · rw [dist_inv hδ c b, hcb, ← hy, inv_inv]

theorem exists_dist_eq_mul_left_of_mem_residue {J : Set ι} {x x' : C}
    (hx : x' ∈ residue cs δ J x) (y : C) : ∃ u ∈ cs.parabolic J, δ x' y = u * δ x y := by
  obtain ⟨v, hv, h⟩ := exists_dist_eq_mul_of_mem_residue hδ (x := y) hx
  refine ⟨v⁻¹, inv_mem hv, ?_⟩
  rw [dist_inv hδ y x', h, mul_inv_rev, ← dist_inv hδ y x]

end Split

abbrev c₀ :
    stdChamber := ((1 : stdGroup) : stdChamber)

abbrev parabolicG
    (I : Set (Fin 4)) : Subgroup stdGroup := (nativeParabolic I).subgroupOf stdGroup

abbrev PJ :
    Subgroup stdGroup := parabolicG firstJ

abbrev PK :
    Subgroup stdGroup := parabolicG FourthResidue.fourthJ

theorem firstJ_eq_J : firstJ = E6Folded.J := rfl

theorem fourthJ_eq_K : FourthResidue.fourthJ = E6Folded.K := rfl

@[expose] def wOf
    (g : stdGroup) : NW := stdDistance c₀ (g : stdChamber)

@[expose] def lev
    (g : stdGroup) : ℤ := level (wOf g)

theorem hδ :

    IsWeylDistanceBuilding ncs stdDistance := isWeylDistanceBuilding_stdDistance

theorem wOf_eq_iff
    (g : stdGroup) (w : NW) : wOf g = w ↔ g ∈ stdCell w := by
  rw [wOf, stdBuilding.1 1 g w, inv_one, one_mul]

theorem mem_stdCell_wOf
    (g : stdGroup) : g ∈ stdCell (wOf g) := (wOf_eq_iff g _).1 rfl

theorem stdDistance_mul_mul
    (k g h : stdGroup) :
    stdDistance ((k * g : stdGroup) : stdChamber) ((k * h : stdGroup) : stdChamber) =
      stdDistance (g : stdChamber) (h : stdChamber) := by
  have e : (k * g)⁻¹ * (k * h) = g⁻¹ * h := by group
  rw [stdBuilding.1, e, ← stdBuilding.1]

theorem stdDistance_mk_mk
    (g h : stdGroup) :
    stdDistance (g : stdChamber) (h : stdChamber) = wOf (g⁻¹ * h) := by
  rw [wOf, ← stdDistance_mul_mul g⁻¹ g h, inv_mul_cancel]

theorem mem_parabolicG_iff
    (I : Set (Fin 4)) (p : stdGroup) :
    p ∈ parabolicG I ↔ wOf p ∈ ncs.parabolic I := by
  rw [Subgroup.mem_subgroupOf, ← mem_baseResidue_iff, baseResidue,
    mem_residue_iff_mem_parabolic hδ]
  rfl

theorem mem_residue_mk_iff
    (I : Set (Fin 4)) (g h : stdGroup) :
    (h : stdChamber) ∈ residue ncs stdDistance I (g : stdChamber) ↔ g⁻¹ * h ∈ parabolicG I := by
  rw [mem_residue_iff_mem_parabolic hδ, stdDistance_mk_mk, mem_parabolicG_iff]

theorem residue_mk_eq_iff
    (I : Set (Fin 4)) (g h : stdGroup) :
    residue ncs stdDistance I (g : stdChamber) = residue ncs stdDistance I (h : stdChamber) ↔
      g⁻¹ * h ∈ parabolicG I := by
  rw [← mem_residue_mk_iff]
  exact ⟨fun e => e ▸ self_mem_residue I _, fun hh => (residue_eq_of_mem hδ hh).symm⟩

theorem wOf_one :
    wOf 1 = 1 := (hδ.eq_one_iff _ _).2 rfl

theorem wOf_inv
    (g : stdGroup) : wOf g⁻¹ = (wOf g)⁻¹ := by
  have h := stdDistance_mk_mk g 1
  rw [mul_one] at h
  rw [← h, wOf, ← dist_inv hδ]

theorem wOf_stdRep
    (w : NW) : wOf (stdRep w) = w := by
  rw [wOf_eq_iff, stdCell_eq]
  exact ⟨stdRep w, ⟨1, one_mem _, stdRep w, rfl, one_mul _⟩, 1, one_mem _, mul_one _⟩

theorem wOf_betaG
    (g : stdGroup) : wOf (betaG g) = wOf g := by
  rw [wOf_eq_iff, mem_stdCell]
  exact (apply_mem_stdBruhatCell_iff betaElt (wOf g) g).2 (mem_stdCell_wOf g)

theorem lev_betaG
    (g : stdGroup) : lev (betaG g) = lev g := by
  rw [lev, lev, wOf_betaG]

theorem lev_stdRep
    (w : NW) : lev (stdRep w) = level w := by
  rw [lev, wOf_stdRep]

theorem lev_mul_mul
    {p p' : stdGroup} (hp : p ∈ PJ) (hp' : p' ∈ PJ) (g : stdGroup) :
    lev (p * g * p') = lev g := by
  have hpr : ((p⁻¹ : stdGroup) : stdChamber) ∈ residue ncs stdDistance firstJ c₀ := by
    rw [mem_residue_mk_iff, inv_one, one_mul]
    exact inv_mem hp
  have hgr : ((g * p' : stdGroup) : stdChamber) ∈
      residue ncs stdDistance firstJ (g : stdChamber) := by
    rw [mem_residue_mk_iff, inv_mul_cancel_left]
    exact hp'
  obtain ⟨u, hu, hu'⟩ := exists_dist_eq_mul_left_of_mem_residue hδ hpr
    ((g * p' : stdGroup) : stdChamber)
  obtain ⟨v, hv, hv'⟩ := exists_dist_eq_mul_of_mem_residue hδ (x := c₀) hgr
  have e : wOf (p * g * p') = u * wOf g * v := by
    have e0 : p⁻¹ * (p * g * p') = g * p' := by group
    rw [wOf, ← stdDistance_mul_mul p⁻¹, e0, mul_one, hu', hv', mul_assoc, wOf]
  rw [lev, lev, e]
  exact level_mul_mul hu hv _

theorem exists_mul_mul_of_lev_eq
    {g h : stdGroup} (hgh : lev h = lev g) :
    ∃ p ∈ PJ, ∃ p' ∈ PJ, h = p * g * p' := by
  obtain ⟨u, hu, v, hv, e⟩ := exists_mul_mul_of_level_eq hgh
  have e1 : stdDistance c₀ (h : stdChamber) = u * (wOf g * v) := by
    rw [← wOf, e, mul_assoc]
  obtain ⟨b, hb1, hb2⟩ := exists_dist_eq_of_dist_eq_mul hδ e1
  induction b using QuotientGroup.induction_on with | H p => ?_
  have hp : p ∈ PJ := (mem_parabolicG_iff firstJ p).2 (by rw [wOf]; exact hb1 ▸ hu)
  have e2 : stdDistance c₀ ((p⁻¹ * h : stdGroup) : stdChamber) = wOf g * v := by
    rw [← stdDistance_mul_mul p⁻¹ p h, inv_mul_cancel] at hb2
    exact hb2
  obtain ⟨b', hb1', hb2'⟩ := exists_dist_eq_of_dist_eq_mul hδ e2
  induction b' using QuotientGroup.induction_on with | H k => ?_
  have hk : k ∈ stdCell (wOf g) := (wOf_eq_iff k _).1 hb1'
  have hp' : k⁻¹ * (p⁻¹ * h) ∈ PJ := by
    rw [mem_parabolicG_iff, ← stdDistance_mk_mk, hb2']
    exact hv
  rw [stdCell_eq] at hk
  have hg := mem_stdCell_wOf g
  rw [stdCell_eq] at hg
  obtain ⟨x, ⟨b₁, hb₁, n, hn, hx⟩, b₂, hb₂, hkx⟩ := hk
  obtain ⟨x', ⟨b₃, hb₃, n', hn', hx'⟩, b₄, hb₄, hgx⟩ := hg
  rw [Set.mem_singleton_iff] at hn hn'
  have hBJ : stdBorelG ≤ PJ := fun b hb => stdBorel_le_nativeParabolic firstJ hb
  refine ⟨p * (b₁ * b₃⁻¹), mul_mem hp (mul_mem (hBJ hb₁) (inv_mem (hBJ hb₃))),
    b₄⁻¹ * b₂ * (k⁻¹ * (p⁻¹ * h)), mul_mem (mul_mem (inv_mem (hBJ hb₄)) (hBJ hb₂)) hp', ?_⟩
  simp only at hx hkx hx' hgx
  rw [← hgx, ← hx', hn']
  rw [← hkx, ← hx, hn]
  group

theorem mem_PJ_PK_PJ_iff
    (h : stdGroup) :
    (∃ p ∈ PJ, ∃ k ∈ PK, ∃ p' ∈ PJ, h = p * k * p') ↔ lev h = 2 ∨ lev h = 1 ∨ lev h = 0 := by
  rw [lev, ← mem_double_coset_K_iff]
  constructor
  · rintro ⟨p, hp, k, hk, p', hp', rfl⟩
    have hpr : ((p⁻¹ : stdGroup) : stdChamber) ∈ residue ncs stdDistance firstJ c₀ := by
      rw [mem_residue_mk_iff, inv_one, one_mul]
      exact inv_mem hp
    have hkr : ((k * p' : stdGroup) : stdChamber) ∈
        residue ncs stdDistance firstJ (k : stdChamber) := by
      rw [mem_residue_mk_iff, inv_mul_cancel_left]
      exact hp'
    obtain ⟨u, hu, hu'⟩ := exists_dist_eq_mul_left_of_mem_residue hδ hpr
      ((k * p' : stdGroup) : stdChamber)
    obtain ⟨v, hv, hv'⟩ := exists_dist_eq_mul_of_mem_residue hδ (x := c₀) hkr
    refine ⟨u, hu, wOf k, (mem_parabolicG_iff _ k).1 hk, v, hv, ?_⟩
    have e0 : p⁻¹ * (p * k * p') = k * p' := by group
    rw [wOf, ← stdDistance_mul_mul p⁻¹, e0, mul_one, hu', hv', wOf, mul_assoc]
  · rintro ⟨a, ha, b, hb, c, hc, e⟩
    have e1 : stdDistance c₀ (h : stdChamber) = a * (b * c) := by rw [← wOf, e, mul_assoc]
    obtain ⟨y, hy1, hy2⟩ := exists_dist_eq_of_dist_eq_mul hδ e1
    induction y using QuotientGroup.induction_on with | H p => ?_
    have hp : p ∈ PJ := (mem_parabolicG_iff firstJ p).2 (by rw [wOf]; exact hy1 ▸ ha)
    have e2 : stdDistance c₀ ((p⁻¹ * h : stdGroup) : stdChamber) = b * c := by
      rw [← stdDistance_mul_mul p⁻¹ p h, inv_mul_cancel] at hy2
      exact hy2
    obtain ⟨y', hy1', hy2'⟩ := exists_dist_eq_of_dist_eq_mul hδ e2
    induction y' using QuotientGroup.induction_on with | H k => ?_
    have hk : k ∈ PK := (mem_parabolicG_iff _ k).2 (by rw [wOf]; exact hy1' ▸ hb)
    have hp' : k⁻¹ * (p⁻¹ * h) ∈ PJ := by
      rw [mem_parabolicG_iff, ← stdDistance_mk_mk, hy2']
      exact hc
    exact ⟨p, hp, k, hk, _, hp', by group⟩

end CFSG.Monster.B.E6.StdF4

module

public import CFSG.RankThree.Chevalley.SteinbergCFEvenF4RootSL2Traces
public import Certificates.Data.F4NA
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.MsideParabolicEscape.F4AdjointCert
public import CFSG.LieType.Chevalley.LargeReeAmbientPositiveCentralizer
public import CFSG.LieType.Simplicity.TitsBits
import all CFSG.LieType.Simplicity.TitsBits

public section

namespace CFSG.RankThree.PartOne.F106

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
  CFSG.LieType.Simplicity.TitsBits CFSG.LieType.Chevalley.RootOps CFSG.RankThree.Chevalley

variable {K : Type} [Field K] [CharP K 2]

section Invariance

theorem f4_prime_cast_eq_zero : ((ReeTag.F4.prime : ℕ) : K) = 0 :=
  CharP.cast_eq_zero K 2

theorem map_shortModule_of_mem (g : ModGL ReeTag.F4.tag K) (hg : g ∈ adjointGroup ReeTag.F4.tag K) :
    (ReeTag.F4.shortModule K).map (g : Module.End K (RootModule ReeTag.F4.tag K)) =
      ReeTag.F4.shortModule K := by
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨i, c, h | h⟩ := hx
    · rw [h]
      exact ReeTag.map_xOp_shortModule K f4_prime_cast_eq_zero i c
    · rw [h]
      exact ReeTag.map_yOp_shortModule K f4_prime_cast_eq_zero i c
  | one =>
    rw [Units.val_one, Module.End.one_eq_id]
    exact Submodule.map_id _
  | mul x y _ _ hx hy =>
    rw [Units.val_mul, Module.End.mul_eq_comp, Submodule.map_comp, hy, hx]
  | inv x _ hx =>
    have h1 : ((x⁻¹ : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) *
        (x : Module.End K (RootModule ReeTag.F4.tag K)) = 1 := by
      rw [← Units.val_mul, inv_mul_cancel, Units.val_one]
    calc (ReeTag.F4.shortModule K).map
          ((x⁻¹ : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K))
        = ((ReeTag.F4.shortModule K).map
            (x : Module.End K (RootModule ReeTag.F4.tag K))).map
          ((x⁻¹ : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) := by
          rw [hx]
      _ = (ReeTag.F4.shortModule K).map
          (((x⁻¹ : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) *
            (x : Module.End K (RootModule ReeTag.F4.tag K))) := by
          rw [Module.End.mul_eq_comp, Submodule.map_comp]
      _ = ReeTag.F4.shortModule K := by
          rw [h1, Module.End.one_eq_id]
          exact Submodule.map_id _

theorem mem_shortModule_of_mem (g : adjointGroup ReeTag.F4.tag K) {v : RootModule ReeTag.F4.tag K}
    (hv : v ∈ ReeTag.F4.shortModule K) :
    ((g : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) v ∈
      ReeTag.F4.shortModule K := by
  rw [← map_shortModule_of_mem g g.2]
  exact Submodule.mem_map_of_mem hv

end Invariance

section Trace

open _root_.Classical in
noncomputable def trOnI (f : Module.End K (RootModule ReeTag.F4.tag K)) : K :=
  if hf : ∀ v ∈ ReeTag.F4.shortModule K, f v ∈ ReeTag.F4.shortModule K then
    LinearMap.trace K (ReeTag.F4.shortModule K) (f.restrict hf)
  else 0

omit [CharP K 2] in
theorem trOnI_of_mem {f : Module.End K (RootModule ReeTag.F4.tag K)}
    (hf : ∀ v ∈ ReeTag.F4.shortModule K, f v ∈ ReeTag.F4.shortModule K) :
    trOnI f = LinearMap.trace K (ReeTag.F4.shortModule K) (f.restrict hf) := by
  rw [trOnI, dite_eq_left hf]

noncomputable def trI (g : adjointGroup ReeTag.F4.tag K) : K :=
  trOnI (g : ModGL ReeTag.F4.tag K)

theorem trI_eq (g : adjointGroup ReeTag.F4.tag K) :
    trI g = LinearMap.trace K (ReeTag.F4.shortModule K)
      (((g : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)).restrict
        (fun _ hv => mem_shortModule_of_mem g hv)) :=
  trOnI_of_mem _

theorem trI_conj (h g : adjointGroup ReeTag.F4.tag K) : trI (h * g * h⁻¹) = trI g := by
  have hW := fun v (hv : v ∈ ReeTag.F4.shortModule K) => mem_shortModule_of_mem h hv
  have hW' := fun v (hv : v ∈ ReeTag.F4.shortModule K) => mem_shortModule_of_mem h⁻¹ hv
  have hg := fun v (hv : v ∈ ReeTag.F4.shortModule K) => mem_shortModule_of_mem g hv
  have hc := fun v (hv : v ∈ ReeTag.F4.shortModule K) => mem_shortModule_of_mem (h * g * h⁻¹) hv
  rw [trI_eq, trI_eq]
  exact trace_restrict_conj (ReeTag.F4.shortModule K) (h : ModGL ReeTag.F4.tag K)
    (g : ModGL ReeTag.F4.tag K) hW hW' hg hc

end Trace

section Bits

theorem posLabel_short_iff {p : ℕ} (hp : p < dim ReeTag.F4.tag) :
    ReeTag.F4.IsShortLabel (posLabel (τ := ReeTag.F4.tag) p hp) ↔ p ∈ f4ShortPos := by
  have hp52 : p < 52 := lt_of_lt_of_eq hp dim_F4
  have h1 : ∀ p : Fin ReeTag.F4.tag.rank, p ∉ ReeTag.F4.longSet ↔ p.1 ∈ f4ShortPos := by
    decide
  have h2 : ∀ p < 52, 4 ≤ p →
      (ReeTag.F4.lengthParam (ReeTag.F4.tag.rootCertificate.root (p - 4)) = 1 ↔
        p ∈ f4ShortPos) := by
    decide +kernel
  by_cases h : p < ReeTag.F4.tag.rank
  · unfold posLabel
    rw [dite_eq_left h]
    exact h1 ⟨p, h⟩
  · unfold posLabel
    rw [dite_eq_right h]
    exact h2 p hp52 (not_lt.1 h)

theorem f4ShortPos_lt : ∀ p ∈ f4ShortPos, p < 52 := by decide

theorem f4ShortPos_nodup : f4ShortPos.Nodup := by decide

theorem trI_of_hasBits {g : adjointGroup ReeTag.F4.tag K} {A : ℕ} (hg : HasBits K g A) :
    trI g = ∑ p ∈ f4ShortPos.toFinset, bitK K (A.testBit (52 * p + p)) := by
  classical
  rw [trI_eq, trace_restrict_shortModule ReeTag.F4 _ (fun _ hv => mem_shortModule_of_mem g hv)]
  let lab : ℕ → Label ReeTag.F4.tag := fun p =>
    if hp : p < dim ReeTag.F4.tag then posLabel (τ := ReeTag.F4.tag) p hp
    else Sum.inl ⟨0, by decide⟩
  have hlab : ∀ p (hp : p < dim ReeTag.F4.tag), lab p = posLabel (τ := ReeTag.F4.tag) p hp :=
    fun p hp => by simp only [lab, dite_eq_left hp]
  have hdim : ∀ p ∈ f4ShortPos, p < dim ReeTag.F4.tag := fun p hp =>
    lt_of_lt_of_eq (f4ShortPos_lt p hp) dim_F4.symm
  have himg : Finset.univ.filter ReeTag.F4.IsShortLabel = f4ShortPos.toFinset.image lab := by
    ext b
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, List.mem_toFinset]
    constructor
    · intro hb
      obtain ⟨p, hp, rfl⟩ := posLabel_surjective b
      exact ⟨p, (posLabel_short_iff hp).1 hb, hlab p hp⟩
    · rintro ⟨p, hp, rfl⟩
      rw [hlab p (hdim p hp)]
      exact (posLabel_short_iff _).2 hp
  rw [himg, Finset.sum_image]
  · refine Finset.sum_congr rfl fun p hp => ?_
    have hp' : p ∈ f4ShortPos := List.mem_toFinset.1 hp
    have hp52 := f4ShortPos_lt p hp'
    have hd := hdim p hp'
    have e1 : (Finsupp.single (lab p) 1 : RootModule ReeTag.F4.tag K) =
        posVec ReeTag.F4.tag K p := by
      rw [hlab p hd, posVec_eq_single hd]
    have e2 : ((g : ModGL ReeTag.F4.tag K) : Module.End K (RootModule ReeTag.F4.tag K)) =
        toEnd K A := hg
    rw [e1, e2, hlab p hd]
    have e3 := posCoord_toEnd_posVec (K := K) A (c := p) (p := p) hp52 hp52
    unfold posCoord at e3
    rw [dite_eq_left hd, Finsupp.lapply_apply] at e3
    exact e3
  · intro a ha b hb hab
    have ha' := hdim a (List.mem_toFinset.1 ha)
    have hb' := hdim b (List.mem_toFinset.1 hb)
    rw [hlab a ha', hlab b hb'] at hab
    exact posLabel_injective ha' hb' hab

theorem bitK_foldr_xor (A : ℕ) (l : List ℕ) :
    bitK K (l.foldr (fun p b => xor (A.testBit (52 * p + p)) b) false) =
      (l.map fun p => bitK K (A.testBit (52 * p + p))).sum := by
  induction l with
  | nil => simp [bitK]
  | cons p l ih =>
    rw [List.foldr_cons, bitK_xor, ih, List.map_cons, List.sum_cons]

theorem trI_eq_bitK {g : adjointGroup ReeTag.F4.tag K} {A : ℕ} (hg : HasBits K g A) :
    trI g = bitK K (trIB A) := by
  rw [trI_of_hasBits hg, List.sum_toFinset _ f4ShortPos_nodup, trIB, bitK_foldr_xor]

theorem trI_eq_zero_iff {g : adjointGroup ReeTag.F4.tag K} {A : ℕ} (hg : HasBits K g A) :
    trI g = 0 ↔ trIB A = false := by
  rw [trI_eq_bitK hg]
  constructor
  · intro h
    by_contra hb
    have : trIB A = true := by simpa using hb
    rw [this] at h
    simp [bitK] at h
  · intro h
    rw [h]
    simp [bitK]

end Bits

namespace ShortRank

open CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.F4Adjoint
  CFSG.LieType.Simplicity.TitsBits Module

abbrev shortLabelsF4 : Set (Label Tag.F4) := ReeTag.F4.shortLabels

noncomputable def shortProj : Module.End K (RootModule Tag.F4 K) := by
  classical
  exact (Finsupp.supported K K shortLabelsF4).subtype.comp
    (Finsupp.restrictDom K K shortLabelsF4)

omit [CharP K 2] in
theorem shortProj_lvec (L : List ℕ) (hL : ∀ l ∈ L, l < 52) :
    shortProj (K := K) (lvec K L) =
      lvec K (L.filter (fun p => p ∈ f4ShortPos)) := by
  induction L with
  | nil => simp [lvec]
  | cons p L ih =>
    rw [lvec_cons, map_add, ih (fun l hl => hL l (List.mem_cons_of_mem _ hl))]
    have hp := hL p List.mem_cons_self
    have hto : toVec K (1 <<< p) = lvec K [p] := by
      rw [toVec_one_shiftLeft' hp, ← lvec_singleton (R := K) hp]
    have hsingle : shortProj (K := K) (lvec K [p]) =
        if p ∈ f4ShortPos then lvec K [p] else 0 := by
      classical
      rw [lvec_singleton (R := K) hp]
      unfold shortProj
      rw [LinearMap.comp_apply, Submodule.subtype_apply, Finsupp.restrictDom_apply]
      have hdim : p < dim ReeTag.F4.tag := by rw [dim_F4]; exact hp
      have hlab : lab ⟨p, hp⟩ = posLabel (τ := ReeTag.F4.tag) p hdim := by
        unfold lab posLabel
        simp only [Tag.rank]
        split_ifs <;> rfl
      have hshort : (lab ⟨p, hp⟩ ∈ shortLabelsF4) ↔ p ∈ f4ShortPos := by
        rw [hlab]
        exact posLabel_short_iff hdim
      by_cases h : p ∈ f4ShortPos
      · rw [if_pos h]
        rw [Finsupp.filter_single_of_pos (p := fun x => x ∈ shortLabelsF4) (h := hshort.2 h)]
      · rw [if_neg h]
        rw [Finsupp.filter_single_of_neg (p := fun x => x ∈ shortLabelsF4)
          (h := fun hh => h (hshort.1 hh))]
    rw [hto, hsingle]
    by_cases h : p ∈ f4ShortPos <;> simp [h, lvec]

def fSX (i : ℕ) (L : List ℕ) : List ℕ :=
  let R := L.filter (fun p => p ∈ f4ShortPos)
  R ++ applyX i R

def pivSX0 : List ℕ := [20, 22, 28, 31, 35, 37]
def preSX0 : List (List ℕ) := [[12], [30], [21], [36], [29], [41]]
def zsSX0 : List ℕ := [1048576, 4194304, 268435456, 2147483648, 34359738368, 137438953472]
theorem certSX0 : certOK (fSX 0) pivSX0 preSX0 zsSX0 = true := by decide +kernel

def pivSX1 : List ℕ := [12, 13, 21, 23, 40, 41]
def preSX1 : List (List ℕ) := [[6], [22], [14], [31], [35], [45]]
def zsSX1 : List ℕ := [4096, 8192, 2097152, 8388608, 1099511627776, 2199023255552]
theorem certSX1 : certOK (fSX 1) pivSX1 preSX1 zsSX1 = true := by decide +kernel

def pivSX2 : List ℕ := [2, 6, 14, 15, 29, 31, 35, 36, 44, 45]
def preSX2 : List (List ℕ) := [[3, 13], [3], [7], [23], [21], [37], [28], [41], [40], [49]]
def zsSX2 : List ℕ := [4, 64, 16384, 32768, 536870912, 2147483648,
  34359738368, 68719476736, 17592186044416, 35184372088832]
theorem certSX2 : certOK (fSX 2) pivSX2 preSX2 zsSX2 = true := by decide +kernel

def pivSX3 : List ℕ := [3, 7, 13, 14, 21, 22, 28, 30, 48, 49]
def preSX3 : List (List ℕ) := [[2, 15], [2], [23], [6], [12], [31], [20], [36], [44], [51]]
def zsSX3 : List ℕ := [8, 128, 8192, 16384, 2097152, 4194304, 268435456,
  1073741824, 281474976710656, 562949953421312]
theorem certSX3 : certOK (fSX 3) pivSX3 preSX3 zsSX3 = true := by decide +kernel

noncomputable def shortMap (i : Fin Tag.F4.rank) : Module.End K (RootModule Tag.F4 K) :=
  (xOp Tag.F4 K i 1 - 1).comp (shortProj (K := K))

noncomputable abbrev S : Submodule K (RootModule Tag.F4 K) := ReeTag.F4.shortModule K

noncomputable def rankSubOne (g : ModGL Tag.F4 K) : ℕ :=
  finrank K (S.map ((g : Module.End K (RootModule Tag.F4 K)) - 1))

theorem map_S_eq_S (h : ModGL Tag.F4 K) (hh : h ∈ adjointGroup Tag.F4 K) :
    S.map (h : Module.End K (RootModule Tag.F4 K)) = S :=
  map_shortModule_of_mem h hh

theorem rankSubOne_conj (h g : ModGL Tag.F4 K) (hh : h ∈ adjointGroup Tag.F4 K) :
    rankSubOne (h * g * h⁻¹) = rankSubOne g := by
  unfold rankSubOne
  have e : ((h * g * h⁻¹ : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K)) - 1 =
      (h : Module.End K (RootModule Tag.F4 K)) *
        ((g : Module.End K (RootModule Tag.F4 K)) - 1) *
          ((h⁻¹ : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K)) := by
    rw [Units.val_mul, Units.val_mul, mul_sub, sub_mul, mul_one, mul_assoc,
      show (h : Module.End K (RootModule Tag.F4 K)) *
        ((h⁻¹ : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K)) = 1 from h.mul_inv]
  rw [e]
  have hmap : S.map ((h : Module.End K (RootModule Tag.F4 K)) *
      ((g : Module.End K (RootModule Tag.F4 K)) - 1) *
        ((h⁻¹ : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K))) =
      (S.map ((g : Module.End K (RootModule Tag.F4 K)) - 1)).map
        (h : Module.End K (RootModule Tag.F4 K)) := by
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp]
    rw [Submodule.map_comp]
    rw [map_S_eq_S h⁻¹ (inv_mem hh)]
    rw [Submodule.map_comp]
  rw [hmap]
  let V := RootModule Tag.F4 K
  let H : Module.End K V := (h : Module.End K (RootModule Tag.F4 K))
  let Hinv : Module.End K V := ((h⁻¹ : ModGL Tag.F4 K) : Module.End K (RootModule Tag.F4 K))
  have hHH' : H * Hinv = 1 := h.mul_inv
  have hH'H : Hinv * H = 1 := h.inv_mul
  let eH : V ≃ₗ[K] V := LinearEquiv.ofLinear H Hinv hHH' hH'H
  exact LinearEquiv.finrank_map_eq eH _

omit [CharP K 2] in
theorem range_shortProj :
    LinearMap.range (shortProj (K := K)) = S := by
  classical
  rw [show S = Finsupp.supported K K shortLabelsF4 from
    ReeTag.shortModule_eq_supported ReeTag.F4 K]
  unfold shortProj
  rw [LinearMap.range_comp, Finsupp.range_restrictDom, Submodule.map_top,
    Submodule.range_subtype]

omit [CharP K 2] in
theorem range_shortMap_eq_map (i : Fin Tag.F4.rank) :
    LinearMap.range (shortMap (K := K) i) = S.map (xOp Tag.F4 K i 1 - 1) := by
  unfold shortMap
  rw [LinearMap.range_comp, range_shortProj]

theorem finrank_shortMap_zero :
    finrank K (LinearMap.range (shortMap (K := K) ⟨0, by decide⟩)) = 6 := by
  have hf : ∀ L : List ℕ, (∀ l ∈ L, l < 52) →
      shortMap (K := K) ⟨0, by decide⟩ (lvec K L) = lvec K (fSX 0 L) := by
    intro L hL
    unfold shortMap
    rw [LinearMap.comp_apply, shortProj_lvec L hL]
    exact sub_one_lvec (f := xOp Tag.F4 K ⟨0, by decide⟩ 1)
      (fIdx := fun L => applyX 0 L)
      (xOp_one_lvec (R := K) ⟨0, by decide⟩ (by
        intro l hl
        exact hL l (List.mem_of_mem_filter hl)))
  simpa [pivSX0] using finrank_range_of_certOK
    (shortMap (K := K) ⟨0, by decide⟩) (fSX 0) hf pivSX0 preSX0 zsSX0 certSX0

theorem finrank_shortMap_one :
    finrank K (LinearMap.range (shortMap (K := K) ⟨1, by decide⟩)) = 6 := by
  have hf : ∀ L : List ℕ, (∀ l ∈ L, l < 52) →
      shortMap (K := K) ⟨1, by decide⟩ (lvec K L) = lvec K (fSX 1 L) := by
    intro L hL
    unfold shortMap
    rw [LinearMap.comp_apply, shortProj_lvec L hL]
    exact sub_one_lvec (f := xOp Tag.F4 K ⟨1, by decide⟩ 1)
      (fIdx := fun L => applyX 1 L)
      (xOp_one_lvec (R := K) ⟨1, by decide⟩ (by
        intro l hl
        exact hL l (List.mem_of_mem_filter hl)))
  simpa [pivSX1] using finrank_range_of_certOK
    (shortMap (K := K) ⟨1, by decide⟩) (fSX 1) hf pivSX1 preSX1 zsSX1 certSX1

theorem finrank_shortMap_two :
    finrank K (LinearMap.range (shortMap (K := K) ⟨2, by decide⟩)) = 10 := by
  have hf : ∀ L : List ℕ, (∀ l ∈ L, l < 52) →
      shortMap (K := K) ⟨2, by decide⟩ (lvec K L) = lvec K (fSX 2 L) := by
    intro L hL
    unfold shortMap
    rw [LinearMap.comp_apply, shortProj_lvec L hL]
    exact sub_one_lvec (f := xOp Tag.F4 K ⟨2, by decide⟩ 1)
      (fIdx := fun L => applyX 2 L)
      (xOp_one_lvec (R := K) ⟨2, by decide⟩ (by
        intro l hl
        exact hL l (List.mem_of_mem_filter hl)))
  simpa [pivSX2] using finrank_range_of_certOK
    (shortMap (K := K) ⟨2, by decide⟩) (fSX 2) hf pivSX2 preSX2 zsSX2 certSX2

theorem finrank_shortMap_three :
    finrank K (LinearMap.range (shortMap (K := K) ⟨3, by decide⟩)) = 10 := by
  have hf : ∀ L : List ℕ, (∀ l ∈ L, l < 52) →
      shortMap (K := K) ⟨3, by decide⟩ (lvec K L) = lvec K (fSX 3 L) := by
    intro L hL
    unfold shortMap
    rw [LinearMap.comp_apply, shortProj_lvec L hL]
    exact sub_one_lvec (f := xOp Tag.F4 K ⟨3, by decide⟩ 1)
      (fIdx := fun L => applyX 3 L)
      (xOp_one_lvec (R := K) ⟨3, by decide⟩ (by
        intro l hl
        exact hL l (List.mem_of_mem_filter hl)))
  simpa [pivSX3] using finrank_range_of_certOK
    (shortMap (K := K) ⟨3, by decide⟩) (fSX 3) hf pivSX3 preSX3 zsSX3 certSX3

omit [CharP K 2] in
theorem rankSubOne_xUnit (i : Fin Tag.F4.rank) :
    rankSubOne (xUnit Tag.F4 K i 1) =
      finrank K (LinearMap.range (shortMap (K := K) i)) := by
  unfold rankSubOne
  rw [range_shortMap_eq_map, coe_xUnit]

theorem rankSubOne_pinnedX (α : Fin Tag.F4.rank → ℤ) :
    rankSubOne (pinnedX Tag.F4 K α 1) =
      rankSubOne (xUnit Tag.F4 K (pinnedData Tag.F4 α).1
        ((pinnedData Tag.F4 α).2.2 • (1 : K))) := by
  change rankSubOne (pinnedWeyl Tag.F4 K α * xUnit Tag.F4 K (pinnedData Tag.F4 α).1
      ((pinnedData Tag.F4 α).2.2 • (1 : K)) * (pinnedWeyl Tag.F4 K α)⁻¹) = _
  exact rankSubOne_conj (h := pinnedWeyl Tag.F4 K α)
    (g := xUnit Tag.F4 K (pinnedData Tag.F4 α).1
      ((pinnedData Tag.F4 α).2.2 • (1 : K)))
    (pinnedWeyl_mem_adjointGroup α)

theorem pinnedSign_smul_one (α : Fin Tag.F4.rank → ℤ) :
    (pinnedData Tag.F4 α).2.2 • (1 : K) = 1 := by
  have hsign : (pinnedData Tag.F4 α).2.2 = 1 ∨ (pinnedData Tag.F4 α).2.2 = -1 := by
    unfold pinnedData
    split_ifs <;> simp
  rcases hsign with h | h
  · rw [h]; norm_num
  · rw [h]; norm_num [CharTwo.neg_eq]

theorem pinnedData_f4_47 :
    (pinnedData Tag.F4 (orbitCertRoot Tag.F4 47)).1 = ⟨0, by decide⟩ := by
  decide +kernel

theorem pinnedData_f4_44 :
    (pinnedData Tag.F4 (orbitCertRoot Tag.F4 44)).1 = ⟨2, by decide⟩ := by
  decide +kernel

theorem rankSubOne_f4x47 : rankSubOne (f4x K 47 1) = 6 := by
  rw [f4x]
  rw [rankSubOne_pinnedX (orbitCertRoot Tag.F4 47)]
  rw [pinnedSign_smul_one (orbitCertRoot Tag.F4 47)]
  rw [pinnedData_f4_47]
  rw [rankSubOne_xUnit]
  exact finrank_shortMap_zero

theorem rankSubOne_f4x44 : rankSubOne (f4x K 44 1) = 10 := by
  rw [f4x]
  rw [rankSubOne_pinnedX (orbitCertRoot Tag.F4 44)]
  rw [pinnedSign_smul_one (orbitCertRoot Tag.F4 44)]
  rw [pinnedData_f4_44]
  rw [rankSubOne_xUnit]
  exact finrank_shortMap_two


end ShortRank

end CFSG.RankThree.PartOne.F106

module

public import CFSG.LocalAnalysis.StandardType.GGE6DepStdFrame
public import CFSG.LocalAnalysis.StandardType.GGE6DepExtract
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelShape
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelOrbit
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelReflClass
public import CFSG.LocalAnalysis.StandardType.GGE6DepKClassForm

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

private theorem evalWord_append {n : ℕ} (g : Fin n → Mat6) (l₁ l₂ : List (Fin n)) :
    evalWord g (l₁ ++ l₂) = evalWord g l₁ * evalWord g l₂ := by
  induction l₁ with
  | nil => simp [evalWord]
  | cons i l ih => simp only [List.cons_append, evalWord, ih, mul_assoc]

private theorem evalWord_singleton (i : Fin 6) : evalWord gensL [i] = gensL i := by
  simp [evalWord]

private theorem gensL_mem_refl36_all : ∀ i : Fin 6, gensL i ∈ refl36 := by
  decide +kernel

private theorem evalWord_conj_refl36 {t : Mat6} (ht : t ∈ refl36) (w : List (Fin 6)) :
    evalWord gensL w * t * evalWord gensL w.reverse ∈ refl36 := by
  induction w with
  | nil => simpa [evalWord] using ht
  | cons i w ih =>
      have heq : evalWord gensL (i :: w) * t * evalWord gensL (i :: w).reverse =
          gensL i * (evalWord gensL w * t * evalWord gensL w.reverse) * gensL i := by
        rw [List.reverse_cons, evalWord_append, evalWord_singleton]
        rw [show evalWord gensL (i :: w) = gensL i * evalWord gensL w from rfl]
        ac_rfl
      rw [heq]
      exact refl36_conj_mem (gensL_mem_refl36_all i) ih

private theorem gensL_mulVec_single5 (i : Fin 6) :
    (gensL i).mulVec (Pi.single 5 (1 : ZMod 3)) = Pi.single 5 (1 : ZMod 3) := by
  revert i
  decide +kernel

private theorem closureL_mulVec_single5 {g : Mat6} (hg : g ∈ closureL) :
    g.mulVec (Pi.single 5 (1 : ZMod 3)) = Pi.single 5 (1 : ZMod 3) := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact gensL_mulVec_single5 i
  | one => exact Matrix.one_mulVec _
  | mul g h _ _ ihg ihh => rw [← Matrix.mulVec_mulVec, ihh, ihg]

private theorem actsAs_conj_of_coord {Bs : Subgroup G} {ι ι' : Additive ↥Bs ≃+ Vec6}
    {k k' : Mat6}
    (hι' : ∀ b : ↥Bs, ι' (Additive.ofMul b) = k.mulVec (ι (Additive.ofMul b)))
    (hk'k : k' * k = 1) {φ : MulAut ↥Bs} {m : Mat6} (hm : ActsAs ι φ m) :
    ActsAs ι' φ (k * m * k') := by
  intro b
  calc
    ι' (Additive.ofMul (φ b)) = k.mulVec (ι (Additive.ofMul (φ b))) := hι' (φ b)
    _ = k.mulVec (m.mulVec (ι (Additive.ofMul b))) := by rw [hm b]
    _ = (k * m).mulVec (ι (Additive.ofMul b)) := by rw [Matrix.mulVec_mulVec]
    _ = ((k * m * k') * k).mulVec (ι (Additive.ofMul b)) := by
          rw [mul_assoc, hk'k, mul_one]
    _ = (k * m * k').mulVec (k.mulVec (ι (Additive.ofMul b))) := by
          rw [Matrix.mulVec_mulVec]
    _ = (k * m * k').mulVec (ι' (Additive.ofMul b)) := by rw [hι' b]

private theorem gS_mem_reflFix_xs_all : ∀ i : Fin 5, gS i ∈ reflFix xs := by
  decide +kernel

theorem ggE6Dep_standardPosition {Bs L : Subgroup G} {x y : G} (hxBs : x ∈ Bs) (hyBs : y ∈ Bs)
    (hxy : y ∉ Subgroup.zpowers x) {ι : Additive ↥Bs ≃+ Vec6}
    (hι : GGE6DepCoord Bs L x hxBs ι)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (b : Λ) (ρ : Λ → MulAut ↥Bs)
    (hρrefl : ∀ l, GGIsReflection 3 (ρ l))
    (hLgen : ggAutomizer L Bs = Subgroup.closure (Set.range ρ))
    (hρy : ∀ l : Λ, l ≠ b → ρ l ⟨y, hyBs⟩ = ⟨y, hyBs⟩)
    (hiso : norm6 (hpart (ι (Additive.ofMul ⟨y, hyBs⟩))) ≠ 0) :
    ∃ (ι' : Additive ↥Bs ≃+ Vec6) (c : ZMod 3) (g : Λ → Mat6),
      GGE6DepCoord Bs L x hxBs ι' ∧
      ι' (Additive.ofMul ⟨y, hyBs⟩) = xs + c • xx ∧
      (∀ l, g l ∈ refl36 ∧ ActsAs ι' (ρ l) (g l)) ∧
      (∀ l, l ≠ b → g l ∈ reflFix xs) ∧
      (∀ i : Fin 5, ∃ φ ∈ Subgroup.closure (Set.range fun l : {l : Λ // l ≠ b} => ρ l),
        ActsAs ι' φ (gS i)) := by
  classical
  obtain ⟨g, v, c₀, hpart1, hv5, hvne, hw_eq, hfix, hConj⟩ :=
    ggE6Dep_extract hxBs hyBs hxy hι.1 hι.2.2.1 hι.2.2.2
      (fun T hT h2 hc => eq_refl36_of_isRefl hT h2 hc) b ρ hρrefl hLgen hρy
  have hw5 : (v + c₀ • (Pi.single 5 (1 : ZMod 3) : Vec6)) 5 = c₀ := by
    simp [hv5]
  have hhpart : hpart (v + c₀ • Pi.single 5 (1 : ZMod 3)) = v := by
    unfold hpart
    rw [hw5, add_sub_cancel_right]
  have hnorm_v : norm6 v ≠ 0 := by
    rw [hw_eq, hhpart] at hiso
    exact hiso
  set T : Finset Mat6 := (Finset.univ.filter fun l : Λ => l ≠ b).image g with hTdef
  have hT_reflFix : T ⊆ reflFix v := by
    intro t ht
    rw [hTdef] at ht
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp ht
    rw [Finset.mem_filter] at hl
    exact hfix l hl.2
  have hgb : g b ∈ refl36 := (hpart1 b).1
  have hins_eq : insert (g b) T = Finset.univ.image g := by
    ext t
    constructor
    · intro ht
      rcases Finset.mem_insert.mp ht with rfl | ht
      · exact Finset.mem_image.mpr ⟨b, Finset.mem_univ b, rfl⟩
      · rw [hTdef] at ht
        obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp ht
        exact Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩
    · intro ht
      obtain ⟨l, _, rfl⟩ := Finset.mem_image.mp ht
      by_cases hlb : l = b
      · subst hlb
        exact Finset.mem_insert_self _ _
      · exact Finset.mem_insert_of_mem (by
          rw [hTdef]
          exact Finset.mem_image.mpr
            ⟨l, Finset.mem_filter.mpr ⟨Finset.mem_univ l, hlb⟩, rfl⟩)
  have hgen : ConjGenerates refl36 (insert (g b) T) := by
    rw [hins_eq]
    exact hConj
  have hshape := shape_theorem hv5 hvne hT_reflFix hgb hgen
  have hmain : norm6 v = 1 ∧ ConjGenerates (reflFix v) T := by
    rcases hshape with h | h
    · exact h
    · exact absurd h hnorm_v
  obtain ⟨hv1, hgen_fix⟩ := hmain
  set S₀ : Finset Mat6 := (reflFix v).filter fun a => a ∈ Submonoid.closure (T : Set Mat6)
    with hS₀def
  have hSsub : S₀ ⊆ reflFix v := by
    intro a ha
    rw [hS₀def] at ha
    exact (Finset.mem_filter.mp ha).1
  have hSconj : ConjClosed S₀ := by
    intro a ha b hb
    rw [hS₀def] at ha hb ⊢
    obtain ⟨haU, haC⟩ := Finset.mem_filter.mp ha
    obtain ⟨hbU, hbC⟩ := Finset.mem_filter.mp hb
    refine Finset.mem_filter.mpr ⟨?_, ?_⟩
    · rw [reflFix, Finset.mem_filter] at haU hbU ⊢
      exact ⟨refl36_conj_mem haU.1 hbU.1, by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, haU.2, hbU.2, haU.2]⟩
    · exact Submonoid.mul_mem _ (Submonoid.mul_mem _ haC hbC) haC
  have hTS : T ⊆ S₀ := by
    intro a ha
    rw [hS₀def]
    exact Finset.mem_filter.mpr ⟨hT_reflFix ha, Submonoid.subset_closure ha⟩
  have hS_eq : S₀ = reflFix v := hgen_fix S₀ hSsub hSconj hTS
  have hclosure : ∀ t ∈ reflFix v, t ∈ Submonoid.closure (T : Set Mat6) := by
    intro t ht
    have htS₀ : t ∈ S₀ := by
      rw [hS_eq]
      exact ht
    rw [hS₀def] at htS₀
    exact (Finset.mem_filter.mp htS₀).2
  obtain ⟨w₁, hw₁⟩ := norm1_perp_orbit_WL v hv1 hv5
  have hxs_norm : norm6 xs = 1 := by decide +kernel
  have hxs5 : xs 5 = 0 := by decide +kernel
  obtain ⟨w₂, hw₂⟩ := norm1_perp_orbit_WL xs hxs_norm hxs5
  set w₀ : List (Fin 6) := w₂ ++ w₁.reverse with hw₀
  set k₀ : Mat6 := evalWord gensL w₀ with hk₀
  set k₀' : Mat6 := evalWord gensL w₀.reverse with hk₀'
  have hk0_mem : k₀ ∈ closureL := by
    rw [hk₀]
    exact evalWord_gensL_mem w₀
  have hk0k0' : k₀ * k₀' = 1 := by
    rw [hk₀, hk₀']
    exact (evalWord_gensL_mul_reverse w₀).1
  have hk0'k0 : k₀' * k₀ = 1 := by
    rw [hk₀', hk₀]
    exact (evalWord_gensL_mul_reverse w₀).2
  have hk0_v : k₀.mulVec v = xs := by
    rw [hk₀, hw₀, evalWord_append, ← Matrix.mulVec_mulVec]
    have hA1rev : (evalWord gensL w₁.reverse).mulVec v = hB := by
      rw [← hw₁, Matrix.mulVec_mulVec, (evalWord_gensL_mul_reverse w₁).2, Matrix.one_mulVec]
    rw [hA1rev, hw₂]
  have hk0'_xs : k₀'.mulVec xs = v := by
    rw [← hk0_v, Matrix.mulVec_mulVec, hk0'k0, Matrix.one_mulVec]
  obtain ⟨ι', hι'b, hι'coord⟩ := ggE6DepCoord_change hι (k := k₀) hk0_mem
  have hxx_eq : (xx : Vec6) = Pi.single 5 (1 : ZMod 3) := by decide +kernel
  have hι_y : ι' (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) = xs + c₀ • xx := by
    rw [hι'b ⟨y, hyBs⟩, hw_eq, Matrix.mulVec_add, Matrix.mulVec_smul, hk0_v,
      closureL_mulVec_single5 hk0_mem, hxx_eq]
  have haux : ∀ m ∈ Submonoid.closure (T : Set Mat6),
      ∃ φ ∈ Subgroup.closure (Set.range fun l : {l : Λ // l ≠ b} => ρ l),
        ActsAs ι φ m := by
    intro m hm
    induction hm using Submonoid.closure_induction with
    | mem x hx =>
        have hxT : x ∈ T := by simpa using hx
        rw [hTdef] at hxT
        obtain ⟨l, hl, rfl⟩ := Finset.mem_image.mp hxT
        rw [Finset.mem_filter] at hl
        exact ⟨ρ l, Subgroup.subset_closure ⟨⟨l, hl.2⟩, rfl⟩, (hpart1 l).2⟩
    | one => exact ⟨1, Subgroup.one_mem _, ActsAs.one ι⟩
    | mul x y _ _ ihx ihy =>
        obtain ⟨φx, hφx, hactx⟩ := ihx
        obtain ⟨φy, hφy, hacty⟩ := ihy
        exact ⟨φx * φy, Subgroup.mul_mem _ hφx hφy, ActsAs.mul hactx hacty⟩
  refine ⟨ι', c₀, fun l => k₀ * g l * k₀', hι'coord, hι_y, ?_, ?_, ?_⟩
  · intro l
    exact ⟨by
        rw [hk₀, hk₀']
        exact evalWord_conj_refl36 (hpart1 l).1 w₀,
      actsAs_conj_of_coord hι'b hk0'k0 (hpart1 l).2⟩
  · intro l hl
    have hgl := hfix l hl
    rw [reflFix, Finset.mem_filter] at hgl
    rw [reflFix, Finset.mem_filter]
    refine ⟨?_, ?_⟩
    · rw [hk₀, hk₀']
      exact evalWord_conj_refl36 hgl.1 w₀
    · rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hk0'_xs, hgl.2, hk0_v]
  · intro i
    have hgS := gS_mem_reflFix_xs_all i
    rw [reflFix, Finset.mem_filter] at hgS
    set t : Mat6 := k₀' * gS i * k₀ with ht_def
    have ht_refl : t ∈ refl36 := by
      rw [ht_def, hk₀', hk₀]
      simpa [List.reverse_reverse] using
        evalWord_conj_refl36 (t := gS i) hgS.1 w₀.reverse
    have ht_fix : t.mulVec v = v := by
      rw [ht_def, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hk0_v, hgS.2, hk0'_xs]
    have ht_cl : t ∈ Submonoid.closure (T : Set Mat6) :=
      hclosure t (Finset.mem_filter.mpr ⟨ht_refl, ht_fix⟩)
    obtain ⟨φ, hφmem, hφact⟩ := haux t ht_cl
    refine ⟨φ, hφmem, ?_⟩
    have hconj := actsAs_conj_of_coord (k := k₀) (k' := k₀') hι'b hk0'k0 hφact
    have ht_eq : k₀ * t * k₀' = gS i := by
      rw [ht_def]
      calc
        k₀ * (k₀' * gS i * k₀) * k₀' = (k₀ * k₀') * gS i * (k₀ * k₀') := by ac_rfl
        _ = gS i := by rw [hk0k0', one_mul, mul_one]
    rwa [ht_eq] at hconj

end E6Dep

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGE6DepModelRefl36
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelActs
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelCoord
public import CFSG.LocalAnalysis.StandardType.GGE6DepCorootDefs
public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelOrbit

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

private theorem actsAs_eq_of {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6} {φ : MulAut ↥Bs}
    {g h : Mat6} (hg : ActsAs ι φ g) (hh : ActsAs ι φ h) : g = h := by
  have key : ∀ v : Vec6, g.mulVec v = h.mulVec v := by
    intro v
    have hgv := hg (Additive.toMul (ι.symm v))
    have hhv := hh (Additive.toMul (ι.symm v))
    simp only [ofMul_toMul, AddEquiv.apply_symm_apply] at hgv hhv
    rw [← hgv, ← hhv]
  refine Matrix.ext fun i j => ?_
  have := congrFun (key (Pi.single j (1 : ZMod 3))) i
  simpa [Matrix.mulVec_single_one] using this

private theorem actsAs_card_fixed {Bs : Subgroup G} {ι : Additive ↥Bs ≃+ Vec6}
    {φ : MulAut ↥Bs} {g : Mat6} (h : ActsAs ι φ g) :
    Nat.card {b : ↥Bs // φ b = b} = Nat.card {v : Vec6 // g.mulVec v = v} := by
  have hfix : ∀ b : ↥Bs, (φ b = b) ↔ g.mulVec (ι (Additive.ofMul b)) = ι (Additive.ofMul b) := by
    intro b
    rw [← h b]
    exact ⟨fun hb => by rw [hb], fun hb => Additive.ofMul.injective (ι.injective hb)⟩
  exact Nat.card_congr (Equiv.subtypeEquiv (Additive.ofMul.trans ι.toEquiv) hfix)

private theorem gensL_mulVec_xx (i : Fin 6) :
    (gensL i).mulVec (Pi.single 5 (1 : ZMod 3)) = Pi.single 5 (1 : ZMod 3) := by
  revert i
  decide +kernel

private theorem closureL_mulVec_xx {g : Mat6} (hg : g ∈ closureL) :
    g.mulVec (Pi.single 5 (1 : ZMod 3)) = Pi.single 5 (1 : ZMod 3) := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact gensL_mulVec_xx i
  | one => exact Matrix.one_mulVec _
  | mul g h _ _ ihg ihh => rw [← Matrix.mulVec_mulVec, ihh, ihg]

theorem ggE6Dep_extract {Bs L : Subgroup G} {x y : G} (hxBs : x ∈ Bs) (hyBs : y ∈ Bs)
    (hxy : y ∉ Subgroup.zpowers x) {ι : Additive ↥Bs ≃+ Vec6}
    (hι : ι (Additive.ofMul ⟨x, hxBs⟩) = Pi.single 5 1)
    (hfr₁ : ∀ φ ∈ ggAutomizer L Bs, ∃ g ∈ closureL, ActsAs ι φ g)
    (hfr₂ : ∀ g ∈ closureL, ∃ φ ∈ ggAutomizer L Bs, ActsAs ι φ g)
    (hR : ∀ T ∈ closureL, T * T = 1 →
      Fintype.card {v : Vec6 // T.mulVec v = v} * 3 = 3 ^ 6 → T ∈ refl36)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (b : Λ) (ρ : Λ → MulAut ↥Bs)
    (hρrefl : ∀ l, GGIsReflection 3 (ρ l))
    (hLgen : ggAutomizer L Bs = Subgroup.closure (Set.range ρ))
    (hρy : ∀ l : Λ, l ≠ b → ρ l ⟨y, hyBs⟩ = ⟨y, hyBs⟩) :
    ∃ (g : Λ → Mat6) (v : Vec6) (c : ZMod 3),
      (∀ l, g l ∈ refl36 ∧ ActsAs ι (ρ l) (g l)) ∧
      v 5 = 0 ∧ v ≠ 0 ∧ ι (Additive.ofMul ⟨y, hyBs⟩) = v + c • Pi.single 5 1 ∧
      (∀ l, l ≠ b → g l ∈ reflFix v) ∧ ConjGenerates refl36 (Finset.univ.image g) := by
  classical
  have hmem_aut : ∀ l : Λ, ρ l ∈ ggAutomizer L Bs := by
    intro l
    rw [hLgen]
    exact Subgroup.subset_closure ⟨l, rfl⟩
  choose g hgmem hgact using fun l => hfr₁ (ρ l) (hmem_aut l)
  have hρ2 : ∀ l, ρ l ^ 2 = 1 := fun l => (hρrefl l).1
  have hg2 : ∀ l, g l * g l = 1 := by
    intro l
    have h1 : ActsAs ι (ρ l * ρ l) (g l * g l) := ActsAs.mul (hgact l) (hgact l)
    rw [show ρ l * ρ l = 1 from by rw [← pow_two]; exact hρ2 l] at h1
    exact actsAs_eq_of h1 (ActsAs.one ι)
  have natCard_Bs : Nat.card ↥Bs = 3 ^ 6 := by
    rw [card_eq_of_ggLin ι, Nat.card_fun (α := Fin 6) (β := ZMod 3), Nat.card_zmod,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hcard : ∀ l, Fintype.card {v : Vec6 // (g l).mulVec v = v} * 3 = 3 ^ 6 := by
    intro l
    have h1 := (hρrefl l).2
    rw [actsAs_card_fixed (hgact l)] at h1
    have h2 : Nat.card {v : Vec6 // (g l).mulVec v = v} =
        Fintype.card {v : Vec6 // (g l).mulVec v = v} := Nat.card_eq_fintype_card
    rw [h2, natCard_Bs] at h1
    exact h1
  have hrefl : ∀ l, g l ∈ refl36 := fun l => hR (g l) (hgmem l) (hg2 l) (hcard l)
  have hpart1 : ∀ l, g l ∈ refl36 ∧ ActsAs ι (ρ l) (g l) := fun l => ⟨hrefl l, hgact l⟩
  set w : Vec6 := ι (Additive.ofMul ⟨y, hyBs⟩) with hwdef
  set c : ZMod 3 := w 5 with hcdef
  set v : Vec6 := w - c • Pi.single 5 (1 : ZMod 3) with hvdef
  have hv5 : v 5 = 0 := by
    rw [hvdef, hcdef]
    simp [Pi.single_eq_same]
  have hw_eq : ι (Additive.ofMul ⟨y, hyBs⟩) = v + c • Pi.single 5 1 := by
    rw [hvdef, sub_add_cancel, hwdef]
  have hvne : v ≠ 0 := by
    intro hv0
    have hw : w = c • Pi.single 5 (1 : ZMod 3) := by
      rw [hvdef] at hv0
      exact sub_eq_zero.mp hv0
    set k : ℕ := c.val with hkdef
    have hk : (k : ZMod 3) = c := by
      rw [hkdef]
      exact ZMod.natCast_zmod_val c
    have hwx : ι (Additive.ofMul ⟨y, hyBs⟩) = ι (k • Additive.ofMul (⟨x, hxBs⟩ : ↥Bs)) := by
      rw [← hwdef, hw, ← hι, ← hk, Nat.cast_smul_eq_nsmul]
      exact (map_nsmul ι k (Additive.ofMul (⟨x, hxBs⟩ : ↥Bs))).symm
    have hsub : Additive.ofMul ⟨y, hyBs⟩ = k • Additive.ofMul (⟨x, hxBs⟩ : ↥Bs) :=
      ι.injective hwx
    have hmem : (⟨y, hyBs⟩ : ↥Bs) = (⟨x, hxBs⟩ : ↥Bs) ^ k := by
      have h := congrArg Additive.toMul hsub
      simpa [toMul_nsmul] using h
    have hy_eq : y = x ^ k := by
      have h := congrArg (fun z : ↥Bs => (z : G)) hmem
      simpa using h
    rw [hy_eq] at hxy
    exact hxy (Subgroup.npow_mem_zpowers x k)
  have hfix : ∀ l, l ≠ b → g l ∈ reflFix v := by
    intro l hl
    rw [reflFix, Finset.mem_filter]
    refine ⟨hrefl l, ?_⟩
    have hgw : (g l).mulVec w = w := by
      rw [hwdef, ← hgact l ⟨y, hyBs⟩, hρy l hl]
    have hgx : (g l).mulVec (Pi.single 5 (1 : ZMod 3)) = Pi.single 5 (1 : ZMod 3) :=
      closureL_mulVec_xx (hgmem l)
    rw [hvdef]
    rw [Matrix.mulVec_sub, Matrix.mulVec_smul, hgw, hgx]
  have hTimg_sub : (Finset.univ.image g : Finset Mat6) ⊆ refl36 := by
    intro t ht
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp ht
    exact hrefl l
  have hclosSM : (Subgroup.closure (Set.range ρ)).toSubmonoid = Submonoid.closure (Set.range ρ) :=
    Subgroup.closure_toSubmonoid_of_isOfFinOrder (fun x hx => by
      obtain ⟨l, rfl⟩ := hx
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hρ2 l⟩)
  have haux : ∀ φ ∈ Submonoid.closure (Set.range ρ),
      ∃ m ∈ Submonoid.closure ((Finset.univ.image g : Finset Mat6) : Set Mat6),
        ActsAs ι φ m := by
    intro φ hφ
    induction hφ using Submonoid.closure_induction with
    | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        exact ⟨g l, Submonoid.subset_closure
          (show g l ∈ (Finset.univ.image g : Finset Mat6) from
            Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩), hgact l⟩
    | one => exact ⟨1, Submonoid.one_mem _, ActsAs.one ι⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨m, hm, hmact⟩ := ihx
        obtain ⟨n, hn, hnact⟩ := ihy
        exact ⟨m * n, Submonoid.mul_mem _ hm hn, ActsAs.mul hmact hnact⟩
  have hgen_mem : ∀ i : Fin 6, gensL i ∈
      Submonoid.closure ((Finset.univ.image g : Finset Mat6) : Set Mat6) := by
    intro i
    obtain ⟨φ, hφaut, hφact⟩ := hfr₂ (gensL i) (Submonoid.subset_closure ⟨i, rfl⟩)
    have hφsub : φ ∈ Subgroup.closure (Set.range ρ) := by
      rw [hLgen] at hφaut
      exact hφaut
    have hφsm : φ ∈ Submonoid.closure (Set.range ρ) := by
      rw [← hclosSM]
      exact hφsub
    obtain ⟨m, hm, hmact⟩ := haux φ hφsm
    have hm_eq : m = gensL i := actsAs_eq_of hmact hφact
    rwa [hm_eq] at hm
  have hclos : Submonoid.closure ((Finset.univ.image g : Finset Mat6) : Set Mat6) = closureL := by
    refine le_antisymm ?_ ?_
    · rw [Submonoid.closure_le]
      intro t ht
      obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp ht
      exact hgmem l
    · change Submonoid.closure (Set.range gensL) ≤
        Submonoid.closure ((Finset.univ.image g : Finset Mat6) : Set Mat6)
      rw [Submonoid.closure_le]
      rintro t ⟨i, rfl⟩
      exact hgen_mem i
  have hConj : ConjGenerates refl36 (Finset.univ.image g) :=
    (closure_eq_closureL_iff hTimg_sub).mp hclos
  exact ⟨g, v, c, hpart1, hv5, hvne, hw_eq, hfix, hConj⟩

end E6Dep

end CFSG.StandardType

end

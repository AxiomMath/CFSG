module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKRefl
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelRefl36
public import CFSG.LocalAnalysis.StandardType.GGE6DepStdFrame

public section

namespace CFSG.StandardType

namespace E6Dep

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {G : Type} [Group G]

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

private theorem actsAsK_eq_of {Bs : Subgroup G} {κ : Additive ↥Bs →+ Vec6}
    (hH : ∀ v : Vec6, v 5 = 0 → ∃ b : ↥Bs, κ (Additive.ofMul b) = v)
    {φ : MulAut ↥Bs} {g h : Mat6} (hg : g ∈ closureL) (hh : h ∈ closureL)
    (hgact : ActsAsK κ φ g) (hhact : ActsAsK κ φ h) : g = h := by
  have key : ∀ v : Vec6, g.mulVec v = h.mulVec v := by
    intro v
    have hv5 : hpart v 5 = 0 := by
      simp [hpart, Pi.single_eq_same]
    obtain ⟨b, hb⟩ := hH (hpart v) hv5
    have hgb : g.mulVec (hpart v) = h.mulVec (hpart v) := by
      rw [← hb, ← hgact b, hhact b]
    have hge : g.mulVec (Pi.single 5 (1 : ZMod 3)) = Pi.single 5 (1 : ZMod 3) :=
      closureL_mulVec_xx hg
    have hhe : h.mulVec (Pi.single 5 (1 : ZMod 3)) = Pi.single 5 (1 : ZMod 3) :=
      closureL_mulVec_xx hh
    have hv : hpart v + (v 5) • Pi.single 5 (1 : ZMod 3) = v := by
      simp only [hpart]
      exact sub_add_cancel v (v 5 • Pi.single 5 (1 : ZMod 3))
    calc
      g.mulVec v = g.mulVec (hpart v + (v 5) • Pi.single 5 (1 : ZMod 3)) :=
            (congrArg (fun w => g.mulVec w) hv).symm
      _ = g.mulVec (hpart v) + (v 5) • g.mulVec (Pi.single 5 (1 : ZMod 3)) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = h.mulVec (hpart v) + (v 5) • h.mulVec (Pi.single 5 (1 : ZMod 3)) := by
            rw [hgb, hge, hhe]
      _ = h.mulVec (hpart v + (v 5) • Pi.single 5 (1 : ZMod 3)) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = h.mulVec v := congrArg (fun w => h.mulVec w) hv
  refine Matrix.ext fun i j => ?_
  have := congrFun (key (Pi.single j (1 : ZMod 3))) i
  simpa [Matrix.mulVec_single_one] using this

theorem ggE6Dep_extractK {Bs X : Subgroup G} {y : G} (hyBs : y ∈ Bs) (hy1 : y ≠ 1)
    (hy3 : y ^ 3 = 1) (hcardBs : Nat.card Bs = 3 ^ 6) {κ : Additive ↥Bs →+ Vec6} (hκ : GGE6DepKFrame Bs X y κ)
    {Λ : Type} [Fintype Λ] [DecidableEq Λ] (ρ : Λ → MulAut ↥Bs)
    (hρrefl : ∀ l, GGIsReflection 3 (ρ l)) (hρy : ∀ l, ρ l ⟨y, hyBs⟩ = ⟨y, hyBs⟩)
    (hgen : ggAutomizer X Bs = Subgroup.closure (Set.range ρ)) :
    ∃ g : Λ → Mat6, (∀ l, g l ∈ refl36 ∧ ActsAsK κ (ρ l) (g l)) ∧
      ConjGenerates refl36 (Finset.univ.image g) := by
  classical
  have hH : ∀ v : Vec6, v 5 = 0 → ∃ b : ↥Bs, κ (Additive.ofMul b) = v := hκ.2.2.1
  have hmem_aut : ∀ l : Λ, ρ l ∈ ggAutomizer X Bs := by
    intro l
    rw [hgen]
    exact Subgroup.subset_closure ⟨l, rfl⟩
  choose g hgmem hgact using fun l => hκ.2.2.2.1 (ρ l) (hmem_aut l)
  have hρ2 : ∀ l, ρ l ^ 2 = 1 := fun l => (hρrefl l).1
  have hrefl : ∀ l, g l ∈ refl36 := fun l =>
    ggE6Dep_frameK_refl hyBs hy1 hy3 hcardBs hκ (hρrefl l) (hρy l) (hgmem l) (hgact l)
  have hpart1 : ∀ l, g l ∈ refl36 ∧ ActsAsK κ (ρ l) (g l) := fun l => ⟨hrefl l, hgact l⟩
  have hTimg_sub : (Finset.univ.image g : Finset Mat6) ⊆ refl36 := by
    intro t ht
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp ht
    exact hrefl l
  have hclos_le : Submonoid.closure ((Finset.univ.image g : Finset Mat6) : Set Mat6) ≤ closureL := by
    rw [Submonoid.closure_le]
    intro t ht
    obtain ⟨l, -, rfl⟩ := Finset.mem_image.mp ht
    exact hgmem l
  have hclosSM : (Subgroup.closure (Set.range ρ)).toSubmonoid = Submonoid.closure (Set.range ρ) :=
    Subgroup.closure_toSubmonoid_of_isOfFinOrder (fun x hx => by
      obtain ⟨l, rfl⟩ := hx
      exact isOfFinOrder_iff_pow_eq_one.mpr ⟨2, by decide, hρ2 l⟩)
  have haux : ∀ φ ∈ Submonoid.closure (Set.range ρ),
      ∃ m ∈ Submonoid.closure ((Finset.univ.image g : Finset Mat6) : Set Mat6),
        ActsAsK κ φ m := by
    intro φ hφ
    induction hφ using Submonoid.closure_induction with
    | mem x hx =>
        obtain ⟨l, rfl⟩ := hx
        exact ⟨g l, Submonoid.subset_closure
          (show g l ∈ (Finset.univ.image g : Finset Mat6) from
            Finset.mem_image.mpr ⟨l, Finset.mem_univ l, rfl⟩), hgact l⟩
    | one => exact ⟨1, Submonoid.one_mem _, ActsAsK.one κ⟩
    | mul x y hx hy ihx ihy =>
        obtain ⟨m, hm, hmact⟩ := ihx
        obtain ⟨n, hn, hnact⟩ := ihy
        exact ⟨m * n, Submonoid.mul_mem _ hm hn, ActsAsK.mul hmact hnact⟩
  have hgen_mem : ∀ i : Fin 6, gensL i ∈
      Submonoid.closure ((Finset.univ.image g : Finset Mat6) : Set Mat6) := by
    intro i
    obtain ⟨φ, hφaut, hφact⟩ := hκ.2.2.2.2 (gensL i) (Submonoid.subset_closure ⟨i, rfl⟩)
    have hφsub : φ ∈ Subgroup.closure (Set.range ρ) := by
      rw [hgen] at hφaut
      exact hφaut
    have hφsm : φ ∈ Submonoid.closure (Set.range ρ) := by
      rw [← hclosSM]
      exact hφsub
    obtain ⟨m, hm, hmact⟩ := haux φ hφsm
    have hm_eq : m = gensL i :=
      actsAsK_eq_of hH (hclos_le hm) (Submonoid.subset_closure ⟨i, rfl⟩) hmact hφact
    rwa [hm_eq] at hm
  have hclos : Submonoid.closure ((Finset.univ.image g : Finset Mat6) : Set Mat6) = closureL := by
    refine le_antisymm hclos_le ?_
    · change Submonoid.closure (Set.range gensL) ≤
        Submonoid.closure ((Finset.univ.image g : Finset Mat6) : Set Mat6)
      rw [Submonoid.closure_le]
      rintro t ⟨i, rfl⟩
      exact hgen_mem i
  have hConj : ConjGenerates refl36 (Finset.univ.image g) :=
    (closure_eq_closureL_iff hTimg_sub).mp hclos
  exact ⟨g, hpart1, hConj⟩

end E6Dep

end CFSG.StandardType

end

module

public import CFSG.LocalAnalysis.StandardType.GGE6DepKDefs
public import CFSG.LocalAnalysis.StandardType.GGE6DepKRefl
public import CFSG.LocalAnalysis.StandardType.GGE6DepKAut
public import CFSG.LocalAnalysis.StandardType.GGE6DepPerpDefs
public import CFSG.LocalAnalysis.StandardType.GGTPChain
public import CFSG.LocalAnalysis.StandardType.GGTPDatumLift
public import CFSG.LocalAnalysis.StandardType.GGE6DepKMatrix
public import CFSG.LocalAnalysis.StandardType.GGE6DepKNoTv
public import CFSG.LocalAnalysis.StandardType.GGE6DepModelRefl36

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem ggTP_actsAs_fst_inj {G : Type} [Group G] {Bs : Subgroup G}
    {ι : Additive ↥Bs ≃+ E6Dep.Vec6} {φ ψ : MulAut ↥Bs} {g : E6Dep.Mat6}
    (hφ : E6Dep.ActsAs ι φ g) (hψ : E6Dep.ActsAs ι ψ g) : φ = ψ := by
  refine MulEquiv.ext fun b => ?_
  exact Additive.ofMul.injective (ι.injective (by rw [hφ b, hψ b]))

private theorem ggTP_ActsAs_pow {G : Type} [Group G] {Bs : Subgroup G}
    {ι : Additive ↥Bs ≃+ E6Dep.Vec6} {φ : MulAut ↥Bs} {g : E6Dep.Mat6}
    (h : E6Dep.ActsAs ι φ g) (n : ℕ) : E6Dep.ActsAs ι (φ ^ n) (g ^ n) := by
  induction n with
  | zero => simpa using E6Dep.ActsAs.one ι
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact E6Dep.ActsAs.mul ih h

private theorem ggTP_ActsAsK_pow {G : Type} [Group G] {Bs : Subgroup G}
    {κ : Additive ↥Bs →+ E6Dep.Vec6} {φ : MulAut ↥Bs} {g : E6Dep.Mat6}
    (h : E6Dep.ActsAsK κ φ g) (n : ℕ) : E6Dep.ActsAsK κ (φ ^ n) (g ^ n) := by
  induction n with
  | zero => simpa using E6Dep.ActsAsK.one κ
  | succ n ih =>
      rw [pow_succ, pow_succ]
      exact E6Dep.ActsAsK.mul ih h

private theorem ggTP_fin6_ne_five_lt {node : Fin 6} (h : node ≠ 5) : node.val < 5 := by
  have hle : node.val ≤ 5 := Nat.le_of_lt_succ node.isLt
  rcases lt_or_eq_of_le hle with hlt | heq
  · exact hlt
  · exact absurd (Fin.ext (by simpa using heq)) h

private theorem ggTP_gensL_mulVec_single5 (i : Fin 6) :
    (E6Dep.gensL i).mulVec (Pi.single 5 (1 : ZMod 3) : E6Dep.Vec6) =
      Pi.single 5 (1 : ZMod 3) := by
  revert i
  decide +kernel

private theorem ggTP_closureL_mulVec_single5 {g : E6Dep.Mat6} (hg : g ∈ E6Dep.closureL) :
    g.mulVec (Pi.single 5 (1 : ZMod 3) : E6Dep.Vec6) = Pi.single 5 (1 : ZMod 3) := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
      obtain ⟨i, rfl⟩ := hg
      exact ggTP_gensL_mulVec_single5 i
  | one => exact Matrix.one_mulVec _
  | mul g h _ _ ihg ihh => rw [← Matrix.mulVec_mulVec, ihh, ihg]

private theorem ggTP_closureL_pow_mem {m : E6Dep.Mat6} (hm : m ∈ E6Dep.closureL) (n : ℕ) :
    m ^ n ∈ E6Dep.closureL := by
  induction n with
  | zero => simpa using Submonoid.one_mem E6Dep.closureL
  | succ n ih => rw [pow_succ]; exact Submonoid.mul_mem _ ih hm

private theorem ggTP_actsAsK_eq_of {G : Type} [Group G] {Bs : Subgroup G}
    {κ : Additive ↥Bs →+ E6Dep.Vec6}
    (hH : ∀ v : E6Dep.Vec6, v 5 = 0 → ∃ b : ↥Bs, κ (Additive.ofMul b) = v)
    {φ : MulAut ↥Bs} {g h : E6Dep.Mat6} (hg : g ∈ E6Dep.closureL) (hh : h ∈ E6Dep.closureL)
    (hgact : E6Dep.ActsAsK κ φ g) (hhact : E6Dep.ActsAsK κ φ h) : g = h := by
  have key : ∀ v : E6Dep.Vec6, g.mulVec v = h.mulVec v := by
    intro v
    have hv5 : E6Dep.hpart v 5 = 0 := by simp [E6Dep.hpart, Pi.single_eq_same]
    obtain ⟨b, hb⟩ := hH (E6Dep.hpart v) hv5
    have hgb : g.mulVec (E6Dep.hpart v) = h.mulVec (E6Dep.hpart v) := by
      rw [← hb, ← hgact b, hhact b]
    have hge : g.mulVec (Pi.single 5 (1 : ZMod 3) : E6Dep.Vec6) = Pi.single 5 (1 : ZMod 3) :=
      ggTP_closureL_mulVec_single5 hg
    have hhe : h.mulVec (Pi.single 5 (1 : ZMod 3) : E6Dep.Vec6) = Pi.single 5 (1 : ZMod 3) :=
      ggTP_closureL_mulVec_single5 hh
    have hdecomp : v = E6Dep.hpart v + (v 5) • (Pi.single 5 (1 : ZMod 3) : E6Dep.Vec6) := by
      simp only [E6Dep.hpart]
      exact (sub_add_cancel v (v 5 • Pi.single 5 (1 : ZMod 3))).symm
    calc
      g.mulVec v = g.mulVec (E6Dep.hpart v + (v 5) • (Pi.single 5 (1 : ZMod 3) : E6Dep.Vec6)) := by
            conv_lhs => rw [hdecomp]
      _ = g.mulVec (E6Dep.hpart v) + (v 5) • g.mulVec (Pi.single 5 (1 : ZMod 3) : E6Dep.Vec6) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = h.mulVec (E6Dep.hpart v) + (v 5) • h.mulVec (Pi.single 5 (1 : ZMod 3) : E6Dep.Vec6) := by
            simp only [hgb, hge, hhe]
      _ = h.mulVec (E6Dep.hpart v + (v 5) • (Pi.single 5 (1 : ZMod 3) : E6Dep.Vec6)) := by
            rw [Matrix.mulVec_add, Matrix.mulVec_smul]
      _ = h.mulVec v := by rw [← hdecomp]
  refine Matrix.ext fun i j => ?_
  have := congrFun (key (Pi.single j (1 : ZMod 3))) i
  simpa [Matrix.mulVec_single_one] using this

private theorem ggTP_gen_of_acts {G : Type} [Group G] {Bs X : Subgroup G}
    {ι : Additive ↥Bs ≃+ E6Dep.Vec6}
    (hfr₁ : ∀ φ ∈ ggAutomizer X Bs, ∃ g ∈ E6Dep.closureL, E6Dep.ActsAs ι φ g)
    {Idx : Type*} (ρ : Idx → MulAut ↥Bs) (g : Idx → E6Dep.Mat6)
    (hρmem : ∀ i, ρ i ∈ ggAutomizer X Bs)
    (hρg : ∀ i, E6Dep.ActsAs ι (ρ i) (g i))
    (hgen : Submonoid.closure (Set.range g) = E6Dep.closureL) :
    ggAutomizer X Bs = Subgroup.closure (Set.range ρ) := by
  refine le_antisymm ?_ ?_
  · intro φ hφ
    obtain ⟨m, hm, hmact⟩ := hfr₁ φ hφ
    have haux : ∀ m ∈ E6Dep.closureL, ∃ ψ ∈ Subgroup.closure (Set.range ρ),
        E6Dep.ActsAs ι ψ m := by
      intro m hm
      rw [← hgen] at hm
      induction hm using Submonoid.closure_induction with
      | mem x hx =>
          obtain ⟨i, rfl⟩ := hx
          exact ⟨ρ i, Subgroup.subset_closure ⟨i, rfl⟩, hρg i⟩
      | one => exact ⟨1, Subgroup.one_mem _, E6Dep.ActsAs.one ι⟩
      | mul x y hx hy ihx ihy =>
          obtain ⟨ψx, hψx, hactx⟩ := ihx
          obtain ⟨ψy, hψy, hacty⟩ := ihy
          exact ⟨ψx * ψy, Subgroup.mul_mem _ hψx hψy, E6Dep.ActsAs.mul hactx hacty⟩
    obtain ⟨ψ, hψ, hψact⟩ := haux m hm
    have hψφ : ψ = φ := ggTP_actsAs_fst_inj hψact hmact
    rw [hψφ] at hψ
    exact hψ
  · rw [Subgroup.closure_le]
    intro φ hφ
    obtain ⟨i, rfl⟩ := hφ
    exact hρmem i

private theorem ggTP_gen_of_actsK {G : Type} [Group G] {Bs K' : Subgroup G} {y' : G}
    (hy'Bs : y' ∈ Bs) (hy'1 : y' ≠ 1) (hBs : IsElemAbelian 3 Bs)
    (hnt : GGNoTransvection 3 Bs)
    (hKy' : K' ≤ Subgroup.centralizer ({y'} : Set G))
    {κ : Additive ↥Bs →+ E6Dep.Vec6} (hκ : E6Dep.GGE6DepKFrame Bs K' y' κ)
    {Idx : Type*} (ρ : Idx → MulAut ↥Bs) (g : Idx → E6Dep.Mat6)
    (hρmem : ∀ i, ρ i ∈ ggAutomizer K' Bs)
    (hρg : ∀ i, E6Dep.ActsAsK κ (ρ i) (g i))
    (hgen : Submonoid.closure (Set.range g) = E6Dep.closureL) :
    ggAutomizer K' Bs = Subgroup.closure (Set.range ρ) := by
  refine le_antisymm ?_ ?_
  · intro ψ hψ
    obtain ⟨m, hm, hmact⟩ := hκ.2.2.2.1 ψ hψ
    have haux : ∀ m ∈ E6Dep.closureL, ∀ ψ ∈ ggAutomizer K' Bs,
        E6Dep.ActsAsK κ ψ m → ψ ∈ Subgroup.closure (Set.range ρ) := by
      intro m hm
      rw [← hgen] at hm
      induction hm using Submonoid.closure_induction with
      | mem x hx =>
          intro ψ hψ hψx
          obtain ⟨i, rfl⟩ := hx
          have heq : ψ = ρ i :=
            ggTPAutK_inj hy'Bs hy'1 hBs hnt hKy' hκ hψ (hρmem i) hψx (hρg i)
          rw [heq]
          exact Subgroup.subset_closure ⟨i, rfl⟩
      | one =>
          intro ψ hψ hψ1
          have heq : ψ = 1 :=
            ggTPAutK_inj hy'Bs hy'1 hBs hnt hKy' hκ hψ (Subgroup.one_mem _) hψ1
              (E6Dep.ActsAsK.one κ)
          rw [heq]
          exact Subgroup.one_mem _
      | mul x y hx hy ihx ihy =>
          intro ψ hψ hψxy
          have hx' : x ∈ E6Dep.closureL := by rwa [← hgen]
          have hy' : y ∈ E6Dep.closureL := by rwa [← hgen]
          obtain ⟨ψx, hψxmem, hψxact⟩ := hκ.2.2.2.2 x hx'
          obtain ⟨ψy, hψymem, hψyact⟩ := hκ.2.2.2.2 y hy'
          have hxcl : ψx ∈ Subgroup.closure (Set.range ρ) := ihx ψx hψxmem hψxact
          have hycl : ψy ∈ Subgroup.closure (Set.range ρ) := ihy ψy hψymem hψyact
          have heq : ψ = ψx * ψy :=
            ggTPAutK_inj hy'Bs hy'1 hBs hnt hKy' hκ hψ
              (Subgroup.mul_mem _ hψxmem hψymem) hψxy (E6Dep.ActsAsK.mul hψxact hψyact)
          rw [heq]
          exact Subgroup.mul_mem _ hxcl hycl
    exact haux m hm ψ hψ hmact
  · rw [Subgroup.closure_le]
    intro φ hφ
    obtain ⟨i, rfl⟩ := hφ
    exact hρmem i

theorem ggTPDatum_of_stab {G : Type} [Group G] {Bs L K' : Subgroup G} {x y y' : G} (hxBs : x ∈ Bs)
    (hyBs : y ∈ Bs) (hy'Bs : y' ∈ Bs) (hy'1 : y' ≠ 1) (hy'3 : y' ^ 3 = 1)
    (hBs : IsElemAbelian 3 Bs) (hcardBs : Nat.card Bs = 3 ^ 6) (hnt : GGNoTransvection 3 Bs)
    (hKy' : K' ≤ Subgroup.centralizer ({y'} : Set G))
    {ι : Additive ↥Bs ≃+ E6Dep.Vec6} (hι : E6Dep.GGE6DepCoord Bs L x hxBs ι)
    (hyι : ι (Additive.ofMul ⟨y, hyBs⟩) = E6Dep.xs) {κ : Additive ↥Bs →+ E6Dep.Vec6}
    (hκ : E6Dep.GGE6DepKFrame Bs K' y' κ)
    (hS : ∀ φ ∈ ggAutomizer L Bs, φ ⟨y, hyBs⟩ = ⟨y, hyBs⟩ → φ ∈ ggAutomizer K' Bs) :
    GGDependentReflectionDatum 3 Bs L K' := by
  classical
  have hgensL_mem : ∀ i : Fin 6, E6Dep.gensL i ∈ E6Dep.closureL :=
    fun i => Submonoid.subset_closure ⟨i, rfl⟩
  let ρ : Fin 6 → MulAut ↥Bs := fun i =>
    Classical.choose (hι.2.2.2 (E6Dep.gensL i) (hgensL_mem i))
  have hρ_mem : ∀ i, ρ i ∈ ggAutomizer L Bs := fun i =>
    (Classical.choose_spec (hι.2.2.2 (E6Dep.gensL i) (hgensL_mem i))).1
  have hρ_act : ∀ i, E6Dep.ActsAs ι (ρ i) (E6Dep.gensL i) := fun i =>
    (Classical.choose_spec (hι.2.2.2 (E6Dep.gensL i) (hgensL_mem i))).2
  have hgensL_mul : ∀ i : Fin 6, E6Dep.gensL i * E6Dep.gensL i = 1 := by decide +kernel
  have hgensL_card : ∀ i : Fin 6,
      Fintype.card {v : E6Dep.Vec6 // (E6Dep.gensL i).mulVec v = v} * 3 = 3 ^ 6 := by
    decide +kernel
  have hρ_refl : ∀ i : Fin 6, GGIsReflection 3 (ρ i) := fun i =>
    E6Dep.ggIsReflection_of_actsAs (hρ_act i) (hgensL_mul i) (hgensL_card i)
  have hgensL_fix_xs : ∀ i : Fin 5, (E6Dep.gensL i.castSucc).mulVec E6Dep.xs = E6Dep.xs := by
    decide +kernel
  have hρ_fix_y : ∀ i : Fin 5, ρ i.castSucc ⟨y, hyBs⟩ = ⟨y, hyBs⟩ := by
    intro i
    have h : ι (Additive.ofMul (ρ i.castSucc ⟨y, hyBs⟩)) =
        ι (Additive.ofMul (⟨y, hyBs⟩ : ↥Bs)) := by
      calc
        ι (Additive.ofMul (ρ i.castSucc ⟨y, hyBs⟩))
            = (E6Dep.gensL i.castSucc).mulVec (ι (Additive.ofMul ⟨y, hyBs⟩)) :=
                hρ_act i.castSucc ⟨y, hyBs⟩
        _ = (E6Dep.gensL i.castSucc).mulVec E6Dep.xs := by rw [hyι]
        _ = E6Dep.xs := hgensL_fix_xs i
        _ = ι (Additive.ofMul ⟨y, hyBs⟩) := hyι.symm
    exact Additive.ofMul.injective (ι.injective h)
  have hρ_K : ∀ i : Fin 5, ρ i.castSucc ∈ ggAutomizer K' Bs := fun i =>
    hS (ρ i.castSucc) (hρ_mem i.castSucc) (hρ_fix_y i)
  let gch : Fin 5 → E6Dep.Mat6 := fun i =>
    Classical.choose (hκ.2.2.2.1 (ρ i.castSucc) (hρ_K i))
  have hgch_mem : ∀ i : Fin 5, gch i ∈ E6Dep.closureL := fun i =>
    (Classical.choose_spec (hκ.2.2.2.1 (ρ i.castSucc) (hρ_K i))).1
  have hgch_act : ∀ i : Fin 5, E6Dep.ActsAsK κ (ρ i.castSucc) (gch i) := fun i =>
    (Classical.choose_spec (hκ.2.2.2.1 (ρ i.castSucc) (hρ_K i))).2
  have hρ_fix_y' : ∀ i : Fin 5, ρ i.castSucc ⟨y', hy'Bs⟩ = ⟨y', hy'Bs⟩ := fun i =>
    E6Dep.ggAutomizer_fix_of_centralizes hy'Bs hKy' (ρ i.castSucc) (hρ_K i)
  have hgch_refl : ∀ i : Fin 5, gch i ∈ E6Dep.refl36 := fun i =>
    E6Dep.ggE6Dep_frameK_refl hy'Bs hy'1 hy'3 hcardBs hκ (hρ_refl i.castSucc)
      (hρ_fix_y' i) (hgch_mem i) (hgch_act i)
  have hcomm_mat : ∀ i j : Fin 5, i.val + 2 ≤ j.val →
      E6Dep.gensL i.castSucc * E6Dep.gensL j.castSucc =
        E6Dep.gensL j.castSucc * E6Dep.gensL i.castSucc := by decide +kernel
  have hbraid_mat : ∀ i j : Fin 5, j.val = i.val + 1 →
      (E6Dep.gensL i.castSucc * E6Dep.gensL j.castSucc) ^ 3 = 1 ∧
        E6Dep.gensL i.castSucc ≠ E6Dep.gensL j.castSucc := by decide +kernel
  have hρ_comm : ∀ i j : Fin 5, i.val + 2 ≤ j.val →
      ρ i.castSucc * ρ j.castSucc = ρ j.castSucc * ρ i.castSucc := by
    intro i j hij
    exact ggTP_actsAs_fst_inj (E6Dep.ActsAs.mul (hρ_act i.castSucc) (hρ_act j.castSucc))
      (by rw [hcomm_mat i j hij]
          exact E6Dep.ActsAs.mul (hρ_act j.castSucc) (hρ_act i.castSucc))
  have hρ_braid : ∀ i j : Fin 5, j.val = i.val + 1 →
      (ρ i.castSucc * ρ j.castSucc) ^ 3 = 1 ∧ ρ i.castSucc ≠ ρ j.castSucc := by
    intro i j hij
    constructor
    · exact ggTP_actsAs_fst_inj
        (ggTP_ActsAs_pow (E6Dep.ActsAs.mul (hρ_act i.castSucc) (hρ_act j.castSucc)) 3)
        (by rw [(hbraid_mat i j hij).1]
            exact E6Dep.ActsAs.one ι)
    · intro heq
      have hmatEq : E6Dep.gensL i.castSucc = E6Dep.gensL j.castSucc :=
        E6Dep.actsAs_inj (hρ_act i.castSucc) (by rw [heq]; exact hρ_act j.castSucc)
      exact (hbraid_mat i j hij).2 hmatEq
  have hgch_comm : ∀ i j : Fin 5, i.val + 2 ≤ j.val → gch i * gch j = gch j * gch i := by
    intro i j hij
    exact ggTP_actsAsK_eq_of hκ.2.2.1
      (Submonoid.mul_mem _ (hgch_mem i) (hgch_mem j))
      (Submonoid.mul_mem _ (hgch_mem j) (hgch_mem i))
      (E6Dep.ActsAsK.mul (hgch_act i) (hgch_act j))
      (by rw [hρ_comm i j hij]
          exact E6Dep.ActsAsK.mul (hgch_act j) (hgch_act i))
  have hgch_braid : ∀ i j : Fin 5, j.val = i.val + 1 →
      (gch i * gch j) ^ 3 = 1 ∧ gch i ≠ gch j := by
    intro i j hij
    constructor
    · have h1 : E6Dep.ActsAsK κ ((ρ i.castSucc * ρ j.castSucc) ^ 3) ((gch i * gch j) ^ 3) :=
        ggTP_ActsAsK_pow (E6Dep.ActsAsK.mul (hgch_act i) (hgch_act j)) 3
      have h2 : E6Dep.ActsAsK κ (1 : MulAut ↥Bs) ((gch i * gch j) ^ 3) := by
        rw [← (hρ_braid i j hij).1]
        exact h1
      exact ggTP_actsAsK_eq_of hκ.2.2.1
        (ggTP_closureL_pow_mem (Submonoid.mul_mem _ (hgch_mem i) (hgch_mem j)) 3)
        (Submonoid.one_mem _) h2 (E6Dep.ActsAsK.one κ)
    · intro heq
      have hρeq : ρ i.castSucc = ρ j.castSucc :=
        ggTPAutK_inj hy'Bs hy'1 hBs hnt hKy' hκ (hρ_K i) (hρ_K j) (hgch_act i)
          (by rw [heq]; exact hgch_act j)
      exact (hρ_braid i j hij).2 hρeq
  obtain ⟨r, hr_refl, hconj⟩ := ggTPA5Chain_completes gch hgch_refl hgch_comm hgch_braid
  have hT_sub : (insert r (Finset.univ.image gch) : Finset E6Dep.Mat6) ⊆ E6Dep.refl36 := by
    intro t ht
    rcases Finset.mem_insert.mp ht with rfl | ht
    · exact hr_refl
    · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp ht
      exact hgch_refl i
  have hclos_chain : Submonoid.closure
      ((insert r (Finset.univ.image gch) : Finset E6Dep.Mat6) : Set E6Dep.Mat6) =
        E6Dep.closureL :=
    (E6Dep.closure_eq_closureL_iff hT_sub).mpr hconj
  obtain ⟨φ', hφ'mem, hφ'act, hφ'refl⟩ :=
    ggTPAutK_lift_refl hy'Bs hy'1 hy'3 hBs hcardBs hnt hKy' hκ hr_refl
  let φ : Option (Fin 6) → MulAut ↥Bs := fun o => match o with
    | none => φ'
    | some i => ρ i
  have hnode_refl : ∀ node : Option (Fin 6), GGIsReflection 3 (φ node) := by
    intro node
    cases node with
    | none => exact hφ'refl
    | some i => exact hρ_refl i
  have hgenL : ggAutomizer L Bs = Subgroup.closure (Set.range ρ) :=
    ggTP_gen_of_acts hι.2.2.1 ρ E6Dep.gensL hρ_mem hρ_act rfl
  let ρK : Option (Fin 5) → MulAut ↥Bs := fun o => match o with
    | none => φ'
    | some i => ρ i.castSucc
  let gK : Option (Fin 5) → E6Dep.Mat6 := fun o => match o with
    | none => r
    | some i => gch i
  have hρKmem : ∀ o, ρK o ∈ ggAutomizer K' Bs := by
    intro o
    cases o with
    | none => exact hφ'mem
    | some i => exact hρ_K i
  have hρKg : ∀ o, E6Dep.ActsAsK κ (ρK o) (gK o) := by
    intro o
    cases o with
    | none => exact hφ'act
    | some i => exact hgch_act i
  have hgK_range : Set.range gK =
      ((insert r (Finset.univ.image gch) : Finset E6Dep.Mat6) : Set E6Dep.Mat6) := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Finset.mem_insert_self _ _
      | some i =>
          exact Finset.mem_insert_of_mem (Finset.mem_image.mpr ⟨i, Finset.mem_univ i, rfl⟩)
    · intro hx
      rcases Finset.mem_insert.mp hx with rfl | hx
      · exact ⟨none, rfl⟩
      · obtain ⟨i, -, rfl⟩ := Finset.mem_image.mp hx
        exact ⟨some i, rfl⟩
  have hgenK_aux : Submonoid.closure (Set.range gK) = E6Dep.closureL := by
    rw [hgK_range]
    exact hclos_chain
  have hgenK' : ggAutomizer K' Bs = Subgroup.closure (Set.range ρK) :=
    ggTP_gen_of_actsK hy'Bs hy'1 hBs hnt hKy' hκ ρK gK hρKmem hρKg hgenK_aux
  have hrangeρK : Set.range ρK =
      Set.range (fun node : {node : Fin 6 // node ≠ 5} => φ (some node)) ∪ {φ none} := by
    ext x
    constructor
    · rintro ⟨o, rfl⟩
      cases o with
      | none => exact Or.inr rfl
      | some i =>
          refine Or.inl ⟨⟨i.castSucc, ?_⟩, rfl⟩
          intro h
          have hv : i.val = 5 := by
            have hh := congrArg Fin.val h
            simpa using hh
          have hlt : i.val < 5 := i.isLt
          rw [hv] at hlt
          exact (Nat.lt_irrefl 5) hlt
    · rintro (hx | hx)
      · obtain ⟨node, rfl⟩ := hx
        refine ⟨some ⟨node.1.val, ?_⟩, ?_⟩
        · exact ggTP_fin6_ne_five_lt node.2
        · show ρ (Fin.castSucc ⟨node.1.val, _⟩) = ρ node.1
          congr 1
      · rw [Set.mem_singleton_iff] at hx
        subst hx
        exact ⟨none, rfl⟩
  have hgenK : ggAutomizer K' Bs = Subgroup.closure
      (Set.range (fun node : {node : Fin 6 // node ≠ 5} => φ (some node)) ∪ {φ none}) := by
    rw [← hrangeρK]
    exact hgenK'
  have hex : ∀ node : Option (Fin 6), ∃ (v : E6Dep.Vec6)
      (f : Module.Dual (ZMod 3) E6Dep.Vec6), f v = 2 ∧
        ∀ w : E6Dep.Vec6, ggLin (p := 3) ι (φ node) w = w - f w • v :=
    fun node => exists_of_ggIsReflection ι (hnode_refl node)
  let hvec : Option (Fin 6) → E6Dep.Vec6 := fun node => Classical.choose (hex node)
  let α : Option (Fin 6) → Module.Dual (ZMod 3) E6Dep.Vec6 :=
    fun node => Classical.choose (Classical.choose_spec (hex node))
  have hαh : ∀ node, α node (hvec node) = 2 :=
    fun node => (Classical.choose_spec (Classical.choose_spec (hex node))).1
  have hlin : ∀ node w, ggLin (p := 3) ι (φ node) w = w - α node w • hvec node :=
    fun node => (Classical.choose_spec (Classical.choose_spec (hex node))).2
  have hne : ∀ node, hvec node ≠ 0 := fun node =>
    (ne_zero_of_apply_eq_two (p := 3) (by norm_num) (hαh node)).1
  have hindep : ¬ LinearIndependent (ZMod 3) hvec := by
    intro hh
    have hc := LinearIndependent.fintype_card_le_finrank (R := ZMod 3) hh
    rw [Fintype.card_option, Fintype.card_fin, Module.finrank_fin_fun] at hc
    omega
  refine ⟨Fin 6, inferInstance, inferInstance, E6Dep.Vec6, inferInstance, inferInstance,
    ι, φ, hvec, α, (5 : Fin 6), hαh, hne, hlin, hindep, ?_, ?_⟩
  · simpa using hgenL
  · rw [← hrangeρK]
    exact hgenK'

end CFSG.StandardType

end

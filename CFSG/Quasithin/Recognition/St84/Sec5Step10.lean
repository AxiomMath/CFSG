module

public import CFSG.Quasithin.Recognition.St84.Sec5Step89
public import CFSG.GroupTheory.SupZpowersIndexTwo
public import CFSG.GroupTheory.PGroup.ExistsNeOneCommute
public import CFSG.GroupTheory.Frattini.MapSubtypeLe
import CFSG.Quasithin.Background.GoldschmidtAmalgamNBasic
import CFSG.Quasithin.Recognition.St84.Gen.MixedCentralZData
import CFSG.Monster.AxisCount.Abstract

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86
  CFSG.Quasithin.F6.GoldAmL3T CFSG.GH74.QTGen4.DSGen4

open scoped Pointwise commutatorElement

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

private theorem n_of_nbr (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (u : Γ.neighborSet (Y.vert 0)) : nOf Γ (u : V) = 1 := by
  have h01 : Γ.Adj (Y.vert 0) (Y.vert 1) := by simpa using Y.adj (0 : ℤ)
  obtain ⟨g, hg, hgu⟩ := L_zero_trans Y (a := Y.vert 1) (b := (u : V)) h01 u.2
  have hs : nOf Γ (g • Y.vert 1) = nOf Γ (Y.vert 1) := Y.hyp.nOf_smul g (Y.vert 1)
  rw [hgu] at hs
  rw [hs]
  exact H.n_one


private def NbrSet (Y : Setup Γ G) (w : Γ.neighborSet (Y.vert 0)) : Set V :=
  Γ.neighborSet (w : V) \ {Y.vert 0}

private theorem ncard_NbrSet (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (w : Γ.neighborSet (Y.vert 0)) : (NbrSet Y w).ncard = 2 := by
  have hn : nOf Γ (w : V) = 1 := n_of_nbr Y H w
  have h := ncard_neighborSet_diff Y.hyp (α := (w : V)) (β := Y.vert 0) w.2.symm
  simpa [NbrSet, hn] using h


private theorem dist_nbr_NbrSet_ne (Y : Setup Γ G)
    {u w : Γ.neighborSet (Y.vert 0)} {v : V} (huw : u ≠ w) (hv : v ∈ NbrSet Y w) :
    Γ.dist (u : V) v = 3 := by
  let P : CFSG.Quasithin.F6.GoldAmL3T.Arc Γ 3 :=
    { vert := fun i => if i = 0 then (u : V) else if i = 1 then Y.vert 0
        else if i = 2 then (w : V) else v
      adj := by
        intro i hi
        have hi3 : i ≤ 2 := by omega
        interval_cases i
        · show Γ.Adj (u : V) (Y.vert 0)
          exact u.2.symm
        · show Γ.Adj (Y.vert 0) (w : V)
          exact w.2
        · show Γ.Adj (w : V) v
          exact hv.1
      nb := by
        intro i hi
        have hi1 : i ≤ 1 := by omega
        interval_cases i
        · show (u : V) ≠ (w : V)
          exact fun h => huw (Subtype.ext h)
        · show Y.vert 0 ≠ v
          exact fun h => hv.2 h.symm }
  have h0 : P.vert 0 = (u : V) := by simp [P]
  have h3 : P.vert 3 = v := by simp [P]
  have hd := Arc.dist_eq Y.hyp.isTree P 3 (le_rfl)
  rwa [h0, h3] at hd

private theorem VNbr0_fixes_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {x : G} (hx : x ∈ Y.VNbr0) : x • Y.vert 0 = Y.vert 0 := by
  exact MulAction.mem_stabilizer_iff.mp ((VNbr0_props Y H hZ).1 hx |> fun h =>
    Y.Q_le_Gi 0 h)

private theorem NbrSet_smul (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {x : G} (hx : x ∈ Y.VNbr0) (w : Γ.neighborSet (Y.vert 0)) :
    x • NbrSet Y w = NbrSet Y w := by
  have hx0 : x • Y.vert 0 = Y.vert 0 := VNbr0_fixes_zero Y H hZ hx
  have hxw : x • (w : V) = w := VNbr0_fixes_nbr Y H hZ hx w.2
  have hxinv : x⁻¹ ∈ Y.VNbr0 := Y.VNbr0.inv_mem hx
  have hxinv0 : x⁻¹ • Y.vert 0 = Y.vert 0 := VNbr0_fixes_zero Y H hZ hxinv
  have hxinvw : x⁻¹ • (w : V) = w := VNbr0_fixes_nbr Y H hZ hxinv w.2
  ext v
  change v ∈ x • (Γ.neighborSet (w : V) \ {Y.vert 0}) ↔
    v ∈ Γ.neighborSet (w : V) \ {Y.vert 0}
  rw [Set.mem_smul_set_iff_inv_smul_mem, Set.mem_diff, Set.mem_diff,
    SimpleGraph.mem_neighborSet, SimpleGraph.mem_neighborSet]
  constructor
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h2' : Γ.Adj (x⁻¹ • (w : V)) (x⁻¹ • v) := by simpa [hxinvw] using h1
      exact (Y.hyp.adj_smul x⁻¹ (w : V) v).mp h2'
    · intro hv0
      have hv0' : v = Y.vert 0 := by simpa using hv0
      exact h2 (by simpa [hv0', hxinv0])
  · rintro ⟨h1, h2⟩
    refine ⟨?_, ?_⟩
    · have h2' : Γ.Adj (x⁻¹ • (w : V)) (x⁻¹ • v) :=
        (Y.hyp.adj_smul x⁻¹ (w : V) v).mpr h1
      simpa [hxinvw] using h2'
    · intro hv0
      apply h2
      have hv0' : x⁻¹ • v = Y.vert 0 := by simpa using hv0
      have h1' := congrArg (fun z => x • z) hv0'
      simpa [hx0] using h1'

private def FixSet (Y : Setup Γ G) (x : G) (w : Γ.neighborSet (Y.vert 0)) : Prop :=
  ∀ v : V, v ∈ NbrSet Y w → x • v = v

private theorem nbrSet_finite (Y : Setup Γ G) (w : Γ.neighborSet (Y.vert 0)) :
    (NbrSet Y w).Finite := (Y.hyp.finite_neighborSet (w : V)).sdiff

private theorem eq_of_ne_of_mem_two {S : Set V} (hS : S.ncard = 2) (hSfin : S.Finite)
    {v a b : V} (hv : v ∈ S) (ha : a ∈ S) (hb : b ∈ S) (hav : a ≠ v) (hbv : b ≠ v) : a = b :=
  (Set.ncard_le_one_iff (s := S \ {v}) hSfin.sdiff).mp
    (by simp [Set.ncard_sdiff_singleton_of_mem hv, hS]) ⟨ha, hav⟩ ⟨hb, hbv⟩

private theorem fixSet_of_fixes_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {x : G} (hx : x ∈ Y.VNbr0) (w : Γ.neighborSet (Y.vert 0)) {v : V}
    (hv : v ∈ NbrSet Y w) (hfix : x • v = v) : FixSet Y x w := by
  intro v' hv'
  by_cases hv'v : v' = v
  · rw [hv'v, hfix]
  · have hS := NbrSet_smul Y H hZ hx w
    have hxv' : x • v' ∈ NbrSet Y w := by
      rw [← hS]; exact Set.smul_mem_smul_set hv'
    have hxne : x • v' ≠ v := by
      intro h
      have h1 : x⁻¹ • (x • v') = x⁻¹ • v := by rw [h]
      rw [inv_smul_smul] at h1
      rw [← hfix, inv_smul_smul] at h1
      exact hv'v h1
    exact eq_of_ne_of_mem_two (ncard_NbrSet Y H w) (nbrSet_finite Y w) hv hxv' hv'
      hxne hv'v

private theorem swap_of_not_fix (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {x : G} (hx : x ∈ Y.VNbr0) (w : Γ.neighborSet (Y.vert 0)) (h : ¬ FixSet Y x w)
    {v : V} (hv : v ∈ NbrSet Y w) : x • v ≠ v ∧ x • (x • v) = v := by
  have hne : x • v ≠ v := fun hfix => h (fixSet_of_fixes_one Y H hZ hx w hv hfix)
  have hS := NbrSet_smul Y H hZ hx w
  have hxv : x • v ∈ NbrSet Y w := by rw [← hS]; exact Set.smul_mem_smul_set hv
  have hxx : x • (x • v) ∈ NbrSet Y w := by rw [← hS]; exact Set.smul_mem_smul_set hxv
  have hxxne : x • (x • v) ≠ x • v := by
    intro hh
    exact hne (MulAction.injective x hh)
  refine ⟨hne, ?_⟩
  have hpair : ({v, x • v} : Set V) ⊆ NbrSet Y w := by
    intro a ha
    rcases (by simpa using ha : a = v ∨ a = x • v) with rfl | rfl
    · exact hv
    · exact hxv
  have hcardpair : ({v, x • v} : Set V).ncard = 2 := Set.ncard_pair (Ne.symm hne)
  have hSeq : ({v, x • v} : Set V) = NbrSet Y w := by
    refine Set.eq_of_subset_of_ncard_le hpair ?_ (nbrSet_finite Y w)
    rw [hcardpair, ncard_NbrSet Y H w]
  have hmem : x • (x • v) ∈ ({v, x • v} : Set V) := hSeq ▸ hxx
  rcases (by simpa using hmem : x • (x • v) = v ∨ x • (x • v) = x • v) with h | h
  · exact h
  · exact absurd h hxxne

private theorem fixSet_mul_iff (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {x y : G} (hx : x ∈ Y.VNbr0) (hy : y ∈ Y.VNbr0) (w : Γ.neighborSet (Y.vert 0)) :
    (FixSet Y x w → (FixSet Y (x * y) w ↔ FixSet Y y w)) ∧
      (¬ FixSet Y x w → (FixSet Y (x * y) w ↔ ¬ FixSet Y y w)) := by
  constructor
  · intro hxfix
    constructor
    · intro h v hv
      have h1 : (x * y) • v = v := h v hv
      have hyv : y • v ∈ NbrSet Y w := by
        rw [← NbrSet_smul Y H hZ hy w]; exact Set.smul_mem_smul_set hv
      rw [mul_smul, hxfix _ hyv] at h1
      exact h1
    · intro h v hv
      rw [mul_smul, hxfix _ (by
        rw [← NbrSet_smul Y H hZ hy w]; exact Set.smul_mem_smul_set hv), h v hv]
  · intro hxfix
    constructor
    · intro h hyfix
      apply hxfix
      intro v hv
      have hyv : y • v = v := hyfix v hv
      have h1 : (x * y) • v = v := h v hv
      rwa [mul_smul, hyv] at h1
    · intro hyne v hv
      have hswap := swap_of_not_fix Y H hZ hx w hxfix hv
      have hyvne : y • v ≠ v := fun hyv => hyne (fixSet_of_fixes_one Y H hZ hy w hv hyv)
      have hyvS : y • v ∈ NbrSet Y w := by
        rw [← NbrSet_smul Y H hZ hy w]; exact Set.smul_mem_smul_set hv
      have hxvS : x • v ∈ NbrSet Y w := by
        rw [← NbrSet_smul Y H hZ hx w]; exact Set.smul_mem_smul_set hv
      have hyveq : y • v = x • v :=
        eq_of_ne_of_mem_two (ncard_NbrSet Y H w) (nbrSet_finite Y w) hv hyvS hxvS
          hyvne hswap.1
      rw [mul_smul, hyveq, hswap.2]

private noncomputable def phi (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.VNbr0 →* Multiplicative (Γ.neighborSet (Y.vert 0) → ZMod 2) where
  toFun x := by
    letI := Classical.propDecidable
    exact Multiplicative.ofAdd fun w => if FixSet Y (x : G) w then 0 else 1
  map_one' := by
    apply Multiplicative.toAdd.injective
    funext w
    have h1 : FixSet Y (1 : G) w := by
      intro v hv
      simp
    simp [h1]
  map_mul' := by
    intro x y
    apply Multiplicative.toAdd.injective
    funext w
    have h11 : (1 : ZMod 2) + 1 = 0 := by decide
    have hiff := fixSet_mul_iff Y H hZ (x := (x : G)) (y := (y : G)) x.2 y.2 w
    by_cases hx : FixSet Y (x : G) w <;> by_cases hy : FixSet Y (y : G) w
    · have hxy : FixSet Y ((x : G) * (y : G)) w := (hiff.1 hx).2 hy
      simp [hxy, hx, hy]
    · have hxy : ¬ FixSet Y ((x : G) * (y : G)) w := by
        intro h
        exact hy ((hiff.1 hx).1 h)
      simp [hxy, hx, hy]
    · have hxy : ¬ FixSet Y ((x : G) * (y : G)) w := by
        intro h
        exact (hiff.2 hx).1 h hy
      simp [hxy, hx, hy, h11]
    · have hxy : FixSet Y ((x : G) * (y : G)) w := (hiff.2 hx).2 hy
      simp [hxy, hx, hy, h11]



private noncomputable def xOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) : G :=
  Classical.choose (exists_mem_vertZ_not_mem_Z_zero Y H hZ u)

private theorem xOf_spec (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) :
    xOf Y H hZ u ∈ vertZ (G := G) (u : V) ∧ xOf Y H hZ u ∉ Y.Z 0 :=
  Classical.choose_spec (exists_mem_vertZ_not_mem_Z_zero Y H hZ u)

private noncomputable def singleVec (Y : Setup Γ G) (u : Γ.neighborSet (Y.vert 0)) :
    Γ.neighborSet (Y.vert 0) → ZMod 2 := by
  classical
  exact fun w => if w = u then 1 else 0

private theorem phi_xOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) :
    phi Y H hZ ⟨xOf Y H hZ u, by
      rw [VNbr0_eq_iSup Y]
      exact le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V)) u
        (xOf_spec Y H hZ u).1⟩ =
      Multiplicative.ofAdd (fun w => 1 + singleVec Y u w) := by
  classical
  apply Multiplicative.toAdd.injective
  funext w
  change (if FixSet Y (xOf Y H hZ u) w then 0 else 1) = 1 + singleVec Y u w
  by_cases hwu : w = u
  · subst hwu
    have hfix : FixSet Y (xOf Y H hZ w) w := by
      intro v hv
      have hxQ : xOf Y H hZ w ∈ pCoreOf 2 (MulAction.stabilizer G (w : V)) :=
        vertZ_le_pCoreOf (G := G) (w : V) (xOf_spec Y H hZ w).1
      exact (Y.hyp.isLocL2_oTwoPrime (w : V)).Q_fixes_neighbors Y.hyp.adj_smul
        (Y.hyp.finite_stab (w : V)) (Y.hyp.valency (w : V)).2 (Y.hyp.valency (w : V)).1
        v hv.1 (xOf Y H hZ w) hxQ
    rw [if_pos hfix]
    simp only [singleVec, if_pos rfl]
    decide
  · have hnotfix : ¬ FixSet Y (xOf Y H hZ u) w := by
      intro hfix
      have hpos : 0 < (NbrSet Y w).ncard := by rw [ncard_NbrSet Y H w]; norm_num
      obtain ⟨v, hv⟩ := (Set.ncard_pos (nbrSet_finite Y w)).mp hpos
      have hdist : Γ.dist (u : V) v = 3 :=
        dist_nbr_NbrSet_ne Y (fun h => hwu h.symm) hv
      have hnotle : ¬ vertZ (G := G) (u : V) ≤ MulAction.stabilizer G v := by
        intro hle
        have h01 : Γ.Adj (Y.vert 0) (Y.vert 1) := by simpa using Y.adj (0 : ℤ)
        obtain ⟨g, hg, hgu⟩ := L_zero_trans Y (a := Y.vert 1) (b := (u : V)) h01 u.2
        have hle' : vertZ (G := G) (g • Y.vert 1) ≤ MulAction.stabilizer G v := by
          rwa [hgu]
        have hd := (vertZ_le_stabilizer_iff Y H hZ 1 g v).mp hle'
        have hd' : Γ.dist (u : V) v ≤ 2 := by simpa [hgu] using hd
        omega
      apply hnotle
      have hcardu : Nat.card (vertZ (G := G) (u : V)) = 4 := card_vertZ_nbr Y H hZ u
      obtain ⟨-, -, -, -, -, -, hcard0, -⟩ := s52_step8 Y H hZ
      haveI : Finite ↥(vertZ (G := G) (u : V)) :=
        Nat.finite_of_card_ne_zero (by rw [hcardu]; norm_num)
      have hgen := CFSG.Quasithin.F6.GoldAmN.sup_zpowers_eq_of_relIndex_two
        (Z_zero_le_vertZ Y H hZ u)
        (CFSG.Monster.AxisCount.relIndex_eq_two_of_card_eq (Z_zero_le_vertZ Y H hZ u)
          (by omega))
        (xOf_spec Y H hZ u).1 (xOf_spec Y H hZ u).2
      rw [← hgen]
      refine sup_le ?_ ?_
      · have hd0 : Γ.dist (Y.vert 0) v ≤ 3 := by
          have h := SimpleGraph.dist_le
            (SimpleGraph.Walk.cons w.2 (SimpleGraph.Walk.cons hv.1 SimpleGraph.Walk.nil))
          have hlen : (SimpleGraph.Walk.cons w.2
              (SimpleGraph.Walk.cons hv.1 SimpleGraph.Walk.nil)).length = 2 := rfl
          rw [hlen] at h
          omega
        have hle := (vertZ_le_stabilizer_iff Y H hZ 0 1 v).mpr (by simpa using hd0)
        simpa [Setup.Z_eq_vertZ] using hle
      · exact Subgroup.zpowers_le.mpr (by simpa [MulAction.mem_stabilizer_iff] using hfix v hv)
    rw [if_neg hnotfix]
    simp [singleVec, hwu]

private noncomputable def xOfVNbr0 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) : Y.VNbr0 :=
  ⟨xOf Y H hZ u, by
    rw [VNbr0_eq_iSup Y]
    exact le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V)) u
      (xOf_spec Y H hZ u).1⟩

private def uZero (Y : Setup Γ G) : Γ.neighborSet (Y.vert 0) :=
  ⟨Y.vert 1, by simpa using Y.adj (0 : ℤ)⟩

private noncomputable def vOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) : (phi Y H hZ).range :=
  ⟨phi Y H hZ (xOfVNbr0 Y H hZ u), MonoidHom.mem_range.mpr ⟨xOfVNbr0 Y H hZ u, rfl⟩⟩

private noncomputable def prodVec (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (A : Finset {u : Γ.neighborSet (Y.vert 0) // u ≠ uZero Y}) :
    (phi Y H hZ).range :=
  A.prod (fun a => vOf Y H hZ a.1)

private theorem prodVec_apply (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (A : Finset {u : Γ.neighborSet (Y.vert 0) // u ≠ uZero Y})
    (w : Γ.neighborSet (Y.vert 0)) :
    (prodVec Y H hZ A).1.toAdd w = ∑ a ∈ A, (1 + singleVec Y a.1 w) := by
  classical
  induction A using Finset.induction_on with
  | empty =>
      rw [prodVec, Finset.prod_empty, Finset.sum_empty]
      rfl
  | insert a A ha ih =>
      rw [prodVec, Finset.prod_insert ha, Finset.sum_insert ha]
      rw [prodVec] at ih
      have hmul : ((vOf Y H hZ a * A.prod (fun a => vOf Y H hZ a.1)).1).toAdd w =
          ((vOf Y H hZ a).1).toAdd w +
            ((A.prod (fun a => vOf Y H hZ a.1)).1).toAdd w := rfl
      rw [hmul, ih]
      have hx : Multiplicative.toAdd ((phi Y H hZ) (xOfVNbr0 Y H hZ a.1)) w =
          1 + singleVec Y a.1 w := by
        simpa [xOfVNbr0] using congrArg (fun f => f w) (congrArg Multiplicative.toAdd
          (phi_xOf Y H hZ a.1))
      simpa [vOf] using hx

private noncomputable def memVec (Y : Setup Γ G) (A : Finset (Γ.neighborSet (Y.vert 0)))
    (w : Γ.neighborSet (Y.vert 0)) : ZMod 2 := by
  classical
  exact if w ∈ A then 1 else 0

private theorem sum_one_add_single (Y : Setup Γ G) (A : Finset (Γ.neighborSet (Y.vert 0)))
    (w : Γ.neighborSet (Y.vert 0)) :
    (∑ a ∈ A, (1 + singleVec Y a w)) =
      (A.card : ZMod 2) + memVec Y A w := by
  classical
  rw [Finset.sum_add_distrib, Finset.sum_const]
  have hsingle : (∑ a ∈ A, singleVec Y a w) = memVec Y A w := by
    simp [singleVec, memVec]
  rw [hsingle]
  simp [nsmul_eq_mul]

private noncomputable def imageVal (Y : Setup Γ G)
    (A : Finset {u : Γ.neighborSet (Y.vert 0) // u ≠ uZero Y}) :
    Finset (Γ.neighborSet (Y.vert 0)) := by
  classical
  exact A.image Subtype.val

private theorem sum_image_val (Y : Setup Γ G)
    (A : Finset {u : Γ.neighborSet (Y.vert 0) // u ≠ uZero Y})
    (f : Γ.neighborSet (Y.vert 0) → ZMod 2) :
    (∑ a ∈ A, f a.1) = ∑ w ∈ imageVal Y A, f w := by
  classical
  rw [imageVal, Finset.sum_image]
  exact Subtype.val_injective.injOn

private theorem prodVec_injective (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Function.Injective (prodVec Y H hZ) := by
  classical
  intro A B hAB
  set A' : Finset (Γ.neighborSet (Y.vert 0)) := imageVal Y A with hA'def
  set B' : Finset (Γ.neighborSet (Y.vert 0)) := imageVal Y B with hB'def
  have hAcard : A'.card = A.card := by
    rw [hA'def, imageVal, Finset.card_image_of_injective _ Subtype.val_injective]
  have hBcard : B'.card = B.card := by
    rw [hB'def, imageVal, Finset.card_image_of_injective _ Subtype.val_injective]
  have hnotA : uZero Y ∉ A' := by
    rw [hA'def, imageVal]
    intro h
    obtain ⟨a, ha, hae⟩ := Finset.mem_image.mp h
    exact a.2 hae
  have hnotB : uZero Y ∉ B' := by
    rw [hB'def, imageVal]
    intro h
    obtain ⟨b, hb, hbe⟩ := Finset.mem_image.mp h
    exact b.2 hbe
  have hfun : ∀ w, (∑ a ∈ A, (1 + singleVec Y a.1 w)) =
      ∑ b ∈ B, (1 + singleVec Y b.1 w) := by
    intro w
    have h1 := congrArg (fun z : (phi Y H hZ).range => (z.1).toAdd w) hAB
    have hA := prodVec_apply Y H hZ A w
    have hB := prodVec_apply Y H hZ B w
    rw [hA, hB] at h1
    exact h1
  have hcard : (A.card : ZMod 2) = (B.card : ZMod 2) := by
    have h := hfun (uZero Y)
    have hAcalc : (∑ a ∈ A, (1 + singleVec Y a.1 (uZero Y))) =
        (A.card : ZMod 2) := by
      calc (∑ a ∈ A, (1 + singleVec Y a.1 (uZero Y)))
          = ∑ w ∈ A', (1 + singleVec Y w (uZero Y)) := by
              simpa [hA'def] using sum_image_val Y A (fun w => 1 + singleVec Y w (uZero Y))
        _ = (A'.card : ZMod 2) + memVec Y A' (uZero Y) := sum_one_add_single Y A' _
        _ = (A.card : ZMod 2) := by
            rw [hAcard, show memVec Y A' (uZero Y) = 0 from by simp [memVec, hnotA],
              add_zero]
    have hBcalc : (∑ b ∈ B, (1 + singleVec Y b.1 (uZero Y))) =
        (B.card : ZMod 2) := by
      calc (∑ b ∈ B, (1 + singleVec Y b.1 (uZero Y)))
          = ∑ w ∈ B', (1 + singleVec Y w (uZero Y)) := by
              simpa [hB'def] using sum_image_val Y B (fun w => 1 + singleVec Y w (uZero Y))
        _ = (B'.card : ZMod 2) + memVec Y B' (uZero Y) := sum_one_add_single Y B' _
        _ = (B.card : ZMod 2) := by
            rw [hBcard, show memVec Y B' (uZero Y) = 0 from by simp [memVec, hnotB],
              add_zero]
    rw [hAcalc, hBcalc] at h
    exact h
  have hmem : ∀ w, memVec Y A' w = memVec Y B' w := by
    intro w
    have h := hfun w
    have hAcalc : (∑ a ∈ A, (1 + singleVec Y a.1 w)) =
        (A.card : ZMod 2) + memVec Y A' w := by
      calc (∑ a ∈ A, (1 + singleVec Y a.1 w))
          = ∑ w' ∈ A', (1 + singleVec Y w' w) := by
              simpa [hA'def] using sum_image_val Y A (fun w' => 1 + singleVec Y w' w)
        _ = (A'.card : ZMod 2) + memVec Y A' w := sum_one_add_single Y A' w
        _ = (A.card : ZMod 2) + memVec Y A' w := by rw [hAcard]
    have hBcalc : (∑ b ∈ B, (1 + singleVec Y b.1 w)) =
        (B.card : ZMod 2) + memVec Y B' w := by
      calc (∑ b ∈ B, (1 + singleVec Y b.1 w))
          = ∑ w' ∈ B', (1 + singleVec Y w' w) := by
              simpa [hB'def] using sum_image_val Y B (fun w' => 1 + singleVec Y w' w)
        _ = (B'.card : ZMod 2) + memVec Y B' w := sum_one_add_single Y B' w
        _ = (B.card : ZMod 2) + memVec Y B' w := by rw [hBcard]
    rw [hAcalc, hBcalc] at h
    rw [hcard] at h
    exact add_left_cancel h
  have hiff : ∀ w, w ∈ A' ↔ w ∈ B' := by
    intro w
    by_cases hA : w ∈ A'
    · have h1 : memVec Y A' w = 1 := by simp [memVec, hA]
      have hB : w ∈ B' := by
        by_contra hB
        have h0 : memVec Y B' w = 0 := by simp [memVec, hB]
        have hw := hmem w
        rw [h1, h0] at hw
        exact one_ne_zero hw
      exact ⟨fun _ => hB, fun _ => hA⟩
    · have h1 : memVec Y A' w = 0 := by simp [memVec, hA]
      have hB : w ∉ B' := by
        intro hB
        have h0 : memVec Y B' w = 1 := by simp [memVec, hB]
        have hw := hmem w
        rw [h1, h0] at hw
        exact zero_ne_one hw
      exact ⟨fun h => absurd h hA, fun h => absurd h hB⟩
  ext a
  constructor
  · intro ha
    have h1 : a.1 ∈ A' := by
      rw [hA'def, imageVal]
      exact Finset.mem_image.mpr ⟨a, ha, rfl⟩
    have h2 : a.1 ∈ B' := (hiff a.1).mp h1
    rw [hB'def, imageVal] at h2
    obtain ⟨b, hb, hba⟩ := Finset.mem_image.mp h2
    have hba' : b = a := Subtype.ext hba
    rwa [hba'] at hb
  · intro hb
    have h1 : a.1 ∈ B' := by
      rw [hB'def, imageVal]
      exact Finset.mem_image.mpr ⟨a, hb, rfl⟩
    have h2 : a.1 ∈ A' := (hiff a.1).mpr h1
    rw [hA'def, imageVal] at h2
    obtain ⟨b, ha, hba⟩ := Finset.mem_image.mp h2
    have hba' : b = a := Subtype.ext hba
    rwa [hba'] at ha

private theorem card_Delta (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Nat.card {u : Γ.neighborSet (Y.vert 0) // u ≠ uZero Y} = 2 ^ n₀ := by
  haveI : Finite (Γ.neighborSet (Y.vert 0)) := (Y.hyp.finite_neighborSet (Y.vert 0)).to_subtype
  haveI : Fintype (Γ.neighborSet (Y.vert 0)) := Fintype.ofFinite _
  haveI : Fintype {u : Γ.neighborSet (Y.vert 0) // u = uZero Y} := Fintype.ofFinite _
  haveI : Fintype {u : Γ.neighborSet (Y.vert 0) // u ≠ uZero Y} := Fintype.ofFinite _
  have hval : Nat.card (Γ.neighborSet (Y.vert 0)) = 2 ^ n₀ + 1 := by
    rw [(Y.hyp.valency (Y.vert 0)).2]
    exact congrArg (fun k => 2 ^ k + 1) H.n_zero
  have hcard : Fintype.card (Γ.neighborSet (Y.vert 0)) = 2 ^ n₀ + 1 := by
    rwa [← Nat.card_eq_fintype_card]
  have hone : Fintype.card {u : Γ.neighborSet (Y.vert 0) // u = uZero Y} = 1 :=
    Fintype.card_subtype_eq (y := uZero Y)
  rw [Nat.card_eq_fintype_card,
    Fintype.card_subtype_compl (p := fun u : Γ.neighborSet (Y.vert 0) => u = uZero Y)]
  rw [hcard, hone]
  have hpos : 0 < 2 ^ n₀ := Nat.two_pow_pos n₀
  omega

private theorem card_finset_Delta (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Nat.card (Finset {u : Γ.neighborSet (Y.vert 0) // u ≠ uZero Y}) = 2 ^ (2 ^ n₀) := by
  haveI : Finite (Γ.neighborSet (Y.vert 0)) := (Y.hyp.finite_neighborSet (Y.vert 0)).to_subtype
  haveI : Fintype {u : Γ.neighborSet (Y.vert 0) // u ≠ uZero Y} := Fintype.ofFinite _
  rw [Nat.card_eq_fintype_card, Fintype.card_finset]
  congr 1
  rw [← Nat.card_eq_fintype_card]
  exact card_Delta Y H

private theorem Z_zero_fixes (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (w : Γ.neighborSet (Y.vert 0)) {v : V} (hv : v ∈ NbrSet Y w) :
    ∀ z ∈ Y.Z 0, z • v = v := by
  intro z hz
  have hle : Y.Z 0 ≤ MulAction.stabilizer G v := by
    have hd0 : Γ.dist (Y.vert 0) v ≤ 3 := by
      have h := SimpleGraph.dist_le
        (SimpleGraph.Walk.cons w.2 (SimpleGraph.Walk.cons hv.1 SimpleGraph.Walk.nil))
      have hlen : (SimpleGraph.Walk.cons w.2
          (SimpleGraph.Walk.cons hv.1 SimpleGraph.Walk.nil)).length = 2 := rfl
      rw [hlen] at h
      omega
    have hle' := (vertZ_le_stabilizer_iff Y H hZ 0 1 v).mpr (by simpa using hd0)
    simpa [Setup.Z_eq_vertZ] using hle'
  exact MulAction.mem_stabilizer_iff.mp (hle hz)

private theorem card_VNbr0_quot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    2 ^ (2 ^ n₀) ≤ (Y.Z 0).relIndex Y.VNbr0 := by
  classical
  obtain ⟨-, -, -, -, -, -, hZcard, -⟩ := s52_step8 Y H hZ
  haveI : Finite ↥(Y.VNbr0) :=
    finite_of_le_stabilizer Y.hyp (H := Y.VNbr0)
      ((VNbr0_props Y H hZ).1.trans (Y.Q_le_Gi 0))
  haveI : Finite ↥(phi Y H hZ).range := by
    refine Finite.of_surjective (fun x : ↥(Y.VNbr0) =>
      (⟨phi Y H hZ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : ↥(phi Y H hZ).range)) ?_
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hrange : 2 ^ (2 ^ n₀) ≤ Nat.card ↥(phi Y H hZ).range := by
    rw [← card_finset_Delta Y H]
    exact Nat.card_le_card_of_injective (prodVec Y H hZ) (prodVec_injective Y H hZ)
  have hZle : Y.Z 0 ≤ Y.VNbr0 := by
    rw [← (VNbr0_props Y H hZ).2.2.2]
    exact Subgroup.commutator_le_self _
  let A : Subgroup ↥(Y.VNbr0) := (Y.Z 0).subgroupOf Y.VNbr0
  let K : Subgroup ↥(Y.VNbr0) := (phi Y H hZ).ker
  have hAK : A ≤ K := by
    intro z hz
    rw [MonoidHom.mem_ker]
    apply Multiplicative.toAdd.injective
    funext w
    have hfix : FixSet Y (z : G) w := by
      intro v hv
      exact Z_zero_fixes Y H hZ w hv (z : G) hz
    change (if FixSet Y (z : G) w then (0 : ZMod 2) else 1) = 0
    rw [if_pos hfix]
  haveI : Finite ↥K :=
    Finite.of_injective (fun x : ↥K => (x : ↥(Y.VNbr0))) (fun a b h => Subtype.ext h)
  haveI : Finite ↥A :=
    Finite.of_injective (fun x : ↥A => (x : ↥(Y.VNbr0))) (fun a b h => Subtype.ext h)
  have hAcard : Nat.card ↥A = 2 := by
    rw [show Nat.card ↥A = Nat.card ↥(Y.Z 0) from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZle).toEquiv]
    exact hZcard
  have hKindex : K.index = Nat.card ↥(phi Y H hZ).range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (phi Y H hZ)).toEquiv
  have hAindex_pos : 0 < A.index := by
    have hc := Subgroup.index_mul_card A
    have hcA : 0 < Nat.card ↥A := by rw [hAcard]; norm_num
    nlinarith [Nat.card_pos (α := ↥(Y.VNbr0))]
  have hrelpos : 0 < A.relIndex K := by
    have h := Subgroup.relIndex_mul_index (H := A) (K := K) hAK
    have hKpos : 0 < K.index := by rw [hKindex]; exact Nat.card_pos
    by_contra hzero
    have h0 : A.relIndex K = 0 := Nat.eq_zero_of_not_pos hzero
    rw [h0, zero_mul] at h
    omega
  have hAindex : A.index = Nat.card ↥(phi Y H hZ).range * A.relIndex K := by
    have h := Subgroup.relIndex_mul_index (H := A) (K := K) hAK
    rw [hKindex] at h
    rw [← h, mul_comm]
  have hrel : (Y.Z 0).relIndex Y.VNbr0 = A.index := by
    have h := Subgroup.relIndex_subgroupOf (H := Y.Z 0) (K := Y.VNbr0) (L := Y.VNbr0)
      le_rfl
    rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h
    exact h.symm
  rw [hrel, hAindex]
  exact le_trans hrange (Nat.le_mul_of_pos_right _ hrelpos)



private theorem pow_two_pow_gt_four_mul (n : ℕ) (hn : 3 ≤ n) :
    4 * 2 ^ n < 2 ^ (2 ^ n) := by
  have h1 : n + 4 ≤ 2 ^ n := by
    induction n with
    | zero => omega
    | succ k ih =>
      by_cases hk : 3 ≤ k
      · have h := ih hk
        rw [pow_succ]
        omega
      · interval_cases k <;> norm_num at *
  have h2 : n + 2 < 2 ^ n := by omega
  calc 4 * 2 ^ n = 2 ^ (n + 2) := by
        rw [show (4 : ℕ) = 2 ^ 2 by norm_num, ← pow_add, show 2 + n = n + 2 by omega]
    _ < 2 ^ (2 ^ n) := Nat.pow_lt_pow_right (by norm_num) h2

private theorem pow_two_pow_gt_eight_mul_sq (n : ℕ) (hn : 4 ≤ n) :
    8 * (2 ^ n) ^ 2 < 2 ^ (2 ^ n) := by
  have h1 : 2 * n + 5 ≤ 2 ^ n := by
    induction n with
    | zero => omega
    | succ k ih =>
      by_cases hk : 4 ≤ k
      · have h := ih hk
        rw [pow_succ]
        omega
      · interval_cases k <;> norm_num at *
  have h2 : 2 * n + 3 < 2 ^ n := by omega
  calc 8 * (2 ^ n) ^ 2 = 2 ^ (2 * n + 3) := by
        rw [show (8 : ℕ) = 2 ^ 3 by norm_num, ← pow_mul, ← pow_add]
        congr 1
        ring
    _ < 2 ^ (2 ^ n) := Nat.pow_lt_pow_right (by norm_num) h2

private theorem card_VNbr0_ge (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    2 ^ (2 ^ n₀ + 1) ≤ Nat.card ↥(Y.VNbr0) := by
  have hrel := card_VNbr0_quot Y H hZ
  obtain ⟨-, -, -, -, -, -, hcardZ, -⟩ := s52_step8 Y H hZ
  have hZle : Y.Z 0 ≤ Y.VNbr0 := by
    rw [← (VNbr0_props Y H hZ).2.2.2]
    exact Subgroup.commutator_le_self _
  haveI : Finite ↥(Y.Z 0) := Nat.finite_of_card_ne_zero (by rw [hcardZ]; norm_num)
  have h := Subgroup.relIndex_mul_card (H := Y.Z 0) (K := Y.VNbr0)
  rw [inf_eq_left.mpr hZle] at h
  calc 2 ^ (2 ^ n₀ + 1) = 2 ^ (2 ^ n₀) * 2 := by
        rw [pow_succ]
    _ ≤ (Y.Z 0).relIndex Y.VNbr0 * Nat.card (Y.Z 0) := by
        rw [hcardZ]
        exact Nat.mul_le_mul hrel le_rfl
    _ = Nat.card ↥(Y.VNbr0) := h

private theorem card_VNbr0_le_Q0 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Nat.card ↥(Y.VNbr0) ≤ Nat.card ↥(Y.Q 0) := by
  haveI : Finite ↥(Y.Q 0) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Q 0) (Y.Q_le_Gi 0)
  exact Nat.card_le_card_of_injective (Subgroup.inclusion (VNbr0_props Y H hZ).1)
    (Subgroup.inclusion_injective _)

private theorem VNbr0_eq_Q_zero_of_card_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) (hQ : Nat.card ↥(Y.Q 0) ≤ 2 ^ (2 ^ n₀ + 1)) : Y.VNbr0 = Y.Q 0 := by
  haveI : Finite ↥(Y.Q 0) := finite_of_le_stabilizer Y.hyp (H := Y.Q 0) (Y.Q_le_Gi 0)
  exact Subgroup.eq_of_le_of_card_ge (VNbr0_props Y H hZ).1
    (hQ.trans (card_VNbr0_ge Y H hZ))

theorem n_eq_two_of_card_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hS : Nat.card Y.S = 8 * 2 ^ (2 * n₀)) : n₀ = 2 ∧ Y.VNbr0 = Y.Q 0 := by
  haveI : Finite ↥(Y.Q 0) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Q 0) (Y.Q_le_Gi 0)
  haveI : Finite ↥(Y.VNbr0) :=
    finite_of_le_stabilizer Y.hyp (H := Y.VNbr0)
      ((VNbr0_props Y H hZ).1.trans (Y.Q_le_Gi 0))
  have hcardS := Y.card_S_eq_two_pow_mul_card_Q_zero H
  have hQ0eq : Nat.card (Y.Q 0) = 8 * 2 ^ n₀ := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos n₀)
    calc 2 ^ n₀ * Nat.card (Y.Q 0) = Nat.card Y.S := hcardS.symm
      _ = 8 * 2 ^ (2 * n₀) := hS
      _ = 2 ^ n₀ * (8 * 2 ^ n₀) := by
          rw [show 2 ^ (2 * n₀) = (2 ^ n₀) ^ 2 by
            rw [show 2 * n₀ = n₀ * 2 by ring, ← pow_mul]]
          ring
  have hQ0le : 2 ^ (2 ^ n₀ + 1) ≤ Nat.card (Y.Q 0) :=
    (card_VNbr0_ge Y H hZ).trans (card_VNbr0_le_Q0 Y H hZ)
  have hq : 2 ^ (2 ^ n₀) ≤ 4 * 2 ^ n₀ := by
    have h := hQ0le
    rw [hQ0eq] at h
    rw [show 2 ^ (2 ^ n₀ + 1) = 2 * 2 ^ (2 ^ n₀) by rw [pow_succ, mul_comm],
      show 8 * 2 ^ n₀ = 2 * (4 * 2 ^ n₀) by ring] at h
    exact Nat.le_of_mul_le_mul_left h (by norm_num)
  have hn2 : n₀ = 2 := by
    by_contra hne
    have h2 : 2 < n₀ := lt_of_le_of_ne H.two_le (Ne.symm hne)
    have hn3 : 3 ≤ n₀ := by omega
    exact absurd hq (not_le_of_gt (pow_two_pow_gt_four_mul n₀ hn3))
  subst hn2
  have hQcard : Nat.card (Y.Q 0) = 32 := by
    rw [hQ0eq]
    norm_num
  exact ⟨rfl, VNbr0_eq_Q_zero_of_card_le Y H hZ (by rw [hQcard]; norm_num)⟩

theorem n_le_three_of_card_S (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hS : Nat.card Y.S = 2 ^ (3 * n₀ + 3)) : n₀ = 2 ∨ (n₀ = 3 ∧ Y.VNbr0 = Y.Q 0) := by
  haveI : Finite ↥(Y.Q 0) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Q 0) (Y.Q_le_Gi 0)
  haveI : Finite ↥(Y.VNbr0) :=
    finite_of_le_stabilizer Y.hyp (H := Y.VNbr0)
      ((VNbr0_props Y H hZ).1.trans (Y.Q_le_Gi 0))
  have hcardS := Y.card_S_eq_two_pow_mul_card_Q_zero H
  have hQ0eq : Nat.card (Y.Q 0) = 8 * 2 ^ (2 * n₀) := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.two_pow_pos n₀)
    calc 2 ^ n₀ * Nat.card (Y.Q 0) = Nat.card Y.S := hcardS.symm
      _ = 2 ^ (3 * n₀ + 3) := hS
      _ = 2 ^ n₀ * (8 * 2 ^ (2 * n₀)) := by
          rw [show 3 * n₀ + 3 = n₀ + (2 * n₀ + 3) by ring, pow_add,
            show 2 * n₀ + 3 = 3 + 2 * n₀ by ring, pow_add,
            show (2 : ℕ) ^ 3 = 8 by norm_num]
  have hQ0le : 2 ^ (2 ^ n₀ + 1) ≤ Nat.card (Y.Q 0) :=
    (card_VNbr0_ge Y H hZ).trans (card_VNbr0_le_Q0 Y H hZ)
  have hq : 2 ^ (2 ^ n₀) ≤ 8 * (2 ^ n₀) ^ 2 := by
    have h := hQ0le
    rw [hQ0eq] at h
    rw [show 2 ^ (2 ^ n₀ + 1) = 2 * 2 ^ (2 ^ n₀) by rw [pow_succ, mul_comm],
      show 8 * 2 ^ (2 * n₀) = 2 * (4 * 2 ^ (2 * n₀)) by ring] at h
    have h' : 2 ^ (2 ^ n₀) ≤ 4 * 2 ^ (2 * n₀) :=
      Nat.le_of_mul_le_mul_left h (by norm_num)
    calc 2 ^ (2 ^ n₀) ≤ 4 * 2 ^ (2 * n₀) := h'
      _ ≤ 8 * (2 ^ n₀) ^ 2 := by
          rw [show 2 ^ (2 * n₀) = (2 ^ n₀) ^ 2 by
            rw [show 2 * n₀ = n₀ * 2 by ring, ← pow_mul]]
          nlinarith
  have hnle : n₀ ≤ 3 := by
    by_contra h
    have hn4 : 4 ≤ n₀ := by omega
    exact absurd hq (not_le_of_gt (pow_two_pow_gt_eight_mul_sq n₀ hn4))
  rcases Nat.lt_or_eq_of_le hnle with hlt | heq
  · left
    have h2 : 2 ≤ n₀ := H.two_le
    omega
  · right
    subst heq
    have hQcard : Nat.card (Y.Q 0) = 512 := by
      rw [hQ0eq]
      norm_num
    exact ⟨rfl, VNbr0_eq_Q_zero_of_card_le Y H hZ (by rw [hQcard]; norm_num)⟩

private noncomputable def zOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    ↥(Y.Z 0) :=
  Classical.choose (Nat.card_eq_two_iff' (1 : ↥(Y.Z 0)) |>.mp (by
    obtain ⟨-, -, -, -, -, -, hZcard, -⟩ := s52_step8 Y H hZ
    exact hZcard))

private theorem zOf_ne_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    zOf Y H hZ ≠ 1 :=
  (Classical.choose_spec (Nat.card_eq_two_iff' (1 : ↥(Y.Z 0)) |>.mp (by
    obtain ⟨-, -, -, -, -, -, hZcard, -⟩ := s52_step8 Y H hZ
    exact hZcard))).1

private theorem xOf_mem (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (u : Γ.neighborSet (Y.vert 0)) : xOf Y H hZ u ∈ Y.VNbr0 := by
  rw [VNbr0_eq_iSup Y]
  exact le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V)) u
    (xOf_spec Y H hZ u).1

private theorem commutator_mem_Z (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {a b : G} (ha : a ∈ Y.VNbr0) (hb : b ∈ Y.VNbr0) : ⁅a, b⁆ ∈ Y.Z 0 := by
  rw [← (VNbr0_props Y H hZ).2.2.2]
  exact Subgroup.commutator_mem_commutator ha hb

private theorem relIndex_Q_zero_inf_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (Y.Q 0 ⊓ Y.Q 1).relIndex (Y.Q 0) = 2 := by
  have h4 : 4 ≤ s := by have := H.five_le; omega
  obtain ⟨-, hBQ0, hBH, -, -⟩ :=
    Q_quot_of_normal_general (X := Y) H.char H.sing h4
  have hBrel : (Y.Q (-1) ⊓ Y.Q 1).relIndex (Y.Q 0) = 2 ^ (2 * Y.n 1) := hBQ0
  have hBHrel : (Y.Q (-1) ⊓ Y.Q 1).relIndex (Y.Q 0 ⊓ Y.Q 1) = 2 ^ Y.n 1 := hBH
  have hBleH : Y.Q (-1) ⊓ Y.Q 1 ≤ Y.Q 0 ⊓ Y.Q 1 :=
    le_inf (Q_neg_one_inf_Q_one_le_Q_zero Y) inf_le_right
  have hmul := Subgroup.relIndex_mul_relIndex (H := Y.Q (-1) ⊓ Y.Q 1)
    (K := Y.Q 0 ⊓ Y.Q 1) (L := Y.Q 0) hBleH inf_le_left
  rw [hBrel, hBHrel, H.n_one] at hmul
  simp only [Nat.reduceMul, Nat.reducePow, pow_one, mul_one] at hmul ⊢
  omega

private theorem Q_one_le_normalizer_Q_two (Y : Setup Γ G) :
    Y.Q 1 ≤ Subgroup.normalizer (Y.Q 2 : Set G) :=
  (by simpa using (Y.Q_le_Gi_adj 1).trans inf_le_right : Y.Q 1 ≤ Y.Gi 2).trans
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 2))

private theorem Q_one_le_normalizer_inf_two (Y : Setup Γ G) :
    Y.Q 1 ≤ Subgroup.normalizer ((Y.Q 2 ⊓ Y.Q 1 : Subgroup G) : Set G) :=
  CFSG.Quasithin.F7.le_normalizer_inf (Q_one_le_normalizer_Q_two Y)
    Subgroup.le_normalizer

private theorem Q_two_inf_Q_one_subgroupOf_normal (Y : Setup Γ G) :
    ((Y.Q 2 ⊓ Y.Q 1).subgroupOf (Y.Q 1)).Normal :=
  Subgroup.normal_subgroupOf_of_le_normalizer
    (Q_one_le_normalizer_inf_two Y)

private theorem Q_one_eq_sup (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    Y.Q 1 = (Y.Q 0 ⊓ Y.Q 1) ⊔ (Y.Q 2 ⊓ Y.Q 1) := by
  have h4 : 4 ≤ s := by have := H.five_le; omega
  have h := (Q_quot_of_normal_general (X := Y.shift 1) H.char H.sing h4).1
  simpa [inf_comm, sup_comm] using h

private def cOf (Y : Setup Γ G) (d : G) : V := d • Y.vert 2

private theorem d_pow_three {d : G} (hd3 : orderOf d = 3) : d ^ 3 = 1 :=
  hd3 ▸ pow_orderOf_eq_one d

private theorem d_fixes_one (Y : Setup Γ G) {d : G} (hd : d ∈ Y.L 1) :
    d • Y.vert 1 = Y.vert 1 :=
  MulAction.mem_stabilizer_iff.mp (Y.L_le_Gi 1 hd)

private theorem cOf_adj (Y : Setup Γ G) {d : G} (hd : d ∈ Y.L 1) :
    Γ.Adj (Y.vert 1) (cOf Y d) := by
  have h := (Y.hyp.adj_smul d (Y.vert 1) (Y.vert 2)).mpr (by simpa using Y.adj 1)
  rwa [d_fixes_one Y hd] at h


private theorem cOf_ne_zero (Y : Setup Γ G) {d : G} (hd3 : orderOf d = 3)
    (hd0 : d • Y.vert 0 = Y.vert 2) : cOf Y d ≠ Y.vert 0 := by
  intro h
  have hc : cOf Y d = d ^ 2 • Y.vert 0 := by
    rw [cOf, ← hd0, ← mul_smul, pow_two]
  rw [hc] at h
  have h1 : d • (d ^ 2 • Y.vert 0) = d • Y.vert 0 := by rw [h]
  rw [← mul_smul, show d * d ^ 2 = d ^ 3 by group, d_pow_three hd3, one_smul] at h1
  exact vert_zero_ne_vert_two Y (h1.trans hd0)

private theorem cOf_ne_two (Y : Setup Γ G) {d : G}
    (hd0 : d • Y.vert 0 = Y.vert 2) : cOf Y d ≠ Y.vert 2 := by
  intro h
  have h' : d • Y.vert 2 = d • Y.vert 0 := h.trans hd0.symm
  have h0 : Y.vert 2 = Y.vert 0 := MulAction.injective d h'
  exact vert_zero_ne_vert_two Y h0.symm

private theorem d_smul_cOf (Y : Setup Γ G) {d : G} (hd3 : orderOf d = 3)
    (hd0 : d • Y.vert 0 = Y.vert 2) : d • cOf Y d = Y.vert 0 := by
  have hd1 : d * d * d = 1 := by
    simpa [pow_succ, pow_two, mul_assoc] using d_pow_three hd3
  rw [cOf, ← hd0, ← mul_smul, ← mul_smul, hd1, one_smul]

private theorem d_smul_vert_two (Y : Setup Γ G) (d : G) : d • Y.vert 2 = cOf Y d := rfl

private def AOf (Y : Setup Γ G) : Subgroup G := Y.Q 0 ⊓ Y.Q 2

private def DOf (Y : Setup Γ G) (d : G) : Subgroup G :=
  AOf Y ⊓ Subgroup.centralizer ({d} : Set G)

@[simp] private theorem AOf_eq (Y : Setup Γ G) : AOf Y = Y.Q 0 ⊓ Y.Q 2 := rfl

@[simp] private theorem DOf_eq (Y : Setup Γ G) (d : G) :
    DOf Y d = AOf Y ⊓ Subgroup.centralizer ({d} : Set G) := rfl

private theorem AOf_le_Q_one (Y : Setup Γ G) : AOf Y ≤ Y.Q 1 :=
  by simpa using (Y.shift 1).Q_neg_one_inf_Q_one_le_Q_zero

private theorem Z_one_le_AOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) : Y.Z 1 ≤ AOf Y := by
  have h := (s52_A_eq Y H hZ hd hd3).1
  rw [show AOf Y = DOf Y d ⊔ Y.Z 1 from h]
  exact le_sup_right

private theorem AOf_eq_DOf_sup_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    AOf Y = DOf Y d ⊔ Y.Z 1 :=
  (s52_A_eq Y H hZ hd hd3).1

private theorem DOf_inf_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) : DOf Y d ⊓ Y.Z 1 = ⊥ :=
  (s52_A_eq Y H hZ hd hd3).2

private theorem Z_one_le_centralizer_AOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.Z 1 ≤ Subgroup.centralizer (AOf Y : Set G) := by
  obtain ⟨-, -, -, -, hsup, -, -, -⟩ := Y.s52_step8 H hZ
  have h0 : Y.Z 0 ≤ Subgroup.centralizer (AOf Y : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hc := (Y.Z_le_center 0 hz).2
    exact Subgroup.mem_centralizer_iff.mp hc a ha.1
  have h2 : Y.Z 2 ≤ Subgroup.centralizer (AOf Y : Set G) := by
    intro z hz
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    have hc := (Y.Z_le_center 2 hz).2
    exact Subgroup.mem_centralizer_iff.mp hc a ha.2
  rw [hsup]
  exact sup_le h0 h2

private theorem exists_DOf_mul_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) {a : G} (ha : a ∈ AOf Y) :
    ∃ δ ∈ DOf Y d, ∃ z ∈ Y.Z 1, a = δ * z := by
  have hZN : Y.Z 1 ≤ Subgroup.normalizer (DOf Y d : Set G) := by
    refine (Z_one_le_centralizer_AOf Y H hZ).trans ?_
    exact (Subgroup.centralizer_le (s := (DOf Y d : Set G)) (t := (AOf Y : Set G))
        (by intro x hx; exact (Subgroup.mem_inf.mp hx).1)).trans
      (Subgroup.centralizer_le_normalizer (DOf Y d : Set G))
  have ha' : a ∈ DOf Y d ⊔ Y.Z 1 := by
    rwa [← AOf_eq_DOf_sup_Z_one Y H hZ hd hd3]
  obtain ⟨δ, hδ, z, hz, haz⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (H := DOf Y d) (K := Y.Z 1) hZN).mp ha'
  exact ⟨δ, hδ, z, hz, haz⟩

private theorem Z_one_le_VNbr0 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.Z 1 ≤ Y.VNbr0 := by
  rw [VNbr0_eq_iSup Y]
  intro z hz
  refine le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V))
    ⟨Y.vert 1, by simpa using Y.adj 0⟩ ?_
  simpa [Setup.Z_eq_vertZ] using hz

private theorem AOf_le_DOf_sup_VNbr0 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    AOf Y ≤ DOf Y d ⊔ Y.VNbr0 := by
  rw [AOf_eq_DOf_sup_Z_one Y H hZ hd hd3]
  exact sup_le le_sup_left ((Z_one_le_VNbr0 Y H hZ).trans le_sup_right)

private theorem Q_one_le_S (Y : Setup Γ G) : Y.Q 1 ≤ Y.S := by
  simpa [Setup.S] using Y.Q_le_edgeSylow_right 1

private theorem sq_mem_AOf (Y : Setup Γ G) {x : G} (hx : x ∈ Y.Q 1) : x ^ 2 ∈ AOf Y := by
  have hS : (Y.mirror1).S = Y.edgeSylow 1 := by
    rw [show Y.edgeSylow 1 = pCoreOf 2 (Y.Gi 1 ⊓ Y.Gi 2) from rfl]
    rw [show (Y.mirror1).S = pCoreOf 2 ((Y.mirror1).Gi 0 ⊓ (Y.mirror1).Gi 1) from rfl]
    simp [inf_comm]
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · exact Y.sq_mem_Q_of_relIndex (Y.edgeSylow_le_L 0) (Y.relIndex_Q_edgeSylow 0) x
      (by rw [Y.edgeSylow_zero]; exact Q_one_le_S Y hx)
  · have h := (Y.mirror1).sq_mem_Q_of_relIndex ((Y.mirror1).edgeSylow_le_L 0)
      ((Y.mirror1).relIndex_Q_edgeSylow 0) x
      (show x ∈ (Y.mirror1).S from hS ▸ Y.Q_le_edgeSylow_left 1 hx)
    simpa using h

private theorem commutator_mem_AOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {x y : G} (hx : x ∈ Y.Q 1) (hy : y ∈ Y.Q 1) : ⁅x, y⁆ ∈ AOf Y := by
  have hxy : x * y ∈ Y.Q 1 := (Y.Q 1).mul_mem hx hy
  have hsq : (x * y) ^ 2 ∈ AOf Y := sq_mem_AOf Y hxy
  have hx2 : x ^ 2 ∈ AOf Y := sq_mem_AOf Y hx
  have hy2 : y ^ 2 ∈ AOf Y := sq_mem_AOf Y hy
  have hyL : y⁻¹ ∈ Y.L 1 := (Y.L 1).inv_mem ((Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).oTwo_le hy)
  have hconj : y⁻¹ * (x ^ 2)⁻¹ * y ∈ AOf Y := by
    have hnorm := (s52_A_normal Y H hZ).1 hyL
    have h := (Subgroup.mem_normalizer_iff.mp hnorm ((x ^ 2)⁻¹)).mp
      ((AOf Y).inv_mem hx2)
    simpa using h
  have hprod : (x * y) ^ 2 * (y⁻¹ * (x ^ 2)⁻¹ * y) * (y ^ 2)⁻¹ ∈ AOf Y :=
    (AOf Y).mul_mem ((AOf Y).mul_mem hsq hconj) ((AOf Y).inv_mem hy2)
  have heq : ⁅x, y⁆ = (x * y) ^ 2 * (y⁻¹ * (x ^ 2)⁻¹ * y) * (y ^ 2)⁻¹ := by
    simp only [commutatorElement_def, pow_two]
    group
  rwa [heq]

private theorem conjSub_Q_two_eq (Y : Setup Γ G) {g : G} {c : V} (hc : g • Y.vert 2 = c) :
    conjSub g (Y.Q 2) = pCoreOf 2 (MulAction.stabilizer G c) := by
  rw [show Y.Q 2 = pCoreOf 2 (Y.Gi 2) from rfl, ← pCoreOf_conjSub,
    ← stabilizer_smul_eq_conjSub, hc]

private theorem conjSub_Q_zero_eq (Y : Setup Γ G) {g : G} {c : V} (hc : g • Y.vert 0 = c) :
    conjSub g (Y.Q 0) = pCoreOf 2 (MulAction.stabilizer G c) := by
  rw [show Y.Q 0 = pCoreOf 2 (Y.Gi 0) from rfl, ← pCoreOf_conjSub,
    ← stabilizer_smul_eq_conjSub, hc]

private theorem conjSub_d_Q_zero (Y : Setup Γ G) {d : G}
    (hd0 : d • Y.vert 0 = Y.vert 2) : conjSub d (Y.Q 0) = Y.Q 2 := by
  rw [conjSub_Q_zero_eq Y hd0]

private theorem AOf_eq_Q_two_inf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd0 : d • Y.vert 0 = Y.vert 2) :
    AOf Y = Y.Q 2 ⊓ pCoreOf 2 (MulAction.stabilizer G (cOf Y d)) := by
  have hnorm := (s52_A_normal Y H hZ).1 hd
  have hconj : conjSub d (AOf Y) = AOf Y := (mem_normalizer_iff_conjSub.mp hnorm)
  conv_lhs => rw [← hconj]
  rw [AOf, conjSub_inf, conjSub_d_Q_zero Y hd0,
    conjSub_Q_two_eq (Y := Y) (g := d) (c := cOf Y d) rfl]

private theorem not_Z_neg_one_le_stab_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) :
    ¬ Y.Z (-1) ≤ MulAction.stabilizer G (Y.vert 2) :=
  (Y.s52_step9_cons H hZ).2 (-1) (by norm_num) |>.2.1

private theorem exists_t_Z_neg_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    ∃ t ∈ Y.Z (-1), t ^ 2 = 1 ∧ t • Y.vert 2 ≠ Y.vert 2 := by
  obtain ⟨t, htZ, ht⟩ := Set.not_subset.mp (not_Z_neg_one_le_stab_two Y H hZ)
  refine ⟨t, htZ, ?_, ?_⟩
  · exact (s52_step8_Z Y H hZ (-1) (by norm_num)).1.2 t htZ
  · intro h
    exact ht (MulAction.mem_stabilizer_iff.mpr h)

private theorem Z_neg_one_le_VNbr0 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) :
    Y.Z (-1) ≤ Y.VNbr0 := by
  rw [VNbr0_eq_iSup Y]
  intro z hz
  refine le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V))
    ⟨Y.vert (-1), by simpa using (Y.adj (-1)).symm⟩ ?_
  simpa [Setup.Z_eq_vertZ] using hz

private theorem mul_d_mem_Q_one_of_fixes_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {d g : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3)
    (hd0 : d • Y.vert 0 = Y.vert 2) (hg : g ∈ Y.L 1) (hg1 : g ∈ Y.Gi 1)
    (hg0 : g • Y.vert 0 = Y.vert 0) (hg2 : g • Y.vert 2 ≠ Y.vert 2) :
    g⁻¹ * d * g * d ∈ Y.Q 1 := by
  have hc_adj : Γ.Adj (Y.vert 1) (cOf Y d) := cOf_adj Y hd
  have hc0 : cOf Y d ≠ Y.vert 0 := cOf_ne_zero Y hd3 hd0
  have hc2 : cOf Y d ≠ Y.vert 2 := cOf_ne_two Y hd0
  have hg2adj : Γ.Adj (Y.vert 1) (g • Y.vert 2) := by
    have h := (Y.hyp.adj_smul g (Y.vert 1) (Y.vert 2)).mpr (by simpa using Y.adj 1)
    rwa [MulAction.mem_stabilizer_iff.mp hg1] at h
  have hg2ne0 : g • Y.vert 2 ≠ Y.vert 0 := by
    intro h
    have h' : g • Y.vert 2 = g • Y.vert 0 := by rw [h, hg0]
    exact (vert_zero_ne_vert_two Y).symm (MulAction.injective g h')
  have hg2c : g • Y.vert 2 = cOf Y d :=
    eq_of_adj_one_of_ne Y H hg2adj hc_adj hg2ne0 hg2 hc0 hc2
  have hgc : g • cOf Y d = Y.vert 2 :=
    (smul_third_of_smul_two Y H hg1 hc_adj hc0 hc2 hg0).2 hg2c
  have hg2' : g • Y.vert 2 = cOf Y d := hg2c
  have hginv0 : g⁻¹ • Y.vert 0 = Y.vert 0 := by
    simpa using (congrArg (fun v => g⁻¹ • v) hg0).symm
  have hginv2 : g⁻¹ • Y.vert 2 = cOf Y d := by
    simpa using (congrArg (fun v => g⁻¹ • v) hgc).symm
  have hginvc : g⁻¹ • cOf Y d = Y.vert 2 := by
    simpa using (congrArg (fun v => g⁻¹ • v) hg2').symm
  have e0 : (g⁻¹ * d * g * d) • Y.vert 0 = Y.vert 0 := by
    calc (g⁻¹ * d * g * d) • Y.vert 0
        = g⁻¹ • (d • (g • (d • Y.vert 0))) := by simp only [mul_smul]
      _ = g⁻¹ • (d • (g • Y.vert 2)) := by rw [hd0]
      _ = g⁻¹ • (d • cOf Y d) := by rw [hg2']
      _ = g⁻¹ • Y.vert 0 := by rw [d_smul_cOf Y hd3 hd0]
      _ = Y.vert 0 := hginv0
  have e2 : (g⁻¹ * d * g * d) • Y.vert 2 = Y.vert 2 := by
    calc (g⁻¹ * d * g * d) • Y.vert 2
        = g⁻¹ • (d • (g • (d • Y.vert 2))) := by simp only [mul_smul]
      _ = g⁻¹ • (d • (g • cOf Y d)) := by rw [d_smul_vert_two]
      _ = g⁻¹ • (d • Y.vert 2) := by rw [hgc]
      _ = g⁻¹ • cOf Y d := by rw [d_smul_vert_two]
      _ = Y.vert 2 := hginvc
  have ec : (g⁻¹ * d * g * d) • cOf Y d = cOf Y d := by
    calc (g⁻¹ * d * g * d) • cOf Y d
        = g⁻¹ • (d • (g • (d • cOf Y d))) := by simp only [mul_smul]
      _ = g⁻¹ • (d • (g • Y.vert 0)) := by rw [d_smul_cOf Y hd3 hd0]
      _ = g⁻¹ • (d • Y.vert 0) := by rw [hg0]
      _ = g⁻¹ • Y.vert 2 := by rw [hd0]
      _ = cOf Y d := hginv2
  have heL : g⁻¹ * d * g * d ∈ Y.L 1 := by
    have h1 : g⁻¹ * d ∈ Y.L 1 := (Y.L 1).mul_mem ((Y.L 1).inv_mem hg) hd
    have h2 : g⁻¹ * d * g ∈ Y.L 1 := (Y.L 1).mul_mem h1 hg
    exact (Y.L 1).mul_mem h2 hd
  refine (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).N_fixes_neighbors_mem_Q
    Y.hyp.adj_smul (Y.hyp.finite_stab (Y.vert 1)) (Y.hyp.valency (Y.vert 1)).2
    (Y.hyp.valency (Y.vert 1)).1 (x := ⟨g⁻¹ * d * g * d, heL⟩) ?_
  intro a ha
  by_cases ha0 : a = Y.vert 0
  · rw [ha0]; exact e0
  by_cases ha2 : a = Y.vert 2
  · rw [ha2]; exact e2
  · have hac : a = cOf Y d :=
      eq_of_adj_one_of_ne Y H ha hc_adj ha0 ha2 hc0 hc2
    rw [hac]; exact ec

private theorem mul_d_mem_Q_one_of_fixes_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {d g : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3)
    (hd0 : d • Y.vert 0 = Y.vert 2) (hg : g ∈ Y.L 1) (hg1 : g ∈ Y.Gi 1)
    (hg2 : g • Y.vert 2 = Y.vert 2) (hg0 : g • Y.vert 0 ≠ Y.vert 0) :
    g⁻¹ * d * g * d ∈ Y.Q 1 := by
  have hc_adj : Γ.Adj (Y.vert 1) (cOf Y d) := cOf_adj Y hd
  have hc0 : cOf Y d ≠ Y.vert 0 := cOf_ne_zero Y hd3 hd0
  have hc2 : cOf Y d ≠ Y.vert 2 := cOf_ne_two Y hd0
  have hg0adj : Γ.Adj (Y.vert 1) (g • Y.vert 0) := by
    have h := (Y.hyp.adj_smul g (Y.vert 1) (Y.vert 0)).mpr (by simpa using (Y.adj 0).symm)
    rwa [MulAction.mem_stabilizer_iff.mp hg1] at h
  have hg0ne2 : g • Y.vert 0 ≠ Y.vert 2 := by
    intro h
    have h' : g • Y.vert 0 = g • Y.vert 2 := h.trans hg2.symm
    exact vert_zero_ne_vert_two Y (MulAction.injective g h')
  have hg0c : g • Y.vert 0 = cOf Y d :=
    eq_of_adj_one_of_ne Y H hg0adj hc_adj hg0 hg0ne2 hc0 hc2
  have hgc : g • cOf Y d = Y.vert 0 :=
    (smul_third_of_smul_zero Y H hg1 hc_adj hc0 hc2 hg2).2 hg0c
  have hginv0 : g⁻¹ • Y.vert 0 = cOf Y d := by
    simpa using (congrArg (fun v => g⁻¹ • v) hgc).symm
  have hginv2 : g⁻¹ • Y.vert 2 = Y.vert 2 := by
    simpa using (congrArg (fun v => g⁻¹ • v) hg2).symm
  have hginvc : g⁻¹ • cOf Y d = Y.vert 0 := by
    simpa using (congrArg (fun v => g⁻¹ • v) hg0c).symm
  have e0 : (g⁻¹ * d * g * d) • Y.vert 0 = Y.vert 0 := by
    calc (g⁻¹ * d * g * d) • Y.vert 0
        = g⁻¹ • (d • (g • (d • Y.vert 0))) := by simp only [mul_smul]
      _ = g⁻¹ • (d • (g • Y.vert 2)) := by rw [hd0]
      _ = g⁻¹ • (d • Y.vert 2) := by rw [hg2]
      _ = g⁻¹ • cOf Y d := by rw [d_smul_vert_two]
      _ = Y.vert 0 := hginvc
  have e2 : (g⁻¹ * d * g * d) • Y.vert 2 = Y.vert 2 := by
    calc (g⁻¹ * d * g * d) • Y.vert 2
        = g⁻¹ • (d • (g • (d • Y.vert 2))) := by simp only [mul_smul]
      _ = g⁻¹ • (d • (g • cOf Y d)) := by rw [d_smul_vert_two]
      _ = g⁻¹ • (d • Y.vert 0) := by rw [hgc]
      _ = g⁻¹ • Y.vert 2 := by rw [hd0]
      _ = Y.vert 2 := hginv2
  have ec : (g⁻¹ * d * g * d) • cOf Y d = cOf Y d := by
    calc (g⁻¹ * d * g * d) • cOf Y d
        = g⁻¹ • (d • (g • (d • cOf Y d))) := by simp only [mul_smul]
      _ = g⁻¹ • (d • (g • Y.vert 0)) := by rw [d_smul_cOf Y hd3 hd0]
      _ = g⁻¹ • (d • cOf Y d) := by rw [hg0c]
      _ = g⁻¹ • Y.vert 0 := by rw [d_smul_cOf Y hd3 hd0]
      _ = cOf Y d := hginv0
  have heL : g⁻¹ * d * g * d ∈ Y.L 1 := by
    have h1 : g⁻¹ * d ∈ Y.L 1 := (Y.L 1).mul_mem ((Y.L 1).inv_mem hg) hd
    have h2 : g⁻¹ * d * g ∈ Y.L 1 := (Y.L 1).mul_mem h1 hg
    exact (Y.L 1).mul_mem h2 hd
  refine (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).N_fixes_neighbors_mem_Q
    Y.hyp.adj_smul (Y.hyp.finite_stab (Y.vert 1)) (Y.hyp.valency (Y.vert 1)).2
    (Y.hyp.valency (Y.vert 1)).1 (x := ⟨g⁻¹ * d * g * d, heL⟩) ?_
  intro a ha
  by_cases ha0 : a = Y.vert 0
  · rw [ha0]; exact e0
  by_cases ha2 : a = Y.vert 2
  · rw [ha2]; exact e2
  · have hac : a = cOf Y d :=
      eq_of_adj_one_of_ne Y H ha hc_adj ha0 ha2 hc0 hc2
    rw [hac]; exact ec

private theorem t_not_mem_Q_one (Y : Setup Γ G)
    {t : G} (ht : t • Y.vert 2 ≠ Y.vert 2) : t ∉ Y.Q 1 := by
  intro htQ1
  exact ht (Y.Q_fixes_neighbors_vert 1 (Y.vert 2) (by simpa using Y.adj 1) t htQ1)

private theorem Q_zero_mem_or_mul_t_mem (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {t : G} (htQ0 : t ∈ Y.Q 0) (ht2 : t ^ 2 = 1) (htH : t ∉ Y.Q 0 ⊓ Y.Q 1)
    {q : G} (hq : q ∈ Y.Q 0) :
    q ∈ Y.Q 0 ⊓ Y.Q 1 ∨ q * t ∈ Y.Q 0 ⊓ Y.Q 1 := by
  obtain ⟨a, haQ0, haH, ha⟩ :=
    (Subgroup.relIndex_eq_two_iff_exists_notMem_and.mp (relIndex_Q_zero_inf_Q_one Y H))
  by_cases hqH : q ∈ Y.Q 0 ⊓ Y.Q 1
  · exact Or.inl hqH
  · right
    have hqa : q * a ∈ Y.Q 0 ⊓ Y.Q 1 := by
      rcases ha q hq with h | h
      · exact h
      · exact absurd h hqH
    have hta : t * a ∈ Y.Q 0 ⊓ Y.Q 1 := by
      rcases ha t htQ0 with h | h
      · exact h
      · exact absurd h htH
    have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht2)
    have hqt : q * t = (q * a) * (t * a)⁻¹ := by
      rw [mul_inv_rev, htinv]
      group
    rw [hqt]
    exact (Y.Q 0 ⊓ Y.Q 1).mul_mem hqa ((Y.Q 0 ⊓ Y.Q 1).inv_mem hta)

private theorem Q_zero_inf_Q_one_le_VNbr0_sup_A (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : Y.Q 0 ⊓ Y.Q 1 ≤ Y.VNbr0 ⊔ AOf Y := by
  have h4 : 4 ≤ s := by have := H.five_le; omega
  obtain ⟨t, htZ, ht2, htmove⟩ := exists_t_Z_neg_one Y H hZ
  have htV0 : t ∈ Y.VNbr0 := Z_neg_one_le_VNbr0 Y H hZ htZ
  have htQ0 : t ∈ Y.Q 0 := (VNbr0_props Y H hZ).1 htV0
  have htH : t ∉ Y.Q 0 ⊓ Y.Q 1 := fun h => t_not_mem_Q_one Y htmove h.2
  have hV0N : Y.Gi 0 ≤ Subgroup.normalizer (Y.VNbr0 : Set G) := (VNbr0_props Y H hZ).2.1
  have hQ1G0 : Y.Q 1 ≤ Y.Gi 0 := by simpa using (Y.Q_le_Gi_adj 1).trans inf_le_left
  have hdecomp : Y.Q 0 ⊓ Y.Q 1 ≤
      ⁅(Y.Q 1 ⊓ Y.Q 2 : Subgroup G), Y.Q 0⁆ ⊔ AOf Y := by
    have h := (Q_quot_of_normal_general (X := Y.mirror1.shift 1)
      H.mirror1.char H.mirror1.sing h4).2.2.2.2
    simpa [AOf, inf_comm, inf_left_comm, inf_assoc] using h
  have hcomm : ⁅(Y.Q 1 ⊓ Y.Q 2 : Subgroup G), Y.Q 0⁆ ≤ Y.VNbr0 ⊔ AOf Y := by
    rw [Subgroup.commutator_le]
    intro b hb q hq
    have hbQ1 : b ∈ Y.Q 1 := hb.1
    have hbG0 : b ∈ Y.Gi 0 := hQ1G0 hbQ1
    rcases Q_zero_mem_or_mul_t_mem Y H htQ0 ht2 htH hq with hqH | hqtH
    · exact Subgroup.mem_sup_right (commutator_mem_AOf Y H hZ hbQ1 hqH.2)
    ·
      set h : G := q * t with hh
      have hhQ1 : h ∈ Y.Q 1 := hqtH.2
      have hqeq : q = h * t := by
        rw [hh, mul_assoc, ← pow_two, ht2, mul_one]
      have hbh : ⁅b, h⁆ ∈ AOf Y := commutator_mem_AOf Y H hZ hbQ1 hhQ1
      have hbt : ⁅b, t⁆ ∈ Y.VNbr0 := by
        have hconj : b * t * b⁻¹ ∈ Y.VNbr0 :=
          (Subgroup.mem_normalizer_iff.mp (hV0N hbG0) t).mp htV0
        have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht2)
        have hmem : b * t * b⁻¹ * t⁻¹ ∈ Y.VNbr0 :=
          (Y.VNbr0).mul_mem hconj ((Y.VNbr0).inv_mem htV0)
        simpa [commutatorElement_def, htinv] using hmem
      have hconjbt : h * ⁅b, t⁆ * h⁻¹ ∈ Y.VNbr0 :=
        (Subgroup.mem_normalizer_iff.mp (hV0N (hQ1G0 hhQ1)) ⁅b, t⁆).mp hbt
      have hform : ⁅b, q⁆ = ⁅b, h⁆ * (h * ⁅b, t⁆ * h⁻¹) := by
        rw [hqeq]
        simp only [commutatorElement_def]
        group
      rw [hform]
      exact (Y.VNbr0 ⊔ AOf Y).mul_mem
        ((le_sup_right : (AOf Y : Subgroup G) ≤ Y.VNbr0 ⊔ AOf Y) hbh)
        ((le_sup_left : (Y.VNbr0 : Subgroup G) ≤ Y.VNbr0 ⊔ AOf Y) hconjbt)
  exact hdecomp.trans (sup_le hcomm le_sup_right)

private theorem exists_mul_of_mem_Q_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {y : G} (hy : y ∈ Y.Q 1) :
    ∃ b ∈ Y.Q 2 ⊓ Y.Q 1, ∃ a ∈ Y.Q 0 ⊓ Y.Q 1, y = b * a := by
  have hKle : Y.Q 2 ⊓ Y.Q 1 ≤ Y.Q 1 := inf_le_right
  have hQ1NK : Y.Q 1 ≤ Subgroup.normalizer ((Y.Q 2 ⊓ Y.Q 1 : Subgroup G) : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKle).mp
      (Q_two_inf_Q_one_subgroupOf_normal Y)
  have hHNK : (Y.Q 0 ⊓ Y.Q 1 : Subgroup G) ≤
      Subgroup.normalizer ((Y.Q 2 ⊓ Y.Q 1 : Subgroup G) : Set G) :=
    inf_le_right.trans hQ1NK
  have hy' : y ∈ (Y.Q 2 ⊓ Y.Q 1 : Subgroup G) ⊔ (Y.Q 0 ⊓ Y.Q 1) := by
    rw [sup_comm, ← Q_one_eq_sup Y H]
    exact hy
  obtain ⟨b, hbK, a, haH, hba⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (H := Y.Q 2 ⊓ Y.Q 1) (K := Y.Q 0 ⊓ Y.Q 1) hHNK).mp hy'
  exact ⟨b, hbK, a, haH, hba⟩

private theorem mem_Q_zero_of_commutator_mem_A (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d t : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3)
    (hd0 : d • Y.vert 0 = Y.vert 2) (htV0 : t ∈ Y.VNbr0) (ht2 : t ^ 2 = 1)
    (htc : t • Y.vert 2 = cOf Y d) {y : G} (hy : y ∈ Y.Q 1)
    (hcomm : ⁅t, y⁆ ∈ AOf Y) : y ∈ Y.Q 0 := by
  obtain ⟨-, -, -, -, hZ1sup, -, -, -⟩ := Y.s52_step8 H hZ
  obtain ⟨b, hbK, a, haH, rfl⟩ := exists_mul_of_mem_Q_one Y H hy
  have hbQ1 : b ∈ Y.Q 1 := hbK.2
  have hbL : b ∈ Y.L 1 := (Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).oTwo_le hbQ1
  have haQ0 : a ∈ Y.Q 0 := haH.1
  have hZ0A : Y.Z 0 ≤ AOf Y := by
    calc Y.Z 0 ≤ Y.Z 1 := by
          rw [hZ1sup]
          exact le_sup_left
      _ ≤ AOf Y := Z_one_le_AOf Y H hZ hd hd3
  have htaZ : ⁅t, a⁆ ∈ Y.Z 0 := by
    have hV0Q0 : ⁅(Y.VNbr0 : Subgroup G), (Y.Q 0 : Subgroup G)⁆ ≤ Y.Z 0 := by
      rw [Subgroup.commutator_comm]
      exact (VNbr0_props Y H hZ).2.2.1
    exact hV0Q0 (Subgroup.commutator_mem_commutator htV0 haQ0)
  have htaA : ⁅t, a⁆ ∈ AOf Y := hZ0A htaZ
  have hconj : b * ⁅t, a⁆ * b⁻¹ ∈ AOf Y :=
    (Subgroup.mem_normalizer_iff.mp ((s52_A_normal Y H hZ).1 hbL) ⁅t, a⁆).mp htaA
  have hform : ⁅t, b * a⁆ = ⁅t, b⁆ * (b * ⁅t, a⁆ * b⁻¹) := by
    simp only [commutatorElement_def]
    group
  have htbA : ⁅t, b⁆ ∈ AOf Y := by
    have heq : ⁅t, b⁆ = ⁅t, b * a⁆ * (b * ⁅t, a⁆ * b⁻¹)⁻¹ := by
      rw [hform]; group
    rw [heq]
    exact (AOf Y).mul_mem hcomm ((AOf Y).inv_mem hconj)
  have htbtQ2 : t * b * t⁻¹ ∈ Y.Q 2 := by
    have hmem : ⁅t, b⁆ * b ∈ Y.Q 2 :=
      (Y.Q 2).mul_mem ((Subgroup.mem_inf.mp htbA).2) hbK.1
    simpa [commutatorElement_def, mul_assoc] using hmem
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht2)
  have hbconj : b ∈ conjSub t⁻¹ (Y.Q 2) := by
    rw [mem_conjSub]
    simpa [htinv] using htbtQ2
  have hQc : conjSub t⁻¹ (Y.Q 2) = pCoreOf 2 (MulAction.stabilizer G (cOf Y d)) :=
    conjSub_Q_two_eq Y (by rw [htinv]; exact htc)
  have hbA : b ∈ AOf Y := by
    rw [AOf_eq_Q_two_inf Y H hZ hd hd0]
    exact ⟨hbK.1, hQc ▸ hbconj⟩
  exact (Y.Q 0).mul_mem ((Subgroup.mem_inf.mp hbA).1) haQ0

private theorem exists_t_smul_two_eq_cOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3)
    (hd0 : d • Y.vert 0 = Y.vert 2) :
    ∃ t : G, t ∈ Y.VNbr0 ∧ t ^ 2 = 1 ∧ t • Y.vert 2 = cOf Y d ∧
      t ∈ Y.L 1 ∧ t ∈ Y.Gi 1 ∧ t • Y.vert 0 = Y.vert 0 ∧ t⁻¹ = t ∧
        t • Y.vert 2 ≠ Y.vert 2 ∧ conjSub t (Y.Q 1) = Y.Q 1 := by
  obtain ⟨t, htZ, ht2, htmove⟩ := exists_t_Z_neg_one Y H hZ
  have htV0 : t ∈ Y.VNbr0 := Z_neg_one_le_VNbr0 Y H hZ htZ
  have htL : t ∈ Y.L 1 := VNbr0_le_L_one Y H hZ htV0
  have htG1 : t ∈ Y.Gi 1 := VNbr0_le_Gi_one Y H hZ htV0
  have ht0 : t • Y.vert 0 = Y.vert 0 :=
    MulAction.mem_stabilizer_iff.mp
      (((VNbr0_props Y H hZ).1.trans (Y.Q_le_Gi 0)) htV0)
  have htadj : Γ.Adj (Y.vert 1) (t • Y.vert 2) := by
    have h := (Y.hyp.adj_smul t (Y.vert 1) (Y.vert 2)).mpr (by simpa using Y.adj 1)
    rwa [MulAction.mem_stabilizer_iff.mp htG1] at h
  have ht2ne0 : t • Y.vert 2 ≠ Y.vert 0 := by
    intro h
    have h' : t • Y.vert 2 = t • Y.vert 0 := h.trans ht0.symm
    exact vert_zero_ne_vert_two Y (MulAction.injective t h'.symm)
  have ht2c : t • Y.vert 2 = cOf Y d :=
    eq_of_adj_one_of_ne Y H htadj (cOf_adj Y hd) ht2ne0 htmove
      (cOf_ne_zero Y hd3 hd0) (cOf_ne_two Y hd0)
  have htinv : t⁻¹ = t := inv_eq_of_mul_eq_one_right (by simpa [pow_two] using ht2)
  have hQ1N : Y.Gi 1 ≤ Subgroup.normalizer (Y.Q 1 : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y.Gi 1)
  have hconjQ1 : conjSub t (Y.Q 1) = Y.Q 1 :=
    mem_normalizer_iff_conjSub.mp (hQ1N htG1)
  exact ⟨t, htV0, ht2, ht2c, htL, htG1, ht0, htinv, htmove, hconjQ1⟩

private theorem commutator_d_eq_conj_commutator {d t x u e : G}
    (hu : u = x * (t * x * t⁻¹)) (he : e = t⁻¹ * d * t * d) (htinv : t⁻¹ = t)
    (ht2 : t * t = 1) (hxd : x * d = d * x) (hdx : d * x * d⁻¹ = x) :
    ⁅d, u⁆ = (x * t) * ⁅e, x⁆ * (x * t)⁻¹ := by
  rw [hu, he]
  simp only [commutatorElement_def]
  rw [htinv]
  simp only [mul_inv_rev, inv_inv, htinv]
  group
  rw [mul_assoc x t t, ht2, mul_one]
  have hR : x * d * t * d * x * d⁻¹ * t * d⁻¹ * t * x⁻¹ * t * x⁻¹ =
      d * x * t * x * t * d⁻¹ * t * x⁻¹ * t * x⁻¹ := by
    calc x * d * t * d * x * d⁻¹ * t * d⁻¹ * t * x⁻¹ * t * x⁻¹
        = d * x * t * d * x * d⁻¹ * t * d⁻¹ * t * x⁻¹ * t * x⁻¹ := by rw [hxd]
      _ = d * x * t * (d * x * d⁻¹) * t * d⁻¹ * t * x⁻¹ * t * x⁻¹ := by group
      _ = d * x * t * x * t * d⁻¹ * t * x⁻¹ * t * x⁻¹ := by rw [hdx]
  simpa using hR.symm

private theorem mem_AOf_of_conj_mem (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d u : G} (hd : d ∈ Y.L 1) (hd0 : d • Y.vert 0 = Y.vert 2)
    (huQ0 : u ∈ Y.Q 0) (hduA : ⁅d, u⁆ ∈ AOf Y) : u ∈ AOf Y := by
  have hdudQ0 : d * u * d⁻¹ ∈ Y.Q 0 := by
    have h := (Y.Q 0).mul_mem ((Subgroup.mem_inf.mp hduA).1) huQ0
    simpa [commutatorElement_def, mul_assoc] using h
  have hdudQ2 : d * u * d⁻¹ ∈ Y.Q 2 := by
    have h := mul_mem_conjSub (g := d) (H := Y.Q 0) huQ0
    rwa [conjSub_d_Q_zero Y hd0] at h
  have hdudA : d * u * d⁻¹ ∈ AOf Y := Subgroup.mem_inf.mpr ⟨hdudQ0, hdudQ2⟩
  have hnorm : conjSub d⁻¹ (AOf Y) = AOf Y :=
    mem_normalizer_iff_conjSub.mp ((s52_A_normal Y H hZ).1 ((Y.L 1).inv_mem hd))
  have hmem : u ∈ conjSub d⁻¹ (AOf Y) := by
    rw [mem_conjSub]
    simpa using hdudA
  rwa [hnorm] at hmem

private theorem C_Q_one_d_le_A (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3)
    (hd0 : d • Y.vert 0 = Y.vert 2) :
    ∀ x ∈ Y.Q 1, x ∈ Subgroup.centralizer ({d} : Set G) → x ∈ AOf Y := by
  obtain ⟨t, htV0, ht2, ht2c, htL, htG1, ht0, htinv, htmove, hconjQ1⟩ :=
    exists_t_smul_two_eq_cOf Y H hZ hd hd3 hd0
  have ht2' : t * t = 1 := by simpa [pow_two] using ht2
  intro x hx hxcent
  have hxd : x * d = d * x := Subgroup.mem_centralizer_singleton_iff.mp hxcent
  have htx : t * x * t⁻¹ ∈ Y.Q 1 := by
    have h := mul_mem_conjSub (g := t) (H := Y.Q 1) hx
    rwa [hconjQ1] at h
  set u : G := x * (t * x * t⁻¹) with hu
  have huQ1 : u ∈ Y.Q 1 := (Y.Q 1).mul_mem hx htx
  have htu : ⁅t, u⁆ = ⁅t * x * t⁻¹, x⁆ := by
    rw [hu, htinv]
    simp only [commutatorElement_def]
    simp only [mul_inv_rev, inv_inv, htinv]
    group
    simp only [mul_assoc, ht2', mul_one]
  have hcomm : ⁅t, u⁆ ∈ AOf Y := by
    rw [htu]
    exact commutator_mem_AOf Y H hZ htx hx
  have huQ0 : u ∈ Y.Q 0 :=
    mem_Q_zero_of_commutator_mem_A Y H hZ hd hd3 hd0 htV0 ht2 ht2c huQ1 hcomm
  set e : G := t⁻¹ * d * t * d with he
  have heQ1 : e ∈ Y.Q 1 := by
    rw [he]
    exact mul_d_mem_Q_one_of_fixes_zero Y H hd hd3 hd0 htL htG1 ht0 htmove
  have hdx' : d * x * d⁻¹ = x := by
    rw [← hxd]
    group
  have hdu : ⁅d, u⁆ = (x * t) * ⁅e, x⁆ * (x * t)⁻¹ :=
    commutator_d_eq_conj_commutator hu he htinv ht2' hxd hdx'
  have hxt : x * t ∈ Y.L 1 :=
    (Y.L 1).mul_mem ((Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).oTwo_le hx) htL
  have hwA : ⁅e, x⁆ ∈ AOf Y := commutator_mem_AOf Y H hZ heQ1 hx
  have hconjA : (x * t) * ⁅e, x⁆ * (x * t)⁻¹ ∈ AOf Y :=
    (Subgroup.mem_normalizer_iff.mp ((s52_A_normal Y H hZ).1 hxt) ⁅e, x⁆).mp hwA
  have hduA : ⁅d, u⁆ ∈ AOf Y := by
    rw [hdu]
    exact hconjA
  have huA : u ∈ AOf Y := mem_AOf_of_conj_mem Y H hZ hd hd0 huQ0 hduA
  have htxeq : ⁅t, x⁆ = (x⁻¹ * u * x) * (x ^ 2)⁻¹ := by
    rw [hu]
    simp only [commutatorElement_def]
    rw [htinv]
    group
  have h1 : x⁻¹ * u * x ∈ AOf Y := by
    have hxL : x⁻¹ ∈ Y.L 1 :=
      (Y.L 1).inv_mem ((Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).oTwo_le hx)
    have h := (Subgroup.mem_normalizer_iff.mp ((s52_A_normal Y H hZ).1 hxL) u).mp huA
    simpa using h
  have h2 : (x ^ 2)⁻¹ ∈ AOf Y := (AOf Y).inv_mem (sq_mem_AOf Y hx)
  have htxA : ⁅t, x⁆ ∈ AOf Y := by
    rw [htxeq]
    exact (AOf Y).mul_mem h1 h2
  have hxQ0 : x ∈ Y.Q 0 :=
    mem_Q_zero_of_commutator_mem_A Y H hZ hd hd3 hd0 htV0 ht2 ht2c hx htxA
  have hxQ2 : x ∈ Y.Q 2 := by
    have hmem : x ∈ conjSub d (Y.Q 0) := by
      rw [mem_conjSub]
      have hcomm' : d⁻¹ * x * d = x := by
        calc d⁻¹ * x * d = d⁻¹ * (x * d) := by group
          _ = d⁻¹ * (d * x) := by rw [hxd]
          _ = x := by group
      rw [hcomm']
      exact hxQ0
    rwa [conjSub_d_Q_zero Y hd0] at hmem
  exact Subgroup.mem_inf.mpr ⟨hxQ0, hxQ2⟩

private theorem DOf_le_AOf (Y : Setup Γ G) (d : G) : DOf Y d ≤ AOf Y := inf_le_left

private theorem sq_mem_DOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) {a : G} (ha : a ∈ AOf Y) :
    a ^ 2 ∈ DOf Y d := by
  obtain ⟨δ, hδ, z, hz, haz⟩ := exists_DOf_mul_Z_one Y H hZ hd hd3 ha
  rw [haz]
  have hz2 : z ^ 2 = 1 := (s52_step8_Z Y H hZ 1 (by norm_num)).1.2 z hz
  have hcent : z * δ = δ * z :=
    (Subgroup.mem_centralizer_iff.mp (Z_one_le_centralizer_AOf Y H hZ hz) δ
      (DOf_le_AOf Y d hδ)).symm
  have hz2' : z * z = 1 := by simpa [pow_two] using hz2
  have hsq : (δ * z) ^ 2 = δ ^ 2 := by
    rw [pow_two]
    calc δ * z * (δ * z) = δ * (z * δ) * z := by group
      _ = δ * (δ * z) * z := by rw [hcent]
      _ = δ * δ * (z * z) := by group
      _ = δ * δ := by rw [hz2', mul_one]
    rw [pow_two]
  rw [hsq]
  exact (DOf Y d).pow_mem hδ 2

private theorem DOf_subgroupOf_normal (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    ((DOf Y d).subgroupOf (AOf Y)).Normal := by
  refine ⟨fun x hx y => ?_⟩
  have hxA : (x : ↥(AOf Y)).1 ∈ AOf Y := (x : ↥(AOf Y)).2
  have hxD : (x : ↥(AOf Y)).1 ∈ DOf Y d := hx
  have hyA : (y : G) ∈ AOf Y := y.2
  obtain ⟨δ, hδ, z, hz, hyz⟩ := exists_DOf_mul_Z_one Y H hZ hd hd3 hyA
  have hcent : z * (x : ↥(AOf Y)).1 = (x : ↥(AOf Y)).1 * z :=
    (Subgroup.mem_centralizer_iff.mp (Z_one_le_centralizer_AOf Y H hZ hz)
      (x : ↥(AOf Y)).1 (DOf_le_AOf Y d hxD)).symm
  have hconj : (y : G) * (x : ↥(AOf Y)).1 * (y : G)⁻¹ =
      δ * (x : ↥(AOf Y)).1 * δ⁻¹ := by
    rw [hyz]
    calc δ * z * (x : ↥(AOf Y)).1 * (δ * z)⁻¹
        = δ * (z * (x : ↥(AOf Y)).1 * z⁻¹) * δ⁻¹ := by group
      _ = δ * (x : ↥(AOf Y)).1 * δ⁻¹ := by rw [hcent]; group
  rw [Subgroup.mem_subgroupOf]
  change (y : G) * (x : G) * (y : G)⁻¹ ∈ DOf Y d
  rw [hconj]
  exact (DOf Y d).mul_mem ((DOf Y d).mul_mem hδ hxD) ((DOf Y d).inv_mem hδ)

private theorem commutator_AOf_le_DOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    ⁅AOf Y, AOf Y⁆ ≤ DOf Y d := by
  have hDA : DOf Y d ≤ AOf Y := DOf_le_AOf Y d
  have hZA : Y.Z 1 ≤ AOf Y := Z_one_le_AOf Y H hZ hd hd3
  have hAZ : AOf Y = DOf Y d ⊔ Y.Z 1 := AOf_eq_DOf_sup_Z_one Y H hZ hd hd3
  have hDnorm : ((DOf Y d).subgroupOf (AOf Y)).Normal :=
    DOf_subgroupOf_normal Y H hZ hd hd3
  have hsup : (DOf Y d).subgroupOf (AOf Y) ⊔ (Y.Z 1).subgroupOf (AOf Y) = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hDA hZA]
    rw [← hAZ, Subgroup.subgroupOf_self]
  have hZcomm : IsMulCommutative ↥((Y.Z 1).subgroupOf (AOf Y)) := by
    refine ⟨⟨fun x y => Subtype.ext (Subtype.ext ?_)⟩⟩
    exact Y.Z_commute 1 (x : ↥(AOf Y)).1 (Subgroup.mem_subgroupOf.mp x.2)
      (y : ↥(AOf Y)).1 (Subgroup.mem_subgroupOf.mp y.2)
  have h := Subgroup.Normal.commutator_le_of_self_sup_commutative_eq_top
    (N := (DOf Y d).subgroupOf (AOf Y)) (H := (Y.Z 1).subgroupOf (AOf Y))
    hsup hZcomm
  have hmap := Subgroup.map_mono (f := (AOf Y).subtype) h
  rwa [Subgroup.map_subtype_commutator,
    Subgroup.map_subgroupOf_eq_of_le hDA] at hmap

private def sqSet (Y : Setup Γ G) : Set G := {x | ∃ a ∈ AOf Y, x = a ^ 2}

private def commSet (Y : Setup Γ G) : Set G :=
  {x | ∃ a ∈ AOf Y, ∃ b ∈ AOf Y, x = ⁅a, b⁆}

private def NOf (Y : Setup Γ G) : Subgroup G := Subgroup.closure (sqSet Y ∪ commSet Y)

private theorem NOf_le_DOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) : NOf Y ≤ DOf Y d := by
  rw [NOf, Subgroup.closure_le]
  rintro x (hx | hx)
  · rcases hx with ⟨a, ha, rfl⟩
    exact sq_mem_DOf Y H hZ hd hd3 ha
  · rcases hx with ⟨a, ha, b, hb, rfl⟩
    exact commutator_AOf_le_DOf Y H hZ hd hd3
      (Subgroup.commutator_mem_commutator ha hb)

private theorem conjSub_NOf_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {l : G} (hl : l ∈ Y.L 1) : conjSub l (NOf Y) ≤ NOf Y := by
  rw [NOf, conjSub, MonoidHom.map_closure, Subgroup.closure_le]
  rintro x ⟨s, hs, rfl⟩
  have hnorm := (s52_A_normal Y H hZ).1 hl
  rcases hs with hs | hs
  · rcases hs with ⟨a, ha, rfl⟩
    have ha' : l * a * l⁻¹ ∈ AOf Y :=
      (Subgroup.mem_normalizer_iff.mp hnorm a).mp ha
    refine Subgroup.subset_closure (Or.inl ⟨l * a * l⁻¹, ha', ?_⟩)
    rw [map_pow]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, pow_two, mul_assoc]
  · rcases hs with ⟨a, ha, b, hb, rfl⟩
    have ha' : l * a * l⁻¹ ∈ AOf Y :=
      (Subgroup.mem_normalizer_iff.mp hnorm a).mp ha
    have hb' : l * b * l⁻¹ ∈ AOf Y :=
      (Subgroup.mem_normalizer_iff.mp hnorm b).mp hb
    refine Subgroup.subset_closure (Or.inr ⟨l * a * l⁻¹, ha', l * b * l⁻¹, hb', ?_⟩)
    rw [map_commutatorElement]
    simp only [commutatorElement_def, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, mul_assoc]

private theorem L_one_le_normalizer_NOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : Y.L 1 ≤ Subgroup.normalizer (NOf Y : Set G) := by
  intro l hl
  refine mem_normalizer_iff_conjSub.mpr ?_
  have h1 := conjSub_NOf_le Y H hZ hl
  have h2 := conjSub_NOf_le Y H hZ ((Y.L 1).inv_mem hl)
  have h3 : NOf Y ≤ conjSub l (NOf Y) := by
    calc NOf Y = conjSub l (conjSub l⁻¹ (NOf Y)) := by
          rw [conjSub_inv_conjSub]
      _ ≤ conjSub l (NOf Y) := conjSub_mono l h2
  exact le_antisymm h1 h3

private theorem NOf_eq_bot (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) : NOf Y = ⊥ := by
  obtain ⟨-, -, -, -, hZ1sup, -, -, -⟩ := Y.s52_step8 H hZ
  haveI : Finite ↥(Y.S) :=
    finite_of_le_stabilizer Y.hyp (H := Y.S)
      ((Y.isSylowTwoOf_edgeSylow 0).1.trans inf_le_left)
  have hSp : IsPGroup 2 Y.S :=
    pCoreOf_isPGroup' (Y.Gi 0 ⊓ Y.Gi 1)
  have hNleD : NOf Y ≤ DOf Y d := NOf_le_DOf Y H hZ hd hd3
  have hNleS : NOf Y ≤ Y.S := by
    refine hNleD.trans ?_
    refine (DOf_le_AOf Y d).trans ?_
    exact (AOf_le_Q_one Y).trans (Q_one_le_S Y)
  have hSleL : Y.S ≤ Y.L 1 := by
    have hSG1 : Y.S ≤ Y.Gi 1 := by
      rw [← Y.edgeSylow_zero]
      exact (Y.isSylowTwoOf_edgeSylow 0).1.trans inf_le_right
    exact le_oTwoPrime_of_isPGroup hSp hSG1
  have hnorm : Y.S ≤ Subgroup.normalizer (NOf Y : Set G) :=
    hSleL.trans (L_one_le_normalizer_NOf Y H hZ)
  by_contra hne
  haveI : Finite ↥(NOf Y) :=
    Finite.of_injective (Subgroup.inclusion hNleS) (Subgroup.inclusion_injective hNleS)
  obtain ⟨z, hzN, hzne, hzcent⟩ := CFSG.GroupTheory.exists_ne_one_commute_of_normalizes hSp
    (hSp.to_le hNleS) hne fun g hg o ho => (Subgroup.mem_normalizer_iff.mp (hnorm hg) o).mp ho
  have hzS : z ∈ Y.S := hNleS hzN
  have hzZ0 : z ∈ Y.Z 0 := by
    have hcenter : Y.Z 0 = centerOf Y.S := ((Y.s52_step8 H hZ).2.1).symm
    rw [hcenter, centerOf]
    refine Subgroup.mem_inf.mpr ⟨hzS, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    exact hzcent s hs
  have hZ0Z1 : Y.Z 0 ≤ Y.Z 1 := by
    rw [hZ1sup]
    exact le_sup_left
  have hzD : z ∈ DOf Y d := hNleD hzN
  have hbot : z ∈ (⊥ : Subgroup G) := by
    have hmem : z ∈ DOf Y d ⊓ Y.Z 1 := Subgroup.mem_inf.mpr ⟨hzD, hZ0Z1 hzZ0⟩
    rwa [DOf_inf_Z_one Y H hZ hd hd3] at hmem
  exact hzne (Subgroup.mem_bot.mp hbot)

private theorem isElemAbelian_AOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) : IsElemAbelian 2 (AOf Y) := by
  have hNbot : NOf Y = ⊥ := NOf_eq_bot Y H hZ hd hd3
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun a ha => ?_⟩
  · have hcomm : ⁅(a : G), (b : G)⁆ ∈ NOf Y :=
      Subgroup.subset_closure (Or.inr ⟨(a : G), a.2, (b : G), b.2, rfl⟩)
    rw [hNbot, Subgroup.mem_bot] at hcomm
    exact commutatorElement_eq_one_iff_mul_comm.mp hcomm
  · have hsq : a ^ 2 ∈ NOf Y := Subgroup.subset_closure (Or.inl ⟨a, ha, rfl⟩)
    rw [hNbot, Subgroup.mem_bot] at hsq
    exact hsq

private theorem Q_zero_eq_DOf_sup_VNbr0 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    Y.Q 0 = DOf Y d ⊔ Y.VNbr0 := by
  obtain ⟨t, htZ, ht2, htmove⟩ := exists_t_Z_neg_one Y H hZ
  have htV0 : t ∈ Y.VNbr0 := Z_neg_one_le_VNbr0 Y H hZ htZ
  have htQ0 : t ∈ Y.Q 0 := (VNbr0_props Y H hZ).1 htV0
  have htH : t ∉ Y.Q 0 ⊓ Y.Q 1 := fun h => t_not_mem_Q_one Y htmove h.2
  have hHle : Y.Q 0 ⊓ Y.Q 1 ≤ DOf Y d ⊔ Y.VNbr0 :=
    (Q_zero_inf_Q_one_le_VNbr0_sup_A Y H hZ).trans
      (sup_le le_sup_right (AOf_le_DOf_sup_VNbr0 Y H hZ hd hd3))
  refine le_antisymm ?_ (sup_le ((DOf_le_AOf Y d).trans inf_le_left)
    (VNbr0_props Y H hZ).1)
  intro q hq
  rcases Q_zero_mem_or_mul_t_mem Y H htQ0 ht2 htH hq with hqH | hqtH
  · exact hHle hqH
  · have hqt : q * t ∈ DOf Y d ⊔ Y.VNbr0 := hHle hqtH
    have ht : t ∈ DOf Y d ⊔ Y.VNbr0 :=
      (le_sup_right : (Y.VNbr0 : Subgroup G) ≤ DOf Y d ⊔ Y.VNbr0) htV0
    have hqeq : q = (q * t) * t := by
      rw [mul_assoc, ← pow_two, ht2, mul_one]
    rw [hqeq]
    exact (DOf Y d ⊔ Y.VNbr0).mul_mem hqt ht

private theorem commutator_Q_zero_eq_Z_zero_of_orderOf_eq_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    ⁅Y.Q 0, Y.Q 0⁆ = Y.Z 0 := by
  have hQ0eq : Y.Q 0 = DOf Y d ⊔ Y.VNbr0 :=
    Q_zero_eq_DOf_sup_VNbr0 Y H hZ hd hd3
  have hDleL0 : DOf Y d ≤ Y.L 0 :=
    (DOf_le_AOf Y d).trans (inf_le_left.trans (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le)
  have hV0leL0 : Y.VNbr0 ≤ Y.L 0 :=
    (VNbr0_props Y H hZ).1.trans (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le
  have hcenter : Y.Z 0 = centerOf (Y.L 0) := (Y.s52_step8 H hZ).1
  have hL0C : Y.L 0 ≤ Subgroup.centralizer (Y.Z 0 : Set G) := by
    intro l hl
    rw [Subgroup.mem_centralizer_iff]
    intro z hz
    have hz' : z ∈ centerOf (Y.L 0) := by rwa [← hcenter]
    exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hz').2 l hl).symm
  have hSN : Subgroup.closure ((DOf Y d : Set G) ∪ (Y.VNbr0 : Set G)) ≤
      Subgroup.normalizer (Y.Z 0 : Set G) := by
    rw [← Subgroup.sup_eq_closure]
    exact sup_le (hDleL0.trans (hL0C.trans (Subgroup.centralizer_le_normalizer _)))
      (hV0leL0.trans (hL0C.trans (Subgroup.centralizer_le_normalizer _)))
  have hZ0Q0 : ⁅(Y.VNbr0 : Subgroup G), (Y.Q 0 : Subgroup G)⁆ ≤ Y.Z 0 := by
    rw [Subgroup.commutator_comm]
    exact (VNbr0_props Y H hZ).2.2.1
  have hcomm1 : ∀ s ∈ ((DOf Y d : Set G) ∪ (Y.VNbr0 : Set G)),
      ∀ k ∈ (DOf Y d : Subgroup G), ⁅s, k⁆ ∈ Y.Z 0 := by
    intro s hs k hk
    rcases hs with hs | hs
    · have hcomm : s * k = k * s :=
        (isElemAbelian_AOf Y H hZ hd hd3).comm (DOf_le_AOf Y d hs) (DOf_le_AOf Y d hk)
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
      exact (Y.Z 0).one_mem
    · exact hZ0Q0 (Subgroup.commutator_mem_commutator hs
        ((Subgroup.mem_inf.mp (DOf_le_AOf Y d hk)).1))
  have hQD : ⁅Subgroup.closure ((DOf Y d : Set G) ∪ (Y.VNbr0 : Set G)),
      (DOf Y d : Subgroup G)⁆ ≤ Y.Z 0 :=
    CFSG.Quasithin.D14.commutator_closure_le hSN hcomm1
  have hQ0closure : Y.Q 0 =
      Subgroup.closure ((DOf Y d : Set G) ∪ (Y.VNbr0 : Set G)) := by
    rw [hQ0eq, Subgroup.sup_eq_closure]
  have hQD' : ⁅(Y.Q 0 : Subgroup G), (DOf Y d : Subgroup G)⁆ ≤ Y.Z 0 := by
    rw [hQ0closure]
    exact hQD
  have hcomm2 : ∀ s ∈ ((DOf Y d : Set G) ∪ (Y.VNbr0 : Set G)),
      ∀ k ∈ (Y.Q 0 : Subgroup G), ⁅s, k⁆ ∈ Y.Z 0 := by
    intro s hs k hk
    rcases hs with hs | hs
    · have hmem : ⁅s, k⁆ ∈ ⁅(DOf Y d : Subgroup G), (Y.Q 0 : Subgroup G)⁆ :=
        Subgroup.commutator_mem_commutator hs hk
      rw [Subgroup.commutator_comm] at hmem
      exact hQD' hmem
    · exact hZ0Q0 (Subgroup.commutator_mem_commutator hs hk)
  have hfull : ⁅Y.Q 0, Y.Q 0⁆ ≤ Y.Z 0 := by
    have h := CFSG.Quasithin.D14.commutator_closure_le (S :=
      ((DOf Y d : Set G) ∪ (Y.VNbr0 : Set G))) (K := (Y.Q 0 : Subgroup G))
      (N := Y.Z 0) hSN hcomm2
    rw [hQ0closure] at h
    rw [hQ0closure]
    exact h
  have hZ0le : Y.Z 0 ≤ ⁅Y.Q 0, Y.Q 0⁆ := by
    rw [← (VNbr0_props Y H hZ).2.2.2]
    exact Subgroup.commutator_mono (VNbr0_props Y H hZ).1 (VNbr0_props Y H hZ).1
  exact le_antisymm hfull hZ0le

private theorem le_Q_one_of_fixes_zero_two (Y : Setup Γ G)
    {P : Subgroup G} (hP : IsPGroup 2 P) (hPG1 : P ≤ Y.Gi 1)
    (hf0 : ∀ y ∈ P, y • Y.vert 0 = Y.vert 0)
    (hf2 : ∀ y ∈ P, y • Y.vert 2 = Y.vert 2) : P ≤ Y.Q 1 :=
  le_pCoreOf_of_isPGroup_fixes_two Y.hyp hP hPG1 (Y.adj 0).symm (Y.adj 1)
    (vert_zero_ne_vert_two Y) hf0 hf2




private theorem conj_mem_centralizer_d {d g e δ : G}
    (he : e = g⁻¹ * d * g * d) (hδd : d * δ = δ * d) (hδe : e * δ = δ * e) :
    g * δ * g⁻¹ ∈ Subgroup.centralizer ({d} : Set G) := by
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hgd : g⁻¹ * d * g = e * d⁻¹ := by rw [he]; group
  have hδdinv : d⁻¹ * δ = δ * d⁻¹ := by
    have h1 : δ * d⁻¹ = d⁻¹ * δ := by
      calc δ * d⁻¹ = d⁻¹ * (d * δ) * d⁻¹ := by group
        _ = d⁻¹ * (δ * d) * d⁻¹ := by rw [hδd]
        _ = d⁻¹ * δ := by group
    exact h1.symm
  calc g * δ * g⁻¹ * d = g * δ * (g⁻¹ * d * g) * g⁻¹ := by group
    _ = g * δ * (e * d⁻¹) * g⁻¹ := by rw [hgd]
    _ = g * (δ * e) * d⁻¹ * g⁻¹ := by group
    _ = g * (e * δ) * d⁻¹ * g⁻¹ := by rw [hδe]
    _ = g * e * (δ * d⁻¹) * g⁻¹ := by group
    _ = g * e * (d⁻¹ * δ) * g⁻¹ := by rw [hδdinv]
    _ = g * (e * d⁻¹) * δ * g⁻¹ := by group
    _ = g * (g⁻¹ * d * g) * δ * g⁻¹ := by rw [hgd]
    _ = d * (g * δ * g⁻¹) := by group

private theorem commute_of_mem_DOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d δ g e : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) (hδD : δ ∈ DOf Y d)
    (hδCenter : δ ∈ centerOf (Y.Q 1)) (he : e = g⁻¹ * d * g * d) (heQ1 : e ∈ Y.Q 1)
    (hcommA : ⁅g, δ⁆ ∈ AOf Y) (hcommZ1 : ⁅g, δ⁆ ∈ Y.Z 1) : g * δ = δ * g := by
  have hδd : d * δ = δ * d :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hδD).2) d (by simp)
  have hδe : e * δ = δ * e :=
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hδCenter).2) e heQ1
  have hcommC : g * δ * g⁻¹ ∈ Subgroup.centralizer ({d} : Set G) :=
    conj_mem_centralizer_d he hδd hδe
  have hcommD : ⁅g, δ⁆ ∈ DOf Y d := Subgroup.mem_inf.mpr ⟨hcommA, by
    have hδcd : δ ∈ Subgroup.centralizer ({d} : Set G) := (Subgroup.mem_inf.mp hδD).2
    have hcomm : ⁅g, δ⁆ = (g * δ * g⁻¹) * δ⁻¹ := rfl
    rw [hcomm]
    exact (Subgroup.centralizer ({d} : Set G)).mul_mem hcommC
      ((Subgroup.centralizer ({d} : Set G)).inv_mem hδcd)⟩
  have hbot : ⁅g, δ⁆ ∈ (⊥ : Subgroup G) := by
    have hmem : ⁅g, δ⁆ ∈ DOf Y d ⊓ Y.Z 1 := Subgroup.mem_inf.mpr ⟨hcommD, hcommZ1⟩
    rwa [DOf_inf_Z_one Y H hZ hd hd3] at hmem
  exact commutatorElement_eq_one_iff_mul_comm.mp (Subgroup.mem_bot.mp hbot)

private theorem VNbr0_le_centralizer_of_mem_DOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d δ : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3)
    (hd0 : d • Y.vert 0 = Y.vert 2) (hδD : δ ∈ DOf Y d)
    (hδCenter : δ ∈ centerOf (Y.Q 1)) :
    Y.VNbr0 ≤ Subgroup.centralizer ({δ} : Set G) := by
  obtain ⟨-, -, -, -, hZ1sup, -, -, -⟩ := Y.s52_step8 H hZ
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hgV0p : IsPGroup 2 (Subgroup.zpowers g) :=
    (VNbr0_isPGroup Y H hZ).to_le (Subgroup.zpowers_le.mpr hg)
  have hV0Q0 : Y.VNbr0 ≤ Y.Q 0 := (VNbr0_props Y H hZ).1
  have hV0G1 : Y.VNbr0 ≤ Y.Gi 1 := VNbr0_le_Gi_one Y H hZ
  have hV0L : Y.VNbr0 ≤ Y.L 1 := VNbr0_le_L_one Y H hZ
  have hZ0Q0 : ⁅(Y.VNbr0 : Subgroup G), (Y.Q 0 : Subgroup G)⁆ ≤ Y.Z 0 := by
    rw [Subgroup.commutator_comm]
    exact (VNbr0_props Y H hZ).2.2.1
  by_cases hg2 : g • Y.vert 2 = Y.vert 2
  · have hg0 : g • Y.vert 0 = Y.vert 0 :=
      MulAction.mem_stabilizer_iff.mp ((hV0Q0.trans (Y.Q_le_Gi 0)) hg)
    have hgP0 : ∀ y ∈ Subgroup.zpowers g, y • Y.vert 0 = Y.vert 0 := fun y hy =>
      MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr
        (MulAction.mem_stabilizer_iff.mpr hg0) hy)
    have hgP2 : ∀ y ∈ Subgroup.zpowers g, y • Y.vert 2 = Y.vert 2 := fun y hy =>
      MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr
        (MulAction.mem_stabilizer_iff.mpr hg2) hy)
    have hgQ1 : g ∈ Y.Q 1 :=
      le_Q_one_of_fixes_zero_two Y hgV0p
        (Subgroup.zpowers_le.mpr (hV0G1 hg)) hgP0 hgP2 (Subgroup.mem_zpowers g)
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hδCenter).2 g hgQ1
  · have hg0 : g • Y.vert 0 = Y.vert 0 :=
      MulAction.mem_stabilizer_iff.mp ((hV0Q0.trans (Y.Q_le_Gi 0)) hg)
    have hgL : g ∈ Y.L 1 := hV0L hg
    have hgG1 : g ∈ Y.Gi 1 := hV0G1 hg
    set e : G := g⁻¹ * d * g * d with he
    have heQ1 : e ∈ Y.Q 1 := by
      have h := mul_d_mem_Q_one_of_fixes_zero Y H hd hd3 hd0 hgL hgG1 hg0 hg2
      simpa [he] using h
    have hcommZ0 : ⁅g, δ⁆ ∈ Y.Z 0 :=
      hZ0Q0 (Subgroup.commutator_mem_commutator hg
        ((Subgroup.mem_inf.mp (DOf_le_AOf Y d hδD)).1))
    have hcommA : ⁅g, δ⁆ ∈ AOf Y := by
      have hZ0A : Y.Z 0 ≤ AOf Y := by
        calc Y.Z 0 ≤ Y.Z 1 := by
              rw [hZ1sup]
              exact le_sup_left
          _ ≤ AOf Y := Z_one_le_AOf Y H hZ hd hd3
      exact hZ0A hcommZ0
    have hcommZ1 : ⁅g, δ⁆ ∈ Y.Z 1 := by
      rw [hZ1sup]
      exact Subgroup.mem_sup_left hcommZ0
    exact commute_of_mem_DOf Y H hZ hd hd3 hδD hδCenter he heQ1 hcommA hcommZ1

private theorem VNbr2_le_centralizer_of_mem_DOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d δ : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3)
    (hd0 : d • Y.vert 0 = Y.vert 2) (hδD : δ ∈ DOf Y d)
    (hδCenter : δ ∈ centerOf (Y.Q 1)) :
    Y.VNbr2 ≤ Subgroup.centralizer ({δ} : Set G) := by
  obtain ⟨-, -, -, -, hZ1sup, -, -, -⟩ := Y.s52_step8 H hZ
  intro g hg
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hgV2p : IsPGroup 2 (Subgroup.zpowers g) :=
    ((pCoreOf_isPGroup' ((Y.shift 2).Gi 0)).to_le
      (VNbr2_le_Q_two Y H hZ)).to_le (Subgroup.zpowers_le.mpr hg)
  have hgG1 : g ∈ Y.Gi 1 := VNbr2_le_Gi_one Y H hZ hg
  have hZ2V2 : ⁅(Y.Q 2 : Subgroup G), (Y.VNbr2 : Subgroup G)⁆ ≤ Y.Z 2 := by
    simpa using (VNbr0_props (Y.shift 2) (H.shift_two 1)
      (Y.Zt_eq_bot_of_even hZ even_two)).2.2.1
  by_cases hg0 : g • Y.vert 0 = Y.vert 0
  · have hg2 : g • Y.vert 2 = Y.vert 2 :=
      MulAction.mem_stabilizer_iff.mp (((VNbr2_le_Q_two Y H hZ).trans (Y.Q_le_Gi 2)) hg)
    have hgP0 : ∀ y ∈ Subgroup.zpowers g, y • Y.vert 0 = Y.vert 0 := fun y hy =>
      MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr
        (MulAction.mem_stabilizer_iff.mpr hg0) hy)
    have hgP2 : ∀ y ∈ Subgroup.zpowers g, y • Y.vert 2 = Y.vert 2 := fun y hy =>
      MulAction.mem_stabilizer_iff.mp (Subgroup.zpowers_le.mpr
        (MulAction.mem_stabilizer_iff.mpr hg2) hy)
    have hgQ1 : g ∈ Y.Q 1 :=
      le_Q_one_of_fixes_zero_two Y hgV2p (Subgroup.zpowers_le.mpr hgG1) hgP0 hgP2
        (Subgroup.mem_zpowers g)
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hδCenter).2 g hgQ1
  · have hg2 : g • Y.vert 2 = Y.vert 2 :=
      MulAction.mem_stabilizer_iff.mp (((VNbr2_le_Q_two Y H hZ).trans (Y.Q_le_Gi 2)) hg)
    have hgL : g ∈ Y.L 1 := VNbr2_le_L_one Y H hZ hg
    set e : G := g⁻¹ * d * g * d with he
    have heQ1 : e ∈ Y.Q 1 := by
      have h := mul_d_mem_Q_one_of_fixes_two Y H hd hd3 hd0 hgL hgG1 hg2 hg0
      simpa [he] using h
    have hcommZ2 : ⁅g, δ⁆ ∈ Y.Z 2 := by
      have hmem : ⁅δ, g⁆ ∈ Y.Z 2 :=
        hZ2V2 (Subgroup.commutator_mem_commutator
          ((Subgroup.mem_inf.mp (DOf_le_AOf Y d hδD)).2) hg)
      have hswap : ⁅g, δ⁆ = ⁅δ, g⁆⁻¹ := by
        simp only [commutatorElement_def]; group
      rw [hswap]
      exact (Y.Z 2).inv_mem hmem
    have hcommA : ⁅g, δ⁆ ∈ AOf Y :=
      (Z_one_le_AOf Y H hZ hd hd3) (by
        rw [hZ1sup]
        exact Subgroup.mem_sup_right hcommZ2)
    have hcommZ1 : ⁅g, δ⁆ ∈ Y.Z 1 := by
      rw [hZ1sup]
      exact Subgroup.mem_sup_right hcommZ2
    exact commute_of_mem_DOf Y H hZ hd hd3 hδD hδCenter he heQ1 hcommA hcommZ1

private theorem center_Q_one_inf_AOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3)
    (hd0 : d • Y.vert 0 = Y.vert 2) :
    centerOf (Y.Q 1) ⊓ AOf Y = Y.Z 1 := by
  have hZ1Q1 : Y.Z 1 ≤ centerOf (Y.Q 1) := Y.Z_le_center 1
  refine le_antisymm ?_ (le_inf hZ1Q1 (Z_one_le_AOf Y H hZ hd hd3))
  intro y hy
  obtain ⟨hyCenter, hyA⟩ := Subgroup.mem_inf.mp hy
  obtain ⟨δ, hδD, z, hzZ1, hyz⟩ := exists_DOf_mul_Z_one Y H hZ hd hd3 hyA
  have hδA : δ ∈ AOf Y := DOf_le_AOf Y d hδD
  have hδL : δ ∈ Y.L 1 :=
    ((Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).oTwo_le) (AOf_le_Q_one Y hδA)
  have hzCenter : z ∈ centerOf (Y.Q 1) := hZ1Q1 hzZ1
  have hδCenter : δ ∈ centerOf (Y.Q 1) := by
    rw [hyz] at hyCenter
    have hmem : (δ * z) * z⁻¹ ∈ centerOf (Y.Q 1) :=
      (centerOf (Y.Q 1)).mul_mem hyCenter ((centerOf (Y.Q 1)).inv_mem hzCenter)
    simpa [mul_assoc] using hmem
  have hV0C : Y.VNbr0 ≤ Subgroup.centralizer ({δ} : Set G) :=
    VNbr0_le_centralizer_of_mem_DOf Y H hZ hd hd3 hd0 hδD hδCenter
  have hV2C : Y.VNbr2 ≤ Subgroup.centralizer ({δ} : Set G) :=
    VNbr2_le_centralizer_of_mem_DOf Y H hZ hd hd3 hd0 hδD hδCenter
  have hQ1C : Y.Q 1 ≤ Subgroup.centralizer ({δ} : Set G) := by
    intro q hq
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hδCenter).2 q hq
  have hL1C : Y.L 1 ≤ Subgroup.centralizer ({δ} : Set G) :=
    (s52_A_normal Y H hZ).2.trans (sup_le (sup_le hV0C hV2C) hQ1C)
  have hδcenterL : δ ∈ centerOf (Y.L 1) := by
    rw [centerOf]
    exact Subgroup.mem_inf.mpr ⟨hδL, by
      rw [Subgroup.mem_centralizer_iff]
      intro l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp (hL1C hl)⟩
  have hbotL : δ ∈ (⊥ : Subgroup G) := by
    have h := (Y.s52_step8 H hZ).2.2.1
    rw [h] at hδcenterL
    exact hδcenterL
  have hδ1 : δ = 1 := Subgroup.mem_bot.mp hbotL
  rw [hyz, hδ1, one_mul]
  exact hzZ1

private theorem commutator_Q_one_AOf_le_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    ⁅Y.Q 1, AOf Y⁆ ≤ Y.Z 1 := by
  obtain ⟨-, -, -, -, hZ1sup, -, -, -⟩ := Y.s52_step8 H hZ
  set V0' : Subgroup G := (Y.mirror1).VNbr0 with hV0'def
  have hZ' : (Y.mirror1).Zt 0 = ⊥ := by
    simpa [Setup.Zt, Setup.mirror1] using Y.Zt_eq_bot_of_even hZ even_two
  have hHle : Y.Q 0 ⊓ Y.Q 1 ≤ Y.VNbr0 ⊔ AOf Y :=
    Q_zero_inf_Q_one_le_VNbr0_sup_A Y H hZ
  have hKle : Y.Q 2 ⊓ Y.Q 1 ≤ V0' ⊔ AOf Y := by
    have h := Q_zero_inf_Q_one_le_VNbr0_sup_A (Y := Y.mirror1) (H := H.mirror1) hZ'
    simpa [V0', AOf, inf_comm, sup_comm] using h
  let S : Set G := (Y.VNbr0 : Set G) ∪ (V0' : Set G) ∪ (AOf Y : Set G)
  have hV0cl : Y.VNbr0 ≤ Subgroup.closure S := by
    rw [← Subgroup.closure_eq (Y.VNbr0)]
    exact Subgroup.closure_mono (by intro x hx; exact Or.inl (Or.inl hx))
  have hV0'cl : V0' ≤ Subgroup.closure S := by
    rw [← Subgroup.closure_eq V0']
    exact Subgroup.closure_mono (by intro x hx; exact Or.inl (Or.inr hx))
  have hAcl : AOf Y ≤ Subgroup.closure S := by
    rw [← Subgroup.closure_eq (AOf Y)]
    exact Subgroup.closure_mono (by intro x hx; exact Or.inr hx)
  have hHcl : Y.Q 0 ⊓ Y.Q 1 ≤ Subgroup.closure S :=
    hHle.trans (sup_le hV0cl hAcl)
  have hKcl : Y.Q 2 ⊓ Y.Q 1 ≤ Subgroup.closure S :=
    hKle.trans (sup_le hV0'cl hAcl)
  have hQ1cl : Y.Q 1 ≤ Subgroup.closure S := by
    rw [Q_one_eq_sup Y H]
    exact sup_le hHcl hKcl
  have hL1Z : Y.L 1 ≤ Subgroup.normalizer (Y.Z 1 : Set G) := by
    intro l hl
    exact mem_normalizer_iff_conjSub.mpr (Y.Z_normal 1 l (Y.L_le_Gi 1 hl))
  have hSN : Subgroup.closure S ≤ Subgroup.normalizer (Y.Z 1 : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    rcases hx with (hxV0 | hxV0') | hxA
    · exact hL1Z (VNbr0_le_L_one Y H hZ hxV0)
    · exact hL1Z (by
        have h := VNbr0_le_L_one (Y.mirror1) H.mirror1 hZ' hxV0'
        simpa using h)
    · exact hL1Z ((Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).oTwo_le (AOf_le_Q_one Y hxA))
  have hZ0Z1 : Y.Z 0 ≤ Y.Z 1 := by
    rw [hZ1sup]
    exact le_sup_left
  have hZ2Z1 : Y.Z 2 ≤ Y.Z 1 := by
    rw [hZ1sup]
    exact le_sup_right
  have hZ0V0 : ⁅(Y.VNbr0 : Subgroup G), (Y.Q 0 : Subgroup G)⁆ ≤ Y.Z 0 := by
    rw [Subgroup.commutator_comm]
    exact (VNbr0_props Y H hZ).2.2.1
  have hZ2V0' : ⁅(Y.Q 2 : Subgroup G), V0'⁆ ≤ Y.Z 2 := by
    have h := (VNbr0_props (Y.mirror1) H.mirror1 hZ').2.2.1
    simpa [V0'] using h
  have hcomm : ∀ s ∈ S, ∀ a ∈ (AOf Y : Subgroup G), ⁅s, a⁆ ∈ Y.Z 1 := by
    intro s hs a ha
    rcases hs with (hsV0 | hsV0') | hsA
    · exact hZ0Z1 (hZ0V0 (Subgroup.commutator_mem_commutator hsV0
        (Subgroup.mem_inf.mp ha).1))
    · have hmem : ⁅s, a⁆ ∈ ⁅V0', (Y.Q 2 : Subgroup G)⁆ :=
        Subgroup.commutator_mem_commutator hsV0' (Subgroup.mem_inf.mp ha).2
      rw [Subgroup.commutator_comm] at hmem
      exact hZ2Z1 (hZ2V0' hmem)
    · have hc : s * a = a * s := (isElemAbelian_AOf Y H hZ hd hd3).comm hsA ha
      rw [commutatorElement_eq_one_iff_mul_comm.mpr hc]
      exact (Y.Z 1).one_mem
  have hmain := CFSG.Quasithin.D14.commutator_closure_le (S := S)
    (K := (AOf Y : Subgroup G)) (N := Y.Z 1) hSN hcomm
  exact (Subgroup.commutator_mono hQ1cl le_rfl).trans hmain

private theorem exists_VNbr0_mul_DOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) {q : G} (hq : q ∈ Y.Q 0) :
    ∃ v ∈ Y.VNbr0, ∃ δ ∈ DOf Y d, q = v * δ := by
  have hDleN : DOf Y d ≤ Subgroup.normalizer (Y.VNbr0 : Set G) :=
    (DOf_le_AOf Y d).trans (inf_le_left.trans
      ((Y.Q_le_Gi 0).trans (VNbr0_props Y H hZ).2.1))
  have hq' : q ∈ Y.VNbr0 ⊔ DOf Y d := by
    rw [sup_comm, ← Q_zero_eq_DOf_sup_VNbr0 Y H hZ hd hd3]
    exact hq
  obtain ⟨v, hv, δ, hδ, hvδ⟩ :=
    (CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes
      (H := Y.VNbr0) (K := DOf Y d) hDleN).mp hq'
  exact ⟨v, hv, δ, hδ, hvδ⟩

private theorem dsFrattini_Q_zero_eq_Z_zero_of_orderOf_eq_three (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    dsFrattini (Y.Q 0) = Y.Z 0 := by
  haveI : Finite ↥(Y.Q 0) := finite_of_le_stabilizer Y.hyp (H := Y.Q 0) (Y.Q_le_Gi 0)
  have hcomm := commutator_Q_zero_eq_Z_zero_of_orderOf_eq_three Y H hZ hd hd3
  have hZ0V0 : ⁅(Y.Q 0 : Subgroup G), (Y.VNbr0 : Subgroup G)⁆ ≤ Y.Z 0 :=
    (VNbr0_props Y H hZ).2.2.1
  let U : Subgroup G :=
    { carrier := {v | v ∈ Y.VNbr0 ∧ v ^ 2 ∈ Y.Z 0}
      one_mem' := ⟨(Y.VNbr0).one_mem, by simp⟩
      mul_mem' := by
        intro a b ha hb
        refine ⟨(Y.VNbr0).mul_mem ha.1 hb.1, ?_⟩
        have hc : ⁅a⁻¹, b⁆ ∈ Y.Z 0 := by
          rw [← (VNbr0_props Y H hZ).2.2.2]
          exact Subgroup.commutator_mem_commutator ((Y.VNbr0).inv_mem ha.1) hb.1
        have hform : (a * b) ^ 2 = a ^ 2 * ⁅a⁻¹, b⁆ * b ^ 2 := by
          rw [pow_two]
          simp only [commutatorElement_def]
          group
        rw [hform]
        exact (Y.Z 0).mul_mem ((Y.Z 0).mul_mem ha.2 hc) hb.2
      inv_mem' := by
        intro a ha
        refine ⟨(Y.VNbr0).inv_mem ha.1, ?_⟩
        rw [inv_pow]
        exact (Y.Z 0).inv_mem ha.2 }
  have hVU : Y.VNbr0 ≤ U := by
    rw [VNbr0_eq_iSup Y]
    refine iSup_le fun u => ?_
    intro v hv
    refine ⟨?_, ?_⟩
    · rw [VNbr0_eq_iSup Y]
      exact le_iSup (fun u : Γ.neighborSet (Y.vert 0) => vertZ (G := G) (u : V)) u hv
    have hv2 : v ^ 2 = 1 := (isElemAbelian_vertZ_nbr Y H hZ u).2 v hv
    rw [hv2]
    exact (Y.Z 0).one_mem
  have hsqV : ∀ v ∈ Y.VNbr0, v ^ 2 ∈ Y.Z 0 := fun v hv => (hVU hv).2
  have hsqQ : ∀ q ∈ Y.Q 0, q ^ 2 ∈ Y.Z 0 := by
    intro q hq
    obtain ⟨v, hv, δ, hδ, rfl⟩ := exists_VNbr0_mul_DOf Y H hZ hd hd3 hq
    have hδA : δ ∈ AOf Y := DOf_le_AOf Y d hδ
    have hδ2 : δ ^ 2 = 1 := (isElemAbelian_AOf Y H hZ hd hd3).2 δ hδA
    have hδQ0 : δ ∈ Y.Q 0 := (Subgroup.mem_inf.mp hδA).1
    have hcommδv : ⁅δ, v⁆ ∈ Y.Z 0 :=
      hZ0V0 (Subgroup.commutator_mem_commutator hδQ0 hv)
    have hcent : ⁅δ, v⁆ * v = v * ⁅δ, v⁆ :=
      (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (Y.Z_le_center 0 hcommδv)).2 v ((VNbr0_props Y H hZ).1 hv)).symm
    have hconj : δ * v * δ⁻¹ = ⁅δ, v⁆ * v := by
      simp only [commutatorElement_def]
      group
    have hstep : (v * δ) ^ 2 = v * (δ * v * δ⁻¹) * δ ^ 2 := by
      rw [pow_two]
      group
    have hform : (v * δ) ^ 2 = v ^ 2 * ⁅δ, v⁆ := by
      calc (v * δ) ^ 2 = v * (δ * v * δ⁻¹) * δ ^ 2 := hstep
        _ = v * (⁅δ, v⁆ * v) * δ ^ 2 := by rw [hconj]
        _ = v * (⁅δ, v⁆ * v) := by rw [hδ2, mul_one]
        _ = v * (v * ⁅δ, v⁆) := by rw [hcent]
        _ = v ^ 2 * ⁅δ, v⁆ := by rw [pow_two]; group
    rw [hform]
    exact (Y.Z 0).mul_mem (hsqV v hv) hcommδv
  have hle : dsFrattini (Y.Q 0) ≤ Y.Z 0 :=
    CFSG.GroupTheory.frattini_map_subtype_le_of_commutator_le_of_pow_mem (p := 2)
      (pCoreOf_isPGroup' (Y.Gi 0)) hcomm.le hsqQ
  have hge : Y.Z 0 ≤ dsFrattini (Y.Q 0) := by
    haveI : Fact (IsPGroup 2 ↥(Y.Q 0)) := ⟨pCoreOf_isPGroup' (Y.Gi 0)⟩
    have hfr := Subgroup.map_mono (f := (Y.Q 0).subtype)
      (CFSG.commutator_le_frattini_of_isPGroup (p := 2) (R := ↥(Y.Q 0)))
    rw [Subgroup.map_subtype_commutator, hcomm] at hfr
    simpa [dsFrattini] using hfr
  exact le_antisymm hle hge


private theorem d_smul_zero_ne_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) : d • Y.vert 0 ≠ Y.vert 0 := by
  intro hd0
  obtain ⟨c, hcadj, hc0, hc2⟩ := Y.exists_third_nbr
  have hdG1 : d ∈ Y.Gi 1 := Y.L_le_Gi 1 hd
  have hd1 : d • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp hdG1
  have hd3pow : d ^ 3 = 1 := d_pow_three hd3
  have h3d : d * d ^ 2 = d ^ 3 := (pow_succ' d 2).symm
  have hd2 : d • Y.vert 2 = Y.vert 2 := by
    by_contra hne
    have hdadj : Γ.Adj (Y.vert 1) (d • Y.vert 2) := by
      have h := (Y.hyp.adj_smul d (Y.vert 1) (Y.vert 2)).mpr (by simpa using Y.adj 1)
      rwa [hd1] at h
    have hne0 : d • Y.vert 2 ≠ Y.vert 0 := by
      intro h
      have h' : d • Y.vert 2 = d • Y.vert 0 := h.trans hd0.symm
      exact (vert_zero_ne_vert_two Y).symm (MulAction.injective d h')
    have hdc2 : d • Y.vert 2 = c :=
      eq_of_adj_one_of_ne Y H hdadj hcadj hne0 hne hc0 hc2
    have hdc : d • c = Y.vert 2 :=
      (smul_third_of_smul_two Y H hdG1 hcadj hc0 hc2 hd0).2 hdc2
    have h2 : d ^ 2 • Y.vert 2 = Y.vert 2 := by
      rw [pow_two, mul_smul, hdc2, hdc]
    have hcontra : Y.vert 2 = c := by
      calc Y.vert 2 = d ^ 3 • Y.vert 2 := by rw [hd3pow, one_smul]
        _ = d • (d ^ 2 • Y.vert 2) := by rw [← h3d, mul_smul]
        _ = d • Y.vert 2 := by rw [h2]
        _ = c := hdc2
    exact hc2 hcontra.symm
  have hdc : d • c = c :=
    (smul_third_of_smul_two Y H hdG1 hcadj hc0 hc2 hd0).1 hd2
  have hfix : ∀ v : V, Γ.Adj (Y.vert 1) v → d • v = v := by
    intro v hv
    by_cases hv0 : v = Y.vert 0
    · rw [hv0]; exact hd0
    by_cases hv2 : v = Y.vert 2
    · rw [hv2]; exact hd2
    have hvc : v = c := eq_of_adj_one_of_ne Y H hv hcadj hv0 hv2 hc0 hc2
    rw [hvc]; exact hdc
  exact (CFSG.Quasithin.F6.GoldAmN.not_mem_of_isPGroup_two
    (pCoreOf_isPGroup' (Y.Gi 1)) hd3)
    ((Y.hyp.isLocL2_oTwoPrime (Y.vert 1)).N_fixes_neighbors_mem_Q Y.hyp.adj_smul
      (Y.hyp.finite_stab (Y.vert 1)) (Y.hyp.valency (Y.vert 1)).2
      (Y.hyp.valency (Y.vert 1)).1 (x := ⟨d, hd⟩) hfix)

private theorem d_sq_smul_zero_eq_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) (hd0 : d • Y.vert 0 ≠ Y.vert 0)
    (hd02 : d • Y.vert 0 ≠ Y.vert 2) : d⁻¹ • Y.vert 0 = Y.vert 2 := by
  obtain ⟨c, hcadj, hc0, hc2⟩ := Y.exists_third_nbr
  have hdG1 : d ∈ Y.Gi 1 := Y.L_le_Gi 1 hd
  have hd1 : d • Y.vert 1 = Y.vert 1 := MulAction.mem_stabilizer_iff.mp hdG1
  have hd3pow : d ^ 3 = 1 := d_pow_three hd3
  have h3d : d * d ^ 2 = d ^ 3 := (pow_succ' d 2).symm
  have hd2inv : d ^ 2 = d⁻¹ :=
    eq_inv_of_mul_eq_one_right (by rw [← pow_succ']; exact hd3pow)
  have hdadj : Γ.Adj (Y.vert 1) (d • Y.vert 0) := by
    have h := (Y.hyp.adj_smul d (Y.vert 1) (Y.vert 0)).mpr (by simpa using (Y.adj 0).symm)
    rwa [hd1] at h
  have hd0c : d • Y.vert 0 = c :=
    eq_of_adj_one_of_ne Y H hdadj hcadj hd0 hd02 hc0 hc2
  have hd2adj : Γ.Adj (Y.vert 1) (d ^ 2 • Y.vert 0) := by
    have h := (Y.hyp.adj_smul (d ^ 2) (Y.vert 1) (Y.vert 0)).mpr
      (by simpa using (Y.adj 0).symm)
    have hd2G1 : d ^ 2 ∈ Y.Gi 1 := (Y.Gi 1).pow_mem hdG1 2
    rwa [MulAction.mem_stabilizer_iff.mp hd2G1] at h
  have hd2ne0 : d ^ 2 • Y.vert 0 ≠ Y.vert 0 := by
    intro h
    have h' : d • (d ^ 2 • Y.vert 0) = d • Y.vert 0 := by rw [h]
    have hL : d • (d ^ 2 • Y.vert 0) = Y.vert 0 := by
      rw [← mul_smul, h3d, hd3pow, one_smul]
    rw [hL] at h'
    exact hd0 h'.symm
  have hd2nec : d ^ 2 • Y.vert 0 ≠ c := by
    intro hcEq
    have hEq : d ^ 2 • Y.vert 0 = d • Y.vert 0 := hcEq.trans hd0c.symm
    have hL : d • (d ^ 2 • Y.vert 0) = Y.vert 0 := by
      rw [← mul_smul, h3d, hd3pow, one_smul]
    have hR : d • (d • Y.vert 0) = d ^ 2 • Y.vert 0 := by
      rw [← mul_smul, pow_two]
    have h' := congrArg (fun v => d • v) hEq
    rw [hL, hR] at h'
    exact hc0 (h'.trans hcEq).symm
  have hd2eq : d ^ 2 • Y.vert 0 = Y.vert 2 := by
    by_contra hne
    exact hd2nec (eq_of_adj_one_of_ne Y H hd2adj hcadj hd2ne0 hne hc0 hc2)
  simpa [hd2inv] using hd2eq

private theorem d_smul_zero_eq_two_or_inv (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    d • Y.vert 0 = Y.vert 2 ∨ d⁻¹ • Y.vert 0 = Y.vert 2 := by
  by_cases hd0 : d • Y.vert 0 = Y.vert 0
  · exact absurd hd0 (d_smul_zero_ne_zero Y H hd hd3)
  · by_cases hd02 : d • Y.vert 0 = Y.vert 2
    · exact Or.inl hd02
    · exact Or.inr (d_sq_smul_zero_eq_two Y H hd hd3 hd0 hd02)

private theorem s52_step10_core (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    {d : G} (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3)
    (hd0 : d • Y.vert 0 = Y.vert 2) :
    (∀ x ∈ Y.Q 1, x ∈ Subgroup.centralizer ({d} : Set G) → x ∈ Y.Q 0 ⊓ Y.Q 2) ∧
      IsElemAbelian 2 (Y.Q 0 ⊓ Y.Q 2) ∧
        ⁅Y.Q 1, (Y.Q 0 ⊓ Y.Q 2)⁆ ≤ Y.Z 1 ∧
          centerOf (Y.Q 1) ⊓ (Y.Q 0 ⊓ Y.Q 2) = Y.Z 1 ∧
            Y.Q 0 = (Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ Y.VNbr0 ∧
              ⁅Y.Q 0, Y.Q 0⁆ = Y.Z 0 ∧ dsFrattini (Y.Q 0) = Y.Z 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro x hx hxc
    simpa [AOf] using C_Q_one_d_le_A Y H hZ hd hd3 hd0 x hx hxc
  · simpa [AOf] using isElemAbelian_AOf Y H hZ hd hd3
  · simpa [AOf] using commutator_Q_one_AOf_le_Z_one Y H hZ hd hd3
  · simpa [AOf] using center_Q_one_inf_AOf Y H hZ hd hd3 hd0
  · simpa [DOf, AOf] using Q_zero_eq_DOf_sup_VNbr0 Y H hZ hd hd3
  · exact commutator_Q_zero_eq_Z_zero_of_orderOf_eq_three Y H hZ hd hd3
  · exact dsFrattini_Q_zero_eq_Z_zero_of_orderOf_eq_three Y H hZ hd hd3

theorem s52_step10 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥) {d : G}
    (hd : d ∈ Y.L 1) (hd3 : orderOf d = 3) :
    (∀ x ∈ Y.Q 1, x ∈ Subgroup.centralizer ({d} : Set G) → x ∈ Y.Q 0 ⊓ Y.Q 2) ∧
      IsElemAbelian 2 (Y.Q 0 ⊓ Y.Q 2) ∧
        ⁅Y.Q 1, (Y.Q 0 ⊓ Y.Q 2)⁆ ≤ Y.Z 1 ∧
          centerOf (Y.Q 1) ⊓ (Y.Q 0 ⊓ Y.Q 2) = Y.Z 1 ∧
            Y.Q 0 = (Y.Q 0 ⊓ Y.Q 2 ⊓ Subgroup.centralizer ({d} : Set G)) ⊔ Y.VNbr0 ∧
              ⁅Y.Q 0, Y.Q 0⁆ = Y.Z 0 ∧ dsFrattini (Y.Q 0) = Y.Z 0 := by
  rcases d_smul_zero_eq_two_or_inv Y H hd hd3 with h | h
  · exact s52_step10_core Y H hZ hd hd3 h
  · have hcore := s52_step10_core Y H hZ ((Y.L 1).inv_mem hd)
      (by rw [orderOf_inv, hd3]) h
    have hinv : Subgroup.centralizer ({d⁻¹} : Set G) = Subgroup.centralizer {d} := by
      ext x
      simp only [Subgroup.mem_centralizer_singleton_iff]
      exact Commute.inv_right_iff
    simpa [DOf, AOf, hinv] using hcore

theorem isElemAbelian_Q_zero_inf_Q_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : IsElemAbelian 2 (Y.Q 0 ⊓ Y.Q 2) := by
  obtain ⟨d, hdJ, hd3⟩ := Y.exists_J_three H
  exact (Y.s52_step10 H hZ (Y.J_le_L 1 hdJ) hd3).2.1

theorem commutator_Q_one_inf_le_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : ⁅Y.Q 1, Y.Q 0 ⊓ Y.Q 2⁆ ≤ Y.Z 1 := by
  obtain ⟨d, hdJ, hd3⟩ := Y.exists_J_three H
  exact (Y.s52_step10 H hZ (Y.J_le_L 1 hdJ) hd3).2.2.1

theorem centerOf_Q_one_inf_eq_Z_one (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : centerOf (Y.Q 1) ⊓ (Y.Q 0 ⊓ Y.Q 2) = Y.Z 1 := by
  obtain ⟨d, hdJ, hd3⟩ := Y.exists_J_three H
  exact (Y.s52_step10 H hZ (Y.J_le_L 1 hdJ) hd3).2.2.2.1

theorem commutator_Q_zero_eq_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : ⁅Y.Q 0, Y.Q 0⁆ = Y.Z 0 := by
  obtain ⟨d, hdJ, hd3⟩ := Y.exists_J_three H
  exact (Y.s52_step10 H hZ (Y.J_le_L 1 hdJ) hd3).2.2.2.2.2.1

theorem dsFrattini_Q_zero_eq_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : dsFrattini (Y.Q 0) = Y.Z 0 := by
  obtain ⟨d, hdJ, hd3⟩ := Y.exists_J_three H
  exact (Y.s52_step10 H hZ (Y.J_le_L 1 hdJ) hd3).2.2.2.2.2.2

theorem isElemSec_Z_zero_Q_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : IsElemSec (Y.Z 0) (Y.Q 0) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI hfinQ : Finite ↥(Y.Q 0) :=
    finite_of_le_stabilizer Y.hyp (H := Y.Q 0) (Y.Q_le_Gi 0)
  haveI hQ2 : Fact (IsPGroup 2 ↥(Y.Q 0)) := ⟨pCoreOf_isPGroup' (Y.Gi 0)⟩
  obtain ⟨d, hdJ, hd3⟩ := Y.exists_J_three H
  obtain ⟨-, -, -, -, -, hcomm, hfratt⟩ :=
    Y.s52_step10 H hZ (Y.J_le_L 1 hdJ) hd3
  refine ⟨Y.Z_le_Q 0, ?_, ?_⟩
  · rw [hcomm]
  · intro e he
    have hmem : e ^ 2 ∈ dsFrattini (Y.Q 0) := by
      have h := pth_power_mem_frattini_of_isPGroup (p := 2) (R := ↥(Y.Q 0)) ⟨e, he⟩
      simpa [dsFrattini] using (Subgroup.mem_map_of_mem (Y.Q 0).subtype h)
    rwa [hfratt] at hmem

private noncomputable def UOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (T : Finset (Γ.neighborSet (Y.vert 0))) : Subgroup G :=
  Y.Z 0 ⊔ ⨆ u ∈ T, Subgroup.zpowers (xOf Y H hZ u)

private theorem UOf_le_VNbr0 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (T : Finset (Γ.neighborSet (Y.vert 0))) : UOf Y H hZ T ≤ Y.VNbr0 := by
  obtain ⟨-, -, -, -, hZ1sup, -, -, -⟩ := Y.s52_step8 H hZ
  refine sup_le ?_ ?_
  · intro z hz
    have hz1 : z ∈ Y.Z 1 := by
      rw [hZ1sup]
      exact (le_sup_left : (Y.Z 0 : Subgroup G) ≤ Y.Z 0 ⊔ Y.Z 2) hz
    exact Z_one_le_VNbr0 Y H hZ hz1
  · refine iSup_le fun u => iSup_le fun _ => ?_
    exact Subgroup.zpowers_le.mpr (xOf_mem Y H hZ u)

private theorem relIndex_UOf (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (T : Finset (Γ.neighborSet (Y.vert 0))) :
    (Y.Z 0).relIndex (UOf Y H hZ T) ≤ 2 ^ T.card := by
  classical
  induction T using Finset.induction_on with
  | empty =>
      simp [UOf]
  | insert a T ha ih =>
      have hUleV : UOf Y H hZ T ≤ Y.VNbr0 := UOf_le_VNbr0 Y H hZ T
      have hxV : xOf Y H hZ a ∈ Y.VNbr0 := xOf_mem Y H hZ a
      have hx2 : xOf Y H hZ a * xOf Y H hZ a = 1 := by
        have h := (isElemAbelian_vertZ_nbr Y H hZ a).2 (xOf Y H hZ a) (xOf_spec Y H hZ a).1
        simpa [pow_two] using h
      have hnorm : ∀ p ∈ UOf Y H hZ T, xOf Y H hZ a * p * (xOf Y H hZ a)⁻¹ ∈
          UOf Y H hZ T := by
        intro p hp
        have hpV : p ∈ Y.VNbr0 := hUleV hp
        have hc : ⁅xOf Y H hZ a, p⁆ ∈ Y.Z 0 :=
          commutator_mem_Z Y H hZ hxV hpV
        have heq : xOf Y H hZ a * p * (xOf Y H hZ a)⁻¹ =
            ⁅xOf Y H hZ a, p⁆ * p := by
          simp only [commutatorElement_def]
          group
        rw [heq]
        exact (UOf Y H hZ T).mul_mem ((le_sup_left : Y.Z 0 ≤ UOf Y H hZ T) hc) hp
      have hstep : (UOf Y H hZ T).relIndex
          (UOf Y H hZ T ⊔ Subgroup.zpowers (xOf Y H hZ a)) ≤ 2 :=
        CFSG.GroupTheory.relIndex_sup_zpowers_le_two hx2 hnorm
      have hUeq : UOf Y H hZ (insert a T) =
          UOf Y H hZ T ⊔ Subgroup.zpowers (xOf Y H hZ a) := by
        rw [UOf, UOf, Finset.iSup_insert]
        ac_rfl
      have hZle : Y.Z 0 ≤ UOf Y H hZ T := le_sup_left
      have hUle : UOf Y H hZ T ≤ UOf Y H hZ (insert a T) := by rw [hUeq]; exact le_sup_left
      have hmul := Subgroup.relIndex_mul_relIndex (H := Y.Z 0) (K := UOf Y H hZ T)
        (L := UOf Y H hZ (insert a T)) hZle hUle
      rw [hUeq] at hmul ⊢
      rw [Finset.card_insert_of_notMem ha]
      calc (Y.Z 0).relIndex (UOf Y H hZ T ⊔ Subgroup.zpowers (xOf Y H hZ a))
          = (Y.Z 0).relIndex (UOf Y H hZ T) *
              (UOf Y H hZ T).relIndex
                (UOf Y H hZ T ⊔ Subgroup.zpowers (xOf Y H hZ a)) := hmul.symm
        _ ≤ 2 ^ T.card * 2 := Nat.mul_le_mul ih hstep
        _ = 2 ^ (T.card + 1) := by rw [pow_succ]

private theorem UOf_univ_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    [Fintype (Γ.neighborSet (Y.vert 0))] :
    UOf Y H hZ Finset.univ = Y.VNbr0 := by
  classical
  obtain ⟨-, -, -, -, -, -, hZcard, -⟩ := Y.s52_step8 H hZ
  haveI : Nonempty (Γ.neighborSet (Y.vert 0)) :=
    ⟨⟨Y.vert 1, by simpa using Y.adj 0⟩⟩
  rw [UOf, VNbr0_eq_iSup Y]
  calc Y.Z 0 ⊔ ⨆ u ∈ (Finset.univ : Finset (Γ.neighborSet (Y.vert 0))),
        Subgroup.zpowers (xOf Y H hZ u)
      = Y.Z 0 ⊔ ⨆ u, Subgroup.zpowers (xOf Y H hZ u) := by simp
    _ = ⨆ u, (Y.Z 0 ⊔ Subgroup.zpowers (xOf Y H hZ u)) := by
          rw [iSup_sup_eq, iSup_const]
    _ = ⨆ u : Γ.neighborSet (Y.vert 0), vertZ (G := G) (u : V) := by
          apply iSup_congr
          intro u
          have hu := card_vertZ_nbr Y H hZ u
          haveI : Finite ↥(vertZ (G := G) (u : V)) :=
            Nat.finite_of_card_ne_zero (by rw [hu]; norm_num)
          exact CFSG.Quasithin.F6.GoldAmN.sup_zpowers_eq_of_relIndex_two
            (Z_zero_le_vertZ Y H hZ u)
            (CFSG.Monster.AxisCount.relIndex_eq_two_of_card_eq (Z_zero_le_vertZ Y H hZ u)
              (by omega))
            (xOf_spec Y H hZ u).1 (xOf_spec Y H hZ u).2

private theorem relIndex_Z_zero_VNbr0_le (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) :
    (Y.Z 0).relIndex Y.VNbr0 ≤ 2 ^ (2 ^ n₀ + 1) := by
  haveI : Finite (Γ.neighborSet (Y.vert 0)) :=
    (Y.hyp.finite_neighborSet (Y.vert 0)).to_subtype
  haveI : Fintype (Γ.neighborSet (Y.vert 0)) := Fintype.ofFinite _
  rw [← UOf_univ_eq Y H hZ]
  refine (relIndex_UOf Y H hZ Finset.univ).trans ?_
  congr 1
  rw [Finset.card_univ]
  have hcard : Fintype.card (Γ.neighborSet (Y.vert 0)) = 2 ^ n₀ + 1 := by
    rw [← Nat.card_eq_fintype_card, (Y.hyp.valency (Y.vert 0)).2]
    exact congrArg (fun k => 2 ^ k + 1) H.n_zero
  rw [hcard]

private theorem exists_Z_three_moving_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) :
    ∃ h ∈ Y.Z 3, h • Y.vert 0 ≠ Y.vert 0 ∧ h • Y.vert 1 = Y.vert 1 ∧
      h • Y.vert 2 = Y.vert 2 ∧ h * h = 1 := by
  have hb3 := (Y.s52_step9_cons H hZ).2 3 (by norm_num)
  have hZ3G1 : Y.Z 3 ≤ Y.Gi 1 := by
    have := hb3.1 (-2) (by norm_num)
    simpa using this
  have hZ3G2 : Y.Z 3 ≤ Y.Gi 2 := by
    have := hb3.1 (-1) (by norm_num)
    simpa using this
  have hZ3notG0 : ¬ Y.Z 3 ≤ Y.Gi 0 := by
    have := hb3.2.2
    simpa using this
  obtain ⟨h, hhZ, hhnotG0⟩ := Set.not_subset.mp hZ3notG0
  refine ⟨h, hhZ, ?_, ?_, ?_, ?_⟩
  · intro hfix0
    exact hhnotG0 (MulAction.mem_stabilizer_iff.mpr hfix0)
  · exact MulAction.mem_stabilizer_iff.mp (hZ3G1 hhZ)
  · exact MulAction.mem_stabilizer_iff.mp (hZ3G2 hhZ)
  · have := (s52_step8_Z Y H hZ 3 (by norm_num)).1.2 h hhZ
    simpa [pow_two] using this

private theorem smul_third_eq_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) {h y : G} {v : V}
    (hy1 : y • Y.vert 1 = Y.vert 1) (hy0 : y • Y.vert 0 = Y.vert 0)
    (hv1 : Γ.Adj (Y.vert 1) v) (hv0 : v ≠ Y.vert 0) (hyv : y • v ≠ v)
    (hp_adj : Γ.Adj (Y.vert 1) (h • Y.vert 0))
    (hp_ne0 : h • Y.vert 0 ≠ Y.vert 0) (hp_ne2 : h • Y.vert 0 ≠ Y.vert 2) :
    y • (h • Y.vert 0) = Y.vert 2 := by
  have hyv_adj : Γ.Adj (Y.vert 1) (y • v) := by
    have h := (Y.hyp.adj_smul y (Y.vert 1) v).mpr hv1
    rwa [hy1] at h
  have hyv_ne0 : y • v ≠ Y.vert 0 := by
    intro h0
    have h' : y • v = y • Y.vert 0 := h0.trans hy0.symm
    exact hv0 (MulAction.injective y h')
  have hvp : v = Y.vert 2 ∨ v = h • Y.vert 0 := by
    by_cases hv2 : v = Y.vert 2
    · exact Or.inl hv2
    · right
      exact eq_of_adj_one_of_ne Y H hv1 hp_adj hv0 hv2 hp_ne0 hp_ne2
  rcases hvp with hv2 | hvp
  · rw [hv2] at hyv
    by_cases hy2 : y • Y.vert 2 = Y.vert 2
    · exact absurd hy2 hyv
    · have hy2adj : Γ.Adj (Y.vert 1) (y • Y.vert 2) := by
        have h := (Y.hyp.adj_smul y (Y.vert 1) (Y.vert 2)).mpr (by simpa using Y.adj 1)
        rwa [hy1] at h
      have hy2ne0 : y • Y.vert 2 ≠ Y.vert 0 := by
        intro h0
        have h' : y • Y.vert 2 = y • Y.vert 0 := h0.trans hy0.symm
        exact (vert_zero_ne_vert_two Y).symm (MulAction.injective y h')
      have hy2p : y • Y.vert 2 = h • Y.vert 0 :=
        eq_of_adj_one_of_ne Y H hy2adj hp_adj hy2ne0 hy2 hp_ne0 hp_ne2
      have hyp_ne0 : y • (h • Y.vert 0) ≠ Y.vert 0 := by
        intro h0
        have h' : y • (h • Y.vert 0) = y • Y.vert 0 := h0.trans hy0.symm
        exact hp_ne0 (MulAction.injective y h')
      have hyp_adj : Γ.Adj (Y.vert 1) (y • (h • Y.vert 0)) := by
        have h := (Y.hyp.adj_smul y (Y.vert 1) (h • Y.vert 0)).mpr hp_adj
        rwa [hy1] at h
      by_cases hyp : y • (h • Y.vert 0) = h • Y.vert 0
      · exfalso
        exact hp_ne2 (MulAction.injective y (hyp.trans hy2p.symm))
      · by_contra hne2
        exact hyp (eq_of_adj_one_of_ne Y H hyp_adj hp_adj hyp_ne0 hne2 hp_ne0 hp_ne2)
  · rw [hvp] at hyv
    rw [hvp] at hyv_adj
    rw [hvp] at hyv_ne0
    by_contra hne2
    exact hyv (eq_of_adj_one_of_ne Y H hyv_adj hp_adj hyv_ne0 hne2 hp_ne0 hp_ne2)

private theorem Z_one_le_centralizer_conj (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {m g h y : G} (hmC : m ∈ centerOf Y.VNbr0)
    (hgG0 : g ∈ Y.Gi 0) (hy : y = g⁻¹ * m * g) (hhZ : h ∈ Y.Z 3)
    (hZ3G1 : Y.Z 3 ≤ Y.Gi 1) :
    Y.Z 1 ≤ Subgroup.centralizer ({h * y * h⁻¹} : Set G) := by
  intro z hz
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hnorm : conjSub h (Y.Z 1) = Y.Z 1 := Y.Z_normal 1 h (hZ3G1 hhZ)
  have hnorm' : conjSub h⁻¹ (Y.Z 1) = Y.Z 1 := by
    have h := congrArg (conjSub h⁻¹) hnorm
    simpa [conjSub_conjSub_inv] using h.symm
  have hzinv : h⁻¹ * z * h ∈ Y.Z 1 := by
    have h := mul_mem_conjSub (g := h⁻¹) (H := Y.Z 1) hz
    simpa [hnorm'] using h
  have hyc : y * (h⁻¹ * z * h) * y⁻¹ = h⁻¹ * z * h := by
    have hconjV : conjSub g⁻¹ (Y.VNbr0) = Y.VNbr0 := by
      have hmem : g⁻¹ ∈ Subgroup.normalizer (Y.VNbr0 : Set G) :=
        (Subgroup.normalizer _).inv_mem ((VNbr0_props Y H hZ).2.1 hgG0)
      exact mem_normalizer_iff_conjSub.mp hmem
    have hyC : y ∈ centerOf Y.VNbr0 := by
      have hc : conjSub g⁻¹ (centerOf Y.VNbr0) = centerOf Y.VNbr0 := by
        rw [← centerOf_conjSub, hconjV]
      have hmemy : y ∈ conjSub g⁻¹ (centerOf Y.VNbr0) := by
        simpa [hy] using mul_mem_conjSub (g := g⁻¹) hmC
      rwa [hc] at hmemy
    have hcent := (Subgroup.mem_inf.mp hyC).2
    have hcomm := Subgroup.mem_centralizer_iff.mp hcent (h⁻¹ * z * h)
      (Z_one_le_VNbr0 Y H hZ hzinv)
    rw [← hcomm]
    group
  have hn_eq : (h * y * h⁻¹) * z * (h * y * h⁻¹)⁻¹ =
      h * (y * (h⁻¹ * z * h) * y⁻¹) * h⁻¹ := by group
  have hmain : (h * y * h⁻¹) * z * (h * y * h⁻¹)⁻¹ = z := by
    rw [hn_eq, hyc]
    group
  calc z * (h * y * h⁻¹) = ((h * y * h⁻¹) * z * (h * y * h⁻¹)⁻¹) * (h * y * h⁻¹) := by
        rw [hmain]
    _ = (h * y * h⁻¹) * z := by group

private theorem zOf_mem_Z_two_of_conj (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) {n : G} (hn0 : n • Y.vert 0 = Y.vert 2)
    (hnZ1 : Y.Z 1 ≤ Subgroup.centralizer ({n} : Set G)) : False := by
  obtain ⟨-, -, -, -, hZ1sup, hZ0infZ2, -, -⟩ := Y.s52_step8 H hZ
  let z0 : ↥(Y.Z 0) := zOf Y H hZ
  have hz0Z1 : (z0 : G) ∈ Y.Z 1 := by
    rw [hZ1sup]
    exact (le_sup_left : (Y.Z 0 : Subgroup G) ≤ Y.Z 0 ⊔ Y.Z 2) z0.2
  have hz0cent : n * (z0 : G) * n⁻¹ = z0 := by
    have hcomm := Subgroup.mem_centralizer_singleton_iff.mp (hnZ1 hz0Z1)
    rw [← hcomm]
    group
  have hconjZ : conjSub n (Y.Z 0) = Y.Z 2 := by
    rw [Setup.Z_eq_vertZ, Setup.Z_eq_vertZ, ← vertZ_smul, hn0]
  have hz0Z2 : (z0 : G) ∈ Y.Z 2 := by
    have hz0cent' : n⁻¹ * (z0 : G) * n = (z0 : G) := by
      calc n⁻¹ * (z0 : G) * n = n⁻¹ * (n * (z0 : G) * n⁻¹) * n := by rw [hz0cent]
        _ = (z0 : G) := by group
    have hmem : (z0 : G) ∈ conjSub n (Y.Z 0) := by
      rw [mem_conjSub, hz0cent']
      exact z0.2
    rwa [hconjZ] at hmem
  have hbot : (z0 : G) ∈ (⊥ : Subgroup G) := by
    have hmem : (z0 : G) ∈ Y.Z 0 ⊓ Y.Z 2 := Subgroup.mem_inf.mpr ⟨z0.2, hz0Z2⟩
    rwa [hZ0infZ2] at hmem
  exact zOf_ne_one Y H hZ (Subtype.ext (Subgroup.mem_bot.mp hbot))

private theorem centerOf_VNbr0_subgroupOf_le_ker_phi (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) :
    ((centerOf Y.VNbr0).subgroupOf Y.VNbr0) ≤ (phi Y H hZ).ker := by
  classical
  intro m hm
  rw [MonoidHom.mem_ker]
  apply Multiplicative.toAdd.injective
  funext w
  have hmV : (m : G) ∈ Y.VNbr0 := m.2
  have hmC : (m : G) ∈ centerOf Y.VNbr0 := hm
  have hmV0 : (m : G) ∈ Y.VNbr0 := hmV
  have hfix : FixSet Y (m : G) w := by
    by_contra hnf
    obtain ⟨g, hgL, hgw⟩ := L_zero_trans Y (a := Y.vert 1) (b := w)
      (by simpa using Y.adj 0) w.2
    have hgG0 : g ∈ Y.Gi 0 := Y.L_le_Gi 0 hgL
    have hg0 : g • Y.vert 0 = Y.vert 0 := MulAction.mem_stabilizer_iff.mp hgG0
    let y : G := g⁻¹ * (m : G) * g
    have hm0 : (m : G) • Y.vert 0 = Y.vert 0 :=
      VNbr0_fixes_zero Y H hZ hmV0
    have hg0inv : g⁻¹ • Y.vert 0 = Y.vert 0 := by
      have h := congrArg (fun v => g⁻¹ • v) hg0
      simpa using h.symm
    have hy0 : y • Y.vert 0 = Y.vert 0 := by
      dsimp only [y]
      simp only [mul_smul]
      rw [hg0, hm0, hg0inv]
    have hy1_inv : g⁻¹ • (w : V) = Y.vert 1 := by
      have h := congrArg (fun v => g⁻¹ • v) hgw
      simpa using h.symm
    have hmw : (m : G) • (w : V) = (w : V) := VNbr0_fixes_nbr Y H hZ hmV0 w.2
    have hy1 : y • Y.vert 1 = Y.vert 1 := by
      dsimp only [y]
      simp only [mul_smul]
      rw [hgw, hmw, hy1_inv]
    have hyG1 : y ∈ Y.Gi 1 := MulAction.mem_stabilizer_iff.mpr hy1
    have hyG0 : y ∈ Y.Gi 0 := by
      rw [MulAction.mem_stabilizer_iff]
      exact hy0
    have hmove : ∃ v0 ∈ NbrSet Y w, (m : G) • v0 ≠ v0 := by
      by_contra hall
      push Not at hall
      exact hnf (fun v hv => hall v hv)
    obtain ⟨v0, hv0, hmv0⟩ := hmove
    let v : V := g⁻¹ • v0
    have hv : v ∈ NbrSet Y ⟨Y.vert 1, by simpa using Y.adj 0⟩ := by
      refine ⟨?_, ?_⟩
      · have hv0adj : Γ.Adj (g⁻¹ • (w : V)) (g⁻¹ • v0) :=
          (Y.hyp.adj_smul g⁻¹ (w : V) v0).mpr hv0.1
        rwa [hy1_inv] at hv0adj
      · intro h
        apply hv0.2
        have h' := congrArg (fun z => g • z) h
        simpa [v, mul_smul, hg0] using h'
    have hyv : y • v ≠ v := by
      intro hfixv
      apply hmv0
      have h := congrArg (fun z => g • z) hfixv
      dsimp only [y, v] at h
      simpa [mul_smul] using h
    obtain ⟨h, hhZ, hh0, hh1, hh2, hh2sq⟩ := exists_Z_three_moving_zero Y H hZ
    have hp_adj : Γ.Adj (Y.vert 1) (h • Y.vert 0) := by
      have h := (Y.hyp.adj_smul h (Y.vert 1) (Y.vert 0)).mpr (by simpa using (Y.adj 0).symm)
      rwa [hh1] at h
    have hp_ne0 : h • Y.vert 0 ≠ Y.vert 0 := hh0
    have hp_ne2 : h • Y.vert 0 ≠ Y.vert 2 := by
      intro hp2
      have h' : h • Y.vert 0 = h • Y.vert 2 := hp2.trans hh2.symm
      exact (vert_zero_ne_vert_two Y).symm (MulAction.injective h h'.symm)
    have hp_inv : h⁻¹ • Y.vert 0 = h • Y.vert 0 := by
      have hhh : h⁻¹ = h := inv_eq_of_mul_eq_one_right hh2sq
      rw [hhh]
    have hp_moved : y • (h • Y.vert 0) = Y.vert 2 :=
      smul_third_eq_two Y H hy1 hy0 hv.1 hv.2 hyv hp_adj hp_ne0 hp_ne2
    let n : G := h * y * h⁻¹
    have hn0 : n • Y.vert 0 = Y.vert 2 := by
      dsimp only [n]
      rw [mul_smul, mul_smul, hp_inv, hp_moved, hh2]
    have hZ3G1 : Y.Z 3 ≤ Y.Gi 1 := by
      have hb3 := (Y.s52_step9_cons H hZ).2 3 (by norm_num)
      have := hb3.1 (-2) (by norm_num)
      simpa using this
    have hnZ1 : Y.Z 1 ≤ Subgroup.centralizer ({n} : Set G) :=
      Z_one_le_centralizer_conj Y H hZ hmC hgG0 rfl hhZ hZ3G1
    exact zOf_mem_Z_two_of_conj Y H hZ hn0 hnZ1
  have hzero : (if FixSet Y (m : G) w then (0 : ZMod 2) else 1) = 0 := by
    rw [if_pos hfix]
  exact hzero

private theorem relIndex_Z_zero_ker_phi_le_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) :
    ((Y.Z 0).subgroupOf Y.VNbr0).relIndex (phi Y H hZ).ker ≤ 2 := by
  obtain ⟨-, -, -, -, hZ1sup, -, -, -⟩ := Y.s52_step8 H hZ
  haveI : Finite ↥Y.VNbr0 := finite_of_le_stabilizer Y.hyp (H := Y.VNbr0)
    ((VNbr0_props Y H hZ).1.trans (Y.Q_le_Gi 0))
  haveI : Finite ↥(phi Y H hZ).range := by
    refine Finite.of_surjective (fun x : ↥(Y.VNbr0) =>
      (⟨phi Y H hZ x, MonoidHom.mem_range.mpr ⟨x, rfl⟩⟩ : ↥(phi Y H hZ).range)) ?_
    rintro ⟨y, hy⟩
    obtain ⟨x, rfl⟩ := hy
    exact ⟨x, rfl⟩
  have hrange : 2 ^ (2 ^ n₀) ≤ Nat.card ↥(phi Y H hZ).range := by
    rw [← card_finset_Delta Y H]
    exact Nat.card_le_card_of_injective (prodVec Y H hZ) (prodVec_injective Y H hZ)
  let A : Subgroup ↥(Y.VNbr0) := (Y.Z 0).subgroupOf Y.VNbr0
  let K : Subgroup ↥(Y.VNbr0) := (phi Y H hZ).ker
  have hZ0center : Y.Z 0 ≤ centerOf Y.VNbr0 := by
    intro z hz
    refine Subgroup.mem_inf.mpr ⟨Z_one_le_VNbr0 Y H hZ (by
      rw [hZ1sup]
      exact (le_sup_left : (Y.Z 0 : Subgroup G) ≤ Y.Z 0 ⊔ Y.Z 2) hz), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro v hv
    have hvL : v ∈ Y.L 0 := by
      exact (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le ((VNbr0_props Y H hZ).1 hv)
    have hzcenter : z ∈ centerOf (Y.L 0) := by
      rw [← (Y.s52_step8 H hZ).1]
      exact hz
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzcenter).2 v hvL
  have hAK : A ≤ K := by
    intro z hz
    exact centerOf_VNbr0_subgroupOf_le_ker_phi Y H hZ (hZ0center hz)
  haveI : Finite ↥K :=
    Finite.of_injective (fun x : ↥K => (x : ↥(Y.VNbr0))) (fun a b h => Subtype.ext h)
  have hKindex : K.index = Nat.card ↥(phi Y H hZ).range := by
    rw [Subgroup.index_eq_card]
    exact Nat.card_congr (QuotientGroup.quotientKerEquivRange (phi Y H hZ)).toEquiv
  have hAindex : A.index = Nat.card ↥(phi Y H hZ).range * A.relIndex K := by
    have h := Subgroup.relIndex_mul_index (H := A) (K := K) hAK
    rw [hKindex] at h
    rw [← h, mul_comm]
  have hrel : (Y.Z 0).relIndex Y.VNbr0 = A.index := by
    have h := Subgroup.relIndex_subgroupOf (H := Y.Z 0) (K := Y.VNbr0) (L := Y.VNbr0)
      le_rfl
    rw [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h
    exact h.symm
  have hupper : (Y.Z 0).relIndex Y.VNbr0 ≤ 2 ^ (2 ^ n₀ + 1) :=
    relIndex_Z_zero_VNbr0_le Y H hZ
  have hEq : Nat.card ↥(phi Y H hZ).range * A.relIndex K ≤ 2 ^ (2 ^ n₀ + 1) := by
    rw [← hAindex, ← hrel]
    exact hupper
  have hbound : 2 ^ (2 ^ n₀) * A.relIndex K ≤ 2 ^ (2 ^ n₀) * 2 := by
    calc 2 ^ (2 ^ n₀) * A.relIndex K ≤ Nat.card ↥(phi Y H hZ).range * A.relIndex K :=
          Nat.mul_le_mul_right _ hrange
      _ ≤ 2 ^ (2 ^ n₀ + 1) := hEq
      _ = 2 ^ (2 ^ n₀) * 2 := by rw [pow_succ]
  simpa [A, K] using Nat.le_of_mul_le_mul_left hbound (Nat.two_pow_pos (2 ^ n₀))

private theorem Z_zero_le_centerOf_VNbr0 (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) : Y.Z 0 ≤ centerOf Y.VNbr0 := by
  obtain ⟨-, -, -, -, hZ1sup, -, -, -⟩ := Y.s52_step8 H hZ
  intro z hz
  refine Subgroup.mem_inf.mpr ⟨Z_one_le_VNbr0 Y H hZ (by
    rw [hZ1sup]
    exact (le_sup_left : (Y.Z 0 : Subgroup G) ≤ Y.Z 0 ⊔ Y.Z 2) hz), ?_⟩
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have hvL : v ∈ Y.L 0 := (Y.hyp.isLocL2_oTwoPrime (Y.vert 0)).oTwo_le ((VNbr0_props Y H hZ).1 hv)
  have hzcenter : z ∈ centerOf (Y.L 0) := by
    rw [← (Y.s52_step8 H hZ).1]
    exact hz
  exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzcenter).2 v hvL

private theorem relIndex_Z_zero_center_le_two (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) :
    (Y.Z 0).relIndex (centerOf Y.VNbr0) ≤ 2 := by
  haveI : Finite ↥Y.VNbr0 := finite_of_le_stabilizer Y.hyp (H := Y.VNbr0)
    ((VNbr0_props Y H hZ).1.trans (Y.Q_le_Gi 0))
  let A : Subgroup ↥(Y.VNbr0) := (Y.Z 0).subgroupOf Y.VNbr0
  let M : Subgroup ↥(Y.VNbr0) := (centerOf Y.VNbr0).subgroupOf Y.VNbr0
  let K : Subgroup ↥(Y.VNbr0) := (phi Y H hZ).ker
  have hAM : A ≤ M := by
    intro z hz
    exact Z_zero_le_centerOf_VNbr0 Y H hZ hz
  have hMK : M ≤ K := centerOf_VNbr0_subgroupOf_le_ker_phi Y H hZ
  haveI : Finite ↥K :=
    Finite.of_injective (fun x : ↥K => (x : ↥(Y.VNbr0))) (fun a b h => Subtype.ext h)
  have hKpos : 0 < A.relIndex K := by
    have hcard : 0 < Nat.card ↥K := Nat.card_pos
    exact Nat.pos_of_dvd_of_pos (Subgroup.relIndex_dvd_card (H := A) (K := K)) hcard
  have hle : A.relIndex M ≤ A.relIndex K :=
    Subgroup.relIndex_le_of_le_right hMK (Nat.pos_iff_ne_zero.mp hKpos)
  have hKle : A.relIndex K ≤ 2 := relIndex_Z_zero_ker_phi_le_two Y H hZ
  have hAM' : A.relIndex M ≤ 2 := hle.trans hKle
  have hMleV : centerOf Y.VNbr0 ≤ Y.VNbr0 := inf_le_left
  have hrel : (Y.Z 0).relIndex (centerOf Y.VNbr0) = A.relIndex M := by
    have h := Subgroup.relIndex_subgroupOf (H := Y.Z 0) (K := centerOf Y.VNbr0)
      (L := Y.VNbr0) hMleV
    exact h.symm
  rwa [hrel]

private theorem commutator_center_L_zero_le_Z_zero (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀)
    (hZ : Y.Zt 0 = ⊥) :
    ∀ m ∈ centerOf Y.VNbr0, ∀ l ∈ Y.L 0, ⁅m, l⁆ ∈ Y.Z 0 := by
  intro m hm l hl
  haveI : Finite ↥Y.VNbr0 := finite_of_le_stabilizer Y.hyp (H := Y.VNbr0)
    ((VNbr0_props Y H hZ).1.trans (Y.Q_le_Gi 0))
  haveI : Finite ↥(centerOf Y.VNbr0) :=
    Finite.of_injective (fun x : ↥(centerOf Y.VNbr0) =>
      (⟨x.1, (Subgroup.mem_inf.mp x.2).1⟩ : ↥Y.VNbr0))
      (fun a b h => Subtype.ext (congrArg (fun y : ↥Y.VNbr0 => (y : G)) h))
  have hle : (Y.Z 0).relIndex (centerOf Y.VNbr0) ≤ 2 :=
    relIndex_Z_zero_center_le_two Y H hZ
  have hpos : 0 < (Y.Z 0).relIndex (centerOf Y.VNbr0) := by
    have hcard : 0 < Nat.card ↥(centerOf Y.VNbr0) := Nat.card_pos
    exact Nat.pos_of_dvd_of_pos
      (Subgroup.relIndex_dvd_card (H := Y.Z 0) (K := centerOf Y.VNbr0)) hcard
  have hdvd : (Y.Z 0).relIndex (centerOf Y.VNbr0) ∣ 2 := by
    have h12 : (Y.Z 0).relIndex (centerOf Y.VNbr0) = 1 ∨
        (Y.Z 0).relIndex (centerOf Y.VNbr0) = 2 := by omega
    rcases h12 with h | h <;> rw [h] <;> norm_num
  obtain ⟨a, haM, ha⟩ :=
    (Subgroup.relIndex_dvd_two_iff.mp hdvd)
  have hVnorm : conjSub l (Y.VNbr0) = Y.VNbr0 :=
    mem_normalizer_iff_conjSub.mp ((VNbr0_props Y H hZ).2.1 (Y.L_le_Gi 0 hl))
  have hMconj : conjSub l (centerOf Y.VNbr0) = centerOf Y.VNbr0 := by
    rw [← centerOf_conjSub, hVnorm]
  have hm' : l * m * l⁻¹ ∈ centerOf Y.VNbr0 := by
    have h := mul_mem_conjSub (g := l) hm
    rwa [hMconj] at h
  by_cases hmZ : m ∈ Y.Z 0
  · have hzcenter : m ∈ centerOf (Y.L 0) := by
      rw [← (Y.s52_step8 H hZ).1]
      exact hmZ
    have hcomm : m * l = l * m :=
      (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hzcenter).2 l hl).symm
    rw [commutatorElement_eq_one_iff_mul_comm.mpr hcomm]
    exact (Y.Z 0).one_mem
  · have hm'Z : l * m * l⁻¹ ∉ Y.Z 0 := by
      intro hm'Z
      apply hmZ
      have hzcenter' : l * m * l⁻¹ ∈ centerOf (Y.L 0) := by
        rw [← (Y.s52_step8 H hZ).1]
        exact hm'Z
      have hcomm := Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp hzcenter').2 l⁻¹ ((Y.L 0).inv_mem hl)
      have hm_eq : m = l * m * l⁻¹ := by
        calc m = l⁻¹ * (l * m * l⁻¹) * l := by group
          _ = (l * m * l⁻¹) := by
              rw [hcomm]
              group
      rwa [hm_eq]
    have hma : m * a ∈ Y.Z 0 := by
      rcases ha m hm with h | h
      · exact h
      · exact absurd h hmZ
    have hm'a : (l * m * l⁻¹) * a ∈ Y.Z 0 := by
      rcases ha (l * m * l⁻¹) hm' with h | h
      · exact h
      · exact absurd h hm'Z
    have hform : ⁅m, l⁆ = (m * a) * ((l * m * l⁻¹) * a)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [hform]
    exact (Y.Z 0).mul_mem hma ((Y.Z 0).inv_mem hm'a)

theorem centerOf_Q_zero_of_VNbr0_eq (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) (hZ : Y.Zt 0 = ⊥)
    (hV : Y.VNbr0 = Y.Q 0) : centerOf (Y.Q 0) = Y.Z 0 := by
  rw [← hV]
  refine le_antisymm ?_ (Z_zero_le_centerOf_VNbr0 Y H hZ)
  intro m hm
  have hmQ0 : m ∈ centerOf (Y.Q 0) := hV ▸ hm
  have hcomm : ∀ l ∈ Y.L 0, ⁅m, l⁆ ∈ Y.Z 0 :=
    commutator_center_L_zero_le_Z_zero Y H hZ m hm
  have hcenterL : m ∈ centerOf (Y.L 0) :=
    Y.mem_centerOf_L_of_commutator_mem
      (Y.L_eq_commutator_sup_Q 0 H.two_le (Y.isL2Quot_L_zero H)) hmQ0 (fun l hl => by
      rw [← (Y.s52_step8 H hZ).1]
      exact hcomm l hl)
  rwa [← (Y.s52_step8 H hZ).1] at hcenterL

end Setup

end CFSG.Quasithin.St84

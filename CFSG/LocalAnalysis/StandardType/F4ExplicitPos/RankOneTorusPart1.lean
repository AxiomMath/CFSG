module

public import CFSG.HardMathSupport.Timmesfeld.ComponentBalance.I_11_3_TablesA
public import CFSG.LieType.Chevalley.E6GraphRadicalDetector
public import CFSG.LieType.SeitzGeneration.HeisTorusU87Arith
public import CFSG.Monster.B.Fischer.Fi22Order
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.BorelTits.CompleteFlag
public import CFSG.LieType.Chevalley.C2E6StandardFixedData
public import CFSG.LieType.Chevalley.C2E6UnitaryFourImages
public import CFSG.LieType.Chevalley.E6GraphHighestRootNormalizer
public import CFSG.LieType.Chevalley.E6GraphRadicalCoords
public import CFSG.LieType.Chevalley.RootCommutatorCertificate
public import CFSG.LieType.Chevalley.SimplyLacedFieldTwoCover
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSubspaceIndex
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Inputs
public import CFSG.LocalAnalysis.GLTheoremB.Prop98Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs

@[expose] public section

public section

namespace CFSG.StandardType.F4ExplicitPos.RankOneTorus

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.CurtisTits CFSG.LieType.Universal

variable {K : Type} [Field K] [CharP K 2]

noncomputable def simpleRootMap
    (K : Type) [Field K] (i : Fin Tag.F4.rank) :
    SL2 K →* ↥(adjointGroup Tag.F4 K) :=
  (simpleRootSL2 Tag.F4 K i).codRestrict (adjointGroup Tag.F4 K)
    (simpleRootSL2_mem_adjointGroup i)

theorem rootGroup_single_eq
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) :
    rootGroup F K (Pi.single i 1) = F.rootSubgroup K (simpleRoot Tag.F4 i) := by
  classical
  rw [show rootGroup F K (Pi.single i 1) =
      (if h : IsRoot Tag.F4 (Pi.single i 1) then F.rootSubgroup K ⟨Pi.single i 1, h⟩ else ⊥)
      from rfl, dif_pos (isRoot_single Tag.F4 i)]
  rfl

theorem rootGroup_neg_single_eq
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) :
    rootGroup F K (-Pi.single i 1) = F.rootSubgroup K (-simpleRoot Tag.F4 i) := by
  classical
  rw [show rootGroup F K (-Pi.single i 1) =
      (if h : IsRoot Tag.F4 (-Pi.single i 1) then F.rootSubgroup K ⟨-Pi.single i 1, h⟩ else ⊥)
      from rfl, dif_pos (isRoot_neg_single Tag.F4 i)]
  rfl

theorem xPar_single_eq
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (c : K) :
    xPar F (Pi.single i 1) c = F.eltElement (simpleRoot Tag.F4 i) c := by
  classical
  rw [show xPar F (Pi.single i 1) c =
      F.eltElement ⟨Pi.single i 1, isRoot_single Tag.F4 i⟩ c from
    dif_pos (isRoot_single Tag.F4 i)]
  rfl

theorem xPar_neg_single_eq
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (c : K) :
    xPar F (-Pi.single i 1) c = F.eltElement (-simpleRoot Tag.F4 i) c := by
  classical
  rw [show xPar F (-Pi.single i 1) c =
      F.eltElement ⟨-Pi.single i 1, isRoot_neg_single Tag.F4 i⟩ c from
    dif_pos (isRoot_neg_single Tag.F4 i)]
  rfl

theorem xPar_coe_single
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (c : K) :
    (xPar F (Pi.single i 1) c : ModGL Tag.F4 K) = xUnit Tag.F4 K i c := by
  rw [xPar_single_eq, F.coe_eltElement, F.eltUnit_simple]

theorem xPar_coe_neg_single
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (c : K) :
    (xPar F (-Pi.single i 1) c : ModGL Tag.F4 K) = yUnit Tag.F4 K i c := by
  rw [xPar_neg_single_eq, F.coe_eltElement, F.eltUnit_neg_simple]

theorem xPar_single_mem
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (c : K) :
    xPar F (Pi.single i 1) c ∈ rootGroup F K (Pi.single i 1) := by
  rw [rootGroup_single_eq, xPar_single_eq]
  exact F.eltElement_mem_rootSubgroup _ c

theorem xPar_neg_single_mem
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (c : K) :
    xPar F (-Pi.single i 1) c ∈ rootGroup F K (-Pi.single i 1) := by
  rw [rootGroup_neg_single_eq, xPar_neg_single_eq]
  exact F.eltElement_mem_rootSubgroup _ c

theorem mem_rootGroup_single_iff
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (g : ↥(adjointGroup Tag.F4 K)) :
    g ∈ rootGroup F K (Pi.single i 1) ↔ ∃ c : K, xPar F (Pi.single i 1) c = g := by
  rw [rootGroup_single_eq]
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := F.mem_rootSubgroup.1 hg
    exact ⟨c, by rw [xPar_single_eq]; exact hc⟩
  · rintro ⟨c, rfl⟩
    rw [xPar_single_eq]
    exact F.eltElement_mem_rootSubgroup _ c

theorem mem_rootGroup_neg_single_iff
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (g : ↥(adjointGroup Tag.F4 K)) :
    g ∈ rootGroup F K (-Pi.single i 1) ↔ ∃ c : K, xPar F (-Pi.single i 1) c = g := by
  rw [rootGroup_neg_single_eq]
  constructor
  · intro hg
    obtain ⟨c, hc⟩ := F.mem_rootSubgroup.1 hg
    exact ⟨c, by rw [xPar_neg_single_eq]; exact hc⟩
  · rintro ⟨c, rfl⟩
    rw [xPar_neg_single_eq]
    exact F.eltElement_mem_rootSubgroup _ c

theorem simpleRootMap_uSL
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (c : K) :
    simpleRootMap K i (uSL c) = xPar F (Pi.single i 1) c := by
  apply Subtype.ext
  change (simpleRootSL2 Tag.F4 K i (uSL c) : ModGL Tag.F4 K) = _
  rw [simpleRootSL2_uSL, xPar_coe_single]

theorem simpleRootMap_vSL
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (c : K) :
    simpleRootMap K i (vSL c) = xPar F (-Pi.single i 1) c := by
  apply Subtype.ext
  change (simpleRootSL2 Tag.F4 K i (vSL c) : ModGL Tag.F4 K) = _
  rw [simpleRootSL2_vSL, xPar_coe_neg_single]

theorem simpleRootMap_HSL
    (i : Fin Tag.F4.rank) (t : Kˣ) :
    simpleRootMap K i (HSL t) = torusElement Tag.F4 K i t := by
  apply Subtype.ext
  change (simpleRootSL2 Tag.F4 K i (HSL t) : ModGL Tag.F4 K) = torusElt Tag.F4 K i t
  rw [simpleRootSL2_HSL]

theorem simpleRootMap_WSL
    (i : Fin Tag.F4.rank) :
    simpleRootMap K i WSL = weylElement Tag.F4 K i := by
  apply Subtype.ext
  change (simpleRootSL2 Tag.F4 K i WSL : ModGL Tag.F4 K) = weylElt Tag.F4 K i 1
  rw [simpleRootSL2_WSL]

theorem simpleRootMap_injective
    (i : Fin Tag.F4.rank) :
    Function.Injective (simpleRootMap (K := K) i) := by
  intro A B h
  apply E6GraphRadical.simpleRootSL2_injective_of_two (CharP.cast_eq_zero K 2) i
  exact congrArg (fun x : ↥(adjointGroup Tag.F4 K) => (x : ModGL Tag.F4 K)) h

theorem rootGroup_single_le_range
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) :
    rootGroup F K (Pi.single i 1) ≤ (simpleRootMap (K := K) i).range := by
  intro g hg
  obtain ⟨c, rfl⟩ := (mem_rootGroup_single_iff F i g).1 hg
  exact ⟨uSL c, simpleRootMap_uSL F i c⟩

theorem rootGroup_neg_single_le_range
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) :
    rootGroup F K (-Pi.single i 1) ≤ (simpleRootMap (K := K) i).range := by
  intro g hg
  obtain ⟨c, rfl⟩ := (mem_rootGroup_neg_single_iff F i g).1 hg
  exact ⟨vSL c, simpleRootMap_vSL F i c⟩

theorem rankOne_le_range
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) :
    rankOne (rootGroup F K) i ≤ (simpleRootMap (K := K) i).range :=
  sup_le (rootGroup_single_le_range F i) (rootGroup_neg_single_le_range F i)

noncomputable def steinbergWeyl
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank)
    (t : Kˣ) : ↥(adjointGroup Tag.F4 K) :=
  xPar F (Pi.single i 1) (t : K) * xPar F (-Pi.single i 1) (-(t⁻¹ : K)) *
    xPar F (Pi.single i 1) (t : K)

theorem steinbergWeyl_eq_weylElt
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (t : Kˣ) :
    steinbergWeyl F i t =
      (⟨weylElt Tag.F4 K i t, weylElt_mem_adjointGroup i t⟩ : ↥(adjointGroup Tag.F4 K)) := by
  apply Subtype.ext
  simp only [steinbergWeyl, Subgroup.coe_mul, xPar_coe_single,
    xPar_coe_neg_single]
  refine Units.ext ?_
  simp only [Units.val_mul, coe_xUnit, coe_yUnit, coe_weylElt]
  rw [Units.val_inv_eq_inv_val]

theorem steinbergWeyl_mem_rankOne
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (t : Kˣ) :
    steinbergWeyl F i t ∈ rankOne (rootGroup F K) i := by
  rw [steinbergWeyl]
  exact mul_mem (mul_mem (Subgroup.mem_sup_left (xPar_single_mem F i _))
    (Subgroup.mem_sup_right (xPar_neg_single_mem F i _)))
    (Subgroup.mem_sup_left (xPar_single_mem F i _))

theorem weylElement_mem_rankOne
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) :
    weylElement Tag.F4 K i ∈ rankOne (rootGroup F K) i := by
  change (⟨weylElt Tag.F4 K i 1, weylElt_mem_adjointGroup i 1⟩ :
    ↥(adjointGroup Tag.F4 K)) ∈ rankOne (rootGroup F K) i
  rw [← steinbergWeyl_eq_weylElt F i 1]
  exact steinbergWeyl_mem_rankOne F i 1

theorem torusElement_mem_rankOne
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) (t : Kˣ) :
    torusElement Tag.F4 K i t ∈ rankOne (rootGroup F K) i := by
  have h : torusElement Tag.F4 K i t =
      (⟨weylElt Tag.F4 K i t, weylElt_mem_adjointGroup i t⟩ : ↥(adjointGroup Tag.F4 K)) *
        (⟨weylElt Tag.F4 K i 1, weylElt_mem_adjointGroup i 1⟩ :
          ↥(adjointGroup Tag.F4 K))⁻¹ := by
    apply Subtype.ext
    change torusElt Tag.F4 K i t = weylElt Tag.F4 K i t * (weylElt Tag.F4 K i 1)⁻¹
    rw [weylElt_inv]
    rfl
  rw [h, ← steinbergWeyl_eq_weylElt F i t, ← steinbergWeyl_eq_weylElt F i 1]
  exact mul_mem (steinbergWeyl_mem_rankOne F i t) (inv_mem (steinbergWeyl_mem_rankOne F i 1))

theorem range_le_rankOne
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) :
    (simpleRootMap (K := K) i).range ≤ rankOne (rootGroup F K) i := by
  intro A hA
  obtain ⟨B, rfl⟩ := MonoidHom.mem_range.1 hA
  by_cases hc : (B : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · rw [eq_HSL_mul_uSL hc, map_mul, simpleRootMap_HSL, simpleRootMap_uSL F]
    exact mul_mem (torusElement_mem_rankOne F i _)
      (Subgroup.mem_sup_left (xPar_single_mem F i _))
  · rw [eq_uSL_mul_HSL_mul_WSL_mul_uSL hc, map_mul, map_mul, map_mul,
      simpleRootMap_uSL F, simpleRootMap_HSL, simpleRootMap_WSL, simpleRootMap_uSL F]
    exact mul_mem (mul_mem (mul_mem (Subgroup.mem_sup_left (xPar_single_mem F i _))
      (torusElement_mem_rankOne F i _)) (weylElement_mem_rankOne F i))
      (Subgroup.mem_sup_left (xPar_single_mem F i _))

theorem simpleRootMap_range
    (F : RootOperatorFamily Tag.F4) (i : Fin Tag.F4.rank) :
    (simpleRootMap (K := K) i).range = rankOne (rootGroup F K) i :=
  le_antisymm (range_le_rankOne F i) (rankOne_le_range F i)

theorem torusElement_mul_weylElement
    (i : Fin Tag.F4.rank) (t : Kˣ) :
    torusElement Tag.F4 K i t * weylElement Tag.F4 K i =
      weylElement Tag.F4 K i * torusElement Tag.F4 K i t⁻¹ := by
  apply Subtype.ext
  change torusElt Tag.F4 K i t * weylElt Tag.F4 K i 1 =
    weylElt Tag.F4 K i 1 * torusElt Tag.F4 K i t⁻¹
  have h2 : torusElt Tag.F4 K i t * weylElt Tag.F4 K i 1 =
      weylElt Tag.F4 K i 1 * torusElt Tag.F4 K i t⁻¹ := by
    have h := weylElt_mul_torusElt_mul_inv (τ := Tag.F4) (K := K) i t⁻¹
    rw [inv_inv] at h
    calc torusElt Tag.F4 K i t * weylElt Tag.F4 K i 1 =
        (weylElt Tag.F4 K i 1 * torusElt Tag.F4 K i t⁻¹ *
          (weylElt Tag.F4 K i 1)⁻¹) * weylElt Tag.F4 K i 1 := by rw [h]
      _ = weylElt Tag.F4 K i 1 * torusElt Tag.F4 K i t⁻¹ := by group
  exact h2

theorem rankOne_bruhat
    (F : RootOperatorFamily Tag.F4)
    (i : Fin Tag.F4.rank) {g : ↥(adjointGroup Tag.F4 K)}
    (hg : g ∈ rankOne (rootGroup F K) i) :
    (∃ h ∈ torus (τ := Tag.F4) K i, ∃ u ∈ rootGroup F K (Pi.single i 1), g = h * u) ∨
      ∃ u ∈ rootGroup F K (Pi.single i 1), ∃ h ∈ torus (τ := Tag.F4) K i,
        ∃ v ∈ rootGroup F K (Pi.single i 1),
          g = u * weylElement Tag.F4 K i * h * v := by
  obtain ⟨A, rfl⟩ := rankOne_le_range F i hg
  by_cases hc : (A : Matrix (Fin 2) (Fin 2) K) 1 0 = 0
  · left
    rw [eq_HSL_mul_uSL hc, map_mul, simpleRootMap_HSL, simpleRootMap_uSL F]
    refine ⟨torusElement Tag.F4 K i _, ⟨_, rfl⟩, xPar F (Pi.single i 1) _,
      xPar_single_mem F i _, rfl⟩
  · right
    rw [eq_uSL_mul_HSL_mul_WSL_mul_uSL hc, map_mul, map_mul, map_mul,
      simpleRootMap_uSL F, simpleRootMap_HSL, simpleRootMap_WSL, simpleRootMap_uSL F]
    set a : K := (A : Matrix (Fin 2) (Fin 2) K) 0 0 / (A : Matrix (Fin 2) (Fin 2) K) 1 0 with ha
    set d : K := (A : Matrix (Fin 2) (Fin 2) K) 1 1 / (A : Matrix (Fin 2) (Fin 2) K) 1 0 with hd
    set t : Kˣ := Units.mk0 (-1 / (A : Matrix (Fin 2) (Fin 2) K) 1 0)
      (div_ne_zero (neg_ne_zero.2 one_ne_zero) hc) with ht
    refine ⟨xPar F (Pi.single i 1) a, xPar_single_mem F i a, torusElement Tag.F4 K i t⁻¹,
      ⟨t⁻¹, rfl⟩, xPar F (Pi.single i 1) d, xPar_single_mem F i d, ?_⟩
    rw [mul_assoc (xPar F (Pi.single i 1) a) (torusElement Tag.F4 K i t)
        (weylElement Tag.F4 K i),
      torusElement_mul_weylElement i t]
    group

theorem eq_one_of_uSL_mul_vSL_mul_inv {c d : K}
    (h : uSL c * vSL 1 * (uSL c)⁻¹ = vSL d) : c = 0 := by
  have h00 := congrArg (fun M : SL2 K => ((M : Matrix (Fin 2) (Fin 2) K) 0 0)) h
  simp [coe_uSL, coe_vSL] at h00
  linear_combination h00

theorem eq_one_of_mem_normalizer
    (F : RootOperatorFamily Tag.F4)
    (i : Fin Tag.F4.rank) {u : ↥(adjointGroup Tag.F4 K)}
    (hu : u ∈ rootGroup F K (Pi.single i 1))
    (hn : u ∈ Subgroup.normalizer (rootGroup F K (-Pi.single i 1) :
      Set ↥(adjointGroup Tag.F4 K))) :
    u = 1 := by
  obtain ⟨c, hc⟩ := (mem_rootGroup_single_iff F i u).1 hu
  have hy : xPar F (-Pi.single i 1) 1 ∈ rootGroup F K (-Pi.single i 1) :=
    xPar_neg_single_mem F i 1
  have hconj : u * xPar F (-Pi.single i 1) 1 * u⁻¹ ∈ rootGroup F K (-Pi.single i 1) :=
    (Subgroup.mem_normalizer_iff.1 hn (xPar F (-Pi.single i 1) 1)).1 hy
  obtain ⟨d, hd⟩ := (mem_rootGroup_neg_single_iff F i _).1 hconj
  have huSL : simpleRootMap K i (uSL c) = u := by
    rw [simpleRootMap_uSL F]
    exact hc
  have hvSL : simpleRootMap K i (vSL 1) = xPar F (-Pi.single i 1) 1 :=
    simpleRootMap_vSL F i 1
  have hdSL : simpleRootMap K i (vSL d) = xPar F (-Pi.single i 1) d :=
    simpleRootMap_vSL F i d
  have hSL : uSL c * vSL 1 * (uSL c)⁻¹ = vSL d := by
    apply simpleRootMap_injective (K := K) i
    rw [map_mul, map_mul, map_inv, huSL, hvSL, hdSL]
    exact hd.symm
  have hc0 : c = 0 := eq_one_of_uSL_mul_vSL_mul_inv hSL
  rw [hc0] at hc
  exact Subtype.ext (by rw [← hc, xPar_coe_single, xUnit_zero]; rfl)

theorem torus_commute
    {i j : Fin Tag.F4.rank} {g h : ↥(adjointGroup Tag.F4 K)}
    (hg : g ∈ torus (τ := Tag.F4) K i) (hh : h ∈ torus (τ := Tag.F4) K j) : Commute g h := by
  obtain ⟨t, rfl⟩ := (MonoidHom.mem_range.1 hg)
  obtain ⟨u, rfl⟩ := (MonoidHom.mem_range.1 hh)
  exact Subtype.ext (torusElt_mul_comm i j t u)

theorem zpow_finset_sum' {G : Type*} [CommGroup G] (a : G) {ι : Type*} (s : Finset ι)
    (f : ι → ℤ) : a ^ (∑ i ∈ s, f i) = ∏ i ∈ s, a ^ f i := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih => rw [Finset.sum_insert hx, Finset.prod_insert hx, zpow_add, ih]

end CFSG.StandardType.F4ExplicitPos.RankOneTorus
end

end

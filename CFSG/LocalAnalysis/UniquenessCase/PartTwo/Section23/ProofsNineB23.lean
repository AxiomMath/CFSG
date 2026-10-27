module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveLine
public import CFSG.GroupTheory.Commutator.SubgroupOf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineK

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem Hinf_inf_L_perfect (c : Ctx23L D Ch) :
    ⁅Hinf (D.M ⊓ c.L), Hinf (D.M ⊓ c.L)⁆ = Hinf (D.M ⊓ c.L) :=
  uc22p21c_Hinf_perfect (D.M ⊓ c.L)

theorem barImage_Hinf_inf_L_perfect (c : Ctx23L D Ch) :
    ⁅barImage D.M (Hinf (D.M ⊓ c.L)), barImage D.M (Hinf (D.M ⊓ c.L))⁆ =
      barImage D.M (Hinf (D.M ⊓ c.L)) := by
  have hKM : Hinf (D.M ⊓ c.L) ≤ D.M :=
    (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left
  unfold barImage
  rw [← Subgroup.map_commutator,
    CFSG.GroupTheory.commutator_subgroupOf_eq hKM hKM, c.Hinf_inf_L_perfect]

theorem barImage_Hinf_inf_L_le_layer (hB1 : S23_9_B1 D Ch) (h1930 : H1930 D)
    (c : Ctx23L D Ch) (h3 : 3 ≤ CFSG.Open.pRank 2 D.Z) :
    barImage D.M (Hinf (D.M ⊓ c.L)) ≤ CFSG.layer (Bar2 D.M) :=
  hB1 h1930 c h3

@[expose] noncomputable def K (c : Ctx23L D Ch) : Subgroup G :=
  Hinf (D.M ⊓ c.L)

theorem K_le_L (c : Ctx23L D Ch) : K c ≤ c.L :=
  (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_right

theorem K_le_M (c : Ctx23L D Ch) : K c ≤ D.M :=
  (uc22p21c_Hinf_le (D.M ⊓ c.L)).trans inf_le_left

noncomputable abbrev Kstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Subgroup ↥(c.H hV) :=
  ((c.phiL hV).comp (Subgroup.inclusion (K_le_L c))).range

@[expose] noncomputable def phiK (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    ↥(K c) →* ↥(Kstar c hV) :=
  ((c.phiL hV).comp (Subgroup.inclusion (K_le_L c))).rangeRestrict

@[expose] noncomputable def RK (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Subgroup ↥(K c) :=
  (CFSG.pCore 2 ↥(Kstar c hV)).comap (phiK c hV)

abbrev KstarBar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) : Type :=
  Bar2 (Kstar c hV)

noncomputable def psiK (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    ↥(K c) →* KstarBar c hV :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥(Kstar c hV))).comp (phiK c hV)

theorem psiK_surjective (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Function.Surjective (psiK c hV) := by
  intro w
  obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥(Kstar c hV)) w
  obtain ⟨k, rfl⟩ := MonoidHom.rangeRestrict_surjective
    ((c.phiL hV).comp (Subgroup.inclusion (K_le_L c))) x
  exact ⟨k, rfl⟩

theorem psiK_ker (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    (psiK c hV).ker = RK c hV := by
  rw [psiK, RK, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']

theorem RK_normal (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    (RK c hV).Normal := by
  rw [← psiK_ker c hV]
  infer_instance

private theorem pCore_subgroupOf_ker_isSolvable (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) :
    Group.IsSolvable ↥((CFSG.pCore 2 ↥c.L).subgroupOf (c.phiL hV).ker) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : Group.IsSolvable ↥(CFSG.pCore 2 ↥c.L) := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥c.L)).isNilpotent
    infer_instance
  haveI : Group.IsSolvable ↥(CFSG.pCore 2 ↥c.L) := hN
  let h : ↥((CFSG.pCore 2 ↥c.L).subgroupOf (c.phiL hV).ker) →*
      ↥(CFSG.pCore 2 ↥c.L) :=
    { toFun := fun x => ⟨(x.1 : ↥c.L), Subgroup.mem_subgroupOf.mp x.2⟩
      map_one' := rfl
      map_mul' := fun _ _ => rfl }
  exact Group.isSolvable_of_isSolvable_injective (f := h) fun a b hab =>
    Subtype.ext (Subtype.ext (congrArg
      (fun y : ↥(CFSG.pCore 2 ↥c.L) => (y : ↥c.L)) hab))

theorem phiL_ker_isSolvable (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    Group.IsSolvable ↥(c.phiL hV).ker := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let N : Subgroup ↥c.L := CFSG.pCore 2 ↥c.L
  let π : ↥c.L →* Bar2 c.L := QuotientGroup.mk' N
  let E : Subgroup (Bar2 c.L) := (c.phiL hV).ker.map π
  have hEcenter : E ≤ Subgroup.center (Bar2 c.L) :=
    image_ker_le_center_of_commutator_le (N := N)
      (c.phiL_ker_commutator_mem_pCore hV hK hnat)
  have hE : Group.IsSolvable ↥E :=
    Group.isSolvable_of_comm fun a b =>
      Subtype.ext (Subgroup.mem_center_iff.mp (hEcenter b.2) (a : Bar2 c.L))
  let S : Subgroup ↥(c.phiL hV).ker := N.subgroupOf (c.phiL hV).ker
  have hS : Group.IsSolvable ↥S := by
    simpa only [S, N] using pCore_subgroupOf_ker_isSolvable c hV
  let g : ↥(c.phiL hV).ker →* ↥E :=
    (π.comp (c.phiL hV).ker.subtype).codRestrict E
      (fun x => Subgroup.mem_map_of_mem π x.2)
  have hgker : g.ker = S := by
    ext x
    change g x = 1 ↔ ((x : ↥c.L) ∈ N)
    constructor
    · intro hx
      have hx1 : π (x : ↥c.L) = 1 := by
        have := congrArg Subtype.val hx
        simpa [g] using this
      exact (QuotientGroup.eq_one_iff (x : ↥c.L)).mp hx1
    · intro hx
      apply Subtype.ext
      change π (x : ↥c.L) = 1
      exact (QuotientGroup.eq_one_iff (x : ↥c.L)).mpr hx
  haveI : Group.IsSolvable ↥S := hS
  haveI : Group.IsSolvable ↥E := hE
  refine Group.isSolvable_of_ker_le_range S.subtype g ?_
  rw [hgker, Subgroup.range_subtype]

private theorem phiK_ker_isSolvable (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    Group.IsSolvable ↥((c.phiL hV).comp (Subgroup.inclusion (K_le_L c))).ker := by
  haveI : Group.IsSolvable ↥(c.phiL hV).ker := phiL_ker_isSolvable c hV hK hnat
  let h : ↥((c.phiL hV).comp (Subgroup.inclusion (K_le_L c))).ker →*
      ↥(c.phiL hV).ker :=
    ((Subgroup.inclusion (K_le_L c)).comp
      (((c.phiL hV).comp (Subgroup.inclusion (K_le_L c))).ker.subtype)).codRestrict
        (c.phiL hV).ker (fun x => by
          simpa using (MonoidHom.mem_ker.mp x.2))
  exact Group.isSolvable_of_isSolvable_injective (f := h) fun a b hab =>
    Subtype.ext (Subgroup.inclusion_injective (K_le_L c)
      (congrArg (fun y : ↥(c.phiL hV).ker => (y : ↥c.L)) hab))

theorem RK_isSolvable (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    Group.IsSolvable ↥(RK c hV) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let φK : ↥(K c) →* ↥(c.H hV) :=
    (c.phiL hV).comp (Subgroup.inclusion (K_le_L c))
  let C0 : Subgroup ↥(K c) := φK.ker
  let P0 : Subgroup ↥(Kstar c hV) := CFSG.pCore 2 ↥(Kstar c hV)
  have hC0 : Group.IsSolvable ↥C0 := by
    simpa only [C0, φK] using phiK_ker_isSolvable c hV hK hnat
  have hP0 : Group.IsSolvable ↥P0 := by
    have := (CFSG.pCore_isPGroup (p := 2) (G := ↥(Kstar c hV))).isNilpotent
    infer_instance
  have hC0R : C0 ≤ RK c hV := by
    intro x hx
    rw [RK, Subgroup.mem_comap]
    have hx' : phiK c hV x = 1 := Subtype.ext (MonoidHom.mem_ker.mp hx)
    rw [hx']
    exact one_mem P0
  let f : ↥C0 →* ↥(RK c hV) := Subgroup.inclusion hC0R
  let g : ↥(RK c hV) →* ↥P0 :=
    ((phiK c hV).comp (RK c hV).subtype).codRestrict P0
      (fun x => Subgroup.mem_comap.mp x.2)
  have hgker : g.ker = C0.subgroupOf (RK c hV) := by
    ext x
    change g x = 1 ↔ φK x.1 = 1
    constructor
    · intro hx
      have hx1 : ((g x : ↥P0) : ↥(Kstar c hV)) = 1 := congrArg Subtype.val hx
      have hx2 : phiK c hV x.1 = 1 := hx1
      simpa [phiK, MonoidHom.coe_rangeRestrict, φK] using congrArg Subtype.val hx2
    · intro hx
      apply Subtype.ext
      change phiK c hV x.1 = 1
      exact Subtype.ext (by simpa [phiK, MonoidHom.coe_rangeRestrict, φK] using hx)
  haveI : Group.IsSolvable ↥C0 := hC0
  haveI : Group.IsSolvable ↥P0 := hP0
  refine Group.isSolvable_of_ker_le_range f g ?_
  rw [hgker, Subgroup.inclusion_range]

@[expose] noncomputable def Kbar (c : Ctx23L D Ch) : Subgroup (Bar2 D.M) :=
  barImage D.M (K c)

@[expose] noncomputable def toBar2M (c : Ctx23L D Ch) : ↥(K c) →* Bar2 D.M :=
  (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).comp (Subgroup.inclusion (K_le_M c))

theorem toBar2M_range (c : Ctx23L D Ch) : (toBar2M c).range = Kbar c := by
  rw [toBar2M, MonoidHom.range_comp, Subgroup.inclusion_range]
  rfl

@[expose] noncomputable def toKbar (c : Ctx23L D Ch) : ↥(K c) →* ↥(Kbar c) :=
  (toBar2M c).codRestrict (Kbar c) fun x => by
    rw [← toBar2M_range c]
    exact MonoidHom.mem_range.mpr ⟨x, rfl⟩

theorem toKbar_surjective (c : Ctx23L D Ch) : Function.Surjective (toKbar c) := by
  intro y
  have hy : (y : Bar2 D.M) ∈ (toBar2M c).range := by
    rw [toBar2M_range c]
    exact y.2
  obtain ⟨x, hx⟩ := MonoidHom.mem_range.mp hy
  exact ⟨x, Subtype.ext (by simpa [toKbar] using hx)⟩

@[expose] noncomputable def RKbar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    Subgroup ↥(Kbar c) :=
  (RK c hV).map (toKbar c)

instance RKbar_normal (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    (RKbar c hV).Normal :=
  (RK_normal c hV).map (toKbar c) (toKbar_surjective c)

theorem RKbar_isSolvable (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hK : KOrdNatural) {n : ℕ} (hnat : IsNaturalClassicalModule (c.H hV) n) :
    Group.IsSolvable ↥(RKbar c hV) := by
  haveI : Group.IsSolvable ↥(RK c hV) := RK_isSolvable c hV hK hnat
  exact Group.isSolvable_of_surjective
    (MonoidHom.subgroupMap_surjective (toKbar c) (RK c hV))

theorem exists_surjective_KstarBar_quotient (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) :
    ∃ f : KstarBar c hV →* (↥(Kbar c) ⧸ RKbar c hV), Function.Surjective f := by
  haveI : (RKbar c hV).Normal := RKbar_normal c hV
  haveI : (RK c hV).Normal := RK_normal c hV
  let h : ↥(K c) →* (↥(Kbar c) ⧸ RKbar c hV) :=
    (QuotientGroup.mk' (RKbar c hV)).comp (toKbar c)
  have hsurj : Function.Surjective h :=
    (QuotientGroup.mk'_surjective (RKbar c hV)).comp (toKbar_surjective c)
  have hR : RK c hV ≤ h.ker := by
    intro r hr
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.mk' (RKbar c hV)) (toKbar c r) = 1
    exact (QuotientGroup.eq_one_iff (toKbar c r)).mpr
      (Subgroup.mem_map_of_mem (toKbar c) hr)
  let lift : ↥(K c) ⧸ RK c hV →* (↥(Kbar c) ⧸ RKbar c hV) :=
    QuotientGroup.lift (RK c hV) h hR
  have hlift : Function.Surjective lift := by
    intro z
    obtain ⟨k, rfl⟩ := hsurj z
    refine ⟨QuotientGroup.mk' (RK c hV) k, ?_⟩
    dsimp only [lift]
    exact QuotientGroup.lift_mk' (RK c hV) hR k
  let e : ↥(K c) ⧸ RK c hV ≃* KstarBar c hV :=
    (QuotientGroup.quotientMulEquivOfEq (psiK_ker c hV).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective (psiK c hV) (psiK_surjective c hV))
  exact ⟨lift.comp e.symm, hlift.comp e.symm.surjective⟩

theorem exists_surjective_KstarBar_range_of_RKbar_le_ker (c : Ctx23L D Ch)
    (hV : IsElemAbelian 2 c.V) {X : Type} [Group X] (π : ↥(Kbar c) →* X)
    (hπ : RKbar c hV ≤ π.ker) :
    ∃ f : KstarBar c hV →* ↥π.range, Function.Surjective f := by
  haveI : (RKbar c hV).Normal := RKbar_normal c hV
  obtain ⟨q, hq⟩ := exists_surjective_KstarBar_quotient c hV
  let p : (↥(Kbar c) ⧸ RKbar c hV) →* X :=
    QuotientGroup.lift (RKbar c hV) π hπ
  have hcomp : p.comp (QuotientGroup.mk' (RKbar c hV)) = π := by
    dsimp only [p]
    exact QuotientGroup.lift_comp_mk' (RKbar c hV) π hπ
  have hp : p.range = π.range := by
    rw [← hcomp, MonoidHom.range_comp,
      MonoidHom.range_eq_top.mpr (QuotientGroup.mk'_surjective _), Subgroup.map_top]
  let f : KstarBar c hV →* ↥π.range :=
    (p.comp q).codRestrict π.range fun w => by
      change p (q w) ∈ π.range
      rw [← hp]
      exact MonoidHom.mem_range.mpr ⟨q w, rfl⟩
  refine ⟨f, ?_⟩
  intro y
  have hy : (y : X) ∈ p.range := by
    rw [hp]
    exact y.2
  obtain ⟨z, hz⟩ := MonoidHom.mem_range.mp hy
  obtain ⟨w, hw⟩ := hq z
  refine ⟨w, ?_⟩
  apply Subtype.ext
  change p (q w) = (y : X)
  rw [hw]
  exact hz

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

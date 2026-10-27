module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsFiveRoot
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ParabolicTransfer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

theorem subgroupOf_map_subtype_eq {G : Type} [Group G] (L : Subgroup G) (C : Subgroup ↥L) :
    (C.map L.subtype).subgroupOf L = C := by
  apply Subgroup.map_subtype_inj.mp
  rw [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (Subgroup.map_subtype_le C)]

theorem map_inf_comap_map_subtype {G X : Type} [Group G] [Group X] (L : Subgroup G)
    (f : ↥L →* X) (A : Subgroup X) (B : Subgroup ↥L) :
    ((((A.comap f ⊓ B).map L.subtype).subgroupOf L).map f) = A ⊓ B.map f := by
  rw [subgroupOf_map_subtype_eq, inf_comm, Subgroup.map_inf_comap, inf_comm]

variable {G : Type} [Group G] [Finite G]

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

noncomputable def sylowL (c : Ctx23L D Ch) : Sylow 2 ↥c.L :=
  (isSylowIn_T_inf_L c).toSylow

@[simp] theorem sylowL_coe (c : Ctx23L D Ch) :
    (sylowL c : Subgroup ↥c.L) = D.T.subgroupOf c.L := by
  rw [sylowL, CFSG.Quasithin.IsSylowIn.coe_toSylow]
  ext x
  simp [Subgroup.mem_subgroupOf]

theorem isPGroup_T_subgroupOf (c : Ctx23L D Ch) :
    IsPGroup 2 (D.T.subgroupOf c.L) := by
  rw [← sylowL_coe c]
  exact (sylowL c).isPGroup'

noncomputable def Pstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V) (P : Subgroup G) :
    Subgroup ↥(c.H hV) :=
  (P.subgroupOf c.L).map (c.phiL hV)

theorem mem_Tstar_iff (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (t : MulAut (c.W hV)) :
    t ∈ c.Tstar hV ↔ ∃ y : ↥D.T, c.phiT hV y = t :=
  Iff.rfl

theorem isParabolicTwo_Pstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (P : Subgroup G) (hP : MinTInvParabolic D.T D.M c.L P) :
    IsParabolicTwo ↥(c.H hV) (Pstar c hV P) := by
  obtain ⟨-, hpar⟩ := parabolicOf_iff.mp hP.1.1
  exact hpar.map (c.phiL hV) (c.phiL_surjective hV)

theorem T_subgroupOf_le_P (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (P : Subgroup G) (hP : MinTInvParabolic D.T D.M c.L P) :
    D.T.subgroupOf c.L ≤ P.subgroupOf c.L := by
  obtain ⟨hPL, hpar⟩ := parabolicOf_iff.mp hP.1.1
  refine hpar.le_of_le_normalizer (isPGroup_T_subgroupOf c) ?_
  rw [← Subgroup.subgroupOf_normalizer_eq hPL]
  exact Subgroup.subgroupOf_mono c.L hP.1.2.1

theorem sylowStar_le_Pstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (P : Subgroup G) (hP : MinTInvParabolic D.T D.M c.L P) :
    (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤ Pstar c hV P := by
  rw [c.sylowStar_coe hV, Pstar]
  exact Subgroup.map_mono (T_subgroupOf_le_P c hV P hP)

theorem exists_conj_image_mem (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {Q : Subgroup ↥(c.H hV)} {t : MulAut (c.W hV)}
    (h : (Q.map (c.H hV).subtype).map (MulAut.conj t).toMonoidHom =
      Q.map (c.H hV).subtype)
    {q : ↥(c.H hV)} (hq : q ∈ Q) :
    ∃ q' ∈ Q, (q' : MulAut (c.W hV)) = MulAut.conj t (q : MulAut (c.W hV)) := by
  have hmem : MulAut.conj t (q : MulAut (c.W hV)) ∈ Q.map (c.H hV).subtype := by
    rw [← h]
    exact Subgroup.mem_map_of_mem (MulAut.conj t).toMonoidHom
      (Subgroup.mem_map_of_mem (c.H hV).subtype hq)
  obtain ⟨q', hq', heq⟩ := Subgroup.mem_map.1 hmem
  exact ⟨q', hq', heq⟩

theorem map_conj_eq_of_le_normalizer (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {Q : Subgroup ↥c.L}
    (hQ : D.T ≤ Subgroup.normalizer (Q.map c.L.subtype : Set G)) :
    ∀ t ∈ c.Tstar hV,
      ((Q.map (c.phiL hV)).map (c.H hV).subtype).map (MulAut.conj t).toMonoidHom =
        (Q.map (c.phiL hV)).map (c.H hV).subtype := by
  intro t ht
  obtain ⟨y, rfl⟩ := (c.mem_Tstar_iff hV t).1 ht
  ext h
  constructor
  · intro hh
    obtain ⟨r, hr, rfl⟩ := Subgroup.mem_map.1 hh
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hr
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hs
    have hnorm : (y : G) * (u : G) * (y : G)⁻¹ ∈ Q.map c.L.subtype :=
      (Subgroup.mem_normalizer_iff.mp (hQ y.2) (u : G)).1
        (Subgroup.mem_map_of_mem c.L.subtype hu)
    obtain ⟨u', hu', hu'eq⟩ := Subgroup.mem_map.1 hnorm
    have hsub : (⟨(y : G) * (u : G) * (y : G)⁻¹, c.conj_mem y u⟩ : ↥c.L) = u' :=
      Subtype.ext hu'eq.symm
    change MulAut.conj (c.phiT hV y) (c.phiL hV u : MulAut (c.W hV)) ∈
      (Q.map (c.phiL hV)).map (c.H hV).subtype
    rw [c.phiT_conj_phiL hV y u, hsub]
    exact Subgroup.mem_map_of_mem (c.H hV).subtype
      (Subgroup.mem_map_of_mem (c.phiL hV) hu')
  · intro hh
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.1 hh
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hs
    have hnorm : (y : G)⁻¹ * (u : G) * ((y : G)⁻¹)⁻¹ ∈ Q.map c.L.subtype :=
      (Subgroup.mem_normalizer_iff.mp (hQ (D.T.inv_mem y.2)) (u : G)).1
        (Subgroup.mem_map_of_mem c.L.subtype hu)
    obtain ⟨u', hu', hu'eq⟩ := Subgroup.mem_map.1 hnorm
    have hsub : (⟨(y : G)⁻¹ * (u : G) * ((y : G)⁻¹)⁻¹, c.conj_mem y⁻¹ u⟩ : ↥c.L) = u' :=
      Subtype.ext hu'eq.symm
    refine Subgroup.mem_map.mpr ⟨(c.H hV).subtype (c.phiL hV u'), ?_, ?_⟩
    · exact Subgroup.mem_map_of_mem (c.H hV).subtype
        (Subgroup.mem_map_of_mem (c.phiL hV) hu')
    · change MulAut.conj (c.phiT hV y) (c.phiL hV u' : MulAut (c.W hV)) =
        (c.phiL hV u : MulAut (c.W hV))
      have h1 : (c.phiL hV u' : MulAut (c.W hV)) =
          MulAut.conj (c.phiT hV y⁻¹) (c.phiL hV u : MulAut (c.W hV)) := by
        rw [← hsub]
        exact (c.phiT_conj_phiL hV y⁻¹ u).symm
      rw [h1, MulAut.conj_apply, MulAut.conj_apply, map_inv]
      group

theorem map_conj_Pstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (P : Subgroup G) (hP : MinTInvParabolic D.T D.M c.L P) :
    ∀ t ∈ c.Tstar hV,
      ((Pstar c hV P).map (c.H hV).subtype).map (MulAut.conj t).toMonoidHom =
        (Pstar c hV P).map (c.H hV).subtype := by
  have hQ : D.T ≤ Subgroup.normalizer ((P.subgroupOf c.L).map c.L.subtype : Set G) := by
    rw [Subgroup.map_subgroupOf_eq_of_le (parabolicOf_iff.mp hP.1.1).1]
    exact hP.1.2.1
  exact c.map_conj_eq_of_le_normalizer hV hQ

theorem not_le_stabilizer_fixedPoint (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (P : Subgroup G) (hP : MinTInvParabolic D.T D.M c.L P) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    ¬ Pstar c hV P ≤ MulAction.stabilizer ↥(c.H hV)
        ((fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) : Subgroup (c.W hV)) :
          Set (c.W hV)) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  intro hle
  have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
    c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA hnat h4 h1930
  have hle' : Pstar c hV P ≤
      MulAction.stabilizer ↥(c.H hV)
        (((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV))) := by
    simpa only [hℓ] using hle
  have hPM : P ≤ D.M := by
    intro x hxP
    have hxL : x ∈ c.L := (parabolicOf_iff.mp hP.1.1).1 hxP
    have hx' : (⟨x, hxL⟩ : ↥c.L) ∈ P.subgroupOf c.L := Subgroup.mem_subgroupOf.mpr hxP
    have hφ : c.phiL hV ⟨x, hxL⟩ ∈ Pstar c hV P :=
      Subgroup.mem_map.mpr ⟨⟨x, hxL⟩, hx', rfl⟩
    exact (c.phiL_mem_stabilizer_Ztil_iff hV h4 h1930 ⟨x, hxL⟩).1 (hle' hφ)
  exact hP.1.2.2 hPM

private theorem T_le_normalizer_map_inf (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    {Qstar : Subgroup ↥(c.H hV)} {P : Subgroup G}
    (hQinv : ∀ t ∈ c.Tstar hV,
      (Qstar.map (c.H hV).subtype).map (MulAut.conj t).toMonoidHom =
        Qstar.map (c.H hV).subtype)
    (hPT : D.T ≤ Subgroup.normalizer (P : Set G)) :
    D.T ≤ Subgroup.normalizer
      (((Qstar.comap (c.phiL hV) ⊓ P.subgroupOf c.L).map c.L.subtype : Subgroup G) : Set G) := by
  set Q : Subgroup G :=
    (Qstar.comap (c.phiL hV) ⊓ P.subgroupOf c.L).map c.L.subtype with hQ
  have hstep : ∀ {s : G}, s ∈ D.T → ∀ q ∈ Q, s * q * s⁻¹ ∈ Q := by
    intro s hs q hq
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
    obtain ⟨hxA, hxB⟩ := Subgroup.mem_inf.1 hx
    have hxQ : c.phiL hV x ∈ Qstar := Subgroup.mem_comap.1 hxA
    have hxP : (x : G) ∈ P := Subgroup.mem_subgroupOf.1 hxB
    have hconjx : s * (x : G) * s⁻¹ ∈ c.L := c.conj_mem ⟨s, hs⟩ x
    refine Subgroup.mem_map.mpr ⟨⟨s * (x : G) * s⁻¹, hconjx⟩, ?_, rfl⟩
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_comap]
      obtain ⟨q', hq', heq⟩ := c.exists_conj_image_mem hV
        (hQinv (c.phiT hV ⟨s, hs⟩) (MonoidHom.mem_range.mpr ⟨⟨s, hs⟩, rfl⟩)) hxQ
      have hphi : c.phiL hV ⟨s * (x : G) * s⁻¹, hconjx⟩ = q' :=
        Subtype.ext ((c.phiT_conj_phiL hV ⟨s, hs⟩ x).symm.trans heq.symm)
      rw [hphi]
      exact hq'
    · rw [Subgroup.mem_subgroupOf]
      exact (Subgroup.mem_normalizer_iff.mp (hPT hs) (x : G)).1 hxP
  intro t ht
  rw [Subgroup.mem_normalizer_iff]
  intro q
  constructor
  · exact hstep ht q
  · intro hq
    have h := hstep (D.T.inv_mem ht) (t * q * t⁻¹) hq
    rwa [show t⁻¹ * (t * q * t⁻¹) * (t⁻¹)⁻¹ = q from by group] at h

private theorem parabolicOf_map_inf_comap (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (P : Subgroup G) (hP : MinTInvParabolic D.T D.M c.L P)
    {Qstar : Subgroup ↥(c.H hV)}
    (hQpar : IsParabolicTwo ↥(c.H hV) Qstar)
    (hQsyl : (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤ Qstar) :
    ParabolicOf c.L ((Qstar.comap (c.phiL hV) ⊓ P.subgroupOf c.L).map c.L.subtype) := by
  refine parabolicOf_iff.mpr ⟨Subgroup.map_subtype_le _, ?_⟩
  rw [subgroupOf_map_subtype_eq]
  refine IsParabolicTwo.inf (hQpar.comap (c.phiL hV) (c.phiL_surjective hV))
    (parabolicOf_iff.mp hP.1.1).2 (sylowL c) ?_ ?_
  · rw [sylowL_coe]
    intro x hx
    rw [Subgroup.mem_comap]
    exact hQsyl (by rw [c.sylowStar_coe hV]; exact Subgroup.mem_map_of_mem _ hx)
  · rw [sylowL_coe]
    exact T_subgroupOf_le_P c hV P hP

private theorem Pstar_le_of_good (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (P : Subgroup G) (hP : MinTInvParabolic D.T D.M c.L P)
    {Qstar : Subgroup ↥(c.H hV)}
    (hQpar : IsParabolicTwo ↥(c.H hV) Qstar)
    (hQsyl : (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤ Qstar)
    (hQinv : ∀ t ∈ c.Tstar hV,
      (Qstar.map (c.H hV).subtype).map (MulAut.conj t).toMonoidHom =
        Qstar.map (c.H hV).subtype)
    (hQle : Qstar ≤ Pstar c hV P) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) := MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    ¬ Qstar ≤ MulAction.stabilizer ↥(c.H hV)
        (((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV))) →
      Pstar c hV P ≤ Qstar := by
  intro hQnotPℓ
  let C : Subgroup ↥c.L := Qstar.comap (c.phiL hV) ⊓ P.subgroupOf c.L
  let Q : Subgroup G := C.map c.L.subtype
  have hmapQ : (Q.subgroupOf c.L).map (c.phiL hV) = Qstar ⊓ Pstar c hV P := by
    dsimp only [Q, C]
    rw [map_inf_comap_map_subtype]
    rfl
  have hQParabolic : ParabolicOf c.L Q :=
    parabolicOf_map_inf_comap c hV P hP hQpar hQsyl
  have hQnorm : D.T ≤ Subgroup.normalizer (Q : Set G) :=
    c.T_le_normalizer_map_inf hV hQinv hP.1.2.1
  have hQnotM : ¬ Q ≤ D.M := by
    intro hQM
    apply hQnotPℓ
    intro h hh
    have hh' : h ∈ (Q.subgroupOf c.L).map (c.phiL hV) := by
      rw [hmapQ]
      exact ⟨hh, hQle hh⟩
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hh'
    exact (c.phiL_mem_stabilizer_Ztil_iff hV h4 h1930 x).2
      (hQM (Subgroup.mem_subgroupOf.1 hx))
  have hQleP : Q ≤ P := by
    intro q hq
    obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.1 hq
    exact Subgroup.mem_subgroupOf.1 (Subgroup.mem_inf.1 hx).2
  have hPQ : P ≤ Q := hP.le_of_le ⟨hQParabolic, hQnorm, hQnotM⟩ hQleP
  have h1 : Pstar c hV P ≤ (Q.subgroupOf c.L).map (c.phiL hV) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono c.L hPQ)
  rw [hmapQ] at h1
  exact h1.trans inf_le_left

theorem minimal_good_Pstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (hA : KTab23a) (h4 : S23_4 D Ch) (h1930 : H1930 D)
    (hnat : IsNaturalClassicalModule (c.H hV) (CFSG.Open.pRank 2 D.Z))
    (P : Subgroup G) (hP : MinTInvParabolic D.T D.M c.L P) :
    letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (c.W hV) :=
      MulAction.compHom (c.W hV) (c.H hV).subtype
    letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
    letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
      MulDistribMulAction.compHom (c.W hV)
        ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
    let ℓ : Subgroup (c.W hV) := fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV)
    let Pℓ : Subgroup ↥(c.H hV) := MulAction.stabilizer ↥(c.H hV) (ℓ : Set (c.W hV))
    let Good : Subgroup ↥(c.H hV) → Prop := fun Pstar =>
      IsParabolicTwo ↥(c.H hV) Pstar ∧ (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤ Pstar ∧
      (∀ t ∈ c.Tstar hV,
        (Pstar.map (c.H hV).subtype).map (MulAut.conj t).toMonoidHom =
          Pstar.map (c.H hV).subtype) ∧
      ¬ Pstar ≤ Pℓ
    Minimal Good (Pstar c hV P) := by
  letI : MulDistribMulAction ↥(c.H hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (c.W hV) :=
    MulAction.compHom (c.W hV) (c.H hV).subtype
  letI : MulAction ↥(c.H hV) (Set (c.W hV)) := Set.mulActionSet
  letI : MulDistribMulAction ↥(c.sylowStar hV) (c.W hV) :=
    MulDistribMulAction.compHom (c.W hV)
      ((c.H hV).subtype.comp (c.sylowStar hV : Subgroup ↥(c.H hV)).subtype)
  let ℓ' : Subgroup (c.W hV) := fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV)
  let Pℓ' : Subgroup ↥(c.H hV) := MulAction.stabilizer ↥(c.H hV) (ℓ' : Set (c.W hV))
  let Good' : Subgroup ↥(c.H hV) → Prop := fun Q =>
    IsParabolicTwo ↥(c.H hV) Q ∧ (c.sylowStar hV : Subgroup ↥(c.H hV)) ≤ Q ∧
    (∀ t ∈ c.Tstar hV,
      (Q.map (c.H hV).subtype).map (MulAut.conj t).toMonoidHom =
        Q.map (c.H hV).subtype) ∧
    ¬ Q ≤ Pℓ'
  change Minimal Good' (Pstar c hV P)
  refine minimal_iff.mpr ⟨?_, ?_⟩
  · refine ⟨c.isParabolicTwo_Pstar hV P hP, c.sylowStar_le_Pstar hV P hP,
      c.map_conj_Pstar hV P hP, ?_⟩
    exact c.not_le_stabilizer_fixedPoint hV hA h4 h1930 hnat P hP
  · intro Qstar hQgood hQle
    obtain ⟨hQpar, hQsyl, hQinv, hQnotPℓ⟩ := hQgood
    have hℓ : fixedPointSubgroup ↥(c.sylowStar hV) (c.W hV) = c.Ztil hV :=
      c.fixedPointSubgroup_sylowStar_eq_Ztil hV hA hnat h4 h1930
    have hPℓ : Pℓ' = MulAction.stabilizer ↥(c.H hV)
        (((c.Ztil hV : Subgroup (c.W hV)) : Set (c.W hV))) := by
      show MulAction.stabilizer ↥(c.H hV) ((ℓ' : Subgroup (c.W hV)) : Set (c.W hV)) = _
      rw [show ℓ' = c.Ztil hV from hℓ]
    refine le_antisymm (Pstar_le_of_good c hV h4 h1930 P hP hQpar hQsyl hQinv hQle ?_) hQle
    intro h
    exact hQnotPℓ (by rwa [hPℓ])

theorem Hinf_Pstar (c : Ctx23L D Ch) (hV : IsElemAbelian 2 c.V)
    (P : Subgroup G) (hP : MinTInvParabolic D.T D.M c.L P) (hcL0 : c.L0 = Hinf P) :
    Hinf (Pstar c hV P) = (c.L0.subgroupOf c.L).map (c.phiL hV) := by
  have hPL : P ≤ c.L := (parabolicOf_iff.mp hP.1.1).1
  have hPsub : (P.subgroupOf c.L).map c.L.subtype = P :=
    Subgroup.map_subgroupOf_eq_of_le hPL
  have h1 : (Hinf (P.subgroupOf c.L)).map c.L.subtype = Hinf P := by
    rw [Hinf_map, hPsub]
  have h2 : Hinf (P.subgroupOf c.L) = c.L0.subgroupOf c.L := by
    apply Subgroup.map_subtype_inj.mp
    rw [h1, ← hcL0]
    exact (Subgroup.map_subgroupOf_eq_of_le c.hL0L).symm
  unfold Pstar
  rw [← Hinf_map (c.phiL hV) (P.subgroupOf c.L), h2]

end Ctx23L

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

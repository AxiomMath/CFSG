module

public import CFSG.Quasithin.Vol2.Ch4Sec1Lem415
public import CFSG.Quasithin.Vol2.Ch4Sec2Lem422
public import CFSG.Quasithin.Vol2.Ch4Sec4Rem442
public import CFSG.Quasithin.Vol2.Ch1Ten

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.A4
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T M L : Subgroup G}

omit [Finite G] in
theorem commutator_le_left_of_le_normalizer {A L : Subgroup G}
    (h : L ≤ Subgroup.normalizer (A : Set G)) : ⁅A, L⁆ ≤ A :=
  Subgroup.le_normalizer_iff_commutator_le_left.mp h

omit [Finite G] in
theorem commutator_le_right_of_le_normalizer {A L : Subgroup G}
    (h : A ≤ Subgroup.normalizer (L : Set G)) : ⁅A, L⁆ ≤ L :=
  Subgroup.le_normalizer_iff_commutator_le_right.mp h

omit [Finite G] in
theorem commutator_eq_commutator_commutator_of_perfect {A L : Subgroup G} (hL : ⁅L, L⁆ = L)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) (hLA : L ≤ Subgroup.normalizer (A : Set G)) :
    ⁅A, L⁆ = ⁅⁅A, L⁆, L⁆ := by
  set W := ⁅⁅A, L⁆, L⁆ with hW
  refine le_antisymm ?_
    (commutator_le_left_of_le_normalizer (Subgroup.normalizer_commutator_ge_right A L))
  have hAW : A ≤ Subgroup.normalizer (W : Set G) := fun a ha =>
    mem_normalizer_commutator
      (mem_normalizer_commutator (Subgroup.le_normalizer ha) (hAL ha)) (hAL ha)
  have hLW : L ≤ Subgroup.normalizer (W : Set G) := fun l hl =>
    mem_normalizer_commutator (mem_normalizer_commutator (hLA hl) (Subgroup.le_normalizer hl))
      (Subgroup.le_normalizer hl)
  have h1 : ⁅⁅L, A⁆, L⁆ ≤ W := by rw [Subgroup.commutator_comm L A]
  have h3 := three_subgroups_le (X := L) (Y := A) (Z := L) (N := W) hLW hAW hLW h1 le_rfl
  rw [hL, Subgroup.commutator_comm] at h3
  exact h3

namespace Hyp4_2_1

variable (h : Hyp4_2_1 G T M L)
include h

theorem pCoreOf_L_le_T (hn : M ≤ Subgroup.normalizer (L : Set G)) : pCoreOf 2 L ≤ T := by
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_le h.sylow le_sup_right
  refine le_of_normal_of_isSylowTwoOf hTsyl ((pCoreOf_le 2 L).trans le_sup_left) ?_
    (pCoreOf_isPGroup 2 L)
  refine Subgroup.normal_subgroupOf_of_le_normalizer ((_root_.sup_le Subgroup.le_normalizer
    (h.T_le.trans hn)).trans
    (normalizer_le_normalizer_pCoreOf 2 L))

theorem pCoreOf_sup_eq (hn : M ≤ Subgroup.normalizer (L : Set G)) :
    pCoreOf 2 (L ⊔ T) = T ⊓ centralizerSection M L (pCoreOf 2 L) := by
  set C := centralizerSection M L (pCoreOf 2 L) with hC
  have hTsyl : IsSylowTwoOf T (L ⊔ T) := isSylowTwoOf_of_le h.sylow le_sup_right
  have hLTM : L ⊔ T ≤ M := h.sup_le
  have hO2L : pCoreOf 2 L ≤ T ⊓ C :=
    le_inf (h.pCoreOf_L_le_T hn) (pCoreOf_le_centralizerSection h.L_le)
  apply le_antisymm
  · refine le_inf (pCoreOf_two_le_of_isSylowTwoOf hTsyl) ?_
    refine (le_centralizerSection_iff (pCoreOf_le 2 L)).mpr ⟨(pCoreOf_le 2 _).trans hLTM, ?_⟩
    have hc1 : ⁅L, pCoreOf 2 (L ⊔ T)⁆ ≤ L :=
      Subgroup.le_normalizer_iff_commutator_le_left.mp ((pCoreOf_le 2 _).trans (hLTM.trans hn))
    have hc2 : ⁅L, pCoreOf 2 (L ⊔ T)⁆ ≤ pCoreOf 2 (L ⊔ T) :=
      Subgroup.le_normalizer_iff_commutator_le_right.mp
        (le_sup_left.trans (le_normalizer_pCoreOf 2 _))
    refine (le_inf hc1 hc2).trans (le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right))
    exact fun l hl => mem_normalizer_inf (Subgroup.le_normalizer hl)
      (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl))
  · refine le_pCoreOf_of_le_normalizer 2 (inf_le_left.trans le_sup_right) (_root_.sup_le ?_ ?_)
      (h.sylow.1.to_le inf_le_left)
    · intro l hl
      refine A4.mem_normalizer_of_conj_mem fun x hx => ?_
      have hc : l * x * l⁻¹ * x⁻¹ ∈ pCoreOf 2 L := by
        have := (mem_centralizerSection.mp hx.2).2.2.2 l hl
        exact this
      have e : l * x * l⁻¹ = (l * x * l⁻¹ * x⁻¹) * x := by group
      rw [e]
      exact (T ⊓ C).mul_mem (hO2L hc) hx
    · intro t ht
      exact mem_normalizer_inf (Subgroup.le_normalizer ht)
        (le_normalizer_centralizerSection' hn (h.T_le ht))

theorem sup_le_normalizer_Rp (hn : M ≤ Subgroup.normalizer (L : Set G)) :
    L ⊔ T ≤ Subgroup.normalizer
      ((T ⊓ centralizerSection M L (pCoreOf 2 L) : Subgroup G) : Set G) := by
  rw [← h.pCoreOf_sup_eq hn]
  exact le_normalizer_pCoreOf 2 _

theorem V_le (hn : M ≤ Subgroup.normalizer (L : Set G)) :
    ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ ≤
      omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)) :=
  commutator_le_left_of_le_normalizer ((le_sup_left.trans (h.sup_le_normalizer_Rp hn)).trans
    (normalizer_le_normalizer_omegaOneCenterOf _))

theorem V_le_L (hn : M ≤ Subgroup.normalizer (L : Set G)) :
    ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ ≤ L :=
  commutator_le_right_of_le_normalizer ((omegaOneCenterOf_le _).trans
    (inf_le_left.trans (h.T_le.trans hn)))

theorem V_eq_commutator (hn : M ≤ Subgroup.normalizer (L : Set G)) :
    ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ =
      ⁅⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆, L⁆ :=
  commutator_eq_commutator_commutator_of_perfect h.perfect
    ((omegaOneCenterOf_le _).trans (inf_le_left.trans (h.T_le.trans hn)))
    ((le_sup_left.trans (h.sup_le_normalizer_Rp hn)).trans
      (normalizer_le_normalizer_omegaOneCenterOf _))

omit h in
theorem twoReducedJoin_le_omegaOneCenterOf (H : Subgroup G) :
    twoReducedJoin H ≤ omegaOneCenterOf (pCoreOf 2 H) := by
  have hV := A4.isTwoReducedIn_twoReducedJoin H
  intro v hv
  refine mem_omegaOneCenterOf (A4.le_pCoreOf_of_isTwoReducedIn hV hv) (fun y hy => ?_)
    (hV.2.2.1.2 v hv)
  exact (Subgroup.mem_centralizer_iff.mp (A4.pCoreOf_le_centralizer_of_isTwoReducedIn hV hy) v
    hv).symm

theorem V_ne_bot (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h39 : A39ForSQTK)
    (hn : M ≤ Subgroup.normalizer (L : Set G)) :
    ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ ≠ ⊥ := by
  have hT := lemma_1_2_10_of_maximal h.qtke h.simple h.nonabelian h36 h37 h39 h.sylow h.maximal
    (H := L ⊔ T) ⟨le_rfl, h.maximal.1.2.2.2⟩
  have h3 : ⁅twoReducedJoin (L ⊔ T), L⁆ ≠ ⊥ := (hT.out 1 3).mp h.faithful
  intro h0
  apply h3
  refine le_bot_iff.mp (h0 ▸ Subgroup.commutator_mono ?_ le_rfl)
  rw [← h.pCoreOf_sup_eq hn]
  exact twoReducedJoin_le_omegaOneCenterOf _

end Hyp4_2_1

structure Hyp4_2_3N (G : Type) [Group G] [Finite G] (T M L Mm I : Subgroup G) : Prop
    extends Hyp4_2_1 G T M L where
  normal : M ≤ Subgroup.normalizer (L : Set G)
  sigma : IsSigma M L Mm
  gammaStar : IsGammaStar M L Mm I
  R_le : pCoreOf 2 I ≤ T ⊓ centralizerSection M L (pCoreOf 2 L)
  L_le_I : L ≤ I

namespace Hyp4_2_3N

variable {Mm I : Subgroup G} (h : Hyp4_2_3N G T M L Mm I)
include h

theorem hyp4_1_1 (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK) :
    Hyp4_1_1 G T M L := by
  have := lemma_4_2_2 h37 h38 h39 h.toHyp4_2_1
  rwa [conjClosure_eq_self (h.T_le.trans h.normal)] at this

theorem isSylowTwoOf_Rp :
    IsSylowTwoOf (T ⊓ centralizerSection M L (pCoreOf 2 L))
      (centralizerSection M L (pCoreOf 2 L)) := by
  have hT : IsSylowTwoOf T (M ⊓ Subgroup.normalizer (L : Set G)) := by
    rw [inf_eq_left.mpr h.normal]
    exact isSylowTwoOf_of_le h.sylow h.T_le
  exact isSylowTwoOf_inf_centralizerSection hT

end Hyp4_2_3N

omit [Finite G] in
theorem isElemAbelian_of_le_omegaOneCenterOf {V X : Subgroup G} (hV : V ≤ omegaOneCenterOf X) :
    IsElemAbelian 2 V := by
  refine ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => sq_eq_one_of_mem_omegaOneCenterOf (hV hx)⟩
  exact (mem_centralizer_of_mem_omegaOneCenterOf (hV a.2) ((omegaOneCenterOf_le X) (hV b.2))).symm

omit [Finite G] in
theorem normalizer_le_CGS {C S : Subgroup G} (hCS : C ≤ S) (hC : C ≠ ⊥)
    (hch : (C.subgroupOf S).Characteristic) : Subgroup.normalizer (C : Set G) ≤ CGS S :=
  le_iSup_of_le C (le_iSup_of_le hCS (le_iSup_of_le hC (le_iSup_of_le hch le_rfl)))

omit [Finite G] in
theorem cgsIn_le_inf_of_CGS_le {H R M : Subgroup G} (h : CGS R ≤ M) : cgsIn H R ≤ H ⊓ M :=
  iSup_le fun _ => iSup_le fun hCR => iSup_le fun hC => iSup_le fun hch =>
    le_inf inf_le_left (inf_le_right.trans ((normalizer_le_CGS hCR hC hch).trans h))

namespace Hyp4_2_3N

variable {Mm I : Subgroup G} (h : Hyp4_2_3N G T M L Mm I)
include h

theorem oTwoUpper_inf_eq (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    {H : Subgroup G} (hIH : I ≤ H) : oTwoUpper (L ⊓ H) = L := by
  rw [inf_eq_left.mpr (h.L_le_I.trans hIH)]
  exact (h.hyp4_1_1 h37 h38 h39).oTwoUpper_eq

theorem pCoreOf_sup_le {H : Subgroup G}
    (hsyl : IsSylowTwoOf (pCoreOf 2 I) (centralizerSection (H ⊓ M) L (pCoreOf 2 L)))
    (hLH : L ≤ H) : pCoreOf 2 (L ⊔ pCoreOf 2 I) ≤ pCoreOf 2 I := by
  set R := pCoreOf 2 I with hR
  set P := pCoreOf 2 (L ⊔ R) with hP
  have hRHM : R ≤ H ⊓ M := hsyl.1.trans (centralizerSection_le_left _ _ _)
  have hLRHM : L ⊔ R ≤ H ⊓ M := _root_.sup_le (le_inf hLH h.L_le) hRHM
  have hPC : P ≤ centralizerSection (H ⊓ M) L (pCoreOf 2 L) := by
    refine (le_centralizerSection_iff (pCoreOf_le 2 L)).mpr ⟨(pCoreOf_le 2 _).trans hLRHM, ?_⟩
    have hc1 : ⁅L, P⁆ ≤ L := Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((pCoreOf_le 2 _).trans (hLRHM.trans (inf_le_right.trans h.normal)))
    have hc2 : ⁅L, P⁆ ≤ P := Subgroup.le_normalizer_iff_commutator_le_right.mp
      (le_sup_left.trans (le_normalizer_pCoreOf 2 _))
    refine (le_inf hc1 hc2).trans (le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((pCoreOf_isPGroup 2 _).to_le inf_le_right))
    exact fun l hl => mem_normalizer_inf (Subgroup.le_normalizer hl)
      (le_normalizer_pCoreOf 2 _ (Subgroup.mem_sup_left hl))
  have hPR2 : IsPGroup 2 ↥(P ⊔ R) :=
    IsPGroup.to_sup_of_normal_left' (pCoreOf_isPGroup 2 _) (pCoreOf_isPGroup 2 I)
      (le_sup_right.trans (le_normalizer_pCoreOf 2 _))
  have hle := (isSylowTwoOf_iff_maximal.mp hsyl).2.2 (P ⊔ R) (_root_.sup_le hPC hsyl.1) hPR2
    le_sup_right
  exact le_sup_left.trans hle

theorem lemma_4_2_4N (h36 : A36ForSQTK) (h37 : A37ForSQTK) (h38 : A38ForSQTK)
    (h39 : A39ForSQTK) {H : Subgroup G} (hH : InH I H) (hHM : ¬ H ≤ M) :
    HypC28 H (pCoreOf 2 I) (H ⊓ M) L
      ⁅omegaOneCenterOf (T ⊓ centralizerSection M L (pCoreOf 2 L)), L⁆ := by
  have h41 := h.hyp4_1_1 h37 h38 h39
  have hS := h.sigma
  have hI := h.gammaStar
  have hLH : L ≤ H := h.L_le_I.trans hH.1
  have hcc : conjClosure L (H ⊓ M) = L := conjClosure_eq_self (inf_le_right.trans h.normal)
  have hsyl : IsSylowTwoOf (pCoreOf 2 I) (centralizerSection (H ⊓ M) L (pCoreOf 2 L)) := by
    have := (lemma_4_1_4_four h41 hS hI hH hHM).2
    rwa [h.oTwoUpper_inf_eq h37 h38 h39 hH.1] at this
  have hRp := h.isSylowTwoOf_Rp
  have hVle := h.V_le h.normal
  have hVne := h.V_ne_bot h36 h37 h39 h.normal
  set Rp := T ⊓ centralizerSection M L (pCoreOf 2 L) with hRpdef
  set V := ⁅omegaOneCenterOf Rp, L⁆ with hVdef
  have hRRp : pCoreOf 2 I ≤ Rp := h.R_le
  have hRM : pCoreOf 2 I ≤ M := (pCoreOf_le 2 I).trans (hI.1.1.1.trans hS.1)
  have hRV : pCoreOf 2 I ≤ Subgroup.normalizer (V : Set G) := fun r hr =>
    mem_normalizer_commutator
      (normalizer_le_normalizer_omegaOneCenterOf Rp
        ((le_sup_right.trans (h.sup_le_normalizer_Rp h.normal)) ((inf_le_left : Rp ≤ T) (hRRp hr))))
      (h.normal (hRM hr))
  have hLV : L ≤ Subgroup.normalizer (V : Set G) := Subgroup.normalizer_commutator_ge_right _ _
  have hVLR : V ≤ pCoreOf 2 (L ⊔ pCoreOf 2 I) :=
    le_pCoreOf_of_le_normalizer 2 ((h.V_le_L h.normal).trans le_sup_left)
      (_root_.sup_le hLV hRV)
      (h.sylow.1.to_le (hVle.trans ((omegaOneCenterOf_le Rp).trans inf_le_left)))
  refine
    { sqtk := sqtkGroup_of_pCoreOf_ne_bot h.qtke h.simple h.nonabelian hH.2
      pgroup := pCoreOf_isPGroup 2 I
      le_M := hsyl.1.trans (centralizerSection_le_left _ _ _)
      le_H := inf_le_left
      charTwo := lemma_4_1_4_six h41 hS hI hH hHM
      pCore_ne := hH.2
      comp := cComp_mem_of_le (h.mem_cComp h37 h39) (le_inf hLH h.L_le) inf_le_right
      sylow := by rw [hcc]; exact hsyl
      cgs := cgsIn_le_inf_of_CGS_le (lemma_4_1_4_two h41 hS hI)
      V_le := by rw [hcc]; exact h.V_le_L h.normal
      V_ne := hVne
      V_elem := isElemAbelian_of_le_omegaOneCenterOf hVle
      V_comm := by rw [hcc]; exact (h.V_eq_commutator h.normal).symm
      V_center := ?_
      V_norm := le_inf inf_le_left (inf_le_right.trans
        (lemma_4_1_5_two h41 hRp hVne hVle rfl)) }
  rw [hcc]
  refine le_inf hVLR ?_
  exact le_centralizer_of_le_omegaOneCenterOf hVle ((h.pCoreOf_sup_le hsyl hLH).trans hRRp)

end Hyp4_2_3N

end CFSG.Quasithin.H13.Ch4

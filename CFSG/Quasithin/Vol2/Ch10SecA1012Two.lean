module

public import CFSG.Quasithin.Vol2.Ch10SecA1012SixHyp
public import CFSG.Quasithin.Background.B2Factorization
public import CFSG.Quasithin.Background.InternalSecISec
public import CFSG.Quasithin.Background.B2FactorizationResidual
public import CFSG.Quasithin.Vol2.Ch10SecA1011A

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

variable {G : Type} [Group G] [Finite G] {T L I : Subgroup G}

theorem fsuUL_ne_conjugate (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) {t : G} (ht : t ∈ T) (htn : t ∉ Subgroup.normalizer (L : Set G)) :
    fsuUL T L I ≠ CFSG.conjugate (fsuUL T L I) t := by
  intro heq
  obtain ⟨_, -, -, ha, -⟩ := hyp.three
  obtain ⟨hsup, -, hUt⟩ := ha t ht htn
  have hconj : CFSG.conjugate (fsuUL T L I) t = ⁅fsuVM T L I, CFSG.conjugate L t⁆ :=
    conjugate_commutator_fsuVM (le_fsuM T L ht)
  have hUL : fsuUL T L I ≤ Subgroup.centralizer (L : Set G) := by
    rw [heq, hconj]
    exact commutator_conjugate_le_centralizer h37 h38 hyp ht htn
  have hU0 : fsuUL T L I ≤ fsuCVM T L I := by
    refine le_inf (Subgroup.le_normalizer_iff_commutator_le_left.mp
      ((le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I))) ?_
    rw [fsuL0_eq_sup h37 h38 hyp ht htn, Subgroup.le_centralizer_iff]
    exact sup_le (Subgroup.le_centralizer_iff.mp hUL) (Subgroup.le_centralizer_iff.mp hUt)
  have hV : fsuVM T L I ≤ fsuCVM T L I := by
    rw [← hsup, ← heq]
    exact sup_le (sup_le hU0 hU0) le_rfl
  apply commutator_fsuVM_ne_bot hyp.fsu
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro v hv
  exact Subgroup.centralizer_le (le_fsuL0 T L) ((hV hv).2)

theorem inf_centralizer_le_T1 (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (hyp : Ch10.Hyp10 G T L I) :
    T ⊓ Subgroup.centralizer (fsuVM T L I : Set G) ≤ T1 T L := by
  intro c hc
  refine ⟨hc.1, ?_⟩
  by_contra hcn
  have hU : CFSG.conjugate (fsuUL T L I) c = fsuUL T L I := by
    rw [conjugate_eq_self_iff]
    have hcU : c ∈ Subgroup.centralizer (fsuUL T L I : Set G) :=
      Subgroup.centralizer_le
        (Subgroup.le_normalizer_iff_commutator_le_left.mp
          ((le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I))) hc.2
    rw [Subgroup.mem_normalizer_iff]
    intro u
    constructor
    · intro hu
      rw [← Subgroup.mem_centralizer_iff.mp hcU u hu, mul_inv_cancel_right]
      exact hu
    · intro hu
      have h := Subgroup.mem_centralizer_iff.mp hcU _ hu
      have e : u = c * u * c⁻¹ := by
        calc u = c⁻¹ * (c * u * c⁻¹ * c) := by group
          _ = c⁻¹ * (c * (c * u * c⁻¹)) := by rw [h]
          _ = c * u * c⁻¹ := by group
      rw [e]
      exact hu
  exact fsuUL_ne_conjugate h37 h38 hyp hc.1 hcn hU.symm

theorem pCoreOf_le_centralizer_fsuVM (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) :
    pCoreOf 2 L ≤ Subgroup.centralizer (fsuVM T L I : Set G) := by
  obtain ⟨hVM, hR⟩ := h322 G T L I hyp.fsu
  exact InternalSec.pCoreOf_le_centralizer_of_isPrimeReduced hVM hR
    (IsSubnormal.step (le_fsuL0 T L) (normal_fsuL0 hyp.fsu.maximal.1) (subnormal_fsuL0 T L))

theorem inf_centralizer_eq_pCoreOf (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) :
    L ⊓ Subgroup.centralizer (fsuVM T L I : Set G) = pCoreOf 2 L := by
  refine le_antisymm (fun x hx => ?_)
    (le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 L) (pCoreOf_le_centralizer_fsuVM h322 hyp))
  rw [← inf_pCoreOf_fsuL0 hyp.fsu.maximal.1]
  exact ⟨hx.1, fsuL0_inf_centralizer_le h37 h38 hyp ⟨le_fsuL0 T L hx.1, hx.2⟩⟩

@[expose] noncomputable def autOnEquivQuot
    (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) :
    ↥(autOn L (fsuVM T L I)) ≃* ↥L ⧸ CFSG.pCore 2 ↥L :=
  let hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  let ψ : ↥L →* ↥(autOn L (fsuVM T L I)) :=
    ((conjAct (fsuVM T L I)).comp (Subgroup.inclusion hLV)).codRestrict _
      fun l => ⟨Subgroup.inclusion hLV l, l.2, rfl⟩
  have hψs : Function.Surjective ψ := by
    rintro ⟨y, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hker : ψ.ker = CFSG.pCore 2 ↥L := by
    rw [← subgroupOf_pCoreOf, ← inf_centralizer_eq_pCoreOf h37 h38 h322 hyp]
    ext l
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro h
      exact ⟨l.2, A4.conjAct_eq_one_iff.mp (congrArg Subtype.val h)⟩
    · intro h
      exact Subtype.ext (A4.conjAct_eq_one_iff.mpr h.2)
  (QuotientGroup.quotientKerEquivOfSurjective ψ hψs).symm.trans
    (QuotientGroup.quotientMulEquivOfEq hker)

omit [Finite G] in
theorem exists_ne_of_isQuasisimple {Q : Type} [Group Q] (hq : CFSG.IsQuasisimple Q) :
    ∃ a b : Q, a * b ≠ b * a := by
  obtain ⟨a, b, hab⟩ := hq.2.2
  obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
  obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
  refine ⟨a, b, fun h => hab ?_⟩
  rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, h]

theorem isSimpleGroup_autOn
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) :
    IsSimpleGroup ↥(autOn L (fsuVM T L I)) ∧ ∃ a b : ↥(autOn L (fsuVM T L I)), a * b ≠ b * a := by
  have hs := isSimpleGroup_of_not_normal h37 h38 hyp.fsu.simple hyp.fsu.nonabelian hyp.fsu.qtke
    hyp.fsu.faithful hyp.not_normal
  set e := autOnEquivQuot h37 h38 h322 hyp
  refine ⟨e.isSimpleGroup, ?_⟩
  obtain ⟨a, b, hab⟩ := exists_ne_of_isQuasisimple hyp.fsu.quasisimple
  refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
  simpa using congrArg e h

theorem isComponentOf_autOn
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (hyp : Ch10.Hyp10 G T L I) :
    IsComponentOf (autOn L (fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I)) := by
  obtain ⟨hs, hnc⟩ := isSimpleGroup_autOn h37 h38 h322 hyp
  exact ⟨A4.autOn_mono ((le_fsuL0 T L).trans le_sup_left),
    A4.autOn_subnormal (isSubnormal_sup (le_fsuL0 T L) (normal_fsuL0 hyp.fsu.maximal.1)),
    isQuasisimple_of_simple hnc⟩

theorem thompsonJ_le_T1
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h322 : TmpL6_3_2_2_two) (h154 : AsB15Part4) (hyp : Ch10.Hyp10 G T L I) :
    thompsonJ T ≤ T1 T L := by
  obtain ⟨t, ht, htn⟩ : ∃ t ∈ T, t ∉ Subgroup.normalizer (L : Set G) := by
    by_contra hne
    push Not at hne
    exact hyp.not_normal hne
  have hel : IsElemAbelian 2 (fsuVM T L I) := isElemAbelian_fsuVM hyp
  have := hel.1
  have hVH : fsuVM T L I ≤ fsuL0 T L ⊔ T := (fsuVM_le_T hyp).trans le_sup_right
  have hHN : fsuL0 T L ⊔ T ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    sup_le (fsuL0_le_normalizer_fsuVM T L I) (le_normalizer_fsuVM T L I)
  have hTH : IsSylowTwoOf T (fsuL0 T L ⊔ T) :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow le_sup_right
  have hLV : L ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (le_fsuL0 T L).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hLtV : CFSG.conjugate L t ≤ Subgroup.normalizer (fsuVM T L I : Set G) :=
    (conjugate_le_fsuL0 ht).trans (fsuL0_le_normalizer_fsuVM T L I)
  have hcomp : IsComponentOf (autI hel L) (autI hel (fsuL0 T L ⊔ T)) :=
    isComponentOf_autOn h37 h38 h322 hyp
  refine iSup₂_le fun A hA => ?_
  by_cases hAV : A ≤ Subgroup.centralizer (fsuVM T L I : Set G)
  · exact (le_inf hA.1 hAV).trans (inf_centralizer_le_T1 h37 h38 hyp)
  have hoff : IsFFStarOffender (autI hel (fsuL0 T L ⊔ T)) (autI hel A) :=
    offenderImages_isFFStarOffender hel hVH hHN
      ⟨A, ⟨isMaxElemAbelian_of_isSylowTwoOf hTH hA, hAV⟩, rfl⟩
  have hN := h154 (IntMod (fsuVM T L I) hel) (fun v => IntMod.sq_eq_one v) _ _ hoff _ hcomp
  intro a haA
  have haT : a ∈ T := hA.1 haA
  refine ⟨haT, ?_⟩
  by_contra han
  have haV : a ∈ Subgroup.normalizer (fsuVM T L I : Set G) := le_normalizer_fsuVM T L I haT
  have h0 : (conjAct (fsuVM T L I) ⟨a, haV⟩)⁻¹ ∈
      Subgroup.normalizer (autOn L (fsuVM T L I) : Set (MulAut ↥(fsuVM T L I))) :=
    (Subgroup.normalizer _).inv_mem (hN (convI_mem_autI hel haA haV))
  have h1 : autOn (CFSG.conjugate L a) (fsuVM T L I) = autOn L (fsuVM T L I) := by
    rw [autOn_conjugate haV]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mp h0
  rw [conjugate_eq_of_not_mem h37 h38 hyp ht htn haT han] at h1
  have h2 := congrArg commV h1
  rw [commV_autOn_eq hLtV, commV_autOn_eq hLV,
    ← conjugate_commutator_fsuVM (le_fsuM T L ht)] at h2
  apply fsuUL_ne_conjugate h37 h38 hyp ht htn
  have hUV : fsuUL T L I ≤ fsuVM T L I :=
    Subgroup.le_normalizer_iff_commutator_le_left.mp hLV
  have hUtV : CFSG.conjugate (fsuUL T L I) t ≤ fsuVM T L I := by
    have h := conjugate_mono hUV t
    rwa [conjugate_fsuVM (le_fsuM T L ht)] at h
  have h2' : (CFSG.conjugate (fsuUL T L I) t).subgroupOf (fsuVM T L I) =
      (fsuUL T L I).subgroupOf (fsuVM T L I) := h2
  rw [← Subgroup.map_subgroupOf_eq_of_le hUtV, h2', Subgroup.map_subgroupOf_eq_of_le hUV]

end CFSG.Quasithin.Vol2.Ch10.SecA

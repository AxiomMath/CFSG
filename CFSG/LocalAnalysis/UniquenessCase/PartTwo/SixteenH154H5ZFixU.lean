module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZWorld
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZFixQ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5ZFull
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154H5SumSecA
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsConj
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrCountCA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKSumConv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
public import CFSG.Monster.B.TwoA.Base.ElemAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

private theorem s16h_mem_stabSub_of_map_eq {W : Type} [CommGroup W] {Z : Subgroup W}
    {g : MulAut W} (hg : Z.map g.toMonoidHom = Z) : g ∈ stabSub Z := by
  intro u
  constructor
  · intro hu
    have h : g u ∈ Z.map g.toMonoidHom := by rwa [hg]
    obtain ⟨v, hv, hvu⟩ := Subgroup.mem_map.mp h
    have hvu' : v = u := g.injective hvu
    rwa [hvu'] at hv
  · intro hu
    have h : g u ∈ Z.map g.toMonoidHom := Subgroup.mem_map.mpr ⟨u, hu, rfl⟩
    rwa [hg] at h

private theorem s16h_secHom_subgroup {W : Type} [CommGroup W] {L N : Subgroup (MulAut W)}
    {Z I : Subgroup W} (hLN : L ≤ N) (hNU : N ≤ stabSub I) (hNZ : N ≤ stabSub Z)
    (hLU : L ≤ stabSub I) (hLZ : L ≤ stabSub Z) (a : ↥L) :
    CFSG.Quasithin.B5.secHom L hLU hLZ a =
      CFSG.Quasithin.B5.secHom N hNU hNZ ⟨(a : MulAut W), hLN a.2⟩ := by
  refine MulEquiv.ext fun x => ?_
  induction x using QuotientGroup.induction_on with
  | H w =>
    rw [CFSG.Quasithin.B5.secHom_mk, CFSG.Quasithin.B5.secHom_mk]

theorem s16h_L3World_fix {U : Type} [CommGroup U] [Finite U] {N L : Subgroup (MulAut U)}
    (h : s16h_L3World N L) {x : MulAut U} (hx : x ∈ N)
    (hfix : ∀ J ∈ irrSet L, J.map x.toMonoidHom = J) : x ∈ L := by
  let Z : Subgroup U := fixV L
  let Q : Type := Sec (⊤ : Subgroup U) Z
  let Λ : Subgroup (MulAut Q) := autSec L (⊤ : Subgroup U) Z
  haveI : Finite Q := inferInstanceAs (Finite (Sec (⊤ : Subgroup U) Z))
  obtain ⟨k, hk, I, hZI, hind, hsup, hnat⟩ := h.sum
  have hshape : ∀ i, SumOfNatShape L (I i) Z 1 := fun i =>
    ⟨3, Or.inl ⟨h.sl3, s16t3_sumOfNat_singleton (hZI i) (hnat i)⟩⟩
  have hJmem : ∀ i, commSub (I i) L ∈ irrSet L := fun i =>
    (s16t3_commSub_mem_irrSet_of_natural h.quasi (hZI i) (hshape i)).1
  have hJsup : ∀ i, commSub (I i) L ⊔ Z = I i := fun i =>
    (s16t3_commSub_mem_irrSet_of_natural h.quasi (hZI i) (hshape i)).2.2
  have hIirr : ∀ i, IsIrrOn L (I i) Z := fun i =>
    SumOfNatShape.isIrrOn h.quasi (hshape i)
  have hLI : ∀ i, L ≤ stabSub (I i) := fun i =>
    s16h_le_stabSub_of_stable (hIirr i).2.1
  have htopStab : L ≤ stabSub (⊤ : Subgroup U) := fun _ _ u => by simp
  have hNtopStab : N ≤ stabSub (⊤ : Subgroup U) := fun _ _ u => by simp
  have hLZ : L ≤ stabSub Z := by
    intro a ha u
    constructor
    · intro hu
      refine mem_fixV.mpr fun l hl => ?_
      have hw := (mem_fixV.mp hu) (a * l * a⁻¹) (L.mul_mem (L.mul_mem ha hl) (L.inv_mem ha))
      calc l u = a⁻¹ ((a * l * a⁻¹) (a u)) := by simp [MulAut.mul_apply]
        _ = a⁻¹ (a u) := by rw [hw]
        _ = u := by simp
    · intro hu
      refine mem_fixV.mpr fun l hl => ?_
      have h1 := (mem_fixV.mp hu) (a⁻¹ * l * a) (L.mul_mem (L.mul_mem (L.inv_mem ha) hl) ha)
      calc l (a u) = a ((a⁻¹ * l * a) u) := by simp [MulAut.mul_apply]
        _ = a u := by rw [h1]
  have hxnorm : ∀ y : MulAut U, y ∈ L ↔ x * y * x⁻¹ ∈ L :=
    Subgroup.mem_normalizer_iff.mp (h.normal hx)
  have hg : ∀ y ∈ L, x * y * x⁻¹ ∈ L := fun y hy => (hxnorm y).mp hy
  have hg' : ∀ y ∈ L, x⁻¹ * y * x ∈ L := by
    intro y hy
    have hxy : x * (x⁻¹ * y * x) * x⁻¹ = y := by group
    exact (hxnorm (x⁻¹ * y * x)).mpr (by rw [hxy]; exact hy)
  have hZmap : Z.map x.toMonoidHom = Z :=
    CFSG.LocalAnalysis.WeakClosure81.map_fixV_of_normalizes hg hg'
  have hNZ : N ≤ stabSub Z := fun a ha => s16h_mem_stabSub_of_map_eq (by
    have haNnorm : ∀ y : MulAut U, y ∈ L ↔ a * y * a⁻¹ ∈ L :=
      Subgroup.mem_normalizer_iff.mp (h.normal ha)
    have hga : ∀ y ∈ L, a * y * a⁻¹ ∈ L := fun y hy => (haNnorm y).mp hy
    have hga' : ∀ y ∈ L, a⁻¹ * y * a ∈ L := by
      intro y hy
      have hxy : a * (a⁻¹ * y * a) * a⁻¹ = y := by group
      exact (haNnorm (a⁻¹ * y * a)).mpr (by rw [hxy]; exact hy)
    exact CFSG.LocalAnalysis.WeakClosure81.map_fixV_of_normalizes hga hga')
  have hfaithTop : L ⊓ centSec (⊤ : Subgroup U) Z = ⊥ := by
    apply le_bot_iff.1
    intro a ha
    rw [Subgroup.mem_inf] at ha
    rw [Subgroup.mem_bot]
    exact h.faithful a (h.le ha.1) (fun u => (mem_centSec.mp ha.2).2 u trivial)
  have hL3 : IsL3 ↥L 1 := s16k_isLn_of_isSLn (by norm_num) h.sl3
  have hcenterL : Subgroup.center ↥L = ⊥ := center_eq_bot_of_isL3 hL3
  let eL : ↥L ≃* ↥Λ := B5.secEquiv L htopStab hLZ hfaithTop
  have hcenterΛ : Subgroup.center ↥Λ = ⊥ := by
    apply le_bot_iff.1
    intro g hg
    rw [Subgroup.mem_bot]
    have hsym : eL.symm g ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      apply eL.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
      exact Subgroup.mem_center_iff.mp hg (eL l)
    have hg1 : eL.symm g = 1 := by
      have hmem := hsym
      rw [hcenterL, Subgroup.mem_bot] at hmem
      exact hmem
    calc g = eL (eL.symm g) := (MulEquiv.apply_symm_apply eL g).symm
      _ = eL 1 := by rw [hg1]
      _ = 1 := map_one eL
  let Ī : Fin k → Subgroup Q := fun i =>
    ((I i).subgroupOf (⊤ : Subgroup U)).map
      (QuotientGroup.mk' (Z.subgroupOf (⊤ : Subgroup U)))
  have hspan : (⨆ i, Ī i) = ⊤ := by
    have hsplit : (Z ⊔ ⨆ i, I i).subgroupOf (⊤ : Subgroup U) =
        Z.subgroupOf (⊤ : Subgroup U) ⊔
          (⨆ i, (I i).subgroupOf (⊤ : Subgroup U)) := by
      rw [Subgroup.subgroupOf_sup le_top le_top, s16h_subgroupOf_iSup (fun _ => le_top)]
    have hZbot : (Z.subgroupOf (⊤ : Subgroup U)).map
        (QuotientGroup.mk' (Z.subgroupOf (⊤ : Subgroup U))) = ⊥ :=
      (Subgroup.map_eq_bot_iff (Z.subgroupOf (⊤ : Subgroup U))).2
        (le_of_eq (QuotientGroup.ker_mk' (Z.subgroupOf (⊤ : Subgroup U))).symm)
    have hmaps : (⨆ i, Ī i) =
        (Z.subgroupOf (⊤ : Subgroup U) ⊔
          ⨆ i, (I i).subgroupOf (⊤ : Subgroup U)).map
            (QuotientGroup.mk' (Z.subgroupOf (⊤ : Subgroup U))) := by
      rw [Subgroup.map_sup, Subgroup.map_iSup, hZbot, bot_sup_eq]
    rw [hmaps, ← hsplit, hsup, Subgroup.subgroupOf_self]
    rw [← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  have hstab : ∀ i, ∀ g ∈ Λ, ∀ y ∈ Ī i, g y ∈ Ī i := by
    intro i g hg y hy
    exact s16h_secIncl_image_stable (L := L) Z (I i) (⊤ : Subgroup U) le_top
      (hLI i) hLZ htopStab g hg y hy
  have hfull : ∀ i, ∀ φ : MulAut ↥(Ī i), ∃ g ∈ Λ, ∀ y : ↥(Ī i),
      g (y : Q) = (φ y : Q) := by
    intro i φ
    let es : Sec (I i) Z ≃* ↥(Ī i) :=
      (MonoidHom.ofInjective
        (s16h_secIncl_injective Z (I i) (⊤ : Subgroup U) le_top)).trans
        (MulEquiv.subgroupCongr (s16h_secIncl_range Z (I i) (⊤ : Subgroup U) le_top))
    have hes : ∀ z : ↥(Ī i),
        s16h_secIncl Z (I i) (⊤ : Subgroup U) le_top (es.symm z) = (z : Q) := by
      intro z
      rw [show es.symm z =
          (MonoidHom.ofInjective
            (s16h_secIncl_injective Z (I i) (⊤ : Subgroup U) le_top)).symm
            ((MulEquiv.subgroupCongr
              (s16h_secIncl_range Z (I i) (⊤ : Subgroup U) le_top)).symm z) from rfl,
        MonoidHom.apply_ofInjective_symm]
      exact MulEquiv.subgroupCongr_symm_apply _ _
    let φ' : MulAut (Sec (I i) Z) := (es.trans φ).trans es.symm
    have hφ'apply : ∀ z, φ' z = es.symm (φ (es z)) := fun _ => rfl
    have hφ'mem : φ' ∈ autSec L (I i) Z := by
      rw [s16h_binarySL3_autSec_eq_top (hnat i)]
      exact Subgroup.mem_top φ'
    obtain ⟨a, ha⟩ := (s16h_mem_autSec_range (hLI i) hLZ).mp hφ'mem
    refine ⟨B5.secHom L htopStab hLZ a,
      (s16h_mem_autSec_range htopStab hLZ).mpr ⟨a, rfl⟩, ?_⟩
    intro y
    calc B5.secHom L htopStab hLZ a (y : Q)
        = B5.secHom L htopStab hLZ a
            (s16h_secIncl Z (I i) (⊤ : Subgroup U) le_top (es.symm y)) := by rw [hes y]
      _ = s16h_secIncl Z (I i) (⊤ : Subgroup U) le_top
            (B5.secHom L (hLI i) hLZ a (es.symm y)) :=
            (s16h_secIncl_secHom Z (I i) (⊤ : Subgroup U) le_top
              (hLI i) hLZ htopStab a (es.symm y)).symm
      _ = s16h_secIncl Z (I i) (⊤ : Subgroup U) le_top (φ' (es.symm y)) := by rw [ha]
      _ = s16h_secIncl Z (I i) (⊤ : Subgroup U) le_top (es.symm (φ y)) := by
            rw [hφ'apply, MulEquiv.apply_symm_apply]
      _ = (φ y : Q) := hes (φ y)
  have hfaith : ∀ i, ∀ g ∈ Λ, (∀ y ∈ Ī i, g y = y) → g = 1 := by
    intro i g hg hgi
    obtain ⟨a, rfl⟩ := (s16h_mem_autSec_range htopStab hLZ).mp hg
    have ha1 : B5.secHom L (hLI i) hLZ a = 1 := by
      refine MulEquiv.ext fun z => ?_
      show B5.secHom L (hLI i) hLZ a z = z
      apply s16h_secIncl_injective Z (I i) (⊤ : Subgroup U) le_top
      have hz : s16h_secIncl Z (I i) (⊤ : Subgroup U) le_top z ∈ Ī i := by
        rw [show (Ī i : Subgroup Q) =
            (s16h_secIncl Z (I i) (⊤ : Subgroup U) le_top).range
            from (s16h_secIncl_range Z (I i) (⊤ : Subgroup U) le_top).symm]
        exact MonoidHom.mem_range.mpr ⟨z, rfl⟩
      have h2 := hgi (s16h_secIncl Z (I i) (⊤ : Subgroup U) le_top z) hz
      rw [← s16h_secIncl_secHom Z (I i) (⊤ : Subgroup U) le_top
        (hLI i) hLZ htopStab a z] at h2
      exact h2
    have hacent : (a : MulAut U) ∈ L ⊓ centSec (I i) Z :=
      ⟨a.2, (B5.mem_ker_secHom L (hLI i) hLZ a).mp (MonoidHom.mem_ker.mpr ha1)⟩
    have habot : (a : MulAut U) ∈ (⊥ : Subgroup (MulAut U)) := by
      rw [← s16h_binarySL3_faithful (hnat i)]
      exact hacent
    have haone : a = 1 := by
      have haU : (a : MulAut U) = 1 := by rwa [Subgroup.mem_bot] at habot
      exact Subtype.ext haU
    rw [haone, map_one]
  let xN : ↥N := ⟨x, hx⟩
  let xbar : MulAut Q := B5.secHom N hNtopStab hNZ xN
  have hIx : ∀ i, (I i).map x.toMonoidHom = I i := by
    intro i
    have hJfix : (commSub (I i) L).map x.toMonoidHom = commSub (I i) L :=
      hfix _ (hJmem i)
    calc (I i).map x.toMonoidHom
        = (commSub (I i) L ⊔ Z).map x.toMonoidHom :=
            congrArg (fun H : Subgroup U => H.map x.toMonoidHom) (hJsup i).symm
      _ = (commSub (I i) L).map x.toMonoidHom ⊔ Z.map x.toMonoidHom :=
            Subgroup.map_sup _ _ _
      _ = commSub (I i) L ⊔ Z := by rw [hJfix, hZmap]
      _ = I i := hJsup i
  have hxI : ∀ i, ∀ y ∈ Ī i, xbar y ∈ Ī i := by
    intro i y hy
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hy
    have huI : (u : U) ∈ I i := hu
    have hxuI : x (u : U) ∈ I i := by
      have hmm : x (u : U) ∈ (I i).map x.toMonoidHom :=
        Subgroup.mem_map.mpr ⟨(u : U), huI, rfl⟩
      rwa [hIx i] at hmm
    refine Subgroup.mem_map.mpr ⟨⟨x (u : U), Subgroup.mem_top _⟩, ?_, ?_⟩
    · exact Subgroup.mem_subgroupOf.mpr hxuI
    · show QuotientGroup.mk' (Z.subgroupOf (⊤ : Subgroup U)) ⟨x (u : U), _⟩ =
        B5.secHom N hNtopStab hNZ xN (QuotientGroup.mk u)
      rw [B5.secHom_mk]
      rfl
  have hxN : ∀ g ∈ Λ, xbar * g * xbar⁻¹ ∈ Λ := by
    intro g hg
    have hgmap : g ∈ (L.subgroupOf N).map (B5.secHom N hNtopStab hNZ) := by
      rw [B5.map_secHom_eq_autSec N hNtopStab hNZ h.le]
      exact hg
    obtain ⟨lN, hlN, rfl⟩ := Subgroup.mem_map.mp hgmap
    have hΛeq : Λ = (L.subgroupOf N).map (B5.secHom N hNtopStab hNZ) :=
      (B5.map_secHom_eq_autSec N hNtopStab hNZ h.le).symm
    rw [hΛeq]
    have hlL : (lN : MulAut U) ∈ L := Subgroup.mem_subgroupOf.mp hlN
    have hxconj : x * (lN : MulAut U) * x⁻¹ ∈ L := (hxnorm (lN : MulAut U)).mp hlL
    have hconj : xN * lN * xN⁻¹ ∈ L.subgroupOf N := by
      rw [Subgroup.mem_subgroupOf]
      simpa using hxconj
    refine Subgroup.mem_map.mpr ⟨xN * lN * xN⁻¹, hconj, ?_⟩
    simp only [map_mul, map_inv]
    rfl
  have hxbarΛ : xbar ∈ Λ :=
    s16h_normalizer_fix_summands hcenterΛ Ī hspan hstab hfull hfaith hxN hxI
  obtain ⟨l, hl⟩ := (s16h_mem_autSec_range htopStab hLZ).mp hxbarΛ
  have haN : x * (l : MulAut U)⁻¹ ∈ N := N.mul_mem hx (N.inv_mem (h.le l.2))
  have hatriv : ∀ u : U, (x * (l : MulAut U)⁻¹) u * u⁻¹ ∈ fixV L := by
    intro u
    have hker : B5.secHom N hNtopStab hNZ ⟨x * (l : MulAut U)⁻¹, haN⟩ = 1 := by
      have hsplit : (⟨x * (l : MulAut U)⁻¹, haN⟩ : ↥N) =
          xN * (⟨(l : MulAut U), h.le l.2⟩ : ↥N)⁻¹ := Subtype.ext rfl
      rw [hsplit, map_mul, map_inv,
        ← s16h_secHom_subgroup h.le hNtopStab hNZ htopStab hLZ l, hl]
      exact mul_inv_cancel xbar
    have hcent := (B5.mem_ker_secHom N hNtopStab hNZ
      ⟨x * (l : MulAut U)⁻¹, haN⟩).mp (MonoidHom.mem_ker.mpr hker)
    exact (mem_centSec.mp hcent).2 u trivial
  have hxone : x * (l : MulAut U)⁻¹ = 1 := h.faithful _ haN hatriv
  have hxl : x = (l : MulAut U) := mul_inv_eq_one.mp hxone
  rw [hxl]
  exact l.2

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

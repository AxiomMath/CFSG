module

public import CFSG.LocalAnalysis.StandardType.GGNsq2RankOne
public import CFSG.LocalAnalysis.StandardType.GGFixedTwoKernelTransport

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.ClassicalInvolution.Phan

namespace NsQuot

variable {G : Type} [Group G] [Finite G] {Q : Type} [Group Q]
variable {p : ℕ} {N : Subgroup G} {f : ↥N →* Q} {L Bs Z : Subgroup G}

theorem Datum.img_rankOneIn (hD : Datum p N f L Bs Z) {r : MulAut ↥Bs}
    (hfix : ∀ z ∈ Z, (∀ h ∈ ggHyperplane Bs r, h * z = z * h) → z = 1) :
    img N f (ggRankOneIn L Bs r) =
      ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau r) := by
  have hH : ggHyperplane Bs r ≤ Bs := Subgroup.map_subtype_le _
  rw [ggRankOneIn, ggRankOneIn, hD.hyperplane_img r, ← hD.centralizer_img hH]
  exact hD.img_ggOTwoPrime (inf_le_left.trans hD.LN) (hD.injOn_centralizer hfix)

theorem Datum.commute_lift (hD : Datum p N f L Bs Z) {r s : MulAut ↥Bs}
    (hfix : ∀ z ∈ Z, (∀ h ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs s, h * z = z * h) → z = 1)
    (hcomm : ∀ u ∈ ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau r),
      ∀ v ∈ ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau s), u * v = v * u) :
    ∀ a ∈ ggRankOneIn L Bs r, ∀ b ∈ ggRankOneIn L Bs s, a * b = b * a := by
  have hfixr : ∀ z ∈ Z, (∀ h ∈ ggHyperplane Bs r, h * z = z * h) → z = 1 :=
    fun z hz hc => hfix z hz fun h hh => hc h hh.1
  have hfixs : ∀ z ∈ Z, (∀ h ∈ ggHyperplane Bs s, h * z = z * h) → z = 1 :=
    fun z hz hc => hfix z hz fun h hh => hc h hh.2
  have hEr := hD.img_rankOneIn hfixr
  have hEs := hD.img_rankOneIn hfixs
  intro a ha b hb
  have haN : a ∈ N := hD.LN (ggOTwoPrime_le _ ha).1
  have hbN : b ∈ N := hD.LN (ggOTwoPrime_le _ hb).1
  have hfa : f ⟨a, haN⟩ ∈ ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau r) := by
    rw [← hEr]
    exact mem_img.2 ⟨⟨a, haN⟩, ha, rfl⟩
  have hfb : f ⟨b, hbN⟩ ∈ ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau s) := by
    rw [← hEs]
    exact mem_img.2 ⟨⟨b, hbN⟩, hb, rfl⟩
  have hker : (⟨a, haN⟩ : ↥N) * ⟨b, hbN⟩ * (⟨b, hbN⟩ * ⟨a, haN⟩)⁻¹ ∈ f.ker := by
    rw [MonoidHom.mem_ker]
    simp only [map_mul, map_inv]
    rw [hcomm _ hfa _ hfb]
    group
  let C : Subgroup G :=
    Subgroup.centralizer ((ggHyperplane Bs r ⊓ ggHyperplane Bs s : Subgroup G) : Set G)
  have hZ : a * b * (b * a)⁻¹ ∈ Z := by
    have h := (hD.mem_ker_iff _).1 hker
    simpa using h
  have hcC : a * b * (b * a)⁻¹ ∈ C := by
    have haC : a ∈ C :=
      Subgroup.centralizer_le (fun x hx => (Subgroup.mem_inf.mp hx).1) (ggOTwoPrime_le _ ha).2
    have hbC : b ∈ C :=
      Subgroup.centralizer_le (fun x hx => (Subgroup.mem_inf.mp hx).2) (ggOTwoPrime_le _ hb).2
    exact C.mul_mem (C.mul_mem haC hbC) (C.inv_mem (C.mul_mem hbC haC))
  have h1 : a * b * (b * a)⁻¹ = 1 :=
    hfix _ hZ fun h hh => Subgroup.mem_centralizer_iff.1 hcC h hh
  exact mul_inv_eq_one.mp h1

private def pairD_lft (L Bs : Subgroup G) (r s : MulAut ↥Bs) : Subgroup G :=
  L ⊓ Subgroup.centralizer ((ggHyperplane Bs r ⊓ ggHyperplane Bs s : Subgroup G) : Set G)

private noncomputable def pairIso_lft {D : Subgroup G}
    (hinj : Function.Injective (fun u : ↥(D.subgroupOf N) => f (u : ↥N))) :
    ↥(D.subgroupOf N) ≃* ↥(img N f D) :=
  MulEquiv.ofBijective
    ((f.comp (Subgroup.subtype (D.subgroupOf N))).codRestrict (img N f D)
      (fun u => mem_img.2 ⟨(u : ↥N), Subgroup.mem_subgroupOf.mp u.2, rfl⟩))
    ⟨fun a b hab => hinj (congrArg Subtype.val hab), fun q => by
      obtain ⟨u, hu, huq⟩ := mem_img.1 q.2
      exact ⟨⟨u, Subgroup.mem_subgroupOf.mpr hu⟩, Subtype.ext huq⟩⟩

private theorem img_subgroupOf_map_equiv_lft {D : Subgroup G} (hDN : D ≤ N)
    (e : ↥(D.subgroupOf N) ≃* ↥(img N f D))
    (he : ∀ u : ↥(D.subgroupOf N), ((e u : ↥(img N f D)) : Q) = f (u : ↥N))
    {S : Subgroup G} (hS : S ≤ D) :
    ((img N f S).subgroupOf (img N f D)).map
      (N.subtype.comp ((Subgroup.subtype (D.subgroupOf N)).comp e.symm.toMonoidHom)) = S := by
  ext x
  constructor
  · intro hx
    obtain ⟨y, hy, hyx⟩ := Subgroup.mem_map.mp hx
    obtain ⟨u, huS, huy⟩ := mem_img.1 (Subgroup.mem_subgroupOf.mp hy)
    have he_symm : f (((e.symm y) : ↥(D.subgroupOf N)) : ↥N) = (y : Q) := by
      calc f (((e.symm y) : ↥(D.subgroupOf N)) : ↥N)
          = ((e (e.symm y) : ↥(img N f D)) : Q) := (he (e.symm y)).symm
        _ = (y : Q) := by rw [MulEquiv.apply_symm_apply e y]
    have huy' : e.symm y =
        (⟨u, Subgroup.mem_subgroupOf.mpr (hS huS)⟩ : ↥(D.subgroupOf N)) := by
      apply e.injective
      apply Subtype.ext
      calc ((e (e.symm y) : ↥(img N f D)) : Q)
          = f (((e.symm y) : ↥(D.subgroupOf N)) : ↥N) := he (e.symm y)
        _ = (y : Q) := he_symm
        _ = f u := huy.symm
        _ = ((e ⟨u, Subgroup.mem_subgroupOf.mpr (hS huS)⟩ : ↥(img N f D)) : Q) :=
            (he ⟨u, Subgroup.mem_subgroupOf.mpr (hS huS)⟩).symm
    rw [← hyx]
    change (((e.symm y : ↥(D.subgroupOf N)) : ↥N) : G) ∈ S
    rw [huy']
    exact huS
  · intro hx
    have hxD : x ∈ D := hS hx
    have hxN : x ∈ N := hDN hxD
    let q : ↥(img N f D) := ⟨f ⟨x, hxN⟩, mem_img.2 ⟨⟨x, hxN⟩, hxD, rfl⟩⟩
    have hq : q ∈ (img N f S).subgroupOf (img N f D) :=
      Subgroup.mem_subgroupOf.mpr (mem_img.2 ⟨⟨x, hxN⟩, hx, rfl⟩)
    refine Subgroup.mem_map.mpr ⟨q, hq, ?_⟩
    have heq : e.symm q =
        (⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.mpr hxD⟩ : ↥(D.subgroupOf N)) := by
      apply e.injective
      rw [MulEquiv.apply_symm_apply e q]
      apply Subtype.ext
      rw [he (⟨⟨x, hxN⟩, Subgroup.mem_subgroupOf.mpr hxD⟩ : ↥(D.subgroupOf N))]
    change N.subtype (Subgroup.subtype (D.subgroupOf N) (e.symm q)) = x
    rw [heq]
    rfl

private theorem exists_pairMap_lft (hD : Datum p N f L Bs Z) {r s : MulAut ↥Bs}
    (hfix : ∀ z ∈ Z, (∀ h ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs s, h * z = z * h) → z = 1) :
    ∃ φ : ↥(img N f (pairD_lft L Bs r s)) →* G,
      Function.Injective φ ∧
      ((ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau r)).subgroupOf
        (img N f (pairD_lft L Bs r s))).map φ = ggRankOneIn L Bs r ∧
      ((ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau s)).subgroupOf
        (img N f (pairD_lft L Bs r s))).map φ = ggRankOneIn L Bs s := by
  have hDN : pairD_lft L Bs r s ≤ N := inf_le_left.trans hD.LN
  have hinj : Function.Injective
      (fun u : ↥((pairD_lft L Bs r s).subgroupOf N) => f (u : ↥N)) :=
    hD.injOn_centralizer (H := ggHyperplane Bs r ⊓ ggHyperplane Bs s) hfix
  let e : ↥((pairD_lft L Bs r s).subgroupOf N) ≃* ↥(img N f (pairD_lft L Bs r s)) :=
    pairIso_lft hinj
  have he : ∀ u : ↥((pairD_lft L Bs r s).subgroupOf N),
      ((e u : ↥(img N f (pairD_lft L Bs r s))) : Q) = f (u : ↥N) := fun _ => rfl
  let φ : ↥(img N f (pairD_lft L Bs r s)) →* G :=
    N.subtype.comp ((Subgroup.subtype ((pairD_lft L Bs r s).subgroupOf N)).comp
      e.symm.toMonoidHom)
  have hφ : Function.Injective φ := fun a b hab =>
    e.symm.injective (Subtype.ext (N.subtype_injective hab))
  have hfixr : ∀ z ∈ Z, (∀ h ∈ ggHyperplane Bs r, h * z = z * h) → z = 1 :=
    fun z hz hc => hfix z hz fun h hh => hc h hh.1
  have hfixs : ∀ z ∈ Z, (∀ h ∈ ggHyperplane Bs s, h * z = z * h) → z = 1 :=
    fun z hz hc => hfix z hz fun h hh => hc h hh.2
  have hSr : ggRankOneIn L Bs r ≤ pairD_lft L Bs r s := by
    refine le_inf ((ggOTwoPrime_le _).trans inf_le_left) ?_
    exact ((ggOTwoPrime_le _).trans inf_le_right).trans
      (Subgroup.centralizer_le (fun x hx => (Subgroup.mem_inf.mp hx).1))
  have hSs : ggRankOneIn L Bs s ≤ pairD_lft L Bs r s := by
    refine le_inf ((ggOTwoPrime_le _).trans inf_le_left) ?_
    exact ((ggOTwoPrime_le _).trans inf_le_right).trans
      (Subgroup.centralizer_le (fun x hx => (Subgroup.mem_inf.mp hx).2))
  have hUr := hD.img_rankOneIn hfixr
  have hUs := hD.img_rankOneIn hfixs
  have hUmap : ((ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau r)).subgroupOf
      (img N f (pairD_lft L Bs r s))).map φ = ggRankOneIn L Bs r := by
    rw [← hUr]
    exact img_subgroupOf_map_equiv_lft hDN e he hSr
  have hVmap : ((ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau s)).subgroupOf
      (img N f (pairD_lft L Bs r s))).map φ = ggRankOneIn L Bs s := by
    rw [← hUs]
    exact img_subgroupOf_map_equiv_lft hDN e he hSs
  exact ⟨φ, hφ, hUmap, hVmap⟩

theorem Datum.pair_lift (hD : Datum p N f L Bs Z) {r s : MulAut ↥Bs}
    (hfix : ∀ z ∈ Z, (∀ h ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs s, h * z = z * h) → z = 1)
    {K : Type} [Field K] [Finite K] [CharP K 2] {f' : ℕ} {W : Subgroup Q}
    (hpair : UnitaryBlockStandardPair K 2 f' W
      (ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau r))
      (ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau s)))
    (hW : W ≤ img N f (L ⊓ Subgroup.centralizer
      ((ggHyperplane Bs r ⊓ ggHyperplane Bs s : Subgroup G) : Set G))) :
    ∃ W' : Subgroup G, UnitaryBlockStandardPair K 2 f' W'
      (ggRankOneIn L Bs r) (ggRankOneIn L Bs s) := by
  classical
  obtain ⟨φ, hφ, hUmap, hVmap⟩ := exists_pairMap_lft hD hfix
  have hpair' : UnitaryBlockStandardPair K 2 f' (W.subgroupOf (img N f (pairD_lft L Bs r s)))
      ((ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau r)).subgroupOf
        (img N f (pairD_lft L Bs r s)))
      ((ggRankOneIn (img N f L) (img N f Bs) (MulAut.congr hD.tau s)).subgroupOf
        (img N f (pairD_lft L Bs r s))) :=
    unitaryBlockStandardPair_restrict hpair (img N f (pairD_lft L Bs r s)) hW
  have hmap := CFSG.GH74.L5U5.unitaryBlockStandardPair_map' hpair' φ hφ
  exact ⟨(W.subgroupOf (img N f (pairD_lft L Bs r s))).map φ,
    by simpa only [hUmap, hVmap] using hmap⟩

end NsQuot

end CFSG.StandardType

end

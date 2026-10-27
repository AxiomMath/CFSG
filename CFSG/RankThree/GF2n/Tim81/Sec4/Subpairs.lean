module

public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec41List
public import CFSG.Quasithin.Background.G2A5Iso
public import CFSG.RankThree.GF2n.Tim81.Sec4.Sec41Split

public section

namespace CFSG.RankThree.GF2n.Tim81

open CFSG CFSG.CGT.Timmesfeld75 CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Tim78
open CFSG.Quasithin.A5Model
open RootHyp
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {M V H : Subgroup G}

abbrev subpair (M V : Subgroup G) (g : G) : Subgroup G :=
  Pc M V ⊔ conjSubgroup g (Pc M V)

abbrev subpairImage (M V H : Subgroup G) (Z : Subgroup (HBar V H)) [Z.Normal] (g : G) :
    Subgroup (HBar V H ⧸ Z) :=
  (imgK V H (subpair M V g)).map (QuotientGroup.mk' Z)

theorem imgK_subpair (hPH : Pc M V ≤ H) {g : G} (hg : g ∈ H) :
    imgK V H (subpair M V g) =
      imgK V H (Pc M V) ⊔
        conjSubgroup (piK V H ⟨g, hg⟩) (imgK V H (Pc M V)) := by
  have hPgH : conjSubgroup g (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hg
  rw [subpair, ← imgK_sup hPH hPgH, imgK_conjSubgroup hg hPH]

theorem map_imgK_subpair (hPH : Pc M V ≤ H) {g : G} (hg : g ∈ H)
    {Z : Subgroup (HBar V H)} [Z.Normal] :
    subpairImage M V H Z g =
      (imgK V H (Pc M V)).map (QuotientGroup.mk' Z) ⊔
        conjSubgroup (QuotientGroup.mk' Z (piK V H ⟨g, hg⟩))
          ((imgK V H (Pc M V)).map (QuotientGroup.mk' Z)) := by
  rw [subpairImage, imgK_subpair hPH hg, Subgroup.map_sup, map_conjSubgroup]

private theorem imgK_le_normalizer_of_le_normalizer {S : Subgroup G} (hPH : Pc M V ≤ H)
    (hSN : S ≤ Subgroup.normalizer (Pc M V : Set G)) :
    imgK V H S ≤ Subgroup.normalizer (imgK V H (Pc M V) : Set (HBar V H)) := by
  intro y hy
  obtain ⟨s, hs, rfl⟩ := mem_imgK_iff.mp hy
  have hsN : (s : G) ∈ Subgroup.normalizer (Pc M V : Set G) := hSN hs
  have hconjP : conjSubgroup (s : G) (Pc M V) = Pc M V :=
    mem_normalizer_iff_conjSubgroup_eq.mp hsN
  rw [← conjSubgroup_eq_self_iff]
  calc conjSubgroup (piK V H s) (imgK V H (Pc M V))
      = imgK V H (conjSubgroup (s : G) (Pc M V)) := (imgK_conjSubgroup s.2 hPH).symm
    _ = imgK V H (Pc M V) := by rw [hconjP]

private theorem imgK_subpair_eq_of_le_M (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {g : G} (hg : g ∈ H)
    (hXM : subpair M V g ≤ M) :
    imgK V H (subpair M V g) = imgK V H (Pc M V) := by
  have hPgH : conjSubgroup g (Pc M V) ≤ H := conjSubgroup_le_of_le_of_mem hPH hg
  have hPgN : conjSubgroup g (Pc M V) ≤ Subgroup.normalizer (Pc M V : Set G) :=
    (le_sup_right.trans hXM).trans h.toHyp.le_normalizer_Pc
  have hnorm := imgK_le_normalizer_of_le_normalizer hPH hPgN
  have hEq := weaklyClosed_imgK h hPH hg hnorm
  change imgK V H (Pc M V ⊔ conjSubgroup g (Pc M V)) = imgK V H (Pc M V)
  rw [← imgK_sup hPH hPgH, hEq, sup_idem]

theorem RootHyp.not_le_of_not_isPGroup (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {g : G} (hg : g ∈ H)
    {Z : Subgroup (HBar V H)} [Z.Normal]
    (hn2 : ¬ IsPGroup 2 (subpairImage M V H Z g)) : ¬ subpair M V g ≤ M := by
  intro hXM
  apply hn2
  have hEq := imgK_subpair_eq_of_le_M h hPH hg hXM
  rw [subpairImage, hEq]
  exact (CFSG.Open.IsElemAbelian.isPGroup (isElemAbelian_imgK h hPH hVH)).map
    (QuotientGroup.mk' Z)

theorem RootHyp.isHMember_sup_conj (h : RootHyp M V) (hPH : Pc M V ≤ H)
    (hVH : V ≤ inSubgroup (pCore 2) H) {g : G} (hg : g ∈ H)
    (hX : ¬ subpair M V g ≤ M) : IsHMember M V (subpair M V g) := by
  classical
  let X : Subgroup G := subpair M V g
  let QH : Subgroup G := inSubgroup (pCore 2) H
  have hXH : X ≤ H := sup_le hPH (conjSubgroup_le_of_le_of_mem hPH hg)
  have hH_le_NQH : H ≤ Subgroup.normalizer (QH : Set G) := (inSubgroup_pCore_two H).2.2
  have hX_le_NQH : X ≤ Subgroup.normalizer (QH : Set G) := hXH.trans hH_le_NQH
  have hQHsub_normal : (QH.subgroupOf X).Normal := by
    have hX_le_inf : X ≤ Subgroup.normalizer (QH : Set G) ⊓
        Subgroup.normalizer (X : Set G) :=
      le_inf hX_le_NQH Subgroup.le_normalizer
    have hX_le : X ≤ Subgroup.normalizer (QH ⊓ X : Set G) :=
      hX_le_inf.trans (Subgroup.inf_normalizer_le_normalizer_inf (H := QH) (K := X))
    rw [← Subgroup.inf_subgroupOf_right QH X]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hX_le
  have hN_normal : ((QH ⊓ X).subgroupOf X).Normal := by
    rw [Subgroup.inf_subgroupOf_right QH X]
    exact hQHsub_normal
  have hNp : IsPGroup 2 ↥(QH ⊓ X) := (inSubgroup_pCore_two H).1.to_le inf_le_left
  have hV_le_N : V ≤ QH ⊓ X := by
    refine le_inf hVH ?_
    show V ≤ X
    exact h.toHyp.le_Pc.trans (by dsimp [X, subpair]; exact le_sup_left)
  have hN_ne : QH ⊓ X ≠ ⊥ :=
    fun hbot => h.toHyp.ne_bot (le_bot_iff.mp (hV_le_N.trans_eq hbot))
  have hN_le_pCore : QH ⊓ X ≤ inSubgroup (pCore 2) X :=
    Tim78.le_inSubgroup_pCore inf_le_right
      ((Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mp hN_normal) hNp
  refine ⟨?_, ?_, hX⟩
  · intro hbot
    exact hN_ne (le_bot_iff.mp (hN_le_pCore.trans (le_of_eq hbot)))
  · show Pc M V ≤ X
    dsimp [X, subpair]
    exact le_sup_left

theorem solvable_quotient_of_commutator_ker_le {X B : Type*} [Group X] [Group B]
    (D K : Subgroup X) [D.Normal] [K.Normal] (hDK : D ≤ K)
    (ψ : X →* B) (hψ : Function.Surjective ψ) (hDψ : D ≤ MonoidHom.ker ψ)
    (hcomm : ⁅MonoidHom.ker ψ, MonoidHom.ker ψ⁆ ≤ D)
    [Group.IsSolvable B] : Group.IsSolvable (X ⧸ K) := by
  classical
  let L : Subgroup (X ⧸ D) := (MonoidHom.ker ψ).map (QuotientGroup.mk' D)
  have hL_normal : L.Normal := by
    dsimp [L]
    infer_instance
  haveI : L.Normal := hL_normal
  have hL_ab : IsMulCommutative ↥L := by
    refine ⟨⟨fun y z => Subtype.ext ?_⟩⟩
    obtain ⟨a, ha, hay⟩ := Subgroup.mem_map.mp y.2
    obtain ⟨b, hb, hbz⟩ := Subgroup.mem_map.mp z.2
    have hy : (y : X ⧸ D) = (QuotientGroup.mk' D) a := hay.symm
    have hz : (z : X ⧸ D) = (QuotientGroup.mk' D) b := hbz.symm
    simp only [Subgroup.coe_mul]
    rw [hy, hz]
    have hc : ⁅a, b⁆ ∈ D := hcomm (Subgroup.commutator_mem_commutator ha hb)
    have h1 : (QuotientGroup.mk' D) ⁅a, b⁆ = 1 := (QuotientGroup.eq_one_iff _).mpr hc
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    simpa using h1
  haveI : Group.IsSolvable ↥L := inferInstance
  have hquot_iso : (X ⧸ D) ⧸ L ≃* B := by
    have e1 : X ⧸ MonoidHom.ker ψ ≃* B :=
      QuotientGroup.quotientKerEquivOfSurjective ψ hψ
    have e2 : (X ⧸ D) ⧸ L ≃* X ⧸ MonoidHom.ker ψ :=
      QuotientGroup.quotientQuotientEquivQuotient (G := X) (N := D)
        (M := MonoidHom.ker ψ) hDψ
    exact e2.trans e1
  have hquot_solv : Group.IsSolvable ((X ⧸ D) ⧸ L) :=
    Group.isSolvable_of_surjective (f := hquot_iso.symm.toMonoidHom)
      hquot_iso.symm.surjective
  haveI : Group.IsSolvable (X ⧸ D) :=
    Group.isSolvable_of_subgroup_quotient (G := X ⧸ D) L
  let π : X ⧸ D →* X ⧸ K :=
    QuotientGroup.lift D (QuotientGroup.mk' K)
      (fun x hx => (QuotientGroup.eq_one_iff x).mpr (hDK hx))
  have hπ : Function.Surjective π := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K y
    exact ⟨QuotientGroup.mk' D x, rfl⟩
  exact Group.isSolvable_of_surjective (f := π) hπ

private theorem isSolvable_map_comap_of_commutator_ker_le {X B : Type*} [Group X] [Group B]
    (D K : Subgroup X) [D.Normal] [K.Normal] (hDK : D ≤ K)
    (ψ : X →* B) (hψ : Function.Surjective ψ) (hDψ : D ≤ MonoidHom.ker ψ)
    (hcomm : ⁅MonoidHom.ker ψ, MonoidHom.ker ψ⁆ ≤ D) (R : Subgroup B) [R.Normal]
    (hR : Group.IsSolvable ↥R) :
    Group.IsSolvable ↥((R.comap ψ).map (QuotientGroup.mk' K)) := by
  classical
  let S : Subgroup X := R.comap ψ
  have hS_normal : S.Normal := by
    dsimp [S]
    infer_instance
  haveI : S.Normal := hS_normal
  let R' : Subgroup (X ⧸ K) := S.map (QuotientGroup.mk' K)
  have hR'_normal : R'.Normal := by
    dsimp [R']
    infer_instance
  haveI : R'.Normal := hR'_normal
  let ψ' : ↥S →* ↥R := MonoidHom.codRestrict (ψ.comp S.subtype) R (fun x => x.2)
  have hψ'_surj : Function.Surjective ψ' := by
    intro r
    obtain ⟨x, hx⟩ := hψ (r : B)
    have hxS : x ∈ S := Subgroup.mem_comap.mpr (by rw [hx]; exact r.2)
    exact ⟨⟨x, hxS⟩, Subtype.ext hx⟩
  let D' : Subgroup ↥S := D.subgroupOf S
  let K' : Subgroup ↥S := K.subgroupOf S
  have hD'_normal : D'.Normal := inferInstance
  have hK'_normal : K'.Normal := inferInstance
  have hD'_le_K' : D' ≤ K' := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr (hDK (Subgroup.mem_subgroupOf.mp hx))
  have hD'_le_ker : D' ≤ MonoidHom.ker ψ' := by
    intro x hx
    rw [MonoidHom.mem_ker]
    apply Subtype.ext
    exact MonoidHom.mem_ker.mp (hDψ (Subgroup.mem_subgroupOf.mp hx))
  have hcomm' : ⁅MonoidHom.ker ψ', MonoidHom.ker ψ'⁆ ≤ D' := by
    rw [Subgroup.commutator_le]
    intro x hx y hy
    apply Subgroup.mem_subgroupOf.mpr
    apply hcomm
    apply Subgroup.commutator_mem_commutator
    · exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hx))
    · exact MonoidHom.mem_ker.mpr (congrArg Subtype.val (MonoidHom.mem_ker.mp hy))
  haveI : Group.IsSolvable ↥R := hR
  have hSK_solv : Group.IsSolvable (↥S ⧸ K') :=
    solvable_quotient_of_commutator_ker_le D' K' hD'_le_K' ψ' hψ'_surj hD'_le_ker hcomm'
  let f : ↥S →* X ⧸ K := (QuotientGroup.mk' K).comp S.subtype
  have hf_ker : MonoidHom.ker f = K' := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact QuotientGroup.eq_one_iff (x : X)
  have hf_range : MonoidHom.range f = R' := by
    ext y
    constructor
    · rintro ⟨x, rfl⟩
      exact Subgroup.mem_map.mpr ⟨x, x.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨x, hx⟩, rfl⟩
  have e' : (↥S ⧸ K') ≃* ↥R' :=
    (QuotientGroup.quotientMulEquivOfEq hf_ker.symm).trans
      ((QuotientGroup.quotientKerEquivRange f).trans (MulEquiv.subgroupCongr hf_range))
  show Group.IsSolvable ↥R'
  exact Group.isSolvable_of_surjective (f := e'.toMonoidHom) e'.surjective

private theorem nonempty_quotient_alt5_of_surjective {Y : Type*} [Group Y]
    {R' : Subgroup Y} [R'.Normal] (hR' : Group.IsSolvable ↥R')
    (α : alternatingGroup (Fin 5) →* Y ⧸ R') (hα_surj : Function.Surjective α)
    (hsolv : ¬ Group.IsSolvable Y) :
    Nonempty (Y ⧸ R' ≃* alternatingGroup (Fin 5)) := by
  classical
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker α) with hbot | htop
  · have hα_inj : Function.Injective α := by
      refine (injective_iff_map_eq_one α).mpr ?_
      intro a ha
      have hmem : a ∈ MonoidHom.ker α := MonoidHom.mem_ker.mpr ha
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact ⟨(MulEquiv.ofBijective α ⟨hα_inj, hα_surj⟩).symm⟩
  · exfalso
    haveI : Subsingleton (Y ⧸ R') := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := hα_surj a
      obtain ⟨y, rfl⟩ := hα_surj b
      rw [show α x = 1 from MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top x),
        show α y = 1 from MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top y)]
    have hR'_top : R' = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have h1 : QuotientGroup.mk' R' x = 1 := Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).mp h1
    have htop_solv : Group.IsSolvable ↥(⊤ : Subgroup Y) := hR'_top ▸ hR'
    let eTop : ↥(⊤ : Subgroup Y) ≃* Y := Subgroup.topEquiv
    exact hsolv (Group.isSolvable_of_surjective (f := eTop.toMonoidHom) eTop.surjective)

private theorem exists_alt5_quotient_of_commutator_ker_le {X B : Type*} [Group X] [Group B]
    (D K : Subgroup X) [D.Normal] [K.Normal] (hDK : D ≤ K)
    (ψ : X →* B) (hψ : Function.Surjective ψ) (hDψ : D ≤ MonoidHom.ker ψ)
    (hcomm : ⁅MonoidHom.ker ψ, MonoidHom.ker ψ⁆ ≤ D)
    (R : Subgroup B) [R.Normal] (hR : Group.IsSolvable ↥R)
    (e : B ⧸ R ≃* alternatingGroup (Fin 5))
    (hsolv : ¬ Group.IsSolvable (X ⧸ K)) :
    ∃ (R' : Subgroup (X ⧸ K)) (_ : R'.Normal), Group.IsSolvable ↥R' ∧
      Nonempty ((X ⧸ K) ⧸ R' ≃* alternatingGroup (Fin 5)) := by
  classical
  let S : Subgroup X := R.comap ψ
  have hS_normal : S.Normal := by
    dsimp [S]
    infer_instance
  haveI : S.Normal := hS_normal
  let R' : Subgroup (X ⧸ K) := S.map (QuotientGroup.mk' K)
  have hR'_normal : R'.Normal := by
    dsimp [R']
    infer_instance
  haveI : R'.Normal := hR'_normal
  have hR'_solv : Group.IsSolvable ↥R' := by
    dsimp [R', S]
    exact isSolvable_map_comap_of_commutator_ker_le D K hDK ψ hψ hDψ hcomm R hR
  let φ : X →* (X ⧸ K) ⧸ R' := (QuotientGroup.mk' R').comp (QuotientGroup.mk' K)
  have hS_ker : S ≤ MonoidHom.ker φ := by
    intro x hx
    rw [MonoidHom.mem_ker]
    have hxR' : (QuotientGroup.mk' K) x ∈ R' :=
      Subgroup.mem_map.mpr ⟨x, hx, rfl⟩
    exact (QuotientGroup.eq_one_iff _).mpr hxR'
  let φ' : X ⧸ S →* (X ⧸ K) ⧸ R' := QuotientGroup.lift S φ hS_ker
  have hφ'_surj : Function.Surjective φ' := by
    intro y
    obtain ⟨z, rfl⟩ := QuotientGroup.mk'_surjective R' y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective K z
    exact ⟨QuotientGroup.mk' S x, rfl⟩
  let ρ : X ⧸ S →* B ⧸ R :=
    QuotientGroup.lift S ((QuotientGroup.mk' R).comp ψ)
      (fun x hx => (QuotientGroup.eq_one_iff (ψ x)).mpr hx)
  have hρ_inj : Function.Injective ρ := by
    rw [injective_iff_map_eq_one]
    intro y hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective S y
    change QuotientGroup.mk' R (ψ x) = 1 at hy
    have hmem : ψ x ∈ R := (QuotientGroup.eq_one_iff (ψ x)).mp hy
    exact (QuotientGroup.eq_one_iff x).mpr hmem
  have hρ_surj : Function.Surjective ρ := by
    intro y
    obtain ⟨b, rfl⟩ := QuotientGroup.mk'_surjective R y
    obtain ⟨x, hx⟩ := hψ b
    refine ⟨QuotientGroup.mk' S x, ?_⟩
    change QuotientGroup.mk' R (ψ x) = QuotientGroup.mk' R b
    rw [hx]
  let eXR : X ⧸ S ≃* B ⧸ R := MulEquiv.ofBijective ρ ⟨hρ_inj, hρ_surj⟩
  let α : alternatingGroup (Fin 5) →* (X ⧸ K) ⧸ R' :=
    φ'.comp (eXR.trans e).symm.toMonoidHom
  have hα_surj : Function.Surjective α :=
    hφ'_surj.comp (eXR.trans e).symm.surjective
  exact ⟨R', hR'_normal, hR'_solv,
    nonempty_quotient_alt5_of_surjective hR'_solv α hα_surj hsolv⟩

theorem alt5_quotient_of_commutator_ker_le {X B : Type*} [Group X] [Group B]
    (D K : Subgroup X) [D.Normal] [K.Normal] (hDK : D ≤ K)
    (ψ : X →* B) (hψ : Function.Surjective ψ) (hDψ : D ≤ MonoidHom.ker ψ)
    (hcomm : ⁅MonoidHom.ker ψ, MonoidHom.ker ψ⁆ ≤ D)
    (R : Subgroup B) [R.Normal] (hR : Group.IsSolvable ↥R)
    (e : B ⧸ R ≃* alternatingGroup (Fin 5)) :
    Group.IsSolvable (X ⧸ K) ∨
      ∃ (R' : Subgroup (X ⧸ K)) (_ : R'.Normal), Group.IsSolvable ↥R' ∧
        Nonempty ((X ⧸ K) ⧸ R' ≃* alternatingGroup (Fin 5)) := by
  classical
  by_cases hsolv : Group.IsSolvable (X ⧸ K)
  · exact Or.inl hsolv
  · exact Or.inr (exists_alt5_quotient_of_commutator_ker_le D K hDK ψ hψ hDψ hcomm R hR e hsolv)

private theorem xOf_subpair_le {V H X : Subgroup G} (hXH : X ≤ H) :
    Tim79a.xOf V X ≤ Tim79a.xOf V H := by
  refine iSup₂_le fun U hU => ?_
  obtain ⟨x, hx, rfl⟩ := hU
  exact Tim79a.le_xOf (Tim79a.conjSubgroup_mem_omegaOf (hXH hx))

private theorem subgroupOf_le_ker_comp_mk {X : Subgroup G} (hXH : X ≤ H)
    {Z : Subgroup (HBar V H)} [Z.Normal] :
    (kOf V H).subgroupOf X ≤
      MonoidHom.ker ((QuotientGroup.mk' Z).comp
        ((piK V H).comp (Subgroup.inclusion hXH))) := by
  intro x hx
  rw [MonoidHom.mem_ker]
  have hxK : (x : G) ∈ kOf V H := Subgroup.mem_subgroupOf.mp hx
  have h1 : piK V H (Subgroup.inclusion hXH x) = 1 :=
    (piK_eq_one_iff (Subgroup.inclusion hXH x)).mpr hxK
  change (QuotientGroup.mk' Z) (piK V H (Subgroup.inclusion hXH x)) = 1
  rw [h1, map_one]

private theorem commutator_ker_comp_mk_le {Y : Type*} [Group Y] (π : Y →* HBar V H)
    {Z : Subgroup (HBar V H)} [Z.Normal] (hZ : Z ≤ Subgroup.center (HBar V H))
    (D : Subgroup Y) (hD : ∀ x, π x = 1 → x ∈ D) :
    ⁅MonoidHom.ker ((QuotientGroup.mk' Z).comp π),
      MonoidHom.ker ((QuotientGroup.mk' Z).comp π)⁆ ≤ D := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  apply hD
  have haZ : π a ∈ Z :=
    (QuotientGroup.eq_one_iff (π a)).mp (MonoidHom.mem_ker.mp ha)
  have hbZ : π b ∈ Z :=
    (QuotientGroup.eq_one_iff (π b)).mp (MonoidHom.mem_ker.mp hb)
  have hcommZ : ⁅π a, π b⁆ = 1 := by
    rw [commutatorElement_eq_one_iff_mul_comm]
    exact (Subgroup.mem_center_iff.mp (hZ haZ) (π b)).symm
  rw [map_commutatorElement]
  exact hcommZ

theorem RootHyp.isSolvable_hBar_of_isSolvable_map (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {g : G} (hg : g ∈ H)
    {Z : Subgroup (HBar V H)} [Z.Normal] (hZ : Z ≤ Subgroup.center (HBar V H))
    (hsolv : Group.IsSolvable (subpairImage M V H Z g)) :
    Group.IsSolvable (HBar V (subpair M V g)) := by
  haveI : Group.IsSolvable (subpairImage M V H Z g) := hsolv
  classical
  let X : Subgroup G := subpair M V g
  have hXH : X ≤ H := sup_le hPH (conjSubgroup_le_of_le_of_mem hPH hg)
  let KX : Subgroup ↥X := (kOf V X).subgroupOf X
  let D : Subgroup ↥X := (kOf V H).subgroupOf X
  have hD_normal : D.Normal := by
    have hX_le : X ≤ Subgroup.normalizer (kOf V H ⊓ X : Set G) :=
      (le_inf (hXH.trans (le_normalizer_kOf V H)) Subgroup.le_normalizer).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := kOf V H) (K := X))
    have h : D = (kOf V H ⊓ X).subgroupOf X := by
      dsimp [D]
      exact (Subgroup.inf_subgroupOf_right (kOf V H) X).symm
    rw [h]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hX_le
  have hKX_normal : KX.Normal := by
    dsimp [KX]
    exact kOf_normal V X
  have hW_le : Tim79a.xOf V X ≤ Tim79a.xOf V H := xOf_subpair_le hXH
  have hDK : D ≤ KX := by
    intro x hx
    have hxK : (x : G) ∈ kOf V H := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_subgroupOf]
    rw [mem_kOf_iff] at hxK ⊢
    refine ⟨x.2, ?_⟩
    exact (Subgroup.centralizer_le
      (show (Tim79a.xOf V X : Set G) ⊆ (Tim79a.xOf V H : Set G) from hW_le)) hxK.2
  let πH : ↥X →* HBar V H := (piK V H).comp (Subgroup.inclusion hXH)
  let πZ : ↥X →* HBar V H ⧸ Z := (QuotientGroup.mk' Z).comp πH
  have hπZ_mem : ∀ x : ↥X, πZ x ∈ subpairImage M V H Z g := by
    intro x
    exact Subgroup.mem_map.mpr
      ⟨πH x, Subgroup.mem_map.mpr ⟨Subgroup.inclusion hXH x, x.2, rfl⟩, rfl⟩
  let ψ : ↥X →* subpairImage M V H Z g :=
    MonoidHom.codRestrict πZ (subpairImage M V H Z g) hπZ_mem
  have hψ_surj : Function.Surjective ψ := by
    intro y
    obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.mp y.2
    obtain ⟨xH, hxH, hxu⟩ := mem_imgK_iff.mp hu
    refine ⟨⟨xH, hxH⟩, ?_⟩
    apply Subtype.ext
    change (QuotientGroup.mk' Z) (piK V H xH) = (y : HBar V H ⧸ Z)
    rw [hxu, huy]
  have hker : MonoidHom.ker ψ = MonoidHom.ker πZ :=
    MonoidHom.ker_codRestrict πZ (subpairImage M V H Z g) hπZ_mem
  have hD_le_kerZ : D ≤ MonoidHom.ker πZ := by
    dsimp [D, πZ, πH]
    exact subgroupOf_le_ker_comp_mk hXH
  have hD_le_ker : D ≤ MonoidHom.ker ψ := by
    rw [hker]
    exact hD_le_kerZ
  have hcomm_ker : ⁅MonoidHom.ker ψ, MonoidHom.ker ψ⁆ ≤ D := by
    rw [hker]
    exact commutator_ker_comp_mk_le πH hZ D (fun x hx =>
      Subgroup.mem_subgroupOf.mpr ((piK_eq_one_iff (Subgroup.inclusion hXH x)).mp hx))
  have h := solvable_quotient_of_commutator_ker_le (X := ↥X) D KX hDK ψ hψ_surj
    hD_le_ker hcomm_ker
  simpa [KX, HBar, X] using h

theorem RootHyp.isSolvable_or_alt5_hBar (h : RootHyp M V) (hPH : Pc M V ≤ H)
    {g : G} (hg : g ∈ H)
    {Z : Subgroup (HBar V H)} [Z.Normal] (hZ : Z ≤ Subgroup.center (HBar V H))
    (R : Subgroup (subpairImage M V H Z g)) [R.Normal]
    (hR : Group.IsSolvable ↥R)
    (e : subpairImage M V H Z g ⧸ R ≃* alternatingGroup (Fin 5)) :
    Group.IsSolvable (HBar V (subpair M V g)) ∨
      ∃ (R' : Subgroup (HBar V (subpair M V g))) (_ : R'.Normal),
        Group.IsSolvable ↥R' ∧
          Nonempty (HBar V (subpair M V g) ⧸ R' ≃* alternatingGroup (Fin 5)) := by
  classical
  let X : Subgroup G := subpair M V g
  have hXH : X ≤ H := sup_le hPH (conjSubgroup_le_of_le_of_mem hPH hg)
  let KX : Subgroup ↥X := (kOf V X).subgroupOf X
  let D : Subgroup ↥X := (kOf V H).subgroupOf X
  have hD_normal : D.Normal := by
    have hX_le : X ≤ Subgroup.normalizer (kOf V H ⊓ X : Set G) :=
      (le_inf (hXH.trans (le_normalizer_kOf V H)) Subgroup.le_normalizer).trans
        (Subgroup.inf_normalizer_le_normalizer_inf (H := kOf V H) (K := X))
    have h : D = (kOf V H ⊓ X).subgroupOf X := by
      dsimp [D]
      exact (Subgroup.inf_subgroupOf_right (kOf V H) X).symm
    rw [h]
    exact (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_right).mpr hX_le
  have hKX_normal : KX.Normal := by
    dsimp [KX]
    exact kOf_normal V X
  have hW_le : Tim79a.xOf V X ≤ Tim79a.xOf V H := xOf_subpair_le hXH
  have hDK : D ≤ KX := by
    intro x hx
    have hxK : (x : G) ∈ kOf V H := Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_subgroupOf]
    rw [mem_kOf_iff] at hxK ⊢
    refine ⟨x.2, ?_⟩
    exact (Subgroup.centralizer_le
      (show (Tim79a.xOf V X : Set G) ⊆ (Tim79a.xOf V H : Set G) from hW_le)) hxK.2
  let πH : ↥X →* HBar V H := (piK V H).comp (Subgroup.inclusion hXH)
  let πZ : ↥X →* HBar V H ⧸ Z := (QuotientGroup.mk' Z).comp πH
  have hπZ_mem : ∀ x : ↥X, πZ x ∈ subpairImage M V H Z g := by
    intro x
    exact Subgroup.mem_map.mpr
      ⟨πH x, Subgroup.mem_map.mpr ⟨Subgroup.inclusion hXH x, x.2, rfl⟩, rfl⟩
  let ψ : ↥X →* subpairImage M V H Z g :=
    MonoidHom.codRestrict πZ (subpairImage M V H Z g) hπZ_mem
  have hψ_surj : Function.Surjective ψ := by
    intro y
    obtain ⟨u, hu, huy⟩ := Subgroup.mem_map.mp y.2
    obtain ⟨xH, hxH, hxu⟩ := mem_imgK_iff.mp hu
    refine ⟨⟨xH, hxH⟩, ?_⟩
    apply Subtype.ext
    change (QuotientGroup.mk' Z) (piK V H xH) = (y : HBar V H ⧸ Z)
    rw [hxu, huy]
  have hker : MonoidHom.ker ψ = MonoidHom.ker πZ :=
    MonoidHom.ker_codRestrict πZ (subpairImage M V H Z g) hπZ_mem
  have hD_le_kerZ : D ≤ MonoidHom.ker πZ := by
    dsimp [D, πZ, πH]
    exact subgroupOf_le_ker_comp_mk hXH
  have hD_le_ker : D ≤ MonoidHom.ker ψ := by
    rw [hker]
    exact hD_le_kerZ
  have hcomm_ker : ⁅MonoidHom.ker ψ, MonoidHom.ker ψ⁆ ≤ D := by
    rw [hker]
    exact commutator_ker_comp_mk_le πH hZ D (fun x hx =>
      Subgroup.mem_subgroupOf.mpr ((piK_eq_one_iff (Subgroup.inclusion hXH x)).mp hx))
  have h := alt5_quotient_of_commutator_ker_le (X := ↥X) D KX hDK ψ hψ_surj
    hD_le_ker hcomm_ker R hR e
  simpa [KX, HBar, X] using h

theorem RootHyp.false_of_solvable_subpair (h79 : Tim79aStatementWCQ) (h : RootHyp M V)
    (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H)
    {Z : Subgroup (HBar V H)} [Z.Normal] (hZ : Z ≤ Subgroup.center (HBar V H))
    {g : G} (hg : g ∈ H) (hsolv : Group.IsSolvable (subpairImage M V H Z g))
    (hn2 : ¬ IsPGroup 2 (subpairImage M V H Z g)) : False := by
  have hnM' : ¬ subpair M V g ≤ M := not_le_of_not_isPGroup h hPH hVH hg hn2
  have hmem : IsHMember M V (subpair M V g) := isHMember_sup_conj h hPH hVH hg hnM'
  have hVX : V ≤ inSubgroup (pCore 2) (subpair M V g) := le_pCore_of_isHMember h79 h hmem
  have hsolvX : Group.IsSolvable (HBar V (subpair M V g)) :=
    isSolvable_hBar_of_isSolvable_map h hPH hg hZ hsolv
  exact not_isSolvable_HBar h hmem.2.1 hVX rfl hmem.2.2 hsolvX

private theorem not_isPGroup_subpairImage_of_alt5
    {g : G} {Z : Subgroup (HBar V H)} [Z.Normal]
    (R : Subgroup (subpairImage M V H Z g)) [R.Normal]
    (e : subpairImage M V H Z g ⧸ R ≃* alternatingGroup (Fin 5)) :
    ¬ IsPGroup 2 (subpairImage M V H Z g) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro h2
  have h2q : IsPGroup 2 (subpairImage M V H Z g ⧸ R) := h2.to_quotient R
  have h2A : IsPGroup 2 (alternatingGroup (Fin 5)) := h2q.of_equiv e
  obtain ⟨n, hn⟩ :=
    (IsPGroup.iff_card (p := 2) (G := alternatingGroup (Fin 5))).mp h2A
  have hcard : Nat.card (alternatingGroup (Fin 5)) = 60 := by
    rw [nat_card_alternatingGroup]
    norm_num
  have h3 : 3 ∣ Nat.card (alternatingGroup (Fin 5)) := by rw [hcard]; norm_num
  have h3pow : 3 ∣ 2 ^ n := by rw [← hn]; exact h3
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3pow) (by norm_num)

private theorem center_eq_bot_of_alt5_injective
    (h : RootHyp M V) {X : Subgroup G}
    (hPX : Pc M V ≤ X) (hVX : V ≤ inSubgroup (pCore 2) X)
    {yX : G} (hyX : yX ∈ X) (hXyX : X = Pc M V ⊔ conjSubgroup yX (Pc M V))
    {α : alternatingGroup (Fin 5) →* HBar V X ⧸ Subgroup.center (HBar V X)}
    (hα_inj : Function.Injective α) (hα_surj : Function.Surjective α)
    (hCT : CentralTIStatement) :
    Subgroup.center (HBar V X) = ⊥ := by
  have eZ : HBar V X ⧸ Subgroup.center (HBar V X) ≃* alternatingGroup (Fin 5) :=
    (MulEquiv.ofBijective α ⟨hα_inj, hα_surj⟩).symm
  obtain ⟨e5⟩ := sl2_four_equiv_alt5 (GaloisField 2 2) card_gf4 card_sl2_gf4
  let T : Subgroup (HBar V X) := imgK V X (Pc M V)
  have hT : Assembly.IsElemAbelian 2 T := isElemAbelian_imgK h hPX hVX
  have hgen : Subgroup.normalClosure (T : Set (HBar V X)) = ⊤ :=
    normalClosure_imgK_eq_top h hPX hyX hXyX
  have hTI : IsTI T := isTI_imgK h hPX hVX
  have hwc : WeaklyClosedIn T
      (Subgroup.normalizer (T : Set (HBar V X))) := by
    refine ⟨Subgroup.le_normalizer, ?_⟩
    intro gbar hgbar
    obtain ⟨x, rfl⟩ := piK_surjective V X gbar
    have hconj : conjSubgroup (piK V X x) T =
        imgK V X (conjSubgroup (x : G) (Pc M V)) :=
      (imgK_conjSubgroup (V := V) (H := X) (S := Pc M V) x.2 hPX).symm
    rw [hconj] at hgbar ⊢
    exact weaklyClosed_imgK h hPX x.2 hgbar
  haveI : Fintype (GaloisField 2 2) := Fintype.ofFinite _
  have hL2 : IsL2OrSzGroup (HBar V X ⧸ Subgroup.center (HBar V X)) := by
    refine Or.inl ⟨GaloisField 2 2, inferInstance, inferInstance, inferInstance, ?_, ?_⟩
    · rw [← Nat.card_eq_fintype_card, card_gf4]
    · exact ⟨eZ.trans e5.symm⟩
  exact hCT (HBar V X) T (Subgroup.center (HBar V X)) hT hgen hTI hwc (le_refl _) hL2

private theorem center_eq_bot_of_alt5_quotient
    (h : RootHyp M V) {X : Subgroup G}
    (hPX : Pc M V ≤ X) (hVX : V ≤ inSubgroup (pCore 2) X)
    {yX : G} (hyX : yX ∈ X) (hXyX : X = Pc M V ⊔ conjSubgroup yX (Pc M V))
    {R' : Subgroup (HBar V X)} [R'.Normal]
    (hR'_center : R' ≤ Subgroup.center (HBar V X))
    (e' : HBar V X ⧸ R' ≃* alternatingGroup (Fin 5))
    (hX_not_solv : ¬ Group.IsSolvable (HBar V X))
    (hCT : CentralTIStatement) :
    Subgroup.center (HBar V X) = ⊥ := by
  classical
  let πR : HBar V X ⧸ R' →* HBar V X ⧸ Subgroup.center (HBar V X) :=
    QuotientGroup.lift R' (QuotientGroup.mk' (Subgroup.center (HBar V X)))
      (fun x hx => (QuotientGroup.eq_one_iff x).mpr (hR'_center hx))
  have hπR_surj : Function.Surjective πR := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    exact ⟨QuotientGroup.mk' R' x, rfl⟩
  let α : alternatingGroup (Fin 5) →* HBar V X ⧸ Subgroup.center (HBar V X) :=
    πR.comp e'.symm.toMonoidHom
  have hα_surj : Function.Surjective α :=
    hπR_surj.comp e'.symm.surjective
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := alternatingGroup.isSimpleGroup_five
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (MonoidHom.ker α) with hbot | htop
  · have hα_inj : Function.Injective α := by
      refine (injective_iff_map_eq_one α).mpr ?_
      intro a ha
      have hmem : a ∈ MonoidHom.ker α := MonoidHom.mem_ker.mpr ha
      rw [hbot] at hmem
      exact Subgroup.mem_bot.mp hmem
    exact center_eq_bot_of_alt5_injective h hPX hVX hyX hXyX hα_inj hα_surj hCT
  · exfalso
    haveI : Subsingleton (HBar V X ⧸ Subgroup.center (HBar V X)) := by
      refine ⟨fun a b => ?_⟩
      obtain ⟨x, rfl⟩ := hα_surj a
      obtain ⟨y, rfl⟩ := hα_surj b
      rw [show α x = 1 from MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top x),
        show α y = 1 from MonoidHom.mem_ker.mp (htop ▸ Subgroup.mem_top y)]
    have hcenter_top : Subgroup.center (HBar V X) = ⊤ := by
      rw [eq_top_iff]
      intro x _
      have h1 : QuotientGroup.mk' (Subgroup.center (HBar V X)) x = 1 :=
        Subsingleton.elim _ _
      exact (QuotientGroup.eq_one_iff x).mp h1
    haveI : IsMulCommutative (HBar V X) :=
      Subgroup.center_eq_top_iff.mp hcenter_top
    exact hX_not_solv inferInstance

theorem RootHyp.false_of_alt5_subpair (h79 : Tim79aStatementWCQ) (hA5 : HA5Statement)
    (hCT : CentralTIStatement) (h : RootHyp M V)
    (hPH : Pc M V ≤ H) (hVH : V ≤ inSubgroup (pCore 2) H)
    {Z : Subgroup (HBar V H)} [Z.Normal] (hZ : Z ≤ Subgroup.center (HBar V H))
    {g : G} (hg : g ∈ H) (R : Subgroup (subpairImage M V H Z g)) [R.Normal]
    (hR : Group.IsSolvable ↥R)
    (e : subpairImage M V H Z g ⧸ R ≃* alternatingGroup (Fin 5)) : False := by
  classical
  have hn2 : ¬ IsPGroup 2 (subpairImage M V H Z g) :=
    not_isPGroup_subpairImage_of_alt5 R e
  have hnM' : ¬ subpair M V g ≤ M := not_le_of_not_isPGroup h hPH hVH hg hn2
  have hmem : IsHMember M V (subpair M V g) := isHMember_sup_conj h hPH hVH hg hnM'
  have hVX : V ≤ inSubgroup (pCore 2) (subpair M V g) := le_pCore_of_isHMember h79 h hmem
  have hXbar_not_solv : ¬ Group.IsSolvable (HBar V (subpair M V g)) :=
    not_isSolvable_HBar h hmem.2.1 hVX rfl hmem.2.2
  have hcases := isSolvable_or_alt5_hBar h hPH hg hZ R hR e
  rcases hcases with hsolvX | ⟨R', hR'_normal, hR'_solv, ⟨e'⟩⟩
  · exact hXbar_not_solv hsolvX
  · haveI : R'.Normal := hR'_normal
    have hR'_center : R' ≤ Subgroup.center (HBar V (subpair M V g)) :=
      le_center_of_isSolvable_normal h hmem.2.1 hVX rfl hmem.2.2 R' hR'_solv
    obtain ⟨yX, hyX, -, -, hXyX⟩ := h.exists_mem_conj_eq_of_eq_sup hmem.2.1 rfl
    have hZbot : Subgroup.center (HBar V (subpair M V g)) = ⊥ :=
      center_eq_bot_of_alt5_quotient (X := subpair M V g) (R' := R') h hmem.2.1 hVX
        hyX hXyX hR'_center e' hXbar_not_solv hCT
    have hR'_bot : R' = ⊥ := by
      exact le_bot_iff.mp (hR'_center.trans (le_of_eq hZbot))
    have eB : HBar V (subpair M V g) ≃* alternatingGroup (Fin 5) :=
      (QuotientGroup.quotientBot (G := HBar V (subpair M V g))).symm.trans
        (hR'_bot ▸ e')
    exact (hA5 G M V h g hmem hVX).false eB

end CFSG.RankThree.GF2n.Tim81

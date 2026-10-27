module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7DKSqueezeAux
import CFSG.LocalAnalysis.StandardType.GGHdRo7DSideData
import CFSG.LocalAnalysis.StandardType.GGHdRo7DAJ
import CFSG.LocalAnalysis.StandardType.GGHdRo7CoprimeSplit
import CFSG.LocalAnalysis.StandardType.GGTriD4NoneTransport
import CFSG.LocalAnalysis.StandardType.GGNbrBalance
import CFSG.RankThree.PartOne.S11d.LieFieldTransfer
import CFSG.LocalAnalysis.StandardType.GGSecFiveNonWeylOfKnown
import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
import CFSG.GroupTheory.LocalCores.Layer.CentralExtension
import CFSG.GroupTheory.PCore.PCoreOfMulEquiv

public section

namespace CFSG.StandardType.HdRo7D

open CFSG.Assembly CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

private theorem hdRo7DKSQAux_nonempty_centerQuot_map {K Q : Type*} [Group K] [Group Q]
    (π : K →* Q) (hker : π.ker ≤ Subgroup.center K) {J : Subgroup K} (hJ : Group.IsPerfect ↥J) :
    Nonempty (↥J ⧸ Subgroup.center ↥J ≃* ↥(J.map π) ⧸ Subgroup.center ↥(J.map π)) := by
  let f : ↥J →* ↥(J.map π) := π.subgroupMap J
  have hf : Function.Surjective f := π.subgroupMap_surjective J
  have hfker : f.ker ≤ Subgroup.center ↥J := by
    intro j hj
    rw [Subgroup.mem_center_iff]
    intro g
    have hj' : (j : K) ∈ π.ker :=
      MonoidHom.mem_ker.2 (congrArg Subtype.val (MonoidHom.mem_ker.1 hj))
    exact Subtype.ext (Subgroup.mem_center_iff.1 (hker hj') g)
  have hc := CFSG.LocalCores.comap_center_eq_of_perfect hJ f hf hfker
  have hc' : Subgroup.center ↥J =
      ((QuotientGroup.mk' (Subgroup.center ↥(J.map π))).comp f).ker := by
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk']
    exact hc.symm
  exact ⟨(QuotientGroup.quotientMulEquivOfEq hc').trans
    (QuotientGroup.quotientKerEquivOfSurjective _ ((QuotientGroup.mk'_surjective _).comp hf))⟩

theorem d_kSqueeze (hRig : GGLabelRigidInput) (hLB : GGLBalanceInput) (hFr : DFrameOmegaLeaf)
    (hT3 : DJBlockOmegaLeaf) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {y : G} {K : Subgroup G} (hH : GGResHyp p B Bs x L D J y K)
    [Fact p.Prime] (hrow : GGResRowAt ggRowDCorank2 p J K) :
    Bs ⊓ Subgroup.centralizer (K : Set G) = Subgroup.zpowers y := by
  have hHcopy : GGResHyp p B Bs x L D J y K := hH
  have hrowK : GGResRowAt ggRowDCorank2 p J K := hrow
  obtain ⟨labJ, labK, hJ2, hK2, hHasJ, hHasK, hp3, htagJ, htagK, hnJ, hnK, hrank,
    hr6⟩ := hrow
  obtain ⟨hcfg, hOp, hIDAll, hNoT, hnbr, hRefl, hScal⟩ := hH
  obtain ⟨hI, hBs, hDJ⟩ := hcfg
  have hBsB : B ≤ Bs := hBs.1
  have hBsEA : IsElemAbelian p Bs := hBs.2.1
  have hBsSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs := hBs.2.2.2
  have hp : p.Prime := Fact.out
  have hS : LargeEvenSStar p B x L := by
    obtain ⟨-, -, -, -, -, -, hS, -⟩ := hI
    exact hS
  have hxBs : x ∈ Bs := hBsB hS.2.1
  have hM : GGInnerDiagOn Bs K := hIDAll.2 y K hnbr
  obtain ⟨hBsN, hinner, hcopK, hframe⟩ :=
    d_sideData hRig hFr hp3 hM hK2 hHasK htagK hnK (by omega)
  have hcop' : p.Coprime (Nat.card (Subgroup.center ↥K)) :=
    (Nat.Prime.coprime_iff_not_dvd hp).mpr hcopK
  have hsplit := ggBstar_split_of_inner_coprime hp hBs hcop' hBsN hinner
  obtain ⟨t, ht, c, hc, hxeq⟩ := hsplit x hxBs
  have htK : t ∈ K := ht.2
  have htBs : t ∈ Bs := ht.1
  have hcC : c ∈ Subgroup.centralizer (K : Set G) := hc.2
  have htp : t ^ p = 1 := hBsEA.2 t htBs
  have hpJ : p ∣ Nat.card J := hdRo7DAJAux_three_dvd_card_of_row hrowK
  have hJK : J ≤ K := le_of_ggNbr hLB hI hDJ hpJ hnbr
  have hJx : IsComponentOf J (K ⊓ Subgroup.centralizer ({x} : Set G)) :=
    isComponentOf_inf_centralizer_of_ggNbr hS hDJ hnbr hJK
  have hcent : K ⊓ Subgroup.centralizer ({x} : Set G) =
      K ⊓ Subgroup.centralizer ({t} : Set G) := by
    have hcz : ∀ z ∈ K, z * c = c * z := by
      intro z hz
      exact Subgroup.mem_centralizer_iff.mp hcC z hz
    ext z
    constructor
    · rintro ⟨hzK, hzx⟩
      refine ⟨hzK, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hzx' : z * x = x * z := Subgroup.mem_centralizer_singleton_iff.mp hzx
      exact mul_right_cancel (by
        calc z * t * c = z * (t * c) := by group
          _ = z * x := by rw [hxeq]
          _ = x * z := hzx'
          _ = (t * c) * z := by rw [hxeq]
          _ = t * (c * z) := by group
          _ = t * (z * c) := by rw [hcz z hzK]
          _ = t * z * c := by group)
    · rintro ⟨hzK, hzt⟩
      refine ⟨hzK, Subgroup.mem_centralizer_singleton_iff.mpr ?_⟩
      have hzt' : z * t = t * z := Subgroup.mem_centralizer_singleton_iff.mp hzt
      calc z * x = z * (t * c) := by rw [hxeq]
        _ = z * t * c := by group
        _ = t * z * c := by rw [hzt']
        _ = t * (z * c) := by group
        _ = t * (c * z) := by rw [← hcz z hzK]
        _ = (t * c) * z := by group
        _ = x * z := by rw [hxeq]
  have hJt : IsComponentOf J (K ⊓ Subgroup.centralizer ({t} : Set G)) := by
    rwa [hcent] at hJx
  have hDpart : CFSG.RankThree.PartOne.IsComponentOf
      (K ⊓ Subgroup.centralizer ({t} : Set G)) J :=
    ⟨hJt.1, (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
      hJt.2.2, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hJt.1).mp hJt.2.1⟩
  have hDq := CFSG.RankThree.PartOne.isComponentOf_map_centerQuotient
    (p := p) hp hcopK htK htp hDpart
  have hDqA : IsComponentOf
      ((J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K)))
      (Subgroup.centralizer
        ({((⟨t, htK⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K)} :
          Set (↥K ⧸ Subgroup.center ↥K))) :=
    ⟨hDq.1, (CFSG.Assembly.IsSubnormal.iff_subgroupOf hDq.1).mpr hDq.2.2,
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr hDq.2.1⟩
  obtain ⟨F, hF, hFfin, hFchar, V, hV, hVmod, hVfd, Q, hF2, hQnd, hdim, ⟨θ⟩⟩ :=
    d_orthModel_of_label hHasK htagK hnK (by omega : 4 ≤ labK.rank)
  let : Field F := hF
  let : Finite F := hFfin
  let : CharP F 2 := hFchar
  let : AddCommGroup V := hV
  let : Module F V := hVmod
  let : FiniteDimensional F V := hVfd
  let R : Type := ↥(CFSG.RankThree.Classical2.orthDerived Q)
  let : Group R := inferInstanceAs (Group ↥(CFSG.RankThree.Classical2.orthDerived Q))
  let ψ : ↥K →* R := θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥K))
  have hψ : Function.Surjective ψ :=
    θ.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center ↥K))
  have hkerψ : ψ.ker = Subgroup.center ↥K := by
    ext z
    rw [MonoidHom.mem_ker]
    show θ ((QuotientGroup.mk' (Subgroup.center ↥K)) z) = 1 ↔ z ∈ Subgroup.center ↥K
    rw [MulEquiv.map_eq_one_iff]
    exact QuotientGroup.eq_one_iff z
  have hkerle : ψ.ker ≤ Subgroup.center ↥K := le_of_eq hkerψ
  have hcopψ : ¬ p ∣ Nat.card ↥ψ.ker := by rw [hkerψ]; exact hcopK
  let E : Subgroup ↥K := (Bs ⊓ K).subgroupOf K
  have hEea : IsElemAbelian p E := hBsEA.mono inf_le_left |>.subgroupOf K
  have hEsc : ∀ g : ↥K, (∀ e ∈ E, g * e = e * g) → g ^ p = 1 → g ∈ E := by
    intro g hg hgp
    rw [Subgroup.mem_subgroupOf]
    refine ⟨?_, g.2⟩
    have hcommBs : ∀ b ∈ Bs, b * (g : G) = (g : G) * b := by
      intro b hb
      obtain ⟨t', ht', c', hc', rfl⟩ := hsplit b hb
      have h1 : t' * (g : G) = (g : G) * t' := by
        have h := hg ⟨t', ht'.2⟩ (Subgroup.mem_subgroupOf.mpr ht')
        exact (congrArg Subtype.val h).symm
      have h2 : c' * (g : G) = (g : G) * c' :=
        (Subgroup.mem_centralizer_iff.mp hc'.2 (g : G) g.2).symm
      calc (t' * c') * (g : G) = t' * (c' * (g : G)) := by group
        _ = t' * ((g : G) * c') := by rw [h2]
        _ = t' * (g : G) * c' := by group
        _ = ((g : G) * t') * c' := by rw [h1]
        _ = (g : G) * (t' * c') := by group
    refine hBsSC (g : G) ?_ ?_
    · exact Subgroup.mem_centralizer_iff.mpr hcommBs
    · simpa only [Subgroup.coe_pow, Subgroup.coe_one] using congrArg Subtype.val hgp
  obtain ⟨hEab, hEsc'⟩ :=
    d_scMap_of_central hp ψ hψ hkerle hcopψ hEea hEsc
  have hEab3 : IsElemAbelian 3 (E.map ψ) := by simpa [hp3] using hEab
  have hEsc3 : ∀ g : R, (∀ e ∈ E.map ψ, g * e = e * g) → g ^ 3 = 1 → g ∈ E.map ψ := by
    simpa [hp3] using hEsc'
  have hDθ : IsComponentOf
      (((J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))).map θ.toMonoidHom)
      ((Subgroup.centralizer
        ({((⟨t, htK⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K)} :
          Set (↥K ⧸ Subgroup.center ↥K))).map θ.toMonoidHom) := by
    refine ⟨Subgroup.map_mono hDqA.1, CFSG.Assembly.IsSubnormal.map θ.toMonoidHom hDqA.2.1,
      ?_⟩
    exact (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mpr
      (CFSG.LocalCores.isQuasisimple_of_mulEquiv
        (Subgroup.equivMapOfInjective _ θ.toMonoidHom θ.injective)
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_native _).mp
          hDqA.2.2))
  have hCmap : (Subgroup.centralizer
        ({((⟨t, htK⟩ : ↥K) : ↥K ⧸ Subgroup.center ↥K)} :
          Set (↥K ⧸ Subgroup.center ↥K))).map θ.toMonoidHom =
      Subgroup.centralizer ({ψ ⟨t, htK⟩} : Set R) := by
    rw [CFSG.GroupTheory.map_centralizer_eq_of_mulEquiv, Set.image_singleton]
    simp [ψ]
  have hJbarEq : (((J.subgroupOf K).map (QuotientGroup.mk' (Subgroup.center ↥K))).map
        θ.toMonoidHom) = (J.subgroupOf K).map ψ := by
    rw [Subgroup.map_map]
  have hJbarComp : IsComponentOf ((J.subgroupOf K).map ψ)
      (Subgroup.centralizer ({ψ ⟨t, htK⟩} : Set R)) := by
    rw [← hJbarEq, ← hCmap]
    exact hDθ
  have hperfSub : Group.IsPerfect ↥(J.subgroupOf K) := by
    have hJperf : Group.IsPerfect ↥J := ⟨hJt.2.2.1⟩
    exact Group.IsPerfect.ofSurjective
      (f := (Subgroup.subgroupOfEquivOfLe hJK).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hJK).symm.surjective
  have hlabel : GGHasLabel labJ (↥((J.subgroupOf K).map ψ) ⧸
      Subgroup.center ↥((J.subgroupOf K).map ψ)) := by
    have hhasSub : GGHasLabel labJ
        (↥(J.subgroupOf K) ⧸ Subgroup.center ↥(J.subgroupOf K)) := by
      obtain ⟨e1⟩ := hdRo7DKSQAux_nonempty_centerQuot_map
        (Subgroup.subtype K) (by rw [Subgroup.ker_subtype]; exact bot_le)
        (J := J.subgroupOf K) hperfSub
      rw [Subgroup.map_subgroupOf_eq_of_le hJK] at e1
      exact ggHasLabel_of_mulEquiv e1.symm hHasJ
    obtain ⟨e2⟩ := hdRo7DKSQAux_nonempty_centerQuot_map
      ψ hkerle (J := J.subgroupOf K) hperfSub
    exact ggHasLabel_of_mulEquiv e2 hhasSub
  have hψtE : ψ ⟨t, htK⟩ ∈ E.map ψ :=
    Subgroup.mem_map.mpr ⟨⟨t, htK⟩, Subgroup.mem_subgroupOf.mpr ht, rfl⟩
  have h9bar : 9 ≤ Nat.card ↥((E.map ψ) ⊓ Subgroup.centralizer
      (((J.subgroupOf K).map ψ) : Set R)) :=
    hT3 hRig F hF2 V Q hQnd labK.rank hdim hr6 (E.map ψ) hEab3 hEsc3 (ψ ⟨t, htK⟩)
      hψtE ((J.subgroupOf K).map ψ) hJbarComp ⟨labJ, hJ2, hlabel, htagJ, hnJ, by omega⟩
  let EK : Subgroup ↥K := E ⊓ Subgroup.centralizer ((J.subgroupOf K) : Set ↥K)
  let EB : Subgroup R := (E.map ψ) ⊓ Subgroup.centralizer (((J.subgroupOf K).map ψ) : Set R)
  have hJcomm : commutator ↥(J.subgroupOf K) = ⊤ := hperfSub.commutator_eq_top
  have hΦ_mem (e : ↥EK) : ψ e ∈ EB := by
    change ψ e ∈ (E.map ψ) ⊓ Subgroup.centralizer (((J.subgroupOf K).map ψ) : Set R)
    refine ⟨Subgroup.mem_map.mpr ⟨e, e.2.1, rfl⟩, ?_⟩
    exact Subgroup.mem_centralizer_iff.mpr (fun y hy => by
      obtain ⟨j, hj, rfl⟩ := Subgroup.mem_map.mp hy
      simpa only [map_mul] using
        congrArg ψ (Subgroup.mem_centralizer_iff.mp e.2.2 j hj))
  let Φ : ↥EK → ↥EB := fun e => ⟨ψ e, hΦ_mem e⟩
  have hΦsurj : Function.Surjective Φ := by
    rintro ⟨y, hy⟩
    change y ∈ (E.map ψ) ⊓
      Subgroup.centralizer (((J.subgroupOf K).map ψ) : Set R) at hy
    obtain ⟨hyE, hyC⟩ := hy
    obtain ⟨e, heE, rfl⟩ := Subgroup.mem_map.mp hyE
    have hecomm : ∀ j ∈ (J.subgroupOf K : Subgroup ↥K), ψ e * ψ j = ψ j * ψ e := by
      intro j hj
      exact (Subgroup.mem_centralizer_iff.mp hyC (ψ j)
        (Subgroup.mem_map.mpr ⟨j, hj, rfl⟩)).symm
    have heC : e ∈ Subgroup.centralizer ((J.subgroupOf K) : Set ↥K) :=
      Subgroup.mem_centralizer_iff.mpr
        (fun j hj => (d_centralizer_lift ψ hkerle hJcomm hecomm j hj).symm)
    refine ⟨⟨e, heE, heC⟩, ?_⟩
    exact Subtype.ext rfl
  have hcardEK : Nat.card ↥EB ≤ Nat.card ↥EK :=
    Nat.card_le_card_of_surjective Φ hΦsurj
  let AG : Subgroup G := (Bs ⊓ K) ⊓ Subgroup.centralizer (J : Set G)
  have hmapEK : EK.map K.subtype = AG := by
    ext z
    constructor
    · rintro ⟨a, ha, rfl⟩
      obtain ⟨haE, haC⟩ := ha
      refine ⟨(Subgroup.mem_subgroupOf.mp haE), ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr (fun j hj => ?_)
      have h := Subgroup.mem_centralizer_iff.mp haC ⟨j, hJK hj⟩
        (Subgroup.mem_subgroupOf.mpr hj)
      exact congrArg Subtype.val h
    · rintro ⟨hzE, hzC⟩
      refine ⟨⟨z, hzE.2⟩, ⟨Subgroup.mem_subgroupOf.mpr hzE, ?_⟩, rfl⟩
      refine Subgroup.mem_centralizer_iff.mpr (fun j hj => ?_)
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC (j : G)
        (Subgroup.mem_subgroupOf.mp hj))
  have hcardAG : Nat.card ↥AG = Nat.card ↥EK := by
    rw [← hmapEK, Subgroup.card_map_of_injective (Subgroup.subtype_injective K)]
  have h9 : 9 ≤ Nat.card ↥AG := by
    calc 9 ≤ Nat.card ↥EB := h9bar
      _ ≤ Nat.card ↥EK := hcardEK
      _ = Nat.card ↥AG := hcardAG.symm
  let Bc : Subgroup G := Bs ⊓ Subgroup.centralizer (K : Set G)
  let Cc : Subgroup G := Bs ⊓ Subgroup.centralizer (J : Set G)
  have htriv : (Bs ⊓ K) ⊓ Subgroup.centralizer (K : Set G) = ⊥ := by
    rw [Subgroup.eq_bot_iff_forall]
    intro z hz
    obtain ⟨⟨hzBs, hzK⟩, hzC⟩ := hz
    have hzKq : (⟨z, hzK⟩ : ↥K) ∈ Subgroup.center ↥K := by
      rw [Subgroup.mem_center_iff]
      intro w
      exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hzC (w : G) w.2)
    have h1 : orderOf (⟨z, hzK⟩ : ↥K) ∣ Nat.card (Subgroup.center ↥K) :=
      Subgroup.orderOf_dvd_natCard _ hzKq
    have h2 : orderOf (⟨z, hzK⟩ : ↥K) ∣ p := by
      rw [orderOf_dvd_iff_pow_eq_one]
      exact Subtype.ext (by simpa using hBsEA.2 z hzBs)
    have h3 : orderOf (⟨z, hzK⟩ : ↥K) = 1 := by
      rcases (Nat.dvd_prime hp).mp h2 with h | h
      · exact h
      · exfalso
        apply hcopK
        rw [← h]
        exact h1
    have h4 : (⟨z, hzK⟩ : ↥K) = 1 := orderOf_eq_one_iff.mp h3
    simpa using congrArg Subtype.val h4
  have hA_le_C : AG ≤ Cc := by
    rintro z ⟨hzE, hzC⟩
    exact ⟨hzE.1, hzC⟩
  have hB_le_C : Bc ≤ Cc := by
    rintro z ⟨hzBs, hzC⟩
    exact ⟨hzBs, Subgroup.centralizer_le (by intro j hj; exact hJK hj) hzC⟩
  let Ψ : ↥AG × ↥Bc → ↥Cc := fun q =>
    ⟨q.1.1 * q.2.1, by
      refine ⟨Bs.mul_mem (hA_le_C q.1.2).1 (hB_le_C q.2.2).1, ?_⟩
      refine Subgroup.mem_centralizer_iff.mpr (fun j hj => ?_)
      have h1 : j * q.1.1 = q.1.1 * j :=
        Subgroup.mem_centralizer_iff.mp (hA_le_C q.1.2).2 j hj
      have h2 : j * q.2.1 = q.2.1 * j :=
        Subgroup.mem_centralizer_iff.mp (hB_le_C q.2.2).2 j hj
      calc j * (q.1.1 * q.2.1) = j * q.1.1 * q.2.1 := by group
        _ = q.1.1 * j * q.2.1 := by rw [h1]
        _ = q.1.1 * (j * q.2.1) := by group
        _ = q.1.1 * (q.2.1 * j) := by rw [h2]
        _ = q.1.1 * q.2.1 * j := by group⟩
  have hΨinj : Function.Injective Ψ := by
    intro q r hqr
    have hval : q.1.1 * q.2.1 = r.1.1 * r.2.1 := congrArg Subtype.val hqr
    have hz : r.1.1⁻¹ * q.1.1 = r.2.1 * q.2.1⁻¹ := by
      calc r.1.1⁻¹ * q.1.1 = r.1.1⁻¹ * (q.1.1 * q.2.1) * q.2.1⁻¹ := by group
        _ = r.1.1⁻¹ * (r.1.1 * r.2.1) * q.2.1⁻¹ := by rw [hval]
        _ = r.2.1 * q.2.1⁻¹ := by group
    have hzK : r.1.1⁻¹ * q.1.1 ∈ Bs ⊓ K := by
      refine ⟨?_, ?_⟩
      · exact Bs.mul_mem (Bs.inv_mem (Subgroup.mem_inf.mp r.1.2.1).1)
          (Subgroup.mem_inf.mp q.1.2.1).1
      · exact K.mul_mem (K.inv_mem (Subgroup.mem_inf.mp r.1.2.1).2)
          (Subgroup.mem_inf.mp q.1.2.1).2
    have hzC : r.2.1 * q.2.1⁻¹ ∈ Subgroup.centralizer (K : Set G) :=
      (Subgroup.centralizer (K : Set G)).mul_mem r.2.2.2
        ((Subgroup.centralizer (K : Set G)).inv_mem q.2.2.2)
    have hzbot : r.1.1⁻¹ * q.1.1 ∈ (Bs ⊓ K) ⊓ Subgroup.centralizer (K : Set G) :=
      ⟨hzK, by rw [hz]; exact hzC⟩
    rw [htriv, Subgroup.mem_bot] at hzbot
    have h1 : r.1.1 = q.1.1 := by
      have := congrArg (fun w => r.1.1 * w) hzbot
      simpa [mul_assoc] using this.symm
    have h2 : r.2.1 = q.2.1 := by
      rw [h1] at hval
      exact (mul_left_cancel hval).symm
    exact Prod.ext (Subtype.ext h1.symm) (Subtype.ext h2.symm)
  have hcount : Nat.card ↥AG * Nat.card ↥Bc ≤ Nat.card ↥Cc := by
    calc Nat.card ↥AG * Nat.card ↥Bc = Nat.card (↥AG × ↥Bc) := (Nat.card_prod _ _).symm
      _ ≤ Nat.card ↥Cc := Nat.card_le_card_of_injective Ψ hΨinj
  have hCc : Nat.card ↥Cc ≤ p ^ 3 := d_card_bstar_centralizer_J_le hHcopy
  have hBc3 : Nat.card ↥Bc ≤ 3 := by
    have h1 : 9 * Nat.card ↥Bc ≤ p ^ 3 :=
      le_trans (Nat.mul_le_mul_right _ h9) (le_trans hcount hCc)
    have hp27 : p ^ 3 = 27 := by rw [hp3]; norm_num
    rw [hp27] at h1
    omega
  have hyB : y ∈ Bc := by
    refine ⟨hBsB hnbr.1.2.1, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr (fun k hk => ?_)
    exact (Subgroup.mem_centralizer_iff.mp (hnbr.1.2.2.2.1 hk) y
      (Set.mem_singleton y)).symm
  have hypow : y ^ p = 1 := hBsEA.2 y (hBsB hnbr.1.2.1)
  have hyne : y ≠ 1 := hnbr.1.2.2.1
  have hzy : Subgroup.zpowers y ≤ Bc := Subgroup.zpowers_le.mpr hyB
  have hzycard : Nat.card ↥(Subgroup.zpowers y) = p := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hypow hyne
  have hBcle : Nat.card ↥Bc ≤ Nat.card ↥(Subgroup.zpowers y) := by
    rw [hzycard]; omega
  exact (Subgroup.eq_of_le_of_card_ge hzy hBcle).symm

end CFSG.StandardType.HdRo7D

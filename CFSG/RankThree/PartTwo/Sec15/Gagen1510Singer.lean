module

public import CFSG.RankThree.PartTwo.Sec4.Notation
public import CFSG.LocalAnalysis.ComponentInitial.GL3TwoFixedModelCases
import CFSG.RankThree.PartTwo.Sec15.Item1510StepsProofTools
import CFSG.RankThree.PartTwo.KFacts.L34Centralizers
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.LocalRank
open CFSG.LocalAnalysis.ComponentInitial

variable {G : Type} [Group G] [Finite G]

private noncomputable abbrev sC (c : G) : Subgroup G :=
  Subgroup.centralizer ({c} : Set G)

private noncomputable abbrev sK (c : G) : Subgroup (sC c) := centralLine c

private noncomputable abbrev sPi (c : G) : sC c →* sC c ⧸ sK c :=
  QuotientGroup.mk' (sK c)

private noncomputable abbrev sThetaL (L : Subgroup G) : Subgroup ↥L :=
  aschbacherSolvableCore 3 ↥L

private noncomputable abbrev sKappa (L : Subgroup G) : ↥L →* ↥L ⧸ sThetaL L :=
  QuotientGroup.mk' (sThetaL L)

private noncomputable abbrev sRho (L : Subgroup G) (e : G)
    (heN : e ∈ Subgroup.normalizer (L : Set G)) : MulAut (↥L ⧸ sThetaL L) :=
  Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩)

private noncomputable abbrev sY (L : Subgroup G) (e : G)
    (heN : e ∈ Subgroup.normalizer (L : Set G)) : Subgroup ↥L :=
  (inSubgroup (aschbacherSolvableCore 3) (GL3TwoFixedModel.autFixed (sRho L e heN))).comap
      (sKappa L) ⊓
    (Subgroup.centralizer ({e} : Set G)).subgroupOf L

private noncomputable abbrev sIota (L : Subgroup G) {c : G} (hLc : L ≤ sC c) : ↥L →* sC c :=
  Subgroup.inclusion hLc

private noncomputable abbrev sY' (L : Subgroup G) {c : G} (hLc : L ≤ sC c) (e : G)
    (heN : e ∈ Subgroup.normalizer (L : Set G)) : Subgroup (sC c) :=
  (sY L e heN).map (sIota L hLc)

private noncomputable abbrev sHt (c e : G) (he : e ∈ sC c) : Subgroup (sC c ⧸ sK c) :=
  Subgroup.centralizer ({sPi c ⟨e, he⟩} : Set (sC c ⧸ sK c))

private noncomputable abbrev sH' (c e : G) (he : e ∈ sC c) : Subgroup (sC c) :=
  (sHt c e he).comap (sPi c)

private noncomputable abbrev sYim' (L : Subgroup G) {c : G} (hLc : L ≤ sC c) (e : G)
    (heN : e ∈ Subgroup.normalizer (L : Set G)) : Subgroup (sC c ⧸ sK c) :=
  (sY' L hLc e heN).map (sPi c)

private noncomputable abbrev sF (c e : G) (he : e ∈ sC c) : sH' c e he →* sHt c e he :=
  ((sPi c).comp (sH' c e he).subtype).codRestrict (sHt c e he) (fun x => x.2)

private lemma centralizer_singleton_mul_mem_center {H : Type*} [Group H] {e z : H}
    (hz : z ∈ Subgroup.center H) :
    Subgroup.centralizer ({e * z} : Set H) = Subgroup.centralizer ({e} : Set H) := by
  ext x
  rw [Subgroup.mem_centralizer_singleton_iff, Subgroup.mem_centralizer_singleton_iff]
  have hz' : x * z = z * x := Subgroup.mem_center_iff.mp hz x
  constructor
  · intro h
    calc x * e = x * e * z * z⁻¹ := by group
      _ = x * (e * z) * z⁻¹ := by group
      _ = (e * z) * x * z⁻¹ := by rw [h]
      _ = e * (z * x) * z⁻¹ := by group
      _ = e * (x * z) * z⁻¹ := by rw [← hz']
      _ = e * x := by group
  · intro h
    calc x * (e * z) = x * e * z := by group
      _ = e * x * z := by rw [h]
      _ = e * (x * z) := by group
      _ = e * (z * x) := by rw [hz']
      _ = e * z * x := by group

private lemma card_map_eq_of_ker_subgroupOf_eq_bot {X Y : Type*} [Group X] [Group Y] [Finite X]
    (f : X →* Y) (H : Subgroup X) (h : f.ker.subgroupOf H = ⊥) :
    Nat.card (H.map f) = Nat.card H := by
  have hcard := CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.card_map_mul_card_ker_subgroupOf f H
  have h1 : Nat.card (f.ker.subgroupOf H) = 1 := (Subgroup.card_eq_one).mpr h
  rw [h1, mul_one] at hcard
  exact hcard

private lemma sRho_conj_eq {L : Subgroup G} {e g z : G}
    (heN : e ∈ Subgroup.normalizer (L : Set G))
    (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (hzN : z ∈ Subgroup.normalizer (L : Set G))
    (hge : g * e * g⁻¹ = z * e)
    (hzL : ∀ x : ↥L, z * (x : G) * z⁻¹ = (x : G)) :
    sRho L g hgN * sRho L e heN * (sRho L g hgN)⁻¹ = sRho L e heN := by
  let N : Subgroup G := Subgroup.normalizer (L : Set G)
  let ρtot : N →* MulAut (↥L ⧸ sThetaL L) :=
    (Sec4.thetaQuotMulAut ↥L).comp L.normalizerMonoidHom
  have h1 : (⟨g, hgN⟩ : N) * ⟨e, heN⟩ * ⟨g, hgN⟩⁻¹ = ⟨z, hzN⟩ * ⟨e, heN⟩ := by
    apply Subtype.ext
    change g * e * g⁻¹ = z * e
    exact hge
  have h2 : ρtot ⟨z, hzN⟩ = 1 := by
    have hz_normHom : L.normalizerMonoidHom ⟨z, hzN⟩ = 1 := by
      ext x
      rw [Sec4.normalizerMonoidHom_apply_coe]
      exact hzL x
    change Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨z, hzN⟩) = 1
    rw [hz_normHom, map_one]
  calc sRho L g hgN * sRho L e heN * (sRho L g hgN)⁻¹
      = ρtot ⟨g, hgN⟩ * ρtot ⟨e, heN⟩ * (ρtot ⟨g, hgN⟩)⁻¹ := rfl
    _ = ρtot (⟨g, hgN⟩ * ⟨e, heN⟩ * ⟨g, hgN⟩⁻¹) := by rw [map_mul, map_mul, map_inv]
    _ = ρtot (⟨z, hzN⟩ * ⟨e, heN⟩) := by rw [h1]
    _ = ρtot ⟨z, hzN⟩ * ρtot ⟨e, heN⟩ := by rw [map_mul]
    _ = 1 * sRho L e heN := by rw [h2]; rfl
    _ = sRho L e heN := one_mul _

private lemma sRho_mem_theta_of_conj_eq {L : Subgroup G} {e g z : G}
    (heN : e ∈ Subgroup.normalizer (L : Set G))
    (hgN : g ∈ Subgroup.normalizer (L : Set G))
    (hzN : z ∈ Subgroup.normalizer (L : Set G))
    (hge : g * e * g⁻¹ = z * e)
    (hzL : ∀ x : ↥L, z * (x : G) * z⁻¹ = (x : G)) :
    ∀ {w : ↥L ⧸ sThetaL L},
      w ∈ inSubgroup (aschbacherSolvableCore 3)
        (GL3TwoFixedModel.autFixed (sRho L e heN)) →
      sRho L g hgN w ∈ inSubgroup (aschbacherSolvableCore 3)
        (GL3TwoFixedModel.autFixed (sRho L e heN)) := by
  have hρcomm : sRho L g hgN * sRho L e heN * (sRho L g hgN)⁻¹ = sRho L e heN :=
    sRho_conj_eq heN hgN hzN hge hzL
  have hfix_map : (GL3TwoFixedModel.autFixed (sRho L e heN)).map
      (sRho L g hgN).toMonoidHom = GL3TwoFixedModel.autFixed (sRho L e heN) := by
    have h1 := CFSG.RankThree.PartTwo.KFacts.L34.autFixed_conj
      (sRho L g hgN) (sRho L e heN)
    rw [hρcomm] at h1
    exact h1.symm
  have htheta_map : (inSubgroup (aschbacherSolvableCore 3)
        (GL3TwoFixedModel.autFixed (sRho L e heN))).map
        (sRho L g hgN).toMonoidHom =
      inSubgroup (aschbacherSolvableCore 3)
        (GL3TwoFixedModel.autFixed (sRho L e heN)) := by
    rw [CFSG.RankThree.PartTwo.map_inSubgroup_aschbacherSolvableCore, hfix_map]
  intro w hw
  rw [← htheta_map]
  exact Subgroup.mem_map_of_mem (sRho L g hgN).toMonoidHom hw

private lemma centralizer_conj_eq_of_mem_center {X : Type*} [Group X] {e z : X}
    (hz : z ∈ Subgroup.center X) {g : X} (hge : g * e * g⁻¹ = e * z) :
    (Subgroup.centralizer ({e} : Set X)).map (MulAut.conj g).toMonoidHom =
      Subgroup.centralizer ({e} : Set X) := by
  rw [CFSG.RankThree.PartTwo.map_centralizer_singleton]
  rw [show (MulAut.conj g) e = e * z by rw [MulAut.conj_apply, hge]]
  exact centralizer_singleton_mul_mem_center hz

private lemma sHt_exists_central {L : Subgroup G} {c e : G} {heC : e ∈ sC c}
    (hLc : L ≤ sC c) (hCN : sC c ≤ Subgroup.normalizer (L : Set G))
    (heN : e ∈ Subgroup.normalizer (L : Set G))
    (g : sC c) (hg : sPi c g ∈ sHt c e heC) :
    ∃ z0 : sC c, z0 ∈ Subgroup.center (sC c) ∧
      (g : sC c) * ⟨e, heC⟩ * (g : sC c)⁻¹ = z0 * ⟨e, heC⟩ ∧
      (∀ x : ↥L, (z0 : sC c).val * (x : G) * (z0 : sC c).val⁻¹ = (x : G)) := by
  have hgz_mem : (g : sC c) * ⟨e, heC⟩ * (g : sC c)⁻¹ * ⟨e, heC⟩⁻¹ ∈ sK c := by
    have hg' : sPi c (g : sC c) * sPi c ⟨e, heC⟩ =
        sPi c ⟨e, heC⟩ * sPi c (g : sC c) := by
      have hgmem : sPi c (g : sC c) ∈
          Subgroup.centralizer ({sPi c ⟨e, heC⟩} : Set (sC c ⧸ sK c)) := hg
      rwa [Subgroup.mem_centralizer_singleton_iff] at hgmem
    have h1 : sPi c ((g : sC c) * ⟨e, heC⟩ * (g : sC c)⁻¹ * ⟨e, heC⟩⁻¹) = 1 := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv, hg']
      group
    rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  set z0 : sC c := (g : sC c) * ⟨e, heC⟩ * (g : sC c)⁻¹ * ⟨e, heC⟩⁻¹ with hz0def
  have hz0K : z0 ∈ sK c := hgz_mem
  have hz0_center : z0 ∈ Subgroup.center (sC c) := by
    rw [sK] at hz0K
    exact centralLine_le_center c hz0K
  have hge : (g : sC c) * ⟨e, heC⟩ * (g : sC c)⁻¹ = z0 * ⟨e, heC⟩ := by
    rw [hz0def]
    group
  have hz0L : ∀ x : ↥L, (z0 : sC c).val * (x : G) * (z0 : sC c).val⁻¹ = (x : G) := by
    intro x
    have hx : (z0 : sC c) * sIota L hLc x = sIota L hLc x * z0 :=
      (Subgroup.mem_center_iff.mp hz0_center (sIota L hLc x)).symm
    have hx' : (z0 : sC c).val * (x : G) = (x : G) * (z0 : sC c).val :=
      congrArg Subtype.val hx
    rw [hx', mul_assoc, mul_inv_cancel, mul_one]
  exact ⟨z0, hz0_center, hge, hz0L⟩

private lemma sY_conj_mem {L : Subgroup G} {c e : G} {heC : e ∈ sC c}
    (hLc : L ≤ sC c) (hCN : sC c ≤ Subgroup.normalizer (L : Set G))
    (heN : e ∈ Subgroup.normalizer (L : Set G))
    (g : sC c) (hg : sPi c g ∈ sHt c e heC)
    {l : ↥L} (hl : l ∈ sY L e heN) :
    ∃ l' ∈ sY L e heN, sIota L hLc l' = g * sIota L hLc l * g⁻¹ := by
  obtain ⟨z0, hz0_center, hge, hz0L⟩ := sHt_exists_central hLc hCN heN g hg
  have hgN : (g : sC c).val ∈ Subgroup.normalizer (L : Set G) := hCN (g : sC c).2
  have hge'' : (g : sC c) * ⟨e, heC⟩ * (g : sC c)⁻¹ = ⟨e, heC⟩ * z0 := by
    rw [hge]
    exact (Subgroup.mem_center_iff.mp hz0_center ⟨e, heC⟩).symm
  have hcent_map : (Subgroup.centralizer ({⟨e, heC⟩} : Set (sC c))).map
      (MulAut.conj (g : sC c)).toMonoidHom =
      Subgroup.centralizer ({⟨e, heC⟩} : Set (sC c)) :=
    centralizer_conj_eq_of_mem_center hz0_center hge''
  have hl'_mem : (g : sC c).val * (l : G) * (g : sC c).val⁻¹ ∈ L :=
    (Subgroup.mem_normalizer_iff.mp hgN (l : G)).mp l.2
  let l' : ↥L := ⟨(g : sC c).val * (l : G) * (g : sC c).val⁻¹, hl'_mem⟩
  have hιl' : sIota L hLc l' = (g : sC c) * sIota L hLc l * (g : sC c)⁻¹ := Subtype.ext rfl
  have hρg_mk_l : (QuotientGroup.mk' (sThetaL L)) l' =
      sRho L (g : sC c).val hgN ((l : ↥L) : ↥L ⧸ sThetaL L) := by
    rw [Sec4.thetaQuotMulAut_mk]
    congr 1
  have hl'_Y : l' ∈ sY L e heN := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · rw [Subgroup.mem_comap, hρg_mk_l]
      exact sRho_mem_theta_of_conj_eq heN hgN (hCN z0.2) (congrArg Subtype.val hge) hz0L
        (Subgroup.mem_comap.mp (Subgroup.mem_inf.mp hl).1)
    · rw [Subgroup.mem_subgroupOf]
      have hl_centG : (l : G) ∈ Subgroup.centralizer ({e} : Set G) :=
        Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hl).2
      have hl_cent : sIota L hLc l ∈
          Subgroup.centralizer ({⟨e, heC⟩} : Set (sC c)) := by
        rw [Subgroup.mem_centralizer_singleton_iff]
        apply Subtype.ext
        exact Subgroup.mem_centralizer_singleton_iff.mp hl_centG
      have hl'_centC : sIota L hLc l' ∈
          Subgroup.centralizer ({⟨e, heC⟩} : Set (sC c)) := by
        have h := Subgroup.mem_map_of_mem (MulAut.conj (g : sC c)).toMonoidHom hl_cent
        rw [hcent_map] at h
        have h' : (MulAut.conj (g : sC c)) (sIota L hLc l) ∈
            Subgroup.centralizer ({⟨e, heC⟩} : Set (sC c)) := h
        rw [MulAut.conj_apply] at h'
        rwa [← hιl'] at h'
      rw [Subgroup.mem_centralizer_singleton_iff]
      exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.mp hl'_centC)
  exact ⟨l', hl'_Y, hιl'⟩

private lemma sY'_normal {L A' : Subgroup G} {c e : G}
    (hLc : L ≤ sC c) (hCN : sC c ≤ Subgroup.normalizer (L : Set G))
    (hA'c : A' ≤ sC c) (heA : e ∈ A') (heN : e ∈ Subgroup.normalizer (L : Set G)) :
    (sY' L hLc e heN).subgroupOf (sH' c e (hA'c heA)) |>.Normal := by
  refine ⟨fun z hz g => ?_⟩
  have hzY' : (z : sC c) ∈ sY' L hLc e heN := Subgroup.mem_subgroupOf.mp hz
  obtain ⟨l, hlY, hlz⟩ := Subgroup.mem_map.mp hzY'
  obtain ⟨l', hl'Y, hl'eq⟩ := sY_conj_mem hLc hCN heN (g : sC c) g.2 hlY
  apply Subgroup.mem_subgroupOf.mpr
  change (g : sC c) * (z : sC c) * (g : sC c)⁻¹ ∈ sY' L hLc e heN
  rw [← hlz, ← hl'eq]
  exact Subgroup.mem_map_of_mem (sIota L hLc) hl'Y

private lemma isSolvable_of_map_le_theta {L : Subgroup G} {Y : Subgroup ↥L}
    {W : Subgroup (↥L ⧸ sThetaL L)}
    (hY : Y.map (sKappa L) ≤ inSubgroup (aschbacherSolvableCore 3) W) :
    Group.IsSolvable ↥Y := by
  let θL := sThetaL L
  let κ := sKappa L
  let Yim : Subgroup (↥L ⧸ θL) := Y.map κ
  have hYim_le : Yim ≤ inSubgroup (aschbacherSolvableCore 3) W := hY
  haveI hThetaSolv : Group.IsSolvable ↥(inSubgroup (aschbacherSolvableCore 3) W) :=
    Sec15.Proof1510Steps.isSolvable_theta W
  haveI hYim_solv : Group.IsSolvable ↥Yim :=
    Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hYim_le)
      (Subgroup.inclusion_injective hYim_le)
  haveI hker_solv : Group.IsSolvable ↥(Y ⊓ θL) := by
    haveI : Group.IsSolvable ↥θL :=
      (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).1
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion (inf_le_right : Y ⊓ θL ≤ θL))
      (Subgroup.inclusion_injective (inf_le_right : Y ⊓ θL ≤ θL))
  let gY : Y →* Yim :=
    (κ.comp Y.subtype).codRestrict Yim (fun y => Subgroup.mem_map_of_mem κ y.2)
  have hgY_ker : gY.ker = (Y ⊓ θL).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    constructor
    · intro h
      have h1 : κ (y : ↥L) = 1 := by
        have := congrArg Subtype.val h
        simpa [gY] using this
      have h1' : (QuotientGroup.mk' θL) (y : ↥L) = 1 := h1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1'
      exact ⟨y.2, h1'⟩
    · rintro ⟨hyY, hyθ⟩
      apply Subtype.ext
      show κ (y : ↥L) = 1
      change (QuotientGroup.mk' θL) (y : ↥L) = 1
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hyθ
  have hfY_range : (Subgroup.inclusion (inf_le_left : Y ⊓ θL ≤ Y)).range =
      (Y ⊓ θL).subgroupOf Y := by
    ext y
    rw [MonoidHom.mem_range, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hy
      exact ⟨⟨y, hy⟩, rfl⟩
  exact Group.isSolvable_of_ker_le_range (Subgroup.inclusion inf_le_left) gY
    (by rw [hgY_ker, hfY_range])

private lemma not_three_dvd_card_of_map_le_theta {L : Subgroup G} {Y : Subgroup ↥L}
    {W : Subgroup (↥L ⧸ sThetaL L)}
    (hY : Y.map (sKappa L) ≤ inSubgroup (aschbacherSolvableCore 3) W) :
    ¬ 3 ∣ Nat.card Y := by
  let θL := sThetaL L
  let κ := sKappa L
  let Yim : Subgroup (↥L ⧸ θL) := Y.map κ
  have hYim_3 : ¬ 3 ∣ Nat.card Yim := by
    intro h
    exact Sec15.Proof1510Steps.not_three_dvd_card_theta W
      (h.trans (Subgroup.card_dvd_of_le hY))
  have hcard := CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.card_map_mul_card_ker_subgroupOf κ Y
  have hcard' : Nat.card Yim * Nat.card ((QuotientGroup.mk' θL).ker.subgroupOf Y) =
      Nat.card Y := hcard
  rw [QuotientGroup.ker_mk'] at hcard'
  have hker_3 : ¬ 3 ∣ Nat.card (θL.subgroupOf Y) := by
    intro hk3
    apply (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.1
    have hdvd : Nat.card (θL.subgroupOf Y) ∣ Nat.card θL := by
      have h1 : Nat.card (Subgroup.map Y.subtype (θL.subgroupOf Y)) =
          Nat.card (θL.subgroupOf Y) :=
        Subgroup.card_map_of_injective Y.subtype_injective
      rw [Subgroup.subgroupOf_map_subtype] at h1
      rw [← h1]
      exact Subgroup.card_dvd_of_le inf_le_left
    exact hk3.trans hdvd
  intro h3
  rw [← hcard'] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · exact hYim_3 h
  · exact hker_3 h

private lemma sY'_inf_K {L : Subgroup G} {c : G} (hLc : L ≤ sC c)
    (hcL : c ∉ L) (hc3 : orderOf c = 3) (e : G)
    (heN : e ∈ Subgroup.normalizer (L : Set G)) :
    sY' L hLc e heN ⊓ sK c = ⊥ := by
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  apply Subtype.ext
  obtain ⟨l, hl, hlx⟩ := Subgroup.mem_map.mp hx.1
  have hxL : (x : sC c).val ∈ L := by
    rw [← hlx]
    exact l.2
  have hxK : (x : sC c).val ∈ Subgroup.zpowers c := by
    rw [sK, centralLine] at hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx.2
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
  have hmem : (x : sC c).val ∈ L ⊓ Subgroup.zpowers c := ⟨hxL, hxK⟩
  rw [inf_comm, CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.zpowers_inf_eq_bot_of_not_mem
    hc3 hcL] at hmem
  exact Subgroup.mem_bot.mp hmem

private lemma sYim'_card {L : Subgroup G} {c : G} (hLc : L ≤ sC c)
    (hcL : c ∉ L) (hc3 : orderOf c = 3) (e : G)
    (heN : e ∈ Subgroup.normalizer (L : Set G)) :
    Nat.card (sYim' L hLc e heN) = Nat.card (sY' L hLc e heN) := by
  have hker : (sPi c).ker.subgroupOf (sY' L hLc e heN) = ⊥ := by
    rw [show (sPi c).ker = sK c from QuotientGroup.ker_mk' (sK c)]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply Subtype.ext
    have hmem : (x : sC c) ∈ sY' L hLc e heN ⊓ sK c :=
      ⟨x.2, Subgroup.mem_subgroupOf.mp hx⟩
    rw [sY'_inf_K hLc hcL hc3 e heN] at hmem
    exact Subgroup.mem_bot.mp hmem
  exact card_map_eq_of_ker_subgroupOf_eq_bot (sPi c) (sY' L hLc e heN) hker

private lemma sY'_le_sH' {L : Subgroup G} {c e : G} (he : e ∈ sC c)
    (hLc : L ≤ sC c) (heN : e ∈ Subgroup.normalizer (L : Set G)) :
    sY' L hLc e heN ≤ sH' c e he := by
  intro z hz
  rw [Subgroup.mem_comap]
  obtain ⟨l, hl, rfl⟩ := Subgroup.mem_map.mp hz
  change sPi c (sIota L hLc l) ∈
    Subgroup.centralizer ({sPi c ⟨e, he⟩} : Set (sC c ⧸ sK c))
  rw [Subgroup.mem_centralizer_singleton_iff]
  have hle : (l : G) ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_subgroupOf.mp (Subgroup.mem_inf.mp hl).2
  have hcomm : sIota L hLc l * ⟨e, he⟩ = ⟨e, he⟩ * sIota L hLc l := by
    apply Subtype.ext
    exact Subgroup.mem_centralizer_singleton_iff.mp hle
  have := congrArg (sPi c) hcomm
  simpa only [map_mul] using this

private lemma sF_surj {c e : G} (he : e ∈ sC c) : Function.Surjective (sF c e he) := by
  intro h
  obtain ⟨g, hg⟩ := QuotientGroup.mk'_surjective (sK c) (h : sC c ⧸ sK c)
  have hgH' : g ∈ sH' c e he := by
    rw [Subgroup.mem_comap, hg]
    exact h.2
  refine ⟨⟨g, hgH'⟩, ?_⟩
  apply Subtype.ext
  exact hg

private lemma sF_map_subgroupOf {L : Subgroup G} {c e : G} (he : e ∈ sC c)
    (hLc : L ≤ sC c) (heN : e ∈ Subgroup.normalizer (L : Set G)) :
    ((sY' L hLc e heN).subgroupOf (sH' c e he)).map (sF c e he) =
      (sYim' L hLc e heN).subgroupOf (sHt c e he) := by
  ext h
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_map_of_mem (sPi c) (Subgroup.mem_subgroupOf.mp hy))
  · intro hh
    obtain ⟨y, hy, hyh⟩ := Subgroup.mem_map.mp (Subgroup.mem_subgroupOf.mp hh)
    have hyH' : y ∈ sH' c e he := by
      rw [Subgroup.mem_comap, hyh]
      exact h.2
    refine ⟨⟨y, hyH'⟩, Subgroup.mem_subgroupOf.mpr hy, ?_⟩
    exact Subtype.ext hyh

private lemma sYim'_subgroupOf_le_theta {L A' : Subgroup G} {c e : G}
    (hLc : L ≤ sC c) (hcL : c ∉ L) (hc3 : orderOf c = 3)
    (hCN : sC c ≤ Subgroup.normalizer (L : Set G))
    (hA'c : A' ≤ sC c) (heA : e ∈ A') (heN : e ∈ Subgroup.normalizer (L : Set G)) :
    (sYim' L hLc e heN).subgroupOf (sHt c e (hA'c heA)) ≤
      aschbacherSolvableCore 3 ↥(sHt c e (hA'c heA)) := by
  let Y := sY L e heN
  let Y' := sY' L hLc e heN
  let Yim' := sYim' L hLc e heN
  let Ht := sHt c e (hA'c heA)
  let H' := sH' c e (hA'c heA)
  let f : H' →* Ht := sF c e (hA'c heA)
  have hY'H' : Y' ≤ H' := sY'_le_sH' (hA'c heA) hLc heN
  have hYim'_le : Yim' ≤ Ht := Subgroup.map_le_iff_le_comap.mpr hY'H'
  have hY'normal : (Y'.subgroupOf H').Normal :=
    sY'_normal hLc hCN hA'c heA heN
  have hYim_le : Y.map (sKappa L) ≤
      inSubgroup (aschbacherSolvableCore 3) (GL3TwoFixedModel.autFixed (sRho L e heN)) := by
    rw [Subgroup.map_le_iff_le_comap]
    exact inf_le_left
  have hY_solv : Group.IsSolvable ↥Y := isSolvable_of_map_le_theta hYim_le
  have hY_3 : ¬ 3 ∣ Nat.card Y := not_three_dvd_card_of_map_le_theta hYim_le
  haveI hY'_solv : Group.IsSolvable ↥Y' :=
    Group.isSolvable_of_surjective (f := (sIota L hLc).subgroupMap Y)
      (MonoidHom.subgroupMap_surjective _ _)
  have hY'_3 : ¬ 3 ∣ Nat.card Y' := by
    rw [show Y' = Y.map (sIota L hLc) from rfl,
      Subgroup.card_map_of_injective (Subgroup.inclusion_injective hLc)]
    exact hY_3
  haveI hYim'_solv : Group.IsSolvable ↥Yim' :=
    Group.isSolvable_of_surjective (f := (sPi c).subgroupMap Y')
      (MonoidHom.subgroupMap_surjective _ _)
  have hYim'_3 : ¬ 3 ∣ Nat.card Yim' := by
    rw [sYim'_card hLc hcL hc3 e heN]
    exact hY'_3
  let YH : Subgroup Ht := Yim'.subgroupOf Ht
  have hf_surj : Function.Surjective f := sF_surj (hA'c heA)
  have hYH_eq : (Y'.subgroupOf H').map f = YH :=
    sF_map_subgroupOf (hA'c heA) hLc heN
  haveI hYH_solv : Group.IsSolvable ↥YH :=
    Group.isSolvable_of_isSolvable_injective
      (f := (Subgroup.subgroupOfEquivOfLe hYim'_le).toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hYim'_le).injective
  have hYH_3 : ¬ 3 ∣ Nat.card YH := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hYim'_le).toEquiv]
    exact hYim'_3
  have hYH_normal : YH.Normal := by
    have hmap := Subgroup.Normal.map hY'normal f hf_surj
    rwa [hYH_eq] at hmap
  exact (solvable_prime_complement_core_characterization (H := ↥Ht) Nat.prime_three).2.2.2.1
    YH hYH_normal hYH_solv hYH_3

private lemma sY_ybar_theta {L A' : Subgroup G} {c e y : G}
    (hLc : L ≤ sC c) (hcL : c ∉ L) (hc3 : orderOf c = 3)
    (hCN : sC c ≤ Subgroup.normalizer (L : Set G))
    (hA'c : A' ≤ sC c) (heA : e ∈ A') (heN : e ∈ Subgroup.normalizer (L : Set G))
    (hyL : y ∈ L) (hye : e * y = y * e)
    (hs : ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L) ∈
      inSubgroup (aschbacherSolvableCore 3) (GL3TwoFixedModel.autFixed (sRho L e heN)))
    (hyY : (⟨y, hyL⟩ : ↥L) ∈ sY L e heN) :
    sPi c ⟨y, hLc hyL⟩ ∈ inSubgroup (aschbacherSolvableCore 3) (sHt c e (hA'c heA)) := by
  let Y' := sY' L hLc e heN
  let Ht := sHt c e (hA'c heA)
  let H' := sH' c e (hA'c heA)
  let f : H' →* Ht := sF c e (hA'c heA)
  have hle := sYim'_subgroupOf_le_theta hLc hcL hc3 hCN hA'c heA heN
  have hιy' : sIota L hLc ⟨y, hyL⟩ ∈ Y' := Subgroup.mem_map_of_mem (sIota L hLc) hyY
  have hιH' : sIota L hLc ⟨y, hyL⟩ ∈ H' := sY'_le_sH' (hA'c heA) hLc heN hιy'
  have hmem : f ⟨sIota L hLc ⟨y, hyL⟩, hιH'⟩ ∈ (sYim' L hLc e heN).subgroupOf Ht := by
    rw [← sF_map_subgroupOf (hA'c heA) hLc heN]
    exact Subgroup.mem_map_of_mem f (Subgroup.mem_subgroupOf.mpr hιy')
  have hmemθ : f ⟨sIota L hLc ⟨y, hyL⟩, hιH'⟩ ∈ aschbacherSolvableCore 3 ↥Ht :=
    hle hmem
  have hval : (f ⟨sIota L hLc ⟨y, hyL⟩, hιH'⟩ : Ht).val = sPi c ⟨y, hLc hyL⟩ := by
    change sPi c (sIota L hLc ⟨y, hyL⟩) = sPi c ⟨y, hLc hyL⟩
    congr 1
  have hmem' : (f ⟨sIota L hLc ⟨y, hyL⟩, hιH'⟩ : Ht).val ∈
      inSubgroup (aschbacherSolvableCore 3) Ht :=
    Subgroup.mem_map_of_mem Ht.subtype hmemθ
  rwa [hval] at hmem'

private lemma comm_mem_thetaAlpha {X : Type*} [Group X] {B : Subgroup X} {a b c : X}
    (ha : a ∈ B) (ha1 : a ≠ 1) (hb : b ∈ B)
    (hc : c ∈ inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set X))) :
    c * b * c⁻¹ * b⁻¹ ∈ thetaAlpha 3 B := by
  have h1 : c * b * c⁻¹ * b⁻¹ ∈
      ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set X)), B⁆ := by
    simpa only [commutatorElement_def] using
      Subgroup.commutator_mem_commutator hc hb
  have h2 : ⁅inSubgroup (aschbacherSolvableCore 3) (Subgroup.centralizer ({a} : Set X)), B⁆ ≤
      thetaJ 3 B := by
    rw [thetaJ]
    exact le_iSup₂_of_le a ha (le_iSup_of_le ha1 le_rfl)
  exact (le_sup_left : thetaJ 3 B ≤ thetaAlpha 3 B) (h2 h1)

private lemma sPiL_inj {L : Subgroup G} {c : G} (hLc : L ≤ sC c)
    (hcL : c ∉ L) (hc3 : orderOf c = 3) :
    Function.Injective ((sPi c).comp (sIota L hLc)) := by
  rw [← MonoidHom.ker_eq_bot_iff]
  rw [show ((sPi c).comp (sIota L hLc)).ker = Subgroup.comap (sIota L hLc) (sK c) by
    rw [← MonoidHom.comap_ker]
    rw [show (sPi c).ker = sK c from QuotientGroup.ker_mk' (sK c)]]
  rw [Subgroup.eq_bot_iff_forall]
  intro x hx
  apply Subtype.ext
  rw [Subgroup.mem_comap] at hx
  have hxK : (x : G) ∈ Subgroup.zpowers c := by
    rw [sK, centralLine] at hx
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
  have hmem : (x : G) ∈ L ⊓ Subgroup.zpowers c := ⟨x.2, hxK⟩
  rw [inf_comm, CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.zpowers_inf_eq_bot_of_not_mem
    hc3 hcL] at hmem
  exact Subgroup.mem_bot.mp hmem

private lemma sT_solv {L : Subgroup G} {c : G} (hLc : L ≤ sC c)
    (hcL : c ∉ L) (hc3 : orderOf c = 3) :
    Group.IsSolvable ↥((aschbacherSolvableCore 3 (sC c ⧸ sK c)).comap
      ((sPi c).comp (sIota L hLc))) := by
  let πL : ↥L →* sC c ⧸ sK c := (sPi c).comp (sIota L hLc)
  let T : Subgroup ↥L := (aschbacherSolvableCore 3 (sC c ⧸ sK c)).comap πL
  have hTπ_le : T.map πL ≤ aschbacherSolvableCore 3 (sC c ⧸ sK c) :=
    Subgroup.map_le_iff_le_comap.mpr (le_refl _)
  let gT : T →* T.map πL :=
    (πL.comp T.subtype).codRestrict (T.map πL) (fun y => Subgroup.mem_map_of_mem πL y.2)
  have hgT_inj : Function.Injective gT := by
    intro x y hxy
    have h1 : πL (x : ↥L) = πL (y : ↥L) := by
      have := congrArg Subtype.val hxy
      simpa [gT] using this
    exact Subtype.ext (sPiL_inj hLc hcL hc3 h1)
  haveI : Group.IsSolvable ↥(T.map πL) := by
    haveI : Group.IsSolvable ↥(aschbacherSolvableCore 3 (sC c ⧸ sK c)) :=
      (solvable_prime_complement_core_characterization (H := sC c ⧸ sK c) Nat.prime_three).1
    exact Group.isSolvable_of_isSolvable_injective
      (f := Subgroup.inclusion hTπ_le)
      (Subgroup.inclusion_injective hTπ_le)
  exact Group.isSolvable_of_isSolvable_injective hgT_inj

private lemma sT_3 {L : Subgroup G} {c : G} (hLc : L ≤ sC c)
    (hcL : c ∉ L) (hc3 : orderOf c = 3) :
    ¬ 3 ∣ Nat.card ↥((aschbacherSolvableCore 3 (sC c ⧸ sK c)).comap
      ((sPi c).comp (sIota L hLc))) := by
  let πL : ↥L →* sC c ⧸ sK c := (sPi c).comp (sIota L hLc)
  let T : Subgroup ↥L := (aschbacherSolvableCore 3 (sC c ⧸ sK c)).comap πL
  have hTπ_le : T.map πL ≤ aschbacherSolvableCore 3 (sC c ⧸ sK c) :=
    Subgroup.map_le_iff_le_comap.mpr (le_refl _)
  have hTπ_3 : ¬ 3 ∣ Nat.card (T.map πL) := by
    intro h
    exact (solvable_prime_complement_core_characterization (H := sC c ⧸ sK c)
      Nat.prime_three).2.2.1 (h.trans (Subgroup.card_dvd_of_le hTπ_le))
  have hker : πL.ker.subgroupOf T = ⊥ := by
    rw [show πL.ker = Subgroup.comap (sIota L hLc) (sK c) by
      rw [← MonoidHom.comap_ker]
      rw [show (sPi c).ker = sK c from QuotientGroup.ker_mk' (sK c)]]
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    apply Subtype.ext
    have hxK : (x : ↥L) ∈ Subgroup.comap (sIota L hLc) (sK c) :=
      Subgroup.mem_subgroupOf.mp hx
    rw [Subgroup.mem_comap] at hxK
    have hxK' : (x : G) ∈ Subgroup.zpowers c := by
      rw [sK, centralLine] at hxK
      obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hxK
      exact Subgroup.mem_zpowers_iff.mpr ⟨n, congrArg Subtype.val hn⟩
    have hmem : (x : G) ∈ L ⊓ Subgroup.zpowers c := ⟨(x : ↥L).2, hxK'⟩
    rw [inf_comm, CFSG.RankThree.PartTwo.Sec19.Step1914TriProof.zpowers_inf_eq_bot_of_not_mem
      hc3 hcL] at hmem
    apply Subtype.ext
    exact Subgroup.mem_bot.mp hmem
  have hcard := card_map_eq_of_ker_subgroupOf_eq_bot πL T hker
  rwa [hcard] at hTπ_3

private lemma sT_le_theta {L : Subgroup G} {c : G} (hLc : L ≤ sC c)
    (hcL : c ∉ L) (hc3 : orderOf c = 3) :
    ((aschbacherSolvableCore 3 (sC c ⧸ sK c)).comap
      ((sPi c).comp (sIota L hLc))) ≤ aschbacherSolvableCore 3 ↥L := by
  let πL : ↥L →* sC c ⧸ sK c := (sPi c).comp (sIota L hLc)
  let T : Subgroup ↥L := (aschbacherSolvableCore 3 (sC c ⧸ sK c)).comap πL
  have hT_normal : T.Normal :=
    Subgroup.Normal.comap (aschbacherSolvableCore_normal 3 (sC c ⧸ sK c)) πL
  exact (solvable_prime_complement_core_characterization (H := ↥L) Nat.prime_three).2.2.2.1
    T hT_normal (sT_solv hLc hcL hc3) (sT_3 hLc hcL hc3)

private lemma sY_comm_not {L : Subgroup G} {c b y : G}
    (hLc : L ≤ sC c) (hcL : c ∉ L) (hc3 : orderOf c = 3)
    (hbL : b ∈ L) (hyL : y ∈ L)
    (hbs : ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
        ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
        (((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L))⁻¹ ≠
      ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L)) :
    sPi c ⟨y, hLc hyL⟩ * sPi c ⟨b, hLc hbL⟩ *
      (sPi c ⟨y, hLc hyL⟩)⁻¹ * (sPi c ⟨b, hLc hbL⟩)⁻¹ ∉
      aschbacherSolvableCore 3 (sC c ⧸ sK c) := by
  intro hmem
  let πL : ↥L →* sC c ⧸ sK c := (sPi c).comp (sIota L hLc)
  let T : Subgroup ↥L := (aschbacherSolvableCore 3 (sC c ⧸ sK c)).comap πL
  have hT_le := sT_le_theta hLc hcL hc3
  have hcommT : (⟨y, hyL⟩ : ↥L) * (⟨b, hbL⟩ : ↥L) * (⟨y, hyL⟩ : ↥L)⁻¹ *
      (⟨b, hbL⟩ : ↥L)⁻¹ ∈ T := by
    rw [Subgroup.mem_comap]
    have hπL : πL ((⟨y, hyL⟩ : ↥L) * (⟨b, hbL⟩ : ↥L) * (⟨y, hyL⟩ : ↥L)⁻¹ *
        (⟨b, hbL⟩ : ↥L)⁻¹) =
        sPi c ⟨y, hLc hyL⟩ * sPi c ⟨b, hLc hbL⟩ *
          (sPi c ⟨y, hLc hyL⟩)⁻¹ * (sPi c ⟨b, hLc hbL⟩)⁻¹ := by
      rw [map_mul, map_mul, map_mul, map_inv, map_inv]
      rfl
    rw [hπL]
    exact hmem
  have hcommθ : (⟨y, hyL⟩ : ↥L) * (⟨b, hbL⟩ : ↥L) * (⟨y, hyL⟩ : ↥L)⁻¹ *
      (⟨b, hbL⟩ : ↥L)⁻¹ ∈ sThetaL L := hT_le hcommT
  have htriv : (((⟨y, hyL⟩ : ↥L) * (⟨b, hbL⟩ : ↥L) * (⟨y, hyL⟩ : ↥L)⁻¹ *
      (⟨b, hbL⟩ : ↥L)⁻¹ : ↥L) : ↥L ⧸ sThetaL L) = 1 := by
    rw [QuotientGroup.eq_one_iff]
    exact hcommθ
  have hcommL : ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
      ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
      ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L)⁻¹ *
      ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L)⁻¹ = 1 := by
    have h1 : (QuotientGroup.mk' (sThetaL L))
        ((⟨y, hyL⟩ : ↥L) * (⟨b, hbL⟩ : ↥L) * (⟨y, hyL⟩ : ↥L)⁻¹ *
          (⟨b, hbL⟩ : ↥L)⁻¹) = 1 := htriv
    rw [map_mul, map_mul, map_mul, map_inv, map_inv] at h1
    exact h1
  have hbary : ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
      ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
      ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L)⁻¹ =
      ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L) := by
    have h2 : ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
        ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L) =
        ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
        ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L) := by
      calc ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
            ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L)
          = (((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
              ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
              ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L)⁻¹ *
              ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L)⁻¹) *
              (((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
              ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L)) := by group
        _ = 1 * (((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
              ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L)) := by rw [hcommL]
        _ = ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ sThetaL L) *
              ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ sThetaL L) := by group
    rw [← h2]
    group
  exact hbs hbary

theorem not_starConditionAt_of_singer {L A' : Subgroup G} {c b e y : G} (hc3 : orderOf c = 3)
    (hLc : L ≤ Subgroup.centralizer ({c} : Set G)) (hcL : c ∉ L)
    (hCN : Subgroup.centralizer ({c} : Set G) ≤ Subgroup.normalizer (L : Set G))
    (hA'c : A' ≤ Subgroup.centralizer ({c} : Set G))
    (hbL : b ∈ L) (hbA : b ∈ A') (heA : e ∈ A') (heN : e ∈ Subgroup.normalizer (L : Set G))
    (hec : e ∉ Subgroup.zpowers c) (hyL : y ∈ L) (hye : e * y = y * e)
    (hs : ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) ∈
      inSubgroup (aschbacherSolvableCore 3)
        (GL3TwoFixedModel.autFixed (Sec4.thetaQuotMulAut ↥L (L.normalizerMonoidHom ⟨e, heN⟩))))
    (hbs : ((⟨b, hbL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) *
        ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L) *
        (((⟨b, hbL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L))⁻¹ ≠
      ((⟨y, hyL⟩ : ↥L) : ↥L ⧸ aschbacherSolvableCore 3 ↥L)) :
    ¬ StarConditionAt A' c := by
  intro hstar
  have hstar' : thetaAlpha 3 ((A'.subgroupOf (sC c)).map (sPi c)) ≤
      aschbacherSolvableCore 3 (sC c ⧸ sK c) := hstar
  have heC : e ∈ sC c := hA'c heA
  have hbC : b ∈ sC c := hA'c hbA
  have hyC : y ∈ sC c := hLc hyL
  let ebar : sC c ⧸ sK c := sPi c ⟨e, heC⟩
  let bbar : sC c ⧸ sK c := sPi c ⟨b, hbC⟩
  let ybar : sC c ⧸ sK c := sPi c ⟨y, hyC⟩
  let Abar : Subgroup (sC c ⧸ sK c) := (A'.subgroupOf (sC c)).map (sPi c)
  have hebar_mem : ebar ∈ Abar :=
    Subgroup.mem_map_of_mem (sPi c) (Subgroup.mem_subgroupOf.mpr heA)
  have hbbar_mem : bbar ∈ Abar :=
    Subgroup.mem_map_of_mem (sPi c) (Subgroup.mem_subgroupOf.mpr hbA)
  have hebar_ne : ebar ≠ 1 := by
    intro h
    have hmem : (⟨e, heC⟩ : sC c) ∈ sK c := by
      have h' : (QuotientGroup.mk' (sK c)) ⟨e, heC⟩ = 1 := h
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h'
    rw [sK, centralLine] at hmem
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hec
    rw [Subgroup.mem_zpowers_iff]
    exact ⟨n, congrArg Subtype.val hn⟩
  have hyY : (⟨y, hyL⟩ : ↥L) ∈ sY L e heN := by
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact Subgroup.mem_comap.mpr hs
    · exact Subgroup.mem_subgroupOf.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hye.symm)
  have hybar_theta : ybar ∈ inSubgroup (aschbacherSolvableCore 3) (sHt c e heC) := by
    have h := sY_ybar_theta hLc hcL hc3 hCN hA'c heA heN hyL hye hs hyY
    rwa [show sPi c ⟨y, hLc hyL⟩ = ybar from congrArg (sPi c) (Subtype.ext rfl)] at h
  have hcomm_mem : ybar * bbar * ybar⁻¹ * bbar⁻¹ ∈ thetaAlpha 3 Abar :=
    comm_mem_thetaAlpha hebar_mem hebar_ne hbbar_mem hybar_theta
  have hcomm_not : ybar * bbar * ybar⁻¹ * bbar⁻¹ ∉
      aschbacherSolvableCore 3 (sC c ⧸ sK c) := by
    have h := sY_comm_not hLc hcL hc3 hbL hyL hbs
    rwa [show sPi c ⟨y, hLc hyL⟩ = ybar from congrArg (sPi c) (Subtype.ext rfl),
      show sPi c ⟨b, hLc hbL⟩ = bbar from congrArg (sPi c) (Subtype.ext rfl)] at h
  exact hcomm_not (hstar' hcomm_mem)

end CFSG.RankThree.PartTwo.Sec15.Proof1510Fuse

module

public import CFSG.LocalAnalysis.WeakClosure81.W16LKU3
public import CFSG.LocalAnalysis.WeakClosure81.TimTI.BenderGenAux1
public import CFSG.Timmesfeld.Bridge.OddLocalRootCore
public import CFSG.LocalAnalysis.EvenBN.GMSK.U3Facts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open
open CFSG.CGT.Timmesfeld75
open Subgroup

variable {X : Type} [Group X] [Finite X] {n : ℕ}

section Certified


theorem IsU3Shape.isL2Pair_sylowCenter_sup (hX : IsU3Shape X n) {R R' : Sylow 2 X}
    (hne : R ≠ R') :
    IsL2Pair ↥(sylowCenter R ⊔ sylowCenter R')
      ((sylowCenter R).subgroupOf (sylowCenter R ⊔ sylowCenter R')) (2 ^ n) := by
  classical
  have hn2 : 2 ≤ n := CFSG.LocalAnalysis.EvenBN.GMSK.two_le_of_lieModel_PSU3 hX.2.1
  have hn0 : n ≠ 0 := by omega
  have hoddZ : Odd (Nat.card (Subgroup.center X)) :=
    Odd.of_dvd_nat ⟨1, by norm_num⟩ hX.2.2
  obtain ⟨e₀⟩ := CFSG.LocalAnalysis.EvenBN.GMSK.exists_mulEquiv_psu3_of_lieModel_PSU3 hX.2.1
  let e : (X ⧸ Subgroup.center X) ≃* CFSG.Theory.Comparator.PSU3Model n :=
    e₀.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 n).symm)
  let Q : Sylow 2 (X ⧸ Subgroup.center X) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) R
  let Q' : Sylow 2 (X ⧸ Subgroup.center X) :=
    Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) R'
  have hbij : Function.Bijective
      (fun T : Sylow 2 X =>
        Sylow.mapSurjective (QuotientGroup.mk'_surjective (Subgroup.center X)) T) :=
    CFSG.Quasithin.sylow_mapSurjective_bijective_of_odd_central_ker
      (QuotientGroup.mk' (Subgroup.center X))
      (QuotientGroup.mk'_surjective (Subgroup.center X))
      (by rw [QuotientGroup.ker_mk'])
      (by rw [QuotientGroup.ker_mk']; exact hoddZ)
  have hneQ : Q ≠ Q' := fun h => hne (hbij.1 h)
  have hmapR : (sylowCenter R).map (QuotientGroup.mk' (Subgroup.center X)) = sylowCenter Q := by
    change (sylowCenter R).map (QuotientGroup.mk' (Subgroup.center X)) =
      sylowCenter (Sylow.mapSurjective
        (QuotientGroup.mk'_surjective (Subgroup.center X)) R)
    exact IsU3Shape.map_sylowCenter hX R
  have hmapR' : (sylowCenter R').map (QuotientGroup.mk' (Subgroup.center X)) =
      sylowCenter Q' := by
    change (sylowCenter R').map (QuotientGroup.mk' (Subgroup.center X)) =
      sylowCenter (Sylow.mapSurjective
        (QuotientGroup.mk'_surjective (Subgroup.center X)) R')
    exact IsU3Shape.map_sylowCenter hX R'
  let L : Subgroup X := sylowCenter R ⊔ sylowCenter R'
  let Lb : Subgroup (X ⧸ Subgroup.center X) :=
    L.map (QuotientGroup.mk' (Subgroup.center X))
  have hLb_eq : Lb = sylowCenter Q ⊔ sylowCenter Q' := by
    change (sylowCenter R ⊔ sylowCenter R').map
      (QuotientGroup.mk' (Subgroup.center X)) = sylowCenter Q ⊔ sylowCenter Q'
    rw [Subgroup.map_sup, hmapR, hmapR']
  have hθ : Nonempty (↥Lb ≃* CFSG.Theory.Comparator.PSL2Model n) := by
    rw [hLb_eq]
    exact CFSG.LocalAnalysis.WeakClosure81.TimTI.timti_isPSL2_sup_rootCenter_of_ne
      hn2 e hneQ
  obtain ⟨θ⟩ := hθ
  have hcard3 : 3 < Nat.card (GaloisField 2 n) := by
    rw [GaloisField.card 2 n hn0]
    calc 3 < 4 := by norm_num
      _ = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
  haveI : Group.IsPerfect (CFSG.Theory.Comparator.PSL2Model n) :=
    CFSG.GorensteinWalter.psl2_isPerfect_of_card_gt_three (GaloisField 2 n) hcard3
  haveI : Group.IsPerfect ↥Lb :=
    Group.IsPerfect.ofSurjective (f := θ.symm.toMonoidHom) θ.symm.surjective
  have hperfLb : commutator ↥Lb = ⊤ := Group.IsPerfect.commutator_eq_top
  have hcentPSL : Subgroup.center (CFSG.Theory.Comparator.PSL2Model n) = ⊥ :=
    CFSG.GorensteinWalter.psl2_center_eq_bot (GaloisField 2 n)
  have hcentLb : Subgroup.center ↥Lb = ⊥ := by
    have hmap : (Subgroup.center ↥Lb).map
        (θ : ↥Lb →* CFSG.Theory.Comparator.PSL2Model n) = ⊥ := by
      rw [Subgroup.map_center_eq θ, hcentPSL]
    exact (Subgroup.map_injective θ.injective) (by rw [hmap, Subgroup.map_bot])
  haveI : Finite ↥L := inferInstance
  let φ : ↥L →* ↥Lb := (QuotientGroup.mk' (Subgroup.center X)).subgroupMap L
  have hφsurj : Function.Surjective φ :=
    (QuotientGroup.mk' (Subgroup.center X)).subgroupMap_surjective L
  have hφker : φ.ker = (Subgroup.center X).subgroupOf L := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hx
      have h' : ((φ x : ↥Lb) : X ⧸ Subgroup.center X) = 1 := congrArg Subtype.val hx
      rw [show ((φ x : ↥Lb) : X ⧸ Subgroup.center X) =
        (QuotientGroup.mk' (Subgroup.center X)) (x : X) from rfl,
        QuotientGroup.mk'_apply] at h'
      exact (QuotientGroup.eq_one_iff (x : X)).mp h'
    · intro hx
      apply Subtype.ext
      show ((φ x : ↥Lb) : X ⧸ Subgroup.center X) = 1
      rw [show ((φ x : ↥Lb) : X ⧸ Subgroup.center X) =
        (QuotientGroup.mk' (Subgroup.center X)) (x : X) from rfl,
        QuotientGroup.mk'_apply]
      exact (QuotientGroup.eq_one_iff (x : X)).mpr hx
  have hmapC : (commutator ↥L).map φ = ⊤ := by
    rw [_root_.commutator_def, Subgroup.map_commutator,
      Subgroup.map_top_of_surjective φ hφsurj]
    rw [← _root_.commutator_def]
    exact hperfLb
  have hCsup : commutator ↥L ⊔ φ.ker = ⊤ := by
    have h := Subgroup.comap_map_eq φ (commutator ↥L)
    rw [hmapC, Subgroup.comap_top] at h
    exact h.symm
  have hZc2 : IsPGroup 2 ((sylowCenter R).subgroupOf L) :=
    ((R.isPGroup').comap_subtype (K := L)).to_le (by rintro x hx; exact hx.1)
  have hZc'2 : IsPGroup 2 ((sylowCenter R').subgroupOf L) :=
    ((R'.isPGroup').comap_subtype (K := L)).to_le (by rintro x hx; exact hx.1)
  have hsup' : (sylowCenter R).subgroupOf L ⊔ (sylowCenter R').subgroupOf L = ⊤ := by
    rw [← Subgroup.subgroupOf_sup (show sylowCenter R ≤ L from le_sup_left)
      (show sylowCenter R' ≤ L from le_sup_right)]
    change L.subgroupOf L = ⊤
    rw [Subgroup.subgroupOf_self]
  have h2quot : IsPGroup 2 (↥L ⧸ commutator ↥L) := by
    let q : ↥L →* (↥L ⧸ commutator ↥L) := QuotientGroup.mk' (commutator ↥L)
    have hAq : IsPGroup 2 (((sylowCenter R).subgroupOf L).map q) := hZc2.map q
    have hBq : IsPGroup 2 (((sylowCenter R').subgroupOf L).map q) := hZc'2.map q
    have hsup'' : ((sylowCenter R).subgroupOf L).map q ⊔
        ((sylowCenter R').subgroupOf L).map q = ⊤ := by
      rw [← Subgroup.map_sup, hsup',
        Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
    exact ((hsup'' ▸ IsPGroup.to_sup_of_normal_right hAq hBq)).of_equiv Subgroup.topEquiv
  have hdivD : Nat.card ((Subgroup.center X).subgroupOf L) ∣
      Nat.card (Subgroup.center X) := by
    rw [← Subgroup.comap_subtype]
    exact Subgroup.card_comap_dvd_of_injective (Subgroup.center X) L.subtype L.subtype_injective
  have hoddD : Odd (Nat.card φ.ker) := by
    rw [hφker]
    exact Odd.of_dvd_nat hoddZ hdivD
  have hoddquot : Odd (Nat.card (↥L ⧸ commutator ↥L)) := by
    let q : ↥L →* (↥L ⧸ commutator ↥L) := QuotientGroup.mk' (commutator ↥L)
    let g : φ.ker →* (↥L ⧸ commutator ↥L) := q.comp φ.ker.subtype
    have hgsurj : Function.Surjective g := by
      have hker_map : (commutator ↥L).map q = ⊥ := by
        rw [eq_bot_iff]
        rintro y ⟨c, hc, rfl⟩
        rw [Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hc
      have hrange : (φ.ker).map q = ⊤ := by
        have h1 : (commutator ↥L ⊔ φ.ker).map q = ⊤ := by
          rw [hCsup, Subgroup.map_top_of_surjective q (QuotientGroup.mk'_surjective _)]
        rwa [Subgroup.map_sup, hker_map, bot_sup_eq] at h1
      intro y
      have hy : y ∈ (φ.ker).map q := by rw [hrange]; trivial
      obtain ⟨d, hd, hdeq⟩ := (Subgroup.mem_map).mp hy
      exact ⟨⟨d, hd⟩, hdeq⟩
    exact hoddD.of_dvd_nat (Subgroup.card_dvd_of_surjective hgsurj)
  have hperfL : commutator ↥L = ⊤ := by
    have hcard1 : Nat.card (↥L ⧸ commutator ↥L) = 1 := by
      rcases h2quot.card_eq_or_dvd with h1 | h2
      · exact h1
      · exact absurd (even_iff_two_dvd.mpr h2) (Nat.not_even_iff_odd.mpr hoddquot)
    exact QuotientGroup.subsingleton_iff.mp (Nat.card_eq_one_iff_unique.mp hcard1).1
  have hDcenter : φ.ker ≤ Subgroup.center ↥L := by
    rw [hφker, ← Subgroup.comap_subtype]
    exact Subgroup.comap_center_le_center L.subtype_injective
  have hcenter_le : Subgroup.center ↥L ≤ φ.ker := by
    intro z hz
    rw [MonoidHom.mem_ker]
    have hzc : φ z ∈ Subgroup.center ↥Lb := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨y, rfl⟩ := hφsurj w
      rw [← map_mul, ← map_mul]
      exact congrArg φ (Subgroup.mem_center_iff.mp hz y)
    rw [hcentLb, Subgroup.mem_bot] at hzc
    exact hzc
  have hcenter_eq : Subgroup.center ↥L = φ.ker := le_antisymm hcenter_le hDcenter
  have hZodd : Odd (Nat.card (Subgroup.center ↥L)) := by
    rw [hcenter_eq, hφker]
    exact Odd.of_dvd_nat hoddZ hdivD
  have hKcenterIso : (↥L ⧸ Subgroup.center ↥L) ≃* ↥Lb :=
    (QuotientGroup.quotientMulEquivOfEq hcenter_eq).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφsurj)
  have hZbot : Subgroup.center ↥L = ⊥ :=
    CFSG.Timmesfeld.Bridge.OddLocal.center_eq_bot_of_psl2 hperfL hZodd
      (hKcenterIso.trans θ)
  have hφinj : Function.Injective φ :=
    (MonoidHom.ker_eq_bot_iff φ).mp (by rw [← hcenter_eq]; exact hZbot)
  have hLiso : ↥L ≃* CFSG.Theory.Comparator.PSL2Model n :=
    (MulEquiv.ofBijective φ ⟨hφinj, hφsurj⟩).trans θ
  have hcardZc : Nat.card ((sylowCenter R).subgroupOf L) = 2 ^ n := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe
      (show sylowCenter R ≤ L from le_sup_left)).toEquiv]
    exact IsU3Shape.card_sylowCenter hX R
  have hcardPSL : Nat.card (CFSG.Theory.Comparator.PSL2Model n) =
      2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr (CFSG.Walter.psl2MulEquivSL2OfCharTwo (K := GaloisField 2 n)).toEquiv,
      card_sl2, GaloisField.card 2 n hn0]
  have hcardL : Nat.card ↥L = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
    rw [Nat.card_congr hLiso.toEquiv, hcardPSL]
  have hidx : ¬ 2 ∣ ((sylowCenter R).subgroupOf L).index := by
    have h2n : 2 ^ n ≠ 0 := pow_ne_zero n (by norm_num)
    have hmul : Nat.card ((sylowCenter R).subgroupOf L) *
        ((sylowCenter R).subgroupOf L).index = Nat.card ↥L :=
      Subgroup.card_mul_index _
    rw [hcardZc, hcardL] at hmul
    have hidxeq : ((sylowCenter R).subgroupOf L).index = (2 ^ n) ^ 2 - 1 :=
      Nat.mul_left_cancel (Nat.pos_of_ne_zero h2n) hmul
    rw [hidxeq]
    have hEven : Even ((2 ^ n) ^ 2) :=
      (even_two.pow_of_ne_zero hn0).pow_of_ne_zero (by norm_num)
    have hle : 1 ≤ (2 ^ n) ^ 2 := by
      have hpos : 0 < (2 ^ n) ^ 2 := pow_pos (pow_pos (by norm_num) n) 2
      omega
    have hodd : Odd ((2 ^ n) ^ 2 - 1) :=
      Nat.Even.sub_odd hle hEven odd_one
    exact fun h2 => (Nat.not_even_iff_odd.mpr hodd) (even_iff_two_dvd.mpr h2)
  change IsL2Pair ↥L ((sylowCenter R).subgroupOf L) (2 ^ n)
  exact IsL2Pair.of_psl_isPGroup hn0 ⟨hLiso⟩ hZc2 hidx

end Certified

end CFSG.LocalAnalysis.WeakClosure81

end

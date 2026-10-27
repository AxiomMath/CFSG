module

public import CFSG.LocalAnalysis.StandardType.GGXInLUDefs
public import CFSG.LocalAnalysis.SeitzReduction.SeitzQ2OddSplitSmall
public import CFSG.GroupTheory.QuasisimpleOddCenterQuotient

public section

open scoped Pointwise

attribute [local instance] commutatorElement

namespace CFSG.StandardType.GGXInL

open CFSG.Assembly CFSG.Open

variable {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G}
  {L D J : Subgroup G} {n : ℕ} {K : Type} [Field K] [Finite K]

theorem lup8f_frame0_eps
    (hS : GGQTwoSetting p B Bs x L D J) (hxL : x ∈ L) (M : lup8f_UnitaryMarking Bs L n K)
    (C : lup8f_CentralCover (lup8f_HT L Bs) (lup8f_L' L Bs) (lup8f_E' L Bs)) [C.N.Normal]
    (hp : p = 3) (hdvd : 3 ∣ n) (hn : 6 ≤ n) :
    ∃ eps : ↥((lup8f_L' L Bs).map (QuotientGroup.mk' C.N)) ≃*
        ↥(LargeEvenSUGroup (Fin n) K 2), lup8f_EpsOver M C.N eps := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hSStar : LargeEvenSStar p B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hcomp := hSStar.2.2.2.1
  have hx1 : x ≠ 1 := hSStar.2.2.1
  have hxB : x ∈ B := hSStar.2.1
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hxB
  have hxp : x ^ p = 1 := hS.1.1.2.1.2.1.2 x hxBs
  have hqL : CFSG.Open.IsQuasisimple ↥L := hcomp.2.2
  have hx3 : orderOf x = 3 := by
    have hxp3 : x ^ 3 = 1 := by rw [← hp]; exact hxp
    exact orderOf_eq_prime hxp3 hx1
  have hxcenterL : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp (hcomp.1 l.2) x (by simp)).symm
  let H' : Type := lup8f_HT L Bs
  let L' : Subgroup H' := lup8f_L' L Bs
  let N : Subgroup H' := C.N
  let Pgrp : Type := ↥L'
  let L0 : Subgroup (H' ⧸ N) := L'.map (QuotientGroup.mk' N)
  let O : Subgroup Pgrp := N.subgroupOf L'
  let Q : Type := Pgrp ⧸ O
  have hNsub_le_center : O ≤ Subgroup.center Pgrp := by
    intro z hz
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    exact (C.central (z : H') (Subgroup.mem_subgroupOf.mp hz) (k : H') k.2)
  have hNsub2 : IsPGroup 2 O :=
    C.two_group.of_equiv (Subgroup.subgroupOfEquivOfLe C.le_L).symm
  have hO : CFSG.Open.pCoreOf 2 (Subgroup.center Pgrp) = O := by
    apply le_antisymm
    · intro z hz
      have hzcenter : z ∈ Subgroup.center Pgrp :=
        CFSG.ClassicalGroups.PCoreSection.pCoreOf_le 2 _ hz
      have hzcent : ∀ l ∈ L', l * (z : H') = (z : H') * l := by
        intro l hl
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hzcenter ⟨l, hl⟩)
      have hz2 : IsPGroup 2 (Subgroup.zpowers (z : H')) := by
        obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp
          (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 (Subgroup.center Pgrp))
          ⟨z, hz⟩
        have hmz : orderOf z = 2 ^ m := by
          simpa using (Subgroup.orderOf_coe
            (⟨z, hz⟩ : ↥(CFSG.Open.pCoreOf 2 (Subgroup.center Pgrp)))).trans hm
        exact IsPGroup.of_card (n := m)
          (by rw [Nat.card_zpowers, Subgroup.orderOf_coe z, hmz])
      exact Subgroup.mem_subgroupOf.mpr (C.contains_two (z : H') z.2 hzcent hz2)
    · apply CFSG.ClassicalGroups.PCoreSection.le_pCoreOf hNsub_le_center
      · intro a ha b hb
        have hcomm : b * a = a * b := Subgroup.mem_center_iff.mp ha b
        have h1 : a * b * a⁻¹ = b := by rw [← hcomm, mul_assoc, mul_inv_cancel, mul_one]
        rw [h1]; exact hb
      · exact hNsub2
  let eL : Pgrp ≃* ↥L := Subgroup.subgroupOfEquivOfLe le_sup_left
  have hq : CFSG.Open.IsQuasisimple Pgrp :=
    CFSG.ComponentClassification.Components.quasisimple_of_equiv eL hqL
  let centerL : Subgroup ↥L := Subgroup.center ↥L
  let g : Pgrp →* LargeEvenProj (LargeEvenSUGroup (Fin n) K 2) :=
    M.theta.toMonoidHom.comp ((QuotientGroup.mk' centerL).comp eL.toMonoidHom)
  have hgker : g.ker = Subgroup.center Pgrp := by
    ext k
    rw [MonoidHom.mem_ker]
    constructor
    · intro hk
      have hmk : QuotientGroup.mk' centerL (eL k) = 1 := by
        have h1 : M.theta (QuotientGroup.mk' centerL (eL k)) = 1 := by
          simpa [g, MonoidHom.comp_apply] using hk
        exact M.theta.injective (by rw [h1, map_one])
      have hcen : eL k ∈ centerL := (QuotientGroup.eq_one_iff _).mp hmk
      rw [Subgroup.mem_center_iff]
      intro k'
      apply eL.injective
      rw [map_mul, map_mul]
      exact Subgroup.mem_center_iff.mp hcen (eL k')
    · intro hk
      have hcen : eL k ∈ centerL := by
        rw [Subgroup.mem_center_iff]
        intro l
        obtain ⟨k', rfl⟩ := eL.surjective l
        calc eL k' * eL k = eL (k' * k) := (map_mul eL k' k).symm
          _ = eL (k * k') := by rw [Subgroup.mem_center_iff.mp hk k']
          _ = eL k * eL k' := map_mul eL k k'
      show M.theta (QuotientGroup.mk' centerL (eL k)) = 1
      rw [QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff _).mpr hcen, map_one]
  have hgsurj : Function.Surjective g :=
    M.theta.surjective.comp ((QuotientGroup.mk'_surjective centerL).comp eL.surjective)
  have hgker_le : O ≤ g.ker := by rw [hgker]; exact hNsub_le_center
  have : Group.IsPerfect Pgrp := ⟨hq.1⟩
  have : Group.IsPerfect Q := by
    refine ⟨?_⟩
    have hmap : Subgroup.map (QuotientGroup.mk' O) (commutator Pgrp) = commutator Q := by
      rw [show commutator Pgrp = ⁅(⊤ : Subgroup Pgrp), ⊤⁆ from rfl]
      rw [Subgroup.map_commutator]
      rw [Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O)]
      rfl
    rw [hq.1, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective O)] at hmap
    exact hmap.symm
  let η : Q →* LargeEvenProj (LargeEvenSUGroup (Fin n) K 2) :=
    QuotientGroup.lift O g hgker_le
  have hηker : η.ker = Subgroup.center Q := by
    rw [QuotientGroup.ker_lift, hgker,
      CFSG.ComponentClassification.Quasisimple.center_map_of_central_kernel
        (QuotientGroup.mk' O) (QuotientGroup.mk'_surjective _)
        (by rw [QuotientGroup.ker_mk']; exact hNsub_le_center)]
  have hηsurj : Function.Surjective η := by
    intro y
    obtain ⟨k, rfl⟩ := hgsurj y
    exact ⟨QuotientGroup.mk' O k, QuotientGroup.lift_mk O hgker_le k⟩
  have hη_ker_le : η.ker ≤ Subgroup.center Q := le_of_eq hηker
  have hodd : Odd (Nat.card η.ker) := by
    rw [hηker]
    have : (CFSG.Open.pCoreOf 2 (Subgroup.center Pgrp)).Normal := by
      rw [hO]; exact C.normal.subgroupOf L'
    have h := CFSG.GroupTheory.odd_card_center_quotient_pCoreOf_center (K := Pgrp) hq
    have hc := Nat.card_congr
      (Subgroup.centerCongr (QuotientGroup.quotientMulEquivOfEq hO)).toEquiv
    rw [hc] at h
    exact h
  let xK : Pgrp := ⟨⟨x, Subgroup.mem_sup_left hxL⟩, Subgroup.mem_subgroupOf.mpr hxL⟩
  have hxKcenter : xK ∈ Subgroup.center Pgrp := by
    rw [Subgroup.mem_center_iff]
    intro k
    apply Subtype.ext
    apply Subtype.ext
    exact (Subgroup.mem_centralizer_iff.mp
      (hcomp.1 (Subgroup.mem_subgroupOf.mp k.2)) x (by simp)).symm
  have hxKpow3 : xK ^ 3 = 1 := by
    apply Subtype.ext
    apply Subtype.ext
    change x ^ 3 = 1
    rw [← hp]
    exact hxp
  have hxK_ne_one : xK ≠ 1 := by
    intro h
    have h1 : ((xK : Pgrp) : H') = ((1 : Pgrp) : H') := congrArg Subtype.val h
    have h2 : (((xK : Pgrp) : H') : G) = (((1 : Pgrp) : H') : G) := congrArg Subtype.val h1
    have h3 : x = 1 := by simpa [xK] using h2
    exact hx1 h3
  have hxKorder : orderOf xK = 3 := orderOf_eq_prime hxKpow3 hxK_ne_one
  have heLxK : eL xK = (⟨x, hxL⟩ : ↥L) := Subtype.ext rfl
  let yq : Q := QuotientGroup.mk' O xK
  have hyq_ker : yq ∈ η.ker := by
    rw [MonoidHom.mem_ker]
    change (QuotientGroup.lift O g hgker_le) (QuotientGroup.mk' O xK) = 1
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
    have hcen : eL xK ∈ centerL := by rw [heLxK]; exact hxcenterL
    have hq1 : QuotientGroup.mk' centerL (eL xK) = 1 :=
      (QuotientGroup.eq_one_iff (eL xK)).mpr hcen
    show M.theta (QuotientGroup.mk' centerL (eL xK)) = 1
    rw [hq1, map_one]
  have hyq_order : orderOf yq = 3 := by
    have hdvd3 : orderOf yq ∣ 3 := by
      apply orderOf_dvd_of_pow_eq_one
      have hyq3 : yq ^ 3 = 1 := by
        change (QuotientGroup.mk' O xK) ^ 3 = 1
        rw [← map_pow, hxKpow3, map_one]
      exact hyq3
    rcases Nat.prime_three.eq_one_or_self_of_dvd (orderOf yq) hdvd3 with h1 | h3
    · exfalso
      have hy1 : yq = 1 := orderOf_eq_one_iff.mp h1
      have hxKO : xK ∈ O := (QuotientGroup.eq_one_iff xK).mp (by
        change (QuotientGroup.mk' O xK : Q) = 1
        rw [show (QuotientGroup.mk' O xK : Q) = yq from rfl, hy1])
      obtain ⟨m, hm⟩ := IsPGroup.iff_orderOf.mp hNsub2 ⟨xK, hxKO⟩
      have hm' : orderOf xK = 2 ^ m := by
        simpa using (Subgroup.orderOf_coe (⟨xK, hxKO⟩ : ↥O)).trans hm
      rw [hxKorder] at hm'
      have hoddx : Odd (2 ^ m) := by rw [← hm']; exact ⟨1, by norm_num⟩
      rcases m with _ | m
      · simp at hm'
      · exact (Nat.not_even_iff_odd.mpr hoddx) ⟨2 ^ m, by rw [pow_succ]; ring⟩
    · exact h3
  let ηst : Q →* StatedProj (StatedSU n (2 ^ 1) K) :=
    { toFun := fun q => η q
      map_one' := map_one η
      map_mul' := fun a b => map_mul η a b }
  have hηstker : ηst.ker = η.ker := rfl
  have hηstsurj : Function.Surjective ηst := hηsurj
  have hηst_ker_le : ηst.ker ≤ Subgroup.center Q := by rw [hηstker]; exact hη_ker_le
  have hoddst : Odd (Nat.card ηst.ker) := by rw [hηstker]; exact hodd
  have h3dvd : 3 ∣ Nat.card ηst.ker := by
    have hle : Subgroup.zpowers yq ≤ ηst.ker :=
      Subgroup.zpowers_le.mpr (by rw [hηstker]; exact hyq_ker)
    have h := Subgroup.card_dvd_of_le hle
    rwa [Nat.card_zpowers, hyq_order] at h
  have hF : Nat.card K = (2 ^ 1) ^ 2 := by rw [M.card_K]; norm_num
  have hm2 : 2 ≤ n := by omega
  have hmq : (n, 2 ^ 1) ≠ (3, 2) := by
    intro h
    have : n = 3 := (Prod.ext_iff.mp h).1
    omega
  have hdiv : Nat.card ηst.ker ∣ n.gcd (2 ^ 1 + 1) :=
    CFSG.SeitzReduction.SeitzQ2.card_ker_dvd_psu (F := K) (f := 1) hF hm2 hmq
      hηstsurj hηst_ker_le hoddst
  have hcard_ker : Nat.card ηst.ker = 3 := by
    have hdvd' : Nat.card ηst.ker ∣ 3 := by
      rw [show 2 ^ 1 + 1 = 3 from rfl, Nat.gcd_eq_right hdvd] at hdiv
      exact hdiv
    exact (Nat.dvd_antisymm h3dvd hdvd').symm
  obtain ⟨α, hα_over, hαsurj, hαker⟩ :=
    CFSG.SeitzReduction.SeitzQ2.exists_surjective_of_psu (F := K) (f := 1) hF hm2 hmq
      hηstsurj hηst_ker_le hoddst
  have hcard_scalars :
      Nat.card ↥((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ 1) K)) = 3 := by
    have h := (CFSG.LinearGroups.unitary_scalar_kernel (p := 2) (f := 1) Nat.prime_two hF
      (n := n) (by omega)).2.2
    rwa [show 2 ^ 1 + 1 = 3 from rfl, Nat.gcd_eq_right hdvd] at h
  have hαker_le : α.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ 1) K) := by
    intro s hs
    rw [MonoidHom.mem_ker] at hs
    have h1 : QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
        (StatedSU n (2 ^ 1) K)) s = 1 := by
      have h' : ηst (α s) = ↑s := hα_over s
      rw [hs, map_one] at h'
      rw [QuotientGroup.mk'_apply]
      exact h'.symm
    rw [QuotientGroup.mk'_apply] at h1
    rwa [QuotientGroup.eq_one_iff] at h1
  have hαinj : Function.Injective α := by
    rw [← MonoidHom.ker_eq_bot_iff α]
    have hdvdK : Nat.card α.ker ∣ 3 := by
      rw [← hcard_scalars]
      exact Subgroup.card_dvd_of_le hαker_le
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvdK with h1 | h3
    · exact Subgroup.card_eq_one.mp h1
    · exfalso
      have hEq : α.ker = (StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ 1) K) :=
        Subgroup.eq_of_le_of_card_ge hαker_le (by rw [h3, hcard_scalars])
      have hbot : ((StatedScalars (Fin n) K).subgroupOf (StatedSU n (2 ^ 1) K)).map α = ⊥ :=
        (Subgroup.map_eq_bot_iff ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (2 ^ 1) K))).mpr (le_of_eq hEq.symm)
      have h1 : Nat.card (Subgroup.map α ((StatedScalars (Fin n) K).subgroupOf
          (StatedSU n (2 ^ 1) K))) = 1 := by rw [hbot]; simp
      rw [← hαker, hcard_ker] at h1
      exact absurd h1 (by norm_num)
  let αe : ↥(StatedSU n (2 ^ 1) K) ≃* Q := MulEquiv.ofBijective α ⟨hαinj, hαsurj⟩
  let f : Pgrp →* ↥L0 :=
    { toFun := fun k => ⟨QuotientGroup.mk' N (k : H'), Subgroup.mem_map_of_mem _ k.2⟩
      map_one' := by apply Subtype.ext; simp
      map_mul' := fun a b => by
        apply Subtype.ext
        exact map_mul (QuotientGroup.mk' N) (a : H') (b : H') }
  have hfker : f.ker = O := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    constructor
    · intro hk
      exact (QuotientGroup.eq_one_iff (k : H')).mp (by simpa [f] using Subtype.ext_iff.mp hk)
    · intro hk
      exact Subtype.ext (by simpa [f] using (QuotientGroup.eq_one_iff (k : H')).mpr hk)
  have hfker_le : O ≤ f.ker := by rw [hfker]
  have hfsurj : Function.Surjective f := by
    intro y
    obtain ⟨h, hh, hhy⟩ := Subgroup.mem_map.mp y.2
    refine ⟨⟨h, hh⟩, ?_⟩
    apply Subtype.ext
    exact hhy
  let e0 : Q ≃* ↥L0 :=
    MulEquiv.ofBijective (QuotientGroup.lift O f hfker_le) (by
      constructor
      · rw [← MonoidHom.ker_eq_bot_iff]
        rw [QuotientGroup.ker_lift, hfker]
        exact (Subgroup.map_eq_bot_iff O).mpr (le_of_eq (QuotientGroup.ker_mk' O).symm)
      · intro y
        obtain ⟨k, rfl⟩ := hfsurj y
        exact ⟨QuotientGroup.mk' O k, QuotientGroup.lift_mk O hfker_le k⟩)
  have e0_mk : ∀ k : Pgrp, e0 (QuotientGroup.mk' O k) = f k := by
    intro k
    change (QuotientGroup.lift O f hfker_le) (QuotientGroup.mk' O k) = f k
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
  let eps : ↥L0 ≃* ↥(LargeEvenSUGroup (Fin n) K 2) :=
    { toFun := fun x => αe.symm (e0.symm x)
      invFun := fun s => e0 (αe s)
      left_inv := fun x => by
        change e0 (αe (αe.symm (e0.symm x))) = x
        rw [MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply]
      right_inv := fun s => by
        change αe.symm (e0.symm (e0 (αe s))) = s
        rw [MulEquiv.symm_apply_apply]
        exact MulEquiv.symm_apply_apply αe s
      map_mul' := fun x y => by
        change αe.symm (e0.symm (x * y)) =
          αe.symm (e0.symm x) * αe.symm (e0.symm y)
        simp only [map_mul] }
  refine ⟨eps, ?_⟩
  intro l
  have hval : eps ⟨QuotientGroup.mk' N (l : H'), Subgroup.mem_map_of_mem _ l.2⟩ =
      αe.symm (QuotientGroup.mk' O l) := by
    change αe.symm (e0.symm ⟨QuotientGroup.mk' N (l : H'), Subgroup.mem_map_of_mem _ l.2⟩) =
      αe.symm (QuotientGroup.mk' O l)
    have he0' : (⟨QuotientGroup.mk' N (l : H'), Subgroup.mem_map_of_mem _ l.2⟩ : ↥L0) =
        e0 (QuotientGroup.mk' O l) := (e0_mk l).symm
    rw [he0', MulEquiv.symm_apply_apply]
  rw [hval]
  let s : ↥(StatedSU n (2 ^ 1) K) := αe.symm (QuotientGroup.mk' O l)
  have hs : α s = QuotientGroup.mk' O l := by
    change (MulEquiv.ofBijective α ⟨hαinj, hαsurj⟩)
      ((MulEquiv.ofBijective α ⟨hαinj, hαsurj⟩).symm (QuotientGroup.mk' O l)) = _
    rw [MulEquiv.apply_symm_apply]
  have hProj : LargeEvenProjMk (LargeEvenSUGroup (Fin n) K 2) s =
      M.theta (QuotientGroup.mk ⟨((l : H') : G), Subgroup.mem_subgroupOf.mp l.2⟩) := by
    have h1 : LargeEvenProjMk (LargeEvenSUGroup (Fin n) K 2) s = ηst (α s) := by
      change (QuotientGroup.mk' ((StatedScalars (Fin n) K).subgroupOf
        (StatedSU n (2 ^ 1) K))) s = η (α s)
      exact (hα_over s).symm
    rw [h1, hs]
    change (QuotientGroup.lift O g hgker_le) (QuotientGroup.mk' O l) =
      M.theta (QuotientGroup.mk ⟨((l : H') : G), Subgroup.mem_subgroupOf.mp l.2⟩)
    rw [QuotientGroup.mk'_apply, QuotientGroup.lift_mk]
    rfl
  exact hProj

end CFSG.StandardType.GGXInL

end

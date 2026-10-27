module

public import CFSG.Quasithin.Vol2.Ch8Sec2L829LM1

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H
open scoped IsMulCommutative

section NSolv

variable {G : Type} [Group G] [Finite G]

theorem s828N_solv (hmod : StmtFSUModule) {T L I H : Subgroup G} {h : G} {k : ℕ}
    (hyp : Hyp7_0_2 G T L I) [hc : IsMulCommutative ↥(fsuV T I)] (hH : IsHStar T (fsuM T L) H)
    (hC : Concl822 T L I H h k) (hL0 : fsuL0 T L = L)
    (hTL : T ≤ Subgroup.normalizer (L : Set G))
    (hD5 : Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃*
      DihedralGroup 5))
    (hr5 : CFSG.Open.pRank 5 H ≤ 1) (hsolv : Group.IsSolvable ↥H) :
    oTwoUpper H ≤ ch82I (fsuV T I) h ⊔ kerIn (H ⊓ fsuM T L) H := by
  obtain ⟨hV, hN⟩ := hmod G T L I hyp.fsu
  have hTM : T ≤ fsuM T L := by
    show T ≤ Subgroup.normalizer (fsuL0 T L : Set G)
    rw [hL0]
    exact hTL
  have hVT : fsuV T I ≤ T := fsuV_le_T hyp.fsu hV hN
  have hT2 : IsPGroup 2 T := hyp.fsu.sylow.1
  have hTsyl : QuasithinUnique.IsSylowTwoOf T H :=
    isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hH.1.1
  have hnN : ¬ H ≤ Subgroup.normalizer (T : Set G) := fun hle =>
    hC.1 (hVT.trans (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hH.1.1 hle hT2))
  obtain ⟨P, hP⟩ := exists_sylow_of_quasithinIsSylowTwo hyp.fsu.sylow
  have hUM : IsUniqueMaxOver H T (H ⊓ fsuM T L) := by
    have := IsHStar.isUniqueMaxOver P (hP ▸ hH) (hP ▸ hTM)
    rwa [hP] at this
  have hMP : MinParabolic H T (H ⊓ fsuM T L) := ⟨hTsyl, hnN, hUM⟩
  obtain ⟨p, hpp, hp2, hO2p2, hJbar, -, -⟩ := hMP.subgroupOf.solvable_structure hsolv
  haveI : Fact p.Prime := ⟨hpp⟩
  have hquot : ∀ y : ↥H ⧸ CFSG.Open.pCore 2 ↥H, ∃ j : ℕ,
      y ^ 2 ^ j ∈ CFSG.Open.pCore p (↥H ⧸ CFSG.Open.pCore 2 ↥H) := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥H) y
    obtain ⟨j, hj⟩ := (B6.upperTwo_eq_top_iff (O2p ↥H p)).mp hO2p2 x
    exact ⟨j, by rw [← map_pow]; exact Subgroup.mem_comap.mp hj⟩
  have hOt : twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H)) =
      CFSG.Open.pCore p (↥H ⧸ CFSG.Open.pCore 2 ↥H) :=
    E2.twoResidual_eq_pCore hpp hp2 hquot
  have hO : oTwoUpper (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H)) =
      CFSG.Open.pCore p (↥H ⧸ CFSG.Open.pCore 2 ↥H) := by
    rw [← CFSG.Quasithin.Vol2.Ch10.SecE.twoResidual_eq_oTwoUpper]
    exact hOt
  have hHIT : H = ch82I (fsuV T I) h ⊔ T := H_eq_ch82I_sup_T_829 hmod hyp hH hC
  have hIH : ch82I (fsuV T I) h ≤ H := by
    rw [hHIT]
    exact le_sup_left
  obtain ⟨m, hm5, ⟨eD⟩⟩ : ∃ m : ℕ, m = 5 ∧ Nonempty (E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) ≃* DihedralGroup m) := ⟨5, rfl, hD5⟩
  let e' : ↥((ch82I (fsuV T I) h).subgroupOf H) ≃* ↥(ch82I (fsuV T I) h) :=
    Subgroup.subgroupOfEquivOfLe hIH
  let πI : ↥(ch82I (fsuV T I) h) →* E2.StarQuot (fsuM T L ⊓ ch82I (fsuV T I) h)
      (ch82I (fsuV T I) h) := QuotientGroup.mk' _
  let ψ : ↥((ch82I (fsuV T I) h).subgroupOf H) →* DihedralGroup m :=
    eD.toMonoidHom.comp (πI.comp e'.toMonoidHom)
  have hψs : Function.Surjective ψ :=
    eD.surjective.comp ((QuotientGroup.mk'_surjective _).comp e'.surjective)
  have hm_prime : m.Prime := by
    rw [hm5]; norm_num
  have hm2 : m ≠ 2 := by
    rw [hm5]; norm_num
  have hJI : ∀ g : G, g ∈ kerIn (H ⊓ fsuM T L) H → g ∈ ch82I (fsuV T I) h →
      g ∈ kerIn (fsuM T L ⊓ ch82I (fsuV T I) h) (ch82I (fsuV T I) h) := by
    intro g hg hgI
    rw [mem_kerIn]
    intro b hb
    exact ⟨((mem_kerIn.mp hg) b (hIH hb)).2,
      (ch82I (fsuV T I) h).mul_mem ((ch82I (fsuV T I) h).mul_mem hb hgI)
        ((ch82I (fsuV T I) h).inv_mem hb)⟩
  have hψJ : ∀ y : ↥((ch82I (fsuV T I) h).subgroupOf H),
      ((y : ↥H)) ∈ kerIn ((H ⊓ fsuM T L).subgroupOf H) ⊤ → ψ y = 1 := by
    intro y hy
    rw [B6.kerIn_subgroupOf_top, Subgroup.mem_subgroupOf] at hy
    have hk : e' y ∈ (kerIn (fsuM T L ⊓ ch82I (fsuV T I) h)
        (ch82I (fsuV T I) h)).subgroupOf (ch82I (fsuV T I) h) :=
      Subgroup.mem_subgroupOf.mpr (hJI _ hy (Subgroup.mem_subgroupOf.mp y.2))
    have hpi : πI (e' y) = 1 := (QuotientGroup.eq_one_iff (e' y)).mpr hk
    show eD (πI (e' y)) = 1
    rw [hpi, map_one]
  have hQT : CFSG.Open.pCore 2 ↥H ≤ T.subgroupOf H := by
    intro x hx
    have hle : CFSG.Open.pCoreOf 2 H ≤ T :=
      CFSG.Quasithin.RonanD33.pCoreOf_le_of_sylow hH.1.1 hT2 hTsyl.2.2
    exact Subgroup.mem_subgroupOf.mpr (hle (Subgroup.mem_map_of_mem H.subtype hx))
  have hTM' : T.subgroupOf H ≤ (H ⊓ fsuM T L).subgroupOf H := by
    intro x hx
    exact Subgroup.mem_subgroupOf.mpr
      (Subgroup.mem_inf.mpr ⟨x.2, hTM (Subgroup.mem_subgroupOf.mp hx)⟩)
  have hnormQ : (CFSG.Open.pCore 2 ↥H).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hQJ : CFSG.Open.pCore 2 ↥H ≤ kerIn ((H ⊓ fsuM T L).subgroupOf H) ⊤ := by
    intro x hx
    rw [mem_kerIn]
    intro b _
    exact hTM' (hQT (hnormQ.conj_mem x hx b))
  have hmp : m = p := prime_eq_of_dihedral_core hm_prime hm2 ψ hψs hψJ hQJ hO
  have hp5 : p = 5 := hmp.symm.trans hm5
  have hr : CFSG.Open.pRank p H ≤ 1 := by
    rw [hp5]
    exact hr5
  have hpH : p ∣ Nat.card ↥H := by
    obtain ⟨y, hy⟩ := hψs (DihedralGroup.r (1 : ZMod m))
    have hr1 : orderOf (ψ y) = m := by
      rw [hy]
      exact DihedralGroup.orderOf_r_one
    have hdvd : orderOf (ψ y) ∣ Nat.card ↥H :=
      (orderOf_map_dvd ψ y).trans
        ((orderOf_dvd_natCard y).trans (Subgroup.card_subgroup_dvd_card _))
    rw [hr1] at hdvd
    rw [← hmp]
    exact hdvd
  have hcycH : IsCyclic ↥(twoResidual (⊤ : Subgroup (↥H ⧸ CFSG.Open.pCore 2 ↥H))) :=
    hMP.isCyclic_twoResidual_ambient hsolv hpp hp2 hpH hr
  rw [hOt] at hcycH
  have hsub : oTwoUpper (⊤ : Subgroup ↥H) ≤
      (ch82I (fsuV T I) h).subgroupOf H ⊔ kerIn ((H ⊓ fsuM T L).subgroupOf H) ⊤ :=
    oTwoUpper_le_of_isCyclic_core hm_prime hm2 ψ hψs hψJ hQJ hO hJbar hcycH
  have hmapO : oTwoUpper H ≤ (oTwoUpper (⊤ : Subgroup ↥H)).map H.subtype := by
    unfold oTwoUpper
    refine (Subgroup.closure_le _).mpr ?_
    rintro x ⟨hxH, hxo⟩
    refine Subgroup.mem_map.mpr ⟨⟨x, hxH⟩, Subgroup.subset_closure ⟨Subgroup.mem_top _, ?_⟩, rfl⟩
    show Odd (orderOf (⟨x, hxH⟩ : ↥H))
    rw [Subgroup.orderOf_mk]
    exact hxo
  have hIsub : ((ch82I (fsuV T I) h).subgroupOf H).map H.subtype = ch82I (fsuV T I) h :=
    Subgroup.map_subgroupOf_eq_of_le hIH
  have hJsub : (kerIn ((H ⊓ fsuM T L).subgroupOf H) ⊤).map H.subtype =
      kerIn (H ⊓ fsuM T L) H := by
    rw [B6.kerIn_subgroupOf_top, Subgroup.map_subgroupOf_eq_of_le (kerIn_le.trans inf_le_left)]
  calc oTwoUpper H ≤ (oTwoUpper (⊤ : Subgroup ↥H)).map H.subtype := hmapO
    _ ≤ (((ch82I (fsuV T I) h).subgroupOf H) ⊔ kerIn ((H ⊓ fsuM T L).subgroupOf H) ⊤).map
          H.subtype := Subgroup.map_mono hsub
    _ = ch82I (fsuV T I) h ⊔ kerIn (H ⊓ fsuM T L) H := by
          rw [Subgroup.map_sup, hIsub, hJsub]

end NSolv

end CFSG.Quasithin.H13

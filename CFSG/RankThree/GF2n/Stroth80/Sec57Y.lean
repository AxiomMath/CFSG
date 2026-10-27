module

public import CFSG.RankThree.GF2n.Smith81.Sec117
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.RankThree.GF2n CFSG.RankThree.GF2n.Smith81
open scoped commutatorElement Pointwise

section Generic

variable {G : Type} [Group G] [Finite G]

private theorem isPGroup_subgroupOf_of_isPGroup {p : ℕ} {R : Subgroup G} (H : Subgroup G)
    (hR : IsPGroup p R) : IsPGroup p (R.subgroupOf H) := by
  intro g
  obtain ⟨n, hn⟩ := hR ⟨((g : H) : G), Subgroup.mem_subgroupOf.mp g.2⟩
  refine ⟨n, Subtype.ext (Subtype.ext ?_)⟩
  simpa using congrArg Subtype.val hn

private theorem le_inSubgroup_pCore_of_normal {p : ℕ} {H R : Subgroup G} (hRH : R ≤ H)
    (hRn : ∀ h ∈ H, ∀ r ∈ R, h * r * h⁻¹ ∈ R) (hRp : IsPGroup p R) :
    R ≤ inSubgroup (CFSG.pCore p) H := by
  have hn : (R.subgroupOf H).Normal :=
    ⟨fun a ha g => by
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      simpa using hRn (g : G) g.2 (a : G) ha⟩
  have hsub : R.subgroupOf H ≤ CFSG.pCore p H :=
    le_sSup ⟨hn, isPGroup_subgroupOf_of_isPGroup H hRp⟩
  intro r hr
  exact Subgroup.mem_map.mpr ⟨⟨r, hRH hr⟩, hsub (Subgroup.mem_subgroupOf.mpr hr), rfl⟩

private theorem inSubgroup_pCore_normal (p : ℕ) (H : Subgroup G) :
    ∀ h ∈ H, ∀ r ∈ inSubgroup (CFSG.pCore p) H, h * r * h⁻¹ ∈ inSubgroup (CFSG.pCore p) H := by
  intro h hh r hr
  obtain ⟨r', hr', rfl⟩ := Subgroup.mem_map.mp hr
  refine Subgroup.mem_map.mpr ⟨(⟨h, hh⟩ : H) * r' * (⟨h, hh⟩ : H)⁻¹, ?_, ?_⟩
  · exact Subgroup.Normal.conj_mem CFSG.pCore_normal r' hr' ⟨h, hh⟩
  · simp

private theorem isPGroup_inSubgroup_pCore (p : ℕ) (H : Subgroup G) :
    IsPGroup p (inSubgroup (CFSG.pCore p) H) :=
  IsPGroup.map CFSG.pCore_isPGroup H.subtype

private theorem inSubgroup_pCore_two_le_gF (H : Subgroup G) :
    inSubgroup (CFSG.pCore 2) H ≤ inSubgroup generalizedFitting H := by
  unfold inSubgroup
  refine Subgroup.map_mono ?_
  have h1 : CFSG.fittingSubgroup ↥H ≤ CFSG.generalizedFitting ↥H := by
    rw [CFSG.generalizedFitting.eq_sup]
    exact le_sup_left
  exact (CFSG.pCore_le_fitting ↥H 2).trans h1

private theorem inf_centralizer_inSubgroup_gF_le (H : Subgroup G) :
    H ⊓ Subgroup.centralizer ((inSubgroup generalizedFitting H : Subgroup G) : Set G) ≤
      inSubgroup generalizedFitting H := by
  intro x hx
  obtain ⟨hxH, hxC⟩ := Subgroup.mem_inf.mp hx
  have hmem : (⟨x, hxH⟩ : ↥H) ∈
      Subgroup.centralizer ((CFSG.generalizedFitting ↥H : Subgroup ↥H) : Set ↥H) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hyG : ((y : ↥H) : G) ∈ inSubgroup generalizedFitting H :=
      Subgroup.mem_map_of_mem H.subtype hy
    exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hxC _ hyG)
  exact Subgroup.mem_map_of_mem H.subtype (CFSG.centralizer_generalizedFitting_le ↥H hmem)

theorem generalizedFitting_le_pCore_two_of_centralizer {K : Type} [Group K] [Finite K]
    (R : Subgroup K) [R.Normal] (hRp : IsPGroup 2 R)
    (hC : Subgroup.centralizer (R : Set K) ≤ R) :
    CFSG.generalizedFitting K ≤ CFSG.pCore 2 K := by
  have hRpc : R ≤ CFSG.pCore 2 K := le_sSup ⟨inferInstance, hRp⟩
  have hRF : R ≤ CFSG.fittingSubgroup K := hRpc.trans (CFSG.pCore_le_fitting K 2)
  have hLC : CFSG.layer K ≤
      Subgroup.centralizer ((CFSG.fittingSubgroup K : Subgroup K) : Set K) := by
    apply Subgroup.commutator_eq_bot_iff_le_centralizer.mp
    rw [Subgroup.commutator_comm]
    exact CFSG.LocalCores.fitting_layer_commute
  have hLR : CFSG.layer K ≤ R :=
    (hLC.trans (Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hRF))).trans hC
  have hFp : CFSG.fittingSubgroup K ≤ CFSG.pCore 2 K := by
    rw [CFSG.fitting_eq_sup_pCore K]
    refine iSup_le fun p => ?_
    by_cases h2 : p.1.1 = 2
    · rw [h2]
    · have hdisj : Disjoint (CFSG.pCore p.1.1 K) R :=
        IsPGroup.disjoint_of_ne p.1.1 2 h2 _ _ CFSG.pCore_isPGroup hRp
      have hpC : CFSG.pCore p.1.1 K ≤ Subgroup.centralizer (R : Set K) := by
        intro x hx
        rw [Subgroup.mem_centralizer_iff]
        intro r hr
        have hc1 : ⁅x, r⁆ ∈ CFSG.pCore p.1.1 K := by
          have e : ⁅x, r⁆ = x * (r * x⁻¹ * r⁻¹) := by
            simp only [commutatorElement_def]; group
          rw [e]
          exact (CFSG.pCore p.1.1 K).mul_mem hx
            (Subgroup.Normal.conj_mem CFSG.pCore_normal x⁻¹
              ((CFSG.pCore p.1.1 K).inv_mem hx) r)
        have hc2 : ⁅x, r⁆ ∈ R := by
          have e : ⁅x, r⁆ = (x * r * x⁻¹) * r⁻¹ := by rw [commutatorElement_def]
          rw [e]
          exact R.mul_mem (Subgroup.Normal.conj_mem ‹R.Normal› r hr x) (R.inv_mem hr)
        have h1 := Subgroup.disjoint_def.mp hdisj hc1 hc2
        exact (commutatorElement_eq_one_iff_mul_comm.mp h1).symm
      exact (hpC.trans hC).trans hRpc
  rw [CFSG.generalizedFitting.eq_sup]
  exact sup_le hFp (hLR.trans hRpc)

end Generic

section Sit

variable {G : Type} [Group G] [Finite G]
  {M Q Z Y : Subgroup G} {t : G}

theorem comm_of_mem_normalizer_zpowers (hs : Sit M Q Z Y t) {n : G}
    (hn : n ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)) :
    n * t = t * n := by
  have hsq : t ^ 2 = 1 := by rw [sq]; exact hs.x_sq
  have hord : orderOf t = 2 := orderOf_eq_prime hsq hs.ne_one
  have hmem : n * t * n⁻¹ ∈ Subgroup.zpowers t :=
    (Subgroup.mem_normalizer_iff.mp hn t).mp (Subgroup.mem_zpowers t)
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have hk2 : t ^ (k % 2) = t ^ k := by
    have h := zpow_mod_orderOf t k
    rw [hord] at h
    exact_mod_cast h
  rcases Int.emod_two_eq_zero_or_one k with h0 | h1
  · exfalso
    rw [h0, zpow_zero] at hk2
    have e : n * t * n⁻¹ = 1 := hk.symm.trans hk2.symm
    apply hs.ne_one
    exact conj_eq_one_iff.mp e
  · rw [h1, zpow_one] at hk2
    have e : n * t * n⁻¹ = t := hk.symm.trans hk2.symm
    calc n * t = n * t * n⁻¹ * n := by group
      _ = t * n := by rw [e]

private theorem conj_mem_zpowers_of_comm {t c h : G} (hc : c * t = t * c)
    (hh : h ∈ Subgroup.zpowers t) : c * h * c⁻¹ ∈ Subgroup.zpowers t := by
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
  have hck : c * t ^ k = t ^ k * c := Commute.zpow_right (show Commute c t from hc) k
  have e : c * t ^ k * c⁻¹ = t ^ k := by rw [hck]; group
  rw [e]
  exact Subgroup.zpow_mem_zpowers t k

private theorem mem_normalizer_zpowers_of_comm {t c : G} (hc : c * t = t * c) :
    c ∈ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  constructor
  · exact conj_mem_zpowers_of_comm hc
  · intro hh
    have hc' : c⁻¹ * t = t * c⁻¹ := Commute.inv_left (show Commute c t from hc)
    have h2 := conj_mem_zpowers_of_comm hc' hh
    have e : c⁻¹ * (c * h * c⁻¹) * c⁻¹⁻¹ = h := by group
    rwa [e] at h2

theorem mem_normalizer_of_comm_Y (hs : Sit M Q Z Y t) {c : G} (hc : c * t = t * c) :
    c ∈ Subgroup.normalizer (Y : Set G) := by
  obtain ⟨g, hgY, -, -⟩ := hs.QB_eq
  have hct : c⁻¹ * t * c = t := by
    calc c⁻¹ * t * c = c⁻¹ * (t * c) := by group
      _ = c⁻¹ * (c * t) := by rw [hc]
      _ = t := by group
  have hmemY : t ∈ conjSubgroup g Z := hgY ▸ hs.mem
  have hmem2 : t ∈ conjSubgroup (c * g) Z := by
    rw [mem_conjSubgroup]
    have e : (c * g)⁻¹ * t * (c * g) = g⁻¹ * (c⁻¹ * t * c) * g := by group
    rw [e, hct]
    exact mem_conjSubgroup.mp hmemY
  have hEq : conjSubgroup g Z = conjSubgroup (c * g) Z :=
    CFSG.RankThree.GF2n.Smith81.conjSubgroup_eq_of_mem_ne_one hs.hyp hs.ne_one hmemY hmem2
  have hcY : conjSubgroup c Y = Y := by
    rw [hgY, ← CFSG.RankThree.GF2n.conjSubgroup_mul, ← hEq]
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have e : c⁻¹ * (c * h * c⁻¹) * c = h := by group
  constructor
  · intro hh
    have h1 : c * h * c⁻¹ ∈ conjSubgroup c Y := mem_conjSubgroup.mpr (by rw [e]; exact hh)
    rw [hcY] at h1
    exact h1
  · intro hh
    have h1 : c * h * c⁻¹ ∈ conjSubgroup c Y := by rw [hcY]; exact hh
    have h2 := mem_conjSubgroup.mp h1
    rw [e] at h2
    exact h2

theorem normalizer_zpowers_le_Y (hs : Sit M Q Z Y t) :
    Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) ≤
      Subgroup.normalizer (Y : Set G) :=
  fun n hn => mem_normalizer_of_comm_Y hs (comm_of_mem_normalizer_zpowers hs hn)

theorem QB_le_normalizer_zpowers_Y (hs : Sit M Q Z Y t) :
    QB Y ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
  fun y hy => mem_normalizer_zpowers_of_comm (hs.QB_comm_X hs.mem hy).symm

theorem isPGroup_QB_Y (hs : Sit M Q Z Y t) : IsPGroup 2 (QB Y) := by
  obtain ⟨g, -, hQBg, -⟩ := hs.QB_eq
  rw [hQBg]
  exact IsPGroup.map (CFSG.RankThree.GF2n.Smith81.Sec117.isPGroup_Q' hs.hyp)
    (MulAut.conj g).toMonoidHom

theorem QB_zpowers_le_normalizer :
    QB (Subgroup.zpowers t) ≤ Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) :=
  Subgroup.map_subtype_le _

theorem QB_zpowers_le_pCore_Y (hs : Sit M Q Z Y t) :
    QB (Subgroup.zpowers t) ≤ inSubgroup (CFSG.pCore 2)
      (Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G)) := by
  set Nt : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) with hNt
  have hQBN : QB Y ≤ Nt := QB_le_normalizer_zpowers_Y hs
  have hQBn : ∀ h ∈ Nt, ∀ r ∈ QB Y, h * r * h⁻¹ ∈ QB Y := fun h hh r hr =>
    hs.normalizer_QB (normalizer_zpowers_le_Y hs hh) hr
  haveI : ((QB Y).subgroupOf Nt).Normal :=
    ⟨fun a ha g => by
      rw [Subgroup.mem_subgroupOf] at ha ⊢
      simpa using hQBn (g : G) g.2 (a : G) ha⟩
  have hRp : IsPGroup 2 ((QB Y).subgroupOf Nt) :=
    isPGroup_subgroupOf_of_isPGroup Nt (isPGroup_QB_Y hs)
  have hC : Subgroup.centralizer (((QB Y).subgroupOf Nt : Subgroup Nt) : Set Nt) ≤
      (QB Y).subgroupOf Nt := by
    intro x hx
    rw [Subgroup.mem_subgroupOf]
    have hxN : (x : G) ∈ Subgroup.normalizer (Y : Set G) := normalizer_zpowers_le_Y hs x.2
    have hcomm : ∀ q ∈ QB Y, q * (x : G) = (x : G) * q := by
      intro q hq
      have hr : (⟨q, hQBN hq⟩ : Nt) ∈ (QB Y).subgroupOf Nt := Subgroup.mem_subgroupOf.mpr hq
      exact congrArg Subtype.val (Subgroup.mem_centralizer_iff.mp hx _ hr)
    exact inf_centralizer_inSubgroup_gF_le (Subgroup.normalizer (Y : Set G))
      ⟨hxN, Subgroup.mem_centralizer_iff.mpr hcomm⟩
  have hF := generalizedFitting_le_pCore_two_of_centralizer ((QB Y).subgroupOf Nt) hRp hC
  exact Subgroup.map_mono hF

theorem key_Y (hs : Sit M Q Z Y t) {x : G} (hxt : x ∈ QB (Subgroup.zpowers t))
    (hxN : x ∈ Subgroup.normalizer (Y : Set G)) (hxC : ∀ y ∈ Y, x * y = y * x) :
    x ∈ QB Y := by
  set N : Subgroup G := Subgroup.normalizer (Y : Set G) with hN
  set Nt : Subgroup G := Subgroup.normalizer ((Subgroup.zpowers t : Subgroup G) : Set G) with hNt
  set D : Subgroup G := N ⊓ Subgroup.centralizer (Y : Set G) with hD
  set P : Subgroup G := inSubgroup (CFSG.pCore 2) Nt with hP
  have hDN' : D ≤ N := inf_le_left
  have hxP : x ∈ P := QB_zpowers_le_pCore_Y hs hxt
  have hxD : x ∈ D := Subgroup.mem_inf.mpr ⟨hxN, Subgroup.mem_centralizer_iff.mpr
    fun y hy => (hxC y hy).symm⟩
  have hDNt : ∀ d ∈ D, d ∈ Nt := by
    intro d hd
    obtain ⟨-, hdC⟩ := Subgroup.mem_inf.mp hd
    exact mem_normalizer_zpowers_of_comm (Subgroup.mem_centralizer_iff.mp hdC t hs.mem).symm
  have hDN : ∀ n ∈ N, ∀ d ∈ D, n * d * n⁻¹ ∈ D := by
    intro n hn d hd
    obtain ⟨hdN, hdC⟩ := Subgroup.mem_inf.mp hd
    refine Subgroup.mem_inf.mpr ⟨N.mul_mem (N.mul_mem hn hdN) (N.inv_mem hn), ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hy' : n⁻¹ * y * n ∈ (Y : Set G) := by
      refine (Subgroup.mem_normalizer_iff.mp hn (n⁻¹ * y * n)).mpr ?_
      have e : n * (n⁻¹ * y * n) * n⁻¹ = y := by group
      rw [e]
      exact hy
    have hdy : (n⁻¹ * y * n) * d = d * (n⁻¹ * y * n) :=
      Subgroup.mem_centralizer_iff.mp hdC _ hy'
    calc y * (n * d * n⁻¹) = n * ((n⁻¹ * y * n) * d) * n⁻¹ := by group
      _ = n * (d * (n⁻¹ * y * n)) * n⁻¹ := by rw [hdy]
      _ = (n * d * n⁻¹) * y := by group
  have hPD_normal : ∀ h ∈ D, ∀ r ∈ P ⊓ D, h * r * h⁻¹ ∈ P ⊓ D := by
    intro h hh r hr
    obtain ⟨hrP, hrD⟩ := Subgroup.mem_inf.mp hr
    exact Subgroup.mem_inf.mpr ⟨inSubgroup_pCore_normal 2 Nt h (hDNt h hh) r hrP,
      D.mul_mem (D.mul_mem hh hrD) (D.inv_mem hh)⟩
  have hPD : P ⊓ D ≤ inSubgroup (CFSG.pCore 2) D :=
    le_inSubgroup_pCore_of_normal inf_le_right hPD_normal
      (IsPGroup.to_le (isPGroup_inSubgroup_pCore 2 Nt) inf_le_left)
  have hOD : inSubgroup (CFSG.pCore 2) D ≤ D := Subgroup.map_subtype_le _
  have hOconj : ∀ n ∈ N, ∀ o ∈ inSubgroup (CFSG.pCore 2) D,
      n * o * n⁻¹ ∈ inSubgroup (CFSG.pCore 2) D := by
    intro n hn o ho
    have hO' : (inSubgroup (CFSG.pCore 2) D).map (MulAut.conj n).toMonoidHom ≤
        inSubgroup (CFSG.pCore 2) D := by
      refine le_inSubgroup_pCore_of_normal ?_ ?_ ?_
      · rintro _ ⟨o', ho', rfl⟩
        exact hDN n hn o' (hOD ho')
      · rintro h hh _ ⟨o', ho', rfl⟩
        have hh' : n⁻¹ * h * n ∈ D := by
          have := hDN n⁻¹ (N.inv_mem hn) h hh
          rwa [inv_inv] at this
        have hmem := inSubgroup_pCore_normal 2 D (n⁻¹ * h * n) hh' o' ho'
        refine Subgroup.mem_map.mpr ⟨(n⁻¹ * h * n) * o' * (n⁻¹ * h * n)⁻¹, hmem, ?_⟩
        show n * ((n⁻¹ * h * n) * o' * (n⁻¹ * h * n)⁻¹) * n⁻¹ = h * (n * o' * n⁻¹) * h⁻¹
        group
      · exact IsPGroup.map (isPGroup_inSubgroup_pCore 2 D) _
    exact hO' (Subgroup.mem_map.mpr ⟨o, ho, rfl⟩)
  have hOle : inSubgroup (CFSG.pCore 2) D ≤ inSubgroup (CFSG.pCore 2) N :=
    le_inSubgroup_pCore_of_normal (hOD.trans hDN') hOconj (isPGroup_inSubgroup_pCore 2 D)
  have hxO : x ∈ inSubgroup (CFSG.pCore 2) D := hPD (Subgroup.mem_inf.mpr ⟨hxP, hxD⟩)
  exact inSubgroup_pCore_two_le_gF N (hOle hxO)

theorem post_Y (hs : Sit M Q Z Y t) {X : Subgroup G} (hX : ∃ g : G, X = conjSubgroup g Z)
    {x : G} (hxX : x ∈ X) (hx1 : x ≠ 1) (hxN : x ∈ Subgroup.normalizer (Y : Set G))
    (hxQ : x ∉ QB Y) :
    ∀ y ∈ X, y ∈ Subgroup.normalizer (Y : Set G) ∧ ∀ w ∈ Y, y * w = w * y := by
  obtain ⟨g, rfl⟩ := hX
  obtain ⟨kY, hkY, hQBY, hNY⟩ := hs.QB_eq
  have hmemN : ∀ w : G, w ∈ Subgroup.normalizer (Y : Set G) ↔ kY⁻¹ * w * kY ∈ M := fun w => by
    rw [hNY, mem_conjSubgroup]
  have hmemQ : ∀ w : G, w ∈ QB Y ↔ kY⁻¹ * w * kY ∈ Q := fun w => by
    rw [hQBY, mem_conjSubgroup]
  have hmemY : ∀ w : G, w ∈ Y ↔ kY⁻¹ * w * kY ∈ Z := fun w => by
    rw [hkY, mem_conjSubgroup]
  have hconj : ∀ w : G, kY⁻¹ * w * kY ∈ conjSubgroup (kY⁻¹ * g) Z ↔
      w ∈ conjSubgroup g Z := by
    intro w
    rw [mem_conjSubgroup, mem_conjSubgroup,
      show (kY⁻¹ * g)⁻¹ * (kY⁻¹ * w * kY) * (kY⁻¹ * g) = g⁻¹ * w * g by group]
  have hx'M : kY⁻¹ * x * kY ∈ M := (hmemN x).mp hxN
  have hx'Q : kY⁻¹ * x * kY ∉ Q := fun h => hxQ ((hmemQ x).mpr h)
  have hx'1 : kY⁻¹ * x * kY ≠ 1 := fun h => hx1 (by
    have e : x = kY * (kY⁻¹ * x * kY) * kY⁻¹ := by group
    rw [e, h]
    group)
  have sit' : Sit M Q Z (conjSubgroup (kY⁻¹ * g) Z) (kY⁻¹ * x * kY) :=
    ⟨hs.hyp, ⟨kY⁻¹ * g, rfl⟩, (hconj x).mpr hxX, hx'1, hx'M, hx'Q⟩
  have hpost := (smith_1_12 sit').1
  intro y hy
  have hy'' : kY⁻¹ * y * kY ∈ conjSubgroup (kY⁻¹ * g) Z := (hconj y).mpr hy
  have hH0 : kY⁻¹ * y * kY ∈ M ⊓ Subgroup.centralizer (Z : Set G) := hpost hy''
  obtain ⟨hyM, hyC⟩ := Subgroup.mem_inf.mp hH0
  refine ⟨(hmemN y).mpr hyM, fun w hw => ?_⟩
  have hc : kY⁻¹ * w * kY ∈ Z := (hmemY w).mp hw
  have hcomm : (kY⁻¹ * w * kY) * (kY⁻¹ * y * kY) = (kY⁻¹ * y * kY) * (kY⁻¹ * w * kY) :=
    Subgroup.mem_centralizer_iff.mp hyC _ hc
  calc y * w = kY * ((kY⁻¹ * y * kY) * (kY⁻¹ * w * kY)) * kY⁻¹ := by group
    _ = kY * ((kY⁻¹ * w * kY) * (kY⁻¹ * y * kY)) * kY⁻¹ := by rw [hcomm]
    _ = w * y := by group

end Sit

section Targets

variable {G : Type} [Group G] [Finite G]
  {M Q Z B : Subgroup G}

theorem Sec5Hyp.exists_root (hc : Ctx M Q Z B) {n : ℕ} {t : G} (h : Sec5Hyp hc n t)
    (hb : ∃ g : G, ∃ b ∈ B, g * t * g⁻¹ = b) :
    ∃ (Y : Subgroup G) (k : G), Y = conjSubgroup k Z ∧ t ∈ Y ∧ Sit M Q Z Y t := by
  obtain ⟨g, b, hbB, hgb⟩ := hb
  obtain ⟨g0, hg0⟩ := hc.conj
  have hbZ : b ∈ conjSubgroup g0 Z := hg0 ▸ hbB
  obtain ⟨k, hk⟩ : ∃ k : G, k = g⁻¹ * g0 := ⟨_, rfl⟩
  have htY : t ∈ conjSubgroup k Z := by
    rw [mem_conjSubgroup]
    have e : k⁻¹ * t * k = g0⁻¹ * (g * t * g⁻¹) * g0 := by rw [hk]; group
    rw [e, hgb]
    exact mem_conjSubgroup.mp hbZ
  have ht1 : t ≠ 1 := by
    intro h1
    apply h.notQ
    rw [h1]
    exact Q.one_mem
  have hs : Sit M Q Z (conjSubgroup k Z) t :=
    ⟨hc.hyp, ⟨k, rfl⟩, htY, ht1, hc.LB_le_M h.mem, h.notQ⟩
  exact ⟨conjSubgroup k Z, k, rfl, htY, hs⟩

theorem QB_le_QB_zpowers {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) :
    QB Y ≤ QB (Subgroup.zpowers t) :=
  (le_inSubgroup_pCore_of_normal (QB_le_normalizer_zpowers_Y hs)
    (fun h hh r hr => hs.normalizer_QB (normalizer_zpowers_le_Y hs hh) hr)
    (isPGroup_QB_Y hs)).trans (inSubgroup_pCore_two_le_gF _)

theorem root_le_QB_of_le_QB_zpowers {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t)
    {X : Subgroup G} (hX : ∃ g : G, X = conjSubgroup g Z)
    (hXt : X ≤ QB (Subgroup.zpowers t)) : X ≤ QB Y := by
  obtain ⟨g, rfl⟩ := hX
  obtain ⟨kY, hkY, hQBY, -⟩ := hs.QB_eq
  by_cases hXY : conjSubgroup g Z = Y
  · rw [hXY, hQBY, hkY]
    exact Subgroup.map_mono hs.hyp.Z_normal.1
  obtain ⟨z, hz, hz1⟩ := CFSG.RankThree.GF2n.Smith81.Sec117.exists_ne_one_Z hs.hyp
  obtain ⟨x, hxdef⟩ : ∃ x : G, x = g * z * g⁻¹ := ⟨_, rfl⟩
  have hxX : x ∈ conjSubgroup g Z := by
    rw [hxdef, mem_conjSubgroup, show g⁻¹ * (g * z * g⁻¹) * g = z by group]
    exact hz
  have hx1 : x ≠ 1 := by
    intro h1
    apply hz1
    have e : z = g⁻¹ * (g * z * g⁻¹) * g := by group
    rw [e, ← hxdef, h1]
    group
  have hxY : x ∉ Y := fun h1 =>
    hXY ((conjSubgroup_eq_of_mem_ne_one hs.hyp hx1 hxX (by rw [hkY] at h1; exact h1)).trans
      hkY.symm)
  have hxt : x ∈ QB (Subgroup.zpowers t) := hXt hxX
  have hxN : x ∈ Subgroup.normalizer (Y : Set G) :=
    normalizer_zpowers_le_Y hs (QB_zpowers_le_normalizer hxt)
  by_cases hxQ : x ∈ QB Y
  ·
    rw [hQBY] at hxQ
    have hx'Q : kY⁻¹ * x * kY ∈ Q := mem_conjSubgroup.mp hxQ
    have hx'Z : kY⁻¹ * x * kY ∉ Z := fun h1 => hxY (by
      rw [hkY]
      exact mem_conjSubgroup.mpr h1)
    have hzZ : g⁻¹ * x * g ∈ Z := mem_conjSubgroup.mp hxX
    have hdec : kY⁻¹ * x * kY = (kY⁻¹ * g) * (g⁻¹ * x * g) * (kY⁻¹ * g)⁻¹ := by group
    obtain ⟨h2, hh2Q, hxh2⟩ :=
      stroth_2_6 hs.hyp hx'Q hx'Z ⟨kY⁻¹ * g, g⁻¹ * x * g, hzZ, hdec⟩
    have hxW : x ∈ conjSubgroup (kY * h2) Z := by
      rw [mem_conjSubgroup]
      have e : (kY * h2)⁻¹ * x * (kY * h2) = h2⁻¹ * (kY⁻¹ * x * kY) * h2 := by group
      rw [e]
      exact mem_conjSubgroup.mp hxh2
    rw [conjSubgroup_eq_of_mem_ne_one hs.hyp hx1 hxX hxW,
      CFSG.RankThree.GF2n.conjSubgroup_mul, hQBY]
    exact Subgroup.map_mono hh2Q
  ·
    have hcomm := (post_Y hs ⟨g, rfl⟩ hxX hx1 hxN hxQ) x hxX
    exact absurd (key_Y hs hxt hxN hcomm.2) hxQ

theorem Z_inf_QB_zpowers {Y : Subgroup G} {t : G} (hs : Sit M Q Z Y t) :
    Z ⊓ QB (Subgroup.zpowers t) = ⊥ := by
  rw [eq_bot_iff]
  intro x hx
  obtain ⟨hxZ, hxt⟩ := Subgroup.mem_inf.mp hx
  rw [Subgroup.mem_bot]
  by_contra hx1
  have hxN : x ∈ Subgroup.normalizer (Y : Set G) :=
    normalizer_zpowers_le_Y hs (QB_zpowers_le_normalizer hxt)
  have hxQB : x ∉ QB Y := fun h1 => by
    have hmem : x ∈ Z ⊓ QB Y := Subgroup.mem_inf.mpr ⟨hxZ, h1⟩
    rw [Z_inf_QB_eq_bot hs (smith_1_12 hs), Subgroup.mem_bot] at hmem
    exact hx1 hmem
  have hZc : ∃ g : G, Z = conjSubgroup g Z :=
    ⟨1, (CFSG.RankThree.GF2n.conjSubgroup_one Z).symm⟩
  have hcomm := (post_Y hs hZc hxZ hx1 hxN hxQB) x hxZ
  exact hxQB (key_Y hs hxt hxN hcomm.2)

end Targets

end CFSG.RankThree.GF2n.Stroth80

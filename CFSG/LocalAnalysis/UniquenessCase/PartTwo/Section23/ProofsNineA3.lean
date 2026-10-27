module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsNineA
public import CFSG.LocalAnalysis.UniquenessCase.UCKUnfaithful
public import CFSG.LocalAnalysis.UniquenessCase.UC22SeedSL
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21c
public import CFSG.GroupTheory.SL2OddSplitTorus
public import CFSG.GroupTheory.CoprimeCentralizerTransport
public import CFSG.Adapters.QiuzhenLegacy.GorensteinWalter.Section2.CoprimeTools
public import CFSG.Walter.Bender1970.S2.PGroup

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section A3

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch} {hV : IsElemAbelian 2 c.V}
  {d : S23_9_A0Data D Ch c} {b : G} {hb : b ∈ c.B0} {r : ℕ}

abbrev S23_9_AdjData.qX
    (a : S23_9_AdjData D Ch c hV d b hb r) : ↥a.X →* Bar2 a.X :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥a.X)

abbrev S23_9_AdjData.dhat
    (a : S23_9_AdjData D Ch c hV d b hb r) : Bar2 a.X :=
  a.qX ⟨a.dRoot, a.hdX⟩

theorem S23_9_AdjData.orderOf_dhat (a : S23_9_AdjData D Ch c hV d b hb r)
    (hr : r.Prime) (hr2 : r ≠ 2) : orderOf a.dhat = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  have hO2X : IsPGroup 2 (CFSG.pCore 2 ↥a.X) := CFSG.pCore_isPGroup
  have hdRoot_order : orderOf (⟨a.dRoot, a.hdX⟩ : ↥a.X) = r := by
    rw [Subgroup.orderOf_mk a.dRoot a.hdX, a.hdorder]
  have hr_not_dvd_O : ¬ r ∣ Nat.card (CFSG.pCore 2 ↥a.X) := by
    intro hdvd
    obtain ⟨k, hk⟩ := hO2X.exists_card_eq
    rw [hk] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdvd))
  exact CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime hr_not_dvd_O hdRoot_order

theorem S23_9_AdjData.inner_bar (a : S23_9_AdjData D Ch c hV d b hb r)
    (x : G) (hx : x ∈ a.X) :
    a.qX ⟨b * x * b⁻¹, (Subgroup.mem_normalizer_iff.mp a.hbX x).mp hx⟩ =
      a.dhat * a.qX ⟨x, hx⟩ * a.dhat⁻¹ := by
  have hx' : a.dRoot * x * a.dRoot⁻¹ ∈ a.X :=
    a.X.mul_mem (a.X.mul_mem a.hdX hx) (a.X.inv_mem a.hdX)
  have hmem : b * x * b⁻¹ ∈ a.X := (Subgroup.mem_normalizer_iff.mp a.hbX x).mp hx
  have hq : a.qX ⟨b * x * b⁻¹, hmem⟩ = a.qX ⟨a.dRoot * x * a.dRoot⁻¹, hx'⟩ := by
    change (QuotientGroup.mk' (CFSG.pCore 2 ↥a.X)) ⟨b * x * b⁻¹, hmem⟩ =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥a.X)) ⟨a.dRoot * x * a.dRoot⁻¹, hx'⟩
    exact QuotientGroup.eq_iff_div_mem.mpr (by
      obtain ⟨n, hn, hny⟩ := a.hinner x hx
      have hdiv : (⟨b * x * b⁻¹, hmem⟩ / ⟨a.dRoot * x * a.dRoot⁻¹, hx'⟩ : ↥a.X) = n := by
        apply Subtype.ext
        simpa [div_eq_mul_inv] using hny.symm
      rw [hdiv]
      exact hn)
  rw [hq]
  change a.qX (⟨a.dRoot, a.hdX⟩ * ⟨x, hx⟩ * ⟨a.dRoot, a.hdX⟩⁻¹) =
    a.dhat * a.qX ⟨x, hx⟩ * a.dhat⁻¹
  simp [S23_9_AdjData.dhat, S23_9_AdjData.qX, map_mul, map_inv]
  all_goals rw [← QuotientGroup.mk_mul]
  all_goals rfl

theorem S23_9_AdjData.bar_twoSubgroup_of_sl2 {K : Type*} [Field K] [Finite K] [CharP K 2]
    (a : S23_9_AdjData D Ch c hV d b hb r)
    (e : Bar2 a.X ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    {S0 : Subgroup (Matrix.SpecialLinearGroup (Fin 2) K)}
    (hS0p : IsPGroup 2 S0) (hS0ne : S0 ≠ ⊥) (hS0sq : ∀ s ∈ S0, s * s = 1)
    (hyS0 : e a.dhat ∈ Subgroup.normalizer
      (S0 : Set (Matrix.SpecialLinearGroup (Fin 2) K)))
    (hne0 : ∃ s ∈ S0, ⁅e a.dhat, s⁆ ≠ 1) :
    ∃ Sbar : Subgroup (Bar2 a.X), IsPGroup 2 Sbar ∧ Sbar ≠ ⊥ ∧
      (∀ z ∈ Sbar, z * z = 1) ∧
      a.dhat ∈ Subgroup.normalizer (Sbar : Set (Bar2 a.X)) ∧
      ∃ t ∈ Sbar, ⁅a.dhat, t⁆ ≠ 1 := by
  let Sbar : Subgroup (Bar2 a.X) := S0.map e.symm.toMonoidHom
  have hSbarp : IsPGroup 2 Sbar := hS0p.map _
  have hSbarne : Sbar ≠ ⊥ := by
    intro hbot
    exact hS0ne ((Subgroup.map_eq_bot_iff_of_injective (H := S0)
      (f := e.symm.toMonoidHom) e.symm.injective).mp hbot)
  have hSbarsq : ∀ z ∈ Sbar, z * z = 1 := by
    intro z hz
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hz
    simpa [map_mul] using congrArg e.symm (hS0sq t ht)
  have hdhatSbar : a.dhat ∈ Subgroup.normalizer (Sbar : Set (Bar2 a.X)) := by
    have h := Subgroup.mem_map_of_mem (f := e.symm.toMonoidHom) hyS0
    rw [Subgroup.map_equiv_normalizer_eq S0 e.symm] at h
    have hy : a.dhat = e.symm (e a.dhat) := (e.symm_apply_apply a.dhat).symm
    rwa [hy]
  have hne_bar : ∃ t ∈ Sbar, ⁅a.dhat, t⁆ ≠ 1 := by
    obtain ⟨s0, hs0, hne0'⟩ := hne0
    refine ⟨e.symm s0, Subgroup.mem_map_of_mem _ hs0, ?_⟩
    have hy : a.dhat = e.symm (e a.dhat) := (e.symm_apply_apply a.dhat).symm
    rw [hy]
    change ⁅e.symm.toMonoidHom (e a.dhat), e.symm.toMonoidHom s0⁆ ≠ 1
    rw [← map_commutatorElement]
    intro h
    exact hne0' (e.symm.injective (by simpa using h))
  exact ⟨Sbar, hSbarp, hSbarne, hSbarsq, hdhatSbar, hne_bar⟩

theorem S23_9_AdjData.exists_bar_twoSubgroup {K : Type*} [Field K] [Finite K] [CharP K 2]
    (a : S23_9_AdjData D Ch c hV d b hb r)
    (e : Bar2 a.X ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    (hKcard : Nat.card K = 2 ^ a.m) (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ Sbar : Subgroup (Bar2 a.X), IsPGroup 2 Sbar ∧ Sbar ≠ ⊥ ∧
      (∀ z ∈ Sbar, z * z = 1) ∧
      a.dhat ∈ Subgroup.normalizer (Sbar : Set (Bar2 a.X)) ∧
      ∃ t ∈ Sbar, ⁅a.dhat, t⁆ ≠ 1 := by
  have hdhat_order : orderOf a.dhat = r := a.orderOf_dhat hr hr2
  let y : Matrix.SpecialLinearGroup (Fin 2) K := e a.dhat
  have hy_order : orderOf y = r := by
    simpa [y] using (MulEquiv.orderOf_eq e a.dhat).trans hdhat_order
  have hy_odd : Odd (orderOf y) := by
    rw [hy_order]
    exact hr.odd_of_ne_two hr2
  have hy_dvd : orderOf y ∣ Nat.card K - 1 := by
    rw [hy_order, hKcard]
    exact a.hrm
  have hy_ne_one : y ≠ 1 := by
    intro hy1
    have h1 : orderOf y = 1 := by rw [hy1, orderOf_one]
    rw [hy_order] at h1
    exact hr.ne_one h1
  obtain ⟨S0, hS0p, hS0ne, hS0sq, hyS0, hne0⟩ :=
    CFSG.GroupTheory.exists_twoSubgroup_normalizer_commutator_eq (F := K)
      hy_odd hy_dvd hy_ne_one
  exact a.bar_twoSubgroup_of_sl2 e hS0p hS0ne hS0sq hyS0 hne0

theorem S23_9_AdjData.exists_twoSubgroup (a : S23_9_AdjData D Ch c hV d b hb r)
    (Sbar : Subgroup (Bar2 a.X)) (hSbarp : IsPGroup 2 Sbar)
    (hSbarsq : ∀ z ∈ Sbar, z * z = 1)
    (hdhatSbar : a.dhat ∈ Subgroup.normalizer (Sbar : Set (Bar2 a.X)))
    (hne_bar : ∃ t ∈ Sbar, ⁅a.dhat, t⁆ ≠ 1) :
    ∃ (S : Subgroup G) (SX : Subgroup ↥a.X),
      S = SX.map a.X.subtype ∧ SX.map a.qX = Sbar ∧
      IsPGroup 2 S ∧ b ∈ Subgroup.normalizer (S : Set G) ∧
      ∃ s ∈ S, ⁅b, s⁆ ∉ (CFSG.pCore 2 ↥a.X).map a.X.subtype := by
  let SX : Subgroup ↥a.X := Sbar.comap a.qX
  let S : Subgroup G := SX.map a.X.subtype
  have hSXp : IsPGroup 2 SX := by
    change IsPGroup 2 (Sbar.comap a.qX)
    refine IsPGroup.comap_of_ker_isPGroup hSbarp a.qX ?_
    rw [show a.qX.ker = CFSG.pCore 2 ↥a.X from
      QuotientGroup.ker_mk' (CFSG.pCore 2 ↥a.X)]
    exact CFSG.pCore_isPGroup
  have hSp : IsPGroup 2 S := hSXp.map _
  have hSX : S ≤ a.X := Subgroup.map_subtype_le _
  have hmap : SX.map a.qX = Sbar := by
    change (Sbar.comap a.qX).map a.qX = Sbar
    simpa [S23_9_AdjData.qX] using
      Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) Sbar
  have hbS : b ∈ Subgroup.normalizer (S : Set G) := by
    have hle : S.map (MulAut.conj b).toMonoidHom ≤ S := by
      rintro s ⟨x, hxS, rfl⟩
      rcases hxS with ⟨x', hx'SX, rfl⟩
      have hx'Sbar : a.qX x' ∈ Sbar := Subgroup.mem_comap.mp hx'SX
      have hmemX : b * (x' : G) * b⁻¹ ∈ a.X :=
        (Subgroup.mem_normalizer_iff.mp a.hbX (x' : G)).mp (x').2
      refine ⟨⟨b * (x' : G) * b⁻¹, hmemX⟩, ?_, rfl⟩
      change (⟨b * (x' : G) * b⁻¹, hmemX⟩ : ↥a.X) ∈ Sbar.comap a.qX
      rw [Subgroup.mem_comap]
      rw [a.inner_bar (x' : G) x'.2]
      exact (Subgroup.mem_normalizer_iff.mp hdhatSbar _).mp hx'Sbar
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    apply Subgroup.eq_of_le_of_card_ge hle
    rw [Subgroup.card_map_of_injective (f := (MulAut.conj b).toMonoidHom)
      (MulAut.conj b).injective]
  have hcomm : ∃ s ∈ S, ⁅b, s⁆ ∉ (CFSG.pCore 2 ↥a.X).map a.X.subtype := by
    obtain ⟨t, ht, hne⟩ := hne_bar
    obtain ⟨x, hqx⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥a.X) t
    have hxSX : x ∈ SX := by
      change x ∈ Sbar.comap a.qX
      rw [Subgroup.mem_comap]
      rwa [show a.qX x = t by simpa [S23_9_AdjData.qX] using hqx]
    refine ⟨a.X.subtype x, Subgroup.mem_map_of_mem _ hxSX, ?_⟩
    have hmem : b * (x : G) * b⁻¹ ∈ a.X :=
      (Subgroup.mem_normalizer_iff.mp a.hbX (x : G)).mp x.2
    have hprod : (⟨⁅b, (x : G)⁆, a.X.mul_mem hmem (a.X.inv_mem x.2)⟩ : ↥a.X) =
        ⟨b * (x : G) * b⁻¹, hmem⟩ * x⁻¹ := by
      apply Subtype.ext
      simp [commutatorElement_def]
    have hqval : a.qX ⟨⁅b, (x : G)⁆, a.X.mul_mem hmem (a.X.inv_mem x.2)⟩ =
        ⁅a.dhat, t⁆ := by
      rw [hprod, map_mul, map_inv, a.inner_bar (x : G) x.2,
        show a.qX x = t by simpa [S23_9_AdjData.qX] using hqx]
      simp [commutatorElement_def]
    intro hmemP
    apply hne
    have h1 : a.qX ⟨⁅b, (x : G)⁆, a.X.mul_mem hmem (a.X.inv_mem x.2)⟩ = 1 := by
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥a.X))
        ⟨⁅b, (x : G)⁆, a.X.mul_mem hmem (a.X.inv_mem x.2)⟩ = 1
      exact (QuotientGroup.eq_one_iff _).mpr (by
        obtain ⟨n, hn, hny⟩ := hmemP
        have hxn : (⟨⁅b, (x : G)⁆, a.X.mul_mem hmem (a.X.inv_mem x.2)⟩ : ↥a.X) = n :=
          Subtype.ext hny.symm
        rwa [hxn])
    rwa [hqval] at h1
  exact ⟨S, SX, rfl, hmap, hSp, hbS, hcomm⟩

theorem S23_9_AdjData.commutator_twoSubgroup (a : S23_9_AdjData D Ch c hV d b hb r)
    {S : Subgroup G} (hSX : S ≤ a.X) (hSp : IsPGroup 2 S)
    (hbS : b ∈ Subgroup.normalizer (S : Set G))
    (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r) :
    ∃ R : Subgroup G, R = ⁅Subgroup.zpowers b, S⁆ ∧ R ≤ S ∧ IsPGroup 2 R ∧
      b ∈ Subgroup.normalizer (R : Set G) ∧ ⁅Subgroup.zpowers b, R⁆ = R := by
  let P : Subgroup G := Subgroup.zpowers b
  let R : Subgroup G := ⁅P, S⁆
  have hPS : P ≤ Subgroup.normalizer (S : Set G) := Subgroup.zpowers_le.mpr hbS
  have hRleS : R ≤ S := by
    change ⁅P, S⁆ ≤ S
    rw [Subgroup.commutator_comm]
    exact CFSG.Walter.commutator_zpowers_le_of_mem_normalizer hbS
  have hR2 : IsPGroup 2 R := IsPGroup.to_le hSp hRleS
  have hbR : b ∈ Subgroup.normalizer (R : Set G) := by
    rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have hconjS : S.map (MulAut.conj b).toMonoidHom = S :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hbS
    have hconjP : P.map (MulAut.conj b).toMonoidHom = P := by
      change (Subgroup.zpowers b).map (MulAut.conj b).toMonoidHom = Subgroup.zpowers b
      rw [MonoidHom.map_zpowers]
      change Subgroup.zpowers (b * b * b⁻¹) = Subgroup.zpowers b
      rw [show b * b * b⁻¹ = b by group]
    change (⁅P, S⁆).map (MulAut.conj b).toMonoidHom = ⁅P, S⁆
    rw [Subgroup.map_commutator, hconjP, hconjS]
  have hPR : ⁅P, R⁆ = R := by
    have hPcard : Nat.card P = r := by
      change Nat.card (Subgroup.zpowers b) = r
      rw [Nat.card_zpowers, hbr]
    have hcop : Nat.Coprime (Nat.card P) (Nat.card S) := by
      rw [hPcard]
      obtain ⟨k, hk⟩ := hSp.exists_card_eq
      rw [hk]
      exact (hr.odd_of_ne_two hr2).coprime_two_right.pow_right k
    have hsolv : Group.IsSolvable ↥S := by
      haveI : Group.IsNilpotent ↥S := hSp.isNilpotent
      infer_instance
    have hdouble := GL83.commutator_double_eq_self P S hPS hcop hsolv
    have hR_eq : R = ⁅S, P⁆ := Subgroup.commutator_comm P S
    rw [hR_eq, Subgroup.commutator_comm P ⁅S, P⁆]
    exact hdouble
  exact ⟨R, rfl, hRleS, hR2, hbR, hPR⟩

theorem S23_9_AdjData.commutator_image_involution (a : S23_9_AdjData D Ch c hV d b hb r)
    {S : Subgroup G} {SX : Subgroup ↥a.X} {Sbar : Subgroup (Bar2 a.X)}
    (hS : S = SX.map a.X.subtype) (hmap : SX.map a.qX = Sbar)
    (hSbarsq : ∀ z ∈ Sbar, z * z = 1) {R : Subgroup G}
    (hR : R = ⁅Subgroup.zpowers b, S⁆) (hRleS : R ≤ S)
    (hcomm : ∃ s ∈ S, ⁅b, s⁆ ∉ (CFSG.pCore 2 ↥a.X).map a.X.subtype) :
    ∃ z ∈ (R.subgroupOf a.X).map a.qX, z ≠ 1 ∧ z * z = 1 := by
  have hSX : S ≤ a.X := hS ▸ Subgroup.map_subtype_le SX
  obtain ⟨s, hs, hne⟩ := hcomm
  have hsub : S.subgroupOf a.X = SX := by
    rw [hS]
    change (SX.map a.X.subtype).comap a.X.subtype = SX
    exact Subgroup.comap_map_eq_self_of_injective a.X.subtype_injective SX
  have hqmap : (S.subgroupOf a.X).map a.qX = Sbar := by rw [hsub, hmap]
  have hmemR : ⁅b, s⁆ ∈ R := by
    rw [hR]
    exact Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers b) hs
  have hmemX : ⁅b, s⁆ ∈ a.X := hSX (hRleS hmemR)
  let z : Bar2 a.X := a.qX ⟨⁅b, s⁆, hmemX⟩
  have hmemSX : (⟨⁅b, s⁆, hmemX⟩ : ↥a.X) ∈ R.subgroupOf a.X :=
    Subgroup.mem_subgroupOf.mpr hmemR
  have hzR : z ∈ (R.subgroupOf a.X).map a.qX := Subgroup.mem_map_of_mem a.qX hmemSX
  have hzSbar : z ∈ Sbar := by
    have h' : z ∈ (S.subgroupOf a.X).map a.qX :=
      Subgroup.map_mono (Subgroup.subgroupOf_mono a.X hRleS) hzR
    rwa [hqmap] at h'
  refine ⟨z, hzR, ?_, hSbarsq z hzSbar⟩
  intro hz1
  have hq1 : a.qX ⟨⁅b, s⁆, hmemX⟩ = 1 := hz1
  change (QuotientGroup.mk' (CFSG.pCore 2 ↥a.X)) ⟨⁅b, s⁆, hmemX⟩ = 1 at hq1
  exact hne (Subgroup.mem_map_of_mem a.X.subtype
    ((QuotientGroup.eq_one_iff _).mp hq1))

theorem S23_9_AdjData.not_le_ker {K : Type} [Field K] [Finite K] [CharP K 2]
    (a : S23_9_AdjData D Ch c hV d b hb r)
    (e : Bar2 a.X ≃* Matrix.SpecialLinearGroup (Fin 2) K)
    {R : Subgroup G} (hRleX : R ≤ a.X)
    {z : Bar2 a.X} (hzR : z ∈ (R.subgroupOf a.X).map a.qX)
    (hz1 : z ≠ 1) (hzsq : z * z = 1) :
    ¬ barImage D.M R ≤ d.rep.ker := by
  have hXM : a.X ≤ D.M :=
    a.hXK.trans ((CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_Hinf_le _).trans inf_le_left)
  let qM : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  let incl : ↥a.X →* ↥D.M := Subgroup.inclusion hXM
  let ψ : ↥a.X →* Bar2 D.M := qM.comp incl
  let N : Subgroup ↥a.X := d.rep.ker.comap ψ
  intro hRker
  have hNnormal : N.Normal := by
    change (d.rep.ker.comap ψ).Normal
    infer_instance
  have hRN : R.subgroupOf a.X ≤ N := by
    intro x hx
    rw [Subgroup.mem_comap]
    have hxR : (x : G) ∈ R := Subgroup.mem_subgroupOf.mp hx
    have hxX : (x : G) ∈ a.X := hRleX hxR
    have hxM : (x : G) ∈ D.M := hXM hxX
    have hmem : qM ⟨(x : G), hxM⟩ ∈ barImage D.M R :=
      Subgroup.mem_map_of_mem qM (Subgroup.mem_subgroupOf.mpr hxR)
    have hker : qM ⟨(x : G), hxM⟩ ∈ d.rep.ker := hRker hmem
    have hψx : ψ x = qM ⟨(x : G), hxM⟩ := by
      change qM (incl x) = qM ⟨(x : G), hxM⟩
      congr 1
    rw [hψx]
    exact hker
  have hzN : z ∈ N.map a.qX := Subgroup.map_mono hRN hzR
  haveI : (N.map a.qX).Normal :=
    Subgroup.Normal.map hNnormal a.qX (by
      simpa [S23_9_AdjData.qX] using QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥a.X))
  have htopN : N.map a.qX = ⊤ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.sl2_normal_eq_top_of_involution
      e (N.map a.qX) hzN hz1 (by simpa [sq] using hzsq)
  haveI : N.Normal := hNnormal
  have hsup : N ⊔ (CFSG.pCore 2 ↥a.X) = ⊤ := by
    rw [eq_top_iff]
    intro x _
    have hx : a.qX x ∈ N.map a.qX := by rw [htopN]; exact Subgroup.mem_top x
    obtain ⟨n, hnN, hqn⟩ := Subgroup.mem_map.mp hx
    have hdiff : n⁻¹ * x ∈ CFSG.pCore 2 ↥a.X := by
      rw [MonoidHom.eq_iff] at hqn
      rw [show a.qX.ker = CFSG.pCore 2 ↥a.X from
        QuotientGroup.ker_mk' (CFSG.pCore 2 ↥a.X)] at hqn
      simpa [mul_inv_rev] using (CFSG.pCore 2 ↥a.X).inv_mem hqn
    have hmul : (↑(N ⊔ (CFSG.pCore 2 ↥a.X)) : Set ↥a.X) =
        (N : Set ↥a.X) * (CFSG.pCore 2 ↥a.X) :=
      Subgroup.normal_mul N (CFSG.pCore 2 ↥a.X)
    have hmem : n * (n⁻¹ * x) ∈ (N : Set ↥a.X) * (CFSG.pCore 2 ↥a.X) :=
      Set.mem_mul.mpr ⟨n, hnN, n⁻¹ * x, hdiff, rfl⟩
    rw [← hmul] at hmem
    rwa [show n * (n⁻¹ * x) = x by group] at hmem
  have hNtop : N = ⊤ := by
    refine CFSG.LieType.TitsSimplicity.eq_top_of_sup_eq_top
      (Subgroup.isPerfect_iff.mpr a.hXperf) ?_ hsup
    haveI : Group.IsNilpotent ↥(CFSG.pCore 2 ↥a.X) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥a.X)).isNilpotent
    infer_instance
  apply a.hnotker
  intro z0 hz0
  rw [MonoidHom.mem_ker]
  obtain ⟨x, hxX, rfl⟩ := Subgroup.mem_map.mp hz0
  have hxX' : (x : G) ∈ a.X := Subgroup.mem_subgroupOf.mp hxX
  have hψN : ψ ⟨(x : G), hxX'⟩ ∈ d.rep.ker := by
    have hmemN : (⟨(x : G), hxX'⟩ : ↥a.X) ∈ N := by
      rw [hNtop]
      exact Subgroup.mem_top _
    change (⟨(x : G), hxX'⟩ : ↥a.X) ∈ d.rep.ker.comap ψ at hmemN
    exact Subgroup.mem_comap.mp hmemN
  have hψ1 : d.rep (ψ ⟨(x : G), hxX'⟩) = 1 := by
    rwa [MonoidHom.mem_ker] at hψN
  change d.rep (qM ⟨(x : G), hXM hxX'⟩) = 1 at hψ1
  have harg : (⟨(x : G), hXM hxX'⟩ : ↥D.M) = x := Subtype.ext rfl
  rwa [harg] at hψ1

theorem S23_9_AdjData.isPGroup_barImage (a : S23_9_AdjData D Ch c hV d b hb r)
    {R : Subgroup G} (hR2 : IsPGroup 2 R) : IsPGroup 2 (barImage D.M R) := by
  change IsPGroup 2 ((R.subgroupOf D.M).map (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)))
  exact (hR2.comap_subtype (K := D.M)).map _

theorem S23_9_AdjData.orderOf_barImage_b (a : S23_9_AdjData D Ch c hV d b hb r)
    (hr : r.Prime) (hr2 : r ≠ 2) (hbr : orderOf b = r) :
    orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, c.hBM hb⟩) = r := by
  haveI : Fact r.Prime := ⟨hr⟩
  apply CFSG.GroupTheory.CoprimeTransport.orderOf_mk_eq_prime
  · intro hdvd
    obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥D.M)).exists_card_eq
    rw [hk] at hdvd
    exact hr2 ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow hdvd))
  · simpa using hbr

theorem S23_9_AdjData.barImage_normalizer (a : S23_9_AdjData D Ch c hV d b hb r)
    {R : Subgroup G} (hRleX : R ≤ a.X) (hXM : a.X ≤ D.M)
    (hbR : b ∈ Subgroup.normalizer (R : Set G)) :
    QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, c.hBM hb⟩ ∈
      Subgroup.normalizer (barImage D.M R : Set (Bar2 D.M)) := by
  have h := CFSG.GroupTheory.map_subgroupOf_le_normalizer (M := D.M)
    (B := Subgroup.zpowers b) (X := R) (f := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M))
    (Subgroup.zpowers_le.mpr hbR)
  have hbP : QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, c.hBM hb⟩ ∈
      ((Subgroup.zpowers b).subgroupOf D.M).map
        (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) :=
    Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.mpr (Subgroup.mem_zpowers b))
  simpa [barImage] using h hbP

theorem S23_9_AdjData.barImage_commutator (a : S23_9_AdjData D Ch c hV d b hb r)
    {R : Subgroup G} (hRleX : R ≤ a.X) (hXM : a.X ≤ D.M)
    (hPR : ⁅Subgroup.zpowers b, R⁆ = R) :
    ⁅Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨b, c.hBM hb⟩),
      barImage D.M R⁆ = barImage D.M R := by
  have h := CFSG.GroupTheory.commutator_zpowers_map_subgroupOf_eq
    (f := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)) (c.hBM hb) (hRleX.trans hXM) hPR
  simpa [barImage] using h

private theorem orderOf_two_ne_two_pow_of_odd_dvd
    (hr : r.Prime) {s : ℕ} (hodd : Odd s) (hsdvd : r ∣ 2 ^ s - 1)
    {k : ℕ} (hk : orderOf (2 : ZMod r) = 2 ^ k) : False := by
  have hpow : (2 : ZMod r) ^ s = 1 := by
    have hmod : 2 ^ s ≡ 1 [MOD r] :=
      ((Nat.modEq_iff_dvd' Nat.one_le_two_pow).mpr hsdvd).symm
    have h := (ZMod.natCast_eq_natCast_iff (2 ^ s) 1 r).2 hmod
    simpa using h
  have hdvd_s : orderOf (2 : ZMod r) ∣ s := orderOf_dvd_of_pow_eq_one hpow
  have hodd_ord : Odd (orderOf (2 : ZMod r)) := Odd.of_dvd_nat hodd hdvd_s
  have hord_ne_one : orderOf (2 : ZMod r) ≠ 1 := by
    intro h1
    have h2 : (2 : ZMod r) = 1 := orderOf_eq_one_iff.mp h1
    have hmod : 2 ≡ 1 [MOD r] :=
      (ZMod.natCast_eq_natCast_iff 2 1 r).1 (by simpa using h2)
    exact hr.not_dvd_one ((Nat.modEq_iff_dvd' (by norm_num : 1 ≤ 2)).mp hmod.symm)
  rcases Nat.eq_zero_or_pos k with h0 | hk0
  · rw [hk, h0, pow_zero] at hord_ne_one
    exact hord_ne_one rfl
  · rw [hk] at hodd_ord
    exact absurd hodd_ord (Nat.not_odd_iff_even.mpr
      (Nat.even_pow.mpr ⟨even_two, hk0.ne'⟩))

end A3

theorem s23_9_A3_of (D : Data G) (Ch : Choice2011 G) : S23_9_A3 D Ch := by
  intro h1930 c hV d b hb r hr hr2 hbr hs dfix hrq a hnotpow
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eK⟩⟩ := a.hXsl
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  letI : Fintype K := Fintype.ofFinite K
  haveI : Fact r.Prime := ⟨hr⟩
  haveI : CharP K 2 :=
    charP_of_card_eq_prime_pow (by rwa [← Nat.card_eq_fintype_card])
  let e : Bar2 a.X ≃* Matrix.SpecialLinearGroup (Fin 2) K :=
    eK.trans (CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL 2 K).symm
  obtain ⟨Sbar, hSbarp, _, hSbarsq, hdhatSbar, hne_bar⟩ :=
    a.exists_bar_twoSubgroup e hKcard hr hr2
  obtain ⟨S, SX, hS, hmap, hSp, hbS, hcomm⟩ :=
    a.exists_twoSubgroup Sbar hSbarp hSbarsq hdhatSbar hne_bar
  have hSX : S ≤ a.X := hS ▸ Subgroup.map_subtype_le SX
  obtain ⟨R, hR, hRleS, hR2, hbR, hPR⟩ :=
    a.commutator_twoSubgroup hSX hSp hbS hr hr2 hbr
  have hRleX : R ≤ a.X := hRleS.trans hSX
  obtain ⟨z, hzR, hz1, hzsq⟩ :=
    a.commutator_image_involution hS hmap hSbarsq hR hRleS hcomm
  have hRnt : ¬ barImage D.M R ≤ d.rep.ker := a.not_le_ker e hRleX hzR hz1 hzsq
  have hXM : a.X ≤ D.M :=
    a.hXK.trans ((CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_Hinf_le _).trans inf_le_left)
  let qM : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  let bbar : Bar2 D.M := qM ⟨b, c.hBM hb⟩
  let T : Subgroup (Bar2 D.M) := barImage D.M R
  have hT2 : IsPGroup 2 T := a.isPGroup_barImage hR2
  have hbbar_order : orderOf bbar = r := a.orderOf_barImage_b hr hr2 hbr
  have hbbar_normalizer : bbar ∈ Subgroup.normalizer (T : Set (Bar2 D.M)) :=
    a.barImage_normalizer hRleX hXM hbR
  have hTb : ⁅Subgroup.zpowers bbar, T⁆ = T := a.barImage_commutator hRleX hXM hPR
  have hfix : d.fixV (Subgroup.zpowers bbar) = ⊥ := by
    have h : barImage D.M (Subgroup.zpowers b) = Subgroup.zpowers bbar := by
      change ((Subgroup.zpowers b).subgroupOf D.M).map qM = Subgroup.zpowers bbar
      rw [show (Subgroup.zpowers b).subgroupOf D.M =
          Subgroup.zpowers ⟨b, c.hBM hb⟩ by
        apply Subgroup.map_injective D.M.subtype_injective
        rw [Subgroup.map_subgroupOf_eq_of_le (Subgroup.zpowers_le.mpr (c.hBM hb)),
          MonoidHom.map_zpowers]
        rfl]
      rw [MonoidHom.map_zpowers]
    rw [← h]
    exact dfix
  have hnt : ∃ t ∈ T, d.rep t ≠ 1 := by
    by_contra h
    push Not at h
    exact hRnt (by
      intro z0 hz0
      rw [MonoidHom.mem_ker]
      exact h z0 hz0)
  obtain ⟨k, hk⟩ := CFSG.LocalAnalysis.UniquenessCase.UCK.orderOf_two_eq_two_pow_of_fixV_eq_bot
    (p := d.q) (Γ := Bar2 D.M) (V := Additive (↥d.E ⧸ frattini ↥d.E))
    (ρ := d.rep) (T := T) (b := bbar) (r := r)
    d.hq2 hT2 hr hr2 hbbar_order hbbar_normalizer hTb hfix hnt
  obtain ⟨s, -, hodd_s, -, hsdvd⟩ := hs
  exact orderOf_two_ne_two_pow_of_odd_dvd hr hodd_s hsdvd hk

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

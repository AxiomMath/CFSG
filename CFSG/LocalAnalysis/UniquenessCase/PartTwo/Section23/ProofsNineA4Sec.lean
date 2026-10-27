module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsNineA4
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22m
public import CFSG.GroupTheory.InvariantMinimal

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC PartTwo Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace S23_9_AdjData

variable {D : Data G} {Ch : Choice2011 G} {c : Ctx23L D Ch} {hV : IsElemAbelian 2 c.V}
  {d : S23_9_A0Data D Ch c} {b : G} {hb : b ∈ c.B0} {r : ℕ}

noncomputable def ctildeAction (a : S23_9_AdjData D Ch c hV d b hb r) :
    ↥(Subgroup.zpowers (ctilde a)) →* MulAut ↥a.X :=
  (a.X.normalizerMonoidHom).comp
    (Subgroup.inclusion (Subgroup.zpowers_le.mpr (ctilde_mem_normalizer a)))

theorem ctildeAction_apply (a : S23_9_AdjData D Ch c hV d b hb r)
    (s : ↥(Subgroup.zpowers (ctilde a))) (x : ↥a.X) :
    ((ctildeAction a s x : ↥a.X) : G) = (s : G) * (x : G) * (s : G)⁻¹ :=
  Subgroup.normalizerMonoidHom_apply_apply_coe a.X _ _

noncomputable def X1 (a : S23_9_AdjData D Ch c hV d b hb r) : Subgroup ↥a.X :=
  ((ctildeAction a) ⟨ctilde a, Subgroup.mem_zpowers (ctilde a)⟩).toMonoidHom.eqLocus
    (MonoidHom.id ↥a.X)

theorem mem_X1 {a : S23_9_AdjData D Ch c hV d b hb r} {x : ↥a.X} :
    x ∈ X1 a ↔
      (ctildeAction a) ⟨ctilde a, Subgroup.mem_zpowers (ctilde a)⟩ x = x :=
  Iff.rfl

private def ctildeGen (a : S23_9_AdjData D Ch c hV d b hb r) :
    ↥(Subgroup.zpowers (ctilde a)) :=
  ⟨ctilde a, Subgroup.mem_zpowers (ctilde a)⟩

private theorem isPGroup_zpowers_ctilde (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) :
    IsPGroup 3 ↥(Subgroup.zpowers (ctilde a)) := by
  refine IsPGroup.of_card_dvd_pow (n := 1) ?_
  rw [Nat.card_zpowers]
  simpa using orderOf_dvd_of_pow_eq_one (ctilde_pow_three a hbr hr3)

private theorem not_three_dvd_card_pCore_X (a : S23_9_AdjData D Ch c hV d b hb r) :
    ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥a.X) := by
  intro hdiv
  obtain ⟨k, hk⟩ := (CFSG.pCore_isPGroup (p := 2) (G := ↥a.X)).exists_card_eq
  rw [hk] at hdiv
  have h32 : 3 ∣ 2 := Nat.prime_three.dvd_of_dvd_pow hdiv
  omega

private theorem ctildeAction_mem_pCore (a : S23_9_AdjData D Ch c hV d b hb r)
    (a' : ↥(Subgroup.zpowers (ctilde a))) {n : ↥a.X}
    (hn : n ∈ CFSG.pCore 2 ↥a.X) :
    ctildeAction a a' n ∈ CFSG.pCore 2 ↥a.X := by
  have h := Subgroup.characteristic_iff_map_eq.mp
    (CFSG.pCore_characteristic (p := 2)) (ctildeAction a a')
  exact h ▸ Subgroup.mem_map_of_mem (f := (ctildeAction a a' : ↥a.X →* ↥a.X)) hn

private theorem quotientAction_ctilde_eq_one (a : S23_9_AdjData D Ch c hV d b hb r)
    (hN : ∀ a' : ↥(Subgroup.zpowers (ctilde a)), ∀ n ∈ CFSG.pCore 2 ↥a.X,
      ctildeAction a a' n ∈ CFSG.pCore 2 ↥a.X)
    (a' : ↥(Subgroup.zpowers (ctilde a))) :
    CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
      (ctildeAction a) (CFSG.pCore 2 ↥a.X) hN a' = 1 := by
  have hgen : CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
      (ctildeAction a) (CFSG.pCore 2 ↥a.X) hN (ctildeGen a) = 1 := by
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction_mk,
        MulAut.one_apply, QuotientGroup.eq]
      have hmem : ctildeAction a (ctildeGen a) y * y⁻¹ ∈ CFSG.pCore 2 ↥a.X := by
        obtain ⟨o, ho, hcoe⟩ := Subgroup.mem_map.mp (ctilde_centralizes_mod_O a y.2)
        have hφy : ctildeAction a (ctildeGen a) y * y⁻¹ = o := by
          apply Subtype.ext
          rw [Subgroup.coe_mul, Subgroup.coe_inv, ctildeAction_apply]
          simpa [ctildeGen] using hcoe.symm
        rw [hφy]
        exact ho
      have hOnormal : (CFSG.pCore 2 ↥a.X).Normal := CFSG.pCore_normal
      have hinv : y * (ctildeAction a (ctildeGen a) y)⁻¹ ∈ CFSG.pCore 2 ↥a.X := by
        simpa [mul_inv_rev] using (CFSG.pCore 2 ↥a.X).inv_mem hmem
      have hconj := hOnormal.conj_mem (y * (ctildeAction a (ctildeGen a) y)⁻¹) hinv y⁻¹
      rwa [show y⁻¹ * (y * (ctildeAction a (ctildeGen a) y)⁻¹) * y⁻¹⁻¹ =
        (ctildeAction a (ctildeGen a) y)⁻¹ * y by group] at hconj
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp a'.2
  have ha' : a' = (ctildeGen a) ^ k := by
    apply Subtype.ext
    rw [Subgroup.coe_zpow]
    simpa [ctildeGen] using hk.symm
  rw [ha', map_zpow, hgen, one_zpow]

theorem map_qX_X1_eq_top (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) :
    (X1 a).map a.qX = ⊤ := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hA : IsPGroup 3 ↥(Subgroup.zpowers (ctilde a)) := isPGroup_zpowers_ctilde a hbr hr3
  have hcop : ¬ 3 ∣ Nat.card (CFSG.pCore 2 ↥a.X) := not_three_dvd_card_pCore_X a
  have hN : ∀ a' : ↥(Subgroup.zpowers (ctilde a)), ∀ n ∈ CFSG.pCore 2 ↥a.X,
      ctildeAction a a' n ∈ CFSG.pCore 2 ↥a.X := ctildeAction_mem_pCore a
  have hq1 := quotientAction_ctilde_eq_one a hN
  have hlift := CFSG.Semidihedral.Principal.coprime_fixed_point_lifting 3 hA
    (ctildeAction a) (CFSG.pCore 2 ↥a.X) hN hcop
  rw [eq_top_iff]
  intro q _
  have hq : q ∈ {q : ↥a.X ⧸ CFSG.pCore 2 ↥a.X |
      ∀ a' : ↥(Subgroup.zpowers (ctilde a)),
        CFSG.Semidihedral.Principal.CoprimeFixedPoint.quotientAction
          (ctildeAction a) (CFSG.pCore 2 ↥a.X) hN a' q = q} :=
    fun a' => by simp [hq1 a']
  rw [hlift] at hq
  obtain ⟨x, hx, hmk⟩ := hq
  exact ⟨x, mem_X1.mpr (hx (ctildeGen a)), hmk⟩

noncomputable def X2 (a : S23_9_AdjData D Ch c hV d b hb r) : Subgroup G :=
  Hinf ((X1 a).map a.X.subtype)

theorem X2_le_X (a : S23_9_AdjData D Ch c hV d b hb r) : X2 a ≤ a.X :=
  (uc22p21c_Hinf_le _).trans (Subgroup.map_subtype_le _)

theorem X2_perfect (a : S23_9_AdjData D Ch c hV d b hb r) : ⁅X2 a, X2 a⁆ = X2 a :=
  uc22p21c_Hinf_perfect _

theorem map_qX_X2_eq_top (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3) :
    ((X2 a).subgroupOf a.X).map a.qX = ⊤ := by
  let Y : Subgroup G := (X1 a).map a.X.subtype
  have hYX : Y ≤ a.X := Subgroup.map_subtype_le _
  let g : ↥Y →* ↥a.X := Subgroup.inclusion hYX
  let f : ↥Y →* Bar2 a.X := a.qX.comp g
  have hf : Function.Surjective f := by
    intro q
    have hq : q ∈ (X1 a).map a.qX := by
      rw [map_qX_X1_eq_top a hbr hr3]
      exact Subgroup.mem_top q
    obtain ⟨x, hx, hqx⟩ := Subgroup.mem_map.mp hq
    refine ⟨⟨(x : G), Subgroup.mem_map_of_mem a.X.subtype hx⟩, ?_⟩
    have hgy : g ⟨(x : G), Subgroup.mem_map_of_mem a.X.subtype hx⟩ = x := Subtype.ext rfl
    rw [show f ⟨(x : G), Subgroup.mem_map_of_mem a.X.subtype hx⟩ =
      a.qX (g ⟨(x : G), Subgroup.mem_map_of_mem a.X.subtype hx⟩) from rfl, hgy, hqx]
  haveI : Group.IsPerfect (Bar2 a.X) :=
    CFSG.GroupTheory.isPerfect_of_isSLn_two a.hm2 a.hXsl
  have hres : (CFSG.perfectResidual ↥Y).map f = ⊤ := by
    have h := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq f hf
    rw [show CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual ↥Y =
      CFSG.perfectResidual ↥Y from rfl] at h
    rw [h]
    exact top_le_iff.mp
      (CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidual
        (⊤ : Subgroup (Bar2 a.X)) (by infer_instance))
  have hcomp : Y.subtype = a.X.subtype.comp g := MonoidHom.ext fun _ => rfl
  have hsub : (X2 a).subgroupOf a.X = (CFSG.perfectResidual ↥Y).map g := by
    change (((CFSG.perfectResidual ↥Y).map Y.subtype)).subgroupOf a.X = _
    rw [hcomp, ← Subgroup.map_map]
    exact Subgroup.comap_map_eq_self_of_injective a.X.subtype_injective _
  rw [hsub, Subgroup.map_map]
  exact hres

theorem dRoot_mem_X1 (a : S23_9_AdjData D Ch c hV d b hb r) :
    (⟨a.dRoot, a.hdX⟩ : ↥a.X) ∈ X1 a := by
  rw [mem_X1]
  apply Subtype.ext
  rw [ctildeAction_apply, ctilde_comm_dRoot]
  group

theorem X2_subgroupOf_le_X1 (a : S23_9_AdjData D Ch c hV d b hb r) :
    (X2 a).subgroupOf a.X ≤ X1 a := by
  intro x hx
  exact (Subgroup.mem_map_iff_mem (f := a.X.subtype) a.X.subtype_injective).mp
    (uc22p21c_Hinf_le ((X1 a).map a.X.subtype) hx)

theorem normal_X2_subgroupOf_X1 (a : S23_9_AdjData D Ch c hV d b hb r) :
    (((X2 a).subgroupOf a.X).subgroupOf (X1 a)).Normal := by
  have hNle : (X2 a).subgroupOf a.X ≤ X1 a := X2_subgroupOf_le_X1 a
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer hNle).mpr ?_
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro n
  have hxY : ((x : ↥a.X) : G) ∈ (X1 a).map a.X.subtype := ⟨x, hx, rfl⟩
  have hnorm := uc22p22m_le_normalizer_Hinf ((X1 a).map a.X.subtype) hxY
  rw [Subgroup.mem_normalizer_iff] at hnorm
  constructor
  · intro hn
    have hn' : (n : G) ∈ Hinf ((X1 a).map a.X.subtype) := Subgroup.mem_subgroupOf.mp hn
    have hres : (x : G) * (n : G) * ((x : G))⁻¹ ∈ Hinf ((X1 a).map a.X.subtype) :=
      (hnorm (n : G)).mp hn'
    exact Subgroup.mem_subgroupOf.mpr hres
  · intro hn
    have hn' : (x : G) * (n : G) * ((x : G))⁻¹ ∈ Hinf ((X1 a).map a.X.subtype) :=
      Subgroup.mem_subgroupOf.mp hn
    have hres : (n : G) ∈ Hinf ((X1 a).map a.X.subtype) := (hnorm (n : G)).mpr hn'
    exact Subgroup.mem_subgroupOf.mpr hres

theorem isPGroup_quotient_X1_X2 (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    [hN : (((X2 a).subgroupOf a.X).subgroupOf (X1 a)).Normal] :
    IsPGroup 2 (↥(X1 a) ⧸ (((X2 a).subgroupOf a.X).subgroupOf (X1 a))) := by
  have hNle : (X2 a).subgroupOf a.X ≤ X1 a := X2_subgroupOf_le_X1 a
  have hKpg : IsPGroup 2 ↥(X1 a ⊓ CFSG.pCore 2 ↥a.X) :=
    (CFSG.pCore_isPGroup (p := 2) (G := ↥a.X)).to_inf_right
  let φ : ↥(X1 a ⊓ CFSG.pCore 2 ↥a.X) →*
      (↥(X1 a) ⧸ (((X2 a).subgroupOf a.X).subgroupOf (X1 a))) :=
    (QuotientGroup.mk' (((X2 a).subgroupOf a.X).subgroupOf (X1 a))).comp
      (Subgroup.inclusion (inf_le_left : X1 a ⊓ CFSG.pCore 2 ↥a.X ≤ X1 a))
  have hφ : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective _ y
    have hq : a.qX (x : ↥a.X) ∈ ((X2 a).subgroupOf a.X).map a.qX := by
      rw [map_qX_X2_eq_top a hbr hr3]
      exact Subgroup.mem_top _
    obtain ⟨n, hn, hqn⟩ := Subgroup.mem_map.mp hq
    have hker : n⁻¹ * (x : ↥a.X) ∈ CFSG.pCore 2 ↥a.X := by
      have h : n⁻¹ * (x : ↥a.X) ∈ a.qX.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hqn, inv_mul_cancel]
      rwa [show a.qX.ker = CFSG.pCore 2 ↥a.X from QuotientGroup.ker_mk' _] at h
    have hkx : n⁻¹ * (x : ↥a.X) ∈ X1 a :=
      (X1 a).mul_mem ((X1 a).inv_mem (hNle hn)) x.2
    let k : ↥(X1 a) := ⟨n⁻¹ * (x : ↥a.X), hkx⟩
    refine ⟨⟨n⁻¹ * (x : ↥a.X), Subgroup.mem_inf.mpr ⟨hkx, hker⟩⟩, ?_⟩
    have hxeq : x = (⟨n, hNle hn⟩ : ↥(X1 a)) * k := by
      apply Subtype.ext
      show (x : ↥a.X) = n * (n⁻¹ * (x : ↥a.X))
      group
    have h1 : QuotientGroup.mk' (((X2 a).subgroupOf a.X).subgroupOf (X1 a))
        (⟨n, hNle hn⟩ : ↥(X1 a)) = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (Subgroup.mem_subgroupOf.mpr hn)
    have hxk : QuotientGroup.mk' (((X2 a).subgroupOf a.X).subgroupOf (X1 a)) x =
        QuotientGroup.mk' (((X2 a).subgroupOf a.X).subgroupOf (X1 a)) k := by
      rw [hxeq, map_mul, h1, one_mul]
    rw [hxk]
    rfl
  exact hKpg.of_surjective φ hφ

theorem dRoot_mem_X2 (a : S23_9_AdjData D Ch c hV d b hb r) (hbr : orderOf b = r)
    (hr3 : r = 3) : a.dRoot ∈ X2 a := by
  have hNle : (X2 a).subgroupOf a.X ≤ X1 a := X2_subgroupOf_le_X1 a
  haveI : (((X2 a).subgroupOf a.X).subgroupOf (X1 a)).Normal := normal_X2_subgroupOf_X1 a
  have hpg := isPGroup_quotient_X1_X2 a hbr hr3
  have h3 : orderOf (⟨a.dRoot, a.hdX⟩ : ↥a.X) = 3 := by
    rw [Subgroup.orderOf_mk, a.hdorder, hr3]
  have hdvd3 : orderOf (QuotientGroup.mk' (((X2 a).subgroupOf a.X).subgroupOf (X1 a))
      ⟨⟨a.dRoot, a.hdX⟩, dRoot_mem_X1 a⟩) ∣ 3 := by
    have h := orderOf_map_dvd (QuotientGroup.mk' (((X2 a).subgroupOf a.X).subgroupOf (X1 a)))
      (⟨⟨a.dRoot, a.hdX⟩, dRoot_mem_X1 a⟩ : ↥(X1 a))
    rw [Subgroup.orderOf_mk, h3] at h
    exact h
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hpg
  have hdvd2 : orderOf (QuotientGroup.mk' (((X2 a).subgroupOf a.X).subgroupOf (X1 a))
      ⟨⟨a.dRoot, a.hdX⟩, dRoot_mem_X1 a⟩) ∣ 2 ^ j := by
    rw [← hj]
    exact orderOf_dvd_natCard _
  have hmem : (⟨⟨a.dRoot, a.hdX⟩, dRoot_mem_X1 a⟩ : ↥(X1 a)) ∈
      ((X2 a).subgroupOf a.X).subgroupOf (X1 a) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hdvd3 with h1 | h3'
    · exact (QuotientGroup.eq_one_iff _).mp (orderOf_eq_one_iff.mp h1)
    · exact absurd (Nat.prime_three.dvd_of_dvd_pow (h3' ▸ hdvd2)) (by norm_num)
  have hmem' : (⟨a.dRoot, a.hdX⟩ : ↥a.X) ∈ (X2 a).subgroupOf a.X :=
    Subgroup.mem_subgroupOf.mpr hmem
  exact Subgroup.mem_subgroupOf.mp hmem'

private theorem fixV_inf_fixV_eq_bot_of_barImage (a : S23_9_AdjData D Ch c hV d b hb r)
    {bc bd bb : Bar2 D.M}
    (hbc : barImage D.M (Subgroup.zpowers (ctilde a)) = Subgroup.zpowers bc)
    (hbd : barImage D.M (Subgroup.zpowers a.dRoot) = Subgroup.zpowers bd)
    (hbb : barImage D.M (Subgroup.zpowers b) = Subgroup.zpowers bb)
    (hbb_eq : bb = bc * bd)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥) :
    d.fixV (barImage D.M (Subgroup.zpowers (ctilde a))) ⊓
      d.fixV (barImage D.M (Subgroup.zpowers a.dRoot)) = ⊥ := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  rw [Submodule.eq_bot_iff]
  intro v hv
  rw [Submodule.mem_inf] at hv
  obtain ⟨hvc, hvd⟩ := hv
  have hvc' : d.rep bc v = v := by
    rw [hbc] at hvc
    exact hvc bc (Subgroup.mem_zpowers bc)
  have hvd' : d.rep bd v = v := by
    rw [hbd] at hvd
    exact hvd bd (Subgroup.mem_zpowers bd)
  have hvb : d.rep bb v = v := by
    rw [hbb_eq, map_mul, Module.End.mul_apply, hvd', hvc']
  have hmem : v ∈ d.fixV (barImage D.M (Subgroup.zpowers b)) := by
    rw [hbb]
    exact (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_fixV_zpowers_uc6 d.rep bb v).mpr hvb
  rw [hfixb] at hmem
  simpa using hmem

theorem fixV_ctilde_inf_fixV_dRoot_eq_bot (a : S23_9_AdjData D Ch c hV d b hb r)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥) :
    d.fixV (barImage D.M (Subgroup.zpowers (ctilde a))) ⊓
      d.fixV (barImage D.M (Subgroup.zpowers a.dRoot)) = ⊥ := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  have hXM : a.X ≤ D.M :=
    a.hXK.trans ((CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p21c_Hinf_le _).trans inf_le_left)
  have hdM : a.dRoot ∈ D.M := hXM a.hdX
  have hcM : ctilde a ∈ D.M := by
    rw [ctilde_eq]
    exact D.M.mul_mem (c.hBM hb) (D.M.inv_mem hdM)
  have hb_eq : ctilde a * a.dRoot = b := by
    rw [ctilde_eq]
    group
  let qM : ↥D.M →* Bar2 D.M := QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)
  let bc : Bar2 D.M := qM ⟨ctilde a, hcM⟩
  let bd : Bar2 D.M := qM ⟨a.dRoot, hdM⟩
  let bb : Bar2 D.M := qM ⟨b, c.hBM hb⟩
  have hbc : barImage D.M (Subgroup.zpowers (ctilde a)) = Subgroup.zpowers bc :=
    barImage_zpowers_eq hcM
  have hbd : barImage D.M (Subgroup.zpowers a.dRoot) = Subgroup.zpowers bd :=
    barImage_zpowers_eq hdM
  have hbb : barImage D.M (Subgroup.zpowers b) = Subgroup.zpowers bb :=
    barImage_zpowers_eq (c.hBM hb)
  have hbb_eq : bb = bc * bd := by
    show qM ⟨b, c.hBM hb⟩ = qM ⟨ctilde a, hcM⟩ * qM ⟨a.dRoot, hdM⟩
    rw [← map_mul]
    exact congrArg qM (Subtype.ext hb_eq.symm)
  exact fixV_inf_fixV_eq_bot_of_barImage a hbc hbd hbb hbb_eq hfixb

abbrev A0V (d : S23_9_A0Data D Ch c) : Type := Additive (↥d.E ⧸ frattini ↥d.E)

noncomputable instance instAddCommGroupA0V (d : S23_9_A0Data D Ch c) : AddCommGroup (A0V d) := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  infer_instance

noncomputable instance instModuleA0V (d : S23_9_A0Data D Ch c) : Module (ZMod d.q) (A0V d) := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  exact IsElementaryAbelian.isVectorSpace d.q

theorem X2_le_DM (a : S23_9_AdjData D Ch c hV d b hb r) : X2 a ≤ D.M :=
  (X2_le_X a).trans (a.hXK.trans ((uc22p21c_Hinf_le _).trans inf_le_left))

theorem dRoot_mem_DM (a : S23_9_AdjData D Ch c hV d b hb r) : a.dRoot ∈ D.M :=
  (a.hXK.trans ((uc22p21c_Hinf_le _).trans inf_le_left)) a.hdX

@[expose] noncomputable def U (a : S23_9_AdjData D Ch c hV d b hb r) :
    Submodule (ZMod d.q) (A0V d) :=
  d.fixV (barImage D.M (Subgroup.zpowers (ctilde a)))

@[expose] noncomputable def rhoX (a : S23_9_AdjData D Ch c hV d b hb r) :
    Representation (ZMod d.q) ↥(X2 a) (A0V d) :=
  d.rep.comp ((QuotientGroup.mk' (CFSG.pCore 2 ↥D.M)).comp (Subgroup.inclusion (X2_le_DM a)))

theorem rhoX_apply (a : S23_9_AdjData D Ch c hV d b hb r) (g : ↥(X2 a)) (v : A0V d) :
    rhoX a g v =
      d.rep (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨(g : G), X2_le_DM a g.2⟩) v :=
  rfl

theorem ctilde_comm_of_mem_X2 (a : S23_9_AdjData D Ch c hV d b hb r) {g : G}
    (hg : g ∈ X2 a) : ctilde a * g = g * ctilde a := by
  have hgX : g ∈ a.X := X2_le_X a hg
  have hgX1 : (⟨g, hgX⟩ : ↥a.X) ∈ X1 a :=
    X2_subgroupOf_le_X1 a (Subgroup.mem_subgroupOf.mpr hg)
  have hfix := mem_X1.mp hgX1
  have h : g = ctilde a * g * (ctilde a)⁻¹ := by
    have h' := a.ctildeAction_apply ⟨ctilde a, Subgroup.mem_zpowers (ctilde a)⟩ ⟨g, hgX⟩
    simp only [hfix] at h'
    simpa using h'
  have h2 : g * ctilde a = ctilde a * g := by
    calc g * ctilde a = (ctilde a * g * (ctilde a)⁻¹) * ctilde a := by
          conv_lhs => rw [h]
      _ = ctilde a * g := by group
  exact h2.symm

theorem commute_barImage_zwpowers (a : S23_9_AdjData D Ch c hV d b hb r) {g : G}
    (hg : g ∈ X2 a) :
    ∀ c ∈ barImage D.M (Subgroup.zpowers (ctilde a)),
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, X2_le_DM a hg⟩) * c =
        c * QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, X2_le_DM a hg⟩ := by
  have hXM : a.X ≤ D.M :=
    a.hXK.trans ((uc22p21c_Hinf_le _).trans inf_le_left)
  have hcM : ctilde a ∈ D.M := by
    rw [ctilde_eq]
    exact D.M.mul_mem (c.hBM hb) (D.M.inv_mem (hXM a.hdX))
  have hcomm : ctilde a * g = g * ctilde a := a.ctilde_comm_of_mem_X2 hg
  have hbcq : Commute (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨ctilde a, hcM⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, X2_le_DM a hg⟩) := by
    show QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨ctilde a, hcM⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, X2_le_DM a hg⟩ =
      QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, X2_le_DM a hg⟩ *
        QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨ctilde a, hcM⟩
    rw [← map_mul, ← map_mul]
    exact congrArg _ (Subtype.ext hcomm)
  intro c hc
  rw [barImage_zpowers_eq hcM] at hc
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hc
  rw [← hk]
  exact (hbcq.zpow_left k).symm

theorem U_invariant (a : S23_9_AdjData D Ch c hV d b hb r) {g : G} (hg : g ∈ X2 a)
    {v : A0V d} (hv : v ∈ U a) :
    d.rep (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨g, X2_le_DM a hg⟩) v ∈ U a := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  exact CFSG.GroupTheory.fixV_le_comap_fixV_of_commute (p := d.q) d.rep
    (a.commute_barImage_zwpowers hg) hv

theorem exists_W (a : S23_9_AdjData D Ch c hV d b hb r) (hc : d.fixV
      (barImage D.M (Subgroup.zpowers (ctilde a))) ≠ ⊥) :
    ∃ W : Submodule (ZMod d.q) (A0V d), W ≤ U a ∧ W ≠ ⊥ ∧
      (∀ g : ↥(X2 a), ∀ w ∈ W, rhoX a g w ∈ W) ∧
      ∀ W' : Submodule (ZMod d.q) (A0V d), W' ≤ W →
        (∀ g : ↥(X2 a), ∀ w ∈ W', rhoX a g w ∈ W') → W' = ⊥ ∨ W' = W := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  have hInv : ∀ g : ↥(X2 a), ∀ v ∈ U a, rhoX a g v ∈ U a := by
    intro g v hv
    exact a.U_invariant g.2 hv
  exact CFSG.GroupTheory.exists_minimal_invariant_submodule (p := d.q) (rhoX a) hc hInv

theorem fixV_dRoot_inf_W_eq_bot (a : S23_9_AdjData D Ch c hV d b hb r)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    {W : Submodule (ZMod d.q) (A0V d)} (hWU : W ≤ U a) :
    d.fixV (barImage D.M (Subgroup.zpowers a.dRoot)) ⊓ W = ⊥ := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  have h := a.fixV_ctilde_inf_fixV_dRoot_eq_bot hfixb
  have hle : d.fixV (barImage D.M (Subgroup.zpowers a.dRoot)) ⊓ W ≤ ⊥ := by
    calc d.fixV (barImage D.M (Subgroup.zpowers a.dRoot)) ⊓ W ≤
          d.fixV (barImage D.M (Subgroup.zpowers a.dRoot)) ⊓
            d.fixV (barImage D.M (Subgroup.zpowers (ctilde a))) := inf_le_inf_left _ hWU
      _ = d.fixV (barImage D.M (Subgroup.zpowers (ctilde a))) ⊓
            d.fixV (barImage D.M (Subgroup.zpowers a.dRoot)) := inf_comm _ _
      _ = ⊥ := h
  exact le_bot_iff.mp hle

theorem exists_dRoot_act_ne (a : S23_9_AdjData D Ch c hV d b hb r)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    {W : Submodule (ZMod d.q) (A0V d)} (hWU : W ≤ U a) (hWne : W ≠ ⊥) :
    ∃ w ∈ W, d.rep (QuotientGroup.mk' (CFSG.pCore 2 ↥D.M) ⟨a.dRoot, a.dRoot_mem_DM⟩) w ≠ w := by
  letI : Fact d.q.Prime := ⟨d.hq⟩
  letI : d.E.Normal := d.hEnorm
  letI : IsPGroup d.q ↥d.E := d.hEp
  letI : IsElementaryAbelian d.q (↥d.E ⧸ frattini ↥d.E) := d.hEel
  letI : CommGroup (↥d.E ⧸ frattini ↥d.E) := IsMulCommutative.instCommGroup
  by_contra h
  push Not at h
  have hfix : W ≤ d.fixV (barImage D.M (Subgroup.zpowers a.dRoot)) := by
    intro w hw
    rw [barImage_zpowers_eq a.dRoot_mem_DM]
    exact (CFSG.LocalAnalysis.UniquenessCase.UC6.mem_fixV_zpowers_uc6 d.rep _ w).mpr (h w hw)
  have hbot : W = ⊥ := by
    rw [← inf_eq_right.mpr hfix, a.fixV_dRoot_inf_W_eq_bot hfixb hWU]
  exact hWne hbot

theorem exists_X2_act_ne (a : S23_9_AdjData D Ch c hV d b hb r)
    (hbr : orderOf b = r) (hr3 : r = 3)
    (hfixb : d.fixV (barImage D.M (Subgroup.zpowers b)) = ⊥)
    {W : Submodule (ZMod d.q) (A0V d)} (hWU : W ≤ U a) (hWne : W ≠ ⊥) :
    ∃ g : ↥(X2 a), ∃ w ∈ W, rhoX a g w ≠ w := by
  obtain ⟨w, hw, hne⟩ := a.exists_dRoot_act_ne hfixb hWU hWne
  exact ⟨⟨a.dRoot, a.dRoot_mem_X2 hbr hr3⟩, w, hw, hne⟩

end S23_9_AdjData

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

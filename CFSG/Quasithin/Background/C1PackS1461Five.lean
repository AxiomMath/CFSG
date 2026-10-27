module

public import CFSG.Quasithin.Background.C1PackS1461Two
public import CFSG.Quasithin.EmptyFaithful.S14113Layer
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Hypotheses

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement Pointwise

namespace C1Pack

section Norm

variable {A W : Type*} [Group A] [Finite A] [CommGroup W]

theorem eq_one_of_fixed_of_mem_closure_commutators (ρ : A →* MulAut W) (hodd : Odd (Nat.card A))
    (hW : ∀ w : W, w ^ 2 = 1) {z : W} (hz : ∀ a : A, ρ a z = z)
    (hmem : z ∈ Subgroup.closure {x : W | ∃ (a : A) (v : W), x = ρ a v * v⁻¹}) : z = 1 := by
  classical
  have : Fintype A := Fintype.ofFinite A
  let N : W →* W :=
    { toFun := fun w => ∏ a : A, ρ a w
      map_one' := by simp
      map_mul' := fun x y => by simp [Finset.prod_mul_distrib] }
  have hN1 : ∀ x ∈ Subgroup.closure {x : W | ∃ (a : A) (v : W), x = ρ a v * v⁻¹}, N x = 1 := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨a, v, rfl⟩ := hx
      have h1 : N (ρ a v) = N v := by
        show ∏ b : A, ρ b (ρ a v) = ∏ b : A, ρ b v
        have : ∀ b : A, ρ b (ρ a v) = ρ (b * a) v := fun b => by rw [map_mul]; rfl
        simp_rw [this]
        exact Fintype.prod_equiv (Equiv.mulRight a) _ _ (fun b => rfl)
      rw [map_mul, map_inv, h1, mul_inv_cancel]
    | one => exact map_one N
    | mul x y _ _ hx hy => rw [map_mul, hx, hy, mul_one]
    | inv x _ hx => rw [map_inv, hx, inv_one]
  have hNz : N z = z := by
    show ∏ b : A, ρ b z = z
    simp_rw [hz]
    rw [Finset.prod_const, Finset.card_univ, ← Nat.card_eq_fintype_card]
    obtain ⟨k, hk⟩ := hodd
    rw [hk, pow_succ, pow_mul, hW z, one_pow, one_mul]
  rw [← hNz]
  exact hN1 z hmem

end Norm

section OddPrime

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem oTwoPIn_le_centralizer (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H) {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) :
    oTwoPIn p H ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) := by
  classical
  have hyp := S.hyp
  have hTH : T ≤ H := hH.1.1
  have hHchar : CharTwo H := charTwo_of_inH' hyp.qtke hyp.sylow hH.1
  have hQT : pCoreOf 2 H ≤ T :=
    pCoreOf_two_le_of_isSylowTwoOf (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hTH)
  obtain ⟨hYH, hQY, hHY, hY2⟩ := oTwoPIn_props H hp
  have hQH : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) := le_normalizer_pCoreOf 2 H
  set Q := pCoreOf 2 H with hQ
  set W := omegaOneCenterOf Q with hW
  set Yp := oTwoPIn p H with hYp
  have hmemW : ∀ w, w ∈ W ↔ w ∈ Q ∧ w ∈ Subgroup.centralizer (Q : Set G) ∧ w ^ 2 = 1 :=
    fun w => mem_quasithinOmegaOneCenter_iff
  have hWQ : W ≤ Q := fun w hw => ((hmemW w).mp hw).1
  have hHW : H ≤ Subgroup.normalizer (W : Set G) := by
    intro h hh
    refine A4.mem_normalizer_of_conj_mem fun w hw => ?_
    obtain ⟨hwQ, hwC, hw2⟩ := (hmemW w).mp hw
    refine (hmemW _).mpr ⟨(Subgroup.mem_normalizer_iff.mp (hQH hh) w).mp hwQ, ?_, ?_⟩
    · refine Subgroup.mem_centralizer_iff.mpr fun q hq => ?_
      have h1 := (Subgroup.mem_normalizer_iff''.mp (hQH hh) q).mp hq
      have h2 := Subgroup.mem_centralizer_iff.mp hwC _ h1
      calc q * (h * w * h⁻¹) = h * ((h⁻¹ * q * h) * w) * h⁻¹ := by group
        _ = h * (w * (h⁻¹ * q * h)) * h⁻¹ := by rw [h2]
        _ = h * w * h⁻¹ * q := by group
    · rw [conj_pow, hw2]
      group
  have hWcomm : ∀ a ∈ W, ∀ b ∈ W, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp ((hmemW a).mp ha).2.1 b ((hmemW b).mp hb).1).symm
  have hYW : Yp ≤ Subgroup.normalizer (W : Set G) := hYH.trans hHW
  by_contra hcon
  have hW1ne : ⁅W, Yp⁆ ≠ ⊥ := by
    intro h
    apply hcon
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact h
  have hW1W : ⁅W, Yp⁆ ≤ W := by
    refine Subgroup.commutator_le.mpr fun w hw y hy => ?_
    have h1 := (Subgroup.mem_normalizer_iff.mp (hYW hy) w⁻¹).mp (W.inv_mem hw)
    have e : ⁅w, y⁆ = w * (y * w⁻¹ * y⁻¹) := by simp only [commutatorElement_def]; group
    rw [e]
    exact W.mul_mem hw h1
  have hW1T : ⁅W, Yp⁆ ≤ T := hW1W.trans (hWQ.trans hQT)
  have hTW1 : T ≤ Subgroup.normalizer ((⁅W, Yp⁆ : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_commutator,
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHW (hTH ht)),
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hHY (hTH ht))]
  have hTnil : Group.IsNilpotent ↥T := hyp.sylow.1.isNilpotent
  have hnormT : (⁅W, Yp⁆.subgroupOf T).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hW1T).mpr hTW1
  have hne : ⁅W, Yp⁆.subgroupOf T ≠ ⊥ := by
    intro h
    apply hW1ne
    rw [eq_bot_iff]
    intro x hx
    have hx' : (⟨x, hW1T hx⟩ : ↥T) ∈ ⁅W, Yp⁆.subgroupOf T := hx
    rw [h, Subgroup.mem_bot] at hx'
    have : x = 1 := congrArg Subtype.val hx'
    rw [this]
    exact Subgroup.one_mem _
  have hcen := Group.IsNilpotent.inf_center_ne_bot_of_normal (H := ⁅W, Yp⁆.subgroupOf T) hne
  obtain ⟨⟨z', hz'⟩, hz1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hcen
  have hz'1 : (z' : G) ≠ 1 := fun h => hz1 (Subtype.ext (Subtype.ext h))
  have hzW1 : (z' : G) ∈ ⁅W, Yp⁆ := Subgroup.mem_subgroupOf.mp hz'.1
  have hzW : (z' : G) ∈ W := hW1W hzW1
  have hzcomm : ∀ t ∈ T, t * (z' : G) = (z' : G) * t := fun t ht =>
    congrArg Subtype.val (Subgroup.mem_center_iff.mp hz'.2 ⟨t, ht⟩)
  have hzZ : (z' : G) ∈ quasithinOmegaOneCenter T :=
    mem_quasithinOmegaOneCenter_iff.mpr ⟨z'.2, Subgroup.mem_centralizer_iff.mpr hzcomm,
      ((hmemW _).mp hzW).2.2⟩
  have hYz : ∀ y ∈ Yp, y * (z' : G) = (z' : G) * y := fun y hy =>
    (Subgroup.mem_centralizer_iff.mp (S.le_mcOf hH (hYH hy)) _ hzZ).symm
  let _ : CommGroup ↥W :=
    { (inferInstance : Group ↥W) with mul_comm := fun a b => Subtype.ext (hWcomm a a.2 b b.2) }
  have hW2 : ∀ w : ↥W, w ^ 2 = 1 := fun w =>
    Subtype.ext (((hmemW w).mp w.2).2.2)
  let ρ : ↥Yp →* MulAut ↥W := (conjAct W).comp (Subgroup.inclusion hYW)
  have hρ : ∀ (y : ↥Yp) (w : ↥W), ((ρ y w : ↥W) : G) = (y : G) * w * (y : G)⁻¹ := fun y w =>
    A1b.conjAct_coe W (Subgroup.inclusion hYW y) w
  have hQnorm : (Q.subgroupOf Yp).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hQY).mpr (hYH.trans hQH)
  have hQker : Q.subgroupOf Yp ≤ ρ.ker := by
    intro a ha
    rw [MonoidHom.mem_ker]
    refine A1b.conjAct_eq_one_iff.mpr (Subgroup.mem_centralizer_iff.mpr fun w hw => ?_)
    exact (Subgroup.mem_centralizer_iff.mp ((hmemW w).mp hw).2.1 (a : G)
      (Subgroup.mem_subgroupOf.mp ha)).symm
  let ρ' : (↥Yp ⧸ Q.subgroupOf Yp) →* MulAut ↥W := QuotientGroup.lift (Q.subgroupOf Yp) ρ hQker
  have hρ' : ∀ y : ↥Yp, ρ' (QuotientGroup.mk y) = ρ y := fun y => rfl
  have hRp : IsPGroup p (↥Yp ⧸ Q.subgroupOf Yp) := by
    intro q
    induction q using QuotientGroup.induction_on with
    | H a =>
      obtain ⟨k, hk⟩ := hY2 a a.2
      refine ⟨k, ?_⟩
      rw [← QuotientGroup.mk_pow, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
      exact hk
  have hodd : Odd (Nat.card (↥Yp ⧸ Q.subgroupOf Yp)) := by
    have : Fact p.Prime := ⟨hp⟩
    obtain ⟨n, hn⟩ := hRp.exists_card_eq
    rw [hn]
    exact (hp.odd_of_ne_two hp2).pow
  let zW : ↥W := ⟨(z' : G), hzW⟩
  have hzfix : ∀ a : ↥Yp ⧸ Q.subgroupOf Yp, ρ' a zW = zW := by
    intro a
    induction a using QuotientGroup.induction_on with
    | H y =>
      rw [hρ']
      apply Subtype.ext
      rw [hρ]
      have := hYz y y.2
      show (y : G) * (z' : G) * (y : G)⁻¹ = (z' : G)
      rw [this]
      group
  have hmem : zW ∈ Subgroup.closure
      {x : ↥W | ∃ (a : ↥Yp ⧸ Q.subgroupOf Yp) (v : ↥W), x = ρ' a v * v⁻¹} := by
    have hle : ⁅W, Yp⁆ ≤ (Subgroup.closure
        {x : ↥W | ∃ (a : ↥Yp ⧸ Q.subgroupOf Yp) (v : ↥W), x = ρ' a v * v⁻¹}).map W.subtype := by
      refine Subgroup.commutator_le.mpr fun w hw y hy => ?_
      refine ⟨(ρ' (QuotientGroup.mk ⟨y, hy⟩) ⟨w, hw⟩ * (⟨w, hw⟩ : ↥W)⁻¹)⁻¹,
        Subgroup.inv_mem _ (Subgroup.subset_closure ⟨_, _, rfl⟩), ?_⟩
      rw [hρ']
      simp only [Subgroup.coe_subtype, Subgroup.coe_inv, Subgroup.coe_mul, hρ, commutatorElement_def]
      group
    obtain ⟨d, hd, hdz⟩ := hle hzW1
    have : d = zW := Subtype.ext hdz
    rwa [this] at hd
  have hz1' : zW = 1 :=
    eq_one_of_fixed_of_mem_closure_commutators ρ' hodd hW2 hzfix hmem
  exact hz'1 (congrArg Subtype.val hz1')

end OddPrime

section Components

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

theorem commutator_eq_bot_of_mem_cComp (S : Setting146 G T M) {H : Subgroup G} (hH : IsHTM T M H)
    {K : Subgroup G} (hK : K ∈ cComp H) : ⁅omegaOneCenterOf (pCoreOf 2 H), K⁆ = ⊥ := by
  by_contra hne
  have hyp := S.hyp
  have hHchar : CharTwo H := charTwo_of_inH' hyp.qtke hyp.sylow hH.1
  have hKc : CharTwo K := charTwo_of_isSubnormal_of_charTwo hHchar (subnormal_of_mem_cComp hK)
  have hXc : IsXClass K :=
    ⟨ne_bot_of_mem_cComp hK, eq_oTwoUpper_of_perfect (perfect_of_mem_cComp hK), hKc⟩
  have hVY : VY K ≠ ⊥ := (a4_9 hXc (subnormal_of_mem_cComp hK)).mp hne
  have hloc : quasithinIsLocal T K :=
    isLocal_of_mem_cComp_of_sylow (isSylowTwoOf_of_quasithinIsSylowTwo hyp.sylow hH.1.1) hH.1.2 hK
  exact hyp.faithful_empty K (isFaithfulLocal_iff_isXf.mpr ⟨hloc, hXc, hVY⟩)

theorem layer_le_imageOTwoQuot_of_cComp {H N : Subgroup G} (hK : ∀ K ∈ cComp H, K ≤ N) :
    CFSG.layer (OTwoQuot H) ≤ imageOTwoQuot H N := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsolv : Group.IsSolvable (CFSG.Open.pCore 2 ↥H) := by
    have hp : IsPGroup 2 (CFSG.Open.pCore 2 ↥H) := CFSG.LieType.BorelTits.pCore_isPGroup 2
    have : Group.IsNilpotent (CFSG.Open.pCore 2 ↥H) := hp.isNilpotent
    infer_instance
  simp only [CFSG.layer.eq_sSup]
  refine sSup_le fun K hK' => ?_
  have hKc : K ∈ cComp (⊤ : Subgroup (OTwoQuot H)) := mem_cComp_top_of_isComponent hK'
  obtain ⟨L', hL', hLK⟩ := (cComp_quotient_bijOn (CFSG.Open.pCore 2 ↥H) hsolv).surjOn hKc
  subst hLK
  have hL : L'.map H.subtype ∈ cComp H := map_subtype_mem_cComp hL'
  have hLN : L'.map H.subtype ≤ N := hK _ hL
  have hle : L' ≤ N.subgroupOf H := fun x hx => hLN ⟨x, hx, rfl⟩
  exact Subgroup.map_mono hle

end Components

end C1Pack

open C1Pack in
theorem stage1461Five : Stage1461Five := by
  intro G _ _ T M S H hH
  have hQW : pCoreOf 2 H ≤ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) := by
    intro q hq
    refine Subgroup.mem_centralizer_iff.mpr fun w hw => ?_
    exact (Subgroup.mem_centralizer_iff.mp ((mem_quasithinOmegaOneCenter_iff.mp hw).2.1) q hq).symm
  set N : Subgroup G := H ⊓ Subgroup.centralizer (omegaOneCenterOf (pCoreOf 2 H) : Set G) with hN
  have hQN : pCoreOf 2 H ≤ N := le_inf (pCoreOf_le 2 H) hQW
  have hLayer : CFSG.layer (OTwoQuot H) ≤ imageOTwoQuot H N :=
    layer_le_imageOTwoQuot_of_cComp fun K hK => le_inf (le_of_mem_cComp hK) (by
      rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
      exact commutator_eq_bot_of_mem_cComp S hH hK)
  have hFit : CFSG.fittingSubgroup (OTwoQuot H) ≤ imageOTwoQuot H N := by
    rw [CFSG.fitting_eq_sup_pCore]
    refine iSup_le fun pp => ?_
    by_cases hp2 : pp.1.1 = 2
    · rw [hp2, pCore_two_quot_eq_bot H]
      exact bot_le
    · have hp : pp.1.1.Prime := Nat.prime_of_mem_primeFactors pp.1.2
      intro u hu
      obtain ⟨u, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥H) u
      have hu' : (u : G) ∈ oTwoPIn pp.1.1 H := mem_oTwoPIn_of_mem_pCore u.2 hu
      exact ⟨u, ⟨u.2, oTwoPIn_le_centralizer S hH hp hp2 hu'⟩, rfl⟩
  have hgen : CFSG.generalizedFitting (OTwoQuot H) ≤ imageOTwoQuot H N := sup_le hFit hLayer
  rw [← map_O2Fstar_eq_oTwoFstarIn]
  rintro _ ⟨z, hz, rfl⟩
  exact (mem_of_mk_mem_imageOTwoQuot hQN (hgen hz)).2

end CFSG.Quasithin

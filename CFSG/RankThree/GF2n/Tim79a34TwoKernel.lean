module

public import CFSG.RankThree.GF2n.Tim79a34StrothHyp
public import CFSG.RankThree.GF2n.Tim79a34GammaSteps
public import CFSG.RankThree.GF2n.Tim79a34C8Base

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open
open scoped commutatorElement

section Generic

variable {G : Type} [Group G] [Finite G]

theorem kp_central_of_series {X N : Subgroup G} (hX2 : IsPGroup 2 X) (hNX : N ≤ X)
    (hNn : ∀ x ∈ X, ∀ m ∈ N, x * m * x⁻¹ ∈ N) {k : G}
    (hodd : Odd (Nat.card (Subgroup.zpowers k)))
    (hkX : k ∈ Subgroup.normalizer (X : Set G)) (hkN : k ∈ Subgroup.normalizer (N : Set G))
    (hN : ∀ m ∈ N, k * m = m * k) (hXN : ∀ a ∈ Subgroup.zpowers k, ∀ x ∈ X, ⁅a, x⁆ ∈ N) :
    ∀ x ∈ X, k * x = x * k := by
  haveI hnorm : Subgroup.Normalizes (Subgroup.zpowers k) X :=
    ⟨Subgroup.zpowers_le.mpr hkX⟩
  have hNn' : (N.subgroupOf X).Normal := by
    refine ⟨fun n hn g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using hNn g.1 g.2 n.1 hn
  have hsmul : ∀ (a : ↥(Subgroup.zpowers k)) (x : ↥X),
      ((a • x : ↥X) : G) = (a : G) * (x : G) * (a : G)⁻¹ :=
    fun a x => Subgroup.conjMulDistribMulActionOfLeNormalizer_smul_coe (Subgroup.zpowers k) X a x
  have hWinv : CFSG.IsInvariant ↥(Subgroup.zpowers k) ↥X (⊥ : Subgroup ↥X) := by
    refine ⟨fun a g => ?_⟩
    rw [Subgroup.mem_bot, Subgroup.mem_bot]
    constructor
    · intro h
      rw [h]
      exact MulDistribMulAction.smul_one a
    · intro h
      have h' := congrArg (fun y => a⁻¹ • y) h
      simpa using h'
  have hNinv : CFSG.IsInvariant ↥(Subgroup.zpowers k) ↥X (N.subgroupOf X) := by
    refine ⟨fun a g => ?_⟩
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hsmul]
    exact Subgroup.mem_normalizer_iff.mp (Subgroup.zpowers_le.mpr hkN a.2) (g : G)
  have hWN_triv : ∀ a : ↥(Subgroup.zpowers k), ∀ m : ↥X, m ∈ N.subgroupOf X →
      (a • m) * m⁻¹ ∈ (⊥ : Subgroup ↥X) := by
    intro a m hm
    rw [Subgroup.mem_subgroupOf] at hm
    rw [Subgroup.mem_bot]
    apply Subtype.ext
    rw [Subgroup.coe_mul, Subgroup.coe_inv, hsmul, Subgroup.coe_one]
    have hcm : (a : G) * (m : G) = (m : G) * (a : G) := sh_zpow_comm (hN _ hm) a.2
    rw [hcm]
    group
  have hNQ_triv : ∀ a : ↥(Subgroup.zpowers k), ∀ x : ↥X,
      (a • x) * x⁻¹ ∈ N.subgroupOf X := by
    intro a x
    rw [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv, hsmul,
      ← commutatorElement_def]
    exact hXN (a : G) a.2 _ x.2
  have hres := CFSG.coprime_action_trivial_mod_of_fixed_normal_and_quotient
    (A := ↥(Subgroup.zpowers k)) (G := ↥X) hodd hX2 ⊥ (N.subgroupOf X) bot_le hWinv hNinv
    hWN_triv hNQ_triv
  intro x hx
  have h1 := hres ⟨k, Subgroup.mem_zpowers k⟩ ⟨x, hx⟩
  rw [Subgroup.mem_bot] at h1
  have h3 := congrArg Subtype.val h1
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, hsmul, Subgroup.coe_one] at h3
  have h4 : k * x * k⁻¹ * x⁻¹ = 1 := h3
  have h5 : k * x * k⁻¹ = x := mul_inv_eq_one.mp h4
  calc k * x = k * x * k⁻¹ * k := by group
    _ = x * k := by rw [h5]

@[expose] def kp_K (M V P : Subgroup G) (hMP : M ≤ Subgroup.normalizer (P : Set G))
    (hMV : ∀ g ∈ M, ∀ y ∈ V, g * y * g⁻¹ ∈ V) : Subgroup G where
  carrier := {k | k ∈ M ∧ ∀ x ∈ P, ⁅k, x⁆ ∈ V}
  mul_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨M.mul_mem ha hb, fun x hx => ?_⟩
    rw [commutatorElement_mul_left_eq_conj_mul]
    exact V.mul_mem (hMV a ha _ (hb' x hx)) (ha' x hx)
  one_mem' := by
    refine ⟨M.one_mem, fun x _ => ?_⟩
    rw [commutatorElement_def]
    simp
  inv_mem' := by
    rintro a ⟨ha, ha'⟩
    refine ⟨M.inv_mem ha, fun x hx => ?_⟩
    have e : ⁅a⁻¹, x⁆ = a⁻¹ * (⁅a, x⁆)⁻¹ * a⁻¹⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact hMV a⁻¹ (M.inv_mem ha) _ (V.inv_mem (ha' x hx))

theorem kp_K_conj {M V P : Subgroup G} (hMP : M ≤ Subgroup.normalizer (P : Set G))
    (hMV : ∀ g ∈ M, ∀ y ∈ V, g * y * g⁻¹ ∈ V) {g k : G} (hg : g ∈ M)
    (hk : k ∈ kp_K M V P hMP hMV) : g * k * g⁻¹ ∈ kp_K M V P hMP hMV := by
  obtain ⟨hkM, hkP⟩ := hk
  refine ⟨M.mul_mem (M.mul_mem hg hkM) (M.inv_mem hg), fun x hx => ?_⟩
  have hy : g⁻¹ * x * g ∈ P :=
    (Subgroup.mem_normalizer_iff.mp (hMP hg) (g⁻¹ * x * g)).mpr
      (by rw [show g * (g⁻¹ * x * g) * g⁻¹ = x by group]; exact hx)
  have e : ⁅g * k * g⁻¹, x⁆ = g * ⁅k, g⁻¹ * x * g⁆ * g⁻¹ := by
    simp only [commutatorElement_def]
    group
  rw [e]
  exact hMV g hg _ (hkP _ hy)

theorem kp_kernel_le {M V Q P : Subgroup G} {z v : G}
    (hMQ : Q = inSubgroup (pCore 2) M) (hfit : M ⊓ Subgroup.centralizer (Q : Set G) ≤ Q)
    (hPQ : P ≤ Q) (hVP : V ≤ P) (hMP : M ≤ Subgroup.normalizer (P : Set G))
    (hMV : ∀ g ∈ M, ∀ y ∈ V, g * y * g⁻¹ ∈ V) (hrel : P.relIndex Q ≤ 2)
    (hV4 : ∀ x ∈ V, x = 1 ∨ x = z ∨ x = v ∨ x = v * z) (hzV : z ∈ V) (hvV : v ∈ V)
    (hz1 : z ≠ 1) (hv1 : v ≠ 1) (hvz : v ≠ z) (hz2 : z * z = 1)
    (hMz : ∀ g ∈ M, g * z = z * g) {k : G} (hkM : k ∈ M) (hk : ∀ x ∈ P, ⁅k, x⁆ ∈ V) :
    k ∈ Q := by
  have hMQn : M ≤ Subgroup.normalizer (Q : Set G) := by
    rw [hMQ]
    exact (inSubgroup_pCore_two M).2.2
  have hQM : Q ≤ M := by
    rw [hMQ]
    exact (inSubgroup_pCore_two M).2.1
  have hQ2 : IsPGroup 2 Q := by
    rw [hMQ]
    exact (inSubgroup_pCore_two M).1
  have hP2 : IsPGroup 2 P := hQ2.to_le hPQ
  have hrel_pos : P.relIndex Q ≠ 0 := by
    have h := Subgroup.relIndex_dvd_index_of_le hPQ
    exact fun h0 => Subgroup.index_ne_zero_of_finite (Nat.eq_zero_of_zero_dvd (h0 ▸ h))
  have hidx : ∀ g ∈ M, ∀ x ∈ Q, g * x * g⁻¹ * x⁻¹ ∈ P := by
    intro g hg x hx
    have hgxQ : g * x * g⁻¹ ∈ Q := (Subgroup.mem_normalizer_iff.mp (hMQn hg) x).mp hx
    by_cases hxP : x ∈ P
    · exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp (hMP hg) x).mp hxP) (P.inv_mem hxP)
    · have hgx : g * x * g⁻¹ ∉ P := fun h =>
        hxP ((Subgroup.mem_normalizer_iff.mp (hMP hg) x).mpr h)
      have h2 : P.relIndex Q = 2 := by
        by_contra hne
        have h1 : P.relIndex Q = 1 := by omega
        exact hxP (Subgroup.relIndex_eq_one.mp h1 hx)
      have h : (⟨g * x * g⁻¹, hgxQ⟩ : ↥Q) * (⟨x, hx⟩ : ↥Q)⁻¹ ∈ P.subgroupOf Q :=
        (Subgroup.mul_mem_iff_of_index_two h2).mpr
          (iff_of_false (fun h => hgx (Subgroup.mem_subgroupOf.mp h))
            (fun h => hxP (Subgroup.mem_subgroupOf.mp ((P.subgroupOf Q).inv_mem_iff.mp h))))
      exact Subgroup.mem_subgroupOf.mp h
  have hodd_kill : ∀ k ∈ kp_K M V P hMP hMV, ∀ m : ℕ, Odd m → k ^ m = 1 → k = 1 := by
    intro k hkK m hm hkm
    obtain ⟨hkM, hkP⟩ := hkK
    have hkz : k * z = z * k := hMz k hkM
    have hkvv : k * v = v * k :=
      sh_odd_kill_fix hkM (fun y hy => hMV k hkM y hy) hvV hV4 hkz hz2 hz1 hv1 hvz hm hkm
    have hkV : ∀ y ∈ V, k * y = y * k := by
      intro y hy
      rcases hV4 y hy with rfl | rfl | rfl | rfl
      · simp
      · exact hkz
      · exact hkvv
      · calc k * (v * z) = (k * v) * z := (mul_assoc k v _).symm
          _ = (v * k) * z := by rw [hkvv]
          _ = v * (k * z) := mul_assoc v k _
          _ = v * (z * k) := by rw [hkz]
          _ = v * z * k := (mul_assoc v _ k).symm
    have hodd : Odd (Nat.card (Subgroup.zpowers k)) := by
      rw [Nat.card_zpowers]
      exact Odd.of_dvd_nat hm (orderOf_dvd_of_pow_eq_one hkm)
    have hkK : k ∈ kp_K M V P hMP hMV := ⟨hkM, hkP⟩
    have hkVn : k ∈ Subgroup.normalizer (V : Set G) := by
      rw [Subgroup.mem_normalizer_iff]
      intro y
      refine ⟨fun h => hMV k hkM y h, fun h => ?_⟩
      have h' := hMV k⁻¹ (M.inv_mem hkM) _ h
      rwa [show k⁻¹ * (k * y * k⁻¹) * k⁻¹⁻¹ = y by group] at h'
    have hcP : ∀ x ∈ P, k * x = x * k :=
      kp_central_of_series hP2 hVP (fun x hx m hm => hMV x (hQM (hPQ hx)) m hm) hodd (hMP hkM)
        hkVn hkV (fun a ha x hx => (Subgroup.zpowers_le.mpr hkK ha).2 x hx)
    have hcQ : ∀ x ∈ Q, k * x = x * k :=
      kp_central_of_series hQ2 hPQ
        (fun x hx m hm => (Subgroup.mem_normalizer_iff.mp (hMP (hQM hx)) m).mp hm) hodd
        (hMQn hkM) (hMP hkM) hcP
        (fun a ha x hx => hidx a (Subgroup.zpowers_le.mpr hkK ha).1 x hx)
    have hkC : k ∈ M ⊓ Subgroup.centralizer (Q : Set G) :=
      Subgroup.mem_inf.mpr ⟨hkM, Subgroup.mem_centralizer_iff.mpr (fun q hq => (hcQ q hq).symm)⟩
    have hkQ' : k ∈ Q := hfit hkC
    obtain ⟨j, hj⟩ := hQ2 ⟨k, hkQ'⟩
    have hkj : k ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hcop : Nat.Coprime (2 ^ j) m :=
      Nat.Coprime.pow_left j ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hm.not_two_dvd_nat)
    have h1 : orderOf k ∣ Nat.gcd (2 ^ j) m :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hkj) (orderOf_dvd_of_pow_eq_one hkm)
    have h2 : Nat.gcd (2 ^ j) m = 1 := hcop
    rw [h2] at h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hK2 : IsPGroup 2 (kp_K M V P hMP hMV) := by
    show ∀ g : ↥(kp_K M V P hMP hMV), ∃ n : ℕ, g ^ 2 ^ n = 1
    intro g
    have hgK : (g : G) ∈ kp_K M V P hMP hMV := g.2
    obtain ⟨j, m, hm, hdec⟩ := Nat.exists_eq_two_pow_mul_odd (orderOf_pos (g : G)).ne'
    have hk'K : (g : G) ^ 2 ^ j ∈ kp_K M V P hMP hMV := (kp_K M V P hMP hMV).pow_mem hgK _
    have hk'm : ((g : G) ^ 2 ^ j) ^ m = 1 := by
      rw [← pow_mul, ← hdec, pow_orderOf_eq_one]
    refine ⟨j, Subtype.ext ?_⟩
    have := hodd_kill _ hk'K m hm hk'm
    simpa using this
  have hKM : kp_K M V P hMP hMV ≤ M := fun k hk => hk.1
  have hMK : M ≤ Subgroup.normalizer ((kp_K M V P hMP hMV : Subgroup G) : Set G) := by
    intro g hg
    rw [Subgroup.mem_normalizer_iff]
    intro k
    constructor
    · intro hk
      exact kp_K_conj hMP hMV hg hk
    · intro hk
      have h' := kp_K_conj hMP hMV (M.inv_mem hg) hk
      rwa [show g⁻¹ * (g * k * g⁻¹) * g⁻¹⁻¹ = k by group] at h'
  have hfin := Tim78.le_inSubgroup_pCore hKM hMK hK2
  rw [← hMQ] at hfin
  exact hfin ⟨hkM, hk⟩

end Generic

theorem tim79a34_mem_Q_iff {G : Type} [Group G] [Finite G] {M V Q P H : Subgroup G}
    (hH : TwoEndHyp M V Q P H) (hZ : Subgroup.center (Xbar V H) = ⊥) (k : G) :
    k ∈ Q ↔ k ∈ M ∧ ∀ x ∈ P, ⁅k, x⁆ ∈ V := by
  have hN : NaturalModuleStatement := naturalModule_holds (memberUnique_holds cxw_holds)
  have hIW : Sec34IWStatement :=
    sec34IW_holds hN spRadFactsStatement_holds commPairingStatement_holds
  have h11a : Lemma11aStatement := lemma11a_holds spRadFactsStatement_holds
  have h11b : Lemma11bStatement := lemma11b_holds hN h11a spRadFactsStatement_holds
  have h12 : Lemma12Statement := lemma12Statement_holds
  have hc : MinCex M V Q P H := hH.setup.mc.toMinCex
  have hcP : cPbar V H P ≤ wOf V H := hIW G M V Q P H hH hZ
  obtain ⟨n, Φ, ψ, -, hequiv, ⟨a, T, ha, hT, hTV⟩, hpoint⟩ := hN G M V Q P H hH hZ
  have hNat : NatCfg V H hc.V_le_H Φ ψ := ⟨hequiv, hpoint⟩
  obtain ⟨hAP, -, -⟩ := h11b G M V Q P H hH hZ hcP
  have hcentM : Subgroup.centralizer ({c8W ψ a} : Set G) = M :=
    (h12 G M V Q P H hH hZ Φ ψ hNat a T ha hT hTV).1
  set aG : G := c8W ψ a with haGdef
  have hMQ : Q = inSubgroup (pCore 2) M := hc.hQ
  have hQM : Q ≤ M := by
    rw [hMQ]
    exact (inSubgroup_pCore_two M).2.1
  have haV : aG ∈ V := hpoint a T ha hT hTV
  have haW : aG ∈ wOf V H := c8W_mem ψ a
  have haG1 : aG ≠ 1 := fun h => ha (c8W_inj ψ (h.trans (c8W_zero ψ).symm))
  have hz2 : aG * aG = 1 := by
    rw [← pow_two]
    exact hc.elemAb.2 _ haV
  have hA2 : Nat.card ↥(V ⊓ wOf V H) = 2 := hH.module.trans hH.q_two
  have hAmem : aG ∈ V ⊓ wOf V H := Subgroup.mem_inf.mpr ⟨haV, haW⟩
  have hAc : ∀ m ∈ M, ∀ x ∈ V ⊓ wOf V H, m * x * m⁻¹ = x := by
    intro m hm x hx
    rcases l12_two_elt hA2 hAmem haG1 x hx with rfl | rfl
    · group
    · have hmc : m ∈ Subgroup.centralizer ({aG} : Set G) := by
        rw [hcentM]
        exact hm
      have := Subgroup.mem_centralizer_iff.mp hmc aG (Set.mem_singleton _)
      rw [← this]
      group
  have hV4 : Nat.card ↥V = 4 := by
    have h := twb_card_barOf_mul (V := V) (H := H) (K := V) hc.V_le_H
    have e1 : Nat.card ↥(barOf V H V) = 2 := hH.q_two
    have e2 : Nat.card ↥(V ⊓ wOf V H) = 2 := by rw [hH.module]; exact hH.q_two
    rw [e1, e2] at h
    omega
  have hPQ : P ≤ Q := hc.P_le_Q
  have hVn : ∀ q ∈ M, ∀ v ∈ V, q * v * q⁻¹ ∈ V := by
    intro q hq v hv
    have hgN : q ∈ Subgroup.normalizer (V : Set G) := by
      rw [hc.normalizer_eq]
      exact hq
    exact (Subgroup.mem_normalizer_iff.mp hgN v).mp hv
  constructor
  · intro hk
    refine ⟨hQM hk, fun x hx => ?_⟩
    obtain ⟨C, hCQ, hPCQ, hPC, -, -, -⟩ := Gamma.sec34GammaStatement_holds G M V Q P H hH hZ
    have hPA : P ≤ Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) :=
      l12_le_normalizer (fun k hk v hv => hAc k (hQM (hPQ hk)) v hv)
    have hCA : C ≤ Subgroup.normalizer ((V ⊓ wOf V H : Subgroup G) : Set G) :=
      l12_le_normalizer (fun k hk v hv => hAc k (hQM (hCQ hk)) v hv)
    have hPP : ∀ p ∈ P, ∀ x ∈ P, ⁅p, x⁆ ∈ V ⊓ wOf V H := fun p hp x hx => by
      rw [← hAP]
      exact Subgroup.commutator_mem_commutator hp hx
    have hPQA : ∀ x ∈ Q, ∀ p ∈ P, ⁅p, x⁆ ∈ V ⊓ wOf V H := by
      rw [← hPCQ]
      exact l12_sup_normalizes hPA hCA hPP hPC
    have h1 := (Subgroup.mem_inf.mp (hPQA k hk x hx)).1
    rw [← commutatorElement_inv]
    exact V.inv_mem h1
  · rintro ⟨hkM, hk⟩
    obtain ⟨v, hvV, hvW⟩ : ∃ v ∈ V, v ∉ wOf V H := by
      by_contra hcon
      push Not at hcon
      exact hc.not_V_le_wOf (fun v hv => hcon v hv)
    have hv1 : v ≠ 1 := fun h => hvW (by rw [h]; exact (wOf V H).one_mem)
    have hvz : v ≠ aG := fun h => hvW (by rw [h]; exact haW)
    have hvz1 : v * aG ≠ 1 := by
      intro h
      apply hvz
      calc v = v * (aG * aG) := by rw [hz2, mul_one]
        _ = (v * aG) * aG := by rw [mul_assoc]
        _ = aG := by rw [h, one_mul]
    have hV4' := sh_V_four hV4 haV hvV haG1 hv1 (Ne.symm hvz) hvz1
    have hrel : P.relIndex Q ≤ 2 := sec34QIndexStatement_holds G M V Q P H hH hZ
    have hfit := Tim78.inf_centralizer_le_of_generalizedFitting_eq hc.fitting
    rw [← hMQ] at hfit
    exact kp_kernel_le hMQ hfit hPQ hc.V_le_P hc.M_le_normalizer_P hVn hrel hV4' haV hvV
      haG1 hv1 hvz hz2 (fun g hg => by
        have hgc : g ∈ Subgroup.centralizer ({aG} : Set G) := by
          rw [hcentM]
          exact hg
        exact (Subgroup.mem_centralizer_iff.mp hgc aG (Set.mem_singleton _)).symm) hkM hk

end CFSG.RankThree.GF2n.Tim79a

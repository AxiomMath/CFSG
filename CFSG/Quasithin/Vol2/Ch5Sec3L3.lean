module

public import CFSG.Quasithin.Vol2.Ch5Sec3Lemmas
import CFSG.Quasithin.Vol2.Ch3Sec1Thm311
import CFSG.LocalAnalysis.QuasithinUnique.GammaFamiliesBasic
import CFSG.Goldschmidt.Steps.Sec87d
public import CFSG.Quasithin.Background.A4Reduced

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem normal_of_charTwo_sylow_commutator_le [Finite G] {H J X : Subgroup G} (hCT : CharTwo H)
    (hJH : IsSylowTwoOf J H) (hXH : X ≤ H ⊓ Subgroup.centralizer (H : Set G)) (hXJ : X ≤ J)
    (hab : ⁅J, J⁆ ≤ X) : H ≤ Subgroup.normalizer (J : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hXn : (X.subgroupOf H).Normal := by
    refine ⟨fun x hx h => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hx ⊢
    have hxc : (x : G) ∈ Subgroup.centralizer (H : Set G) := (hXH hx).2
    have : (h : G) * x = x * h := Subgroup.mem_centralizer_iff.mp hxc h h.2
    have e : (h : G) * x * (h : G)⁻¹ = x := by rw [this]; group
    show (h : G) * x * (h : G)⁻¹ ∈ X
    rw [e]
    exact hx
  have hA18 := centralizer_pCore_quotient_subgroupOf_le (p := 2) hXH hCT
  set Q := H ⧸ X.subgroupOf H with hQ
  set π : H →* Q := QuotientGroup.mk' (X.subgroupOf H) with hπ
  have hker : π.ker = X.subgroupOf H := QuotientGroup.ker_mk' _
  have hJ' : J.subgroupOf H ≥ π.ker := by
    rw [hker]
    exact fun x hx => Subgroup.mem_subgroupOf.2 (hXJ (Subgroup.mem_subgroupOf.1 hx))
  set J' : Subgroup Q := (J.subgroupOf H).map π with hJ'def
  have hJp : IsPGroup 2 (J.subgroupOf H) :=
    hJH.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hJH.1).symm
  have hJ'p : IsPGroup 2 J' := hJp.map π
  have hJ'idx : ¬ 2 ∣ J'.index := by
    rw [hJ'def, Subgroup.index_map_eq (J.subgroupOf H) (QuotientGroup.mk'_surjective _) hJ']
    exact hJH.2.2
  let S : Sylow 2 Q := hJ'p.toSylow hJ'idx
  have hcomm : ∀ x ∈ J', ∀ y ∈ J', x * y = y * x := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, hπ, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have ha' : (a : G) ∈ J := Subgroup.mem_subgroupOf.1 ha
    have hb' : (b : G) ∈ J := Subgroup.mem_subgroupOf.1 hb
    have := Subgroup.commutator_mem_commutator (J.inv_mem hb') (J.inv_mem ha')
    have h2 := hab this
    simpa [commutatorElement_def, mul_assoc] using h2
  have hpC : IsPGroup 2 (CFSG.Open.pCore 2 Q) := CFSG.LieType.BorelTits.pCore_isPGroup 2
  have hNc : (CFSG.Open.pCore 2 Q).Normal := CFSG.LieType.BorelTits.pCore_normal 2
  have hcore : CFSG.Open.pCore 2 Q ≤ J' := hpC.le_sylow_of_normal S
  have hJ'le : J' ≤ CFSG.Open.pCore 2 Q := by
    intro x hx
    apply hA18
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hcomm x hx y (hcore hy)).symm
  have hJeq : J' = CFSG.Open.pCore 2 Q := le_antisymm hJ'le hcore
  have hJnormal : J'.Normal := hJeq ▸ hNc
  have hcomap : J'.comap π = J.subgroupOf H := Subgroup.comap_map_eq_self hJ'
  have : (J.subgroupOf H).Normal := hcomap ▸ hJnormal.comap π
  exact (Subgroup.normal_subgroupOf_iff_le_normalizer hJH.1).1 this

@[expose] def Stmt5_3_L3_facts : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n f : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfLieType52 M L H B D T .PSL 3 f → 2 ≤ f →
      T ⊓ Subgroup.centralizer (sec53ZS T L : Set G) = sec53S T L ∧
      (IsElemAbelian 2 (pCoreOf 2 L) ∧ IsElemAbelian 2 (pCoreOf 2 (oTwoUpper H)) ∧
        pCoreOf 2 L ⊔ pCoreOf 2 (oTwoUpper H) = sec53S T L ∧
        pCoreOf 2 L ⊓ pCoreOf 2 (oTwoUpper H) = sec53ZS T L ∧
        ⁅sec53S T L, sec53S T L⁆ ≤ sec53ZS T L) ∧
      ((∀ A : Subgroup G, A ≤ sec53S T L → IsElemAbelian 2 A →
          A ≤ pCoreOf 2 L ∨ A ≤ pCoreOf 2 (oTwoUpper H)) ∧
        (∀ A : Subgroup G, sec53ZS T L < A → A ≤ pCoreOf 2 L →
          sec53S T L ⊓ Subgroup.centralizer (A : Set G) = pCoreOf 2 L) ∧
        ∀ A : Subgroup G, sec53ZS T L < A → A ≤ pCoreOf 2 (oTwoUpper H) →
          sec53S T L ⊓ Subgroup.centralizer (A : Set G) = pCoreOf 2 (oTwoUpper H)) ∧
      (∀ z ∈ sec53ZS T L, z ≠ 1 → ∀ z' ∈ sec53ZS T L, z' ≠ 1 →
        ∃ g ∈ sec53M12 L H, g * z * g⁻¹ = z') ∧
      (∀ z ∈ sec53ZS T L, z ≠ 1 →
        sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H ∧
          sec53M2 H ⊓ Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H) ∧
      (3 ≤ f → ∀ z ∈ sec53ZS T L, z ∈ centerOf T → z ≠ 1 →
          pCoreOf 2 (sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G)) = sec53S T L ∧
            pCoreOf 2 (sec53M2 H ⊓ Subgroup.centralizer ({z} : Set G)) = sec53S T L)

@[expose] def Stmt5_3_7_exc : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n f : ℕ),
    Hyp5_2_4 G T M L V H B D L₂ n → IsOfLieType52 M L H B D T .PSL 3 f → 2 ≤ f →
    (∀ z ∈ sec53ZS T L, orderOf z = 2 →
      ¬ Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H) →
    f = 2 →
    ∀ z ∈ sec53ZS T L, z ∈ centerOf T → orderOf z = 2 →
      pCoreOf 2 (sec53M1 L ⊓ Subgroup.centralizer ({z} : Set G)) ≠ sec53S T L →
      Subgroup.centralizer ({z} : Set G) ≤ sec53M12 L H

section Proofs

theorem le_normalizer_inf_of_normalizes {X A B : Subgroup G}
    (hA : X ≤ Subgroup.normalizer (A : Set G)) (hB : X ≤ Subgroup.normalizer (B : Set G)) :
    X ≤ Subgroup.normalizer ((A ⊓ B : Subgroup G) : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro y
  rw [Subgroup.mem_inf, Subgroup.mem_inf, Subgroup.mem_normalizer_iff.mp (hA hx) y,
    Subgroup.mem_normalizer_iff.mp (hB hx) y]

theorem normalizer_le_normalizer_centralizer (P : Subgroup G) :
    Subgroup.normalizer (P : Set G) ≤
      Subgroup.normalizer ((Subgroup.centralizer (P : Set G) : Subgroup G) : Set G) := by
  refine Subgroup.le_set_normalizer_iff.mpr fun g hg c hc => ?_
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hc ⊢
  intro p hp
  have hp' : g⁻¹ * p * g ∈ P := by
    have := (Subgroup.mem_normalizer_iff.mp hg (g⁻¹ * p * g)).mpr (by simpa [mul_assoc] using hp)
    exact this
  have := hc _ hp'
  calc p * (g * c * g⁻¹) = g * ((g⁻¹ * p * g) * c) * g⁻¹ := by group
    _ = g * (c * (g⁻¹ * p * g)) * g⁻¹ := by rw [this]
    _ = g * c * g⁻¹ * p := by group

theorem pCoreOf_le_pCoreOf_of_sylow [Finite G] {T H X : Subgroup G} (hT : IsSylowTwoOf T X)
    (hTH : T ≤ H) (hHX : H ≤ X) : pCoreOf 2 X ≤ pCoreOf 2 H := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOT : pCoreOf 2 X ≤ T := hT.le_of_normalizes (CFSG.LieType.BorelTits.pCoreOf_le 2 X)
    (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X) (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hOT.trans hTH)
    (hHX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 X))
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)

theorem stmt5_3_5_of (h531 : Stmt5_3_1) (hfacts : Stmt5_3_L3_facts) :
    ∀ (G : Type) [Group G] [Finite G] (T M L V H B D L₂ : Subgroup G) (n f : ℕ),
      Hyp5_2_4 G T M L V H B D L₂ n → IsOfLieType52 M L H B D T .PSL 3 f → 2 ≤ f →
        Subgroup.normalizer (sec53ZS T L : Set G) = sec53M12 L H := by
  intro G _ _ T M L V H B D L₂ n f hyp hty hf
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  obtain ⟨-, -, ⟨hNS, -, -⟩, -⟩ := h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  obtain ⟨hCT, ⟨-, -, -, -, hSS⟩, -⟩ := hfacts G T M L V H B D L₂ n f hyp hty hf
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hyp.T_le.trans hyp.normal
  have hTS : T ≤ Subgroup.normalizer (sec53S T L : Set G) :=
    le_normalizer_inf_of_normalizes Subgroup.le_normalizer hTL
  have hTZ : T ≤ Subgroup.normalizer (sec53ZS T L : Set G) :=
    hTS.trans (normalizer_le_normalizer_centerOf _)
  have hZS : sec53ZS T L ≤ sec53S T L := inf_le_left
  have hZ2 : IsPGroup 2 (sec53ZS T L) := hyp.sylow.1.to_le (hZS.trans inf_le_left)
  obtain ⟨z, hz, hz2⟩ := exists_involution_sec53ZS hyp.toHyp5_0_1
  have hZne : sec53ZS T L ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.mem_bot] at hz
    rw [hz, orderOf_one] at hz2
    exact absurd hz2 (by norm_num)
  have hZN : sec53ZS T L ≤ pCoreOf 2 (Subgroup.normalizer (sec53ZS T L : Set G)) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 Subgroup.le_normalizer le_rfl hZ2
  have hCN2 : CharTwo (Subgroup.normalizer (sec53ZS T L : Set G)) :=
    charTwo_of_inH' hyp.qtke hyp.sylow ⟨hTZ, fun h0 => hZne (le_bot_iff.mp (h0 ▸ hZN))⟩
  have hCleN : Subgroup.centralizer (sec53ZS T L : Set G) ≤
      Subgroup.normalizer (sec53ZS T L : Set G) := Subgroup.centralizer_le_normalizer _
  have hNC := normalizer_le_normalizer_centralizer (sec53ZS T L)
  have hCchar : CharTwo (Subgroup.centralizer (sec53ZS T L : Set G)) :=
    A4.charTwo_of_subnormal (A3.subnormal_of_normal hCleN
      ((Subgroup.normal_subgroupOf_iff_le_normalizer hCleN).mpr hNC)) hCN2
  have hTN : IsSylowTwoOf T (Subgroup.normalizer (sec53ZS T L : Set G)) :=
    isSylowTwoOf_of_isSylowTwo hyp.sylow hTZ
  have hSC : IsSylowTwoOf (sec53S T L) (Subgroup.centralizer (sec53ZS T L : Set G)) := by
    have := A4.isSylowTwoOf_inf_normal hTN hCleN hNC
    rwa [hCT] at this
  have hZC : sec53ZS T L ≤ Subgroup.centralizer (sec53ZS T L : Set G) ⊓
      Subgroup.centralizer ((Subgroup.centralizer (sec53ZS T L : Set G) : Subgroup G) : Set G) := by
    refine le_inf ?_ (Subgroup.le_centralizer_iff.mpr le_rfl)
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y (Subgroup.mem_inf.mp hy).1
  have hCS := normal_of_charTwo_sylow_commutator_le hCchar hSC hZC hZS hSS
  have hSO : pCoreOf 2 (Subgroup.centralizer (sec53ZS T L : Set G)) = sec53S T L :=
    le_antisymm (hSC.le_of_normalizes (CFSG.LieType.BorelTits.pCoreOf_le 2 _)
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _))
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hSC.1 hCS hSC.2.1)
  have hNS' : Subgroup.normalizer (sec53ZS T L : Set G) ≤
      Subgroup.normalizer (sec53S T L : Set G) := by
    rw [← hSO]
    exact hNC.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  refine le_antisymm (hNS ▸ hNS') ?_
  rw [← hNS]
  exact normalizer_le_normalizer_centerOf _

@[expose] def omegaOneCenterOf (R : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ centerOf R ∧ x ^ 2 = 1}

theorem omegaOneCenterOf_le (R : Subgroup G) : omegaOneCenterOf R ≤ centerOf R :=
  (Subgroup.closure_le _).mpr fun _ hx => hx.1

theorem centerOf_comm {R : Subgroup G} {x y : G} (hx : x ∈ centerOf R) (hy : y ∈ centerOf R) :
    x * y = y * x :=
  (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y (Subgroup.mem_inf.mp hy).1).symm

theorem isElemAbelian_omegaOneCenterOf (R : Subgroup G) : IsElemAbelian 2 (omegaOneCenterOf R) := by
  refine ⟨⟨⟨fun a b => Subtype.ext (centerOf_comm (omegaOneCenterOf_le R a.2)
    (omegaOneCenterOf_le R b.2))⟩⟩, fun x hx => ?_⟩
  induction hx using Subgroup.closure_induction with
  | mem x hx => exact hx.2
  | one => exact one_pow 2
  | mul x y hx hy ihx ihy =>
    rw [(Commute.mul_pow (centerOf_comm (omegaOneCenterOf_le R hx)
      (omegaOneCenterOf_le R hy)) 2), ihx, ihy, one_mul]
  | inv x hx ih => rw [inv_pow, ih, inv_one]

private theorem normalizer_le_normalizer_omegaOneCenterOf (R : Subgroup G) :
    Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (omegaOneCenterOf R : Set G) := by
  rw [omegaOneCenterOf, Subgroup.le_normalizer_closure_iff]
  rintro h hh g ⟨hg, hg2⟩
  refine Subgroup.subset_closure ⟨conj_mem_centerOf hh hg, ?_⟩
  rw [conj_pow, hg2, mul_one, mul_inv_cancel]

theorem normalizer_pCoreOf_le_of_isUniqueM [Finite G] {X M V : Subgroup G} (hU : IsUniqueM X M)
    (hV : pCoreOf 2 M = V) (hV1 : V ≠ ⊥) : Subgroup.normalizer (V : Set G) ≤ M := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  refine le_of_isUniqueM_of_isTwoLocal hU ⟨V, hV1, hV ▸ CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 M,
    rfl⟩ (hU.1.2.trans ?_)
  rw [← hV]
  exact CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M

theorem stmt5_3_7_of (h531 : Stmt5_3_1) (hfacts : Stmt5_3_L3_facts) (hexc : Stmt5_3_7_exc) :
    Stmt5_3_7 := by
  intro G _ _ T M L V H B D L₂ n f hyp hty hf h2 z hz hz2
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hpar : IsSec53Param .PSL 3 f := ⟨hf, Or.inl ⟨rfl, rfl⟩⟩
  have h535 := stmt5_3_5_of h531 hfacts G T M L V H B D L₂ n f hyp hty hf
  obtain ⟨⟨-, -, hU1, hU2, -⟩, ⟨-, hO1, -, hO2⟩, -, -⟩ :=
    h531 G T M L V H B D L₂ n .PSL 3 f hyp hty hpar
  obtain ⟨-, ⟨hV1e, hV2e, -, hZ12, -⟩, ⟨hA, hC1, hC2⟩, htr, hCM, hO⟩ :=
    hfacts G T M L V H B D L₂ n f hyp hty hf
  have hT1 : T ≤ sec53M1 L := hyp.T_le.trans hyp.normal
  have hZV1 : sec53ZS T L ≤ pCoreOf 2 L := hZ12 ▸ inf_le_left
  have hZV2 : sec53ZS T L ≤ pCoreOf 2 (oTwoUpper H) := hZ12 ▸ inf_le_right
  have hzne : z ≠ 1 := fun h => by rw [h, orderOf_one] at hz2; exact absurd hz2 (by norm_num)
  have hZne : sec53ZS T L ≠ ⊥ := fun h0 => by
    have := hz
    rw [h0, Subgroup.mem_bot] at this
    exact hzne this
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := hT1
  have hTZ : T ≤ Subgroup.normalizer (sec53ZS T L : Set G) :=
    (le_normalizer_inf_of_normalizes Subgroup.le_normalizer hTL).trans
      (normalizer_le_normalizer_centerOf _)
  have hZT : sec53ZS T L ≤ T := inf_le_left.trans inf_le_left
  obtain ⟨w', hw'1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp
    (CFSG.Goldschmidt.Sec8.inf_center_ne_bot' hyp.sylow.1 hZT hTZ hZne)
  obtain ⟨hwZ, hwT⟩ := Subgroup.mem_inf.mp w'.2
  set w : G := (w' : G) with hwdef
  have hw1 : w ≠ 1 := fun h => hw'1 (Subtype.ext h)
  have hw2 : orderOf w = 2 := by
    have hsq : w ^ 2 = 1 := hV1e.2 w (hZV1 hwZ)
    exact orderOf_eq_prime hsq hw1
  suffices hsuff : Subgroup.centralizer ({w} : Set G) ≤ sec53M12 L H by
    obtain ⟨g, hg, hgw⟩ := htr w hwZ hw1 z hz hzne
    intro c hc
    rw [Subgroup.mem_centralizer_singleton_iff] at hc
    have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer ({w} : Set G) := by
      rw [Subgroup.mem_centralizer_singleton_iff]
      have h0 : w = g⁻¹ * z * g := by rw [← hgw]; group
      rw [h0]
      calc g⁻¹ * c * g * (g⁻¹ * z * g) = g⁻¹ * (c * z) * g := by group
        _ = g⁻¹ * (z * c) * g := by rw [hc]
        _ = g⁻¹ * z * g * (g⁻¹ * c * g) := by group
    have hcM := hsuff hc'
    have : c = g * (g⁻¹ * c * g) * g⁻¹ := by group
    rw [this]
    exact (sec53M12 L H).mul_mem ((sec53M12 L H).mul_mem hg hcM) ((sec53M12 L H).inv_mem hg)
  by_cases hO1w : pCoreOf 2 (sec53M1 L ⊓ Subgroup.centralizer ({w} : Set G)) = sec53S T L
  swap
  · have hf2 : f = 2 := by
      by_contra hne
      exact hO1w (hO (by omega) w hwZ hwT hw1).1
    exact hexc G T M L V H B D L₂ n f hyp hty hf h2 hf2 w hwZ hwT hw2 hO1w
  have hwc : w ∈ Subgroup.centralizer (T : Set G) := (Subgroup.mem_inf.mp hwT).2
  have hTGw : T ≤ Subgroup.centralizer ({w} : Set G) := by
    intro t ht
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact Subgroup.mem_centralizer_iff.mp hwc t ht
  have hwR : w ∈ pCoreOf 2 (Subgroup.centralizer ({w} : Set G)) := by
    have hzp : IsPGroup 2 (Subgroup.zpowers w) := by
      refine IsPGroup.of_card (n := 1) ?_
      rw [Nat.card_zpowers, hw2, pow_one]
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((Subgroup.zpowers_le).mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) ?_ hzp
      (Subgroup.mem_zpowers w)
    intro c hc
    have hwc' : Commute w c := (Subgroup.mem_centralizer_singleton_iff.mp hc).symm
    have hc' : c ∈ Subgroup.centralizer ((Subgroup.zpowers w : Subgroup G) : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro x hx
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact (Commute.zpow_left hwc' k).eq
    exact Subgroup.centralizer_le_normalizer _ hc'
  have hRne : pCoreOf 2 (Subgroup.centralizer ({w} : Set G)) ≠ ⊥ := fun h0 => by
    rw [h0, Subgroup.mem_bot] at hwR
    exact hw1 hwR
  have hGch : CharTwo (Subgroup.centralizer ({w} : Set G)) :=
    charTwo_of_inH' hyp.qtke hyp.sylow ⟨hTGw, hRne⟩
  set R := pCoreOf 2 (Subgroup.centralizer ({w} : Set G)) with hRdef
  have hRS : R ≤ sec53S T L := by
    have := pCoreOf_le_pCoreOf_of_sylow (isSylowTwoOf_of_isSylowTwo hyp.sylow hTGw)
      (le_inf hT1 hTGw) inf_le_right
    rwa [hO1w] at this
  have hZG : sec53ZS T L ≤ Subgroup.centralizer ({w} : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact centerOf_comm hx hwZ
  have hZcR : sec53ZS T L ≤ Subgroup.centralizer (R : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hx).2 y (hRS hy)
  have hZR : sec53ZS T L ≤ R := fun x hx => hGch (Subgroup.mem_inf.mpr ⟨hZG hx, hZcR hx⟩)
  have hZZR : sec53ZS T L ≤ omegaOneCenterOf R := fun x hx =>
    Subgroup.subset_closure ⟨⟨hZR hx, hZcR hx⟩, hV1e.2 x (hZV1 hx)⟩
  have hGR : Subgroup.centralizer ({w} : Set G) ≤ Subgroup.normalizer (R : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _
  have hGZR := hGR.trans (normalizer_le_normalizer_omegaOneCenterOf R)
  rcases eq_or_lt_of_le hZZR with heq | hlt
  ·
    rw [← heq] at hGZR
    rw [← h535]
    exact hGZR
  ·
    have hRc : R ≤ Subgroup.centralizer (omegaOneCenterOf R : Set G) := by
      intro r hr
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.mem_inf.mp (omegaOneCenterOf_le R hy)).2 r hr).symm
    have hZRS : omegaOneCenterOf R ≤ sec53S T L :=
      ((omegaOneCenterOf_le R).trans inf_le_left).trans hRS
    rcases hA _ hZRS (isElemAbelian_omegaOneCenterOf R) with h1 | h1
    · have hRV : R ≤ pCoreOf 2 L := by
        rw [← hC1 _ hlt h1]
        exact le_inf hRS hRc
      have hVR : pCoreOf 2 L ≤ R := by
        intro v hv
        refine hGch (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val
            (isMulCommutative_iff.mp hV1e.1 (⟨v, hv⟩ : ↥(pCoreOf 2 L)) ⟨w, hZV1 hwZ⟩)
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact congrArg Subtype.val
            (isMulCommutative_iff.mp hV1e.1 (⟨y, hRV hy⟩ : ↥(pCoreOf 2 L)) ⟨v, hv⟩)
      have hGM : Subgroup.centralizer ({w} : Set G) ≤ sec53M1 L := by
        refine hGR.trans ?_
        rw [le_antisymm hRV hVR]
        exact normalizer_pCoreOf_le_of_isUniqueM hU1 hO1
          (fun h0 => hZne (le_bot_iff.mp (h0 ▸ hZV1)))
      exact (le_inf hGM le_rfl).trans (hCM w hwZ hw1).1
    · have hRV : R ≤ pCoreOf 2 (oTwoUpper H) := by
        rw [← hC2 _ hlt h1]
        exact le_inf hRS hRc
      have hVR : pCoreOf 2 (oTwoUpper H) ≤ R := by
        intro v hv
        refine hGch (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact congrArg Subtype.val (isMulCommutative_iff.mp hV2e.1
            (⟨v, hv⟩ : ↥(pCoreOf 2 (oTwoUpper H))) ⟨w, hZV2 hwZ⟩)
        · rw [Subgroup.mem_centralizer_iff]
          intro y hy
          exact congrArg Subtype.val (isMulCommutative_iff.mp hV2e.1
            (⟨y, hRV hy⟩ : ↥(pCoreOf 2 (oTwoUpper H))) ⟨v, hv⟩)
      have hGM : Subgroup.centralizer ({w} : Set G) ≤ sec53M2 H := by
        refine hGR.trans ?_
        rw [le_antisymm hRV hVR]
        exact normalizer_pCoreOf_le_of_isUniqueM hU2 hO2
          (fun h0 => hZne (le_bot_iff.mp (h0 ▸ hZV2)))
      exact (le_inf hGM le_rfl).trans (hCM w hwZ hw1).2

end Proofs

end CFSG.Quasithin.H13

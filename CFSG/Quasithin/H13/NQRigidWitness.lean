module

public import CFSG.Quasithin.H13.NQRigidConjugate
public import CFSG.Quasithin.H13.NQBlockOddResidual
public import CFSG.Quasithin.H13.NQSetupPlaneAction

public section

namespace CFSG.Quasithin.H13.NQRigid

open Subgroup CFSG.Open
open CFSG.Quasithin.SteinbergCC (normalizerFrattiniConj)
open CFSG.QuasithinUnique.Setup.Campbell (NoPQuotient)

variable {G : Type} [Group G] [Finite G]

theorem isStronglyQuasithin_of_le {L M : Subgroup G} (hLM : L ≤ M)
    (hM : CFSG.IsStronglyQuasithin M) : CFSG.IsStronglyQuasithin L := by
  intro r hr hr2
  rw [CFSG.SectionRank.pRank_eq_open_pRank_top]
  refine (CFSG.SectionRank.pRank_top_le_of_injective hr.one_lt (inclusion hLM)
    (inclusion_injective hLM)).trans ?_
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top]
  exact hM r hr hr2

theorem pCore_map_ne_bot_of_qtnq {T L M : Subgroup G} (h : QTNQ T L M) :
    (CFSG.pCore 2 M).map M.subtype ≠ ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨-, -, -, -, ⟨hU1, hUM, hUn, hUel⟩, -⟩ :=
    NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hU2 : IsPGroup 2 (qtnqU L M) := CFSG.IsElementaryAbelian.isPGroup 2 _
  have hle : (qtnqU L M).subgroupOf M ≤ CFSG.pCore 2 M :=
    SteinbergCC.le_pCore_of_normal_of_isPGroup hUn hU2.comap_subtype
  intro hbot
  apply hU1
  rw [eq_bot_iff]
  intro u hu
  have h1 : (⟨u, hUM hu⟩ : M) ∈ CFSG.pCore 2 M := hle hu
  have h2 : u ∈ (CFSG.pCore 2 M).map M.subtype := ⟨⟨u, hUM hu⟩, h1, rfl⟩
  rw [hbot] at h2
  exact h2

theorem isStronglyQuasithin_of_qtnq {T L M : Subgroup G} (h : QTNQ T L M) :
    CFSG.IsStronglyQuasithin M :=
  QuasithinUnique.isStronglyQuasithin_of_pCoreOf_ne_bot_of_evenRank h.qtke.2.2
    (by unfold pCoreOf; exact pCore_map_ne_bot_of_qtnq h)

omit [Finite G] in
theorem le_pCore_map_of_pCore_eq_bot {X M : Subgroup G} (hXM : X ≤ M)
    (hMX : M ≤ normalizer (X : Set G)) (hX : CFSG.pCore 2 X = ⊥)
    (hM : CFSG.IsCharacteristicP 2 M) : X ≤ (CFSG.pCore 2 M).map M.subtype := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Q : Subgroup G := (CFSG.pCore 2 M).map M.subtype with hQ
  have hMQ : M ≤ normalizer (Q : Set G) :=
    le_normalizer.trans (normalizer_le_normalizer_map_pCore 2 M)
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup.map _
  have hXQ : X ⊓ Q = ⊥ := by
    have hle : Q.subgroupOf X ≤ CFSG.pCore 2 X := by
      refine SteinbergCC.le_pCore_of_normal_of_isPGroup ?_ hQ2.comap_subtype
      refine ⟨fun a ha b => ?_⟩
      simp only [mem_subgroupOf, coe_mul, coe_inv] at ha ⊢
      exact (mem_normalizer_iff.mp (hMQ (hXM b.2)) _).mp ha
    rw [hX] at hle
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxX, hxQ⟩ := mem_inf.mp hx
    have h1 : (⟨x, hxX⟩ : X) ∈ Q.subgroupOf X := hxQ
    have h2 := hle h1
    rw [mem_bot] at h2 ⊢
    exact congrArg Subtype.val h2
  intro x hx
  have hxM : x ∈ M := hXM hx
  have hcent : (⟨x, hxM⟩ : M) ∈ centralizer (CFSG.pCore 2 M : Set M) := by
    rw [mem_centralizer_iff]
    intro q hq
    have hqQ : (q : G) ∈ Q := ⟨q, hq, rfl⟩
    have hc : x * q * x⁻¹ * (q : G)⁻¹ ∈ X ⊓ Q := by
      refine mem_inf.mpr ⟨?_, ?_⟩
      · have h1 : (q : G) * x⁻¹ * (q : G)⁻¹ ∈ X :=
          (mem_normalizer_iff.mp (hMX q.2) x⁻¹).mp (X.inv_mem hx)
        rw [show x * q * x⁻¹ * (q : G)⁻¹ = x * ((q : G) * x⁻¹ * (q : G)⁻¹) by group]
        exact X.mul_mem hx h1
      · have h1 : x * q * x⁻¹ ∈ Q := (mem_normalizer_iff.mp (hMQ hxM) q).mp hqQ
        exact Q.mul_mem h1 (Q.inv_mem hqQ)
    rw [hXQ, mem_bot] at hc
    have hc' : x * q = q * x := by
      have := congrArg (· * ((q : G) * x)) hc
      simp only [one_mul] at this
      rw [← this]
      group
    exact Subtype.ext hc'.symm
  exact ⟨_, hM hcent, rfl⟩

theorem configuration_centralizer_conjugate_rigidity_witness
    {T L M : Subgroup G}
    (h : QTNQ T L M) :
    ∃ p : ℕ, p.Prime ∧ 5 ≤ p ∧ ∃ X : Subgroup G, X ≤ L ∧ (X.subgroupOf L).Characteristic ∧
      X ≤ (CFSG.solvableRadical L).map L.subtype ∧ NoPQuotient 2 X ∧
      Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p ∧ CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 ∧
      CFSG.pCore 2 X ≠ ⊥ ∧ normalizer (X : Set G) = M ∧
      Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 ∧
      IsFrattiniIrreducible X L ∧ (∀ u ∈ qtnqU L M, X ≤ M ⊓ centralizer {u}) ∧
      ∀ u ∈ qtnqU L M, IsFrattiniIrreducible X (M ⊓ centralizer {u}) →
        ∀ g : G, M ⊓ centralizer {u} ≤ CFSG.conjugate M g → g ∈ M ∧ CFSG.conjugate M g = M := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hcharM, -, -, -, -, -⟩ := NQTerm.nonquasisimple_normalizer_internal_module_properties h
  have hSQTM := isStronglyQuasithin_of_qtnq h
  have hSQT : CFSG.IsStronglyQuasithin L := isStronglyQuasithin_of_le h.l_le hSQTM
  have hLC := NQSetup.isCComponent_top_of_qtnq h
  obtain ⟨p, hp, hp5, D, -, -, -, hEX⟩ :=
    NQBlock.nq_characteristic_radical_odd_residual_witness hSQT hLC h.not_quasisimple
  obtain ⟨-, hXc₀, hXR₀, hX2₀, -, -, hexp₀, hrk₀, hW₀, -, hirr₀⟩ := hEX _ _ rfl rfl
  generalize hX₀def : closure {x | x ∈ D.comap (QuotientGroup.mk' (CFSG.pCore 2 L)) ∧
    Odd (orderOf x)} = X₀ at hXc₀ hXR₀ hX2₀ hexp₀ hrk₀ hW₀ hirr₀
  have hp1 : 1 < p := hp.one_lt
  set X : Subgroup G := X₀.map L.subtype with hXdef
  have hXL : X ≤ L := map_subtype_le _
  have hXsub : X.subgroupOf L = X₀ := comap_map_eq_self_of_injective L.subtype_injective X₀
  have hXchar : (X.subgroupOf L).Characteristic := hXsub ▸ hXc₀
  have hXRad : X ≤ (CFSG.solvableRadical L).map L.subtype := map_mono hXR₀
  set eX : X₀ ≃* X := X₀.equivMapOfInjective L.subtype L.subtype_injective with heX
  have hpc : (CFSG.pCore 2 X₀).map (eX : X₀ →* X) = CFSG.pCore 2 X := CFSG.pCore_map_iso 2 eX
  set eQ : (X₀ ⧸ CFSG.pCore 2 X₀) ≃* (X ⧸ CFSG.pCore 2 X) :=
    QuotientGroup.congr _ _ eX hpc with heQ
  set eW : ((X₀ ⧸ CFSG.pCore 2 X₀) ⧸ frattini (X₀ ⧸ CFSG.pCore 2 X₀)) ≃*
      ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) :=
    QuotientGroup.congr _ _ eQ (map_frattini_mulEquiv eQ) with heW
  have hX2 : NoPQuotient 2 X := NoPQuotient.of_surjective eX.toMonoidHom eX.surjective hX2₀
  have hexp : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = p := by
    rw [← Monoid.exponent_eq_of_mulEquiv eQ, hexp₀]
  have hrk : CFSG.pRank p (X ⧸ CFSG.pCore 2 X) = 2 := by rw [← pRank_congr hp1 eQ, hrk₀]
  have hW : Nat.card ((X ⧸ CFSG.pCore 2 X) ⧸ frattini (X ⧸ CFSG.pCore 2 X)) = p ^ 2 := by
    rw [← Nat.card_congr eW.toEquiv, hW₀]
  have hMX : M ≤ normalizer (X : Set G) := by
    rw [h.eq_normalizer]
    exact NQSetup.normalizer_le_normalizer_of_characteristic hXL hXchar
  have hXM : X ≤ M := hXL.trans h.l_le
  have hpow : ∀ w : X ⧸ CFSG.pCore 2 X, w ^ p = 1 := fun w => by
    rw [← hexp]
    exact Monoid.pow_exponent_eq_one w
  have hO2 : CFSG.pCore 2 X ≠ ⊥ := by
    intro hbot
    have hle := le_pCore_map_of_pCore_eq_bot hXM hMX hbot hcharM
    have hX2' : IsPGroup 2 X := by
      have h2 : IsPGroup 2 ((CFSG.pCore 2 M).map M.subtype) := CFSG.pCore_isPGroup.map _
      exact h2.to_le hle
    have htop : CFSG.pCore 2 X = ⊤ := by
      rw [eq_top_iff]
      exact SteinbergCC.le_pCore_of_normal_of_isPGroup normal_top
        (hX2'.of_equiv Subgroup.topEquiv.symm)
    have hsub : Subsingleton (X ⧸ CFSG.pCore 2 X) := by
      rw [htop]
      exact QuotientGroup.subsingleton_quotient_top
    have h1 : Monoid.exponent (X ⧸ CFSG.pCore 2 X) = 1 := Monoid.exp_eq_one_iff.mpr hsub
    rw [hexp] at h1
    exact hp1.ne' h1
  set A : Subgroup G := (CFSG.pCore 2 X).map X.subtype with hA
  have hA1 : A ≠ ⊥ := by
    intro hA0
    apply hO2
    rw [eq_bot_iff]
    intro a ha
    have h1 : (a : G) ∈ A := ⟨a, ha, rfl⟩
    rw [hA0, mem_bot] at h1
    exact (mem_bot).mpr (Subtype.ext h1)
  have hA2 : IsPGroup 2 A := CFSG.pCore_isPGroup.map _
  have hNA : normalizer (A : Set G) = M := by
    have hloc : IsTwoLocal (normalizer (A : Set G)) := ⟨A, hA1, hA2, rfl⟩
    exact h.max_two_local.2 _ hloc (hMX.trans (normalizer_le_normalizer_map_pCore 2 X))
  have hNX : normalizer (X : Set G) = M :=
    le_antisymm (hNA ▸ normalizer_le_normalizer_map_pCore 2 X) hMX
  have hLN : L ≤ normalizer (X : Set G) := h.l_le.trans hMX
  have hirrL : IsFrattiniIrreducible X L := by
    intro Y hY
    by_contra hne
    push Not at hne
    obtain ⟨hY0, hYT⟩ := hne
    have hYcard : Nat.card Y = p := by
      have hdvd : Nat.card Y ∣ p ^ 2 := hW ▸ Y.card_subgroup_dvd_card
      obtain ⟨k, hk, hYk⟩ := (Nat.dvd_prime_pow hp).1 hdvd
      interval_cases k
      · exact absurd (Subgroup.eq_bot_of_card_eq Y (by rw [hYk, pow_zero])) hY0
      · rw [hYk, pow_one]
      · exact absurd (Subgroup.eq_top_of_card_eq Y (by rw [hYk, hW])) hYT
    have hcompat : ∀ (l : L) (w : (X₀ ⧸ CFSG.pCore 2 X₀) ⧸ frattini (X₀ ⧸ CFSG.pCore 2 X₀)),
        eW (NQBlock.residualAction X₀ l w) =
          normalizerFrattiniConj X ⟨(l : G), hLN l.2⟩ (eW w) := by
      intro l w
      obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective w
      obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective w
      rfl
    obtain ⟨l, u, hu, hlu⟩ := hirr₀ (Y.map eW.symm.toMonoidHom) (by
      rw [card_map_of_injective (f := eW.symm.toMonoidHom) eW.symm.injective, hYcard])
    obtain ⟨y, hy, rfl⟩ := hu
    apply hlu
    refine ⟨normalizerFrattiniConj X ⟨(l : G), hLN l.2⟩ y, hY _ l.2 y hy, ?_⟩
    apply eW.injective
    rw [hcompat]
    simp
  have hXU : ∀ u ∈ qtnqU L M, X ≤ M ⊓ centralizer {u} := by
    intro u hu x hx
    refine mem_inf.mpr ⟨hXM hx, mem_centralizer_singleton_iff.mpr ?_⟩
    obtain ⟨l, hl, rfl⟩ := hXRad hx
    exact NQSetup.radical_commute_qtnqVc h hl (NQSetup.qtnqU_le_qtnqVc h hu)
  refine ⟨p, hp, hp5, X, hXL, hXchar, hXRad, hX2, hexp, hrk, hO2, hNX, hW, hirrL, hXU, ?_⟩
  intro u hu hirru g hg
  have hXn : (X.subgroupOf M).Normal := (normal_subgroupOf_iff_le_normalizer hXM).mpr hMX
  exact irreducible_residual_normalizer_conjugate_uniqueness hp (by omega) hXM hXn
    (hSQTM p hp (by omega)) hNX hX2 hexp hrk (hXU u hu) inf_le_left hirru g hg

end CFSG.Quasithin.H13.NQRigid

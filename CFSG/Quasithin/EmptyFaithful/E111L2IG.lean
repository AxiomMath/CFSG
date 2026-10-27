module

public import CFSG.Quasithin.EmptyFaithful.E111L2IF
public import CFSG.Quasithin.EmptyFaithful.E111L2IB

public section

namespace CFSG.Quasithin.E2.E22N.E111L.KMI

open CFSG.Open CFSG.Quasithin.Vol2.Ch11.SecB E111R
open scoped commutatorElement

variable {G : Type} [Group G]

section Diag

variable {X T A S C : Subgroup G} (h : DiagSetting X T A S C) [Fintype ↥C] [Finite G]
  {L₀ P V' : Subgroup G}
  (hd : S4Data (diagSub S C h.diagComm) T (T ⊓ Subgroup.centralizer (A : Set G)) L₀ P V')
include h hd

omit [Fintype ↥C] [Finite G] hd in
theorem A_le_K : A ≤ sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
    (T ⊓ Subgroup.centralizer (A : Set G)) :=
  fun _ ha => Subgroup.mem_sup_right ⟨h.AT ha, Subgroup.mem_centralizer_iff.mpr
    fun _ hb => h.comm hb ha⟩

omit hd [Finite G] in
theorem mem_centralizer_iff_of_conj {V' : Subgroup G} (hV'D : V' ≤ diagSub S C h.diagComm)
    (hcent : Subgroup.centralizer (V' : Set G) ⊓ diagSub S C h.diagComm = V') {a w : G}
    (hwD : w ∈ diagSub S C h.diagComm)
    (hw : ∀ x ∈ diagSub S C h.diagComm, a * x * a⁻¹ = w * x * w⁻¹) :
    a ∈ Subgroup.centralizer (V' : Set G) ↔ w ∈ V' := by
  have key : a ∈ Subgroup.centralizer (V' : Set G) ↔
      w ∈ Subgroup.centralizer (V' : Set G) := by
    simp only [Subgroup.mem_centralizer_iff]
    constructor
    · intro ha v hv
      have h1 := hw v (hV'D hv)
      have h2 := ha v hv
      have h3 : a * v * a⁻¹ = v := by rw [← h2]; group
      have h4 : w * v * w⁻¹ = v := by rw [← h1]; exact h3
      calc v * w = (w * v * w⁻¹) * w := by rw [h4]
        _ = w * v := by group
    · intro hw' v hv
      have h1 := hw v (hV'D hv)
      have h2 := hw' v hv
      have h3 : w * v * w⁻¹ = v := by rw [← h2]; group
      have h4 : a * v * a⁻¹ = v := by rw [h1]; exact h3
      calc v * a = (a * v * a⁻¹) * a := by rw [h4]
        _ = a * v := by group
  rw [key]
  constructor
  · intro h1
    have h2 : w ∈ Subgroup.centralizer (V' : Set G) ⊓ diagSub S C h.diagComm := ⟨h1, hwD⟩
    rwa [hcent] at h2
  · intro h1
    have h2 : w ∈ Subgroup.centralizer (V' : Set G) ⊓ diagSub S C h.diagComm := by
      rw [hcent]
      exact h1
    exact h2.1

theorem le_pCoreOf_of_centralizer
    (hcent : Subgroup.centralizer (V' : Set G) ⊓ diagSub S C h.diagComm = V')
    (hV' : IsKleinFour ↥V') {a : G} (ha : a ∈ A)
    (haV : a ∈ Subgroup.centralizer (V' : Set G)) :
    a ∈ pCoreOf 2 (sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
      (T ⊓ Subgroup.centralizer (A : Set G))) := by
  refine inf_centralizer_le_pCoreOf h hd hcent hV' (Subgroup.mem_inf.mpr ⟨A_le_K h ha, ?_⟩)
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  have hle : sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) V') ≤
      Subgroup.centralizer ({a} : Set G) := by
    refine sSup_le fun Z hZ => ?_
    obtain ⟨k, rfl⟩ := hZ
    intro x hx
    rw [A1b.mem_conjSub_iff] at hx
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hka : (k : G) * a = a * k := (Subgroup.mem_centralizer_iff.mp k.2.2 a ha).symm
    have hva := Subgroup.mem_centralizer_iff.mp haV _ hx
    refine Eq.symm ?_
    calc a * x = a * (k * ((k : G)⁻¹ * x * k) * (k : G)⁻¹) := by group
      _ = k * (a * ((k : G)⁻¹ * x * k)) * (k : G)⁻¹ := by
          rw [show a * (k * ((k : G)⁻¹ * x * k) * (k : G)⁻¹) =
            (a * k) * ((k : G)⁻¹ * x * k) * (k : G)⁻¹ by group, ← hka]
          group
      _ = k * (((k : G)⁻¹ * x * k) * a) * (k : G)⁻¹ := by rw [hva]
      _ = x * a := by
          rw [show (k : G) * (((k : G)⁻¹ * x * k) * a) * (k : G)⁻¹ =
            x * (k * a) * (k : G)⁻¹ by group, hka]
          group
  exact Subgroup.mem_centralizer_singleton_iff.mp (hle hx)

theorem not_mem_pCoreOf {y : G} (hyP : y ∈ P)
    (hy : ∀ w ∈ L₀, w ∉ V' → w * w = 1 → ∀ n : ℕ, ⁅y, w⁆ ^ 2 ^ n ≠ 1) {a w : G}
    (hwL : w ∈ L₀) (hwV : w ∉ V') (hww : w * w = 1)
    (hw : ∀ x ∈ diagSub S C h.diagComm, a * x * a⁻¹ = w * x * w⁻¹) :
    a ∉ pCoreOf 2 (sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
      (T ⊓ Subgroup.centralizer (A : Set G))) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro haO
  set K := sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
    (T ⊓ Subgroup.centralizer (A : Set G)) with hK
  have hyL : y ∈ L₀ := hd.P_le hyP
  have hyK : y ∈ K := by
    refine Subgroup.mem_sup_left (le_sSup (conj_mem_conjFam (Subgroup.one_mem _)) ?_)
    rw [A1b.conjSub_one]
    exact hyL
  have hyD : y⁻¹ ∈ diagSub S C h.diagComm := Subgroup.inv_mem _ (hd.L_le hyL)
  have hc : ⁅y, a⁆ = ⁅y, w⁆ := by
    calc ⁅y, a⁆ = y * (a * y⁻¹ * a⁻¹) := by rw [commutatorElement_def]; group
      _ = y * (w * y⁻¹ * w⁻¹) := by rw [hw _ hyD]
      _ = ⁅y, w⁆ := by rw [commutatorElement_def]; group
  have hcO : ⁅y, a⁆ ∈ pCoreOf 2 K := by
    rw [commutatorElement_def]
    exact Subgroup.mul_mem _ (conj_mem_pCoreOf K y hyK a haO) (Subgroup.inv_mem _ haO)
  obtain ⟨n, hn⟩ := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K ⟨_, hcO⟩
  apply hy w hwL hwV hww n
  rw [← hc]
  simpa using congrArg Subtype.val hn

theorem relIndex_pCoreOf (hCV : C ⊔ (A ⊓ Subgroup.normalizer (S : Set G)) = A)
    (hinn : ∀ a ∈ A ⊓ Subgroup.normalizer (S : Set G), ∃ s ∈ S,
      s⁻¹ * a ∈ Subgroup.centralizer (S : Set G))
    (hcent : Subgroup.centralizer (V' : Set G) ⊓ diagSub S C h.diagComm = V')
    (hV' : IsKleinFour ↥V') (hV₀ : IsKleinFour ↥(diagInner A S C h.diagComm))
    (hV₀L : diagInner A S C h.diagComm ≤ L₀)
    (hV₀V : Nat.card ↥(diagInner A S C h.diagComm ⊓ V') = 2) {y : G} (hyP : y ∈ P)
    (hy : ∀ w ∈ L₀, w ∉ V' → w * w = 1 → ∀ n : ℕ, ⁅y, w⁆ ^ 2 ^ n ≠ 1) :
    (pCoreOf 2 (sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
      (T ⊓ Subgroup.centralizer (A : Set G)))).relIndex A = 2 := by
  set V₀ := diagInner A S C h.diagComm with hV₀def
  set O := pCoreOf 2 (sSup (conjFam (T ⊓ Subgroup.centralizer (A : Set G)) L₀) ⊔
    (T ⊓ Subgroup.centralizer (A : Set G))) with hO
  have hVD := S4Data.V_le_D h hd
  have hww : ∀ w ∈ V₀, w * w = 1 := fun w hw => congrArg Subtype.val (hV₀.mul_self ⟨w, hw⟩)
  have hmemO : ∀ a ∈ A, a ∈ O ↔ a ∈ Subgroup.centralizer (V' : Set G) := by
    intro a ha
    refine ⟨fun haO => ?_, le_pCoreOf_of_centralizer h hd hcent hV' ha⟩
    by_contra haV
    obtain ⟨w, hw, hwa⟩ := exists_conj_diagInner h hCV hinn ha
    have hwV : w ∉ V' := fun h1 =>
      haV ((mem_centralizer_iff_of_conj h hVD hcent (diagInner_le_diag h hw) hwa).mpr h1)
    exact not_mem_pCoreOf h hd hyP hy (hV₀L hw) hwV (hww w hw) hwa haO
  have hidx : ((V₀ ⊓ V').subgroupOf V₀).index = 2 := by
    have h1 := Subgroup.relIndex_mul_card (V₀ ⊓ V') V₀
    rw [inf_eq_left.mpr (inf_le_left : V₀ ⊓ V' ≤ V₀), hV₀V, hV₀.card_four] at h1
    have h2 : (V₀ ⊓ V').relIndex V₀ = 2 := by omega
    exact h2
  obtain ⟨w₀, hw₀, hw₀V⟩ : ∃ w₀ ∈ V₀, w₀ ∉ V' := by
    by_contra hc
    push Not at hc
    have hle : V₀ ≤ V₀ ⊓ V' := fun x hx => ⟨hx, hc x hx⟩
    have h1 := Nat.card_le_card_of_injective _ (Subgroup.inclusion_injective hle)
    rw [hV₀V, hV₀.card_four] at h1
    omega
  obtain ⟨v, hvA, hv⟩ := exists_of_mem_diagInner h hw₀
  refine Subgroup.index_eq_two_iff.mpr ⟨⟨v, hvA⟩, fun b => ?_⟩
  obtain ⟨wb, hwb, hwbb⟩ := exists_conj_diagInner h hCV hinn b.2
  have hbv : ∀ x ∈ diagSub S C h.diagComm,
      (b : G) * v * x * ((b : G) * v)⁻¹ = (wb * w₀) * x * (wb * w₀)⁻¹ := by
    intro x hx
    have h1 : w₀ * x * w₀⁻¹ ∈ diagSub S C h.diagComm :=
      Subgroup.mul_mem _ (Subgroup.mul_mem _ (diagInner_le_diag h hw₀) hx)
        (Subgroup.inv_mem _ (diagInner_le_diag h hw₀))
    calc (b : G) * v * x * ((b : G) * v)⁻¹ = b * (v * x * v⁻¹) * (b : G)⁻¹ := by group
      _ = b * (w₀ * x * w₀⁻¹) * (b : G)⁻¹ := by rw [hv x hx]
      _ = wb * (w₀ * x * w₀⁻¹) * wb⁻¹ := hwbb _ h1
      _ = (wb * w₀) * x * (wb * w₀)⁻¹ := by group
  have hwbw₀ : wb * w₀ ∈ diagSub S C h.diagComm :=
    Subgroup.mul_mem _ (diagInner_le_diag h hwb) (diagInner_le_diag h hw₀)
  have e1 := mem_centralizer_iff_of_conj h hVD hcent hwbw₀ hbv
  have e2 := mem_centralizer_iff_of_conj h hVD hcent (diagInner_le_diag h hwb) hwbb
  have e3 : wb * w₀ ∈ V' ↔ (wb ∈ V' ↔ w₀ ∈ V') := by
    have := Subgroup.mul_mem_iff_of_index_two hidx (a := ⟨wb, hwb⟩) (b := ⟨w₀, hw₀⟩)
    simpa [Subgroup.mem_subgroupOf, hwb, hw₀] using this
  rw [xor_iff_iff_not]
  change (b : G) * v ∈ O ↔ ¬ ((b : G) ∈ O)
  rw [hmemO _ (A.mul_mem b.2 hvA), hmemO _ b.2, e1, e2, e3]
  tauto

end Diag

end CFSG.Quasithin.E2.E22N.E111L.KMI

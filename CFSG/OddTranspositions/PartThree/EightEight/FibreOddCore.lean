module

public import Mathlib.Algebra.Group.Commutator
public import CFSG.GroupTheory.PCore.Defs
public import CFSG.OddTranspositions.HalphaQuotient
public import CFSG.OddTranspositions.PartThree.EightEight.WreathFourBlocks
import CFSG.OddTranspositions.PartThree.Nine.NineFiveX
import CFSG.LocalAnalysis.ComponentClassification.Foote47Lift
import CFSG.LocalAnalysis.ComponentInitial.SteinbergCCOddNormalCore
import CFSG.OddTranspositions.PartThree.EightOne.Quotient

public section

namespace CFSG.OddTranspositions.PartThree.EightEight

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {D : Set G}

omit [Finite G] in
@[expose] def Qalpha (D ρ : Set G) : Subgroup (Halpha D ρ) :=
  (CFSG.oddCore (CFSG.solvableRadical (Halpha D ρ))).map
    (CFSG.solvableRadical (Halpha D ρ)).subtype

omit [Finite G] in
theorem Qalpha_le_solvableRadical (D ρ : Set G) :
    Qalpha D ρ ≤ CFSG.solvableRadical (Halpha D ρ) := by
  exact Subgroup.map_subtype_le _

omit [Finite G] in
instance Qalpha_normal (D ρ : Set G) : (Qalpha D ρ).Normal := by
  have hchar : (CFSG.oddCore (CFSG.solvableRadical (Halpha D ρ))).Characteristic :=
    CFSG.LocalAnalysis.ComponentInitial.OddNormalCore.oddCore_characteristic _
  have hMn : (CFSG.solvableRadical (Halpha D ρ)).Normal :=
    Subgroup.sSup_normal _ fun _ hN => hN.1
  exact ConjAct.normal_of_characteristic_of_normal (hH := hMn) (h := hchar)

theorem odd_card_Qalpha (D ρ : Set G) : Odd (Nat.card (Qalpha D ρ)) := by
  rw [Qalpha, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact EightOne.odd_card_oddCore

omit [Finite G] in
theorem le_Qalpha {ρ : Set G} {K : Subgroup (Halpha D ρ)}
    (hKM : K ≤ CFSG.solvableRadical (Halpha D ρ))
    (hK : ∀ μ ∈ CFSG.solvableRadical (Halpha D ρ), ∀ k ∈ K, μ * k * μ⁻¹ ∈ K)
    (hodd : Odd (Nat.card K)) : K ≤ Qalpha D ρ := by
  let M : Subgroup (Halpha D ρ) := CFSG.solvableRadical (Halpha D ρ)
  have hKn : (K.subgroupOf M).Normal := by
    rw [Subgroup.normal_subgroupOf_iff hKM]
    exact fun h m hh hm => hK m hm h hh
  have hcard : Nat.card (K.subgroupOf M) = Nat.card K :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hKM).toEquiv
  have hle : K.subgroupOf M ≤ CFSG.oddCore M :=
    le_sSup (s := {N : Subgroup M | N.Normal ∧ Odd (Nat.card N)})
      ⟨hKn, by rw [hcard]; exact hodd⟩
  have hmain : K ≤ (CFSG.oddCore M).map M.subtype := by
    calc K = (K.subgroupOf M).map M.subtype :=
          (Subgroup.map_subgroupOf_eq_of_le hKM).symm
      _ ≤ (CFSG.oddCore M).map M.subtype := Subgroup.map_mono hle
  exact hmain

private theorem conj_mem_closure_mul_fibre (hC : HypothesisC D) {δ μ : Halpha D hC.alpha}
    (hδ : δ ∈ DstarH hC) (hμ : μ ∈ CFSG.solvableRadical (Halpha D hC.alpha))
    {F : Set (Halpha D hC.alpha)}
    (hF : ∀ u, u ∈ F ↔ u ∈ DstarH hC ∧
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) u =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) δ)
    {x : Halpha D hC.alpha} (hx : x ∈ Subgroup.closure ((fun u => u * δ) '' F)) :
    μ * x * μ⁻¹ ∈ Subgroup.closure ((fun u => u * δ) '' F) := by
  have hμ1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) μ = 1 :=
    (QuotientGroup.eq_one_iff μ).mpr hμ
  have hδ2 : δ * δ = 1 := (DstarH_isOddTransp hC).mul_self_eq_one hδ
  induction hx using Subgroup.closure_induction with
  | mem g hg =>
      obtain ⟨u, hu, rfl⟩ := hg
      have hu₀ := (hF u).mp hu
      have hu' : μ * u * μ⁻¹ ∈ F := (hF _).mpr ⟨DstarH_conj_mem hC hu₀.1, by
        rw [map_mul, map_mul, map_inv, hμ1, one_mul, hu₀.2, inv_one, mul_one]⟩
      have hδ'D : μ * δ * μ⁻¹ ∈ DstarH hC := DstarH_conj_mem hC hδ
      have hδ' : μ * δ * μ⁻¹ ∈ F := (hF _).mpr ⟨hδ'D, by
        rw [map_mul, map_mul, map_inv, hμ1, one_mul, inv_one, mul_one]⟩
      have h1 : (μ * u * μ⁻¹) * δ ∈ Subgroup.closure ((fun u => u * δ) '' F) :=
        Subgroup.subset_closure ⟨_, hu', rfl⟩
      have h2 : (μ * δ * μ⁻¹) * δ ∈ Subgroup.closure ((fun u => u * δ) '' F) :=
        Subgroup.subset_closure ⟨_, hδ', rfl⟩
      have he : μ * (u * δ) * μ⁻¹ =
          ((μ * u * μ⁻¹) * δ) * ((μ * δ * μ⁻¹) * δ)⁻¹ := by
        have h1 : δ⁻¹ = δ := inv_eq_of_mul_eq_one_right hδ2
        have h2 : (μ * δ * μ⁻¹)⁻¹ = μ * δ * μ⁻¹ :=
          inv_eq_of_mul_eq_one_right ((DstarH_isOddTransp hC).mul_self_eq_one hδ'D)
        have h3 : ((μ * δ * μ⁻¹) * δ)⁻¹ = δ * (μ * δ * μ⁻¹) := by
          rw [mul_inv_rev, h1, h2]
        rw [h3]
        rw [show μ * u * μ⁻¹ * δ * (δ * (μ * δ * μ⁻¹)) =
          μ * u * μ⁻¹ * (δ * δ) * (μ * δ * μ⁻¹) by group]
        rw [hδ2]
        group
      rw [he]
      exact Subgroup.mul_mem _ h1 (Subgroup.inv_mem _ h2)
  | one => simp
  | mul a b _ _ ha hb =>
      have he : μ * (a * b) * μ⁻¹ = (μ * a * μ⁻¹) * (μ * b * μ⁻¹) := by
        group
      rw [he]
      exact Subgroup.mul_mem _ ha hb
  | inv a _ ha =>
      have he : μ * a⁻¹ * μ⁻¹ = (μ * a * μ⁻¹)⁻¹ := by
        group
      rw [he]
      exact Subgroup.inv_mem _ ha

theorem closure_mul_fibre_le_Qalpha (hC : HypothesisC D) (hA : FibresAnticlique D hC.alpha)
    {δ : Halpha D hC.alpha} (hδ : δ ∈ DstarH hC) :
    Subgroup.closure ((fun u => u * δ) ''
        {u | u ∈ DstarH hC ∧ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) u =
          QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) δ}) ≤
      Qalpha D hC.alpha := by
  let H := Halpha D hC.alpha
  let M : Subgroup H := CFSG.solvableRadical H
  let mk : H →* H ⧸ M := QuotientGroup.mk' M
  have hδ2 : δ * δ = 1 := (DstarH_isOddTransp hC).mul_self_eq_one hδ
  let F : Set H := {u | u ∈ DstarH hC ∧ mk u = mk δ}
  have hF : ∀ u : H, u ∈ F ↔ u ∈ DstarH hC ∧ mk u = mk δ := fun _ => Iff.rfl
  have hcomm_mk : ∀ y ∈ Subgroup.closure F, Commute (mk y) (mk δ) := by
    intro y hy
    induction hy using Subgroup.closure_induction with
    | mem u hu =>
        have hu' : mk u = mk δ := ((hF u).mp hu).2
        rw [hu']
    | one => exact Commute.one_left _
    | mul a b _ _ ha hb => simpa using ha.mul_left hb
    | inv a _ ha => simpa using ha.inv_left
  have hPn : ∀ y ∈ Subgroup.closure F, ∀ u ∈ F, y * u * y⁻¹ ∈ F := by
    intro y hy u hu
    refine (hF _).mpr ⟨DstarH_conj_mem hC hu.1, ?_⟩
    have hmul : mk (y * u * y⁻¹) = mk y * mk u * (mk y)⁻¹ := by
      rw [map_mul, map_mul, map_inv]
    rw [hmul, hu.2, Commute.eq (hcomm_mk y hy)]
    group
  have hP : ∀ a ∈ F, ∀ b ∈ F, Commute a b → a = b := by
    intro a ha b hb hab
    by_contra hne
    exact hA a b ha.1 hb.1 hne (ha.2.trans hb.2.symm) hab
  have hδF : δ ∈ F := (hF δ).mpr ⟨hδ, rfl⟩
  have hOodd : Odd (Nat.card (Subgroup.closure ((fun u => u * δ) '' F))) :=
    Nine.odd_card_closure_mul_of_forall_commute (DstarH_isOddTransp hC)
      (fun _ hu => hu.1) hP hPn hδF
  have hO_le_M : Subgroup.closure ((fun u => u * δ) '' F) ≤ M := by
    rw [Subgroup.closure_le]
    rintro _ ⟨u, hu, rfl⟩
    refine (QuotientGroup.eq_one_iff (u * δ)).mp ?_
    change mk (u * δ) = 1
    rw [map_mul, hu.2, ← map_mul, hδ2, map_one]
  exact le_Qalpha hO_le_M (fun μ hμ x hx => conj_mem_closure_mul_fibre hC hδ hμ hF hx) hOodd

theorem mem_fibre_iff_exists_conj (hC : HypothesisC D) (hA : FibresAnticlique D hC.alpha)
    {δ p : Halpha D hC.alpha} (hδ : δ ∈ DstarH hC) :
    (p ∈ DstarH hC ∧ QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) δ) ↔
      ∃ q ∈ Qalpha D hC.alpha, p = q * δ * q⁻¹ := by
  let H := Halpha D hC.alpha
  let M : Subgroup H := CFSG.solvableRadical H
  let mk : H →* H ⧸ M := QuotientGroup.mk' M
  have hmkM : ∀ x ∈ M, mk x = 1 := fun x hx => (QuotientGroup.eq_one_iff x).mpr hx
  constructor
  · intro hpF
    have hpδ : p * δ ∈ Qalpha D hC.alpha :=
      closure_mul_fibre_le_Qalpha hC hA hδ (Subgroup.subset_closure ⟨p, hpF, rfl⟩)
    have hoddord : Odd (orderOf (p * δ)) :=
      (odd_card_Qalpha D hC.alpha).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hpδ)
    obtain ⟨u, hu, hueq⟩ :=
      CFSG.ComponentClassification.Foote47.exists_conj_of_odd_orderOf_mul
        ((DstarH_isOddTransp hC).mul_self_eq_one hpF.1)
        ((DstarH_isOddTransp hC).mul_self_eq_one hδ) hoddord
    refine ⟨u, Subgroup.zpowers_le.mpr hpδ hu, ?_⟩
    rw [hueq]
    group
  · rintro ⟨q, hq, rfl⟩
    refine ⟨DstarH_conj_mem hC hδ, ?_⟩
    rw [map_mul, map_mul, map_inv, hmkM q (Qalpha_le_solvableRadical D hC.alpha hq), one_mul,
      inv_one, mul_one]

theorem exists_mem_Qalpha_conj_eq (hC : HypothesisC D) (hA : FibresAnticlique D hC.alpha)
    {p μ : Halpha D hC.alpha} (hp : p ∈ DstarH hC)
    (hμ : μ ∈ CFSG.solvableRadical (Halpha D hC.alpha)) :
    ∃ q ∈ Qalpha D hC.alpha, μ * p * μ⁻¹ = q * p * q⁻¹ := by
  have hμ1 : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) μ = 1 :=
    (QuotientGroup.eq_one_iff μ).mpr hμ
  have hp' : μ * p * μ⁻¹ ∈ DstarH hC := DstarH_conj_mem hC hp
  have hmk : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) (μ * p * μ⁻¹) =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p := by
    rw [map_mul, map_mul, map_inv, hμ1, one_mul, inv_one, mul_one]
  exact (mem_fibre_iff_exists_conj hC hA (δ := p) hp).mp ⟨hp', hmk⟩

theorem commutatorElement_mem_Qalpha (hC : HypothesisC D) (hA : FibresAnticlique D hC.alpha)
    {μ : Halpha D hC.alpha} (hμ : μ ∈ CFSG.solvableRadical (Halpha D hC.alpha))
    (h : Halpha D hC.alpha) : ⁅μ, h⁆ ∈ Qalpha D hC.alpha := by
  let H := Halpha D hC.alpha
  let Q : Subgroup H := Qalpha D hC.alpha
  have hgen : ∀ p ∈ DstarH hC, ⁅μ, p⁆ ∈ Q := by
    intro p hp
    obtain ⟨q, hq, hqeq⟩ := exists_mem_Qalpha_conj_eq hC hA hp hμ
    have he : ⁅μ, p⁆ = q * (p * q⁻¹ * p⁻¹) := by
      rw [commutatorElement_def, hqeq]
      group
    rw [he]
    exact Subgroup.mul_mem _ hq ((inferInstance : Q.Normal).conj_mem _ (Subgroup.inv_mem _ hq) p)
  have hcl : ∀ x ∈ Subgroup.closure (DstarH hC), ⁅μ, x⁆ ∈ Q := by
    intro x hx
    induction hx using Subgroup.closure_induction with
    | mem p hp => exact hgen p hp
    | one => simp [commutatorElement_def]
    | mul a b _ _ ha hb =>
        have he : ⁅μ, a * b⁆ = ⁅μ, a⁆ * (a * ⁅μ, b⁆ * a⁻¹) := by
          rw [commutatorElement_def, commutatorElement_def]
          group
        rw [he]
        exact Subgroup.mul_mem _ ha ((inferInstance : Q.Normal).conj_mem _ hb a)
    | inv a _ ha =>
        have he : ⁅μ, a⁻¹⁆ = a⁻¹ * ⁅μ, a⁆⁻¹ * a := by
          rw [commutatorElement_def, commutatorElement_def]
          group
        rw [he]
        simpa using (inferInstance : Q.Normal).conj_mem _ (Subgroup.inv_mem _ ha) a⁻¹
  exact hcl h (by rw [DstarH_closure_eq_top hC]; exact Subgroup.mem_top h)

private theorem conj_mul_conj_eq_of_conj_eq (hC : HypothesisC D) {m x₀ h p : Halpha D hC.alpha}
    (hact : ∀ f ∈ DstarH hC, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) f =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x₀ →
          m * f * m⁻¹ = x₀ * f * x₀⁻¹)
    (hh : h * x₀ * h⁻¹ = p) {f : Halpha D hC.alpha} (hf : f ∈ DstarH hC)
    (hmkf : QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) f =
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p) :
    (h * m * h⁻¹) * f * (h * m * h⁻¹)⁻¹ = p * f * p⁻¹ := by
  let mk := QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha))
  have hf₀ : h⁻¹ * f * h ∈ DstarH hC := by
    simpa using DstarH_conj_mem hC (h := h⁻¹) hf
  have hmk₀ : mk (h⁻¹ * f * h) = mk x₀ := by
    have hp' : mk p = mk h * mk x₀ * (mk h)⁻¹ := by
      rw [← hh, map_mul, map_mul, map_inv]
    have hf' : mk (h⁻¹ * f * h) = (mk h)⁻¹ * mk f * mk h := by
      rw [map_mul, map_mul, map_inv]
    rw [hf', hmkf, hp']
    group
  have hconj := congrArg (fun z => h * z * h⁻¹) (hact (h⁻¹ * f * h) hf₀ hmk₀)
  have e1 : h * (m * (h⁻¹ * f * h) * m⁻¹) * h⁻¹ = (h * m * h⁻¹) * f * (h * m * h⁻¹)⁻¹ := by
    group
  have e2 : h * (x₀ * (h⁻¹ * f * h) * x₀⁻¹) * h⁻¹ = p * f * p⁻¹ := by
    rw [← hh]
    group
  rwa [e1, e2] at hconj

theorem exists_mem_Qalpha_conj_eq_conj (hC : HypothesisC D) (hA : FibresAnticlique D hC.alpha)
    {m : Halpha D hC.alpha} (hm : m ∈ CFSG.solvableRadical (Halpha D hC.alpha))
    (hm2 : m * m = 1) (h : Halpha D hC.alpha) :
    ∃ g ∈ Qalpha D hC.alpha, m = g * (h * m * h⁻¹) * g⁻¹ := by
  have hm'2 : (h * m * h⁻¹) * (h * m * h⁻¹) = 1 := by
    rw [show (h * m * h⁻¹) * (h * m * h⁻¹) = h * (m * m) * h⁻¹ by group, hm2]
    group
  have hm'm_Q : (h * m * h⁻¹) * m ∈ Qalpha D hC.alpha := by
    have hmi : m⁻¹ = m := inv_eq_of_mul_eq_one_right hm2
    have he : (h * m * h⁻¹) * m = ⁅m, h⁆⁻¹ := by
      rw [commutatorElement_def]
      have h1 : (m * h * m⁻¹ * h⁻¹)⁻¹ = h * m * h⁻¹ * m := by
        simp only [mul_inv_rev, inv_inv, hmi]
        group
      rw [h1]
    rw [he]
    exact Subgroup.inv_mem _ (commutatorElement_mem_Qalpha hC hA hm h)
  have hodd : Odd (orderOf ((h * m * h⁻¹) * m)) :=
    (odd_card_Qalpha D hC.alpha).of_dvd_nat (Subgroup.orderOf_dvd_natCard _ hm'm_Q)
  obtain ⟨u, hu, hueq⟩ :=
    CFSG.ComponentClassification.Foote47.exists_conj_of_odd_orderOf_mul hm'2 hm2 hodd
  refine ⟨u⁻¹, Subgroup.inv_mem _ (Subgroup.zpowers_le.mpr hm'm_Q hu), ?_⟩
  rw [inv_inv]
  exact hueq

theorem exists_forall_mem_fibre_commute_iff (hC : HypothesisC D)
    (hA : FibresAnticlique D hC.alpha) {m x₀ : Halpha D hC.alpha}
    (hm : m ∈ CFSG.solvableRadical (Halpha D hC.alpha)) (hm2 : m * m = 1)
    (hx₀ : x₀ ∈ DstarH hC)
    (hact : ∀ f ∈ DstarH hC, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) f =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x₀ →
          m * f * m⁻¹ = x₀ * f * x₀⁻¹)
    {p : Halpha D hC.alpha} (hp : p ∈ DstarH hC) :
    ∃ g ∈ Qalpha D hC.alpha, ∀ f ∈ DstarH hC,
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) f =
          QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p →
        (Commute f m ↔ f = g * p * g⁻¹) := by
  let H := Halpha D hC.alpha
  let M : Subgroup H := CFSG.solvableRadical H
  let Q : Subgroup H := Qalpha D hC.alpha
  let mk : H →* H ⧸ M := QuotientGroup.mk' M
  have hQM : Q ≤ M := Qalpha_le_solvableRadical D hC.alpha
  have hmkM : ∀ x ∈ M, mk x = 1 := fun x hx => (QuotientGroup.eq_one_iff x).mpr hx
  obtain ⟨h, hh⟩ := DstarH_transitive hC hx₀ hp
  let m' : H := h * m * h⁻¹
  have hact' : ∀ f ∈ DstarH hC, mk f = mk p → m' * f * m'⁻¹ = p * f * p⁻¹ :=
    fun f hf hmkf => conj_mul_conj_eq_of_conj_eq hC hact hh hf hmkf
  obtain ⟨g, hgQ, hgeq⟩ : ∃ g ∈ Q, m = g * m' * g⁻¹ :=
    exists_mem_Qalpha_conj_eq_conj hC hA hm hm2 h
  refine ⟨g, hgQ, fun f hf hmkf => ?_⟩
  have hX : g⁻¹ * f * g ∈ DstarH hC := by
    simpa using DstarH_conj_mem hC (h := g⁻¹) hf
  have hmkX : mk (g⁻¹ * f * g) = mk p := by
    rw [map_mul, map_mul, map_inv, hmkM g (hQM hgQ), inv_one, one_mul, hmkf, mul_one]
  have key : ∀ a b : H, Commute b a ↔ a * b * a⁻¹ = b := fun a b =>
    Commute.symm_iff.trans ((commute_iff_eq a b).trans mul_inv_eq_iff_eq_mul.symm)
  have stepA : Commute f m ↔ Commute (g⁻¹ * f * g) m' := by
    have h1 := (Commute.conj_iff (a := f) (b := m) g⁻¹).symm
    rwa [inv_inv, show g⁻¹ * m * g = m' by rw [hgeq]; group] at h1
  have stepB : Commute (g⁻¹ * f * g) m' ↔ Commute (g⁻¹ * f * g) p := by
    rw [key, key, hact' (g⁻¹ * f * g) hX hmkX]
  have stepC : Commute (g⁻¹ * f * g) p ↔ g⁻¹ * f * g = p :=
    ⟨fun hc => Classical.byContradiction fun hne =>
        hA p _ hp hX (fun hpq => hne hpq.symm) hmkX.symm hc.symm,
      fun he => (congrArg (fun x => Commute x p) he).mpr (Commute.refl p)⟩
  have stepD : g⁻¹ * f * g = p ↔ f = g * p * g⁻¹ :=
    ⟨fun he => by rw [← he]; group, fun he => by rw [he]; group⟩
  exact stepA.trans (stepB.trans (stepC.trans stepD))

theorem existsUnique_mem_fibre_commute (hC : HypothesisC D)
    (hA : FibresAnticlique D hC.alpha) {m x₀ : Halpha D hC.alpha}
    (hm : m ∈ CFSG.solvableRadical (Halpha D hC.alpha)) (hm2 : m * m = 1)
    (hx₀ : x₀ ∈ DstarH hC)
    (hact : ∀ f ∈ DstarH hC, QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) f =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) x₀ →
          m * f * m⁻¹ = x₀ * f * x₀⁻¹)
    {p : Halpha D hC.alpha} (hp : p ∈ DstarH hC) :
    ∃! f, f ∈ DstarH hC ∧
      QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) f =
        QuotientGroup.mk' (CFSG.solvableRadical (Halpha D hC.alpha)) p ∧ Commute f m := by
  let H := Halpha D hC.alpha
  let M : Subgroup H := CFSG.solvableRadical H
  let Q : Subgroup H := Qalpha D hC.alpha
  let mk : H →* H ⧸ M := QuotientGroup.mk' M
  have hQM : Q ≤ M := Qalpha_le_solvableRadical D hC.alpha
  have hmkM : ∀ x ∈ M, mk x = 1 := fun x hx => (QuotientGroup.eq_one_iff x).mpr hx
  obtain ⟨g, hgQ, hg⟩ := exists_forall_mem_fibre_commute_iff hC hA hm hm2 hx₀ hact hp
  have hgp : g * p * g⁻¹ ∈ DstarH hC := DstarH_conj_mem hC hp
  have hgpmk : mk (g * p * g⁻¹) = mk p := by
    rw [map_mul, map_mul, map_inv, hmkM g (hQM hgQ), inv_one, one_mul, mul_one]
  have hcomm : Commute (g * p * g⁻¹) m := (hg _ hgp hgpmk).mpr rfl
  refine ⟨g * p * g⁻¹, ⟨hgp, hgpmk, hcomm⟩, ?_⟩
  rintro f ⟨hf, hfm, hfc⟩
  exact (hg f hf hfm).mp hfc

end CFSG.OddTranspositions.PartThree.EightEight

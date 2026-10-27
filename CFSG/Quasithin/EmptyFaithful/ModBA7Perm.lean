module

public import CFSG.Quasithin.EmptyFaithful.S14610Q3
public import CFSG.Quasithin.Vol2.Ch12Sec2Action
public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.C1Blocks
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Quasithin.EmptyFaithful.S1422Basic

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique Equiv Equiv.Perm CFSG.Quasithin.G6
open scoped commutatorElement IsMulCommutative

namespace ModB

@[expose] def A7PerfectSixCore : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) → Nat.card W = 2 ^ 6 →
    ∀ ρ : ↥(alternatingGroup (Fin 7)) →* MulAut W, commV ρ.range = ⊤ →
      ∃ Φ : W ≃* ↥(coreMod 7), ∀ (σ : ↥(alternatingGroup (Fin 7))) (w : W),
        Φ (ρ σ w) = coreAct 7 (σ : Perm (Fin 7)) (Φ w)

theorem exists_fixed_core_of_stable (Y : Subgroup ↥(alternatingGroup (Fin 7))) (S : Finset (Fin 7))
    (hS : ∀ σ ∈ Y, ∀ j, j ∈ S ↔ (σ : Perm (Fin 7)) j ∈ S) (hne : S.Nonempty)
    (hev : Even S.card) :
    ∃ v ∈ coreMod 7, v ≠ 1 ∧ ∀ σ ∈ Y, permAct 7 (σ : Perm (Fin 7)) v = v := by
  classical
  let v : PermMod 7 := Multiplicative.ofAdd (fun i => if i ∈ S then (1 : ZMod 2) else 0)
  refine ⟨v, ?_, ?_, ?_⟩
  · rw [mem_coreMod]
    simp only [v, toAdd_ofAdd, Finset.sum_boole]
    have : (S.card : ZMod 2) = 0 := by
      rcases hev with ⟨k, hk⟩
      rw [hk]
      have : (k + k : ℕ) = 2 * k := by ring
      rw [this]
      push_cast
      have : (2 : ZMod 2) = 0 := by decide
      rw [this, zero_mul]
    have e : Finset.univ.filter (fun x => x ∈ S) = S := by ext; simp
    rw [e]
    exact this
  · intro h
    obtain ⟨j, hj⟩ := hne
    have := congrArg (fun x : PermMod 7 => Multiplicative.toAdd x j) h
    simp [v, hj] at this
  · intro σ hσ
    apply Multiplicative.toAdd.injective
    funext i
    rw [permAct_apply]
    simp only [v, toAdd_ofAdd]
    have h1 := hS σ⁻¹ (inv_mem hσ) i
    rw [Subgroup.coe_inv] at h1
    show (if (↑σ : Perm (Fin 7))⁻¹ i ∈ S then (1 : ZMod 2) else 0) = if i ∈ S then 1 else 0
    by_cases h : i ∈ S
    · have h' := h1.mp h
      simp only [h, h', ↓reduceIte]
    · have h' : (↑σ : Perm (Fin 7))⁻¹ i ∉ S := fun h' => h (h1.mpr h')
      simp only [h, h', ↓reduceIte]

theorem exists_fixed_core_seven (Y : Subgroup ↥(alternatingGroup (Fin 7))) (hY : ¬ 7 ∣ Nat.card Y) :
    ∃ v ∈ coreMod 7, v ≠ 1 ∧ ∀ σ ∈ Y, permAct 7 (σ : Perm (Fin 7)) v = v := by
  classical
  let O : Finset (Fin 7) := Finset.univ.filter fun j => ∃ σ ∈ Y, (σ : Perm (Fin 7)) 0 = j
  have hO0 : (0 : Fin 7) ∈ O := by
    simp only [O, Finset.mem_filter, Finset.mem_univ, true_and]
    exact ⟨1, Y.one_mem, rfl⟩
  have hOS : ∀ σ ∈ Y, ∀ j, j ∈ O ↔ (σ : Perm (Fin 7)) j ∈ O := by
    have h1 : ∀ σ ∈ Y, ∀ j, j ∈ O → (σ : Perm (Fin 7)) j ∈ O := by
      intro σ hσ j hj
      simp only [O, Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      obtain ⟨τ, hτ, rfl⟩ := hj
      exact ⟨σ * τ, Y.mul_mem hσ hτ, rfl⟩
    intro σ hσ j
    refine ⟨h1 σ hσ j, fun h => ?_⟩
    have := h1 σ⁻¹ (Y.inv_mem hσ) _ h
    simpa using this
  have hOne : O ≠ Finset.univ := by
    intro h
    apply hY
    have hdvd : Nat.card (MulAction.orbit Y (0 : Fin 7)) ∣ Nat.card Y := by
      rw [Nat.card_congr (MulAction.orbitEquivQuotientStabilizer Y (0 : Fin 7))]
      exact Subgroup.index_dvd_card _
    have hcard : Nat.card (MulAction.orbit Y (0 : Fin 7)) = 7 := by
      have : MulAction.orbit Y (0 : Fin 7) = Set.univ := by
        refine Set.eq_univ_iff_forall.mpr fun j => ?_
        have hj : j ∈ O := by rw [h]; exact Finset.mem_univ j
        simp only [O, Finset.mem_filter, Finset.mem_univ, true_and] at hj
        obtain ⟨σ, hσ, rfl⟩ := hj
        exact ⟨⟨σ, hσ⟩, rfl⟩
      rw [this]
      simp
    rwa [hcard] at hdvd
  rcases Nat.even_or_odd O.card with hev | hodd
  · exact exists_fixed_core_of_stable Y O hOS ⟨0, hO0⟩ hev
  · refine exists_fixed_core_of_stable Y Oᶜ ?_ ?_ ?_
    · intro σ hσ j
      simp only [Finset.mem_compl]
      exact not_congr (hOS σ hσ j)
    · exact Finset.nonempty_iff_ne_empty.mpr fun h => hOne ((Finset.compl_eq_empty_iff O).1 h)
    · have hc := Finset.card_compl O
      rw [Fintype.card_fin] at hc
      rw [hc]
      have : O.card ≤ 7 := by
        have := Finset.card_le_univ O
        simpa using this
      rcases hodd with ⟨k, hk⟩
      exact ⟨(7 - O.card) / 2, by omega⟩


section Reduction

variable {G : Type} [Group G] [Finite G]

theorem card_eq_168_of_isPSL_three_two {X : Type} [Group X] (h : IsPSL 3 2 1 X) :
    Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem wOf1469_eq_blockU_of_short {K : Subgroup G} (hK : IsShort2 K) :
    wOf1469 K = blockU K := by
  have hUQ : blockU K ≤ blockQ K ⊓ Subgroup.centralizer (blockQ K : Set G) := hK.2.2.1.1
  apply le_antisymm
  · have hA : omegaOneCenterOf (pCoreOf 2 K) ≤ pCoreOf 2 K :=
      (Subgroup.closure_le _).mpr (fun _ hx => hx.1.1)
    exact Subgroup.commutator_mono hA le_rfl
  · have hUA : blockU K ≤ omegaOneCenterOf (pCoreOf 2 K) := fun x hx =>
      Subgroup.subset_closure ⟨hUQ hx, hK.2.2.1.2 x hx⟩
    calc blockU K = ⁅blockU K, K⁆ := (C1.commutator_blockU hK).symm
      _ ≤ ⁅omegaOneCenterOf (pCoreOf 2 K), K⁆ := Subgroup.commutator_mono hUA le_rfl

private theorem inf_centralizer_ne_bot_of_alt7 (h : A7PerfectSixCore) (K V : Subgroup G)
    [IsMulCommutative ↥V] (hKV : K ≤ Subgroup.normalizer (V : Set G)) (hcomm : ⁅V, K⁆ = V)
    (hsq : ∀ v ∈ V, v ^ 2 = 1) (hcard : Nat.card V = 64)
    (hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (V : Set G))
    (e : ↥K ⧸ CFSG.pCore 2 ↥K ≃* alternatingGroup (Fin 7)) (X : Subgroup G) (hXK : X ≤ K)
    (hX7 : ¬ 7 ∣ Nat.card X) : V ⊓ Subgroup.centralizer (X : Set G) ≠ ⊥ := by
  have hne : ¬ K ≤ Subgroup.centralizer (V : Set G) := by
    intro h
    have hbot : ⁅V, K⁆ = ⊥ :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mpr (Subgroup.le_centralizer_iff.mpr h)
    rw [hcomm] at hbot
    rw [hbot] at hcard
    simp at hcard
  have : IsSimpleGroup (alternatingGroup (Fin 7)) := alternatingGroup.isSimpleGroup (by simp)
  obtain ⟨eA⟩ := H13.nonempty_autOn_mulEquiv_of_simple hKV hO2 hne e
  have hc' := H13.commV_autOn_eq_top hKV hcomm
  have hsq' : ∀ w : ↥V, w ^ 2 = 1 := fun w => Subtype.ext (hsq w w.2)
  let ρ : alternatingGroup (Fin 7) →* MulAut ↥V :=
    (autOn K V).subtype.comp eA.symm.toMonoidHom
  have hρ : ρ.range = autOn K V := by
    ext a
    constructor
    · rintro ⟨σ, rfl⟩
      exact (eA.symm σ).2
    · intro ha
      exact ⟨eA ⟨a, ha⟩, by simp [ρ]⟩
  obtain ⟨Φ, hΦ⟩ := h ↥V hsq' (by rw [hcard]; norm_num) ρ (by rw [hρ]; exact hc')
  let α : ↥K →* MulAut ↥V := A4.actionOn V K hKV
  have hα : ∀ k : ↥K, α k ∈ autOn K V := fun k => (A4.mem_autOn_iff hKV).2 ⟨k, rfl⟩
  let α' : ↥K →* ↥(autOn K V) := α.codRestrict (autOn K V) hα
  let σ : ↥X →* alternatingGroup (Fin 7) :=
    (eA : ↥(autOn K V) →* alternatingGroup (Fin 7)).comp (α'.comp (Subgroup.inclusion hXK))
  have hY7 : ¬ 7 ∣ Nat.card σ.range := fun h7 => hX7 (h7.trans (Subgroup.card_range_dvd σ))
  obtain ⟨v, hvc, hv1, hvf⟩ := exists_fixed_core_seven σ.range hY7
  let w : ↥V := Φ.symm ⟨v, hvc⟩
  have hw1 : w ≠ 1 := by
    intro hw
    apply hv1
    have : Φ w = Φ 1 := by rw [hw]
    rw [map_one] at this
    simpa [w] using congrArg Subtype.val this
  refine fun hbot => hw1 ?_
  have hmem : (w : G) ∈ V ⊓ Subgroup.centralizer (X : Set G) := by
    refine ⟨w.2, Subgroup.mem_centralizer_iff.mpr fun x hx => ?_⟩
    have hx' : x ∈ K := hXK hx
    set s : alternatingGroup (Fin 7) := σ ⟨x, hx⟩ with hs
    have hsr : s ∈ σ.range := ⟨⟨x, hx⟩, rfl⟩
    have hfix := hvf s hsr
    have hρs : ρ s = α ⟨x, hx'⟩ := by
      have h1 : eA.symm s = α' ⟨x, hx'⟩ := by
        rw [hs]
        show eA.symm (eA (α' (Subgroup.inclusion hXK ⟨x, hx⟩))) = α' ⟨x, hx'⟩
        rw [MulEquiv.symm_apply_apply]
        rfl
      show ((eA.symm s : ↥(autOn K V)) : MulAut ↥V) = α ⟨x, hx'⟩
      rw [h1]
      rfl
    have h1 : Φ (ρ s w) = Φ w := by
      rw [hΦ s w]
      have : Φ w = ⟨v, hvc⟩ := by simp [w]
      rw [this]
      apply Subtype.ext
      exact hfix
    have h2 : ρ s w = w := Φ.injective h1
    rw [hρs] at h2
    have h3 := congrArg Subtype.val h2
    change (x : G) * w * (x : G)⁻¹ = w at h3
    calc (x : G) * w = ((x : G) * w * (x : G)⁻¹) * x := by group
      _ = w * x := by rw [h3]
  rw [hbot] at hmem
  simpa using hmem

end Reduction

end ModB


theorem input14610PermFixedA7_of_core (h : ModB.A7PerfectSixCore) : Input14610PermFixedA7 := by
  intro G _ _ T M H u I I₂ K _ hK hA hW X hXK hX7
  have hblock : IsBlock2 I K := by
    rcases hK.shape with ⟨hL32, -⟩ | ⟨hb, -⟩
    · exfalso
      obtain ⟨e⟩ := hA
      have h1 : Nat.card (OTwoQuot K) = 2520 := by
        rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
        simp [Nat.factorial]
      have h2 : Nat.card (OTwoQuot K) = 168 := ModB.card_eq_168_of_isPSL_three_two hL32
      omega
    · exact hb
  have hshort : IsShort2 K := hblock.1
  rw [ModB.wOf1469_eq_blockU_of_short hshort] at hW ⊢
  have hUQ : blockU K ≤ blockQ K ⊓ Subgroup.centralizer (blockQ K : Set G) := hshort.2.2.1.1
  have hUQ' : blockU K ≤ blockQ K := hUQ.trans inf_le_left
  have hcomm' : ∀ a ∈ blockU K, ∀ b ∈ blockU K, a * b = b * a := fun a ha b hb =>
    ((Subgroup.mem_centralizer_iff.mp (hUQ ha).2) b (hUQ' hb)).symm
  have : IsMulCommutative ↥(blockU K) := ⟨⟨fun a b => Subtype.ext (hcomm' a a.2 b b.2)⟩⟩
  have hO2 : pCoreOf 2 K ≤ Subgroup.centralizer (blockU K : Set G) := fun q hq =>
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      ((Subgroup.mem_centralizer_iff.mp (hUQ hu).2) q hq).symm
  obtain ⟨e⟩ := hA
  exact ModB.inf_centralizer_ne_bot_of_alt7 h K (blockU K) (C1.le_normalizer_blockU K)
    (C1.commutator_blockU hshort) (fun v hv => hshort.2.2.1.2 v hv) (by rw [hW]; norm_num) hO2
    ((QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥K 2)).trans e) X hXK hX7

end CFSG.Quasithin

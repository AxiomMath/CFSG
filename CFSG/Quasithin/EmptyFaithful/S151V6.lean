module

public import CFSG.Quasithin.EmptyFaithful.S151V5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem inf_blockQ_le_blockU {L V : Subgroup G} (hcomm : ∀ a ∈ V, ∀ b ∈ V, a * b = b * a) {c : G}
    (hcL : c ∈ L) (hcV : ∀ a ∈ V, c * a * c⁻¹ ∈ V) (hfpf : ∀ a ∈ V, c * a * c⁻¹ = a → a = 1) :
    V ⊓ blockQ L ≤ blockU L := by
  have hQ : ∀ a ∈ V ⊓ blockQ L, c * a * c⁻¹ ∈ V ⊓ blockQ L := fun a ha =>
    ⟨hcV a ha.1, (Subgroup.mem_normalizer_iff.mp (L_le_normalizer_blockQ L hcL) a).mp ha.2⟩
  have hsurj := (fpf_iff_surj (E := V ⊓ blockQ L) (fun a ha b hb => hcomm a ha.1 b hb.1) hQ).mp
    (fun a ha h => hfpf a ha.1 h)
  intro a ha
  obtain ⟨v, hv, hva⟩ := hsurj a ha
  rw [← hva]
  exact Subgroup.commutator_mem_commutator hv.2 hcL

omit [Finite G] in
theorem inf_blockZ_trivial {L V : Subgroup G} {c : G} (hcL : c ∈ L)
    (hfpf : ∀ a ∈ V, c * a * c⁻¹ = a → a = 1) : ∀ a ∈ V, a ∈ blockZ L → a = 1 :=
  fun a ha haZ => hfpf a ha (s151v_blockZ_comm haZ hcL)

theorem z2_facts (hK : KnownFacts15122Types) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (h15 : Lemma1515Concl T Mc M) (hc : Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L) (hb : IsLnBlock L 3)
    (h7n : ¬ Ce15Seven T Mc M) :
    Z₂ ≤ V₂ ∧ Z₂ ≤ L ∧ Z₂ ≤ blockQ L ∧ IsSylowTwoOf (s1516 T Z₁ ⊓ L) L ∧
      ∀ ℓ ∈ s1516 T Z₁ ⊓ L, ∀ z ∈ Z₂, ℓ * z * ℓ⁻¹ = z := by
  have hS := hc.ctx.setting
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  have hLG : L ≤ g1_1516 Z₁ := le_of_mem_cComp hc.hL.comp
  obtain ⟨hY₀L, hV2Y₀, -, -⟩ := v2_data hK h15 hc hb
  have hsh : IsShort2 L := hb.1
  have hZ₂V₂ : Z₂ ≤ V₂ := hS.z2_le_v2 h7n
  have hdiag := (hS.diagonal hc.small h7n).1
  obtain ⟨-, hMLeq, -, -, -, -⟩ := case15122Two_of_ln3 hK hb hc.h22
  have hsyl : IsSylowTwoOf (s1516 T Z₁ ⊓ L) L :=
    lemma_15_1_20_sylow hc.h18.four (hc.hL.isL1520 hc.h18.four (hS.pCore_g1_ne_bot hq hMf))
  have hSMZ : s1516 T Z₁ ≤ mZ1516 Mc Z₁ := fun x hx =>
    ⟨s1516_le_g1 T Z₁ hx, hq.t_le_mc (s1516_le T Z₁ hx)⟩
  have hBML : s1516 T Z₁ ⊓ L ≤ mZ1516 Mc Z₁ ⊓ L := inf_le_inf_right _ hSMZ
  have hMLZ₂ : ∀ ℓ ∈ mZ1516 Mc Z₁ ⊓ L, ∀ z ∈ Z₂, ℓ * z * ℓ⁻¹ = z := by
    intro ℓ hℓ z hz
    have h1 : ℓ ∈ L ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
      rw [← hMLeq]; exact hℓ
    have h2 : ℓ ∈ g1_1516 Z₁ ⊓ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) :=
      ⟨hLG h1.1, h1.2⟩
    rw [hdiag] at h2
    have := Subgroup.mem_centralizer_iff.mp h2.2 z hz
    rw [← this]; group
  have hZ₂L : Z₂ ≤ L := hZ₂V₂.trans (hV2Y₀.trans hY₀L)
  have hQB : blockQ L ≤ s1516 T Z₁ ⊓ L := pCoreOf_le_of_isSylowTwoOf hsyl
  have hZ₂Q : Z₂ ≤ blockQ L := by
    intro z hz
    have hcen : z ∈ L ⊓ Subgroup.centralizer (pCoreOf 2 L : Set G) := by
      refine ⟨hZ₂L hz, Subgroup.mem_centralizer_iff.mpr fun q hq' => ?_⟩
      have := hMLZ₂ q (hBML (hQB hq')) z hz
      calc q * z = (q * z * q⁻¹) * q := by group
        _ = z * q := by rw [this]
    exact hsh.2.1 hcen
  exact ⟨hZ₂V₂, hZ₂L, hZ₂Q, hsyl, fun ℓ hℓ a ha => hMLZ₂ ℓ (hBML hℓ) a ha⟩

theorem blockV2_six_false (hK : KnownFacts15122Types) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (h15 : Lemma1515Concl T Mc M) (hc : Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L) (hb : IsLnBlock L 3)
    (h6 : Ce15Six T Mc M 3) : False := by
  have hS := hc.ctx.setting
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  obtain ⟨hY₀L, -, hnorm, c, hcY, hfpf⟩ := v2_data hK h15 hc hb
  obtain ⟨e, β, hs⟩ := exists_lnStr hb
  obtain ⟨hZ₂V₂, -, hZ₂Q, hsyl, hfix⟩ := z2_facts hK h15 hc hb h6.not_seven
  have hr := hS.ranks_six ⟨3, Or.inl rfl, h6⟩
  have hcomm : ∀ a ∈ V₂, ∀ b ∈ V₂, a * b = b * a := by
    have hV2ab : IsElemAbelian 2 V₂ := isElemAbelian_mono151 hS.v2_le (hS.V_isElemAbelian hq hMf)
    intro a ha b hb'
    have := hV2ab.1
    have h1 := mul_comm' (⟨a, ha⟩ : V₂) ⟨b, hb'⟩
    exact congrArg (fun z : V₂ => (z : G)) h1
  have hcL : c ∈ L := hY₀L hcY
  have hU := inf_blockQ_le_blockU hcomm hcL (hnorm c hcY) hfpf
  have hZ₂U : Z₂ ≤ blockU L := fun z hz => hU ⟨hZ₂V₂ hz, hZ₂Q hz⟩
  have hZ := inf_blockZ_trivial (L := L) hcL hfpf
  refine local_contra_six hs hsyl hZ₂U (fun a ha haZ => hZ a (hZ₂V₂ ha) haZ) ?_ hfix
  have h4 : Nat.card Z₂ = 4 := (hr.2.2 (Or.inr (Or.inl h6))).2
  omega

theorem blockV2_seven_false (hK : KnownFacts15122Types) {T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G}
    (h15 : Lemma1515Concl T Mc M) (hc : Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L) (hb : IsLnBlock L 3)
    (h7 : Ce15Seven T Mc M) (hV2Q : V₂ ≤ pCoreOf 2 L) : False := by
  have hS := hc.ctx.setting
  have hq := hc.ctx.qtfe
  have hMf := hc.ctx.mf
  obtain ⟨hY₀L, -, hnorm, c, hcY, hfpf⟩ := v2_data hK h15 hc hb
  obtain ⟨e, β, hs⟩ := exists_lnStr hb
  have hcomm : ∀ a ∈ V₂, ∀ b ∈ V₂, a * b = b * a := by
    have hV2ab : IsElemAbelian 2 V₂ := isElemAbelian_mono151 hS.v2_le (hS.V_isElemAbelian hq hMf)
    intro a ha b hb'
    have := hV2ab.1
    have h1 := mul_comm' (⟨a, ha⟩ : V₂) ⟨b, hb'⟩
    exact congrArg (fun z : V₂ => (z : G)) h1
  have hcL : c ∈ L := hY₀L hcY
  have hU := inf_blockQ_le_blockU hcomm hcL (hnorm c hcY) hfpf
  have hV2U : V₂ ≤ blockU L := fun a ha => hU ⟨ha, hV2Q ha⟩
  have h8 := local_card_le_eight hs hV2U (inf_blockZ_trivial (L := L) hcL hfpf)
  have h16 := (hS.ranks_seven h7).2.2.1
  omega

@[expose] def Input15124SevenV2InQ : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T Mc M Z₁ Z₂ V₁ V₂ L : Subgroup G),
    Ctx15124 T Mc M Z₁ Z₂ V₁ V₂ L → Ce15Seven T Mc M → IsLnBlock L 3 → V₂ ≤ pCoreOf 2 L

theorem input15124BlockV2_of (hK : KnownFacts15122Types) (h15 : StageLemma1515CE)
    (r7 : Input15124SevenV2InQ) : Input15124BlockV2 := by
  intro G _ _ T Mc M Z₁ Z₂ V₁ V₂ L hc hb
  have hL15 : Lemma1515Concl T Mc M := h15 G T Mc M hc.ctx.qtfe hc.ctx.mf hc.ctx.ce
  rcases hc.small with h4 | h6 | h7
  · exact (hc.ctx.setting.ranks_four h4).2.1
  · exact (blockV2_six_false hK hL15 hc hb h6).elim
  · exact (blockV2_seven_false hK hL15 hc hb h7 (r7 G T Mc M Z₁ Z₂ V₁ V₂ L hc h7 hb)).elim

end CFSG.Quasithin

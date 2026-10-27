module

public import CFSG.Quasithin.Background.C126A5Lift7
public import CFSG.Quasithin.Background.F1Models

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C126.A5

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 Equiv
  CFSG.LieType.BorelTits

open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem blockU_le_blockQ_gen (K : Subgroup G) : blockU K ≤ blockQ K := by
  unfold blockU
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h := (Subgroup.mem_normalizer_iff.1 (le_normalizer_pCoreOf 2 K hb) a⁻¹).1
    ((blockQ K).inv_mem ha)
  have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
  rw [e]
  exact (blockQ K).mul_mem ha h

namespace Lift

variable {H T M V Y : Subgroup G} {hV : IsElemAbelian 2 V} {s : Setting H T M V Y hV}
  {d : Data H T V Y hV}

namespace XData

variable {x : G} (hx : XData s d x)

include hx

theorem eq_top_of_isPGroup_quotient (N : Subgroup ↥(Khat s d x)) [N.Normal]
    (hN : IsPGroup 2 (↥(Khat s d x) ⧸ N)) : N = ⊤ := by
  have h3 : ∀ k : ↥(Khat s d x), k ^ 3 = 1 → k ∈ N := by
    intro k hk
    have h1 : (QuotientGroup.mk k : ↥(Khat s d x) ⧸ N) ^ 3 = 1 := by
      rw [← QuotientGroup.mk_pow, hk, QuotientGroup.mk_one]
    obtain ⟨m, hm⟩ := hN (QuotientGroup.mk k)
    exact (QuotientGroup.eq_one_iff k).1 (eq_one_of_pow_three h1 hm)
  have hK : Khat s d x ≤ N.map (Khat s d x).subtype := by
    refine conjClosure_le fun a ha z hz => ?_
    have hmem : a * z * a⁻¹ ∈ Khat s d x := mem_conjClosure ha hz
    refine ⟨⟨_, hmem⟩, h3 _ (Subtype.ext ?_), rfl⟩
    have hz3 : z ^ 3 = 1 :=
      orderOf_dvd_iff_pow_eq_one.1 (hx.ord ▸ orderOf_dvd_of_mem_zpowers hz)
    simp [conj_pow, hz3]
  rw [eq_top_iff]
  intro k _
  obtain ⟨n, hn, hnk⟩ := hK k.2
  have : n = k := Subtype.ext hnk
  rwa [← this]

variable (hY : IsShort2 Y) (hA3 : IsAltType Y 3)

include hY hA3

theorem clause3 : blockU (Khat s d x) ≤ blockQ (Khat s d x) ⊓
      Subgroup.centralizer (blockQ (Khat s d x) : Set G) ∧
    ∀ y ∈ blockU (Khat s d x), y ^ 2 = 1 := by
  have hU := hx.blockU_eq_Vc hY hA3
  refine ⟨le_inf (blockU_le_blockQ_gen _) ?_, fun y hy => ?_⟩
  · intro u hu
    rw [Subgroup.mem_centralizer_iff]
    intro q hq
    have hq' : q ∈ pCoreOf 2 (Khat s d x) := hq
    have hqQ : q ∈ pCoreOf 2 H := (hx.pCoreOf_Khat ▸ hq').2
    have huV : u ∈ V := Vc_le_V (hU ▸ hu)
    exact (Subgroup.mem_centralizer_iff.1 (s.Q_le_C hqQ) u huV).symm
  · have hyV : y ∈ V := Vc_le_V (hU ▸ hy)
    exact hV.2 y hyV

theorem clause5 : blockZ (Khat s d x) < blockU (Khat s d x) ∧
    ∀ W : Subgroup G, blockZ (Khat s d x) ≤ W → W ≤ blockU (Khat s d x) →
      Khat s d x ≤ Subgroup.normalizer (W : Set G) →
      W = blockZ (Khat s d x) ∨ W = blockU (Khat s d x) := by
  refine ⟨?_, fun W _ hWU hN => ?_⟩
  · rw [hx.blockZ_eq_bot hY hA3]
    exact bot_lt_iff_ne_bot.2 (hx.blockU_ne_bot hY hA3)
  · have hW : W ≤ Vc d := (hx.blockU_eq_Vc hY hA3) ▸ hWU
    rcases hx.irred_Vc hW hN with h | h
    · left; rw [h, hx.blockZ_eq_bot hY hA3]
    · right; rw [h, hx.blockU_eq_Vc hY hA3]

theorem isShort2 (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    IsShort2 (Khat s d x) := by
  refine ⟨fun N _ hN => hx.eq_top_of_isPGroup_quotient N hN, hx.charTwo_Khat,
    hx.clause3 hY hA3, Or.inl ?_, hx.clause5 hY hA3⟩
  have e : ↥(Khat s d x) ⧸ CFSG.pCore 2 ↥(Khat s d x) ≃* ↥(alternatingGroup (Fin 5)) :=
    (QuotientGroup.quotientMulEquivOfEq (hx.alpha_ker hRad).symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective hx.alpha hx.alpha_surj)
  exact isQuasisimple_of_alt_five e

theorem isBlock2 (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    IsBlock2 H (Khat s d x) :=
  ⟨hx.isShort2 hY hA3 hRad, hx.Khat_le_H, hx.Khat_subgroupOf_isSubnormal⟩

theorem isChi0Block (hRad : twoResidual H ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 H) :
    IsChi0Block H (Khat s d x) :=
  ⟨hx.isBlock2 hY hA3 hRad, Or.inr (Or.inr (hx.isAltType_five hY hA3 hRad))⟩

end XData

end Lift

end CFSG.Quasithin.C126.A5

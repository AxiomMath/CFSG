module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC11E3ParaB
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.LinearPilotQ2LFiveKBasic
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs.L3YC

abbrev GL32 : Type := GL (Fin 3) (ZMod 2)

private theorem map_conj_symm (φ : MulAut GL32) (S : Subgroup GL32) :
    (S.map φ.toMonoidHom).map φ.symm.toMonoidHom = S := by
  rw [Subgroup.map_map]
  have hcomp : φ.symm.toMonoidHom.comp φ.toMonoidHom = MonoidHom.id GL32 := by
    ext x; simp
  rw [hcomp, Subgroup.map_id]

private theorem map_symm_conj (φ : MulAut GL32) (S : Subgroup GL32) :
    (S.map φ.symm.toMonoidHom).map φ.toMonoidHom = S := by
  rw [Subgroup.map_map]
  have hcomp : φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id GL32 := by
    ext x; simp
  rw [hcomp, Subgroup.map_id]

private theorem gl32_conj_of_card_eight (T : Subgroup GL32) (hT : Nat.card ↥T = 8) :
    ∃ c : GL32, U3.map (MulAut.conj c).toMonoidHom = T := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hT2 : IsPGroup 2 T := IsPGroup.of_card (n := 3) (by rw [hT]; norm_num)
  have hTidx : ¬ 2 ∣ T.index := by
    have h := T.card_mul_index
    rw [hT, card_GL_three_two] at h
    have : T.index = 21 := by omega
    rw [this]; norm_num
  have hU3idx : ¬ 2 ∣ U3.index := by
    have h := U3.card_mul_index
    rw [card_U3, card_GL_three_two] at h
    have : U3.index = 21 := by omega
    rw [this]; norm_num
  let Us : Sylow 2 GL32 :=
    (IsPGroup.of_card (n := 3)
      (show Nat.card ↥U3 = 2 ^ 3 by rw [card_U3]; norm_num)).toSylow hU3idx
  let Ts : Sylow 2 GL32 := hT2.toSylow hTidx
  obtain ⟨c, hc⟩ := MulAction.exists_smul_eq GL32 Us Ts
  refine ⟨c, ?_⟩
  have hcoe : ((c • Us : Sylow 2 GL32) : Subgroup GL32) = (Ts : Subgroup GL32) :=
    congrArg (fun P : Sylow 2 GL32 => (P : Subgroup GL32)) hc
  rw [Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def] at hcoe
  dsimp only [Us, Ts] at hcoe
  rw [IsPGroup.toSylow_coe, IsPGroup.toSylow_coe] at hcoe
  exact hcoe

private theorem stabPoint_ne_stabPlane : stabPoint ≠ stabPlane := by
  intro hp
  have hinf : U3 = stabPoint := by
    rw [← stabPoint_inf_stabPlane]
    exact inf_eq_left.mpr hp.le
  have hcard := card_U3
  rw [hinf, card_stabPoint] at hcard
  norm_num at hcard

private theorem gl32_two_parabolics (T : Subgroup GL32) (hT : Nat.card ↥T = 8) :
    ∃ P₁ P₂ : Subgroup GL32, T ≤ P₁ ∧ T ≤ P₂ ∧ Nat.card ↥P₁ = 24 ∧ Nat.card ↥P₂ = 24 ∧
      P₁ ≠ P₂ ∧ P₁ ⊓ P₂ = T ∧
      ∀ Q : Subgroup GL32, T ≤ Q → Nat.card ↥Q = 24 → Q = P₁ ∨ Q = P₂ := by
  obtain ⟨c, hc⟩ := gl32_conj_of_card_eight T hT
  let φ : MulAut GL32 := MulAut.conj c
  have hcφ : U3.map φ.toMonoidHom = T := hc
  refine ⟨stabPoint.map φ.toMonoidHom, stabPlane.map φ.toMonoidHom,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hcφ]; exact Subgroup.map_mono U3_le_stabs.1
  · rw [← hcφ]; exact Subgroup.map_mono U3_le_stabs.2
  · rw [Subgroup.card_map_of_injective φ.injective, card_stabPoint]
  · rw [Subgroup.card_map_of_injective φ.injective, card_stabPlane]
  · intro h
    exact stabPoint_ne_stabPlane (by
      have := congrArg (Subgroup.map φ.symm.toMonoidHom) h
      rwa [map_conj_symm, map_conj_symm] at this)
  · rw [← hcφ, ← Subgroup.map_inf stabPoint stabPlane φ.toMonoidHom φ.injective,
      stabPoint_inf_stabPlane]
  · intro Q hTQ hQ
    have hQ' : Nat.card ↥(Q.map φ.symm.toMonoidHom) = 24 := by
      rw [Subgroup.card_map_of_injective φ.symm.injective, hQ]
    have hUQ' : U3 ≤ Q.map φ.symm.toMonoidHom := by
      have := Subgroup.map_mono hTQ (f := φ.symm.toMonoidHom)
      rwa [← hcφ, map_conj_symm] at this
    rcases (overgroups_U3 (Q.map φ.symm.toMonoidHom) hUQ') with h | h | h | h
    · exfalso
      rw [h, card_U3] at hQ'
      norm_num at hQ'
    · left
      have := congrArg (Subgroup.map φ.toMonoidHom) h
      rwa [map_symm_conj] at this
    · right
      have := congrArg (Subgroup.map φ.toMonoidHom) h
      rwa [map_symm_conj] at this
    · exfalso
      have htop : Nat.card ↥(⊤ : Subgroup GL32) = 168 := by
        rw [Nat.card_congr
          (Subgroup.topEquiv : ↥(⊤ : Subgroup GL32) ≃* GL32).toEquiv, card_GL_three_two]
      rw [h, htop] at hQ'
      norm_num at hQ'

private theorem map_equiv_symm_self {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (S : Subgroup G) : (S.map e.toMonoidHom).map e.symm.toMonoidHom = S := by
  rw [Subgroup.map_map]
  have hcomp : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext x; simp
  rw [hcomp, Subgroup.map_id]

private theorem map_equiv_self_symm {G H : Type} [Group G] [Group H] (e : G ≃* H)
    (S : Subgroup H) : (S.map e.symm.toMonoidHom).map e.toMonoidHom = S := by
  rw [Subgroup.map_map]
  have hcomp : e.toMonoidHom.comp e.symm.toMonoidHom = MonoidHom.id H := by ext x; simp
  rw [hcomp, Subgroup.map_id]

theorem s1611e3_l3_two_parabolics {L : Type} [Group L] [Finite L] (hL : IsL3 L 1)
    {T₁ : Subgroup L} (hT₁ : Nat.card ↥T₁ = 8) :
    ∃ P₁ P₂ : Subgroup L, T₁ ≤ P₁ ∧ T₁ ≤ P₂ ∧ Nat.card ↥P₁ = 24 ∧ Nat.card ↥P₂ = 24 ∧
      P₁ ≠ P₂ ∧ P₁ ⊓ P₂ = T₁ ∧
      ∀ Q : Subgroup L, T₁ ≤ Q → Nat.card ↥Q = 24 → Q = P₁ ∨ Q = P₂ := by
  obtain ⟨e⟩ := CFSG.SeitzReduction.LinearPilot.nonempty_equiv_GL32_of_lieModel hL
  let T : Subgroup GL32 := T₁.map e.toMonoidHom
  have hcardT : Nat.card ↥T = 8 := by
    rw [Subgroup.card_map_of_injective e.injective, hT₁]
  obtain ⟨P₁, P₂, hTP₁, hTP₂, hc₁, hc₂, hne, hinf, huniq⟩ := gl32_two_parabolics T hcardT
  refine ⟨P₁.map e.symm.toMonoidHom, P₂.map e.symm.toMonoidHom,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← map_equiv_symm_self e T₁]
    exact Subgroup.map_mono hTP₁
  · rw [← map_equiv_symm_self e T₁]
    exact Subgroup.map_mono hTP₂
  · rw [Subgroup.card_map_of_injective e.symm.injective, hc₁]
  · rw [Subgroup.card_map_of_injective e.symm.injective, hc₂]
  · intro h
    exact hne (by
      have := congrArg (Subgroup.map e.toMonoidHom) h
      rwa [map_equiv_self_symm e P₁, map_equiv_self_symm e P₂] at this)
  · rw [← map_equiv_symm_self e T₁,
      ← Subgroup.map_inf P₁ P₂ e.symm.toMonoidHom e.symm.injective, hinf]
  · intro Q hTQ hQ
    have hQ' : Nat.card ↥(Q.map e.toMonoidHom) = 24 := by
      rw [Subgroup.card_map_of_injective e.injective, hQ]
    have hTQ' : T ≤ Q.map e.toMonoidHom := Subgroup.map_mono hTQ
    rcases huniq (Q.map e.toMonoidHom) hTQ' hQ' with h | h
    · left
      have := congrArg (Subgroup.map e.symm.toMonoidHom) h
      rwa [map_equiv_symm_self e Q] at this
    · right
      have := congrArg (Subgroup.map e.symm.toMonoidHom) h
      rwa [map_equiv_symm_self e Q] at this

theorem s1611e3_natural_stab {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)}
    (hL : IsL3 ↥L 1) {I : Subgroup W} (hI : BinaryNaturalSL L I ⊥ 3 1)
    {T₁ : Subgroup (MulAut W)} (hT₁L : T₁ ≤ L) (hT₁ : IsSylowIn 2 T₁ L) :
    Nat.card ↥(I ⊓ fixV T₁) = 2 ∧
      ∀ w ∈ I, w ≠ 1 → Nat.card ↥(L ⊓ centSub (Subgroup.zpowers w)) = 24 := by
  obtain ⟨K, hKfield, hKfin, hKcard, π₀, hπ₀⟩ := hI
  let π : ↥(StatedSL 3 K) →* ↥L := π₀
  have hπ : (FFModel.nat (StatedSL 3 K)).RealizesVia L I ⊥ π := hπ₀
  have hK : Nat.card K = 2 := by rw [hKcard]; norm_num
  exact ⟨s1611e3_transport_fix hK hπ hT₁L hT₁, s1611e3_transport_stab hK hπ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

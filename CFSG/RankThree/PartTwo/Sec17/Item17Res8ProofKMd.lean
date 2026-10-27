module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.Sporadic.ON
public import CFSG.RankThree.PartTwo.Sec17.Item17Setup

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] noncomputable def Claim143LdThree : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → omegaA A = {Subgroup.zpowers c} →
    Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2) →
    ∀ d ∈ A, d ≠ 1 → IsThreeCentralIn L d →
    ∀ K ∈ thetaComponentsAt 3 d,
      K ≤ delta A (lB A) (Subgroup.centralizer ({d} : Set G)) →
        K ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({d} : Set G)) ∨
          inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K

namespace Proof17Res8

section Types

theorem card_subgroupOf_dvd {X : Type*} [Group X] (H K : Subgroup X) :
    Nat.card (H.subgroupOf K) ∣ Nat.card H := by
  rw [← Subgroup.inf_subgroupOf_right,
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right : H ⊓ K ≤ K)).toEquiv]
  exact Subgroup.card_dvd_of_le inf_le_left

theorem eq_bot_of_isTripleCover {Q : Type*} [Group Q] [Finite Q] {T : Type*} [Group T]
    [IsSimpleGroup T] (h3 : 3 ∣ Nat.card T) (hQ : Sec4.IsTripleCover Q T) (N : Subgroup Q)
    [hN : N.Normal] (hN3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  obtain ⟨hZ3, ⟨e⟩⟩ := hQ
  set f : Q →* T := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q)) with hf
  have hfs : Function.Surjective f :=
    e.surjective.comp (QuotientGroup.mk'_surjective (Subgroup.center Q))
  have hNf : (N.map f).Normal := hN.map f hfs
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.map f) with h | h
  · have hNZ : N ≤ Subgroup.center Q := by
      intro n hn
      have h1 : f n ∈ N.map f := Subgroup.mem_map_of_mem f hn
      rw [h, Subgroup.mem_bot, hf, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
        MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      exact h1
    have hd : Nat.card N ∣ 3 := hZ3 ▸ Subgroup.card_dvd_of_le hNZ
    rcases (Nat.dvd_prime Nat.prime_three).mp hd with h1 | h1
    · exact Subgroup.eq_bot_of_card_eq N h1
    · exact absurd (by rw [h1]) hN3
  · have hd := Subgroup.card_map_dvd N f
    rw [h, Subgroup.card_top] at hd
    exact absurd (h3.trans hd) hN3

theorem three_dvd_card_alternatingGroup_six : 3 ∣ Nat.card (alternatingGroup (Fin 6)) := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem eq_bot_of_isCentralProductA6Covers {Q : Type*} [Group Q] [Finite Q]
    (hQ : IsCentralProductA6Covers Q) (N : Subgroup Q) [hN : N.Normal]
    (hN3 : ¬ 3 ∣ Nat.card N) : N = ⊥ := by
  obtain ⟨U, V, hUn, hVn, hUV, hcomm, hUV3, hUt, hVt⟩ := hQ
  have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
  have hmeet : ∀ W : Subgroup Q, W.Normal →
      Sec4.IsTripleCover ↥W (alternatingGroup (Fin 6)) → N ⊓ W = ⊥ := by
    intro W hWn hWt
    have hNW : (N.subgroupOf W).Normal := Subgroup.Normal.subgroupOf hN W
    have hNW3 : ¬ 3 ∣ Nat.card (N.subgroupOf W) := fun h =>
      hN3 (h.trans (card_subgroupOf_dvd N W))
    have h1 := eq_bot_of_isTripleCover three_dvd_card_alternatingGroup_six hWt
      (N.subgroupOf W) hNW3
    rw [eq_bot_iff]
    intro x hx
    have : (⟨x, hx.2⟩ : ↥W) ∈ N.subgroupOf W := Subgroup.mem_subgroupOf.mpr hx.1
    rw [h1, Subgroup.mem_bot] at this
    exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
  have hNU := hmeet U hUn hUt
  have hNV := hmeet V hVn hVt
  have hNVc : N ≤ Subgroup.centralizer (V : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (le_bot_iff.mp (hNV ▸ Subgroup.commutator_le_inf N V))
  have hUVc : U ≤ Subgroup.centralizer (V : Set Q) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hZV : ∀ v ∈ V, (∀ w ∈ V, w * v = v * w) → v ∈ U := by
    set ZV : Subgroup Q := (Subgroup.center ↥V).map V.subtype with hZVdef
    have hUVZ : U ⊓ V ≤ ZV := by
      intro x hx
      refine ⟨⟨x, hx.2⟩, Subgroup.mem_center_iff.mpr fun w => Subtype.ext ?_, rfl⟩
      exact Subgroup.mem_centralizer_iff.mp (hUVc hx.1) w w.2
    have hcardZV : Nat.card ZV = 3 := by
      rw [hZVdef, Subgroup.card_map_of_injective V.subtype_injective]
      exact hVt.1
    have heq : U ⊓ V = ZV := Subgroup.eq_of_le_of_card_ge hUVZ (by rw [hcardZV, hUV3])
    intro v hv hvc
    have hvZ : v ∈ ZV :=
      ⟨⟨v, hv⟩, Subgroup.mem_center_iff.mpr fun w => Subtype.ext (hvc w w.2), rfl⟩
    rw [← heq] at hvZ
    exact hvZ.1
  rw [eq_bot_iff, ← hNU]
  intro n hn
  have hnUV : n ∈ ((U ⊔ V : Subgroup Q) : Set Q) := by rw [hUV]; exact Subgroup.mem_top n
  rw [Subgroup.normal_mul] at hnUV
  obtain ⟨u, hu, v, hv, rfl⟩ := hnUV
  refine ⟨hn, mul_mem hu (hZV v hv fun w hw => ?_)⟩
  have h1 : w * (u * v) = (u * v) * w := Subgroup.mem_centralizer_iff.mp (hNVc hn) w hw
  have h2 : w * u = u * w := Subgroup.mem_centralizer_iff.mp (hUVc hu) w hw
  calc w * v = u⁻¹ * (u * w) * v := by group
    _ = u⁻¹ * (w * u) * v := by rw [h2]
    _ = u⁻¹ * (w * (u * v)) := by group
    _ = u⁻¹ * ((u * v) * w) := by rw [h1]
    _ = v * w := by group

theorem le_theta_of_normal_of_types {X : Type*} [Group X]
    [Finite X]
    (htypes : Sec4.IsTripleCover (X ⧸ aschbacherSolvableCore 3 X)
        CFSG.Blueprint.NativeSporadic.ON ∨
      Sec4.IsTripleCover (X ⧸ aschbacherSolvableCore 3 X) (alternatingGroup (Fin 6)) ∨
      IsCentralProductA6Covers (X ⧸ aschbacherSolvableCore 3 X))
    (N : Subgroup X) [hN : N.Normal] (hN3 : ¬ 3 ∣ Nat.card N) :
    N ≤ aschbacherSolvableCore 3 X := by
  set θ := aschbacherSolvableCore 3 X with hθ
  set f := QuotientGroup.mk' θ with hf
  have hNf : (N.map f).Normal := hN.map f (QuotientGroup.mk'_surjective θ)
  have hNf3 : ¬ 3 ∣ Nat.card (N.map f) := fun h => hN3 (h.trans (Subgroup.card_map_dvd N f))
  have hbot : N.map f = ⊥ := by
    rcases htypes with hT | hT | hT
    · have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
      exact eq_bot_of_isTripleCover (by rw [CFSG.Sporadic.ON.card_ON]; norm_num) hT _ hNf3
    · have : IsSimpleGroup (alternatingGroup (Fin 6)) := alternatingGroup.isSimpleGroup (by simp)
      exact eq_bot_of_isTripleCover three_dvd_card_alternatingGroup_six hT _ hNf3
    · exact eq_bot_of_isCentralProductA6Covers hT _ hNf3
  intro n hn
  have h1 : f n ∈ N.map f := Subgroup.mem_map_of_mem f hn
  rw [hbot, Subgroup.mem_bot, hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
  exact h1

end Types

end Proof17Res8

end CFSG.RankThree.PartTwo.Sec17

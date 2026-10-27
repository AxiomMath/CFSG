module

public import CFSG.StronglyEmbedded.BenderCentre
import CFSG.StronglyEmbedded.BenderU3Generation
import CFSG.GH74.Uniqueness.Bender.Core
import CFSG.Goldschmidt.Steps.G3aBorel
import CFSG.Timmesfeld.Bridge.Asc72Bender
import CFSG.Models.BenderSuzuki

public section

namespace CFSG.StronglyEmbedded.BenderCentre

open CFSG.BenderSuzuki
open CFSG.GH74.Uniqueness.Bender (conj_mem_rootCenter mem_sylow_smul_iff)
open CFSG.Open (pCoreOf)
open CFSG.Timmesfeld.Bridge.Asc72
open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter mem_sylowCenter
  sylowCenter_le)

variable {K : Type} [Group K] [Finite K]

section Normalizer

theorem mul_self_eq_one_of_mem_sylowCenter (hK : IsBenderGroup K) (S : Sylow 2 K) {z : K}
    (hz : z ∈ sylowCenter (S : Subgroup K)) : z * z = 1 :=
  IsBenderGroup.mul_self_eq_one_of_commute hK S (sylowCenter_le _ hz) fun y hy =>
    ((mem_sylowCenter.mp hz).2 y hy).symm

theorem four_le_card_sylowCenter (hK : IsBenderGroup K) (S : Sylow 2 K) :
    4 ≤ Nat.card (sylowCenter (S : Subgroup K)) := by
  rw [← map_center_eq S, Subgroup.card_map_of_injective (Subgroup.subtype_injective _)]
  exact IsBenderGroup.four_le_card_center hK S

theorem sylowCenter_ne_bot (hK : IsBenderGroup K) (S : Sylow 2 K) :
    sylowCenter (S : Subgroup K) ≠ ⊥ := by
  intro h
  have h4 := four_le_card_sylowCenter hK S
  rw [h, Subgroup.card_bot] at h4
  omega

theorem normalizer_sylowCenter_eq (hK : IsBenderGroup K) (S : Sylow 2 K) :
    Subgroup.normalizer (sylowCenter (S : Subgroup K) : Set K) =
      Subgroup.normalizer ((S : Subgroup K) : Set K) := by
  apply le_antisymm
  · intro n hn
    have hle : sylowCenter (S : Subgroup K) ≤ ((n • S : Sylow 2 K) : Subgroup K) := by
      intro z hz
      rw [mem_sylow_smul_iff]
      have h1 := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hn) z).mp hz
      rw [inv_inv] at h1
      exact sylowCenter_le _ h1
    have hS := sylow_eq_of_le_sylowCenter hK (sylowCenter_ne_bot hK S) le_rfl
      (le_sylowCenter_of_sq_eq_one hK hle fun z hz => mul_self_eq_one_of_mem_sylowCenter hK S hz)
    exact Sylow.smul_eq_iff_mem_normalizer.mp hS.symm
  · intro n hn
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · exact fun hz => conj_mem_rootCenter hn hz
    · intro hz
      have h1 := conj_mem_rootCenter (Subgroup.inv_mem _ hn) hz
      have e : n⁻¹ * (n * z * n⁻¹) * n⁻¹⁻¹ = z := by group
      rwa [e] at h1

theorem pCoreOf_normalizer_sylow (S : Sylow 2 K) :
    pCoreOf 2 (Subgroup.normalizer ((S : Subgroup K) : Set K)) = (S : Subgroup K) := by
  set N := Subgroup.normalizer ((S : Subgroup K) : Set K) with hN
  have hSN : (S : Subgroup K) ≤ N := Subgroup.le_normalizer
  apply le_antisymm
  · have hQ : IsPGroup 2 (pCoreOf 2 N) :=
      (CFSG.pCore_isPGroup (p := 2) (G := ↥N)).map N.subtype
    have hQN : pCoreOf 2 N ≤ N := Subgroup.map_subtype_le _
    have h1 : pCoreOf 2 N ≤ pCoreOf 2 N ⊓ (S : Subgroup K) := by
      rw [← hQ.inf_normalizer_sylow S]
      exact le_inf le_rfl hQN
    exact h1.trans inf_le_right
  · have hnorm : ((S : Subgroup K).subgroupOf N).Normal :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hSN).mpr le_rfl
    have hp : IsPGroup 2 ((S : Subgroup K).subgroupOf N) :=
      S.isPGroup'.of_equiv (Subgroup.subgroupOfEquivOfLe hSN).symm
    have hcore : (S : Subgroup K).subgroupOf N ≤ CFSG.pCore 2 ↥N := by
      rw [CFSG.pCore_eq_iSup]
      exact le_iSup_of_le _ (le_iSup_of_le hnorm (le_iSup_of_le hp le_rfl))
    rw [← Subgroup.map_subgroupOf_eq_of_le hSN]
    exact Subgroup.map_mono hcore

theorem benderRoot_pCoreOf_normalizer {A : Subgroup K} {S : Sylow 2 K} (hK : IsBenderGroup K)
    (hS : sylowCenter (S : Subgroup K) = A) :
    Subgroup.normalizer (A : Set K) = Subgroup.normalizer ((S : Subgroup K) : Set K) ∧
      pCoreOf 2 (Subgroup.normalizer (A : Set K)) = (S : Subgroup K) := by
  subst hS
  have h := normalizer_sylowCenter_eq hK S
  exact ⟨h, by rw [h]; exact pCoreOf_normalizer_sylow S⟩

end Normalizer

section Irreducible

theorem eq_sylowCenter_or_eq_of_normalized
    (hK : IsBenderGroup K) (S : Sylow 2 K) {W : Subgroup K}
    (hZW : sylowCenter (S : Subgroup K) ≤ W) (hWS : W ≤ (S : Subgroup K))
    (hW : ∀ b ∈ Subgroup.normalizer ((S : Subgroup K) : Set K), ∀ w ∈ W, b * w * b⁻¹ ∈ W) :
    W = sylowCenter (S : Subgroup K) ∨ W = (S : Subgroup K) := by
  obtain ⟨D, hD⟩ :=
    CFSG.Goldschmidt.G3a.exists_borelSetup (fusionIsBenderGroup_of_isBenderGroup hK) S
  have hDW : D ≤ Subgroup.normalizer (W : Set K) := fun d hd => by
    have hdN := hD.le hd
    rw [Subgroup.mem_normalizer_iff]
    intro w
    refine ⟨hW d hdN w, fun h => ?_⟩
    have h1 := hW d⁻¹ (Subgroup.inv_mem _ hdN) _ h
    have e : d⁻¹ * (d * w * d⁻¹) * d⁻¹⁻¹ = w := by group
    rwa [e] at h1
  rcases hK with ⟨n, hn, e⟩ | ⟨a, ha, e⟩ | ⟨n, hn, e⟩
  · exact Or.inr (le_antisymm hWS ((sylowCenter_eq_of_psl2 hn e S).symm.le.trans hZW))
  · let e' : K ≃* CFSG.Open.Sz a :=
      e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderSzModel_eq_sz a))
    obtain ⟨hZc, hSc, hDc⟩ := hD.orders_sz ha e'
    exact hD.eq_or_eq_of_invariant (Or.inl ⟨by rw [hSc, hZc], by rw [hDc, hZc]⟩) hZW hWS hDW
  · let e' : K ≃* CFSG.Open.PSU3 2 n :=
      e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 n))
    obtain ⟨hZc, hSc, hDc⟩ := hD.orders_psu3 hn e'
    exact hD.eq_or_eq_of_invariant (Or.inr ⟨by rw [hSc, hZc], by rw [hDc, hZc]⟩) hZW hWS hDW

end Irreducible

section Automorphisms

theorem eq_conj_sylow (hK : IsBenderGroup K) (S : Sylow 2 K)
    (α : MulAut K) (hα : ∀ z ∈ sylowCenter (S : Subgroup K), α z = z)
    (hS : ∀ b ∈ (S : Subgroup K), b⁻¹ * α b ∈ sylowCenter (S : Subgroup K)) :
    ∃ s ∈ (S : Subgroup K), α = MulAut.conj s := by
  refine aut_eq_conj_of_centralizes hK S α (fun s hs => ?_) hα hS
  have e : α s = s * (s⁻¹ * α s) := by group
  rw [e]
  exact Subgroup.mul_mem _ hs (sylowCenter_le _ (hS s hs))

theorem eq_conj_sylowCenter
    (hK : IsBenderGroup K) (S : Sylow 2 K) (α : MulAut K)
    (hα : ∀ z ∈ sylowCenter (S : Subgroup K), α z = z)
    (hN : ∀ b ∈ Subgroup.normalizer ((S : Subgroup K) : Set K),
      b⁻¹ * α b ∈ sylowCenter (S : Subgroup K)) :
    ∃ s ∈ sylowCenter (S : Subgroup K), α = MulAut.conj s := by
  have hSN : (S : Subgroup K) ≤ Subgroup.normalizer ((S : Subgroup K) : Set K) :=
    Subgroup.le_normalizer
  obtain ⟨s, hs, rfl⟩ := eq_conj_sylow hK S α hα fun b hb => hN b (hSN hb)
  refine ⟨s, ?_, rfl⟩
  set Z := sylowCenter (S : Subgroup K) with hZ
  set W := Subgroup.zpowers s ⊔ Z with hW
  have hZW : Z ≤ W := le_sup_right
  have hsW : s ∈ W := Subgroup.mem_sup_left (Subgroup.mem_zpowers s)
  have hWS : W ≤ (S : Subgroup K) := sup_le (Subgroup.zpowers_le.mpr hs) (sylowCenter_le _)
  have hWs : W ≤ Subgroup.centralizer ({s} : Set K) := by
    refine sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)) ?_
    intro z hz
    exact Subgroup.mem_centralizer_singleton_iff.mpr ((mem_sylowCenter.mp hz).2 s hs).symm
  have hinv : ∀ b ∈ Subgroup.normalizer ((S : Subgroup K) : Set K), ∀ w ∈ W,
      b * w * b⁻¹ ∈ W := by
    intro b hb
    have hle : W ≤ W.comap (MulAut.conj b).toMonoidHom := by
      refine sup_le (Subgroup.zpowers_le.mpr ?_) ?_
      · rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        have h1 := hN b⁻¹ (Subgroup.inv_mem _ hb)
        rw [MulAut.conj_apply, inv_inv] at h1
        have e : b * s * b⁻¹ = b * (s * b⁻¹ * s⁻¹) * s := by group
        rw [e]
        exact Subgroup.mul_mem _ (hZW h1) hsW
      · intro z hz
        rw [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        exact hZW (conj_mem_rootCenter hb hz)
    intro w hw
    have h1 := hle hw
    rwa [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at h1
  rcases eq_sylowCenter_or_eq_of_normalized hK S hZW hWS hinv with h | h
  · rw [h] at hsW
    exact hsW
  · refine mem_sylowCenter.mpr ⟨hs, fun t ht => ?_⟩
    have htW : t ∈ W := by rw [h]; exact ht
    exact Subgroup.mem_centralizer_singleton_iff.mp (hWs htW)

end Automorphisms

section Generation

theorem not_mem_normalizer_of_not_commute (S : Sylow 2 K) {g : K}
    (hg : ¬ ∀ a ∈ sylowCenter (S : Subgroup K),
      ∀ b ∈ conjSubgroup g (sylowCenter (S : Subgroup K)), a * b = b * a) :
    g ∉ Subgroup.normalizer ((S : Subgroup K) : Set K) := by
  intro hgN
  refine hg fun a ha b hb => ?_
  have hb' : b ∈ sylowCenter (S : Subgroup K) := by
    have h1 := conj_mem_rootCenter hgN (mem_conjSubgroup.mp hb)
    have e : g * (g⁻¹ * b * g) * g⁻¹ = b := by group
    rwa [e] at h1
  exact (mem_sylowCenter.mp hb').2 a (sylowCenter_le _ ha)

theorem sylow_sup_zpowers_eq_top
    (hK : IsBenderGroup K) (S : Sylow 2 K) {g : K}
    (hg : g ∉ Subgroup.normalizer ((S : Subgroup K) : Set K)) {a : K}
    (ha : a ∈ conjSubgroup g (sylowCenter (S : Subgroup K))) (ha1 : a ≠ 1) :
    (S : Subgroup K) ⊔ Subgroup.zpowers a = ⊤ := by
  have haN := not_mem_normalizer_of_mem_conj hK le_rfl hg ha ha1
  have ha2 : a * a = 1 := by
    have h1 := mul_self_eq_one_of_mem_sylowCenter hK S (mem_conjSubgroup.mp ha)
    calc a * a = g * ((g⁻¹ * a * g) * (g⁻¹ * a * g)) * g⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨D, hD⟩ :=
    CFSG.Goldschmidt.G3a.exists_borelSetup (fusionIsBenderGroup_of_isBenderGroup hK) S
  rcases hK with ⟨n, hn, e⟩ | ⟨m, hm, e⟩ | ⟨n, hn, e⟩
  · rw [eq_top_iff, ← sylowCenter_sup_zpowers_eq_top (Or.inl ⟨n, hn, ⟨e⟩⟩) S haN]
    exact sup_le_sup_right (sylowCenter_le _) _
  · rw [eq_top_iff, ← sylowCenter_sup_zpowers_eq_top (Or.inr ⟨m, hm, ⟨e⟩⟩) S haN]
    exact sup_le_sup_right (sylowCenter_le _) _
  · have hZS : sylowCenter (S : Subgroup K) < (S : Subgroup K) := by
      let e' : K ≃* CFSG.Open.PSU3 2 n :=
        e.trans (MulEquiv.subgroupCongr (CFSG.Models.benderPSU3Model_eq_psu3 n))
      obtain ⟨hZc, hSc, -⟩ := hD.orders_psu3 hn e'
      refine lt_of_le_of_ne (sylowCenter_le _) fun h => ?_
      rw [h, hSc] at hZc
      have h3 : 2 ^ n < (2 ^ n) ^ 3 := by
        calc 2 ^ n = (2 ^ n) ^ 1 := (pow_one _).symm
          _ < (2 ^ n) ^ 3 := Nat.pow_lt_pow_right (Nat.one_lt_two_pow (by omega)) (by norm_num)
      omega
    exact u3NormalizedGenerationStatement_holds K n hn ⟨e⟩ S S le_rfl hZS
      (fun b hb _ r hr => (Subgroup.mem_normalizer_iff.mp hb r).mp hr) a ha1 ha2 haN

end Generation

section Squares

theorem mul_self_mem_sylowCenter (hK : IsBenderGroup K)
    (S : Sylow 2 K) {s : K} (hs : s ∈ (S : Subgroup K)) :
    s * s ∈ sylowCenter (S : Subgroup K) := by
  by_cases hab : IsMulCommutative (S : Subgroup K)
  · have hZ : sylowCenter (S : Subgroup K) = (S : Subgroup K) :=
      le_antisymm (sylowCenter_le _) fun x hx =>
        mem_sylowCenter.mpr ⟨hx, fun t ht =>
          congrArg Subtype.val (hab.is_comm.comm ⟨t, ht⟩ ⟨x, hx⟩)⟩
    rw [hZ]
    exact Subgroup.mul_mem _ hs hs
  · obtain ⟨D, hD⟩ :=
      CFSG.Goldschmidt.G3a.exists_borelSetup (fusionIsBenderGroup_of_isBenderGroup hK) S
    rw [← sq]
    exact hD.sq_mem_center hab hs

end Squares

end CFSG.StronglyEmbedded.BenderCentre

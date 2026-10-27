module

public import CFSG.LocalAnalysis.UniquenessCase.UC6K36OddDefChar

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK

open CFSG.Open Subgroup

@[expose] def TwoSigTriv (p : ℕ) (K : Type*) [Group K] : Prop :=
  ∀ S : Sylow p K, ∀ W : Subgroup (MulAut K), IsPGroup 2 W →
    (∀ g ∈ (S : Subgroup K), MulAut.conj g ∈ normalizer (W : Set (MulAut K))) → W = ⊥

theorem TwoSigTriv.of_mulEquiv {p : ℕ} [Fact p.Prime] {K K' : Type*} [Group K] [Group K'] [Finite K]
    (e : K ≃* K') (h : TwoSigTriv p K) : TwoSigTriv p K' := by
  intro S W hW hnorm
  let f : MulAut K' →* MulAut K := (MulAut.congr e.symm).toMonoidHom
  have hf : Function.Injective f := (MulAut.congr e.symm).injective
  have hK' : Finite K' := Finite.of_equiv _ e.toEquiv
  let S₀ : Sylow p K := S.mapSurjective (f := e.symm.toMonoidHom) e.symm.surjective
  have hbot : W.map f = ⊥ := by
    refine h S₀ (W.map f) (hW.map f) fun g hg => ?_
    obtain ⟨g', hg', rfl⟩ := Subgroup.mem_map.1 hg
    have hc : MulAut.conj (e.symm.toMonoidHom g') = f (MulAut.conj g') :=
      (CFSG.ComponentClassification.OuterAutomorphisms.congr_conj e.symm g').symm
    rw [hc]
    exact Subgroup.le_normalizer_map f (Subgroup.mem_map_of_mem f (hnorm g' hg'))
  rw [eq_bot_iff]
  intro w hw
  have hfw : f w ∈ W.map f := Subgroup.mem_map_of_mem f hw
  rw [hbot, Subgroup.mem_bot] at hfw
  exact Subgroup.mem_bot.2 (hf (hfw.trans (map_one f).symm))

namespace Hyp36

open Odd

variable {G : Type} [Group G] [Finite G] {M E : Subgroup G} {p : ℕ}

theorem false_of_twoSigTriv (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hL : CFSG.IsComponent L)
    (hne : ⁅L, pCoreOf 2 M⁆ ≠ ⊥) {K : Type} [Group K] (φ : ↥L ⧸ Subgroup.center ↥L ≃* K)
    (hT : TwoSigTriv p K) : False := by
  classical
  haveI : Fact p.Prime := ⟨h.prime⟩
  have hLc : commutator ↥L = ⊤ := hL.1.1.commutator_eq_top
  obtain ⟨P, hEP⟩ := IsPGroup.exists_le_sylow h.isPGroup
  have hPM : (P : Subgroup G) ≤ M := h.le_of_isPGroup P.isPGroup' hEP
  obtain ⟨R, hRP⟩ := CFSG.Walter.exists_sylow_map_eq_inf_of_isSubnormal P hL.2
  let S : Sylow p K :=
    (R.mapSurjective (f := QuotientGroup.mk' (Subgroup.center ↥L)) (QuotientGroup.mk'_surjective _)).mapSurjective
      (f := φ.toMonoidHom) φ.surjective
  have hSeq : (S : Subgroup K) =
      ((R : Subgroup ↥L).map (QuotientGroup.mk' (Subgroup.center ↥L))).map φ.toMonoidHom := rfl
  set Ψ : G →* MulAut K := psi L φ with hΨ
  have hQ2 : IsPGroup 2 (pCoreOf 2 M) := by
    rw [pCoreOf]
    exact CFSG.pCore_isPGroup.map _
  have hnorm : ∀ g ∈ (S : Subgroup K), MulAut.conj g ∈ normalizer (((pCoreOf 2 M).map Ψ : Subgroup _) :
      Set (MulAut K)) := by
    intro g hg
    rw [hSeq] at hg
    obtain ⟨c, ⟨r, hr, rfl⟩, rfl⟩ := Subgroup.mem_map.1 hg
    have hrP : (r : G) ∈ (P : Subgroup G) := by
      have : (r : G) ∈ (P : Subgroup G) ⊓ L := by
        rw [← hRP]
        exact Subgroup.mem_map_of_mem L.subtype hr
      exact this.1
    have hconj : MulAut.conj (φ.toMonoidHom (QuotientGroup.mk' (Subgroup.center ↥L) r)) = Ψ (r : G) :=
      (psi_eq_conj L φ r.2).symm
    rw [hconj]
    exact Subgroup.le_normalizer_map Ψ
      (Subgroup.mem_map_of_mem Ψ (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M (hPM hrP)))
  have hbot := hT S ((pCoreOf 2 M).map Ψ) (hQ2.map Ψ) hnorm
  apply hne
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro q hq
  have hΨq : Ψ q = 1 := by
    have hmem : Ψ q ∈ (pCoreOf 2 M).map Ψ := Subgroup.mem_map_of_mem Ψ hq
    rw [hbot] at hmem
    exact Subgroup.mem_bot.1 hmem
  have hcomm : ∀ y ∈ L, q * y * q⁻¹ * y⁻¹ ∈ centerOf L := by
    intro y hy
    rw [← psi_mk_eq_iff L φ q y hy, ← hΨ, hΨq]
    rfl
  exact centralizes_of_forall_comm_mem L hLc hcomm y hy

theorem inf_centralizer_eq_bot (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hLM : L ⊔ M = ⊤) :
    pCoreOf 2 M ⊓ centralizer (L : Set G) = ⊥ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X : Subgroup G := pCoreOf 2 M ⊓ centralizer (L : Set G) with hX
  have hX2 : IsPGroup 2 X := by
    have hQ2 : IsPGroup 2 (pCoreOf 2 M) := by
      rw [pCoreOf]
      exact CFSG.pCore_isPGroup.map _
    exact hQ2.to_le inf_le_left
  have hLN : L ≤ normalizer (X : Set G) := by
    have hXC : X ≤ centralizer (L : Set G) := inf_le_right
    exact (Subgroup.le_centralizer_iff.1 hXC).trans (Subgroup.centralizer_le_normalizer _)
  have hMN : M ≤ normalizer (X : Set G) := by
    intro m hm
    have hmQ := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 M hm
    have hmC : m ∈ normalizer (centralizer (L : Set G) : Set G) := by
      rw [mem_normalizer_iff]
      intro c
      have key : ∀ (g : G) (c : G), c ∈ centralizer (L : Set G) →
          g * c * g⁻¹ ∈ centralizer (L : Set G) := by
        intro g c hc
        rw [Subgroup.mem_centralizer_iff]
        intro y hy
        have hy' : g⁻¹ * y * g ∈ L := by
          simpa using (inferInstance : L.Normal).conj_mem y hy g⁻¹
        have h1 := Subgroup.mem_centralizer_iff.1 hc _ hy'
        calc y * (g * c * g⁻¹) = g * ((g⁻¹ * y * g) * c) * g⁻¹ := by group
          _ = g * (c * (g⁻¹ * y * g)) * g⁻¹ := by rw [h1]
          _ = g * c * g⁻¹ * y := by group
      constructor
      · exact key m c
      · intro hc
        have := key m⁻¹ _ hc
        simpa [mul_assoc] using this
    rw [mem_normalizer_iff]
    intro x
    rw [mem_normalizer_iff] at hmQ hmC
    exact ⟨fun hx => ⟨(hmQ x).1 hx.1, (hmC x).1 hx.2⟩, fun hx => ⟨(hmQ x).2 hx.1, (hmC x).2 hx.2⟩⟩
  have htop : normalizer (X : Set G) = ⊤ := by
    rw [eq_top_iff, ← hLM]
    exact sup_le hLN hMN
  have hXn : (X.subgroupOf ⊤).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer le_top).2 (by rw [htop])
  have hle : X ≤ pCoreOf 2 (⊤ : Subgroup G) :=
    CFSG.LieType.BorelTits.le_pCoreOf 2 le_top hXn hX2
  rw [h.pCoreOf_top_eq_bot] at hle
  exact le_bot_iff.1 hle

theorem eq_one_of_psi_eq_one (h : Hyp36 G M p E) {L : Subgroup G} [L.Normal] (hLc : commutator ↥L = ⊤)
    (hLM : L ⊔ M = ⊤) {K : Type} [Group K] (φ : ↥L ⧸ Subgroup.center ↥L ≃* K) {q : G}
    (hq : q ∈ pCoreOf 2 M) (hΨq : psi L φ q = 1) : q = 1 := by
  have hcomm : ∀ y ∈ L, q * y * q⁻¹ * y⁻¹ ∈ centerOf L := by
    intro y hy
    rw [← psi_mk_eq_iff L φ q y hy, hΨq]
    rfl
  have hc := centralizes_of_forall_comm_mem L hLc hcomm
  have hmem : q ∈ pCoreOf 2 M ⊓ centralizer (L : Set G) := by
    refine Subgroup.mem_inf.2 ⟨hq, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (hc y hy).symm
  rw [h.inf_centralizer_eq_bot hLM] at hmem
  exact Subgroup.mem_bot.1 hmem

end Hyp36

end CFSG.LocalAnalysis.UniquenessCase.UCK

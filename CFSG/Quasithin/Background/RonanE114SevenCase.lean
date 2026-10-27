module

public import CFSG.Quasithin.Background.RonanE114SevenCore
public import CFSG.Quasithin.Background.RonanE114SevenLevi
public import CFSG.GH74.GLS.IVK.Proofs2.Lemma44b
public import CFSG.Quasithin.Vol2.Ch11SecU1L3IZ
public import CFSG.Quasithin.Vol2.Ch11SecU1U3D

public section

namespace CFSG.Quasithin.RonanE114.Seven

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Quasithin.A38c15 CFSG.Quasithin.Vol2.Ch11
open CFSG.GH74.GLS.IVK.Proofs2

theorem quasithinIsSylowTwo_of_isSylowIn_top {G : Type} [Group G] {T : Subgroup G}
    (h : IsSylowIn 2 T ⊤) : quasithinIsSylowTwo T :=
  ⟨h.2.1, by
    have h2 : ¬ 2 ∣ T.relIndex ⊤ := h.2.2
    rwa [Subgroup.relIndex_top_right] at h2⟩

section L3


theorem nParam_le_one_of_psl3_wreathed (hirr : SL3OddIrr) {p : ℕ} (hp : p.Prime) (hp13 : 13 ≤ p)
    (hp4 : p % 4 = 1) {G : Type} [Group G] [Finite G]
    (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G))
    (hF : IsPSL 3 p 1 ↥(CFSG.generalizedFitting G)) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) (hTL : ¬ T ≤ CFSG.generalizedFitting G) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  set L := CFSG.generalizedFitting G with hL
  obtain ⟨e⟩ := E2P.Asc80.exists_equiv_psl3 hF
  have hnab : ∃ a b : ↥L, a * b ≠ b * a := by
    obtain ⟨a, b, hab⟩ := SecU1.L3I.exists_ne_comm_psl3 (p := p)
    refine ⟨e.symm a, e.symm b, fun h => hab ?_⟩
    have h1 := congrArg e h
    simpa using h1
  have hAS := SecE3.almostSimple_generalizedFitting hs hnab hT.2.1 hFT
  have h2 : 2 ∣ Nat.card ↥L := by
    rw [Nat.card_congr e.toEquiv, ← SecU1.L3I.orderOf_zc hp2]
    exact orderOf_dvd_natCard _
  have hGL : ∃ t : G, t ∉ L := by
    obtain ⟨t, -, ht⟩ := SetLike.not_le_iff_exists.mp hTL
    exact ⟨t, ht⟩
  have hwr : ∀ S : Sylow 2 ↥L, ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (↥(S : Subgroup ↥L) ≃* CFSG.Open.WreathedTwoGroup m) := by
    obtain ⟨-, K, hK, hfin, hcard, ⟨eK⟩⟩ := hF
    intro S
    exact Lemma44b.sylow_L3_wr hp hp2 (Or.inl ⟨rfl, K, hK, hfin, hcard, ⟨eK⟩⟩)
      (by simpa using hp4) (by simpa using hp.one_lt) S
  exact nParam_le_one_of_wreathed hAS hT h2 hwr
    (fun x hx hx2 => SecU1.L3I.isCoatom_centralizer_L3 hirr hp2 hAS e hGL hx hx2)
    (nParam_centralizer_le_one_L3 (by omega) hAS e)

end L3

section U3


theorem nParam_le_one_of_psu3_wreathed {p : ℕ} (hp : p.Prime) (hp7 : 7 ≤ p) (hp4 : p % 4 = 3)
    {G : Type} [Group G] [Finite G] (hs : IsSimpleGroup ↥(CFSG.generalizedFitting G))
    (hU : IsPSU 3 p 1 ↥(CFSG.generalizedFitting G)) {T : Subgroup G} (hT : IsSylowIn 2 T ⊤)
    (hFT : CFSG.generalizedFitting G ⊔ T = ⊤) :
    E1.nParam (⊤ : Subgroup G) ≤ 1 := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  have hp3 : p ≠ 3 := by omega
  obtain ⟨F, _, _, hF, ψ, hAS, h2⟩ := SecU1.U3.exists_psu3_model hp2 hU hs
    (quasithinIsSylowTwo_of_isSylowIn_top hT) hFT
  have hwr : ∀ S : Sylow 2 ↥(CFSG.generalizedFitting G), ∃ m : ℕ, 2 ≤ m ∧
      Nonempty (↥(S : Subgroup ↥(CFSG.generalizedFitting G)) ≃*
        CFSG.Open.WreathedTwoGroup m) := by
    obtain ⟨-, K, hK, hfin, hcard, ⟨eK⟩⟩ := hU
    intro S
    exact Lemma44b.sylow_U3_wr hp hp2 (Or.inr ⟨rfl, K, hK, hfin, hcard, ⟨eK⟩⟩)
      (by simpa using hp4) S
  exact nParam_le_one_of_wreathed hAS hT h2 hwr
    (fun x hx hx2 => SecU1.U3.isCoatom_centralizer hp2 hp3 hF hAS hT ψ hx hx2)
    (nParam_centralizer_le_one_U3 hp7 hF hAS ψ)

end U3

end CFSG.Quasithin.RonanE114.Seven

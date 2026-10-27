module

public import CFSG.Quasithin.Background.RonanF13Bender
public import CFSG.Quasithin.Background.RonanF13Hall
public import CFSG.Quasithin.Recognition.St84.SetupOf
public import CFSG.Quasithin.Vol2.Ch11SecSXK3

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.GH74.Uniqueness.Bender

theorem card_isCyclic_of_hallTwoPrime {G : Type} [Group G]
    [Finite G] {L S D : Subgroup G} {n i : ℕ} (hsyl : IsSylowTwoOf (S ⊓ L) L)
    (hD : RonanF13.HallTwoPrime D (borelOf L S)) (hBD : borelOf L S = (S ⊓ L) ⊔ D)
    (hBt : BenderType (oTwoQuot ↥L) n i 1) :
    Nat.card D = 2 ^ n - 1 ∧ IsCyclic ↥D := by
  classical
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (CFSG.pCore 2 ↥L) with hπ
  set T : Subgroup (oTwoQuot ↥L) := ((S ⊓ L).subgroupOf L).map π with hT
  set Dbar : Subgroup (oTwoQuot ↥L) := (D.subgroupOf L).map π with hDbar
  have hDL : D ≤ L := hD.1.trans (F1.borelOf_le L S)
  obtain ⟨hTpg, hTodd, hmap⟩ := F1.map_borelOf_eq_normalizer hsyl
  have hsup : T ⊔ Dbar = Subgroup.normalizer (T : Set (oTwoQuot ↥L)) := by
    have hmap_sup : T ⊔ Dbar =
        (((S ⊓ L).subgroupOf L) ⊔ (D.subgroupOf L)).map π := by
      rw [hT, hDbar, ← Subgroup.map_sup]
    rw [hmap_sup, ← Subgroup.subgroupOf_sup (B := L)
      (inf_le_right : S ⊓ L ≤ L) hDL, ← hBD]
    simpa [hT, hπ] using hmap
  have hDbarOdd : Odd (Nat.card ↥Dbar) := by
    have hle : Nat.card ↥Dbar ∣ Nat.card ↥D := by
      have h1 : Nat.card ↥(D.subgroupOf L) = Nat.card ↥D :=
        Nat.card_congr (Subgroup.subgroupOfEquivOfLe hDL).toEquiv
      rw [hDbar, ← h1]
      exact Subgroup.card_map_dvd _ π
    exact Odd.of_dvd_nat hD.2.1 hle
  have hcardDbar : Nat.card ↥Dbar = (2 ^ n - 1) * 1 :=
    RonanF13.bender_card_hall hBt hTpg hTodd hsup hDbarOdd
  have hcycDbar : IsCyclic ↥Dbar :=
    RonanF13.bender_hall_cyclic hBt hTpg hTodd hsup hDbarOdd
  have hinj : Function.Injective (π.comp (D.subgroupOf L).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [hπ, MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have hxO : ((x : ↥L) : G) ∈ pCoreOf 2 L := by
      rw [CFSG.Quasithin.Vol2.Ch11.SecS.pCoreOf_two_eq_map]
      exact ⟨(x : ↥L), hx, rfl⟩
    have hbot : pCoreOf 2 L ⊓ D = ⊥ :=
      RonanF13.inf_eq_bot_of_odd (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L) hD.2.1
    have hxbot : ((x : ↥L) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hbot]
      exact ⟨hxO, Subgroup.mem_subgroupOf.mp x.2⟩
    rw [Subgroup.mem_bot] at hxbot
    exact Subtype.ext (Subtype.ext hxbot)
  have hrange : (π.comp (D.subgroupOf L).subtype).range = Dbar := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype, hDbar]
  have hcardD : Nat.card ↥Dbar = Nat.card ↥D := by
    rw [hDbar]
    simpa [hπ, CFSG.Quasithin.modO2Image] using
      CFSG.Quasithin.Vol2.Ch11.SecS.card_modO2Image_of_odd (Y := L) (X := D) hDL hD.2.1
  have hcycSub : IsCyclic ↥(D.subgroupOf L) := by
    haveI : IsCyclic ↥(π.comp (D.subgroupOf L).subtype).range := by
      rw [hrange]
      exact hcycDbar
    let e := MonoidHom.ofInjective hinj
    exact isCyclic_of_surjective e.symm.toMonoidHom e.symm.surjective
  refine ⟨?_, ?_⟩
  · rw [← hcardD, hcardDbar, mul_one]
  · exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hDL).toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hDL).surjective

theorem exists_mem_normalizer_of_frattini {G : Type} [Group G] [Finite G]
    {P K Q N : Subgroup G} (hKP : K ≤ P) (hPK : P ≤ Subgroup.normalizer (K : Set G))
    (hQK : Q ≤ K) (hPQ : P ≤ Subgroup.normalizer (Q : Set G)) (hQ : IsSylowTwoOf Q K)
    (hN : RonanF13.HallTwoPrime N K) :
    ∀ g ∈ P, ∃ m ∈ P ⊓ Subgroup.normalizer (N : Set G), m⁻¹ * g ∈ Q := by
  intro g hgP
  have hQNbot : Q ⊓ N = ⊥ :=
    RonanF13.inf_eq_bot_of_odd hQ.2.1 hN.2.1
  have hQNsup : Q ⊔ N = K :=
    RonanF13.sup_eq_of_hallTwoPrime hQK le_rfl hQ.2.2 hN
  have hgK : g ∈ Subgroup.normalizer (K : Set G) := hPK hgP
  have hgQ : g ∈ Subgroup.normalizer (Q : Set G) := hPQ hgP
  have hconjK : conjSub g K = K :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgK
  have hconjQ : conjSub g Q = Q :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mp hgQ
  set N' : Subgroup G := conjSub g N with hN'
  have hN'K : N' ≤ K := by
    rw [hN']
    calc conjSub g N ≤ conjSub g K := conjSub_mono g hN.1
      _ = K := hconjK
  have hQN'sup : Q ⊔ N' = K := by
    have h := conjSub_sup g Q N
    rw [hQNsup, hconjQ, hconjK, ← hN'] at h
    exact h.symm
  have hQN'bot : Q ⊓ N' = ⊥ := by
    have h := conjSub_inf g Q N
    rw [hQNbot, conjSub_bot, hconjQ, ← hN'] at h
    exact h.symm
  have hQnormal : (Q.subgroupOf K).Normal :=
    Subgroup.normal_subgroupOf_of_le_normalizer (hKP.trans hPQ)
  obtain ⟨n, hnQ, hnEq⟩ :=
    CFSG.Quasithin.St84.exists_conj_eq_of_complement
      (F := K) (N := Q) hQK hQnormal hQ hN.1 hN'K hQNsup hQN'sup hQNbot hQN'bot
  refine ⟨n * g, ⟨?_, ?_⟩, ?_⟩
  · exact P.mul_mem (hKP (hQK hnQ)) hgP
  · have hm : conjSub (n * g) N = N := by
      rw [conjSub_mul, ← hN', hnEq, conjSub_inv_conjSub]
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr hm
  · have hninv : n⁻¹ ∈ Q := Q.inv_mem hnQ
    have hginv : g⁻¹ ∈ Subgroup.normalizer (Q : Set G) :=
      (Subgroup.normalizer (Q : Set G)).inv_mem hgQ
    have hconj : g⁻¹ * n⁻¹ * g ∈ Q := by
      have := (Subgroup.mem_normalizer_iff.mp hginv (n⁻¹)).mp hninv
      simpa using this
    have hcalc : (n * g)⁻¹ * g = g⁻¹ * n⁻¹ * g := by group
    rw [hcalc]
    exact hconj

end CFSG.Quasithin.Stroth

end

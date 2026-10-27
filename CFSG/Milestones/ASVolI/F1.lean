module

public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
import CFSG.Quasithin.Background.RonanF13Core
import CFSG.Quasithin.Background.RonanF13Listed

public section

namespace CFSG.ASVolI.ChF

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin

abbrev HypF_1_1 {G : Type} [Group G] (L₁ L₂ S : Subgroup G) : Prop := Hyp111 L₁ L₂ S

@[expose] def IsHallTwoPrime {G : Type} [Group G] (D X : Subgroup G) : Prop :=
  D ≤ X ∧ Odd (Nat.card D) ∧ ∃ k : ℕ, D.relIndex X = 2 ^ k

@[expose] def F13Conclusion {G : Type} [Group G] (Li Lj S : Subgroup G) : Prop :=
  ((borelOf Li S ≠ Li ∧ S ⊓ Li ≤ borelOf Li S ∧
      (∀ M : Subgroup G, S ⊓ Li ≤ M → M ≤ Li → M ≠ Li → M ≤ borelOf Li S)) ∧
    ((borelOf Li S).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li)) =
      Subgroup.normalizer
        ((((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li)) :
          Subgroup (↥Li ⧸ pCore 2 ↥Li)) : Set (↥Li ⧸ pCore 2 ↥Li)) ∧
    (IsPGroup 2 (((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li))) ∧
      ¬ 2 ∣ (((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li))).index) ∧
    pCoreOf 2 (borelOf Li S) = S ⊓ Li) ∧
  borelOf Lj S = Lj ⊓ Subgroup.normalizer (Li : Set G) ∧
  (borelOf Lj S ≤ Subgroup.normalizer (borelOf Li S : Set G) ∧
    borelOf Lj S ≤ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G)) ∧
  (borelOf Li S ⊔ borelOf Lj S ⊔ S =
      (Li ⊔ S ⊔ borelOf Lj S) ⊓ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) ∧
    Group.IsSolvable ↥(borelOf Li S ⊔ borelOf Lj S ⊔ S)) ∧
  (∃ Di Dj : Subgroup G, IsHallTwoPrime Di (borelOf Li S) ∧ IsHallTwoPrime Dj (borelOf Lj S) ∧
      borelOf Li S = (S ⊓ Li) ⊔ Di ∧ borelOf Lj S = (S ⊓ Lj) ⊔ Dj ∧
      Di ≤ Subgroup.normalizer (Dj : Set G) ∧
      borelOf Li S ⊔ borelOf Lj S ⊔ S = S ⊔ Di ⊔ Dj ∧
      (∀ x ∈ Di ⊔ Dj, ∀ y ∈ Di ⊔ Dj, x * y = y * x) ∧
      IsHallTwoPrime (Di ⊔ Dj) (borelOf Li S ⊔ borelOf Lj S ⊔ S)) ∧
  ((Li ⊔ (borelOf Li S ⊔ borelOf Lj S ⊔ S)) ⊓ (Lj ⊔ (borelOf Li S ⊔ borelOf Lj S ⊔ S)) =
    borelOf Li S ⊔ borelOf Lj S ⊔ S)

end CFSG.ASVolI.ChF

namespace CFSG.ASVolI

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin
open CFSG.ASVolI.ChF

@[expose] def F_1_2 : Prop :=
  ∀ (G : Type) [Group G] (L₁ L₂ S : Subgroup G),
    (HypF_1_1 L₁ L₂ S →
      ∀ (Li Lj : Subgroup G), (Li = L₁ ∧ Lj = L₂) ∨ (Li = L₂ ∧ Lj = L₁) →
        (∃ Dj : Subgroup G, IsHallTwoPrime Dj (borelOf Lj S) ∧ borelOf Lj S = (S ⊓ Lj) ⊔ Dj) ∧
        ∀ Dj : Subgroup G, IsHallTwoPrime Dj (borelOf Lj S) →
          borelOf Lj S = (S ⊓ Lj) ⊔ Dj ∧ Li ⊔ S ⊔ borelOf Lj S = Li ⊔ S ⊔ Dj) ∧
    (∀ (Li Lj : Subgroup G), (Li = L₁ ∧ Lj = L₂) ∨ (Li = L₂ ∧ Lj = L₁) →
      (Finite ↥S ∧ IsPGroup 2 S ∧ S ≤ Subgroup.normalizer (Li : Set G) ∧
          S ≤ Subgroup.normalizer (Lj : Set G)) →
      (IsSylowTwoOf (S ⊓ Li) Li ∧ IsSylowTwoOf (S ⊓ Lj) Lj) →
      (IsRankOneListed (oTwoQuot ↥Li) ∧ IsRankOneListed (oTwoQuot ↥Lj)) →
        ∀ Dj : Subgroup G, IsHallTwoPrime Dj (borelOf Lj S) → Dj ≤ Subgroup.normalizer (Li : Set G) →
          borelOf Lj S ≤ Subgroup.normalizer (Li : Set G))

private theorem f12_sup_eq_of_hall {G : Type} [Group G] {B T L D : Subgroup G}
    (hTB : T ≤ B) (hBL : B ≤ L) (hT : ¬ 2 ∣ T.relIndex L) (hD : IsHallTwoPrime D B) :
    T ⊔ D = B := by
  unfold IsHallTwoPrime at hD
  obtain ⟨hDB, -, k, hk⟩ := hD
  have hDE : D ≤ T ⊔ D := le_sup_right
  have hEB : T ⊔ D ≤ B := sup_le hTB hDB
  have h1 : (T ⊔ D).relIndex B ∣ 2 ^ k := by
    rw [← hk, ← Subgroup.relIndex_mul_relIndex D (T ⊔ D) B hDE hEB]
    exact dvd_mul_left _ _
  have h2 : (T ⊔ D).relIndex B ∣ T.relIndex L := by
    rw [← Subgroup.relIndex_mul_relIndex T B L hTB hBL,
      ← Subgroup.relIndex_mul_relIndex T (T ⊔ D) B le_sup_left hEB]
    exact ⟨T.relIndex (T ⊔ D) * B.relIndex L, by ring⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h1
  rw [hj] at h2
  have hj0 : j = 0 := by
    by_contra hne
    exact hT ((dvd_pow_self 2 hne).trans h2)
  have hone : (T ⊔ D).relIndex B = 1 := by rw [hj, hj0, pow_zero]
  exact le_antisymm hEB (Subgroup.relIndex_eq_one.mp hone)

private theorem f12_exists_hall {G : Type} [Group G] {B T : Subgroup G}
    (hTB : T ≤ B) (hfin : Finite ↥T) (hN : (T.subgroupOf B).Normal) (hp : IsPGroup 2 T)
    (hodd : ¬ 2 ∣ (T.subgroupOf B).index) :
    ∃ D : Subgroup G, IsHallTwoPrime D B := by
  have hpN : IsPGroup 2 ↥(T.subgroupOf B) := hp.of_equiv (Subgroup.subgroupOfEquivOfLe hTB).symm
  have hfinN : Finite ↥(T.subgroupOf B) :=
    Finite.of_equiv ↥T (Subgroup.subgroupOfEquivOfLe hTB).symm.toEquiv
  obtain ⟨m, hm⟩ := hpN.exists_card_eq
  have hcop : Nat.Coprime (Nat.card ↥(T.subgroupOf B)) (T.subgroupOf B).index := by
    rw [hm]
    exact Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr hodd)
  obtain ⟨K, hK⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hsub : (K.map B.subtype).subgroupOf B = K :=
    Subgroup.comap_map_eq_self_of_injective B.subtype_injective K
  refine ⟨K.map B.subtype, ?_⟩
  unfold IsHallTwoPrime
  refine ⟨Subgroup.map_subtype_le K, ?_, m, ?_⟩
  · rw [Subgroup.card_map_of_injective B.subtype_injective, ← hK.symm.index_eq_card]
    exact Nat.odd_iff.mpr (by omega)
  · rw [Subgroup.relIndex, hsub, hK.index_eq_card, hm]

private theorem f12_borel_hall {G : Type} [Group G] {Lj S : Subgroup G}
    (hS : Finite ↥S) (h : IsSylowTwoOf (S ⊓ Lj) Lj) :
    (∃ D : Subgroup G, IsHallTwoPrime D (borelOf Lj S)) ∧
      ∀ D : Subgroup G, IsHallTwoPrime D (borelOf Lj S) → (S ⊓ Lj) ⊔ D = borelOf Lj S := by
  have hTB : S ⊓ Lj ≤ borelOf Lj S := le_inf h.1 Subgroup.le_normalizer
  have hBL : borelOf Lj S ≤ Lj := inf_le_left
  have hT : ¬ 2 ∣ (S ⊓ Lj).relIndex Lj := h.2.2
  have hfin : Finite ↥(S ⊓ Lj) :=
    Finite.of_injective (fun x : ↥(S ⊓ Lj) => (⟨x.1, (inf_le_left : S ⊓ Lj ≤ S) x.2⟩ : ↥S))
      (fun a b hab => Subtype.ext (Subtype.mk.inj hab))
  have hN : ((S ⊓ Lj).subgroupOf (borelOf Lj S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hTB).mpr inf_le_right
  have hodd : ¬ 2 ∣ ((S ⊓ Lj).subgroupOf (borelOf Lj S)).index := by
    intro hd
    have hdiv : (S ⊓ Lj).relIndex (borelOf Lj S) ∣ (S ⊓ Lj).relIndex Lj :=
      ⟨(borelOf Lj S).relIndex Lj, (Subgroup.relIndex_mul_relIndex (S ⊓ Lj) (borelOf Lj S) Lj hTB hBL).symm⟩
    exact hT (hd.trans hdiv)
  exact ⟨f12_exists_hall hTB hfin hN h.2.1 hodd, fun D hD => f12_sup_eq_of_hall hTB hBL hT hD⟩

private theorem f12_borel {G : Type} [Group G] {Li Lj S : Subgroup G} (hS : Finite ↥S)
    (hsyl : IsSylowTwoOf (S ⊓ Lj) Lj) :
    (∃ Dj : Subgroup G, IsHallTwoPrime Dj (borelOf Lj S) ∧ borelOf Lj S = (S ⊓ Lj) ⊔ Dj) ∧
      ∀ Dj : Subgroup G, IsHallTwoPrime Dj (borelOf Lj S) →
        borelOf Lj S = (S ⊓ Lj) ⊔ Dj ∧ Li ⊔ S ⊔ borelOf Lj S = Li ⊔ S ⊔ Dj := by
  obtain ⟨hex, huniq⟩ := f12_borel_hall hS hsyl
  refine ⟨?_, fun Dj hD => ?_⟩
  · obtain ⟨D, hD⟩ := hex
    exact ⟨D, hD, (huniq D hD).symm⟩
  · have hB : borelOf Lj S = (S ⊓ Lj) ⊔ Dj := (huniq Dj hD).symm
    refine ⟨hB, ?_⟩
    rw [hB]
    apply le_antisymm
    · exact sup_le le_sup_left
        (sup_le (inf_le_left.trans (le_sup_right.trans le_sup_left)) le_sup_right)
    · exact sup_le_sup_left le_sup_right _

theorem as_F_1_2 : F_1_2 := by
  unfold F_1_2
  intro G _ L₁ L₂ S
  refine ⟨fun hyp Li Lj hcase => ?_, fun Li Lj hcase hdata hsyl _ Dj hD hDN => ?_⟩
  · rcases hcase with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact f12_borel hyp.h1.finite hyp.h2.sylow
    · exact f12_borel hyp.h1.finite hyp.h1.sylow
  · obtain ⟨hfin, -, hSLi, -⟩ := hdata
    rw [((f12_borel (Li := Li) hfin hsyl.2).2 Dj hD).1]
    exact sup_le (inf_le_left.trans hSLi) hDN

section Loc

open CFSG.LieType.BorelTits CFSG.Quasithin.F7

variable {G : Type} [Group G]

private theorem loc_le_of_isPGroup_of_odd {P T : Subgroup G} (hP : IsPGroup 2 ↥P) (hTP : T ≤ P)
    (hT : ¬ 2 ∣ T.relIndex P) : P ≤ T := by
  have hne : (T.subgroupOf P).index ≠ 0 := by
    intro h0
    exact hT (by rw [Subgroup.relIndex, h0]; exact dvd_zero 2)
  haveI : (T.subgroupOf P).FiniteIndex := ⟨hne⟩
  obtain ⟨n, hn⟩ := hP.index (T.subgroupOf P)
  have hn0 : n = 0 := by
    by_contra hn0
    exact hT (by rw [Subgroup.relIndex, hn]; exact dvd_pow_self 2 hn0)
  rw [hn0, pow_zero, Subgroup.index_eq_one] at hn
  intro x hx
  have hmem : (⟨x, hx⟩ : ↥P) ∈ T.subgroupOf P := by
    rw [hn]
    exact Subgroup.mem_top _
  exact (Subgroup.mem_subgroupOf).mp hmem

private theorem loc_pCoreOf_isPGroup (H : Subgroup G) : IsPGroup 2 ↥(pCoreOf 2 H) :=
  (CFSG.pCore_isPGroup (p := 2) (G := ↥H)).map H.subtype

private theorem loc_pCoreOf_le {T H : Subgroup G} (h : IsSylowTwoOf T H) : pCoreOf 2 H ≤ T := by
  have hNH : pCoreOf 2 H ≤ H := CFSG.LieType.BorelTits.pCoreOf_le 2 H
  have hHN : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hTP : T ≤ pCoreOf 2 H ⊔ T := le_sup_right
  have hPH : pCoreOf 2 H ⊔ T ≤ H := sup_le hNH h.1
  have hP : IsPGroup 2 ↥(pCoreOf 2 H ⊔ T) :=
    IsPGroup.to_sup_of_normal_left' (loc_pCoreOf_isPGroup H) h.2.1 (h.1.trans hHN)
  have hdvd : T.relIndex (pCoreOf 2 H ⊔ T) ∣ T.relIndex H := by
    rw [← Subgroup.relIndex_mul_relIndex T (pCoreOf 2 H ⊔ T) H hTP hPH]
    exact dvd_mul_right _ _
  have hodd : ¬ 2 ∣ T.relIndex (pCoreOf 2 H ⊔ T) := fun hd => h.2.2 (hd.trans hdvd)
  exact le_sup_left.trans (loc_le_of_isPGroup_of_odd hP hTP hodd)

private theorem loc_pCoreOf_inf_le {K H : Subgroup G} (hKH : K ≤ H) :
    pCoreOf 2 H ⊓ K ≤ pCoreOf 2 K := by
  refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_right ?_
    ((loc_pCoreOf_isPGroup H).to_le inf_le_left)
  exact CFSG.Quasithin.F7.le_normalizer_inf
    (hKH.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H)) Subgroup.le_normalizer

private theorem loc_borelOf_eq_normalizer {Li Lj S : Subgroup G} (h : Hyp111R Li Lj S) :
    borelOf Lj S = Lj ⊓ Subgroup.normalizer (Li : Set G) := by
  have hi := h.hyp.h1
  apply le_antisymm (le_inf (CFSG.Quasithin.F1.borelOf_le Lj S) hi.borel_le)
  by_cases hN : Lj ⊓ Subgroup.normalizer (Li : Set G) = Lj
  · exfalso
    have hLjLi : Lj ≤ Subgroup.normalizer (Li : Set G) := inf_eq_left.mp hN
    have hG0 : Li ⊔ Lj ⊔ S ≤ Subgroup.normalizer (pCoreOf 2 Li : Set G) :=
      sup_le (sup_le (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Li)
        (CFSG.Quasithin.F7.le_normalizer_pCoreOf_of_le_normalizer hLjLi))
        (CFSG.Quasithin.F7.le_normalizer_pCoreOf_of_le_normalizer hi.normalizes)
    have hO : pCoreOf 2 Li = ⊥ := by
      have h1 := CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
        ((CFSG.LieType.BorelTits.pCoreOf_le 2 Li).trans (le_sup_left.trans le_sup_left)) hG0
        (loc_pCoreOf_isPGroup Li)
      rw [h.hyp.o2] at h1
      exact le_bot_iff.mp h1
    set P := Li ⊔ S ⊔ borelOf Lj S with hP
    have hPnorm : P ≤ Subgroup.normalizer (Li : Set G) :=
      sup_le (sup_le Subgroup.le_normalizer hi.normalizes) hi.borel_le
    have hLiP : Li ≤ P := le_sup_left.trans le_sup_left
    have hinf : pCoreOf 2 P ⊓ Li ≤ ⊥ := by
      have := loc_pCoreOf_inf_le hLiP
      rwa [hO] at this
    have hcomm : ⁅Li, pCoreOf 2 P⁆ = ⊥ := by
      refine le_bot_iff.mp (le_trans (CFSG.Quasithin.F7.commutator_le_inf_of_normalizes ?_ ?_)
        (by rw [inf_comm]; exact hinf))
      · exact hLiP.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P)
      · exact (CFSG.LieType.BorelTits.pCoreOf_le 2 P).trans hPnorm
    have hcent : Li ≤ Subgroup.centralizer (pCoreOf 2 P : Set G) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
    have hLiQ : Li ≤ pCoreOf 2 P := fun x hx => hi.charTwo ⟨hLiP hx, hcent hx⟩
    have hLi2 : IsPGroup 2 ↥Li := (loc_pCoreOf_isPGroup P).to_le hLiQ
    have hsyl : Li ≤ S ⊓ Li := loc_le_of_isPGroup_of_odd hLi2 inf_le_right hi.sylow.2.2
    apply h.r1.borel_ne
    have e : S ⊓ Li = Li := le_antisymm inf_le_right hsyl
    rw [e]
    exact inf_eq_left.mpr Subgroup.le_normalizer
  · have hM : Lj ⊓ Subgroup.normalizer (Li : Set G) ≤
        Subgroup.normalizer ((S ⊓ Lj : Subgroup G) : Set G) := by
      refine h.r2.unique_max _ ?_ inf_le_left hN
      exact le_inf inf_le_right (inf_le_left.trans hi.normalizes)
    exact le_inf inf_le_left hM

private theorem loc_borelOf_le_normalizer_borelOf {Li Lj S : Subgroup G} (h : Hyp111R Li Lj S) :
    borelOf Lj S ≤ Subgroup.normalizer ((borelOf Li S : Subgroup G) : Set G) := by
  have hi := h.hyp.h1
  have hj := h.hyp.h2
  have hBi : borelOf Li S = Li ⊓ Subgroup.normalizer (Lj : Set G) :=
    loc_borelOf_eq_normalizer h.symm
  set X : Subgroup G := S ⊔ borelOf Lj S with hX
  have hXLj : X ≤ Subgroup.normalizer (Lj : Set G) :=
    sup_le hj.normalizes ((CFSG.Quasithin.F1.borelOf_le Lj S).trans Subgroup.le_normalizer)
  have hYB : X ⊓ Li ≤ borelOf Li S := by
    rw [hBi]
    exact le_inf inf_le_right (inf_le_left.trans hXLj)
  have hSY : S ⊓ Li ≤ X ⊓ Li := inf_le_inf_right Li le_sup_left
  have key : ∀ b ∈ borelOf Lj S,
      conjSub b (borelOf Li S) ≤ borelOf Li S := by
    intro b hb
    have hbX : b ∈ X := Subgroup.mem_sup_right hb
    have hbLi : b ∈ Subgroup.normalizer (Li : Set G) := hi.borel_le hb
    have hcLi : conjSub b Li = Li := CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer hbLi
    have hbY : conjSub b (X ⊓ Li) = X ⊓ Li :=
      CFSG.Quasithin.F1.conjSub_eq_of_mem_normalizer
        (CFSG.Quasithin.F7.mem_normalizer_inf (Subgroup.le_normalizer hbX) hbLi)
    have hM1 : conjSub b (borelOf Li S) ≤ Li :=
      (conjSub_mono b (CFSG.Quasithin.F1.borelOf_le Li S)).trans hcLi.le
    have hM2 : S ⊓ Li ≤ conjSub b (borelOf Li S) :=
      calc S ⊓ Li ≤ X ⊓ Li := hSY
        _ = conjSub b (X ⊓ Li) := hbY.symm
        _ ≤ conjSub b (borelOf Li S) := conjSub_mono b hYB
    have hM3 : conjSub b (borelOf Li S) ≠ Li := by
      intro heq
      apply h.r1.borel_ne
      have : conjSub b (borelOf Li S) = conjSub b Li := heq.trans hcLi.symm
      exact (conjSub_inj b).mp this
    exact le_inf hM1 (h.r1.unique_max _ hM2 hM1 hM3)
  intro b hb
  exact CFSG.Quasithin.F7.mem_normalizer_of_conj_le (key b hb) (key b⁻¹ ((borelOf Lj S).inv_mem hb))

private theorem loc_pCoreOf_borelOf {Li S : Subgroup G} (h : IsSylowTwoOf (S ⊓ Li) Li) :
    pCoreOf 2 (borelOf Li S) = S ⊓ Li := by
  apply le_antisymm
  · exact loc_pCoreOf_le (isSylowTwoOf_mono_right h (CFSG.Quasithin.F1.sylow_le_borelOf Li S)
      (CFSG.Quasithin.F1.borelOf_le Li S))
  · exact CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      (CFSG.Quasithin.F1.sylow_le_borelOf Li S) (CFSG.Quasithin.F1.borelOf_le_normalizer Li S) h.2.1

private theorem loc_borelOf_le_normalizer_sylow {Li Lj S : Subgroup G} (h : Hyp111R Li Lj S) :
    borelOf Lj S ≤ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) := by
  have := CFSG.Quasithin.F7.le_normalizer_pCoreOf_of_le_normalizer
    (loc_borelOf_le_normalizer_borelOf h)
  rwa [loc_pCoreOf_borelOf h.hyp.h1.sylow] at this

private theorem loc_bigB_le_normalizer_sylow {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S) :
    bigB L1 L2 S ≤ Subgroup.normalizer ((S ⊓ L1 : Subgroup G) : Set G) ∧
      bigB L1 L2 S ≤ Subgroup.normalizer ((S ⊓ L2 : Subgroup G) : Set G) :=
  ⟨sup_le (sup_le (CFSG.Quasithin.F1.borelOf_le_normalizer L1 S) (loc_borelOf_le_normalizer_sylow h))
      (CFSG.Quasithin.F1.le_normalizer_inf_of_le h.hyp.h1.normalizes),
    sup_le (sup_le (loc_borelOf_le_normalizer_sylow h.symm)
        (CFSG.Quasithin.F1.borelOf_le_normalizer L2 S))
      (CFSG.Quasithin.F1.le_normalizer_inf_of_le h.hyp.h2.normalizes)⟩

private theorem loc_isSylowTwoOf_bigB_of_normal {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S)
    (hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G)) :
    IsSylowTwoOf S (bigB L1 L2 S) := by
  have hB1B : borelOf L1 S ≤ bigB L1 L2 S := le_sup_left.trans le_sup_left
  have hB2B : borelOf L2 S ≤ bigB L1 L2 S := le_sup_right.trans le_sup_left
  have hSB' : S ≤ bigB L1 L2 S := le_sup_right
  refine isSylowTwoOf_of_relIndex hSB' h.hyp.h1.pgroup ?_
  have hS1 : S ≤ borelOf L1 S ⊔ S := le_sup_right
  have hle : borelOf L1 S ⊔ S ≤ bigB L1 L2 S := sup_le hB1B hSB'
  rw [← Subgroup.relIndex_mul_relIndex S (borelOf L1 S ⊔ S) (bigB L1 L2 S) hS1 hle]
  have hf1 : ¬ 2 ∣ S.relIndex (borelOf L1 S ⊔ S) := by
    rw [CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer (hB1B.trans hSB),
      ← Subgroup.inf_relIndex_right]
    have hinf : S ⊓ borelOf L1 S = S ⊓ L1 :=
      le_antisymm (inf_le_inf_left S (CFSG.Quasithin.F1.borelOf_le L1 S))
        (le_inf inf_le_left (CFSG.Quasithin.F1.sylow_le_borelOf L1 S))
    rw [hinf]
    exact isSylowTwoOf_odd_relIndex
      (isSylowTwoOf_mono_right h.hyp.h1.sylow (CFSG.Quasithin.F1.sylow_le_borelOf L1 S)
        (CFSG.Quasithin.F1.borelOf_le L1 S))
  have hB2N : borelOf L2 S ≤ Subgroup.normalizer ((borelOf L1 S ⊔ S : Subgroup G) : Set G) :=
    CFSG.Quasithin.F1.le_normalizer_sup (loc_borelOf_le_normalizer_borelOf h) (hB2B.trans hSB)
  have hbig : bigB L1 L2 S = borelOf L2 S ⊔ (borelOf L1 S ⊔ S) := by
    simp only [bigB]
    rw [← sup_assoc, sup_comm (borelOf L2 S) (borelOf L1 S)]
  have hf2 : ¬ 2 ∣ (borelOf L1 S ⊔ S).relIndex (bigB L1 L2 S) := by
    rw [hbig, CFSG.Quasithin.F1.relIndex_sup_eq_of_le_normalizer hB2N]
    intro hd
    have hS2 : S ⊓ L2 ≤ borelOf L1 S ⊔ S := inf_le_left.trans le_sup_right
    have hdvd := Subgroup.relIndex_dvd_of_le_left (borelOf L2 S) hS2
    exact (isSylowTwoOf_odd_relIndex
      (isSylowTwoOf_mono_right h.hyp.h2.sylow (CFSG.Quasithin.F1.sylow_le_borelOf L2 S)
        (CFSG.Quasithin.F1.borelOf_le L2 S)))
      (hd.trans hdvd)
  intro hd
  rcases (Nat.Prime.dvd_mul Nat.prime_two).mp hd with hd | hd
  · exact hf1 hd
  · exact hf2 hd

private theorem loc_F110_2 {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S)
    (hcase : (borelOf L1 S ≤ Subgroup.normalizer (S : Set G) ∧
        borelOf L2 S ≤ Subgroup.normalizer (S : Set G)) ∨ S ≤ L1 ∨ S ≤ L2) :
    S = pCoreOf 2 (borelOf L1 S ⊔ borelOf L2 S ⊔ S) ∧
      borelOf L1 S ⊔ borelOf L2 S ⊔ S =
        borelOf L1 S ⊔ borelOf L2 S ⊔ pCoreOf 2 (borelOf L1 S ⊔ borelOf L2 S ⊔ S) := by
  have hSB : bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) := by
    rcases hcase with ⟨h1, h2⟩ | hS | hS
    · exact sup_le (sup_le h1 h2) Subgroup.le_normalizer
    · have := (loc_bigB_le_normalizer_sylow h).1
      rwa [inf_eq_left.mpr hS] at this
    · have := (loc_bigB_le_normalizer_sylow h).2
      rwa [inf_eq_left.mpr hS] at this
  have hsyl := loc_isSylowTwoOf_bigB_of_normal h hSB
  have hO : pCoreOf 2 (borelOf L1 S ⊔ borelOf L2 S ⊔ S) = S :=
    le_antisymm (loc_pCoreOf_le hsyl)
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hsyl.1 hSB h.hyp.h1.pgroup)
  refine ⟨hO.symm, ?_⟩
  rw [hO]

private theorem loc_parabolic_inf_parabolic {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S) :
    (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) = bigB L1 L2 S := by
  have hne : (L1 ⊔ bigB L1 L2 S) ⊓ (L2 ⊔ bigB L1 L2 S) ≠ L1 ⊔ bigB L1 L2 S := by
    intro heq
    have h1 : L1 ⊔ bigB L1 L2 S ≤ L2 ⊔ bigB L1 L2 S := inf_eq_left.mp heq
    have hP2 : L2 ⊔ bigB L1 L2 S ≤ Subgroup.normalizer (L2 : Set G) :=
      sup_le Subgroup.le_normalizer (CFSG.Quasithin.F1.bigB_le_normalizer_left h).2
    have hL1 : L1 ≤ Subgroup.normalizer (L2 : Set G) := le_sup_left.trans (h1.trans hP2)
    have hL1B : L1 ≤ borelOf L1 S := by
      rw [loc_borelOf_eq_normalizer h.symm]
      exact le_inf le_rfl hL1
    exact (CFSG.Quasithin.F1.lt_borelOf h).not_ge hL1B
  rcases CFSG.Quasithin.F1.bigB_maximal_in_parabolic h _ (le_inf le_sup_right le_sup_right)
    inf_le_left with h' | h'
  · exact h'
  · exact absurd h' hne

private theorem loc_rankOneAt {L T : Subgroup G} (hT : IsSylowTwoOf T L)
    (h : IsRankOneSylow (oTwoQuot ↥L)) : RankOneAt L T := by
  set π : ↥L →* oTwoQuot ↥L := QuotientGroup.mk' (pCore 2 ↥L) with hπ
  set T' : Subgroup ↥L := T.subgroupOf L with hT'
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ T' := by
    rw [hπ, QuotientGroup.ker_mk']
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 L := (CFSG.Quasithin.F1.mem_pCore_iff_coe x).mp hx
    exact loc_pCoreOf_le hT h1
  set Tb : Subgroup (oTwoQuot ↥L) := T'.map π with hTb
  have hTb2 : IsPGroup 2 Tb := (hT.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hT.1).symm).map π
  have hTbodd : ¬ 2 ∣ Tb.index := by
    rw [hTb, Subgroup.index_map_eq (f := π) (H := T') hsurj hker]
    exact hT.2.2
  obtain ⟨h1, h2, h3⟩ := h Tb hTb2 hTbodd
  have hmem : ∀ u : ↥L, π u ∈ Tb ↔ u ∈ T' := by
    intro u
    constructor
    · rintro ⟨t, ht, hπt⟩
      have hk : t⁻¹ * u ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπt, inv_mul_cancel]
      have := T'.mul_mem ht (hker hk)
      simpa using this
    · intro hu
      exact ⟨u, hu, rfl⟩
  have hnorm : ∀ u : ↥L, u ∈ Subgroup.normalizer (T' : Set ↥L) ↔
      π u ∈ Subgroup.normalizer (Tb : Set (oTwoQuot ↥L)) := by
    intro u
    rw [Subgroup.mem_normalizer_iff, Subgroup.mem_normalizer_iff]
    constructor
    · intro hu y
      obtain ⟨v, rfl⟩ := hsurj y
      rw [← map_inv, ← map_mul, ← map_mul, hmem, hmem]
      exact hu v
    · intro hu v
      have := hu (π v)
      rwa [← map_inv, ← map_mul, ← map_mul, hmem, hmem] at this
  have hbor : ∀ (g : G) (hg : g ∈ L), (⟨g, hg⟩ : ↥L) ∈ Subgroup.normalizer (T' : Set ↥L) ↔
      g ∈ Subgroup.normalizer (T : Set G) := by
    intro g hg
    have := CFSG.Quasithin.F1.normalizer_subgroupOf_eq (Li := L) (S := T)
    rw [inf_eq_left.mpr hT.1] at this
    rw [show Subgroup.normalizer (T' : Set ↥L) = (borelOf L T).subgroupOf L from this,
      Subgroup.mem_subgroupOf]
    show g ∈ L ⊓ Subgroup.normalizer ((T ⊓ L : Subgroup G) : Set G) ↔ _
    rw [inf_eq_left.mpr hT.1]
    exact ⟨fun h => h.2, fun h => ⟨hg, h⟩⟩
  refine ⟨?_, ?_, ?_⟩
  · intro heq
    apply h1
    rw [eq_top_iff]
    intro k _
    obtain ⟨u, rfl⟩ := hsurj k
    refine (hnorm u).mp ?_
    have hu : (u : G) ∈ L ⊓ Subgroup.normalizer (T : Set G) := by
      rw [heq]
      exact u.2
    exact (hbor u u.2).mpr hu.2
  · intro M hTM hML hMne m hm
    set M' : Subgroup ↥L := M.subgroupOf L with hM'
    have hT'M' : T' ≤ M' := fun t ht => hTM ht
    have hMb : Tb ≤ M'.map π := Subgroup.map_mono hT'M'
    have hMtop : M'.map π ≠ ⊤ := by
      intro htop
      apply hMne
      apply le_antisymm hML
      intro l hl
      have h5 : π ⟨l, hl⟩ ∈ M'.map π := htop ▸ Subgroup.mem_top _
      obtain ⟨u, hu, hπu⟩ := h5
      have hk : u⁻¹ * ⟨l, hl⟩ ∈ π.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hπu, inv_mul_cancel]
      have h8 := M'.mul_mem hu (hT'M' (hker hk))
      have h9 : (⟨l, hl⟩ : ↥L) ∈ M' := by simpa using h8
      exact h9
    have h6 := h2 (M'.map π) hMb hMtop
    have hmL : m ∈ L := hML hm
    have h7 : π ⟨m, hmL⟩ ∈ M'.map π := ⟨⟨m, hmL⟩, hm, rfl⟩
    exact (hbor m hmL).mp ((hnorm _).mpr (h6 h7))
  · intro x hx y hy
    have hxL : x ∈ L := hx.1
    have hyL : y ∈ L := hy.1
    have hx' : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.normalizer (T' : Set ↥L) := (hbor x hxL).mpr hx.2
    have hy' : (⟨y, hyL⟩ : ↥L) ∈ Subgroup.normalizer (T' : Set ↥L) := (hbor y hyL).mpr hy.2
    have h7 := h3 _ ((hnorm _).mp hx') _ ((hnorm _).mp hy')
    rw [← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul, hmem] at h7
    exact h7

private theorem loc_hyp111R_of {L1 L2 S : Subgroup G} (hF : RankOneListedFacts.{0})
    (h : Hyp111 L1 L2 S) : Hyp111R L1 L2 S :=
  ⟨h, loc_rankOneAt h.h1.sylow (hF _ h.h1.listed), loc_rankOneAt h.h2.sylow (hF _ h.h2.listed)⟩

end Loc

@[expose] def F_1_3 : Prop :=
  ∀ (G : Type) [Group G] (L₁ L₂ S : Subgroup G), HypF_1_1 L₁ L₂ S →
    F13Conclusion L₁ L₂ S ∧ F13Conclusion L₂ L₁ S

section LocF13

open CFSG.Quasithin.RonanF13 (F13Setup)

variable {G : Type} [Group G]

private theorem loc_isSolvable_of_isPGroup_two {P : Subgroup G} [Finite ↥P] (hP : IsPGroup 2 ↥P) :
    Group.IsSolvable ↥P := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsNilpotent ↥P := hP.isNilpotent
  infer_instance

private theorem loc_isSolvable_borelOf {Li S : Subgroup G} (hfin : Finite ↥S)
    (hsyl : IsSylowTwoOf (S ⊓ Li) Li) (hR : RankOneAt Li (S ⊓ Li)) :
    Group.IsSolvable (borelOf Li S) := by
  have hfinT : Finite ↥(S ⊓ Li) :=
    Finite.of_injective (fun x : ↥(S ⊓ Li) => (⟨x.1, x.2.1⟩ : ↥S))
      (fun a b hab => Subtype.ext (Subtype.mk.inj hab))
  have hN : ((S ⊓ Li).subgroupOf (borelOf Li S)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.Quasithin.F1.sylow_le_borelOf Li S)).mpr
      (CFSG.Quasithin.F1.borelOf_le_normalizer Li S)
  refine CFSG.Quasithin.F1.isSolvable_of_normal_subgroupOf
    (CFSG.Quasithin.F1.sylow_le_borelOf Li S) (loc_isSolvable_of_isPGroup_two hsyl.2.1) ?_
  refine Group.isSolvable_of_comm fun a b => ?_
  induction a using QuotientGroup.induction_on with
  | H x =>
    induction b using QuotientGroup.induction_on with
    | H y =>
      rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
      rw [Subgroup.mem_subgroupOf]
      have := hR.comm ((y⁻¹ : ↥(borelOf Li S)) : G) (y⁻¹).2 ((x⁻¹ : ↥(borelOf Li S)) : G) (x⁻¹).2
      simpa [mul_assoc] using this

private theorem loc_isSolvable_bigB {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S) :
    Group.IsSolvable (bigB L1 L2 S) := by
  have hfin := h.hyp.h1.finite
  have hB1 := loc_isSolvable_borelOf hfin h.hyp.h1.sylow h.r1
  have hB2 := loc_isSolvable_borelOf hfin h.hyp.h2.sylow h.r2
  have hX : Group.IsSolvable ↥(borelOf L1 S ⊔ borelOf L2 S) :=
    CFSG.Quasithin.F1.isSolvable_sup_of_le_normalizer hB1 hB2 (loc_borelOf_le_normalizer_borelOf h)
  have hS : Group.IsSolvable S := loc_isSolvable_of_isPGroup_two h.hyp.h1.pgroup
  exact CFSG.Quasithin.F1.isSolvable_sup_of_le_normalizer hX hS
    (CFSG.Quasithin.F1.le_normalizer_sup
      (CFSG.Quasithin.F1.le_normalizer_borelOf h.hyp.h1.normalizes)
      (CFSG.Quasithin.F1.le_normalizer_borelOf h.hyp.h2.normalizes))

private theorem loc_bigB_eq_inf_normalizer {Li Lj S : Subgroup G} (h : Hyp111R Li Lj S) :
    bigB Li Lj S =
      (Li ⊔ S ⊔ borelOf Lj S) ⊓ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) := by
  have hi := h.hyp.h1
  have hXB : S ⊔ borelOf Lj S ≤ bigB Li Lj S :=
    sup_le le_sup_right (le_sup_right.trans le_sup_left)
  apply le_antisymm
  · refine le_inf ?_ (loc_bigB_le_normalizer_sylow h).1
    exact sup_le (sup_le ((CFSG.Quasithin.F1.borelOf_le Li S).trans (le_sup_left.trans le_sup_left))
      (le_sup_right (a := Li ⊔ S) (b := borelOf Lj S))) (le_sup_right.trans le_sup_left)
  · intro x hx
    obtain ⟨hxP, hxN⟩ := Subgroup.mem_inf.mp hx
    have hX : S ⊔ borelOf Lj S ≤ Subgroup.normalizer (Li : Set G) :=
      sup_le hi.normalizes hi.borel_le
    rw [sup_assoc, CFSG.Quasithin.F1.mem_sup_iff_exists_mul_of_normalizes hX] at hxP
    obtain ⟨a, ha, b, hb, rfl⟩ := hxP
    have hbB : b ∈ bigB Li Lj S := hXB hb
    have hbN : b ∈ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) :=
      (loc_bigB_le_normalizer_sylow h).1 hbB
    have haN : a ∈ Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G) := by
      have := (Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G)).mul_mem hxN
        ((Subgroup.normalizer ((S ⊓ Li : Subgroup G) : Set G)).inv_mem hbN)
      simpa using this
    have haB : a ∈ bigB Li Lj S :=
      (le_sup_left.trans le_sup_left : borelOf Li S ≤ bigB Li Lj S) ⟨ha, haN⟩
    exact (bigB Li Lj S).mul_mem haB hbB

private theorem loc_map_borelOf_eq_normalizer {Li S : Subgroup G}
    (hsyl : IsSylowTwoOf (S ⊓ Li) Li) :
    IsPGroup 2 (((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li))) ∧
      ¬ 2 ∣ (((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li))).index ∧
      ((borelOf Li S).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li)) =
        Subgroup.normalizer
          ((((S ⊓ Li).subgroupOf Li).map (QuotientGroup.mk' (pCore 2 ↥Li)) :
            Subgroup (oTwoQuot ↥Li)) : Set (oTwoQuot ↥Li)) := by
  set π : ↥Li →* oTwoQuot ↥Li := QuotientGroup.mk' (pCore 2 ↥Li) with hπ
  set T : Subgroup ↥Li := (S ⊓ Li).subgroupOf Li with hT
  have hsurj : Function.Surjective π := QuotientGroup.mk'_surjective _
  have hker : π.ker ≤ T := by
    rw [hπ, QuotientGroup.ker_mk']
    intro x hx
    have h1 : (x : G) ∈ pCoreOf 2 Li := (CFSG.Quasithin.F1.mem_pCore_iff_coe x).mp hx
    exact loc_pCoreOf_le hsyl h1
  refine ⟨?_, ?_, ?_⟩
  · exact (hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hsyl.1).symm).map π
  · rw [Subgroup.index_map_eq (f := π) (H := T) hsurj hker]
    exact hsyl.2.2
  · rw [← CFSG.Quasithin.F1.normalizer_subgroupOf_eq]
    have h1 : (Subgroup.normalizer ((T.map π : Subgroup (oTwoQuot ↥Li)) :
        Set (oTwoQuot ↥Li))).comap π = Subgroup.normalizer T := by
      rw [Subgroup.comap_normalizer_eq_of_surjective _ hsurj, Subgroup.comap_map_eq_self hker]
    conv_rhs => rw [← Subgroup.map_comap_eq_self_of_surjective hsurj
      (Subgroup.normalizer ((T.map π : Subgroup (oTwoQuot ↥Li)) : Set (oTwoQuot ↥Li))), h1]

private theorem loc_finite_of_hyp {Li Lj S : Subgroup G} (h : Hyp111At Li Lj S) : Finite ↥Li := by
  have hq : Finite (oTwoQuot ↥Li) := h.listed.finite
  have hS := h.finite
  have hN : Finite ↥(pCore 2 ↥Li) := by
    refine Finite.of_injective
      (fun x : ↥(pCore 2 ↥Li) => (⟨((x : ↥Li) : G),
        (inf_le_left : S ⊓ Li ≤ S) (loc_pCoreOf_le h.sylow
          ((CFSG.Quasithin.F1.mem_pCore_iff_coe (x : ↥Li)).mp x.2))⟩ : ↥S))
      (fun a b hab => Subtype.ext (Subtype.ext (Subtype.mk.inj hab)))
  exact Finite.of_equiv _ (Subgroup.groupEquivQuotientProdSubgroup (s := pCore 2 ↥Li)).symm

private theorem loc_f13Setup {L1 L2 S : Subgroup G} (h : Hyp111R L1 L2 S) : F13Setup L1 L2 S where
  finS := h.hyp.h1.finite
  pS := h.hyp.h1.pgroup
  finL1 := loc_finite_of_hyp h.hyp.h1
  finL2 := loc_finite_of_hyp h.hyp.h2
  syl1 := h.hyp.h1.sylow
  syl2 := h.hyp.h2.sylow
  comm1 := fun x hx y hy => h.r1.comm x hx y hy
  comm2 := fun x hx y hy => h.r2.comm x hx y hy
  b2_le_nL1 := h.hyp.h1.borel_le
  b1_le_nL2 := h.hyp.h2.borel_le
  pcore1 := loc_pCoreOf_le h.hyp.h1.sylow
  pcore2 := loc_pCoreOf_le h.hyp.h2.sylow
  b2_le_nb1 := loc_borelOf_le_normalizer_borelOf h
  b1_le_nb2 := loc_borelOf_le_normalizer_borelOf h.symm
  s_le_nb1 := CFSG.Quasithin.F1.le_normalizer_borelOf h.hyp.h1.normalizes
  s_le_nb2 := CFSG.Quasithin.F1.le_normalizer_borelOf h.hyp.h2.normalizes
  bigB_le_ns1 := (loc_bigB_le_normalizer_sylow h).1
  bigB_le_ns2 := (loc_bigB_le_normalizer_sylow h).2
  solvable := loc_isSolvable_bigB h

private theorem loc_le_normalizer_of_commute {A B : Subgroup G}
    (h : ∀ x ∈ A, ∀ y ∈ B, x * y = y * x) : A ≤ Subgroup.normalizer (B : Set G) := by
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · intro hy
    have h1 := h a ha y hy
    have : a * y * a⁻¹ = y := by rw [h1]; group
    rw [this]
    exact hy
  · intro hay
    have h1 := h a⁻¹ (A.inv_mem ha) _ hay
    have h2 : y = a⁻¹ * (a * y * a⁻¹) * a := by group
    have h3 : a⁻¹ * (a * y * a⁻¹) = (a * y * a⁻¹) * a⁻¹ := h1
    have h4 : y = a * y * a⁻¹ := by
      calc y = a⁻¹ * (a * y * a⁻¹) * a := h2
        _ = (a * y * a⁻¹) * a⁻¹ * a := by rw [h3]
        _ = a * y * a⁻¹ := by group
    rw [h4]
    exact hay

private theorem loc_f13_of_part5 {Li Lj S : Subgroup G} (h : Hyp111R Li Lj S)
    (h5 : ∃ Di Dj : Subgroup G, IsHallTwoPrime Di (borelOf Li S) ∧
      IsHallTwoPrime Dj (borelOf Lj S) ∧
      borelOf Li S = (S ⊓ Li) ⊔ Di ∧ borelOf Lj S = (S ⊓ Lj) ⊔ Dj ∧
      Di ≤ Subgroup.normalizer (Dj : Set G) ∧
      borelOf Li S ⊔ borelOf Lj S ⊔ S = S ⊔ Di ⊔ Dj ∧
      (∀ x ∈ Di ⊔ Dj, ∀ y ∈ Di ⊔ Dj, x * y = y * x) ∧
      IsHallTwoPrime (Di ⊔ Dj) (borelOf Li S ⊔ borelOf Lj S ⊔ S)) :
    F13Conclusion Li Lj S := by
  obtain ⟨hmapP, hmapI, hmapE⟩ := loc_map_borelOf_eq_normalizer h.hyp.h1.sylow
  refine ⟨⟨⟨h.r1.borel_ne, CFSG.Quasithin.F1.sylow_le_borelOf Li S, fun M hSM hML hMne =>
      le_inf hML (h.r1.unique_max M hSM hML hMne)⟩, hmapE, ⟨hmapP, hmapI⟩,
      loc_pCoreOf_borelOf h.hyp.h1.sylow⟩,
    loc_borelOf_eq_normalizer h,
    ⟨loc_borelOf_le_normalizer_borelOf h, loc_borelOf_le_normalizer_sylow h⟩,
    ⟨loc_bigB_eq_inf_normalizer h, loc_isSolvable_bigB h⟩, h5,
    loc_parabolic_inf_parabolic h⟩

end LocF13

section CertF13


open CFSG.Quasithin.RonanF13 (core5 rankOneTwist_of_listed)

private theorem f13_main : F_1_3 := by
  intro G _ L₁ L₂ S h
  have hR : Hyp111R L₁ L₂ S := loc_hyp111R_of rankOneListedFacts h
  have hset := loc_f13Setup hR
  have hT1 := rankOneTwist_of_listed h.h1.listed
  have hT2 := rankOneTwist_of_listed h.h2.listed
  obtain ⟨D1, D2, hD1, hD2, hE1, hE2, hcomm, hBE, hHall, hab⟩ := core5 hset hT1 hT2
  have hcomm' : ∀ x ∈ D2, ∀ y ∈ D1, x * y = y * x := fun x hx y hy => (hcomm y hy x hx).symm
  refine ⟨loc_f13_of_part5 hR ⟨D1, D2, hD1, hD2, hE1, hE2, loc_le_normalizer_of_commute hcomm,
      hBE, hab, hHall⟩, loc_f13_of_part5 hR.symm ⟨D2, D1, hD2, hD1, hE2, hE1,
      loc_le_normalizer_of_commute hcomm', ?_, ?_, ?_⟩⟩
  · rw [sup_comm (borelOf L₂ S) (borelOf L₁ S), hBE]
    exact sup_right_comm S D1 D2
  · rw [sup_comm D2 D1]
    exact hab
  · rw [sup_comm D2 D1, sup_comm (borelOf L₂ S) (borelOf L₁ S)]
    exact hHall

end CertF13

section CertF13Main


theorem as_F_1_3 : F_1_3 := by
  exact f13_main

end CertF13Main

@[expose] def F_1_5_hypothesis : Prop :=
  ∀ (G : Type) [Group G] (L₁ L₂ S : Subgroup G), HypF_1_1 L₁ L₂ S →
    (L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊓ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) =
      borelOf L₁ S ⊔ borelOf L₂ S ⊔ S ∧
    (RankTwoAmalgam.ofSubgroups (L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))
        (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))).IsInjective

@[expose] def F_1_5 : Prop :=
  (∀ (G : Type) [Group G] (P₁ P₂ : Subgroup G),
    (RankTwoAmalgam.ofSubgroups P₁ P₂).IsInjective) ∧ F_1_5_hypothesis

section CertF15

theorem as_F_1_5 : F_1_5 := by
  unfold F_1_5 F_1_5_hypothesis
  refine ⟨fun G _ P₁ P₂ => RankTwoAmalgam.ofSubgroups_isInjective P₁ P₂, ?_⟩
  intro G _ L₁ L₂ S h
  exact ⟨loc_parabolic_inf_parabolic (loc_hyp111R_of rankOneListedFacts h),
    RankTwoAmalgam.ofSubgroups_isInjective _ _⟩

end CertF15

@[expose] def F_1_6 : Prop :=
  (∀ (G : Type) [Group G] (P₁ P₂ : Subgroup G),
    ∃ c : (RankTwoAmalgam.ofSubgroups P₁ P₂).Completion ↥(P₁ ⊔ P₂), c.IsFaithful ∧
      (∀ g : ↥P₁, ((c.φ1 g : ↥(P₁ ⊔ P₂)) : G) = (g : G)) ∧
      (∀ g : ↥(P₁ ⊓ P₂), ((c.φ12 g : ↥(P₁ ⊔ P₂)) : G) = (g : G)) ∧
      (∀ g : ↥P₂, ((c.φ2 g : ↥(P₁ ⊔ P₂)) : G) = (g : G))) ∧
  (∀ (G : Type) [Group G] (L₁ L₂ S : Subgroup G), HypF_1_1 L₁ L₂ S →
    (L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) = L₁ ⊔ L₂ ⊔ S ∧
    ∃ c : (RankTwoAmalgam.ofSubgroups (L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))
          (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))).Completion
        ↥((L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))),
      c.IsFaithful ∧
      (∀ g : ↥(L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)),
        ((c.φ1 g : ↥((L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)))) : G) =
          (g : G)) ∧
      (∀ g : ↥((L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊓ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))),
        ((c.φ12 g : ↥((L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)))) : G) =
          (g : G)) ∧
      (∀ g : ↥(L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)),
        ((c.φ2 g : ↥((L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)))) : G) =
          (g : G))) ∧
  (∀ (α : RankTwoAmalgam.{0}) (Y : Type) [Group Y] (c : α.Completion Y),
    Function.Surjective (Amalgam.Completion.hat c.toCompletion) ∧
    ∀ (d : RankTwoIndex) (x : α.X d),
      Amalgam.Completion.hat c.toCompletion (Amalgam.ξ α.toAmalgam d x) = c.homFamily d x)

private theorem f16_parabolic_sup {G : Type} [Group G] (L₁ L₂ S : Subgroup G) :
    (L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) =
      L₁ ⊔ L₂ ⊔ S := by
  have hB1 : borelOf L₁ S ≤ L₁ ⊔ L₂ ⊔ S := inf_le_left.trans (le_sup_left.trans le_sup_left)
  have hB2 : borelOf L₂ S ≤ L₁ ⊔ L₂ ⊔ S := inf_le_left.trans (le_sup_right.trans le_sup_left)
  have hB : borelOf L₁ S ⊔ borelOf L₂ S ⊔ S ≤ L₁ ⊔ L₂ ⊔ S := sup_le (sup_le hB1 hB2) le_sup_right
  apply le_antisymm
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) hB)
      (sup_le (le_sup_right.trans le_sup_left) hB)
  · exact sup_le (sup_le (le_sup_left.trans le_sup_left) (le_sup_left.trans le_sup_right))
      ((le_sup_right.trans (le_sup_right.trans le_sup_left)))

theorem as_F_1_6 : F_1_6 := by
  unfold F_1_6
  refine ⟨fun G _ P₁ P₂ => ?_, fun G _ L₁ L₂ S _ => ?_, fun α Y _ c => ?_⟩
  · exact ⟨RankTwoAmalgam.inclusionCompletion P₁ P₂ (P₁ ⊔ P₂) rfl,
      RankTwoAmalgam.inclusionCompletion_isFaithful P₁ P₂ (P₁ ⊔ P₂) rfl,
      fun _ => rfl, fun _ => rfl, fun _ => rfl⟩
  · refine ⟨f16_parabolic_sup L₁ L₂ S,
      RankTwoAmalgam.inclusionCompletion (L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))
        (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))
        ((L₁ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)) ⊔ (L₂ ⊔ (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S))) rfl,
      ?_⟩
    exact ⟨RankTwoAmalgam.inclusionCompletion_isFaithful _ _ _ rfl, fun _ => rfl, fun _ => rfl,
      fun _ => rfl⟩
  · exact ⟨Amalgam.Completion.hat_surjective c.toCompletion,
      fun d x => Amalgam.Completion.hat_ξ c.toCompletion d x⟩

@[expose] def F_1_10 : Prop :=
  ∀ (G : Type) [Group G] (L₁ L₂ S : Subgroup G), HypF_1_1 L₁ L₂ S →
    ((S = pCoreOf 2 (L₁ ⊔ S) ⊔ (S ⊓ L₁) → S = pCoreOf 2 (L₂ ⊔ S) ⊔ (S ⊓ L₂) →
        borelOf L₁ S ≤ Subgroup.normalizer (S : Set G) ∧ borelOf L₂ S ≤ Subgroup.normalizer (S : Set G)) ∧
    (((borelOf L₁ S ≤ Subgroup.normalizer (S : Set G) ∧ borelOf L₂ S ≤ Subgroup.normalizer (S : Set G)) ∨
        S ≤ L₁ ∨ S ≤ L₂) →
      S = pCoreOf 2 (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S) ∧
      borelOf L₁ S ⊔ borelOf L₂ S ⊔ S =
        borelOf L₁ S ⊔ borelOf L₂ S ⊔ pCoreOf 2 (borelOf L₁ S ⊔ borelOf L₂ S ⊔ S)))

section CertF10

theorem as_F_1_10 : F_1_10 := by
  unfold F_1_10
  intro G _ L₁ L₂ S hyp
  have hR : Hyp111R L₁ L₂ S := loc_hyp111R_of rankOneListedFacts hyp
  exact ⟨fun h1 h2 => ⟨CFSG.Quasithin.F1.borelOf_le_normalizer_of_eq h1,
      CFSG.Quasithin.F1.borelOf_le_normalizer_of_eq h2⟩,
    fun hcase => loc_F110_2 hR hcase⟩

end CertF10

@[expose] def F_1_11 : Prop :=
  (∀ α β : RankTwoAmalgam.{0}, Nonempty (α.Iso β) → α.ParabolicIso β) ∧
  (∃ α β : RankTwoAmalgam.{0}, α.IsInjective ∧ β.IsInjective ∧ α.ParabolicIso β ∧ ¬ Nonempty (α.Iso β))

private def f11_emb : DihedralGroup 2 →* DihedralGroup 4 where
  toFun x := match x with
    | .r i => .r (2 * ((i.val : ℕ) : ZMod 4))
    | .sr i => .sr (2 * ((i.val : ℕ) : ZMod 4))
  map_one' := by decide
  map_mul' := by decide

private def f11_sig : DihedralGroup 2 →* DihedralGroup 2 where
  toFun x := if x = .r 1 then .sr 0 else if x = .sr 0 then .r 1 else x
  map_one' := by decide
  map_mul' := by decide

private theorem f11_centre (φ : DihedralGroup 4 ≃* DihedralGroup 4) : φ (.r 2) = .r 2 := by
  have hcomm : ∀ w : DihedralGroup 4,
      (DihedralGroup.r 2 : DihedralGroup 4) * w = w * DihedralGroup.r 2 := by decide
  have hc : ∀ y : DihedralGroup 4, φ (.r 2) * y = y * φ (.r 2) := by
    intro y
    obtain ⟨w, rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, hcomm w]
  have hcls : ∀ x : DihedralGroup 4,
      (∀ y : DihedralGroup 4, x * y = y * x) → x = 1 ∨ x = .r 2 := by decide
  rcases hcls _ hc with h | h
  · exfalso
    have h1 : (DihedralGroup.r 2 : DihedralGroup 4) = 1 := by
      apply φ.injective
      rw [h, map_one]
    revert h1
    decide
  · exact h

private theorem f11_emb_r1 : f11_emb (.r 1) = .r 2 := by decide

private theorem f11_emb_inj : ∀ x : DihedralGroup 2, f11_emb x = .r 2 → x = .r 1 := by decide

private def f11_alpha : RankTwoAmalgam.{0} where
  G1 := DihedralGroup 4
  G12 := DihedralGroup 2
  G2 := DihedralGroup 4
  α1 := f11_emb
  α2 := f11_emb

private def f11_beta : RankTwoAmalgam.{0} where
  G1 := DihedralGroup 4
  G12 := DihedralGroup 2
  G2 := DihedralGroup 4
  α1 := f11_emb
  α2 := f11_emb.comp f11_sig

private theorem f11_emb_injective : Function.Injective f11_emb := by
  have key : ∀ a b : DihedralGroup 2, f11_emb a = f11_emb b → a = b := by decide
  exact key

private theorem f11_sig_injective : Function.Injective f11_sig := by
  have key : ∀ a b : DihedralGroup 2, f11_sig a = f11_sig b → a = b := by decide
  exact key

private theorem f11_alpha_injective : f11_alpha.IsInjective := by
  unfold RankTwoAmalgam.IsInjective
  exact ⟨f11_emb_injective, f11_emb_injective⟩

private theorem f11_beta_injective : f11_beta.IsInjective := by
  unfold RankTwoAmalgam.IsInjective
  exact ⟨f11_emb_injective, f11_emb_injective.comp f11_sig_injective⟩

private theorem f11_parabolic : f11_alpha.ParabolicIso f11_beta := by
  unfold RankTwoAmalgam.ParabolicIso
  exact ⟨⟨MulEquiv.refl _⟩, ⟨MulEquiv.refl _⟩, ⟨MulEquiv.refl _⟩⟩

private theorem f11_not_iso : ¬ Nonempty (f11_alpha.Iso f11_beta) := by
  rintro ⟨e⟩
  have hc1 : e.φ1 (DihedralGroup.r 2) = DihedralGroup.r 2 := f11_centre e.φ1
  have hc2 : e.φ2 (DihedralGroup.r 2) = DihedralGroup.r 2 := f11_centre e.φ2
  have h1 : f11_emb (e.φ12 (DihedralGroup.r 1)) = e.φ1 (f11_emb (DihedralGroup.r 1)) :=
    e.comm1 (DihedralGroup.r 1)
  rw [f11_emb_r1, hc1] at h1
  have h2 : e.φ12 (DihedralGroup.r 1) = DihedralGroup.r 1 := f11_emb_inj _ h1
  have h3 : (f11_emb.comp f11_sig) (e.φ12 (DihedralGroup.r 1)) =
      e.φ2 (f11_emb (DihedralGroup.r 1)) := e.comm2 (DihedralGroup.r 1)
  rw [h2, f11_emb_r1, hc2] at h3
  have h4 : f11_emb (f11_sig (DihedralGroup.r 1)) = DihedralGroup.r 2 := h3
  have h5 : f11_sig (DihedralGroup.r 1) = DihedralGroup.sr 0 := by decide
  rw [h5] at h4
  revert h4
  decide

theorem as_F_1_11 : F_1_11 := by
  unfold F_1_11
  exact ⟨fun α β ⟨e⟩ => e.parabolicIso,
    ⟨f11_alpha, f11_beta, f11_alpha_injective, f11_beta_injective, f11_parabolic, f11_not_iso⟩⟩

end CFSG.ASVolI

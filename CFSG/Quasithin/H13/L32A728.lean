module

public import CFSG.Quasithin.H13.L32ASk1
public import CFSG.Quasithin.H13.L32ASk7
public import CFSG.Quasithin.H13.L32A706f
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.OddNormalizerOrderThreeCentralizes

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

theorem normal_map_of_characteristic {X : Type*} [Group X] {N : Subgroup X} [N.Normal]
    (K : Subgroup ↥N) [hK : K.Characteristic] : (K.map N.subtype).Normal := by
  constructor
  rintro _ ⟨k, hk, rfl⟩ g
  have hfix := hK.fixed (MulAut.conjNormal g)
  have hk' : k ∈ K.comap (MulAut.conjNormal g).toMonoidHom := by rw [hfix]; exact hk
  exact ⟨_, hk', MulAut.conjNormal_apply g k⟩

theorem oddCore_eq_pCore_three {X : Type} [Group X] [Finite X]
    (hF : IsPGroup 3 ↥(CFSG.fittingSubgroup X)) (hP : Nat.card ↥(CFSG.pCore 3 X) ∣ 3) :
    CFSG.oddCore X = CFSG.pCore 3 X := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set O := CFSG.oddCore X with hO
  set P := CFSG.pCore 3 X with hPdef
  have hPp : IsPGroup 3 ↥P := CFSG.pCore_isPGroup
  have hPO : P ≤ O := by
    refine le_sSup ⟨CFSG.pCore_normal, ?_⟩
    obtain ⟨k, hk⟩ := hPp.exists_card_eq
    rw [hk]
    exact Odd.pow (by decide)
  have hOn : O.Normal := CFSG.oddCore_normal X
  have hOodd : Odd (Nat.card ↥O) := CFSG.Quasithin.A312.odd_card_oddCore X
  have hOs : Group.IsSolvable ↥O := CFSG.Quasithin.A312.oddCore_isSolvable X
  set FO := CFSG.fittingSubgroup ↥O with hFO
  have hFOn : (FO.map O.subtype).Normal := normal_map_of_characteristic FO
  have hFOnil : Group.IsNilpotent ↥(FO.map O.subtype) :=
    Group.nilpotent_of_mulEquiv (FO.equivMapOfInjective O.subtype O.subtype_injective)
  have hFOF : FO.map O.subtype ≤ CFSG.fittingSubgroup X := le_sSup ⟨hFOn, hFOnil⟩
  have hFOP : FO.map O.subtype ≤ P :=
    le_sSup ⟨hFOn, hF.to_le hFOF⟩
  have hcent : O ≤ Subgroup.centralizer (P : Set X) := by
    rcases (Nat.dvd_prime Nat.prime_three).mp hP with h1 | h3
    · intro o _
      rw [Subgroup.mem_centralizer_iff]
      intro p hp
      have : p = 1 := by
        have := (Subgroup.card_eq_one.mp h1)
        rw [this] at hp
        exact (Subgroup.mem_bot.mp hp)
      rw [this, one_mul, mul_one]
    · exact CFSG.GorensteinWalter.odd_subgroup_le_centralizer_of_le_normalizer_card_three O P
        hOodd h3 (fun o _ => by
          rw [Subgroup.normalizer_eq_top (H := P)]
          exact Subgroup.mem_top o)
  have hCF := CFSG.centralizer_fittingSubgroup_le_fittingSubgroup_of_solvable hOs
  refine le_antisymm (fun o ho => ?_) hPO
  have hoC : (⟨o, ho⟩ : ↥O) ∈ Subgroup.centralizer (FO : Set ↥O) := by
    rw [Subgroup.mem_centralizer_iff]
    intro f hf
    apply Subtype.ext
    have hfP : (f : X) ∈ P := hFOP ⟨f, hf, rfl⟩
    exact Subgroup.mem_centralizer_iff.mp (hcent ho) _ hfP
  exact hFOP ⟨_, hCF hoC, rfl⟩

theorem card_dvd_three_of_isPGroup {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}
    (S : Setting147 G T L V H) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h3 : IsPGroup 3 ↥(modO2Image H (l1 T L V))) :
    Nat.card ↥(modO2Image H (l1 T L V)) ∣ 3 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨k, hk⟩ := h3.exists_card_eq
  have hl1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hdvd : Nat.card ↥(modO2Image H (l1 T L V)) ∣ Nat.card ↥(l1 T L V) := by
    have h1 := Subgroup.card_map_dvd ((l1 T L V).subgroupOf H)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H))
    rwa [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hl1H).toEquiv] at h1
  have hidx := (M76.relIndex_l1_T S h1222 h1332 h1334).1
  have hcard : Nat.card ↥(l1 T L V) = Nat.card ↥(pCoreOf 2 (l1 T L V)) * 3 := by
    have h1 := Subgroup.relIndex_mul_card (H := pCoreOf 2 (l1 T L V)) (K := l1 T L V)
    rw [inf_eq_left.mpr (pCoreOf_le 2 (l1 T L V)), hidx] at h1
    rw [← h1, mul_comm]
  obtain ⟨a, ha⟩ := (pCoreOf_isPGroup 2 (l1 T L V)).exists_card_eq
  rw [hcard, ha, hk] at hdvd
  rw [hk]
  have hcop : Nat.Coprime (3 ^ k) (2 ^ a) := Nat.Coprime.pow k a (by decide)
  exact hcop.dvd_of_dvd_mul_left hdvd

theorem lemma14_7_28_of (h27 : Lemma14_7_27) (h76 : Lemma14_7_6) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) : Lemma14_7_28 := by
  intro G _ _ T L V H S
  have hF := h76 G T L V H S
  have hP : Nat.card ↥(CFSG.pCore 3 (↥H ⧸ CFSG.pCore 2 ↥H)) ∣ 3 := by
    rcases h27 G T L V H S with h | h
    · rw [h, Subgroup.card_bot]
      exact one_dvd 3
    · have h3 : IsPGroup 3 ↥(modO2Image H (l1 T L V)) := by
        rw [← h]
        exact CFSG.pCore_isPGroup
      rw [h]
      exact card_dvd_three_of_isPGroup S h1222 h1332 h1334 h3
  rw [oddCore_eq_pCore_three hF hP]
  exact h27 G T L V H S

end CFSG.Quasithin.H13.L32A

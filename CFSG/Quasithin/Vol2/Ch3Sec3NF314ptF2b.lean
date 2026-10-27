module

public import CFSG.Quasithin.Vol2.Ch3Sec3NF314ptSyl
public import CFSG.Monster.B.TwoA.Census.PermClasses
public import CFSG.Quasithin.Background.F1Models
public import CFSG.Quasithin.Vol2.Ch1Local

public section

namespace CFSG.Quasithin.H13.NF314pt

open CFSG.Open
open scoped commutatorElement

theorem f2_mem_pCore_iff {G : Type} [Group G] {K : Subgroup G} (y : ↥K) :
    y ∈ CFSG.pCore 2 ↥K ↔ (y : G) ∈ pCoreOf 2 K :=
  (Subgroup.mem_map_iff_mem K.subtype_injective).symm

theorem f2_mem_cComp_of_le {G : Type} [Group G] {X Y B : Subgroup G}
    (hB : B ∈ CFSG.Quasithin.cComp X) (hBY : B ≤ Y) (hYX : Y ≤ X) :
    B ∈ CFSG.Quasithin.cComp Y := by
  obtain ⟨hne, hperf, hsub, hmin⟩ := hB
  show CFSG.Open.quasithinIsCComponent B Y
  unfold CFSG.Open.quasithinIsCComponent
  refine ⟨hne, hperf, ?_, ?_⟩
  · have h := CFSG.Open.IsSubnormal.inf_of_le hsub hYX
    rwa [inf_eq_left.2 hBY] at h
  · intro K' hlt hK'ne hK'perf hK'Y
    have h1 := CFSG.Open.IsSubnormal.inf_of_le hK'Y hBY
    rw [inf_eq_left.2 hlt.le] at h1
    exact hmin K' hlt hK'ne hK'perf (CFSG.Open.IsSubnormal.trans h1 hsub)

theorem f2_center_mod {G : Type} [Group G] [Finite G] {H K : Subgroup G} (hKH : K ≤ H)
    (hK2 : pCoreOf 2 K ≤ pCoreOf 2 H)
    (hsimp : IsSimpleGroup (↥K ⧸ CFSG.pCore 2 ↥K))
    (hnab : ∃ a b : ↥K ⧸ CFSG.pCore 2 ↥K, a * b ≠ b * a) :
    ∀ a ∈ K, (∀ x ∈ K, ⁅a, x⁆ ∈ pCoreOf 2 H) → a ∈ pCoreOf 2 H := by
  intro a ha hcomm
  have hQK : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
    refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 H).to_le inf_le_right)
    intro k hk
    have hnk := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H (hKH hk)
    rw [Subgroup.mem_normalizer_iff] at hnk ⊢
    intro y
    constructor
    · intro hy
      obtain ⟨hyK, hyQ⟩ := Subgroup.mem_inf.1 hy
      exact Subgroup.mem_inf.2 ⟨K.mul_mem (K.mul_mem hk hyK) (K.inv_mem hk), (hnk y).1 hyQ⟩
    · intro hy
      obtain ⟨hkyK, hkyQ⟩ := Subgroup.mem_inf.1 hy
      have hyK : y ∈ K := by
        have e : k⁻¹ * (k * y * k⁻¹) * k = y := by group
        have h := K.mul_mem (K.mul_mem (K.inv_mem hk) hkyK) hk
        rwa [e] at h
      exact Subgroup.mem_inf.2 ⟨hyK, (hnk y).2 hkyQ⟩
  have hcomK : ∀ y : ↥K, ⁅(⟨a, ha⟩ : ↥K), y⁆ ∈ CFSG.pCore 2 ↥K := by
    intro y
    rw [f2_mem_pCore_iff]
    show ⁅a, (y : G)⁆ ∈ pCoreOf 2 K
    have hmem : ⁅a, (y : G)⁆ ∈ K ⊓ pCoreOf 2 H := by
      refine Subgroup.mem_inf.2 ⟨?_, hcomm _ y.2⟩
      rw [commutatorElement_def]
      exact K.mul_mem (K.mul_mem (K.mul_mem ha y.2) (K.inv_mem ha)) (K.inv_mem y.2)
    exact hQK hmem
  have hcentre : ((⟨a, ha⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K) ∈
      Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
    rw [Subgroup.mem_center_iff]
    intro g
    obtain ⟨y, rfl⟩ := QuotientGroup.mk_surjective g
    have key : ⁅((⟨a, ha⟩ : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K), ((y : ↥K) : ↥K ⧸ CFSG.pCore 2 ↥K)⁆
        = 1 := by
      have h := map_commutatorElement (QuotientGroup.mk' (CFSG.pCore 2 ↥K)) (⟨a, ha⟩ : ↥K) y
      simp only [QuotientGroup.mk'_apply] at h
      rw [← h, QuotientGroup.eq_one_iff]
      exact hcomK y
    exact (commutatorElement_eq_one_iff_mul_comm.1 key).symm
  haveI := hsimp
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
      (Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K)) with hbot | htop
  · rw [hbot, Subgroup.mem_bot, QuotientGroup.eq_one_iff] at hcentre
    exact hK2 ((f2_mem_pCore_iff ⟨a, ha⟩).1 hcentre)
  · exfalso
    obtain ⟨u, v, huv⟩ := hnab
    have hu : u ∈ Subgroup.center (↥K ⧸ CFSG.pCore 2 ↥K) := by
      rw [htop]
      exact Subgroup.mem_top u
    exact huv (Subgroup.mem_center_iff.1 hu v).symm

theorem f2_isLocal_TL {G : Type} [Group G] [Finite G] {T TL K₀ B : Subgroup G} {e : G}
    (hT : CFSG.Open.quasithinIsSylowTwo T) (hTL : TL ≤ T)
    (hTL' : T ⊓ Subgroup.centralizer ({e} : Set G) = TL)
    (heT : e ∈ T) (he1 : e ≠ 1) (he2 : e ^ 2 = 1)
    (hK₀e : K₀ ≤ Subgroup.centralizer ({e} : Set G))
    (hTN : T ≤ Subgroup.normalizer (K₀ : Set G)) (hBK₀ : B ≤ K₀)
    (hB : B ∈ CFSG.Quasithin.cComp (B ⊔ T)) :
    CFSG.Open.quasithinIsLocal TL B := by
  have hTL2 : IsPGroup 2 ↥TL := IsPGroup.to_le hT.1 hTL
  have hTsyl : CFSG.QuasithinUnique.IsSylowTwoOf T (K₀ ⊔ T) :=
    CFSG.Quasithin.isSylowTwoOf_of_quasithinIsSylowTwo hT le_sup_right
  have hTK₀ : CFSG.QuasithinUnique.IsSylowTwoOf (T ⊓ K₀) K₀ :=
    CFSG.Quasithin.A4.isSylowTwoOf_inf_normal hTsyl le_sup_left
      (sup_le Subgroup.le_normalizer hTN)
  have hTLC : TL ≤ Subgroup.centralizer ({e} : Set G) := by
    rw [← hTL']
    exact inf_le_right
  have hSTL : T ⊓ K₀ ≤ TL := by
    intro x hx
    rw [← hTL']
    exact Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hx).1, hK₀e (Subgroup.mem_inf.1 hx).2⟩
  have hTLN : TL ≤ Subgroup.normalizer (K₀ : Set G) := hTL.trans hTN
  have hTLsyl : CFSG.QuasithinUnique.IsSylowTwoOf TL (K₀ ⊔ TL) :=
    CFSG.Quasithin.H13.NF314pt.isSylowTwoOf_sup_of_normalizer hTL2 hTLN hTK₀ hSTL
  have hTLsyl' : CFSG.QuasithinUnique.IsSylowTwoOf TL (B ⊔ TL) :=
    CFSG.Quasithin.A4.isSylowTwoOf_mono hTLsyl le_sup_right (sup_le_sup_right hBK₀ TL)
  have hBTL : B ∈ CFSG.Quasithin.cComp (B ⊔ TL) :=
    f2_mem_cComp_of_le hB le_sup_left (sup_le_sup_left hTL B)
  have he_cent : e ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_centralizer_iff.2 fun h hh => by rw [Set.mem_singleton_iff.1 hh]
  have heTL : e ∈ TL := by
    rw [← hTL']
    exact Subgroup.mem_inf.2 ⟨heT, he_cent⟩
  have hBC : B ⊔ TL ≤ Subgroup.centralizer ({e} : Set G) :=
    sup_le (hBK₀.trans hK₀e) hTLC
  have hzpow : Subgroup.zpowers e ≤ B ⊔ TL := Subgroup.zpowers_le.2 (Subgroup.mem_sup_right heTL)
  have hcentz : B ⊔ TL ≤ Subgroup.centralizer ((Subgroup.zpowers e : Subgroup G) : Set G) := by
    intro x hx
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    have hx' : e * x = x * e := Subgroup.mem_centralizer_iff.1 (hBC hx) e (Set.mem_singleton e)
    exact Commute.zpow_left hx' k
  have hnorm : B ⊔ TL ≤ Subgroup.normalizer ((Subgroup.zpowers e : Subgroup G) : Set G) :=
    hcentz.trans (Subgroup.centralizer_le_normalizer _)
  have hord : orderOf e = 2 := orderOf_eq_prime he2 he1
  have hPG : IsPGroup 2 ↥(Subgroup.zpowers e) :=
    IsPGroup.of_card (n := 1) (by simp only [Nat.card_zpowers, hord, pow_one])
  have hzle : Subgroup.zpowers e ≤ pCoreOf 2 (B ⊔ TL) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hzpow hnorm hPG
  have he_core : e ∈ pCoreOf 2 (B ⊔ TL) := hzle (Subgroup.mem_zpowers e)
  unfold CFSG.Open.quasithinIsLocal
  refine ⟨hTL2, hBTL, hTLsyl'.2.2, ?_⟩
  intro hbot
  rw [hbot] at he_core
  exact he1 (Subgroup.mem_bot.1 he_core)

theorem f2_pCoreOf_le_sandwich {G : Type} [Group G] [Finite G] {K K₀ H : Subgroup G}
    (hKK₀ : K ≤ K₀) (hK₀ : K₀ ≤ Subgroup.normalizer (K : Set G)) (hK₀H : K₀ ≤ H)
    (hH : H ≤ Subgroup.normalizer (K₀ : Set G)) :
    pCoreOf 2 K ≤ pCoreOf 2 H := by
  have h1 : pCoreOf 2 K ≤ pCoreOf 2 K₀ :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKK₀)
      (hK₀.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K)
  have h2 : pCoreOf 2 K₀ ≤ pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((CFSG.LieType.BorelTits.pCoreOf_le 2 K₀).trans hK₀H)
      (hH.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K₀))
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K₀)
  exact h1.trans h2

end CFSG.Quasithin.H13.NF314pt

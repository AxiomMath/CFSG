module

public import CFSG.RankThree.GF2n.Parrott.LiftOrderThree
public import CFSG.RankThree.GF2n.Parrott.CentralizerJoinQA45

public section

namespace CFSG.RankThree.GF2n.Parrott

open CFSG CFSG.ComponentClassification.CatFactsSmall.PSp43

private theorem mem_normalizer_zpowers_of_conj_eq_inv {K : Type*} [Group K] {g a : K}
    (h : g * a * g⁻¹ = a⁻¹) :
    g ∈ Subgroup.normalizer ((Subgroup.zpowers a : Subgroup K) : Set K) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, MonoidHom.map_zpowers]
  change Subgroup.zpowers (g * a * g⁻¹) = Subgroup.zpowers a
  rw [h, Subgroup.zpowers_inv]

private theorem centralizer_le_normalizer_zpowers {K : Type*} [Group K] (a : K) :
    Subgroup.centralizer ({a} : Set K) ≤
      Subgroup.normalizer ((Subgroup.zpowers a : Subgroup K) : Set K) := by
  rw [Subgroup.zpowers_eq_closure]
  exact (Subgroup.centralizer_le_normalizer ({a} : Set K)).trans
    (Subgroup.normalizer_le_normalizer_closure ({a} : Set K))

variable {G : Type} [Group G] [Finite G] {z : G}
variable [hN : ((J z).subgroupOf (H z)).Normal]
variable (D : QuotientData (z := z) hN)

theorem map_centralizer_qH_of_orderOf_three (x : ↥(H z)) (hx : orderOf x = 3) :
    (Subgroup.centralizer ({x} : Set ↥(H z))).map (qH D) =
      Subgroup.centralizer ({qH D x} : Set QA45.originalSubgroup) := by
  classical
  set K : Subgroup ↥(H z) := Subgroup.centralizer ({x} : Set ↥(H z)) with hK
  set f : ↥K →* QA45.originalSubgroup := (qH D).comp K.subtype with hf
  have hx3 : IsPGroup 3 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx]
    norm_num
  have hcop : Nat.Coprime 3 (Nat.card ((J z).subgroupOf (H z))) :=
    coprime_three_card_J_subgroupOf (z := z)
  have hmain := CFSG.card_centralizer_eq_card_inf_mul_card_quotient
    (G := ↥(H z)) (p := 3) (N := (J z).subgroupOf (H z)) (x := x) hx3 hcop
  have hquot := card_centralizer_quotient_eq (D := D) x
  have hker : f.ker = (K ⊓ (J z).subgroupOf (H z)).subgroupOf K := by
    ext y
    constructor
    · intro hy
      have hy1 : (qH D) (y : ↥(H z)) = 1 := MonoidHom.mem_ker.mp hy
      rw [Subgroup.mem_subgroupOf]
      exact ⟨y.2, (J_mem_iff D (y : ↥(H z))).mpr hy1⟩
    · intro hy
      rw [Subgroup.mem_subgroupOf] at hy
      exact MonoidHom.mem_ker.mpr ((J_mem_iff D (y : ↥(H z))).mp hy.2)
  have hkercard : Nat.card ↥f.ker = Nat.card ↥(K ⊓ (J z).subgroupOf (H z)) := by
    rw [hker]
    exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_left :
      K ⊓ (J z).subgroupOf (H z) ≤ K)).toEquiv
  have hpos : 0 < Nat.card ↥(K ⊓ (J z).subgroupOf (H z)) := Nat.card_pos
  have hrangecard : Nat.card ↥f.range =
      Nat.card (Subgroup.centralizer ({qH D x} : Set QA45.originalSubgroup)) := by
    have hmul := Subgroup.card_ker_mul_card_range f
    rw [hkercard, hmain, hquot] at hmul
    exact Nat.eq_of_mul_eq_mul_left hpos hmul
  have hrange : f.range = K.map (qH D) := by
    rw [hf, MonoidHom.range_comp]
    congr 1
    exact K.range_subtype
  have hle : f.range ≤ Subgroup.centralizer ({qH D x} : Set QA45.originalSubgroup) := by
    intro y hy
    rw [hrange] at hy
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hy
    rw [Subgroup.mem_centralizer_singleton_iff]
    have hk' : (k : ↥(H z)) * x = x * (k : ↥(H z)) := Subgroup.mem_centralizer_singleton_iff.mp hk
    have hq := congrArg (qH D) hk'
    simpa only [map_mul] using hq
  have hfinal : f.range = Subgroup.centralizer ({qH D x} : Set QA45.originalSubgroup) :=
    Subgroup.eq_of_le_of_card_ge hle (le_of_eq hrangecard.symm)
  rw [← hrange]
  exact hfinal

theorem map_normalizer_qH_of_orderOf_three (x : ↥(H z)) (hx : orderOf x = 3) :
    (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup ↥(H z)) : Set ↥(H z))).map (qH D) =
      Subgroup.normalizer ((Subgroup.zpowers (qH D x) : Subgroup QA45.originalSubgroup) :
        Set QA45.originalSubgroup) := by
  classical
  have hx3 : IsPGroup 3 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 1)
    rw [Nat.card_zpowers, hx]
    norm_num
  have : Fact (IsPGroup 3 ↥(Subgroup.zpowers x)) := ⟨hx3⟩
  have hcop : Nat.Coprime 3 (Nat.card ((J z).subgroupOf (H z))) :=
    coprime_three_card_J_subgroupOf (z := z)
  have hFr : Subgroup.normalizer (((Subgroup.zpowers x).map
        (QuotientGroup.mk' ((J z).subgroupOf (H z))) :
          Subgroup (↥(H z) ⧸ (J z).subgroupOf (H z))) : Set (↥(H z) ⧸ (J z).subgroupOf (H z))) =
      (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup ↥(H z)) : Set ↥(H z))).map
        (QuotientGroup.mk' ((J z).subgroupOf (H z))) :=
    CFSG.normalizer_map_quotient_eq_map_normalizer 3 (Subgroup.zpowers x)
      ((J z).subgroupOf (H z)) hN hcop
  have hq : qH D = (quotientEquivQA45 D).toMonoidHom.comp
      (QuotientGroup.mk' ((J z).subgroupOf (H z))) :=
    MonoidHom.ext fun a => (quotientEquivQA45_coe D a).symm
  calc (Subgroup.normalizer ((Subgroup.zpowers x : Subgroup ↥(H z)) : Set ↥(H z))).map (qH D)
      = ((Subgroup.normalizer ((Subgroup.zpowers x : Subgroup ↥(H z)) : Set ↥(H z))).map
          (QuotientGroup.mk' ((J z).subgroupOf (H z)))).map
            (quotientEquivQA45 D).toMonoidHom := by
        rw [hq, Subgroup.map_map]
    _ = (Subgroup.normalizer (((Subgroup.zpowers x).map
          (QuotientGroup.mk' ((J z).subgroupOf (H z))) :
            Subgroup (↥(H z) ⧸ (J z).subgroupOf (H z))) :
              Set (↥(H z) ⧸ (J z).subgroupOf (H z)))).map
            (quotientEquivQA45 D).toMonoidHom := by
        rw [hFr]
    _ = Subgroup.normalizer ((((Subgroup.zpowers x).map
          (QuotientGroup.mk' ((J z).subgroupOf (H z)))).map
            (quotientEquivQA45 D).toMonoidHom : Subgroup QA45.originalSubgroup) :
              Set QA45.originalSubgroup) :=
        Subgroup.map_equiv_normalizer_eq _ (quotientEquivQA45 D)
    _ = Subgroup.normalizer ((Subgroup.zpowers (qH D x) : Subgroup QA45.originalSubgroup) :
          Set QA45.originalSubgroup) := by
        rw [Subgroup.map_map, ← hq, MonoidHom.map_zpowers]

theorem exists_lift_inverting_sigma {s₁ : ↥(H z)} (hs₁ : orderOf s₁ = 3)
    (hq₁ : qH D s₁ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)) :
    ∃ vh : ↥(H z), qH D vh = (⟨v, v_mem_A⟩ : QA45.originalSubgroup) ∧
      vh ∈ Subgroup.normalizer ((Subgroup.zpowers s₁ : Subgroup ↥(H z)) : Set ↥(H z)) ∧
      vh * s₁ * vh⁻¹ = s₁⁻¹ := by
  have hvσ : (⟨v, v_mem_A⟩ : QA45.originalSubgroup) * ⟨sigma1, sigma1_mem_A⟩ *
      (⟨v, v_mem_A⟩ : QA45.originalSubgroup)⁻¹ =
        (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)⁻¹ := Subtype.ext sigma1_conj_v
  have hvN : (⟨v, v_mem_A⟩ : QA45.originalSubgroup) ∈ Subgroup.normalizer
      ((Subgroup.zpowers (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) :
        Subgroup QA45.originalSubgroup) : Set QA45.originalSubgroup) :=
    mem_normalizer_zpowers_of_conj_eq_inv hvσ
  have hvmap : (⟨v, v_mem_A⟩ : QA45.originalSubgroup) ∈
      (Subgroup.normalizer ((Subgroup.zpowers s₁ : Subgroup ↥(H z)) : Set ↥(H z))).map (qH D) := by
    rw [map_normalizer_qH_of_orderOf_three D s₁ hs₁, hq₁]
    exact hvN
  obtain ⟨vh, hvhN, hvhq⟩ := Subgroup.mem_map.mp hvmap
  have hmem : vh * s₁ * vh⁻¹ ∈ Subgroup.zpowers s₁ :=
    (Subgroup.mem_normalizer_iff.mp hvhN s₁).mp (Subgroup.mem_zpowers s₁)
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hmem
  have h1 : (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ^ m =
      (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup)⁻¹ := by
    have h := congrArg (qH D) hm
    rw [map_zpow, hq₁, map_mul, map_mul, map_inv, hvhq, hq₁] at h
    rw [h]
    exact hvσ
  have h2 : (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) ^ (m + 1) = 1 := by
    rw [zpow_add_one, h1, inv_mul_cancel]
  have h3 : ((orderOf (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup) : ℕ) : ℤ) ∣ m + 1 :=
    orderOf_dvd_iff_zpow_eq_one.mpr h2
  rw [orderOf_sigma1_subtype] at h3
  have h4 : s₁ ^ (m + 1) = 1 := by
    rw [← orderOf_dvd_iff_zpow_eq_one, hs₁]
    exact h3
  have h5 : s₁ ^ m = s₁⁻¹ := by
    rw [zpow_add_one] at h4
    exact eq_inv_of_mul_eq_one_left h4
  refine ⟨vh, hvhq, hvhN, ?_⟩
  rw [← hm, h5]

theorem sup_J_centralizer_sigma_v_eq_top {s₁ s₂ vh : ↥(H z)}
    (hs₁ : orderOf s₁ = 3) (hq₁ : qH D s₁ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup))
    (hs₂ : orderOf s₂ = 3) (hq₂ : qH D s₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup))
    (hv : qH D vh = (⟨v, v_mem_A⟩ : QA45.originalSubgroup)) :
    (J z).subgroupOf (H z) ⊔ Subgroup.centralizer ({s₁} : Set ↥(H z)) ⊔ Subgroup.zpowers vh ⊔
      Subgroup.centralizer ({s₂} : Set ↥(H z)) = ⊤ := by
  set T : Subgroup ↥(H z) := (J z).subgroupOf (H z) ⊔ Subgroup.centralizer ({s₁} : Set ↥(H z)) ⊔
    Subgroup.zpowers vh ⊔ Subgroup.centralizer ({s₂} : Set ↥(H z)) with hT
  have hker : (qH D).ker ≤ T := by
    rw [ker_qH D]
    exact le_trans le_sup_left (le_trans le_sup_left le_sup_left)
  have hJ : ((J z).subgroupOf (H z)).map (qH D) = ⊥ :=
    (Subgroup.map_eq_bot_iff _).mpr (ker_qH D).ge
  have hmap : T.map (qH D) = ⊤ := by
    rw [hT, Subgroup.map_sup, Subgroup.map_sup, Subgroup.map_sup, hJ,
      map_centralizer_qH_of_orderOf_three D s₁ hs₁, map_centralizer_qH_of_orderOf_three D s₂ hs₂,
      MonoidHom.map_zpowers, hv, hq₁, hq₂, bot_sup_eq]
    exact sup_centralizer_sigma_v_QA45
  rw [← Subgroup.comap_map_eq_self hker, hmap, Subgroup.comap_top]

theorem sup_J_normalizer_centralizer_eq_top {s₁ s₂ : ↥(H z)}
    (hs₁ : orderOf s₁ = 3) (hq₁ : qH D s₁ = (⟨sigma1, sigma1_mem_A⟩ : QA45.originalSubgroup))
    (hs₂ : orderOf s₂ = 3) (hq₂ : qH D s₂ = (⟨sigma2, sigma2_mem_A⟩ : QA45.originalSubgroup)) :
    (J z).subgroupOf (H z) ⊔
      Subgroup.normalizer ((Subgroup.zpowers s₁ : Subgroup ↥(H z)) : Set ↥(H z)) ⊔
      Subgroup.centralizer ({s₂} : Set ↥(H z)) = ⊤ := by
  obtain ⟨vh, hvq, hvN, -⟩ := exists_lift_inverting_sigma D hs₁ hq₁
  have hA := sup_J_centralizer_sigma_v_eq_top D hs₁ hq₁ hs₂ hq₂ hvq
  rw [eq_top_iff, ← hA]
  refine sup_le (sup_le (sup_le ?_ ?_) ?_) ?_
  · exact le_trans le_sup_left le_sup_left
  · exact le_trans (centralizer_le_normalizer_zpowers s₁) (le_trans le_sup_right le_sup_left)
  · exact le_trans (Subgroup.zpowers_le.mpr hvN) (le_trans le_sup_right le_sup_left)
  · exact le_sup_right

end CFSG.RankThree.GF2n.Parrott

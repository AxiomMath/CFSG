module

public import CFSG.Quasithin.H13.L32AC47a
public import CFSG.Quasithin.H13.L32AC30b

public section

namespace CFSG.Quasithin.H13.L32A.C

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G}

theorem mem_pCoreOf_iff_of_mem_cComp {K : Subgroup G} (hK : K ∈ cComp H) {k : G} (hk : k ∈ K) :
    k ∈ pCoreOf 2 H ↔ k ∈ pCoreOf 2 K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  constructor
  · intro h
    have hN : K ⊓ pCoreOf 2 H ≤ pCoreOf 2 K := by
      refine le_pCoreOf 2 inf_le_left ?_ ((pCoreOf_isPGroup 2 H).to_inf_right)
      constructor
      intro n hn g
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
      refine ⟨K.mul_mem (K.mul_mem g.2 hn.1) (K.inv_mem g.2), ?_⟩
      have := (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_pCoreOf 2 H (le_of_mem_cComp hK g.2)) n).mp hn.2
      simpa using this
    exact hN ⟨hk, h⟩
  · intro h
    exact A4.pCoreOf_le_of_subnormal 2 (subnormal_of_mem_cComp hK) h

omit [Finite G] in
theorem mk_eq_mk_iff {x y : ↥H} :
    (QuotientGroup.mk' (CFSG.pCore 2 ↥H) x = QuotientGroup.mk' (CFSG.pCore 2 ↥H) y) ↔
      (x : G)⁻¹ * y ∈ pCoreOf 2 H := by
  rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
    ← subgroupOf_pCoreOf_eq_pCore H, Subgroup.mem_subgroupOf]
  simp

theorem hat_center (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4)
    (h28 : Lemma14_7_28) (S : Setting147 G T L V H) {K : Subgroup G} (hK : K ∈ cComp H)
    (hHat : IsHat (cStar K) (NativeSporadic.Carrier .M22)) :
    (∀ l ∈ l1 T L V, ∃ k ∈ K, l⁻¹ * k ∈ pCoreOf 2 H ∧
      ∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 K) ∧
    (∀ k ∈ K, (∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 K) →
      ∃ l ∈ l1 T L V, l⁻¹ * k ∈ pCoreOf 2 H) ∧ (modO2Image H (l1 T L V)).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKH : K ≤ H := le_of_mem_cComp hK
  have hL1H : l1 T L V ≤ H := le_sup_left.trans S.hz.1.1
  have hL3 := relIndex_l1 h1222 h1332 h1334 S.hyp
  set mk := QuotientGroup.mk' (CFSG.pCore 2 ↥H) with hmk
  set Kb := modO2Image H K with hKb
  obtain ⟨e⟩ := CFSG.Quasithin.modO2_mulEquiv hK
  have hZ3 : Nat.card (Subgroup.center ↥Kb) = 3 := by
    rw [← card_center_eq_of_mulEquiv ((cStarEquiv K).trans e)]
    exact hHat.2.1
  set Zb := (Subgroup.center ↥Kb).map Kb.subtype with hZb
  have hZbc : Nat.card Zb = 3 := by
    rw [hZb, Subgroup.card_map_of_injective Kb.subtype_injective, hZ3]
  have hKbs : Kb.IsSubnormal := A3.subnormal_top_iff.mp (modO2Image_mem_cComp hK).2.2.1
  have hZn : (Zb.subgroupOf Kb).Normal := by
    rw [hZb, map_subtype_subgroupOf']
    infer_instance
  have hZs : Zb.IsSubnormal :=
    Subgroup.IsSubnormal.step _ _ (Subgroup.map_subtype_le _) hKbs hZn
  have hle := le_oddCore_of_isSubnormal hZs (by rw [hZbc]; decide)
  have hO : CFSG.oddCore (↥H ⧸ CFSG.pCore 2 ↥H) = modO2Image H (l1 T L V) := by
    rcases h28 G T L V H S with h0 | h1
    · exfalso
      rw [h0, le_bot_iff] at hle
      rw [hle, Subgroup.card_bot] at hZbc
      omega
    · exact h1
  have hZL : Zb = modO2Image H (l1 T L V) := by
    rw [hO] at hle
    have hoddL : Odd (Nat.card (modO2Image H (l1 T L V))) := hO ▸ odd_card_oddCore
    have hd := card_modO2Image_dvd_three hL1H hL3 hoddL
    refine Subgroup.eq_of_le_of_card_ge hle ?_
    rw [hZbc]
    exact Nat.le_of_dvd (by norm_num) hd
  have hnormal : (modO2Image H (l1 T L V)).Normal := by
    rw [← hO, oddCore_eq_pPrimeCore]
    exact CFSG.pPrimeCore_normal
  have hcent : ∀ k : G, ∀ hk : k ∈ K,
      (∀ k' ∈ K, k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 K) ↔ mk ⟨k, hKH hk⟩ ∈ Zb := by
    intro k hk
    constructor
    · intro hc
      refine ⟨⟨mk ⟨k, hKH hk⟩, ⟨⟨k, hKH hk⟩, Subgroup.mem_subgroupOf.mpr hk, rfl⟩⟩,
        Subgroup.mem_center_iff.mpr ?_, rfl⟩
      rintro ⟨_, ⟨y, hy, rfl⟩⟩
      apply Subtype.ext
      show mk y * mk ⟨k, hKH hk⟩ = mk ⟨k, hKH hk⟩ * mk y
      rw [← map_mul, ← map_mul, mk_eq_mk_iff]
      have hyK : (y : G) ∈ K := hy
      have h1 := hc (y : G) hyK
      have h2 : ((y : G) * k)⁻¹ * (k * y) =
          ((y : G) * k)⁻¹ * (k * y * k⁻¹ * (y : G)⁻¹) * ((y : G) * k) := by
        group
      simp only [Subgroup.coe_mul]
      rw [h2]
      have h3 := (mem_pCoreOf_iff_of_mem_cComp hK (K.mul_mem (K.mul_mem (K.mul_mem hk hyK)
        (K.inv_mem hk)) (K.inv_mem hyK))).mpr h1
      exact (Subgroup.mem_normalizer_iff''.mp
        (le_normalizer_pCoreOf 2 H (H.mul_mem y.2 (hKH hk))) _).mp h3
    · rintro ⟨⟨z, hzK⟩, hz, hzk⟩ k' hk'
      have hzk' : z = mk ⟨k, hKH hk⟩ := hzk
      have hc := Subgroup.mem_center_iff.mp hz ⟨mk ⟨k', hKH hk'⟩, ⟨⟨k', hKH hk'⟩, hk', rfl⟩⟩
      have hc' : mk ⟨k', hKH hk'⟩ * mk ⟨k, hKH hk⟩ = mk ⟨k, hKH hk⟩ * mk ⟨k', hKH hk'⟩ := by
        have := congrArg Subtype.val hc
        simp only [Subgroup.coe_mul] at this
        rw [hzk'] at this
        exact this
      rw [← map_mul, ← map_mul, mk_eq_mk_iff] at hc'
      have hm : k * k' * k⁻¹ * k'⁻¹ ∈ pCoreOf 2 H := by
        have e1 : k * k' * k⁻¹ * k'⁻¹ = (k' * k) * (((k' * k)⁻¹ * (k * k'))⁻¹)⁻¹ * (k' * k)⁻¹ := by
          group
        have h4 : ((k' * k)⁻¹ * (k * k'))⁻¹ ∈ pCoreOf 2 H := inv_mem (by simpa using hc')
        rw [e1]
        exact (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 H
          (H.mul_mem (hKH hk') (hKH hk))) _).mp (inv_mem h4)
      exact (mem_pCoreOf_iff_of_mem_cComp hK (K.mul_mem (K.mul_mem (K.mul_mem hk hk')
        (K.inv_mem hk)) (K.inv_mem hk'))).mp hm
  refine ⟨fun l hl => ?_, fun k hk hc => ?_, hnormal⟩
  · have hlZ : mk ⟨l, hL1H hl⟩ ∈ Zb := by
      rw [hZL]
      exact ⟨⟨l, hL1H hl⟩, hl, rfl⟩
    obtain ⟨⟨z, hzK⟩, hz, hzl⟩ := hlZ
    obtain ⟨y, hy, rfl⟩ := hzK
    have hyK : (y : G) ∈ K := hy
    refine ⟨y, hyK, ?_, (hcent y hyK).mpr ⟨⟨mk y, ⟨y, hy, rfl⟩⟩, hz, rfl⟩⟩
    have h1 : mk ⟨l, hL1H hl⟩ = mk y := hzl.symm
    exact (mk_eq_mk_iff.mp h1)
  · have hkZ := (hcent k hk).mp hc
    rw [hZL] at hkZ
    obtain ⟨y, hy, hyk⟩ := hkZ
    exact ⟨y, hy, mk_eq_mk_iff.mp hyk⟩

end CFSG.Quasithin.H13.L32A.C

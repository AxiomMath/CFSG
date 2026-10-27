module

public import CFSG.RankThree.PartOne.TAIL.SylCfg
public import CFSG.RankThree.PartOne.TAIL.Data

public section

namespace CFSG.RankThree.PartOne.TAIL

open Subgroup CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree
  CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory CFSG.RankThree.PartOne

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L B : Subgroup G} {n : ℕ}

theorem mem_A_of_normalizer_centralizer (cfg : Sec109.Config 7 A c L B n) {K : Subgroup G}
    (hKd : KData G K c) (hLd : LData G L B)
    (h81 : ∀ x ∈ Subgroup.centralizer (B : Set G), (∃ k : ℕ, orderOf x = 7 ^ k) →
      x ∈ Subgroup.normalizer (K : Set G))
    (hcout : c ∉ K ⊔ Subgroup.centralizer (K : Set G))
    (hC1 : CFSG.pRank 7 ↥(Subgroup.centralizer (L : Set G)) ≤ 1) {x : G}
    (hxc : x ∈ Subgroup.centralizer ({c} : Set G)) (hxA : x ∈ Subgroup.normalizer (A : Set G))
    (hx7 : ∃ k : ℕ, orderOf x = 7 ^ k) : x ∈ A := by
  have hp : Nat.Prime 7 := by norm_num
  have : Fact (Nat.Prime 7) := ⟨hp⟩
  obtain ⟨hBL, hBp, hBidx⟩ := hLd.sylow
  have hZL : Subgroup.center ↥L = ⊥ := (Sec109.lnTwoOuter ↥L n cfg.model).1
  have hxN : x ∈ Subgroup.normalizer (L : Set G) := mem_normalizer_L_of_normalizer_A cfg hxc hxA
  obtain ⟨k, hk⟩ := hx7
  obtain ⟨l, hlL, z, hzC, hxlz⟩ := exists_decomp_sup_centralizer (hLd.out_seven x hxN ⟨k, hk⟩)
  have hlz : Commute l z := Subgroup.mem_centralizer_iff.mp hzC l hlL
  have hx1 : x ^ (7 ^ k) = 1 := by rw [← hk]; exact pow_orderOf_eq_one x
  have hlz1 : l ^ (7 ^ k) * z ^ (7 ^ k) = 1 := by
    rw [← hlz.mul_pow, ← hxlz]
    exact hx1
  have hl1 : l ^ (7 ^ k) = 1 := by
    have hlz' : l ^ (7 ^ k) = (z ^ (7 ^ k))⁻¹ := eq_inv_of_mul_eq_one_left hlz1
    refine eq_one_of_mem_inf_centralizer hZL (L.pow_mem hlL _) ?_
    rw [hlz']
    exact Subgroup.inv_mem _ ((Subgroup.centralizer (L : Set G)).pow_mem hzC _)
  have hz1 : z ^ (7 ^ k) = 1 := by
    rw [hl1, one_mul] at hlz1
    exact hlz1
  have hlcomm : ∀ b ∈ B, l * b * l⁻¹ = x * b * x⁻¹ := by
    intro b hb
    have hzb : z * b = b * z := (Subgroup.mem_centralizer_iff.mp hzC b (hBL hb)).symm
    have h1 : z * b * z⁻¹ = b := by rw [hzb]; group
    rw [hxlz]
    calc l * b * l⁻¹ = l * (z * b * z⁻¹) * l⁻¹ := by rw [h1]
      _ = l * z * b * (l * z)⁻¹ := by group
  have hlBcond : ∀ b ∈ B, l * b * l⁻¹ ∈ B := by
    intro b hb
    have h1 : x * b * x⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hxA b).mp (cfg.B_le_A hb)
    have h2 : l * b * l⁻¹ ∈ L := L.mul_mem (L.mul_mem hlL (hBL hb)) (L.inv_mem hlL)
    rw [hlcomm b hb] at h2 ⊢
    rw [cfg.B_eq]
    exact ⟨h1, h2⟩
  have hlN : l ∈ Subgroup.normalizer (B : Set G) := normalizer_of_conj_mem_of_finite hlBcond
  have hS : CFSG.ABGLocalTools.IsSylowOf 7 B L :=
    CFSG.ABGLocalTools.isSylowOf_iff.mpr ⟨hBL, hBp, hBidx⟩
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hl1)
  have hlB : l ∈ B := mem_of_normalizer_of_isSylowOf hS hlL hlN hj
  have hc7 : orderOf c = 7 := orderOf_eq_prime (cfg.pow_p_eq_one cfg.c_mem) cfg.c_ne_one
  have hlc : l * c = c * l := cfg.A_comm l (cfg.B_le_A hlB) c cfg.c_mem
  have hxc' : x * c = c * x := Subgroup.mem_centralizer_singleton_iff.mp hxc
  have hlc' : l⁻¹ * c = c * l⁻¹ := (Commute.inv_left (show Commute l c from hlc)).eq
  have hzc : z * c = c * z := by
    have hz : z = l⁻¹ * x := by rw [hxlz]; group
    rw [hz]
    calc l⁻¹ * x * c = l⁻¹ * (x * c) := by group
      _ = l⁻¹ * (c * x) := by rw [hxc']
      _ = (l⁻¹ * c) * x := by group
      _ = (c * l⁻¹) * x := by rw [hlc']
      _ = c * (l⁻¹ * x) := by group
  have hcC : c ∈ Subgroup.centralizer (L : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun g hg => cfg.mem_L_comm_c hg
  obtain ⟨j2, -, hj2⟩ := (Nat.dvd_prime_pow hp).1 (orderOf_dvd_of_pow_eq_one hz1)
  have hzp : IsPGroup 7 ↥(Subgroup.zpowers z) :=
    IsPGroup.of_card (n := j2) (by rw [Nat.card_zpowers, hj2])
  have hcp : IsPGroup 7 ↥(Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hc7]; norm_num)
  have hcNz : Subgroup.zpowers c ≤ Subgroup.normalizer (Subgroup.zpowers z : Set G) :=
    Subgroup.zpowers_le.mpr (mem_normalizer_zpowers_of_comm hzc.symm)
  set R : Subgroup G := Subgroup.zpowers z ⊔ Subgroup.zpowers c with hR
  have hRp : IsPGroup 7 ↥R := hzp.to_sup_of_normal_left' hcp hcNz
  have hRC : R ≤ Subgroup.centralizer (L : Set G) :=
    sup_le (Subgroup.zpowers_le.mpr hzC) (Subgroup.zpowers_le.mpr hcC)
  have hRN : R ≤ Subgroup.normalizer (K : Set G) := by
    intro y hy
    refine h81 y ?_ ?_
    · exact Subgroup.centralizer_le (SetLike.coe_subset_coe.mpr hBL) (hRC hy)
    · obtain ⟨m, hm⟩ := (IsPGroup.iff_orderOf.mp hRp) ⟨y, hy⟩
      exact ⟨m, by rwa [Subgroup.orderOf_mk] at hm⟩
  have hout := hKd.out_index R hRp hRN
  have hRcomm : ∀ y ∈ R, y * c = c * y := by
    intro y hy
    have hle : R ≤ Subgroup.centralizer ({c} : Set G) :=
      sup_le (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr hzc))
        (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl))
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle hy)
  have hcardc : Nat.card ↥(Subgroup.zpowers c) = 7 := by rw [Nat.card_zpowers, hc7]
  have hR0 : R ⊓ (K ⊔ Subgroup.centralizer (K : Set G)) = ⊥ := by
    by_contra hne
    set R₀ : Subgroup G := R ⊓ (K ⊔ Subgroup.centralizer (K : Set G)) with hR₀
    have hR0p : IsPGroup 7 ↥R₀ := hRp.to_inf_left
    rcases hR0p.card_eq_or_dvd with h1 | h7
    · exact hne (Subgroup.card_eq_one.mp h1)
    · obtain ⟨y, hy7⟩ := exists_prime_orderOf_dvd_card' 7 h7
      have hyR : (y : G) ∈ R := (inf_le_left : R₀ ≤ R) y.2
      have hy7' : orderOf (y : G) = 7 := by rw [← Subgroup.orderOf_coe] at hy7; exact hy7
      have hyc : (y : G) ∈ Subgroup.zpowers c :=
        mem_zpowers_of_pRank hc7 hy7' hcC (hRC hyR) (hRcomm _ hyR) hC1
      have hle : Subgroup.zpowers (y : G) ≤ Subgroup.zpowers c := Subgroup.zpowers_le.mpr hyc
      have hcardy : Nat.card ↥(Subgroup.zpowers (y : G)) = 7 := by rw [Nat.card_zpowers, hy7']
      have heq : Subgroup.zpowers (y : G) = Subgroup.zpowers c :=
        Subgroup.eq_of_le_of_card_ge hle (by omega)
      have hcR0 : c ∈ R₀ := by
        have : c ∈ Subgroup.zpowers (y : G) := by rw [heq]; exact Subgroup.mem_zpowers c
        exact (Subgroup.zpowers_le.mpr y.2) this
      exact hcout ((inf_le_right : R₀ ≤ K ⊔ Subgroup.centralizer (K : Set G)) hcR0)
  have hRcard : Nat.card ↥R ≤ 7 := by
    rw [hR0, Subgroup.relIndex_bot_left] at hout
    exact hout
  have hRc : Subgroup.zpowers c = R :=
    Subgroup.eq_of_le_of_card_ge (le_sup_right : Subgroup.zpowers c ≤ R) (by omega)
  have hzc_mem : z ∈ Subgroup.zpowers c := by
    rw [hRc]
    exact (le_sup_left : Subgroup.zpowers z ≤ R) (Subgroup.mem_zpowers z)
  rw [hxlz]
  exact A.mul_mem (cfg.B_le_A hlB) ((Subgroup.zpowers_le.mpr cfg.c_mem) hzc_mem)

theorem not_dvd_relIndex_centralizer (cfg : Sec109.Config 7 A c L B n) {K : Subgroup G}
    (hKd : KData G K c) (hLd : LData G L B)
    (h81 : ∀ x ∈ Subgroup.centralizer (B : Set G), (∃ k : ℕ, orderOf x = 7 ^ k) →
      x ∈ Subgroup.normalizer (K : Set G))
    (hcout : c ∉ K ⊔ Subgroup.centralizer (K : Set G))
    (hC1 : CFSG.pRank 7 ↥(Subgroup.centralizer (L : Set G)) ≤ 1) :
    ¬ 7 ∣ A.relIndex (Subgroup.centralizer ({c} : Set G)) := by
  intro h7
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (cfg.A_comm a ha c cfg.c_mem)
  have hP : IsPGroup 7 ↥(A.subgroupOf (Subgroup.centralizer ({c} : Set G))) := by
    have := cfg.A_elem
    exact (IsElementaryAbelian.isPGroup 7 ↥A).comap_subtype
  obtain ⟨x, hxN, hxP, k, hk⟩ := exists_normalizer_of_not_sylow hP h7
  have hxA : (x : G) ∈ Subgroup.normalizer (A : Set G) := by
    refine normalizer_of_conj_mem_of_finite fun a ha => ?_
    have h1 : (⟨a, hAC ha⟩ : ↥(Subgroup.centralizer ({c} : Set G))) ∈
        A.subgroupOf (Subgroup.centralizer ({c} : Set G)) := ha
    exact (Subgroup.mem_normalizer_iff.mp hxN _).mp h1
  have hxA' : (x : G) ∈ A :=
    mem_A_of_normalizer_centralizer cfg hKd hLd h81 hcout hC1 x.2 hxA
      ⟨k, by rw [Subgroup.orderOf_coe]; exact hk⟩
  exact hxP hxA'

theorem aSylow_of_config (cfg : Sec109.Config 7 A c L B n) {K : Subgroup G}
    (hKd : KData G K c) (hLd : LData G L B)
    (h81 : ∀ x ∈ Subgroup.centralizer (B : Set G), (∃ k : ℕ, orderOf x = 7 ^ k) →
      x ∈ Subgroup.normalizer (K : Set G))
    (hcout : c ∉ K ⊔ Subgroup.centralizer (K : Set G))
    (hC1 : CFSG.pRank 7 ↥(Subgroup.centralizer (L : Set G)) ≤ 1) :
    (A ≤ Subgroup.centralizer ({c} : Set G) ∧ IsPGroup 7 ↥A ∧
      ¬ 7 ∣ A.relIndex (Subgroup.centralizer ({c} : Set G))) ∧
    (A ≤ Subgroup.normalizer (A : Set G) ⊓ Subgroup.normalizer (Subgroup.zpowers c : Set G) ∧
      ¬ 7 ∣ A.relIndex (Subgroup.normalizer (A : Set G) ⊓
        Subgroup.normalizer (Subgroup.zpowers c : Set G))) := by
  have hp : Nat.Prime 7 := by norm_num
  have : Fact (Nat.Prime 7) := ⟨hp⟩
  have hc7 : orderOf c = 7 := orderOf_eq_prime (cfg.pow_p_eq_one cfg.c_mem) cfg.c_ne_one
  have hAC : A ≤ Subgroup.centralizer ({c} : Set G) := fun a ha =>
    Subgroup.mem_centralizer_singleton_iff.mpr (cfg.A_comm a ha c cfg.c_mem)
  have h1 := not_dvd_relIndex_centralizer cfg hKd hLd h81 hcout hC1
  have hApg : IsPGroup 7 ↥A := by
    have := cfg.A_elem
    exact IsElementaryAbelian.isPGroup 7 ↥A
  refine ⟨⟨hAC, hApg, h1⟩, ?_, ?_⟩
  · refine le_inf (Subgroup.le_normalizer) ?_
    intro a ha
    exact mem_normalizer_zpowers_of_comm (cfg.A_comm a ha c cfg.c_mem)
  · set N : Subgroup G := Subgroup.normalizer (A : Set G) ⊓
      Subgroup.normalizer (Subgroup.zpowers c : Set G) with hN
    have hAN : A ≤ N := by
      refine le_inf (Subgroup.le_normalizer) ?_
      intro a ha
      exact mem_normalizer_zpowers_of_comm (cfg.A_comm a ha c cfg.c_mem)
    have hNz : N ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) := inf_le_right
    set C : Subgroup G := Subgroup.centralizer ({c} : Set G) with hC
    have hACN : A ≤ C ⊓ N := le_inf hAC hAN
    have h6 : (C ⊓ N).relIndex N ∣ 6 := relIndex_centralizer_dvd_six hc7 hNz
    have e1 : A.relIndex (C ⊓ N) * (C ⊓ N).relIndex N = A.relIndex N :=
      Subgroup.relIndex_mul_relIndex A (C ⊓ N) N hACN inf_le_right
    have e2 : A.relIndex (C ⊓ N) * (C ⊓ N).relIndex C = A.relIndex C :=
      Subgroup.relIndex_mul_relIndex A (C ⊓ N) C hACN inf_le_left
    intro h7
    rw [← e1] at h7
    rcases (Nat.Prime.dvd_mul hp).1 h7 with h8 | h8
    · exact h1 (h8.trans (Dvd.intro _ e2))
    · have := Nat.le_of_dvd (by norm_num) (h8.trans h6)
      omega

end CFSG.RankThree.PartOne.TAIL

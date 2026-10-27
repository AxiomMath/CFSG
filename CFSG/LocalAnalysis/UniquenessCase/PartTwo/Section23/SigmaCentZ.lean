module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsRootModule
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.StatementsComponents
public import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846a
public import CFSG.GH74.GLS.Stage2.Local.P34NS12Grp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def AutZCartan (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx23L D Ch, ∃ C : Subgroup G,
    D.M ⊓ Subgroup.centralizer (D.Z : Set G) ≤ C ∧ C ≤ D.M ∧ (C.subgroupOf D.M).Normal ∧
    (D.M ⊓ Subgroup.centralizer (D.Z : Set G)).relIndex C = 2 ^ CFSG.Open.pRank 2 D.Z - 1 ∧
    (∃ m ∈ D.M, ∀ x ∈ D.M, ∃ k : ℤ, x * (m ^ k)⁻¹ ∈ C)

@[expose] def SigmaCentZ (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx23L D Ch, ∀ p ∈ D.sig, Opp p D.M ≤ Subgroup.centralizer (D.Z : Set G)

private theorem isCyclic_quotient_of_sup_zpowers {M C : Subgroup G}
    (hC_normal : (C.subgroupOf M).Normal) {m : G} (hm : m ∈ M)
    (hgen : ∀ x ∈ M, ∃ k : ℤ, x * (m ^ k)⁻¹ ∈ C) :
    IsCyclic (↥M ⧸ C.subgroupOf M) := by
  classical
  let R₁ : Subgroup ↥M := C.subgroupOf M
  let R₂ : Subgroup ↥M := (Subgroup.zpowers m).subgroupOf M
  haveI : R₁.Normal := hC_normal
  have hsup : R₁ ⊔ R₂ = ⊤ := by
    rw [eq_top_iff]
    intro x _
    obtain ⟨k, hk⟩ := hgen x.val x.2
    have hmem : x.val * (m ^ k)⁻¹ ∈ M :=
      M.mul_mem x.2 (M.inv_mem (M.zpow_mem hm k))
    have hx_eq : x = (⟨x.val * (m ^ k)⁻¹, hmem⟩ : ↥M) * ⟨m ^ k, M.zpow_mem hm k⟩ := by
      ext
      simp [mul_assoc]
    rw [hx_eq]
    refine Subgroup.mul_mem _ ?_ ?_
    · exact Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hk)
    · exact Subgroup.mem_sup_right
        (Subgroup.mem_subgroupOf.mpr (Subgroup.zpow_mem_zpowers _ k))
  have hR₂cyc : IsCyclic R₂ := by
    have hle : Subgroup.zpowers m ≤ M := Subgroup.zpowers_le.mpr hm
    exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hle)).2
      (Subgroup.isCyclic_zpowers m)
  exact quotient_isCyclic_of_sup_cyclic_right hsup hR₂cyc

private theorem closure_pPrime_eq_top_of_opRes_eq_top {M : Subgroup G} {p : ℕ} (hp : p.Prime)
    (h : F10.OpRes p M = M) :
    Subgroup.closure {y : ↥M | ¬ p ∣ orderOf y} = ⊤ := by
  have hres : CFSG.GH74.GLS.oResidual p ↥M = ⊤ := by
    apply Subgroup.map_injective M.subtype_injective
    rw [← UC6.opRes_eq_map_oResidual_uc6 hp, h, Subgroup.map_top, Subgroup.range_subtype]
  rw [← hres, CFSG.GH74.GLS.oResidual]
  congr 1
  ext y
  simp only [Set.mem_setOf_eq]
  rw [Nat.coprime_comm]
  exact (hp.coprime_iff_not_dvd (n := orderOf y)).symm

private theorem mem_C_of_orderOf_eq_prime_pow {M C : Subgroup G}
    (hC_normal : (C.subgroupOf M).Normal)
    (hcyc : IsCyclic (↥M ⧸ C.subgroupOf M)) {p : ℕ}
    (hgen : Subgroup.closure {y : ↥M | ¬ p ∣ orderOf y} = ⊤)
    (hp : p.Prime) {x : G} (hxM : x ∈ M) {k : ℕ} (hxord : orderOf x = p ^ k) :
    x ∈ C := by
  let N : Subgroup ↥M := C.subgroupOf M
  letI : N.Normal := hC_normal
  have hxk : (⟨x, hxM⟩ : ↥M) ^ (p ^ k) = 1 := by
    have ha : orderOf (⟨x, hxM⟩ : ↥M) = p ^ k := by
      rw [← Subgroup.orderOf_coe, hxord]
    rw [← ha, pow_orderOf_eq_one]
  have hxN : (⟨x, hxM⟩ : ↥M) ∈ N :=
    CFSG.LocalAnalysis.UniquenessCase.UC6S846.mem_inner_of_pPow (I := N) (N := N) (H := ⊤)
      hcyc (by intro φ hφ; exact N.pow_mem hφ 3) hp (Or.inr le_rfl)
      (by simpa using hgen) (Subgroup.mem_top _) hxk
  exact Subgroup.mem_subgroupOf.mp hxN

private theorem mem_centralizer_of_mem_C (D : Data G) (Ch : Choice2011 G) (h1930 : H1930 D)
    (c : Ctx23L D Ch) (h4 : S23_4 D Ch) (h52 : S23_5_2 D Ch)
    (h212 : S21_2 D Ch) (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (h6 : S23_6 D Ch) {p : ℕ} (hpσ : p ∈ D.sig) {C : Subgroup G}
    (hCMZ_le_C : D.M ⊓ Subgroup.centralizer (D.Z : Set G) ≤ C) (hC_le_M : C ≤ D.M)
    (hrel : (D.M ⊓ Subgroup.centralizer (D.Z : Set G)).relIndex C =
      2 ^ CFSG.Open.pRank 2 D.Z - 1)
    {x : G} (hxC : x ∈ C) {k : ℕ} (hxord : orderOf x = p ^ k) :
    x ∈ Subgroup.centralizer (D.Z : Set G) := by
  classical
  obtain ⟨hp, -⟩ := D.sig_prime p hpσ
  haveI : Fact p.Prime := ⟨hp⟩
  have hp1 : p ∈ D.sig1 := (h6 h1930 c) ▸ hpσ
  have hsp' := hsp p hp1
  by_contra hxnot
  have hxM : x ∈ D.M := hC_le_M hxC
  obtain ⟨hUZ, -, hMN⟩ := h4 h1930 c
  have hMNZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := hUZ ▸ hMN
  have hMNCZ : D.M ≤ Subgroup.normalizer
      (Subgroup.centralizer (D.Z : Set G) : Set G) :=
    hMNZ.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup D.Z)
  have hM_le_NM : D.M ≤ Subgroup.normalizer (D.M : Set G) := Subgroup.le_normalizer
  have hM_le_NCMZ : D.M ≤ Subgroup.normalizer
      ((D.M ⊓ Subgroup.centralizer (D.Z : Set G) : Subgroup G) : Set G) :=
    (le_inf hM_le_NM hMNCZ).trans Subgroup.inf_normalizer_le_normalizer_inf
  have hCMZ_normal_C : ((D.M ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf C).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hCMZ_le_C).mpr (hC_le_M.trans hM_le_NCMZ)
  let N_C : Subgroup ↥C := (D.M ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf C
  letI : N_C.Normal := hCMZ_normal_C
  let π : ↥C →* ↥C ⧸ N_C := QuotientGroup.mk' N_C
  have hxnotN : (⟨x, hxC⟩ : ↥C) ∉ N_C := by
    intro hxN
    exact hxnot (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hxN)).2
  have hq_ne : π ⟨x, hxC⟩ ≠ 1 := by
    intro hq
    exact hxnotN ((QuotientGroup.eq_one_iff _).mp hq)
  have hq_dvd : orderOf (π ⟨x, hxC⟩) ∣ p ^ k := by
    have h1 : orderOf (π ⟨x, hxC⟩) ∣ orderOf (⟨x, hxC⟩ : ↥C) := orderOf_map_dvd π _
    rwa [← Subgroup.orderOf_coe, hxord] at h1
  have hq_ne_one : orderOf (π ⟨x, hxC⟩) ≠ 1 := fun h =>
    hq_ne (orderOf_eq_one_iff.mp h)
  have hpdvd_q : p ∣ orderOf (π ⟨x, hxC⟩) := by
    obtain ⟨j, -, hord⟩ := (Nat.dvd_prime_pow hp).1 hq_dvd
    rcases Nat.eq_zero_or_pos j with rfl | hjpos
    · rw [pow_zero] at hord
      exact absurd hord hq_ne_one
    · rw [hord]
      exact dvd_pow_self p hjpos.ne'
  have hcard : Nat.card (↥C ⧸ N_C) = 2 ^ CFSG.Open.pRank 2 D.Z - 1 := by
    rw [← Subgroup.index_eq_card]
    change (D.M ⊓ Subgroup.centralizer (D.Z : Set G)).relIndex C = _
    exact hrel
  have hpdvd : p ∣ 2 ^ CFSG.Open.pRank 2 D.Z - 1 := by
    have h := hpdvd_q.trans (orderOf_dvd_natCard (π ⟨x, hxC⟩))
    rwa [hcard] at h
  have hmdvd : CFSG.Open.pRank 2 D.Z ∣ c.n := by
    rcases h52 h1930 c with h | ⟨-, -, h2⟩
    · rw [← h]
    · rw [h2]
      exact dvd_mul_left _ 2
  have hdiv : 2 ^ CFSG.Open.pRank 2 D.Z - 1 ∣ 2 ^ c.n - 1 :=
    Nat.pow_sub_one_dvd_pow_sub_one 2 hmdvd
  have hpeta : p ∈ etaSet c.n := ⟨hp, hpdvd.trans hdiv⟩
  have hpB0 : p ∈ piSet c.B0 := by
    rwa [c.hpi]
  obtain ⟨b, hborder⟩ := exists_prime_orderOf_dvd_card' (G := ↥c.B0) p hpB0.2
  let A : Subgroup G := Subgroup.zpowers (b : G)
  have hbB0 : (b : G) ∈ c.B0 := b.2
  have hborder' : orderOf (b : G) = p := by
    rw [Subgroup.orderOf_coe, hborder]
  have hA_le_B0 : A ≤ c.B0 := Subgroup.zpowers_le.mpr hbB0
  have hA_le_M : A ≤ D.M := hA_le_B0.trans c.hBM
  have hb_ne : (b : G) ≠ 1 := by
    intro hb1
    have h1 : orderOf (b : G) = 1 := by rw [hb1, orderOf_one]
    rw [hborder'] at h1
    exact hp.ne_one h1
  have hA_ne : A ≠ ⊥ := Subgroup.zpowers_ne_bot.mpr hb_ne
  have hAp : IsPGroup p A :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hborder', pow_one])
  have hNleM : Subgroup.normalizer (A : Set G) ≤ D.M :=
    hsp'.normalizer_le hA_ne hAp hA_le_M
  let c0 : Ctx21 D Ch := { c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl }
  have hA_le_c0B : A ≤ c0.B := hA_le_B0
  exact (h212 h1930 c0 A hA_le_c0B) hNleM

theorem sigmaCentZ_of (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch) (h638 : UC6.R6_38 D)
    (hZ : AutZCartan D Ch) (h52 : S23_5_2 D Ch) (h212 : S21_2 D Ch)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) (h6 : S23_6 D Ch) :
    SigmaCentZ D Ch := by
  intro h1930 c p hpσ
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨C, hCMZ_le_C, hC_le_M, hC_normal, hrel, hgenM⟩ := hZ h1930 c
  obtain ⟨m, hm, hgenM⟩ := hgenM
  have hOp : F10.OpRes p D.M = D.M := h638 p hp hp2 (Or.inl hpσ)
  have hcyc : IsCyclic (↥D.M ⧸ C.subgroupOf D.M) :=
    isCyclic_quotient_of_sup_zpowers hC_normal hm hgenM
  have hgen : Subgroup.closure {y : ↥D.M | ¬ p ∣ orderOf y} = ⊤ :=
    closure_pPrime_eq_top_of_opRes_eq_top hp hOp
  have hmemC : ∀ x ∈ D.M, ∀ k : ℕ, orderOf x = p ^ k → x ∈ C := by
    intro x hxM k hxord
    exact mem_C_of_orderOf_eq_prime_pow hC_normal hcyc hgen hp hxM hxord
  rw [Opp, CFSG.RankThree.PartOne.pElementSubgroup]
  refine (Subgroup.closure_le _).mpr ?_
  rintro x ⟨hxM, k, hxord⟩
  exact mem_centralizer_of_mem_C D Ch h1930 c h4 h52 h212 hsp h6 hpσ hCMZ_le_C hC_le_M
    hrel (hmemC x hxM k hxord) hxord

theorem le_centralizer_Z_of_perfect (D : Data G) (Ch : Choice2011 G) (h4 : S23_4 D Ch)
    (h1930 : H1930 D) (c : Ctx23L D Ch) {K : Subgroup G} (hKM : K ≤ D.M) (hK : ⁅K, K⁆ = K) :
    K ≤ Subgroup.centralizer (D.Z : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hUZ, -, hMN⟩ := h4 h1930 c
  have hMNZ : D.M ≤ Subgroup.normalizer (D.Z : Set G) := hUZ ▸ hMN
  have hT_CGZ : D.T ≤ Subgroup.centralizer (D.Z : Set G) :=
    Subgroup.le_centralizer_iff.mp fun z hz =>
      (Subgroup.mem_inf.mp
        (CFSG.LocalAnalysis.RankThreeUC.omegaOneCenterIn_le_inf_centralizer D.T hz)).2
  have hMNCZ : D.M ≤ Subgroup.normalizer
      (Subgroup.centralizer (D.Z : Set G) : Set G) :=
    hMNZ.trans (CFSG.GorensteinWalter.normalizer_le_normalizer_centralizer_subgroup D.Z)
  have hM_le_NCMZ : D.M ≤ Subgroup.normalizer
      ((D.M ⊓ Subgroup.centralizer (D.Z : Set G) : Subgroup G) : Set G) :=
    (le_inf (Subgroup.le_normalizer : D.M ≤ Subgroup.normalizer (D.M : Set G)) hMNCZ).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hCMZn : ((D.M ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf D.M).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer inf_le_left).mpr hM_le_NCMZ
  haveI := hCMZn
  have hTodd : Odd (D.T.relIndex D.M) :=
    Nat.not_even_iff_odd.mp fun he =>
      (CFSG.ABGLocalTools.isSylowOf_iff.mp D.sylowM).2.2 (even_iff_two_dvd.mp he)
  have hquotodd : Odd (Nat.card
      (↥D.M ⧸ (D.M ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf D.M)) := by
    change Odd ((D.M ⊓ Subgroup.centralizer (D.Z : Set G)).relIndex D.M)
    exact Odd.of_dvd_nat hTodd
      (Subgroup.relIndex_dvd_of_le_left D.M (le_inf D.sylowM.le hT_CGZ))
  have hK' : ⁅K.subgroupOf D.M, K.subgroupOf D.M⁆ = K.subgroupOf D.M := by
    apply Subgroup.map_injective D.M.subtype_injective
    rw [Subgroup.map_commutator, Subgroup.map_subgroupOf_eq_of_le hKM, hK]
  have hKle : K.subgroupOf D.M ≤
      (D.M ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf D.M :=
    CFSG.GH74.GLS.Stage2.Local.P34NS.perfect_le_of_odd_quot hquotodd hK'
  intro k hk
  have hk' : (⟨k, hKM hk⟩ : ↥D.M) ∈
      (D.M ⊓ Subgroup.centralizer (D.Z : Set G)).subgroupOf D.M :=
    hKle (Subgroup.mem_subgroupOf.mpr hk)
  exact (Subgroup.mem_inf.mp (Subgroup.mem_subgroupOf.mp hk')).2

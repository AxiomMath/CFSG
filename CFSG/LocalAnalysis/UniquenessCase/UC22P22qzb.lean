module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qza
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qo
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qj

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools
open CFSG.Blueprint (LieModel)
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

theorem uc22p22qzb_le_centralizer_layer {M P P₀ : Subgroup G} {p : ℕ} (h5 : 5 ≤ p)
    (hcl : uniqueFourClauseTwo M P P₀ p) :
    uniqueFourPrimeCore p (centralizer (P₀ : Set G)) ⊔ P₀ ≤
      centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G) := by
  classical
  obtain ⟨-, -, -, ⟨hf, n, hn, ⟨e⟩⟩, -, -, -, -⟩ := hcl
  haveI := hf
  have hp : p.Prime := hf.out
  set C : Subgroup G := centralizer (P₀ : Set G) with hC
  set E : Subgroup G := rankThreeLayer C with hE
  have hEC : E ≤ C := uc22p22q_layer_le C
  refine sup_le ?_ fun z hz => mem_centralizer_iff.2 fun l hl =>
    ((mem_centralizer_iff.1 (hEC hl)) z hz).symm
  have h25 : 5 ≤ p ^ n := h5.trans (Nat.le_self_pow (by omega) p)
  have hLie : LieModel ↥E .PSL 2 p n :=
    Or.inl ⟨by decide, CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv _ p n h25 e⟩
  haveI hsimple : IsSimpleGroup ↥E := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hLie
  have hpE : p ∣ Nat.card ↥E := by
    obtain ⟨R⟩ := (inferInstance : Nonempty (Sylow p ↥E))
    have hS : IsSylowOf p (R : Subgroup ↥E) ⊤ :=
      isSylowOf_iff.2 ⟨le_top, R.isPGroup', by rw [Subgroup.relIndex_top_right]; exact R.not_dvd_index⟩
    obtain ⟨-, hcard⟩ := uc22p22q_psl2_sylow_elem hp (by omega) hLie hS
    have h1 : p ^ n ∣ Nat.card ↥E := hcard ▸ Subgroup.card_subgroup_dvd_card _
    exact (dvd_pow_self p (by omega)).trans h1
  unfold uniqueFourPrimeCore relPPrimeCore
  refine sSup_le ?_
  rintro N ⟨hNC, hNn, hNcop⟩
  have hNconj : ∀ c ∈ C, ∀ x ∈ N, c * x * c⁻¹ ∈ N := fun c hc x hx => by
    have := hNn.conj_mem ⟨x, hNC hx⟩ (mem_subgroupOf.2 hx) ⟨c, hc⟩
    simpa [mem_subgroupOf] using this
  have hNE : ∀ x ∈ N, x ∈ E → x = 1 := by
    have hnorm : (N.subgroupOf E).Normal := ⟨fun x hx g => by
      rw [mem_subgroupOf] at hx ⊢
      simpa using hNconj g (hEC g.2) x hx⟩
    haveI := hnorm
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (N.subgroupOf E) with hbot | htop
    · intro x hx hxE
      have h1 : (⟨x, hxE⟩ : ↥E) ∈ N.subgroupOf E := mem_subgroupOf.2 hx
      rw [hbot, mem_bot] at h1
      exact congrArg Subtype.val h1
    · exfalso
      have hEN : E ≤ N := fun x hx => by
        have h1 : (⟨x, hx⟩ : ↥E) ∈ N.subgroupOf E := by rw [htop]; trivial
        exact mem_subgroupOf.1 h1
      exact (Nat.Prime.coprime_iff_not_dvd hp).1 hNcop (hpE.trans (Subgroup.card_dvd_of_le hEN))
  intro x hx
  rw [mem_centralizer_iff]
  intro l hl
  have hw : x * l * x⁻¹ * l⁻¹ = 1 := by
    apply hNE
    · have h1 : l * x⁻¹ * l⁻¹ ∈ N := hNconj l (hEC hl) _ (N.inv_mem hx)
      have h2 := N.mul_mem hx h1
      simpa [mul_assoc] using h2
    · exact E.mul_mem (uc22p22qo_layer_conj (hNC hx) hl) (E.inv_mem hl)
  have h3 : x * l = l * x := by
    calc x * l = x * l * x⁻¹ * l⁻¹ * (l * x) := by group
      _ = l * x := by rw [hw, one_mul]
  exact h3.symm

theorem uc22p22qzb_inter_layer (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) {p : ℕ}
    {P P₀ : Subgroup G} (hH : UC6.Hyp612 (UC6.dataOfSetup4 hS hU S) p P P₀) (h5 : 5 ≤ p)
    (hab : IsMulCommutative P) (hcl : uniqueFourClauseTwo (UC6.dataOfSetup4 hS hU S).M P P₀ p) :
    ∃ n : ℕ, 2 ≤ n ∧ IsElemAbelian p (P ⊓ rankThreeLayer (centralizer (P₀ : Set G))) ∧
      Nat.card ↥(P ⊓ rankThreeLayer (centralizer (P₀ : Set G))) = p ^ n := by
  classical
  obtain ⟨hP₀P, -, -, ⟨hf, n, hn, ⟨e⟩⟩, -, -, -, -⟩ := hcl
  haveI := hf
  have hp : p.Prime := hf.out
  have hpσ : p ∈ (UC6.dataOfSetup4 hS hU S).sig := hH.mem_sig2.1
  set X : Subgroup G := centralizer (P₀ : Set G) with hX
  set E : Subgroup G := rankThreeLayer X with hE
  have hEX : E ≤ X := uc22p22q_layer_le X
  have hXE : X ≤ normalizer (E : Set G) := fun x hx =>
    uc22p22qk_mem_normalizer fun y hy => uc22p22qo_layer_conj hx hy
  have h25 : 5 ≤ p ^ n := h5.trans (Nat.le_self_pow (by omega) p)
  have hLie : LieModel ↥E .PSL 2 p n :=
    Or.inl ⟨by decide, CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv _ p n h25 e⟩
  have hPX : P ≤ X := fun y hy => mem_centralizer_iff.2 fun z hz =>
    congrArg Subtype.val (hab.is_comm.comm ⟨z, hP₀P hz⟩ ⟨y, hy⟩)
  have hPG : IsSylowOf p P ⊤ :=
    uc22p22q_isSylowOf_top (UC6.dataOfSetup4 hS hU S) (sigma23Std_ofSetup4 hS hU S) hpσ hH.sylow
  have hSE : IsSylowOf p (P ⊓ E) E := (hPG.of_le hPX le_top).inf_of_le_normalizer hEX hXE
  have hle : P ⊓ E ≤ E := inf_le_right
  have hS' : IsSylowOf p ((P ⊓ E).subgroupOf E) ⊤ := by
    have := (isSylowOf_map_subtype_iff (p := p) E (A := (P ⊓ E).subgroupOf E) (B := ⊤)).1
    refine this ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_top, Subgroup.range_subtype]
    exact hSE
  obtain ⟨hel, hcard⟩ := uc22p22q_psl2_sylow_elem hp (by omega) hLie hS'
  refine ⟨n, hn, CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport p _ (P ⊓ E)
    (Subgroup.subgroupOfEquivOfLe hle) hel, ?_⟩
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
  exact hcard

theorem uc22p22qzb_centralizer_layer_le (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) {p : ℕ}
    {P P₀ : Subgroup G} (hH : UC6.Hyp612 (UC6.dataOfSetup4 hS hU S) p P P₀) (h5 : 5 ≤ p)
    (hab : IsMulCommutative P) (hcl : uniqueFourClauseTwo (UC6.dataOfSetup4 hS hU S).M P P₀ p) :
    centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G) ≤ (UC6.dataOfSetup4 hS hU S).M := by
  obtain ⟨n, hn, hel, hcard⟩ := uc22p22qzb_inter_layer hS hU S hH h5 hab hcl
  have hpσ : p ∈ (UC6.dataOfSetup4 hS hU S).sig := hH.mem_sig2.1
  have hp : p.Prime := ((UC6.dataOfSetup4 hS hU S).sig_prime p hpσ).1
  have hnc : ¬ IsCyclic ↥(P ⊓ rankThreeLayer (centralizer (P₀ : Set G))) :=
    uc22p22n_not_isCyclic_of_card hp hel (by rw [hcard]; exact Nat.pow_le_pow_right hp.pos hn)
  have hSM : P ⊓ rankThreeLayer (centralizer (P₀ : Set G)) ≤ (UC6.dataOfSetup4 hS hU S).M :=
    inf_le_left.trans hH.sylow.le
  have hNS := uc22p22q_normalizer_le_of_noncyclic (UC6.dataOfSetup4 hS hU S) (UC6.r6_1_dataOfSetup4 hS hU S)
    hpσ hSM hH.sylow.isPGroup.to_inf_left hnc
  exact (Subgroup.centralizer_le (SetLike.coe_subset_coe.2 inf_le_right)).trans
    ((_root_.Subgroup.centralizer_le_normalizer _).trans hNS)

theorem uc22p22qzb_not_two_dvd (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) {p : ℕ}
    {P P₀ : Subgroup G} (hH : UC6.Hyp612 (UC6.dataOfSetup4 hS hU S) p P P₀) (h5 : 5 ≤ p)
    (hab : IsMulCommutative P) (hcl : uniqueFourClauseTwo (UC6.dataOfSetup4 hS hU S).M P P₀ p) :
    ¬ 2 ∣ Nat.card ↥(centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G)) := by
  classical
  intro h2
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨n, hn, hel, hcard⟩ := uc22p22qzb_inter_layer hS hU S hH h5 hab hcl
  have hnot := hcl.2.2.2.2.1
  have hpσ : p ∈ (UC6.dataOfSetup4 hS hU S).sig := hH.mem_sig2.1
  have hp : p.Prime := ((UC6.dataOfSetup4 hS hU S).sig_prime p hpσ).1
  set E : Subgroup G := rankThreeLayer (centralizer (P₀ : Set G)) with hE
  obtain ⟨t, ht⟩ := exists_prime_orderOf_dvd_card' (G := ↥(centralizer (E : Set G))) 2 h2
  have ht' : orderOf (t : G) = 2 := by rw [Subgroup.orderOf_coe, ht]
  have hH2 : IsTwoLocal (normalizer ((zpowers (t : G) : Subgroup G) : Set G)) := by
    refine ⟨zpowers (t : G), ?_, ?_, rfl⟩
    · intro hbot
      have h1 : (t : G) ∈ zpowers (t : G) := mem_zpowers _
      rw [hbot, mem_bot] at h1
      rw [h1, orderOf_one] at ht'
      omega
    · exact IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, ht', pow_one])
  have hEH : E ≤ normalizer ((zpowers (t : G) : Subgroup G) : Set G) := by
    intro l hl
    refine uc22p22qk_mem_normalizer fun w hw => ?_
    obtain ⟨i, rfl⟩ := mem_zpowers_iff.1 hw
    have h1 : l * (t : G) = (t : G) * l := mem_centralizer_iff.1 t.2 l hl
    have h3 : l * (t : G) ^ i = (t : G) ^ i * l := Commute.zpow_right h1 i
    rw [h3, mul_inv_cancel_right]
    exact zpow_mem (mem_zpowers _) i
  have hrank : 2 ≤ Open.pRank p (P ⊓ E) :=
    hn.trans (CFSG.SectionRank.le_pRank hp.one_lt le_rfl hel hcard)
  have hSM : P ⊓ E ≤ S.M := inf_le_left.trans hH.sylow.le
  have hHM := UC6.sec61 hU S.maxLocal hH.mem_sig2.1 hSM hrank hH2 (inf_le_right.trans hEH)
  exact hnot (hEH.trans hHM)

@[expose] def Frob4Prime (D : Data G) : Prop :=
  ∀ (p : ℕ) (P P₀ : Subgroup G), UC6.Hyp612 D p P P₀ → 5 ≤ p → IsMulCommutative P →
    uniqueFourClauseTwo D.M P P₀ p →
    ∀ d ∈ centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G), (orderOf d).Prime →
      d ∈ centralizer (P₀ : Set G)

theorem uc22p22qzb_frobenius_iff (hS : Standing4 G) (hU : uniqueFourUnique G) (S : Setup4 G) {p : ℕ}
    {P P₀ : Subgroup G} (hH : UC6.Hyp612 (UC6.dataOfSetup4 hS hU S) p P P₀) (h5 : 5 ≤ p)
    (hab : IsMulCommutative P) (hcl : uniqueFourClauseTwo (UC6.dataOfSetup4 hS hU S).M P P₀ p) :
    uniqueFourIsFrobenius
        (uniqueFourPrimeCore p (UC6.dataOfSetup4 hS hU S).M ⊔
          centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G))
        (pCoreOf 2 (UC6.dataOfSetup4 hS hU S).M)
        (centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G)) ↔
      ∀ d ∈ centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G), d ≠ 1 →
        ∀ t ∈ pCoreOf 2 (UC6.dataOfSetup4 hS hU S).M, t * d = d * t → t = 1 := by
  classical
  refine ⟨fun hF => hF.2.2.2.2.2.2.2, fun hfpf => ?_⟩
  have hcl' := hcl
  obtain ⟨-, -, -, ⟨hf, -, -, -⟩, -, -, hfrob, -⟩ := hcl'
  haveI := hf
  obtain ⟨hT1, hV1, hTR, -, -, hReq, -, -⟩ := hfrob
  have hE1 := uc22p22qzb_le_centralizer_layer h5 hcl
  have hE2 := uc22p22qzb_centralizer_layer_le hS hU S hH h5 hab hcl
  have hE3 := uc22p22qzb_not_two_dvd hS hU S hH h5 hab hcl
  have hP₀D : P₀ ≤ centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G) := le_sup_right.trans hE1
  have hQM : uniqueFourPrimeCore p (UC6.dataOfSetup4 hS hU S).M ≤ (UC6.dataOfSetup4 hS hU S).M := by
    unfold uniqueFourPrimeCore relPPrimeCore
    exact sSup_le fun N hN => hN.1
  have hTle : pCoreOf 2 (UC6.dataOfSetup4 hS hU S).M ≤ uniqueFourPrimeCore p (UC6.dataOfSetup4 hS hU S).M ⊔
      centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G) :=
    hTR.trans (sup_le_sup_left hP₀D _)
  refine ⟨hT1, fun hbot => hV1 (le_bot_iff.1 (hE1.trans hbot.le)), hTle, ?_, le_sup_right, ?_, ?_, hfpf⟩
  · rw [Subgroup.normal_subgroupOf_iff_le_normalizer hTle]
    exact (sup_le hQM hE2).trans (UC6.le_normalizer_pCoreOf 2 _)
  · apply le_antisymm
    · exact sup_le ((le_sup_left.trans hReq.le).trans (sup_le_sup_left hE1 _)) le_sup_right
    · exact sup_le hTle le_sup_right
  ·
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    have hpg : IsPGroup 2 ↥(pCoreOf 2 (UC6.dataOfSetup4 hS hU S).M ⊓
        centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G)) :=
      (uc22p22qh_isPGroup_pCoreOf _).to_inf_left
    obtain ⟨k, hk⟩ := hpg.exists_card_eq
    have hdvd := Subgroup.card_dvd_of_le (inf_le_right (a := pCoreOf 2 (UC6.dataOfSetup4 hS hU S).M)
      (b := centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G)))
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact Subgroup.card_eq_one.1 hk
    · exact absurd ((dvd_pow_self 2 (Nat.succ_ne_zero k)).trans (hk ▸ hdvd)) hE3

theorem uc22p22qzb_frob4_iff {hS : Standing4 G} {hU : uniqueFourUnique G} {S : Setup4 G} :
    Frob4 (UC6.dataOfSetup4 hS hU S) ↔
      ∀ (p : ℕ) (P P₀ : Subgroup G), UC6.Hyp612 (UC6.dataOfSetup4 hS hU S) p P P₀ → 5 ≤ p →
        IsMulCommutative P → uniqueFourClauseTwo (UC6.dataOfSetup4 hS hU S).M P P₀ p →
        ∀ d ∈ centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G), d ≠ 1 →
          ∀ t ∈ pCoreOf 2 (UC6.dataOfSetup4 hS hU S).M, t * d = d * t → t = 1 :=
  ⟨fun hF p P P₀ hH h5 hab hcl => (uc22p22qzb_frobenius_iff hS hU S hH h5 hab hcl).1 (hF p P P₀ hH h5 hab hcl),
    fun hF p P P₀ hH h5 hab hcl => (uc22p22qzb_frobenius_iff hS hU S hH h5 hab hcl).2 (hF p P P₀ hH h5 hab hcl)⟩

theorem frob4_of_frob4Prime {hS : Standing4 G} {hU : uniqueFourUnique G} {S : Setup4 G}
    (h : Frob4Prime (UC6.dataOfSetup4 hS hU S)) : Frob4 (UC6.dataOfSetup4 hS hU S) := by
  refine uc22p22qzb_frob4_iff.2 fun p P P₀ hH h5 hab hcl d hd hd1 t ht htd => ?_
  have hcl' := hcl
  obtain ⟨-, -, -, ⟨hf, -, -, -⟩, -, -, -, -⟩ := hcl'
  haveI := hf
  have hord1 : orderOf d ≠ 1 := fun h1 => hd1 (orderOf_eq_one_iff.1 h1)
  obtain ⟨r, hr, hrd⟩ := Nat.exists_prime_and_dvd hord1
  have hu : orderOf (d ^ (orderOf d / r)) = r := orderOf_pow_orderOf_div (orderOf_pos d).ne' hrd
  have huD : d ^ (orderOf d / r) ∈ centralizer (rankThreeLayer (centralizer (P₀ : Set G)) : Set G) :=
    pow_mem hd _
  have huC := h p P P₀ hH h5 hab hcl _ huD (by rw [hu]; exact hr)
  have hu1 : d ^ (orderOf d / r) ≠ 1 := by
    intro h1
    rw [h1, orderOf_one] at hu
    exact hr.ne_one hu.symm
  exact uc22p22qza_fpf_of_mem_centralizer hcl huD huC hu1 t ht (Commute.pow_right htd _)

end CFSG.LocalAnalysis.UniquenessCase.UC22

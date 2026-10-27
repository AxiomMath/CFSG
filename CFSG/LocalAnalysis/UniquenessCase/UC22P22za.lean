module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qz
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qg
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qo
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22qs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.PartOneThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup CFSG.ABGLocalTools CFSG.GH74.GLS.IVK
open CFSG.Blueprint (LieModel)
open CFSG.ASVolI.ChIJK (IsWeaklyClosedIn)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22p22za_pRank_le_evenRank {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {H : Subgroup G} (hH : IsTwoLocal H) :
    CFSG.Open.pRank p H ≤ CFSG.Open.evenRank G := by
  refine le_csSup ⟨Nat.card G, ?_⟩ ⟨p, H, hp, hp2, hH, rfl⟩
  rintro _ ⟨q, K, hq, -, -, rfl⟩
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro j ⟨E, -, -, hj⟩
  have h1 : q ^ j ≤ Nat.card G := hj ▸ Subgroup.card_le_card_group E
  have h2 : j < q ^ j := Nat.lt_pow_self hq.one_lt
  omega

theorem uc22p22za_rank_le {p n : ℕ} [Fact p.Prime] {M P₀ P₁ : Subgroup G} (hP₀M : P₀ ≤ M) (hP₁M : P₁ ≤ M)
    (hP₀ : Nat.card P₀ = p) (hP₁el : IsElemAbelian p P₁) (hP₁ : Nat.card P₁ = p ^ n) (hnle : ¬ P₀ ≤ P₁)
    (hcomm : ∀ z ∈ P₀, ∀ y ∈ P₁, z * y = y * z) (hr3 : CFSG.Open.pRank p M ≤ 3) : n ≤ 2 := by
  have hp : p.Prime := Fact.out
  have hP₀el : IsElemAbelian p P₀ := UC6.isElemAbelian_of_card_prime hp hP₀
  have hEel : IsElemAbelian p (P₀ ⊔ P₁) := CFSG.Open.IsElemAbelian.sup_of_commute hP₀el hP₁el hcomm
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := p)).1 (uc22p22e_isPGroup_of_elem hEel)
  have hlt : P₁ < P₀ ⊔ P₁ := lt_of_le_of_ne le_sup_right (fun h => hnle (le_sup_left.trans h.ge))
  have hcl := Subgroup.card_lt_of_lt hlt
  rw [hP₁, hk] at hcl
  have hnk : n < k := (Nat.pow_lt_pow_iff_right hp.one_lt).1 hcl
  have hkr : k ≤ CFSG.Open.pRank p M := by
    unfold CFSG.Open.pRank
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨P₀ ⊔ P₁, sup_le hP₀M hP₁M, hEel, hk⟩
    rintro j ⟨E, -, -, hj⟩
    have h1 : p ^ j ≤ Nat.card G := hj ▸ Subgroup.card_le_card_group E
    have h2 : j < p ^ j := Nat.lt_pow_self hp.one_lt
    omega
  omega

theorem uc22p22za_cent_pair (D : Data G) (hstd : Sigma23Std D) (h61 : UC6.R6_1 D) {p : ℕ} {P P₀ : Subgroup G}
    (hH : UC6.Hyp612 D p P P₀) (hc2 : UC6.Clause2Print D p P P₀) (hr3 : CFSG.Open.pRank p D.M ≤ 3) :
    P ≤ centralizer ((P ⊓ UC6.inftyOf (centralizer (P₀ : Set G)) : Subgroup G) : Set G) := by
  have hid := uc22p22qo_ident_pair D hstd h61 hH hc2
  obtain ⟨h5, hsolv, hwc, ⟨hfact, n, hn2, ⟨e⟩⟩, hnot, hfrob, hN⟩ := hc2
  haveI : Fact p.Prime := hfact
  have hpP : p.Prime := hfact.out
  have hp2 : p ≠ 2 := by omega
  have hLie : LieModel (UC6.inftyOf (centralizer (P₀ : Set G))) .PSL 2 p n := by
    rw [hid]
    have h25 : 5 ≤ p ^ n := (by omega : 5 ≤ p).trans (Nat.le_self_pow (by omega) p)
    exact Or.inl ⟨by decide, CFSG.Assembly.LowTwoRank.statedClassicalModel_psl_two_of_mulEquiv _ p n h25 e⟩
  set X : Subgroup G := centralizer (P₀ : Set G) with hX
  set L : Subgroup G := UC6.inftyOf X with hLdef
  have hcen₀ : ∀ y ∈ P, ∀ z ∈ P₀, y * z = z * y :=
    uc22p22q_central_of_weaklyClosed hpP hH.sylow.isPGroup hH.le hH.card (uc22p22q_weak_elem hwc)
  have hPX : P ≤ X := fun y hy => Subgroup.mem_centralizer_iff.2 fun z hz => (hcen₀ y hy z hz).symm
  have hLX : L ≤ X := Subgroup.map_subtype_le _
  have hS : IsSylowOf p (P ⊓ L) L := uc22p22q_isSylowOf_P1 D hstd hH hwc
  have hle : P ⊓ L ≤ L := inf_le_right
  have hS' : IsSylowOf p ((P ⊓ L).subgroupOf L) ⊤ := by
    have := (isSylowOf_map_subtype_iff (p := p) L (A := (P ⊓ L).subgroupOf L) (B := ⊤)).1
    refine this ?_
    rw [Subgroup.map_subgroupOf_eq_of_le hle, Subgroup.map_top, Subgroup.range_subtype]
    exact hS
  obtain ⟨hel, hcard⟩ := uc22p22q_psl2_sylow_elem hpP hp2 hLie hS'
  have hP₁el : IsElemAbelian p (P ⊓ L) :=
    CFSG.RankThreeCoreUniqueness.Helpers.elementary_transport p _ (P ⊓ L)
      (Subgroup.subgroupOfEquivOfLe hle) hel
  have hP₁card : Nat.card (P ⊓ L : Subgroup G) = p ^ n := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hle).toEquiv]
    exact hcard
  haveI hsimple : IsSimpleGroup ↥L := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hLie
  have hdvd : p ^ n ∣ Nat.card ↥L := by
    rw [← hcard]
    exact Subgroup.card_subgroup_dvd_card _
  have hP₀L : ∀ z ∈ P₀, z ∈ L → z = 1 := fun z hz hzL =>
    uc22p22qz_eq_one_of_central hpP hn2 hdvd hzL fun l hl =>
      Subgroup.mem_centralizer_iff.1 (hLX hl) z hz
  have hP₀1 : P₀ ≠ ⊥ := by
    intro h
    have := hH.card
    rw [h, Subgroup.card_bot] at this
    exact hpP.one_lt.ne this
  have hnle : ¬ P₀ ≤ P ⊓ L := by
    intro hle'
    obtain ⟨⟨z, hz⟩, hz1⟩ := Subgroup.ne_bot_iff_exists_ne_one.1 hP₀1
    exact hz1 (Subtype.ext (hP₀L z hz (hle' hz).2))
  have hcomm : ∀ z ∈ P₀, ∀ y ∈ P ⊓ L, z * y = y * z := fun z hz y hy =>
    Subgroup.mem_centralizer_iff.1 (hLX hy.2) z hz
  have hn : n ≤ 2 :=
    uc22p22za_rank_le (hH.le.trans hH.sylow.le) (inf_le_left.trans hH.sylow.le) hH.card hP₁el hP₁card hnle
      hcomm hr3
  have hn2' : n = 2 := by omega
  have hpn : ¬ p ∣ n := fun hd => by
    have := Nat.le_of_dvd (by omega) hd
    omega
  obtain ⟨-, hSp, hSnd⟩ := isSylowOf_iff.1 hS'
  let W : Sylow p ↥L := hSp.toSylow (by simpa [Subgroup.relIndex_top_right] using hSnd)
  have hWmem : ∀ k : ↥L, k ∈ (W : Subgroup ↥L) ↔ (k : G) ∈ P ⊓ L := fun k => Subgroup.mem_subgroupOf
  obtain ⟨F, hFf, hFfin, e', hF, hFq⟩ := CFSG.GH74.GLS.EvenSelP.exists_l2Field_of_lieModel' hpP hp2 hLie
  obtain ⟨c, hstd', -⟩ := L2Borel.exists_isStd hpP hFq e' W
  have hodd : Odd (Nat.card F) := by
    rw [hFq]
    exact (hpP.odd_of_ne_two hp2).pow
  have h2 : (2 : F) ≠ 0 := L2Borel.two_ne_zero_of_odd_card hodd
  intro a ha
  rw [Subgroup.mem_centralizer_iff]
  intro y hy
  have haN : a ∈ normalizer (L : Set G) := by
    have haXN : a ∈ normalizer (X : Set G) := Subgroup.le_normalizer (hPX ha)
    rw [mem_normalizer_iff]
    intro x
    constructor
    · exact fun hx => uc22p22q_inftyOf_conj haXN hx
    · intro hx
      have := uc22p22q_inftyOf_conj (inv_mem haXN) hx
      simpa [mul_assoc] using this
  let α : MulAut ↥L := UC6.conjOn L haN
  have hαapp : ∀ k : ↥L, ((α k : ↥L) : G) = a * k * a⁻¹ := fun k => rfl
  have hstab : α ∈ MulAction.stabilizer (MulAut ↥L) (W : Subgroup ↥L) := by
    rw [L2Borel.mem_stabilizer_iff_forall]
    intro k
    rw [hWmem, hWmem, hαapp]
    constructor
    · intro hk
      refine ⟨?_, k.2⟩
      have h1 : a⁻¹ * (a * (k : G) * a⁻¹) * a ∈ P := P.mul_mem (P.mul_mem (P.inv_mem ha) hk.1) ha
      simpa [mul_assoc] using h1
    · intro hk
      exact ⟨P.mul_mem (P.mul_mem ha hk.1) (P.inv_mem ha), (α k).2⟩
  obtain ⟨j, hj⟩ := uc22p22qz_exists_pow hH.sylow.isPGroup ha
  have hα1 : α ^ p ^ j = 1 := by
    refine MulEquiv.ext fun k => Subtype.ext ?_
    rw [uc22p22qz_pow_apply hαapp, hj]
    simp
  have htriv := fun t : F =>
    uc22p22qz_action_trivial hstd' h2 hpP hFq (by omega : 1 ≤ n) hpn hstab hα1 t
  have hyW : (⟨y, hy.2⟩ : ↥L) ∈ (W : Subgroup ↥L) := (hWmem _).2 hy
  obtain ⟨t, ht⟩ := hstd'.exists_wt hyW
  have h3 : α ⟨y, hy.2⟩ = ⟨y, hy.2⟩ := by
    rw [ht]
    exact htriv t
  have h4 : a * y * a⁻¹ = y := congrArg Subtype.val h3
  calc y * a = (a * y * a⁻¹) * a := by rw [h4]
    _ = a * y := by group

theorem r613cent_ofSetup (hS : RankThreeUC.Standing G) (S : RankThreeUC.Setup G) :
    UC6.R613Cent (PartTwo.Three.dataOfSetup hS S) := by
  intro p P' P₀' hH'
  have hstd := sigma23Std_ofSetup hS S
  have h61 := PartTwo.Three.r6_1_dataOfSetup hS S
  obtain ⟨P, P₀, hH, hc2⟩ := sigma2Print_ofSetup hS S p hH'.mem_sig2
  have hpσ : p ∈ (PartTwo.Three.dataOfSetup hS S).sig := by
    rw [(PartTwo.Three.dataOfSetup hS S).sig_sub]
    exact Or.inl (Or.inr hH'.mem_sig2)
  have hpp := (PartTwo.Three.dataOfSetup hS S).sig_prime p hpσ
  have hr3 : CFSG.Open.pRank p (PartTwo.Three.dataOfSetup hS S).M ≤ 3 := by
    have := uc22p22za_pRank_le_evenRank hpp.1 hpp.2 (PartTwo.Three.dataOfSetup hS S).maxLocal.1
    rwa [hS.rank] at this
  have hcent := uc22p22za_cent_pair _ hstd h61 hH hc2 hr3
  have hd := uc22p22q_r613defAt_of _ hstd h61 hH hc2 (uc22p22qo_ident_pair _ hstd h61 hH hc2) hcent
  obtain ⟨m, hm, rfl, rfl⟩ := uc22p22qi_pair_conj _ hH hH' hc2.2.2.2.2.2.2
  exact (uc22p22qi_r613defAt_map _ hpp.1 hm hH.sylow.isPGroup hd).2

end CFSG.LocalAnalysis.UniquenessCase.UC22

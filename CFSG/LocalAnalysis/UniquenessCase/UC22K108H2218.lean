module

public import CFSG.LocalAnalysis.UniquenessCase.UC22K108HCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rx
import CFSG.LocalAnalysis.UniquenessCase.UC22P22c
import CFSG.Adapters.StatedPSLTwo
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22rt
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.FFModules CFSG.HardMathSupport.Meierfrankenfeld.GeneralFF
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem uc22p22r_false_of_fixed_H207 (D : Data G) (hK : F10.K108H207) (h201 : S20_1_124 D) (h204 : S20_4 D)
    (h207 : S20_7 D) (h1930 : H1930 D) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) {v : G} (hv1 : v ≠ 1)
    (hv2 : IsPGroup 2 (Subgroup.zpowers v)) (hvT : ∀ s ∈ D.T, s * v = v * s)
    (hCv : ¬ centralizer ({v} : Set G) ≤ D.M) {A : Subgroup G} (hAM : A ≤ D.M)
    (hAv : A ≤ centralizer ({v} : Set G)) (hA1 : A ≠ ⊥) (hAp : IsPGroup p A) (hAe : ∀ a ∈ A, a ^ p = 1)
    (hAc : ∀ a ∈ A, ∀ b ∈ A, a * b = b * a) (hAT : Permutes A D.T)
    (hAr : CFSG.Open.pRank p A ≤ 2) : False := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hQ1 : Subgroup.zpowers v ≠ ⊥ := by
    intro h
    exact hv1 (by simpa using (Subgroup.zpowers_eq_bot).1 h)
  have hloc : IsTwoLocal (normalizer ((Subgroup.zpowers v : Subgroup G) : Set G)) := ⟨_, hQ1, hv2, rfl⟩
  obtain ⟨H, hHmax, hNH⟩ := uc22p20a_exists_max_ge hloc
  have hCN : centralizer ({v} : Set G) ≤ normalizer ((Subgroup.zpowers v : Subgroup G) : Set G) := by
    intro g hg
    apply Subgroup.mem_normalizer_fintype
    intro y hy
    obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.1 hy
    have hc : Commute g v := Subgroup.mem_centralizer_singleton_iff.1 hg
    refine Subgroup.mem_zpowers_iff.2 ⟨i, ?_⟩
    rw [(hc.zpow_right i).eq, mul_inv_cancel_right]
  have hCH : centralizer ({v} : Set G) ≤ H := hCN.trans hNH
  have hTH : D.T ≤ H := fun s hs =>
    hCH (Subgroup.mem_centralizer_singleton_iff.2 (hvT s hs))
  have hHM : ¬ H ≤ D.M := fun h => hCv (hCH.trans h)
  have hH : H ∈ hSet D.T D.M := ⟨hTH, hHM, D.standing.charTwo H hHmax.1⟩
  have hAH : A ≤ H := hAv.trans hCH
  obtain ⟨L, K, hL, hKc, -, hKM⟩ := uc22p22r_exists_K D h204 h1930 hH
  have hU : ∀ a ∈ A, a ≠ 1 → Subgroup.zpowers a ∈ uniqueSet D.M := by
    intro a ha ha1
    refine uc22p22r_mem_uniqueSet_of_sp D hp hsp ((Subgroup.zpowers_le.2 ha).trans hAM)
      (hAp.to_le (Subgroup.zpowers_le.2 ha)) ?_
    intro h
    exact ha1 (by simpa using (Subgroup.zpowers_eq_bot).1 h)
  have hord : ∀ a ∈ A, a ≠ 1 → orderOf a = p := fun a ha ha1 =>
    orderOf_eq_prime (hAe a ha) ha1
  have hAK : A ≤ normalizer (K : Set G) := by
    intro a ha
    by_cases ha1 : a = 1
    · rw [ha1]
      exact Subgroup.one_mem _
    have hUa : ∀ h ∈ H, h⁻¹ * a * h ∈ D.M → h ∈ D.M := fun h _ hh =>
      uc22p22r_mem_of_conj_mem_of_unique D (hU a ha ha1) hh
    exact uc22p22r_normalizes_calC D h201 h1930 hH hL hKc hKM hp (hord a ha ha1) (hAH ha) (hAM ha) hUa
  obtain ⟨a, ha, ha1⟩ : ∃ a ∈ A, a ≠ 1 := by
    by_contra hcon
    push Not at hcon
    exact hA1 (eq_bot_iff.2 fun x hx => Subgroup.mem_bot.2 (hcon x hx))
  have hXp : Nat.card (Subgroup.zpowers a) = p := by
    rw [Nat.card_zpowers, hord a ha ha1]
  have hAo : Odd (Nat.card A) := by
    obtain ⟨k, hk⟩ := hAp.exists_card_eq
    rw [hk]
    exact (hp.odd_of_ne_two hp2).pow
  have hAr' : ∀ r : ℕ, r.Prime → r ∣ Nat.card A → CFSG.Open.pRank r A ≤ 2 := by
    intro r hr hrd
    obtain ⟨k, hk⟩ := hAp.exists_card_eq
    rw [hk] at hrd
    have hrp : r = p := (Nat.prime_dvd_prime_iff_eq hr hp).1 (hr.dvd_of_dvd_pow hrd)
    rw [hrp]
    exact hAr
  exact uc22p22r_hall_core_H207 D hK h201 h207 h1930 hH hL hKc hKM hAM hAK hAc hAo hAT hAr'
    (Subgroup.zpowers_le.2 ha) (hXp ▸ hp) (by rw [hXp]; exact hp2) (hU a ha ha1)

theorem uc22p22r_s22_18_of_k108H207 (D : Data G) (Ch : Choice2011 G) (hK : F10.K108H207)
    (h201 : S20_1_124 D) (h204 : S20_4 D) (h207 : S20_7 D) (hSg : UC6S846.SigmaStd D) (h8 : S22_8 D Ch)
    (hV : S22_V D Ch) (h15 : S22_15 D Ch) (h17 : S22_17 D Ch) : S22_18 D Ch := by
  intro h1930 c p hp K n hK2213 t htT htK
  by_contra hne
  classical
  obtain ⟨hpP, hp2⟩ := D.sig_prime p hp
  haveI : Fact p.Prime := ⟨hpP⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKC : K ∈ calC D.M := hK2213.1
  have hKM : K ≤ D.M := uc22p22a_le_of_isSubnormal hKC.1
  have htM : t ∈ D.M := D.sylowM.le htT
  have hnn : ¬ (K.subgroupOf D.M).Normal := fun hn =>
    htK (((Subgroup.normal_subgroupOf_iff_le_normalizer hKM).1 hn) htM)
  set Kb := mbarImage D.M c.V K with hKbdef
  have hL2 : IsL2 ↥Kb n := h15 h1930 c p hp K n hK2213
  haveI hKbs : IsSimpleGroup ↥Kb := CFSG.Blueprint.LieModel.isSimpleGroup_psl_two hL2
  have hZK := uc22p22g_center_bot hL2
  have hnt : Kb ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot _).1 inferInstance
  have hKV : ¬ K ≤ centralizer (c.V : Set G) := fun hle =>
    hnt ((uc22br4_mbarImage_eq_bot_iff D.M c.V K c.hVM hKM).2 hle)
  have hred : TwoReduced D.M c.V := (hV h1930 c).1.2.2
  have hpc : CFSG.pCore 2 (MBar D.M c.V) = ⊥ := (uc22br4_pCore_bot_iff D.M c.V c.hVM).2 hred
  have hcomp := uc22br4_isComponentOf_mbarImage D.M c.V K c.hVM hpc hKC hKV
  have h3 : (((2 < n ∧ (IsL2 ↥Kb n ∨ IsSz ↥Kb n)) ∨ (IsJ1 ↥Kb ∧ n = 3)) ∧ (conjSetOf D.M K).ncard = 2) := by
    rcases hK2213.2.2 with ⟨hsp, -, -⟩ | ⟨hsu, -⟩ | h3 | ⟨hyp, -, -⟩
    · exfalso
      obtain ⟨e⟩ := uc22p21k_quotCenter_equiv hZK
      exact uc22p21k_not_isL2 hcomp.2.2 (Or.inl ⟨n, CFSG.Blueprint.LieModel.of_mulEquiv e.symm hsp⟩) n hL2
    · exact (uc22p21k_not_isL2 hcomp.2.2 (Or.inr ⟨n, hsu.2⟩) n hL2).elim
    · exact h3
    · exact (hnn (hyp.2.1 K hKC).1).elim
  have hn3 : 3 ≤ n := by
    rcases h3.1 with ⟨h, -⟩ | ⟨-, h⟩ <;> omega
  have hpn : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] := by
    rcases hK2213.2.1 with ⟨-, -, -, hnot⟩ | h | ⟨hSz, -⟩
    · exact (hnot hL2).elim
    · exact h
    · exact (uc22p22g_isSz_isL2_false hSz hL2).elim
  set tb : MBar D.M c.V := QuotientGroup.mk (⟨t, htM⟩ : ↥D.M) with htb
  have hne' : K.map (MulAut.conj t).toMonoidHom ≠ K := fun h =>
    htK (Subgroup.mem_normalizer_iff_map_conj_eq.2 h)
  have hKt : K.map (MulAut.conj t).toMonoidHom ∈ CFSG.Quasithin.cComp D.M :=
    uc22p20b_cj_mem_cComp (uc22p20e_cComp_of_calC hKC) htM
  have hbarne : Kb ≠ mbarImage D.M c.V (K.map (MulAut.conj t).toMonoidHom) :=
    uc22p22d_mbarImage_ne D.M c.V hKC hKt hne'.symm hnt
  have hKt' : mbarImage D.M c.V (K.map (MulAut.conj t).toMonoidHom) = Kb.map (MulAut.conj tb).toMonoidHom :=
    uc22br4_mbarImage_map_conj D.M c.V K ⟨t, htM⟩
  have hbarne' : Kb ≠ Kb.map (MulAut.conj tb).toMonoidHom := hKt' ▸ hbarne
  have hKtM : K.map (MulAut.conj t).toMonoidHom ≤ D.M := by
    rintro _ ⟨k, hk, rfl⟩
    exact D.M.mul_mem (D.M.mul_mem htM (hKM hk)) (D.M.inv_mem htM)
  have hXbar : mbarImage D.M c.V (K ⊔ K.map (MulAut.conj t).toMonoidHom) =
      Kb ⊔ Kb.map (MulAut.conj tb).toMonoidHom := by
    rw [← hKt', hKbdef]
    unfold mbarImage
    rw [Subgroup.subgroupOf_sup hKM hKtM, Subgroup.map_sup]
  have hclosure : conjClosure D.M K = K ⊔ K.map (MulAut.conj t).toMonoidHom :=
    uc22p22d_conjClosure_pair htM hne' h3.2
  have hlg : Ext.lgConj Kb = Kb ⊔ Kb.map (MulAut.conj tb).toMonoidHom := by
    rw [hKbdef, uc22br4_lgConj_mbarImage D.M c.V K hKM, hclosure, hXbar]
  have hXn : (Kb ⊔ Kb.map (MulAut.conj tb).toMonoidHom).Normal := hlg ▸ uc22p22r_lgConj_normal Kb
  have hcomp' : CFSG.Open.IsComponentOf (Kb.map (MulAut.conj tb).toMonoidHom) ⊤ := by
    refine CFSG.ComponentClassification.LocalComponents.image hcomp (MulAut.conj tb).toMonoidHom
      (MulAut.conj tb).surjective ?_
    intro hle
    apply hnt
    rw [eq_bot_iff]
    intro x hx
    have h1 := hle hx
    rw [MonoidHom.mem_ker] at h1
    have h1' : (MulAut.conj tb) x = 1 := h1
    rw [Subgroup.mem_bot]
    exact (MulAut.conj tb).injective (by rw [h1', map_one])
  have hcommb : ∀ a ∈ Kb, ∀ b ∈ Kb.map (MulAut.conj tb).toMonoidHom, a * b = b * a := by
    have h1 := CFSG.ComponentClassification.LocalComponents.commute_of_ne _ _ hcomp hcomp' hbarne'
    intro a ha b hb
    have h2 : ⁅a, b⁆ ∈ ⁅Kb, Kb.map (MulAut.conj tb).toMonoidHom⁆ := Subgroup.commutator_mem_commutator ha hb
    rw [h1, Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm] at h2
    exact h2
  have hTb : CFSG.ABGLocalTools.IsSylowOf 2 (mbarImage D.M c.V D.T) ⊤ :=
    uc22p22r_isSylowOf_mbarImage D.sylowM
  have htbT : tb ∈ mbarImage D.M c.V D.T := ⟨⟨t, htM⟩, htT, rfl⟩
  have htbK : tb ∉ normalizer (Kb : Set (MBar D.M c.V)) := by
    intro h
    have := Subgroup.mem_normalizer_iff_map_conj_eq.1 h
    exact hbarne' this.symm
  have hneb : Kb ⊔ Kb.map (MulAut.conj tb).toMonoidHom ≠
      CFSG.RankThree.PartOne.pElementSubgroup p ⊤ := by
    rw [← hXbar]
    exact hne
  have hel : CFSG.Open.IsElemAbelian 2 c.V := (hV h1930 c).1.1.1.2.2.2
  obtain ⟨Vmod, _, _, _, e, ρ, hc⟩ := uc22br4_exists_conjModule D.M c.V c.hVM hel
  have hfaith : Function.Injective ρ := uc22br4_injective D.M c.V c.hVM e ρ hc
  have hsh := h17 h1930 c p hp K n hK2213 t htT htK Vmod e ρ hc
  rw [hXbar, hKt'] at hsh
  obtain ⟨Y, hY, hF1, hF2⟩ := uc22p22r_shape_facts ρ hfaith hpP hp2 hpn hn3 hL2 hcommb hsh
  obtain ⟨R, z, hRT, hRn, hzR, hzo, hRz, w, hw0, hwfix⟩ :=
    uc22p22r_exists_rbar ρ hpP hp2 hpn hL2 hTb htbT htbK hcommb hXn hneb hF1 hY hF2
  have hrk : CFSG.Open.pRank p (D.M ⊓ centralizer (c.V : Set G)) ≤ 1 := ((hV h1930 c).2 p hp).2
  obtain ⟨v, hvV, hv1, hvT, A, hAM, hAv, hA1, hAp, hAe, hAc, hAT, hAr⟩ :=
    uc22p22r_lift c.hVM D.sylowM e ρ hc hpP hp2 hrk hRT hRn hzR hzo hRz hw0 hwfix
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M := hSg.sig1_sp p (h8 h1930 c ▸ hp)
  obtain ⟨hVU1, -⟩ := uc22p22c_U_facts D
  have hVT : c.V ≤ D.T := (c.hVU.trans (hVU1.trans inf_le_left)).trans (uc22p22c_pCoreOf_le_T D)
  have hvT' : v ∈ D.T := hVT hvV
  have hv2 : v ^ 2 = 1 := hel.2 v hvV
  have hvZ : v ∈ D.Z := by
    have hcen : (⟨v, hvT'⟩ : ↥D.T) ∈ Subgroup.center ↥D.T := by
      rw [Subgroup.mem_center_iff]
      intro s
      exact Subtype.ext (hvT s s.2)
    show v ∈ CFSG.RankThree.PartOne.omegaOneCenterIn D.T
    unfold CFSG.RankThree.PartOne.omegaOneCenterIn CFSG.RankThree.PartOne.omegaOne
    exact Subgroup.subset_closure ⟨⟨⟨v, hvT'⟩, hcen, rfl⟩, hv2⟩
  have hCZ : centralizer (D.Z : Set G) ≤ centralizer ({v} : Set G) :=
    Subgroup.centralizer_le (Set.singleton_subset_iff.2 hvZ)
  have hCv : ¬ centralizer ({v} : Set G) ≤ D.M := fun h => c.hC (hCZ.trans h)
  have hvp : IsPGroup 2 ↥(Subgroup.zpowers v) := by
    have h1 : orderOf v ∣ 2 ^ 1 := orderOf_dvd_of_pow_eq_one (by rw [pow_one]; exact hv2)
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1 h1
    exact IsPGroup.of_card (by rw [Nat.card_zpowers, hj])
  exact uc22p22r_false_of_fixed_H207 D hK h201 h204 h207 h1930 hpP hp2 hsp hv1 hvp hvT hCv hAM hAv hA1 hAp hAe hAc
    hAT hAr

end CFSG.LocalAnalysis.UniquenessCase.UC22

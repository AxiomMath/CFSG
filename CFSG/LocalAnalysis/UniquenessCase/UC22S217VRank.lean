module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S217VJ1
import CFSG.LocalAnalysis.UniquenessCase.UC22P21a
import CFSG.LocalAnalysis.UniquenessCase.UC22P218a
import CFSG.LocalAnalysis.UniquenessCase.UC22P218s
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214c
import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
import CFSG.LocalAnalysis.UniquenessCase.UC22FinThreeK1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.ProofsNineteenJankoOne
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.JankoOne
import CFSG.Timmesfeld.Bridge.RootStructR2Incidence
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.ABGLocalTools Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

theorem uc22s217v_not_sp (D : Data G) (Ch : Choice2011 G) (hH : H1930 D) (c : Ctx21 D Ch)
    {b : G} (hb : b ∈ c.B0) {r : ℕ} (hr : r.Prime) (hbr : orderOf b = r) :
    ¬ IsStronglyPEmbedded r D.M := by
  intro hsp
  haveI : Fact r.Prime := ⟨hr⟩
  have hZ1 : zpowers b ≠ ⊥ := zpowers_ne_bot.2 fun h => by
    rw [h, orderOf_one] at hbr; exact hr.one_lt.ne hbr
  exact s21_2 D Ch hH { c with B := c.B0, hB := c.hB0, hle := le_rfl } (zpowers b)
    (zpowers_le.2 hb) (hsp.normalizer_le hZ1
      (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hbr, pow_one]))
      (zpowers_le.2 (c.hBM hb)))

theorem uc22s217v_ncard_le_three (D : Data G) (hSg : UC6S846.SigmaStd D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hJ1 : IsJ1 (Bar2 L)) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrJ : r ∣ 175560) (hnsp : ¬ IsStronglyPEmbedded r D.M) : (conjSetOf D.M L).ncard ≤ 3 := by
  classical
  have hns := UC6S846.not_solvable_of_mem_calC hL
  have hrM : CFSG.Open.pRank r D.M ≤ 3 := by
    by_contra h
    exact hnsp (UC6S846.sp_of_mem_sig hSg hns (hSg.four_mem r hr hr2 (by omega)))
  have hfin := Set.toFinite (conjSetOf D.M L)
  rw [Set.ncard_eq_toFinset_card _ hfin]
  refine le_trans (P22fin3.card_le_pRank_of_finset hr hr2 (fun K hK => ?_) (fun K hK => ?_)
    (fun K hK => ?_)) hrM
  · exact uc22p2214_calC_of_mem_conjSetOf hL (hfin.mem_toFinset.1 hK)
  · have hKC := uc22p2214_calC_of_mem_conjSetOf hL (hfin.mem_toFinset.1 hK)
    have hJK := uc22s217v_isJ1_of_mem hJ1 (hfin.mem_toFinset.1 hK)
    haveI := (kJ1_holds _ hJK).2.1
    rw [uc22p21k_center_eq_bot hKC.2.2, Subgroup.card_bot]
    exact hr.not_dvd_one
  · have hJK := uc22s217v_isJ1_of_mem hJ1 (hfin.mem_toFinset.1 hK)
    exact (show r ∣ Nat.card (Bar2 K) by rw [(kJ1_holds _ hJK).1]; exact hrJ).trans
      (Subgroup.card_quotient_dvd_card _)

theorem uc22s217v_exists_three_mem_normalizer {K T : Subgroup G} (hT : IsPGroup 2 T)
    (hTK : T ≤ normalizer (K : Set G)) (hS : IsSylowOf 2 (T ⊓ K) K) (hJ1 : IsJ1 (Bar2 K)) :
    ∃ u ∈ K, orderOf u = 3 ∧ u ∈ normalizer (T : Set G) := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hinn : (T.subgroupOf (normalizer (K : Set G))).map (UC6S846.rhoL K) ≤
      (MulAut.conj : Bar2 K →* MulAut (Bar2 K)).range := by
    rintro θ ⟨t, -, ht⟩
    obtain ⟨x, hx⟩ := (kJ1_holds (Bar2 K) hJ1).2.2 (UC6S846.rhoL K t)
    exact ⟨x, by rw [← hx]; exact ht⟩
  have hle := inf_normalizer_le_normalizer_of_inner hT hTK hS hinn
  obtain ⟨Q, hQ⟩ := hS
  let π : ↥K →* Bar2 K := QuotientGroup.mk' (CFSG.pCore 2 ↥K)
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective _
  obtain ⟨ybar, hybarN, hybar3⟩ :=
    exists_orderOf_eq_three_mem_normalizer_of_isJ1 hJ1 (Q.mapSurjective (f := π) hπ)
  obtain ⟨y, rfl⟩ := hπ ybar
  have hker : π.ker ≤ Q := by
    rw [show π.ker = CFSG.pCore 2 ↥K from QuotientGroup.ker_mk' _]
    exact CFSG.fitting_pCore_le_sylow Q
  have hyQ : y ∈ normalizer ((Q : Subgroup ↥K) : Set ↥K) := by
    have h1 := Subgroup.le_normalizer_comap
      (H := ((Q.mapSurjective (f := π) hπ : Sylow 2 (Bar2 K)) : Subgroup (Bar2 K))) π hybarN
    rwa [Sylow.coe_mapSurjective, Subgroup.comap_map_eq_self hker] at h1
  have hyT : (y : G) ∈ normalizer (T : Set G) := by
    refine hle ⟨y.2, ?_⟩
    have h2 := Subgroup.le_normalizer_map (H := (Q : Subgroup ↥K)) K.subtype ⟨y, hyQ, rfl⟩
    rwa [hQ] at h2
  have h3 : 3 ∣ orderOf (y : G) := by
    rw [Subgroup.orderOf_coe, ← hybar3]
    exact orderOf_map_dvd π y
  exact ⟨(y : G) ^ (orderOf (y : G) / 3), K.pow_mem y.2 _,
    orderOf_pow_orderOf_div (orderOf_pos (y : G)).ne' h3,
    (normalizer (T : Set G)).pow_mem hyT _⟩

theorem uc22s217v_false_of_ncard_three (D : Data G) (Ch : Choice2011 G) (h211 : S21_1 D Ch)
    (h8107 : F08.R8107 D) (hH : H1930 D) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hc3 : (conjSetOf D.M L).ncard = 3) (hJ1 : IsJ1 (Bar2 L)) : False := by
  classical
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hstab : ∀ t ∈ D.T, ∀ K ∈ conjSetOf D.M L,
      K.map (MulAut.conj t).toMonoidHom ∈ conjSetOf D.M L := by
    rintro t ht K ⟨m, hmM, rfl⟩
    exact ⟨t * m, D.M.mul_mem (D.sylowM.le ht) hmM, by rw [uc22p22d_map_conj_map_conj]⟩
  obtain ⟨K, hK, hfix⟩ := CFSG.Timmesfeld.Bridge.exists_map_conj_eq_of_isPGroup (p := 2)
    D.sylowM.isPGroup hstab (by rw [hc3]; norm_num)
  have hTK : D.T ≤ normalizer (K : Set G) := fun t ht =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hfix t ht)
  have hKC := uc22p2214_calC_of_mem_conjSetOf hL hK
  have hJK := uc22s217v_isJ1_of_mem hJ1 hK
  have hS : IsSylowOf 2 (D.T ⊓ K) K :=
    (D.sylowM.of_le le_sup_left (sup_le D.sylowM.le hKC.1.le)).inf_of_le_normalizer le_sup_right
      (sup_le hTK Subgroup.le_normalizer)
  obtain ⟨u, huK, huo, huT⟩ :=
    uc22s217v_exists_three_mem_normalizer D.sylowM.isPGroup hTK hS hJK
  rw [← uc22p2214_conjSetOf_eq hK] at hc3
  obtain ⟨K', hK', hK'K⟩ := Set.exists_ne_of_one_lt_ncard (by rw [hc3]; norm_num) K
  have hU := uc22s217v_mem_uniqueSet D h8107 hKC (uc22p2214_calC_of_mem_conjSetOf hKC hK')
    hK'K.symm hJK (uc22s217v_isJ1_of_mem hJK hK') (zpowers_le.2 huK)
    (by rw [Nat.card_zpowers, huo])
  exact uc22p218s_false_of_le_normalizer D Ch h211 hH c Nat.prime_three (by norm_num) huo hU
    (zpowers_le.2 huT)

end CFSG.LocalAnalysis.UniquenessCase.UC22

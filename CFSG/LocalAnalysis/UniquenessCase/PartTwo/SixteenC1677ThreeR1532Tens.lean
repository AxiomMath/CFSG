module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKTensProd
public import CFSG.Adapters.LieModelSimple
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclCard
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC165ExclDirect
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC7SixtyTwoComp
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10NatRank
public import CFSG.Quasithin.EmptyFaithful.T1515C4Mod

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

section Generic

variable {W : Type} [CommGroup W]

private theorem s168e3_pCoreOf_isPGroup {A : Type*} [Group A] (p : ℕ) (H : Subgroup A) :
    IsPGroup p ↥(CFSG.Open.pCoreOf p H) := by
  rw [CFSG.Open.pCoreOf]
  exact (CFSG.pCore_isPGroup (p := p) (G := ↥H)).map H.subtype

private theorem s168e3_center_ne_top {Q : Type*} [Group Q] (hQ : CFSG.Open.IsQuasisimple Q) :
    Subgroup.center Q ≠ ⊤ := by
  intro h
  haveI : IsSimpleGroup (Q ⧸ Subgroup.center Q) := hQ.2
  obtain ⟨p, q, hpq⟩ := exists_pair_ne (Q ⧸ Subgroup.center Q)
  obtain ⟨p, rfl⟩ := QuotientGroup.mk_surjective p
  obtain ⟨q, rfl⟩ := QuotientGroup.mk_surjective q
  exact hpq (QuotientGroup.eq.mpr (h ▸ Subgroup.mem_top _))

private theorem s168e3_not_comm_of_quasisimple {Q : Type*} [Group Q]
    (hQ : CFSG.Open.IsQuasisimple Q) : ¬ ∀ a b : Q, a * b = b * a := by
  intro hc
  refine s168e3_center_ne_top hQ ?_
  rw [eq_top_iff]
  intro x _
  rw [Subgroup.mem_center_iff]
  intro y
  exact (hc x y).symm

private theorem s168e3_not_comm_of_isAlt_five {X : Type} [Group X]
    (h : UC22.IsAlt X 5) : ¬ ∀ a b : X, a * b = b * a := by
  obtain ⟨e⟩ := h
  intro hcomm
  have hcomm' : ∀ a b : alternatingGroup (Fin 5), a * b = b * a := fun a b => by
    calc a * b = e (e.symm a * e.symm b) := by
          rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
      _ = e (e.symm b * e.symm a) := by rw [hcomm]
      _ = b * a := by rw [map_mul, e.apply_symm_apply, e.apply_symm_apply]
  have hle := (alternatingGroup.isMulCommutative_iff_card_le_three (α := Fin 5)).mp
    (isMulCommutative_iff.mpr hcomm')
  rw [Nat.card_eq_fintype_card, Fintype.card_fin] at hle
  omega

private theorem s168e3_153_2_not_comm [Finite W] {K₀ : Subgroup (MulAut W)} {p : ℕ}
    (hK : (p = 5 ∧ UC22.IsAlt ↥K₀ 5) ∨ (p = 7 ∧ UC22.IsL3 ↥K₀ 1)) :
    ¬ ∀ a b : ↥K₀, a * b = b * a := by
  rcases hK with ⟨-, h⟩ | ⟨-, h⟩
  · exact s168e3_not_comm_of_isAlt_five h
  · exact s168e3_not_comm_of_quasisimple (s16c7_isQuasisimple_of_isL3 h)

private theorem s168e3_153_2_not_prime_power {m p : ℕ} (hm : m = 60 ∨ m = 168)
    (hp : p.Prime) {n : ℕ} (h : m ^ 2 = p ^ n) : False := by
  have h2 : 2 ∣ m := by rcases hm with h | h <;> rw [h] <;> norm_num
  have h3 : 3 ∣ m := by rcases hm with h | h <;> rw [h] <;> norm_num
  have hmdvd : m ∣ p ^ n := by rw [← h]; exact dvd_pow_self m (by norm_num)
  have h2p : 2 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_two (h2.trans hmdvd)
  have h3p : 3 ∣ p := Nat.Prime.dvd_of_dvd_pow Nat.prime_three (h3.trans hmdvd)
  have hp2 : p = 2 := (hp.dvd_iff_eq (by norm_num : (2 : ℕ) ≠ 1)).1 h2p
  have hp3 : p = 3 := (hp.dvd_iff_eq (by norm_num : (3 : ℕ) ≠ 1)).1 h3p
  omega

private theorem s168e3_153_2_not_quasisimple {A : Type*} [Group A] {L K₀ N : Subgroup A}
    (hdir : IsDirectProdOfConj L K₀ N) (h2 : (conjSet K₀ N).ncard = 2)
    (hLcard : Nat.card ↥L = Nat.card ↥K₀ ^ 2)
    (hK0card : Nat.card ↥K₀ = 60 ∨ Nat.card ↥K₀ = 168)
    (hnab : ¬ ∀ a b : ↥K₀, a * b = b * a) :
    ¬ CFSG.Open.IsQuasisimple ↥L := by
  intro hq
  have hK0mem : K₀ ∈ conjSet K₀ N := s15_T7_mem_conjSet_self K₀ N
  have hK0leL : K₀ ≤ L := hdir.1 K₀ hK0mem
  have hnorm : L ≤ Subgroup.normalizer (K₀ : Set A) := by
    rw [← hdir.2.1]
    refine iSup_le fun Y => iSup_le fun hY => ?_
    by_cases hYK : Y = K₀
    · rw [hYK]; exact Subgroup.le_normalizer
    · have hcomm : ⁅K₀, Y⁆ = ⊥ :=
        hdir.2.2.1 K₀ hK0mem Y hY (fun h => hYK h.symm)
      rw [Subgroup.commutator_comm] at hcomm
      exact (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm).trans
        (Subgroup.centralizer_le_normalizer _)
  have hN : (K₀.subgroupOf L).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hK0leL).2 hnorm
  have hne_top : K₀.subgroupOf L ≠ ⊤ := by
    intro htop
    have h1 : Nat.card ↥(K₀.subgroupOf L) = Nat.card ↥L := by
      rw [htop, Nat.card_congr Subgroup.topEquiv.toEquiv]
    have h2 : Nat.card ↥(K₀.subgroupOf L) = Nat.card ↥K₀ :=
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hK0leL).toEquiv
    rw [h2, hLcard] at h1
    rcases hK0card with h | h <;> rw [h] at h1 <;> norm_num at h1
  haveI := hN
  have hle := CFSG.ComponentClassification.Quasisimple.normal_le_center_of_ne_top
    hq (K₀.subgroupOf L) hne_top
  exact hnab fun a b => by
    have hc := Subgroup.mem_center_iff.mp
      (hle (show (⟨a.1, hK0leL a.2⟩ : ↥L) ∈ K₀.subgroupOf L from a.2))
      (⟨b.1, hK0leL b.2⟩ : ↥L)
    exact Subtype.ext (congrArg Subtype.val hc).symm

theorem s168e3_natTensor_rk {H : Subgroup (MulAut W)} {U : Subgroup W} {d a : ℕ}
    (h : NatTensor H U ⊥ d a) : rk ↥U = d * d * a := by
  obtain ⟨K, hfield, hfinite, hcard, π, hπ⟩ := h
  letI := hfield
  letI := hfinite
  obtain ⟨-, -, -, -, -, -, -, β, hβs, hβk, -⟩ := hπ
  have hinj : Function.Injective β := by
    rw [injective_iff_map_eq_one]
    intro u hu
    have := (hβk u).1 hu
    exact Subtype.ext (by simpa using this)
  have hd : Nat.card (Fin d) = d := by
    rw [Nat.card_eq_fintype_card, Fintype.card_fin]
  have hmat : Nat.card (Matrix (Fin d) (Fin d) K) = Nat.card K ^ (d * d) := by
    change Nat.card (Fin d → Fin d → K) = Nat.card K ^ (d * d)
    rw [Nat.card_fun, Nat.card_fun, hd, ← pow_mul]
  have hUcard : Nat.card ↥U = 2 ^ (d * d * a) := by
    calc Nat.card ↥U
        = Nat.card (↥(⊤ : Subgroup (Multiplicative (Matrix (Fin d) (Fin d) K))) ⧸
            ((⊥ : Subgroup (Multiplicative (Matrix (Fin d) (Fin d) K))).subgroupOf ⊤)) :=
          Nat.card_congr (Equiv.ofBijective β ⟨hinj, hβs⟩)
      _ = Nat.card (Multiplicative (Matrix (Fin d) (Fin d) K)) :=
          Nat.card_congr (CFSG.Quasithin.B5.natQuotEquiv _).toEquiv
      _ = Nat.card (Matrix (Fin d) (Fin d) K) := Nat.card_congr Multiplicative.toAdd
      _ = Nat.card K ^ (d * d) := hmat
      _ = (2 ^ a) ^ (d * d) := by rw [hcard]
      _ = 2 ^ (d * d * a) := by rw [← pow_mul, mul_comm a (d * d)]
  rw [s16c1610_rk_of_card_two_pow hUcard]

theorem s168e3_153_2_tensor [Finite W] {A L K₀ : Subgroup (MulAut W)} {t : MulAut W}
    (hW : Conc4_136W A t L)
    (hdir : IsDirectProdOfConj L K₀ (A ⊓ Subgroup.normalizer (L : Set (MulAut W))))
    (h2 : (conjSet K₀ (A ⊓ Subgroup.normalizer (L : Set (MulAut W)))).ncard = 2) {p : ℕ}
    (hK : (p = 5 ∧ UC22.IsAlt ↥K₀ 5) ∨ (p = 7 ∧ IsL3 ↥K₀ 1)) :
    (p = 5 ∧ NatTensor L (commSub ⊤ L) ⊥ 2 2) ∨ (p = 7 ∧ NatTensor L (commSub ⊤ L) ⊥ 3 1) := by
  have hK0card : Nat.card ↥K₀ = 60 ∨ Nat.card ↥K₀ = 168 := by
    rcases hK with ⟨-, h⟩ | ⟨-, h⟩
    · exact Or.inl (Om8Excl.card_isAlt_five h)
    · exact Or.inr (Om8Excl.card_isL3_one h)
  have hLcard : Nat.card ↥L = Nat.card ↥K₀ ^ 2 := Om8Excl.card_eq_sq_of_ncard_two hdir h2
  have hnab := s168e3_153_2_not_comm hK
  obtain ⟨-, -, hcases⟩ := hW
  rcases hcases with h133 | hcomp2 | hcomp3 | hcomp4
  · obtain ⟨p', hp'prime, hLpcore, -⟩ := h133
    haveI : Fact p'.Prime := ⟨hp'prime⟩
    have hpgroup : IsPGroup p' ↥L := (s168e3_pCoreOf_isPGroup p' A).to_le hLpcore
    obtain ⟨n, hn⟩ := hpgroup.exists_card_eq
    exact (s168e3_153_2_not_prime_power hK0card hp'prime (by rw [← hLcard, hn])).elim
  · obtain ⟨K, hKcomp, g, hg, hne, hLK, htens⟩ := hcomp2
    have hKL : Nat.card ↥L = Nat.card ↥K ^ 2 := by
      rcases htens with ⟨hL3K, -⟩ | ⟨hL2K, -⟩ | ⟨hL3K, -⟩
      · have hsimple : IsSimpleGroup ↥K :=
          CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3K
        obtain ⟨-, -, ⟨e⟩⟩ := s16k_components_conj hKcomp hg hne hsimple
        rw [hLK, Nat.card_congr e.toEquiv, Nat.card_prod,
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
        ring
      · have hsimple : IsSimpleGroup ↥K :=
          CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2K
        obtain ⟨-, -, ⟨e⟩⟩ := s16k_components_conj hKcomp hg hne hsimple
        rw [hLK, Nat.card_congr e.toEquiv, Nat.card_prod,
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
        ring
      · have hsimple : IsSimpleGroup ↥K :=
          CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL3K
        obtain ⟨-, -, ⟨e⟩⟩ := s16k_components_conj hKcomp hg hne hsimple
        rw [hLK, Nat.card_congr e.toEquiv, Nat.card_prod,
          Subgroup.card_map_of_injective (MulAut.conj g).injective]
        ring
    have hKeq : Nat.card ↥K = Nat.card ↥K₀ :=
      Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) (hKL.symm.trans hLcard)
    rcases htens with ⟨hL3K, hT31⟩ | ⟨hL2K2, hT22⟩ | ⟨hL2K3, hT23⟩
    · have hKcard : Nat.card ↥K = 168 := Om8Excl.card_isL3_one hL3K
      rw [hKcard] at hKeq
      rcases hK with ⟨hp5, hAlt⟩ | ⟨hp7, -⟩
      · have := Om8Excl.card_isAlt_five hAlt; omega
      · exact Or.inr ⟨hp7, hT31⟩
    · have hKcard : Nat.card ↥K = 60 := by
        have hc := uc22p22r_L2_card hL2K2
        norm_num at hc ⊢
        exact hc
      rw [hKcard] at hKeq
      rcases hK with ⟨hp5, -⟩ | ⟨hp7, hL3₀⟩
      · exact Or.inl ⟨hp5, hT22⟩
      · have := Om8Excl.card_isL3_one hL3₀; omega
    · have hKcard : Nat.card ↥K = 504 := by
        have hc := uc22p22r_L2_card hL2K3
        norm_num at hc ⊢
        exact hc
      rw [hKcard] at hKeq
      omega
  · exact absurd hcomp3.1.2.2 (s168e3_153_2_not_quasisimple hdir h2 hLcard hK0card hnab)
  · exact absurd hcomp4.2.2.1.2.2 (s168e3_153_2_not_quasisimple hdir h2 hLcard hK0card hnab)

end Generic

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214b
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22uc
import CFSG.LocalAnalysis.UniquenessCase.UC22P20d
import CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194SpBlocks
import CFSG.HardMathSupport.Timmesfeld.Tables.Census.U3Rank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

namespace P2214R

theorem dvd_of_cong {m p : ℕ} (h : (2 : ℤ) ^ m ≡ -1 [ZMOD (p : ℤ)]) : p ∣ 2 ^ m + 1 := by
  have h1 := Int.ModEq.dvd h.symm
  have h2 : (((2 ^ m + 1 : ℕ)) : ℤ) = (2 : ℤ) ^ m - -1 := by push_cast; ring
  exact Int.natCast_dvd_natCast.1 (h2 ▸ h1)

theorem dvd_sq_sub_one {p q : ℕ} (h : p ∣ q + 1) : p ∣ q ^ 2 - 1 := by
  have e : q ^ 2 - 1 = (q + 1) * (q - 1) := by rw [← Nat.sq_sub_sq, one_pow]
  rw [e]
  exact h.mul_right _

theorem two_le_pRank_sp4 {X : Type} [Group X] [Finite X] {n p : ℕ} (hX : IsSp4 X n)
    (hp : p.Prime) (hpd : p ∣ (2 ^ n) ^ 2 - 1) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  obtain ⟨-, F, _, _, hF, ⟨e⟩⟩ := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  haveI := Fintype.ofFinite F
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.le_pRank_statedProj_sp (n := 2) hp
    (by rw [hF]; exact hpd)

theorem two_le_pRank_u3 {X : Type} [Group X] [Finite X] {n p : ℕ} (hX : IsU3 X n) (hodd : Odd n)
    (hp : p.Prime) (hpd : p ∣ 2 ^ n + 1) : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X) := by
  have hm := CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  by_cases hp3 : p = 3
  · subst hp3
    exact CFSG.HardMathSupport.Timmesfeld.Tables.Census.two_le_pRank_three_psu_three_two_pow_odd
      hodd hm
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hm
  haveI : Fact p.Prime := ⟨hp⟩
  have hq0 : 2 ^ n ≠ 0 := by positivity
  have hKu : Nat.card Kˣ = (2 ^ n + 1) * (2 ^ n - 1) := by
    rw [Nat.card_units, hK, ← Nat.sq_sub_sq, one_pow]
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' (G := Kˣ) p (by rw [hKu]; exact hpd.mul_right _)
  have hζq : ζ ^ (2 ^ n + 1) = 1 := orderOf_dvd_iff_pow_eq_one.1 (by rw [hζ]; exact hpd)
  rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt e]
  exact CFSG.QuasithinUnique.Vol2Native.EvenWit.two_le_pRank_torus hp3 hζ (i₀ := (0 : Fin 3))
    (i₁ := 1) (i₂ := 2) (by decide) (by decide) (by decide)
    (CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU hq0
      (CFSG.SectionRank.ClassicalEven.prod_torusVec ζ _ _)
      (by rw [CFSG.SectionRank.ClassicalEven.torusVec_pow, hζq,
        CFSG.SectionRank.ClassicalEven.torusVec_one]))
    (CFSG.SectionRank.ClassicalEven.torusDiag_mem_SU hq0
      (CFSG.SectionRank.ClassicalEven.prod_torusVec ζ _ _)
      (by rw [CFSG.SectionRank.ClassicalEven.torusVec_pow, hζq,
        CFSG.SectionRank.ClassicalEven.torusVec_one]))

theorem three_dvd_card_u3 {X : Type} [Group X] [Finite X] {n : ℕ} (hX : IsU3 X n)
    (hodd : Odd n) : 3 ∣ Nat.card X := by
  have h2 := CFSG.HardMathSupport.Timmesfeld.Tables.Census.two_le_pRank_three_psu_three_two_pow_odd
    hodd (CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide))
  obtain ⟨E, -, -, hcard⟩ :=
    CFSG.PreuniquenessRankFour.Helpers.pRank_attained 3 Nat.prime_three (⊤ : Subgroup X)
  have h3 : 3 ∣ Nat.card E := by
    rw [hcard]
    exact dvd_pow_self 3 (by omega)
  exact h3.trans (Subgroup.card_subgroup_dvd_card E)

theorem two_le_pRank_of_sp4 (M V : Subgroup G) {K : Subgroup G} (hKM : K ≤ M) {n p : ℕ}
    (hsp : IsSp4 ↥(mbarImage M V K) n) (hp : p.Prime) (hp2 : p ≠ 2) (hpd : p ∣ (2 ^ n) ^ 2 - 1) :
    2 ≤ CFSG.Open.pRank p K := by
  obtain ⟨f, hf⟩ := uc22p22a_exists_surj M V K hKM
  exact uc22p2214_two_le_pRank_of_surj f hf hp hp2 (two_le_pRank_sp4 hsp hp hpd)

theorem two_le_pRank_of_su3 (M V : Subgroup G) {K : Subgroup G} (hKM : K ≤ M) {n p : ℕ}
    (hsu : IsSU3 ↥(mbarImage M V K) n) (hodd : Odd n) (hp : p.Prime) (hp2 : p ≠ 2)
    (hpd : p ∣ 2 ^ n + 1) : 2 ≤ CFSG.Open.pRank p K := by
  obtain ⟨f, hf⟩ := uc22p22a_exists_surj M V K hKM
  exact uc22p2214_two_le_pRank_of_surj ((QuotientGroup.mk' (center ↥(mbarImage M V K))).comp f)
    ((QuotientGroup.mk'_surjective _).comp hf) hp hp2 (two_le_pRank_u3 hsu.2 hodd hp hpd)

theorem two_le_pRank_of_conj {X K K' L : Subgroup G} (hK : K ∈ calC X) (hK' : K' ∈ calC X)
    (hne : K' ≠ K) (hconj : ∃ g : G, K' = uniqueFourConj g K) (hKL : K ≤ L) (hK'L : K' ≤ L)
    (hLX : L ≤ X) {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hrK : r ∣ (Subgroup.center (Bar2 K)).index) : 2 ≤ CFSG.Open.pRank r L := by
  obtain ⟨g, rfl⟩ := hconj
  have hcomm := uc22p22l_barImage_commute hK hK' hne.symm
  obtain ⟨eA, -⟩ := uc22p22l_barImage_equiv hK
  obtain ⟨eB, -⟩ := uc22p22l_barImage_equiv hK'
  obtain ⟨eC⟩ : Nonempty (Bar2 K ≃* Bar2 (uniqueFourConj g K)) := uc22p20d_bar2_conj g⁻¹ K
  haveI : Fact r.Prime := ⟨hr⟩
  have hrA : r ∣ (Subgroup.center ↥(barImage X K)).index := by
    rwa [← uc22p22u_index_center_eq eA]
  have hrB : r ∣ (Subgroup.center ↥(barImage X (uniqueFourConj g K))).index := by
    rwa [← uc22p22u_index_center_eq (eC.trans eB)]
  obtain ⟨SA⟩ := (inferInstance : Nonempty (Sylow r ↥(barImage X K)))
  obtain ⟨SB⟩ := (inferInstance : Nonempty (Sylow r ↥(barImage X (uniqueFourConj g K))))
  obtain ⟨hpg, hnc⟩ := uc22p22u_noncyclic_of_commuting hcomm SA SB
    (uc22p22u_sylow_not_le_center SA hrA) (uc22p22u_sylow_not_le_center SB hrB)
  exact uc22p22u_two_le_pRank_of_bar hLX hr hr2 hpg hnc
    (sup_le ((Subgroup.map_subtype_le _).trans (uc22p22u_barImage_mono hKL))
      ((Subgroup.map_subtype_le _).trans (uc22p22u_barImage_mono hK'L)))

theorem two_le_pRank_pair {M K : Subgroup G} (hK : K ∈ calC M) (hc2 : (conjSetOf M K).ncard = 2)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrK : r ∣ (Subgroup.center (Bar2 K)).index) :
    2 ≤ CFSG.Open.pRank r (conjClosure M K) := by
  obtain ⟨K', hK', hne⟩ : ∃ K' ∈ conjSetOf M K, K' ≠ K := by
    by_contra hall
    have hsub : conjSetOf M K ⊆ {K} := fun A hA => by
      by_contra hA'
      exact hall ⟨A, hA, hA'⟩
    have := Set.ncard_le_ncard hsub (Set.finite_singleton K)
    rw [hc2, Set.ncard_singleton] at this
    omega
  obtain ⟨g, hg, rfl⟩ := hK'
  have hMM : M ≤ normalizer (M : Set G) := Subgroup.le_normalizer
  have hconj : K.map (MulAut.conj g).toMonoidHom = uniqueFourConj g⁻¹ K := by
    simp [uniqueFourConj]
  have hK'C : K.map (MulAut.conj g).toMonoidHom ∈ calC M := by
    rw [hconj]
    exact uc22p22u_calC_conj hMM hK (M.inv_mem hg)
  have hle : ∀ A ∈ conjSetOf M K, A ≤ conjClosure M K := fun A hA =>
    le_iSup₂_of_le (f := fun A (_ : A ∈ conjSetOf M K) => A) A hA le_rfl
  exact two_le_pRank_of_conj hK hK'C hne ⟨g⁻¹, hconj⟩ (hle K ⟨1, M.one_mem, by ext x; simp⟩)
    (hle _ ⟨g, hg, rfl⟩) (uc22p22u_conjClosure_isProd le_rfl hMM hK).1 hr hr2 hrK

theorem dvd_index_center_bar2 (D : Data G) {Ch : Choice2011 G} (c : Ctx22b D Ch)
    {K : Subgroup G} (hKC : K ∈ calC D.M) (hq : CFSG.Open.IsQuasisimple ↥(mbarImage D.M c.V K))
    [IsSimpleGroup ↥(mbarImage D.M c.V K)] {p : ℕ}
    (hp : p ∣ Nat.card ↥(mbarImage D.M c.V K)) : p ∣ (Subgroup.center (Bar2 K)).index := by
  obtain ⟨⟨e⟩, -⟩ := uc22p22a_data D c hKC hq
  rw [Subgroup.index_eq_card, Nat.card_congr e.toEquiv,
    uc22p21k_card_quot_center (uc22p21k_center_eq_bot hq)]
  exact hp

end P2214R

end CFSG.LocalAnalysis.UniquenessCase.UC22

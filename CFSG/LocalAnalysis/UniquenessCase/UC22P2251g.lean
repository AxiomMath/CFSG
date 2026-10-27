module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251d
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251f
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251a
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
import CFSG.RankThree.PartOne.S11c.Simple168

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)

variable {G : Type} [Group G] [Finite G]

namespace P2251g

theorem not_sq_dvd_card (D : Data G) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb)
    {i : Fin m} (hS3 : ∀ k, k ≠ i → IsL2Ev ↥(Nb k) 1) (hbad : ¬ ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2) {p : ℕ}
    (hp : p.Prime) (hp5 : 5 ≤ p) : ¬ p ^ 2 ∣ Nat.card ↥(mbarImage D.M D.U (proofN D)) := by
  classical
  have hcard : Nat.card ↥(mbarImage D.M D.U (proofN D)) = ∏ k, Nat.card ↥(Nb k) := by
    rw [← P22y.piMul_range hNb.1,
      ← Nat.card_congr (MonoidHom.ofInjective (P22y.piMul_injective hNb.1)).toEquiv, Nat.card_pi]
  have h6 : Nat.Coprime (p ^ 2) 6 := by
    refine Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 fun h => ?_)
    rcases (Nat.Prime.dvd_mul hp).1 (show p ∣ 2 * 3 from h) with h' | h' <;>
      have := Nat.le_of_dvd (by norm_num) h' <;> omega
  have hcop : Nat.Coprime (p ^ 2) (∏ k ∈ Finset.univ.erase i, Nat.card ↥(Nb k)) :=
    Nat.Coprime.prod_right fun k hk => by
      rwa [P22y.card_of_isL2Ev_one (hS3 k (Finset.ne_of_mem_erase hk))]
  rw [hcard, ← Finset.mul_prod_erase _ _ (Finset.mem_univ i)]
  intro h
  have h2 := hcop.dvd_of_dvd_mul_right h
  have hle : p ^ 2 ≤ 168 := by
    rcases P2251b.card_of_bad (hNb.2 i) hbad with h' | h' | h' <;> rw [h'] at h2 <;>
      exact (Nat.le_of_dvd (by norm_num) h2).trans (by norm_num)
  have hp12 : p ≤ 12 := by nlinarith
  interval_cases p <;> rcases P2251b.card_of_bad (hNb.2 i) hbad with h' | h' | h' <;> rw [h'] at h2 <;>
    norm_num at h2

theorem exists_noncyclic (D : Data G) {p : ℕ} (hp : p.Prime)
    (hN : ¬ p ^ 2 ∣ Nat.card ↥(mbarImage D.M D.U (proofN D))) (hr : 2 < CFSG.pRank p (MBar D.M D.U)) :
    ∃ P : Subgroup G, P ≤ D.M ∧ IsPGroup p P ∧ P ≤ normalizer (jOf D.T : Set G) ∧
      ¬ IsCyclic ↥(mbarImage D.M D.U P) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNM : proofN D ≤ D.M := uc22p22e_jOf_le_self D.M
  have hMN := uc22p22t_M_le_normalizer_jOf D
  set Hn : Subgroup G := D.M ⊓ normalizer ((D.T ⊓ proofN D : Subgroup G) : Set G) with hHn
  have hHnM : Hn ≤ D.M := inf_le_left
  have hMeq : Hn ⊔ proofN D = D.M := by
    refine le_antisymm (sup_le hHnM hNM) ?_
    have h := uc22p22t_frattini_sup hNM hMN (D.sylowM.inf_of_le_normalizer hNM hMN)
    rw [sup_comm] at h
    exact h
  have hHnJ : Hn ≤ normalizer (jOf D.T : Set G) := fun y hy =>
    CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem (uc22p22e_conj_jOf fun x hx =>
      (mem_inf.1 ((mem_normalizer_iff.1 (mem_inf.1 hy).2 x).1
        (mem_inf.2 ⟨uc22p22e_jOf_le_self D.T hx, uc22p22e_jOf_le D.sylowM hx⟩))).1)
  set Nb := mbarImage D.M D.U (proofN D) with hNb
  haveI : Nb.Normal :=
    ((normal_subgroupOf_iff_le_normalizer hNM).2 hMN).map _ (QuotientGroup.mk'_surjective _)
  have hsup : mbarImage D.M D.U Hn ⊔ Nb = ⊤ := by
    rw [hNb, mbarImage, mbarImage, ← Subgroup.map_sup, ← subgroupOf_sup hHnM hNM, hMeq, subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  let φ : ↥Hn →* MBar D.M D.U ⧸ Nb :=
    (QuotientGroup.mk' Nb).comp ((QuotientGroup.mk' (kerAct D.M D.U).normalCore).comp (inclusion hHnM))
  have hφapp : ∀ y : ↥Hn,
      φ y = QuotientGroup.mk' Nb (QuotientGroup.mk' (kerAct D.M D.U).normalCore (inclusion hHnM y)) :=
    fun _ => rfl
  have hφ : Function.Surjective φ := by
    intro z
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective Nb z
    have hx : x ∈ mbarImage D.M D.U Hn ⊔ Nb := by
      rw [hsup]
      exact mem_top x
    obtain ⟨_, ⟨y, hy, rfl⟩, n, hn, rfl⟩ := mem_sup_of_normal_right.1 hx
    exact ⟨⟨(y : G), hy⟩, by rw [hφapp]; exact (QuotientGroup.mk'_eq_mk' _).2 ⟨n, hn, rfl⟩⟩
  obtain ⟨A, -, hA, hAc⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (MBar D.M D.U))
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at hAc
  have hA'c : ¬ IsCyclic ↥(A.map (QuotientGroup.mk' Nb)) := by
    intro hc
    have hψ : ((QuotientGroup.mk' Nb).comp A.subtype).range = A.map (QuotientGroup.mk' Nb) := by
      rw [MonoidHom.range_comp, range_subtype]
    have hk : Nat.card ((QuotientGroup.mk' Nb).comp A.subtype).ker ≤ p := by
      obtain ⟨a, ha⟩ :=
        IsPGroup.iff_card.1 (hA.isPGroup.to_subgroup ((QuotientGroup.mk' Nb).comp A.subtype).ker)
      have hdvd : Nat.card ((QuotientGroup.mk' Nb).comp A.subtype).ker ∣ Nat.card Nb := by
        rw [← card_map_of_injective A.subtype_injective]
        refine card_dvd_of_le ?_
        rintro _ ⟨x, hx, rfl⟩
        exact (QuotientGroup.eq_one_iff _).1 (MonoidHom.mem_ker.1 hx)
      rw [ha] at hdvd ⊢
      have ha1 : a ≤ 1 := by
        by_contra h
        exact hN ((pow_dvd_pow p (show 2 ≤ a by omega)).trans hdvd)
      exact (Nat.pow_le_pow_right hp.pos ha1).trans_eq (pow_one p)
    have hA'p : Nat.card ↥(A.map (QuotientGroup.mk' Nb)) ≤ p := by
      haveI := hc
      refine Nat.le_of_dvd hp.pos ?_
      rw [← IsCyclic.exponent_eq_card]
      refine Monoid.exponent_dvd_of_forall_pow_eq_one fun x => ?_
      obtain ⟨_, ⟨a, ha, rfl⟩⟩ := x
      exact Subtype.ext (by rw [Subgroup.coe_pow, ← map_pow, hA.2 a ha, map_one, Subgroup.coe_one])
    have h1 := Subgroup.card_ker_mul_card_range ((QuotientGroup.mk' Nb).comp A.subtype)
    rw [hψ, hAc] at h1
    have h3 : p ^ CFSG.pRank p (MBar D.M D.U) ≤ p ^ 2 := by
      rw [← h1, sq]
      exact Nat.mul_le_mul hk hA'p
    exact absurd h3 (not_le.2 (Nat.pow_lt_pow_right hp.one_lt hr))
  obtain ⟨Q, hQ⟩ := (hA.isPGroup.map (QuotientGroup.mk' Nb)).exists_le_sylow
  obtain ⟨S, hS⟩ := Sylow.mapSurjective_surjective hφ p Q
  have hQle : (Q : Subgroup (MBar D.M D.U ⧸ Nb)) ≤
      (mbarImage D.M D.U ((S : Subgroup Hn).map Hn.subtype)).map (QuotientGroup.mk' Nb) := by
    rw [← hS, Sylow.coe_mapSurjective]
    rintro _ ⟨s, hs, rfl⟩
    rw [hφapp]
    exact mem_map_of_mem _ (mem_map_of_mem _ (mem_map_of_mem Hn.subtype hs))
  refine ⟨(S : Subgroup Hn).map Hn.subtype, (map_subtype_le _).trans hHnM, S.isPGroup'.map _,
    (map_subtype_le _).trans hHnJ, fun hc => hA'c ?_⟩
  haveI := hc
  haveI : IsCyclic ↥((mbarImage D.M D.U ((S : Subgroup Hn).map Hn.subtype)).map (QuotientGroup.mk' Nb)) :=
    isCyclic_of_surjective _ ((QuotientGroup.mk' Nb).subgroupMap_surjective _)
  exact Subgroup.isCyclic_of_le (hQ.trans hQle)

theorem calCGS_le (D : Data G) (h61 : UC6.R6_1 D) {p : ℕ} (hp : p ∈ D.sig) {P : Subgroup G}
    (hPM : P ≤ D.M) (hPp : IsPGroup p P) (hPJ : P ≤ normalizer (jOf D.T : Set G))
    (hPK : P ⊓ centralizer (proofE D : Set G) ≤ centralizer (D.U : Set G))
    (hnc : ¬ IsCyclic ↥(mbarImage D.M D.U P)) : UC6.calCGS (proofS D) ≤ D.M := by
  haveI : Fact p.Prime := ⟨(D.sig_prime p hp).1⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hJE : normalizer (jOf D.T : Set G) ≤ normalizer (proofE D : Set G) := fun y hy =>
    CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem (uc22p22e_conj_omegaZJ
      (fun x hx => (mem_normalizer_iff.1 hy x).1 hx)
      (fun x hx => by simpa using (mem_normalizer_iff.1 (inv_mem hy) x).1 hx))
  have hKH : D.M ⊓ centralizer (proofE D : Set G) ≤ D.M ⊓ normalizer (proofE D : Set G) :=
    inf_le_inf_left _ (centralizer_le_normalizer _)
  have hHK : D.M ⊓ normalizer (proofE D : Set G) ≤
      normalizer ((D.M ⊓ centralizer (proofE D : Set G) : Subgroup G) : Set G) :=
    (inf_le_inf le_normalizer ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).1
      (normal_subgroupOf_centralizer_normalizer _))).trans inf_normalizer_le_normalizer_inf
  have hTH : D.T ≤ D.M ⊓ normalizer (proofE D : Set G) := fun y hy => mem_inf.2 ⟨D.sylowM.le hy,
    hJE (CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem (uc22p22e_normalizes_jOf_T D y hy))⟩
  have hSK : CFSG.ABGLocalTools.IsSylowOf 2 (proofS D) (D.M ⊓ centralizer (proofE D : Set G)) := by
    have h := (D.sylowM.of_le hTH inf_le_left).inf_of_le_normalizer hKH hHK
    rw [← inf_assoc, inf_of_le_left D.sylowM.le] at h
    exact h
  obtain ⟨X, hXH, hXp, hXnc, hXN⟩ := uc22p22t_frattini_bar D hKH hHK inf_le_left hSK hPp
    (le_inf hPM (hPJ.trans hJE)) ((inf_le_inf_left _ inf_le_right).trans hPK) hnc
  exact uc22p22e_calCGS_le D h61 hp (hXH.trans inf_le_left) hXp hXnc hXN inf_le_left

end P2251g

theorem s22_5_1K2_of (D : Data G) (Ch : Choice2011 G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (h119 : R119W D) (h17 : S21_17 D Ch) (h31 : S22_3_1 D Ch) (h33 : S22_3_3 D Ch)
    (he : 3 < CFSG.Open.evenRank G) (hSg : UC6S846.SigmaStd D) (hk : D.k = 2) (h76 : F07.R76Sig D)
    (h614 : UC6.R6_14 D) : S22_5_1 D Ch := by
  intro hH c m Nb hNb i
  by_contra hbad
  have h76' : ∀ L ∈ calC D.M, ∀ p ∈ D.sig, Conclusion76 D.M p := fun L hL p hp =>
    h76 p hp (D.sig_prime p hp).2 (UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp)
  have hS3 := uc22p2251d_isL2Ev_one D Ch hx h61 h119 h17 hH c.toCtx22 he hSg hk h76' h614 hNb hbad
  have hbad' : IsL2Ev ↥(Nb i) 2 ∨ IsL3 ↥(Nb i) 1 ∨ IsS5 ↥(Nb i) := by
    rcases hNb.2 i with ⟨n, hn⟩ | h | h
    · obtain rfl : n = 2 := by
        by_contra hne
        exact hbad ⟨n, hn, hne⟩
      exact Or.inl hn
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  obtain ⟨K, hK, -⟩ := uc22p2251b_exists_bad D hx h61 h119 h17 hH c.toCtx22 hNb hbad
  have hns := UC6S846.not_solvable_of_mem_calC hK
  have h3 := (Data.k_eq_two_iff D).1 hk
  have h3σ : 3 ∉ D.sig := fun h => h3 (UC6S846.sp_of_mem_sig hSg hns h)
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hp5 : 5 ≤ p := by
    have h2 := hpp.two_le
    have hp3 : p ≠ 3 := fun h => h3σ (h ▸ hp)
    have hp4 : p ≠ 4 := by
      rintro rfl
      norm_num at hpp
    omega
  obtain ⟨P, hPM, hPp, hPJ, hnc⟩ := P2251g.exists_noncyclic D hpp
    (P2251g.not_sq_dvd_card D hNb hS3 hbad hpp hp5) (uc22p2251a_two_lt_pRank_mbarU D hx h61 he c.toCtx22 p hp)
  exact (h31 hH c).2 (P2251g.calCGS_le D h61 hp hPM hPp hPJ
    (uc22p2251f_le_centralizer D Ch h33 hH c hNb hS3 hbad' hpp hp5 hPM hPJ hPp) hnc)

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

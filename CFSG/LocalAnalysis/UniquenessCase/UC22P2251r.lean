module

import CFSG.LocalAnalysis.UniquenessCase.UC22P2251f
import CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin
import CFSG.RankThree.PartOne.S11c.Simple168
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge4
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2251g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (jOf)

variable {G : Type} [Group G] [Finite G]

@[expose] def S22_5_1RStarSn (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ _ : Ctx22c D Ch, ∀ (m : ℕ) (Nb : Fin m → Subgroup (MBar D.M D.U)),
    NbarSplit D Nb → ∀ i, D.k ≠ 1 → CFSG.Open.evenRank G = 3 →
      (¬ ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2) → (∀ j, j ≠ i → IsL2Ev ↥(Nb j) 1) →
      (∀ p ∈ D.sig, p ∣ Nat.card ↥(Nb i)) →
      (∀ p ∈ D.sig, CFSG.pRank p (MBar D.M D.U) = 2) →
      (∀ p ∈ D.sig, ∀ P : Subgroup G, P ≤ D.M → IsPGroup p ↥P →
        P ≤ normalizer (jOf D.T : Set G) → IsCyclic ↥(mbarImage D.M D.U P)) →
      ∀ p ∈ D.sig, ∀ C : Subgroup G, C ≠ ⊥ → C ≤ proofS D →
        (C.subgroupOf (proofS D)).Characteristic → ¬ normalizer (C : Set G) ≤ D.M →
        CFSG.Open.IsSubnormal (mbarImage D.M D.U (Opp p (normalizer (C : Set G) ⊓ D.M))) ⊤

namespace P2251r

theorem not_dvd_card_mbarImage {M V K P : Subgroup G} {p : ℕ} [Fact p.Prime]
    (hV : M ≤ normalizer (V : Set G)) (hKM : K ≤ M) (hP : CFSG.ABGLocalTools.IsSylowOf p P K)
    (hPV : P ≤ centralizer (V : Set G)) : ¬ p ∣ Nat.card (mbarImage M V K) := by
  obtain ⟨-, -, hidx⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  rw [uc22br4_card_mbarImage M V K hV hKM]
  exact fun h => hidx (h.trans (Subgroup.index_dvd_of_le fun x hx => hPV hx))

theorem exists_pSubgroup (D : Data G) (Ch : Choice2011 G) (h33 : S22_3_3 D Ch) (hH : H1930 D)
    (c : Ctx22c D Ch) {m : ℕ} {Nb : Fin m → Subgroup (MBar D.M D.U)} (hNb : NbarSplit D Nb)
    {i : Fin m} (hbad : ¬ ∃ n : ℕ, IsL2Ev ↥(Nb i) n ∧ n ≠ 2)
    (hS3 : ∀ j, j ≠ i → IsL2Ev ↥(Nb j) 1) {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p)
    (hrk : 1 < CFSG.pRank p (MBar D.M D.U)) :
    ∃ Q : Subgroup G, Q ≤ D.M ∧ Q ≤ normalizer (proofS D : Set G) ∧ IsPGroup p ↥Q ∧
      ¬ Q ≤ centralizer (D.U : Set G) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hbad' : IsL2Ev ↥(Nb i) 2 ∨ IsL3 ↥(Nb i) 1 ∨ IsS5 ↥(Nb i) := by
    rcases hNb.2 i with ⟨n, hn⟩ | h | h
    · obtain rfl : n = 2 := by
        by_contra hne
        exact hbad ⟨n, hn, hne⟩
      exact Or.inl hn
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  have hV : D.M ≤ normalizer (D.U : Set G) := (uc22p22e_inCalV_U D).2.2.1
  have hNM : proofN D ≤ D.M := uc22p22e_jOf_le_self D.M
  have hMN := uc22p22t_M_le_normalizer_jOf D
  set X : Subgroup G := D.M ⊓ normalizer (jOf D.T : Set G) with hX
  have hXM : X ≤ D.M := inf_le_left
  have hXJ : X ≤ normalizer (jOf D.T : Set G) := inf_le_right
  have hXN : X ⊔ proofN D = D.M := by
    refine le_antisymm (sup_le hXM hNM) ?_
    refine (uc22p22t_frattini_sup hNM hMN (D.sylowM.inf_of_le_normalizer hNM hMN)).trans
      (sup_le le_sup_right (le_sup_of_le_left (le_inf inf_le_left fun y hy => ?_)))
    exact CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem (uc22p22e_conj_jOf fun x hx =>
      (mem_inf.1 ((mem_normalizer_iff.1 (mem_inf.1 hy).2 x).1
        (mem_inf.2 ⟨uc22p22e_jOf_le_self D.T hx, uc22p22e_jOf_le D.sylowM hx⟩))).1)
  have hJE : normalizer (jOf D.T : Set G) ≤ normalizer (proofE D : Set G) := fun y hy =>
    CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem (uc22p22e_conj_omegaZJ
      (fun x hx => (mem_normalizer_iff.1 hy x).1 hx)
      (fun x hx => by simpa using (mem_normalizer_iff.1 (inv_mem hy) x).1 hx))
  have hKX : X ⊓ centralizer (proofE D : Set G) ≤ X := inf_le_left
  have hWX : X ⊓ normalizer (proofS D : Set G) ≤ X := inf_le_left
  have hXK : X ≤ normalizer ((X ⊓ centralizer (proofE D : Set G) : Subgroup G) : Set G) :=
    (le_inf le_normalizer (hXJ.trans (hJE.trans
      ((normal_subgroupOf_iff_le_normalizer (centralizer_le_normalizer _)).1
        (normal_subgroupOf_centralizer_normalizer _))))).trans inf_normalizer_le_normalizer_inf
  have hTX : D.T ≤ X := fun y hy => mem_inf.2 ⟨D.sylowM.le hy,
    CFSG.RankThree.PartOne.mem_normalizer_of_forall_conj_mem (uc22p22e_normalizes_jOf_T D y hy)⟩
  have hSK : CFSG.ABGLocalTools.IsSylowOf 2 (proofS D) (X ⊓ centralizer (proofE D : Set G)) := by
    have h := (D.sylowM.of_le hTX hXM).inf_of_le_normalizer hKX hXK
    rw [← inf_assoc, inf_of_le_left hTX] at h
    exact h
  have hXeq : (X ⊓ normalizer (proofS D : Set G)) ⊔ (X ⊓ centralizer (proofE D : Set G)) = X :=
    le_antisymm (sup_le hWX hKX)
      ((uc22p22t_frattini_sup hKX hXK hSK).trans (sup_comm _ _).le)
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (X ⊓ centralizer (proofE D : Set G))
  have hPU : P ≤ centralizer (D.U : Set G) := fun x hx => by
    have hxK := hP.le hx
    exact uc22p2251f_mem_centralizer D Ch h33 hH c hNb hS3 hbad' hp hp5
      (hXM (mem_inf.1 hxK).1) (hP.isPGroup.to_le (zpowers_le.2 hx)) (hXJ (mem_inf.1 hxK).1)
      (mem_inf.1 hxK).2
  have hpK : ¬ p ∣ Nat.card (mbarImage D.M D.U (X ⊓ centralizer (proofE D : Set G))) :=
    not_dvd_card_mbarImage hV (hKX.trans hXM) hP hPU
  obtain ⟨A, -, -, hAc⟩ :=
    CFSG.SectionRank.exists_pRank hp.one_lt (⊤ : Subgroup (MBar D.M D.U))
  rw [← CFSG.SectionRank.pRank_eq_open_pRank_top] at hAc
  have hpM : p ^ 2 ∣ Nat.card (MBar D.M D.U) := by
    refine (pow_dvd_pow p (show 2 ≤ CFSG.pRank p (MBar D.M D.U) by omega)).trans ?_
    rw [← hAc]
    exact Subgroup.card_subgroup_dvd_card A
  have hNn : (mbarImage D.M D.U (proofN D)).Normal :=
    ((normal_subgroupOf_iff_le_normalizer hNM).2 hMN).map _ (QuotientGroup.mk'_surjective _)
  have htop : mbarImage D.M D.U X ⊔ mbarImage D.M D.U (proofN D) = ⊤ := by
    rw [mbarImage, mbarImage, ← Subgroup.map_sup, ← subgroupOf_sup hXM hNM, hXN, subgroupOf_self]
    exact map_top_of_surjective _ (QuotientGroup.mk'_surjective _)
  have hpX : p ∣ Nat.card (mbarImage D.M D.U X) := by
    have h1 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf
      (H := mbarImage D.M D.U X) (K := mbarImage D.M D.U (proofN D))
      (le_top.trans (normalizer_eq_top_iff.mpr hNn).ge)
    rw [htop, card_top] at h1
    by_contra hnd
    exact P2251g.not_sq_dvd_card D hNb hS3 hbad hp hp5
      ((Nat.Coprime.pow_left 2 ((Nat.Prime.coprime_iff_not_dvd hp).2 hnd)).dvd_of_dvd_mul_left
        (hpM.trans (Dvd.intro _ h1)))
  have hWK : mbarImage D.M D.U (X ⊓ normalizer (proofS D : Set G)) ≤ normalizer
      (mbarImage D.M D.U (X ⊓ centralizer (proofE D : Set G)) : Set (MBar D.M D.U)) := by
    rintro _ ⟨x, hx, rfl⟩
    exact P2251f.mem_normalizer_mbarImage x.2 (hXK (hWX (mem_subgroupOf.1 hx)))
  have h2 := CFSG.GroupTheory.CoprimeActionSupport.NormalSubgroupSylowJoin.card_sup_mul_card_inf hWK
  have hXb : mbarImage D.M D.U (X ⊓ normalizer (proofS D : Set G)) ⊔
      mbarImage D.M D.U (X ⊓ centralizer (proofE D : Set G)) = mbarImage D.M D.U X := by
    rw [mbarImage, mbarImage, mbarImage, ← Subgroup.map_sup,
      ← subgroupOf_sup (hWX.trans hXM) (hKX.trans hXM), hXeq]
  rw [hXb] at h2
  have hpW : p ∣ Nat.card (mbarImage D.M D.U (X ⊓ normalizer (proofS D : Set G))) :=
    ((Nat.Prime.dvd_mul hp).1 (hpX.trans (Dvd.intro _ h2))).resolve_right hpK
  obtain ⟨Q, hQ⟩ := CFSG.ABGLocalTools.exists_isSylowOf p (X ⊓ normalizer (proofS D : Set G))
  exact ⟨Q, hQ.le.trans (hWX.trans hXM), hQ.le.trans inf_le_right, hQ.isPGroup,
    fun hQU => not_dvd_card_mbarImage hV (hWX.trans hXM) hQ hQU hpW⟩

end P2251r

end CFSG.LocalAnalysis.UniquenessCase.UC22

end

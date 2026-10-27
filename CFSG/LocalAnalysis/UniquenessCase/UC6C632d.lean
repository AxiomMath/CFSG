module

public import CFSG.LocalAnalysis.UniquenessCase.UC6C632Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC6C632a
public import CFSG.LocalAnalysis.UniquenessCase.UC6C632b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem relIndex_dvd_card_of_sup_eq {G : Type*} [Group G] [Finite G] {K U C : Subgroup G}
    (hUK : U ≤ K) (hCK : C ≤ K) (hn : K ≤ normalizer (U : Set G)) (hsup : K = U ⊔ C) :
    C.relIndex K ∣ Nat.card U := by
  classical
  set U' : Subgroup ↥K := U.subgroupOf K with hU'
  set C' : Subgroup ↥K := C.subgroupOf K with hC'
  haveI hU'n : U'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hUK).2 hn
  have hsup' : U' ⊔ C' = ⊤ := by
    apply Subgroup.map_injective K.subtype_injective
    rw [Subgroup.map_sup, hU', hC', Subgroup.map_subgroupOf_eq_of_le hUK,
      Subgroup.map_subgroupOf_eq_of_le hCK, ← MonoidHom.range_eq_map, Subgroup.range_subtype]
    exact hsup.symm
  have h1 : U'.index = U'.relIndex C' := by
    rw [← Subgroup.relIndex_top_right, ← hsup', Subgroup.relIndex_sup_left]
  have h2 : Nat.card U' * U'.index = Nat.card ↥K := Subgroup.card_mul_index U'
  have h3 : Nat.card C' * C'.index = Nat.card ↥K := Subgroup.card_mul_index C'
  have h4 : U'.relIndex C' * Nat.card (U' ⊓ C' : Subgroup ↥K) = Nat.card C' :=
    Subgroup.relIndex_mul_card (H := U') (K := C')
  have h5 : U'.relIndex C' ≠ 0 := h1 ▸ Subgroup.index_ne_zero_of_finite
  have h6 : Nat.card ↥(U' ⊓ C' : Subgroup ↥K) * C'.index = Nat.card U' := by
    apply Nat.eq_of_mul_eq_mul_left (Nat.pos_of_ne_zero h5)
    calc U'.relIndex C' * (Nat.card ↥(U' ⊓ C' : Subgroup ↥K) * C'.index)
        = (U'.relIndex C' * Nat.card ↥(U' ⊓ C' : Subgroup ↥K)) * C'.index := by ring
      _ = Nat.card C' * C'.index := by rw [h4]
      _ = Nat.card U' * U'.index := h3.trans h2.symm
      _ = U'.relIndex C' * Nat.card U' := by rw [h1]; ring
  have h7 : C'.index ∣ Nat.card U' := ⟨Nat.card ↥(U' ⊓ C' : Subgroup ↥K), by rw [← h6]; ring⟩
  have h8 : Nat.card U' = Nat.card U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUK).toEquiv
  rw [h8] at h7
  exact h7

namespace Mz614

variable {G : Type} [Group G] [Finite G] (m : Mz614 G)

theorem isStronglyPEmbedded_M {p : ℕ} (hp : p ∈ uniqueFourSigma m.M) : IsStronglyPEmbedded p m.M :=
  isStronglyPEmbedded_of_sigmaOne m.hU m.S.maxLocal hp (m.hσ1 hp)

theorem exists_sylow_centralized {p : ℕ} (hp : p ∈ uniqueFourSigma m.M)
    (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) (h626 : m.C626) (h628b : m.C628b) (h631 : m.C631) :
    ∃ P₁ : Subgroup G, IsSylowOf p P₁ m.M ∧ m.A ⊓ m.L ≤ centralizer (P₁ : Set G) := by
  classical
  haveI : Fact m.r.Prime := ⟨m.hr⟩
  have hpr : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hpr⟩
  set Y : Subgroup G := m.A ⊓ m.L with hY
  have hYR : Y ≤ m.R := inf_le_left.trans (sup_le m.hZ.le m.E_le_R)
  have hYr : IsPGroup m.r Y := m.d.sylow.isPGroup.to_le hYR
  have hYK : Y ≤ normalizer (m.K : Set G) := fun y hy => m.mem_normalizer_K (m.R_le_M (hYR hy))
  have hcop : ¬ m.r ∣ Nat.card m.U := (Nat.Prime.coprime_iff_not_dvd m.hr).1 m.coprime_card_U
  have hKeq : m.K = m.U ⊔ (m.K ⊓ centralizer (Y : Set G)) :=
    eq_sup_centralizer_of_coprime m.U_le_K m.K_le_normalizer_U hYr hYK h631 hcop
  set C : Subgroup G := m.K ⊓ centralizer (Y : Set G) with hC
  have hCK : C ≤ m.K := inf_le_left
  have hbot : IsPGroup p (⊥ : Subgroup G) := IsPGroup.of_card (n := 0) (by simp)
  obtain ⟨P₁, hP₁C, -⟩ := exists_isSylowOf_ge (K := C) bot_le hbot
  have hP₁C' := (isSylowOf_iff.1 hP₁C)
  have hpU : ¬ p ∣ Nat.card m.U := by rw [m.card_U]; exact h628b p hp
  have hCdvd : C.relIndex m.K ∣ Nat.card m.U :=
    relIndex_dvd_card_of_sup_eq m.U_le_K hCK m.K_le_normalizer_U hKeq
  have hpCK : ¬ p ∣ C.relIndex m.K := fun h => hpU (h.trans hCdvd)
  have hpKM : ¬ p ∣ m.K.relIndex m.M := m.not_dvd_index_K hp hcyc h626
  refine ⟨P₁, ?_, ?_⟩
  · rw [isSylowOf_iff]
    refine ⟨hP₁C'.1.trans (hCK.trans m.K_le_M), hP₁C'.2.1, ?_⟩
    have hrel : P₁.relIndex m.M = P₁.relIndex C * C.relIndex m.K * m.K.relIndex m.M := by
      rw [Subgroup.relIndex_mul_relIndex P₁ C m.K hP₁C'.1 hCK,
        Subgroup.relIndex_mul_relIndex P₁ m.K m.M (hP₁C'.1.trans hCK) m.K_le_M]
    rw [hrel]
    intro hdvd
    rcases (Nat.Prime.dvd_mul hpr).1 hdvd with h | h
    · rcases (Nat.Prime.dvd_mul hpr).1 h with h' | h'
      · exact hP₁C'.2.2 h'
      · exact hpCK h'
    · exact hpKM h
  · intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hxC : x ∈ C := hP₁C'.1 hx
    exact ((Subgroup.mem_centralizer_iff.1 hxC.2) y hy).symm


theorem four_le_pRank_sylow_M {p : ℕ} (hp : p ∈ uniqueFourSigma m.M) {P₁ : Subgroup G}
    (hP₁ : IsSylowOf p P₁ m.M) : 4 ≤ CFSG.Open.pRank p P₁ := by
  classical
  have hpr : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hpr⟩
  obtain ⟨E, hEM, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hpr m.M
  obtain ⟨k, hkM, hk⟩ := exists_conj_le_of_isSylowOf hP₁ hEM hEel.isPGroup
  have hE'le : E.map (MulAut.conj k⁻¹).toMonoidHom ≤ P₁ := by
    rintro _ ⟨x, hx, rfl⟩
    simpa [MulAut.conj_apply] using hk x hx
  have hE'el : IsElemAbelian p (E.map (MulAut.conj k⁻¹).toMonoidHom) :=
    IsElemAbelian.map hEel _
  have hE'card : Nat.card (E.map (MulAut.conj k⁻¹).toMonoidHom) = p ^ CFSG.Open.pRank p m.M := by
    rw [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective, hEcard]
  exact (four_le_pRank_of_sigma hp).trans (le_pRank_of_elemAbelian hpr hE'le hE'el hE'card)

theorem two_lt_pRank_normalizer {p : ℕ} (hp : p ∈ uniqueFourSigma m.M)
    (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) (h626 : m.C626) (h628b : m.C628b) (h631 : m.C631)
    {B : Subgroup G} (hB : B ≤ m.A ⊓ m.L) :
    2 < CFSG.Open.pRank p (⊤ : Subgroup ↥(normalizer (B : Set G))) := by
  classical
  have hpr : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hpr⟩
  obtain ⟨P₁, hP₁, hcent⟩ := m.exists_sylow_centralized hp hcyc h626 h628b h631
  have hP₁N : P₁ ≤ normalizer (B : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact ((Subgroup.mem_centralizer_iff.1 (hcent (hB hb))) x hx).symm
  have h1 : CFSG.Open.pRank p (P₁.subgroupOf (normalizer (B : Set G))) = CFSG.Open.pRank p P₁ := by
    have := pRank_map_subtype_uc6 hpr (normalizer (B : Set G)) (P₁.subgroupOf (normalizer (B : Set G)))
    rw [Subgroup.map_subgroupOf_eq_of_le hP₁N] at this
    exact this.symm
  have h2 : CFSG.Open.pRank p (P₁.subgroupOf (normalizer (B : Set G))) ≤
      CFSG.Open.pRank p (⊤ : Subgroup ↥(normalizer (B : Set G))) :=
    CFSG.SectionRank.pRank_mono hpr.one_lt le_top
  have h4 := m.four_le_pRank_sylow_M hp hP₁
  omega


theorem dvd_card_inf_normalizer {p : ℕ} (hp : p ∈ uniqueFourSigma m.M)
    (hcyc : ∀ S : Sylow m.r ↥m.K, IsCyclic ↥S) (h626 : m.C626) (h628b : m.C628b) (h631 : m.C631)
    {B : Subgroup G} (hB : B ≤ m.A ⊓ m.L) : p ∣ Nat.card ↥(m.M ⊓ normalizer (B : Set G)) := by
  classical
  have hpr : p.Prime := hp.1.1
  haveI : Fact p.Prime := ⟨hpr⟩
  obtain ⟨P₁, hP₁, hcent⟩ := m.exists_sylow_centralized hp hcyc h626 h628b h631
  have hP₁N : P₁ ≤ normalizer (B : Set G) := by
    intro x hx
    refine Subgroup.centralizer_le_normalizer _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    exact ((Subgroup.mem_centralizer_iff.1 (hcent (hB hb))) x hx).symm
  have hP₁M : P₁ ≤ m.M := (isSylowOf_iff.1 hP₁).1
  obtain ⟨E, hEP, hEel, hEcard⟩ := CFSG.PreuniquenessRankFour.Helpers.pRank_attained p hpr P₁
  have h4 := m.four_le_pRank_sylow_M hp hP₁
  have hdvdE : p ∣ Nat.card E := by
    rw [hEcard]
    exact dvd_pow_self p (by omega)
  exact hdvdE.trans (Subgroup.card_dvd_of_le (hEP.trans (le_inf hP₁M hP₁N)))

end Mz614

end CFSG.LocalAnalysis.UniquenessCase.UC6

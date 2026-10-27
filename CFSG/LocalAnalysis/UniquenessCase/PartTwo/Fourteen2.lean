module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1b

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08 (R8107)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def Thm1421 (D : Data G) : Prop :=
  ∀ L₁ L₂ X : Subgroup G, Hyp141 D L₁ L₂ X → X ⊓ L₁ ∈ uniqueSet D.M ∧ X ⊓ L₂ ∈ uniqueSet D.M

theorem thm1421 {D : Data G} (h8107 : R8107 D) : Thm1421 D := by
  intro L₁ L₂ X h
  exact h8107 L₁ h.mem₁ L₂ h.mem₂ h.ne (pRank_three_of_isL3 h.shape₁)
    (pRank_three_of_isL3 h.shape₂) (Or.inl (thin8_of_isL3 h.shape₁))
    (Or.inl (thin8_of_isL3 h.shape₂)) (X ⊓ L₁) (X ⊓ L₂) inf_le_right
    (Hyp141.card_inf_left h) inf_le_right (Hyp141.card_inf_right h)

theorem card_eq_card_pCoreOf_mul_card_bar2 (H : Subgroup G) :
    Nat.card H = Nat.card (pCoreOf 2 H) * Nat.card (Bar2 H) := by
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥H)
  have h2 : Nat.card (pCoreOf 2 H) = Nat.card (CFSG.pCore 2 ↥H) := by
    rw [CFSG.openPCoreOf_eq_map_pCore,
      Subgroup.card_map_of_injective H.subtype_injective]
  rw [h2, h1]
  exact Nat.mul_comm _ _

theorem pCoreOf_eq_inf {K L : Subgroup G} (hKL : K ≤ L) (hL : L = K ⊔ pCoreOf 2 L) :
    pCoreOf 2 K = K ⊓ pCoreOf 2 L := by
  have hKQ : K ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
    hKL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L)
  apply le_antisymm
  · refine le_inf (CFSG.LieType.BorelTits.pCoreOf_le 2 K) ?_
    obtain ⟨a, ha⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K).exists_card_eq
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
    have hPQ : pCoreOf 2 K ≤ Subgroup.normalizer (pCoreOf 2 L : Set G) :=
      (CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKQ
    have hprod := CFSG.GH74.Uniqueness.card_sup_mul_card_inf'
      (A := pCoreOf 2 L) (C := pCoreOf 2 K) hPQ
    have hcardN : Nat.card (pCoreOf 2 K ⊔ pCoreOf 2 L : Subgroup G) ∣ 2 ^ (a + b) := by
      refine ⟨Nat.card (pCoreOf 2 L ⊓ pCoreOf 2 K : Subgroup G), ?_⟩
      rw [hprod, hb, ha, ← pow_add, Nat.add_comm]
    have hNp : IsPGroup 2 (pCoreOf 2 K ⊔ pCoreOf 2 L : Subgroup G) :=
      IsPGroup.of_card_dvd_pow hcardN
    have hN_le : pCoreOf 2 K ⊔ pCoreOf 2 L ≤ L :=
      sup_le ((CFSG.LieType.BorelTits.pCoreOf_le 2 K).trans hKL)
        (CFSG.LieType.BorelTits.pCoreOf_le 2 L)
    have hL_norm : L ≤ Subgroup.normalizer
        ((pCoreOf 2 K ⊔ pCoreOf 2 L : Subgroup G) : Set G) := by
      refine hL.trans_le ?_
      refine sup_le ?_ ?_
      · exact (le_inf (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K) hKQ).trans
          (Subgroup.inf_normalizer_le_normalizer_sup (pCoreOf 2 K) (pCoreOf 2 L))
      · exact (le_sup_right : pCoreOf 2 L ≤ pCoreOf 2 K ⊔ pCoreOf 2 L).trans
          Subgroup.le_normalizer
    exact (le_sup_left : pCoreOf 2 K ≤ pCoreOf 2 K ⊔ pCoreOf 2 L).trans
      (CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 hN_le hL_norm hNp)
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left ?_
      ((CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).to_le inf_le_right)
    exact (le_inf Subgroup.le_normalizer hKQ).trans
      Subgroup.inf_normalizer_le_normalizer_inf

theorem exists_isSylowOf_le {K L : Subgroup G} {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hKL : K ≤ L)
    (hL : L = K ⊔ pCoreOf 2 L) : ∃ P ≤ K, CFSG.ABGLocalTools.IsSylowOf p P L := by
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨P, hP⟩ := CFSG.ABGLocalTools.exists_isSylowOf p K
  have hnotKL : ¬ p ∣ K.relIndex L := by
    intro hpdvd
    obtain ⟨b, hb⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
    have hdvd : K.relIndex L ∣ 2 ^ b := by
      have hprod := CFSG.GH74.Uniqueness.card_sup_mul_card_inf'
        (A := pCoreOf 2 L) (C := K)
        (hKL.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 L))
      rw [← hL] at hprod
      refine ⟨Nat.card (pCoreOf 2 L ⊓ K : Subgroup G), ?_⟩
      rw [← hb]
      have hrel := Subgroup.relIndex_mul_card K L
      rw [inf_eq_left.mpr hKL] at hrel
      have hcancel : K.relIndex L * Nat.card (pCoreOf 2 L ⊓ K : Subgroup G) * Nat.card K
          = Nat.card (pCoreOf 2 L) * Nat.card K := by
        calc K.relIndex L * Nat.card (pCoreOf 2 L ⊓ K : Subgroup G) * Nat.card K
            = (K.relIndex L * Nat.card K) * Nat.card (pCoreOf 2 L ⊓ K : Subgroup G) := by
              ring
          _ = Nat.card L * Nat.card (pCoreOf 2 L ⊓ K : Subgroup G) := by rw [hrel]
          _ = Nat.card (pCoreOf 2 L) * Nat.card K := hprod
      exact (Nat.mul_right_cancel Nat.card_pos hcancel).symm
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp
      (hp.dvd_of_dvd_pow (hpdvd.trans hdvd)))
  refine ⟨P, hP.le, ?_⟩
  rw [CFSG.ABGLocalTools.isSylowOf_iff] at hP ⊢
  obtain ⟨hPK, hPp, hPdvd⟩ := hP
  refine ⟨hPK.trans hKL, hPp, ?_⟩
  have hrel : P.relIndex L = P.relIndex K * K.relIndex L :=
    (Subgroup.relIndex_mul_relIndex P K L hPK hKL).symm
  rw [hrel, hp.dvd_mul]
  rintro (h | h)
  · exact hPdvd h
  · exact hnotKL h

theorem card_eq_three_or_seven_of_isL3 {L A : Subgroup G} (h : IsL3 (Bar2 L) 1) (hA : A ≤ L)
    (hp : (Nat.card A).Prime) (hodd : Odd (Nat.card A)) : Nat.card A = 3 ∨ Nat.card A = 7 := by
  have hcard168 : Nat.card (Bar2 L) = 168 := card_eq_of_isL3 h
  obtain ⟨k, hk⟩ := (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 L).exists_card_eq
  have hcardL : Nat.card L = 2 ^ k * 168 := by
    have h1 := card_eq_card_pCoreOf_mul_card_bar2 L
    rw [h1, hcard168, hk]
  have hdvdL : Nat.card A ∣ 2 ^ k * 168 := by
    rw [← hcardL]
    exact Subgroup.card_dvd_of_le hA
  have hqne2 : Nat.card A ≠ 2 := by
    intro h2
    rw [h2] at hodd
    exact absurd hodd (by norm_num)
  rcases (hp.dvd_mul.mp hdvdL) with h2k | h168
  · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2k)) hqne2
  · have h21 : Nat.card A ∣ 3 * 7 := by
      have h168' : 168 = 2 ^ 3 * (3 * 7) := by norm_num
      rw [h168'] at h168
      rcases (hp.dvd_mul.mp h168) with h8 | h37
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h8)) hqne2
      · exact h37
    rcases (hp.dvd_mul.mp h21) with h3 | h7
    · left; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    · right; exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).mp h7

theorem calNOf_eq_singleton_of_forall_le {M K : Subgroup G} (hM : M ≠ ⊤) (hKM : K ≤ M)
    (h : ∀ H : Subgroup G, H ≠ ⊤ → K ≤ H → H ≤ M) : calNOf K = {M} := by
  ext N
  constructor
  · intro hN
    rw [calNOf, Set.mem_setOf_eq] at hN
    obtain ⟨hcoat, hKN⟩ := hN
    have hNM : N ≤ M := h N hcoat.ne_top hKN
    rcases hcoat.le_iff.mp hNM with htop | hMN
    · exact absurd htop hM
    · rw [Set.mem_singleton_iff]; exact hMN.symm
  · intro hN
    rw [Set.mem_singleton_iff] at hN
    rw [hN, calNOf, Set.mem_setOf_eq]
    refine ⟨?_, hKM⟩
    rw [isCoatom_iff_ge_of_le]
    refine ⟨hM, ?_⟩
    intro b hb hMb
    exact h b hb (hKM.trans hMb)

namespace Hyp141

variable {D : Data G} {L₁ L₂ X : Subgroup G}

theorem mem_isL3 (h : Hyp141 D L₁ L₂ X) {L : Subgroup G}
    (hL : L ∈ ({L₁, L₂} : Set (Subgroup G))) : L ∈ calC D.M ∧ IsL3 (Bar2 L) 1 := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL
  rcases hL with rfl | rfl
  · exact ⟨h.mem₁, h.shape₁⟩
  · exact ⟨h.mem₂, h.shape₂⟩

theorem card_three_mem_uniqueSet (h : Hyp141 D L₁ L₂ X) (h1421 : Thm1421 D)
    {L : Subgroup G} (hL : L ∈ ({L₁, L₂} : Set (Subgroup G))) {A : Subgroup G} (hA : A ≤ L)
    (hcard : Nat.card A = 3) : A ∈ uniqueSet D.M := by
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hL
  rcases hL with hL1 | hL2
  · rw [hL1] at hA
    have hX1 : X ⊓ L₁ ∈ uniqueSet D.M := (h1421 L₁ L₂ X h).1
    have hS : CFSG.ABGLocalTools.IsSylowOf 3 (X ⊓ L₁) L₁ := isSylowOf_inf_left h
    have hcardS : Nat.card (X ⊓ L₁ : Subgroup G) = 3 := card_inf_left h
    have hSA : CFSG.ABGLocalTools.IsSylowOf 3 A L₁ := by
      apply CFSG.ABGLocalTools.isSylowOf_of_card hA
      rw [hcard]
      exact hcardS.symm.trans hS.card_eq
    obtain ⟨k, hkL, hk⟩ := hS.exists_mem_conj hSA
    have hAeq : A = (X ⊓ L₁).map (MulAut.conj k).toMonoidHom := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · intro hx
        refine ⟨k⁻¹ * x * k, (hk x).mp hx, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro ⟨y, hy, hyx⟩
        refine (hk x).mpr ?_
        rw [hyx.symm]
        have hconj : k⁻¹ * ((MulAut.conj k).toMonoidHom y) * k = y := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [hconj]
        exact hy
    rw [hAeq]
    exact conj_mem_uniqueSet hX1 (CFSG.Quasithin.A3.subnormal_le h.mem₁.1 hkL)
  · rw [hL2] at hA
    have hX2 : X ⊓ L₂ ∈ uniqueSet D.M := (h1421 L₁ L₂ X h).2
    have hS : CFSG.ABGLocalTools.IsSylowOf 3 (X ⊓ L₂) L₂ := isSylowOf_inf_right h
    have hcardS : Nat.card (X ⊓ L₂ : Subgroup G) = 3 := card_inf_right h
    have hSA : CFSG.ABGLocalTools.IsSylowOf 3 A L₂ := by
      apply CFSG.ABGLocalTools.isSylowOf_of_card hA
      rw [hcard]
      exact hcardS.symm.trans hS.card_eq
    obtain ⟨k, hkL, hk⟩ := hS.exists_mem_conj hSA
    have hAeq : A = (X ⊓ L₂).map (MulAut.conj k).toMonoidHom := by
      ext x
      rw [Subgroup.mem_map]
      constructor
      · intro hx
        refine ⟨k⁻¹ * x * k, (hk x).mp hx, ?_⟩
        simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
        group
      · rintro ⟨y, hy, hyx⟩
        refine (hk x).mpr ?_
        rw [hyx.symm]
        have hconj : k⁻¹ * ((MulAut.conj k).toMonoidHom y) * k = y := by
          simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
          group
        rw [hconj]
        exact hy
    rw [hAeq]
    exact conj_mem_uniqueSet hX2 (CFSG.Quasithin.A3.subnormal_le h.mem₂.1 hkL)

theorem normalizer_le_of_odd_prime_card (h : Hyp141 D L₁ L₂ X) (h1421 : Thm1421 D)
    (hSg : UC6S846.SigmaStd D) {L : Subgroup G} (hL : L ∈ ({L₁, L₂} : Set (Subgroup G)))
    {A : Subgroup G} (hA : A ≤ L) (hp : (Nat.card A).Prime) (hodd : Odd (Nat.card A)) :
    normalizer (A : Set G) ≤ D.M := by
  obtain ⟨hLC, hshape⟩ := mem_isL3 h hL
  rcases card_eq_three_or_seven_of_isL3 hshape hA hp hodd with h3 | h7
  · exact CFSG.LocalAnalysis.RankThreeUC.normalizer_le_of_mem_uniqueSet D.maxLocal
      (card_three_mem_uniqueSet h h1421 hL hA h3)
  · haveI : Fact (Nat.Prime 7) := ⟨by norm_num⟩
    have hSE : CFSG.RankThree.PartOne.IsStronglyPEmbedded 7 D.M :=
      UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hLC) (by rw [h.sig]; simp)
    have hne : A ≠ ⊥ := by
      rintro rfl
      rw [Subgroup.card_bot] at h7
      norm_num at h7
    have hAp : IsPGroup 7 A := IsPGroup.of_card (n := 1) (by rw [h7, pow_one])
    exact hSE.normalizer_le hne hAp (hA.trans (CFSG.Quasithin.A3.subnormal_le hLC.1))

end Hyp141

@[expose] def Thm1422 (D : Data G) : Prop :=
  ∀ L₁ L₂ X : Subgroup G, Hyp141 D L₁ L₂ X → ∀ L ∈ ({L₁, L₂} : Set (Subgroup G)),
    ∀ K : Subgroup G, K ≤ L → L = K ⊔ pCoreOf 2 L → calNOf K = {D.M}

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99InnerFour
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight99PairFour
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Sz

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)

variable {G : Type} [Group G] [Finite G]

theorem r899_sp_of_normal {D : Data G}
    (hSg : UC6S846.SigmaStd D) (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h614 : UC6.R6_14 D) (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    {K₁ K₂ : Subgroup G} (h1C : K₁ ∈ calC D.M) (h2C : K₂ ∈ calC D.M) (hne : K₁ ≠ K₂)
    (h1N : D.M ≤ normalizer (K₁ : Set G)) (h2N : D.M ≤ normalizer (K₂ : Set G))
    {n₁ n₂ s r : ℕ} (h1S : IsL2 (Bar2 K₁) n₁ ∨ IsSz (Bar2 K₁) n₁)
    (h2S : IsL2 (Bar2 K₂) n₂ ∨ IsSz (Bar2 K₂) n₂) (hs₁ : s ∣ n₁) (hs₂ : s ∣ n₂)
    (hr : r.Prime) (hr2 : r ≠ 2) (hrs : r ∣ 2 ^ s - 1) :
    IsStronglyPEmbedded r D.M := by
  classical
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC h1C
  have hsp : IsStronglyPEmbedded p D.M := UC6S846.sp_of_mem_sig hSg hns hp
  have hOp : UC22.F10.OpRes p D.M = D.M :=
    UC6.opRes_eq_of_stronglyEmbedded_uc6 D.standing.simple D.standing.nonab hpp hsp
  have h76p : Conclusion76 D.M p := h76 p hp hsp
  obtain ⟨A₀, hA₀M, hA₀el, hA₀c⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (k := 4) hpp (hfour p hp)
  have hA₀N₁ : A₀ ≤ normalizer (K₁ : Set G) := hA₀M.trans h1N
  have hA₀N₂ : A₀ ≤ normalizer (K₂ : Set G) := hA₀M.trans h2N
  have hcomm₁ : ∀ a b : Outer (Bar2 K₁), a * b = b * a := by
    rcases h1S with hX | hX
    · exact uc22p22g_outer_comm hX
    · exact r899_outer_comm_Sz hX
  have hcomm₂ : ∀ a b : Outer (Bar2 K₂), a * b = b * a := by
    rcases h2S with hX | hX
    · exact uc22p22g_outer_comm hX
    · exact r899_outer_comm_Sz hX
  have hZ₁ : center (Bar2 K₁) = ⊥ := by
    rcases h1S with hX | hX
    · exact uc22p22g_center_bot hX
    · have : IsSimpleGroup (Bar2 K₁) :=
        CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX
      exact uc22p21k_center_eq_bot h1C.2.2
  have hZ₂ : center (Bar2 K₂) = ⊥ := by
    rcases h2S with hX | hX
    · exact uc22p22g_center_bot hX
    · have : IsSimpleGroup (Bar2 K₂) :=
        CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hX
      exact uc22p21k_center_eq_bot h2C.2.2
  have hle₁ : ∀ Q : Subgroup (Bar2 K₁), IsElemAbelian p Q → Nat.card Q ≤ p := by
    intro Q hQ
    rcases h1S with hX | hX
    · have : CFSG.IsElementaryAbelian p ↥Q := hQ.isElementaryAbelian
      exact uc22p22g_rank hpp hp2 hX Q
    · exact uc22s21r8100_card_le_of_isSz hX hpp hp2 hQ
  have hle₂ : ∀ Q : Subgroup (Bar2 K₂), IsElemAbelian p Q → Nat.card Q ≤ p := by
    intro Q hQ
    rcases h2S with hX | hX
    · have : CFSG.IsElementaryAbelian p ↥Q := hQ.isElementaryAbelian
      exact uc22p22g_rank hpp hp2 hX Q
    · exact uc22s21r8100_card_le_of_isSz hX hpp hp2 hQ
  have hinn₁ : ∀ b (hb : b ∈ A₀), UC6S846.rhoL K₁ ⟨b, hA₀N₁ hb⟩ ∈
      (MulAut.conj : Bar2 K₁ →* MulAut (Bar2 K₁)).range :=
    fun b hb => r899_inner_of_le_normalizer h1N hpp hOp hcomm₁ (hA₀M hb) (hA₀el.2 b hb)
  obtain ⟨C₁, hC₁A₀, hC₁c, hC₁card⟩ :=
    r899_exists_centralizesBar_of_inner (K := K₁) hpp hp2 hZ₁ hle₁ hA₀el hA₀N₁ hinn₁
  have hC₁el : IsElemAbelian p C₁ := hA₀el.mono hC₁A₀
  have hC₁N₂ : C₁ ≤ normalizer (K₂ : Set G) := hC₁A₀.trans hA₀N₂
  have hinn₂ : ∀ b (hb : b ∈ C₁), UC6S846.rhoL K₂ ⟨b, hC₁N₂ hb⟩ ∈
      (MulAut.conj : Bar2 K₂ →* MulAut (Bar2 K₂)).range :=
    fun b hb =>
      r899_inner_of_le_normalizer h2N hpp hOp hcomm₂ (hA₀M (hC₁A₀ hb)) (hC₁el.2 b hb)
  obtain ⟨C₂, hC₂C₁, hC₂c, hC₂card⟩ :=
    r899_exists_centralizesBar_of_inner (K := K₂) hpp hp2 hZ₂ hle₂ hC₁el hC₁N₂ hinn₂
  have hC₂p : p ^ 2 ≤ Nat.card C₂ := by
    have h4 : p ^ 2 * p ^ 2 ≤ p ^ 2 * Nat.card C₂ :=
      calc p ^ 2 * p ^ 2 = p ^ 4 := by ring
        _ = Nat.card A₀ := hA₀c.symm
        _ ≤ p * Nat.card C₁ := hC₁card
        _ ≤ p * (p * Nat.card C₂) := Nat.mul_le_mul_left _ hC₂card
        _ = p ^ 2 * Nat.card C₂ := by ring
    exact Nat.le_of_mul_le_mul_left h4 (pow_pos hpp.pos 2)
  obtain ⟨A, hAC₂, hAel, hAc⟩ :=
    UC6S846.exists_card_p_sq hpp (hC₁el.mono hC₂C₁) hC₂p
  have hAM : A ≤ D.M := hAC₂.trans ((hC₂C₁.trans hC₁A₀).trans hA₀M)
  have hRN : ∀ R : Subgroup G, CFSG.ABGLocalTools.IsSylowOf r R D.M →
      R ≤ normalizer (K₁ : Set G) ∧ R ≤ normalizer (K₂ : Set G) :=
    fun R hR => ⟨hR.le.trans h1N, hR.le.trans h2N⟩
  refine r899_sp_of_pair_centralizing (K₁ := K₁) (K₂ := K₂) (n₁ := n₁) (n₂ := n₂) (s := s)
    (r := r) (p := p) (A := A) hSg h614 h1C h2C hne h1S h2S hs₁ hs₂ hr hr2 hrs hRN hpp hp2 h76p
    hAM hAel hAc ?_
  exact fun a ha => ⟨hC₁c a (hC₂C₁ (hAC₂ ha)), hC₂c a (hAC₂ ha)⟩

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

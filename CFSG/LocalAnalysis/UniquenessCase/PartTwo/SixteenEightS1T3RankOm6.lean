module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Kbar
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Rank13
public import CFSG.GroupTheory.PRankBound
public import CFSG.GroupTheory.WeirSylow.CrossRankLinear

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {W : Type} [CommGroup W] [Finite W] {A L T : Subgroup (MulAut W)}

private theorem s16t3_pRank_le_of_index_le_two {G : Type} [Group G] [Finite G]
    {H K : Subgroup G} (hHK : H ≤ K) (hidx : (H.subgroupOf K).index ≤ 2) :
    CFSG.Open.pRank 3 K ≤ CFSG.Open.pRank 3 H := by
  obtain ⟨E, hEK, hEab, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) K
  have hEH : E ≤ H := by
    intro x hx
    have hxK : x ∈ K := hEK hx
    let x' : ↥K := ⟨x, hxK⟩
    have hx'3 : x' ^ 3 = 1 := Subtype.ext (hEab.2 x hx)
    have hidx0 : (H.subgroupOf K).index ≠ 0 := (H.subgroupOf K).index_ne_zero_of_finite
    have hx'H : x' ∈ H.subgroupOf K := by
      rcases (by omega : (H.subgroupOf K).index = 1 ∨
          (H.subgroupOf K).index = 2) with h1 | h2
      · rw [Subgroup.index_eq_one] at h1
        rw [h1]
        exact Subgroup.mem_top x'
      · have hsq : x' ^ 2 ∈ H.subgroupOf K := Subgroup.sq_mem_of_index_two h2 x'
        have hx'eq : x' = (x' ^ 2)⁻¹ := by
          apply eq_inv_of_mul_eq_one_left
          have h : x' * x' ^ 2 = 1 := by
            have h3 := hx'3
            rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_succ'] at h3
            exact h3
          exact h
        rw [hx'eq]
        exact Subgroup.inv_mem _ hsq
    exact Subgroup.mem_subgroupOf.mp hx'H
  exact CFSG.SectionRank.le_pRank (p := 3) (by norm_num) hEH hEab hEcard

private theorem s16t3_index_subgroupOf_le_two {W : Type} [CommGroup W] [Finite W]
    {A L T : Subgroup (MulAut W)} (h : ThreeNat A L T) (h7 : Nat.card ↥(irrSet L) = 7)
    {N : Subgroup (MulAut W)} (hNA : N ≤ A) (hLN : L ≤ N)
    (hcomm : ∀ n ∈ N, ∀ k ∈ s1t3KBar A L, n * k = k * n)
    (hdisj : N ⊓ s1t3KBar A L = ⊥) (hsup : N ⊔ s1t3KBar A L = A) :
    (L.subgroupOf N).index ≤ 2 := by
  have hNinf : N ⊓ (L ⊔ s1t3KBar A L) = L := by
    have hKnorm : s1t3KBar A L ≤ Subgroup.normalizer (L : Set (MulAut W)) := by
      rw [Subgroup.le_normalizer_iff]
      intro k hk l hl
      have h := hcomm l (hLN hl) k hk
      rw [← h, mul_assoc, mul_inv_cancel, mul_one]
      exact hl
    refine le_antisymm ?_ fun x hx => ⟨hLN hx, Subgroup.mem_sup_left hx⟩
    intro x hx
    obtain ⟨hxN, hxsup⟩ := Subgroup.mem_inf.mp hx
    have hxmul : x ∈ (↑(L ⊔ s1t3KBar A L) : Set (MulAut W)) := hxsup
    rw [Subgroup.coe_mul_of_right_le_normalizer_left L (s1t3KBar A L) hKnorm,
      Set.mem_mul] at hxmul
    obtain ⟨l, hl, k, hk, hlk⟩ := hxmul
    have hk_eq : k = l⁻¹ * x := by
      rw [← hlk]
      exact (inv_mul_cancel_left l k).symm
    have hkN : k ∈ N := by
      rw [hk_eq]
      exact N.mul_mem (N.inv_mem (hLN hl)) hxN
    have hkbot : k ∈ (⊥ : Subgroup (MulAut W)) := by
      have : k ∈ N ⊓ s1t3KBar A L := ⟨hkN, hk⟩
      rwa [hdisj] at this
    rw [Subgroup.mem_bot.mp hkbot, mul_one] at hlk
    rwa [← hlk]
  have hthree : ∀ x y z : ↥N, x⁻¹ * y ∈ L.subgroupOf N ∨ x⁻¹ * z ∈ L.subgroupOf N ∨
      y⁻¹ * z ∈ L.subgroupOf N := by
    intro x y z
    have hmem := ThreeNat.index_kBar_le_two h h7 (hNA x.2) (hNA y.2) (hNA z.2)
    have key : ∀ w : ↥N, (w : MulAut W) ∈ L ⊔ s1t3KBar A L → w ∈ L.subgroupOf N := by
      intro w hw
      refine Subgroup.mem_subgroupOf.mpr ?_
      have : (w : MulAut W) ∈ N ⊓ (L ⊔ s1t3KBar A L) := ⟨w.2, hw⟩
      rwa [hNinf] at this
    rcases hmem with hmem | hmem | hmem
    · exact Or.inl (key _ (by simpa using hmem))
    · exact Or.inr (Or.inl (key _ (by simpa using hmem)))
    · exact Or.inr (Or.inr (key _ (by simpa using hmem)))
  rcases s16t3_index_eq_two_of_thirds (L.subgroupOf N) hthree with htop | hidx
  · rw [htop, Subgroup.index_top]
    norm_num
  · rw [hidx]

theorem ThreeNat.pRank_three_le_three_omegaMinus6 (h : ThreeNat A L T)
    (h7 : Nat.card ↥(irrSet L) = 7) (hL : IsOmegaMinus ↥L 6 1)
    (hK : Nat.card ↥(s1t3KBar A L) = 7) : CFSG.Open.pRank 3 A ≤ 3 := by
  obtain ⟨N, hNA, hLN, _hfix, hcomm, hdisj, hsup, _hKbar⟩ := h.structure_of_seven h7
  have hKN : s1t3KBar A L ≤ Subgroup.centralizer (N : Set (MulAut W)) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    intro n hn
    exact hcomm n hn k hk
  have hrankA : CFSG.Open.pRank 3 A =
      CFSG.Open.pRank 3 N + CFSG.Open.pRank 3 (s1t3KBar A L) := by
    have hh := s13_pRank_sup_eq_add (p := 3) (by norm_num) hKN hdisj
    rw [hsup] at hh
    exact hh
  have hK0 : CFSG.Open.pRank 3 (s1t3KBar A L) ≤ 0 :=
    CFSG.GroupTheory.pRank_le_of_not_dvd_pow_succ (p := 3) (k := 0) (by norm_num)
      (by rw [hK]; norm_num)
  have hidx : (L.subgroupOf N).index ≤ 2 :=
    s16t3_index_subgroupOf_le_two h h7 hNA hLN hcomm hdisj hsup
  have hNL : CFSG.Open.pRank 3 N ≤ CFSG.Open.pRank 3 L :=
    s16t3_pRank_le_of_index_le_two hLN hidx
  have hL3 : CFSG.Open.pRank 3 L ≤ 3 := by
    obtain ⟨-, K, hKf, hKfin, b, c, hKcard, _hirr, ⟨e⟩⟩ := hL
    letI : Field K := hKf
    letI : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by simpa using hKcard
    have h1 : CFSG.Open.pRank 3 L = CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) :=
      CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := 3) L
    have h2 : CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Open.StatedProj
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c)))) :=
      CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e
    have hKunits : Nat.card Kˣ = 1 := by rw [Nat.card_units, hK2]
    haveI : Subsingleton Kˣ := Finite.card_le_one_iff_subsingleton.mp (by rw [hKunits])
    have h3 : CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Open.StatedProj
          (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c)))) =
        CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Open.StatedOmega
          (CFSG.Open.StatedQuadMinus 3 K b c))) :=
      CFSG.GroupTheory.WeirSylow.pRank_top_statedProj_eq (p := 3) (d := 1) (by norm_num)
        (fun c _ => by rw [Subsingleton.elim c 1, one_pow])
    have h4 : CFSG.Open.pRank 3 (⊤ : Subgroup (CFSG.Open.StatedOmega
          (CFSG.Open.StatedQuadMinus 3 K b c))) ≤
        CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.GeneralLinearGroup
          (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K)) :=
      CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num)
        (Subgroup.subtype (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c)))
        (Subgroup.subtype_injective (CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 3 K b c)))
    have h5 : CFSG.Open.pRank 3 (⊤ : Subgroup (Matrix.GeneralLinearGroup
        (Fin 2 ⊕ Fin 2 ⊕ Fin 2) K)) = 3 := by
      rw [CFSG.GroupTheory.WeirSylow.pRank_top_gl_eq (p := 3) (by norm_num)
        (by rw [hK2]; norm_num)]
      rw [hK2]
      have hcard : Fintype.card (Fin 2 ⊕ Fin 2 ⊕ Fin 2) = 6 := by decide
      rw [hcard]
      have ho : orderOf (((2 : ℕ) : ZMod 3)) = 2 := by
        haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
        rw [orderOf_eq_prime_iff]
        exact ⟨(by decide : (((2 : ℕ) : ZMod 3)) ^ 2 = 1),
          (by decide : (((2 : ℕ) : ZMod 3)) ≠ 1)⟩
      rw [ho]
    omega
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

module

public import CFSG.Quasithin.Vol2.Ch11SecBHBMain
public import CFSG.Quasithin.Background.E2TwoCLie

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.H13

theorem derivedHallBorel_core (hFB : FactBorelComm) {G : Type} [Group G] [Finite G]
    {T M H K : Subgroup G} (hT : quasithinIsSylowTwo T) (hTH : T ≤ H) (hTM : T ≤ M)
    (hU : IsUniqueMaxOver H T (H ⊓ M)) (hns : ¬ Group.IsSolvable ↥H) (hKc : K ∈ cComp H)
    (hHK : H = K ⊔ T) (hlie : E2.E22LieCases H T (H ⊓ M) K) :
    ∃ B : Subgroup G, QuasithinUnique.Lin2.IsHallTwoPrimeOf B (H ⊓ M) ∧
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
      T ≤ pCoreOf 2 (H ⊓ M) ⊔ (T ⊓ Subgroup.normalizer (B : Set G)) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := H ⊓ M with hXdef
  have hTX : T ≤ X := le_inf hTH hTM
  have hTS : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hT hTH
  have hKH : K ≤ H := hHK ▸ le_sup_left
  have hKperf : ⁅K, K⁆ = K := (show quasithinIsCComponent K H from hKc).2.1
  have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hOT : pCoreOf 2 H ≤ T := B6.pCoreOf_two_le_of_isSylowTwoOf hTS
  have hOJ : pCoreOf 2 H ≤ kerIn X H := le_kerIn_of_le_normalizer (hOT.trans hTX) hHO
  have hOK : pCoreOf 2 K ≤ kerIn X H :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2
      (subnormal_of_mem_cComp hKc)).trans hOJ
  suffices hNex : ∃ N : Subgroup G, N ≤ X ∧ X ≤ Subgroup.normalizer (N : Set G) ∧
      (∀ x ∈ X, ∃ k : ℕ, x ^ 2 ^ k ∈ N) ∧ IsPGroup 2 ↥⁅N, N⁆ by
    obtain ⟨N, hNX, hXN, h2, hC⟩ := hNex
    exact exists_hall_of_commutator hNX hXN h2 hC (isSylowTwoOf_of_quasithinIsSylowTwo hT hTX)
  dsimp only [E2.E22LieCases] at hlie
  rcases hlie with ⟨hJ, t, ht, -, hMeq, n, hn, htype, hBor⟩ | ⟨hTK, hJ, h2⟩
  ·
    have hcent : ∀ k ∈ K, k ∈ kerIn X H → ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
      intro k hk hkJ y hy
      rw [hJ] at hkJ
      refine inf_pCoreOf_le_pCoreOf hKH ⟨K.mul_mem (K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk))
        (K.inv_mem hy), ?_⟩
      have h3 : y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (hHO (hKH hy)) _).mp ((pCoreOf 2 H).inv_mem hkJ)
      have := (pCoreOf 2 H).mul_mem hkJ h3
      simpa [mul_assoc] using this
    have hXK := isPGroup_commutator_inf_of_isBorelIn hFB hKH hKperf hOK hcent hn
      (Or.inl ⟨hn, htype.elim Or.inl fun h => Or.inr (Or.inl h)⟩) hBor
    set N := conjClosure (X ⊓ K) T ⊔ pCoreOf 2 H with hNdef
    have hCX : conjClosure (X ⊓ K) T ≤ X := conjClosure_le fun s hs z hz =>
      X.mul_mem (X.mul_mem (hTX hs) hz.1) (X.inv_mem (hTX hs))
    have hNX : N ≤ X := sup_le hCX (hOT.trans hTX)
    have hcj : cjSub t (X ⊓ K) ≤ N := by
      intro x hx
      rw [mem_cjSub] at hx
      have := mem_conjClosure ht hx
      rw [show t * (t⁻¹ * x * t) * t⁻¹ = x by group] at this
      exact Subgroup.mem_sup_left this
    have hXKN : X ⊓ K ≤ N := (le_conjClosure _ _).trans le_sup_left
    have hXle : X ≤ T ⊔ N := by
      rw [hMeq]
      exact sup_le (sup_le (hXKN.trans le_sup_right) (hcj.trans le_sup_right)) le_sup_left
    have hXN : X ≤ Subgroup.normalizer (N : Set G) := by
      rw [hMeq]
      refine sup_le (sup_le ((hXKN.trans Subgroup.le_normalizer))
        (hcj.trans Subgroup.le_normalizer)) fun s hs => ?_
      exact mem_normalizer_sup_of_mem (le_normalizer_conjClosure _ _ hs) (hHO (hTH hs))
    refine ⟨N, hNX, hXN, B6.isTwoQuotient_of_sup_eq hT.1 hXN
      (le_antisymm (sup_le hTX hNX) hXle), ?_⟩
    exact isPGroup_commutator_case_one hU hT.1 hns hKc hJ hXK
  ·
    have hn : ∃ n : ℕ, 2 ≤ n ∧ (E2.IsBenderOf n ↥(E2.star X H K) ∨
        IsPSL 3 2 n ↥(E2.star X H K) ∨ IsPSp4 2 n ↥(E2.star X H K)) ∧
        E2.IsBorelIn (E2.star X H K) (E2.star X H (X ⊓ K)) := by
      rcases h2 with ⟨n, hBen, hBor⟩ | ⟨n, hn, htype, -, hBor⟩
      · exact ⟨n, hBen.1, Or.inl hBen, hBor⟩
      · exact ⟨n, hn, Or.inr htype, hBor⟩
    obtain ⟨n, hn, htype, hBor⟩ := hn
    have hcent : ∀ k ∈ K, k ∈ kerIn X H → ∀ y ∈ K, k * y * k⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
      intro k hk hkJ y hy
      refine inf_pCoreOf_le_pCoreOf hKH ⟨K.mul_mem (K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk))
        (K.inv_mem hy), ?_⟩
      exact ((hJ k).mp hkJ).2 y (Subgroup.mem_sup_left hy)
    have hXK := isPGroup_commutator_inf_of_isBorelIn hFB hKH hKperf hOK hcent hn htype hBor
    have hHKn : H ≤ Subgroup.normalizer (K : Set G) := by
      rw [hHK]
      exact sup_le Subgroup.le_normalizer hTK
    have hXN : X ≤ Subgroup.normalizer ((X ⊓ K : Subgroup G) : Set G) := fun x hx =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hx, hHKn hx.1⟩
    have h2K := B6.isTwoQuotient_of_sup_eq hT.1 hHKn (by rw [sup_comm]; exact hHK.symm)
    refine ⟨X ⊓ K, inf_le_left, hXN, fun x hx => ?_, hXK⟩
    obtain ⟨k, hk⟩ := h2K x hx.1
    exact ⟨k, X.pow_mem hx _, hk⟩

end CFSG.Quasithin.Vol2.Ch11.SecB

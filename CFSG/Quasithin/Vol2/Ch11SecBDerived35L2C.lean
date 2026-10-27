module

public import CFSG.Quasithin.Vol2.Ch11SecBDerived35L2
public import CFSG.Quasithin.Vol2.Ch11SecB35C
public import CFSG.Quasithin.Vol2.Ch11SecBHBMain

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecB

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped commutatorElement

theorem derivedL2ListC_of_parts (h701 : Stmt7_0_1) (hd : L2Faithful) (ho : L2Overgroup)
    (hc : L2NotJ4Orth) (ha : L2Graph) (hb : L2Suzuki) (he : L2Unitary) : DerivedL2ListC := by
  intro G _ _ T L I n H K hyp hH hZH hn1 hKc hHK hq hcases
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set X := H ⊓ Subgroup.normalizer (L : Set G) with hXdef
  have hKH : K ≤ H := le_of_mem_cComp hKc
  have hTH : T ≤ H := hH.1.1
  have hTX : T ≤ X := le_inf hTH hyp.normal
  have hTS : IsSylowTwoOf T H := isSylowTwoOf_of_quasithinIsSylowTwo hyp.fsu.sylow hTH
  have hHO : H ≤ Subgroup.normalizer (pCoreOf 2 H : Set G) :=
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hOJ : pCoreOf 2 H ≤ kerIn X H :=
    le_kerIn_of_le_normalizer ((B6.pCoreOf_two_le_of_isSylowTwoOf hTS).trans hTX) hHO
  have hOK : pCoreOf 2 K ≤ kerIn X H :=
    (CFSG.RankThreeEvenClassification.Helpers.pCoreOf_le_pCoreOf_of_subnormal 2
      (subnormal_of_mem_cComp hKc)).trans hOJ
  have hn1' : E1.nParam H ≠ 1 := hn1.ne'
  have hS : ∀ k : ℕ, 2 ≤ k → E1.nParam H ≤ k → L2Setting G T L I n H K k := fun k hk hle =>
    ⟨hyp, hH, hZH, ⟨hn1, hle⟩, hk, hKc, hHK, hq, hcases⟩
  have hFF4 : ∀ k : ℕ, L2Setting G T L I n H K k → L2BadType k ↥(E2.star X H K) →
      ∃ Kp Ip : Subgroup G, K ≤ Kp ∧ ∃ _ : FSU G T Kp Ip, ∃ _ : IsMulCommutative ↥(fsuV T Ip),
        Concl701FF T Kp Ip ∨ Concl701Four T Kp Ip := by
    intro k hS' hbt
    obtain ⟨Kp, Ip, hKK, hfsu⟩ := ho G T L I n H K k hS' (hd G T L I n H K k hS') hbt
    obtain ⟨hcomm, -, -, hconcl⟩ := h701 G T Kp Ip hfsu
    obtain ⟨hJ4, hOr⟩ := hc G T L I n H K k hS' hbt Kp Ip hKK hfsu hcomm
    refine ⟨Kp, Ip, hKK, hfsu, hcomm, ?_⟩
    rcases hconcl with h | h | h | h
    · exact Or.inl h
    · exact absurd h hJ4
    · exact absurd h hOr
    · exact Or.inr h
  have hcases0 := hcases
  dsimp only [E2.E22CasesC] at hcases0
  rcases hcases0 with ⟨hJ, -, -, -, -, h1⟩ | ⟨hTK, hJ, h2⟩
  ·
    have hcent : ∀ k' ∈ K, k' ∈ kerIn X H → ∀ y ∈ K, k' * y * k'⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
      intro k' hk hkJ y hy
      rw [hJ] at hkJ
      refine inf_pCoreOf_le_pCoreOf hKH ⟨K.mul_mem (K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk))
        (K.inv_mem hy), ?_⟩
      have h3 : y * k'⁻¹ * y⁻¹ ∈ pCoreOf 2 H :=
        (Subgroup.mem_normalizer_iff.mp (hHO (hKH hy)) _).mp ((pCoreOf 2 H).inv_mem hkJ)
      have := (pCoreOf 2 H).mul_mem hkJ h3
      simpa [mul_assoc] using this
    rcases h1 with ⟨n', hn'2, htype, -, hle⟩ | ⟨_, _, _, _, _, _, h1⟩
    · refine ⟨n', hle, hn'2, ?_⟩
      rcases htype with hP | hSz
      · exact exists_hom_SL2_of_isPSL hKH hOK hcent hP
      · obtain ⟨Kp, Ip, hKK, hfsu, hcomm, hff⟩ := hFF4 n' (hS n' hn'2 hle) (Or.inl hSz)
        exact (hb G T L I n H K n' (hS n' hn'2 hle) hSz Kp Ip hKK hfsu hcomm hff).elim
    · exact absurd h1 hn1'
  ·
    have hcent : ∀ k' ∈ K, k' ∈ kerIn X H → ∀ y ∈ K, k' * y * k'⁻¹ * y⁻¹ ∈ pCoreOf 2 K := by
      intro k' hk hkJ y hy
      refine inf_pCoreOf_le_pCoreOf hKH ⟨K.mul_mem (K.mul_mem (K.mul_mem hk hy) (K.inv_mem hk))
        (K.inv_mem hy), ?_⟩
      exact ((hJ k').mp hkJ).2 y (Subgroup.mem_sup_left hy)
    rcases h2 with ⟨n', hBen, -, hle, -⟩ | ⟨n', -, htype, hdiag, -, hle, -⟩ |
        ⟨_, _, _, _, _, _, _, _, _, h1⟩ | ⟨_, _, _, _, _, h1⟩
    · have hS' := hS n' hBen.1 hle
      refine ⟨n', hle, hBen.1, ?_⟩
      rcases hBen.2 with hP | hSz | hU
      · exact exists_hom_SL2_of_isPSL hKH hOK hcent hP
      · obtain ⟨Kp, Ip, hKK, hfsu, hcomm, hff⟩ := hFF4 n' hS' (Or.inl hSz)
        exact (hb G T L I n H K n' hS' hSz Kp Ip hKK hfsu hcomm hff).elim
      · obtain ⟨Kp, Ip, hKK, hfsu, hcomm, hff⟩ := hFF4 n' hS' (Or.inr (Or.inl hU))
        exact (he G T L I n H K n' hS' hU Kp Ip hKK hfsu hcomm hff).elim
    · have hn'2 : 2 ≤ n' := E2.E22A.two_le_of_one_lt_of_le hn1 hle
      have hS' := hS n' hn'2 hle
      have hbt : L2BadType n' ↥(E2.star X H K) := by
        rcases htype with h | h
        · exact Or.inr (Or.inr (Or.inl h))
        · exact Or.inr (Or.inr (Or.inr h))
      obtain ⟨Kp, Ip, hKK, hfsu, hcomm, hff⟩ := hFF4 n' hS' hbt
      exact (ha G T L I n H K n' hS' hTK htype hdiag Kp Ip hKK hfsu hcomm hff).elim
    · exact absurd h1 hn1'
    · exact absurd h1 hn1'

end CFSG.Quasithin.Vol2.Ch11.SecB

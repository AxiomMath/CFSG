module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223KcV2
public import CFSG.Quasithin.EmptyFaithful.S152U21
public import CFSG.Quasithin.EmptyFaithful.S146xThreeA
public import CFSG.Quasithin.Vol2.Ch1Faithful
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.A4Bridge
public import CFSG.Quasithin.Background.A1aFStar
public import CFSG.Quasithin.Background.OrderingMax
public import CFSG.Quasithin.H13.LocDblCComp
public import CFSG.Quasithin.Background.A3Structure38Basic
public import CFSG.LocalAnalysis.RankThreeEvenClassification.SubnormalCore
public import CFSG.Quasithin.Background.A1cTransferVariants
public import CFSG.Quasithin.Background.D2
public import CFSG.Quasithin.Background.D2Dihedral
public import CFSG.Quasithin.EmptyFaithful.S152UAut
public import CFSG.Quasithin.EmptyFaithful.S152UGen2
public import CFSG.Quasithin.EmptyFaithful.S152UOm4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace S15223

variable {G : Type} [Group G] [Finite G]

theorem le_centralizer_of_not_faithful {T Mc : Subgroup G} (hq : quasithinQTFE14Cat G T Mc)
    {L Z : Subgroup G} (hloc : quasithinIsLocal T L) (hZT : Z ≤ T) (hZe : IsElemAbelian 2 Z)
    (hQZ : pCoreOf 2 (L ⊔ T) ≤ Subgroup.centralizer (Z : Set G))
    (hQL : pCoreOf 2 (L ⊔ T) ≤ Subgroup.normalizer (L : Set G)) :
    L ≤ Subgroup.centralizer (Z : Set G) := by
  by_contra hnot
  have hne : ⁅Z, L⁆ ≠ ⊥ := fun h => hnot (by
    rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer] at h
    exact h)
  obtain ⟨S₂, hS₂⟩ := hq.exists_sylow
  have hH : InH T (L ⊔ T) := ⟨le_sup_right, hloc.2.2.2⟩
  have hchar : CharTwo (L ⊔ T) := by
    subst hS₂
    exact charTwo_of_inH hq.qtke.2.1 S₂ hH
  have hcomp : L ∈ cComp (L ⊔ T) := hloc.2.1
  have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hcomp
  have hsub : IsSubnormal L (L ⊔ T) := subnormal_of_mem_cComp hcomp
  have hV2 := quasithinV2_ne_bot_of_commutator_ne_bot hchar le_sup_left hsub hperf
    (hZT.trans le_sup_right) hZe hQZ hQL hne
  refine hq.faithful_empty L ⟨hloc, ?_, ?_, hV2⟩
  · exact (eq_oTwoUpper_iff_forall_normal L).mp (eq_oTwoUpper_of_perfect hperf)
  · exact (quasithinGenFitting_eq_pCoreOf_iff L 2).mpr (A4.charTwo_of_subnormal hsub hchar)

theorem eq_bot_of_perfect_of_le_pGroup {X L : Subgroup G} (hX : IsPGroup 2 X) (hLX : L ≤ X)
    (hperf : ⁅L, L⁆ = L) : L = ⊥ := by
  have h := eq_oTwoUpper_of_perfect hperf
  rw [h, oTwoUpper, eq_bot_iff, Subgroup.closure_le]
  rintro x ⟨hxL, hodd⟩
  obtain ⟨k, hk⟩ := hX ⟨x, hLX hxL⟩
  have h1 : x ^ 2 ^ k = 1 := by simpa using congrArg Subtype.val hk
  have h2 : orderOf x ∣ 2 ^ k := orderOf_dvd_of_pow_eq_one h1
  obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).mp h2
  have h3 : orderOf x = 1 := by
    cases j with
    | zero => simpa using hj
    | succ j =>
      exfalso
      have := Nat.odd_iff.mp hodd
      rw [hj, Nat.pow_succ, Nat.mul_mod_left] at this
      omega
  exact Subgroup.mem_bot.mpr (orderOf_eq_one_iff.mp h3)

theorem mem_normalizer_of_case_iii {Mc K L : Subgroup G} {t q : G} (hL : L ∈ cComp Mc)
    (htMc : t ∈ Mc) (hKc : K = L ⊔ conjSub t L) (hKn : Mc ≤ Subgroup.normalizer (K : Set G))
    (hcomm : ⁅L, conjSub t L⁆ ≤ pCoreOf 2 Mc) (hqMc : q ∈ Mc)
    (hqL : ∀ l ∈ L, q * l * q⁻¹ * l⁻¹ ∈ pCoreOf 2 Mc) :
    q ∈ Subgroup.normalizer (L : Set G) := by
  have hLt : conjSub t L ∈ cComp Mc :=
    H13.LocDbl.map_conj_mem_cComp hL (Subgroup.le_normalizer htMc)
  have hLq : conjSub q L ∈ cComp Mc :=
    H13.LocDbl.map_conj_mem_cComp hL (Subgroup.le_normalizer hqMc)
  have hKq : conjSub q K = K := A38.map_conj_eq_iff.mpr (hKn hqMc)
  have hLK : L ≤ K := hKc ▸ le_sup_left
  have hle : conjSub q L ≤ L ⊔ conjSub t L :=
    calc conjSub q L ≤ conjSub q K := Subgroup.map_mono hLK
      _ = K := hKq
      _ = L ⊔ conjSub t L := hKc
  rcases cComp_eq_of_le_sup hLq hL hLt hle with h | h
  · exact A38.map_conj_eq_iff.mp h
  · exfalso
    have hLMc : L ≤ Mc := le_of_mem_cComp hL
    have hPn : ∀ g ∈ Mc, ∀ x ∈ pCoreOf 2 Mc, g * x * g⁻¹ ∈ pCoreOf 2 Mc := fun g hg x hx =>
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 Mc hg) x).mp hx
    have hLLP : ⁅L, L⁆ ≤ pCoreOf 2 Mc := by
      rw [Subgroup.commutator_le]
      intro l hl m hm
      have hmem : q * m * q⁻¹ ∈ conjSub t L := by
        rw [← h, mem_conjSub]
        have e : q⁻¹ * (q * m * q⁻¹) * q = m := by group
        rw [e]
        exact hm
      have h1 : ⁅l, q * m * q⁻¹⁆ ∈ pCoreOf 2 Mc :=
        hcomm (Subgroup.commutator_mem_commutator hl hmem)
      have hc : q * m * q⁻¹ * m⁻¹ ∈ pCoreOf 2 Mc := hqL m hm
      have e : ⁅l, m⁆ = (l * (q * m * q⁻¹ * m⁻¹)⁻¹ * l⁻¹) * ⁅l, q * m * q⁻¹⁆ *
          (q * m * q⁻¹ * m⁻¹) := by simp only [commutatorElement_def]; group
      rw [e]
      exact (pCoreOf 2 Mc).mul_mem ((pCoreOf 2 Mc).mul_mem
        (hPn l (hLMc hl) _ ((pCoreOf 2 Mc).inv_mem hc)) h1) hc
    have hperf : ⁅L, L⁆ = L := perfect_of_mem_cComp hL
    exact ne_bot_of_mem_cComp hL (eq_bot_of_perfect_of_le_pGroup (pCoreOf_isPGroup 2 Mc)
      (hperf ▸ hLLP) hperf)

end S15223

end CFSG.Quasithin

module

public import CFSG.Quasithin.Background.ONanE68Sp4Cube
public import CFSG.Quasithin.Background.ONanE68Sp4Roots
public import CFSG.Quasithin.Background.ONanE68Sp4Solv
public import CFSG.Quasithin.Background.ONanE68Sp4Map

public section

namespace CFSG.Quasithin

namespace E6

namespace E68Proof

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.UnbalancedCatalog.SpChain CFSG.QuasithinUnique.Setup.X7b
  CFSG.Quasithin.SteinbergBS

namespace Sp4

variable {K : Type} [Field K] [CharP K 2] [Finite K]

theorem e68Sp4Data_antiUnipotent {n : ℕ} (hK : Nat.card K = 2 ^ n) (hn : 2 ≤ n) :
    E68Sp4Data (antiUnipotent K) n where
  quot_comm a ha b hb := quot_comm ha hb
  order_three c hc h3 := four_lt_relIndex hK hn hc h3
  card_root := by rw [card_omegaCenter, hK, ← pow_add, ← two_mul]
  split := by
    obtain ⟨xs, hxs, hxs1, hxs2⟩ := exists_singer_short (K := K)
    obtain ⟨xl, hxl, hxl1, hxl2⟩ := exists_singer_long (K := K)
    refine ⟨rootShort K, rootLong K, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ⟨xs, hxs, hxs1, hxs2⟩,
      ⟨xl, hxl, hxl1, hxl2⟩, fun y hy => exists_torus_conj_short hy,
      fun y hy => exists_torus_conj_long hy, not_centralizer_short_le, not_centralizer_long_le⟩
    · rw [omegaCenter_eq]
      exact rootShort_le_center
    · rw [omegaCenter_eq]
      exact rootLong_le_center
    · rw [inf_comm]
      exact rootLong_inf_rootShort
    · rw [omegaCenter_eq, sup_comm]
      exact rootLong_sup_rootShort
    · rw [card_rootShort, hK]
    · rw [card_rootLong, hK]
    · exact fun b hb z hz => conj_mem_rootShort (mem_normalizer_iff_upper.2
        (upper_of_mem_normalizer hb)) hz
    · exact fun b hb z hz => conj_mem_rootLong (mem_normalizer_iff_upper.2
        (upper_of_mem_normalizer hb)) hz
  centralizer_root := centralizer_omegaCenter_le
  not_solvable Y hlt hY := not_solvable_overgroup hK hn hlt hY

end Sp4

theorem isPGroup_and_not_dvd_index {X : Type} [Group X] {T : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) : IsPGroup 2 T ∧ ¬ 2 ∣ T.index := by
  obtain ⟨-, hT2, hidx⟩ := hT
  exact ⟨hT2, by
    rwa [show (T.subgroupOf ⊤).index = T.index from Subgroup.relIndex_top_right T] at hidx⟩

theorem exists_equiv_map_eq_sylow {L G : Type} [Group L] [Finite L] [Group G] {p : ℕ}
    [Fact p.Prime] (e : L ≃* G) (U : Sylow p L) (P : Sylow p G) :
    ∃ e' : L ≃* G, (U : Subgroup L).map e'.toMonoidHom = P := by
  have : Finite G := Finite.of_equiv L e.toEquiv
  set U' := U.mapSurjective (f := (e : L →* G)) e.surjective with hU'
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G U' P
  refine ⟨e.trans (MulAut.conj g), ?_⟩
  have h2 : ((g • U' : Sylow p G) : Subgroup G) =
      (U' : Subgroup G).map (MulAut.conj g).toMonoidHom := by
    rw [Sylow.smul_def, Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    rfl
  rw [hg, hU', Sylow.coe_mapSurjective, Subgroup.map_map] at h2
  exact h2.symm

theorem e68Sp4Data_holds : ∀ (S : Type) [Group S] [Finite S] (n : ℕ), 2 ≤ n →
    CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSp 2 2 n →
      ∀ P : Subgroup S, IsSylowTwoOf P ⊤ → E68Sp4Data P n := by
  intro S _ _ n hn hS P hP
  obtain ⟨-, K, _, _, hK, ⟨e⟩⟩ := hS
  have hchar : CharP K 2 :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two
      (by omega) hK
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hU2, hUidx⟩ := isPGroup_and_not_dvd_index
    (card_and_isSylowTwoOf_antiUnipotent (K := K)).2
  obtain ⟨hP2, hPidx⟩ := isPGroup_and_not_dvd_index hP
  obtain ⟨e', he'⟩ := exists_equiv_map_eq_sylow ((antiProjEquiv K).trans e.symm)
    (hU2.toSylow hUidx) (hP2.toSylow hPidx)
  have hmap : (antiUnipotent K).map e'.toMonoidHom = P := he'
  rw [← hmap]
  exact (Sp4.e68Sp4Data_antiUnipotent hK hn).map e'

end E68Proof

end E6

end CFSG.Quasithin

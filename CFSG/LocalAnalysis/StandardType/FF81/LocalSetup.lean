module

public import CFSG.LocalAnalysis.StandardType.FF81.Defs
import CFSG.LocalAnalysis.StandardType.FF81.LocalSetupCen
import CFSG.LocalAnalysis.StandardType.GGFFLocalFus
import CFSG.LocalAnalysis.StandardType.GGFFLocalNotNor
import CFSG.LocalAnalysis.StandardType.GGFFLocalSyl

@[expose] public section

namespace CFSG.StandardType.FF81

open CFSG.RankThree.PartTwo.Sec21.FF79 (Cen CenS Nor conjBy)

theorem HypA.settingCore {G : Type} [Group G] [Finite G] {n : ℕ} {b : G} {L : Subgroup G}
    (hA : HypA G n b L) {z : Fin 3 → ↥L} (hz : GGFF.Model ↥L z) : GGFF.SettingCore b L z := by
  have hcyc : ∀ P : Subgroup G, P ≤ CenS L → IsPGroup 3 P → IsCyclic P := by
    intro P hPC hP
    have hsub : IsPGroup 3 (P.subgroupOf (CenS L)) :=
      hP.of_equiv (Subgroup.subgroupOfEquivOfLe hPC).symm
    obtain ⟨Q, hPQ⟩ := hsub.exists_le_sylow
    have hQc : IsCyclic ↥(Q : Subgroup ↥(CenS L)) := hA.cyc Q
    have hcycSub : IsCyclic (P.subgroupOf (CenS L)) := Subgroup.isCyclic_of_le hPQ
    exact (MulEquiv.isCyclic (Subgroup.subgroupOfEquivOfLe hPC)).mp hcycSub
  exact
    { ord := hA.ord
      le := hA.le
      nor := fun c hc k hk => (Subgroup.mem_normalizer_iff.mp (hA.nor hc) k).mp hk
      model := hz
      cyc := hcyc }

theorem localSetup_holds : LocalSetup := by
  intro G _ _ _ _ _ n b L hA z hz
  have hS := hA.settingCore hz
  have hN := hS.not_nor_le hA.notWC
  have hcen := cen_of_model hA.n_cases hA.model hz
  refine ⟨?_, hN, ?_, ?_, ?_⟩
  · intro P hPL hPb hP hbP
    exact hS.syl hcen hN hPL hPb hP hbP
  · intro g hg
    exact hS.fusion hg rfl
  · intro g hg
    exact hS.fusC hg
  · intro n hn hb i
    have hnb : conjBy n (Subgroup.zpowers b) = Subgroup.zpowers b := by
      refine Subgroup.eq_of_le_of_card_ge ?_ ?_
      · rw [conjBy, MonoidHom.map_zpowers]
        exact Subgroup.zpowers_le.2 (by simpa [MulAut.conj_apply] using hb)
      · rw [conjBy, Subgroup.card_map_of_injective (MulAut.conj n).injective]
    have hsq : ∀ j : Fin 3, (GGFF.zs z j)⁻¹ = GGFF.zs z j ^ 2 := fun j => (hS.zs_sq j).symm
    have hmem : n * GGFF.zs z i * n⁻¹ ∈
        ({GGFF.zs z 0, (GGFF.zs z 0)⁻¹, GGFF.zs z 1, (GGFF.zs z 1)⁻¹,
          GGFF.zs z 2, (GGFF.zs z 2)⁻¹} : Set G) :=
      (hS.stab n hn hnb).2 (GGFF.zs z i) (by fin_cases i <;> simp)
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hmem
    rcases hmem with h | h | h | h | h | h
    · exact ⟨0, 1, Or.inl rfl, by rw [h, pow_one]⟩
    · exact ⟨0, 2, Or.inr rfl, by rw [h, hsq 0]⟩
    · exact ⟨1, 1, Or.inl rfl, by rw [h, pow_one]⟩
    · exact ⟨1, 2, Or.inr rfl, by rw [h, hsq 1]⟩
    · exact ⟨2, 1, Or.inl rfl, by rw [h, pow_one]⟩
    · exact ⟨2, 2, Or.inr rfl, by rw [h, hsq 2]⟩

end CFSG.StandardType.FF81

end

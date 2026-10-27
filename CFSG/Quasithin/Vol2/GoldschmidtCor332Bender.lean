module

public import CFSG.StronglyEmbedded.BenderUnitaryBorel
public import CFSG.Quasithin.Vol2.GoldschmidtCor332Gen
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderLinearBorel
import CFSG.Adapters.QiuzhenLegacy.BenderSuzuki.BenderSuzukiBorel

public section

namespace CFSG.Quasithin.H13.Cor332

open CFSG.Open CFSG.LieType.BorelTits
open scoped MatrixGroups

variable {G : Type*} [Group G] [Finite G]

theorem normalizer_le_of_stronglyEmbedded {T : Sylow 2 G}
    (hSE : fusionStronglyEmbedded (Subgroup.normalizer ((T : Subgroup G) : Set G)))
    {U : Subgroup G} (hU : U ≠ ⊥) (hUT : U ≤ (T : Subgroup G)) :
    Subgroup.normalizer (U : Set G) ≤ Subgroup.normalizer ((T : Subgroup G) : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro g hg
  by_contra hgB
  obtain ⟨-, -, hodd⟩ := hSE
  have hgodd := hodd g hgB
  set B := Subgroup.normalizer ((T : Subgroup G) : Set G) with hB
  have hTB : (T : Subgroup G) ≤ B := Subgroup.le_normalizer
  have hUle : U ≤ B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom := by
    intro u hu
    refine ⟨hTB (hUT hu), Subgroup.mem_map.mpr ⟨g * u * g⁻¹, ?_, ?_⟩⟩
    · exact hTB (hUT ((Subgroup.mem_normalizer_iff.mp hg u).mp hu))
    · simp [mul_assoc]
  have hne : Nontrivial U := (Subgroup.nontrivial_iff_ne_bot U).mpr hU
  have hU2 : IsPGroup 2 U := T.isPGroup'.to_le hUT
  obtain ⟨n, hn, hcard⟩ := hU2.nontrivial_iff_card.mp hne
  have hdvd : 2 ∣ Nat.card (B ⊓ B.map (MulAut.conj g⁻¹).toMonoidHom : Subgroup G) :=
    (dvd_pow_self 2 hn.ne').trans (hcard ▸ Subgroup.card_dvd_of_le hUle)
  exact (Nat.not_even_iff_odd.mpr hgodd) (even_iff_two_dvd.mpr hdvd)

theorem isSolvable_normalizer_of_cyclic {T D : Subgroup G} (hT : IsPGroup 2 T) (hD : IsCyclic D)
    (hTD : T ⊔ D = Subgroup.normalizer (T : Set G)) :
    Group.IsSolvable (Subgroup.normalizer (T : Set G)) := by
  set B := Subgroup.normalizer (T : Set G) with hB
  have hTB : T ≤ B := Subgroup.le_normalizer
  have hDB : D ≤ B := hTD ▸ le_sup_right
  set T' := T.subgroupOf B
  set D' := D.subgroupOf B
  have hT'n : T'.Normal := Subgroup.normal_in_normalizer
  have hT'p : IsPGroup 2 T' := hT.of_equiv (Subgroup.subgroupOfEquivOfLe hTB).symm
  have : Group.IsNilpotent T' := hT'p.isNilpotent
  have : Group.IsSolvable T' := inferInstance
  have hD'c : IsCyclic D' :=
    isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe hDB).symm.toMonoidHom
      (Subgroup.subgroupOfEquivOfLe hDB).symm.surjective
  have htop : T' ⊔ D' = ⊤ := by
    rw [← Subgroup.subgroupOf_sup hTB hDB, hTD, Subgroup.subgroupOf_self]
  have hmap : D'.map (QuotientGroup.mk' T') = ⊤ := by
    have h1 : (T' ⊔ D').map (QuotientGroup.mk' T') = ⊤ := by
      rw [htop, Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective T')]
    rwa [Subgroup.map_sup, (Subgroup.map_eq_bot_iff T').2 (QuotientGroup.ker_mk' T').ge,
      bot_sup_eq] at h1
  have hsurj : Function.Surjective ((QuotientGroup.mk' T').comp D'.subtype) := by
    intro y
    obtain ⟨d, hd, rfl⟩ := Subgroup.mem_map.1 (hmap ▸ Subgroup.mem_top y)
    exact ⟨⟨d, hd⟩, rfl⟩
  have : IsCyclic (↥B ⧸ T') := isCyclic_of_surjective _ hsurj
  exact Group.isSolvable_of_subgroup_quotient T'


theorem twoLocalsSolvable_of_fusionBenderBorel {q k : ℕ} (hB : fusionBenderBorel G q k) :
    TwoLocalsSolvable G := by
  intro Q H hQ hQ2 hHQ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨T, hQT⟩ := hQ2.exists_le_sylow
  obtain ⟨hSE, ⟨D, hDc, -, -, hTD⟩, -⟩ := hB T
  have hNB := normalizer_le_of_stronglyEmbedded hSE hQ hQT
  have hsolv := isSolvable_normalizer_of_cyclic T.isPGroup' hDc hTD
  exact Group.isSolvable_of_isSolvable_injective
    (Subgroup.inclusion_injective (hHQ.trans hNB))

theorem twoLocalsSolvable_of_fusionIsBenderGroup (hX : fusionIsBenderGroup G) :
    TwoLocalsSolvable G := by
  obtain ⟨q, k, hBB⟩ : ∃ q k : ℕ, fusionBenderBorel G q k := by
    rcases hX with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
    · have : Finite PSL(2, GaloisField 2 f) := Finite.of_equiv G e.toEquiv
      exact ⟨2 ^ f, 1, (bender_psl2_borel_full f hf).map_mulEquiv e.symm⟩
    · have : Finite (PSU3 2 f) := Finite.of_equiv G e.toEquiv
      exact ⟨2 ^ f, 3, (bender_psu3_borel_full f hf).map_mulEquiv e.symm⟩
    · have : Finite (Sz a) := Finite.of_equiv G e.toEquiv
      exact ⟨2 ^ (2 * a + 1), 2, (bender_suzuki_borel_full a ha).map_mulEquiv e.symm⟩
  exact twoLocalsSolvable_of_fusionBenderBorel hBB

end CFSG.Quasithin.H13.Cor332

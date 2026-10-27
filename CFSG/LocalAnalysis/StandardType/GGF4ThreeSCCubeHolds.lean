module

public import CFSG.LocalAnalysis.StandardType.GGF4ThreeSCCubeCore
public import CFSG.LocalAnalysis.StandardType.GGF4ThreeNbrInputs
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross.ExcLangNF4Two

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.ExcCross

@[expose] def GGF4ThreeSylowNormalInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2],
    3 ∣ Nat.card K + 1 →
    ∃ P : Sylow 3 ↥(adjointGroup .F4 K),
      ∃ T : Subgroup ↥(adjointGroup .F4 K),
        T ≤ (P : Subgroup _) ∧ IsElemAbelian 3 T ∧
        Nat.card T = 3 ^ 4 ∧
        (P : Subgroup _) ≤ Subgroup.normalizer (T : Set ↥(adjointGroup .F4 K))

theorem ggF4ThreeSylowNormalInput_holds :
    GGF4ThreeSylowNormalInput := by
  intro K _ _ _ hq
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let L := AlgebraicClosure K
  have : IsAlgClosure K L := inferInstance
  obtain ⟨Fr, hFr⟩ := CFSG.RankThree.Chevalley.exists_ringHom_pow_card K L
  obtain ⟨w0, hw0⟩ := exists_weyl_neg_F4
  let n := canonicalRep (coxeterSystem Tag.F4) L w0
  let Φ : ModGL Tag.F4 L →* ModGL Tag.F4 L := Units.map (entrywiseHom Fr)
  let N := NFix n Fr
  have : Finite N := finite_NFix_F4 Fr hFr hw0
  let V := V3 n Φ
  have hV_le_N : V ≤ N :=
    (V3_le (n := n) (Φ := Φ)).trans (twistedTorusOf_le_NFix n Fr)
  have hV_comm : IsMulCommutative V :=
    ⟨⟨fun a b => Subtype.ext
      (mul_comm_of_mem_V3 (isMulCommutative_twistedTorusOf Fr w0 hw0) a.2 b.2)⟩⟩
  have hV_el : IsElemAbelian 3 V :=
    ⟨hV_comm, fun x hx => pow_three_eq_one_of_mem_V3 hx⟩
  let A : Subgroup N := V.subgroupOf N
  have hA_el : IsElemAbelian 3 A := hV_el.subgroupOf N
  have hV_card : Nat.card V = 3 ^ 4 := by
    have h : Nat.card V = 3 ^ Tag.F4.rank := by
      simpa [V, n, Φ] using
        card_V3_negOne (τ := Tag.F4) (K := K) (L := L) Fr w0 hw0 hFr hq
    rwa [show (3 : ℕ) ^ Tag.F4.rank = 3 ^ 4 from rfl] at h
  have hA_card : Nat.card A = 3 ^ 4 := by
    rw [show Nat.card A = Nat.card V from
      Nat.card_congr (Subgroup.subgroupOfEquivOfLe hV_le_N).toEquiv, hV_card]
  have hA_normal : A.Normal := by
    refine Subgroup.Normal.mk fun a ha g => ?_
    rw [Subgroup.mem_subgroupOf] at ha ⊢
    rw [mem_V3 (isMulCommutative_twistedTorusOf Fr w0 hw0)]
    refine ⟨?_, ?_⟩
    · have h := NFix_conj_mem_twistedTorusOf (n := n) (Fr := Fr) g.2
        (V3_le (n := n) (Φ := Φ) ha)
      simpa using h
    · have h3 : ((g : ModGL Tag.F4 L) * (a : ModGL Tag.F4 L) *
          (g : ModGL Tag.F4 L)⁻¹) ^ 3 = 1 := by
        rw [conj_pow, pow_three_eq_one_of_mem_V3 ha, mul_one, mul_inv_cancel]
      simpa using h3
  have : A.Normal := hA_normal
  obtain ⟨ι, hι_inj, P0, hP0p, hP0card⟩ := exists_F4_two_sylow Fr hFr hq hw0
  let : Finite ↥(adjointGroup Tag.F4 K) := generated_group_finite Tag.F4 K
  obtain ⟨S_N, hP0_SN⟩ := hP0p.exists_le_sylow
  have hA_SN : A ≤ (S_N : Subgroup N) := IsPGroup.le_sylow_of_normal hA_el.isPGroup S_N
  have hcard_map : Nat.card (P0.map ι) =
      3 ^ (Nat.card ↥(adjointGroup Tag.F4 K)).factorization 3 := by
    rw [Subgroup.card_map_of_injective hι_inj, hP0card]
  let S_R : Sylow 3 ↥(adjointGroup Tag.F4 K) := Sylow.ofCard (P0.map ι) hcard_map
  have hS_R_coe : (S_R : Subgroup ↥(adjointGroup Tag.F4 K)) = P0.map ι :=
    Sylow.coe_ofCard (P0.map ι) hcard_map
  have hmap_le : (S_R : Subgroup _) ≤ (S_N : Subgroup N).map ι := by
    rw [hS_R_coe]
    exact Subgroup.map_mono hP0_SN
  have hmap_p : IsPGroup 3 ((S_N : Subgroup N).map ι) := S_N.isPGroup'.map ι
  have hmap_eq : (S_N : Subgroup N).map ι = (S_R : Subgroup _) :=
    S_R.is_maximal' hmap_p hmap_le
  have hSN_le_N : (S_N : Subgroup N) ≤ Subgroup.normalizer (A : Set N) := by
    have : Subgroup.normalizer (A : Set N) = ⊤ := Subgroup.normalizer_eq_top A
    rw [this]
    exact le_top
  have hS_R_le_NT : (S_R : Subgroup _) ≤
      Subgroup.normalizer (A.map ι : Set ↥(adjointGroup Tag.F4 K)) := by
    rw [← hmap_eq, Subgroup.le_normalizer_iff]
    rintro _ ⟨g, hgS, rfl⟩ _ ⟨a, ha, rfl⟩
    exact Subgroup.mem_map.mpr ⟨g * a * g⁻¹,
      Subgroup.le_normalizer_iff.mp hSN_le_N g hgS a ha, by simp [map_mul]⟩
  refine ⟨S_R, A.map ι, ?_, ?_, ?_, ?_⟩
  · exact hmap_eq ▸ Subgroup.map_mono hA_SN
  · exact hA_el.map ι
  · rw [Subgroup.card_map_of_injective hι_inj, hA_card]
  · exact hS_R_le_NT

theorem ggF4ThreeSCCubeInput_of_sylow
    (h : GGF4ThreeSylowNormalInput) : GGF4ThreeSCCubeInput := by
  intro K _ _ _ hq E hE hcard hSC
  let : Finite ↥(adjointGroup Tag.F4 K) := generated_group_finite Tag.F4 K
  unfold GGF4ThreeSylowNormalInput at h
  obtain ⟨P, T, -, hT, hTcard, hPT⟩ := h K hq
  exact exists_transvection_of_SC_cube_sylow Nat.prime_three hT
    (le_of_eq hTcard.symm) hPT hE hcard hSC

theorem ggF4ThreeSCCubeInput_holds :
    GGF4ThreeSCCubeInput :=
  ggF4ThreeSCCubeInput_of_sylow ggF4ThreeSylowNormalInput_holds

end CFSG.StandardType

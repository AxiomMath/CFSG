module

public import CFSG.Quasithin.Vol2.Ch11SecOE7A
public import CFSG.Quasithin.Vol2.Ch11SecE3LieTau
public import CFSG.Quasithin.Background.E3ClosedTwo
public import CFSG.GroupTheory.ABGLocalTools.Constraint

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

open CFSG.Open CFSG.Quasithin

namespace Sp4

variable {G : Type} [Group G]

theorem conjSub_top_eq (g : G) : A1b.conjSub g (⊤ : Subgroup G) = ⊤ :=
  Subgroup.map_top_of_surjective _ (MulAut.conj g).surjective

theorem le_conjSub_inv {g : G} {A T : Subgroup G} (h : A1b.conjSub g A ≤ T) :
    A ≤ A1b.conjSub g⁻¹ T := by
  have h1 := A1b.conjSub_mono g⁻¹ h
  rwa [← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one] at h1

theorem le_normalizer_map_subtype {K : Subgroup G} {N : Subgroup ↥K} (hN : N.Normal) :
    K ≤ Subgroup.normalizer ((N.map K.subtype : Subgroup G) : Set G) := by
  have h : (N.map K.subtype).subgroupOf K = N :=
    Subgroup.comap_map_eq_self_of_injective K.subtype_injective N
  refine (Subgroup.normal_subgroupOf_iff_le_normalizer (Subgroup.map_subtype_le N)).mp ?_
  rw [h]
  exact hN

theorem le_normalizer_inf {K L : Subgroup G} [L.Normal] :
    K ≤ Subgroup.normalizer ((K ⊓ L : Subgroup G) : Set G) :=
  (le_inf Subgroup.le_normalizer (by
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact le_top)).trans Subgroup.inf_normalizer_le_normalizer_inf

variable [Finite G]

theorem subgroupOf_le_pCore {K L N : Subgroup G} [L.Normal] (hNR : N ≤ K ⊓ L)
    (hNn : (N.subgroupOf (K ⊓ L)).Normal) (hN2 : IsPGroup 2 N) :
    N.subgroupOf K ≤ CFSG.Open.pCore 2 ↥K := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hNP : N ≤ pCoreOf 2 (K ⊓ L) := CFSG.LieType.BorelTits.le_pCoreOf 2 hNR hNn hN2
  have hPK : pCoreOf 2 (K ⊓ L) ≤ K := (CFSG.LieType.BorelTits.pCoreOf_le 2 _).trans inf_le_left
  have hKP : K ≤ Subgroup.normalizer ((pCoreOf 2 (K ⊓ L) : Subgroup G) : Set G) :=
    le_normalizer_inf.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 _)
  have hPn : ((pCoreOf 2 (K ⊓ L)).subgroupOf K).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPK).mpr hKP
  have hP2 : IsPGroup 2 ↥((pCoreOf 2 (K ⊓ L)).subgroupOf K) :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).of_equiv
      (Subgroup.subgroupOfEquivOfLe hPK).symm
  exact (Subgroup.subgroupOf_mono K hNP).trans (CFSG.LieType.BorelTits.le_pCore 2 hPn hP2)

omit [Finite G] in
theorem card_barRad_eq {K L A : Subgroup G} [L.Normal] (hAK : A ≤ K) (hAL : A ≤ L)
    (h : A ⊓ ((CFSG.solvableRadical ↥K).map K.subtype ⊓ L) = ⊥) :
    Nat.card (E1.barRad ↥K (A.subgroupOf K)) = Nat.card A := by
  have hinf : CFSG.solvableRadical ↥K ⊓ A.subgroupOf K = ⊥ := by
    refine eq_bot_iff.mpr fun x hx => ?_
    have hx' : (x : G) ∈ A ⊓ ((CFSG.solvableRadical ↥K).map K.subtype ⊓ L) :=
      ⟨hx.2, ⟨x, hx.1, rfl⟩, hAL hx.2⟩
    rw [h, Subgroup.mem_bot] at hx'
    exact Subgroup.mem_bot.mpr (Subtype.ext hx')
  rw [E3.card_barRad_eq_relIndex, ← Subgroup.inf_relIndex_right, hinf,
    Subgroup.relIndex_bot_left, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hAK).toEquiv]

theorem solvableRadical_inf_normal {K L : Subgroup G} [L.Normal] :
    (((CFSG.solvableRadical ↥K).map K.subtype ⊓ L).subgroupOf (K ⊓ L)).Normal ∧
      Group.IsSolvable ↥((CFSG.solvableRadical ↥K).map K.subtype ⊓ L) := by
  have hle : (CFSG.solvableRadical ↥K).map K.subtype ⊓ L ≤ K ⊓ L :=
    inf_le_inf_right L (Subgroup.map_subtype_le _)
  refine ⟨(Subgroup.normal_subgroupOf_iff_le_normalizer hle).mpr ?_, ?_⟩
  · refine (le_inf ?_ ?_).trans Subgroup.inf_normalizer_le_normalizer_inf
    · exact inf_le_left.trans (le_normalizer_map_subtype inferInstance)
    · rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
      exact le_top
  · have : Group.IsSolvable ↥(CFSG.solvableRadical ↥K) :=
      CFSG.ABGLocalTools.solvableRadical_isSolvable
    have : Group.IsSolvable ↥((CFSG.solvableRadical ↥K).map K.subtype) :=
      Group.isSolvable_of_surjective (K.subtype.subgroupMap_surjective _)
    exact Group.isSolvable_of_isSolvable_injective (Subgroup.inclusion_injective inf_le_left)

end Sp4

variable {G : Type} [Group G] [Finite G]

open Sp4 in
theorem le_nParam_of_overgroups {n : ℕ} {T L A : Subgroup G} [L.Normal] (hn : 2 ≤ n)
    (hT : IsSylowIn 2 T ⊤) (hO2 : ∀ N : Subgroup G, N.Normal → IsPGroup 2 N → N = ⊥)
    (hAT : A ≤ T) (hAL : A ≤ L) (hA : IsElemAbelian 2 A) (hA1 : A ≠ ⊥)
    (hcard : 2 ^ n ≤ Nat.card A)
    (hR : ∀ R : Subgroup G, R ≤ L → A ≤ R →
      (∃ N : Subgroup G, N ≤ R ∧ (N.subgroupOf R).Normal ∧ IsPGroup 2 N ∧ A ≤ N) ∨
      (¬ Group.IsSolvable ↥R ∧ ∀ N : Subgroup G, N ≤ R → (N.subgroupOf R).Normal →
        Group.IsSolvable ↥N → A ⊓ N = ⊥)) :
    (n : ℕ∞) ≤ E1.nParam (⊤ : Subgroup G) := by
  refine le_nParam_of_forall_not_isE hn hT hO2 hAT hA hA1 fun g hgT K hK => ?_
  have hK' : E1.IsE (n - 1) ⊤ (A1b.conjSub g⁻¹ T) A (A1b.conjSub g⁻¹ K) := by
    have h := (E1.isE_conj g⁻¹).mpr hK
    rwa [conjSub_top_eq, ← A1b.conjSub_mul, inv_mul_cancel, A1b.conjSub_one] at h
  set K' := A1b.conjSub g⁻¹ K with hK'def
  have hAT' : A ≤ A1b.conjSub g⁻¹ T := le_conjSub_inv hgT
  obtain ⟨-, hτ, -, hrank⟩ := hK'
  have hAK : A ≤ K' :=
    (SecE3.le_tauOf_self le_top hAT' hA).trans (hτ.trans inf_le_right)
  rcases hR (K' ⊓ L) inf_le_right (le_inf hAK hAL) with ⟨N, hNR, hNn, hN2, hAN⟩ | ⟨hns, hsol⟩
  ·
    have hAO : A.subgroupOf K' ≤ CFSG.Open.pCore 2 ↥K' :=
      (Subgroup.subgroupOf_mono K' hAN).trans (subgroupOf_le_pCore hNR hNn hN2)
    have hbar2 : E1.barO2 ↥K' (A.subgroupOf K') = ⊥ := by
      rw [E1.barO2, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hAO
    have hbarR : E1.barRad ↥K' (A.subgroupOf K') = ⊥ := by
      rw [E1.barRad, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
      exact hAO.trans E3.pCore_two_le_solvableRadical
    rcases hrank with ⟨⟨p, -, -, -, -, -, h2⟩, -⟩ | ⟨hE2, -⟩
    · rw [hbar2, Subgroup.card_bot] at h2
      exact absurd h2 (by norm_num)
    · exact E1.RootLift.not_eTwo_of_barRad_eq_bot hbarR hE2
  · rcases hrank with ⟨hE1, -⟩ | ⟨-, hc⟩
    ·
      have := E1.RootLift.isSolvable_of_eOne hE1
      exact hns (Group.isSolvable_of_isSolvable_injective
        (Subgroup.inclusion_injective (inf_le_left : K' ⊓ L ≤ K')))
    ·
      obtain ⟨hn₀, hs₀⟩ := solvableRadical_inf_normal (K := K') (L := L)
      have h0 := hsol _ (inf_le_inf_right L (Subgroup.map_subtype_le _)) hn₀ hs₀
      have hcb := card_barRad_eq hAK hAL h0
      have hlt : 2 ^ (n - 1) < 2 ^ n := Nat.pow_lt_pow_right (by norm_num) (by omega)
      omega

end CFSG.Quasithin.Vol2.Ch11.SecE3.Lie3

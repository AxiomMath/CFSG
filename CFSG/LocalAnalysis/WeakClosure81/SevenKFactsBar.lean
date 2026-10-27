module

public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.GroupTheory.ElemAbelianClosure
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

variable {G : Type} [Group G] [Finite G]

theorem isElemAbelian_barSub {K A : Subgroup G} (hA : IsElemAbelian 2 A) {X : Type} [Group X]
    (φ : ↥K →* X) : IsElemAbelian 2 (barSub K φ A) := by
  exact CFSG.Open.IsElemAbelian.map (CFSG.Open.IsElemAbelian.comap hA K.subtype_injective) φ

theorem barSub_conjSubgroup {K : Subgroup G} {X : Type} [Group X] (φ : ↥K →* X)
    (A : Subgroup G) (k : ↥K) :
    barSub K φ (conjSubgroup A (k : G)) = conjSubgroup (barSub K φ A) (φ k) := by
  ext x
  rw [mem_conjSubgroup_iff, mem_barSub, mem_barSub]
  constructor
  · rintro ⟨y, hy, rfl⟩
    refine ⟨k * y * k⁻¹, ?_, ?_⟩
    · have hy' : (k : G) * (y : G) * (k : G)⁻¹ ∈ A := (mem_conjSubgroup_iff.mp hy)
      simpa only [Subgroup.coe_mul, Subgroup.coe_inv] using hy'
    · rw [map_mul, map_mul, map_inv]
  · rintro ⟨a, ha, haφ⟩
    refine ⟨k⁻¹ * a * k, ?_, ?_⟩
    · rw [mem_conjSubgroup_iff]
      have hco : (k : G) * ((k⁻¹ * a * k : ↥K) : G) * (k : G)⁻¹ = (a : G) := by
        rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]
        group
      rw [hco]
      exact ha
    · rw [map_mul, map_mul, map_inv, haφ]
      group

theorem barSub_sup {K A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ K) {X : Type} [Group X]
    (φ : ↥K →* X) : barSub K φ (A ⊔ B) = barSub K φ A ⊔ barSub K φ B := by
  change ((A ⊔ B).subgroupOf K).map φ =
    (A.subgroupOf K).map φ ⊔ (B.subgroupOf K).map φ
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

theorem card_barSub_eq_relIndex_of_isBarMap {K N A : Subgroup G} (hA : A ≤ K) (hN : N ≤ K)
    {X : Type} [Group X] {φ : ↥K →* X} (hφ : IsBarMap K N φ) :
    Nat.card (barSub K φ A) = N.relIndex A := by
  have hker : φ.ker = N.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφ.ker_iff k
  change Nat.card ((A.subgroupOf K).map φ) = N.relIndex A
  rw [← Subgroup.relIndex_ker (K := A.subgroupOf K) φ, hker]
  exact Subgroup.relIndex_subgroupOf (H := N) (K := A) (L := K) hA

theorem pCore_eq_bot_of_isBarMap {K : Subgroup G} {X : Type} [Group X] {φ : ↥K →* X}
    (hφ : IsBarMap K (pCoreOf 2 K) φ) : CFSG.pCore 2 X = ⊥ := by
  haveI : Fact (Nat.Prime 2) := Nat.fact_prime_two
  let J : Subgroup G := pCoreOf 2 K
  let P : Subgroup X := CFSG.pCore 2 X
  let Q : Subgroup ↥K := P.comap φ
  have hJK : J ≤ K := CFSG.LieType.BorelTits.pCoreOf_le 2 K
  have hJ2 : IsPGroup 2 J := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 K
  have hker : φ.ker = J.subgroupOf K := by
    ext k
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf]
    exact hφ.ker_iff k
  have hker2 : IsPGroup 2 φ.ker := by
    rw [hker]
    exact hJ2.of_equiv (Subgroup.subgroupOfEquivOfLe hJK).symm
  have hP2 : IsPGroup 2 P := CFSG.pCore_isPGroup (p := 2) (G := X)
  have hQ2 : IsPGroup 2 Q := IsPGroup.comap_of_ker_isPGroup hP2 φ hker2
  have hQnorm : Q.Normal := (inferInstance : P.Normal).comap φ
  have hQle : Q ≤ CFSG.pCore 2 ↥K := CFSG.LieType.BorelTits.le_pCore 2 hQnorm hQ2
  refine (Subgroup.eq_bot_iff_forall (CFSG.pCore 2 X)).mpr fun x hx => ?_
  obtain ⟨k, hk⟩ := hφ.surjective x
  have hkQ : k ∈ Q := by
    rw [Subgroup.mem_comap, hk]
    exact hx
  have hkcore : (k : G) ∈ J := by
    change (k : G) ∈ (CFSG.pCore 2 ↥K).map K.subtype
    exact Subgroup.mem_map_of_mem K.subtype (hQle hkQ)
  have h1 : φ k = 1 := (hφ.ker_iff k).mpr hkcore
  rw [← hk, h1]

theorem barSub_eq_top_iff {K N A : Subgroup G} (hA : A ≤ K) (hN : N ≤ K) {X : Type} [Group X]
    {φ : ↥K →* X} (hφ : IsBarMap K N φ) : barSub K φ A = ⊤ ↔ K = N ⊔ A := by
  constructor
  · intro htop
    refine le_antisymm ?_ (sup_le hN hA)
    intro k hk
    let k' : ↥K := ⟨k, hk⟩
    have hkA : φ k' ∈ barSub K φ A := by rw [htop]; exact Subgroup.mem_top _
    obtain ⟨a, ha, haφ⟩ := mem_barSub.mp hkA
    have hkerφ : φ (a⁻¹ * k') = 1 := by
      rw [map_mul, map_inv, haφ, inv_mul_cancel]
    have hNmem : ((a⁻¹ * k' : ↥K) : G) ∈ N := (hφ.ker_iff _).mp hkerφ
    rw [sup_comm]
    have heq : k = (a : G) * ((a⁻¹ * k' : ↥K) : G) := by
      rw [Subgroup.coe_mul, Subgroup.coe_inv, mul_inv_cancel_left]
    rw [heq]
    exact Subgroup.mul_mem_sup ha hNmem
  · intro hKA
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨k, rfl⟩ := hφ.surjective x
    have hAcomap : A.subgroupOf K ≤ (barSub K φ A).comap φ := by
      intro a ha
      rw [Subgroup.mem_comap]
      exact mem_barSub.mpr ⟨a, Subgroup.mem_subgroupOf.mp ha, rfl⟩
    have hNcomap : N.subgroupOf K ≤ (barSub K φ A).comap φ := by
      intro n hn
      rw [Subgroup.mem_comap]
      have hn1 : φ n = 1 := (hφ.ker_iff n).mpr (Subgroup.mem_subgroupOf.mp hn)
      rw [hn1]
      exact (barSub K φ A).one_mem
    have hsup : ((N ⊔ A).subgroupOf K) = A.subgroupOf K ⊔ N.subgroupOf K := by
      rw [sup_comm, Subgroup.subgroupOf_sup hA hN]
    have htop : ((N ⊔ A).subgroupOf K) = ⊤ := by
      rw [← hKA, Subgroup.subgroupOf_self]
    have hle : ((N ⊔ A).subgroupOf K) ≤ (barSub K φ A).comap φ := by
      rw [hsup]
      exact sup_le hAcomap hNcomap
    have hk : k ∈ (N ⊔ A).subgroupOf K := by
      rw [htop]
      exact Subgroup.mem_top _
    exact (Subgroup.mem_comap.mp (hle hk))

end CFSG.LocalAnalysis.WeakClosure81

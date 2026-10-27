module

public import CFSG.RankThree.PartTwo.Census.DoubleCoverLift
public import CFSG.RankThree.PartTwo.Sec4.Census.RankOmegaF4
public import Mathlib.GroupTheory.Perm.ViaEmbedding
public import CFSG.LocalAnalysis.SectionRank.Sporadic.LocalWitness
public import CFSG.LocalAnalysis.SectionRank.Sporadic.OpsF2
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Bridge.RuSurj
public import Certificates.Data.DoubleCoverRanks
public import Certificates.Certificate8093
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Suzuki.Torus
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.LieType.Multipliers.Sz8Field
import CFSG.Sporadic.Bridge.M22
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCover
public import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPerm
import CFSG.LocalAnalysis.ComponentInitial.GroupAlternatingCoverPresentation
import all CFSG.Blueprint.NativeSporadic
public import CFSG.Sporadic.Th.Max3.Quotient
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.GH74.GLS.Classes
public import CFSG.GH74.Statements
public import CFSG.GroupTheory.HallHigmanPiCore
public import CFSG.LieType.Chevalley.EvenRootCommutatorF4
public import CFSG.LieType.Multipliers.U42Bridge
public import CFSG.LieType.Multipliers.U62Action
public import CFSG.LieType.Multipliers.U62Bridge
public import CFSG.LieType.Multipliers.U62Kernel
public import CFSG.LocalAnalysis.ComponentClassification.BlockTwoProductAction
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHermitianIsometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.NormalizedProductSylow
public import CFSG.LocalAnalysis.ComponentClassification.StandardRecognitionQuaternion
public import CFSG.LocalAnalysis.ComponentClassification.TBLitCover
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionFixedInvolution
public import CFSG.LocalAnalysis.ComponentClassification.TwoActionInvariantSylow
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedGSBFixedLayer
public import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeCheckBase
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NativeModel
public import CFSG.LocalAnalysis.EvenSmallLie.Sp6JCondition
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.CentralInvolutionStructure
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.TypeB2
public import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Unitary
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.LocalAnalysis.SectionRank.Sporadic.TitsGen
public import CFSG.Monster.B.Classical.PlaneAut
public import CFSG.Monster.B.TwoA.Amalgam.Data
public import CFSG.Monster.B.TwoA.Sp8.Par1
public import CFSG.Monster.B.TwoA.Unitary.LinThree
public import CFSG.RankThree.PartTwo.Census.Spin.Main
public import CFSG.RankThree.PartTwo.Sec4.Census.Interface
public import CFSG.Sporadic.SmallOddCore.CheckSpec
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.YGroups.Y322Central
public import Certificates.Certificate10005
public import Certificates.Certificate10006
public import Certificates.Certificate10007
public import Certificates.Certificate10008
public import Certificates.Certificate10009
public import Certificates.Certificate10010
public import Certificates.Certificate10016
public import Certificates.Certificate10018
public import Certificates.Certificate10091Base
public import Certificates.Certificate12041
public import Certificates.Certificate12042
public import Certificates.Certificate12043
public import Certificates.Certificate12044
public import Certificates.Certificate12045
public import Certificates.Certificate12046
public import Certificates.Certificate16015
public import Certificates.Certificate16040
public import Certificates.Certificate2154
public import Certificates.Certificate2157
public import Certificates.Certificate2267
public import Certificates.Certificate2326
public import Certificates.Certificate3006
public import Certificates.Certificate3007
public import Certificates.Certificate3008
public import Certificates.Certificate3063
public import Certificates.Certificate3077
public import Certificates.Certificate3082
public import Certificates.Certificate3083
public import Certificates.Certificate8033
public import Certificates.Certificate8171
public import TauCeti.GroupTheory.SpecificGroups.CFSG.TypeC.Agreement

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Equiv
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverLift

namespace DoubleCoverRanks

theorem noRankThreeDoubleCover_of_datum {X : Type} [Group X] {a₁ a₂ a₃ n : X}
    (h : E8Datum a₁ a₂ a₃ n) : NoRankThreeDoubleCover X := by
  intro J _ _ _ hZ ⟨e⟩
  set φ : J →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ Subgroup.center J := fun x hx => by
    rw [MonoidHom.mem_ker] at hx
    have hx' : (QuotientGroup.mk' (Subgroup.center J)) x = 1 :=
      e.injective (by rw [map_one]; exact hx)
    exact (QuotientGroup.eq_one_iff x).mp hx'
  have : Nontrivial (Subgroup.center J) := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  obtain ⟨z, hz⟩ := exists_ne (1 : Subgroup.center J)
  have hz2 : (z : J) ^ 2 = 1 := by
    have := pow_card_eq_one' (G := Subgroup.center J) (x := z)
    rw [hZ] at this
    exact congrArg Subtype.val this
  have hzk : φ z = 1 := by
    change e (QuotientGroup.mk (z : J)) = 1
    rw [(QuotientGroup.eq_one_iff (z : J)).mpr z.2, map_one]
  have := h.four_le_pRank hφ hker hzk (fun e1 => hz (Subtype.ext e1)) hz2
  omega

theorem noRankThreeTwoCover_of_datum {X : Type} [Group X] {a₁ a₂ a₃ n : X}
    (h : E8Datum a₁ a₂ a₃ n) : NoRankThreeTwoCover X := by
  intro J _ _ ⟨_, hZ2, hZnt, ⟨e⟩⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set φ : J →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
  have hφ : Function.Surjective φ := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : φ.ker ≤ Subgroup.center J := fun x hx => by
    rw [MonoidHom.mem_ker] at hx
    have hx' : (QuotientGroup.mk' (Subgroup.center J)) x = 1 :=
      e.injective (by rw [map_one]; exact hx)
    exact (QuotientGroup.eq_one_iff x).mp hx'
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' 2 (two_dvd_card_center hZ2 hZnt)
  have hz2 : (z : J) ^ 2 = 1 := by
    rw [← Subgroup.orderOf_coe] at hz
    rw [← hz]
    exact pow_orderOf_eq_one _
  have hz1 : (z : J) ≠ 1 := by
    intro e1
    rw [← Subgroup.orderOf_coe, e1, orderOf_one] at hz
    exact absurd hz (by norm_num)
  have hzk : φ z = 1 := by
    change e (QuotientGroup.mk (z : J)) = 1
    rw [(QuotientGroup.eq_one_iff (z : J)).mpr z.2, map_one]
  have := h.four_le_pRank hφ hker hzk hz1 hz2
  omega

theorem noRankThreeDoubleCover_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : NoRankThreeDoubleCover X) : NoRankThreeDoubleCover Y :=
  fun J _ _ hq hZ ⟨f⟩ => h J hq hZ ⟨f.trans e.symm⟩

theorem noRankThreeTwoCover_of_mulEquiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : NoRankThreeTwoCover X) : NoRankThreeTwoCover Y :=
  fun J _ _ ⟨hq, hZ2, hZnt, ⟨f⟩⟩ => h J ⟨hq, hZ2, hZnt, ⟨f.trans e.symm⟩⟩

@[expose] def alt8A₁ : alternatingGroup (Fin 8) :=
  ⟨swap 0 1 * swap 2 3 * swap 4 5 * swap 6 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def alt8A₂ : alternatingGroup (Fin 8) :=
  ⟨swap 0 2 * swap 1 3 * swap 4 6 * swap 5 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def alt8A₃ : alternatingGroup (Fin 8) :=
  ⟨swap 0 4 * swap 1 5 * swap 2 6 * swap 3 7, Perm.mem_alternatingGroup.mpr (by decide)⟩

@[expose] def alt8N : alternatingGroup (Fin 8) :=
  ⟨List.formPerm [1, 2, 4, 3, 6, 7, 5], Perm.mem_alternatingGroup.mpr (by decide)⟩

theorem alt8_e8Datum : E8Datum alt8A₁ alt8A₂ alt8A₃ alt8N where
  ne_one := by decide
  sq := by decide
  comm₁₂ := (by decide : alt8A₁ * alt8A₂ = alt8A₂ * alt8A₁)
  comm₁₃ := (by decide : alt8A₁ * alt8A₃ = alt8A₃ * alt8A₁)
  conj₁ := by decide
  conj₂ := by decide
  conj₃ := by decide

noncomputable def altEmbed {n : ℕ} (hn : 8 ≤ n) :
    alternatingGroup (Fin 8) →* alternatingGroup (Fin n) :=
  ((Perm.viaEmbeddingHom (Fin.castLEEmb hn)).comp (alternatingGroup (Fin 8)).subtype).codRestrict
    _ fun σ => by
      rw [Perm.mem_alternatingGroup, MonoidHom.comp_apply, Perm.viaEmbeddingHom_apply,
        Perm.viaEmbedding, Perm.sign_extendDomain]
      exact σ.2

theorem altEmbed_injective {n : ℕ} (hn : 8 ≤ n) : Function.Injective (altEmbed hn) := by
  intro σ τ h
  exact Subtype.ext (Perm.viaEmbeddingHom_injective (Fin.castLEEmb hn) (congrArg Subtype.val h))

theorem noRankThreeDoubleCover_alternating {n : ℕ} (hn : 8 ≤ n) :
    NoRankThreeDoubleCover (alternatingGroup (Fin n)) :=
  noRankThreeDoubleCover_of_datum (alt8_e8Datum.map (altEmbed hn) (altEmbed_injective hn))

section AltSmall

open CFSG.LocalAnalysis.ComponentInitial

theorem cycleType_eq_of_sq_eq_one {n : ℕ} (hn : n ≤ 7) {σ : Perm (Fin n)} (h2 : σ ^ 2 = 1)
    (h1 : σ ≠ 1) (hs : Perm.sign σ = 1) : σ.cycleType = {2, 2} := by
  have ho : orderOf σ = 2 := orderOf_eq_prime h2 h1
  obtain ⟨k, hk⟩ := Perm.cycleType_prime_order (ho ▸ Nat.prime_two)
  rw [ho] at hk
  have hsum : σ.cycleType.sum ≤ n := by
    rw [Perm.sum_cycleType]
    exact (Finset.card_le_univ _).trans (by simp)
  rw [hk, Multiset.sum_replicate, smul_eq_mul] at hsum
  have hsign := Perm.sign_of_cycleType σ
  rw [hs, hk, Multiset.sum_replicate, Multiset.card_replicate, smul_eq_mul] at hsign
  have hk2 : k ≤ 2 := by omega
  interval_cases k
  · exact absurd hsign (by decide)
  · rw [hk]; rfl
  · exact absurd hsign (by decide)

theorem isConj_of_sq_eq_one {n : ℕ} (hn6 : 6 ≤ n) (hn7 : n ≤ 7)
    {σ τ : alternatingGroup (Fin n)} (hσ2 : σ ^ 2 = 1) (hσ1 : σ ≠ 1) (hτ2 : τ ^ 2 = 1)
    (hτ1 : τ ≠ 1) : IsConj σ τ := by
  have hc : ∀ ρ : alternatingGroup (Fin n), ρ ^ 2 = 1 → ρ ≠ 1 →
      (ρ : Perm (Fin n)).cycleType = {2, 2} := fun ρ h2 h1 =>
    cycleType_eq_of_sq_eq_one hn7 (by rw [← Subgroup.coe_pow, h2]; rfl)
      (fun h => h1 (Subtype.ext h)) (Perm.mem_alternatingGroup.mp ρ.2)
  refine alternatingGroup.isConj_of (Perm.isConj_iff_cycleType_eq.2 (by
    rw [hc σ hσ2 hσ1, hc τ hτ2 hτ1])) ?_
  rw [← Perm.sum_cycleType, hc σ hσ2 hσ1, Fintype.card_fin]
  simp only [Multiset.insert_eq_cons, Multiset.sum_cons, Multiset.sum_singleton]
  omega

theorem sq_lift_ne_one {P : Type*} [Group P] [Finite P] [Group.IsPerfect P] {m : ℕ}
    (hm : 3 ≤ m) (η : P →* alternatingGroup (Fin (m + 2))) (hη : Function.Surjective η)
    (hK : η.ker ≤ Subgroup.center P) (hK2 : Nat.card η.ker = 2) {x : Fin m → P}
    (hxη : ∀ i, η (x i) = altThreeCycle i) (hx3 : ∀ i, x i ^ 3 = 1) :
    (x ⟨0, by omega⟩ * x ⟨1, by omega⟩) ^ 2 ≠ 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hKp : IsPGroup 2 η.ker := IsPGroup.of_card (n := 1) (by rw [hK2, pow_one])
  intro h1
  have hzij : ∀ i j, i ≠ j → (x i * x j) ^ 2 = 1 := fun i j hij => by
    rw [lift_sq_eq η hη hK hKp hxη hx3 hij (show (⟨0, by omega⟩ : Fin m) ≠ ⟨1, by omega⟩ by
      simp [Fin.ext_iff]), h1]
  have hL : Subgroup.closure (Set.range x) = ⊤ := by
    have hmap : (Subgroup.closure (Set.range x)).map η = ⊤ := by
      rw [MonoidHom.map_closure, ← Set.range_comp]
      have : η ∘ x = altThreeCycle := funext hxη
      rw [this, closure_altThreeCycle]
    have hsup : Subgroup.closure (Set.range x) ⊔ η.ker = ⊤ := by
      rw [← Subgroup.comap_map_eq, hmap, Subgroup.comap_top]
    have h := CFSG.ComponentClassification.CentralExtensions.commutator_sup_central
      (Subgroup.closure (Set.range x)) η.ker hK
    rw [hsup, ← commutator_def, Group.IsPerfect.commutator_eq_top] at h
    exact eq_top_iff.mpr (h.le.trans (Subgroup.commutator_le_self _))
  have hcard := card_closure_le_of_carmichael m x hx3 hzij
  rw [hL, Subgroup.card_top] at hcard
  have hP : Nat.card P = Nat.card (alternatingGroup (Fin (m + 2))) * Nat.card η.ker := by
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup η.ker,
      Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective η hη).toEquiv]
  have hA : Nat.card (alternatingGroup (Fin (m + 2))) = (m + 2).factorial / 2 := by
    rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  have hApos : 0 < (m + 2).factorial / 2 := by
    rw [← hA]
    exact Nat.card_pos
  rw [hP, hA, hK2] at hcard
  omega

theorem noRankThreeDoubleCover_alternating_small {n : ℕ} (hn6 : 6 ≤ n) (hn7 : n ≤ 7) :
    NoRankThreeDoubleCover (alternatingGroup (Fin n)) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 2 := ⟨n - 2, by omega⟩
  intro J _ _ hq hZ ⟨e⟩
  have : Group.IsPerfect J := hq.1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set η : J →* alternatingGroup (Fin (m + 2)) :=
    e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center J))
  have hη : Function.Surjective η := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hkerη : η.ker = Subgroup.center J := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk x) = 1 ↔ _
    rw [map_eq_one_iff e e.injective, QuotientGroup.eq_one_iff]
  have hK : η.ker ≤ Subgroup.center J := hkerη.le
  have hK2 : Nat.card η.ker = 2 := by rw [hkerη, hZ]
  have hKp : IsPGroup 2 η.ker := IsPGroup.of_card (n := 1) (by rw [hK2, pow_one])
  have hlift : ∀ i : Fin m, ∃ x : J, η x = altThreeCycle i ∧ x ^ 3 = 1 := fun i => by
    obtain ⟨y, hy⟩ := hη (altThreeCycle i)
    obtain ⟨x, hx, hx3⟩ := exists_lift_pow_three_eq_one hK hKp
      (by rw [hy]; exact altThreeCycle_pow_three i)
    exact ⟨x, hx.trans hy, hx3⟩
  choose x hxη hx3 using hlift
  set z := (x ⟨0, by omega⟩ * x ⟨1, by omega⟩) ^ 2 with hz
  have hz1 : z ≠ 1 := sq_lift_ne_one (by omega) η hη hK hK2 hxη hx3
  have hzK : z ∈ η.ker := by
    rw [MonoidHom.mem_ker, hz, map_pow, map_mul, hxη, hxη, altThreeCycle_mul_sq]
    simp [Fin.ext_iff]
  have hzc : z ∈ Subgroup.center J := hK hzK
  have hk2 : ∀ k ∈ η.ker, k ^ 2 = 1 := fun k hk => by
    have := pow_card_eq_one' (G := η.ker) (x := ⟨k, hk⟩)
    rw [hK2] at this
    exact congrArg Subtype.val this
  set τ := altThreeCycle (n := m) ⟨0, by omega⟩ * altThreeCycle ⟨1, by omega⟩ with hτ
  have hτ2 : τ ^ 2 = 1 := altThreeCycle_mul_sq (by simp [Fin.ext_iff])
  have hτη : η (x ⟨0, by omega⟩ * x ⟨1, by omega⟩) = τ := by rw [map_mul, hxη, hxη]
  have hτ1 : τ ≠ 1 := fun h => hz1 (hk2 _ (by rw [MonoidHom.mem_ker, hτη, h]))
  have hinv : ∀ a : J, a ^ 2 = 1 → a ∈ η.ker := by
    intro a ha
    by_contra hη1
    rw [MonoidHom.mem_ker] at hη1
    have ha2 : η a ^ 2 = 1 := by rw [← map_pow, ha, map_one]
    obtain ⟨g, hg⟩ := isConj_iff.mp (isConj_of_sq_eq_one (by omega) hn7 hτ2 hτ1 ha2 hη1)
    obtain ⟨h, rfl⟩ := hη g
    set y := h * (x ⟨0, by omega⟩ * x ⟨1, by omega⟩) * h⁻¹ with hy
    have hk : y⁻¹ * a ∈ η.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hy, map_mul, map_mul, map_inv, hτη, hg,
        inv_mul_cancel]
    have hkc : Commute y (y⁻¹ * a) := (Subgroup.mem_center_iff.mp (hK hk) y)
    have hy2 : y ^ 2 = z := by
      rw [hy, conj_pow, ← hz, Subgroup.mem_center_iff.mp hzc h, mul_inv_cancel_right]
    apply hz1
    calc z = y ^ 2 := hy2.symm
      _ = y ^ 2 * (y⁻¹ * a) ^ 2 := by rw [hk2 _ hk, mul_one]
      _ = (y * (y⁻¹ * a)) ^ 2 := (hkc.mul_pow 2).symm
      _ = a ^ 2 := by rw [mul_inv_cancel_left]
      _ = 1 := ha
  have hle : CFSG.pRank 2 J ≤ 1 := by
    refine csSup_le' ?_
    rintro r ⟨A, hA, hcard⟩
    have hAK : A ≤ η.ker := fun a ha => hinv a (elemPow_eq_one_of_isElementaryAbelian a ha)
    have h2 : 2 ^ r ≤ 2 ^ 1 := by
      rw [← hcard, pow_one, ← hK2]
      exact Subgroup.card_le_of_le hAK
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h2
  omega

end AltSmall

@[expose] def m22α : Perm (Fin 22) :=
  List.formPerm [0, 12] * List.formPerm [1, 7] * List.formPerm [2, 15] * List.formPerm [3, 11] *
    List.formPerm [5, 21] * List.formPerm [6, 16] * List.formPerm [8, 9] * List.formPerm [10, 13]

@[expose] def m22β : Perm (Fin 22) :=
  List.formPerm [0, 21, 2, 20] * List.formPerm [1, 17, 3, 12] * List.formPerm [4, 11] *
    List.formPerm [5, 10, 6, 14] * List.formPerm [7, 13, 19, 9] * List.formPerm [16, 18]

theorem m22α_mem : m22α ∈ NativeSporadic.M22 := Subgroup.subset_closure (Set.mem_insert _ _)

theorem m22β_mem : m22β ∈ NativeSporadic.M22 :=
  Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)

@[expose] def m22T : Perm (Fin 22) :=
  swap 1 5 * swap 2 16 * swap 3 19 * swap 4 13 * swap 6 7 * swap 10 14 * swap 11 17 * swap 15 21

@[expose] def m22N : Perm (Fin 22) :=
  List.formPerm [0, 8, 6, 17, 1, 12, 13] * List.formPerm [2, 14, 15, 16, 21, 3, 19] *
    List.formPerm [4, 18, 20, 7, 11, 5, 9]

@[expose] def m22Word : List Char → Perm (Fin 22)
  | [] => 1
  | c :: w => (if c = 'a' then m22α else if c = 'b' then m22β else m22β⁻¹) * m22Word w

theorem m22Word_mem : ∀ w, m22Word w ∈ NativeSporadic.M22
  | [] => Subgroup.one_mem _
  | c :: w => by
    unfold m22Word
    refine Subgroup.mul_mem _ ?_ (m22Word_mem w)
    split_ifs
    · exact m22α_mem
    · exact m22β_mem
    · exact Subgroup.inv_mem _ m22β_mem

theorem m22T_eq : m22T = m22Word "aBabbaBabbababbaba".toList := by
  decide +kernel

theorem m22N_eq : m22N = m22Word "ababababbaB".toList := by
  decide +kernel

theorem m22T_mem : m22T ∈ NativeSporadic.M22 := m22T_eq ▸ m22Word_mem _

theorem m22N_mem : m22N ∈ NativeSporadic.M22 := m22N_eq ▸ m22Word_mem _

theorem m22_perm_e8Datum : E8Datum m22T (m22N * m22T * m22N⁻¹)
    (m22N * (m22N * m22T * m22N⁻¹) * m22N⁻¹) m22N where
  ne_one := by decide +kernel
  sq := by decide +kernel
  comm₁₂ := (by decide +kernel : m22T * (m22N * m22T * m22N⁻¹) = (m22N * m22T * m22N⁻¹) * m22T)
  comm₁₃ := (by decide +kernel : m22T * (m22N * (m22N * m22T * m22N⁻¹) * m22N⁻¹) =
    (m22N * (m22N * m22T * m22N⁻¹) * m22N⁻¹) * m22T)
  conj₁ := rfl
  conj₂ := rfl
  conj₃ := by decide +kernel

theorem m22_e8Datum :
    E8Datum (⟨m22T, m22T_mem⟩ : NativeSporadic.M22)
      (⟨m22N, m22N_mem⟩ * ⟨m22T, m22T_mem⟩ * ⟨m22N, m22N_mem⟩⁻¹)
      (⟨m22N, m22N_mem⟩ * (⟨m22N, m22N_mem⟩ * ⟨m22T, m22T_mem⟩ * ⟨m22N, m22N_mem⟩⁻¹) *
        ⟨m22N, m22N_mem⟩⁻¹) ⟨m22N, m22N_mem⟩ :=
  E8Datum.of_map NativeSporadic.M22.subtype Subtype.val_injective m22_perm_e8Datum

theorem noRankThreeDoubleCover_m22 : NoRankThreeDoubleCover (Spor .M22) := by
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have h₀ : NoRankThreeDoubleCover NativeSporadic.M22 := noRankThreeDoubleCover_of_datum m22_e8Datum
  have e' : NativeSporadic.M22 ≃* Spor .M22 := e
  have h₁ := noRankThreeDoubleCover_of_mulEquiv (X := NativeSporadic.M22) (Y := Spor .M22) e' h₀
  exact h₁

section Native

open CFSG.SectionRank CFSG.SectionRank.Native CFSG.SectionRank.LocalWitness
open CFSG.RankThree.PartTwo.Sec4.Census.DoubleCoverRanks.Native

theorem e8Datum_of_check {M V : Type} {O : Ops M V} {p d : ℕ} (Sp : OpsSpec O p d)
    [Inhabited M] [Inhabited V] (D : E8Data) (h : e8Check O D = true) :
    ∃ a₁ a₂ a₃ n : (NativeSporadic.seedMonoid p d 1 D.seedA D.seedB)ˣ, E8Datum a₁ a₂ a₃ n := by
  set S := NativeSporadic.seedMonoid p d 1 D.seedA D.seedB
  unfold e8Check at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨-, hprog⟩, hrx⟩, hrh⟩, hoh⟩, hX2⟩, hHo⟩, hXt⟩, hc12⟩, hc13⟩, hconj⟩ := h
  set R := O.regsOf D.seedA D.seedB D.nregs D.prog
  obtain ⟨wX, mX⟩ := Sp.regsOf_ok hprog hrx
  obtain ⟨wH, mH⟩ := Sp.regsOf_ok hprog hrh
  have eX := Sp.pow_eq_one_of_check wX hX2
  have eH := Sp.pow_eq_one_of_check wH hHo
  let x := unitOf S mX two_ne_zero eX
  let g := unitOf S mH hoh.ne' eH
  have fx : valHom S x = Sp.toMat R[D.rx]! := valHom_unitOf S _ _ _
  have fg : valHom S g = Sp.toMat R[D.rh]! := valHom_unitOf S _ _ _
  have hg : g ^ D.oh = 1 := unitOf_pow S mH _ eH
  set H' := O.pow R[D.rh]! (D.oh - 1)
  have wH' : Sp.WF H' := (Sp.pow_spec wH _).1
  have fgi : valHom S g⁻¹ = Sp.toMat H' := by
    rw [valHom_inv_of_pow S hoh.ne' hg, fg, (Sp.pow_spec wH _).2]
  set X₂ := O.mul (O.mul R[D.rh]! R[D.rx]!) H'
  set X₃ := O.mul (O.mul R[D.rh]! X₂) H'
  have wX₂ : Sp.WF X₂ := Sp.mul_wf (Sp.mul_wf wH wX) wH'
  have wX₃ : Sp.WF X₃ := Sp.mul_wf (Sp.mul_wf wH wX₂) wH'
  have f₂ : valHom S (g * x * g⁻¹) = Sp.toMat X₂ := by
    rw [map_mul, map_mul, fg, fx, fgi, Sp.toMat_mul (Sp.mul_wf wH wX) wH', Sp.toMat_mul wH wX]
  have f₃ : valHom S (g * (g * x * g⁻¹) * g⁻¹) = Sp.toMat X₃ := by
    rw [map_mul, map_mul, fg, f₂, fgi, Sp.toMat_mul (Sp.mul_wf wH wX₂) wH', Sp.toMat_mul wH wX₂]
  refine ⟨x, g * x * g⁻¹, g * (g * x * g⁻¹) * g⁻¹, g,
    ⟨?_, unitOf_pow S mX _ eX, ?_, ?_, rfl, rfl, ?_⟩⟩
  · intro h1
    apply Sp.toVec_ne hXt
    rw [Sp.toVec_vmul (Sp.unit_wf _) wX, ← fx, h1, map_one, Matrix.vecMul_one]
  · show x * (g * x * g⁻¹) = (g * x * g⁻¹) * x
    apply valHom_injective S
    rw [map_mul (valHom S) x, map_mul (valHom S) _ x, fx, f₂, ← Sp.toMat_mul wX wX₂,
      ← Sp.toMat_mul wX₂ wX]
    exact Sp.toMat_eq (Sp.mul_wf wX wX₂) (Sp.mul_wf wX₂ wX) hc12
  · show x * (g * (g * x * g⁻¹) * g⁻¹) = (g * (g * x * g⁻¹) * g⁻¹) * x
    apply valHom_injective S
    rw [map_mul (valHom S) x, map_mul (valHom S) _ x, fx, f₃, ← Sp.toMat_mul wX wX₃,
      ← Sp.toMat_mul wX₃ wX]
    exact Sp.toMat_eq (Sp.mul_wf wX wX₃) (Sp.mul_wf wX₃ wX) hc13
  · rw [mul_inv_eq_iff_eq_mul]
    apply valHom_injective S
    rw [map_mul (valHom S) g, map_mul (valHom S) _ g, map_mul (valHom S) x, fg, f₃, fx, f₂]
    have := Sp.toMat_of_conjOK wH wX₃ (Sp.mul_wf wX wX₂) hconj
    rwa [Sp.toMat_mul wX wX₂] at this

theorem hs_e8_check : e8Check (ops2 20) hsE8Data = true :=
  Certificates.certificate8093.1

theorem ru_e8_check : e8Check (ops2 28) ruE8Data = true :=
  Certificates.certificate8093.2

theorem hs_e8Datum :
    ∃ a₁ a₂ a₃ n : NativeSporadic.HS, E8Datum a₁ a₂ a₃ n :=
  e8Datum_of_check (spec2 20) hsE8Data hs_e8_check

theorem ru_e8Datum :
    ∃ a₁ a₂ a₃ n : NativeSporadic.Ru, E8Datum a₁ a₂ a₃ n :=
  e8Datum_of_check (spec2 28) ruE8Data ru_e8_check

end Native

theorem noRankThreeDoubleCover_hs :
    NoRankThreeDoubleCover (Spor .HS) := by
  obtain ⟨a₁, a₂, a₃, n, h⟩ := hs_e8Datum
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have h₀ : NoRankThreeDoubleCover NativeSporadic.HS := noRankThreeDoubleCover_of_datum h
  have e' : NativeSporadic.HS ≃* Spor .HS := e
  have h₁ := noRankThreeDoubleCover_of_mulEquiv (X := NativeSporadic.HS) (Y := Spor .HS) e' h₀
  exact h₁

theorem noRankThreeDoubleCover_ru :
    NoRankThreeDoubleCover (Spor .Ru) := by
  obtain ⟨a₁, a₂, a₃, n, h⟩ := ru_e8Datum
  obtain ⟨e⟩ := CFSG.Sporadic.Bridge.Ru.nonempty_mulEquiv
  have h₀ : NoRankThreeDoubleCover NativeSporadic.Ru := noRankThreeDoubleCover_of_datum h
  have e' : NativeSporadic.Ru ≃* Spor .Ru := e
  have h₁ := noRankThreeDoubleCover_of_mulEquiv (X := NativeSporadic.Ru) (Y := Spor .Ru) e' h₀
  exact h₁

section Sp62

open Matrix RankOmegaF4
open CFSG.Assembly.RankThreeEven (projSp sympForm)

@[expose] def spU (A : Matrix (Fin 3) (Fin 3) (ZMod 2)) :
    Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  fromBlocks 1 A 0 1

@[expose] def spA₁ : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ⟨spU !![0, 0, 0; 0, 0, 1; 0, 1, 0], spU !![0, 0, 0; 0, 0, 1; 0, 1, 0], by decide +kernel,
    by decide +kernel⟩

@[expose] def spA₂ : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ⟨spU !![0, 0, 1; 0, 0, 0; 1, 0, 0], spU !![0, 0, 1; 0, 0, 0; 1, 0, 0], by decide +kernel,
    by decide +kernel⟩

@[expose] def spA₃ : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ⟨spU !![0, 1, 0; 1, 0, 1; 0, 1, 0], spU !![0, 1, 0; 1, 0, 1; 0, 1, 0], by decide +kernel,
    by decide +kernel⟩

@[expose] def spN : GL (Fin 3 ⊕ Fin 3) (ZMod 2) :=
  ⟨fromBlocks !![0, 0, 1; 1, 0, 0; 0, 1, 1] 0 0 !![0, 1, 1; 1, 0, 0; 0, 1, 0],
    fromBlocks !![0, 1, 0; 1, 0, 1; 1, 0, 0] 0 0 !![0, 1, 0; 0, 0, 1; 1, 0, 1],
    by decide +kernel, by decide +kernel⟩

theorem sp62_gl_e8Datum : E8Datum spA₁ spA₂ spA₃ spN where
  ne_one := by decide +kernel
  sq := by decide +kernel
  comm₁₂ := (by decide +kernel : spA₁ * spA₂ = spA₂ * spA₁)
  comm₁₃ := (by decide +kernel : spA₁ * spA₃ = spA₃ * spA₁)
  conj₁ := by decide +kernel
  conj₂ := by decide +kernel
  conj₃ := by decide +kernel

theorem spA₁_symplectic : (spA₁ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))ᵀ *
    sympForm 3 (ZMod 2) * spA₁ = sympForm 3 (ZMod 2) := by
  decide +kernel

theorem spA₂_symplectic : (spA₂ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))ᵀ *
    sympForm 3 (ZMod 2) * spA₂ = sympForm 3 (ZMod 2) := by
  decide +kernel

theorem spA₃_symplectic : (spA₃ : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))ᵀ *
    sympForm 3 (ZMod 2) * spA₃ = sympForm 3 (ZMod 2) := by
  decide +kernel

theorem spN_symplectic : (spN : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))ᵀ *
    sympForm 3 (ZMod 2) * spN = sympForm 3 (ZMod 2) := by
  decide +kernel

theorem projF2_injective {ι : Type} [Fintype ι] [DecidableEq ι] :
    Function.Injective (projF2 (ι := ι)) := by
  rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
  intro x hx
  have hc := ker_projF2_le hx
  rw [Matrix.GeneralLinearGroup.center_eq_range_scalar] at hc
  obtain ⟨u, rfl⟩ := hc
  have hu : ∀ v : (ZMod 2)ˣ, v = 1 := by decide
  rw [hu u, map_one]
  exact Subgroup.one_mem _

theorem sympForm_map_f2 : (sympForm 3 (ZMod 2)).map f2 = sympForm 3 (GaloisField 2 1) := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp only [sympForm, Matrix.map_apply, Matrix.fromBlocks_apply₁₁, Matrix.fromBlocks_apply₁₂,
      Matrix.fromBlocks_apply₂₁, Matrix.fromBlocks_apply₂₂, Matrix.zero_apply, Matrix.neg_apply,
      Matrix.one_apply, map_zero, map_neg] <;>
    split_ifs <;> simp

theorem projF2_mem_projSp {M : GL (Fin 3 ⊕ Fin 3) (ZMod 2)}
    (hM : (M : Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (ZMod 2))ᵀ * sympForm 3 (ZMod 2) * M =
      sympForm 3 (ZMod 2)) :
    projF2 M ∈ projSp 3 (GaloisField 2 1) := by
  refine ⟨toF2 M, Subgroup.subset_closure ?_, rfl⟩
  change ((toF2 M : GL (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) :
      Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) (GaloisField 2 1))ᵀ * sympForm 3 (GaloisField 2 1) *
    (toF2 M : GL (Fin 3 ⊕ Fin 3) (GaloisField 2 1)) = sympForm 3 (GaloisField 2 1)
  rw [coe_toF2, ← sympForm_map_f2, ← Matrix.transpose_map, ← RingEquiv.coe_toRingHom f2,
    ← Matrix.map_mul, ← Matrix.map_mul, hM]

noncomputable def sp62A₁ : projSp 3 (GaloisField 2 1) :=
  ⟨projF2 spA₁, projF2_mem_projSp spA₁_symplectic⟩

noncomputable def sp62A₂ : projSp 3 (GaloisField 2 1) :=
  ⟨projF2 spA₂, projF2_mem_projSp spA₂_symplectic⟩

noncomputable def sp62A₃ : projSp 3 (GaloisField 2 1) :=
  ⟨projF2 spA₃, projF2_mem_projSp spA₃_symplectic⟩

noncomputable def sp62N : projSp 3 (GaloisField 2 1) :=
  ⟨projF2 spN, projF2_mem_projSp spN_symplectic⟩

theorem sp62_e8Datum : E8Datum sp62A₁ sp62A₂ sp62A₃ sp62N :=
  E8Datum.of_map (projSp 3 (GaloisField 2 1)).subtype Subtype.val_injective
    (sp62_gl_e8Datum.map projF2 projF2_injective)

theorem noRankThreeDoubleCover_sp62 : NoRankThreeDoubleCover (projSp 3 (GaloisField 2 1)) :=
  noRankThreeDoubleCover_of_datum sp62_e8Datum

end Sp62

section Sz8

open TauCeti

local notation "F₈" => GaloisField 2 (2 * 1 + 1)

local notation "ω₈" => CFSG.LieType.Multipliers.Sz8.omega

theorem omega_ne_zero : ω₈ ≠ 0 := by
  intro h
  have h3 := CFSG.LieType.Multipliers.Sz8.omega_cube
  rw [h] at h3
  simp at h3

theorem omega_pow_seven : ω₈ ^ 7 = 1 := by
  have h3 := CFSG.LieType.Multipliers.Sz8.omega_cube
  have h2 : (2 : F₈) = 0 := CharTwo.two_eq_zero
  linear_combination (ω₈ ^ 4 + ω₈ ^ 2 + ω₈ + 1) * h3 + (ω₈ ^ 2 + ω₈) * h2

noncomputable def kappa : F₈ˣ := Units.mk0 (ω₈ ^ 5) (pow_ne_zero _ omega_ne_zero)

theorem div_kappa (b : F₈) : b / (kappa : F₈) ^ 2 ^ (1 + 1) = ω₈ * b := by
  have h7 := omega_pow_seven
  rw [kappa, Units.val_mk0, div_eq_iff (pow_ne_zero _ (pow_ne_zero _ omega_ne_zero))]
  calc b = b * (ω₈ ^ 7) ^ 3 := by rw [h7]; ring
    _ = ω₈ * b * (ω₈ ^ 5) ^ 2 ^ (1 + 1) := by ring

noncomputable def sz8U (b : F₈) : GL (Fin 4) F₈ := Suzuki.unipotent 1 0 b

noncomputable def sz8N : GL (Fin 4) F₈ := Suzuki.torus 1 kappa

theorem sz8U_mem (b : F₈) : sz8U b ∈ TauCeti.suzukiGroup 1 := Suzuki.unipotent_mem_suzukiGroup 0 b

theorem sz8N_mem : sz8N ∈ TauCeti.suzukiGroup 1 := Suzuki.torus_mem_suzukiGroup 1 kappa

theorem sz8U_mul (b c : F₈) : sz8U b * sz8U c = sz8U (b + c) := by
  rw [sz8U, sz8U, Suzuki.unipotent_mul_unipotent, add_zero, zero_mul, add_zero, sz8U]

theorem sz8N_conj (b : F₈) : sz8N * sz8U b * sz8N⁻¹ = sz8U (ω₈ * b) := by
  rw [sz8N, sz8U, Suzuki.torus_mul_unipotent_mul_torus_inv, mul_zero, div_kappa, sz8U]

theorem sz8_gl_e8Datum : E8Datum (sz8U 1) (sz8U ω₈) (sz8U (ω₈ ^ 2)) sz8N where
  ne_one := by
    intro h
    have := congrArg (fun g : GL (Fin 4) F₈ => (g : Matrix (Fin 4) (Fin 4) F₈) 3 1) h
    simp [sz8U, Suzuki.coe_unipotent] at this
  sq := by
    rw [pow_two, sz8U_mul, CharTwo.add_self_eq_zero, sz8U, Suzuki.unipotent_zero_zero]
  comm₁₂ := by
    show sz8U 1 * sz8U ω₈ = sz8U ω₈ * sz8U 1
    rw [sz8U_mul, sz8U_mul, add_comm (1 : F₈)]
  comm₁₃ := by
    show sz8U 1 * sz8U (ω₈ ^ 2) = sz8U (ω₈ ^ 2) * sz8U 1
    rw [sz8U_mul, sz8U_mul, add_comm (1 : F₈)]
  conj₁ := by
    rw [sz8N_conj]
    congr 1
    ring
  conj₂ := by
    rw [sz8N_conj]
    congr 1
    ring
  conj₃ := by
    rw [sz8N_conj, sz8U_mul]
    congr 1
    linear_combination CFSG.LieType.Multipliers.Sz8.omega_cube

theorem sz8_e8Datum :
    E8Datum (⟨sz8U 1, sz8U_mem 1⟩ : TauCeti.suzukiGroup 1) ⟨sz8U ω₈, sz8U_mem ω₈⟩
      ⟨sz8U (ω₈ ^ 2), sz8U_mem (ω₈ ^ 2)⟩ ⟨sz8N, sz8N_mem⟩ :=
  E8Datum.of_map (TauCeti.suzukiGroup 1).subtype Subtype.val_injective sz8_gl_e8Datum

theorem noRankThreeTwoCover_sz8 (hm : (TauCeti.LieTypeIndex.suzuki 1).Valid) :
    NoRankThreeTwoCover (TauCeti.CFSGIndex.lie ⟨.suzuki 1, hm⟩).Group := by
  have h₀ : NoRankThreeTwoCover (TauCeti.suzukiGroup 1) := noRankThreeTwoCover_of_datum sz8_e8Datum
  have e : ↥(TauCeti.suzukiGroup 1) ≃* (TauCeti.CFSGIndex.lie ⟨.suzuki 1, hm⟩).Group :=
    ((CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hm).trans
      (CFSG.BenderSuzuki.Catalog.suzukiGroupEquiv 1).symm).symm
  have h₁ := noRankThreeTwoCover_of_mulEquiv (X := TauCeti.suzukiGroup 1)
    (Y := (TauCeti.CFSGIndex.lie ⟨.suzuki 1, hm⟩).Group) e h₀
  exact h₁

end Sz8

end DoubleCoverRanks

open DoubleCoverRanks
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

structure TwoCoverRanksOpen'' : Prop where
  psu42 : NoRankThreeDoubleCover (projSU 4 2 1)
  psl34 : ∀ (J : Type) [Group J] [Finite J], IsTwoCover J (projSL 3 (GaloisField 2 2)) →
    CFSG.pRank 2 J = 3 → IsCyclic (Subgroup.center J) ∧ Nat.card (Subgroup.center J) = 4
  g24 : ∀ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.G2 q).Valid), q.p = 2 →
    q.exponent = 2 → NoRankThreeDoubleCover (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group

theorem TwoCoverRanksOpen'.of_open''
    (h : TwoCoverRanksOpen'') : TwoCoverRanksOpen' where
  alternating n hn6 _ := by
    rcases Nat.lt_or_ge n 8 with hn | hn
    · exact noRankThreeDoubleCover_alternating_small hn6 (by omega)
    · exact noRankThreeDoubleCover_alternating hn
  hs := noRankThreeDoubleCover_hs
  ru := noRankThreeDoubleCover_ru
  m22 := noRankThreeDoubleCover_m22
  psu42 := h.psu42
  psl34 := h.psl34
  g24 := h.g24
  sz8 := noRankThreeTwoCover_sz8
  sp62 := noRankThreeDoubleCover_sp62

end CFSG.RankThree.PartTwo.Sec4.Census

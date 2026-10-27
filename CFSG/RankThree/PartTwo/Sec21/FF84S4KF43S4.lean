module

public import CFSG.RankThree.PartTwo.Sec21.FF84S4KF43Main
public import CFSG.RankThree.PartTwo.Sec21.FF84S4SzAut3
public import CFSG.RankThree.PartOne.N143.T2LargeAll
public import CFSG.LocalAnalysis.ComponentClassification.GoldschmidtTDGriess

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF84.S4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF84
open CFSG.Assembly (InCatalog)
open CFSG.Assembly.RankThreeEven (localRank)
open CFSG.RankThree.LocalRank (aschbacherSolvableCore)

private theorem kf43s4_card_alt5 : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Fintype.card_fin]
  decide

private theorem kf43s4_alt5_nonab : ∃ x y : alternatingGroup (Fin 5), x * y ≠ y * x := by
  decide

@[expose] def S43_KFactS4 : Prop :=
  ∀ (H : Type) [Group H] [Finite H], KCore.KGroupNonab InCatalog H → PartTwo.SectionFourHyp H →
    ∀ K : Subgroup H, Group.IsPerfect ↥K → IsTypeLnq 2 2 2 K →
      ⁅K, pPrimeCore 3 H⁆ ≤ aschbacherSolvableCore 3 H

theorem s43_kfactS4_of (h41 : PartTwo.Sec4.Item4_1LargeAll)
    (hSz : LemmaSz) (hAut : LemmaSzAut3) : S43_KFactS4 := by
  intro H _ _ hKG hS4 K hKp hKt
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hQ3 := kf43_image_not_dvd_three (H := H)
  have hrad := kf43_radical_free_image (H := H)
  set Θ := aschbacherSolvableCore 3 H with hΘ
  set π : H →* H ⧸ Θ := QuotientGroup.mk' Θ with hπ
  set Qs : Subgroup (H ⧸ Θ) := (pPrimeCore 3 H).map π with hQs
  haveI hQn : Qs.Normal := kf43_image_normal
  have hKQ : KCore.KGroupNonab InCatalog ↥Qs :=
    KCore.KGroupNonab.subgroup Assembly.inCatalog_isoInvariant
      (KCore.KGroupNonab.quotient Assembly.inCatalog_isoInvariant hKG Θ) Qs
  have hrank : localRank 5 ↥(layer ↥Qs) ≤ 2 := by
    let Y : Subgroup (H ⧸ Θ) := (layer ↥Qs).map Qs.subtype
    have hf : Function.Surjective (π.subgroupComap Y) :=
      MonoidHom.subgroupComap_surjective_of_surjective π Y (QuotientGroup.mk'_surjective Θ)
    let e : ↥(layer ↥Qs) ≃* ↥Y :=
      Subgroup.equivMapOfInjective (layer ↥Qs) Qs.subtype Qs.subtype_injective
    let f : ↥(Y.comap π) →* ↥(layer ↥Qs) := e.symm.toMonoidHom.comp (π.subgroupComap Y)
    have hfs : Function.Surjective f := e.symm.surjective.comp hf
    let ε : (↥(Y.comap π) ⧸ f.ker) ≃* ↥(layer ↥Qs) :=
      QuotientGroup.quotientKerEquivOfSurjective f hfs
    have hlay : layer (↥(Y.comap π) ⧸ f.ker) = ⊤ :=
      CFSG.LocalCores.layer_eq_top_of_surjective CFSG.WholeGroup.layer_layer_eq_top
        ε.symm.toMonoidHom ε.symm.surjective
    have h5 := h41 H hS4 (Y.comap π) f.ker hlay 5 (by norm_num) (by norm_num)
    rw [Census.localRank_eq_of_mulEquiv ε Nat.prime_five] at h5
    omega
  obtain ⟨e5⟩ := CFSG.ComponentClassification.RankTwoClassical.nonempty_equiv_a5_of_psl hKt
  haveI : IsSimpleGroup (alternatingGroup (Fin 5)) := inferInstance
  have hPs : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := e5.isSimpleGroup
  have hPn : ∃ x y : ↥K ⧸ Subgroup.center ↥K, x * y ≠ y * x := by
    obtain ⟨a, b, hab⟩ := kf43s4_alt5_nonab
    exact ⟨e5.symm a, e5.symm b, fun h => hab (by simpa using congrArg e5 h)⟩
  have hP3 : 3 ∣ Nat.card (↥K ⧸ Subgroup.center ↥K) := by
    rw [Nat.card_congr e5.toEquiv, kf43s4_card_alt5]
    norm_num
  let φ : ↥K →* MulAut ↥Qs := (MulAut.conjNormal (H := Qs)).comp (π.comp K.subtype)
  have hφ := kf43_action_trivial_of_radical_free hSz hrad hKQ hQ3 hrank hAut hKp hPs hPn hP3 φ
  rw [Subgroup.commutator_le]
  intro k hk n hn
  have hnQ : π n ∈ Qs := Subgroup.mem_map_of_mem π hn
  have h1 := congrArg (fun f : ↥K →* MulAut ↥Qs => ((f ⟨k, hk⟩ ⟨π n, hnQ⟩ : ↥Qs) : H ⧸ Θ)) hφ
  have h2 : π k * π n * (π k)⁻¹ = π n := by
    simpa [φ, MulAut.conjNormal_apply] using h1
  show k * n * k⁻¹ * n⁻¹ ∈ Θ
  rw [← QuotientGroup.eq_one_iff]
  show π (k * n * k⁻¹ * n⁻¹) = 1
  rw [map_mul, map_mul, map_mul, map_inv, map_inv, h2]
  group

theorem s43_kfactS4
    : S43_KFactS4 :=
  s43_kfactS4_of
    (PartTwo.Sec4.Item41Narrow.item4_1LargeAll_of_griess
      CFSG.ComponentClassification.TBLit.griessMultipliersAllModels_holds)
    lemmaSz_holds lemmaSzAut3_holds

end CFSG.RankThree.PartTwo.Sec21.FF84.S4

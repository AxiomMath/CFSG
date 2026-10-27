module

public import CFSG.RankThree.PartOne.K133H.WeylKey
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeHat
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual
public import CFSG.RankThree.LocalRank.SelectorCases
public import CFSG.RankThree.PartOne.S10.Defs

public section

namespace CFSG.StandardType

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Chevalley
  CFSG.RankThree.PartOne

namespace NoOffE6Three

section WeylDiagGen

variable {τ : Tag} {k : Type} [Field k]

theorem rootDiagUnit_conj_mem_rootSpan (a : Fin τ.rank → kˣ)
    {S : Set (Fin τ.rank → ℤ)} (hS : ∀ α ∈ S, IsRoot τ α) {u : ModGL τ k}
    (hu : u ∈ rootSpan τ k S) :
    rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ ∈ rootSpan τ k S := by
  have h : (rootSpan τ k S).map (MulAut.conj (rootDiagUnit τ a)).toMonoidHom =
      rootSpan τ k S :=
    map_rootSpan_of_forall fun α hα => map_conj_rootDiagUnit_rootSubgroup a (hS α hα)
  rw [← h]
  exact ⟨u, hu, rfl⟩

theorem rootDiagUnit_conj_mem_posUnipotent_of_rootSpan (a : Fin τ.rank → kˣ) {u : ModGL τ k}
    (hu : u ∈ posUnipotent τ k) :
    rootDiagUnit τ a * u * (rootDiagUnit τ a)⁻¹ ∈ posUnipotent τ k :=
  rootDiagUnit_conj_mem_rootSpan a (fun _ hα => hα.1) hu

theorem rootDiagUnit_mul_comm (a b : Fin τ.rank → kˣ) :
    rootDiagUnit τ a * rootDiagUnit τ b = rootDiagUnit τ b * rootDiagUnit τ a := by
  rw [← rootDiagUnit_mul, ← rootDiagUnit_mul, mul_comm]

theorem exists_conj_eq_canonicalRep_of_mem_normalizer_rootDiag {V : Set (ModGL τ k)}
    (hVD : ∀ x ∈ V, ∃ a : Fin τ.rank → kˣ, x = rootDiagUnit τ a) {g : ModGL τ k}
    (hgC : g ∈ adjointGroup τ k) (hgV : ∀ x ∈ V, g * x * g⁻¹ ∈ V) :
    ∃ w : WeylGroup τ, ∀ x ∈ V, g * x * g⁻¹ =
      canonicalRep (coxeterSystem τ) k w * x * (canonicalRep (coxeterSystem τ) k w)⁻¹ := by
  have hB := Chevalley_toral_centralizer_Bruhat_factors τ k (1 : Fin τ.rank → kˣ)
  have hg1 : g ∈ toralCentralizer τ k 1 :=
    mem_toralCentralizer.2 ⟨hgC, by rw [rootDiagUnit_one, one_mul, inv_one, mul_one]⟩
  obtain ⟨w, -, h, hh, u, hu, v, hv, hgeq⟩ := hB.1 g hg1
  have huU : u ∈ posUnipotent τ k := rootSpan_le_posUnipotent (fun α hα => hα.2) hu
  have hvI : v ∈ rootSpan τ k (inversionSet w) := rootSpan_mono Set.inter_subset_right hv
  refine ⟨w, fun x hx => ?_⟩
  set n := canonicalRep (coxeterSystem τ) k w with hn
  have hnC : n ∈ adjointGroup τ k := by
    rw [hn]; exact canonicalRep_mem_adjointGroup (coxeterSystem τ) k w
  have huC : u ∈ adjointGroup τ k := posUnipotent_le_adjointGroup huU
  have hvC : v ∈ adjointGroup τ k :=
    posUnipotent_le_adjointGroup (rootSpan_le_posUnipotent (fun α hα => inversionSet_pos hα) hvI)
  obtain ⟨a, rfl⟩ := hVD x hx
  obtain ⟨a', ha'⟩ := hVD _ (hgV _ hx)
  obtain ⟨b, hb⟩ := exists_rootDiagUnit_eq_of_mem_torusGroup hh
  have hy : n * rootDiagUnit τ a * n⁻¹ = rootDiagUnit τ (weylTuple w a) := by
    rw [hn]; exact canonicalRep_conj_rootDiagUnit (K := k) w a
  set u' := (n * rootDiagUnit τ a * n⁻¹)⁻¹ * u * (n * rootDiagUnit τ a * n⁻¹) with hu'def
  set v' := (rootDiagUnit τ a)⁻¹ * v * rootDiagUnit τ a with hv'def
  have hu'U : u' ∈ posUnipotent τ k := by
    rw [hu'def, hy]
    have h := rootDiagUnit_conj_mem_posUnipotent_of_rootSpan (weylTuple w a)⁻¹ huU
    simpa [rootDiagUnit_inv] using h
  have hv'I : v' ∈ rootSpan τ k (inversionSet w) := by
    rw [hv'def]
    have h := rootDiagUnit_conj_mem_rootSpan a⁻¹ (fun α hα => (inversionSet_pos hα).1) hvI
    simpa [rootDiagUnit_inv] using h
  have heq : h * (n * rootDiagUnit τ a * n⁻¹) * u' * n * v'
      = (g * rootDiagUnit τ a * g⁻¹) * h * u * n * v := by
    rw [hu'def, hv'def, hgeq]
    group
  set s := ((g * rootDiagUnit τ a * g⁻¹) * h)⁻¹ * (h * (n * rootDiagUnit τ a * n⁻¹)) with hsdef
  have hsuv : s * u' * n * v' = u * n * v := by
    have h2 : s * u' * n * v' = ((g * rootDiagUnit τ a * g⁻¹) * h)⁻¹ *
        (h * (n * rootDiagUnit τ a * n⁻¹) * u' * n * v') := by
      rw [hsdef]; group
    rw [h2, heq]
    group
  have hs_eq : s = rootDiagUnit τ ((a' * b)⁻¹ * (b * weylTuple w a)) := by
    rw [hsdef, ha', hb, hy, ← rootDiagUnit_mul, ← rootDiagUnit_mul, rootDiagUnit_inv,
      ← rootDiagUnit_mul]
  have hu'C : u' ∈ adjointGroup τ k := posUnipotent_le_adjointGroup hu'U
  have hv'C : v' ∈ adjointGroup τ k :=
    posUnipotent_le_adjointGroup (rootSpan_le_posUnipotent (fun α hα => inversionSet_pos hα) hv'I)
  have hsC : s ∈ adjointGroup τ k := by
    have hform : s = (u * n * v) * (u' * n * v')⁻¹ := by
      rw [← hsuv]; group
    rw [hform]
    exact mul_mem (mul_mem (mul_mem huC hnC) hvC)
      (inv_mem (mul_mem (mul_mem hu'C hnC) hv'C))
  have hsT : s ∈ torusGroup τ k := by
    have hmemC : rootDiagUnit τ ((a' * b)⁻¹ * (b * weylTuple w a)) ∈ adjointGroup τ k := by
      rw [← hs_eq]; exact hsC
    rw [hs_eq]
    exact CFSG.SeitzReduction.E6Pilot.rootDiagUnit_mem_torusGroup_of_mem_adjointGroup _
      hmemC
  obtain ⟨-, hs1, -⟩ := hB.2.1 w w s 1 u' u v' v hsT (one_mem _) hu'U huU hv'I hvI
    (by simpa only [one_mul] using hsuv)
  have hhy : h * (n * rootDiagUnit τ a * n⁻¹) = (g * rootDiagUnit τ a * g⁻¹) * h := by
    have h1 : ((g * rootDiagUnit τ a * g⁻¹) * h)⁻¹ *
        (h * (n * rootDiagUnit τ a * n⁻¹)) = 1 := by
      rw [← hsdef]; exact hs1
    exact (inv_mul_eq_one.mp h1).symm
  have hcomm : (g * rootDiagUnit τ a * g⁻¹) * h = h * (g * rootDiagUnit τ a * g⁻¹) := by
    rw [ha', hb, rootDiagUnit_mul_comm]
  have hyx : n * rootDiagUnit τ a * n⁻¹ = g * rootDiagUnit τ a * g⁻¹ :=
    mul_left_cancel (hhy.trans hcomm)
  exact hyx.symm

end WeylDiagGen

end NoOffE6Three

end CFSG.StandardType

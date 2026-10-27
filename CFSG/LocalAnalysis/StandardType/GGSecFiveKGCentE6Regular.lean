module

public import CFSG.RankThree.PartOne.KE8F.FamBruhat
import CFSG.LocalAnalysis.SeitzReduction.EPilotRootSL2Basic
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsExcToral
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KE.StabGeneral
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.KGCentE6

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.PartOne.KE8F

private theorem exists_rootDiagUnit_mem_rootSpan_pair_E6
    {K : Type} [Field K]
    {β : Fin Tag.E6.rank → ℤ} (hβ : IsRoot .E6 β) (ζ : Kˣ) :
    ∃ a : Fin Tag.E6.rank → Kˣ, rootDiagUnit .E6 a ∈ rootSpan .E6 K {β, -β} ∧
      rootChar a β = ζ ^ 2 ∧ ∀ i, ∃ m : ℤ, a i = ζ ^ m := by
  have hτ : Tag.E6 = .E6 ∨ Tag.E6 = .E7 ∨ Tag.E6 = .E8 := Or.inl rfl
  have hχ : ∀ γ, rootChar (fun j => ζ ^ iform β (Pi.single j 1)) γ = ζ ^ iform β γ := by
    intro γ
    rw [SeitzReduction.F4Pilot.iform_eq_sum_mul_iform_single β γ, rootChar,
      ← Finset.prod_zpow_eq_zpow_sum]
    exact Finset.prod_congr rfl fun j _ => by rw [← zpow_mul, mul_comm]
  obtain ⟨v, i, hv⟩ := isRoot_iff_exists_smul_single.1 hβ
  refine ⟨fun j => ζ ^ iform β (Pi.single j 1), ?_, ?_, fun j => ⟨_, rfl⟩⟩
  · have e : rootDiagUnit .E6 (fun j => ζ ^ iform β (Pi.single j 1)) =
        canonicalRep (coxeterSystem .E6) K v * torusElt .E6 K i ζ *
          (canonicalRep (coxeterSystem .E6) K v)⁻¹ := by
      rw [torusElt_eq_rootDiagUnit]
      refine (rootDiagUnit_eq_conj_canonicalRep_iff _ _ v).2 fun x => ?_
      rw [hχ, SeitzReduction.EPilot.rootChar_cartan_row, ← hv, iform_smul, iform_comm,
        SeitzReduction.EPilot.iform_single_eq_coPair hτ]
    have hmap : (rootSubgroup .E6 K (Pi.single i 1) ⊔ rootSubgroup .E6 K (-Pi.single i 1)).map
        (MulAut.conj (canonicalRep (coxeterSystem .E6) K v)).toMonoidHom =
          rootSubgroup .E6 K β ⊔ rootSubgroup .E6 K (-β) := by
      rw [Subgroup.map_sup, (canonical_weyl_root_transport .E6 K).2.1 v _ (isRoot_single .E6 i),
        (canonical_weyl_root_transport .E6 K).2.1 v _ (IsRoot.neg (isRoot_single .E6 i)),
        smul_neg, hv]
    have hmem : rootDiagUnit .E6 (fun j => ζ ^ iform β (Pi.single j 1)) ∈
        rootSubgroup .E6 K β ⊔ rootSubgroup .E6 K (-β) := by
      rw [e, ← hmap]
      exact ⟨_, SeitzReduction.F4Pilot.torusElt_mem_rootPair i ζ, rfl⟩
    have h1 : rootSubgroup .E6 K β ≤ rootSpan .E6 K {β, -β} :=
      le_iSup₂_of_le β (Set.mem_insert _ _) le_rfl
    have h2 : rootSubgroup .E6 K (-β) ≤ rootSpan .E6 K {β, -β} :=
      le_iSup₂_of_le (-β) (Set.mem_insert_of_mem _ rfl) le_rfl
    exact sup_le h1 h2 hmem
  · rw [hχ, SeitzReduction.EPilot.iform_self_eq_two hτ hβ]
    exact zpow_two ζ |>.trans (sq ζ).symm

theorem exists_family_famKernel_eq_empty_E6
    {K : Type} [Field K] [Finite K] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hpK : p ∣ Nat.card Kˣ) {F : Set (Fin Tag.E6.rank → Kˣ)} (hF : ∀ a ∈ F, ∀ i, a i ^ p = 1)
    {α : MulAut (adjointGroup .E6 K)}
    (hαF : ∀ a ∈ F, α * rootDiagAutHom .E6 K a = rootDiagAutHom .E6 K a * α)
    (hfix : ∀ β ∈ famKernel F, ∀ x : adjointGroup .E6 K,
      (x : ModGL .E6 K) ∈ rootSubgroup .E6 K β → α x = x) :
    ∃ F' : Set (Fin Tag.E6.rank → Kˣ), F ⊆ F' ∧ (∀ a ∈ F', ∀ i, a i ^ p = 1) ∧
      famKernel F' = ∅ ∧ ∀ a ∈ F', α * rootDiagAutHom .E6 K a = rootDiagAutHom .E6 K a * α := by
  have : Fact p.Prime := ⟨hp⟩
  have hp2' : ¬ p ∣ 2 := fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 h)
  obtain ⟨ζ, hζ⟩ := exists_prime_orderOf_dvd_card' p hpK
  have hζp : ζ ^ p = 1 := hζ ▸ pow_orderOf_eq_one ζ
  have hζ2 : ζ ^ 2 ≠ 1 := fun h => hp2' (hζ ▸ orderOf_dvd_of_pow_eq_one h)
  choose! A hA using fun β (hβ : IsRoot .E6 β) => exists_rootDiagUnit_mem_rootSpan_pair_E6 hβ ζ
  have hfix2 : ∀ β ∈ famKernel F, ∀ x : adjointGroup .E6 K,
      (x : ModGL .E6 K) ∈ rootSpan .E6 K {β, -β} → α x = x := by
    intro β hβ x hx
    have hle : rootSpan .E6 K {β, -β} ≤
        (α.toMonoidHom.eqLocus (MonoidHom.id _)).map (adjointGroup .E6 K).subtype := by
      refine iSup₂_le fun γ hγ => ?_
      intro y hy
      have hγF : γ ∈ famKernel F := by
        rcases hγ with rfl | rfl
        · exact hβ
        · exact LayerExc.neg_mem_famKernel hβ
      have hyC := rootSubgroup_le_adjointGroup γ hy
      exact ⟨⟨y, hyC⟩, hfix γ hγF ⟨y, hyC⟩ hy, rfl⟩
    obtain ⟨y, hy, hyx⟩ := hle hx
    obtain rfl : y = x := Subtype.ext hyx
    exact hy
  refine ⟨F ∪ A '' famKernel F, Set.subset_union_left, ?_, ?_, ?_⟩
  · rintro a (ha | ⟨β, hβ, rfl⟩) i
    · exact hF a ha i
    · obtain ⟨m, hm⟩ := (hA β hβ.1).2.2 i
      rw [hm, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hζp, one_zpow]
  · refine Set.eq_empty_of_forall_notMem fun β hβ => ?_
    have hβF : β ∈ famKernel F := ⟨hβ.1, fun a ha => hβ.2 a (Or.inl ha)⟩
    have h1 := hβ.2 (A β) (Or.inr ⟨β, hβF, rfl⟩)
    rw [(hA β hβ.1).2.1] at h1
    exact hζ2 h1
  · rintro a (ha | ⟨β, hβ, rfl⟩)
    · exact hαF a ha
    · obtain ⟨hmem, -, -⟩ := hA β hβ.1
      set d : adjointGroup .E6 K :=
        ⟨rootDiagUnit .E6 (A β), SeitzReduction.EPilot.rootSpan_le_adjointGroup' _ hmem⟩
      have hαd : α d = d := hfix2 β hβ d hmem
      have hδ : ∀ y, rootDiagAutHom .E6 K (A β) y = d * y * d⁻¹ := fun y => Subtype.ext rfl
      refine MulEquiv.ext fun x => ?_
      rw [MulAut.mul_apply, MulAut.mul_apply, hδ, hδ, map_mul α, map_mul α, map_inv α, hαd]

end CFSG.StandardType.KGCentE6

end

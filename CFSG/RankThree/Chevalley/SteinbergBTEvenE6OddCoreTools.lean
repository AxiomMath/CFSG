module

public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogEvenGraphField

public noncomputable section

namespace CFSG.RankThree.Chevalley

open CFSG.ComponentClassification.OuterAutomorphisms (inner)
open CFSG.ComponentClassification.UnbalancedCatalog (EvenCatalog.oddCore_eq_bot_of_mulEquiv
  EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer EvenCatalog.centralizerConjEquivMap
  EvenCatalog.inner_le_map_conj EvenCatalog.oddCore_eq_bot_of_isSimpleGroup)

theorem oddCore_inf_centralizer_eq_bot_of_simple {G : Type*} [Group G] {C J : Subgroup G}
    [Finite C] {η : MulAut C} (hη : η ^ 2 = 1) (hJC : J ≤ C) (hJs : IsSimpleGroup J)
    (hJe : Even (Nat.card J)) (hinj : Set.InjOn (MulAut.conj : C →* MulAut C) (J.subgroupOf C))
    (hNη : (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) ≤ Subgroup.centralizer {η})
    (hNnorm : (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C)).subgroupOf
      (Subgroup.centralizer {η})).Normal)
    (hcent : Subgroup.centralizer {η} ⊓ Subgroup.centralizer
      (((J.subgroupOf C).map (MulAut.conj : C →* MulAut C) : Subgroup (MulAut C)) :
        Set (MulAut C)) = Subgroup.zpowers η)
    (H : Subgroup (MulAut C)) (hIH : inner C ≤ H) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {η}) = ⊥ := by
  have : Finite (MulAut C) := Finite.of_injective (fun β : MulAut C => (β : C → C))
    fun _ _ h => MulEquiv.ext (congrFun h)
  have : Finite J := Finite.of_injective (fun x : J => (⟨x, hJC x.2⟩ : C))
    fun x y h => Subtype.ext (congrArg Subtype.val h :)
  set N := (J.subgroupOf C).map (MulAut.conj : C →* MulAut C) with hN
  let φ : ↥(J.subgroupOf C) →* N :=
    ((MulAut.conj : C →* MulAut C).comp (J.subgroupOf C).subtype).codRestrict N
      fun x => ⟨x, x.2, rfl⟩
  have hφ : Function.Bijective φ := by
    refine ⟨fun x y h => Subtype.ext (hinj x.2 y.2 (congrArg Subtype.val h)), ?_⟩
    rintro ⟨_, x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, rfl⟩
  have hNcore : CFSG.oddCore N = ⊥ := by
    have hJcore := @EvenCatalog.oddCore_eq_bot_of_isSimpleGroup J _ inferInstance hJs hJe
    exact EvenCatalog.oddCore_eq_bot_of_mulEquiv
      ((Subgroup.subgroupOfEquivOfLe hJC).symm.trans (MulEquiv.ofBijective φ hφ)) hJcore
  have hη2 : η * η = 1 := by rw [← sq, hη]
  refine EvenCatalog.oddCore_eq_bot_of_normal_of_centralizer (R := N) ?_ ?_ hNcore ?_
  · intro n hn
    refine Subgroup.mem_inf.2 ⟨hIH ?_, hNη hn⟩
    obtain ⟨j, -, rfl⟩ := hn
    exact ⟨j, rfl⟩
  · intro c hc n hn
    have h := hNnorm.conj_mem ⟨n, hNη hn⟩ (Subgroup.mem_subgroupOf.2 hn)
      ⟨c, (Subgroup.mem_inf.1 hc).2⟩
    exact Subgroup.mem_subgroupOf.1 h
  · intro c hc hcN
    have hc' : c ∈ Subgroup.centralizer {η} ⊓ Subgroup.centralizer (N : Set (MulAut C)) :=
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_inf.1 hc).2,
        Subgroup.mem_centralizer_iff.2 fun n hn => (hcN n hn).symm⟩
    rw [hcent] at hc'
    obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc'
    refine ⟨1, ?_⟩
    rw [pow_one, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, Nat.cast_ofNat, zpow_two, hη2,
      one_zpow]

theorem oddCore_inf_centralizer_conj_eq_bot {C : Type*} [Group C] {η : MulAut C}
    (h : ∀ H : Subgroup (MulAut C), inner C ≤ H → CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {η}) = ⊥)
    (H : Subgroup (MulAut C)) (hIH : inner C ≤ H) {α φ : MulAut C} (hα : φ * α * φ⁻¹ = η) :
    CFSG.oddCore ↥(H ⊓ Subgroup.centralizer {α}) = ⊥ := by
  have hα' : α = φ⁻¹ * η * φ⁻¹⁻¹ := by
    rw [← hα]
    group
  rw [hα']
  exact EvenCatalog.oddCore_eq_bot_of_mulEquiv (EvenCatalog.centralizerConjEquivMap H φ⁻¹ η).symm
    (h _ (EvenCatalog.inner_le_map_conj hIH φ⁻¹))

end CFSG.RankThree.Chevalley

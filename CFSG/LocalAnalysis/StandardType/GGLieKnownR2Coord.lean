module

public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.CoordProd
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.Normalizer
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.DegZero
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Defs
public import CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Detect.Heis.NormalForm
public import CFSG.HardMathSupport.Timmesfeld.Torality.FamilyBruhat
public import CFSG.LieType.Chevalley.EvenOddCentralizerRadicalPairing
public import CFSG.LieType.Chevalley.OrdinaryRootHyperplaneGeneration
public import CFSG.LieType.Chevalley.ParabolicRadicalNormalizer
public import CFSG.LieType.Chevalley.ParabolicRadicalsOpposite
public import CFSG.LinearAlgebra.LinearGroups.LinearTwo
public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherAutomorphismData
public import CFSG.Monster.B.Geometry.CoxeterWords
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import CFSG.Walter.Defs

public section

namespace CFSG.StandardType.LieKnownR2.Coord

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.SeitzReduction
  CFSG.HardMathSupport.Foote.Coordinator.SplitFrame.Heis

open Classical in
theorem pinnedX_conj_simplyLaced_param
    (τ : Tag) (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8)
    {F : Type} [CommRing F] (h2 : (2 : F) = 0) {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β)
    (hγ : IsRoot τ γ) (hne : γ ≠ β) (hne' : γ ≠ -β) (t c : F) :
    pinnedX τ F γ t * pinnedX τ F β c * (pinnedX τ F γ t)⁻¹ =
      (if IsRoot τ (γ + β) then pinnedX τ F (γ + β) (t * c) else 1) * pinnedX τ F β c := by
  obtain ⟨hroot, hnot⟩ := simply_laced_root_commutator_unit τ hτ hγ hβ hne hne'
  split_ifs with h
  · obtain ⟨hε, hf⟩ := hroot h
    have e := hf F t c
    have hneg : (-1 : F) = 1 := by linear_combination (-1 : F) * h2
    have hc : ((commConst τ γ β (1, 1) : ℤ) : F) * t * c = t * c := by
      rcases hε with hε | hε <;> rw [hε] <;> simp [hneg]
    rw [hc, commutatorElement_def] at e
    rw [← e]
    group
  · have hcomm := hnot h F _ (Subgroup.subset_closure ⟨t, rfl⟩) _ (Subgroup.subset_closure ⟨c, rfl⟩)
    rw [hcomm.eq, mul_inv_cancel_right, one_mul]

theorem conj_mem_Qθ
    {τ : Tag} {K : Type} [Field K] {g q : ModGL τ K} (hg : g ∈ Pθ τ K) (hq : q ∈ Qθ τ K) :
    g * q * g⁻¹ ∈ Qθ τ K :=
  (Subgroup.mem_normalizer_iff.1 (Pθ_le_normalizer_Qθ τ K hg) q).1 hq

theorem conj_mem_Uθ
    {τ : Tag} {K : Type} [Field K] {g u : ModGL τ K} (hg : g ∈ Pθ τ K) (hu : u ∈ Uθ τ K) :
    g * u * g⁻¹ ∈ Uθ τ K :=
  (Subgroup.mem_normalizer_iff.1 (Pθ_le_normalizer_Uθ τ K hg) u).1 hu

theorem pinnedX_mem_Pθ
    {τ : Tag} {K : Type} [Field K] {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγ0 : γ (iθ τ) = 0) (t : K) :
    pinnedX τ K γ t ∈ Pθ τ K :=
  Lθ_le_Pθ τ K (pinnedX_mem_Lθ_of_deg_zero hγ hγ0 t)

theorem prodX_mem_Qθ
    {τ : Tag} {K : Type} [Field K] {L : List (Fin τ.rank → ℤ)} (hL : ∀ β ∈ L, β ∈ Deg1 τ)
    (c : (Fin τ.rank → ℤ) → K) : CoordAux.prodX L c ∈ Qθ τ K := by
  induction L with
  | nil => rw [CoordAux.prodX_nil]; exact one_mem _
  | cons a L ih =>
    rw [CoordAux.prodX_cons]
    exact mul_mem (pinnedX_mem_Qθ_of_mem_Deg1 (hL a List.mem_cons_self) _)
      (ih fun b hb => hL b (List.mem_cons_of_mem _ hb))

open Classical in
theorem heisCoord_conj_pinnedX_param
    {τ : Tag} {K : Type} [Field K] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [CharP K 2]
    {γ β : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγ0 : γ (iθ τ) = 0) (hβ : β ∈ Deg1 τ) (t c : K) :
    heisCoord τ K (pinnedX τ K γ t * pinnedX τ K β c * (pinnedX τ K γ t)⁻¹) =
      Pi.single β c + if IsRoot τ (γ + β) then Pi.single (γ + β) (t * c) else 0 := by
  have hs := heisCoord_spec τ K
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have hβ1 := CoordAux.mem_Deg1.1 hβ
  have hne : γ ≠ β := fun h => by
    have := congrFun h (iθ τ)
    rw [hγ0, hβ1.2] at this
    exact absurd this (by norm_num)
  have hne' : γ ≠ -β := fun h => by
    have := congrFun h (iθ τ)
    rw [hγ0, Pi.neg_apply, hβ1.2] at this
    exact absurd this (by norm_num)
  rw [pinnedX_conj_simplyLaced_param τ hτ h2 hβ1.1 hγ hne hne' t c]
  split_ifs with h
  · have hγβ : γ + β ∈ Deg1 τ := CoordAux.mem_Deg1.2 ⟨h, by rw [Pi.add_apply, hγ0, hβ1.2, zero_add]⟩
    rw [hs.mul _ (pinnedX_mem_Qθ_of_mem_Deg1 hγβ (t * c)) _ (pinnedX_mem_Qθ_of_mem_Deg1 hβ c),
      hs.pinnedX_deg1 _ hγβ, hs.pinnedX_deg1 _ hβ, add_comm]
  · rw [one_mul, hs.pinnedX_deg1 _ hβ, add_zero]

open Classical in
theorem heisCoord_conj_prodX_param
    {τ : Tag} {K : Type} [Field K] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [CharP K 2]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγ0 : γ (iθ τ) = 0) (t : K)
    (c : (Fin τ.rank → ℤ) → K) :
    ∀ L : List (Fin τ.rank → ℤ), (∀ β ∈ L, β ∈ Deg1 τ) →
      heisCoord τ K (pinnedX τ K γ t * CoordAux.prodX L c * (pinnedX τ K γ t)⁻¹) =
        (L.map fun β => Pi.single β (c β) +
          if IsRoot τ (γ + β) then Pi.single (γ + β) (t * c β) else 0).sum
  | [], _ => by
    rw [CoordAux.prodX_nil, mul_one, mul_inv_cancel, heisCoord_one]
    simp
  | β :: L, hL => by
    have hβ := hL β List.mem_cons_self
    have hL' : ∀ b ∈ L, b ∈ Deg1 τ := fun b hb => hL b (List.mem_cons_of_mem _ hb)
    have hg := pinnedX_mem_Pθ (K := K) hγ hγ0 t
    have e : ∀ a P : ModGL τ K, pinnedX τ K γ t * (a * P) * (pinnedX τ K γ t)⁻¹ =
        (pinnedX τ K γ t * a * (pinnedX τ K γ t)⁻¹) *
          (pinnedX τ K γ t * P * (pinnedX τ K γ t)⁻¹) := fun a P => by group
    rw [CoordAux.prodX_cons, e, (heisCoord_spec τ K).mul _
      (conj_mem_Qθ hg (pinnedX_mem_Qθ_of_mem_Deg1 hβ _)) _ (conj_mem_Qθ hg (prodX_mem_Qθ hL' c)),
      heisCoord_conj_pinnedX_param hτ hγ hγ0 hβ, heisCoord_conj_prodX_param hτ hγ hγ0 t c L hL',
      List.map_cons, List.sum_cons]

open Classical in
theorem heisCoord_conj_param
    {τ : Tag} {K : Type} [Field K] (hτ : τ = .D4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) [CharP K 2]
    {γ : Fin τ.rank → ℤ} (hγ : IsRoot τ γ) (hγ0 : γ (iθ τ) = 0) {q : ModGL τ K}
    (hq : q ∈ Qθ τ K) (t : K) (ν : Fin τ.rank → ℤ) :
    heisCoord τ K (pinnedX τ K γ t * q * (pinnedX τ K γ t)⁻¹) ν =
      heisCoord τ K q ν +
        if ν - γ ∈ Deg1 τ ∧ IsRoot τ ν then t * heisCoord τ K q (ν - γ) else 0 := by
  obtain ⟨L, hnd, hLm⟩ := CoordAux.exists_list_Deg1 (τ := τ)
  have hD : ∀ β ∈ L, β ∈ Deg1 τ := fun β hβ => (hLm β).1 hβ
  have hs := heisCoord_spec τ K
  obtain ⟨u, hu, hqe⟩ := exists_prodX_of_support hnd hD hq
    (fun ν hν => hs.support q hq ν (fun h => hν ((hLm ν).2 h)))
  set c := heisCoord τ K q with hc
  set g := pinnedX τ K γ t with hgdef
  have hg := pinnedX_mem_Pθ (K := K) hγ hγ0 t
  have e : g * q * g⁻¹ = (g * u * g⁻¹) * (g * CoordAux.prodX L c * g⁻¹) := by
    conv_lhs => rw [hqe]
    group
  have hu0 : heisCoord τ K (g * u * g⁻¹) = 0 :=
    (hs.eq_zero_iff _ (Uθ_le_Qθ (conj_mem_Uθ hg hu))).2 (conj_mem_Uθ hg hu)
  rw [e, hs.mul _ (Uθ_le_Qθ (conj_mem_Uθ hg hu)) _ (conj_mem_Qθ hg (prodX_mem_Qθ hD c)), hu0,
    zero_add, heisCoord_conj_prodX_param hτ hγ hγ0 t c L hD, ← List.sum_toFinset _ hnd,
    Finset.sum_apply]
  simp only [Pi.add_apply, Finset.sum_add_distrib]
  congr 1
  · simp only [Pi.single_apply]
    rw [Finset.sum_ite_eq]
    split_ifs with h
    · rfl
    · exact (hs.support q hq ν (fun h' => h (List.mem_toFinset.2 ((hLm ν).2 h')))).symm
  · have : ∀ β ∈ L.toFinset, ((if IsRoot τ (γ + β) then Pi.single (γ + β) (t * c β) else 0 :
        (Fin τ.rank → ℤ) → K) ν) = if ν - γ = β then (if IsRoot τ ν then t * c β else 0) else 0 := by
      intro β _
      by_cases hνβ : ν - γ = β
      · subst hνβ
        simp only [add_sub_cancel, if_true]
        split_ifs <;> simp
      · rw [if_neg hνβ]
        split_ifs with hr
        · rw [Pi.single_apply, if_neg]
          rintro rfl
          exact hνβ (by abel)
        · rfl
    rw [Finset.sum_congr rfl this, Finset.sum_ite_eq]
    by_cases h1 : ν - γ ∈ Deg1 τ <;> by_cases h2 : IsRoot τ ν <;> simp [h1, h2, hLm]

end CFSG.StandardType.LieKnownR2.Coord

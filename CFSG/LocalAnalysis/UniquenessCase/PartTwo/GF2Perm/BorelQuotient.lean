module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.Witness
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbNodes
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm.Core
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbCore
import CFSG.LocalAnalysis.AGLEmbeddingD2.Tits.GN516.GOrbIndepLie
import CFSG.LocalAnalysis.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.CoverOneParab
import CFSG.GH74.GLS.SP.DatumBN

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

open CFSG.LieType.Universal CFSG.LieType.CurtisTits CFSG.LieType.Steinberg
  CFSG.AGLEmbedding.ParabHub CFSG.AGLEmbeddingD2.Tits.MsideParabolicEscape.MinPar
  CFSG.AGLEmbeddingD2.Tits.GN516.Nodes CFSG.AGLEmbeddingD2.Tits.GN516.Core
  CFSG.AGLEmbeddingD2.Tits.GN516.Levi CFSG.AGLEmbeddingD2.Tits.GN516.Indep

variable {K G : Type} [Group K] [Finite K] [Group G] [Finite G] {D : UniversalRootDatum K}
  {n : Fin D.rank → K} {H : Fin D.rank → Subgroup K} {π : K →* G} {M : ℕ}

@[expose] noncomputable def endNodesThree (D : UniversalRootDatum K)
    (H : Fin D.rank → Subgroup K) : Set (Fin D.rank) :=
  {j | (TauCeti.diagramGraph D.cartan).degree j = 1 ∧
    Nat.card (parJ D H {j}) = 3 * Nat.card (borel D H)}

theorem nodePerm_image_endNodesThree (h : BorelQuotient D n H π M) (α : MulAut G)
    (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π) :
    nodePerm h α hα '' endNodesThree D H = endNodesThree D H := by
  classical
  have hsub : Set.MapsTo (nodePerm h α hα) (endNodesThree D H) (endNodesThree D H) := by
    intro j hj
    obtain ⟨hdeg, hcard⟩ := hj
    refine ⟨?_, ?_⟩
    · have hd : (TauCeti.diagramGraph D.cartan).degree ((nodePerm h α hα) j) =
          (TauCeti.diagramGraph D.cartan).degree j :=
        SimpleGraph.Iso.degree_eq
          { toEquiv := nodePerm h α hα
            map_rel_iff' := fun {a b} => nodePerm_adj_iff h α hα a b } j
      rw [hd]
      exact hdeg
    · rw [card_parJ_nodePerm h α hα j]
      exact hcard
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact hsub hy
  · intro hx
    have hsymm : Set.MapsTo (nodePerm h α hα).symm (endNodesThree D H) (endNodesThree D H) :=
      (nodePerm h α hα).perm_symm_mapsTo_of_mapsTo hsub
    exact ⟨_, hsymm hx, (nodePerm h α hα).apply_symm_apply x⟩

omit [Finite K] in
theorem cartan_eq_zero_of_degree_eq_one (hconn : (TauCeti.diagramGraph D.cartan).Connected)
    (hr : 3 ≤ D.rank) {j k : Fin D.rank} (hj : (TauCeti.diagramGraph D.cartan).degree j = 1)
    (hk : (TauCeti.diagramGraph D.cartan).degree k = 1) (hjk : j ≠ k) : D.cartan j k = 0 := by
  classical
  by_contra hne
  have hadj : (TauCeti.diagramGraph D.cartan).Adj j k :=
    D.isFiniteType.diagramGraph_adj_iff.2 ⟨hjk, hne⟩
  have huniqj : ∀ v, (TauCeti.diagramGraph D.cartan).Adj j v → v = k := by
    obtain ⟨w, _, huniq⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj).1 hj
    intro v hv
    exact (huniq v hv).trans (huniq k hadj).symm
  have huniqk : ∀ v, (TauCeti.diagramGraph D.cartan).Adj k v → v = j := by
    obtain ⟨w, _, huniq⟩ := (SimpleGraph.degree_eq_one_iff_existsUnique_adj).1 hk
    intro v hv
    exact (huniq v hv).trans (huniq j hadj.symm).symm
  have hclosure : ∀ {u v : Fin D.rank}, u ∈ ({j, k} : Set (Fin D.rank)) →
      (TauCeti.diagramGraph D.cartan).Adj u v → v ∈ ({j, k} : Set (Fin D.rank)) := by
    intro u v hu huv
    rcases hu with rfl | rfl
    · exact Or.inr (huniqj v huv)
    · exact Or.inl (huniqk v huv)
  have hall : ∀ x : Fin D.rank, x ∈ ({j, k} : Set (Fin D.rank)) := by
    intro x
    obtain ⟨p⟩ := hconn.set_univ_walk_nonempty j x
    exact p.recOn (motive := fun u v _ => u ∈ ({j, k} : Set (Fin D.rank)) →
      v ∈ ({j, k} : Set (Fin D.rank))) (fun {_} hu => hu)
      (fun h _ ih hu => ih (hclosure hu h)) (Or.inl rfl)
  have hcard : Fintype.card (Fin D.rank) ≤ 2 := by
    have hsub : (Finset.univ : Finset (Fin D.rank)) ⊆ {j, k} := by
      intro x _
      simpa using hall x
    calc Fintype.card (Fin D.rank) = (Finset.univ : Finset (Fin D.rank)).card := rfl
      _ ≤ ({j, k} : Finset (Fin D.rank)).card := Finset.card_le_card hsub
      _ = 2 := by rw [Finset.card_pair hjk]
  rw [Fintype.card_fin] at hcard
  omega

omit [Finite G] in
private theorem card_map_rankOne_of_card_six (h : BorelQuotient D n H π M) {j : Fin D.rank}
    (h6 : Nat.card (rankOne D.rootGroup j) = 6)
    (hnc : ∃ a ∈ rankOne D.rootGroup j, ∃ b ∈ rankOne D.rootGroup j, a * b ≠ b * a) :
    Nat.card ↥((rankOne D.rootGroup j).map π) = Nat.card ↥(rankOne D.rootGroup j) := by
  have hinj : Set.InjOn (π : K → G) ↑(rankOne D.rootGroup j) := by
    intro x hx y hy hxy
    have hker : x * y⁻¹ ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hxy, mul_inv_cancel]
    have hmem : x * y⁻¹ ∈ rankOne D.rootGroup j :=
      Subgroup.mul_mem _ hx (Subgroup.inv_mem _ hy)
    have h1 : x * y⁻¹ = 1 :=
      CFSG.AGLEmbeddingD2.McLaughlin.Lie.eq_one_of_central_of_card_six h6 hnc hmem
        fun l _ => (Subgroup.mem_center_iff.1 (h.ker_central _ hker) l).symm
    exact mul_inv_eq_one.1 h1
  have h := Set.InjOn.ncard_image hinj
  change Nat.card ↑(((rankOne D.rootGroup j).map π : Set G)) =
    Nat.card ↑(((rankOne D.rootGroup j) : Set K))
  rw [Nat.card_coe_set_eq, Nat.card_coe_set_eq, Subgroup.coe_map]
  exact h

theorem permWitness_of_borelQuotient (h : BorelQuotient D n H π M) (hM : M ∣ 3)
    {J : Set (Fin D.rank)}
    (hJ : ∀ (α : MulAut G)
      (hα : ((posUnipotent D).map π).map α.toMonoidHom = (posUnipotent D).map π),
      nodePerm h α hα '' J = J)
    (h6 : ∀ j ∈ J, Nat.card (rankOne D.rootGroup j) = 6 ∧
      ∃ a ∈ rankOne D.rootGroup j, ∃ b ∈ rankOne D.rootGroup j, a * b ≠ b * a)
    (horth : ∀ j ∈ J, ∀ k ∈ J, j ≠ k → D.cartan j k = 0)
    {E : Subgroup G} (hEP : E ≤ (parJ D H J).map π) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) :
    PermWitness G := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hU2 : IsPGroup 2 ((posUnipotent D).map π) := (isPGroup_posUnipotent h).map π
  have hidx : ¬ 2 ∣ ((posUnipotent D).map π).index := fun hd =>
    h.not_dvd_index (hd.trans (Subgroup.index_map_dvd (posUnipotent D) (f := π) h.surj))
  let U₀ : Sylow 2 G := hU2.toSylow hidx
  have hU₀ : (U₀ : Subgroup G) = (posUnipotent D).map π := IsPGroup.toSylow_coe hU2 hidx
  refine permWitness_of_permWitnessAt U₀ ?_
  refine permWitnessAt_of_generators (ι := Fin D.rank) (W := (parJ D H J).map π)
    (V := (unipRad D J).map π) (T := (⨆ i, H i).map π) (J := J)
    (L := fun j => (rankOne D.rootGroup j).map π) (E := E) U₀
    ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · rw [hU₀]
    exact Subgroup.map_mono (posUnipotent_le_borel.trans (borel_le_parJ J))
  · intro φ hφ
    have hφ' : ((posUnipotent D).map π).map φ.toMonoidHom = (posUnipotent D).map π := by
      simpa [hU₀] using hφ
    have hW := map_parJ_nodePerm h φ hφ' J
    rwa [hJ φ hφ'] at hW
  · have hK : parJ D H J = unipRad D J ⊔ (⨆ i, H i) ⊔
        ⨆ j ∈ J, rankOne D.rootGroup j := by
      rw [parJ_eq_sup, unipJ_eq_sup h.ct h.extras J]
      simp only [sup_assoc, sup_comm]
    rw [hK, Subgroup.map_sup, Subgroup.map_sup]
    simp only [Subgroup.map_iSup]
  · exact ((isPGroup_posUnipotent h).to_le (unipRad_le_posUnipotent J)).map π
  · exact (Subgroup.map_mono (parJ_le_normalizer_unipRad h.ct h.extras J)).trans
      (Subgroup.le_normalizer_map π)
  · intro x hx y hy
    obtain ⟨s, hs, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hy
    simpa only [map_mul] using congrArg π (CFSG.GH74.GLS.SP.commute_of_mem_iSup h.extras hs ht).eq
  · intro x hx
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨c, hc⟩ := hM
    have h3 : t ^ 3 = 1 := by
      rw [hc, pow_mul, h.pow_eq_one_of_mem_iSup ht, one_pow]
    rw [← map_pow, h3, map_one]
  · intro j hj
    rw [card_map_rankOne_of_card_six h (h6 j hj).1 (h6 j hj).2, (h6 j hj).1]
  · intro j hj k hk hjk x hx y hy
    obtain ⟨x', hx', rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨y', hy', rfl⟩ := Subgroup.mem_map.mp hy
    have hc := map_rankOne_le_centralizer h hjk (horth j hj k hk hjk)
      (Subgroup.mem_map_of_mem π hx')
    exact (Subgroup.mem_centralizer_iff.1 hc (π y') (Subgroup.mem_map_of_mem π hy')).symm
  · intro j hj x hx y hy
    obtain ⟨t, ht, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.mp hy
    simpa only [map_mul] using congrArg π
      (CFSG.AGLEmbeddingD2.McLaughlin.TightPairAndPureRank.iSup_torus_le_centralizer
        h (h6 j hj).1 t ht g hg)
  · exact hEP
  · exact hE.2
  · exact hE9

theorem permWitness_of_borelQuotient_singleton (h : BorelQuotient D n H π M) (hM : M ∣ 3)
    {a : Fin D.rank} (hend : endNodesThree D H = {a})
    (h6 : Nat.card (rankOne D.rootGroup a) = 6 ∧
      ∃ x ∈ rankOne D.rootGroup a, ∃ y ∈ rankOne D.rootGroup a, x * y ≠ y * x)
    {E : Subgroup G} (hEP : E ≤ (parJ D H {a}).map π) (hE : CFSG.Open.IsElemAbelian 3 E)
    (hE9 : Nat.card E = 9) :
    PermWitness G := by
  refine permWitness_of_borelQuotient h hM (J := {a}) (fun α hα => ?_) (fun j hj => ?_)
    (fun j hj k hk hjk => absurd ((Set.mem_singleton_iff.1 hj).trans
      (Set.mem_singleton_iff.1 hk).symm) hjk) hEP hE hE9
  · rw [← hend]
    exact nodePerm_image_endNodesThree h α hα
  · rw [Set.mem_singleton_iff.1 hj]
    exact h6

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.GF2Perm

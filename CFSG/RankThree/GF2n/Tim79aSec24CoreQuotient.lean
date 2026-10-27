module

public import CFSG.RankThree.GF2n.Tim79aRootStatements

public section

namespace CFSG.RankThree.GF2n.Tim79a

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.BenderSuzuki CFSG.Timmesfeld.ARS
  CFSG.Timmesfeld.Transvection
open CFSG.StronglyEmbedded.BenderCentre
open CFSG.ComponentClassification.AschbacherToolkit.Bender (sylowCenter)

theorem map_pCoreOf_comap_eq_of_ker_le_center {Y Yb : Type*} [Group Y] [Group Yb] [Finite Y]
    {p : ℕ} [Fact p.Prime] (π : Y →* Yb) (hπ : Function.Surjective π)
    (hker : π.ker ≤ Subgroup.center Y) (Nb : Subgroup Yb) :
    (pCoreOf p (Nb.comap π)).map π = pCoreOf p Nb := by
  haveI : Finite Yb := Finite.of_surjective π hπ
  set N : Subgroup Y := Nb.comap π with hN
  refine le_antisymm ?_ ?_
  · refine CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer p ?_ ?_ ?_
    · rintro _ ⟨x, hx, rfl⟩
      exact Subgroup.mem_comap.mp (CFSG.LieType.BorelTits.pCoreOf_le p N hx)
    · intro y hy
      obtain ⟨yt, rfl⟩ := hπ y
      exact Subgroup.le_normalizer_map π ⟨yt,
        CFSG.LieType.BorelTits.le_normalizer_pCoreOf p N (Subgroup.mem_comap.mpr hy), rfl⟩
    · exact (CFSG.LieType.BorelTits.pCoreOf_isPGroup p N).map π
  · set Ob : Subgroup Yb := pCoreOf p Nb with hOb
    have hObN : Ob ≤ Nb := CFSG.LieType.BorelTits.pCoreOf_le p Nb
    have hOb2 : IsPGroup p Ob := CFSG.LieType.BorelTits.pCoreOf_isPGroup p Nb
    set T : Subgroup ↥N := (Ob.comap π).subgroupOf N with hT
    have hmemT : ∀ t : ↥N, t ∈ T ↔ π (t : Y) ∈ Ob := fun t => by
      rw [hT, Subgroup.mem_subgroupOf, Subgroup.mem_comap]
    have hTn : T.Normal := by
      refine ⟨fun t ht n => ?_⟩
      rw [hmemT] at ht ⊢
      have hn : π (n : Y) ∈ Nb := n.2
      have h1 := (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf p Nb hn) (π (t : Y))).mp ht
      simpa using h1
    let φ : ↥T →* ↥Ob := ((π.comp N.subtype).comp T.subtype).codRestrict Ob
      (fun t => (hmemT (t : ↥N)).mp t.2)
    have hφ : ∀ t : ↥T, ((φ t : ↥Ob) : Yb) = π ((t : ↥N) : Y) := fun t => rfl
    have hφs : Function.Surjective φ := by
      rintro ⟨o, ho⟩
      obtain ⟨y, rfl⟩ := hπ o
      have hyN : y ∈ N := hObN ho
      refine ⟨⟨⟨y, hyN⟩, (hmemT ⟨y, hyN⟩).mpr ho⟩, Subtype.ext ?_⟩
      rfl
    haveI : Group.IsNilpotent ↥Ob := hOb2.isNilpotent
    have hTnil : Group.IsNilpotent ↥T := by
      refine isNilpotent_of_ker_le_center φ fun t ht => ?_
      have ht1 : π ((t : ↥N) : Y) = 1 := by
        rw [← hφ, MonoidHom.mem_ker.mp ht]
        rfl
      have htc : ((t : ↥N) : Y) ∈ Subgroup.center Y := hker (MonoidHom.mem_ker.mpr ht1)
      rw [Subgroup.mem_center_iff]
      intro s
      apply Subtype.ext
      apply Subtype.ext
      exact Subgroup.mem_center_iff.mp htc ((s : ↥N) : Y)
    obtain ⟨S⟩ := (inferInstance : Nonempty (Sylow p ↥T))
    have hSle : (S : Subgroup ↥T).map T.subtype ≤ pCore p ↥N := Sylow.map_le_pCore hTn hTnil p S
    have htop : (S : Subgroup ↥T).map φ = ⊤ := by
      have h := (Sylow.mapSurjective hφs S).is_maximal' (hOb2.to_subgroup ⊤) le_top
      rw [Sylow.coe_mapSurjective] at h
      exact h.symm
    intro o ho
    have hmem : (⟨o, ho⟩ : ↥Ob) ∈ (S : Subgroup ↥T).map φ := by
      rw [htop]
      exact Subgroup.mem_top _
    obtain ⟨s, hs, hso⟩ := Subgroup.mem_map.mp hmem
    refine ⟨((s : ↥N) : Y), ?_, ?_⟩
    · rw [CFSG.openPCoreOf_eq_map_pCore]
      exact ⟨(s : ↥N), hSle ⟨s, hs, rfl⟩, rfl⟩
    · rw [← hφ, hso]

theorem pCoreOf_subgroupOf_of_le {Γ : Type*} [Group Γ] (p : ℕ) {X K : Subgroup Γ}
    (hKX : K ≤ X) : pCoreOf p (K.subgroupOf X) = (pCoreOf p K).subgroupOf X := by
  let ψ : ↥(K.subgroupOf X) ≃* ↥K := Subgroup.subgroupOfEquivOfLe hKX
  have hcomp : K.subtype.comp ψ.toMonoidHom = X.subtype.comp (K.subgroupOf X).subtype := by
    ext z
    rfl
  have hsub : ∀ L : Subgroup ↥X, (L.map X.subtype).subgroupOf X = L := fun L =>
    Subgroup.comap_map_eq_self_of_injective X.subtype_injective L
  rw [CFSG.openPCoreOf_eq_map_pCore, CFSG.openPCoreOf_eq_map_pCore, ← CFSG.pCore_map_iso p ψ,
    Subgroup.map_map, hcomp, ← Subgroup.map_map, hsub]

variable {G : Type} [Group G]

theorem VZ_mem_rootClassZ (V H : Subgroup G) : VZ V H ∈ rootClassZ V H :=
  ⟨1, (CFSG.Timmesfeld.ARS.conjSub_one _).symm⟩

theorem benderRootOfTwoStatement_holds : BenderRootOfTwoStatement := by
  intro G _ _ M V Q P H _ hTwo
  rcases hTwo with ⟨f, hf, -, ⟨e⟩, S, hS⟩ | ⟨n, hn, -, ⟨e⟩, S, hS⟩ | ⟨f, hf, -, ⟨e⟩, S, hS⟩
  · exact ⟨.isPSL2 f hf e, S, (sylowCenter_eq_of_psl2 hf e S).trans hS⟩
  · exact ⟨.isSuzuki n hn e, S, (map_center_eq S).symm.trans hS.symm⟩
  · exact ⟨.isPSU3 f hf e, S, (map_center_eq S).symm.trans hS.symm⟩

theorem classicalRootOfKindStatement_holds : ClassicalRootOfKindStatement := by
  intro G _ _ M V Q P H _ hk
  rcases hk with ⟨f, hf, -, hSp⟩ | ⟨f, hf, -, hSU⟩
  · exact Or.inl ⟨f, rootClassZ V H, hf, hSp, VZ_mem_rootClassZ V H⟩
  · exact Or.inr ⟨f, hf, rootClassZ V H, hSU, VZ_mem_rootClassZ V H⟩

theorem rootPairOfKindStatement_holds : RootPairOfKindStatement :=
  rootPairOfKind_of_parts benderRootOfTwoStatement_holds classicalRootOfKindStatement_holds

end CFSG.RankThree.GF2n.Tim79a

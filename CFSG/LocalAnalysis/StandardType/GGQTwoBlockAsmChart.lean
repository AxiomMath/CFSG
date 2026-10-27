module

public import CFSG.LocalAnalysis.StandardType.GGQTwoBlockHubDefs
import CFSG.LocalAnalysis.StandardType.GGQTwoSU34
import CFSG.LocalAnalysis.GLTheoremA.CatA.S267BadExcTwE6ConcSU

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalInvolution.Phan CFSG.ClassicalInvolution.Balance.StrongBalance.Unitary

variable {K : Type} [Field K] [Finite K] [CharP K 2] {m N : ℕ} {G : Type} [Group G]
  {H : Subgroup G}

private theorem qTwoChartCommon_exists_extend {k : ℕ} (hkm : k ≤ m) (hmN : m ≤ N)
    (g : Fin k ↪ Fin N) : ∃ ε : Fin m ↪ Fin N, ∀ i : Fin k, ε (Fin.castLEEmb hkm i) = g i := by
  classical
  have hkN : k ≤ N := hkm.trans hmN
  have hN : (N : ℕ∞) ≤ ENat.card (Fin N) := by
    simp
  obtain ⟨x, hx⟩ :=
    Fin.Embedding.restrictSurjective_of_le_ENatCard (α := Fin N) (m := k) (n := N) hkN hN g
  refine ⟨(Fin.castLEEmb hmN).trans x, fun i => ?_⟩
  have hcast : Fin.castLEEmb hmN (Fin.castLEEmb hkm i) = Fin.castLEEmb hkN i := by
    rw [Fin.castLEEmb_apply, Fin.castLEEmb_apply, Fin.castLEEmb_apply]
    exact congrFun (Fin.castLE_comp_castLE hkm hmN) i
  have hx' : ∀ i : Fin k, x (Fin.castLEEmb hkN i) = g i := fun i =>
    congrArg (fun e : Fin k ↪ Fin N => e i) hx
  exact (congrArg x hcast).trans (hx' i)

namespace QTwoCanonBlocks

theorem exists_chart_of_embedding (B : QTwoCanonBlocks K m N H) {k : ℕ} (hkm : k ≤ m)
    (hmN : m ≤ N) (g : Fin k ↪ Fin N) :
    ∃ φ : Su K 2 1 m →* G, φ.ker ≤ Subgroup.center (Su K 2 1 m) ∧
      ∀ J : Finset (Fin k), 2 ≤ J.card → J.card ≤ 4 →
        B.blk (J.map g) = (coordBlockSU K 2 1 (J.map (Fin.castLEEmb hkm))).map φ := by
  classical
  obtain ⟨ε, hε⟩ := qTwoChartCommon_exists_extend hkm hmN g
  obtain ⟨φ, hker, hφ⟩ := B.chart ε
  have hε' : (Fin.castLEEmb hkm).trans ε = g :=
    Function.Embedding.ext fun i => hε i
  refine ⟨φ, hker, fun J hJ2 hJ4 => ?_⟩
  set J' := J.map (Fin.castLEEmb hkm) with hJ'
  have hJ'2 : 2 ≤ J'.card := by rw [hJ', Finset.card_map]; exact hJ2
  have hJ'4 : J'.card ≤ 4 := by rw [hJ', Finset.card_map]; exact hJ4
  have hJg : J'.map ε = J.map g := by rw [hJ', Finset.map_map, hε']
  rw [← hJg, hφ J' hJ'2 hJ'4]

private theorem qTwoChartCommon_chart_of_finset (B : QTwoCanonBlocks K m N H) (hmN : m ≤ N)
    (S : Finset (Fin N)) (hS : S.card ≤ m) :
    ∃ φ : Su K 2 1 m →* G, φ.ker ≤ Subgroup.center (Su K 2 1 m) ∧
      ∃ c : Finset (Fin N) → Finset (Fin m),
        (∀ T : Finset (Fin N), T ⊆ S → (c T).card = T.card) ∧
        (∀ T : Finset (Fin N), T ⊆ S → 2 ≤ T.card → T.card ≤ 4 →
          B.blk T = (coordBlockSU K 2 1 (c T)).map φ) ∧
        (∀ T₁ T₂ : Finset (Fin N), T₁ ⊆ S → T₂ ⊆ S →
          c (T₁ ∪ T₂) = c T₁ ∪ c T₂) ∧
        (∀ T₁ T₂ : Finset (Fin N), T₁ ⊆ S → T₂ ⊆ S →
          Disjoint T₁ T₂ → Disjoint (c T₁) (c T₂)) := by
  classical
  let g : Fin S.card ↪ Fin N := (S.orderEmbOfFin rfl).toEmbedding
  have hrange : Set.range g = (S : Set (Fin N)) := by
    simp [g]
  obtain ⟨φ, hker, hφ⟩ := exists_chart_of_embedding B hS hmN g
  let c : Finset (Fin N) → Finset (Fin m) := fun T =>
    (T.preimage g g.injective.injOn).map (Fin.castLEEmb hS)
  have hpre : ∀ T : Finset (Fin N), T ⊆ S →
      (T.preimage g g.injective.injOn).map g = T := by
    intro T hTS
    rw [Finset.map_eq_image, Finset.image_preimage]
    ext x
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.1, fun hx => ⟨hx, hrange ▸ hTS hx⟩⟩
  have hcardpre : ∀ T : Finset (Fin N), T ⊆ S →
      (T.preimage g g.injective.injOn).card = T.card := by
    intro T hTS
    calc
      (T.preimage g g.injective.injOn).card =
          ((T.preimage g g.injective.injOn).map g).card := (Finset.card_map g).symm
      _ = T.card := by rw [hpre T hTS]
  refine ⟨φ, hker, c, ?_, ?_, ?_, ?_⟩
  · intro T hTS
    calc
      (c T).card = (T.preimage g g.injective.injOn).card := Finset.card_map _
      _ = T.card := hcardpre T hTS
  · intro T hTS hT2 hT4
    have hT'2 : 2 ≤ (T.preimage g g.injective.injOn).card := by
      rw [hcardpre T hTS]; exact hT2
    have hT'4 : (T.preimage g g.injective.injOn).card ≤ 4 := by
      rw [hcardpre T hTS]; exact hT4
    have h := hφ (T.preimage g g.injective.injOn) hT'2 hT'4
    rwa [hpre T hTS] at h
  · intro T₁ T₂ hT₁ hT₂
    simp only [c]
    rw [Finset.preimage_union, Finset.map_union]
  · intro T₁ T₂ hT₁ hT₂ hd
    simp only [c]
    exact (Finset.disjoint_map (Fin.castLEEmb hS)).mpr (Finset.disjoint_preimage hd)

theorem commute_of_disjoint (B : QTwoCanonBlocks K m N H) (hmN : m ≤ N) {I J : Finset (Fin N)}
    (hIJ : Disjoint I J) (hcard : (I ∪ J).card ≤ m) (hI : 2 ≤ I.card) (hI4 : I.card ≤ 4)
    (hJ : 2 ≤ J.card) (hJ4 : J.card ≤ 4) :
    ∀ x ∈ B.blk I, ∀ y ∈ B.blk J, x * y = y * x := by
  classical
  obtain ⟨φ, -, c, -, hblk, -, hdisj⟩ :=
    qTwoChartCommon_chart_of_finset B hmN (I ∪ J) hcard
  have hIeq := hblk I Finset.subset_union_left hI hI4
  have hJeq := hblk J Finset.subset_union_right hJ hJ4
  have hd : Disjoint (c I) (c J) :=
    hdisj I J Finset.subset_union_left Finset.subset_union_right hIJ
  intro x hx y hy
  rw [hIeq] at hx
  rw [hJeq] at hy
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hx
  obtain ⟨b, hb, rfl⟩ := Subgroup.mem_map.mp hy
  have hsub : c J ⊆ (c I)ᶜ := by
    intro z hz
    simp only [Finset.mem_compl]
    exact fun hzI => Finset.disjoint_left.mp hd hzI hz
  have hcomm :=
    CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc.commute_of_mem_coordBlockSU
      ha (CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc.coordBlockSU_mono hsub hb)
  calc
    φ a * φ b = φ (a * b) := by rw [map_mul]
    _ = φ (b * a) := by rw [hcomm]
    _ = φ b * φ a := by rw [map_mul]

theorem blk_le_of_subset (B : QTwoCanonBlocks K m N H) (hmN : m ≤ N) {I J : Finset (Fin N)}
    (hJI : J ⊆ I) (hJ : 2 ≤ J.card) (hI4 : I.card ≤ 4) (hIm : I.card ≤ m) :
    B.blk J ≤ B.blk I := by
  classical
  obtain ⟨φ, -, c, -, hblk, hunion, -⟩ := qTwoChartCommon_chart_of_finset B hmN I hIm
  have hJI' : J.card ≤ I.card := Finset.card_le_card hJI
  have hIeq := hblk I (Finset.Subset.refl _) (hJ.trans hJI') hI4
  have hJeq := hblk J hJI hJ (hJI'.trans hI4)
  have hcJI : c J ⊆ c I := by
    have h := hunion J I hJI (Finset.Subset.refl _)
    rw [Finset.union_eq_right.2 hJI] at h
    calc c J ⊆ c J ∪ c I := Finset.subset_union_left
      _ = c I := h.symm
  rw [hIeq, hJeq]
  exact Subgroup.map_mono
    (CFSG.LocalAnalysis.GLTheoremA.S267.BadExc.TwE6Conc.coordBlockSU_mono hcJI)

theorem sup_eq_of_card_three (hK : Nat.card K = 4) (B : QTwoCanonBlocks K m N H) (hmN : m ≤ N)
    (hm : 4 ≤ m) {I J : Finset (Fin N)} (hI : I.card = 3) (hJ : J.card = 3)
    (hIJ : (I ∪ J).card = 4) : B.blk I ⊔ B.blk J = B.blk (I ∪ J) := by
  classical
  have hS : (I ∪ J).card ≤ m := by omega
  obtain ⟨φ, -, c, hcard, hblk, hunion, -⟩ :=
    qTwoChartCommon_chart_of_finset B hmN (I ∪ J) hS
  have hIeq := hblk I Finset.subset_union_left (by omega) (by omega)
  have hJeq := hblk J Finset.subset_union_right (by omega) (by omega)
  have hIJe := hblk (I ∪ J) (Finset.Subset.refl _) (by omega) (by omega)
  have hun := hunion I J Finset.subset_union_left Finset.subset_union_right
  have hcI : (c I).card = 3 := by rw [hcard I Finset.subset_union_left, hI]
  have hcJ : (c J).card = 3 := by rw [hcard J Finset.subset_union_right, hJ]
  have hcIJ : (c (I ∪ J)).card = 4 := by
    rw [hcard (I ∪ J) (Finset.Subset.refl _), hIJ]
  have hcU : (c I ∪ c J).card = 4 := by rw [← hun, hcIJ]
  have hsup : coordBlockSU K 2 1 (c I) ⊔ coordBlockSU K 2 1 (c J) =
      coordBlockSU K 2 1 (c I ∪ c J) := coordBlockSU_sup_three hK hcI hcJ hcU
  calc
    B.blk I ⊔ B.blk J =
        (coordBlockSU K 2 1 (c I)).map φ ⊔ (coordBlockSU K 2 1 (c J)).map φ := by
      rw [hIeq, hJeq]
    _ = (coordBlockSU K 2 1 (c I) ⊔ coordBlockSU K 2 1 (c J)).map φ := by
      rw [Subgroup.map_sup]
    _ = (coordBlockSU K 2 1 (c I ∪ c J)).map φ := by rw [hsup]
    _ = (coordBlockSU K 2 1 (c (I ∪ J))).map φ := by rw [hun]
    _ = B.blk (I ∪ J) := hIJe.symm

end QTwoCanonBlocks

end CFSG.StandardType.QTwo

end

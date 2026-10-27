module

public import CFSG.Quasithin.Vol2.Ch12Sec6P31PropAStar
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.Quasithin.EmptyFaithful.S153DGen
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.Quasithin.H13.P31Sz

open CFSG.Open CFSG.Blueprint CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.F126 S126 S126P31
open scoped IsMulCommutative

section Star

variable {G : Type} [Group G] {H : Subgroup G}

theorem star_map_conj {X : Subgroup G} {g : G} (hg : g ∈ H) :
    star H (X.map (MulAut.conj g).toMonoidHom) =
      (star H X).map (MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : HStar H)).toMonoidHom := by
  unfold S126.star
  have e1 : (X.map (MulAut.conj g).toMonoidHom).subgroupOf H =
      (X.subgroupOf H).map (MulAut.conj (⟨g, hg⟩ : ↥H)).toMonoidHom := by
    ext x
    rw [Subgroup.mem_subgroupOf, A38.mem_map_conj, A38.mem_map_conj, Subgroup.mem_subgroupOf]
    rfl
  have e2 : (MulAut.conj (QuotientGroup.mk ⟨g, hg⟩ : HStar H)).toMonoidHom.comp
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)) =
      (QuotientGroup.mk' (CFSG.pCore 2 ↥H)).comp (MulAut.conj (⟨g, hg⟩ : ↥H)).toMonoidHom := by
    ext x
    simp [MulAut.conj_apply]
  rw [e1, Subgroup.map_map, Subgroup.map_map, e2]

theorem star_pCoreOf_eq_bot : star H (pCoreOf 2 H) = ⊥ := by
  rw [eq_bot_iff]
  rintro _ ⟨a, ha, rfl⟩
  rw [Subgroup.mem_bot]
  exact F126.mkH_eq_one_iff.2 (Subgroup.mem_subgroupOf.1 ha)

theorem commute_star_of_commutator_le {X Y : Subgroup G} (hX : X ≤ H) (hY : Y ≤ H)
    (h : ⁅X, Y⁆ ≤ pCoreOf 2 H) : ∀ a ∈ star H X, ∀ b ∈ star H Y, a * b = b * a := by
  have h1 : ⁅star H X, star H Y⁆ = ⊥ := by
    rw [← P31A.star_commutator hX hY, eq_bot_iff, ← star_pCoreOf_eq_bot (H := H)]
    exact S126P31.star_mono h
  intro a ha b hb
  have h2 := Subgroup.commutator_eq_bot_iff_le_centralizer.1 h1 ha
  exact (Subgroup.mem_centralizer_iff.1 h2 b hb).symm

theorem mk_mem_normalizer_star {X : Subgroup G} (hXH : X ≤ H) {s : ↥H}
    (hs : (s : G) ∈ Subgroup.normalizer (X : Set G)) :
    (QuotientGroup.mk s : HStar H) ∈ Subgroup.normalizer (star H X : Set (HStar H)) := by
  have hZ : Subgroup.zpowers (s : G) ≤ H := (Subgroup.zpowers_le).2 s.2
  have hZN : Subgroup.zpowers (s : G) ≤ Subgroup.normalizer (X : Set G) :=
    (Subgroup.zpowers_le).2 hs
  exact S126P31.star_le_normalizer_star hXH hZ hZN
    (S126P31.mk_mem_star (Subgroup.mem_zpowers (s : G)))

end Star

section Finite

variable {G : Type} [Group G] [Finite G] {H : Subgroup G}

theorem mem_normalizer_of_mk_mem_normalizer_star {K : Subgroup G} (hK : K ∈ cComp H) {t : G}
    (ht : t ∈ H)
    (h : (QuotientGroup.mk ⟨t, ht⟩ : HStar H) ∈ Subgroup.normalizer (star H K : Set (HStar H))) :
    t ∈ Subgroup.normalizer (K : Set G) := by
  have hKH : K ≤ H := le_of_mem_cComp hK
  have h1 : (star H K).map (MulAut.conj (QuotientGroup.mk ⟨t, ht⟩ : HStar H)).toMonoidHom =
      star H K := A38.map_conj_eq_iff.mpr h
  rw [← star_map_conj ht] at h1
  have hKt : K.map (MulAut.conj t).toMonoidHom ∈ cComp H := map_conj_mem_cComp hK ht
  exact A38.map_conj_eq_iff.mp (L1233.star_injOn hKt hK h1)

theorem le_normalizer_of_oTwoUpper (h37 : A37ForSQTK) (h38 : A38ForSQTK) (hHq : SQTKGroup ↥H)
    {K X : Subgroup G} (hKc : K ∈ cComp H) (hXH : X ≤ H) (hX : oTwoUpper X = X) :
    X ≤ Subgroup.normalizer (K : Set G) := by
  have hQ : SQTKHyp (↥H ⧸ CFSG.pCore 2 ↥H) := SQTKHyp.of_sqtkGroup ↥H hHq
  exact S153D.le_normalizer_of_oTwoUpper_eq (le_of_mem_cComp hKc) hXH hX
    ((lemma_1_2_1_three_of_a3_sq (h37 _ hQ) (h38 _ hQ) hKc).imp id fun h => h.1)

end Finite

section Suzuki

theorem suzukiModel_of_odd_center {N : Type} [Group N] [Finite N] [Group.IsPerfect N]
    (hZodd : Odd (Nat.card ↥(Subgroup.center N))) {n : ℕ}
    (hSz : SuzukiModel (N ⧸ Subgroup.center N) 2 n) : SuzukiModel N 2 n := by
  obtain ⟨h2, a, ha, K', hF, hFin, hn, hK', ⟨α⟩⟩ := hSz
  have hK'' : Nat.card K' = 2 ^ (2 * a + 1) := hn ▸ hK'
  let e := CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup (a := a) hK''
  let α' : (N ⧸ Subgroup.center N) ≃* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    α.trans e
  let π : N →* CFSG.BenderSuzuki.MatrixGroups.SuzukiMatrixGroup a :=
    α'.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center N))
  have hπ : Function.Surjective π := α'.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : π.ker = Subgroup.center N := CFSG.SectionRank.center_eq_ker_of_mulEquiv α'
  have hZ := CFSG.SectionRank.suzuki_perfect_odd_cover_trivial a (by omega) π hπ hker.le
    (hker ▸ hZodd)
  rw [hker] at hZ
  exact ⟨h2, a, ha, K', hF, hFin, hn, hK',
    ⟨((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).symm.trans α⟩⟩

end Suzuki

end CFSG.Quasithin.H13.P31Sz

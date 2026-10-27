module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329Data
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitRes
import CFSG.Adapters.LieModelSimple
import CFSG.LocalAnalysis.RankThreeCoreUniqueness.PerfectResiduals
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight7xK329SplitOrder

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Blueprint (LieModel)

theorem k329_mem_centralizer_equiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') (u k : S) :
    e k ∈ Subgroup.centralizer ({e u} : Set S') ↔ k ∈ Subgroup.centralizer ({u} : Set S) := by
  simp only [Subgroup.mem_centralizer_iff, Set.mem_singleton_iff, forall_eq]
  rw [← map_mul e u k, ← map_mul e k u, e.injective.eq_iff]

theorem K329UDatum.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {u : S}
    (h : K329UDatum S u) : K329UDatum S' (e u) := by
  obtain ⟨hord, M, N, hMC, hMn, hNM, hNn, hN3, a, ha, b, hb, hab⟩ := h
  have hcent : ∀ k : S', k ∈ Subgroup.centralizer ({e u} : Set S') ↔
      e.symm k ∈ Subgroup.centralizer ({u} : Set S) := fun k => by
    have := k329_mem_centralizer_equiv e u (e.symm k)
    rwa [MulEquiv.apply_symm_apply] at this
  have hM'C : M.map (e : S →* S') ≤ Subgroup.centralizer ({e u} : Set S') := by
    rintro _ ⟨m, hm, rfl⟩
    exact (k329_mem_centralizer_equiv e u m).2 (hMC hm)
  refine ⟨(orderOf_injective (e : S →* S') e.injective u).trans hord,
    M.map (e : S →* S'), N.map (e : S →* S'), hM'C, ?_, Subgroup.map_mono hNM, ?_,
    hN3.map (e : S →* S'), e a, ⟨a, ha, rfl⟩, e b, ⟨b, hb, rfl⟩, fun hc => hab (e.injective ?_)⟩
  · rw [Subgroup.normal_subgroupOf_iff hM'C]
    rintro _ k ⟨m, hm, rfl⟩ hk
    refine ⟨e.symm k * m * (e.symm k)⁻¹,
      (Subgroup.normal_subgroupOf_iff hMC).1 hMn m (e.symm k) hm ((hcent k).1 hk), ?_⟩
    simp
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hNM)]
    rintro _ k ⟨n, hn, rfl⟩ ⟨m, hm, rfl⟩
    exact ⟨m * n * m⁻¹, (Subgroup.normal_subgroupOf_iff hNM).1 hNn n m hn hm, by simp⟩
  · simpa using hc

theorem K329ZDatum.of_mulEquiv {S S' : Type} [Group S] [Group S'] (e : S ≃* S') {z : S}
    (h : K329ZDatum S z) : K329ZDatum S' (e z) := by
  obtain ⟨hord, M, Y, hMC, hMn, hCC, hYM, hYn, hY⟩ := h
  have hcent : ∀ k : S', k ∈ Subgroup.centralizer ({e z} : Set S') ↔
      e.symm k ∈ Subgroup.centralizer ({z} : Set S) := fun k => by
    have := k329_mem_centralizer_equiv e z (e.symm k)
    rwa [MulEquiv.apply_symm_apply] at this
  have hM'C : M.map (e : S →* S') ≤ Subgroup.centralizer ({e z} : Set S') := by
    rintro _ ⟨m, hm, rfl⟩
    exact (k329_mem_centralizer_equiv e z m).2 (hMC hm)
  have hC' : Subgroup.centralizer ({e z} : Set S') ≤
      (Subgroup.centralizer ({z} : Set S)).map (e : S →* S') :=
    fun k hk => ⟨e.symm k, (hcent k).1 hk, by simp⟩
  refine ⟨(orderOf_injective (e : S →* S') e.injective z).trans hord,
    M.map (e : S →* S'), Y.map (e : S →* S'), hM'C, ?_, ?_, Subgroup.map_mono hYM, ?_, ?_⟩
  · rw [Subgroup.normal_subgroupOf_iff hM'C]
    rintro _ k ⟨m, hm, rfl⟩ hk
    refine ⟨e.symm k * m * (e.symm k)⁻¹,
      (Subgroup.normal_subgroupOf_iff hMC).1 hMn m (e.symm k) hm ((hcent k).1 hk), ?_⟩
    simp
  · calc ⁅Subgroup.centralizer ({e z} : Set S'), Subgroup.centralizer ({e z} : Set S')⁆
        ≤ ⁅(Subgroup.centralizer ({z} : Set S)).map (e : S →* S'),
            (Subgroup.centralizer ({z} : Set S)).map (e : S →* S')⁆ :=
          Subgroup.commutator_mono hC' hC'
      _ = ⁅Subgroup.centralizer ({z} : Set S), Subgroup.centralizer ({z} : Set S)⁆.map
            (e : S →* S') := (Subgroup.map_commutator _ _ _).symm
      _ ≤ M.map (e : S →* S') := Subgroup.map_mono hCC
  · rw [Subgroup.normal_subgroupOf_iff (Subgroup.map_mono hYM)]
    rintro _ k ⟨y, hy, rfl⟩ ⟨m, hm, rfl⟩
    exact ⟨m * y * m⁻¹, (Subgroup.normal_subgroupOf_iff hYM).1 hYn y m hy hm, by simp⟩
  · exact CFSG.Blueprint.LieModel.of_mulEquiv (e.subgroupMap Y) hY

theorem k329_S1_uNormal {S : Type} [Group S] {u : S} (h : K329UDatum S u) :
    orderOf u = 3 ∧ ∃ N : Subgroup S, N ≤ Subgroup.centralizer ({u} : Set S) ∧
      (N.subgroupOf (Subgroup.centralizer ({u} : Set S))).Normal ∧ IsPGroup 3 N ∧
      ∃ a ∈ N, ∃ b ∈ N, a * b ≠ b * a := by
  obtain ⟨hord, M, N, hMC, hMn, hNM, hNn, hN3, a, ha, b, hb, hab⟩ := h
  have hN' : IsPGroup 3 ↥(N.subgroupOf M) := hN3.comap_subtype
  have hNle : N.subgroupOf M ≤ CFSG.pCore 3 ↥M := le_sSup ⟨hNn, hN'⟩
  have hNP : N ≤ (CFSG.pCore 3 ↥M).map M.subtype := fun x hx =>
    ⟨⟨x, hNM hx⟩, hNle (Subgroup.mem_subgroupOf.2 hx), rfl⟩
  have hPC : (CFSG.pCore 3 ↥M).map M.subtype ≤ Subgroup.centralizer ({u} : Set S) :=
    (Subgroup.map_subtype_le _).trans hMC
  refine ⟨hord, (CFSG.pCore 3 ↥M).map M.subtype, hPC, ?_,
    (CFSG.pCore_isPGroup (p := 3) (G := ↥M)).map M.subtype, a, hNP ha, b, hNP hb, hab⟩
  rw [Subgroup.normal_subgroupOf_iff_le_normalizer hPC]
  exact ((Subgroup.normal_subgroupOf_iff_le_normalizer hMC).1 hMn).trans
    (CFSG.RankThreeCoreUniqueness.Helpers.normalizer_le_normalizer_characteristic_map M _
      inferInstance)

theorem k329_psl28_perfect {S : Type} [Group S] [Finite S] {Y : Subgroup S}
    (hY : LieModel ↥Y .PSL 2 2 3) : ⁅Y, Y⁆ = Y := by
  have hcard : Nat.card ↥Y = 504 := k329_card_psl28 hY
  have hsimple : IsSimpleGroup ↥Y :=
    CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags
      (by simp [CFSG.Blueprint.classicalTags]) hY
  have hna : ∃ a b : ↥Y, a * b ≠ b * a := by
    by_contra hcon
    push Not at hcon
    let _ : CommGroup ↥Y := { (inferInstance : Group ↥Y) with mul_comm := fun a b => hcon a b }
    have hp := IsSimpleGroup.prime_card (α := ↥Y)
    rw [hcard] at hp
    norm_num at hp
  exact Subgroup.isPerfect_iff.1 ⟨(k329_quasisimple_of_simple_nonabelian hsimple hna).1⟩

theorem k329_S1_zResidual {S : Type} [Group S] [Finite S] {z : S} (h : K329ZDatum S z) :
    orderOf z = 3 ∧ ∃ Y : Subgroup S, LieModel ↥Y .PSL 2 2 3 ∧
      Y ≤ K329Res (Subgroup.centralizer ({z} : Set S)) ∧
      (Y.subgroupOf (K329Res (Subgroup.centralizer ({z} : Set S)))).Normal := by
  obtain ⟨hord, M, Y, hMC, -, hCC, hYM, hYn, hY⟩ := h
  have hYres : Y ≤ K329Res (Subgroup.centralizer ({z} : Set S)) :=
    k329_perfect_le_res (hYM.trans hMC) (k329_psl28_perfect hY)
  have hresM : K329Res (Subgroup.centralizer ({z} : Set S)) ≤ M :=
    (k329_res_le_commutator _).trans hCC
  refine ⟨hord, Y, hY, hYres, ?_⟩
  rw [Subgroup.normal_subgroupOf_iff hYres]
  intro y r hy hr
  exact (Subgroup.normal_subgroupOf_iff hYM).1 hYn y r hy (hresM hr)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

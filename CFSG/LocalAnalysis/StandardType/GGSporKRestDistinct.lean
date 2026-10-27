module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestClLink
public import CFSG.LocalAnalysis.StandardType.GGSporKRestDistinctDefs

public section

namespace CFSG.StandardType.SporadicShape

open Equiv CFSG.Sporadic.Th CFSG.Sporadic.Th.Native

theorem sporKRest_complete_of_distinct {K : Type} [Group K] {p N : ℕ} (ρ : Fin N → K)
    (hlib : ∀ s : K, orderOf s = p → ∃ k, IsConj s (ρ k)) (r : Fin N → K)
    (hord : ∀ j, orderOf (r j) = p) (hnc : ∀ j j', IsConj (r j) (r j') → j = j') :
    ∀ s : K, orderOf s = p → ∃ j, IsConj (r j) s := by
  have hex : ∀ j, ∃ k, IsConj (r j) (ρ k) := fun j => by
    obtain ⟨k, hk⟩ := hlib (r j) (hord j)
    exact ⟨k, hk⟩
  choose f hf using hex
  have hinj : Function.Injective f := by
    intro j j' h
    apply hnc
    refine (hf j).trans ?_
    rw [h]
    exact (hf j').symm
  have hsurj : Function.Surjective f := Finite.injective_iff_surjective.mp hinj
  intro s hs
  obtain ⟨k, hk⟩ := hlib s hs
  obtain ⟨j, rfl⟩ := hsurj k
  exact ⟨j, (hf j).trans hk.symm⟩

namespace PermCover


private theorem ggSporKRestDist_eval_mem {n : ℕ} (a b : Perm (Fin n)) (H : Subgroup (Perm (Fin n)))
    (ha : a ∈ H) (hb : b ∈ H) (w : List ℤ) :
    sporKRestEval [a, b] w ∈ H := by
  apply sporKRestEval_mem
  intro g hg
  rcases List.mem_cons.mp hg with rfl | hg
  · exact ha
  · rw [List.mem_singleton] at hg
    rw [hg]
    exact hb

private theorem ggSporKRestDist_rep_mem {n : ℕ} (a b : Perm (Fin n))
    (H : Subgroup (Perm (Fin n))) (ha : a ∈ H) (hb : b ∈ H) (c : ClassData) :
    rep a b c ∈ H :=
  ggSporKRestDist_eval_mem a b H ha hb (sporKRestParse c.x)

theorem classInvOkK_sound {n : ℕ} {B : List ℕ} {p : ℕ} (hp : p.Prime) {a b : Perm (Fin n)} {d : Data}
    (hB : IsBase B (Subgroup.closure {a, b})) (h : classInvOkK B p a b d = true) :
    (∀ c ∈ d.classes, orderOf (rep a b c) = p) ∧ (d.classes.map fun c => fixCnt (rep a b c)).Nodup := by
  let H : Subgroup (Perm (Fin n)) := Subgroup.closure ({a, b} : Set (Perm (Fin n)))
  have ha : a ∈ H := Subgroup.subset_closure (by simp)
  have hb : b ∈ H := Subgroup.subset_closure (by simp)
  unfold classInvOkK at h
  dsimp only at h
  simp only [mat_eq, repMat_eq, keyEq, decide_eq_true_eq, Bool.and_eq_true, List.all_eq_true,
    Bool.not_eq_true_eq_eq_false, decide_eq_false_iff_not] at h
  obtain ⟨hall, hnodup⟩ := h
  have hrep : ∀ c ∈ d.classes, rep a b c ∈ H := fun c _ => ggSporKRestDist_rep_mem a b H ha hb c
  constructor
  · intro c hc
    obtain ⟨hp1, hp2⟩ := hall c hc
    have hpow : rep a b c ^ p = 1 :=
      eq_of_keyOf_eq hB (H.pow_mem (hrep c hc) p) H.one_mem hp1
    have hne : rep a b c ≠ 1 := fun h1 => hp2 (by rw [h1])
    haveI : Fact p.Prime := ⟨hp⟩
    exact orderOf_eq_prime hpow hne
  · rw [← List.map_congr_left (fun c _ => fixCntL_eq (rep a b c))]
    exact hnodup

end PermCover

theorem sporKRest_cover_of_classInvK {K : Type} [Group K] [Finite K] {n : ℕ} (φ : K →* Perm (Fin n))
    (hφ : Function.Injective φ) (a b : K) (hab : Subgroup.closure ({a, b} : Set K) = ⊤) (B : List ℕ)
    (hB : PermCover.IsBase B (Subgroup.closure {φ a, φ b})) {p : ℕ} (hp : p.Prime) (m : ℕ)
    (d : PermCover.Data) (hcheck : PermCover.checkClMatK B (φ a) (φ b) (p ^ m) d = true)
    (hinv : PermCover.classInvOkK B p (φ a) (φ b) d = true) {N : ℕ} (ρ : Fin N → K)
    (hlib : ∀ s : K, orderOf s = p → ∃ k, IsConj s (ρ k)) (hN : d.classes.length = N) :
    SporKRestCover p K := by
  obtain ⟨hordphi, hnodupphi⟩ := PermCover.classInvOkK_sound hp hB hinv
  have hj : ∀ j : Fin N, j.1 < d.classes.length := fun j => by rw [hN]; exact j.2
  let g : PermCover.ClassData → ℕ := fun c => PermCover.fixCnt (PermCover.rep (φ a) (φ b) c)
  let r : Fin N → K := fun j => ggSporKRestPC_rep a b (d.classes[j.1]'(hj j))
  have hmap : ∀ j : Fin N, φ (r j) =
      PermCover.rep (φ a) (φ b) (d.classes[j.1]'(hj j)) := by
    intro j
    dsimp only [r]
    exact ggSporKRestPC_rep_map φ a b _
  have hord : ∀ j, orderOf (r j) = p := by
    intro j
    have hmem : d.classes[j.1]'(hj j) ∈ d.classes := List.getElem_mem _
    rw [← orderOf_injective φ hφ (r j), hmap j]
    exact hordphi _ hmem
  have hnc : ∀ j j', IsConj (r j) (r j') → j = j' := by
    intro j j' hc
    have hcφ : IsConj (φ (r j)) (φ (r j')) := by
      obtain ⟨c, hc'⟩ := isConj_iff.mp hc
      refine isConj_iff.mpr ⟨φ c, ?_⟩
      simpa only [map_mul, map_inv] using congrArg φ hc'
    have hfix := PermCover.fixCnt_of_isConj hcφ
    rw [hmap j, hmap j'] at hfix
    have hentry : (d.classes.map g)[j.1]'(by rw [List.length_map]; exact hj j) =
        (d.classes.map g)[j'.1]'(by rw [List.length_map]; exact hj j') := by
      rw [List.getElem_map, List.getElem_map]
      simpa only [g] using hfix
    exact Fin.ext ((hnodupphi.getElem_inj_iff).mp hentry)
  obtain hcomplete := sporKRest_complete_of_distinct ρ hlib r hord hnc
  refine sporKRest_cover_of_classCheckK φ hφ a b hab B hB hp m d hcheck ?_
  intro s hs
  obtain ⟨j, hjs⟩ := hcomplete s hs
  exact ⟨d.classes[j.1]'(hj j), List.getElem_mem _,
    by simpa only [r, ggSporKRestPC_rep] using hjs⟩

theorem sporKRest_cover_of_actionClInvK {K : Type} [Group K] [Finite K] {n : ℕ} [MulAction K (Fin n)]
    (B : List ℕ)
    (hbase : ∀ g : K, (∀ i ∈ B, ∀ h : i < n, g • (⟨i, h⟩ : Fin n) = ⟨i, h⟩) → g = 1) (a b : K)
    (α β : Perm (Fin n)) (ha : ∀ i : Fin n, a • i = α i) (hb : ∀ i : Fin n, b • i = β i)
    (hab : Subgroup.closure ({a, b} : Set K) = ⊤) {p : ℕ} (hp : p.Prime) (m : ℕ) (d : PermCover.Data)
    (hcheck : PermCover.checkClMatK B α β (p ^ m) d = true)
    (hinv : PermCover.classInvOkK B p α β d = true) {N : ℕ} (ρ : Fin N → K)
    (hlib : ∀ s : K, orderOf s = p → ∃ k, IsConj s (ρ k)) (hN : d.classes.length = N) :
    SporKRestCover p K := by
  have hfaith : ∀ g : K, (∀ i : Fin n, g • i = i) → g = 1 :=
    fun g hg => hbase g fun i _ h => hg ⟨i, h⟩
  have hφa : MulAction.toPermHom K (Fin n) a = α := Equiv.ext fun i => ha i
  have hφb : MulAction.toPermHom K (Fin n) b = β := Equiv.ext fun i => hb i
  have hB := sporKRest_isBase_of_action B hbase a b α β ha hb hab
  refine sporKRest_cover_of_classInvK (MulAction.toPermHom K (Fin n))
    (sporKRest_toPermHom_injective hfaith) a b hab B ?_ hp m d ?_ ?_ ρ hlib hN
  · rw [hφa, hφb]
    exact hB
  · rw [hφa, hφb]
    exact hcheck
  · rw [hφa, hφb]
    exact hinv

theorem sporKRest_cover_of_tableClInvK {G : Type} [Group G] [Finite G] {n : ℕ} [MulAction G (Fin n)]
    (B : List ℕ)
    (hbase : ∀ g : G, (∀ i ∈ B, ∀ h : i < n, g • (⟨i, h⟩ : Fin n) = ⟨i, h⟩) → g = 1) (a b : G)
    (Ta Tb : Table) (ha : Rep n Ta a) (hb : Rep n Tb b) (hTa : PermCover.tablePermOK n Ta = true)
    (hTb : PermCover.tablePermOK n Tb = true) (hab : Subgroup.closure ({a, b} : Set G) = ⊤)
    {p : ℕ} (hp : p.Prime) (m : ℕ) (d : PermCover.Data)
    (hcheck : PermCover.checkClMatK B (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb) (p ^ m) d = true)
    (hinv : PermCover.classInvOkK B p (PermCover.tablePerm n Ta) (PermCover.tablePerm n Tb) d = true)
    {N : ℕ} (ρ : Fin N → G) (hlib : ∀ s : G, orderOf s = p → ∃ k, IsConj s (ρ k))
    (hN : d.classes.length = N) : SporKRestCover p G := by
  exact sporKRest_cover_of_actionClInvK B hbase a b (PermCover.tablePerm n Ta)
    (PermCover.tablePerm n Tb) (sporKRest_smul_eq_tablePerm ha hTa)
    (sporKRest_smul_eq_tablePerm hb hTb) hab hp m d hcheck hinv ρ hlib hN

end CFSG.StandardType.SporadicShape

module

public import CFSG.LieType.Multipliers.CoverWords
public import CFSG.Sporadic.Recognition.CoverTransfer

public section

namespace CFSG.Sporadic.Recognition.CoverCyclic

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Open CFSG.Sporadic.Recognition.CoverTransfer
  Subgroup

variable {m : ℕ}

private theorem card_finite_of_orderCheck {ws : List (List (Fin m × Bool))} {k cap n fuel : ℕ}
    {words : List (List (Fin m × Bool) × ℕ)} (h : orderCheck ws [] k cap n words fuel = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n := by
  have hS : subsetOf m [] = [] := by simp [subsetOf]
  have : Finite (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) := by
    rw [hS]; exact (inferInstance : Finite (PG 0 _))
  have hc : Nat.card (PG (subsetOf m []).length (restrictWords (subsetOf m []) ws)) = 1 := by
    rw [hS]; exact card_PG_zero _
  have := card_le_of_subsetCheckShortC ws [] (subsetCheckShortC_of_orderCheck h)
  rwa [hc, mul_one] at this

theorem bounds_of_orderCheck {ws : List (List (Fin m × Bool))} {w : List (Fin m × Bool)}
    {N k cap n fuel : ℕ} (hN : 0 < N) (h : orderCheck ws [] k cap n [(w, N)] fuel = true) :
    Finite (PG m ws) ∧ Nat.card (PG m ws) ≤ n ∧
      N ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin m) | r ∈ ws.map FreeGroup.mk}
        (FreeGroup.mk w)) :=
  ⟨(card_finite_of_orderCheck h).1, (card_finite_of_orderCheck h).2,
    dvd_orderOf_of_orderCheck h (List.mem_singleton_self _) hN⟩

theorem cover_ker_cyclic_of_bounds {X : Type} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R))
    (c : Fin m → List (List (Fin m × Bool) × List (Fin m × Bool)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i) {N : ℕ}
    {w : List (Fin m × Bool)} (hw1 : FreeGroup.lift g (FreeGroup.mk w) = 1) {n : ℕ}
    (hb : Finite (PG m (coverWords R fun i => commWords (c i))) ∧
      Nat.card (PG m (coverWords R fun i => commWords (c i))) ≤ n ∧
      N ∣ orderOf (PresentedGroup.mk
        {r : FreeGroup (Fin m) | r ∈ (coverWords R fun i => commWords (c i)).map FreeGroup.mk}
        (FreeGroup.mk w)))
    (hn : n ≤ N * Nat.card X) :
    ∃ hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i,
      IsCyclic (coverMap hP hw).ker ∧ Nat.card (coverMap hP hw).ker = N := by
  have hcomm : ∀ i, FreeGroup.mk (commWords (c i)) ∈ commutator (FreeGroup (Fin m)) :=
    fun i => mk_commWords_mem_commutator _
  refine ⟨hwg, ?_⟩
  obtain ⟨hfin, hle, hord⟩ := hb
  have hset := coverRelators_wordSet R fun i => commWords (c i)
  have key : ∀ S : Set (FreeGroup (Fin m)), wordSet (coverWords R fun i => commWords (c i)) = S →
      S = coverRelators (wordSet R) (fun i => FreeGroup.mk (commWords (c i))) →
      IsCyclic (coverMap hP hwg).ker ∧ Nat.card (coverMap hP hwg).ker = N := by
    rintro S rfl hS
    have : Finite (PresentedCover (wordSet R) fun i => FreeGroup.mk (commWords (c i))) := by
      rw [PresentedCover, ← hS]; exact hfin
    have hcard : Nat.card (PresentedCover (wordSet R) fun i => FreeGroup.mk (commWords (c i))) ≤
        N * Nat.card X := by
      rw [PresentedCover, ← hS]; exact hle.trans hn
    set π := coverMap hP hwg
    have : Finite X := Finite.of_surjective _ (coverMap_surjective hP hwg)
    have hP' := card_presentedCover hP hcomm hwg
    have hker : Nat.card π.ker =
        Nat.card (griessHopfMultiplier X) := by
      rw [Nat.card_congr (griessHopfMultiplierEquivKer hP hcomm hwg).toEquiv]
    have hXpos : 0 < Nat.card X := Nat.card_pos
    have hM : Nat.card π.ker ≤ N := by
      rw [hker]
      rw [hP', mul_comm] at hcard
      exact Nat.le_of_mul_le_mul_right hcard hXpos
    have hordz : N ∣ orderOf (PresentedGroup.mk
        (coverRelators (wordSet R) fun i => FreeGroup.mk (commWords (c i))) (FreeGroup.mk w)) := by
      rw [← hS]; exact hord
    set z := PresentedGroup.mk (coverRelators (wordSet R) fun i => FreeGroup.mk (commWords (c i)))
      (FreeGroup.mk w)
    have hz : z ∈ π.ker := by
      rw [MonoidHom.mem_ker, coverMap_mk]
      exact hw1
    have hdvd : N ∣ Nat.card π.ker := by
      refine hordz.trans ?_
      rw [← Subgroup.orderOf_mk z hz]
      exact orderOf_dvd_natCard _
    have hK : Nat.card π.ker = N := le_antisymm hM (Nat.le_of_dvd Nat.card_pos hdvd)
    refine ⟨?_, hK⟩
    have hord' : orderOf (⟨z, hz⟩ : π.ker) = Nat.card π.ker := by
      have h1 : orderOf (⟨z, hz⟩ : π.ker) ∣ Nat.card π.ker := orderOf_dvd_natCard _
      have h2 : N ∣ orderOf (⟨z, hz⟩ : π.ker) := by
        rw [Subgroup.orderOf_mk z hz]; exact hordz
      rw [hK] at h1 ⊢
      exact Nat.dvd_antisymm h1 h2
    exact isCyclic_of_orderOf_eq_card _ hord'
  exact key _ rfl hset.symm

theorem cover_ker_cyclic_of_orderCheck {X : Type} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R))
    (c : Fin m → List (List (Fin m × Bool) × List (Fin m × Bool)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i) {N : ℕ} (hN : 0 < N)
    {w : List (Fin m × Bool)} (hw1 : FreeGroup.lift g (FreeGroup.mk w) = 1) {k cap n fuel : ℕ}
    (h : orderCheck (coverWords R fun i => commWords (c i)) [] k cap n [(w, N)] fuel = true)
    (hn : n ≤ N * Nat.card X) :
    ∃ hw : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i,
      IsCyclic (coverMap hP hw).ker ∧ Nat.card (coverMap hP hw).ker = N :=
  cover_ker_cyclic_of_bounds hP c hwg hw1 (bounds_of_orderCheck hN h) hn

theorem ker_cyclic_dvd_of_bounds {X : Type} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R))
    (c : Fin m → List (List (Fin m × Bool) × List (Fin m × Bool)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i) {N : ℕ}
    {w : List (Fin m × Bool)} (hw1 : FreeGroup.lift g (FreeGroup.mk w) = 1) {n : ℕ}
    (hb : Finite (PG m (coverWords R fun i => commWords (c i))) ∧
      Nat.card (PG m (coverWords R fun i => commWords (c i))) ≤ n ∧
      N ∣ orderOf (PresentedGroup.mk
        {r : FreeGroup (Fin m) | r ∈ (coverWords R fun i => commWords (c i)).map FreeGroup.mk}
        (FreeGroup.mk w)))
    (hn : n ≤ N * Nat.card X) {E : Type} [Group E] [Group.IsPerfect E] (q : E →* X)
    (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    IsCyclic q.ker ∧ Nat.card q.ker ∣ N := by
  obtain ⟨hwg', hcyc, hcard⟩ := cover_ker_cyclic_of_bounds hP c hwg hw1 hb hn
  have hcomm : ∀ i, FreeGroup.mk (commWords (c i)) ∈ commutator (FreeGroup (Fin m)) :=
    fun i => mk_commWords_mem_commutator _
  obtain ⟨φ, hφ, hcomp⟩ := exists_surjective_lift (w := fun i => FreeGroup.mk (commWords (c i)))
    hP hcomm hwg' q hq hker
  set K := (coverMap hP hwg').ker with hK
  have hmap : q.ker = K.map φ := by
    ext z
    constructor
    · intro hz
      obtain ⟨y, rfl⟩ := hφ z
      refine ⟨y, ?_, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker, ← hcomp, MonoidHom.comp_apply]
      exact hz
    · rintro ⟨y, hy, rfl⟩
      rw [SetLike.mem_coe, MonoidHom.mem_ker] at hy
      rw [MonoidHom.mem_ker, ← MonoidHom.comp_apply, hcomp]
      exact hy
  refine ⟨?_, ?_⟩
  · have := hcyc
    have h1 : IsCyclic ↥(K.map φ) := isCyclic_of_surjective (φ.subgroupMap K)
      (φ.subgroupMap_surjective K)
    have := h1
    exact isCyclic_of_surjective (MulEquiv.subgroupCongr hmap.symm).toMonoidHom
      (MulEquiv.subgroupCongr hmap.symm).surjective
  · have hdvd := Subgroup.card_map_dvd K φ
    rw [hcard, ← hmap] at hdvd
    exact hdvd

theorem ker_cyclic_dvd_of_orderCheck {X : Type} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R))
    (c : Fin m → List (List (Fin m × Bool) × List (Fin m × Bool)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i) {N : ℕ} (hN : 0 < N)
    {w : List (Fin m × Bool)} (hw1 : FreeGroup.lift g (FreeGroup.mk w) = 1) {k cap n fuel : ℕ}
    (h : orderCheck (coverWords R fun i => commWords (c i)) [] k cap n [(w, N)] fuel = true)
    (hn : n ≤ N * Nat.card X) {E : Type} [Group E] [Group.IsPerfect E] (q : E →* X)
    (hq : Function.Surjective q) (hker : q.ker ≤ center E) :
    IsCyclic q.ker ∧ Nat.card q.ker ∣ N :=
  ker_cyclic_dvd_of_bounds hP c hwg hw1 (bounds_of_orderCheck hN h) hn q hq hker

theorem center_cyclic_dvd_of_bounds {X : Type} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R))
    (c : Fin m → List (List (Fin m × Bool) × List (Fin m × Bool)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i) {N : ℕ}
    {w : List (Fin m × Bool)} (hw1 : FreeGroup.lift g (FreeGroup.mk w) = 1) {n : ℕ}
    (hb : Finite (PG m (coverWords R fun i => commWords (c i))) ∧
      Nat.card (PG m (coverWords R fun i => commWords (c i))) ≤ n ∧
      N ∣ orderOf (PresentedGroup.mk
        {r : FreeGroup (Fin m) | r ∈ (coverWords R fun i => commWords (c i)).map FreeGroup.mk}
        (FreeGroup.mk w)))
    (hn : n ≤ N * Nat.card X) {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* X) :
    IsCyclic (Subgroup.center Q) ∧ Nat.card (Subgroup.center Q) ∣ N := by
  have := hQ
  set q : Q →* X := e.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center Q)) with hq
  have hqs : Function.Surjective q := e.surjective.comp (QuotientGroup.mk'_surjective _)
  have hqk : q.ker = Subgroup.center Q := by
    ext x
    rw [MonoidHom.mem_ker]
    change e (QuotientGroup.mk' (Subgroup.center Q) x) = 1 ↔ _
    rw [map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  have := ker_cyclic_dvd_of_bounds hP c hwg hw1 hb hn q hqs (le_of_eq hqk)
  rwa [hqk] at this

theorem center_cyclic_dvd_of_orderCheck {X : Type} [Group X] {g : Fin m → X}
    {R : List (List (Fin m × Bool))} (hP : IsPresentation g (wordSet R))
    (c : Fin m → List (List (Fin m × Bool) × List (Fin m × Bool)))
    (hwg : ∀ i, FreeGroup.lift g (FreeGroup.mk (commWords (c i))) = g i) {N : ℕ} (hN : 0 < N)
    {w : List (Fin m × Bool)} (hw1 : FreeGroup.lift g (FreeGroup.mk w) = 1) {k cap n fuel : ℕ}
    (h : orderCheck (coverWords R fun i => commWords (c i)) [] k cap n [(w, N)] fuel = true)
    (hn : n ≤ N * Nat.card X) {Q : Type} [Group Q] (hQ : Group.IsPerfect Q)
    (e : Q ⧸ Subgroup.center Q ≃* X) :
    IsCyclic (Subgroup.center Q) ∧ Nat.card (Subgroup.center Q) ∣ N :=
  center_cyclic_dvd_of_bounds hP c hwg hw1 (bounds_of_orderCheck hN h) hn hQ e

end CFSG.Sporadic.Recognition.CoverCyclic

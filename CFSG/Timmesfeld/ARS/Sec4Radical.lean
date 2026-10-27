module

public import CFSG.Timmesfeld.ARS.Sec4Closure

public section

namespace CFSG.Timmesfeld.ARS

open scoped commutatorElement
open CFSG.Timmesfeld.RankOne

variable {G : Type*} [Group G] {R : Set (Subgroup G)}

@[expose] def rootNorm (R : Set (Subgroup G)) (A B : Subgroup G) : Subgroup G :=
  gen (rootClosure R A) ⊓ stabSet (rootClosure R B)

@[expose] def radPart (R : Set (Subgroup G)) (A : Subgroup G) : Subgroup G :=
  Subgroup.closure {x | x ∈ gen (rootClosure R A) ∧ x ∉ rootElts R}

@[expose] def radical (R : Set (Subgroup G)) : Subgroup G := ⨆ A ∈ R, radPart R A

theorem rootNorm_le_gen (A B : Subgroup G) : rootNorm R A B ≤ gen (rootClosure R A) :=
  inf_le_left

theorem rootNorm_le_stabSet (A B : Subgroup G) :
    rootNorm R A B ≤ stabSet (rootClosure R B) :=
  inf_le_right

theorem radPart_le_gen (A : Subgroup G) : radPart R A ≤ gen (rootClosure R A) :=
  Subgroup.closure_le _ |>.2 fun _ hx => hx.1

theorem conjSub_radPart (hR : IsRootClass R) (A : Subgroup G) (g : G) :
    conjSub (radPart R A) g = radPart R (conjSub A g) := by
  rw [radPart, radPart, conjSub, MonoidHom.map_closure]
  congr 1
  ext y
  constructor
  · rintro ⟨x, ⟨hx, hxD⟩, rfl⟩
    refine ⟨?_, fun h => hxD ((conj_mem_rootElts_iff hR g).1 h)⟩
    rw [rootClosure_conjSub hR, ← conjSub_gen]
    exact conj_mem_conjSub g hx
  · rintro ⟨hy, hyD⟩
    refine ⟨g⁻¹ * y * g, ⟨?_, fun h => hyD ?_⟩, ?_⟩
    · rw [rootClosure_conjSub hR, ← conjSub_gen, mem_conjSub] at hy
      exact hy
    · have := (conj_mem_rootElts_iff hR g).2 h
      rwa [show g * (g⁻¹ * y * g) * g⁻¹ = y by group] at this
    · change g * (g⁻¹ * y * g) * g⁻¹ = y
      group

section RootNorm

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) {A B : Subgroup G} (hA : A ∈ R)
  (hB : B ∈ R) (hAB : Opposite A B)
include hR hiso hA hB hAB

theorem exists_inv_mul_mem_rootNorm {A' : Subgroup G} (hA' : A' ∈ rootClosure R A) {a' : G}
    (ha' : a' ∈ A') (ha'1 : a' ≠ 1) : ∃ a ∈ A, a ≠ 1 ∧ a⁻¹ * a' ∈ rootNorm R A B := by
  have hA'B : Opposite A' B :=
    opposite_of_mem_rootClosure hR hiso hA hB hAB hA' (mem_rootClosure_self hB)
  obtain ⟨b, hb, hb1, hA'b⟩ := hA'B.2.1 a' ha' ha'1
  obtain ⟨a, ha, ha1, hBa⟩ := hAB.2.2 b hb hb1
  refine ⟨a, ha, ha1, Subgroup.mem_inf.2 ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _
    (le_gen (mem_rootClosure_self hA) ha)) (le_gen hA' ha'), ?_⟩⟩
  have h1 : conjSet (rootClosure R B) a' = conjSet (rootClosure R A) b := by
    rw [← rootClosure_conjSub hR, ← hA'b, rootClosure_conjSub hR, rootClosure_eq_of_mem hA']
  have h2 : conjSet (rootClosure R B) a = conjSet (rootClosure R A) b := by
    rw [← rootClosure_conjSub hR, hBa, rootClosure_conjSub hR]
  rw [mem_stabSet, conjSet_mul, h1, ← h2, conjSet_conjSet_inv]

theorem exists_mul_eq_of_mem_gen_rootClosure {x : G} (hx : x ∈ gen (rootClosure R A)) :
    ∃ a ∈ A, ∃ n ∈ rootNorm R A B, a * n = x := by
  have hc := commuting_gen_rootClosure hR hA
  have hle : A ≤ Subgroup.normalizer ((rootNorm R A B : Subgroup G) : Set G) :=
    le_normalizer_of_conjSub_le fun a ha => (conjSub_of_forall_commute fun n hn =>
      hc a (le_gen (mem_rootClosure_self hA) ha) n (rootNorm_le_gen A B hn)).le
  have hsub : gen (rootClosure R A) ≤ A ⊔ rootNorm R A B := by
    refine gen_le fun A' hA' a' ha' => ?_
    rcases eq_or_ne a' 1 with rfl | ha'1
    · exact one_mem _
    obtain ⟨a, ha, -, han⟩ := exists_inv_mul_mem_rootNorm hR hiso hA hB hAB hA' ha' ha'1
    rw [show a' = a * (a⁻¹ * a') by group]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left ha) (Subgroup.mem_sup_right han)
  have hx' : x ∈ ((A ⊔ rootNorm R A B : Subgroup G) : Set G) := hsub hx
  rw [Subgroup.coe_mul_of_left_le_normalizer_right _ _ hle] at hx'
  obtain ⟨a, ha, n, hn, rfl⟩ := hx'
  exact ⟨a, ha, n, hn, rfl⟩

theorem commutatorElement_mem_rootNorm {n u : G} (hn : n ∈ rootNorm R A B)
    (hu : u ∈ gen (rootClosure R B)) : ⁅n, u⁆ ∈ rootNorm R B A := by
  have hcA := commuting_gen_rootClosure hR hA
  have hcB := commuting_gen_rootClosure hR hB
  have hAT : A ≤ gen (rootClosure R A) := le_gen (mem_rootClosure_self hA)
  have hnT := rootNorm_le_gen A B hn
  have hnA : conjSub A n = A := conjSub_of_forall_commute fun x hx => hcA n hnT x (hAT hx)
  have key : ∀ B' ∈ rootClosure R B, ∀ b ∈ B', ⁅n, b⁆ ∈ rootNorm R B A := by
    intro B' hB' b hb
    rcases eq_or_ne b 1 with rfl | hb1
    · rw [commutatorElement_one_right]
      exact one_mem _
    have hAB' : Opposite A B' :=
      opposite_of_mem_rootClosure hR hiso hA hB hAB (mem_rootClosure_self hA) hB'
    obtain ⟨a, ha, -, hab⟩ := hAB'.2.2 b hb hb1
    have hna : n * a = a * n := (hcA n hnT a (hAT ha)).eq
    set b' := n * b * n⁻¹ with hb'def
    have hB'n : conjSub B' n ∈ rootClosure R B :=
      conjSub_mem_of_mem_stabSet (rootNorm_le_stabSet A B hn) hB'
    have hb' : b' ∈ conjSub B' n := conj_mem_conjSub n hb
    have e1 : conjSub (conjSub B' n) a = conjSub A b' := by
      calc conjSub (conjSub B' n) a = conjSub B' (a * n) := (conjSub_mul B' a n).symm
        _ = conjSub B' (n * a) := by rw [hna]
        _ = conjSub (conjSub B' a) n := conjSub_mul B' n a
        _ = conjSub (conjSub A b) n := by rw [hab]
        _ = conjSub A (n * b) := (conjSub_mul A n b).symm
        _ = conjSub A (b' * n) := by rw [hb'def, inv_mul_cancel_right]
        _ = conjSub (conjSub A n) b' := conjSub_mul A b' n
        _ = conjSub A b' := by rw [hnA]
    have h1 : conjSet (rootClosure R A) b' = conjSet (rootClosure R B) a := by
      rw [← rootClosure_conjSub hR, ← e1, rootClosure_conjSub hR, rootClosure_eq_of_mem hB'n]
    have h2 : conjSet (rootClosure R A) b = conjSet (rootClosure R B) a := by
      rw [← rootClosure_conjSub hR, ← hab, rootClosure_conjSub hR, rootClosure_eq_of_mem hB']
    have hstab : b'⁻¹ * b ∈ stabSet (rootClosure R A) := by
      rw [mem_stabSet, conjSet_mul, h2, ← h1, conjSet_conjSet_inv]
    have hb'T : b' ∈ gen (rootClosure R B) := le_gen hB'n hb'
    have hbT : b ∈ gen (rootClosure R B) := le_gen hB' hb
    have e2 : ⁅n, b⁆ = (b'⁻¹ * b)⁻¹ := by
      rw [commutatorElement_def, mul_inv_rev, inv_inv]
      exact (hcB b' hb'T b⁻¹ (Subgroup.inv_mem _ hbT)).eq
    rw [e2]
    exact Subgroup.inv_mem _ (Subgroup.mem_inf.2
      ⟨Subgroup.mul_mem _ (Subgroup.inv_mem _ hb'T) hbT, hstab⟩)
  refine (gen_induction (p := fun u => u ∈ gen (rootClosure R B) ∧ ⁅n, u⁆ ∈ rootNorm R B A) hu
    (fun B' hB' y hy => ⟨le_gen hB' hy, key B' hB' y hy⟩)
    ⟨one_mem _, by rw [commutatorElement_one_right]; exact one_mem _⟩
    fun y z ⟨hy, h1⟩ ⟨hz, h2⟩ => ⟨Subgroup.mul_mem _ hy hz, ?_⟩).2
  have e : ⁅n, y * z⁆ = ⁅n, y⁆ * (y * ⁅n, z⁆ * y⁻¹) := by
    simp only [commutatorElement_def]
    group
  rw [e, (hcB y hy _ (rootNorm_le_gen B A h2)).eq, mul_inv_cancel_right]
  exact Subgroup.mul_mem _ h1 h2

omit hB hAB in
theorem notMem_rootElts_of_mem_rootNorm (hB : B ∈ omegaSet R A) {x : G}
    (hx : x ∈ rootNorm R A B) : x ∉ rootElts R := by
  rintro ⟨C, hC, hxC, hx1⟩
  have hCA : C ∈ rootClosure R A := by
    refine mem_rootClosure_of_centralSet_subset hR hA hC fun E hE => ⟨hE.1, ?_⟩
    exact commuting_of_forall_commute hR hiso hC hE.1 hxC hx1 fun e he =>
      (commuting_gen_rootClosure_of_mem_centralSet hE) x (rootNorm_le_gen A B hx) e he
  have hCB : Opposite C B :=
    opposite_of_mem_rootClosure hR hiso hA hB.1 hB.2 hCA (mem_rootClosure_self hB.1)
  have hBx : conjSub B x ∈ rootClosure R B :=
    conjSub_mem_of_mem_stabSet (rootNorm_le_stabSet A B hx) (mem_rootClosure_self hB.1)
  have hne : conjSub B x ≠ B := fun h => hx1 (hCB.eq_one_of_conjSub_eq hxC h)
  have hcomm : Commuting B (conjSub B x) :=
    commuting_of_mem_rootClosure (mem_rootClosure_self hB.1)
      (mem_centralSet_of_mem_rootClosure hR hB.1 hBx)
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hB.1
  have heq := hCB.symm.conjSub_eq_of_commute (hR.mul_self B hB.1) (x := 1) (y := x) (one_mem _)
    (Subgroup.mem_sup_right hxC) (by rw [conjSub_one]; exact hb) hb1 (conj_mem_conjSub x hb)
    (fun h => hb1 (conj_eq_one_iff.1 h)) (hcomm b hb _ (conj_mem_conjSub x hb))
  rw [conjSub_one] at heq
  exact hne heq

end RootNorm

section Center

variable [Finite G] (hR : IsRootClass R) (hiso : NoIsolated R) (hnd : IsNondegenerate R)
  (hZ : Subgroup.center G = ⊥) {A B : Subgroup G} (hA : A ∈ R) (hB : B ∈ omegaSet R A)
include hR hiso hnd hZ hA hB

theorem eq_one_of_forall_commute_lambdaSet {z : G}
    (h1 : ∀ E ∈ lambdaSet R A, ∀ e ∈ E, Commute z e) (h2 : ∀ b ∈ B, Commute z b) : z = 1 := by
  have hle : gen (lambdaSet R A) ⊔ B ≤ Subgroup.centralizer {z} := by
    refine sup_le (gen_le fun E hE e he => ?_) fun b hb => ?_
    · exact Subgroup.mem_centralizer_singleton_iff.2 (h1 E hE e he).eq.symm
    · exact Subgroup.mem_centralizer_singleton_iff.2 (h2 b hb).eq.symm
  rw [gen_lambdaSet_sup_eq_top_of hR hiso hnd hA hB] at hle
  have hz : z ∈ Subgroup.center G := Subgroup.mem_center_iff.2 fun g =>
    Subgroup.mem_centralizer_singleton_iff.1 (hle (Subgroup.mem_top g))
  rw [hZ, Subgroup.mem_bot] at hz
  exact hz

theorem rootNorm_inf_rootNorm_eq_bot : rootNorm R A B ⊓ rootNorm R B A = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun z hz => ?_
  refine eq_one_of_forall_commute_lambdaSet hR hiso hnd hZ hA hB (fun E hE e he => ?_)
    fun b hb => ?_
  · exact commuting_gen_rootClosure_of_mem_centralSet ⟨hE.1.1, hE.1.2.2⟩ z
      (rootNorm_le_gen A B (Subgroup.mem_inf.1 hz).1) e he
  · exact commuting_gen_rootClosure hR hB.1 z (rootNorm_le_gen B A (Subgroup.mem_inf.1 hz).2) b
      (le_gen (mem_rootClosure_self hB.1) hb)

theorem commute_of_mem_rootNorm {n m : G} (hn : n ∈ rootNorm R A B) (hm : m ∈ rootNorm R B A) :
    Commute n m := by
  have h1 := commutatorElement_mem_rootNorm hR hiso hA hB.1 hB.2 hn (rootNorm_le_gen B A hm)
  have h2 := commutatorElement_mem_rootNorm hR hiso hB.1 hA hB.2.symm hm (rootNorm_le_gen A B hn)
  have h3 : ⁅n, m⁆ ∈ rootNorm R A B := by
    rw [← commutatorElement_inv]
    exact Subgroup.inv_mem _ h2
  have h4 : ⁅n, m⁆ ∈ rootNorm R A B ⊓ rootNorm R B A := Subgroup.mem_inf.2 ⟨h3, h1⟩
  rw [rootNorm_inf_rootNorm_eq_bot hR hiso hnd hZ hA hB, Subgroup.mem_bot,
    commutatorElement_eq_one_iff_mul_comm] at h4
  exact h4

theorem eq_one_of_commute_of_mem_rootNorm {m a : G} (hm : m ∈ rootNorm R B A) (ha : a ∈ A)
    (ha1 : a ≠ 1) (hc : Commute m a) : m = 1 := by
  have hBR : B ∈ R := hB.1
  have hAm : conjSub A m = A := by
    have hAmR : conjSub A m ∈ R := hR.conjSub_mem hA m
    by_contra hne
    have hmem : a ∈ A ⊓ conjSub A m := by
      refine Subgroup.mem_inf.2 ⟨ha, ?_⟩
      rw [mem_conjSub, mul_assoc, ← hc.eq, inv_mul_cancel_left]
      exact ha
    rw [inf_eq_bot hR hiso hA hAmR (Ne.symm hne), Subgroup.mem_bot] at hmem
    exact ha1 hmem
  have hcA : ∀ a' ∈ A, Commute m a' := by
    intro a' ha'
    have h1 : ⁅m, a'⁆ ∈ A := by
      rw [commutatorElement_def]
      refine A.mul_mem ?_ (A.inv_mem ha')
      rw [← hAm]
      exact conj_mem_conjSub m ha'
    have h2 : ⁅m, a'⁆ ∈ rootNorm R A B := commutatorElement_mem_rootNorm hR hiso hBR hA hB.2.symm
      hm (le_gen (mem_rootClosure_self hA) ha')
    by_contra hne
    have hne' : ⁅m, a'⁆ ≠ 1 := fun h => hne (commutatorElement_eq_one_iff_mul_comm.1 h)
    exact notMem_rootElts_of_mem_rootNorm hR hiso hA hB h2 ⟨A, hA, h1, hne'⟩
  have hAB : A ∈ omegaSet R B := ⟨hA, hB.2.symm⟩
  exact eq_one_of_forall_commute_lambdaSet hR hiso hnd hZ hBR hAB (fun E hE e he =>
    commuting_gen_rootClosure_of_mem_centralSet ⟨hE.1.1, hE.1.2.2⟩ m (rootNorm_le_gen B A hm) e
      he) hcA

theorem injOn_commutatorElement_rootNorm {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Set.InjOn (fun m => ⁅m, a⁆) (rootNorm R B A : Set G) := by
  intro m hm m' hm' h
  have h' : ⁅m, a⁆ = ⁅m', a⁆ := h
  have hc : Commute (m'⁻¹ * m) a := by
    rw [commutatorElement_def, commutatorElement_def, mul_left_inj] at h'
    calc m'⁻¹ * m * a = m'⁻¹ * (m * a * m⁻¹) * m := by group
      _ = m'⁻¹ * (m' * a * m'⁻¹) * m := by rw [h']
      _ = a * (m'⁻¹ * m) := by group
  have := eq_one_of_commute_of_mem_rootNorm hR hiso hnd hZ hA hB
    (Subgroup.mul_mem _ (Subgroup.inv_mem _ hm') hm) ha ha1 hc
  rw [inv_mul_eq_one] at this
  exact this.symm

theorem bijOn_commutatorElement_rootNorm {a : G} (ha : a ∈ A) (ha1 : a ≠ 1) :
    Set.BijOn (fun m => ⁅m, a⁆) (rootNorm R B A : Set G) (rootNorm R A B : Set G) := by
  have hBR : B ∈ R := hB.1
  have hAB : A ∈ omegaSet R B := ⟨hA, hB.2.symm⟩
  have hmaps : Set.MapsTo (fun m => ⁅m, a⁆) (rootNorm R B A : Set G) (rootNorm R A B : Set G) :=
    fun m hm => commutatorElement_mem_rootNorm hR hiso hBR hA hB.2.symm hm
      (le_gen (mem_rootClosure_self hA) ha)
  have hinj := injOn_commutatorElement_rootNorm hR hiso hnd hZ hA hB ha ha1
  obtain ⟨b, hb, hb1⟩ := hR.exists_ne_one hBR
  have hinj' := injOn_commutatorElement_rootNorm hR hiso hnd hZ hBR hAB hb hb1
  have hmaps' : Set.MapsTo (fun n => ⁅n, b⁆) (rootNorm R A B : Set G) (rootNorm R B A : Set G) :=
    fun n hn => commutatorElement_mem_rootNorm hR hiso hA hBR hB.2 hn
      (le_gen (mem_rootClosure_self hBR) hb)
  have hle1 := Set.ncard_le_ncard_of_injOn _ hmaps hinj (Set.toFinite _)
  have hle2 := Set.ncard_le_ncard_of_injOn _ hmaps' hinj' (Set.toFinite _)
  refine ⟨hmaps, hinj, ?_⟩
  have himg : (fun m => ⁅m, a⁆) '' (rootNorm R B A : Set G) = (rootNorm R A B : Set G) := by
    refine Set.eq_of_subset_of_ncard_le (Set.image_subset_iff.2 hmaps) ?_ (Set.toFinite _)
    rw [hinj.ncard_image]
    omega
  intro n hn
  rw [← himg] at hn
  exact hn

theorem mem_rootElts_of_notMem_rootNorm {x : G} (hx : x ∈ gen (rootClosure R A))
    (hxN : x ∉ rootNorm R A B) : x ∈ rootElts R := by
  obtain ⟨a, ha, n, hn, rfl⟩ := exists_mul_eq_of_mem_gen_rootClosure hR hiso hA hB.1 hB.2 hx
  have ha1 : a ≠ 1 := by
    rintro rfl
    rw [one_mul] at hxN
    exact hxN hn
  obtain ⟨m, hm, hmn⟩ := (bijOn_commutatorElement_rootNorm hR hiso hnd hZ hA hB ha ha1).surjOn hn
  have hmn' : ⁅m, a⁆ = n := hmn
  have hcA := commuting_gen_rootClosure hR hA
  refine ⟨conjSub A m, hR.conjSub_mem hA m, ?_, ?_⟩
  · have e : a * n = m * a * m⁻¹ := by
      rw [(hcA a (le_gen (mem_rootClosure_self hA) ha) n (rootNorm_le_gen A B hn)).eq, ← hmn',
        commutatorElement_def]
      group
    rw [e]
    exact conj_mem_conjSub m ha
  · intro h
    exact hxN (h ▸ one_mem _)

theorem coe_rootNorm :
    (rootNorm R A B : Set G) = {x | x ∈ gen (rootClosure R A) ∧ x ∉ rootElts R} := by
  ext x
  exact ⟨fun hx => ⟨rootNorm_le_gen A B hx, notMem_rootElts_of_mem_rootNorm hR hiso hA hB hx⟩,
    fun ⟨hx, hxD⟩ => by_contra fun hxN =>
      hxD (mem_rootElts_of_notMem_rootNorm hR hiso hnd hZ hA hB hx hxN)⟩

theorem rootNorm_eq_radPart : rootNorm R A B = radPart R A := by
  rw [radPart, ← coe_rootNorm hR hiso hnd hZ hA hB, Subgroup.closure_eq]

end Center

end CFSG.Timmesfeld.ARS

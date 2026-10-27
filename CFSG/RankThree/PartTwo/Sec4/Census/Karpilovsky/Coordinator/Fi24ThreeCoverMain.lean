module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24ThreeCoverInputs
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.CoverBounds
public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplierPG
public import CFSG.Sporadic.Bridge.Fi24Surj

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

open CFSG.CosetTable CFSG.Sporadic.Presentation.Fi24Prime CFSG.Sporadic.Recognition.PresentedWords
  CFSG.Sporadic.Recognition.Fi24PrimeMultiplier CFSG.Certificates.CosetEnumeration
  CFSG.RankThree.PerfectCover Subgroup
open scoped commutatorElement

theorem wprod_replicate_true {G : Type*} [Group G] {n : ℕ} (y : Fin n → G) (a : Fin n) (k : ℕ) :
    wprod y (List.replicate k (a, true)) = y a ^ k := by
  induction k with
  | zero => simp
  | succ k ih => rw [List.replicate_succ, wprod_cons, ih]; simp [pow_succ']

theorem wprod_genFam_wsQ (hm0 : m0 = 11) {E : Type*} [Group E] (xh : Fin m0 → E) (ζE : ℕ → E)
    (hA : ∀ v ∈ X0, (!v.any fun l => l.1.val == 8) = true → wprod xh v = 1)
    (hB : wprod xh (X0.getD sqIdx []) = 1)
    (hdef : ∀ k < 11, ζE k = wprod xh (X0.getD (repIdx3.getD k 0) []))
    (h9 : ∀ k, ζE k ^ 9 = 1) (hcomm : ∀ k (g : E), g * ζE k = ζE k * g) :
    ∀ w ∈ wsQ, wprod (genFam xh ζE) w = 1 := by
  intro w hw
  simp only [wsQ, List.mem_append, List.mem_map, List.mem_filter, List.mem_singleton] at hw
  rcases hw with (⟨v, ⟨hvX, hv8⟩, rfl⟩ | rfl) | hw
  · rw [wprod_genFam_liftL hm0]
    exact hA v hvX hv8
  · rw [wprod_genFam_liftL hm0]
    exact hB
  · simp only [centralWords3, List.mem_flatMap, List.mem_append, List.mem_cons, List.mem_map,
      List.mem_range, List.not_mem_nil, or_false] at hw
    obtain ⟨k, hk, hw⟩ := hw
    rcases hw with (rfl | rfl) | ⟨i, hi, rfl⟩
    · rw [wprod_append, wprod_genFam_liftL hm0, wprod_cons, wprod_nil, genFam_zeta hm0 xh ζE hk,
        ← hdef k hk]
      simp
    · rw [wprod_replicate_true, genFam_zeta hm0 xh ζE hk]
      exact h9 k
    · simp only [wprod_cons, wprod_nil, genFam_zeta hm0 xh ζE hk]
      have h := hcomm k (genFam xh ζE (Fin.ofNat nG i))
      have key : ζE k * genFam xh ζE (Fin.ofNat nG i) * (ζE k)⁻¹ *
          (genFam xh ζE (Fin.ofNat nG i))⁻¹ = 1 := by
        calc ζE k * genFam xh ζE (Fin.ofNat nG i) * (ζE k)⁻¹ * (genFam xh ζE (Fin.ofNat nG i))⁻¹
            = (ζE k * genFam xh ζE (Fin.ofNat nG i)) *
              (genFam xh ζE (Fin.ofNat nG i) * ζE k)⁻¹ := by group
          _ = 1 := by rw [h]; simp
      simp only [Bool.false_eq_true, ↓reduceIte, mul_one]
      refine Eq.trans ?_ key
      group

abbrev Q3 : Type := PG nG wsQ

@[expose] def gQ (i : Fin m0) : Fin nG := (liftL (i, true)).1

theorem gQ_val (hm0 : m0 = 11) (i : Fin m0) : (gQ i).val = i.val := by
  have : i.val < 11 := hm0 ▸ i.isLt
  simp only [gQ, liftL]
  exact Nat.mod_eq_of_lt (by unfold nG; omega)

theorem liftL_eq (l : Fin m0 × Bool) : liftL l = (gQ l.1, l.2) := rfl

noncomputable def toG (hm0 : m0 = 11) : Q3 →* PG m0 X0 :=
  pgHom (genFam (fun i : Fin m0 => (PresentedGroup.of i : PG m0 X0)) (fun _ => 1))
    (wprod_genFam_wsQ hm0 _ _ (fun v hv _ => wprod_of_relator hv) (wprod_getD_relator X0 sqIdx)
      (fun k _ => (wprod_getD_relator X0 _).symm) (fun _ => one_pow _) (fun _ g => by simp))

theorem toG_of (hm0 : m0 = 11) (i : Fin m0) :
    toG hm0 (PresentedGroup.of (gQ i)) = PresentedGroup.of i := by
  unfold toG
  rw [pgHom_of, gQ, genFam_liftL hm0]

theorem toG_zeta (hm0 : m0 = 11) {k : ℕ} (hk : k < 11) :
    toG hm0 (PresentedGroup.of (zeta k)) = 1 := by
  unfold toG
  rw [pgHom_of, genFam_zeta hm0 _ _ hk]

theorem toG_surjective (hm0 : m0 = 11) : Function.Surjective (toG hm0) := by
  rw [← MonoidHom.range_eq_top, eq_top_iff, ← PresentedGroup.closure_range_of,
    Subgroup.closure_le]
  rintro _ ⟨i, rfl⟩
  exact ⟨PresentedGroup.of (gQ i), toG_of hm0 i⟩


theorem ne_eight_of_mem {i : Fin m0} (h : i ∈ subsetOf m0 S0) : i.val ≠ 8 := by
  have := mem_subsetOf_iff.1 h
  simp only [S0, List.mem_cons, List.not_mem_nil, or_false] at this
  omega

theorem theta_rels : ∀ v' ∈ X1, wprod (fun j : Fin (subsetOf m0 S0).length =>
    (PresentedGroup.of (gQ ((subsetOf m0 S0).get j)) : Q3)) v' = 1 := by
  intro v' hv'
  obtain ⟨v, hvX, hren⟩ := List.mem_filterMap.1 hv'
  have hmap := map_renumber (subsetOf m0 S0) v v' hren
  have hv8 : (!v.any fun l => l.1.val == 8) = true := by
    rw [Bool.not_eq_true', Bool.eq_false_iff]
    intro h
    obtain ⟨l, hl, hl8⟩ := List.any_eq_true.1 h
    rw [← hmap] at hl
    obtain ⟨l', -, rfl⟩ := List.mem_map.1 hl
    exact ne_eight_of_mem (List.get_mem (subsetOf m0 S0) l'.1) (by simpa using hl8)
  have hmem : v.map liftL ∈ wsQ := by
    simp only [wsQ, List.mem_append, List.mem_map, List.mem_filter]
    exact Or.inl (Or.inl ⟨v, ⟨hvX, hv8⟩, rfl⟩)
  have h1 := wprod_of_relator hmem
  have h2 : v.map liftL = v.map (fun l => (gQ l.1, l.2)) := rfl
  rw [h2, wprod_comp_letters (fun i => gQ i) (fun i => (PresentedGroup.of i : Q3)) v] at h1
  calc _ = wprod (fun i => (PresentedGroup.of (gQ i) : Q3))
        (v'.map fun l => ((subsetOf m0 S0).get l.1, l.2)) :=
        (wprod_comp_letters (fun j => (subsetOf m0 S0).get j)
          (fun i => (PresentedGroup.of (gQ i) : Q3)) v').symm
    _ = 1 := by rw [hmap]; exact h1

noncomputable def theta : PG10 →* Q3 := pgHom _ theta_rels

theorem theta_of (j : Fin (subsetOf m0 S0).length) :
    theta (PresentedGroup.of j) = PresentedGroup.of (gQ ((subsetOf m0 S0).get j)) :=
  pgHom_of _ _ j

theorem genSub_le_range (hm0 : m0 = 11) :
    genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0) ≤
      theta.range := by
  rw [genSub, Subgroup.closure_le]
  rintro _ ⟨i, hi, rfl⟩
  have hi' : i.val ∈ S0 := mem_subsetOf_iff.1 hi
  have hlt : i.val < m0 := by
    simp only [S0, List.mem_cons, List.not_mem_nil, or_false] at hi'
    omega
  have hmem : (⟨i.val, hlt⟩ : Fin m0) ∈ subsetOf m0 S0 := mem_subsetOf_iff.2 hi'
  obtain ⟨j, hj⟩ := List.mem_iff_get.1 hmem
  refine ⟨PresentedGroup.of j, ?_⟩
  rw [theta_of, hj]
  show PresentedGroup.of (gQ ⟨i.val, hlt⟩) = PresentedGroup.of i
  congr 1
  exact Fin.ext (by rw [gQ_val hm0])

theorem card_Q3_le (hm0 : m0 = 11)
    (hindex : (genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).index ≤ 920808) :
    Finite Q3 ∧ Nat.card Q3 ≤ 920808 * 4089470473293004800 := by
  obtain ⟨hfi, hidx⟩ := hindex
  obtain ⟨hf10, hc10⟩ := card_PG10_le
  set H := genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)
  have hle := genSub_le_range hm0
  have hfinR : Finite theta.range := Finite.of_surjective _ theta.rangeRestrict_surjective
  have hfinH : Finite H :=
    Finite.of_injective (Subgroup.inclusion hle) (Subgroup.inclusion_injective hle)
  have hfinQ : Finite Q3 := by
    have : Finite (Q3 ⧸ H) := Subgroup.finite_quotient_of_finiteIndex
    exact Finite.of_subgroup_quotient H
  refine ⟨hfinQ, ?_⟩
  rw [← H.index_mul_card]
  exact Nat.mul_le_mul hidx ((Subgroup.card_le_of_le hle).trans
    ((Nat.card_le_card_of_surjective _ theta.rangeRestrict_surjective).trans hc10))


theorem isPerfect_of_simple_card {X : Type*} [Group X] [IsSimpleGroup X]
    (h : Nat.card X = 1255205709190661721292800) : Group.IsPerfect X := by
  refine Group.isPerfect_def.2 ?_
  by_contra hne
  have hab : ∀ a b : X, a * b = b * a := by
    rcases (Subgroup.commutator_normal (⊤ : Subgroup X) ⊤).eq_bot_or_eq_top with hb | ht
    · intro a b
      have hm : ⁅a, b⁆ ∈ _root_.commutator X :=
        Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
      rw [_root_.commutator_def, hb, Subgroup.mem_bot] at hm
      exact commutatorElement_eq_one_iff_mul_comm.1 hm
    · exact absurd (by rw [_root_.commutator_def]; exact ht) hne
  let _ : CommGroup X := { ‹Group X› with mul_comm := hab }
  have := IsSimpleGroup.prime_card (α := X)
  rw [h] at this
  norm_num at this

theorem nonempty_native_equiv :
    Nonempty (CFSG.Blueprint.NativeSporadic.Fi24prime ≃* PG m0 X0) := by
  have h := CFSG.Sporadic.Bridge.Fi24.nonempty_mulEquiv
  revert h
  show Nonempty (CFSG.Blueprint.NativeSporadic.Fi24prime ≃*
    PresentedGroup TauCeti.SporadicName.Fi24Prime.presentation.relatorSet) → _
  rw [CFSG.Sporadic.Presentation.relatorSet_eq]
  exact id

theorem isPerfect_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y)
    (h : Group.IsPerfect X) : Group.IsPerfect Y :=
  have := h
  Group.IsPerfect.ofSurjective (f := e.toMonoidHom) e.surjective

theorem card_eq_of_equiv {X Y : Type} [Group X] [Group Y] (e : X ≃* Y) :
    Nat.card X = Nat.card Y := Nat.card_congr e.toEquiv

theorem perfect_and_card_G :
    Group.IsPerfect (PG m0 X0) ∧ 1255205709190661721292800 ≤ Nat.card (PG m0 X0) := by
  obtain ⟨e⟩ := nonempty_native_equiv
  have hs := CFSG.Sporadic.Fi24.isSimpleGroup_Fi24prime
  have hc := CFSG.Sporadic.Fi24.card_Fi24prime
  have hperf : Group.IsPerfect CFSG.Blueprint.NativeSporadic.Fi24prime :=
    isPerfect_of_simple_card hc
  have h1 : Group.IsPerfect (PG m0 X0) := isPerfect_of_equiv (X := CFSG.Blueprint.NativeSporadic.Fi24prime) (Y := PG m0 X0) e hperf
  have h2 : Nat.card CFSG.Blueprint.NativeSporadic.Fi24prime = Nat.card (PG m0 X0) :=
    card_eq_of_equiv (X := CFSG.Blueprint.NativeSporadic.Fi24prime) (Y := PG m0 X0) e
  exact ⟨h1, by omega⟩

theorem sq_relator (hsq : (X0.getD sqIdx []).map (fun l => (l.1.val, l.2)) =
      [(8, true), (8, true)]) :
    ∃ g : Fin nG, g.val = 8 ∧ (PresentedGroup.of g : Q3) * PresentedGroup.of g = 1 := by
  have hmem : (X0.getD sqIdx []).map liftL ∈ wsQ := by
    simp [wsQ]
  have h1 := wprod_of_relator hmem
  generalize X0.getD sqIdx [] = w at hsq h1
  rcases w with _ | ⟨l1, _ | ⟨l2, _ | ⟨l3, t⟩⟩⟩
  · simp at hsq
  · simp at hsq
  · simp only [List.map_cons, List.map_nil, List.cons.injEq, Prod.mk.injEq, and_true] at hsq
    obtain ⟨⟨h1v, h1b⟩, h2v, h2b⟩ := hsq
    have hg : gQ l2.1 = gQ l1.1 := Fin.ext (by
      simp only [gQ, liftL]; rw [h1v, h2v])
    refine ⟨gQ l1.1, ?_, ?_⟩
    · simp only [gQ, liftL]
      rw [h1v]; rfl
    · simp only [List.map_cons, List.map_nil, wprod_cons, wprod_nil, liftL_eq, h1b, h2b, hg,
        ite_true, mul_one] at h1
      exact h1
  · simp at hsq

theorem wprod_liftL_eq_one {E : Type*} [Group E] (y : Fin nG → E)
    (hy : ∀ j : Fin m0, y (gQ j) = 1) (w : List (Fin m0 × Bool)) :
    wprod y (w.map liftL) = 1 := by
  induction w with
  | nil => rfl
  | cons l w ih => rw [List.map_cons, wprod_cons, ih, liftL_eq]; simp [hy]

theorem zeta_relator {k : ℕ} (hk : k < 11) :
    (X0.getD (repIdx3.getD k 0) []).map liftL ++ [(zeta k, false)] ∈ wsQ := by
  simp only [wsQ, centralWords3, List.mem_append, List.mem_flatMap, List.mem_cons, List.mem_map,
    List.mem_range, List.not_mem_nil, or_false]
  right
  exact ⟨k, hk, Or.inl (Or.inl rfl)⟩

theorem isPerfect_Q3 (hm0 : m0 = 11)
    (hGperf : Group.IsPerfect (PG m0 X0))
    (hker3 : ∀ k ∈ (toG hm0).ker, k ^ 3 = 1)
    (hsq : (X0.getD sqIdx []).map (fun l => (l.1.val, l.2)) = [(8, true), (8, true)]) :
    Group.IsPerfect Q3 := by
  classical
  have hs := toG_surjective hm0
  set ψ := toG hm0 with hψ
  let f : Q3 →* Abelianization Q3 := Abelianization.of
  have hker : f.ker = _root_.commutator Q3 := Abelianization.ker_of Q3
  have hθ : theta.range ≤ f.ker := by
    have hP := isPerfect_PG10
    rw [hker]
    calc theta.range = (⊤ : Subgroup PG10).map theta := MonoidHom.range_eq_map _
      _ = (_root_.commutator PG10).map theta := by rw [hP.commutator_eq_top]
      _ ≤ _root_.commutator Q3 := by
          rw [_root_.commutator_def, Subgroup.map_commutator]
          rw [_root_.commutator_def]
          exact Subgroup.commutator_mono le_top le_top
  have hS0 : ∀ j : Fin m0, j ∈ subsetOf m0 S0 → f (PresentedGroup.of (gQ j)) = 1 := by
    intro j hj
    obtain ⟨idx, hidx⟩ := List.mem_iff_get.1 hj
    have : PresentedGroup.of (gQ j) ∈ theta.range :=
      ⟨PresentedGroup.of idx, by rw [theta_of, hidx]⟩
    exact MonoidHom.mem_ker.1 (hθ this)
  obtain ⟨g, hg8, hgg⟩ := sq_relator hsq
  have h8 : f (PresentedGroup.of g) = 1 := by
    set a : Q3 := PresentedGroup.of g with ha
    have hmap : (_root_.commutator Q3).map ψ = ⊤ := by
      rw [_root_.commutator_def, Subgroup.map_commutator, Subgroup.map_top,
        MonoidHom.range_eq_top.2 hs]
      have := hGperf.commutator_eq_top
      rwa [_root_.commutator_def] at this
    have hmem : ψ a ∈ (_root_.commutator Q3).map ψ := by rw [hmap]; trivial
    obtain ⟨q, hq, hqa⟩ := hmem
    have hfq : f q = 1 := MonoidHom.mem_ker.1 (hker ▸ hq)
    have hk : q⁻¹ * a ∈ ψ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hqa, inv_mul_cancel]
    have hk3 := hker3 _ hk
    have hfk : f (q⁻¹ * a) = f a := by rw [map_mul, map_inv, hfq, inv_one, one_mul]
    have h3 : f a ^ 3 = 1 := by rw [← hfk, ← map_pow, hk3, map_one]
    have h2 : f a ^ 2 = 1 := by rw [sq, ← map_mul, hgg, map_one]
    calc f a = f a ^ 3 * (f a ^ 2)⁻¹ := by group
      _ = 1 := by rw [h3, h2]; simp
  have hj : ∀ j : Fin m0, f (PresentedGroup.of (gQ j)) = 1 := by
    intro j
    by_cases hj : j ∈ subsetOf m0 S0
    · exact hS0 j hj
    · have hj8 : j.val = 8 := by
        have hlt : j.val < 11 := hm0 ▸ j.isLt
        have := mem_subsetOf_iff.not.1 hj
        simp only [S0, List.mem_cons, List.not_mem_nil, or_false, not_or] at this
        omega
      have : gQ j = g := Fin.ext (by rw [gQ_val hm0, hj8, hg8])
      rw [this]
      exact h8
  have hz : ∀ k < 11, f (PresentedGroup.of (zeta k)) = 1 := by
    intro k hk
    have h := wprod_of_relator (zeta_relator hk)
    rw [wprod_append, wprod_cons, wprod_nil] at h
    simp only [Bool.false_eq_true, ↓reduceIte, mul_one] at h
    have h' := mul_inv_eq_one.1 h
    have := congrArg f h'
    rw [map_wprod f] at this
    rw [← this]
    exact wprod_liftL_eq_one _ hj _
  have hall : ∀ i : Fin nG, f (PresentedGroup.of i) = 1 := by
    intro i
    by_cases hi : i.val < 11
    · have : i = gQ ⟨i.val, by omega⟩ := Fin.ext (by rw [gQ_val hm0])
      rw [this]
      exact hj _
    · have hk : i.val - 11 < 11 := by have := i.isLt; unfold nG at this; omega
      have : i = zeta (i.val - 11) := by
        apply Fin.ext
        simp only [zeta, Fin.val_ofNat]
        have := i.isLt
        unfold nG at this ⊢
        omega
      rw [this]
      exact hz _ hk
  have hf1 : f = 1 := PresentedGroup.ext fun i => by rw [hall i]; rfl
  refine Group.isPerfect_def.2 ?_
  rw [← hker, hf1]
  exact MonoidHom.ker_one

theorem three_dvd_card_hopfMultiplier_PG (hm0 : m0 = 11)
    (hindex : (genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).FiniteIndex ∧
      (genSub {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk} (subsetOf nG S0)).index ≤ 920808)
    (hzeta : 3 ∣ orderOf (PresentedGroup.mk {r : FreeGroup (Fin nG) | r ∈ wsQ.map FreeGroup.mk}
      (FreeGroup.mk (zetaWord 10))))
    (hsq : (X0.getD sqIdx []).map (fun l => (l.1.val, l.2)) = [(8, true), (8, true)]) :
    3 ∣ Nat.card (hopfMultiplier (PG m0 X0)) := by
  obtain ⟨hfinQ, hcardQ⟩ := card_Q3_le hm0 hindex
  obtain ⟨hGperf, hG⟩ := perfect_and_card_G
  have hs := toG_surjective hm0
  set ψ := toG hm0 with hψ
  have hcardQ' := CFSG.GH74.Generic.card_eq_card_mul_card_ker ψ hs
  have hker_le : Nat.card ψ.ker ≤ 3 := by
    by_contra h
    have h4 : 4 ≤ Nat.card ψ.ker := by omega
    have := Nat.mul_le_mul_left (Nat.card (PG m0 X0)) h4
    omega
  have hker_pos : 0 < Nat.card ψ.ker := Nat.card_pos
  set z : Q3 := PresentedGroup.of (zeta 10) with hz
  have hz1 : z ∈ ψ.ker := MonoidHom.mem_ker.2 (toG_zeta hm0 (by norm_num))
  have hord : 3 ∣ orderOf z := hzeta
  have hdvdK : orderOf z ∣ Nat.card ψ.ker := by
    rw [← Subgroup.orderOf_mk z hz1]
    exact orderOf_dvd_natCard _
  have hKeq : Nat.card ψ.ker = 3 :=
    le_antisymm hker_le (Nat.le_of_dvd hker_pos (hord.trans hdvdK))
  have hordz : orderOf z = 3 := Nat.dvd_antisymm (hKeq ▸ hdvdK) hord
  have hzp : zpowers z = ψ.ker := by
    refine Subgroup.eq_of_le_of_card_ge (zpowers_le.2 hz1) ?_
    rw [Nat.card_zpowers, hordz, hKeq]
  have hperf : Group.IsPerfect Q3 := by
    refine isPerfect_Q3 hm0 hGperf (fun k hk => ?_) hsq
    have h := pow_card_eq_one' (G := ψ.ker) (x := ⟨k, hk⟩)
    rw [hKeq] at h
    exact congrArg Subtype.val h
  have hnorm : (zpowers z).Normal := by rw [hzp]; infer_instance
  have hzc : z ∈ center Q3 := mem_center_iff.2 fun g =>
    CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.commute_of_normal_zpowers_of_perfect
      hperf hnorm g
  have hcentral : ψ.ker ≤ center Q3 := hzp ▸ zpowers_le.2 hzc
  have := CFSG.GH74.Generic.card_ker_dvd_hopfMultiplier hperf ψ hs hcentral
  rwa [hKeq] at this

end CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.Fi24Three

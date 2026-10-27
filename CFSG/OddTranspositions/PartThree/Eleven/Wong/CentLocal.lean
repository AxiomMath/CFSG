module

public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentDiag
public import CFSG.OddTranspositions.PartThree.Eleven.Wong.CentSL5
import CFSG.GH74.GLS.SP.GenOrder

public section

namespace CFSG.OddTranspositions.PartThree.Wong

open Subgroup

theorem hM_mul_eq_iff (x : SL5) : hM * x = x * hM ↔ x = 1 ∨ x = -1 ∨ x = hM ∨ x = -hM := by
  rw [eq_comm, ← commute_iff_eq, commute_hM_iff]

theorem hM_mul_eq_neg_iff (x : SL5) :
    hM * x = -(x * hM) ↔ x = cM ∨ x = -cM ∨ x = hM * cM ∨ x = -(hM * cM) := by
  rw [← conj_hM_eq_inv_iff, ← mul_neg, neg_hM, mul_inv_eq_iff_eq_mul, eq_mul_inv_iff_mul_eq,
    eq_inv_mul_iff_mul_eq, mul_assoc]

@[expose] def centHM : Finset SL5 := {1, -1, hM, -hM}

@[expose] def invHM : Finset SL5 := {cM, -cM, hM * cM, -(hM * cM)}

theorem card_centHM_product_union : ((centHM ×ˢ centHM) ∪ (invHM ×ˢ invHM)).card = 32 := by
  rw [Finset.card_union_of_disjoint (Finset.disjoint_product.mpr (Or.inl (by decide))),
    Finset.card_product, Finset.card_product, show centHM.card = 4 by decide,
    show invHM.card = 4 by decide]

theorem card_closure_pair {G : Type*} [Group G] {a b : G} (ha : orderOf a = 2)
    (hb : orderOf b = 2) (hab : Commute a b) (hne : b ≠ a) :
    Nat.card (closure {a, b} : Subgroup G) = 4 := by
  have hle : zpowers b ≤ normalizer (zpowers a : Set G) := by
    refine zpowers_le.mpr (centralizer_le_normalizer _ (mem_centralizer_iff.mpr fun g hg => ?_))
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hg
    exact (hab.zpow_left k).eq
  have hinf : zpowers a ⊓ zpowers b = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    obtain ⟨hga, hgb⟩ := mem_inf.mp hg
    rcases (mem_zpowers_of_orderOf_eq_two hb).mp hgb with h | h
    · rw [h]
      exact one_mem _
    · rcases (mem_zpowers_of_orderOf_eq_two ha).mp hga with h' | h'
      · rw [h']
        exact one_mem _
      · exact absurd (h.symm.trans h') hne
  rw [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure,
    ← Subgroup.zpowers_eq_closure, CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot hle hinf,
    Nat.card_zpowers, Nat.card_zpowers, ha, hb]

theorem sq_eq_one_of_mem_closure {G : Type*} [Group G] {s : Set G}
    (hs : ∀ a ∈ s, ∀ b ∈ s, Commute a b) (hs2 : ∀ a ∈ s, a ^ 2 = 1) {g : G}
    (hg : g ∈ closure s) : g ^ 2 = 1 := by
  have hc : closure s ≤ centralizer (closure s : Set G) := by
    rw [centralizer_closure]
    exact (closure_le _).mpr fun a ha => mem_centralizer_iff.mpr fun b hb => (hs b hb a ha).eq
  induction hg using Subgroup.closure_induction with
  | mem a ha => exact hs2 a ha
  | one => exact one_pow 2
  | mul x y hx hy hx2 hy2 =>
    have hxy : Commute x y := mem_centralizer_iff.mp (hc hy) x hx
    rw [hxy.mul_pow, hx2, hy2, one_mul]
  | inv x _ hx2 => rw [inv_pow, hx2, inv_one]

theorem apply_mem_zpowers_hM {G : Type*} [Group G] (i : SL5 →* G) {x : SL5} (hx : hM * x = x * hM) :
    i x ∈ zpowers (i hM) := by
  rcases (hM_mul_eq_iff x).mp hx with rfl | rfl | rfl | rfl
  · rw [map_one]
    exact one_mem _
  · rw [← hM_sq, map_pow]
    exact pow_mem (mem_zpowers _) 2
  · exact mem_zpowers _
  · rw [neg_hM, map_inv]
    exact inv_mem (mem_zpowers _)

theorem exists_mul_cM_of_hM_mul_eq_neg {x : SL5} (hx : hM * x = -(x * hM)) :
    ∃ s : SL5, hM * s = s * hM ∧ x = s * cM := by
  have h1 : ∀ s : SL5, (s = 1 ∨ s = -1 ∨ s = hM ∨ s = -hM) → hM * s = s * hM :=
    fun s hs => (hM_mul_eq_iff s).mpr hs
  rcases (hM_mul_eq_neg_iff x).mp hx with rfl | rfl | rfl | rfl
  · exact ⟨1, h1 1 (Or.inl rfl), (one_mul _).symm⟩
  · exact ⟨-1, h1 (-1) (Or.inr (Or.inl rfl)), (neg_one_mul _).symm⟩
  · exact ⟨hM, h1 hM (Or.inr (Or.inr (Or.inl rfl))), rfl⟩
  · exact ⟨-hM, h1 (-hM) (Or.inr (Or.inr (Or.inr rfl))), (neg_mul _ _).symm⟩

namespace SwapData

variable {G : Type} [Group G] (D : SwapData G)

theorem v_eq_d : D.v = D.d hM := rfl

theorem w_eq_d : D.w = D.d cM := rfl

theorem d_neg (x : SL5) : D.d (-x) = D.d x := by
  rw [D.d_apply, D.d_apply, D.i1_neg, D.i2_neg, mul_assoc, ← mul_assoc (D.i1 x),
    ← (D.t_commute_i1 x).eq, mul_assoc, ← mul_assoc, D.t_mul_t, one_mul]

theorem prod_mul_prod (x y x' y' : SL5) :
    D.i1 x * D.i2 y * (D.i1 x' * D.i2 y') = D.i1 (x * x') * D.i2 (y * y') := by
  rw [map_mul, map_mul, mul_assoc, ← mul_assoc (D.i2 y), ← (D.commute x' y).eq,
    mul_assoc (D.i1 x'), ← mul_assoc]

theorem prod_mem_centralizer_v_iff (x y : SL5) :
    D.i1 x * D.i2 y ∈ centralizer {D.v} ↔
      (hM * x = x * hM ∧ hM * y = y * hM) ∨ (hM * x = -(x * hM) ∧ hM * y = -(y * hM)) := by
  rw [mem_centralizer_singleton_iff, show D.v = D.i1 hM * D.i2 hM from rfl, D.prod_mul_prod,
    D.prod_mul_prod, D.prod_eq_iff]

theorem t_mem_centralizer_v : D.t ∈ centralizer {D.v} :=
  mem_centralizer_singleton_iff.mpr (D.d_commute_t hM).eq.symm

theorem u_mem_centralizer_v : D.u ∈ centralizer {D.v} :=
  mem_centralizer_singleton_iff.mpr (D.d_commute_u hM).eq.symm

theorem commute_v_w : Commute D.v D.w := by
  show D.d hM * D.d cM = D.d cM * D.d hM
  rw [← map_mul, ← map_mul, (hM_mul_eq_neg_iff cM).mpr (Or.inl rfl), D.d_neg]

theorem t_mem_zpowers_h1 : D.t ∈ zpowers D.h1 := by
  rw [D.t_eq_i1]
  exact apply_mem_zpowers_hM D.i1 (by rw [mul_neg_one, neg_one_mul])

theorem prod_mem_closure_of_mem_centralizer_v {x y : SL5}
    (h : D.i1 x * D.i2 y ∈ centralizer {D.v}) :
    D.i1 x * D.i2 y ∈ closure {D.r, D.h1, D.h2, D.w} := by
  have hh1 : zpowers D.h1 ≤ closure {D.r, D.h1, D.h2, D.w} :=
    zpowers_le.mpr (subset_closure (by simp))
  have hh2 : zpowers D.h2 ≤ closure {D.r, D.h1, D.h2, D.w} :=
    zpowers_le.mpr (subset_closure (by simp))
  have hw : D.w ∈ closure {D.r, D.h1, D.h2, D.w} := subset_closure (by simp)
  rcases (D.prod_mem_centralizer_v_iff x y).mp h with ⟨hx, hy⟩ | ⟨hx, hy⟩
  · exact mul_mem (hh1 (apply_mem_zpowers_hM D.i1 hx)) (hh2 (apply_mem_zpowers_hM D.i2 hy))
  · obtain ⟨s, hs, rfl⟩ := exists_mul_cM_of_hM_mul_eq_neg hx
    obtain ⟨s', hs', rfl⟩ := exists_mul_cM_of_hM_mul_eq_neg hy
    rw [← D.prod_mul_prod]
    exact mul_mem (mul_mem (hh1 (apply_mem_zpowers_hM D.i1 hs))
      (hh2 (apply_mem_zpowers_hM D.i2 hs'))) hw

theorem u_mem_closure : D.u ∈ closure {D.r, D.h1, D.h2, D.w} := by
  have ht : D.t ∈ closure {D.r, D.h1, D.h2, D.w} :=
    zpowers_le.mpr (subset_closure (by simp)) D.t_mem_zpowers_h1
  have hu : D.u = D.t * D.r := by
    rw [show D.r = D.t * D.u from rfl, ← mul_assoc, D.t_mul_t, one_mul]
  rw [hu]
  exact mul_mem ht (subset_closure (by simp))

private theorem gens_mem_centralizer_t_inf_v :
    ({D.r, D.h1, D.h2, D.w} : Set G) ⊆ centralizer {D.t} ⊓ centralizer {D.v} := by
  have hct : D.t ∈ centralizer {D.t} := mem_centralizer_singleton_iff.mpr rfl
  rintro g (rfl | rfl | rfl | rfl)
  · exact mem_inf.mpr ⟨mul_mem hct D.u_mem_centralizer_t,
      mul_mem D.t_mem_centralizer_v D.u_mem_centralizer_v⟩
  · refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (D.t_commute_i1 hM).eq.symm, ?_⟩
    have := (D.prod_mem_centralizer_v_iff hM 1).mpr (Or.inl ⟨rfl, by rw [mul_one, one_mul]⟩)
    rwa [map_one, mul_one] at this
  · refine mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (D.t_commute_i2 hM).eq.symm, ?_⟩
    have := (D.prod_mem_centralizer_v_iff 1 hM).mpr (Or.inl ⟨by rw [mul_one, one_mul], rfl⟩)
    rwa [map_one, one_mul] at this
  · have hc := (hM_mul_eq_neg_iff cM).mpr (Or.inl rfl)
    exact mem_inf.mpr ⟨mem_centralizer_singleton_iff.mpr (D.d_commute_t cM).eq,
      (D.prod_mem_centralizer_v_iff cM cM).mpr (Or.inr ⟨hc, hc⟩)⟩

theorem centralizer_t_inf_centralizer_v [Finite G] :
    centralizer {D.t} ⊓ centralizer {D.v} = closure {D.r, D.h1, D.h2, D.w} := by
  refine le_antisymm (fun g hg => ?_) ((closure_le _).mpr D.gens_mem_centralizer_t_inf_v)
  obtain ⟨hgt, hgv⟩ := mem_inf.mp hg
  rcases D.mem_centralizer_t_iff.mp hgt with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
  · exact D.prod_mem_closure_of_mem_centralizer_v hgv
  · have h := mul_mem hgv (inv_mem D.u_mem_centralizer_v)
    rw [mul_inv_cancel_right] at h
    exact mul_mem (D.prod_mem_closure_of_mem_centralizer_v h) D.u_mem_closure

theorem card_K_inf_centralizer_v : Nat.card (D.K ⊓ centralizer {D.v} : Subgroup G) = 16 := by
  have hmap : (comap (prodHom D.commute) (centralizer {D.v})).map (prodHom D.commute) =
      D.K ⊓ centralizer {D.v} := by
    rw [map_comap_eq, range_prodHom]
    rfl
  have hker : (prodHom D.commute).ker ≤ comap (prodHom D.commute) (centralizer {D.v}) :=
    fun p hp => by
      rw [mem_comap, MonoidHom.mem_ker.mp hp]
      exact one_mem _
  have hset : ((comap (prodHom D.commute) (centralizer {D.v}) : Subgroup (SL5 × SL5)) :
      Set (SL5 × SL5)) = ↑((centHM ×ˢ centHM) ∪ (invHM ×ˢ invHM)) := by
    ext ⟨x, y⟩
    simp only [SetLike.mem_coe, mem_comap, prodHom_apply, Finset.coe_union, Finset.coe_product,
      Set.mem_union, Set.mem_prod]
    rw [D.prod_mem_centralizer_v_iff, hM_mul_eq_iff, hM_mul_eq_iff, hM_mul_eq_neg_iff,
      hM_mul_eq_neg_iff]
    simp only [centHM, invHM, Finset.mem_insert, Finset.mem_singleton]
  have hQ : Nat.card (comap (prodHom D.commute) (centralizer {D.v})) = 32 := by
    rw [← SetLike.coe_sort_coe, hset, Nat.card_coe_set_eq, Set.ncard_coe_finset,
      card_centHM_product_union]
  have h := relIndex_mul_card (H := (prodHom D.commute).ker)
    (K := comap (prodHom D.commute) (centralizer {D.v}))
  rw [relIndex_ker, hmap, inf_eq_left.mpr hker,
    card_ker_prodHom D.inj1 D.inj2 D.orderOf_t D.commute D.range_inf, hQ] at h
  omega

private theorem centralizer_t_inf_v_eq_sup [Finite G] :
    centralizer {D.t} ⊓ centralizer {D.v} = (D.K ⊓ centralizer {D.v}) ⊔ zpowers D.u := by
  refine le_antisymm (fun g hg => ?_) (sup_le (inf_le_inf_right _ ?_) ?_)
  · obtain ⟨hgt, hgv⟩ := mem_inf.mp hg
    rcases D.mem_centralizer_t_iff.mp hgt with ⟨x, y, rfl⟩ | ⟨x, y, rfl⟩
    · exact mem_sup_left (mem_inf.mpr ⟨D.mem_K_iff.mpr ⟨x, y, rfl⟩, hgv⟩)
    · have h := mul_mem hgv (inv_mem D.u_mem_centralizer_v)
      rw [mul_inv_cancel_right] at h
      exact mul_mem (mem_sup_left (mem_inf.mpr ⟨D.mem_K_iff.mpr ⟨x, y, rfl⟩, h⟩))
        (mem_sup_right (mem_zpowers _))
  · intro g hg
    obtain ⟨x, y, rfl⟩ := D.mem_K_iff.mp hg
    rw [D.mem_centralizer_t_iff]
    exact Or.inl ⟨x, y, rfl⟩
  · exact zpowers_le.mpr (mem_inf.mpr ⟨D.u_mem_centralizer_t, D.u_mem_centralizer_v⟩)

theorem card_centralizer_t_inf_centralizer_v [Finite G] :
    Nat.card (centralizer {D.t} ⊓ centralizer {D.v} : Subgroup G) = 32 := by
  have hN : D.u ∈ normalizer ((D.K ⊓ centralizer {D.v} : Subgroup G) : Set G) := by
    refine mem_normalizer_iff.mpr fun g => ?_
    rw [mem_inf, mem_inf, mem_normalizer_iff.mp D.u_mem_normalizer_K g,
      mem_normalizer_iff.mp (le_normalizer D.u_mem_centralizer_v) g]
  have hinf : (D.K ⊓ centralizer {D.v}) ⊓ zpowers D.u = ⊥ := by
    refine eq_bot_iff.mpr fun g hg => ?_
    obtain ⟨hgK, hgu⟩ := mem_inf.mp hg
    rcases (mem_zpowers_of_orderOf_eq_two D.orderOf_u).mp hgu with h | h
    · rw [h]
      exact one_mem _
    · exact absurd (h ▸ (mem_inf.mp hgK).1) D.u_not_mem
  rw [D.centralizer_t_inf_v_eq_sup, CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot
    (zpowers_le.mpr hN) hinf, D.card_K_inf_centralizer_v, Nat.card_zpowers, D.orderOf_u]

theorem orderOf_v : orderOf D.v = 2 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [D.v_eq_d, ← map_pow, hM_sq, D.d_neg, map_one]
  · rw [D.v_eq_d, D.d_apply] at h
    rcases (diag_eq_one_iff D.inj1 D.inj2 D.orderOf_t D.range_inf).mp h with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)

theorem orderOf_w : orderOf D.w = 2 := by
  refine orderOf_eq_prime ?_ fun h => ?_
  · rw [D.w_eq_d, ← map_pow, cM_sq, D.d_neg, map_one]
  · rw [D.w_eq_d, D.d_apply] at h
    rcases (diag_eq_one_iff D.inj1 D.inj2 D.orderOf_t D.range_inf).mp h with h | h
    · exact absurd h (by decide)
    · exact absurd h (by decide)

theorem w_ne_v : D.w ≠ D.v := by
  intro h
  rw [D.w_eq_d, D.v_eq_d, ← mul_inv_eq_one, ← map_inv, ← map_mul, D.d_apply] at h
  rcases (diag_eq_one_iff D.inj1 D.inj2 D.orderOf_t D.range_inf).mp h with h | h
  · exact absurd h (by decide)
  · exact absurd h (by decide)

theorem u_ne_t : D.u ≠ D.t := fun h => D.u_not_mem (by rw [h]; exact D.t_mem_K)

theorem J_le_A : D.J ≤ D.A := by
  refine (closure_le _).mpr ?_
  rintro _ (rfl | rfl)
  exacts [⟨hM, rfl⟩, ⟨cM, rfl⟩]

theorem card_J : Nat.card D.J = 4 :=
  card_closure_pair D.orderOf_v D.orderOf_w D.commute_v_w D.w_ne_v

theorem E_eq_sup : D.E = closure {D.t, D.u} ⊔ D.J := by
  rw [show D.E = closure {D.t, D.u, D.v, D.w} from rfl, show D.J = closure {D.v, D.w} from rfl,
    ← Subgroup.closure_union, Set.insert_union, Set.singleton_union]

private theorem commute_gens_E {a b : G} (ha : a ∈ ({D.t, D.u, D.v, D.w} : Set G))
    (hb : b ∈ ({D.t, D.u, D.v, D.w} : Set G)) : Commute a b := by
  have h : Commute D.t b ∧ Commute D.u b ∧ Commute D.v b ∧ Commute D.w b := by
    rcases hb with rfl | rfl | rfl | rfl
    · exact ⟨Commute.refl _, D.t_commute_u.symm, D.d_commute_t hM, D.d_commute_t cM⟩
    · exact ⟨D.t_commute_u, Commute.refl _, D.d_commute_u hM, D.d_commute_u cM⟩
    · exact ⟨(D.d_commute_t hM).symm, (D.d_commute_u hM).symm, Commute.refl _,
        D.commute_v_w.symm⟩
    · exact ⟨(D.d_commute_t cM).symm, (D.d_commute_u cM).symm, D.commute_v_w, Commute.refl _⟩
  obtain ⟨h1, h2, h3, h4⟩ := h
  rcases ha with rfl | rfl | rfl | rfl
  exacts [h1, h2, h3, h4]

theorem sq_eq_one_of_mem_E {x : G} (hx : x ∈ D.E) : x ^ 2 = 1 := by
  refine sq_eq_one_of_mem_closure (fun a ha b hb => D.commute_gens_E ha hb) ?_ hx
  have h2 : ∀ g : G, orderOf g = 2 → g ^ 2 = 1 := fun g hg => by
    have := pow_orderOf_eq_one g
    rwa [hg] at this
  rintro a (rfl | rfl | rfl | rfl)
  exacts [h2 _ D.orderOf_t, h2 _ D.orderOf_u, h2 _ D.orderOf_v, h2 _ D.orderOf_w]

theorem J_le_centralizer_closure_t_u : D.J ≤ centralizer (closure {D.t, D.u} : Set G) := by
  rw [centralizer_closure]
  refine (closure_le _).mpr fun a ha => mem_centralizer_iff.mpr fun b hb => ?_
  exact (D.commute_gens_E (by rcases hb with rfl | rfl <;> simp)
    (by rcases ha with rfl | rfl <;> simp)).eq

theorem card_E : Nat.card D.E = 16 := by
  have hJc := D.J_le_centralizer_closure_t_u
  have hinf : closure {D.t, D.u} ⊓ D.J = ⊥ :=
    eq_bot_iff.mpr ((inf_le_inf_left _ D.J_le_A).trans D.closure_t_u_inf_A.le)
  rw [D.E_eq_sup, CFSG.GH74.GLS.SP.card_sup_of_inf_eq_bot
    (fun g hg => centralizer_le_normalizer _ (hJc hg)) hinf,
    card_closure_pair D.orderOf_t D.orderOf_u D.t_commute_u D.u_ne_t, D.card_J]

theorem d_mem_J_of_mem_centralizer_v {x : SL5} (h : D.d x ∈ centralizer {D.v}) :
    D.d x ∈ D.J := by
  have hv : D.v ∈ D.J := subset_closure (Set.mem_insert _ _)
  have hw : D.w ∈ D.J := subset_closure (Set.mem_insert_of_mem _ rfl)
  rcases (D.prod_mem_centralizer_v_iff x x).mp h with ⟨hx, -⟩ | ⟨hx, -⟩
  · rcases (hM_mul_eq_iff x).mp hx with rfl | rfl | rfl | rfl
    · rw [map_one]
      exact one_mem _
    · rw [D.d_neg, map_one]
      exact one_mem _
    · exact hv
    · rw [D.d_neg]
      exact hv
  · rcases (hM_mul_eq_neg_iff x).mp hx with rfl | rfl | rfl | rfl
    · exact hw
    · rw [D.d_neg]
      exact hw
    · rw [map_mul]
      exact mul_mem hv hw
    · rw [D.d_neg, map_mul]
      exact mul_mem hv hw

theorem closure_t_u_le_normalizer_A : closure {D.t, D.u} ≤ normalizer (D.A : Set G) := by
  refine (closure_le _).mpr ?_
  rintro _ (rfl | rfl) <;> refine centralizer_le_normalizer _ (mem_centralizer_iff.mpr ?_) <;>
    rintro _ ⟨x, rfl⟩
  exacts [(D.d_commute_t x).eq, (D.d_commute_u x).eq]

theorem centralizer_t_u_v [Finite G] : centralizer ({D.t, D.u, D.v} : Set G) = D.E := by
  refine le_antisymm (fun g hg => ?_) ((closure_le _).mpr fun a ha =>
    mem_centralizer_iff.mpr fun b hb => (D.commute_gens_E
      (by rcases hb with rfl | rfl | rfl <;> simp) ha).eq)
  have hmem := mem_centralizer_iff.mp hg
  have hc : ∀ k ∈ ({D.t, D.u, D.v} : Set G), g ∈ centralizer {k} := fun k hk =>
    mem_centralizer_singleton_iff.mpr (hmem k hk).symm
  have hg' : g ∈ closure {D.t, D.u} ⊔ D.A := by
    rw [← D.centralizer_t_inf_centralizer_u]
    exact mem_inf.mpr ⟨hc _ (by simp), hc _ (by simp)⟩
  rw [← SetLike.mem_coe, coe_mul_of_left_le_normalizer_right _ _ D.closure_t_u_le_normalizer_A,
    Set.mem_mul] at hg'
  obtain ⟨c, hcm, _, ⟨x, rfl⟩, rfl⟩ := hg'
  have hcv : c ∈ centralizer {D.v} := (closure_le _).mpr (by
    rintro _ (rfl | rfl)
    exacts [D.t_mem_centralizer_v, D.u_mem_centralizer_v]) hcm
  have hdv := mul_mem (inv_mem hcv) (hc D.v (by simp))
  rw [inv_mul_cancel_left] at hdv
  rw [D.E_eq_sup]
  exact mul_mem (mem_sup_left hcm) (mem_sup_right (D.d_mem_J_of_mem_centralizer_v hdv))

end SwapData

end CFSG.OddTranspositions.PartThree.Wong

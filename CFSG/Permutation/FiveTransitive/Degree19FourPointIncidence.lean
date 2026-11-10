module

public import CFSG.Permutation.FiveTransitive.Degree19FiveNormalizer

public section

namespace CFSG

namespace FiveTransitive.Degree19

open MulAction Subgroup
open scoped Pointwise

abbrev SylowFixesEmbedding
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p m : ℕ)
    (e : Fin m ↪ X) :=
  {S : Sylow p P //
    (S : Subgroup P) ≤ fixingSubgroup P (Set.range e)}

noncomputable instance sylowFixesEmbeddingFintype
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p m : ℕ)
    [Fact p.Prime] (e : Fin m ↪ X) :
    Fintype (SylowFixesEmbedding P p m e) :=
  Fintype.ofFinite _

theorem smul_range_embedding
    {G X : Type} [Group G] [MulAction G X]
    {m : ℕ} (g : G) (e : Fin m ↪ X) :
    g • Set.range e = Set.range (g • e) := by
  ext x
  constructor
  · rintro ⟨y, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, rfl⟩
  · rintro ⟨i, rfl⟩
    exact ⟨e i, ⟨i, rfl⟩, rfl⟩

private noncomputable def sylowFixesEmbeddingConjEquiv
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p m : ℕ)
    (g : P) (e : Fin m ↪ X) :
    SylowFixesEmbedding P p m e ≃
      SylowFixesEmbedding P p m (g • e) where
  toFun S := ⟨g • S.1, by
    rw [Sylow.coe_subgroup_smul, ← smul_range_embedding g e,
      SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj]
    exact Subgroup.map_mono S.2⟩
  invFun S := ⟨g⁻¹ • S.1, by
    have hrange :
        g⁻¹ • Set.range (g • e) = Set.range e := by
      rw [smul_range_embedding]
      exact congrArg (fun z : Fin m ↪ X => Set.range z)
        (inv_smul_smul g e)
    rw [Sylow.coe_subgroup_smul, ← hrange,
      SubMulAction.fixingSubgroup_smul_eq_fixingSubgroup_map_conj]
    exact Subgroup.map_mono S.2⟩
  left_inv S := by
    apply Subtype.ext
    exact inv_smul_smul g S.1
  right_inv S := by
    apply Subtype.ext
    exact smul_inv_smul g S.1

theorem card_sylowFixesEmbedding_eq_of_smul_eq
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p m : ℕ)
    [Fact p.Prime]
    (g : P) (e e' : Fin m ↪ X) (hge : g • e = e') :
    Fintype.card (SylowFixesEmbedding P p m e) =
      Fintype.card (SylowFixesEmbedding P p m e') := by
  subst e'
  exact Fintype.card_congr
    (sylowFixesEmbeddingConjEquiv P p m g e)

theorem card_sylowFixesEmbedding_eq_of_pretransitive
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p m : ℕ)
    [Fact p.Prime]
    (hm : MulAction.IsMultiplyPretransitive P X m)
    (e e' : Fin m ↪ X) :
    Fintype.card (SylowFixesEmbedding P p m e) =
      Fintype.card (SylowFixesEmbedding P p m e') := by
  obtain ⟨g, hg⟩ := hm.exists_smul_eq e e'
  exact card_sylowFixesEmbedding_eq_of_smul_eq
    P p m g e e' hg

private noncomputable def sylowEmbeddingIncidenceEquiv
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p m : ℕ) :
    (Σ e : Fin m ↪ X, SylowFixesEmbedding P p m e) ≃
      (Σ S : Sylow p P,
        MulAction.fixedPoints S (Fin m ↪ X)) where
  toFun z := ⟨z.2.1, ⟨z.1, by
    rw [MulAction.mem_fixedPoints]
    intro q
    apply Function.Embedding.ext
    intro i
    have hq := z.2.2 q.prop
    rw [mem_fixingSubgroup_iff] at hq
    exact hq (z.1 i) ⟨i, rfl⟩⟩⟩
  invFun z := ⟨z.2.1, ⟨z.1, by
    intro q hq
    rw [mem_fixingSubgroup_iff]
    intro x hx
    obtain ⟨i, rfl⟩ := hx
    have hfixed := z.2.2 ⟨q, hq⟩
    exact congrArg (fun e : Fin m ↪ X => e i) hfixed⟩⟩
  left_inv z := by
    rcases z with ⟨e, S, hS⟩
    rfl
  right_inv z := by
    rcases z with ⟨S, e, he⟩
    rfl

private theorem card_embedding_mul_card_sylowFixesEmbedding
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (p m f : ℕ)
    [Fact p.Prime]
    (hm : MulAction.IsMultiplyPretransitive P X m)
    (hfixed :
      ∀ S : Sylow p P,
        Nat.card
          (MulAction.fixedPoints S (Fin m ↪ X)) = f)
    (e₀ : Fin m ↪ X) :
    Fintype.card (Fin m ↪ X) *
        Fintype.card (SylowFixesEmbedding P p m e₀) =
      Nat.card (Sylow p P) * f := by
  classical
  let E := Fin m ↪ X
  letI : Fintype (Sylow p P) :=
    Fintype.ofFinite _
  letI (S : Sylow p P) :
      Fintype (MulAction.fixedPoints S E) :=
    Fintype.ofFinite _
  let c :=
    Fintype.card (SylowFixesEmbedding P p m e₀)
  have hfiber (e : E) :
      Fintype.card (SylowFixesEmbedding P p m e) = c :=
    card_sylowFixesEmbedding_eq_of_pretransitive
      P p m hm e e₀
  have hleft :
      Fintype.card
          (Σ e : E, SylowFixesEmbedding P p m e) =
        Fintype.card E * c := by
    rw [Fintype.card_sigma]
    simp_rw [hfiber]
    simp
  have hright :
      Fintype.card
          (Σ S : Sylow p P,
            MulAction.fixedPoints S E) =
        Nat.card (Sylow p P) * f := by
    have hfixed' (S : Sylow p P) :
        Fintype.card (MulAction.fixedPoints S E) = f := by
      rw [← Nat.card_eq_fintype_card]
      exact hfixed S
    rw [Fintype.card_sigma]
    simp_rw [hfixed']
    rw [Finset.sum_const, Finset.card_univ,
      ← Nat.card_eq_fintype_card]
    exact nsmul_eq_mul (Nat.card (Sylow p P)) f
  calc
    Fintype.card E * c =
        Fintype.card
          (Σ e : E, SylowFixesEmbedding P p m e) :=
      hleft.symm
    _ = Fintype.card
          (Σ S : Sylow p P,
            MulAction.fixedPoints S E) :=
      Fintype.card_congr
        (sylowEmbeddingIncidenceEquiv P p m)
    _ = Nat.card (Sylow p P) * f :=
      hright

private theorem card_fixedPoints_sylowFive_four_embeddings_eq_twentyFour
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (h : ℕ) (hPcard : Nat.card P = 1395360 * h)
    (hnotFive : ¬5 ∣ h)
    (S : Sylow 5 P) :
    Nat.card
        (MulAction.fixedPoints S (Fin 4 ↪ X)) = 24 := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hScard : Nat.card S = 5 :=
    sylow_five_card_eq_five P h hPcard hnotFive S
  letI : IsCyclic S :=
    isCyclic_of_prime_card hScard
  obtain ⟨u, huorder⟩ :=
    IsCyclic.exists_ofOrder_eq_natCard (α := S)
  have huorderS : orderOf u = 5 :=
    huorder.trans hScard
  have huNe : u ≠ 1 := by
    intro hu
    rw [hu, orderOf_one] at huorderS
    norm_num at huorderS
  have huorderP : orderOf (u : P) = 5 := by
    calc
      orderOf (u : P) = orderOf u :=
        Subgroup.orderOf_coe _
      _ = 5 := huorderS
  have husupport :
      ((u : P) : Equiv.Perm X).support.card = 15 :=
    support_card_eq_fifteen_of_order_five_of_not_alternating
      X P hcard h5 hnotAlt (u : P) huorderP
  have hfixedX :
      Fintype.card (MulAction.fixedBy X (u : P)) = 4 := by
    rw [Degree15.card_fixedBy_subgroup_perm, hcard,
      husupport]
  have hfixedSet :
      MulAction.fixedPoints S (Fin 4 ↪ X) =
        MulAction.fixedBy (Fin 4 ↪ X) (u : P) := by
    ext e
    constructor
    · intro he
      exact he u
    · intro he q
      have hqgen : q ∈ Subgroup.zpowers u :=
        mem_zpowers_of_prime_card hScard huNe
      obtain ⟨z, hz⟩ :=
        Subgroup.mem_zpowers_iff.mp hqgen
      rw [← hz]
      exact MulAction.mem_fixedBy_zpow he z
  rw [hfixedSet, Nat.card_eq_fintype_card]
  calc
    Fintype.card
        (MulAction.fixedBy (Fin 4 ↪ X) (u : P)) =
        (Fintype.card
          (MulAction.fixedBy X (u : P))).descFactorial
            (Fintype.card (Fin 4)) :=
      Degree15.card_fixedBy_embedding
        (G := P) (X := X) (I := Fin 4) (u : P)
    _ = 24 := by
      rw [hfixedX, Fintype.card_fin]
      norm_num [Nat.descFactorial]

private theorem card_sylowFixesEmbedding_eq_three_mul_stabilizer
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (e : Fin 4 ↪ X) :
    Nat.card (SylowFixesEmbedding P 5 4 e) =
      3 * Nat.card (fixingSubgroup P s) := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  have hnotFive : ¬5 ∣ h :=
    five_not_dvd_five_point_stabilizer_of_not_alternating
      X P hcard h5 hnotAlt s hs
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hfixIndex := hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hfixIndex
  norm_num at hfixIndex
  have hHindex : H.index = 1395360 := by
    change (fixingSubgroup P s).index = 1395360
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 1395360 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let S : Sylow 5 P := Sylow.nonempty.some
  have hnormalizer :
      Nat.card (Subgroup.normalizer (S : Set P)) = 120 :=
    (sylow_five_normalizer_card_eq_one_twenty
      X P hcard h5 hnotAlt s hs S).1
  have hsylowCard :
      Nat.card (Sylow 5 P) = 11628 * h := by
    rw [S.card_eq_index_normalizer]
    have hindexCard :=
      (Subgroup.normalizer (S : Set P)).index_mul_card
    rw [hnormalizer, hPcard] at hindexCard
    omega
  have hP4 : MulAction.IsMultiplyPretransitive P X 4 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 4) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hfixed (T : Sylow 5 P) :
      Nat.card
          (MulAction.fixedPoints T (Fin 4 ↪ X)) = 24 :=
    card_fixedPoints_sylowFive_four_embeddings_eq_twentyFour
      X P hcard h5 hnotAlt h hPcard hnotFive T
  have hdouble :=
    card_embedding_mul_card_sylowFixesEmbedding
      P 5 4 24 hP4 hfixed e
  rw [Fintype.card_embedding_eq, Fintype.card_fin,
    hcard, hsylowCard] at hdouble
  norm_num [Nat.descFactorial] at hdouble
  change
    Nat.card (SylowFixesEmbedding P 5 4 e) =
      3 * h
  rw [Nat.card_eq_fintype_card]
  omega

private noncomputable def extendSylowThroughSubtype
    {G : Type} [Group G] {p : ℕ}
    (H : Subgroup G) (T : Sylow p H) :
    Sylow p G :=
  Classical.choose T.exists_comap_subtype_eq

private theorem extendSylowThroughSubtype_comap
    {G : Type} [Group G] {p : ℕ}
    (H : Subgroup G) (T : Sylow p H) :
    (extendSylowThroughSubtype H T).comap H.subtype = T :=
  Classical.choose_spec T.exists_comap_subtype_eq

private theorem extendSylowThroughSubtype_le
    {G : Type} [Group G] [Fintype G] {p : ℕ}
    (H : Subgroup G)
    (hglobal : ∀ Q : Sylow p G, Nat.card Q = p)
    (hlocal : ∀ T : Sylow p H, Nat.card T = p)
    (T : Sylow p H) :
    (extendSylowThroughSubtype H T : Subgroup G) ≤ H := by
  let Q := extendSylowThroughSubtype H T
  have hmapLe :
      (T : Subgroup H).map H.subtype ≤
        (Q : Subgroup G) := by
    rw [Subgroup.map_le_iff_le_comap,
      extendSylowThroughSubtype_comap]
  have hmapCard :
      Nat.card ((T : Subgroup H).map H.subtype) = p := by
    calc
      Nat.card ((T : Subgroup H).map H.subtype) =
          Nat.card T :=
        Nat.card_congr
          ((T : Subgroup H).equivMapOfInjective
            H.subtype H.subtype_injective).toEquiv.symm
      _ = p := hlocal T
  have hmapEq :
      (T : Subgroup H).map H.subtype =
        (Q : Subgroup G) :=
    Subgroup.eq_of_le_of_card_ge hmapLe (by
      rw [hmapCard, hglobal Q])
  rw [← hmapEq]
  exact Subgroup.map_subtype_le (T : Subgroup H)

private noncomputable def sylowSubtypeEquiv
    {G : Type} [Group G] [Fintype G] {p : ℕ}
    (H : Subgroup G)
    (hglobal : ∀ Q : Sylow p G, Nat.card Q = p)
    (hlocal : ∀ T : Sylow p H, Nat.card T = p) :
    Sylow p H ≃ {Q : Sylow p G // (Q : Subgroup G) ≤ H} where
  toFun T :=
    ⟨extendSylowThroughSubtype H T,
      extendSylowThroughSubtype_le H hglobal hlocal T⟩
  invFun Q := Q.1.subtype Q.2
  left_inv T := by
    apply Sylow.ext
    exact extendSylowThroughSubtype_comap H T
  right_inv Q := by
    let T := Q.1.subtype Q.2
    let R := extendSylowThroughSubtype H T
    have hRle : (R : Subgroup G) ≤ H :=
      extendSylowThroughSubtype_le H hglobal hlocal T
    have hsubtype :
        R.subtype hRle = Q.1.subtype Q.2 := by
      apply Sylow.ext
      exact extendSylowThroughSubtype_comap H T
    have hRQ : R = Q.1 :=
      Sylow.subtype_injective hsubtype
    change
      (⟨R, hRle⟩ :
        {Q : Sylow p G // (Q : Subgroup G) ≤ H}) = Q
    exact Subtype.ext hRQ

theorem sylow_five_card_eq_five_of_card_eq_fifteen_mul
    (K : Type) [Group K] [Fintype K]
    (h : ℕ) (hKcard : Nat.card K = 15 * h)
    (hnotFive : ¬5 ∣ h)
    (T : Sylow 5 K) :
    Nat.card T = 5 := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hh : h ≠ 0 := by
    intro hz
    subst h
    exact hnotFive (dvd_zero 5)
  have hfactorization :
      (15 * h).factorization 5 = 1 := by
    rw [show 15 = 5 * 3 by norm_num,
      Nat.mul_assoc,
      Nat.factorization_mul (by norm_num)
        (Nat.mul_ne_zero (by norm_num) hh),
      Finsupp.add_apply,
      (show Nat.Prime 5 by norm_num).factorization,
      Finsupp.single_eq_same,
      Nat.factorization_mul (by norm_num) hh,
      Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num),
      Nat.factorization_eq_zero_of_not_dvd hnotFive]
    norm_num
  rw [T.card_eq_multiplicity, hKcard,
    hfactorization]
  norm_num

private theorem four_point_stabilizer_sylowFive_card
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (e : Fin 4 ↪ X) :
    let K := fixingSubgroup P (Set.range e)
    Nat.card (Sylow 5 K) =
      3 * Nat.card (fixingSubgroup P s) := by
  classical
  dsimp
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  let K : Subgroup P :=
    fixingSubgroup P (Set.range e)
  have hnotFive : ¬5 ∣ h :=
    five_not_dvd_five_point_stabilizer_of_not_alternating
      X P hcard h5 hnotAlt s hs
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hP4 : MulAction.IsMultiplyPretransitive P X 4 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 4) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hecard : (Set.range e).ncard = 4 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hKindexRaw :=
    hP4.index_of_fixingSubgroup_mul hecard
  rw [Nat.card_eq_fintype_card, hcard] at hKindexRaw
  norm_num at hKindexRaw
  have hKindex : K.index = 93024 := by
    change
      (fixingSubgroup P (Set.range e)).index = 93024
    omega
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 1395360 := by
    change (fixingSubgroup P s).index = 1395360
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 1395360 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hKindexCard := K.index_mul_card
  have hKcard : Nat.card K = 15 * h := by
    rw [hKindex, hPcard] at hKindexCard
    omega
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hglobal (Q : Sylow 5 P) :
      Nat.card Q = 5 :=
    sylow_five_card_eq_five
      P h hPcard hnotFive Q
  have hlocal (T : Sylow 5 K) :
      Nat.card T = 5 :=
    sylow_five_card_eq_five_of_card_eq_fifteen_mul
      K h hKcard hnotFive T
  have hequiv :
      Sylow 5 K ≃ SylowFixesEmbedding P 5 4 e := by
    change
      Sylow 5 K ≃
        {Q : Sylow 5 P //
          (Q : Subgroup P) ≤ K}
    exact sylowSubtypeEquiv K hglobal hlocal
  calc
    Nat.card (Sylow 5 K) =
        Nat.card (SylowFixesEmbedding P 5 4 e) :=
      Nat.card_congr hequiv
    _ = 3 * Nat.card (fixingSubgroup P s) :=
      card_sylowFixesEmbedding_eq_three_mul_stabilizer
        X P hcard h5 hnotAlt s hs e

theorem four_point_stabilizer_sylowFive_normalizer_card_eq_five
    (X : Type) [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X))
    (hcard : Fintype.card X = 19)
    (h5 : ∀ a b : Fin 5 → X, Function.Injective a →
      Function.Injective b →
      ∃ g : P, ∀ i, g • a i = b i)
    (hnotAlt : ¬alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (e : Fin 4 ↪ X)
    (T : Sylow 5
      (fixingSubgroup P (Set.range e))) :
    Nat.card
        (Subgroup.normalizer
          (T : Set (fixingSubgroup P (Set.range e)))) = 5 := by
  classical
  let H : Subgroup P := fixingSubgroup P s
  let h := Nat.card H
  let K : Subgroup P :=
    fixingSubgroup P (Set.range e)
  have hnotFive : ¬5 ∣ h :=
    five_not_dvd_five_point_stabilizer_of_not_alternating
      X P hcard h5 hnotAlt s hs
  have hh : 0 < h :=
    Nat.card_pos
  have hP5 : MulAction.IsMultiplyPretransitive P X 5 := by
    rw [MulAction.isMultiplyPretransitive_iff]
    intro a b
    obtain ⟨q, hq⟩ :=
      h5 a b a.injective b.injective
    refine ⟨q, ?_⟩
    ext i
    exact hq i
  have hP4 : MulAction.IsMultiplyPretransitive P X 4 := by
    letI : MulAction.IsMultiplyPretransitive P X 5 := hP5
    exact MulAction.isMultiplyPretransitive_of_le
      (G := P) (α := X) (m := 4) (n := 5)
        (by omega) (by
          rw [Nat.card_eq_fintype_card, hcard]
          omega)
  have hecard : (Set.range e).ncard = 4 := by
    rw [Set.ncard_range_of_injective e.injective,
      Nat.card_eq_fintype_card, Fintype.card_fin]
  have hKindexRaw :=
    hP4.index_of_fixingSubgroup_mul hecard
  rw [Nat.card_eq_fintype_card, hcard] at hKindexRaw
  norm_num at hKindexRaw
  have hKindex : K.index = 93024 := by
    change
      (fixingSubgroup P (Set.range e)).index = 93024
    omega
  have hHindexRaw :=
    hP5.index_of_fixingSubgroup_mul hs
  rw [Nat.card_eq_fintype_card, hcard] at hHindexRaw
  norm_num at hHindexRaw
  have hHindex : H.index = 1395360 := by
    change (fixingSubgroup P s).index = 1395360
    omega
  have hHindexCard := H.index_mul_card
  have hPcard : Nat.card P = 1395360 * h := by
    rw [hHindex] at hHindexCard
    exact hHindexCard.symm
  have hKindexCard := K.index_mul_card
  have hKcard : Nat.card K = 15 * h := by
    rw [hKindex, hPcard] at hKindexCard
    omega
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsylowCard :
      Nat.card (Sylow 5 K) = 3 * h := by
    change
      Nat.card
          (Sylow 5
            (fixingSubgroup P (Set.range e))) =
        3 * Nat.card (fixingSubgroup P s)
    exact four_point_stabilizer_sylowFive_card
      X P hcard h5 hnotAlt s hs e
  let N : Subgroup K :=
    Subgroup.normalizer (T : Set K)
  have hNindex : N.index = 3 * h := by
    change
      (Subgroup.normalizer (T : Set K)).index =
        3 * h
    rw [← T.card_eq_index_normalizer,
      hsylowCard]
  have hNindexCard := N.index_mul_card
  have hcancel :
      h * (3 * Nat.card N) = h * 15 := by
    rw [hNindex, hKcard] at hNindexCard
    nlinarith
  have hthree :
      3 * Nat.card N = 15 :=
    Nat.mul_left_cancel hh hcancel
  change Nat.card N = 5
  omega

private noncomputable def normalFiveComplement
    {K : Type} [Group K] [Fintype K]
    (T : Sylow 5 K)
    (hnormalizer :
      Subgroup.normalizer (T : Set K) ≤
        Subgroup.centralizer (T : Set K)) :
    Subgroup K :=
  (MonoidHom.transferSylow T hnormalizer).ker

private theorem normalFiveComplement_isComplement
    {K : Type} [Group K] [Fintype K]
    (T : Sylow 5 K)
    (hnormalizer :
      Subgroup.normalizer (T : Set K) ≤
        Subgroup.centralizer (T : Set K)) :
    IsComplement' (normalFiveComplement T hnormalizer) T := by
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact MonoidHom.ker_transferSylow_isComplement'
    T hnormalizer

theorem exists_normal_five_complement_of_normalizer_card_eq_five
    {K : Type} [Group K] [Fintype K]
    (T : Sylow 5 K)
    (hTcard : Nat.card T = 5)
    (hNormalizerCard :
      Nat.card
          (Subgroup.normalizer (T : Set K)) = 5) :
    ∃ Q : Subgroup K,
      Q.Normal ∧ IsComplement' Q T := by
  classical
  letI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hnormalizerEq :
      Subgroup.normalizer (T : Set K) =
        (T : Subgroup K) :=
    (Subgroup.eq_of_le_of_card_ge T.le_normalizer (by
      have hNormalizerCard' :
          Nat.card
              (Subgroup.normalizer
                ((T : Subgroup K) : Set K)) = 5 := by
        simpa only [T.coe_coe] using hNormalizerCard
      rw [hNormalizerCard', hTcard])).symm
  letI : IsCyclic T :=
    isCyclic_of_prime_card hTcard
  letI : IsMulCommutative T :=
    IsCyclic.isMulCommutative
  have hTcentralizer :
      (T : Subgroup K) ≤
        Subgroup.centralizer (T : Set K) := by
    intro a ha b hb
    exact congrArg Subtype.val
      (mul_comm'
        (⟨b, hb⟩ : T) (⟨a, ha⟩ : T))
  have hnormalizer :
      Subgroup.normalizer (T : Set K) ≤
        Subgroup.centralizer (T : Set K) := by
    rw [hnormalizerEq]
    exact hTcentralizer
  refine
    ⟨normalFiveComplement T hnormalizer, ?_, ?_⟩
  · dsimp only [normalFiveComplement]
    infer_instance
  · exact normalFiveComplement_isComplement
      T hnormalizer

end FiveTransitive.Degree19

end CFSG

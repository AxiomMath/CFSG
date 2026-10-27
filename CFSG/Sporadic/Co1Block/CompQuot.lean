module

public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupActions.PrimitiveCoprimeSimplicity

public section

namespace CFSG.Sporadic.Co1Block

open Subgroup

theorem le_of_isPerfect_of_isSolvable_quotient {G : Type*} [Group G] (N : Subgroup G)
    [N.Normal] [Group.IsSolvable (G ⧸ N)] (L : Subgroup G) [Group.IsPerfect L] : L ≤ N := by
  have hP : Group.IsPerfect (L.map (QuotientGroup.mk' N)) := Group.IsPerfect.map _
  have hbot : L.map (QuotientGroup.mk' N) = ⊥ := by
    by_contra h
    have : Nontrivial (L.map (QuotientGroup.mk' N)) := (Subgroup.nontrivial_iff_ne_bot _).2 h
    exact Group.IsPerfect.not_isSolvable (L.map (QuotientGroup.mk' N)) inferInstance
  rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot

theorem isSolvable_of_card_two_pow {G : Type*} [Group G] {m : ℕ} (h : Nat.card G = 2 ^ m) :
    Group.IsSolvable G := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Finite G := Nat.finite_of_card_ne_zero (by rw [h]; positivity)
  have := (IsPGroup.of_card h).isNilpotent
  infer_instance

theorem center_eq_bot_of_isSimpleGroup {G : Type*} [Group G] (hG : IsSimpleGroup G) (a b : G)
    (hab : a * b ≠ b * a) : center G = ⊥ := by
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (center G) with h | h
  · exact h
  · exact absurd ((mem_center_iff.1 (h ▸ mem_top b : b ∈ center G)) a) hab

theorem isSimpleGroup_closure_pair {n : ℕ} {x y : Equiv.Perm (Fin n)}
    [MulAction.IsPreprimitive (closure ({x, y} : Set (Equiv.Perm (Fin n)))) (Fin n)]
    (hn : 2 ≤ n) (hxy : (orderOf x).Coprime (orderOf y)) (ω : Fin n)
    (hst : (orderOf (x * y)).Coprime
      (Nat.card (MulAction.stabilizer (closure ({x, y} : Set (Equiv.Perm (Fin n)))) ω))) :
    IsSimpleGroup (closure ({x, y} : Set (Equiv.Perm (Fin n)))) := by
  set K := closure ({x, y} : Set (Equiv.Perm (Fin n)))
  have : FaithfulSMul K (Fin n) := ⟨fun h => Subtype.ext (Equiv.ext h)⟩
  have hx : x ∈ K := subset_closure (Set.mem_insert _ _)
  have hy : y ∈ K := subset_closure (Set.mem_insert_of_mem _ rfl)
  refine CFSG.GroupActions.isSimpleGroup_of_preprimitive_of_coprime_generator_orders
    (Ω := Fin n) (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn) ⟨x, hx⟩ ⟨y, hy⟩
    ?_ ω ?_ ?_
  · have h := closure_closure_coe_preimage (k := ({x, y} : Set (Equiv.Perm (Fin n))))
    convert h using 2
    ext ⟨g, hg⟩
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff, Set.mem_preimage, Subtype.ext_iff]
  · rwa [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
  · rwa [← Subgroup.orderOf_coe, Subgroup.coe_mul]

theorem card_quotient_center_of_isComponent {C P : Type*} [Group C] [Group P] [Finite C]
    (φ : C →* P) (D : Subgroup P) (hDR : D ≤ φ.range) (hN : φ.range ≤ normalizer (D : Set P))
    (hD : IsSimpleGroup D) (a b : D) (hab : a * b ≠ b * a) {k : ℕ}
    (hR : Nat.card φ.range = Nat.card D * 2 ^ k) {m : ℕ} (hK : Nat.card φ.ker = 2 ^ m)
    (B : Subgroup C) (hB : CFSG.IsComponent B) :
    Nat.card (B ⧸ center B) = Nat.card D := by
  classical
  obtain ⟨hq, hsn⟩ := hB
  set R := φ.range
  set ψ : C →* R := φ.rangeRestrict
  have hψ : Function.Surjective ψ := φ.rangeRestrict_surjective
  have : Finite R := Finite.of_surjective ψ hψ
  have : Finite D := Finite.of_injective (Subgroup.inclusion hDR) (Subgroup.inclusion_injective hDR)
  set D' : Subgroup R := D.subgroupOf R
  have : D'.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hDR).2 hN
  let eD : D' ≃* D := Subgroup.subgroupOfEquivOfLe hDR
  have hD' : IsSimpleGroup D' := @MulEquiv.isSimpleGroup D' _ D _ hD eD
  have hcardD' : Nat.card D' = Nat.card D := Nat.card_congr eD.toEquiv
  have hcardQ : Nat.card (R ⧸ D') = 2 ^ k := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup D'
    rw [hcardD', hR, mul_comm] at h1
    exact (Nat.eq_of_mul_eq_mul_right Nat.card_pos h1).symm
  have : Group.IsSolvable (R ⧸ D') := isSolvable_of_card_two_pow hcardQ
  have hBp : Group.IsPerfect B := hq.1
  have hBnt : Nontrivial B := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    have hs := hq.2.1
    exact not_subsingleton (B ⧸ center B) inferInstance
  set L : Subgroup R := B.map ψ
  have : Group.IsPerfect L := Group.IsPerfect.map ψ
  have hLD : L ≤ D' := le_of_isPerfect_of_isSolvable_quotient D' L
  have hLeq : L = D' := by
    rcases (hsn.map hψ).subgroupOf.eq_bot_or_top_of_isSimpleGroup hD' with h | h
    · exfalso
      have hLbot : L = ⊥ := by
        rw [Subgroup.subgroupOf_eq_bot] at h
        exact disjoint_self.1 (h.mono_right hLD)
      have hBK : B ≤ φ.ker := by
        rw [← MonoidHom.ker_rangeRestrict φ]
        exact (Subgroup.map_eq_bot_iff B).1 hLbot
      obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_two).1
        (hK ▸ Subgroup.card_dvd_of_le hBK)
      exact Group.IsPerfect.not_isSolvable B (isSolvable_of_card_two_pow hj)
    · exact le_antisymm hLD (Subgroup.subgroupOf_eq_top.1 h)
  set f : B →* R := ψ.comp B.subtype
  have hfr : f.range = D' := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
    exact hLeq
  have hZD' : center D' = ⊥ :=
    center_eq_bot_of_isSimpleGroup hD' (eD.symm a) (eD.symm b) fun h => hab (by
      have := congrArg eD h
      rwa [map_mul, map_mul, MulEquiv.apply_symm_apply, MulEquiv.apply_symm_apply] at this)
  have hker : f.ker = center B := by
    apply le_antisymm
    · rcases CFSG.LocalCores.quasisimple_normal_subgroups hq f.normal_ker with h | h
      · exfalso
        have hbot : f.range = ⊥ := by
          rw [MonoidHom.range_eq_bot_iff, ← MonoidHom.ker_eq_top_iff]
          exact h
        rw [hfr] at hbot
        have := hD'.toNontrivial
        exact (Subgroup.nontrivial_iff_ne_bot D').1 this hbot
      · exact h
    · intro z hz
      rw [MonoidHom.mem_ker]
      have hzD : f z ∈ D' := hfr ▸ ⟨z, rfl⟩
      have hc : (⟨f z, hzD⟩ : D') ∈ center D' := by
        rw [mem_center_iff]
        rintro ⟨y, hy⟩
        rw [← hfr] at hy
        obtain ⟨w, rfl⟩ := hy
        apply Subtype.ext
        show f w * f z = f z * f w
        rw [← map_mul, ← map_mul, (mem_center_iff.1 hz) w]
      rw [hZD', Subgroup.mem_bot] at hc
      exact congrArg Subtype.val hc
  rw [← hker, Nat.card_congr (QuotientGroup.quotientKerEquivRange f).toEquiv, hfr, hcardD']

@[expose] def centralizerConjEquiv {G : Type*} [Group G] (g x : G) :
    centralizer ({x} : Set G) ≃* centralizer ({g * x * g⁻¹} : Set G) where
  toFun c := ⟨g * c * g⁻¹, by
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 c.2
    calc g * c * g⁻¹ * (g * x * g⁻¹) = g * (c * x) * g⁻¹ := by group
      _ = g * (x * c) * g⁻¹ := by rw [h]
      _ = g * x * g⁻¹ * (g * c * g⁻¹) := by group⟩
  invFun c := ⟨g⁻¹ * c * g, by
    rw [mem_centralizer_singleton_iff]
    have h := mem_centralizer_singleton_iff.1 c.2
    calc g⁻¹ * c * g * x = g⁻¹ * (c * (g * x * g⁻¹)) * g := by group
      _ = g⁻¹ * ((g * x * g⁻¹) * c) * g := by rw [h]
      _ = x * (g⁻¹ * c * g) := by group⟩
  left_inv c := Subtype.ext (by simp only; group)
  right_inv c := Subtype.ext (by simp only; group)
  map_mul' a b := Subtype.ext (by simp only [Subgroup.coe_mul]; group)

theorem forall_card_quotient_center_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    {n : ℕ} (h : ∀ B : Subgroup H, CFSG.IsComponent B → Nat.card (B ⧸ center B) = n) :
    ∀ B : Subgroup K, CFSG.IsComponent B → Nat.card (B ⧸ center B) = n := by
  intro B hB
  rw [← h _ (CFSG.LocalCores.isComponent_map_mulEquiv e.symm hB)]
  let f : B ≃* B.map e.symm.toMonoidHom :=
    B.equivMapOfInjective e.symm.toMonoidHom e.symm.injective
  exact Nat.card_congr (QuotientGroup.congr _ _ f (Subgroup.map_center_eq f)).toEquiv

theorem forall_card_quotient_center_of_isConj {G : Type*} [Group G] {a t : G} (h : IsConj a t)
    {n : ℕ} (ha : ∀ B : Subgroup (centralizer ({a} : Set G)), CFSG.IsComponent B →
      Nat.card (B ⧸ center B) = n) :
    ∀ B : Subgroup (centralizer ({t} : Set G)), CFSG.IsComponent B →
      Nat.card (B ⧸ center B) = n := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  exact forall_card_quotient_center_of_mulEquiv (centralizerConjEquiv g a) ha

theorem centralizer_map_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    (Q : Subgroup H) :
    centralizer ((Q.map e.toMonoidHom : Subgroup K) : Set K) =
      (centralizer (Q : Set H)).map e.toMonoidHom := by
  ext k
  rw [Subgroup.mem_map_equiv, mem_centralizer_iff, mem_centralizer_iff]
  constructor
  · intro h q hq
    apply e.injective
    rw [map_mul, map_mul, MulEquiv.apply_symm_apply]
    exact h (e q) ⟨q, hq, rfl⟩
  · rintro h _ ⟨q, hq, rfl⟩
    have := congrArg e (h q hq)
    rwa [map_mul, map_mul, MulEquiv.apply_symm_apply] at this

theorem selfCentralizing_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K) {m : ℕ}
    (h : ∃ Q : Subgroup H, Q.Normal ∧ Nat.card Q = m ∧ centralizer (Q : Set H) ≤ Q ∧
      ∀ B : Subgroup H, ¬ CFSG.IsComponent B) :
    ∃ Q : Subgroup K, Q.Normal ∧ Nat.card Q = m ∧ centralizer (Q : Set K) ≤ Q ∧
      ∀ B : Subgroup K, ¬ CFSG.IsComponent B := by
  obtain ⟨Q, hn, hc, hcen, hB⟩ := h
  refine ⟨Q.map e.toMonoidHom, hn.map _ e.surjective,
    by rw [Subgroup.card_map_of_injective e.injective, hc], ?_, fun B hBc => ?_⟩
  · rw [centralizer_map_mulEquiv]
    exact Subgroup.map_mono hcen
  · exact hB _ (CFSG.LocalCores.isComponent_map_mulEquiv e.symm hBc)

theorem elemSelfCentralizing_of_mulEquiv {H K : Type*} [Group H] [Group K] (e : H ≃* K)
    {m : ℕ} (h : ∃ Q : Subgroup H, Q.Normal ∧ CFSG.IsElementaryAbelian 2 Q ∧ Nat.card Q = m ∧
      centralizer (Q : Set H) = Q ∧ ∀ B : Subgroup H, ¬ CFSG.IsComponent B) :
    ∃ Q : Subgroup K, Q.Normal ∧ CFSG.IsElementaryAbelian 2 Q ∧ Nat.card Q = m ∧
      centralizer (Q : Set K) = Q ∧ ∀ B : Subgroup K, ¬ CFSG.IsComponent B := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨Q, hn, he, hc, hcen, hB⟩ := h
  refine ⟨Q.map e.toMonoidHom, hn.map _ e.surjective, CFSG.IsElementaryAbelian.map _,
    by rw [Subgroup.card_map_of_injective e.injective, hc], ?_, fun B hBc => ?_⟩
  · rw [centralizer_map_mulEquiv, hcen]
  · exact hB _ (CFSG.LocalCores.isComponent_map_mulEquiv e.symm hBc)

theorem selfCentralizing_of_isConj {G : Type*} [Group G] {a t : G} (h : IsConj a t) {m : ℕ}
    (ha : ∃ Q : Subgroup (centralizer ({a} : Set G)), Q.Normal ∧ Nat.card Q = m ∧
      centralizer (Q : Set (centralizer ({a} : Set G))) ≤ Q ∧
      ∀ B : Subgroup (centralizer ({a} : Set G)), ¬ CFSG.IsComponent B) :
    ∃ Q : Subgroup (centralizer ({t} : Set G)), Q.Normal ∧ Nat.card Q = m ∧
      centralizer (Q : Set (centralizer ({t} : Set G))) ≤ Q ∧
      ∀ B : Subgroup (centralizer ({t} : Set G)), ¬ CFSG.IsComponent B := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  exact selfCentralizing_of_mulEquiv (centralizerConjEquiv g a) ha

theorem elemSelfCentralizing_of_isConj {G : Type*} [Group G] {a t : G} (h : IsConj a t)
    {m : ℕ} (ha : ∃ Q : Subgroup (centralizer ({a} : Set G)), Q.Normal ∧
      CFSG.IsElementaryAbelian 2 Q ∧ Nat.card Q = m ∧
      centralizer (Q : Set (centralizer ({a} : Set G))) = Q ∧
      ∀ B : Subgroup (centralizer ({a} : Set G)), ¬ CFSG.IsComponent B) :
    ∃ Q : Subgroup (centralizer ({t} : Set G)), Q.Normal ∧ CFSG.IsElementaryAbelian 2 Q ∧
      Nat.card Q = m ∧ centralizer (Q : Set (centralizer ({t} : Set G))) = Q ∧
      ∀ B : Subgroup (centralizer ({t} : Set G)), ¬ CFSG.IsComponent B := by
  obtain ⟨g, rfl⟩ := isConj_iff.1 h
  exact elemSelfCentralizing_of_mulEquiv (centralizerConjEquiv g a) ha

end CFSG.Sporadic.Co1Block

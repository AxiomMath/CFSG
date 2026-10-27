module

public import CFSG.Quasithin.SteinbergCBAlternatingAut

public section

namespace CFSG.Quasithin.SteinbergCB

open Equiv Equiv.Perm Subgroup CFSG.ComponentClassification.OuterAutomorphisms

theorem sq_eq_one_of_pow_four_alternating_five :
    ∀ g : alternatingGroup (Fin 5), g ^ 4 = 1 → g ^ 2 = 1 := by
  decide +kernel

theorem centralizer_involution_alternating_five :
    ∀ t : alternatingGroup (Fin 5), t ≠ 1 → t ^ 2 = 1 →
      ∃ α : Fin 5, (∀ β, (t : Perm (Fin 5)) β = β ↔ β = α) ∧
        ∀ g : alternatingGroup (Fin 5), g * t = t * g ↔
          g = 1 ∨ (g ^ 2 = 1 ∧ g ≠ 1 ∧ (g : Perm (Fin 5)) α = α) := by
  decide +kernel

theorem involution_iff_cycleType_alternating_five (g : alternatingGroup (Fin 5)) :
    (g ^ 2 = 1 ∧ g ≠ 1) ↔ (g : Perm (Fin 5)).cycleType = {2, 2} := by
  constructor
  · rintro ⟨h2, h1⟩
    have hord : orderOf (g : Perm (Fin 5)) = 2 := by
      rw [Subgroup.orderOf_coe]
      exact orderOf_eq_prime h2 h1
    obtain ⟨n, hn⟩ := cycleType_prime_order (hord ▸ Nat.prime_two)
    rw [hord] at hn
    have hsum := sum_cycleType (g : Perm (Fin 5))
    have hle : (g : Perm (Fin 5)).support.card ≤ 5 :=
      (Finset.card_le_univ _).trans (Fintype.card_fin 5).le
    have hsign := sign_of_cycleType (g : Perm (Fin 5))
    rw [mem_alternatingGroup.1 g.2, hn, Multiset.sum_replicate, Multiset.card_replicate,
      smul_eq_mul] at hsign
    rw [hn, Multiset.sum_replicate, smul_eq_mul] at hsum
    have hn1 : n ≤ 1 := by omega
    interval_cases n
    · exact absurd hsign (by decide)
    · rw [hn]
      rfl
  · intro h
    have hord : orderOf (g : Perm (Fin 5)) = 2 := by
      rw [← lcm_cycleType, h]
      rfl
    rw [Subgroup.orderOf_coe] at hord
    refine ⟨by rw [← hord]; exact pow_orderOf_eq_one g, fun h1 => ?_⟩
    rw [h1, orderOf_one] at hord
    exact absurd hord (by norm_num)

theorem nat_card_alternating_five : Nat.card (alternatingGroup (Fin 5)) = 60 := by
  rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_fin]
  rfl

theorem nat_card_sylow_two_alternating_five (P : Sylow 2 (alternatingGroup (Fin 5))) :
    Nat.card P = 4 := by
  rw [Sylow.card_eq_multiplicity, nat_card_alternating_five]
  have h60 : (60 : ℕ) = 2 ^ 2 * 15 := by norm_num
  rw [h60, Nat.factorization_mul_apply_of_coprime (by decide), Nat.factorization_pow,
    Finsupp.coe_smul, Pi.smul_apply, smul_eq_mul, Nat.prime_two.factorization_self,
    Nat.factorization_eq_zero_of_not_dvd (by decide)]
  norm_num

theorem sylow_eq_centralizer (P : Sylow 2 (alternatingGroup (Fin 5)))
    {t : alternatingGroup (Fin 5)} (htP : t ∈ P) (ht1 : t ≠ 1) :
    (P : Subgroup (alternatingGroup (Fin 5))) = centralizer {t} := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hcard := nat_card_sylow_two_alternating_five P
  have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := P)
    (by rw [hcard]; norm_num)
  have ht4 : t ^ 4 = 1 := by
    have h := pow_card_eq_one' (G := P) (x := ⟨t, htP⟩)
    rw [hcard] at h
    simpa using congrArg Subtype.val h
  obtain ⟨α, -, hC⟩ := centralizer_involution_alternating_five t ht1
    (sq_eq_one_of_pow_four_alternating_five t ht4)
  have hle : (P : Subgroup (alternatingGroup (Fin 5))) ≤ centralizer {t} := fun g hg => by
    rw [mem_centralizer_singleton_iff]
    exact congrArg Subtype.val (hcomm.is_comm.comm ⟨g, hg⟩ ⟨t, htP⟩)
  have hp : IsPGroup 2 (centralizer ({t} : Set (alternatingGroup (Fin 5)))) := by
    intro g
    refine ⟨1, Subtype.ext ?_⟩
    rcases (hC g).1 (mem_centralizer_singleton_iff.1 g.2) with h | ⟨h, -, -⟩
    · simp [h]
    · simpa using h
  exact (P.is_maximal' hp hle).symm

theorem sylow_two_alternating_five (P : Sylow 2 (alternatingGroup (Fin 5))) :
    ∃ α : Fin 5, (∀ β : Fin 5, (∀ p ∈ P, (p : Perm (Fin 5)) β = β) ↔ β = α) ∧
      ∀ g : alternatingGroup (Fin 5), g ∈ P ↔
        g = 1 ∨ (g ^ 2 = 1 ∧ g ≠ 1 ∧ (g : Perm (Fin 5)) α = α) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨⟨t, htP⟩, ht1⟩ : ∃ t : P, t ≠ 1 := by
    have : Nontrivial P := by
      rw [← Finite.one_lt_card_iff_nontrivial, nat_card_sylow_two_alternating_five]
      norm_num
    exact exists_ne 1
  have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
  have hPC := sylow_eq_centralizer P htP ht1'
  have ht4 : t ^ 4 = 1 := by
    have h := pow_card_eq_one' (G := P) (x := ⟨t, htP⟩)
    rw [nat_card_sylow_two_alternating_five] at h
    simpa using congrArg Subtype.val h
  obtain ⟨α, hα, hC⟩ := centralizer_involution_alternating_five t ht1'
    (sq_eq_one_of_pow_four_alternating_five t ht4)
  have hmem : ∀ g : alternatingGroup (Fin 5), g ∈ P ↔
      g = 1 ∨ (g ^ 2 = 1 ∧ g ≠ 1 ∧ (g : Perm (Fin 5)) α = α) := fun g => by
    change g ∈ (P : Subgroup (alternatingGroup (Fin 5))) ↔ _
    rw [hPC, mem_centralizer_singleton_iff]
    exact hC g
  refine ⟨α, fun β => ⟨fun h => (hα β).1 (h t htP), fun h p hp => ?_⟩, hmem⟩
  rcases (hmem p).1 hp with h1 | ⟨-, -, h2⟩
  · rw [h1, h]
    rfl
  · rw [h]
    exact h2


theorem nonempty_stabilizer_alternatingGroup_mulEquiv {X : Type*} [Fintype X] [DecidableEq X]
    (a : X) : Nonempty (MulAction.stabilizer (alternatingGroup X) a ≃*
      alternatingGroup {x : X // x ≠ a}) := by
  let φ : alternatingGroup {x : X // x ≠ a} →* MulAction.stabilizer (alternatingGroup X) a :=
    { toFun := fun σ => ⟨⟨ofSubtype (σ : Perm {x : X // x ≠ a}), by
          rw [mem_alternatingGroup, sign_ofSubtype]
          exact σ.2⟩, by
          rw [MulAction.mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def]
          exact ofSubtype_apply_of_not_mem _ (not_not.2 rfl)⟩
      map_one' := by
        ext x
        simp
      map_mul' := fun σ τ => by
        ext x
        simp }
  have hφ : ∀ σ, (((φ σ : MulAction.stabilizer (alternatingGroup X) a) : alternatingGroup X) :
      Perm X) = ofSubtype (σ : Perm {x : X // x ≠ a}) := fun _ => rfl
  have hinj : Function.Injective φ := fun σ τ h => by
    have := congrArg (fun g : MulAction.stabilizer (alternatingGroup X) a =>
      ((g : alternatingGroup X) : Perm X)) h
    simp only [hφ] at this
    exact Subtype.ext (ofSubtype_injective this)
  have hsurj : Function.Surjective φ := by
    rintro ⟨⟨g, hg⟩, hga⟩
    have hga' : g a = a := hga
    have h₁ : ∀ x, (g x ≠ a ↔ x ≠ a) := fun x => by
      constructor
      · intro h hx
        exact h (hx ▸ hga')
      · intro h hx
        exact h (g.injective (hx.trans hga'.symm))
    have h₂ : ∀ x, g x ≠ x → x ≠ a := fun x hx hxa => hx (hxa ▸ hga')
    refine ⟨⟨g.subtypePerm h₁, ?_⟩, ?_⟩
    · rw [mem_alternatingGroup, sign_subtypePerm _ _ h₂]
      exact hg
    · apply Subtype.ext
      apply Subtype.ext
      rw [hφ]
      exact ofSubtype_subtypePerm h₁ h₂
  exact ⟨(MulEquiv.ofBijective φ ⟨hinj, hsurj⟩).symm⟩

theorem alternating_five_unique_Sylow_two_containment_and_solvable_normalizer :
    Nat.card (alternatingGroup (Fin 5)) = 60 ∧
    (∀ P : Sylow 2 (alternatingGroup (Fin 5)), CFSG.IsElementaryAbelian 2 P ∧ Nat.card P = 4 ∧
      ∃ α : Fin 5, (∀ β : Fin 5, (∀ p ∈ P, (p : Perm (Fin 5)) β = β) ↔ β = α) ∧
        (∀ g : alternatingGroup (Fin 5), g ∈ P ↔
          g = 1 ∨ ((g : Perm (Fin 5)).cycleType = {2, 2} ∧ (g : Perm (Fin 5)) α = α)) ∧
        normalizer ((P : Subgroup (alternatingGroup (Fin 5))) : Set (alternatingGroup (Fin 5))) =
          MulAction.stabilizer (alternatingGroup (Fin 5)) α ∧
        Nonempty (MulAction.stabilizer (alternatingGroup (Fin 5)) α ≃*
          alternatingGroup {β : Fin 5 // β ≠ α}) ∧
        Group.IsSolvable (MulAction.stabilizer (alternatingGroup (Fin 5)) α) ∧
        Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) α) = 12) ∧
    (∀ H : Subgroup (alternatingGroup (Fin 5)), IsPGroup 2 H → H ≠ ⊥ →
      ∃! P : Sylow 2 (alternatingGroup (Fin 5)), H ≤ P) ∧
    (∀ P Q : Sylow 2 (alternatingGroup (Fin 5)), P ≠ Q →
      (P : Subgroup (alternatingGroup (Fin 5))) ⊓ Q = ⊥) ∧
    5 ∣ Nat.card (alternatingGroup (Fin 5)) ∧
    Group.IsSolvable (Outer (alternatingGroup (Fin 5))) ∧
    Nat.card (Outer (alternatingGroup (Fin 5))) ∣ 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have huniq : ∀ (P Q : Sylow 2 (alternatingGroup (Fin 5))) (t : alternatingGroup (Fin 5)),
      t ∈ P → t ∈ Q → t ≠ 1 → P = Q := fun P Q t htP htQ ht1 =>
    Sylow.ext ((sylow_eq_centralizer P htP ht1).trans (sylow_eq_centralizer Q htQ ht1).symm)
  refine ⟨nat_card_alternating_five, fun P => ?_, fun H hH hH1 => ?_, fun P Q hPQ => ?_,
    by rw [nat_card_alternating_five]; norm_num, isSolvable_outer_alternatingGroup (Or.inl rfl)⟩
  · have hcard := nat_card_sylow_two_alternating_five P
    obtain ⟨α, hfix, hmem⟩ := sylow_two_alternating_five P
    have hcomm := IsPGroup.isMulCommutative_of_card_eq_prime_sq (p := 2) (G := P)
      (by rw [hcard]; norm_num)
    have hsq : ∀ g : P, g ^ 2 = 1 := fun g => by
      rcases (hmem g).1 g.2 with h | ⟨h, -, -⟩
      · exact Subtype.ext (by simp [h])
      · exact Subtype.ext (by simpa using h)
    have helem : CFSG.IsElementaryAbelian 2 P :=
      { toIsMulCommutative := hcomm
        exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one hsq }
    have hconj : ∀ (g h : alternatingGroup (Fin 5)), (g : Perm (Fin 5)) α = α →
        h ∈ P → g * h * g⁻¹ ∈ P := by
      intro g h hg hh
      rcases (hmem h).1 hh with rfl | ⟨h2, h1, hα⟩
      · rw [mul_one, mul_inv_cancel]
        exact one_mem _
      · refine (hmem _).2 (Or.inr ⟨?_, ?_, ?_⟩)
        · rw [show (g * h * g⁻¹) ^ 2 = g * h ^ 2 * g⁻¹ by rw [pow_two, pow_two]; group, h2,
            mul_one, mul_inv_cancel]
        · intro h'
          apply h1
          have : h = g⁻¹ * (g * h * g⁻¹) * g := by group
          rw [this, h', mul_one, inv_mul_cancel]
        · have hgi : (g⁻¹ : alternatingGroup (Fin 5)) • α = α := by
            rw [inv_smul_eq_iff]
            exact hg.symm
          change ((g : Perm (Fin 5)) * h * (g : Perm (Fin 5))⁻¹) α = α
          have hgi' : (g : Perm (Fin 5))⁻¹ α = α := hgi
          rw [Perm.mul_apply, Perm.mul_apply, hgi', hα, hg]
    have hN : normalizer ((P : Subgroup (alternatingGroup (Fin 5))) :
        Set (alternatingGroup (Fin 5))) = MulAction.stabilizer (alternatingGroup (Fin 5)) α := by
      ext g
      rw [mem_normalizer_iff, MulAction.mem_stabilizer_iff, Subgroup.smul_def, Perm.smul_def]
      constructor
      · intro hg
        refine (hfix _).1 fun p hp => ?_
        have hp' : g⁻¹ * p * g ∈ P := by
          have := (hg (g⁻¹ * p * g)).2 (by rw [show g * (g⁻¹ * p * g) * g⁻¹ = p by group]; exact hp)
          exact this
        have h1 := (hfix α).2 rfl _ hp'
        change ((g : Perm (Fin 5))⁻¹ * p * g) α = α at h1
        rw [Perm.mul_apply, Perm.mul_apply, Perm.inv_eq_iff_eq] at h1
        exact h1
      · intro hg h
        refine ⟨hconj g h hg, fun hh => ?_⟩
        have hgi : (g⁻¹ : alternatingGroup (Fin 5)) • α = α := by
          rw [inv_smul_eq_iff, Subgroup.smul_def, Perm.smul_def]
          exact hg.symm
        have := hconj g⁻¹ _ hgi hh
        rwa [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at this
    obtain ⟨e⟩ := nonempty_stabilizer_alternatingGroup_mulEquiv α
    have hcard12 : Nat.card (MulAction.stabilizer (alternatingGroup (Fin 5)) α) = 12 := by
      rw [Nat.card_congr e.toEquiv]
      have : Nontrivial {β : Fin 5 // β ≠ α} := by
        rw [← Fintype.one_lt_card_iff_nontrivial, Fintype.card_subtype_compl,
          Fintype.card_fin, Fintype.card_subtype_eq]
        norm_num
      rw [nat_card_alternatingGroup, Nat.card_eq_fintype_card, Fintype.card_subtype_compl,
        Fintype.card_fin, Fintype.card_subtype_eq]
      rfl
    have hsolv : Group.IsSolvable (normalizer ((P : Subgroup (alternatingGroup (Fin 5))) :
        Set (alternatingGroup (Fin 5)))) := by
      set N := normalizer ((P : Subgroup (alternatingGroup (Fin 5))) :
        Set (alternatingGroup (Fin 5))) with hNdef
      set K := (P : Subgroup (alternatingGroup (Fin 5))).subgroupOf N with hK
      have hKn : K.Normal := Subgroup.normal_in_normalizer
      have hKcard : Nat.card K = 4 :=
        (Nat.card_congr (subgroupOfEquivOfLe
          (le_normalizer (H := (P : Subgroup (alternatingGroup (Fin 5)))))).toEquiv).trans hcard
      have hNcard : Nat.card N = 12 := by rw [hN, hcard12]
      have hQcard : Nat.card (N ⧸ K) = 3 := by
        have h := Subgroup.card_eq_card_quotient_mul_card_subgroup K
        rw [hNcard, hKcard] at h
        omega
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      have hQcyc := isCyclic_of_prime_card hQcard
      have hKsolv : Group.IsSolvable K := Group.isSolvable_of_comm fun a b => Subtype.ext
        (Subtype.ext (by
          have := hcomm.is_comm.comm ⟨((a : N) : alternatingGroup (Fin 5)), a.2⟩
            ⟨((b : N) : alternatingGroup (Fin 5)), b.2⟩
          have h' := congrArg (fun x : P => (x : alternatingGroup (Fin 5))) this
          simpa using h'))
      have hQsolv : Group.IsSolvable (N ⧸ K) := Group.isSolvable_of_comm fun a b =>
        (IsCyclic.isMulCommutative (α := N ⧸ K)).is_comm.comm a b
      exact Group.isSolvable_of_ker_le_range K.subtype (QuotientGroup.mk' K)
        (by rw [QuotientGroup.ker_mk', Subgroup.range_subtype])
    refine ⟨helem, hcard, α, hfix, fun g => ?_, hN, ⟨e⟩, hN ▸ hsolv, hcard12⟩
    rw [hmem g]
    constructor
    · rintro (h | ⟨h2, h1, hα⟩)
      · exact Or.inl h
      · exact Or.inr ⟨(involution_iff_cycleType_alternating_five g).1 ⟨h2, h1⟩, hα⟩
    · rintro (h | ⟨hct, hα⟩)
      · exact Or.inl h
      · obtain ⟨h2, h1⟩ := (involution_iff_cycleType_alternating_five g).2 hct
        exact Or.inr ⟨h2, h1, hα⟩
  ·
    obtain ⟨P, hP⟩ := hH.exists_le_sylow
    obtain ⟨⟨t, htH⟩, ht1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).1 hH1
    have ht1' : t ≠ 1 := fun h => ht1 (Subtype.ext h)
    exact ⟨P, hP, fun Q hQ => huniq Q P t (hQ htH) (hP htH) ht1'⟩
  ·
    rw [eq_bot_iff]
    intro t ht
    by_contra ht1
    exact hPQ (huniq P Q t ht.1 ht.2 ((Subgroup.mem_bot).not.1 ht1))

end CFSG.Quasithin.SteinbergCB

module

public import CFSG.GroupTheory.HyperplaneGeneration
public import CFSG.Quasithin.Background.A1bKrullSchmidt

public section

namespace CFSG.Quasithin

open CFSG CFSG.SolvableHall
open scoped IsMulCommutative

namespace A1b

theorem exists_cyclic_quotient_acting_trivially_of_irreducible
    {A H : Type*} [CommGroup A] [Finite A] [CommGroup H] [Finite H] [Nontrivial H]
    [MulDistribMulAction A H]
    (hirr : ∀ U : Subgroup H, (∀ a : A, ∀ x ∈ U, a • x ∈ U) → U = ⊥ ∨ U = ⊤) :
    ∃ B : Subgroup A, IsCyclic (A ⧸ B) ∧ ∀ b ∈ B, ∀ x : H, b • x = x := by
  classical
  let φ : A →* AddMonoid.End (Additive H) :=
    { toFun := fun a => MonoidHom.toAdditive (MulDistribMulAction.toMonoidHom H a)
      map_one' := by
        ext x
        change Additive.ofMul ((1 : A) • Additive.toMul x) = x
        rw [one_smul, ofMul_toMul]
      map_mul' := fun a b => by
        ext x
        change Additive.ofMul ((a * b) • Additive.toMul x) =
          Additive.ofMul (a • Additive.toMul (Additive.ofMul (b • Additive.toMul x)))
        rw [toMul_ofMul, mul_smul] }
  have hφ : ∀ (a : A) (x : H), φ a (Additive.ofMul x) = Additive.ofMul (a • x) :=
    fun _ _ => rfl
  set S : Set (AddMonoid.End (Additive H)) := Set.range φ with hS
  have hcomm : ∀ x ∈ S, ∀ y ∈ S, x * y = y * x := by
    rintro _ ⟨a, rfl⟩ _ ⟨b, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm]
  set R : Subring (AddMonoid.End (Additive H)) := Subring.centralizer (Set.centralizer S) with hR
  have hRcomm : ∀ x ∈ R, ∀ y ∈ R, x * y = y * x :=
    Set.centralizer_centralizer_comm_of_comm (fun x hx y hy _ => hcomm x hx y hy)
  have hSR : ∀ a : A, φ a ∈ R := fun a => Set.subset_centralizer_centralizer ⟨a, rfl⟩
  have hSc : ∀ a : A, φ a ∈ Set.centralizer S := fun a y hy => (hcomm _ hy _ ⟨a, rfl⟩)
  have : IsMulCommutative R := ⟨⟨fun x y => Subtype.ext (hRcomm _ x.2 _ y.2)⟩⟩
  have hinj : ∀ r ∈ R, r ≠ 0 → ∀ x : Additive H, r x = 0 → x = 0 := by
    intro r hr hr0
    let U : Subgroup H := AddSubgroup.toSubgroup' (AddMonoidHom.ker r)
    have hU : ∀ x : H, x ∈ U ↔ r (Additive.ofMul x) = 0 := fun x => Iff.rfl
    have hinv : ∀ a : A, ∀ x ∈ U, a • x ∈ U := by
      intro a x hx
      rw [hU] at hx ⊢
      rw [← hφ]
      have h := congrArg (fun f : AddMonoid.End (Additive H) => f (Additive.ofMul x))
        (hr (φ a) (hSc a))
      change φ a (r (Additive.ofMul x)) = r (φ a (Additive.ofMul x)) at h
      rw [← h, hx, map_zero]
    rcases hirr U hinv with h | h
    · intro x hx
      have hx' : Additive.toMul x ∈ U := by rw [hU, ofMul_toMul]; exact hx
      rw [h, Subgroup.mem_bot] at hx'
      rw [← ofMul_toMul x, hx', ofMul_one]
    · exfalso
      apply hr0
      ext x
      have hx' : Additive.toMul x ∈ U := by rw [h]; exact Subgroup.mem_top _
      rw [hU, ofMul_toMul] at hx'
      exact hx'
  have hnzd : NoZeroDivisors R := by
    refine ⟨fun {x y} hxy => ?_⟩
    by_contra hne'
    have hne := not_or.mp hne'
    have hx : (x : AddMonoid.End (Additive H)) ≠ 0 := fun h => hne.1 (Subtype.ext h)
    apply hne.2
    apply Subtype.ext
    ext v
    have h := congrArg (fun z : R => (z : AddMonoid.End (Additive H)) v) hxy
    change (x : AddMonoid.End (Additive H)) ((y : AddMonoid.End (Additive H)) v) = 0 at h
    exact hinj x x.2 hx _ h
  have hnt : Nontrivial R := by
    refine ⟨⟨0, 1, fun h => ?_⟩⟩
    obtain ⟨v, hv⟩ := exists_ne (1 : H)
    have h' := congrArg (fun z : R => (z : AddMonoid.End (Additive H)) (Additive.ofMul v)) h
    change (0 : Additive H) = Additive.ofMul v at h'
    exact hv (Additive.ofMul.injective h'.symm)
  have : IsDomain R := NoZeroDivisors.to_isDomain R
  let ψ : A →* R :=
    { toFun := fun a => ⟨φ a, hSR a⟩
      map_one' := Subtype.ext (map_one φ)
      map_mul' := fun a b => Subtype.ext (map_mul φ a b) }
  let ψu : A →* Rˣ := MonoidHom.toHomUnits ψ
  have hinjκ : Function.Injective ((Units.coeHom R).comp (QuotientGroup.kerLift ψu)) := by
    intro x y hxy
    exact QuotientGroup.kerLift_injective ψu (Units.val_injective hxy)
  have hcyc : IsCyclic (A ⧸ ψu.ker) :=
    isCyclic_of_injective_ringHom (R := R) (G := A ⧸ ψu.ker)
      ((Units.coeHom R).comp (QuotientGroup.kerLift ψu)) hinjκ
  have hker : ∀ a ∈ ψu.ker, ∀ x : H, a • x = x := by
    intro a ha x
    have h := congrArg (fun z : Rˣ => ((z : R) : AddMonoid.End (Additive H)) (Additive.ofMul x))
      (MonoidHom.mem_ker.mp ha)
    change Additive.ofMul (a • x) = Additive.ofMul x at h
    exact Additive.ofMul.injective h
  exact ⟨ψu.ker, hcyc, hker⟩

section Generation

universe u w

variable {r : ℕ} [Fact r.Prime] {A : Type w} [CommGroup A] [Finite A]

theorem coprime_card_subgroup_of_isPGroup (hA : IsPGroup r A) (B : Subgroup A) {n : ℕ}
    (hn : ¬ r ∣ n) : Nat.Coprime (Nat.card B) n := by
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp (hA.to_subgroup B)
  rw [hk]
  exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Fact.out).mpr hn)

omit [Fact r.Prime] [Finite A] in
theorem le_cyclic_join_of_invariant {H : Type u} [Group H] [MulDistribMulAction A H]
    (U : Subgroup H) [CFSG.IsInvariant A H U]
    (hU : ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B U = ⊤) :
    U ≤ ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B H := by
  intro u hu
  have h1 : (⟨u, hu⟩ : U) ∈ ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B U :=
    hU ▸ Subgroup.mem_top _
  have h2 := Subgroup.mem_map_of_mem U.subtype h1
  simp only [Subgroup.map_iSup] at h2
  have hle : (⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)),
      (fixedPointSubgroup B U).map U.subtype) ≤
      ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B H := by
    refine iSup_mono fun B => iSup_mono fun _ => ?_
    rintro _ ⟨y, hy, rfl⟩
    intro b
    exact congrArg Subtype.val (hy b)
  exact hle h2

theorem cyclic_join_eq_top_of_normal (hA : IsPGroup r A) {H : Type u} [Group H] [Finite H]
    [MulDistribMulAction A H] (hr : ¬ r ∣ Nat.card H) (U : Subgroup H) [U.Normal]
    [hUinv : CFSG.IsInvariant A H U] (hUsolv : Group.IsSolvable U)
    (hU : ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B U = ⊤)
    (hQ : letI : MulDistribMulAction A (H ⧸ U) :=
        quotientMulDistribMulAction (A := A) (G := H) U hUinv
      ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B (H ⧸ U) = ⊤) :
    ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B H = ⊤ := by
  classical
  set X := ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B H with hX
  have hUp : ¬ r ∣ Nat.card U := fun h => hr (h.trans (Subgroup.card_subgroup_dvd_card U))
  have hUX : U ≤ X := le_cyclic_join_of_invariant U hU
  let : MulDistribMulAction A (H ⧸ U) := quotientMulDistribMulAction (A := A) (G := H) U hUinv
  let : MulAction.QuotientAction A U := quotientAction_of_isInvariant (A := A) U hUinv
  have himage : ∀ B : Subgroup A,
      fixedPointSubgroup B (H ⧸ U) ≤ (fixedPointSubgroup B H).map (QuotientGroup.mk' U) := by
    intro B x hx
    obtain ⟨h, rfl⟩ := QuotientGroup.mk_surjective x
    have hBinv : CFSG.IsInvariant B H U :=
      ⟨fun b g => hUinv.invariant (b : A) g⟩
    have hg : ∀ b : B, h⁻¹ * (b • h) ∈ U := by
      intro b
      have hb := hx b
      change (b : A) • (h : H ⧸ U) = (h : H ⧸ U) at hb
      rw [MulAction.Quotient.smul_coe] at hb
      exact QuotientGroup.eq.mp hb.symm
    obtain ⟨c, hc, hcg⟩ := exists_fixed_of_coset_fixed U hBinv hUsolv
      (coprime_card_subgroup_of_isPGroup hA B hUp) h hg
    exact ⟨c, hc, (QuotientGroup.eq.mpr hcg)⟩
  have hXmap : X.map (QuotientGroup.mk' U) = ⊤ := by
    rw [eq_top_iff, ← hQ, hX]
    simp only [Subgroup.map_iSup]
    exact iSup_mono fun B => iSup_mono fun _ => himage B
  rw [eq_top_iff]
  intro h _
  have hmem : (h : H ⧸ U) ∈ X.map (QuotientGroup.mk' U) := hXmap ▸ Subgroup.mem_top _
  obtain ⟨x, hx, hxh⟩ := hmem
  have hxu : x⁻¹ * h ∈ U := QuotientGroup.eq.mp hxh
  have : h = x * (x⁻¹ * h) := by group
  rw [this]
  exact X.mul_mem hx (hUX hxu)

theorem abelian_cyclic_generation (hA : IsPGroup r A) {H : Type u} [CommGroup H] [Finite H]
    [MulDistribMulAction A H] (hr : ¬ r ∣ Nat.card H) :
    ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B H = ⊤ := by
  classical
  suffices key : ∀ n : ℕ, ∀ (H : Type u) [CommGroup H] [Finite H] [MulDistribMulAction A H],
      Nat.card H = n → ¬ r ∣ Nat.card H →
      ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B H = ⊤ from key _ H rfl hr
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ _ hn hr
  by_cases hU : ∃ U : Subgroup H, U ≠ ⊥ ∧ U ≠ ⊤ ∧ ∀ a : A, ∀ x ∈ U, a • x ∈ U
  · obtain ⟨U, hU1, hUtop, hUinv⟩ := hU
    have : CFSG.IsInvariant A H U := isInvariant_of_forall_smul_mem hUinv
    have hUlt : Nat.card U < n := by
      rw [← hn, ← Subgroup.card_top (G := H)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hUtop)
    have hUp : ¬ r ∣ Nat.card U := fun h => hr (h.trans (Subgroup.card_subgroup_dvd_card U))
    let : MulDistribMulAction A (H ⧸ U) := quotientMulDistribMulAction (A := A) (G := H) U this
    have hQlt : Nat.card (H ⧸ U) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup U]
      have h1 : 1 < Nat.card U := by
        rw [Finite.one_lt_card_iff_nontrivial]
        exact (Subgroup.nontrivial_iff_ne_bot U).mpr hU1
      have h0 : 0 < Nat.card (H ⧸ U) := Nat.card_pos
      nlinarith
    have hQp : ¬ r ∣ Nat.card (H ⧸ U) := fun h => hr (h.trans (Subgroup.card_quotient_dvd_card U))
    exact cyclic_join_eq_top_of_normal hA hr U inferInstance (ih _ hUlt U rfl hUp)
      (ih _ hQlt (H ⧸ U) rfl hQp)
  · have hirr : ∀ U : Subgroup H, (∀ a : A, ∀ x ∈ U, a • x ∈ U) → U = ⊥ ∨ U = ⊤ := by
      intro U hUinv
      by_contra hne
      exact hU ⟨U, fun h => hne (Or.inl h), fun h => hne (Or.inr h), hUinv⟩
    rcases subsingleton_or_nontrivial H with hsub | hnt
    · exact Subsingleton.elim _ _
    · obtain ⟨B, hB, hBfix⟩ := exists_cyclic_quotient_acting_trivially_of_irreducible (A := A) hirr
      rw [eq_top_iff]
      refine le_trans ?_ (le_iSup₂ (f := fun (B : Subgroup A) (_ : IsCyclic (A ⧸ B)) =>
        fixedPointSubgroup B H) B hB)
      intro x _ b
      exact hBfix b b.2 x

theorem solvable_cyclic_generation (hA : IsPGroup r A) {H : Type u} [Group H] [Finite H]
    [MulDistribMulAction A H] (hH : Group.IsSolvable H) (hr : ¬ r ∣ Nat.card H) :
    ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B H = ⊤ := by
  classical
  suffices key : ∀ n : ℕ, ∀ (H : Type u) [Group H] [Finite H] [MulDistribMulAction A H],
      Nat.card H = n → Group.IsSolvable H → ¬ r ∣ Nat.card H →
      ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B H = ⊤ from
    key _ H rfl hH hr
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro H _ _ _ hn hH hr
  by_cases hab : commutator H = ⊥
  · let : CommGroup H :=
      { (inferInstance : Group H) with
        mul_comm := fun x y => by
          rw [commutator_def] at hab
          have h := (Subgroup.commutator_eq_bot_iff_le_centralizer).mp hab (Subgroup.mem_top x)
          exact (Subgroup.mem_centralizer_iff.mp h y (Subgroup.mem_top y)).symm }
    exact abelian_cyclic_generation hA hr
  · rcases subsingleton_or_nontrivial H with hsub | hnt
    · exact Subsingleton.elim _ _
    set U := commutator H with hUdef
    have hUtop : U ≠ ⊤ := (Group.IsSolvable.commutator_lt_top_of_nontrivial H).ne
    have hUinv : ∀ a : A, ∀ x ∈ U, a • x ∈ U := by
      intro a x hx
      have hmem : a • x ∈ U.map (MulDistribMulAction.toMonoidHom H a) :=
        Subgroup.mem_map_of_mem _ hx
      rw [hUdef, commutator_def, Subgroup.map_commutator] at hmem
      rw [hUdef, commutator_def]
      exact Subgroup.commutator_mono le_top le_top hmem
    have : CFSG.IsInvariant A H U := isInvariant_of_forall_smul_mem hUinv
    have hUlt : Nat.card U < n := by
      rw [← hn, ← Subgroup.card_top (G := H)]
      exact Subgroup.card_lt_of_lt (lt_top_iff_ne_top.mpr hUtop)
    have hUp : ¬ r ∣ Nat.card U := fun h => hr (h.trans (Subgroup.card_subgroup_dvd_card U))
    let : MulDistribMulAction A (H ⧸ U) := quotientMulDistribMulAction (A := A) (G := H) U this
    have hQlt : Nat.card (H ⧸ U) < n := by
      rw [← hn, Subgroup.card_eq_card_quotient_mul_card_subgroup U]
      have h1 : 1 < Nat.card U := by
        rw [Finite.one_lt_card_iff_nontrivial]
        exact (Subgroup.nontrivial_iff_ne_bot U).mpr hab
      have h0 : 0 < Nat.card (H ⧸ U) := Nat.card_pos
      nlinarith
    have hQp : ¬ r ∣ Nat.card (H ⧸ U) := fun h => hr (h.trans (Subgroup.card_quotient_dvd_card U))
    have hUsolv : Group.IsSolvable U := inferInstance
    exact cyclic_join_eq_top_of_normal hA hr U hUsolv (ih _ hUlt U rfl hUsolv hUp)
      (ih _ hQlt (H ⧸ U) rfl inferInstance hQp)

omit [Finite A] in
theorem exists_invariant_sylow_of_isPGroup (hA : IsPGroup r A) {H : Type*} [Group H] [Finite H]
    [MulDistribMulAction A H] (hr : ¬ r ∣ Nat.card H) (q : ℕ) [Fact q.Prime] :
    ∃ Q : Sylow q H, ∀ a : A, ∀ x ∈ (Q : Subgroup H), a • x ∈ (Q : Subgroup H) := by
  classical
  have hcard : ¬ r ∣ Nat.card (Sylow q H) := by
    obtain ⟨P⟩ := (inferInstance : Nonempty (Sylow q H))
    intro h
    exact hr (h.trans ((Sylow.card_dvd_index P).trans (Subgroup.index_dvd_card _)))
  obtain ⟨Q, hQ⟩ := hA.nonempty_fixed_point_of_prime_not_dvd_card (Sylow q H) hcard
  refine ⟨Q, fun a x hx => ?_⟩
  have hmem : a • x ∈ ((a • Q : Sylow q H) : Subgroup H) := by
    rw [Sylow.pointwise_smul_def, Subgroup.pointwise_smul_def]
    exact ⟨x, hx, rfl⟩
  rwa [hQ a] at hmem

theorem cyclic_generation (hA : IsPGroup r A) {H : Type u} [Group H] [Finite H]
    [MulDistribMulAction A H] (hr : ¬ r ∣ Nat.card H) :
    ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B H = ⊤ := by
  classical
  set X := ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B)), fixedPointSubgroup B H with hX
  have hsyl : ∀ (q : ℕ) [Fact q.Prime], ∃ Q : Sylow q H, (Q : Subgroup H) ≤ X := by
    intro q _
    obtain ⟨Q, hQ⟩ := exists_invariant_sylow_of_isPGroup hA hr q
    have : CFSG.IsInvariant A H Q := isInvariant_of_forall_smul_mem hQ
    have hQp : ¬ r ∣ Nat.card (Q : Subgroup H) :=
      fun h => hr (h.trans (Subgroup.card_subgroup_dvd_card _))
    have : Group.IsNilpotent (Q : Subgroup H) := Q.isPGroup'.isNilpotent
    exact ⟨Q, le_cyclic_join_of_invariant (A := A) (Q : Subgroup H)
      (solvable_cyclic_generation hA inferInstance hQp)⟩
  have hdvd : Nat.card H ∣ Nat.card X := by
    apply (Nat.factorization_le_iff_dvd Nat.card_pos.ne' Nat.card_pos.ne').mp
    intro q
    by_cases hq : q.Prime
    · have : Fact q.Prime := ⟨hq⟩
      obtain ⟨Q, hQX⟩ := hsyl q
      have h2 : Nat.card (Q : Subgroup H) ∣ Nat.card X := Subgroup.card_dvd_of_le hQX
      rw [Sylow.card_eq_multiplicity Q] at h2
      exact (hq.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp h2
    · simp [Nat.factorization_eq_zero_of_not_prime _ hq]
  exact (Subgroup.card_eq_iff_eq_top X).mp
    (Nat.dvd_antisymm (Subgroup.card_subgroup_dvd_card X) hdvd)

end Generation

section Norm

variable {A : Type*} [CommGroup A] {G : Type*} [CommGroup G] [MulDistribMulAction A G]

@[expose] noncomputable def subgroupNorm (B : Subgroup A) [Fintype B] : G →* G where
  toFun g := ∏ b : B, (b : A) • g
  map_one' := by simp
  map_mul' g h := by simp [Finset.prod_mul_distrib]

theorem subgroupNorm_apply (B : Subgroup A) [Fintype B] (g : G) :
    subgroupNorm B g = ∏ b : B, (b : A) • g := rfl

theorem smul_subgroupNorm (B : Subgroup A) [Fintype B] (a : A) (g : G) :
    a • subgroupNorm B g = subgroupNorm B (a • g) := by
  rw [subgroupNorm_apply, subgroupNorm_apply]
  have := map_prod (MulDistribMulAction.toMonoidHom G a) (fun b : B => (b : A) • g) Finset.univ
  rw [MulDistribMulAction.toMonoidHom_apply] at this
  rw [this]
  refine Finset.prod_congr rfl fun b _ => ?_
  rw [MulDistribMulAction.toMonoidHom_apply, ← mul_smul, ← mul_smul, mul_comm]

theorem smul_subgroupNorm_of_mem (B : Subgroup A) [Fintype B] {b : A} (hb : b ∈ B) (g : G) :
    b • subgroupNorm B g = subgroupNorm B g := by
  rw [subgroupNorm_apply]
  have := map_prod (MulDistribMulAction.toMonoidHom G b) (fun x : B => (x : A) • g) Finset.univ
  rw [MulDistribMulAction.toMonoidHom_apply] at this
  rw [this]
  refine Fintype.prod_equiv (Equiv.mulLeft (⟨b, hb⟩ : B)) _ _ fun x => ?_
  rw [MulDistribMulAction.toMonoidHom_apply, ← mul_smul]
  rfl

theorem subgroupNorm_of_fixed (B : Subgroup A) [Fintype B] {x : G}
    (hx : ∀ b : B, (b : A) • x = x) : subgroupNorm B x = x ^ Fintype.card B := by
  rw [subgroupNorm_apply]
  simp [hx]

end Norm

section Part2

variable {r : ℕ} [Fact r.Prime] {A : Type*} [CommGroup A] [Finite A] {G : Type*} [CommGroup G]
  [Finite G] [MulDistribMulAction A G]

omit [Fact r.Prime] [Finite A] [Finite G] in
theorem isPGroup_of_pow_eq_one (hA : ∀ a : A, a ^ r = 1) : IsPGroup r A :=
  fun a => ⟨1, by simpa using hA a⟩

omit [Finite G] in
theorem fixedPointSubgroup_top_eq_bot (hA : IsPGroup r A) (hG : ¬ r ∣ Nat.card G)
    (hGA : commutatorAction A G = ⊤) : fixedPointSubgroup (⊤ : Subgroup A) G = ⊥ := by
  classical
  have : Fintype (⊤ : Subgroup A) := Fintype.ofFinite _
  have hker : commutatorAction A G ≤ MonoidHom.ker (subgroupNorm (⊤ : Subgroup A) : G →* G) := by
    unfold commutatorAction commutatorSubgroup
    rw [Subgroup.closure_le]
    rintro _ ⟨a, h, -, rfl⟩
    rw [SetLike.mem_coe, MonoidHom.mem_ker, map_mul, map_inv, ← smul_subgroupNorm,
      smul_subgroupNorm_of_mem ⊤ (Subgroup.mem_top a), inv_mul_cancel]
  rw [eq_bot_iff]
  intro c hc
  have h1 : subgroupNorm (⊤ : Subgroup A) c = 1 := hker (hGA ▸ Subgroup.mem_top c)
  rw [subgroupNorm_of_fixed _ hc] at h1
  have h2 : c ^ Nat.card G = 1 := pow_card_eq_one'
  have h3 : Nat.Coprime (Fintype.card (⊤ : Subgroup A)) (Nat.card G) := by
    rw [← Nat.card_eq_fintype_card]
    exact coprime_card_subgroup_of_isPGroup hA ⊤ hG
  have := pow_gcd_eq_one.2 ⟨h1, h2⟩
  rwa [h3.gcd_eq_one, pow_one] at this

omit [Finite G] in
theorem index_eq_of_cyclic (hA : ∀ a : A, a ^ r = 1) (hG : ¬ r ∣ Nat.card G)
    (hGA : commutatorAction A G = ⊤) {B : Subgroup A} (hB : IsCyclic (A ⧸ B))
    (hne : fixedPointSubgroup B G ≠ ⊥) : B.index = r := by
  have hBtop : B ≠ ⊤ := by
    rintro rfl
    exact hne (fixedPointSubgroup_top_eq_bot (isPGroup_of_pow_eq_one hA) hG hGA)
  have hexp : ∀ x : A ⧸ B, x ^ r = 1 := by
    intro x
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    rw [← QuotientGroup.mk_pow, hA a, QuotientGroup.mk_one]
  have hdvd : B.index ∣ r := by
    rw [Subgroup.index, ← IsCyclic.exponent_eq_card]
    exact Monoid.exponent_dvd_of_forall_pow_eq_one hexp
  exact ((Nat.dvd_prime Fact.out).1 hdvd).resolve_left fun h => hBtop (Subgroup.index_eq_one.1 h)

omit [Finite G] [MulDistribMulAction A G] in
theorem sup_eq_top_of_index_eq {B₀ B : Subgroup A} (h₀ : B₀.index = r) (h : B.index = r)
    (hne : B₀ ≠ B) : B₀ ⊔ B = ⊤ := by
  by_contra hne'
  have h1 : (B₀ ⊔ B).index ∣ r := h₀ ▸ Subgroup.index_dvd_of_le le_sup_left
  have h2 : (B₀ ⊔ B).index ≠ 1 := fun h => hne' (Subgroup.index_eq_one.1 h)
  have h3 : (B₀ ⊔ B).index = r := ((Nat.dvd_prime Fact.out).1 h1).resolve_left h2
  have hcard : ∀ K : Subgroup A, K.index = r → Nat.card K * r = Nat.card A := fun K hK => by
    rw [← hK]
    exact K.card_mul_index
  have e0 : B₀ = B₀ ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_left (by
    have := (hcard B₀ h₀).trans (hcard (B₀ ⊔ B) h3).symm
    exact (Nat.eq_of_mul_eq_mul_right (Fact.out : r.Prime).pos this).ge)
  have e1 : B = B₀ ⊔ B := Subgroup.eq_of_le_of_card_ge le_sup_right (by
    have := (hcard B h).trans (hcard (B₀ ⊔ B) h3).symm
    exact (Nat.eq_of_mul_eq_mul_right (Fact.out : r.Prime).pos this).ge)
  exact hne (e0.trans e1.symm)

omit [Finite G] in
theorem subgroupNorm_eq_one_of_fixed (hA : ∀ a : A, a ^ r = 1) (hG : ¬ r ∣ Nat.card G)
    (hGA : commutatorAction A G = ⊤) (B₀ B : Subgroup A) [Fintype B₀] (h₀ : B₀.index = r)
    (h : B.index = r) (hne : B₀ ≠ B) {x : G} (hx : x ∈ fixedPointSubgroup B G) :
    subgroupNorm B₀ x = 1 := by
  have hsup := sup_eq_top_of_index_eq h₀ h hne
  have hz : subgroupNorm B₀ x ∈ fixedPointSubgroup (⊤ : Subgroup A) G := by
    intro a
    have ha : (a : A) ∈ B₀ ⊔ B := by rw [hsup]; exact Subgroup.mem_top _
    obtain ⟨b₀, hb₀, b, hb, hab⟩ := Subgroup.mem_sup.1 ha
    have h1 : b • subgroupNorm B₀ x = subgroupNorm B₀ x := by
      rw [smul_subgroupNorm]
      congr 1
      exact hx ⟨b, hb⟩
    have h2 : b₀ • subgroupNorm B₀ x = subgroupNorm B₀ x := smul_subgroupNorm_of_mem B₀ hb₀ x
    show (a : A) • subgroupNorm B₀ x = subgroupNorm B₀ x
    rw [← hab, mul_smul, h1, h2]
  rw [fixedPointSubgroup_top_eq_bot (isPGroup_of_pow_eq_one hA) hG hGA, Subgroup.mem_bot] at hz
  exact hz

end Part2

end A1b

open A1b

theorem a117_generation {r : ℕ} [Fact r.Prime] {A : Type*} [CommGroup A] [Finite A]
    (hA : IsPGroup r A) {G : Type*} [Group G] [Finite G] [MulDistribMulAction A G]
    (hG : ¬ r ∣ Nat.card G) :
    ⨆ (B : Subgroup A) (_ : IsCyclic (A ⧸ B) ∧ fixedPointSubgroup B G ≠ ⊥),
      fixedPointSubgroup B G = ⊤ := by
  rw [eq_top_iff, ← cyclic_generation hA hG]
  refine iSup₂_le fun B hB => ?_
  by_cases h : fixedPointSubgroup B G = ⊥
  · rw [h]
    exact bot_le
  · exact le_iSup₂ (f := fun (B : Subgroup A)
      (_ : IsCyclic (A ⧸ B) ∧ fixedPointSubgroup B G ≠ ⊥) => fixedPointSubgroup B G) B ⟨hB, h⟩

theorem a117_index_eq {r : ℕ} [Fact r.Prime] {A : Type*} [CommGroup A] [Finite A]
    (hA : ∀ a : A, a ^ r = 1) {G : Type*} [CommGroup G] [MulDistribMulAction A G]
    (hG : ¬ r ∣ Nat.card G) (hGA : commutatorAction A G = ⊤) {B : Subgroup A}
    (hB : IsCyclic (A ⧸ B)) (hne : fixedPointSubgroup B G ≠ ⊥) : B.index = r :=
  index_eq_of_cyclic hA hG hGA hB hne

theorem a117_isIndexedDirectProduct {r : ℕ} [Fact r.Prime] {A : Type*} [CommGroup A] [Finite A]
    (hA : ∀ a : A, a ^ r = 1) {G : Type*} [CommGroup G] [Finite G] [MulDistribMulAction A G]
    (hG : ¬ r ∣ Nat.card G) (hGA : commutatorAction A G = ⊤) :
    IsIndexedDirectProduct
      (fun B : {B : Subgroup A | IsCyclic (A ⧸ B) ∧ fixedPointSubgroup B G ≠ ⊥} =>
        fixedPointSubgroup (B : Subgroup A) G) := by
  classical
  have hAp : IsPGroup r A := isPGroup_of_pow_eq_one hA
  refine ⟨fun B => inferInstance, ?_, ?_⟩
  · intro B₀
    obtain ⟨B₀, hB₀⟩ := B₀
    have : Fintype B₀ := Fintype.ofFinite _
    rw [disjoint_iff, eq_bot_iff]
    rintro x ⟨hx0, hxsup⟩
    have hker : (⨆ (j : {B : Subgroup A | IsCyclic (A ⧸ B) ∧ fixedPointSubgroup B G ≠ ⊥})
        (_ : j ≠ ⟨B₀, hB₀⟩), fixedPointSubgroup (j : Subgroup A) G) ≤
        MonoidHom.ker (subgroupNorm B₀ : G →* G) := by
      refine iSup₂_le fun j hj y hy => ?_
      rw [MonoidHom.mem_ker]
      refine subgroupNorm_eq_one_of_fixed hA hG hGA B₀ j (a117_index_eq hA hG hGA hB₀.1 hB₀.2)
        (a117_index_eq hA hG hGA j.2.1 j.2.2) ?_ hy
      intro h
      exact hj (Subtype.ext h.symm)
    have h1 : subgroupNorm B₀ x = 1 := hker hxsup
    rw [subgroupNorm_of_fixed _ hx0] at h1
    have h2 : x ^ Nat.card G = 1 := pow_card_eq_one'
    have h3 : Nat.Coprime (Fintype.card B₀) (Nat.card G) := by
      rw [← Nat.card_eq_fintype_card]
      exact coprime_card_subgroup_of_isPGroup hAp B₀ hG
    have := pow_gcd_eq_one.2 ⟨h1, h2⟩
    rw [h3.gcd_eq_one, pow_one] at this
    exact Subgroup.mem_bot.2 this
  · have h := a117_generation hAp (G := G) hG
    rw [← h]
    exact (iSup_subtype' (p := fun B : Subgroup A =>
      IsCyclic (A ⧸ B) ∧ fixedPointSubgroup B G ≠ ⊥) (f := fun B _ => fixedPointSubgroup B G)).symm

end CFSG.Quasithin

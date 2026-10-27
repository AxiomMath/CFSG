module

public import CFSG.RankThree.PartOne.KE6.E6LStdIso
public import CFSG.RankThree.PartOne.KE6.E6LComm27
public import CFSG.RankThree.Chevalley.SteinbergBIE6Commutant

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Minuscule
  CFSG.RankThree.PartOne.KD4T CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.LieType.AlgebraicGroups
open CFSG.RankThree.PartOne.KE (twistedFixedPoints mem_twistedFixedPoints)
open CFSG.RankThree.Chevalley (eq_zero_of_forall_sum_pow_smul)
open scoped Matrix MatrixGroups

section SL2

variable {τ : Tag} {L : Type} [Field L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem rho6_three : rho6 3 = 3 := by decide

theorem StdTwist6.middle_SL2 [E6Sub τ] {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (h : StdTwist6 n₁ π) {k : Type} [Field k] [Algebra k L] (hk : Nat.card k = ℓ ^ f)
    (Y : SL(2, k)) :
    simpleRootSL2 τ L (e6Idx 3) (Matrix.SpecialLinearGroup.map (algebraMap k L) Y) ∈
      stdLayer τ ℓ f n₁ := by
  have hπ3 : π (e6Idx (3 : Fin Tag.E6.rank)) = e6Idx 3 := by
    rcases h.hπ with rfl | rfl
    · rfl
    · rw [rhoτ_e6Idx, rho6_three]
  have hkfin : Finite k := Nat.finite_of_card_ne_zero (by
    rw [hk]
    exact pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero)
  have : Fintype k := Fintype.ofFinite k
  have hι : ∀ b : k, algebraMap k L b ^ ℓ ^ f = algebraMap k L b := fun b => by
    rw [← map_pow]
    congr 1
    have := FiniteField.pow_card b
    rwa [← Nat.card_eq_fintype_card, hk] at this
  have hj : e6Idx (3 : Fin Tag.E6.rank) ∈ e6Set τ := e6Idx_mem_e6Set 3
  have hfix : ∀ c : L, c ^ ℓ ^ f = c → xUnit τ L (e6Idx 3) c ∈ stdLayer τ ℓ f n₁ ∧
      yUnit τ L (e6Idx 3) c ∈ stdLayer τ ℓ f n₁ := fun c hc => by
    refine ⟨mem_stdLayer.2 ⟨xUnit_mem_subsystemGroup hj c, ?_⟩,
      mem_stdLayer.2 ⟨yUnit_mem_subsystemGroup hj c, ?_⟩⟩
    · rw [units_map_entrywiseHom_xUnit, iterateFrobenius_def, hc, (h.hgen _ hj c).1, hπ3]
    · rw [units_map_entrywiseHom_yUnit, iterateFrobenius_def, hc, (h.hgen _ hj c).2, hπ3]
  have hT : (stdLayer τ ℓ f n₁).comap ((simpleRootSL2 τ L (e6Idx 3)).comp
      (Matrix.SpecialLinearGroup.map (algebraMap k L))) = ⊤ := by
    refine eq_top_iff.2 ?_
    rw [← (CFSG.LocalAnalysis.ComponentInitial.sl2_closure_upper_lower :
      Subgroup.closure (Set.range (uSL (K := k)) ∪ Set.range vSL) = ⊤), Subgroup.closure_le]
    rintro _ (⟨b, rfl⟩ | ⟨b, rfl⟩)
    · change simpleRootSL2 τ L (e6Idx 3) (Matrix.SpecialLinearGroup.map (algebraMap k L) (uSL b)) ∈
        stdLayer τ ℓ f n₁
      rw [map_uSL, simpleRootSL2_uSL]
      exact (hfix _ (hι b)).1
    · change simpleRootSL2 τ L (e6Idx 3) (Matrix.SpecialLinearGroup.map (algebraMap k L) (vSL b)) ∈
        stdLayer τ ℓ f n₁
      rw [map_vSL, simpleRootSL2_vSL]
      exact (hfix _ (hι b)).2
  have hA : Y ∈ (stdLayer τ ℓ f n₁).comap ((simpleRootSL2 τ L (e6Idx 3)).comp
      (Matrix.SpecialLinearGroup.map (algebraMap k L))) := hT ▸ Subgroup.mem_top Y
  exact hA

end SL2

theorem commute_of_interpolation {L : Type} {M : Type*} [Field L] [Ring M] [Algebra L M]
    (X E F : M) {q : ℕ} (hq : 2 ≤ q) (S : Finset L) (hS : q ^ 2 ≤ S.card)
    (h : ∀ c ∈ S, Commute X ((1 + c • E) * (1 + c ^ q • F))) : Commute X E ∧ Commute X F := by
  have hn : Function.Injective (![1, q, q + 1] : Fin 3 → ℕ) := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp at hij ⊢ <;> omega
  have hlt : ∀ i : Fin 3, (![1, q, q + 1] : Fin 3 → ℕ) i < S.card := by
    intro i
    fin_cases i <;> simp <;> nlinarith
  have key : ∀ c ∈ S, ∑ i : Fin 3, c ^ (![1, q, q + 1] : Fin 3 → ℕ) i •
      (![X * E - E * X, X * F - F * X, X * (E * F) - (E * F) * X] : Fin 3 → M) i = 0 := by
    intro c hc
    have h1 := (h c hc).eq
    have e1 : X * ((1 + c • E) * (1 + c ^ q • F)) = X + c • (X * E) + c ^ q • (X * F) +
        (c ^ q * c) • (X * (E * F)) := by
      simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
        smul_add, smul_smul, add_assoc]
    have e2 : ((1 + c • E) * (1 + c ^ q • F)) * X = X + c • (E * X) + c ^ q • (F * X) +
        (c ^ q * c) • ((E * F) * X) := by
      simp only [mul_add, add_mul, mul_one, one_mul, mul_smul_comm, smul_mul_assoc,
        smul_add, smul_smul, add_assoc]
    rw [e1, e2] at h1
    have h2 := sub_eq_zero.2 h1
    rw [Fin.sum_univ_three]
    change c ^ 1 • (X * E - E * X) + c ^ q • (X * F - F * X) +
      c ^ (q + 1) • (X * (E * F) - E * F * X) = 0
    rw [pow_one, pow_succ, smul_sub, smul_sub, smul_sub, ← h2]
    abel
  have h0 := eq_zero_of_forall_sum_pow_smul (n := (![1, q, q + 1] : Fin 3 → ℕ)) (F := S)
    (c := (![X * E - E * X, X * F - F * X, X * (E * F) - (E * F) * X] : Fin 3 → M)) hn hlt key 0
  have h1 := eq_zero_of_forall_sum_pow_smul (n := (![1, q, q + 1] : Fin 3 → ℕ)) (F := S)
    (c := (![X * E - E * X, X * F - F * X, X * (E * F) - (E * F) * X] : Fin 3 → M)) hn hlt key 1
  exact ⟨sub_eq_zero.1 h0, sub_eq_zero.1 h1⟩

section Pairs

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] {ℓ f : ℕ} [Fact ℓ.Prime]
  [CharP L ℓ]

theorem pair_roots : ∀ a b : Fin Tag.E6.rank, rho6 a ≠ a → b = rho6 a →
    (List.ofFn (Pi.single a 1 + Pi.single b 1 : Fin Tag.E6.rank → ℤ) ∉ Tag.E6.artifactRoots ∧
      List.ofFn ((-Pi.single a 1) + (-Pi.single b 1) : Fin Tag.E6.rank → ℤ) ∉
        Tag.E6.artifactRoots ∧
      (Pi.single a 1 + Pi.single b 1 : Fin Tag.E6.rank → ℤ) ≠ 0 ∧
      ((-Pi.single a 1) + (-Pi.single b 1) : Fin Tag.E6.rank → ℤ) ≠ 0) := by
  decide +kernel

theorem xm_comm_x {a b : Fin Tag.E6.rank} (ha : rho6 a ≠ a) (hb : b = rho6 a) (c d : L) :
    e6Data_valid.xm L (Pi.single a 1) c * e6Data_valid.xm L (Pi.single b 1) d =
      e6Data_valid.xm L (Pi.single b 1) d * e6Data_valid.xm L (Pi.single a 1) c := by
  obtain ⟨h1, -, h3, -⟩ := pair_roots a b ha hb
  have hnr : ¬ IsRoot Tag.E6 (Pi.single a 1 + Pi.single b 1) := by
    rw [isRoot_iff_mem_artifactRoots]
    exact h1
  exact commutatorElement_eq_one_iff_mul_comm.1
    ((e6Data_valid.commutator_xm L (isRoot_single _ a) (isRoot_single _ b) h3).2 hnr c d)

theorem xm_comm_y {a b : Fin Tag.E6.rank} (ha : rho6 a ≠ a) (hb : b = rho6 a) (c d : L) :
    e6Data_valid.xm L (-Pi.single a 1) c * e6Data_valid.xm L (-Pi.single b 1) d =
      e6Data_valid.xm L (-Pi.single b 1) d * e6Data_valid.xm L (-Pi.single a 1) c := by
  obtain ⟨-, h2, -, h4⟩ := pair_roots a b ha hb
  have hnr : ¬ IsRoot Tag.E6 ((-Pi.single a 1) + (-Pi.single b 1)) := by
    rw [isRoot_iff_mem_artifactRoots]
    exact h2
  exact commutatorElement_eq_one_iff_mul_comm.1
    ((e6Data_valid.commutator_xm L (isRoot_neg_single _ a) (isRoot_neg_single _ b) h4).2 hnr c d)

theorem xUnit_comm {a b : Fin Tag.E6.rank} (ha : rho6 a ≠ a) (hb : b = rho6 a)
    (c d : L) :
    xUnit τ L (e6Idx a) c * xUnit τ L (e6Idx b) d = xUnit τ L (e6Idx b) d * xUnit τ L (e6Idx a) c := by
  have := m27ResMin_injective (τ := τ) (K := L)
    (a₁ := ⟨xUnit τ L (e6Idx a) c, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set a) c⟩ *
      ⟨xUnit τ L (e6Idx b) d, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set b) d⟩)
    (a₂ := ⟨xUnit τ L (e6Idx b) d, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set b) d⟩ *
      ⟨xUnit τ L (e6Idx a) c, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set a) c⟩)
    (by rw [map_mul, map_mul, m27ResMin_xUnit, m27ResMin_xUnit, xm_comm_x ha hb])
  exact congrArg Subtype.val this

theorem yUnit_comm {a b : Fin Tag.E6.rank} (ha : rho6 a ≠ a) (hb : b = rho6 a)
    (c d : L) :
    yUnit τ L (e6Idx a) c * yUnit τ L (e6Idx b) d = yUnit τ L (e6Idx b) d * yUnit τ L (e6Idx a) c := by
  have := m27ResMin_injective (τ := τ) (K := L)
    (a₁ := ⟨yUnit τ L (e6Idx a) c, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set a) c⟩ *
      ⟨yUnit τ L (e6Idx b) d, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set b) d⟩)
    (a₂ := ⟨yUnit τ L (e6Idx b) d, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set b) d⟩ *
      ⟨yUnit τ L (e6Idx a) c, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set a) c⟩)
    (by rw [map_mul, map_mul, m27ResMin_yUnit, m27ResMin_yUnit, xm_comm_y ha hb])
  exact congrArg Subtype.val this

theorem StdTwist6.pair_mem_x {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (h : StdTwist6 n₁ π) (hπ : π = rhoτ τ) {a b : Fin Tag.E6.rank} (ha : rho6 a ≠ a)
    (hb : b = rho6 a) {c : L} (hc : c ^ (ℓ ^ f * ℓ ^ f) = c) :
    xUnit τ L (e6Idx a) c * xUnit τ L (e6Idx b) (c ^ ℓ ^ f) ∈ stdLayer τ ℓ f n₁ := by
  have hba : rho6 b = a := by rw [hb, rho6_rho6]
  refine mem_stdLayer.2 ⟨mul_mem (xUnit_mem_subsystemGroup (e6Idx_mem_e6Set a) _)
    (xUnit_mem_subsystemGroup (e6Idx_mem_e6Set b) _), ?_⟩
  show frobTwistGL τ L ℓ f n₁ (xUnit τ L (e6Idx a) c * xUnit τ L (e6Idx b) (c ^ ℓ ^ f)) =
    xUnit τ L (e6Idx a) c * xUnit τ L (e6Idx b) (c ^ ℓ ^ f)
  rw [map_mul, h.theta_xUnit (e6Idx_mem_e6Set a), h.theta_xUnit (e6Idx_mem_e6Set b), hπ,
    rhoτ_e6Idx, rhoτ_e6Idx, ← hb, hba, ← pow_mul, hc]
  exact (xUnit_comm ha hb c _).symm

theorem StdTwist6.pair_mem_y {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (h : StdTwist6 n₁ π) (hπ : π = rhoτ τ) {a b : Fin Tag.E6.rank} (ha : rho6 a ≠ a)
    (hb : b = rho6 a) {c : L} (hc : c ^ (ℓ ^ f * ℓ ^ f) = c) :
    yUnit τ L (e6Idx a) c * yUnit τ L (e6Idx b) (c ^ ℓ ^ f) ∈ stdLayer τ ℓ f n₁ := by
  have hba : rho6 b = a := by rw [hb, rho6_rho6]
  refine mem_stdLayer.2 ⟨mul_mem (yUnit_mem_subsystemGroup (e6Idx_mem_e6Set a) _)
    (yUnit_mem_subsystemGroup (e6Idx_mem_e6Set b) _), ?_⟩
  show frobTwistGL τ L ℓ f n₁ (yUnit τ L (e6Idx a) c * yUnit τ L (e6Idx b) (c ^ ℓ ^ f)) =
    yUnit τ L (e6Idx a) c * yUnit τ L (e6Idx b) (c ^ ℓ ^ f)
  rw [map_mul, h.theta_yUnit (e6Idx_mem_e6Set a), h.theta_yUnit (e6Idx_mem_e6Set b), hπ,
    rhoτ_e6Idx, rhoτ_e6Idx, ← hb, hba, ← pow_mul, hc]
  exact (yUnit_comm ha hb c _).symm

end Pairs

section CommMain

variable {τ : Tag} [M27Ok τ] [E6Sub τ] {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ}
  [Fact ℓ.Prime] [CharP L ℓ]

theorem StdTwist6.commute_of_commute {n₁ : ModGL τ L} {π : Equiv.Perm (Fin τ.rank)}
    (h : StdTwist6 n₁ π) (hf : 1 ≤ f) {q' : ModGL τ L}
    (hq' : q' ∈ subsystemGroup τ L (e6Set τ)) (hc : ∀ u ∈ stdLayer τ ℓ f n₁, q' * u = u * q') :
    ∀ g ∈ subsystemGroup τ L (e6Set τ), q' * g = g * q' := by
  set X : Module.End L (Fin e6Data.d →₀ L) :=
    ((m27Res L e6Set_lt' ⟨q', hq'⟩ : GL27 L) : Module.End L (Fin e6Data.d →₀ L)) with hXdef
  have hXu : ∀ (u : ModGL τ L) (hu : u ∈ stdLayer τ ℓ f n₁),
      Commute X ((m27Res L e6Set_lt' ⟨u, stdLayer_le n₁ hu⟩ : GL27 L) :
        Module.End L (Fin e6Data.d →₀ L)) := by
    intro u hu
    have h1 : (⟨q', hq'⟩ : subsystemGroup τ L (e6Set τ)) * ⟨u, stdLayer_le n₁ hu⟩ =
        ⟨u, stdLayer_le n₁ hu⟩ * ⟨q', hq'⟩ := Subtype.ext (hc u hu)
    have h2 := congrArg (m27Res L e6Set_lt') h1
    rw [map_mul, map_mul] at h2
    have h3 := congrArg (fun z : GL27 L => (z : Module.End L (Fin e6Data.d →₀ L))) h2
    rw [Units.val_mul, Units.val_mul] at h3
    exact h3
  have hone : ∀ {E : Module.End L (Fin e6Data.d →₀ L)}, Commute X (1 + (1 : L) • E) →
      Commute X E := fun {E} hc1 => by
    simpa [Commute, SemiconjBy, mul_add, add_mul] using hc1
  have hfixed : ∀ j : Fin Tag.E6.rank, π (e6Idx j) = e6Idx j →
      Commute X (e6Data.rootOp L (Pi.single j 1)) ∧ Commute X (e6Data.rootOp L (-Pi.single j 1)) := by
    intro j hj
    have hjJ : e6Idx (τ := τ) j ∈ e6Set τ := e6Idx_mem_e6Set j
    have hx : xUnit τ L (e6Idx j) 1 ∈ stdLayer τ ℓ f n₁ := mem_stdLayer.2
      ⟨xUnit_mem_subsystemGroup hjJ 1, by
        rw [units_map_entrywiseHom_xUnit, map_one, (h.hgen _ hjJ 1).1, hj]⟩
    have hy : yUnit τ L (e6Idx j) 1 ∈ stdLayer τ ℓ f n₁ := mem_stdLayer.2
      ⟨yUnit_mem_subsystemGroup hjJ 1, by
        rw [units_map_entrywiseHom_yUnit, map_one, (h.hgen _ hjJ 1).2, hj]⟩
    have c1 := hXu _ hx
    have c2 := hXu _ hy
    rw [m27Res_xUnit e6Set_lt' j hjJ 1, e6Data_valid.xu_val] at c1
    rw [m27Res_yUnit e6Set_lt' j hjJ 1, e6Data_valid.xu_val] at c2
    exact ⟨hone c1, hone c2⟩

  have hpair : π = rhoτ τ → ∀ a : Fin Tag.E6.rank, rho6 a ≠ a →
      (Commute X (e6Data.rootOp L (Pi.single a 1)) ∧
        Commute X (e6Data.rootOp L (Pi.single (rho6 a) 1))) ∧
      (Commute X (e6Data.rootOp L (-Pi.single a 1)) ∧
        Commute X (e6Data.rootOp L (-Pi.single (rho6 a) 1))) := by
    intro hπ a ha
    classical
    have : Finite (frobeniusFixedField L ℓ (2 * f)) := finite_frobeniusFixedField (by omega)
    have : Fintype (frobeniusFixedField L ℓ (2 * f)) := Fintype.ofFinite _
    set S : Finset L := (Finset.univ : Finset (frobeniusFixedField L ℓ (2 * f))).map
      ⟨Subtype.val, Subtype.val_injective⟩ with hSdef
    have hℓ2 : 2 ≤ ℓ := (Fact.out : ℓ.Prime).two_le
    have hq2 : 2 ≤ ℓ ^ f := by
      calc 2 ≤ ℓ := hℓ2
        _ = ℓ ^ 1 := (pow_one ℓ).symm
        _ ≤ ℓ ^ f := Nat.pow_le_pow_right (by omega) hf
    have hScard : (ℓ ^ f) ^ 2 ≤ S.card := by
      rw [hSdef, Finset.card_map, Finset.card_univ,
        ← Nat.card_eq_fintype_card, card_frobeniusFixedField_pow (by omega), ← pow_mul,
        mul_comm]
    have hS : ∀ c ∈ S, c ^ (ℓ ^ f * ℓ ^ f) = c := by
      intro c hc
      obtain ⟨c', -, rfl⟩ := Finset.mem_map.1 hc
      have := mem_frobeniusFixedField.1 c'.2
      rwa [← pow_add, ← two_mul]
    refine ⟨commute_of_interpolation X _ _ hq2 S hScard (fun c hc => ?_),
      commute_of_interpolation X _ _ hq2 S hScard (fun c hc => ?_)⟩
    · have hmem := h.pair_mem_x hπ ha rfl (hS c hc)
      have c1 := hXu _ hmem
      have e : (⟨xUnit τ L (e6Idx a) c * xUnit τ L (e6Idx (rho6 a)) (c ^ ℓ ^ f),
          stdLayer_le n₁ hmem⟩ : subsystemGroup τ L (e6Set τ)) =
          ⟨xUnit τ L (e6Idx a) c, xUnit_mem_subsystemGroup (e6Idx_mem_e6Set a) c⟩ *
          ⟨xUnit τ L (e6Idx (rho6 a)) (c ^ ℓ ^ f),
            xUnit_mem_subsystemGroup (e6Idx_mem_e6Set (rho6 a)) _⟩ := rfl
      rw [e, map_mul, m27Res_xUnit e6Set_lt' a (e6Idx_mem_e6Set a) c,
        m27Res_xUnit e6Set_lt' (rho6 a) (e6Idx_mem_e6Set (rho6 a)), Units.val_mul,
        e6Data_valid.xu_val, e6Data_valid.xu_val] at c1
      exact c1
    · have hmem := h.pair_mem_y hπ ha rfl (hS c hc)
      have c1 := hXu _ hmem
      have e : (⟨yUnit τ L (e6Idx a) c * yUnit τ L (e6Idx (rho6 a)) (c ^ ℓ ^ f),
          stdLayer_le n₁ hmem⟩ : subsystemGroup τ L (e6Set τ)) =
          ⟨yUnit τ L (e6Idx a) c, yUnit_mem_subsystemGroup (e6Idx_mem_e6Set a) c⟩ *
          ⟨yUnit τ L (e6Idx (rho6 a)) (c ^ ℓ ^ f),
            yUnit_mem_subsystemGroup (e6Idx_mem_e6Set (rho6 a)) _⟩ := rfl
      rw [e, map_mul, m27Res_yUnit e6Set_lt' a (e6Idx_mem_e6Set a) c,
        m27Res_yUnit e6Set_lt' (rho6 a) (e6Idx_mem_e6Set (rho6 a)), Units.val_mul,
        e6Data_valid.xu_val, e6Data_valid.xu_val] at c1
      exact c1
  have hall : ∀ j : Fin Tag.E6.rank, Commute X (e6Data.rootOp L (Pi.single j 1)) ∧
      Commute X (e6Data.rootOp L (-Pi.single j 1)) := by
    intro j
    rcases h.hπ with hπ | hπ
    · exact hfixed j (by rw [hπ]; rfl)
    · by_cases hj : rho6 j = j
      · exact hfixed j (by rw [hπ, rhoτ_e6Idx, hj])
      · have hcases : j = 0 ∨ j = 5 ∨ j = 2 ∨ j = 4 := by
          revert j
          decide
        rcases hcases with rfl | rfl | rfl | rfl
        · exact ⟨(hpair hπ 0 hj).1.1, (hpair hπ 0 hj).2.1⟩
        · have hp := hpair hπ 0 (by decide)
          exact ⟨hp.1.2, hp.2.2⟩
        · exact ⟨(hpair hπ 2 hj).1.1, (hpair hπ 2 hj).2.1⟩
        · have hp := hpair hπ 2 (by decide)
          exact ⟨hp.1.2, hp.2.2⟩
  obtain ⟨cc, hcc⟩ := eq_smul_one_of_commute (fun j => (hall j).1) (fun j => (hall j).2)
  intro g hg
  have h1 : (⟨q', hq'⟩ : subsystemGroup τ L (e6Set τ)) * ⟨g, hg⟩ =
      ⟨g, hg⟩ * ⟨q', hq'⟩ := by
    apply m27ResMin_injective (τ := τ) (K := L)
    rw [map_mul, map_mul]
    apply Subtype.ext
    apply Units.ext
    change X * ((m27Res L e6Set_lt' ⟨g, hg⟩ : GL27 L) : Module.End L (Fin e6Data.d →₀ L)) =
      ((m27Res L e6Set_lt' ⟨g, hg⟩ : GL27 L) : Module.End L (Fin e6Data.d →₀ L)) * X
    rw [hcc, smul_mul_assoc, one_mul, mul_smul_comm, mul_one]
  exact congrArg Subtype.val h1

end CommMain

end CFSG.RankThree.PartOne.KE6

module

public import CFSG.RankThree.PartOne.Q1327T.Item7U3B

public section

namespace CFSG.RankThree.PartOne.Q1327T

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU CFSG.Assembly.LowTwoRank

section Generic

variable {Q : Type} [Group Q] {K : Type} [Field K] {p : ℕ}

omit [Group Q] in
@[expose] def ent3 (g : GL (Fin 3) K) (i j : Fin 3) : K := (g : Matrix (Fin 3) (Fin 3) K) i j

omit [Group Q] in
theorem injective_of_ne3 {d : Fin 3 → Kˣ} (h01 : d 0 ≠ d 1) (h02 : d 0 ≠ d 2) (h12 : d 1 ≠ d 2) :
    Function.Injective d := by
  intro i j hij
  fin_cases i <;> fin_cases j <;> first | rfl | (exfalso; simp_all)

omit [Group Q] in
theorem conj_mem_scalars_iff' {n : ℕ} (P y : GL (Fin n) K) :
    P * y * P⁻¹ ∈ StatedScalars (Fin n) K ↔ y ∈ StatedScalars (Fin n) K := by
  constructor
  · intro h
    have := (StatedScalars.normal (Fin n) K).conj_mem _ h P⁻¹
    simpa [mul_assoc] using this
  · intro h
    exact (StatedScalars.normal (Fin n) K).conj_mem _ h P

theorem block_card_core [Finite K] {M : Subgroup (GL (Fin 3) K)} (hp : p.Prime) (π : M →* Q)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center M) (hpk : ¬ p ∣ Nat.card π.ker)
    {ct : M} (hc : ct ^ p = 1) {d : Fin 3 → Kˣ} (hd : (ct : GL (Fin 3) K) = diagU d)
    (h01 : d 0 = d 1) (h02 : d 0 ≠ d 2) {Kb : Subgroup Q}
    (hKbc : Kb ≤ Subgroup.centralizer ({π ct} : Set Q))
    (hKbN : (Kb.subgroupOf (Subgroup.centralizer ({π ct} : Set Q))).Normal)
    (hKbp : ⁅Kb, Kb⁆ = Kb) (hKb1 : Kb ≠ ⊥) (L : Subgroup M)
    (hLC : L ≤ Subgroup.centralizer ({ct} : Set M)) (hLs : IsSimpleGroup L)
    (hLinj : ∀ g ∈ L, π g = 1 → g = 1)
    (hLmem : ∀ g : M, ent3 (g : GL (Fin 3) K) 0 2 = 0 → ent3 (g : GL (Fin 3) K) 1 2 = 0 →
      ent3 (g : GL (Fin 3) K) 2 0 = 0 → ent3 (g : GL (Fin 3) K) 2 1 = 0 →
      ent3 (g : GL (Fin 3) K) 2 2 = 1 → g ∈ L) :
    Nat.card Kb = Nat.card L := by
  have hblock : ∀ g : Subgroup.centralizer ({ct} : Set M),
      (((g : M) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 0 2 = 0 ∧
      (((g : M) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 1 2 = 0 ∧
      (((g : M) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 0 = 0 ∧
      (((g : M) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 1 = 0 := by
    intro g
    have h1 : (g : M) * ct = ct * g := Subgroup.mem_centralizer_singleton_iff.1 g.2
    have h2 := congrArg (fun x : M => (x : GL (Fin 3) K)) h1
    simp only [Subgroup.coe_mul, hd] at h2
    exact block_of_commute_diagU h01 h02 h2
  let χ : Subgroup.centralizer ({ct} : Set M) →* Kˣ :=
    { toFun := fun g => Units.mk0 ((((g : M) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2)
        (entry22_ne_zero (hblock g).1 (hblock g).2.1 (hblock g).2.2.1 (hblock g).2.2.2)
      map_one' := by
        apply Units.ext
        simp
      map_mul' := fun g h => by
        apply Units.ext
        simp only [Units.val_mul, Units.val_mk0]
        exact entry22_mul (hblock g).2.2.1 (hblock g).2.2.2 (hblock h).1 (hblock h).2.1 }
  have hχ : ∀ g : Subgroup.centralizer ({ct} : Set M), χ g = 1 → (g : M) ∈ L := by
    intro g hg
    have h22 : (((g : M) : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) 2 2 = 1 := by
      have := congrArg Units.val hg
      simpa [χ] using this
    exact hLmem g (hblock g).1 (hblock g).2.1 (hblock g).2.2.1 (hblock g).2.2.2 h22
  exact card_eq_of_component hp π hπ hker hpk hc (C := Subgroup.centralizer {ct}) rfl
    (CQ := Subgroup.centralizer {π ct}) rfl hKbc hKbN hKbp hKb1 L hLC hLs hLinj χ hχ

theorem ker_eq_scalars {M : Subgroup (GL (Fin 3) K)} (π : M →* Q)
    (hscal : ∀ g, π g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K) :
    π.ker = (StatedScalars (Fin 3) K).subgroupOf M := by
  ext x
  rw [MonoidHom.mem_ker, hscal, Subgroup.mem_subgroupOf]

omit [Group Q] in
theorem scalars_subgroupOf_le_center (M : Subgroup (GL (Fin 3) K)) :
    (StatedScalars (Fin 3) K).subgroupOf M ≤ Subgroup.center M := by
  intro x hx
  obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.1 hx
  rw [Subgroup.mem_center_iff]
  intro y
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, ← hc]
  exact (Subgroup.mem_center_iff.1 (by
    rw [Matrix.GeneralLinearGroup.center_eq_range_scalar]
    exact ⟨c, rfl⟩) (y : GL (Fin 3) K))

theorem block_card_conj [Finite K] {M : Subgroup (GL (Fin 3) K)} (hp : p.Prime) (π : M →* Q)
    (hπ : Function.Surjective π)
    (hscal : ∀ g, π g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    (hpN : ¬ p ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf M)) {ct : M} (hc : ct ^ p = 1)
    (s : M) {d : Fin 3 → Kˣ} (hd : ((s⁻¹ * ct * s : M) : GL (Fin 3) K) = diagU d)
    (h01 : d 0 = d 1) (h02 : d 0 ≠ d 2) {Kb : Subgroup Q}
    (hKbc : Kb ≤ Subgroup.centralizer ({π ct} : Set Q))
    (hKbN : (Kb.subgroupOf (Subgroup.centralizer ({π ct} : Set Q))).Normal)
    (hKbp : ⁅Kb, Kb⁆ = Kb) (hKb1 : Kb ≠ ⊥) (L : Subgroup M)
    (hLC : L ≤ Subgroup.centralizer ({s⁻¹ * ct * s} : Set M)) (hLs : IsSimpleGroup L)
    (hLinj : ∀ g ∈ L, (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K → g = 1)
    (hLmem : ∀ g : M, ent3 (g : GL (Fin 3) K) 0 2 = 0 → ent3 (g : GL (Fin 3) K) 1 2 = 0 →
      ent3 (g : GL (Fin 3) K) 2 0 = 0 → ent3 (g : GL (Fin 3) K) 2 1 = 0 →
      ent3 (g : GL (Fin 3) K) 2 2 = 1 → g ∈ L) :
    Nat.card Kb = Nat.card L := by
  let π' : M →* Q := π.comp (MulAut.conj s).toMonoidHom
  have hπ' : Function.Surjective π' := hπ.comp (MulAut.conj s).surjective
  have hπ'ct : π' (s⁻¹ * ct * s) = π ct := by
    change π (s * (s⁻¹ * ct * s) * s⁻¹) = π ct
    congr 1
    group
  have hscal' : ∀ g, π' g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K := by
    intro g
    change π (s * g * s⁻¹) = 1 ↔ _
    rw [hscal]
    exact conj_mem_scalars_iff' (s : GL (Fin 3) K) g
  have hkerN := ker_eq_scalars π' hscal'
  have hc' : (s⁻¹ * ct * s) ^ p = 1 := by
    have h := conj_pow (a := s⁻¹) (b := ct) (i := p)
    rw [inv_inv] at h
    rw [h, hc]
    group
  refine block_card_core hp π' hπ' (hkerN ▸ scalars_subgroupOf_le_center M) (hkerN ▸ hpN)
    hc' hd h01 h02 (Kb := Kb) (by rw [hπ'ct]; exact hKbc) (by rw [hπ'ct]; exact hKbN) hKbp hKb1 L
    hLC hLs (fun g hg h1 => hLinj g hg ((hscal' g).1 h1)) hLmem

theorem block_card_of_diag [Finite K] {M : Subgroup (GL (Fin 3) K)} (hp : p.Prime)
    (hsw12 : (swGL12 : GL (Fin 3) K) ∈ M) (hsw02 : (swGL02 : GL (Fin 3) K) ∈ M) (π : M →* Q)
    (hπ : Function.Surjective π)
    (hscal : ∀ g, π g = 1 ↔ (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K)
    (hpN : ¬ p ∣ Nat.card ((StatedScalars (Fin 3) K).subgroupOf M)) {ct : M} (hc : ct ^ p = 1)
    (hct1 : π ct ≠ 1) {d : Fin 3 → Kˣ} (hd : (ct : GL (Fin 3) K) = diagU d) {Kb : Subgroup Q}
    (hKbc : Kb ≤ Subgroup.centralizer ({π ct} : Set Q))
    (hKbN : (Kb.subgroupOf (Subgroup.centralizer ({π ct} : Set Q))).Normal)
    (hKbp : ⁅Kb, Kb⁆ = Kb) (hKb1 : Kb ≠ ⊥) (L : Subgroup M)
    (hLdiag : ∀ d' : Fin 3 → Kˣ, d' 0 = d' 1 → ∀ g ∈ L,
      (g : GL (Fin 3) K) * diagU d' = diagU d' * g)
    (hLs : IsSimpleGroup L)
    (hLinj : ∀ g ∈ L, (g : GL (Fin 3) K) ∈ StatedScalars (Fin 3) K → g = 1)
    (hLmem : ∀ g : M, ent3 (g : GL (Fin 3) K) 0 2 = 0 → ent3 (g : GL (Fin 3) K) 1 2 = 0 →
      ent3 (g : GL (Fin 3) K) 2 0 = 0 → ent3 (g : GL (Fin 3) K) 2 1 = 0 →
      ent3 (g : GL (Fin 3) K) 2 2 = 1 → g ∈ L) :
    Nat.card Kb = Nat.card L := by
  have hLC : ∀ (s : M) {d' : Fin 3 → Kˣ},
      ((s⁻¹ * ct * s : M) : GL (Fin 3) K) = diagU d' → d' 0 = d' 1 →
        L ≤ Subgroup.centralizer ({s⁻¹ * ct * s} : Set M) := by
    intro s d' hd' h01' g hg
    rw [Subgroup.mem_centralizer_singleton_iff]
    apply Subtype.ext
    change (g : GL (Fin 3) K) * ((s⁻¹ * ct * s : M) : GL (Fin 3) K) =
      ((s⁻¹ * ct * s : M) : GL (Fin 3) K) * (g : GL (Fin 3) K)
    rw [hd']
    exact hLdiag d' h01' g hg
  have key : ∀ (s : M) {d' : Fin 3 → Kˣ}, ((s⁻¹ * ct * s : M) : GL (Fin 3) K) = diagU d' →
      d' 0 = d' 1 → d' 0 ≠ d' 2 → Nat.card Kb = Nat.card L := fun s d' hd' h01' h02' =>
    block_card_conj hp π hπ hscal hpN hc s hd' h01' h02' hKbc hKbN hKbp hKb1 L
      (hLC s hd' h01') hLs hLinj hLmem
  by_cases h01 : d 0 = d 1
  · by_cases h02 : d 0 = d 2
    · exfalso
      apply hct1
      rw [hscal]
      refine ⟨d 0, ?_⟩
      have hd' : d = fun _ => d 0 := funext fun i => by
        fin_cases i
        · rfl
        · exact h01.symm
        · exact h02.symm
      apply Units.ext
      rw [hd, hd']
      simp [diagU_val, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply]
    · exact key 1 (by simpa using hd) h01 h02
  · by_cases h02 : d 0 = d 2
    · refine key (⟨swGL12, hsw12⟩ : M) (d' := ![d 0, d 2, d 1]) ?_ (by simpa using h02)
        (by simpa using h01)
      change (swGL12 : GL (Fin 3) K)⁻¹ * (ct : GL (Fin 3) K) * swGL12 = _
      rw [hd, swGL12_conj]
    · by_cases h12 : d 1 = d 2
      · refine key (⟨swGL02, hsw02⟩ : M) (d' := ![d 2, d 1, d 0]) ?_ (by simpa using h12.symm) (by
          simp only [Matrix.cons_val_zero, Matrix.cons_val]
          intro h
          exact h01 (h.symm.trans h12.symm))
        change (swGL02 : GL (Fin 3) K)⁻¹ * (ct : GL (Fin 3) K) * swGL02 = _
        rw [hd, swGL02_conj]
      · exfalso
        have hinj : Function.Injective d := injective_of_ne3 h01 h02 h12
        have hkerN := ker_eq_scalars π hscal
        refine false_of_commutative_centralizer hp π hπ (hkerN ▸ scalars_subgroupOf_le_center M)
          (hkerN ▸ hpN) hc hKbc hKbp hKb1 ?_
        intro a ha b hb
        have hoff : ∀ x : M, x ∈ Subgroup.centralizer ({ct} : Set M) →
            ∀ i j : Fin 3, i ≠ j → ((x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j = 0 := by
          intro x hx i j hij
          have h1 : x * ct = ct * x := Subgroup.mem_centralizer_singleton_iff.1 hx
          have h2 := congrArg (fun y : M => (y : GL (Fin 3) K)) h1
          simp only [Subgroup.coe_mul, hd] at h2
          exact offdiag_zero_of_commute_diagU hinj h2 hij
        apply Subtype.ext
        rw [Subgroup.coe_mul, Subgroup.coe_mul]
        exact commute_of_offdiag_zero' (hoff a ha) (hoff b hb)

end Generic

end CFSG.RankThree.PartOne.Q1327T

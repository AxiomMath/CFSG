module

public import CFSG.RankThree.PartTwo.Sec16.Item16Res6ProofActComp

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiL2

open CFSG CFSG.Blueprint CFSG.RankThree.PartTwo.Sec16.Res6Act

theorem four_le_pRank_of_commuting {X : Type} [Group X] [Finite X] {x₁ x₂ x₃ x₄ : X}
    (c12 : Commute x₁ x₂) (c13 : Commute x₁ x₃) (c14 : Commute x₁ x₄) (c23 : Commute x₂ x₃)
    (c24 : Commute x₂ x₄) (c34 : Commute x₃ x₄)
    (hind : ∀ e₁ e₂ e₃ e₄ : ℤ, x₁ ^ e₁ * x₂ ^ e₂ * x₃ ^ e₃ * x₄ ^ e₄ = 1 →
      (5 : ℤ) ∣ e₁ ∧ (5 : ℤ) ∣ e₂ ∧ (5 : ℤ) ∣ e₃ ∧ (5 : ℤ) ∣ e₄) :
    4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) := by
  classical
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  let k : Set X := {x₁, x₂, x₃, x₄}
  have hk : k.Pairwise Commute := by
    intro a ha b hb _
    simp only [k, Set.mem_insert_iff, Set.mem_singleton_iff] at ha hb
    rcases ha with rfl | rfl | rfl | rfl <;> rcases hb with rfl | rfl | rfl | rfl <;>
      solve_by_elim [Commute.refl, Commute.symm, c12, c13, c14, c23, c24, c34]
  let _ : CommGroup (Subgroup.closure k) := Subgroup.closureCommGroupOfComm hk
  let y₁ : Subgroup.closure k := ⟨x₁, Subgroup.subset_closure (by simp [k])⟩
  let y₂ : Subgroup.closure k := ⟨x₂, Subgroup.subset_closure (by simp [k])⟩
  let y₃ : Subgroup.closure k := ⟨x₃, Subgroup.subset_closure (by simp [k])⟩
  let y₄ : Subgroup.closure k := ⟨x₄, Subgroup.subset_closure (by simp [k])⟩
  let θ' : Multiplicative (Fin 4 → ℤ) →* Subgroup.closure k :=
    { toFun := fun n => y₁ ^ (Multiplicative.toAdd n 0) * y₂ ^ (Multiplicative.toAdd n 1) *
        y₃ ^ (Multiplicative.toAdd n 2) * y₄ ^ (Multiplicative.toAdd n 3)
      map_one' := by simp
      map_mul' := fun a b => by
        simp only [toAdd_mul, Pi.add_apply, zpow_add]
        ac_rfl }
  let θ : Multiplicative (Fin 4 → ℤ) →* X := (Subgroup.closure k).subtype.comp θ'
  have hθ : ∀ n : Fin 4 → ℤ, θ (Multiplicative.ofAdd n) =
      x₁ ^ n 0 * x₂ ^ n 1 * x₃ ^ n 2 * x₄ ^ n 3 := fun n => by
    simp [θ, θ', y₁, y₂, y₃, y₄]
  set A := θ.range with hA
  have hAc : ∀ a b : A, a * b = b * a := by
    rintro ⟨_, n, rfl⟩ ⟨_, m, rfl⟩
    apply Subtype.ext
    change θ n * θ m = θ m * θ n
    rw [← map_mul, ← map_mul, mul_comm n m]
  let pw : A →* A :=
    { toFun := fun a => a ^ 5
      map_one' := one_pow _
      map_mul' := fun a b => (show Commute a b from hAc a b).mul_pow 5 }
  have hθ5 : ∀ n : Fin 4 → ℤ, θ (Multiplicative.ofAdd n) ^ 5 =
      θ (Multiplicative.ofAdd ((5 : ℤ) • n)) := by
    intro n
    rw [← map_pow]
    congr 1
  let emb : (Fin 4 → Fin 5) → A ⧸ pw.range := fun e =>
    ((⟨θ (Multiplicative.ofAdd fun i => ((e i : ℕ) : ℤ)), ⟨_, rfl⟩⟩ : A) : A ⧸ pw.range)
  have hemb : Function.Injective emb := by
    intro e e' hee
    simp only [emb, QuotientGroup.eq] at hee
    obtain ⟨⟨_, n, rfl⟩, hn⟩ := hee
    have hn' := congrArg Subtype.val hn
    simp only [pw, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_pow, Subgroup.coe_mul,
      Subgroup.coe_inv] at hn'
    obtain ⟨n, rfl⟩ := Multiplicative.ofAdd.surjective n
    rw [hθ5, ← map_inv, ← map_mul, ← ofAdd_neg, ← ofAdd_add] at hn'
    have h1 : θ (Multiplicative.ofAdd ((5 : ℤ) • n - (-(fun i => ((e i : ℕ) : ℤ)) +
        fun i => ((e' i : ℕ) : ℤ)))) = 1 := by
      rw [sub_eq_add_neg, ofAdd_add, map_mul, hn', ofAdd_neg, map_inv, mul_inv_cancel]
    rw [hθ] at h1
    obtain ⟨d0, d1, d2, d3⟩ := hind _ _ _ _ h1
    funext i
    apply Fin.ext
    have key : ∀ j : Fin 4, (5 : ℤ) ∣ (5 : ℤ) * n j - (-((e j : ℕ) : ℤ) + ((e' j : ℕ) : ℤ)) := by
      intro j
      fin_cases j
      · simpa using d0
      · simpa using d1
      · simpa using d2
      · simpa using d3
    have hi := key i
    have hi' : (5 : ℤ) ∣ ((e' i : ℕ) : ℤ) - ((e i : ℕ) : ℤ) := by
      have h5 : (5 : ℤ) ∣ (5 : ℤ) * n i := dvd_mul_right 5 _
      have := dvd_sub h5 hi
      simpa [sub_sub_cancel_left, sub_eq_add_neg, add_comm] using this
    have he := (e i).isLt
    have he' := (e' i).isLt
    omega
  have hquot : 625 ≤ Nat.card (A ⧸ pw.range) := by
    have h := Nat.card_le_card_of_injective emb hemb
    rw [Nat.card_fun, Nat.card_eq_fintype_card (α := Fin 5), Fintype.card_fin,
      Nat.card_eq_fintype_card (α := Fin 4), Fintype.card_fin] at h
    norm_num at h
    exact h
  have hker : Nat.card pw.ker = Nat.card (A ⧸ pw.range) := by
    have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup pw.ker
    have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup pw.range
    rw [Nat.card_congr (QuotientGroup.quotientKerEquivRange pw).toEquiv] at h1
    have hpos : 0 < Nat.card pw.range := Nat.card_pos
    rw [h1, mul_comm] at h2
    exact Nat.eq_of_mul_eq_mul_right hpos h2
  set Ω := pw.ker.map A.subtype with hΩ
  have hΩcard : Nat.card Ω = Nat.card pw.ker := by
    rw [hΩ, Subgroup.card_map_of_injective A.subtype_injective]
  have hΩexp : ∀ x ∈ Ω, x ^ 5 = 1 := by
    rintro _ ⟨a, ha, rfl⟩
    have h1 : a ^ 5 = 1 := ha
    simpa using congrArg Subtype.val h1
  have hΩel : CFSG.Assembly.IsElemAbelian 5 Ω := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, hΩexp⟩
    obtain ⟨a', -, ha'⟩ := a.2
    obtain ⟨b', -, hb'⟩ := b.2
    apply Subtype.ext
    change (a : X) * b = b * a
    rw [← ha', ← hb']
    exact congrArg Subtype.val (hAc a' b')
  have hΩp : IsPGroup 5 Ω := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, Subgroup.coe_one]
    exact hΩexp x x.2)⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp hΩp
  have hj4 : 4 ≤ j := by
    have h625 : 5 ^ 4 ≤ 5 ^ j := by
      rw [← hj, hΩcard, hker]
      norm_num
      exact hquot
    exact (Nat.pow_le_pow_iff_right (by norm_num)).mp h625
  exact hj4.trans (CFSG.SectionRank.le_pRank (by norm_num) le_top hΩel hj)

theorem commute_of_mul_mul_eq_one {X : Type*} [Group X] {P x S y : X} (h : P * x * S = 1)
    (hP : Commute P y) (hS : Commute S y) : Commute x y := by
  have hx : x = P⁻¹ * S⁻¹ := by
    calc x = P⁻¹ * (P * x * S) * S⁻¹ := by group
      _ = P⁻¹ * S⁻¹ := by rw [h, mul_one]
  rw [hx]
  exact hP.inv_left.mul_left hS.inv_left

theorem four_le_pRank_of_components {X : Type} [Group X] [Finite X] {J₁ J₂ J₃ J₄ : Subgroup X}
    (h1 : CFSG.IsComponent J₁) (h2 : CFSG.IsComponent J₂) (h3 : CFSG.IsComponent J₃)
    (h4 : CFSG.IsComponent J₄) (h12 : J₁ ≠ J₂) (h13 : J₁ ≠ J₃) (h14 : J₁ ≠ J₄) (h23 : J₂ ≠ J₃)
    (h24 : J₂ ≠ J₄) (h34 : J₃ ≠ J₄) {x₁ : ↥J₁} {x₂ : ↥J₂} {x₃ : ↥J₃} {x₄ : ↥J₄}
    (hx₁ : orderOf (x₁ : ↥J₁ ⧸ Subgroup.center ↥J₁) = 5)
    (hx₂ : orderOf (x₂ : ↥J₂ ⧸ Subgroup.center ↥J₂) = 5)
    (hx₃ : orderOf (x₃ : ↥J₃ ⧸ Subgroup.center ↥J₃) = 5)
    (hx₄ : orderOf (x₄ : ↥J₄ ⧸ Subgroup.center ↥J₄) = 5) :
    4 ≤ CFSG.Open.pRank 5 (⊤ : Subgroup X) := by
  have hcomm : ∀ {A B : Subgroup X}, CFSG.IsComponent A → CFSG.IsComponent B → A ≠ B →
      ∀ a ∈ A, ∀ b ∈ B, Commute a b := by
    intro A B hA hB hAB a ha b hb
    rcases CFSG.LocalCores.distinct_components_commute hA hB with h | h
    · exact absurd h hAB
    · have hle := Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      exact (Subgroup.mem_centralizer_iff.mp (hle ha) b hb).symm
  have hdiv : ∀ {J : Subgroup X} {x : ↥J}, orderOf (x : ↥J ⧸ Subgroup.center ↥J) = 5 →
      ∀ e : ℤ, (∀ y ∈ J, Commute ((x : X) ^ e) y) → (5 : ℤ) ∣ e := by
    intro J x hx e hc
    have hz := mk_eq_one_of_commute (J := J) (z := (x : X) ^ e) (zpow_mem x.2 e)
      (fun y hy => (hc y hy).eq)
    have hz' : ((x ^ e : ↥J) : ↥J ⧸ Subgroup.center ↥J) = 1 := by
      rw [← hz]
      congr 1
    rw [QuotientGroup.mk_zpow] at hz'
    have := orderOf_dvd_iff_zpow_eq_one.mpr hz'
    rwa [hx] at this
  refine four_le_pRank_of_commuting (hcomm h1 h2 h12 _ x₁.2 _ x₂.2)
    (hcomm h1 h3 h13 _ x₁.2 _ x₃.2) (hcomm h1 h4 h14 _ x₁.2 _ x₄.2)
    (hcomm h2 h3 h23 _ x₂.2 _ x₃.2) (hcomm h2 h4 h24 _ x₂.2 _ x₄.2)
    (hcomm h3 h4 h34 _ x₃.2 _ x₄.2) fun e₁ e₂ e₃ e₄ he => ⟨?_, ?_, ?_, ?_⟩
  · refine hdiv hx₁ e₁ fun y hy => commute_of_mul_mul_eq_one (P := 1)
      (S := (x₂ : X) ^ e₂ * (x₃ : X) ^ e₃ * (x₄ : X) ^ e₄)
      (by simpa only [one_mul, mul_assoc] using he)
      (Commute.one_left y) ?_
    exact (((hcomm h1 h2 h12 y hy _ (zpow_mem x₂.2 e₂)).symm.mul_left
      (hcomm h1 h3 h13 y hy _ (zpow_mem x₃.2 e₃)).symm).mul_left
      (hcomm h1 h4 h14 y hy _ (zpow_mem x₄.2 e₄)).symm)
  · refine hdiv hx₂ e₂ fun y hy => commute_of_mul_mul_eq_one (P := (x₁ : X) ^ e₁)
      (S := (x₃ : X) ^ e₃ * (x₄ : X) ^ e₄) (by simpa only [mul_assoc] using he) ?_ ?_
    · exact hcomm h1 h2 h12 _ (zpow_mem x₁.2 e₁) y hy
    · exact ((hcomm h2 h3 h23 y hy _ (zpow_mem x₃.2 e₃)).symm.mul_left
        (hcomm h2 h4 h24 y hy _ (zpow_mem x₄.2 e₄)).symm)
  · refine hdiv hx₃ e₃ fun y hy => commute_of_mul_mul_eq_one
      (P := (x₁ : X) ^ e₁ * (x₂ : X) ^ e₂) (S := (x₄ : X) ^ e₄) he ?_ ?_
    · exact (hcomm h1 h3 h13 _ (zpow_mem x₁.2 e₁) y hy).mul_left
        (hcomm h2 h3 h23 _ (zpow_mem x₂.2 e₂) y hy)
    · exact (hcomm h3 h4 h34 y hy _ (zpow_mem x₄.2 e₄)).symm
  · refine hdiv hx₄ e₄ fun y hy => commute_of_mul_mul_eq_one
      (P := (x₁ : X) ^ e₁ * (x₂ : X) ^ e₂ * (x₃ : X) ^ e₃) (S := 1) (by rw [mul_one]; exact he)
      ?_ (Commute.one_left y)
    exact ((hcomm h1 h4 h14 _ (zpow_mem x₁.2 e₁) y hy).mul_left
      (hcomm h2 h4 h24 _ (zpow_mem x₂.2 e₂) y hy)).mul_left
      (hcomm h3 h4 h34 _ (zpow_mem x₃.2 e₃) y hy)

theorem map_eq_of_perfect_three {X S : Type} [Group X] [Finite X] [Group S] [Finite S]
    (hS6 : ∀ (H : Type) [Group H] (f : S →* H), Nat.card f.range ∣ 6 → f.range = ⊥)
    (φ : S →* MulAut X) (hrank5 : CFSG.Open.pRank 5 (⊤ : Subgroup X) ≤ 3)
    (H5 : ∀ J' : Subgroup X, CFSG.IsComponent J' →
      ∃ x : ↥J', orderOf (x : ↥J' ⧸ Subgroup.center ↥J') = 5)
    {J : Subgroup X} (hJ : CFSG.IsComponent J) (s : S) : J.map (φ s).toMonoidHom = J := by
  classical
  set Ω : Set (Subgroup X) := Set.range fun t : S => J.map (φ t).toMonoidHom with hΩ
  have hcomp : ∀ t, CFSG.IsComponent (J.map (φ t).toMonoidHom) := fun t =>
    CFSG.LocalCores.isComponent_map_mulEquiv (φ t) hJ
  have hcomp' : ∀ (a b : S) (H : Subgroup X),
      (H.map (φ b).toMonoidHom).map (φ a).toMonoidHom = H.map (φ (a * b)).toMonoidHom := by
    intro a b H
    rw [Subgroup.map_map, map_mul]
    rfl
  have hone : ∀ H : Subgroup X, H.map (φ 1).toMonoidHom = H := by
    intro H
    rw [map_one]
    exact Subgroup.map_id H
  have hmem : ∀ (a : S) (H : Ω), (H : Subgroup X).map (φ a).toMonoidHom ∈ Ω := by
    rintro a ⟨_, ⟨t, rfl⟩⟩
    exact ⟨a * t, (hcomp' a t J).symm⟩
  let π : S →* Equiv.Perm Ω :=
    { toFun := fun a =>
        { toFun := fun H => ⟨(H : Subgroup X).map (φ a).toMonoidHom, hmem a H⟩
          invFun := fun H => ⟨(H : Subgroup X).map (φ a⁻¹).toMonoidHom, hmem a⁻¹ H⟩
          left_inv := fun H => Subtype.ext (by
            change ((H : Subgroup X).map (φ a).toMonoidHom).map (φ a⁻¹).toMonoidHom = H
            rw [hcomp', inv_mul_cancel, hone])
          right_inv := fun H => Subtype.ext (by
            change ((H : Subgroup X).map (φ a⁻¹).toMonoidHom).map (φ a).toMonoidHom = H
            rw [hcomp', mul_inv_cancel, hone]) }
      map_one' := Equiv.ext fun H => Subtype.ext (hone H)
      map_mul' := fun a b => Equiv.ext fun H => Subtype.ext (hcomp' a b H).symm }
  have hJΩ : J ∈ Ω := ⟨1, hone J⟩
  have : Finite Ω := Set.finite_range _ |>.to_subtype
  by_cases h4 : 4 ≤ Nat.card Ω
  · exfalso
    have : Fintype Ω := Fintype.ofFinite Ω
    obtain ⟨f⟩ : Nonempty (Fin 4 ↪ Ω) := Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
      exact h4)
    have hc : ∀ i : Fin 4, CFSG.IsComponent ((f i : Ω) : Subgroup X) := fun i => by
      obtain ⟨t, ht⟩ := (f i).2
      rw [← ht]
      exact hcomp t
    have hne : ∀ i j : Fin 4, i ≠ j → ((f i : Ω) : Subgroup X) ≠ (f j : Ω) := fun i j hij h =>
      hij (f.injective (Subtype.ext h))
    obtain ⟨x₁, hx₁⟩ := H5 _ (hc 0)
    obtain ⟨x₂, hx₂⟩ := H5 _ (hc 1)
    obtain ⟨x₃, hx₃⟩ := H5 _ (hc 2)
    obtain ⟨x₄, hx₄⟩ := H5 _ (hc 3)
    have := four_le_pRank_of_components (hc 0) (hc 1) (hc 2) (hc 3) (hne 0 1 (by decide))
      (hne 0 2 (by decide)) (hne 0 3 (by decide)) (hne 1 2 (by decide)) (hne 1 3 (by decide))
      (hne 2 3 (by decide)) hx₁ hx₂ hx₃ hx₄
    omega
  · have h6 : Nat.card (Equiv.Perm Ω) ∣ 6 := by
      rw [Nat.card_perm]
      have : Nat.card Ω ≤ 3 := by omega
      interval_cases (Nat.card Ω) <;> decide
    have hr := hS6 _ π ((Subgroup.card_subgroup_dvd_card _).trans h6)
    have hs : π s = 1 := by
      have : π s ∈ π.range := ⟨s, rfl⟩
      rwa [hr, Subgroup.mem_bot] at this
    have := congrArg Subtype.val (Equiv.ext_iff.mp hs ⟨J, hJΩ⟩)
    exact this

section FixComponent


theorem fix_component_of_rank_three {X S : Type} [Group X] [Finite X] [Group S] [Finite S]
    (hSp : Group.IsPerfect S)
    (hS3 : ∀ (H : Type) [Group H] (f : S →* H), ¬ 3 ∣ Nat.card f.range → f.range = ⊥)
    (hS6 : ∀ (H : Type) [Group H] (f : S →* H), Nat.card f.range ∣ 6 → f.range = ⊥)
    (φ : S →* MulAut X) (hK : CFSG.IsKGroup X) (h3 : ¬ 3 ∣ Nat.card X)
    (hrank5 : CFSG.Open.pRank 5 (⊤ : Subgroup X) ≤ 3) {J : Subgroup X} (hJ : CFSG.IsComponent J)
    (s : S) {x : X} (hx : x ∈ J) : φ s x = x := by
  have := hSp
  have hJinv : ∀ t, J.map (φ t).toMonoidHom = J := map_eq_of_perfect_three hS6 φ hrank5
    (fun J' hJ' => exists_five_of_component hK h3 hJ') hJ
  set ρ := restrictAct φ J hJinv with hρ
  refine fix_of_range_eq_bot φ J hJinv ?_ s hx
  obtain ⟨f, hf⟩ := suzukiModel_of_component hK h3 hJ
  have : Group.IsPerfect ↥J := hJ.1.1
  have hcyc := ((CFSG.LieType.Suzuki.Suzuki_model_and_perfect_cover_outer_cyclicity _ 2 f hf).2
    ↥J ⟨MulEquiv.refl _⟩).1
  have : Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J) :=
    Group.isSolvable_of_comm fun a b => by
      have := IsCyclic.isMulCommutative
        (α := CFSG.ComponentClassification.OuterAutomorphisms.Outer ↥J)
      exact mul_comm' a b
  have hinner : ρ.range ≤ (MulAut.conj : ↥J →* MulAut ↥J).range := by
    rintro _ ⟨t, rfl⟩
    obtain ⟨j, hj⟩ := CFSG.ComponentClassification.OuterAutomorphisms.perfect_action_inner ρ t
    exact ⟨j, hj.symm⟩
  refine hS3 _ ρ fun h3ρ => h3 ?_
  have h1 : Nat.card ρ.range ∣ Nat.card (MulAut.conj : ↥J →* MulAut ↥J).range :=
    Subgroup.card_dvd_of_le hinner
  have h2 : Nat.card (MulAut.conj : ↥J →* MulAut ↥J).range ∣ Nat.card ↥J := by
    rw [← Nat.card_congr (QuotientGroup.quotientKerEquivRange _).toEquiv]
    exact Subgroup.card_quotient_dvd_card _
  exact (h3ρ.trans h1).trans (h2.trans (Subgroup.card_subgroup_dvd_card J))

end FixComponent

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.SuzukiL2

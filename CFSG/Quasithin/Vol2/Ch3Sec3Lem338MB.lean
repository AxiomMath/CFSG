module

public import CFSG.Quasithin.Background.B4Models

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.H13.M338

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K] {n : ℕ}

@[expose] noncomputable def tv (i j : Fin n) (h : i ≠ j) (c : K) : ↥(StatedSL n K) :=
  ⟨Matrix.SpecialLinearGroup.toGL
      ⟨Matrix.transvection i j c, Matrix.det_transvection_of_ne i j h c⟩,
    Subgroup.subset_closure (Matrix.det_transvection_of_ne i j h c)⟩

theorem transvection_mulVec (i j : Fin n) (c : K) (v : Fin n → K) :
    (Matrix.transvection i j c).mulVec v = v + Pi.single i (c * v j) := by
  rw [Matrix.transvection, Matrix.add_mulVec, Matrix.one_mulVec, Matrix.single_mulVec]
  rfl

theorem natAct_tv (i j : Fin n) (h : i ≠ j) (c : K) (x : Multiplicative (Fin n → K)) :
    natAct (StatedSL n K) (tv i j h c) x =
      x * Multiplicative.ofAdd (Pi.single i (c * Multiplicative.toAdd x j)) := by
  show Multiplicative.ofAdd ((Matrix.transvection i j c).mulVec (Multiplicative.toAdd x)) = _
  rw [transvection_mulVec]
  rfl

theorem exists_ne (hn : 2 ≤ n) (j : Fin n) : ∃ i : Fin n, i ≠ j := by
  by_cases hj : (j : ℕ) = 0
  · exact ⟨⟨1, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩
  · exact ⟨⟨0, by omega⟩, fun h => by simp [Fin.ext_iff] at h; omega⟩

theorem nat_fix_aux (hn : 2 ≤ n) (m : Multiplicative (Fin n → K))
    (hm : ∀ γ : ↥(StatedSL n K), natAct (StatedSL n K) γ m * m⁻¹ ∈
      (⊥ : Subgroup (Multiplicative (Fin n → K)))) :
    m ∈ (⊥ : Subgroup (Multiplicative (Fin n → K))) := by
  rw [Subgroup.mem_bot]
  apply Multiplicative.toAdd.injective
  funext j
  obtain ⟨i, hij⟩ := exists_ne hn j
  have h1 := hm (tv i j hij 1)
  rw [natAct_tv, Subgroup.mem_bot, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul] at h1
  have h2 := congrFun (congrArg Multiplicative.toAdd h1) i
  simpa using h2

theorem nat_fix (hn : 2 ≤ n) :
    ∀ m ∈ (FFModel.nat (StatedSL n K)).sec,
      (∀ γ : (FFModel.nat (StatedSL n K)).Gam,
        (FFModel.nat (StatedSL n K)).act γ m * m⁻¹ ∈ (FFModel.nat (StatedSL n K)).ker) →
      m ∈ (FFModel.nat (StatedSL n K)).ker :=
  fun m _ hm => nat_fix_aux hn m hm

theorem nat_gen_aux (hn : 2 ≤ n) (x : Multiplicative (Fin n → K)) :
    x ∈ Subgroup.closure {x | ∃ γ : ↥(StatedSL n K),
      ∃ y ∈ (⊤ : Subgroup (Multiplicative (Fin n → K))), natAct (StatedSL n K) γ y * y⁻¹ = x} := by
  have hsingle : ∀ (i : Fin n) (c : K),
      Multiplicative.ofAdd (Pi.single i c) ∈ Subgroup.closure {x | ∃ γ : ↥(StatedSL n K),
        ∃ y ∈ (⊤ : Subgroup (Multiplicative (Fin n → K))),
          natAct (StatedSL n K) γ y * y⁻¹ = x} := by
    intro i c
    obtain ⟨j, hij⟩ := exists_ne hn i
    refine Subgroup.subset_closure ⟨tv i j hij.symm c,
      Multiplicative.ofAdd (Pi.single j 1), Subgroup.mem_top _, ?_⟩
    rw [natAct_tv, mul_comm, ← mul_assoc, inv_mul_cancel, one_mul]
    simp
  have hx : x = ∏ i, Multiplicative.ofAdd (Pi.single i (Multiplicative.toAdd x i)) := by
    apply Multiplicative.toAdd.injective
    rw [toAdd_prod]
    simp only [toAdd_ofAdd]
    exact (Finset.univ_sum_single _).symm
  rw [hx]
  exact Subgroup.prod_mem _ fun i _ => hsingle i _

theorem nat_gen (hn : 2 ≤ n) :
    (FFModel.nat (StatedSL n K)).sec ≤
      Subgroup.closure {x | ∃ γ : (FFModel.nat (StatedSL n K)).Gam,
        ∃ y ∈ (FFModel.nat (StatedSL n K)).sec,
          (FFModel.nat (StatedSL n K)).act γ y * y⁻¹ = x} ⊔ (FFModel.nat (StatedSL n K)).ker :=
  fun x _ => Subgroup.mem_sup_left (nat_gen_aux hn x)

local instance coreMemDec5 : DecidablePred (· ∈ G6.coreMod 5) := fun _ =>
  decidable_of_iff _ G6.mem_coreMod.symm

@[expose] def cyc (a b c : Fin 5) : Equiv.Perm (Fin 5) := Equiv.swap a b * Equiv.swap b c

theorem cyc_mem (a b c : Fin 5) (hab : a ≠ b) (hbc : b ≠ c) :
    cyc a b c ∈ alternatingGroup (Fin 5) := by
  rw [Equiv.Perm.mem_alternatingGroup, cyc, Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hab,
    Equiv.Perm.sign_swap hbc]
  rfl

theorem fix5_check : ∀ m : G6.PermMod 5, G6.permAct 5 (cyc 0 1 2) m = m →
    G6.permAct 5 (cyc 2 3 4) m = m → m ∈ G6.coreMod 5 → m = 1 := by
  decide +kernel

theorem allOnes_not_mem : G6.allOnes 5 ∉ G6.coreMod 5 := by decide +kernel

theorem allOnes_sq : G6.allOnes 5 * G6.allOnes 5 = 1 := by decide +kernel

theorem mem_zpowers_allOnes {x : G6.PermMod 5} (hx : x ∈ Subgroup.zpowers (G6.allOnes 5)) :
    x = 1 ∨ x = G6.allOnes 5 := by
  rw [Subgroup.zpowers_eq_closure] at hx
  induction hx using Subgroup.closure_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx
    exact Or.inr hx
  | one => exact Or.inl rfl
  | mul x y _ _ hx hy =>
    rcases hx with rfl | rfl <;> rcases hy with rfl | rfl
    · exact Or.inl (one_mul 1)
    · exact Or.inr (one_mul _)
    · exact Or.inr (mul_one _)
    · exact Or.inl allOnes_sq
  | inv x _ hx =>
    rcases hx with rfl | rfl
    · exact Or.inl inv_one
    · exact Or.inr (inv_eq_of_mul_eq_one_right allOnes_sq)

theorem ker5_eq_bot : (FFModel.altDn 5).ker = ⊥ := by
  rw [eq_bot_iff]
  rintro x ⟨hx, hxc⟩
  rcases mem_zpowers_allOnes hx with rfl | rfl
  · exact Subgroup.one_mem _
  · exact absurd hxc allOnes_not_mem

theorem alt5_fix :
    ∀ m ∈ (FFModel.altDn 5).sec,
      (∀ γ : (FFModel.altDn 5).Gam,
        (FFModel.altDn 5).act γ m * m⁻¹ ∈ (FFModel.altDn 5).ker) →
      m ∈ (FFModel.altDn 5).ker := by
  intro m hm hfix
  rw [ker5_eq_bot] at hfix ⊢
  have h1 := hfix ⟨cyc 0 1 2, cyc_mem 0 1 2 (by decide) (by decide)⟩
  have h2 := hfix ⟨cyc 2 3 4, cyc_mem 2 3 4 (by decide) (by decide)⟩
  rw [Subgroup.mem_bot, mul_inv_eq_one] at h1 h2
  rw [Subgroup.mem_bot]
  exact fix5_check m h1 h2 hm

@[expose] def pair5 (a b : Fin 5) : G6.PermMod 5 :=
  Multiplicative.ofAdd (Pi.single a 1 + Pi.single b 1)

theorem pair5_mem (a b : Fin 5) (hab : a ≠ b) : pair5 a b ∈ G6.coreMod 5 := by
  revert a b
  decide +kernel

theorem gen5_check : ∀ m : G6.PermMod 5, m ∈ G6.coreMod 5 → ∃ c₀ c₁ c₂ c₃ : Bool,
    m = (if c₀ then pair5 0 1 else 1) * (if c₁ then pair5 1 2 else 1) *
      (if c₂ then pair5 2 3 else 1) * (if c₃ then pair5 3 4 else 1) := by
  decide +kernel

theorem comm5_check : G6.permAct 5 (cyc 0 1 2) (pair5 0 3) * (pair5 0 3)⁻¹ = pair5 0 1 ∧
    G6.permAct 5 (cyc 1 2 3) (pair5 1 4) * (pair5 1 4)⁻¹ = pair5 1 2 ∧
    G6.permAct 5 (cyc 2 3 4) (pair5 2 0) * (pair5 2 0)⁻¹ = pair5 2 3 ∧
    G6.permAct 5 (cyc 3 4 0) (pair5 3 1) * (pair5 3 1)⁻¹ = pair5 3 4 := by
  decide +kernel

theorem alt5_gen :
    (FFModel.altDn 5).sec ≤
      Subgroup.closure {x | ∃ γ : (FFModel.altDn 5).Gam, ∃ y ∈ (FFModel.altDn 5).sec,
          (FFModel.altDn 5).act γ y * y⁻¹ = x} ⊔ (FFModel.altDn 5).ker := by
  intro m hm
  refine Subgroup.mem_sup_left ?_
  set S := {x | ∃ γ : (FFModel.altDn 5).Gam, ∃ y ∈ (FFModel.altDn 5).sec,
    (FFModel.altDn 5).act γ y * y⁻¹ = x}
  obtain ⟨h0, h1, h2, h3⟩ := comm5_check
  have g0 : pair5 0 1 ∈ Subgroup.closure S := Subgroup.subset_closure
    ⟨⟨cyc 0 1 2, cyc_mem 0 1 2 (by decide) (by decide)⟩, pair5 0 3,
      pair5_mem 0 3 (by decide), h0⟩
  have g1 : pair5 1 2 ∈ Subgroup.closure S := Subgroup.subset_closure
    ⟨⟨cyc 1 2 3, cyc_mem 1 2 3 (by decide) (by decide)⟩, pair5 1 4,
      pair5_mem 1 4 (by decide), h1⟩
  have g2 : pair5 2 3 ∈ Subgroup.closure S := Subgroup.subset_closure
    ⟨⟨cyc 2 3 4, cyc_mem 2 3 4 (by decide) (by decide)⟩, pair5 2 0,
      pair5_mem 2 0 (by decide), h2⟩
  have g3 : pair5 3 4 ∈ Subgroup.closure S := Subgroup.subset_closure
    ⟨⟨cyc 3 4 0, cyc_mem 3 4 0 (by decide) (by decide)⟩, pair5 3 1,
      pair5_mem 3 1 (by decide), h3⟩
  have hb : ∀ (c : Bool) {g : G6.PermMod 5}, g ∈ Subgroup.closure S →
      (if c then g else 1) ∈ Subgroup.closure S := by
    intro c g hg
    cases c
    · exact Subgroup.one_mem _
    · exact hg
  obtain ⟨c₀, c₁, c₂, c₃, rfl⟩ := gen5_check m hm
  exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mul_mem _ (hb c₀ g0) (hb c₁ g1))
    (hb c₂ g2)) (hb c₃ g3)

end CFSG.Quasithin.H13.M338

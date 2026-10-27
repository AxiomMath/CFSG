module

public import CFSG.RankThree.PartOne.KE.E6TwThreeShape

public noncomputable section

namespace CFSG.RankThree.PartOne.KE6

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.E6
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley CFSG.RankThree.Classical2
open CFSG.RankThree.PartOne.KETw3 (chainRoot13_orientation_aux chainRoot13_add chainRoot56_add
  map_zero_of_add map_neg_of_add)
open Matrix
open scoped Matrix MatrixGroups

section Lattice

variable {T : (Fin Tag.E6.rank → ℤ) → Fin Tag.E6.rank → ℤ}

theorem ncard_parabolicRoots_support56' :
    (parabolicRoots Tag.E6 support56).ncard = 6 :=
  ncard_parabolicRoots_eq mem_support56 (by decide +kernel)

theorem cross_sum_not_mem {α β : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E6 support13) (hβ : β ∈ parabolicRoots Tag.E6 support56) :
    α + β ∉ parabolicRoots Tag.E6 supportA2A2 := by
  intro h
  rw [parabolicRoots_supportA2A2] at h
  have hβ0 : β ≠ 0 := IsRoot.ne_zero hβ.1
  have hα0 : α ≠ 0 := IsRoot.ne_zero hα.1
  rcases h with h | h
  · apply hβ0
    funext i
    by_cases hi : i ∈ support56
    · have h1 : (α + β) i = 0 := h.2 i (fun hi' => by
        rcases (mem_support56 i).1 hi with rfl | rfl <;>
          rcases (mem_support13 _).1 hi' with h' | h' <;> exact absurd h' (by decide))
      have h2 : α i = 0 := hα.2 i (fun hi' => by
        rcases (mem_support56 i).1 hi with rfl | rfl <;>
          rcases (mem_support13 _).1 hi' with h' | h' <;> exact absurd h' (by decide))
      simpa [h2] using h1
    · exact hβ.2 i hi
  · apply hα0
    funext i
    by_cases hi : i ∈ support13
    · have h1 : (α + β) i = 0 := h.2 i (fun hi' => by
        rcases (mem_support13 i).1 hi with rfl | rfl <;>
          rcases (mem_support56 _).1 hi' with h' | h' <;> exact absurd h' (by decide))
      have h2 : β i = 0 := hβ.2 i (fun hi' => by
        rcases (mem_support13 i).1 hi with rfl | rfl <;>
          rcases (mem_support56 _).1 hi' with h' | h' <;> exact absurd h' (by decide))
      simpa [h2] using h1
    · exact hα.2 i hi

theorem eq_two_single {α : Fin Tag.E6.rank → ℤ} {a b : Fin Tag.E6.rank} (hab : a ≠ b)
    (h : ∀ i, i ≠ a → i ≠ b → α i = 0) :
    α = α a • Pi.single a 1 + α b • Pi.single b 1 := by
  funext i
  by_cases hia : i = a
  · subst hia
    simp [hab]
  · by_cases hib : i = b
    · subst hib
      simp [hab.symm]
    · simp [hia, hib, h i hia hib]

theorem parabolicRoots_support13_le :
    parabolicRoots Tag.E6 support13 ≤ parabolicRoots Tag.E6 supportA2A2 := fun α hα => by
  rw [parabolicRoots_supportA2A2]
  exact Or.inl hα

theorem parabolicRoots_support56_le :
    parabolicRoots Tag.E6 support56 ≤ parabolicRoots Tag.E6 supportA2A2 := fun α hα => by
  rw [parabolicRoots_supportA2A2]
  exact Or.inr hα

theorem side_cases (hadd : ∀ x y, T (x + y) = T x + T y)
    (hT : ∀ α ∈ parabolicRoots Tag.E6 supportA2A2, T α ∈ parabolicRoots Tag.E6 supportA2A2)
    {J : Set (Fin Tag.E6.rank)} {a b : Fin Tag.E6.rank} (hab : a ≠ b)
    (hJab : ∀ i, i ∈ J ↔ i = a ∨ i = b)
    (ha : (Pi.single a 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 J)
    (hb : (Pi.single b 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 J)
    (hsum : (Pi.single a 1 + Pi.single b 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 J)
    (hJS : parabolicRoots Tag.E6 J ≤ parabolicRoots Tag.E6 supportA2A2) :
    (∀ α ∈ parabolicRoots Tag.E6 J, T α ∈ parabolicRoots Tag.E6 support13) ∨
      (∀ α ∈ parabolicRoots Tag.E6 J, T α ∈ parabolicRoots Tag.E6 support56) := by
  classical
  set Tadd : (Fin Tag.E6.rank → ℤ) →+ (Fin Tag.E6.rank → ℤ) := AddMonoidHom.mk' T hadd
  have hTz : ∀ (n : ℤ) x, T (n • x) = n • T x := fun n x => map_zsmul Tadd n x
  have hu := hT _ (hJS ha)
  have hv := hT _ (hJS hb)
  have hsumT : T (Pi.single a 1) + T (Pi.single b 1) ∈ parabolicRoots Tag.E6 supportA2A2 := by
    rw [← hadd]
    exact hT _ (hJS hsum)
  rw [parabolicRoots_supportA2A2] at hu hv
  have key : ∀ (K : Set (Fin Tag.E6.rank)),
      (T (Pi.single a 1) ∈ parabolicRoots Tag.E6 K) → (T (Pi.single b 1) ∈ parabolicRoots Tag.E6 K) →
      ∀ α ∈ parabolicRoots Tag.E6 J, T α ∈ parabolicRoots Tag.E6 K := by
    intro K hu' hv' α hα
    have hαS := hT α (hJS hα)
    refine ⟨hαS.1, fun i hi => ?_⟩
    have hαe : α = α a • Pi.single a 1 + α b • Pi.single b 1 := eq_two_single hab (fun i hia hib =>
      hα.2 i (fun hiJ => by rcases (hJab i).1 hiJ with h | h; exacts [hia h, hib h]))
    have : T α = α a • T (Pi.single a 1) + α b • T (Pi.single b 1) := by
      conv_lhs => rw [hαe]
      rw [hadd, hTz, hTz]
    rw [this]
    simp [hu'.2 i hi, hv'.2 i hi]
  rcases hu with hu | hu <;> rcases hv with hv | hv
  · exact Or.inl (key _ hu hv)
  · exact absurd hsumT (cross_sum_not_mem hu hv)
  · exact absurd hsumT (by rw [add_comm]; exact cross_sum_not_mem hv hu)
  · exact Or.inr (key _ hu hv)

theorem single13_mem :
    (Pi.single (e6Index 0) 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 support13 ∧
      (Pi.single (e6Index 2) 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 support13 ∧
      (Pi.single (e6Index 0) 1 + Pi.single (e6Index 2) 1 : Fin Tag.E6.rank → ℤ) ∈
        parabolicRoots Tag.E6 support13 := by
  refine ⟨?_, ?_, ?_⟩
  · have := chainRoot13_mem_parabolicRoots (show (0 : Fin 3) ≠ 1 by decide)
    rwa [chainRoot13_simple.1] at this
  · have := chainRoot13_mem_parabolicRoots (show (1 : Fin 3) ≠ 2 by decide)
    rwa [chainRoot13_simple.2.1] at this
  · have := chainRoot13_mem_parabolicRoots (show (0 : Fin 3) ≠ 2 by decide)
    rwa [← chainRoot13_add 0 1 2, chainRoot13_simple.1, chainRoot13_simple.2.1] at this

theorem single56_mem :
    (Pi.single (e6Index 4) 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 support56 ∧
      (Pi.single (e6Index 5) 1 : Fin Tag.E6.rank → ℤ) ∈ parabolicRoots Tag.E6 support56 ∧
      (Pi.single (e6Index 4) 1 + Pi.single (e6Index 5) 1 : Fin Tag.E6.rank → ℤ) ∈
        parabolicRoots Tag.E6 support56 := by
  refine ⟨?_, ?_, ?_⟩
  · have := chainRoot56_mem_parabolicRoots (show (0 : Fin 3) ≠ 1 by decide)
    rwa [chainRoot56_simple.1] at this
  · have := chainRoot56_mem_parabolicRoots (show (1 : Fin 3) ≠ 2 by decide)
    rwa [chainRoot56_simple.2.1] at this
  · have := chainRoot56_mem_parabolicRoots (show (0 : Fin 3) ≠ 2 by decide)
    rwa [← chainRoot56_add 0 1 2, chainRoot56_simple.1, chainRoot56_simple.2.1] at this

theorem T_cases (hadd : ∀ x y, T (x + y) = T x + T y)
    (hinj : Function.Injective T)
    (hT : ∀ α ∈ parabolicRoots Tag.E6 supportA2A2, T α ∈ parabolicRoots Tag.E6 supportA2A2) :
    ((∀ α ∈ parabolicRoots Tag.E6 support13, T α ∈ parabolicRoots Tag.E6 support13) ∧
      ∀ α ∈ parabolicRoots Tag.E6 support56, T α ∈ parabolicRoots Tag.E6 support56) ∨
    ((∀ α ∈ parabolicRoots Tag.E6 support13, T α ∈ parabolicRoots Tag.E6 support56) ∧
      ∀ α ∈ parabolicRoots Tag.E6 support56, T α ∈ parabolicRoots Tag.E6 support13) := by
  classical
  obtain ⟨ha13, hb13, hs13⟩ := single13_mem
  obtain ⟨ha56, hb56, hs56⟩ := single56_mem
  have h13 := side_cases (T := T) hadd hT (J := support13) (a := e6Index 0) (b := e6Index 2)
    (by decide) mem_support13 ha13 hb13 hs13 parabolicRoots_support13_le
  have h56 := side_cases (T := T) hadd hT (J := support56) (a := e6Index 4) (b := e6Index 5)
    (by decide) mem_support56 ha56 hb56 hs56 parabolicRoots_support56_le
  have hS : ∀ α ∈ parabolicRoots Tag.E6 supportA2A2,
      α ∈ parabolicRoots Tag.E6 support13 ∨ α ∈ parabolicRoots Tag.E6 support56 := fun α hα => by
    rwa [parabolicRoots_supportA2A2] at hα
  rcases h13 with h13 | h13 <;> rcases h56 with h56 | h56
  · exfalso
    have hfin : (parabolicRoots Tag.E6 support13).Finite :=
      Set.finite_of_ncard_ne_zero (by rw [ncard_parabolicRoots_support13]; norm_num)
    have := Set.ncard_le_ncard_of_injOn T (s := parabolicRoots Tag.E6 supportA2A2)
      (t := parabolicRoots Tag.E6 support13) (fun α hα => by
        rcases hS α hα with h | h
        exacts [h13 α h, h56 α h]) hinj.injOn hfin
    rw [ncard_parabolicRoots_supportA2A2, ncard_parabolicRoots_support13] at this
    omega
  · exact Or.inl ⟨h13, h56⟩
  · exact Or.inr ⟨h13, h56⟩
  · exfalso
    have hfin : (parabolicRoots Tag.E6 support56).Finite :=
      Set.finite_of_ncard_ne_zero (by rw [ncard_parabolicRoots_support56']; norm_num)
    have := Set.ncard_le_ncard_of_injOn T (s := parabolicRoots Tag.E6 supportA2A2)
      (t := parabolicRoots Tag.E6 support56) (fun α hα => by
        rcases hS α hα with h | h
        exacts [h13 α h, h56 α h]) hinj.injOn hfin
    rw [ncard_parabolicRoots_supportA2A2, ncard_parabolicRoots_support56'] at this
    omega

theorem transition_pos_gen {ι : Fin 2 → Fin Tag.E6.rank}
    (hsrc : ∀ a b c : Fin 3, chainRoot ι a b + chainRoot ι b c = chainRoot ι a c)
    (hadd : ∀ x y, T (x + y) = T x + T y) (π : Equiv.Perm (Fin 3))
    (h01 : T (chainRoot ι 0 1) = chainRoot chain13 (π 0) (π 1))
    (h12 : T (chainRoot ι 1 2) = chainRoot chain13 (π 1) (π 2)) :
    ∀ i j : Fin 3, T (chainRoot ι i j) = chainRoot chain13 (π i) (π j) := by
  have h0 := map_zero_of_add hadd
  intro i j
  fin_cases i <;> fin_cases j
  · show T (chainRoot ι 0 0) = chainRoot chain13 (π 0) (π 0)
    rw [chainRoot_self, chainRoot_self, h0]
  · exact h01
  · show T (chainRoot ι 0 2) = chainRoot chain13 (π 0) (π 2)
    rw [← hsrc 0 1 2, hadd, h01, h12, chainRoot13_add]
  · show T (chainRoot ι 1 0) = chainRoot chain13 (π 1) (π 0)
    rw [chainRoot_swap ι 0 1, chainRoot_swap chain13 (π 0) (π 1), map_neg_of_add hadd, h01]
  · show T (chainRoot ι 1 1) = chainRoot chain13 (π 1) (π 1)
    rw [chainRoot_self, chainRoot_self, h0]
  · exact h12
  · show T (chainRoot ι 2 0) = chainRoot chain13 (π 2) (π 0)
    rw [chainRoot_swap ι 0 2, chainRoot_swap chain13 (π 0) (π 2), ← hsrc 0 1 2,
      map_neg_of_add hadd, hadd, h01, h12, chainRoot13_add]
  · show T (chainRoot ι 2 1) = chainRoot chain13 (π 2) (π 1)
    rw [chainRoot_swap ι 1 2, chainRoot_swap chain13 (π 1) (π 2), map_neg_of_add hadd, h12]
  · show T (chainRoot ι 2 2) = chainRoot chain13 (π 2) (π 2)
    rw [chainRoot_self, chainRoot_self, h0]

theorem transition_neg_gen {ι : Fin 2 → Fin Tag.E6.rank}
    (hsrc : ∀ a b c : Fin 3, chainRoot ι a b + chainRoot ι b c = chainRoot ι a c)
    (hadd : ∀ x y, T (x + y) = T x + T y) (π : Equiv.Perm (Fin 3))
    (h01 : T (chainRoot ι 0 1) = chainRoot chain13 (π 1) (π 0))
    (h12 : T (chainRoot ι 1 2) = chainRoot chain13 (π 2) (π 1)) :
    ∀ i j : Fin 3, T (chainRoot ι i j) = chainRoot chain13 (π j) (π i) := by
  have h0 := map_zero_of_add hadd
  intro i j
  fin_cases i <;> fin_cases j
  · show T (chainRoot ι 0 0) = chainRoot chain13 (π 0) (π 0)
    rw [chainRoot_self, chainRoot_self, h0]
  · exact h01
  · show T (chainRoot ι 0 2) = chainRoot chain13 (π 2) (π 0)
    rw [← hsrc 0 1 2, hadd, h01, h12, add_comm, chainRoot13_add]
  · show T (chainRoot ι 1 0) = chainRoot chain13 (π 0) (π 1)
    rw [chainRoot_swap ι 0 1, map_neg_of_add hadd, h01, chainRoot_swap chain13 (π 1) (π 0)]
  · show T (chainRoot ι 1 1) = chainRoot chain13 (π 1) (π 1)
    rw [chainRoot_self, chainRoot_self, h0]
  · exact h12
  · show T (chainRoot ι 2 0) = chainRoot chain13 (π 0) (π 2)
    rw [chainRoot_swap ι 0 2, ← hsrc 0 1 2, map_neg_of_add hadd, hadd, h01, h12,
      add_comm, chainRoot13_add, chainRoot_swap chain13 (π 2) (π 0)]
  · show T (chainRoot ι 2 1) = chainRoot chain13 (π 1) (π 2)
    rw [chainRoot_swap ι 1 2, map_neg_of_add hadd, h12, chainRoot_swap chain13 (π 2) (π 1)]
  · show T (chainRoot ι 2 2) = chainRoot chain13 (π 2) (π 2)
    rw [chainRoot_self, chainRoot_self, h0]

theorem transition_cases_gen {ι : Fin 2 → Fin Tag.E6.rank}
    (hsrc : ∀ a b c : Fin 3, chainRoot ι a b + chainRoot ι b c = chainRoot ι a c)
    (hadd : ∀ x y, T (x + y) = T x + T y)
    (hroots : ∀ i j : Fin 3, i ≠ j → ∃ a b : Fin 3, a ≠ b ∧
      T (chainRoot ι i j) = chainRoot chain13 a b) :
    IsPositiveTransition T ι chain13 ∨ IsNegativeTransition T ι chain13 := by
  obtain ⟨a, b, hab, h01⟩ := hroots 0 1 (by decide)
  obtain ⟨c, d, hcd, h12⟩ := hroots 1 2 (by decide)
  obtain ⟨e, f, hef, h02⟩ := hroots 0 2 (by decide)
  have hs : chainRoot chain13 a b + chainRoot chain13 c d = chainRoot chain13 e f := by
    rw [← h01, ← h12, ← h02, ← hadd, hsrc]
  rcases chainRoot13_orientation_aux a b c d e f hab hcd hef hs with ⟨hbc, had⟩ | ⟨had, hbc⟩
  · subst hbc
    have hinj : Function.Injective ![a, b, d] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all
    let π : Equiv.Perm (Fin 3) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
    left
    exact ⟨π, transition_pos_gen hsrc hadd π h01 h12⟩
  · subst had
    have hinj : Function.Injective ![b, a, c] := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> simp_all [eq_comm]
    let π : Equiv.Perm (Fin 3) := Equiv.ofBijective _ (Finite.injective_iff_bijective.1 hinj)
    right
    exact ⟨π, transition_neg_gen hsrc hadd π h01 h12⟩

theorem support13_cases_aux' : ∀ m : Fin 72,
    (∀ i, ¬(i = e6Index 0 ∨ i = e6Index 2) → e6RootVec m i = 0) →
    ∃ a b : Fin 3, a ≠ b ∧ e6RootVec m = chainRoot chain13 a b := by
  decide +kernel

theorem exists_chainRoot13_of_mem' {α : Fin Tag.E6.rank → ℤ}
    (hα : α ∈ parabolicRoots Tag.E6 support13) :
    ∃ a b : Fin 3, a ≠ b ∧ α = chainRoot chain13 a b := by
  obtain ⟨m, rfl⟩ := isRoot_iff_exists_e6RootVec.1 hα.1
  exact support13_cases_aux' m (fun i hi => hα.2 i ((mem_support13 i).not.2 hi))

end Lattice

section Linear

variable {Ω : Type} [Field Ω]

theorem exists_sl3_linear_11 (θ' : ModGL Tag.E6 Ω →* ModGL Tag.E6 Ω)
    (τ₁ τ₂ : Fin 3 → Fin 3 → Fin 3) (hne : ∀ i j : Fin 3, i ≠ j → τ₁ i j ≠ τ₂ i j)
    (hθ : ∀ i j : Fin 3, i ≠ j → ∃ μ : Ωˣ, ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) =
        pinnedX Tag.E6 Ω (chainRoot chain13 (τ₁ i j) (τ₂ i j)) ((μ : Ω) * c)) :
    ∃ hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support13, θ' g ∈ subsystemGroup Tag.E6 Ω support13,
      ∃ b : Fin 3 → Fin 3 → Ωˣ, ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
        ((a2Equiv₁ Ω ⟨θ' ((a2Equiv₁ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t)),
          hQ _ ((a2Equiv₁ Ω).symm _).2⟩ : SL(3, Ω)) : Matrix (Fin 3) (Fin 3) Ω) =
          1 + single (τ₁ i j) (τ₂ i j) ((b i j : Ω) * t) := by
  classical
  obtain ⟨h01, h12, h10, h21⟩ := chainRoot13_simple
  have hmemθ : ∀ i j : Fin 3, i ≠ j → ∀ c : Ω,
      θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) c) ∈ subsystemGroup Tag.E6 Ω support13 :=
    fun i j hij c => by
      obtain ⟨μ, h⟩ := hθ i j hij
      rw [h]
      exact pinnedX_chainRoot13_mem (hne i j hij) _
  have hQ : ∀ g ∈ subsystemGroup Tag.E6 Ω support13,
      θ' g ∈ subsystemGroup Tag.E6 Ω support13 := by
    intro g hg
    induction hg using Subgroup.closure_induction with
    | mem x hx =>
      obtain ⟨i, hi, c, rfl | rfl⟩ := hx
      · rcases (mem_support13 i).1 hi with rfl | rfl
        · rw [← pinnedX_single, ← h01]
          exact hmemθ 0 1 (by decide) c
        · rw [← pinnedX_single, ← h12]
          exact hmemθ 1 2 (by decide) c
      · rcases (mem_support13 i).1 hi with rfl | rfl
        · rw [← pinnedX_neg_single, ← h10]
          exact hmemθ 1 0 (by decide) c
        · rw [← pinnedX_neg_single, ← h21]
          exact hmemθ 2 1 (by decide) c
    | one =>
      rw [map_one]
      exact one_mem _
    | mul x y _ _ hx hy =>
      rw [map_mul]
      exact mul_mem hx hy
    | inv x _ hx =>
      rw [map_inv]
      exact inv_mem hx
  choose s hs hρ using fun (i j : Fin 3) (hij : i ≠ j) =>
    a2Mat₁_pinnedX_chainRoot13 (Ω := Ω) hij
  choose μ hμ using hθ
  have hsymm : ∀ (i j : Fin 3) (hij : i ≠ j) (t : Ω),
      (a2Equiv₁ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t) =
        ⟨pinnedX Tag.E6 Ω (chainRoot chain13 i j) ((s i j hij : Ω) * t),
          pinnedX_chainRoot13_mem hij _⟩ := by
    intro i j hij t
    rw [MulEquiv.symm_apply_eq]
    refine Subtype.ext ?_
    rw [a2Equiv₁_apply, coe_a2Rep₁, hρ i j hij, ← mul_assoc, CFSG.RankThree.Classical2.sign_mul_self (hs i j hij), one_mul]
    rfl
  refine ⟨hQ, fun i j => if hij : i ≠ j then
    Units.mkOfMulEqOne ((s (τ₁ i j) (τ₂ i j) (hne i j hij) : ℤ) : Ω)
      ((s (τ₁ i j) (τ₂ i j) (hne i j hij) : ℤ) : Ω)
      (CFSG.RankThree.Classical2.sign_mul_self (hs (τ₁ i j) (τ₂ i j) (hne i j hij))) * μ i j hij *
      Units.mkOfMulEqOne ((s i j hij : ℤ) : Ω) ((s i j hij : ℤ) : Ω)
        (CFSG.RankThree.Classical2.sign_mul_self (hs i j hij)) else 1, fun i j hij t => ?_⟩
  simp only [ne_eq, hij, not_false_eq_true, ↓reduceDIte, Units.val_mul, Units.val_mkOfMulEqOne]
  rw [a2Equiv₁_apply, coe_a2Rep₁]
  change a2Mat₁ (θ' ((a2Equiv₁ Ω).symm (Matrix.SpecialLinearGroup.transvection hij t))) = _
  rw [hsymm i j hij t]
  change a2Mat₁ (θ' (pinnedX Tag.E6 Ω (chainRoot chain13 i j) ((s i j hij : Ω) * t))) = _
  rw [hμ i j hij, hρ (τ₁ i j) (τ₂ i j) (hne i j hij)]
  congr 2
  ring

end Linear

end CFSG.RankThree.PartOne.KE6

module

public import CFSG.LocalAnalysis.StandardType.GGTypeAReflOverDefs
public import Mathlib.Algebra.Field.ZMod
public import Mathlib.GroupTheory.Perm.ClosureSwap
public import Mathlib.GroupTheory.Perm.DomMulAct

public section

namespace CFSG.StandardType.TypeAReflOver

variable {p n : ℕ}

@[expose] def heartVec (p n : ℕ) (v : Fin (n + 1) → ZMod p) (ω : Fin (n + 3)) : ZMod p :=
  if h : (ω : ℕ) < n + 1 then v ⟨ω, h⟩
  else if (ω : ℕ) = n + 1 then 0
  else -∑ i, v i

@[simp]
theorem heartVec_castSucc_castSucc (v : Fin (n + 1) → ZMod p) (a : Fin (n + 1)) :
    heartVec p n v (a.castSucc.castSucc) = v a := by
  simp only [heartVec, Fin.val_castSucc]
  rw [dif_pos a.isLt]

@[simp]
theorem heartVec_n_one (v : Fin (n + 1) → ZMod p) :
    heartVec p n v ((Fin.last (n + 1)).castSucc) = 0 := by
  simp only [heartVec, Fin.val_castSucc, Fin.val_last]
  rw [dif_neg (by omega)]
  simp

@[simp]
theorem heartVec_last (v : Fin (n + 1) → ZMod p) :
    heartVec p n v (Fin.last (n + 2)) = -∑ i, v i := by
  simp only [heartVec, Fin.val_last]
  rw [dif_neg (by omega), if_neg (by omega)]

private theorem fin_n3_cases (ω : Fin (n + 3)) :
    (∃ a : Fin n, ω = a.castSucc.castSucc.castSucc) ∨
    ω = (Fin.last n).castSucc.castSucc ∨
    ω = (Fin.last (n + 1)).castSucc ∨
    ω = Fin.last (n + 2) := by
  have hω := ω.isLt
  by_cases h1 : (ω : ℕ) < n
  · exact Or.inl ⟨⟨ω, h1⟩, by ext; simp⟩
  · by_cases h2 : (ω : ℕ) = n
    · exact Or.inr (Or.inl (by ext; simp [h2]))
    · by_cases h3 : (ω : ℕ) = n + 1
      · exact Or.inr (Or.inr (Or.inl (by ext; simp [h3])))
      · exact Or.inr (Or.inr (Or.inr (by ext; simp; omega)))

private theorem fin_n3_cases' (ω : Fin (n + 3)) :
    (∃ j : Fin (n + 1), ω = j.castSucc.castSucc) ∨
    ω = (Fin.last (n + 1)).castSucc ∨
    ω = Fin.last (n + 2) := by
  have hω := ω.isLt
  by_cases h1 : (ω : ℕ) < n + 1
  · exact Or.inl ⟨⟨ω, h1⟩, by ext; simp⟩
  · by_cases h2 : (ω : ℕ) = n + 1
    · exact Or.inr (Or.inl (by ext; simp [h2]))
    · exact Or.inr (Or.inr (by ext; simp; omega))

private theorem heartVec_coordPerm_cast (a b j : Fin (n + 1))
    (v : Fin (n + 1) → ZMod p) :
    heartVec p n (coordPerm p n (Equiv.swap a b) v) (j.castSucc.castSucc) =
      heartVec p n v ((Equiv.swap a.castSucc.castSucc b.castSucc.castSucc).symm
        (j.castSucc.castSucc)) := by
  have hs : (Equiv.swap a.castSucc.castSucc b.castSucc.castSucc).symm
      (j.castSucc.castSucc) = ((Equiv.swap a b).symm j).castSucc.castSucc := by
    rw [Equiv.symm_swap, Equiv.symm_swap]
    by_cases hja : j = a
    · rw [hja]; simp
    · by_cases hjb : j = b
      · rw [hjb]; simp
      · have h1 : j.castSucc.castSucc ≠ a.castSucc.castSucc := by
          intro h
          exact hja (by simpa using h)
        have h2 : j.castSucc.castSucc ≠ b.castSucc.castSucc := by
          intro h
          exact hjb (by simpa using h)
        rw [Equiv.swap_apply_of_ne_of_ne h1 h2, Equiv.swap_apply_of_ne_of_ne hja hjb]
  rw [hs, heartVec_castSucc_castSucc, heartVec_castSucc_castSucc, coordPerm_apply]

theorem heartVec_coordPerm (a b : Fin (n + 1))
    (v : Fin (n + 1) → ZMod p) (ω : Fin (n + 3)) :
    heartVec p n (coordPerm p n (Equiv.swap a b) v) ω =
      heartVec p n v ((Equiv.swap a.castSucc.castSucc b.castSucc.castSucc).symm ω) := by
  rcases fin_n3_cases' (n := n) ω with ⟨j, rfl⟩ | rfl | rfl
  · exact heartVec_coordPerm_cast a b j v
  · have hs : (Equiv.swap a.castSucc.castSucc b.castSucc.castSucc).symm
        ((Fin.last (n + 1)).castSucc) = (Fin.last (n + 1)).castSucc := by
      rw [Equiv.symm_swap]
      exact Equiv.swap_apply_of_ne_of_ne
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
    rw [hs, heartVec_n_one, heartVec_n_one]
  · have hs : (Equiv.swap a.castSucc.castSucc b.castSucc.castSucc).symm
        (Fin.last (n + 2)) = Fin.last (n + 2) := by
      rw [Equiv.symm_swap]
      exact Equiv.swap_apply_of_ne_of_ne
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
    have hsum : ∑ i, coordPerm p n (Equiv.swap a b) v i = ∑ i, v i := by
      simpa [coordPerm_apply] using Equiv.sum_comp (Equiv.swap a b).symm v
    rw [hs, heartVec_last, heartVec_last, hsum]

theorem heartVec_kRefl (hp : p ∣ n + 3) (v : Fin (n + 1) → ZMod p)
    (ω : Fin (n + 3)) :
    heartVec p n (kRefl p n v) ω =
      heartVec p n v ((Equiv.swap ((Fin.last n).castSucc.castSucc)
        ((Fin.last (n + 1)).castSucc)).symm ω) + (- v (Fin.last n)) := by
  have h3 : ((n + 3 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (n + 3) p).mpr hp
  have hn2 : ((n + 2 : ℕ) : ZMod p) = -1 := by
    have h : ((n + 2 : ℕ) : ZMod p) + 1 = 0 := by
      rw [← h3]
      push_cast
      ring
    linear_combination h
  have hroot : ∑ i : Fin (n + 1), kRoot p n i = ((n + 2 : ℕ) : ZMod p) := by
    simp only [kRoot, Pi.add_apply, Pi.one_apply, Finset.sum_add_distrib]
    rw [Fintype.sum_pi_single']
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, mul_one]
    push_cast
    ring
  have hsum : ∑ i, kRefl p n v i =
      ∑ i, v i - ((n + 2 : ℕ) : ZMod p) * v (Fin.last n) := by
    rw [kRefl_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hroot]
    ring
  rcases fin_n3_cases (n := n) ω with ⟨a, rfl⟩ | rfl | rfl | rfl
  · have ha : (a.castSucc : Fin (n + 1)) ≠ Fin.last n := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have hs : (Equiv.swap ((Fin.last n).castSucc.castSucc)
        ((Fin.last (n + 1)).castSucc)).symm
        (a.castSucc.castSucc.castSucc) = a.castSucc.castSucc.castSucc := by
      rw [Equiv.symm_swap]
      exact Equiv.swap_apply_of_ne_of_ne
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
    rw [hs, heartVec_castSucc_castSucc, heartVec_castSucc_castSucc, kRefl_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, kRoot, Pi.add_apply,
      Pi.single_eq_of_ne ha, Pi.one_apply, smul_eq_mul, mul_one]
    ring
  · have hs : (Equiv.swap ((Fin.last n).castSucc.castSucc)
        ((Fin.last (n + 1)).castSucc)).symm
        ((Fin.last n).castSucc.castSucc) = (Fin.last (n + 1)).castSucc := by
      rw [Equiv.symm_swap, Equiv.swap_apply_left]
    rw [hs, heartVec_n_one, heartVec_castSucc_castSucc, kRefl_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, kRoot, Pi.add_apply,
      Pi.single_eq_same, Pi.one_apply, smul_eq_mul]
    ring
  · have hs : (Equiv.swap ((Fin.last n).castSucc.castSucc)
        ((Fin.last (n + 1)).castSucc)).symm
        ((Fin.last (n + 1)).castSucc) = (Fin.last n).castSucc.castSucc := by
      rw [Equiv.symm_swap, Equiv.swap_apply_right]
    rw [hs, heartVec_n_one, heartVec_castSucc_castSucc]
    ring
  · have hs : (Equiv.swap ((Fin.last n).castSucc.castSucc)
        ((Fin.last (n + 1)).castSucc)).symm
        (Fin.last (n + 2)) = Fin.last (n + 2) := by
      rw [Equiv.symm_swap]
      exact Equiv.swap_apply_of_ne_of_ne
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
    rw [hs, heartVec_last, heartVec_last, hsum, hn2]
    ring

theorem heartVec_kThreeRefl (v : Fin (n + 1) → ZMod p) (ω : Fin (n + 3)) :
    heartVec p n (kThreeRefl p n v) ω =
      heartVec p n v ((Equiv.swap ((Fin.last n).castSucc.castSucc)
        (Fin.last (n + 2))).symm ω) := by
  have hroot : ∑ i : Fin (n + 1), kThreeRoot p n i = 1 := by
    simp [kThreeRoot]
  have hsum : ∑ i, kThreeRefl p n v i = - v (Fin.last n) := by
    rw [kThreeRefl_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_sub_distrib]
    rw [← Finset.mul_sum, hroot, mul_one, Fin.sum_univ_castSucc]
    ring
  rcases fin_n3_cases (n := n) ω with ⟨a, rfl⟩ | rfl | rfl | rfl
  · have ha : (a.castSucc : Fin (n + 1)) ≠ Fin.last n := by
      intro h
      have := congrArg Fin.val h
      simp at this
      omega
    have hs : (Equiv.swap ((Fin.last n).castSucc.castSucc)
        (Fin.last (n + 2))).symm
        (a.castSucc.castSucc.castSucc) = a.castSucc.castSucc.castSucc := by
      rw [Equiv.symm_swap]
      exact Equiv.swap_apply_of_ne_of_ne
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
    rw [hs, heartVec_castSucc_castSucc, heartVec_castSucc_castSucc, kThreeRefl_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, kThreeRoot, Pi.single_eq_of_ne ha,
      smul_eq_mul, mul_zero, sub_zero]
  · have hs : (Equiv.swap ((Fin.last n).castSucc.castSucc)
        (Fin.last (n + 2))).symm ((Fin.last n).castSucc.castSucc) = Fin.last (n + 2) := by
      rw [Equiv.symm_swap, Equiv.swap_apply_left]
    rw [hs, heartVec_last, heartVec_castSucc_castSucc, kThreeRefl_apply]
    simp only [Pi.sub_apply, Pi.smul_apply, kThreeRoot, Pi.single_eq_same,
      smul_eq_mul, mul_one]
    rw [Fin.sum_univ_castSucc]
    ring
  · have hs : (Equiv.swap ((Fin.last n).castSucc.castSucc)
        (Fin.last (n + 2))).symm ((Fin.last (n + 1)).castSucc) =
        (Fin.last (n + 1)).castSucc := by
      rw [Equiv.symm_swap]
      exact Equiv.swap_apply_of_ne_of_ne
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
        (by
          intro h
          have hval := congrArg Fin.val h
          simp only [Fin.val_last, Fin.val_castSucc] at hval
          omega)
    rw [hs, heartVec_n_one, heartVec_n_one]
  · have hs : (Equiv.swap ((Fin.last n).castSucc.castSucc)
        (Fin.last (n + 2))).symm (Fin.last (n + 2)) = (Fin.last n).castSucc.castSucc := by
      rw [Equiv.symm_swap, Equiv.swap_apply_right]
    rw [hs, heartVec_last, heartVec_castSucc_castSucc, hsum]
    ring

theorem heartVec_transport (hp : p ∣ n + 3)
    (T : Equiv.Perm (Fin (n + 3)) →*
      ((Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p)))
    (hT₁ : ∀ a b : Fin (n + 1),
      T (Equiv.swap a.castSucc.castSucc b.castSucc.castSucc) = coordPerm p n (Equiv.swap a b))
    (hT₂ : T (Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last (n + 1)).castSucc) =
      kRefl p n)
    (hT₃ : T (Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last (n + 2))) = kThreeRefl p n)
    (σ : Equiv.Perm (Fin (n + 3))) (v : Fin (n + 1) → ZMod p) :
    ∃ c : ZMod p, ∀ ω, heartVec p n (T σ v) ω = heartVec p n v (σ.symm ω) + c := by
  let H : Subgroup (Equiv.Perm (Fin (n + 3))) :=
    { carrier := {τ | ∀ v : Fin (n + 1) → ZMod p, ∃ c : ZMod p,
        ∀ ω, heartVec p n (T τ v) ω = heartVec p n v (τ.symm ω) + c}
      one_mem' := by
        intro v
        refine ⟨0, fun ω => ?_⟩
        rw [map_one]
        change heartVec p n v ω = heartVec p n v ω + 0
        rw [add_zero]
      mul_mem' := by
        intro τ ρ hτ hρ v
        obtain ⟨cρ, hcρ⟩ := hρ v
        obtain ⟨cτ, hcτ⟩ := hτ (T ρ v)
        refine ⟨cρ + cτ, fun ω => ?_⟩
        rw [map_mul, LinearEquiv.mul_apply, hcτ, hcρ]
        have hs : (τ * ρ).symm ω = ρ.symm (τ.symm ω) := by
          apply (τ * ρ).injective
          simp [Equiv.Perm.mul_apply]
        rw [hs]
        ring
      inv_mem' := by
        intro τ hτ v
        obtain ⟨d, hd⟩ := hτ (T (τ⁻¹) v)
        have hTinv : T τ (T (τ⁻¹) v) = v := by
          rw [← LinearEquiv.mul_apply, ← map_mul, mul_inv_cancel, map_one]
          simp
        refine ⟨-d, fun ω => ?_⟩
        have h := hd (τ ω)
        rw [hTinv, Equiv.symm_apply_apply] at h
        change heartVec p n (T (τ⁻¹) v) ω = heartVec p n v (τ ω) + -d
        linear_combination -h }
  let npt : Fin (n + 3) := (Fin.last n).castSucc.castSucc
  let n1 : Fin (n + 3) := (Fin.last (n + 1)).castSucc
  let n2 : Fin (n + 3) := Fin.last (n + 2)
  let star : Set (Equiv.Perm (Fin (n + 3))) :=
    {τ | ∃ x : Fin (n + 3), x ≠ npt ∧ τ = Equiv.swap npt x}
  have hstar_mem : ∀ τ ∈ star, τ ∈ H := by
    rintro τ ⟨x, hx, rfl⟩ v
    rcases fin_n3_cases (n := n) x with ⟨a, rfl⟩ | rfl | rfl | rfl
    · refine ⟨0, fun ω => ?_⟩
      rw [hT₁ (Fin.last n) a.castSucc]
      simpa using heartVec_coordPerm (p := p) (n := n) (Fin.last n) a.castSucc v ω
    · exact absurd rfl hx
    · refine ⟨-v (Fin.last n), fun ω => ?_⟩
      rw [hT₂]
      exact heartVec_kRefl hp v ω
    · refine ⟨0, fun ω => ?_⟩
      rw [hT₃]
      simpa using heartVec_kThreeRefl (p := p) (n := n) v ω
  have hgen : Subgroup.closure star = ⊤ := by
    have hswap : ∀ τ ∈ star, τ.IsSwap := by
      rintro τ ⟨x, hx, rfl⟩
      exact Equiv.Perm.swap_isSwap_iff.mpr (Ne.symm hx)
    have hpre : MulAction.IsPretransitive (Subgroup.closure star) (Fin (n + 3)) := by
      refine ⟨fun x y => ?_⟩
      by_cases hx : x = npt
      · subst hx
        by_cases hy : y = npt
        · subst hy
          exact ⟨1, by simp⟩
        · exact ⟨⟨Equiv.swap npt y, Subgroup.subset_closure ⟨y, hy, rfl⟩⟩,
            by simp [Equiv.swap_apply_left]⟩
      · by_cases hy : y = npt
        · subst hy
          exact ⟨⟨Equiv.swap npt x, Subgroup.subset_closure ⟨x, hx, rfl⟩⟩,
            by simp [Equiv.swap_apply_left]⟩
        · refine ⟨⟨Equiv.swap npt y * Equiv.swap npt x,
            Subgroup.mul_mem _ (Subgroup.subset_closure ⟨y, hy, rfl⟩)
              (Subgroup.subset_closure ⟨x, hx, rfl⟩)⟩, ?_⟩
          simp [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    haveI : MulAction.IsPretransitive (Subgroup.closure star) (Fin (n + 3)) := hpre
    exact closure_of_isSwap_of_isPretransitive (S := star) hswap
  have hclosure_le : Subgroup.closure star ≤ H := (Subgroup.closure_le H).mpr hstar_mem
  have hHtop : H = ⊤ := by
    apply le_antisymm le_top
    rw [← hgen]
    exact hclosure_le
  have hσH : σ ∈ H := by
    rw [hHtop]
    exact Subgroup.mem_top σ
  exact hσH v

theorem eq_zero_of_shift_of_card_fiber {Ω : Type*} [Fintype Ω] [DecidableEq Ω] {p : ℕ}
    [Fact p.Prime] {u : Ω → ZMod p} {σ : Equiv.Perm Ω} {c : ZMod p}
    (hu : ∀ ω, u ω = u (σ.symm ω) + c) {t : ZMod p} {k : ℕ}
    (hk : k ≤ (Finset.univ.filter fun ω => u ω = t).card) (hlt : Fintype.card Ω < p * k) :
    c = 0 := by
  by_contra hc
  have hshift : ∀ (m : ℕ) (ω : Ω),
      u ((σ.symm ^ m) ω) = u ω - (m : ZMod p) * c := by
    intro m
    induction m with
    | zero => intro ω; simp
    | succ m ih =>
        intro ω
        rw [pow_succ', Equiv.Perm.mul_apply]
        have h := hu ((σ.symm ^ m) ω)
        rw [ih ω] at h
        push_cast
        linear_combination -h
  let f : {ω : Ω // u ω = t} × ZMod p → Ω := fun x => (σ.symm ^ x.2.val) x.1
  have hf : Function.Injective f := by
    rintro ⟨⟨ω, hω⟩, j⟩ ⟨⟨ω', hω'⟩, j'⟩ hxy
    have h1 : u ((σ.symm ^ j.val) ω) = u ((σ.symm ^ j'.val) ω') := by
      simpa [f] using congrArg u hxy
    rw [hshift j.val ω, hshift j'.val ω', hω, hω'] at h1
    have hjc : (j.val : ZMod p) * c = (j'.val : ZMod p) * c := sub_right_inj.mp h1
    have hjeq : (j.val : ZMod p) = (j'.val : ZMod p) := by
      have hsub : ((j.val : ZMod p) - j'.val) * c = 0 := by
        rw [sub_mul, hjc, sub_self]
      rcases mul_eq_zero.mp hsub with h0 | hc0
      · exact sub_eq_zero.mp h0
      · exact absurd hc0 hc
    have hval : j.val = j'.val := by
      have h := congrArg ZMod.val hjeq
      simpa [ZMod.val_natCast_of_lt (ZMod.val_lt j),
        ZMod.val_natCast_of_lt (ZMod.val_lt j')] using h
    have hjj : j = j' := ZMod.val_injective p hval
    subst hjj
    have hωeq : ω = ω' := by
      apply (σ.symm ^ j.val).injective
      simpa [f] using hxy
    subst hωeq
    exact Prod.ext (Subtype.ext rfl) rfl
  have hcard : Fintype.card ({ω : Ω // u ω = t} × ZMod p) ≤ Fintype.card Ω :=
    Fintype.card_le_of_injective f hf
  rw [Fintype.card_prod, Fintype.card_subtype, ZMod.card] at hcard
  have hcard' : p * (Finset.univ.filter fun ω => u ω = t).card ≤ Fintype.card Ω := by
    rw [Nat.mul_comm]
    exact hcard
  have hpk : p * k ≤ Fintype.card Ω :=
    (Nat.mul_le_mul_left p hk).trans hcard'
  omega

theorem eq_three_and_card_dvd_of_sup_eq_top [Fact p.Prime] (hp2 : p ≠ 2) (hn : 3 ≤ n)
    (hp : p ∣ n + 3)
    (T : Equiv.Perm (Fin (n + 3)) →*
      ((Fin (n + 1) → ZMod p) ≃ₗ[ZMod p] (Fin (n + 1) → ZMod p)))
    (hT₁ : ∀ a b : Fin (n + 1),
      T (Equiv.swap a.castSucc.castSucc b.castSucc.castSucc) = coordPerm p n (Equiv.swap a b))
    (hT₂ : T (Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last (n + 1)).castSucc) =
      kRefl p n)
    (hT₃ : T (Equiv.swap (Fin.last n).castSucc.castSucc (Fin.last (n + 2))) = kThreeRefl p n)
    {P₁ P₂ : Subgroup (Equiv.Perm (Fin (n + 3)))} (hP : P₁ ⊔ P₂ = ⊤)
    {v₁ v₂ : Fin (n + 1) → ZMod p} (hv₁ : ∀ σ ∈ P₁, T σ v₁ = v₁)
    (hv₂ : ∀ σ ∈ P₂, T σ v₂ = v₂) {c : ZMod p} (hc : c ≠ 0)
    (hcv : v₁ = fun _ => c)
    (hW : ∀ i j : Fin (n + 1), i ≠ 0 → j ≠ 0 → v₂ i = v₂ j)
    (h01 : v₂ 0 ≠ v₂ 1) :
    p = 3 ∧ Nat.card ↥P₂ ∣ 6 * n.factorial := by
  have hp3 : 3 ≤ p := by
    have hodd : Odd p := (Fact.out : p.Prime).odd_of_ne_two hp2
    exact (Nat.Prime.odd_iff Fact.out).mp hodd
  have hcast3 : ((n + 3 : ℕ) : ZMod p) = 0 := (ZMod.natCast_eq_zero_iff (n + 3) p).mpr hp
  have hn1 : ((n + 1 : ℕ) : ZMod p) = -2 := by
    have h : ((n + 1 : ℕ) : ZMod p) + 2 = 0 := by
      rw [← hcast3]
      push_cast
      ring
    linear_combination h
  have htwo : (2 : ZMod p) ≠ 0 := by
    intro h
    have hpdiv : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h
    exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hpdiv)
  set α : ZMod p := v₂ 1 with hα
  set β : ZMod p := v₂ 0 - α with hβ
  have hv₂0 : v₂ 0 = α + β := by rw [hβ]; ring
  have hβ0 : β ≠ 0 := by
    intro hb
    apply h01
    rw [hv₂0, hb, add_zero, hα]
  have h10 : (1 : Fin (n + 1)) ≠ 0 := by
    intro h
    have hval := congrArg Fin.val h
    simp at hval
    omega
  have hαβ : ∀ i : Fin (n + 1), i ≠ 0 → v₂ i = α := by
    intro i hi
    exact hW i 1 hi h10
  have hval₁ : ∀ a : Fin (n + 1), heartVec p n v₁ (a.castSucc.castSucc) = c := by
    intro a
    rw [hcv, heartVec_castSucc_castSucc]
  have hval_n1 : heartVec p n v₁ ((Fin.last (n + 1)).castSucc) = 0 := by
    rw [hcv, heartVec_n_one]
  have hsumconst : ∑ i : Fin (n + 1), (c : ZMod p) = ((n + 1 : ℕ) : ZMod p) * c := by
    simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  have hval_last : heartVec p n v₁ (Fin.last (n + 2)) = 2 * c := by
    rw [hcv, heartVec_last, hsumconst, hn1]
    ring
  have hc_ne_last : c ≠ 2 * c := by
    intro h
    have hneg : -c = 0 := by linear_combination h
    exact hc (neg_eq_zero.mp hneg)
  have hlast_ne_zero : 2 * c ≠ 0 := mul_ne_zero htwo hc
  have hlt₁ : Fintype.card (Fin (n + 3)) < p * (n + 1) := by
    rw [Fintype.card_fin]
    have h1 : 3 * (n + 1) ≤ p * (n + 1) := Nat.mul_le_mul_right _ hp3
    omega
  have hshift₁ : ∀ σ ∈ P₁, ∀ ω,
      heartVec p n v₁ ω = heartVec p n v₁ (σ.symm ω) := by
    intro σ hσ ω
    obtain ⟨d, hd⟩ := heartVec_transport (p := p) (n := n) hp T hT₁ hT₂ hT₃ σ v₁
    have hd' : ∀ ω, heartVec p n v₁ ω = heartVec p n v₁ (σ.symm ω) + d :=
      fun ω => by simpa [hv₁ σ hσ] using hd ω
    have hfib : n + 1 ≤ (Finset.univ.filter fun ω => heartVec p n v₁ ω = c).card := by
      let g : Fin (n + 1) → {ω : Fin (n + 3) // heartVec p n v₁ ω = c} :=
        fun a => ⟨a.castSucc.castSucc, hval₁ a⟩
      have hg : Function.Injective g := by
        intro a b hab
        have h := congrArg Subtype.val hab
        exact Fin.castSucc_injective (n + 1) (Fin.castSucc_injective (n + 2) h)
      have h := Fintype.card_le_of_injective g hg
      simpa [Fintype.card_fin, Fintype.card_subtype] using h
    have hd0 : d = 0 :=
      eq_zero_of_shift_of_card_fiber (u := heartVec p n v₁) (σ := σ) (c := d) hd' hfib hlt₁
    simpa [hd0] using hd' ω
  have hfix_n1 : ∀ σ ∈ P₁, σ.symm ((Fin.last (n + 1)).castSucc) =
      (Fin.last (n + 1)).castSucc := by
    intro σ hσ
    have h := hshift₁ σ hσ ((Fin.last (n + 1)).castSucc)
    rw [hval_n1] at h
    rcases fin_n3_cases' (n := n) (σ.symm ((Fin.last (n + 1)).castSucc)) with
      ⟨j, hj⟩ | hj | hj
    · rw [hj, hval₁] at h
      exact absurd h.symm hc
    · exact hj
    · rw [hj, hval_last] at h
      exact absurd h.symm hlast_ne_zero
  have hfix_n2 : ∀ σ ∈ P₁, σ.symm (Fin.last (n + 2)) = Fin.last (n + 2) := by
    intro σ hσ
    have h := hshift₁ σ hσ (Fin.last (n + 2))
    rw [hval_last] at h
    rcases fin_n3_cases' (n := n) (σ.symm (Fin.last (n + 2))) with ⟨j, hj⟩ | hj | hj
    · rw [hj, hval₁] at h
      exact absurd h.symm hc_ne_last
    · rw [hj, hval_n1] at h
      exact absurd h hlast_ne_zero
    · exact hj
  have hAmap : ∀ σ ∈ P₁, ∀ a : Fin (n + 1),
      ∃ j : Fin (n + 1), σ (a.castSucc.castSucc) = j.castSucc.castSucc := by
    intro σ hσ a
    by_contra hx
    rcases fin_n3_cases' (n := n) (σ (a.castSucc.castSucc)) with ⟨j, hj⟩ | hj | hj
    · exact hx ⟨j, hj⟩
    · have hcomp : σ.symm (σ (a.castSucc.castSucc)) = a.castSucc.castSucc :=
        Equiv.symm_apply_apply σ _
      rw [hj, hfix_n1 σ hσ] at hcomp
      have hne : ((Fin.last (n + 1)).castSucc : Fin (n + 3)) ≠ a.castSucc.castSucc := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_last] at hval
        omega
      exact hne hcomp
    · have hcomp : σ.symm (σ (a.castSucc.castSucc)) = a.castSucc.castSucc :=
        Equiv.symm_apply_apply σ _
      rw [hj, hfix_n2 σ hσ] at hcomp
      have hne : (Fin.last (n + 2) : Fin (n + 3)) ≠ a.castSucc.castSucc := by
        intro h
        have hval := congrArg Fin.val h
        simp only [Fin.val_castSucc, Fin.val_last] at hval
        omega
      exact hne hcomp
  have hsum₂ : ∑ i : Fin (n + 1), v₂ i = ((n + 1 : ℕ) : ZMod p) * α + β := by
    rw [Fin.sum_univ_succ]
    have hsucc : ∀ i : Fin n, v₂ i.succ = α := fun i => hαβ i.succ (Fin.succ_ne_zero i)
    rw [hv₂0]
    simp only [hsucc, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    push_cast
    ring
  have hlt₂ : Fintype.card (Fin (n + 3)) < p * n := by
    rw [Fintype.card_fin]
    have h1 : 3 * n ≤ p * n := Nat.mul_le_mul_right _ hp3
    omega
  have hshift₂ : ∀ σ ∈ P₂, ∀ ω,
      heartVec p n v₂ ω = heartVec p n v₂ (σ.symm ω) := by
    intro σ hσ ω
    obtain ⟨d, hd⟩ := heartVec_transport (p := p) (n := n) hp T hT₁ hT₂ hT₃ σ v₂
    have hd' : ∀ ω, heartVec p n v₂ ω = heartVec p n v₂ (σ.symm ω) + d :=
      fun ω => by simpa [hv₂ σ hσ] using hd ω
    have hfib : n ≤ (Finset.univ.filter fun ω => heartVec p n v₂ ω = α).card := by
      let g : Fin n → {ω : Fin (n + 3) // heartVec p n v₂ ω = α} :=
        fun i => ⟨(Fin.succ i).castSucc.castSucc, by
          rw [heartVec_castSucc_castSucc]
          exact hαβ (Fin.succ i) (Fin.succ_ne_zero i)⟩
      have hg : Function.Injective g := by
        intro i j hij
        have h := congrArg Subtype.val hij
        exact Fin.succ_injective n
          (Fin.castSucc_injective (n + 1) (Fin.castSucc_injective (n + 2) h))
      have h := Fintype.card_le_of_injective g hg
      simpa [Fintype.card_fin, Fintype.card_subtype] using h
    have hd0 : d = 0 :=
      eq_zero_of_shift_of_card_fiber (u := heartVec p n v₂) (σ := σ) (c := d) hd' hfib hlt₂
    simpa [hd0] using hd' ω
  have hpres₂ : ∀ σ ∈ P₂, ∀ ω,
      heartVec p n v₂ (σ ω) = heartVec p n v₂ ω := by
    intro σ hσ ω
    simpa using hshift₂ σ hσ (σ ω)
  let S : Set (Fin (n + 3)) := fun ω =>
    heartVec p n v₂ ω = α ∨ heartVec p n v₂ ω = α + β
  have hS_A : ∀ a : Fin (n + 1), a.castSucc.castSucc ∈ S := by
    intro a
    by_cases ha : a = 0
    · right
      rw [ha, heartVec_castSucc_castSucc, hv₂0]
    · left
      rw [heartVec_castSucc_castSucc, hαβ a ha]
  let K : Subgroup (Equiv.Perm (Fin (n + 3))) :=
    { carrier := {τ | ∀ ω, ω ∈ S ↔ τ ω ∈ S}
      one_mem' := by intro ω; simp
      mul_mem' := by
        intro τ ρ hτ hρ ω
        rw [Equiv.Perm.mul_apply]
        exact (hρ ω).trans (hτ (ρ ω))
      inv_mem' := by
        intro τ hτ ω
        have h := hτ (τ⁻¹ ω)
        simpa using h.symm }
  have hP₁K : P₁ ≤ K := by
    intro σ hσ ω
    rcases fin_n3_cases' (n := n) ω with ⟨a, rfl⟩ | rfl | rfl
    · obtain ⟨j, hj⟩ := hAmap σ hσ a
      rw [hj]
      exact iff_of_true (hS_A a) (hS_A j)
    · have hfix : σ ((Fin.last (n + 1)).castSucc) = (Fin.last (n + 1)).castSucc := by
        have h := congrArg σ (hfix_n1 σ hσ)
        simpa using h.symm
      rw [hfix]
    · have hfix : σ (Fin.last (n + 2)) = Fin.last (n + 2) := by
        have h := congrArg σ (hfix_n2 σ hσ)
        simpa using h.symm
      rw [hfix]
  have hP₂K : P₂ ≤ K := by
    intro σ hσ ω
    have h := hpres₂ σ hσ ω
    change (heartVec p n v₂ ω = α ∨ heartVec p n v₂ ω = α + β) ↔
      (heartVec p n v₂ (σ ω) = α ∨ heartVec p n v₂ (σ ω) = α + β)
    rw [h]
  have hKtop : K = ⊤ := by
    apply le_antisymm le_top
    rw [← hP]
    exact sup_le hP₁K hP₂K
  have hn1S : (Fin.last (n + 1)).castSucc ∈ S := by
    have hmem : Equiv.swap (0 : Fin (n + 3)) ((Fin.last (n + 1)).castSucc) ∈ K := by
      rw [hKtop]
      exact Subgroup.mem_top _
    have h0 : (0 : Fin (n + 3)) ∈ S := by simpa using hS_A 0
    have h := (hmem 0).mp h0
    simpa [Equiv.swap_apply_left] using h
  have hn2S : Fin.last (n + 2) ∈ S := by
    have hmem : Equiv.swap (0 : Fin (n + 3)) (Fin.last (n + 2)) ∈ K := by
      rw [hKtop]
      exact Subgroup.mem_top _
    have h0 : (0 : Fin (n + 3)) ∈ S := by simpa using hS_A 0
    have h := (hmem 0).mp h0
    simpa [Equiv.swap_apply_left] using h
  have hzero : (0 : ZMod p) = α ∨ (0 : ZMod p) = α + β := by
    have h : heartVec p n v₂ ((Fin.last (n + 1)).castSucc) = α ∨
        heartVec p n v₂ ((Fin.last (n + 1)).castSucc) = α + β := hn1S
    rw [show heartVec p n v₂ ((Fin.last (n + 1)).castSucc) = 0 from
      heartVec_n_one v₂] at h
    exact h
  have htwo' : 2 * α - β = α ∨ 2 * α - β = α + β := by
    have h : heartVec p n v₂ (Fin.last (n + 2)) = α ∨
        heartVec p n v₂ (Fin.last (n + 2)) = α + β := hn2S
    have hval : heartVec p n v₂ (Fin.last (n + 2)) = 2 * α - β := by
      rw [heartVec_last, hsum₂, hn1]
      ring
    rw [hval] at h
    exact h
  have hα0 : α ≠ 0 := by
    intro ha
    have hβzero : β = 0 := by
      rcases htwo' with h | h
      · linear_combination -h + ha
      · have h2b : (2 : ZMod p) * β = 0 := by linear_combination -h + ha
        rcases mul_eq_zero.mp h2b with h2 | hb
        · exact absurd h2 htwo
        · exact hb
    exact hβ0 hβzero
  have hzero' : (0 : ZMod p) = α + β := by
    rcases hzero with h | h
    · exact absurd h.symm hα0
    · exact h
  have hβeq : β = -α := by
    have h : α + β = 0 := hzero'.symm
    linear_combination h
  have hp_eq_three : p = 3 := by
    have h3α : (3 : ZMod p) * α = 0 := by
      rcases htwo' with h | h
      · rw [hβeq] at h
        have h2a : (2 : ZMod p) * α = 0 := by linear_combination h
        rcases mul_eq_zero.mp h2a with h2 | ha
        · exact absurd h2 htwo
        · exact absurd ha hα0
      · rw [hβeq] at h
        linear_combination h
    have h3 : (3 : ZMod p) = 0 := by
      rcases mul_eq_zero.mp h3α with h3 | ha
      · exact h3
      · exact absurd ha hα0
    exact (Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_three).mp
      ((ZMod.natCast_eq_zero_iff 3 p).mp h3)
  have hval_n2 : heartVec p n v₂ (Fin.last (n + 2)) = 0 := by
    rw [heartVec_last, hsum₂, hβeq, hn1]
    have h3z : (3 : ZMod p) = 0 := by
      have h : ((3 : ℕ) : ZMod p) = 0 :=
        (ZMod.natCast_eq_zero_iff 3 p).mpr (by rw [hp_eq_three])
      simpa using h
    have h : (3 : ZMod p) * α = 0 := by rw [h3z, zero_mul]
    linear_combination h
  have hv20 : v₂ 0 = 0 := by
    rw [hv₂0, hβeq]
    ring
  have hv2 : ∀ a : Fin (n + 1), v₂ a = 0 ∨ v₂ a = α := by
    intro a
    by_cases ha : a = 0
    · left
      rw [ha]
      exact hv20
    · right
      exact hαβ a ha
  have hval₂ : ∀ ω : Fin (n + 3), heartVec p n v₂ ω = 0 ∨ heartVec p n v₂ ω = α := by
    intro ω
    rcases fin_n3_cases' (n := n) ω with ⟨a, rfl⟩ | rfl | rfl
    · rw [heartVec_castSucc_castSucc]
      exact hv2 a
    · rw [heartVec_n_one]
      left
      rfl
    · rw [hval_n2]
      left
      rfl
  let Stab : Subgroup (Equiv.Perm (Fin (n + 3))) :=
    { carrier := {g | ∀ x, heartVec p n v₂ (g x) = heartVec p n v₂ x}
      one_mem' := by intro x; rfl
      mul_mem' := by
        intro a b ha hb x
        rw [Equiv.Perm.mul_apply, ha (b x), hb x]
      inv_mem' := by
        intro g hg x
        have h := hg (g⁻¹ x)
        simpa using h.symm }
  have hP₂Stab : P₂ ≤ Stab := by
    intro σ hσ x
    exact hpres₂ σ hσ x
  have h0ge : 3 ≤ Fintype.card {ω : Fin (n + 3) // heartVec p n v₂ ω = 0} := by
    have hsub : ({0, (Fin.last (n + 1)).castSucc, Fin.last (n + 2)} : Finset (Fin (n + 3))) ⊆
        Finset.univ.filter (fun ω => heartVec p n v₂ ω = 0) := by
      intro ω hω
      simp only [Finset.mem_insert, Finset.mem_singleton] at hω
      simp only [Finset.mem_filter, Finset.mem_univ, true_and]
      rcases hω with rfl | rfl | rfl
      · rw [show (0 : Fin (n + 3)) = ((0 : Fin (n + 1)).castSucc.castSucc) from rfl,
          heartVec_castSucc_castSucc]
        exact hv20
      · rw [heartVec_n_one]
      · rw [hval_n2]
    have h0n1 : (0 : Fin (n + 3)) ≠ (Fin.last (n + 1)).castSucc := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_castSucc, Fin.val_last] at hval
      omega
    have h0n2 : (0 : Fin (n + 3)) ≠ Fin.last (n + 2) := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_zero, Fin.val_last] at hval
      omega
    have hn1n2 : ((Fin.last (n + 1)).castSucc : Fin (n + 3)) ≠ Fin.last (n + 2) := by
      intro h
      have hval := congrArg Fin.val h
      simp only [Fin.val_castSucc, Fin.val_last] at hval
      omega
    have hcard : ({0, (Fin.last (n + 1)).castSucc, Fin.last (n + 2)} :
        Finset (Fin (n + 3))).card = 3 := by
      rw [Finset.card_triple_eq_three_iff]
      exact ⟨h0n1, h0n2, hn1n2⟩
    have hle := Finset.card_le_card hsub
    rw [hcard] at hle
    rwa [Fintype.card_subtype]
  have hαge : n ≤ Fintype.card {ω : Fin (n + 3) // heartVec p n v₂ ω = α} := by
    let g : Fin n → {ω : Fin (n + 3) // heartVec p n v₂ ω = α} :=
      fun i => ⟨(Fin.succ i).castSucc.castSucc, by
        rw [heartVec_castSucc_castSucc]
        exact hαβ (Fin.succ i) (Fin.succ_ne_zero i)⟩
    have hg : Function.Injective g := by
      intro i j hij
      have h := congrArg Subtype.val hij
      exact Fin.succ_injective n
        (Fin.castSucc_injective (n + 1) (Fin.castSucc_injective (n + 2) h))
    have h := Fintype.card_le_of_injective g hg
    simpa [Fintype.card_fin] using h
  have htotal : Fintype.card {ω : Fin (n + 3) // heartVec p n v₂ ω = 0} +
      Fintype.card {ω : Fin (n + 3) // heartVec p n v₂ ω = α} = n + 3 := by
    let F0 : Finset (Fin (n + 3)) := Finset.univ.filter fun ω => heartVec p n v₂ ω = 0
    let Fα : Finset (Fin (n + 3)) := Finset.univ.filter fun ω => heartVec p n v₂ ω = α
    have hdisj : Disjoint F0 Fα := by
      rw [Finset.disjoint_left]
      intro ω h0 hα'
      simp only [F0, Fα, Finset.mem_filter, Finset.mem_univ, true_and] at h0 hα'
      exact hα0 (hα'.symm.trans h0)
    have hunion : F0 ∪ Fα = Finset.univ := by
      ext ω
      simp only [F0, Fα, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      exact ⟨fun _ => trivial, fun _ => hval₂ ω⟩
    have hc := Finset.card_union_of_disjoint hdisj
    rw [hunion, Finset.card_univ, Fintype.card_fin] at hc
    rw [Fintype.card_subtype, Fintype.card_subtype]
    change F0.card + Fα.card = n + 3
    omega
  have hcard0 : Fintype.card {ω : Fin (n + 3) // heartVec p n v₂ ω = 0} = 3 := by
    omega
  have hcardα : Fintype.card {ω : Fin (n + 3) // heartVec p n v₂ ω = α} = n := by
    omega
  have hprod : (∏ i, Nat.factorial
      (Fintype.card {ω : Fin (n + 3) // heartVec p n v₂ ω = i})) = 6 * n.factorial := by
    have hsubset : ({0, α} : Finset (ZMod p)) ⊆ Finset.univ := by simp
    have hother : ∀ i ∈ Finset.univ, i ∉ ({0, α} : Finset (ZMod p)) →
        Nat.factorial (Fintype.card {ω : Fin (n + 3) // heartVec p n v₂ ω = i}) = 1 := by
      intro i _ hi
      have hempty : IsEmpty {ω : Fin (n + 3) // heartVec p n v₂ ω = i} := by
        refine ⟨fun x => ?_⟩
        rcases hval₂ x.1 with h | h
        · exact hi (by rw [← x.2, h]; simp)
        · exact hi (by rw [← x.2, h]; simp)
      rw [Fintype.card_eq_zero_iff.mpr hempty, Nat.factorial_zero]
    rw [← Finset.prod_eq_of_subset hsubset _ hother]
    rw [Finset.prod_pair (Ne.symm hα0)]
    rw [hcard0, hcardα]
    norm_num [Nat.factorial]
  haveI : Fintype ↥Stab := Fintype.ofFinite _
  have hstabcard : Nat.card ↥Stab = 6 * n.factorial := by
    rw [Nat.card_eq_fintype_card]
    calc Fintype.card ↥Stab
        = Fintype.card {g : Equiv.Perm (Fin (n + 3)) //
            heartVec p n v₂ ∘ g = heartVec p n v₂} :=
          Fintype.card_congr
            { toFun := fun g => ⟨g.1, funext g.2⟩
              invFun := fun g => ⟨g.1, fun x => congrFun g.2 x⟩
              left_inv := fun g => rfl
              right_inv := fun g => rfl }
      _ = ∏ i, Nat.factorial
          (Fintype.card {ω : Fin (n + 3) // heartVec p n v₂ ω = i}) :=
          DomMulAct.stabilizer_card (f := heartVec p n v₂)
      _ = 6 * n.factorial := hprod
  have hdvd : Nat.card ↥P₂ ∣ Nat.card ↥Stab := Subgroup.card_dvd_of_le hP₂Stab
  rw [hstabcard] at hdvd
  exact ⟨hp_eq_three, hdvd⟩

end CFSG.StandardType.TypeAReflOver

end

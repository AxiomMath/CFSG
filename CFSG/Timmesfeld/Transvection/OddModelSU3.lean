module

public import CFSG.Timmesfeld.Transvection.OddModelHeis
public import CFSG.Timmesfeld.Transvection.OddModelBlock
import CFSG.Timmesfeld.Transvection.PresSUHalf
import CFSG.LocalAnalysis.UniquenessCase.Lie.SU3

public section

namespace CFSG.Timmesfeld.Transvection.Pres

open Matrix CFSG.LieType.Universal.Unitary CFSG.LieType.Universal.Unitary.SUExtras
  CFSG.LieType.Steinberg CFSG.LieType.BorelTits CFSG.LocalAnalysis.UniquenessCase
  CFSG.HardMathSupport.Cooperstein.Coordinator.LieInput
open CFSG.LieType.Universal.Symplectic.SpExtras (wt)
open scoped commutatorElement

variable {F : Type} [Field F] {σ : F ≃+* F} (hσ : ∀ c, σ (σ c) = c)

private theorem toStd_three_eq_self (v : Fin (3 / 2) → ℤ) : toStd 3 v = v := by
  funext a
  have ha : a.val = 0 := by have := a.isLt; omega
  rw [toStd, if_neg (show ¬ Even 3 by decide)]
  simp [ha]

theorem toStd_three_single :
    toStd 3 (Pi.single (0 : Fin (3 / 2)) 1) = wt (Sum.inl (0 : Fin (3 / 2))) := by
  rw [toStd_last_odd (k := (0 : Fin (3 / 2))) (n := 3) (by decide) (by decide)]
  exact (weight_crd (m := 3) (Sum.inl (0 : Fin (3 / 2)))).symm

private theorem toStd_three_neg_single :
    toStd 3 (-Pi.single (0 : Fin (3 / 2)) 1) = wt (Sum.inr (0 : Fin (3 / 2))) := by
  rw [toStd_three_eq_self]
  rfl

private theorem toStd_three_two_smul :
    toStd 3 (2 • Pi.single (0 : Fin (3 / 2)) 1) =
      rt (Sum.inl (0 : Fin (3 / 2))) (Sum.inl (0 : Fin (3 / 2))) := by
  rw [toStd_three_eq_self, rt_inl_inl]

private theorem lastIdxOdd_crd_inl_zero {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) :
    lastIdxOdd k hn (crd (Sum.inl (0 : Fin (3 / 2)))) = lowIdx k := rfl

private theorem lastIdxOdd_crd_inr_zero {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) :
    lastIdxOdd k hn (crd (Sum.inr (0 : Fin (3 / 2)))) = Fin.rev (lowIdx k) := rfl

private theorem lastIdxOdd_midIdx_three {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) :
    lastIdxOdd k hn (midIdx 3 (by decide)) = midIdx n hn := rfl

theorem su3Emb_suHeis_inl {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) (u v : F) :
    su3Emb σ hn k (suHeis σ hσ (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩)
        (Sum.inl (0 : Fin (3 / 2))) u v) =
      suHeis σ hσ hn (Sum.inl k) u v := by
  by_cases h : v + σ v + σ u * u = 0
  · apply mat_injective
    rw [show su3Emb σ hn k = suEmbed σ (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)
      from rfl]
    rw [mat_suEmbed, mat_suHeis hσ (by decide) h, mat_suHeis hσ hn h]
    rw [extendMat_heisenbergMatrix (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)
      (crd (Sum.inl (0 : Fin (3 / 2)))) (midIdx 3 (by decide)) (rev_midIdx (by decide)) u v]
    rw [lastIdxOdd_crd_inl_zero, lastIdxOdd_midIdx_three, crd_inl]
  · rw [suHeis_of_not hσ (by decide : ¬ Even 3) h, suHeis_of_not hσ hn h, map_one]

theorem su3Emb_suHeis_inr {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2)) (u v : F) :
    su3Emb σ hn k (suHeis σ hσ (Nat.not_even_iff_odd.mpr ⟨1, rfl⟩)
        (Sum.inr (0 : Fin (3 / 2))) u v) =
      suHeis σ hσ hn (Sum.inr k) u v := by
  by_cases h : v + σ v + σ u * u = 0
  · apply mat_injective
    rw [show su3Emb σ hn k = suEmbed σ (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)
      from rfl]
    rw [mat_suEmbed, mat_suHeis hσ (by decide) h, mat_suHeis hσ hn h]
    rw [extendMat_heisenbergMatrix (lastIdxOdd_injective' hn k) (lastIdxOdd_rev hn)
      (crd (Sum.inr (0 : Fin (3 / 2)))) (midIdx 3 (by decide)) (rev_midIdx (by decide)) u v]
    rw [lastIdxOdd_crd_inr_zero, lastIdxOdd_midIdx_three, crd_inr]
  · rw [suHeis_of_not hσ (by decide : ¬ Even 3) h, suHeis_of_not hσ hn h, map_one]

theorem map_rootGroup_su3Emb {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2))
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = wt (Sum.inl k)) :
    (CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
        (Pi.single (0 : Fin (3 / 2)) 1)).map (su3Emb σ hn k) =
      CFSG.LieType.Universal.Unitary.rootGroup σ hσ n γ := by
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨u, v, h, rfl⟩ :=
      (mem_rootGroup_iff_suHeis hσ (by decide : ¬ Even 3) (a := Sum.inl (0 : Fin (3 / 2)))
        toStd_three_single A).mp hA
    exact (mem_rootGroup_iff_suHeis hσ hn (a := Sum.inl k) hγ
      (su3Emb σ hn k (suHeis σ hσ (by decide : ¬ Even 3)
        (Sum.inl (0 : Fin (3 / 2))) u v))).mpr
      ⟨u, v, h, (su3Emb_suHeis_inl hσ hn k u v).symm⟩
  · intro hx
    obtain ⟨u, v, h, rfl⟩ :=
      (mem_rootGroup_iff_suHeis hσ hn (a := Sum.inl k) hγ x).mp hx
    refine Subgroup.mem_map.mpr
      ⟨suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u v, ?_,
        su3Emb_suHeis_inl hσ hn k u v⟩
    exact (mem_rootGroup_iff_suHeis hσ (by decide : ¬ Even 3) (a := Sum.inl (0 : Fin (3 / 2)))
      toStd_three_single _).mpr ⟨u, v, h, rfl⟩

theorem map_rootGroup_su3Emb_neg {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2))
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = wt (Sum.inr k)) :
    (CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
        (-Pi.single (0 : Fin (3 / 2)) 1)).map (su3Emb σ hn k) =
      CFSG.LieType.Universal.Unitary.rootGroup σ hσ n γ := by
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨u, v, h, rfl⟩ :=
      (mem_rootGroup_iff_suHeis hσ (by decide : ¬ Even 3) (a := Sum.inr (0 : Fin (3 / 2)))
        toStd_three_neg_single A).mp hA
    exact (mem_rootGroup_iff_suHeis hσ hn (a := Sum.inr k) hγ
      (su3Emb σ hn k (suHeis σ hσ (by decide : ¬ Even 3)
        (Sum.inr (0 : Fin (3 / 2))) u v))).mpr
      ⟨u, v, h, (su3Emb_suHeis_inr hσ hn k u v).symm⟩
  · intro hx
    obtain ⟨u, v, h, rfl⟩ :=
      (mem_rootGroup_iff_suHeis hσ hn (a := Sum.inr k) hγ x).mp hx
    refine Subgroup.mem_map.mpr
      ⟨suHeis σ hσ (by decide : ¬ Even 3) (Sum.inr (0 : Fin (3 / 2))) u v, ?_,
        su3Emb_suHeis_inr hσ hn k u v⟩
    exact (mem_rootGroup_iff_suHeis hσ (by decide : ¬ Even 3) (a := Sum.inr (0 : Fin (3 / 2)))
      toStd_three_neg_single _).mpr ⟨u, v, h, rfl⟩

theorem map_rootGroup_su3Emb_long {n : ℕ} (hn : ¬ Even n) (k : Fin (n / 2))
    {γ : Fin (n / 2) → ℤ} (hγ : toStd n γ = rt (Sum.inl k) (Sum.inl k)) :
    (CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
        (2 • Pi.single (0 : Fin (3 / 2)) 1)).map (su3Emb σ hn k) =
      CFSG.LieType.Universal.Unitary.rootGroup σ hσ n γ := by
  ext x
  constructor
  · rintro ⟨A, hA, rfl⟩
    obtain ⟨c, hc, rfl⟩ :=
      (mem_rootGroup_iff_suLong_odd hσ (a := Sum.inl (0 : Fin (3 / 2)))
        toStd_three_two_smul A).mp hA
    exact (mem_rootGroup_iff_suLong_odd hσ (a := Sum.inl k) hγ
      (su3Emb σ hn k (suLong σ (Sum.inl (0 : Fin (3 / 2))) c))).mpr
      ⟨c, hc, (su3Emb_suLong_inl hn k c).symm⟩
  · intro hx
    obtain ⟨c, hc, rfl⟩ :=
      (mem_rootGroup_iff_suLong_odd hσ (a := Sum.inl k) hγ x).mp hx
    refine Subgroup.mem_map.mpr
      ⟨suLong σ (Sum.inl (0 : Fin (3 / 2))) c, ?_, su3Emb_suLong_inl hn k c⟩
    exact suLong_mem hσ (a := Sum.inl (0 : Fin (3 / 2))) toStd_three_two_smul c

theorem rootGroup_three_isSylow {F : Type} [Field F] [Finite F] [CharP F 2] {f : ℕ}
    (hF : Nat.card F = (2 ^ f) ^ 2) :
    ∃ S : Sylow 2 (SU (unitaryInvolution F 2 f) 3),
      (S : Subgroup _) = CFSG.LieType.Universal.Unitary.rootGroup _
        (unitaryInvolution_involutive hF) 3 (Pi.single 0 1) := by
  have hf : 1 ≤ f := by
    have h2 : 1 < Nat.card F := Finite.one_lt_card
    rcases Nat.eq_zero_or_pos f with h | h
    · rw [h] at hF
      norm_num at hF
      omega
    · exact h
  refine ⟨(UC22.uc22pwsu3X_isPGroup hF).toSylow (UC22.uc22pwsu3X_index hf hF), ?_⟩
  rw [IsPGroup.toSylow_coe]

private theorem suLong_eq_zero_of_eq_one {a : Fin (3 / 2) ⊕ Fin (3 / 2)} {c : F}
    (hc : c + σ c = 0) (h : suLong σ a c = 1) : c = 0 := by
  have h1 := mat_suLong_apply (a := a) hc
  rw [h, map_one] at h1
  have h2 : (1 : Matrix (Fin 3) (Fin 3) F) (crd a) (crd (Sum.swap a)) = c := h1
  rw [Matrix.one_apply_ne (by rw [crd_swap]; exact crd_ne_rev a)] at h2
  exact h2.symm

private theorem suHeis_first_eq_zero_of_mem_center [CharP F 2]
    (hne : ∃ c, σ c ≠ c) (htr : ∀ x, σ x = x → ∃ c, c + σ c = x)
    {u v : F} (hv : v + σ v + σ u * u = 0)
    {z : ↥(CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
      (Pi.single (0 : Fin (3 / 2)) 1))}
    (hz : z ∈ Subgroup.center (CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
      (Pi.single (0 : Fin (3 / 2)) 1)))
    (hzuv : (z : SU σ 3) = suHeis σ hσ (by decide : ¬ Even 3)
      (Sum.inl (0 : Fin (3 / 2))) u v) : u = 0 := by
  classical
  have hvalid : ∀ u' : F, ∃ v' : F, v' + σ v' + σ u' * u' = 0 := by
    intro u'
    have hfix : σ (σ u' * u') = σ u' * u' := by rw [map_mul, hσ, mul_comm]
    obtain ⟨v', hv'⟩ := htr (σ u' * u') hfix
    exact ⟨v', by rw [hv']; exact CharTwo.add_self_eq_zero (σ u' * u')⟩
  have hcomm : ∀ u' : F,
      suLong σ (Sum.inl (0 : Fin (3 / 2))) (u * σ u' + u' * σ u) = 1 := by
    intro u'
    obtain ⟨v', hv'⟩ := hvalid u'
    have hmem : suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u' v' ∈
        CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
          (Pi.single (0 : Fin (3 / 2)) 1) :=
      suHeis_mem hσ (by decide : ¬ Even 3) (a := Sum.inl (0 : Fin (3 / 2)))
        toStd_three_single u' v'
    have hcent := Subgroup.mem_center_iff.mp hz
      (⟨suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u' v', hmem⟩ :
        ↥(CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
          (Pi.single (0 : Fin (3 / 2)) 1)))
    have hcentSU : suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u v *
        suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u' v' =
        suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u' v' *
          suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u v := by
      have h' : (z : SU σ 3) * suHeis σ hσ (by decide : ¬ Even 3)
          (Sum.inl (0 : Fin (3 / 2))) u' v' =
          suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u' v' *
            (z : SU σ 3) := congrArg (fun e : ↥(CFSG.LieType.Universal.Unitary.rootGroup
              σ hσ 3 (Pi.single (0 : Fin (3 / 2)) 1)) => (e : SU σ 3)) hcent.symm
      simpa only [hzuv] using h'
    have hc : ⁅suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u v,
        suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u' v'⁆ = 1 :=
      commutatorElement_eq_one_iff_mul_comm.mpr hcentSU
    rwa [suHeis_comm_self hσ (by decide : ¬ Even 3) hv hv'] at hc
  have h1 : suLong σ (Sum.inl (0 : Fin (3 / 2))) (u + σ u) = 1 := by
    simpa using hcomm 1
  have htrace : (u + σ u) + σ (u + σ u) = 0 := by
    rw [map_add, hσ]
    calc u + σ u + (σ u + u) = (u + u) + (σ u + σ u) := by ring
      _ = 0 := by rw [CharTwo.add_self_eq_zero, CharTwo.add_self_eq_zero, add_zero]
  have hu : u + σ u = 0 := suLong_eq_zero_of_eq_one htrace h1
  have hσu : σ u = u := (CharTwo.add_eq_zero.mp hu).symm
  obtain ⟨c, hcne⟩ := hne
  have hzero : u * σ c + c * σ u = 0 := by
    have hc0 : suLong σ (Sum.inl (0 : Fin (3 / 2))) (u * σ c + c * σ u) = 1 := hcomm c
    refine suLong_eq_zero_of_eq_one ?_ hc0
    simp only [map_add, map_mul, hσ, hσu]
    calc u * σ c + c * u + (u * c + σ c * u) =
        (u * σ c + c * u) + (u * σ c + c * u) := by ring
      _ = 0 := CharTwo.add_self_eq_zero _
  have hzero' : u * (σ c + c) = 0 := by
    calc u * (σ c + c) = u * σ c + c * σ u := by rw [hσu]; ring
      _ = 0 := hzero
  have hne0 : σ c + c ≠ 0 := fun h0 => hcne (CharTwo.add_eq_zero.mp h0)
  rcases mul_eq_zero.mp hzero' with h | h
  · exact h
  · exact absurd h hne0

theorem center_rootGroup_three [CharP F 2] (hne : ∃ c, σ c ≠ c)
    (htr : ∀ x, σ x = x → ∃ c, c + σ c = x) :
    (Subgroup.center (CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
      (Pi.single (0 : Fin (3 / 2)) 1))).map
        (CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
          (Pi.single (0 : Fin (3 / 2)) 1)).subtype =
      CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3 (2 • Pi.single (0 : Fin (3 / 2)) 1) := by
  refine le_antisymm ?_ ?_
  · rintro y hy
    obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp hy
    obtain ⟨u, v, hv, hzuv⟩ :=
      (mem_rootGroup_iff_suHeis hσ (by decide : ¬ Even 3) (a := Sum.inl (0 : Fin (3 / 2)))
        toStd_three_single z).mp z.2
    have hu : u = 0 := suHeis_first_eq_zero_of_mem_center hσ hne htr hv hz hzuv.symm
    change (z : SU σ 3) ∈ CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
      (2 • Pi.single (0 : Fin (3 / 2)) 1)
    rw [← hzuv, hu, suHeis_zero_left hσ (by decide) (a := Sum.inl (0 : Fin (3 / 2)))]
    exact suLong_mem hσ (a := Sum.inl (0 : Fin (3 / 2))) toStd_three_two_smul v
  · intro y hy
    obtain ⟨c, -, rfl⟩ :=
      (mem_rootGroup_iff_suLong_odd hσ (a := Sum.inl (0 : Fin (3 / 2)))
        toStd_three_two_smul y).mp hy
    have hyX : suLong σ (Sum.inl (0 : Fin (3 / 2))) c ∈
        CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3 (Pi.single (0 : Fin (3 / 2)) 1) := by
      rw [← suHeis_zero_left hσ (by decide) (a := Sum.inl (0 : Fin (3 / 2))) c]
      exact suHeis_mem hσ (by decide : ¬ Even 3) (a := Sum.inl (0 : Fin (3 / 2)))
        toStd_three_single 0 c
    have hcent : (⟨suLong σ (Sum.inl (0 : Fin (3 / 2))) c, hyX⟩ :
        ↥(CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3 (Pi.single (0 : Fin (3 / 2)) 1))) ∈
        Subgroup.center (CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
          (Pi.single (0 : Fin (3 / 2)) 1)) := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨u, v, -, hgu⟩ :=
        (mem_rootGroup_iff_suHeis hσ (by decide : ¬ Even 3) (a := Sum.inl (0 : Fin (3 / 2)))
          toStd_three_single g).mp g.2
      have hguX : (⟨suHeis σ hσ (by decide : ¬ Even 3) (Sum.inl (0 : Fin (3 / 2))) u v,
          suHeis_mem hσ (by decide : ¬ Even 3) (a := Sum.inl (0 : Fin (3 / 2)))
            toStd_three_single u v⟩ :
          ↥(CFSG.LieType.Universal.Unitary.rootGroup σ hσ 3
            (Pi.single (0 : Fin (3 / 2)) 1))) = g := Subtype.ext hgu
      rw [← hguX]
      exact Subtype.ext (commutatorElement_eq_one_iff_mul_comm.mp
        (suHeis_comm_suLong hσ (by decide : ¬ Even 3) (a := Sum.inl 0) (c := Sum.inl 0)
          (by simp) u v c))
    exact Subgroup.mem_map.mpr
      ⟨⟨suLong σ (Sum.inl (0 : Fin (3 / 2))) c, hyX⟩, hcent, rfl⟩

end CFSG.Timmesfeld.Transvection.Pres


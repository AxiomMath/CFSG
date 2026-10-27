module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.RankThree.PartTwo.Census CFSG.Assembly CFSG.Assembly.RankThreeEven Matrix
  Matrix.SpecialLinearGroup

variable {K : Type} [Field K]

theorem le_localRank_quotient_torus [Finite K] [CharP K 2] {r m n : ℕ} (hr : r.Prime)
    (hrK : r ∣ Nat.card Kˣ) (hmn : m < n) (h1n : 1 < n) (hcen : m + 1 < n ∨ ¬ r ∣ n)
    (N : Subgroup (SpecialLinearGroup (Fin n) K)) [N.Normal] (hN : N ≤ Subgroup.center _) :
    m ≤ localRank r (SpecialLinearGroup (Fin n) K ⧸ N) := by
  have hμ := card_rootsOfUnity_of_dvd hr hrK
  set incl := (rootsOfUnity r K).subtype
  set φ := (torusSL m n hmn K).comp (incl.compLeft (Fin m))
  have hφ : Function.Injective φ :=
    (torusSL_injective hmn).comp fun s t hst => funext fun j =>
      Subtype.ext (congrFun hst j)
  have hentry : ∀ s i, ((φ s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) i i =
      ((incl (torusEntries (rootsOfUnity r K) m n s i) : Kˣ) : K) := by
    intro s i
    change ((torusSL m n hmn K (incl.compLeft (Fin m) s) : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) i i = _
    rw [coe_torusSL, diagonal_apply_eq, torusEntries_compLeft]
    rfl
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, h1n⟩ := by simp
  set P := (rootSL h01 K).range
  refine le_localRank_quotient_of_le_normalizer N hr (E := φ.range) (P := P)
    (isElemAbelian_range (fun s => funext fun j => rootsOfUnity_pow_eq_one (s j)) φ)
    ?_ ?_ ?_ ?_ ?_
  · rw [← Nat.card_congr (MonoidHom.ofInjective hφ).toEquiv]
    exact card_fun_rootsOfUnity hμ
  · rw [eq_bot_iff]
    rintro x ⟨⟨s, rfl⟩, hxN⟩
    obtain ⟨c, hcn, hc⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hN hxN)
    rw [Fintype.card_fin] at hcn
    have hci : ∀ i, c = ((incl (torusEntries (rootsOfUnity r K) m n s i) : Kˣ) : K) := by
      intro i
      rw [← hentry, ← hc, scalar_apply, diagonal_apply_eq]
    have hc1 : c = 1 := by
      rcases hcen with h | h
      · rw [hci ⟨m + 1, h⟩, torusEntries_of_gt _ (by simp), map_one, Units.val_one]
      · have hcr : c ^ r = 1 := by
          rw [hci ⟨0, by omega⟩, ← Units.val_pow_eq_pow_val, ← map_pow,
            rootsOfUnity_pow_eq_one, map_one, Units.val_one]
        have hg : c ^ Nat.gcd r n = 1 := pow_gcd_eq_one.mpr ⟨hcr, hcn⟩
        rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hr).mpr h), pow_one]
          at hg
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    rw [← hc, hc1, map_one]
    rfl
  · intro y
    obtain ⟨c, hc⟩ := y.2
    refine ⟨1, Subtype.ext ?_⟩
    rw [pow_one, pow_two, Subgroup.coe_mul, ← hc, ← map_mul, OneMemClass.coe_one]
    change SpecialLinearGroup.transvection h01 (c.toAdd + c.toAdd) = 1
    rw [CharTwo.add_self_eq_zero, SpecialLinearGroup.transvection_coeff_zero]
  · intro hP
    have h1 : rootSL h01 K (Multiplicative.ofAdd 1) ∈ P := ⟨_, rfl⟩
    have := (SpecialLinearGroup.transvection_mem_center_iff h01 (1 : K)).mp (hN (hP h1))
    exact one_ne_zero this
  · refine le_normalizer_of_conj_mem ?_
    rintro _ ⟨s, rfl⟩ _ ⟨c, rfl⟩
    set d := incl.compLeft (Fin n) (torusEntries (rootsOfUnity r K) m n s)
    refine ⟨Multiplicative.ofAdd ((d ⟨0, by omega⟩ : K) * c.toAdd *
      ((d ⟨1, h1n⟩)⁻¹ : Kˣ)), ?_⟩
    rw [eq_mul_inv_iff_mul_eq]
    refine Subtype.ext ?_
    change Matrix.transvection _ _ _ * ((φ s : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) = ((φ s : SpecialLinearGroup (Fin n) K) :
      Matrix (Fin n) (Fin n) K) * Matrix.transvection _ _ c.toAdd
    have hφs : ((φ s : SpecialLinearGroup (Fin n) K) : Matrix (Fin n) (Fin n) K) =
        diagonal fun l => (d l : K) := by
      change ((torusSL m n hmn K (incl.compLeft (Fin m) s) : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) = _
      rw [coe_torusSL, torusEntries_compLeft]
    rw [hφs, diagonal_mul_transvection h01 d]
    rfl

theorem le_localRank_of_surjective_torus [Finite K] [CharP K 2] {r m n : ℕ} (hr : r.Prime)
    (hrK : r ∣ Nat.card Kˣ) (hmn : m < n) (h1n : 1 < n) (hcen : m + 1 < n ∨ ¬ r ∣ n)
    {L : Type} [Group L] [Finite L] (ρ : SpecialLinearGroup (Fin n) K →* L)
    (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ Subgroup.center _) : m ≤ localRank r L := by
  have h := le_localRank_quotient_torus hr hrK hmn h1n hcen ρ.ker hker
  have e := QuotientGroup.quotientKerEquivOfSurjective ρ hρ
  rw [localRank_eq_of_mulEquiv e hr] at h
  exact h

end CFSG.RankThree.PartOne.KFU

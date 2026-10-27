module

public import CFSG.RankThree.PartTwo.Census.Classical.EvenWitness

public section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Assembly CFSG.Assembly.RankThreeEven Matrix CFSG.RankThree.PartTwo.Census
  CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem le_localRank_statedSU_torus_quot [Finite K] {p f : ℕ} (h : UnitaryFieldData p f K)
    [CharP K 2] {r k n : ℕ} (hr : r.Prime) (hrq : r ∣ p ^ f + 1) (hkn : k + 2 < n)
    (hcen : k + 3 < n ∨ ¬ r ∣ n) (N : Subgroup (StatedSU n (p ^ f) K)) [N.Normal]
    (hN : N ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)) :
    k + 1 ≤ localRank r (↥(StatedSU n (p ^ f) K) ⧸ N) := by
  have : Fact p.Prime := ⟨h.prime⟩
  have hn2 : 2 ≤ n := by omega
  have hrK : r ∣ Nat.card Kˣ := by
    rw [Nat.card_units, h.card, pow_mul', sq,
      show p ^ f * p ^ f - 1 = p ^ f * p ^ f - 1 * 1 by rw [mul_one],
      Nat.mul_self_sub_mul_self_eq]
    exact dvd_mul_of_dvd_left hrq _
  have hμ := card_rootsOfUnity_of_dvd hr hrK
  set μ := rootsOfUnity r K
  set incl := μ.subtype
  set u : (Fin (k + 1) → μ) →* (Fin n → μ) := (torusEntries μ (k + 2) n).comp (dupHom μ k)
  set d : (Fin (k + 1) → μ) →* (Fin n → Kˣ) := (incl.compLeft (Fin n)).comp u
  set ψ := (diagGL n K).comp d
  have hd : ∀ s i, d s i = incl (u s i) := fun _ _ => rfl
  have hdr : ∀ s i, (d s i : K) ^ r = 1 := by
    intro s i
    rw [hd, ← Units.val_pow_eq_pow_val, ← map_pow, rootsOfUnity_pow_eq_one, map_one,
      Units.val_one]
  have hcoe : ∀ s, ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) =
      diagonal fun i => (d s i : K) := fun _ => rfl
  have hmem : ∀ s, ψ s ∈ StatedSU n (p ^ f) K := by
    intro s
    refine (mem_unitarySU_iff h).mpr ⟨?_, ?_⟩
    · rw [hcoe, det_diagonal, ← Units.coe_prod]
      have : ∏ i, d s i = incl (∏ i, torusEntries μ (k + 2) n (dupHom μ k s) i) := by
        rw [map_prod]
        rfl
      rw [this, prod_torusEntries hkn, map_one, Units.val_one]
    · rw [hcoe, diagonal_map (map_zero _), diagonal_transpose, diagonal_mul_diagonal,
        ← diagonal_one]
      refine congrArg diagonal (funext fun i => ?_)
      obtain ⟨m, hm⟩ := hrq
      rw [h.bar_apply, ← pow_succ, hm, pow_mul, hdr, one_pow]
  set ψ' : (Fin (k + 1) → μ) →* StatedSU n (p ^ f) K := ψ.codRestrict _ hmem
  have hψ' : Function.Injective ψ' := by
    intro s t hst
    have h1 : ψ s = ψ t := congrArg Subtype.val hst
    have h2 : d s = d t := by
      funext i
      have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) h1
      simp only [hcoe, diagonal_apply_eq] at this
      exact Units.ext this
    have h3 : u s = u t := funext fun i => Subtype.ext (congrFun h2 i)
    exact dupHom_injective k (torusEntries_injective hkn.le h3)
  set t : StatedSU n (p ^ f) K := ⟨swapGL hn2, swapGL_mem_statedSU h hn2⟩
  refine le_localRank_quotient_of_commute N hr (E := ψ'.range)
    (isElemAbelian_range (fun s => funext fun j => rootsOfUnity_pow_eq_one (s j)) ψ') ?_ ?_
    (t := t) ?_ ?_ ?_
  · rw [← Nat.card_congr (MonoidHom.ofInjective hψ').toEquiv]
    exact card_fun_rootsOfUnity hμ
  · rw [eq_bot_iff]
    rintro x ⟨⟨s, rfl⟩, hxN⟩
    obtain ⟨c, hc⟩ := (Subgroup.mem_subgroupOf.mp (hN hxN))
    have hc' : GeneralLinearGroup.scalar (Fin n) c = ψ s := hc
    have hci : ∀ i, (c : K) = (d s i : K) := by
      intro i
      have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) i i) hc'
      simpa only [GeneralLinearGroup.coe_scalar, scalar_apply, diagonal_apply_eq, hcoe]
        using this
    have hc1 : (c : K) = 1 := by
      rcases hcen with hlt | hndvd
      · rw [hci ⟨k + 3, hlt⟩, hd]
        change ((incl (torusEntries μ (k + 2) n (dupHom μ k s) ⟨k + 3, hlt⟩) : Kˣ) : K) = 1
        rw [torusEntries_of_gt _ (by simp), map_one, Units.val_one]
      · have hcr : (c : K) ^ r = 1 := by rw [hci ⟨0, by omega⟩, hdr]
        have hcn : (c : K) ^ n = 1 := by
          have hdet := ((mem_unitarySU_iff h).mp (hmem s)).1
          rw [← hc', GeneralLinearGroup.coe_scalar, scalar_apply, det_diagonal,
            Finset.prod_const, Finset.card_univ, Fintype.card_fin] at hdet
          exact hdet
        have hg : (c : K) ^ Nat.gcd r n = 1 := pow_gcd_eq_one.mpr ⟨hcr, hcn⟩
        rwa [Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd hr).mpr hndvd), pow_one]
          at hg
    rw [Subgroup.mem_bot]
    refine Subtype.ext ?_
    change ψ s = 1
    rw [← hc', show c = 1 from Units.ext hc1, map_one]
  · intro htN
    obtain ⟨c, hc⟩ := Subgroup.mem_subgroupOf.mp (hN htN)
    have := congrArg (fun A : GL (Fin n) K => (A : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
      ⟨1, by omega⟩) hc
    simp only [GeneralLinearGroup.coe_scalar, scalar_apply, t, coe_swapGL, swapBlock,
      Matrix.add_apply, of_apply, Matrix.one_apply] at this
    simp at this
  · rw [show t ^ 2 = 1 from Subtype.ext (Units.ext (by
      rw [pow_two]
      exact one_add_mul_one_add (swapBlock_mul_self hn2)))]
    exact N.one_mem
  · rintro _ ⟨s, rfl⟩
    refine Subtype.ext (Units.ext ?_)
    change ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K) * (1 + swapBlock n K) =
      (1 + swapBlock n K) * ((ψ s : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    rw [hcoe]
    refine diagonal_mul_swap fun i j hi hj => ?_
    have key : ∀ l : Fin n, l.val < 2 → (d s l : K) = ((incl (s ⟨0, by omega⟩) : Kˣ) : K) := by
      intro l hl
      rw [hd]
      change ((incl (torusEntries μ (k + 2) n (dupHom μ k s) l) : Kˣ) : K) = _
      rw [torusEntries_of_lt _ (by omega), dupHom_apply]
      congr 3
      ext
      simp only
      omega
    rw [key i hi, key j hj]

theorem le_localRank_of_surjective_statedSU_torus [Finite K] {p f : ℕ}
    (h : UnitaryFieldData p f K) [CharP K 2] {r k n : ℕ} (hr : r.Prime) (hrq : r ∣ p ^ f + 1)
    (hkn : k + 2 < n) (hcen : k + 3 < n ∨ ¬ r ∣ n) {L : Type} [Group L] [Finite L]
    (ρ : StatedSU n (p ^ f) K →* L) (hρ : Function.Surjective ρ)
    (hker : ρ.ker ≤ (StatedScalars (Fin n) K).subgroupOf (StatedSU n (p ^ f) K)) :
    k + 1 ≤ localRank r L := by
  have h1 := le_localRank_statedSU_torus_quot h hr hrq hkn hcen ρ.ker hker
  have e := QuotientGroup.quotientKerEquivOfSurjective ρ hρ
  rw [localRank_eq_of_mulEquiv e hr] at h1
  exact h1

end CFSG.RankThree.PartOne.KFU

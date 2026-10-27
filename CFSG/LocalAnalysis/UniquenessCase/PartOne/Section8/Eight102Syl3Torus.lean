module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Syl3Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial CFSG.Open

variable {p f : ℕ} {K : Type} [Field K]

private theorem bar_apply_eq_self (h : UnitaryFieldData p f K) {m : ℕ}
    (hm : m ∣ p ^ f - 1) {a : Kˣ} (ha : a ^ m = 1) : h.bar (a : K) = (a : K) := by
  obtain ⟨c, hc⟩ := hm
  have hq : p ^ f = m * c + 1 := by
    have hqpos : 0 < p ^ f := pow_pos h.prime.pos f
    calc p ^ f = p ^ f - 1 + 1 := (Nat.sub_add_cancel (Nat.succ_le_of_lt hqpos)).symm
      _ = m * c + 1 := by rw [hc]
  have hpow : a ^ (p ^ f) = a := by
    calc a ^ (p ^ f) = a ^ (m * c + 1) := by rw [hq]
      _ = a ^ (m * c) * a := pow_succ _ _
      _ = (a ^ m) ^ c * a := by rw [pow_mul]
      _ = 1 ^ c * a := by rw [ha]
      _ = a := by simp
  have hval : (a : K) ^ (p ^ f) = (a : K) := by
    simpa [Units.val_pow_eq_pow_val] using congrArg Units.val hpow
  rw [h.bar_apply, hval]

private theorem torusRatio_one_of_roots (h : UnitaryFieldData p f K) {r ε m : ℕ}
    (hm : m ∣ p ^ f - 1) {a : Fin r → Kˣ} (ha : ∀ i, a i ^ m = 1) :
    torusRatio h a (1 : Fin ε → Kˣ) = 1 := by
  rw [torusRatio]
  have hprod : (∏ i, (a i : K) / h.bar (a i)) = 1 := by
    refine Finset.prod_eq_one fun i _ => ?_
    rw [bar_apply_eq_self h hm (ha i), div_self (a i).ne_zero]
  rw [hprod]
  simp

private theorem card_rootsOfUnity_of_dvd_unitary (h : UnitaryFieldData p f K) {m : ℕ}
    (hm : m ∣ p ^ f - 1) : Nat.card (rootsOfUnity m K) = m := by
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [zero_dvd_iff] at hm
    have hq : 0 < p ^ f - 1 := by
      have hf0 : f ≠ 0 := by
        have := h.one_le
        omega
      have hlt : 1 < p ^ f := Nat.one_lt_pow hf0 h.prime.one_lt
      omega
    omega
  have hdvd : m ∣ Nat.card K - 1 := by
    rw [h.card]
    have hdiv : p ^ f - 1 ∣ p ^ (2 * f) - 1 := by
      have h := Nat.sub_dvd_pow_sub_pow (p ^ f) 1 2
      rw [one_pow, ← pow_mul, Nat.mul_comm f 2] at h
      exact h
    exact dvd_trans hm hdiv
  exact @CFSG.LinearGroups.card_rootsOfUnity_of_dvd K _ h.finite m ⟨hm0⟩ hdvd

private theorem exists_torusPow_equiv (h : UnitaryFieldData p f K) (r ε : ℕ) {m : ℕ}
    (hm : m ∣ p ^ f - 1) :
    Nonempty ((Fin r → rootsOfUnity m K) ≃ torusPow h r ε m) := by
  classical
  let hex : ∀ ζ : Fin r → rootsOfUnity m K,
      ∃ g ∈ hypTorus h r ε,
        (((g : GL (HypIndex r ε) K) : Matrix (HypIndex r ε) (HypIndex r ε) K) =
          diagonal (torusEntries h (fun i => (ζ i : Kˣ)) 1)) := fun ζ =>
    torusMat_mem_hypSU h (fun i => (ζ i : Kˣ)) (d := 1)
      (by intro k; simp [UnitaryFieldData.norm])
      (torusRatio_one_of_roots h hm fun i => (ζ i).2)
  let f : (Fin r → rootsOfUnity m K) → torusPow h r ε m := fun ζ =>
    ⟨Classical.choose (hex ζ), by
      exact ⟨fun i => (ζ i : Kˣ), fun i => (ζ i).2,
        (Classical.choose_spec (hex ζ)).2⟩⟩
  have hfmat : ∀ ζ : Fin r → rootsOfUnity m K,
      (((f ζ : torusPow h r ε m) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
        diagonal (torusEntries h (fun i => (ζ i : Kˣ)) 1) := by
    intro ζ
    dsimp [f]
    exact (Classical.choose_spec (hex ζ)).2
  have hinj : Function.Injective f := by
    intro ζ ζ' hζ
    funext i
    have h1 : ((ζ i : Kˣ) : K) = ((ζ' i : Kˣ) : K) := by
      have hmat : (((f ζ : torusPow h r ε m) : GL (HypIndex r ε) K) :
          Matrix (HypIndex r ε) (HypIndex r ε) K) =
          (((f ζ' : torusPow h r ε m) : GL (HypIndex r ε) K) :
            Matrix (HypIndex r ε) (HypIndex r ε) K) := by
        rw [hζ]
      have h := congrFun (congrFun hmat (Sum.inl i)) (Sum.inl i)
      rw [hfmat ζ, hfmat ζ'] at h
      simpa [torusEntries, Matrix.diagonal_apply_eq] using h
    exact Subtype.ext (Units.ext h1)
  have hsurj : Function.Surjective f := by
    intro x
    obtain ⟨a, ha, hx⟩ := mem_torusPow.mp x.2
    refine ⟨fun i => ⟨a i, ha i⟩, ?_⟩
    apply Subtype.ext
    apply Subtype.ext
    apply Units.ext
    rw [hfmat, hx]
  exact ⟨Equiv.ofBijective f ⟨hinj, hsurj⟩⟩

theorem pow_eq_one_of_mem_torusPow {h : UnitaryFieldData p f K} {r ε m : ℕ} {g : hypSU h r ε}
    (hg : g ∈ torusPow h r ε m) : g ^ m = 1 := by
  obtain ⟨a, ha, hmat⟩ := hg
  apply Subtype.ext
  apply Units.ext
  change (((g ^ m : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = 1
  rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hmat, diagonal_pow, ← diagonal_one]
  congr 1
  funext x
  rcases x with i | k | i
  · simpa [torusEntries, Units.val_pow_eq_pow_val] using congrArg Units.val (ha i)
  · simp [torusEntries]
  · have haK : (a i : K) ^ m = 1 := by
      simpa [Units.val_pow_eq_pow_val] using congrArg Units.val (ha i)
    have hbarm : (h.bar (a i : K)) ^ m = 1 := by
      rw [← map_pow, haK, map_one]
    simp [torusEntries, inv_pow, hbarm]

theorem mem_torusPow_of_pow_eq_one {h : UnitaryFieldData p f K} {r ε m k : ℕ}
    {g : hypSU h r ε} (hg : g ∈ torusPow h r ε m) (hk : g ^ k = 1) : g ∈ torusPow h r ε k := by
  obtain ⟨a, ha, hmat⟩ := hg
  refine ⟨a, fun i => Units.ext ?_, hmat⟩
  have hdiag : (((g ^ k : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) =
      diagonal (fun x => torusEntries h a (1 : Fin ε → Kˣ) x ^ k) := by
    rw [SubgroupClass.coe_pow, Units.val_pow_eq_pow_val, hmat, diagonal_pow]
    congr 1
  have hmatk : (((g ^ k : hypSU h r ε) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) = 1 := by
    rw [hk]
    simp
  have hentry : (torusEntries h a (1 : Fin ε → Kˣ) (Sum.inl i)) ^ k = 1 := by
    have h := congrFun (congrFun hdiag (Sum.inl i)) (Sum.inl i)
    rw [hmatk] at h
    simpa [torusEntries, Matrix.diagonal_apply_eq] using h.symm
  simpa [torusEntries, Units.val_pow_eq_pow_val, Units.val_one] using hentry

theorem torusPow_le_of_dvd (h : UnitaryFieldData p f K) (r ε : ℕ) {m k : ℕ} (hmk : m ∣ k) :
    torusPow h r ε m ≤ torusPow h r ε k := by
  intro g hg
  obtain ⟨c, rfl⟩ := hmk
  rw [mem_torusPow] at hg ⊢
  obtain ⟨a, ha, hmat⟩ := hg
  exact ⟨a, fun i => by rw [pow_mul, ha i, one_pow], hmat⟩

theorem isElemAbelian_torusPow (h : UnitaryFieldData p f K) (r ε m : ℕ) :
    IsElemAbelian m (torusPow h r ε m) := by
  refine ⟨?_, fun x hx => pow_eq_one_of_mem_torusPow hx⟩
  refine IsMulCommutative.of_comm fun x y => ?_
  apply Subtype.ext
  apply Subtype.ext
  apply Units.ext
  change (((x : torusPow h r ε m) : GL (HypIndex r ε) K) :
      Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (((y : torusPow h r ε m) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) =
      (((y : torusPow h r ε m) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K) *
      (((x : torusPow h r ε m) : GL (HypIndex r ε) K) :
        Matrix (HypIndex r ε) (HypIndex r ε) K)
  obtain ⟨a, ha, hx⟩ := mem_torusPow.mp x.2
  obtain ⟨b, hb, hy⟩ := mem_torusPow.mp y.2
  rw [hx, hy, diagonal_mul_diagonal, diagonal_mul_diagonal]
  congr 1
  funext i
  exact mul_comm _ _

theorem card_torusPow (h : UnitaryFieldData p f K) (r ε : ℕ) {m : ℕ} (hm : m ∣ p ^ f - 1) :
    Nat.card (torusPow h r ε m) = m ^ r := by
  obtain ⟨e⟩ := exists_torusPow_equiv h r ε hm
  calc Nat.card (torusPow h r ε m) = Nat.card (Fin r → rootsOfUnity m K) :=
        (Nat.card_congr e).symm
    _ = Nat.card (rootsOfUnity m K) ^ r := by
        rw [Nat.card_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    _ = m ^ r := by rw [card_rootsOfUnity_of_dvd_unitary h hm]

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Syl3

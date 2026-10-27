module

public import CFSG.RankThree.PartOne.KE.EDualStabilizer
public import CFSG.RankThree.PartOne.KE.CTTorusFixed

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.E6 (charVal charVal_single charVal_smul charVal_mulVec)
open scoped Matrix

theorem rootChar_ne_one_of_column_regular {τ : Tag} {L : Type} [Field L]
    (M : Matrix (Fin τ.rank) (Fin τ.rank) ℤ) (Fr : L →+* L) {q : ℕ} (hFr : ∀ c, Fr c = c ^ q)
    {p : ℕ} (hp : p.Prime) {a : Fin τ.rank → Lˣ} (ha : a ∈ fixedCharTuples M Fr)
    (hap : ∀ i, a i ^ p = 1) (ha1 : a ≠ 1)
    (hreg : ∀ z : Fin τ.rank → ZMod p, z ≠ 0 →
      ((M.map (Int.cast : ℤ → ZMod p)).transpose).mulVec z = (q : ZMod p) • z →
      ∀ α : Fin τ.rank → ℤ, IsRoot τ α → charVal z α ≠ 0)
    {α : Fin τ.rank → ℤ} (hα : IsRoot τ α) : rootChar a α ≠ 1 := by
  classical
  have : NeZero p := ⟨hp.ne_zero⟩
  obtain ⟨i0, hi0⟩ : ∃ i, a i ≠ 1 := by
    by_contra h
    exact ha1 (funext fun i => not_not.1 fun hi => h ⟨i, hi⟩)
  have hord : orderOf (a i0) = p := by
    rcases (Nat.dvd_prime hp).1 (orderOf_dvd_of_pow_eq_one (hap i0)) with h | h
    · exact absurd (orderOf_eq_one_iff.1 h) hi0
    · exact h
  have hprim : IsPrimitiveRoot ((a i0 : Lˣ) : L) p :=
    IsPrimitiveRoot.coe_units_iff.2 (IsPrimitiveRoot.iff_orderOf.2 hord)
  have hexp : ∀ i, ∃ n : ℕ, a i = (a i0) ^ n := fun i => by
    have hi : ((a i : Lˣ) : L) ^ p = 1 := by
      rw [← Units.val_pow_eq_pow_val, hap i, Units.val_one]
    obtain ⟨n, -, hn⟩ := hprim.eq_pow_of_pow_eq_one hi
    exact ⟨n, Units.ext (by rw [Units.val_pow_eq_pow_val]; exact hn.symm)⟩
  choose e he using hexp
  have hz0 : (fun i => (e i : ZMod p) : Fin τ.rank → ZMod p) ≠ 0 := by
    intro h0
    have h1 : (e i0 : ZMod p) = 0 := congrFun h0 i0
    obtain ⟨k, hk⟩ := (ZMod.natCast_eq_zero_iff _ p).1 h1
    apply hi0
    calc a i0 = (a i0) ^ e i0 := he i0
      _ = 1 := by rw [hk, pow_mul, hap i0, one_pow]
  have hfix : ∀ y : Fin τ.rank → ℤ, charVal (fun i => (e i : ZMod p)) (M *ᵥ y) =
      (q : ZMod p) * charVal (fun i => (e i : ZMod p)) y := by
    intro y
    have h1 : rootChar a (M *ᵥ y) = rootChar a ((q : ℤ) • y) := by
      rw [ha y, CTTorus.map_units_eq_pow hFr, rootChar_zsmul, zpow_natCast]
    have h2 := (rootChar_eq_rootChar_iff hord e a he (M *ᵥ y) ((q : ℤ) • y)).1 h1
    rw [charVal_smul] at h2
    simpa using h2
  have heig : ((M.map (Int.cast : ℤ → ZMod p)).transpose).mulVec (fun i => (e i : ZMod p)) =
      (q : ZMod p) • (fun i => (e i : ZMod p)) := by
    funext j
    have h1 := hfix (Pi.single j 1)
    rw [← charVal_mulVec] at h1
    simp only [charVal_single] at h1
    simpa using h1
  intro h1
  refine hreg _ hz0 heig α hα ?_
  have h3 := (rootChar_eq_rootChar_iff hord e a he α 0).1 (by rw [h1, rootChar_zero])
  simpa [charVal] using h3

end CFSG.RankThree.PartOne.KE

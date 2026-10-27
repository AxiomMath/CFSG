module

public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOneBasic
public import CFSG.RankThree.PartOne.KC.OrthogonalQPlusOnePlanes
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalComponentFacts

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal

section Restrict

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V} {p : ℕ}

@[expose] noncomputable def restrictHom (Ã : Subgroup (orthDerived Q)) (W : Submodule K V)
    (hinv : ∀ y : Ã, ∀ w ∈ W, (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) w ∈ W) :
    Ã →* (W ≃ₗ[K] W) :=
  MonoidHom.mk' (fun y => restrictEquiv W (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V)
    (hinv y) (hinv y⁻¹)) fun y y' => by
    refine LinearEquiv.ext fun w => Subtype.ext ?_
    rfl

theorem coe_restrictHom (Ã : Subgroup (orthDerived Q)) (W : Submodule K V)
    (hinv : ∀ y : Ã, ∀ w ∈ W, (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) w ∈ W) (y : Ã) (w : W) :
    ((restrictHom Ã W hinv y w : W) : V) = (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) (w : V) :=
  rfl

theorem pow_apply_plane {W : Type} [AddCommGroup W] [Module K W] {E : Type} [Field E]
    [Algebra K E] {β : W ≃ₗ[K] W} {ζ : E} {s : ℕ} (φ : E →ₗ[K] W)
    (hφ : ∀ z, β (φ z) = φ (ζ ^ s * z)) (n : ℕ) (z : E) :
    (β ^ n) (φ z) = φ (ζ ^ (s * n) * z) := by
  induction n generalizing z with
  | zero => simp
  | succ n ih =>
    rw [pow_succ, LinearEquiv.mul_apply, hφ, ih, ← mul_assoc, ← pow_add, mul_add, mul_one]

end Restrict

section Sector

variable {K V : Type} [Field K] [Finite K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ}

theorem exists_sector_planes (hp : p.Prime) (hp3 : 3 < p) (hpl : p ≠ ringChar K)
    (hpq : p ∣ Nat.card K + 1) (Ã : Subgroup (orthDerived Q)) [IsMulCommutative Ã]
    (hcard : Nat.card Ã = p ^ 2) (hpow : ∀ x ∈ Ã, x ^ p = 1) (M : Subgroup Ã)
    (hM : Nat.card M = p) (W : Submodule K V)
    (hW : (polarBilin (Q.comp W.subtype)).Nondegenerate)
    (hMW : ∀ y ∈ M, ∀ w ∈ W, (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) w = w)
    (hinv : ∀ y : Ã, ∀ w ∈ W, (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) w ∈ W)
    (hfix : ∀ w ∈ W, (∀ y : Ã, (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) w = w) → w = 0)
    {E : Type} [Field E] [Algebra K E] (hE : finrank K E = 2) {ζ : E} (hζ : orderOf ζ = p) :
    ∃ (ι : Type) (_ : Fintype ι) (φ : ι → E →ₗ[K] V) (χ : ι → Ã →* Multiplicative (ZMod p)),
      (∀ i, Function.Injective (φ i)) ∧
      (∀ i z, algebraMap K E (Q (φ i z)) = z * z ^ Nat.card K) ∧
      (∀ i z, φ i z ∈ W) ∧ (∀ i j, i ≠ j → ∀ z w, polar Q (φ i z) (φ j w) = 0) ∧
      (∀ i z, (∀ w, polar Q (φ i z) (φ i w) = 0) → z = 0) ∧
      (⨆ i, LinearMap.range (φ i)) = W ∧
      (∀ i (y : Ã) z, (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) (φ i z) =
        φ i (ζ ^ (χ i y).toAdd.val * z)) ∧
      (∀ i (y : Ã), χ i y = 1 ↔ y ∈ M) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  by_cases hW0 : W = ⊥
  · exact ⟨Empty, inferInstance, nofun, nofun, nofun, nofun, nofun, nofun, nofun, by simp [hW0],
      nofun, nofun⟩
  obtain ⟨b, hb⟩ : ∃ b : Ã, b ∉ M := by
    by_contra hcon
    push Not at hcon
    have hMtop : M = ⊤ := eq_top_iff.mpr fun x _ => hcon x
    have hc : Nat.card M = Nat.card Ã := by rw [hMtop, Subgroup.card_top]
    rw [hM, hcard, pow_two] at hc
    have : p * 1 = p * p := by rw [mul_one]; exact hc
    have := Nat.eq_of_mul_eq_mul_left hp.pos this
    exact hp.one_lt.ne this
  set ρ := restrictHom Ã W hinv with hρdef
  have hρM : ∀ y ∈ M, ρ y = 1 := fun y hy =>
    LinearEquiv.ext fun w => Subtype.ext (hMW y hy w w.2)
  have hbG : ∀ y : Ã, ∃ n : ℤ, ρ y = ρ b ^ n := fun y => by
    obtain ⟨n, m, hm, rfl⟩ := exists_zpow_mul_of_card hp hcard hM hb y
    exact ⟨n, by rw [map_mul, map_zpow, hρM m hm, mul_one]⟩
  have hbp : b ^ p = 1 := Subtype.ext (hpow b b.2)
  have hρbp : ρ b ^ p = 1 := by rw [← map_pow, hbp, map_one]
  obtain ⟨w₀, hw₀, hw₀0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hW0
  have hρb1 : ρ b ≠ 1 := by
    intro h1
    apply hw₀0
    refine hfix w₀ hw₀ fun y => ?_
    obtain ⟨n, hn⟩ := hbG y
    have h2 : ((ρ y ⟨w₀, hw₀⟩ : W) : V) = (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) w₀ :=
      coe_restrictHom Ã W hinv y ⟨w₀, hw₀⟩
    rw [← h2, hn, h1]
    simp
  have hord : orderOf (ρ b) = p := orderOf_eq_prime hρbp hρb1
  obtain ⟨k, hk⟩ := exists_zmod_char ρ b hbG hord
  have hρy : ∀ (y : Ã) (w : W),
      ((ρ y w : W) : V) = (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) (w : V) := fun y w =>
    coe_restrictHom Ã W hinv y w
  have hβ : OddOrderIsometry (Q.comp W.subtype) p (ρ b) := by
    refine ⟨?_, hρbp, ?_, fun v hv => hW.1 v fun w => by simpa using hv w⟩
    · rw [TauCeti.QuadraticMap.mem_orthogonalGroup_iff]
      intro w
      show Q ((ρ b w : W) : V) = Q (w : V)
      rw [hρy]
      exact TauCeti.QuadraticMap.mem_orthogonalGroup_iff.mp
        (orthDerived_le_orthogonalGroup (b : orthDerived Q).2) _
    · intro h0
      have h1 := (ringChar.spec K p).mp h0
      have hℓ : (ringChar K).Prime := CharP.char_is_prime K _
      rcases (Nat.dvd_prime hp).mp h1 with h2 | h2
      · exact hℓ.one_lt.ne' h2
      · exact hpl h2.symm
  have hfixβ : ∀ w : W, ρ b w = w → w = 0 := by
    intro w hw
    apply Subtype.ext
    refine hfix w w.2 fun y => ?_
    have hpw : ∀ n : ℕ, (ρ b ^ n) w = w := fun n => by
      induction n with
      | zero => simp
      | succ n ih => rw [pow_succ, LinearEquiv.mul_apply, hw, ih]
    rw [← hρy, hk y, hpw]
  obtain ⟨ι, hι, φ', s, hs0, hinj, hnorm, horth, hact, hspan, hreg⟩ :=
    hβ.exists_plane_family hp hp3 hpq hfixβ hE hζ
  let χ : ι → Ã →* Multiplicative (ZMod p) := fun i =>
    (AddMonoidHom.mulLeft (s i)).toMultiplicative.comp k
  have hχ : ∀ i y, (χ i y).toAdd = s i * (k y).toAdd := fun i y => rfl
  refine ⟨ι, hι, fun i => W.subtype ∘ₗ φ' i, χ, fun i => Subtype.val_injective.comp (hinj i),
    fun i z => hnorm i z, fun i z => (φ' i z).2, fun i j hij z w => ?_, fun i z hz => ?_, ?_, ?_,
    ?_⟩
  · have := horth i j hij z w
    rw [polar_comp_subtype_eq] at this
    exact this
  · refine hreg i z fun w => ?_
    rw [polar_comp_subtype_eq]
    exact hz w
  · have h1 : (⨆ i, LinearMap.range (W.subtype ∘ₗ φ' i)) =
        Submodule.map W.subtype (⨆ i, LinearMap.range (φ' i)) := by
      rw [Submodule.map_iSup]
      exact iSup_congr fun i => LinearMap.range_comp _ _
    show (⨆ i, LinearMap.range (W.subtype ∘ₗ φ' i)) = W
    rw [h1, hspan, Submodule.map_top, Submodule.range_subtype]
  · intro i y z
    show (((y : Ã) : orthDerived Q) : V ≃ₗ[K] V) ((φ' i z : W) : V) =
      ((φ' i (ζ ^ (χ i y).toAdd.val * z) : W) : V)
    rw [← hρy, hk y, pow_apply_plane (φ' i) (hact i) (k y).toAdd.val z]
    congr 3
    rw [hχ, ZMod.val_mul]
    have h := pow_mod_orderOf ζ ((s i).val * (k y).toAdd.val)
    rw [hζ] at h
    exact h.symm
  · intro i y
    have hχy : (χ i y).toAdd = s i * (k y).toAdd := hχ i y
    constructor
    · intro h1
      have h2 : s i * (k y).toAdd = 0 := by rw [← hχy, h1]; rfl
      have h3 : (k y).toAdd = 0 := (mul_eq_zero.mp h2).resolve_left (hs0 i)
      obtain ⟨n, m, hm, hy⟩ := exists_zpow_mul_of_card hp hcard hM hb y
      have h4 : ρ b ^ n = 1 := by
        have h5 : ρ y = 1 := by rw [hk y, h3]; simp
        rw [hy, map_mul, map_zpow, hρM m hm, mul_one] at h5
        exact h5
      have h6 : (p : ℤ) ∣ n := by
        have := orderOf_dvd_iff_zpow_eq_one.mpr h4
        rwa [hord] at this
      have h7 : b ^ n = 1 := by
        have : (orderOf b : ℤ) ∣ n :=
          (Int.natCast_dvd_natCast.mpr (orderOf_dvd_of_pow_eq_one hbp)).trans h6
        exact orderOf_dvd_iff_zpow_eq_one.mp this
      rw [hy, h7, one_mul]
      exact hm
    · intro hyM
      have h1 : ρ b ^ (k y).toAdd.val = 1 := by rw [← hk y]; exact hρM y hyM
      have h2 : p ∣ (k y).toAdd.val := by
        have := orderOf_dvd_of_pow_eq_one h1
        rwa [hord] at this
      have h3 : (k y).toAdd.val = 0 := Nat.eq_zero_of_dvd_of_lt h2 (ZMod.val_lt _)
      have h4 : (k y).toAdd = 0 := (ZMod.val_eq_zero _).mp h3
      exact toAdd_eq_zero.mp (by rw [hχy, h4, mul_zero])

end Sector

end CFSG.RankThree.PartOne.KCOrthogonal

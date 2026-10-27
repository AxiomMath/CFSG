module

public import CFSG.RankThree.PartOne.N143.TorusLift
public import CFSG.RankThree.Classical2.UnitarySplitPrimeRank

public section

namespace CFSG.RankThree.PartOne.N143

open Matrix CFSG.Assembly CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.Classical2
  CFSG.LocalAnalysis.ComponentInitial CFSG.SectionRank.OddCover CFSG.RankThree.Classical
open CFSG.Assembly.RankThreeEven (localRank)

variable {ℓ f : ℕ} {K : Type} [Field K]

theorem succ_le_localRank_unitary_even (hK : UnitaryFieldData ℓ f K) (hℓ2 : ℓ = 2)
    (hpq : 3 ∣ ℓ ^ f + 1) {Y : Type} [Group Y] [Finite Y] {r n : ℕ} (hn : r + 3 = n)
    (φ : Y →* unitaryPSU hK n) (hφ : Function.Surjective φ)
    (hker : φ.ker ≤ Subgroup.center Y) (h3 : 3 ∣ Nat.card φ.ker) : r + 1 ≤ localRank 3 Y := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hchar : CharP K 2 := hℓ2 ▸ hK.charP
  have h2K : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
  have hneg : (-1 : K) = 1 := by linear_combination -h2K
  obtain ⟨ζ, hζ, hζN⟩ := exists_orderOf_eq_norm_one hK Nat.prime_three hpq
  have hζp : ζ ^ 3 = 1 := hζ ▸ pow_orderOf_eq_one ζ
  let pos : Fin r → Fin n := fun j => ⟨j.val + 2, by omega⟩
  let L : Fin n := ⟨r + 2, by omega⟩
  have hpos_inj : Function.Injective pos := fun j j' h => by
    simp only [pos, Fin.ext_iff] at h
    exact Fin.ext (by omega)
  have hposL : ∀ j, pos j ≠ L := fun j h => by
    simp only [pos, L, Fin.ext_iff] at h
    have := j.isLt
    omega
  set c : Fin r → Fin n → Kˣ := fun j i =>
    if i = pos j then ζ else if i = L then ζ⁻¹ else 1 with hcdef
  have hcp : ∀ j i, c j i ^ 3 = 1 := by
    intro j i
    simp only [hcdef]
    split_ifs
    · exact hζp
    · rw [inv_pow, hζp, inv_one]
    · exact one_pow 3
  have hcnorm : ∀ j i, c j i ^ (ℓ ^ f + 1) = 1 := by
    intro j i
    simp only [hcdef]
    split_ifs
    · exact hζN
    · rw [inv_pow, hζN, inv_one]
    · exact one_pow _
  have hcpos : ∀ j j', c j (pos j') = if j = j' then ζ else 1 := by
    intro j j'
    simp only [hcdef]
    by_cases h : j = j'
    · subst h
      simp
    · have : pos j' ≠ pos j := fun hh => h (hpos_inj hh).symm
      simp [this, hposL j', h]
  have hcL : ∀ j, c j L = ζ⁻¹ := by
    intro j
    simp only [hcdef]
    have : L ≠ pos j := fun hh => hposL j hh.symm
    simp [this]
  have hcother : ∀ j i, i ≠ pos j → i ≠ L → c j i = 1 := by
    intro j i h1 h2
    simp [hcdef, h1, h2]
  have hcprod : ∀ j, ∏ i, c j i = 1 := by
    intro j
    rw [Fintype.prod_eq_mul (pos j) L (hposL j) (fun x hx => hcother j x hx.1 hx.2),
      hcpos j j, hcL j]
    simp
  have hpriv : ∀ j, ∃ i, (∀ j', j' ≠ j → c j' i = 1) ∧ orderOf (c j i) = 3 := by
    intro j
    refine ⟨pos j, fun j' hj' => ?_, ?_⟩
    · simp [hcpos, hj']
    · simp [hcpos, hζ]
  have hswapS : ∀ a b : Fin n, permGL (Equiv.swap a b) ∈ unitarySU ℓ f K n := by
    intro a b
    rw [mem_unitarySU_iff hK]
    refine ⟨?_, permGL_unitary hK _⟩
    rw [det_permGL]
    rcases eq_or_ne a b with rfl | hab
    · rw [Equiv.swap_self, Equiv.Perm.sign_refl]
      simp
    · rw [Equiv.Perm.sign_swap hab]
      simp [hneg]
  have hcswap : ∀ j j' : Fin r, c j ∘ (Equiv.swap (pos j) (pos j')).symm = c j' := by
    intro j j'
    funext i
    rw [Function.comp_apply, Equiv.symm_swap]
    by_cases h1 : i = pos j
    · subst h1
      rw [Equiv.swap_apply_left, hcpos, hcpos]
      by_cases hjj : j = j'
      · subst hjj; simp
      · simp [hjj, Ne.symm hjj]
    by_cases h2 : i = pos j'
    · subst h2
      rw [Equiv.swap_apply_right, hcpos, hcpos]
      simp
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2]
      by_cases h3 : i = L
      · subst h3
        rw [hcL, hcL]
      · rw [hcother j i h1 h3, hcother j' i h2 h3]
  have hcinv : ∀ j, c j ∘ (Equiv.swap (pos j) L).symm = fun i => (c j i)⁻¹ := by
    intro j
    funext i
    rw [Function.comp_apply, Equiv.symm_swap]
    by_cases h1 : i = pos j
    · subst h1
      rw [Equiv.swap_apply_left, hcL, hcpos]; simp
    by_cases h2 : i = L
    · subst h2
      rw [Equiv.swap_apply_right, hcL, hcpos]; simp
    · rw [Equiv.swap_apply_of_ne_of_ne h1 h2, hcother j i h1 h2, inv_one]
  have hcS : ∀ a, diagHom n (expHom (p := 3) c hcp a) ∈ unitarySU ℓ f K n :=
    diagHom_expHom_mem_unitarySU hK c hcp hcprod hcnorm
  have hinj : Function.Injective (expHom (p := 3) c hcp) := expHom_injective c hcp hpriv
  set S := unitarySU ℓ f K n with hSdef
  set E := expHom (p := 3) c hcp with hEdef
  let δ : Multiplicative (Fin r → ZMod 3) →* S := ((diagHom n).comp E).codRestrict S hcS
  have hδ : ∀ a, (δ a : GL (Fin n) K) = diagHom n (E a) := fun a => rfl
  let θ : Multiplicative (Fin r → ZMod 3) →* unitaryPSU hK n := (unitaryProj hK n).comp δ
  have hθsingle : ∀ j, (δ (Multiplicative.ofAdd (Pi.single j 1)) : GL (Fin n) K) =
      diagHom n (c j) := fun j => by rw [hδ, hEdef, expHom_single]
  have hθinj : Function.Injective θ := by
    rw [injective_iff_map_eq_one]
    intro a ha
    have hmem : δ a ∈ unitaryScalars hK n := by
      rw [← ker_unitaryProj hK n]
      exact ha
    obtain ⟨c', -, hcn, hc⟩ := mem_unitaryScalars.mp hmem
    have h0 : (⟨0, by omega⟩ : Fin n) ≠ L := by simp [L, Fin.ext_iff]
    have hc0 : ∀ j, c j ⟨0, by omega⟩ = 1 := fun j =>
      hcother j _ (fun h => by simp [pos, Fin.ext_iff] at h) h0
    have hE0 : E a ⟨0, by omega⟩ = 1 := by
      rw [hEdef, expHom_apply]
      simp [hc0]
    have h1 := congrArg (fun g : GL (Fin n) K => (g : Matrix (Fin n) (Fin n) K) ⟨0, by omega⟩
      ⟨0, by omega⟩) (hc.symm.trans (hδ a))
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply, coe_diagHom,
      Matrix.diagonal_apply_eq, hE0, Units.val_one] at h1
    have hc1 : c' = 1 := Units.ext h1
    have h2 : E a = 1 := by
      apply diagHom_injective n
      rw [← hδ a, hc, hc1, map_one, map_one]
    exact hinj (h2.trans (map_one E).symm)
  have hθS : ∀ (w : GL (Fin n) K) (hw : w ∈ S) (a : Multiplicative (Fin r → ZMod 3))
      (e : Multiplicative (Fin r → ZMod 3)) (hwe : w * diagHom n (E a) * w⁻¹ = diagHom n (E e)),
      unitaryProj hK n ⟨w, hw⟩ * θ a * (unitaryProj hK n ⟨w, hw⟩)⁻¹ = θ e := by
    intro w hw a e hwe
    change unitaryProj hK n (⟨w, hw⟩ * δ a * ⟨w, hw⟩⁻¹) = unitaryProj hK n (δ e)
    congr 1
    apply Subtype.ext
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hδ, hδ]
    exact hwe
  have hswap : ∀ j j' : Fin r, j ≠ j' → ∃ w : unitaryPSU hK n,
      w * θ (Multiplicative.ofAdd (Pi.single j 1)) * w⁻¹ =
        θ (Multiplicative.ofAdd (Pi.single j' 1)) ∧
      w * θ (Multiplicative.ofAdd (Pi.single j' 1)) * w⁻¹ =
        θ (Multiplicative.ofAdd (Pi.single j 1)) := by
    intro j j' _
    refine ⟨unitaryProj hK n ⟨permGL (Equiv.swap (pos j) (pos j')), hswapS _ _⟩, ?_, ?_⟩
    · refine hθS _ (hswapS _ _) _ _ ?_
      rw [hEdef, expHom_single, expHom_single, permGL_mul_diagHom_mul_inv, hcswap]
    · refine hθS _ (hswapS _ _) _ _ ?_
      rw [hEdef, expHom_single, expHom_single, permGL_mul_diagHom_mul_inv, Equiv.swap_comm,
        hcswap]
  have hinv : ∀ j : Fin r, ∃ w : unitaryPSU hK n,
      w * θ (Multiplicative.ofAdd (Pi.single j 1)) * w⁻¹ =
        (θ (Multiplicative.ofAdd (Pi.single j 1)))⁻¹ := by
    intro j
    refine ⟨unitaryProj hK n ⟨permGL (Equiv.swap (pos j) L), hswapS _ _⟩, ?_⟩
    have hθinv : (θ (Multiplicative.ofAdd (Pi.single j 1)))⁻¹ =
        θ (Multiplicative.ofAdd (-(Pi.single j (1 : ZMod 3)))) := by
      rw [ofAdd_neg]
      exact (map_inv θ _).symm
    rw [hθinv]
    refine hθS _ (hswapS _ _) _ _ ?_
    have hEinv : E (Multiplicative.ofAdd (-(Pi.single j (1 : ZMod 3)))) = fun i => (c j i)⁻¹ := by
      have h1 : E (Multiplicative.ofAdd (-(Pi.single j (1 : ZMod 3)))) =
          (E (Multiplicative.ofAdd (Pi.single j (1 : ZMod 3))))⁻¹ := by
        rw [ofAdd_neg]
        exact map_inv E _
      rw [h1, hEdef, expHom_single]
      rfl
    rw [hEinv, hEdef, expHom_single, permGL_mul_diagHom_mul_inv, hcinv]
  have h01 : (⟨0, by omega⟩ : Fin n) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hz₀sc : ∀ c' : Kˣ, permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) ≠
      Matrix.GeneralLinearGroup.scalar (Fin n) c' := fun c' h =>
    permGL_not_mem_statedScalars (fun h' => h01 (Equiv.swap_eq_one_iff.mp h'))
      (show permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) ∈
        CFSG.Assembly.LowTwoRank.StatedScalars (Fin n) K from ⟨c', h.symm⟩)
  have hz₀2 : (permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩) : GL (Fin n) K) ^ 2 =
      1 := by
    rw [← map_pow, pow_two, Equiv.swap_mul_self, map_one]
  have hc01 : ∀ j i, c j (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩ i) = c j i := by
    intro j i
    have hp0 : (⟨0, by omega⟩ : Fin n) ≠ pos j := fun h => by simp [pos, Fin.ext_iff] at h
    have hp1 : (⟨1, by omega⟩ : Fin n) ≠ pos j := fun h => by simp [pos, Fin.ext_iff] at h
    have hL0 : (⟨0, by omega⟩ : Fin n) ≠ L := fun h => by simp [L, Fin.ext_iff] at h
    have hL1 : (⟨1, by omega⟩ : Fin n) ≠ L := fun h => by simp [L, Fin.ext_iff] at h
    by_cases hi0 : i = ⟨0, by omega⟩
    · subst hi0
      rw [Equiv.swap_apply_left, hcother j _ hp1 hL1, hcother j _ hp0 hL0]
    by_cases hi1 : i = ⟨1, by omega⟩
    · subst hi1
      rw [Equiv.swap_apply_right, hcother j _ hp1 hL1, hcother j _ hp0 hL0]
    · rw [Equiv.swap_apply_of_ne_of_ne hi0 hi1]
  have hz₀c : ∀ a, Commute (permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩))
      (diagHom n (E a)) := by
    intro a
    have h := permGL_mul_diagHom_mul_inv (K := K) (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩)
      (E a)
    have he : E a ∘ (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩).symm = E a := by
      funext i
      simp only [Function.comp_apply, Equiv.symm_swap, hEdef, expHom_apply, hc01]
    rw [he, mul_inv_eq_iff_eq_mul] at h
    exact h
  set z : unitaryPSU hK n :=
    unitaryProj hK n ⟨permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩), hswapS _ _⟩ with hz
  have hz1 : z ≠ 1 := by
    intro h
    have hmem : (⟨permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩), hswapS _ _⟩ : S) ∈
        unitaryScalars hK n := by
      rw [← ker_unitaryProj hK n]
      exact h
    obtain ⟨c', -, -, hc⟩ := mem_unitaryScalars.mp hmem
    exact hz₀sc c' hc
  have hz2 : z ^ 2 = 1 := by
    rw [hz, ← map_pow]
    have : (⟨permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩), hswapS _ _⟩ : S) ^ 2 =
        1 := Subtype.ext (by rw [Subgroup.coe_pow]; exact hz₀2)
    rw [this, map_one]
  have hzE : ∀ a, Commute z (θ a) := by
    intro a
    change Commute (unitaryProj hK n ⟨permGL (Equiv.swap (⟨0, by omega⟩ : Fin n) ⟨1, by omega⟩),
      hswapS _ _⟩) (unitaryProj hK n (δ a))
    refine Commute.map ?_ _
    exact Subtype.ext (hz₀c a).eq
  exact succ_le_localRank_of_torus hφ hker Nat.prime_three (by norm_num) h3 θ hθinj hswap hinv hz1
    hz2 hzE

end CFSG.RankThree.PartOne.N143

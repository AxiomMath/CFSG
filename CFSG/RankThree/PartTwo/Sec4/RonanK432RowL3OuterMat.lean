module

public import CFSG.RankThree.PartTwo.Sec4.RonanK432L3HardMat
public import CFSG.RankThree.PartTwo.Sec4.RonanK432RowTools
import CFSG.Quasithin.Background.A318PC4
import CFSG.RankThree.PartTwo.Sec4.LThreePiIrred

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK432

namespace L3Outer

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank

local notation "pmk" => Matrix.ProjGenLinGroup.mk

section Group

variable {G : Type*} [Group G]

theorem pow_conj_eq {w y s : G} (hs : ∀ g : G, g * s = s * g) (h : w * y * w⁻¹ = s * y) (k : ℕ) :
    w ^ k * y * (w ^ k)⁻¹ = s ^ k * y := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hc : Commute w s := hs w
    have hws : w * s ^ k = s ^ k * w := (hc.pow_right k).eq
    calc w ^ (k + 1) * y * (w ^ (k + 1))⁻¹ = w * (w ^ k * y * (w ^ k)⁻¹) * w⁻¹ := by
          rw [pow_succ']
          group
      _ = w * (s ^ k * y) * w⁻¹ := by rw [ih]
      _ = (w * s ^ k) * y * w⁻¹ := by group
      _ = (s ^ k * w) * y * w⁻¹ := by rw [hws]
      _ = s ^ k * (w * y * w⁻¹) := by group
      _ = s ^ (k + 1) * y := by rw [h, ← mul_assoc, ← pow_succ]

theorem mul_pow_three_eq {w y s : G} (hs : ∀ g : G, g * s = s * g) (h : w * y * w⁻¹ = s * y)
    (hw : w ^ 3 = 1) : (w * y) ^ 3 = y ^ 3 := by
  have h2 := pow_conj_eq hs h 2
  have h3 := pow_conj_eq hs h 3
  rw [hw, inv_one, mul_one, one_mul] at h3
  have hs3 : s ^ 3 = 1 := by
    have : s ^ 3 * y = 1 * y := by rw [one_mul, ← h3]
    exact mul_right_cancel this
  have hc : Commute y s := hs y
  have hsy : y * s ^ 2 = s ^ 2 * y := (hc.pow_right 2).eq
  have key : (w * y) ^ 3 =
      (w * y * w⁻¹) * (w ^ 2 * y * (w ^ 2)⁻¹) * (w ^ 3 * y * (w ^ 3)⁻¹) * w ^ 3 := by
    rw [pow_three']
    group
  rw [key, h, h2, hw]
  simp only [inv_one, one_mul, mul_one]
  calc s * y * (s ^ 2 * y) * y = s * (y * s ^ 2) * y * y := by group
    _ = s * (s ^ 2 * y) * y * y := by rw [hsy]
    _ = s ^ 3 * y ^ 3 := by simp only [pow_succ, pow_zero, one_mul, mul_assoc]
    _ = y ^ 3 := by rw [hs3, one_mul]

variable {Q : Type} [Group Q]

theorem hom_witness_of_conj_eq (φ : G →* Q) (hker : ∀ g, φ g = 1 → ∀ h, g * h = h * g)
    {w y s : G} (hs : φ s = 1) (h : w * y * w⁻¹ = s * y) (hnc : ¬ y * w = w * y) :
    (φ w * φ y) * φ y = φ y * (φ w * φ y) ∧ φ w * φ y ∉ Subgroup.zpowers (φ y) := by
  refine ⟨?_, ?_⟩
  · have hc := L3Hard.hom_commute_of_conj_eq φ h hs
    calc (φ w * φ y) * φ y = (φ y * φ w) * φ y := by rw [hc]
      _ = φ y * (φ w * φ y) := mul_assoc _ _ _
  · intro hmem
    have hw : φ w ∈ Subgroup.zpowers (φ y) :=
      (Subgroup.mul_mem_cancel_right _ (Subgroup.mem_zpowers (φ y))).mp hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hw
    have h1 : φ (w * (y ^ k)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
    have h2 := hker _ h1 y
    have hu : y * (y ^ k)⁻¹ = (y ^ k)⁻¹ * y := ((Commute.refl y).zpow_right k).inv_right.eq
    apply hnc
    have h3 : (w * y) * (y ^ k)⁻¹ = (y * w) * (y ^ k)⁻¹ := by
      calc (w * y) * (y ^ k)⁻¹ = w * (y * (y ^ k)⁻¹) := mul_assoc _ _ _
        _ = w * ((y ^ k)⁻¹ * y) := by rw [hu]
        _ = (w * (y ^ k)⁻¹) * y := (mul_assoc _ _ _).symm
        _ = y * (w * (y ^ k)⁻¹) := h2
        _ = (y * w) * (y ^ k)⁻¹ := (mul_assoc _ _ _).symm
    exact (mul_right_cancel h3).symm

end Group

section Matrix

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem coe_pow_three_eq_smul {g : GL (Fin 3) K} {u : Kˣ}
    (h : g ^ 3 = GeneralLinearGroup.scalar (Fin 3) u) :
    (g : Matrix (Fin 3) (Fin 3) K) ^ 3 = (u : K) • 1 := by
  rw [← Units.val_pow_eq_pow_val, h, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
    Matrix.smul_one_eq_diagonal]

theorem exists_witness_of_type_three (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (hxH : x ∈ glPi π 3 (p ^ f) K) (hx3 : x ^ 3 ∈ zPi π 3 (p ^ f) K)
    (hirr : ∀ W : Submodule K (Fin 3 → K), (∀ v ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) →
      W = ⊥ ∨ W = ⊤) :
    ∃ t ∈ slPi π 3 (p ^ f) K,
      (pmk t * pmk x * (pmk t)⁻¹) * pmk x = pmk x * (pmk t * pmk x * (pmk t)⁻¹) ∧
        pmk t * pmk x * (pmk t)⁻¹ ∉ Subgroup.zpowers (pmk x) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  obtain ⟨c, -, hc⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hx3
  have hcube := CFSG.Quasithin.A318P.not_cube_of_irreducible hτ hτ1
    (coe_pow_three_eq_smul hc.symm) hirr
  obtain ⟨y, ⟨z, hz, rfl⟩, -, -, hirry, -, -, w, hwL, hwo, hwC, hcent, -⟩ :=
    irreducible_case hK hq hτ hτ1 hxH hc.symm hcube
  have hzs : z ∈ StatedScalars (Fin 3) K := mem_statedScalars_of_mem_zPi hK hq hτ hτ1 hz
  have hz1 : pmk z = 1 := mk_eq_one_iff_mem_statedScalars.mpr hzs
  obtain ⟨ζ, -, hζ⟩ := exists_scalar_of_mem_zPi hK hq hτ hτ1 hz
  have hzH : z ∈ glPi π 3 (p ^ f) K := (Subgroup.mem_inf.mp ((zPi_eq hπ hq' hτ hτ1) ▸ hz)).1
  have hyH : x * z ∈ glPi π 3 (p ^ f) K := mul_mem hxH hzH
  have hy3 : (x * z) ^ 3 = GeneralLinearGroup.scalar (Fin 3) (c * ζ ^ 3) := by
    rw [(show Commute x z from commute_of_mem_statedScalars hzs x).mul_pow, ← hc, ← hζ,
      ← map_pow, ← map_mul]
  have hℓ := CFSG.Quasithin.A318P.not_cube_of_irreducible hτ hτ1 (coe_pow_three_eq_smul hy3) hirry
  have hwcm : w ∈ centMod (slPi π 3 (p ^ f) K) (x * z) := by
    rw [hcent]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers w)
  obtain ⟨-, s, hs, hwy⟩ := mem_centMod_iff_scalar.mp hwcm
  have hnc : ¬ (x * z) * w = w * (x * z) := fun h =>
    hwC (Subgroup.mem_inf.mpr ⟨hwL, Subgroup.mem_centralizer_singleton_iff.mpr h.symm⟩)
  have hw3 : w ^ 3 = 1 := by
    have := pow_orderOf_eq_one w
    rwa [hwo] at this
  have hwy3 : (w * (x * z)) ^ 3 = (x * z) ^ 3 :=
    mul_pow_three_eq (fun g => commute_of_mem_statedScalars hs g) hwy hw3
  obtain ⟨t, htL, hty⟩ := CFSG.Quasithin.A318P.exists_conj_slPi hK hq hyH
    (mul_mem (slPi_le_glPi hπ hwL) hyH) hℓ (coe_pow_three_eq_smul hy3)
    (coe_pow_three_eq_smul (hwy3.trans hy3))
  refine ⟨t, htL, ?_⟩
  have hconj : pmk t * pmk x * (pmk t)⁻¹ = pmk w * pmk x := by
    have := congrArg (pmk : GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K) hty
    simpa [map_mul, map_inv, hz1] using this
  obtain ⟨hc1, hn1⟩ := hom_witness_of_conj_eq
    (pmk : GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K)
    (fun g hg h => (commute_of_mem_statedScalars (mk_eq_one_iff_mem_statedScalars.mp hg) h).symm)
    (mk_eq_one_iff_mem_statedScalars.mpr hs) hwy hnc
  simp only [map_mul, hz1, mul_one] at hc1 hn1
  rw [hconj]
  exact ⟨hc1, hn1⟩

theorem exists_witness_of_ne_zPi (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {x : GL (Fin 3) K} (hxH : x ∈ glPi π 3 (p ^ f) K) (hxZ : x ∉ zPi π 3 (p ^ f) K)
    (hx3 : x ^ 3 ∈ zPi π 3 (p ^ f) K) :
    ∃ t ∈ slPi π 3 (p ^ f) K,
      (pmk t * pmk x * (pmk t)⁻¹) * pmk x = pmk x * (pmk t * pmk x * (pmk t)⁻¹) ∧
        pmk t * pmk x * (pmk t)⁻¹ ∉ Subgroup.zpowers (pmk x) := by
  by_cases hirr : ∀ W : Submodule K (Fin 3 → K),
      (∀ v ∈ W, (x : Matrix (Fin 3) (Fin 3) K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤
  · exact exists_witness_of_type_three hK hq hxH hx3 hirr
  · exact L3Hard.exists_witness_of_not_type_three hK hq hxH hxZ hx3 fun h3 => hirr h3.2.2

end Matrix

theorem not_autWeaklyClosed_of_hom_witness {S : Type} [Group S] {G Q : Type} [Group G] [Group Q]
    (c : G →* MulAut S) (φ : G →* Q) (hker : ∀ g, c g = 1 ↔ φ g = 1) {x t : G}
    (hinner : c t ∈ (MulAut.conj : S →* MulAut S).range)
    (hc : (φ t * φ x * (φ t)⁻¹) * φ x = φ x * (φ t * φ x * (φ t)⁻¹))
    (hn : φ t * φ x * (φ t)⁻¹ ∉ Subgroup.zpowers (φ x)) : ¬ AutWeaklyClosed (c x) := by
  obtain ⟨s, hs⟩ := hinner
  have hconj : MulAut.conj s * c x * (MulAut.conj s)⁻¹ = c (t * x * t⁻¹) := by
    rw [hs, map_mul, map_mul, map_inv]
  have hcongr : ∀ a b : G, φ a = φ b → c a = c b := fun a b h => by
    have h1 : c (a * b⁻¹) = 1 := (hker _).mpr (by rw [map_mul, map_inv, h, mul_inv_cancel])
    rw [map_mul, map_inv, mul_inv_eq_one] at h1
    exact h1
  refine not_autWeaklyClosed_of_commute_conj (x := s) ?_ ?_
  · rw [hconj, ← map_mul, ← map_mul]
    refine hcongr _ _ ?_
    simp only [map_mul, map_inv]
    exact hc
  · rw [hconj]
    intro hmem
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    apply hn
    refine Subgroup.mem_zpowers_iff.mpr ⟨k, ?_⟩
    have h1 : c (x ^ k * (t * x * t⁻¹)⁻¹) = 1 := by
      rw [map_mul, map_inv, map_zpow, hk, mul_inv_cancel]
    have h2 := (hker _).mp h1
    rw [map_mul, map_inv, map_zpow, mul_inv_eq_one] at h2
    simpa [map_mul, map_inv] using h2

section Diagonal

variable {K : Type} [Field K] {p f : ℕ} {π : Bool}

theorem not_autWeaklyClosed_of_diagonal (hK : PiField π p f K) (hq : ModThree π (p ^ f))
    {S : Type} [Group S] {G : Type} [Group G] (c : G →* MulAut S) (ι : G →* GL (Fin 3) K)
    (hker : ∀ g, c g = 1 ↔ pmk (ι g) = 1) (hH : ∀ g, ι g ∈ glPi π 3 (p ^ f) K)
    (hinn : ∀ g, ι g ∈ slPi π 3 (p ^ f) K → c g ∈ (MulAut.conj : S →* MulAut S).range)
    (hlift : ∀ t ∈ slPi π 3 (p ^ f) K, ∃ g, ι g = t) {y : G}
    (hys : ι y ∉ StatedScalars (Fin 3) K) (hy3 : ι y ^ 3 ∈ StatedScalars (Fin 3) K) :
    ¬ AutWeaklyClosed (c y) := by
  have hπ : π = false → UnitaryFieldData p f K := fun h => by subst h; exact hK.unitary
  have hq' : π = false → ModThree false (p ^ f) := fun h => by subst h; exact hq
  obtain ⟨τ, hτ, hτ1⟩ := exists_tau hK hq
  have hxH := hH y
  have hxZ : ι y ∉ zPi π 3 (p ^ f) K := fun h =>
    hys (mem_statedScalars_of_mem_zPi hK hq hτ hτ1 h)
  have hx3 : ι y ^ 3 ∈ zPi π 3 (p ^ f) K := by
    rw [zPi_eq hπ hq' hτ hτ1]
    exact Subgroup.mem_inf.mpr ⟨pow_mem hxH 3, hy3⟩
  obtain ⟨t, htL, hc, hn⟩ := exists_witness_of_ne_zPi hK hq hxH hxZ hx3
  obtain ⟨g, rfl⟩ := hlift t htL
  exact not_autWeaklyClosed_of_hom_witness c
    ((pmk : GL (Fin 3) K →* Matrix.ProjGenLinGroup (Fin 3) K).comp ι) hker (hinn g htL) hc hn

end Diagonal

end L3Outer

end CFSG.RankThree.PartTwo.Sec4.RonanK432

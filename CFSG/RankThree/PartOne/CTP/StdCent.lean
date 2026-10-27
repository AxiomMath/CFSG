module

public import CFSG.RankThree.PartOne.CTP.StdGen

public section

namespace CFSG.RankThree.PartOne.CTP

open Matrix CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.KFU
  CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.Classical (subfieldGL subfieldGL_injective coe_subfieldGL subfieldPSU
  subfieldPSU_mk subfieldSU fixingSubgroup_range_subfieldPSU)

section Fix

variable {F : Type} [Field F] [Finite F] {f e : ℕ}

theorem mem_zpowers_of_fixes (hF : UnitaryFieldData 2 f F) {σ : F ≃+* F} {K₀ : Subfield F}
    (hK : ∀ x, x ∈ K₀ ↔ σ x = x) (h₀ : UnitaryFieldData 2 e K₀)
    (hbar : ∀ c : K₀, (h₀.bar c : F) = hF.bar c) (hq : ¬(3 = 3 ∧ 2 ^ f = 2))
    (hq₀ : ¬(3 = 3 ∧ 2 ^ e = 2))
    (β : MulAut (primeFormP hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)))
    (hβ : ∀ y ∈ (subfieldPSU hF h₀ hbar 3).range, β y = y) :
    β ∈ Subgroup.zpowers (primeFormFieldHom hF (isPrimeFormGram_one (n := 3)) σ) := by
  obtain rfl : K₀ = CFSG.LieType.Chevalley.fixSubfield σ :=
    Subfield.ext fun x => (hK x).trans (CFSG.LieType.Chevalley.mem_fixSubfield σ).symm
  obtain ⟨h1, h2, -⟩ := fixingSubgroup_range_subfieldPSU hF 3 h₀ hbar (le_refl 3) hq hq₀
  have hmem : β ∈ fixingSubgroup (MulAut (primeFormP hF ((1 : GL (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F))) ((subfieldPSU hF h₀ hbar 3).range :
        Set (primeFormP hF ((1 : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))) := by
    rw [mem_fixingSubgroup_iff]
    intro y hy
    rw [MulAut.smul_def]
    exact hβ y hy
  rw [h1, h2] at hmem
  exact hmem

end Fix

section Cent

variable {G : Type} [Group G] [Finite G] {c : G} {f₀ : ℕ} {I K BK : Subgroup G}
  {J : Fin 3 → Fin 3 → Subgroup G} (cfg : IConfig c f₀ I K BK J) (pic : StdData c f₀ I K BK J)

omit [Finite G] cfg in
theorem Psi_mem_gramSU (x : ↥I) :
    pic.Ψ x ∈ gramSU pic.hF ((1 : GL (Fin 3) pic.F) : Matrix (Fin 3) (Fin 3) pic.F) := by
  have h : pic.Ψ x ∈ unitarySU 2 (5 * f₀) pic.F 3 := by
    rw [← pic.Ψ_range]
    exact ⟨x, rfl⟩
  rw [unitarySU_eq_gramSU pic.hF 3] at h
  exact h

@[expose] noncomputable def eSU : ↥I ≃* ↥(gramSU pic.hF ((1 : GL (Fin 3) pic.F) :
    Matrix (Fin 3) (Fin 3) pic.F)) :=
  MulEquiv.ofBijective (pic.Ψ.codRestrict _ (Psi_mem_gramSU pic))
    ⟨fun x y h => pic.Ψ_inj (congrArg Subtype.val h), fun g => by
      have hg : (g : GL (Fin 3) pic.F) ∈ unitarySU 2 (5 * f₀) pic.F 3 := by
        rw [unitarySU_eq_gramSU pic.hF 3]
        exact g.2
      obtain ⟨x, hx⟩ := exists_pre pic hg
      exact ⟨x, Subtype.ext hx⟩⟩

include cfg pic

omit [Finite G] in
theorem cfg_inv_centralizes {t : G} (ht : t ∈ Subgroup.normalizer (I : Set G)) (ht2 : t ^ 2 = 1)
    (hK : ∀ k ∈ K, t * k = k * t) : ∀ u ∈ I, t * u = u * t := by
  have hQe : Even (5 * f₀) := (even_of_five_dvd cfg.dvd5).mul_left 5
  have hgcd : Nat.gcd 3 (2 ^ (5 * f₀) + 1) = 1 := coprime_three_two_pow_add_one hQe
  have hq4 : 4 ≤ 2 ^ f₀ := four_le_two_pow cfg.f_two
  have hq : ¬(3 = 3 ∧ 2 ^ (5 * f₀) = 2) := by
    rintro ⟨-, h⟩
    have : 2 ^ f₀ ≤ 2 ^ (5 * f₀) := Nat.pow_le_pow_right (by norm_num) (by have := cfg.f_two; omega)
    omega
  have hq₀ : ¬(3 = 3 ∧ 2 ^ f₀ = 2) := by
    rintro ⟨-, h⟩
    omega
  set τ : MulAut ↥I := conjAut I t ht with hτ
  have hτ2 : τ ^ 2 = 1 := by
    rw [hτ]
    unfold conjAut
    rw [← map_pow]
    have : (⟨t, ht⟩ : Subgroup.normalizer (I : Set G)) ^ 2 = 1 := Subtype.ext (by simpa using ht2)
    rw [this, map_one]
  have hτx : ∀ x : ↥I, ((τ x : ↥I) : G) = t * x * t⁻¹ := fun x => Equivariance.coe_conjAut ht x
  let eP : ↥I ≃* primeFormP pic.hF ((1 : GL (Fin 3) pic.F) : Matrix (Fin 3) (Fin 3) pic.F) :=
    (eSU pic).trans (suEquivP pic.hF hgcd)
  set β : MulAut (primeFormP pic.hF ((1 : GL (Fin 3) pic.F) : Matrix (Fin 3) (Fin 3) pic.F)) :=
    MulAut.congr eP τ with hβdef
  have hβ2 : β ^ 2 = 1 := by rw [hβdef, ← map_pow, hτ2, map_one]
  have hβfix : ∀ y ∈ (subfieldPSU pic.hF pic.h₀ pic.bar_eq 3).range, β y = y := by
    rintro _ ⟨y₀, rfl⟩
    induction y₀ using QuotientGroup.induction_on with
    | H g₀ =>
      rw [subfieldPSU_mk]
      have hg₀ : (g₀ : GL (Fin 3) pic.K₀) ∈ unitarySU 2 f₀ pic.K₀ 3 := by
        rw [unitarySU_eq_gramSU pic.h₀]
        exact g₀.2
      have hmem : subfieldGL pic.K₀ 3 g₀ ∈ tr I pic.Ψ K := by
        rw [pic.tr_K]
        exact ⟨g₀, hg₀, rfl⟩
      obtain ⟨k, hk, hkΨ⟩ := hmem
      have hkK : (k : G) ∈ K := hk
      have hePk : eP k = ((subfieldSU pic.hF pic.h₀ pic.bar_eq 3 g₀ :
          gramSU pic.hF ((1 : GL (Fin 3) pic.F) : Matrix (Fin 3) (Fin 3) pic.F)) :
            primeFormP pic.hF ((1 : GL (Fin 3) pic.F) : Matrix (Fin 3) (Fin 3) pic.F)) := by
        show suEquivP pic.hF hgcd (eSU pic k) = _
        rw [suEquivP_apply]
        congr 1
        exact Subtype.ext hkΨ
      have hτk : τ k = k := Subtype.ext (by
        rw [hτx]
        have := hK k hkK
        rw [mul_inv_eq_iff_eq_mul]
        exact this)
      rw [← hePk, hβdef]
      show eP (τ (eP.symm (eP k))) = eP k
      rw [MulEquiv.symm_apply_apply, hτk]
  have hβmem := mem_zpowers_of_fixes pic.hF pic.K₀_iff pic.h₀ pic.bar_eq hq hq₀ β hβfix
  have hσ5 : pic.σ ^ 5 = 1 := by
    have := pow_orderOf_eq_one pic.σ
    rwa [pic.σ_order] at this
  have hg5 : (primeFormFieldHom pic.hF (isPrimeFormGram_one (n := 3)) pic.σ) ^ 5 = 1 := by
    rw [← map_pow, hσ5, map_one]
  have hβ5 : orderOf β ∣ 5 :=
    (orderOf_dvd_of_mem_zpowers hβmem).trans (orderOf_dvd_of_pow_eq_one hg5)
  have hβ1 : β = 1 := by
    have h1 : orderOf β ∣ Nat.gcd 2 5 :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hβ2) hβ5
    have h2 : Nat.gcd 2 5 = 1 := by norm_num
    rw [h2] at h1
    exact orderOf_eq_one_iff.mp (Nat.dvd_one.mp h1)
  have hτ1 : τ = 1 := (MulAut.congr eP).injective (by rw [← hβdef, hβ1, map_one])
  intro u hu
  have h1 := congrArg (fun φ : MulAut ↥I => ((φ ⟨u, hu⟩ : ↥I) : G)) hτ1
  simp only [hτx, MulAut.one_apply] at h1
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1

end Cent

end CFSG.RankThree.PartOne.CTP

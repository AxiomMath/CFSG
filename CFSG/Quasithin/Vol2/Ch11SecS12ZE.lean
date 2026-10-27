module

public import CFSG.Quasithin.Vol2.Ch11SecS12ZD
public import CFSG.LinearAlgebra.DesarguesianPlanes.SteinbergRecognition
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagOrder

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

open Matrix

theorem subsingleton_of_isPGroup_of_perfect {P : Type*} [Group P] [Finite P] {p : ℕ}
    [Fact p.Prime] (hP : IsPGroup p P) (hperf : commutator P = ⊤) : Subsingleton P := by
  have hnil : Group.IsNilpotent P := hP.isNilpotent
  obtain ⟨n, hn⟩ := (Subgroup.nilpotent_iff_lowerCentralSeries).mp hnil
  have htop : ∀ k, (⊤ : Subgroup P).lowerCentralSeries k = ⊤ := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih => rw [Subgroup.lowerCentralSeries_succ, ih, ← commutator_def, hperf]
  rw [htop n] at hn
  exact Subgroup.subsingleton_iff.mp (subsingleton_of_bot_eq_top hn.symm)

theorem pow_three_eq_one_of_pow_three_pow {F : Type*} [Field F] [Fintype F]
    (hF : Fintype.card F = 4) {g : Matrix.SpecialLinearGroup (Fin 3) F} :
    ∀ k : ℕ, g ^ 3 ^ k = 1 → g ^ 3 = 1 := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro hk
    rcases k with _ | _ | k
    · simp only [pow_zero, pow_one] at hk
      rw [hk, one_pow]
    · simpa using hk
    · have h9 : (g ^ 3 ^ k) ^ 9 = 1 := by
        rw [← pow_mul, show 3 ^ k * 9 = 3 ^ (k + 2) by ring]
        exact hk
      have hM := pow_three_eq_one_of_pow_nine hF
        (M := ((g ^ 3 ^ k : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F))
        (g ^ 3 ^ k).2 (by
          rw [← Matrix.SpecialLinearGroup.coe_pow, h9, Matrix.SpecialLinearGroup.coe_one])
      have h3 : (g ^ 3 ^ k) ^ 3 = 1 := Subtype.ext (by
        rw [Matrix.SpecialLinearGroup.coe_pow, hM, Matrix.SpecialLinearGroup.coe_one])
      refine ih (k + 1) (by omega) ?_
      rw [pow_succ, pow_mul]
      exact h3

theorem eq_one_of_pow_two_pow_of_pow_three_pow {G : Type*} [Group G] {x : G} {m k : ℕ}
    (h2 : x ^ 2 ^ m = 1) (h3 : x ^ 3 ^ k = 1) : x = 1 :=
  orderOf_eq_one_iff.mp (Nat.eq_one_of_dvd_coprimes
    (Nat.Coprime.pow m k (by norm_num)) (orderOf_dvd_of_pow_eq_one h2)
    (orderOf_dvd_of_pow_eq_one h3))

theorem eq_one_of_isPGroup_range {A B : Type*} [Group A] [Finite A] [Group B]
    (hA : commutator A = ⊤) {p : ℕ} [Fact p.Prime] (f : A →* B) (hf : IsPGroup p f.range) :
    f = 1 := by
  have hQ : IsPGroup p (A ⧸ f.ker) := hf.of_equiv (QuotientGroup.quotientKerEquivRange f).symm
  have hQperf : commutator (A ⧸ f.ker) = ⊤ := by
    rw [commutator_def, ← Subgroup.map_top_of_surjective _ (QuotientGroup.mk'_surjective f.ker),
      ← Subgroup.map_commutator, ← commutator_def, hA]
  have := subsingleton_of_isPGroup_of_perfect hQ hQperf
  ext a
  have h1 : ((a : A ⧸ f.ker) : A ⧸ f.ker) = 1 := Subsingleton.elim _ _
  rw [QuotientGroup.eq_one_iff] at h1
  simpa using h1

theorem hom_eq_one_of_SL34 {A : Type*} [Group A] [Finite A] (hA : commutator A = ⊤)
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 4)
    (π : A →* Matrix.SpecialLinearGroup (Fin 3) F) (hπ : Function.Surjective π)
    (hker : IsPGroup 2 π.ker) {p : ℕ} [hp : Fact p.Prime] (ρ : A →* GL (Fin 2) (ZMod p)) :
    ρ = 1 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hquasi : CFSG.Open.IsQuasisimple (Matrix.SpecialLinearGroup (Fin 3) F) :=
    CFSG.ComponentClassification.CatalogueBAlternating.quasisimple_iff_native.mp
      (CFSG.ComponentClassification.CatalogueBGeneralLinear.specialLinear_quasisimple 3 F
        (by norm_num) (Or.inl (by norm_num)) (Or.inl (by norm_num)))
  have hN : (ρ.ker.map π).Normal := Subgroup.Normal.map inferInstance π hπ
  rcases CFSG.ComponentClassification.Quasisimple.normal_le_center_or_eq_top hquasi
    (ρ.ker.map π) with hZ | htop
  · exfalso
    have hdet : ∀ a : A,
        ((ρ a : GL (Fin 2) (ZMod p)) : Matrix (Fin 2) (Fin 2) (ZMod p)).det = 1 := by
      intro a
      have h1 := Abelianization.commutator_subset_ker
        ((Matrix.GeneralLinearGroup.det).comp ρ) (hA ▸ Subgroup.mem_top a : a ∈ commutator A)
      rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at h1
      have := congrArg Units.val h1
      simpa [Matrix.GeneralLinearGroup.val_det_apply] using this
    obtain ⟨S⟩ : Nonempty (Sylow 3 A) := inferInstance
    have h27 : 3 ^ 3 ∣ Nat.card S := by
      refine S.pow_dvd_card_of_pow_dvd_card (dvd_trans ?_ (Subgroup.card_dvd_of_surjective hπ))
      rw [CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num),
        Nat.card_eq_fintype_card, hF]
      decide
    have hS3 : ∀ s ∈ (S : Subgroup A), s ^ 3 = 1 := by
      intro s hs
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨s, hs⟩
      have hk' : s ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
      have hπ3 : π s ^ 3 = 1 :=
        pow_three_eq_one_of_pow_three_pow hF k (by rw [← map_pow, hk', map_one])
      have hmem : s ^ 3 ∈ π.ker := by rw [MonoidHom.mem_ker, map_pow, hπ3]
      obtain ⟨m, hm⟩ := hker ⟨_, hmem⟩
      have hm' : (s ^ 3) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
      have h3k : (s ^ 3) ^ 3 ^ k = 1 := by rw [← pow_mul, mul_comm, pow_mul, hk', one_pow]
      exact eq_one_of_pow_two_pow_of_pow_three_pow hm' h3k
    have hρS : Nat.card ((S : Subgroup A).map ρ) ≤ 3 := by
      refine card_le_three_of_exponent_three _ ?_ ?_
      · rintro _ ⟨s, -, rfl⟩
        exact hdet s
      · rintro _ ⟨s, hs, rfl⟩
        rw [← map_pow, hS3 s hs, map_one]
    have hSN : Nat.card ↥((S : Subgroup A) ⊓ ρ.ker) ≤ 3 := by
      set g := π.comp ((S : Subgroup A) ⊓ ρ.ker).subtype with hgdef
      have hg : Function.Injective g := by
        rw [injective_iff_map_eq_one]
        intro x hx
        obtain ⟨k, hk⟩ := S.isPGroup' ⟨x, x.2.1⟩
        have hk' : (x : A) ^ 3 ^ k = 1 := by simpa using congrArg Subtype.val hk
        obtain ⟨m, hm⟩ := hker ⟨x, hx⟩
        have hm' : (x : A) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
        exact Subtype.ext (eq_one_of_pow_two_pow_of_pow_three_pow hm' hk')
      have hrange : g.range ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F) := by
        rintro _ ⟨x, rfl⟩
        exact hZ ⟨x, x.2.2, rfl⟩
      calc Nat.card ↥((S : Subgroup A) ⊓ ρ.ker) = Nat.card g.range :=
            Nat.card_congr (MonoidHom.ofInjective hg).toEquiv
        _ ≤ Nat.card (Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) :=
            Subgroup.card_le_of_le hrange
        _ ≤ 3 := CFSG.DesarguesianPlanes.card_center_SL3_le
    set f := ρ.comp (S : Subgroup A).subtype with hfdef
    have hfr : f.range = (S : Subgroup A).map ρ := by
      rw [hfdef, MonoidHom.range_comp, Subgroup.range_subtype]
    have hfk : Nat.card f.ker ≤ Nat.card ↥((S : Subgroup A) ⊓ ρ.ker) := by
      rw [← Subgroup.card_map_of_injective (K := f.ker)
        (Subgroup.subtype_injective (S : Subgroup A))]
      refine Subgroup.card_le_of_le ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨x.2, hx⟩
    have hcard := Subgroup.card_ker_mul_card_range f
    rw [hfr] at hcard
    have hle : Nat.card ↥(S : Subgroup A) ≤ 9 := by
      rw [← hcard]
      calc Nat.card f.ker * Nat.card ((S : Subgroup A).map ρ) ≤ 3 * 3 :=
            Nat.mul_le_mul (hfk.trans hSN) hρS
        _ = 9 := by norm_num
    have h27' : 27 ≤ Nat.card ↥(S : Subgroup A) := Nat.le_of_dvd Nat.card_pos h27
    omega
  ·
    refine eq_one_of_isPGroup_range hA ρ (p := 2) ?_
    rintro ⟨_, a, rfl⟩
    obtain ⟨n, hn, hna⟩ : π a ∈ ρ.ker.map π := htop ▸ Subgroup.mem_top _
    have hmem : n⁻¹ * a ∈ π.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, hna, inv_mul_cancel]
    obtain ⟨m, hm⟩ := hker ⟨_, hmem⟩
    have hm' : (n⁻¹ * a) ^ 2 ^ m = 1 := by simpa using congrArg Subtype.val hm
    have hρ : ρ a = ρ (n⁻¹ * a) := by
      rw [map_mul, map_inv, (MonoidHom.mem_ker).mp hn, inv_one, one_mul]
    refine ⟨m, Subtype.ext ?_⟩
    simp only [SubgroupClass.coe_pow, OneMemClass.coe_one]
    rw [hρ, ← map_pow, hm', map_one]

end CFSG.Quasithin.Vol2.Ch11.SecS.C11AmS.S12

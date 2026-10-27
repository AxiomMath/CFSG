module

public import CFSG.Quasithin.Background.P3Sp44Semi
public import CFSG.Quasithin.Background.P3Sp44Desc

public section

namespace CFSG.Quasithin

namespace G11

namespace G118

open Equiv CFSG.ComponentClassification.PresentationLocal Matrix CFSG.Assembly.LowTwoRank

variable {K : Type} [Field K]

theorem sp44_elemAbelian_S6 (R : Subgroup (Perm (Fin 6))) (hR : ∀ r ∈ R, r * r = 1) :
    Nat.card R ≤ 8 := by
  have hR2 : IsPGroup 2 R := fun x => ⟨1, by
    apply Subtype.ext
    simpa [sq] using hR x x.2⟩
  obtain ⟨P, hP⟩ := IsPGroup.exists_le_sylow hR2
  have hcardG : Nat.card (Perm (Fin 6)) = 720 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  have hcardP : Nat.card P = 16 := by
    rw [Sylow.card_eq_multiplicity, hcardG]
    have h : (720 : ℕ) = 2 ^ 4 * 45 := by norm_num
    rw [h, Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
      Nat.Prime.factorization_pow Nat.prime_two, Finsupp.single_eq_same,
      Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    norm_num
  by_contra hlt
  push Not at hlt
  have hdvd : Nat.card R ∣ Nat.card P := Subgroup.card_dvd_of_le hP
  have hR16 : Nat.card R = 16 := by
    rw [hcardP] at hdvd
    have hle : Nat.card R ≤ 16 := Nat.le_of_dvd (by norm_num) hdvd
    have : Nat.card R ∣ 16 := hdvd
    interval_cases h : Nat.card R <;> simp_all
  have hRP : R = (P : Subgroup (Perm (Fin 6))) :=
    Subgroup.eq_of_le_of_card_ge hP (by rw [hcardP, hR16])
  let x : Perm (Fin 6) := swap 0 1 * swap 1 2 * swap 2 3
  have hx4 : x ^ 4 = 1 := by decide
  have hx2 : x * x ≠ 1 := by decide
  have hxo : orderOf x = 2 ^ 2 := by
    apply orderOf_eq_prime_pow (p := 2) (n := 1)
    · decide
    · exact hx4
  have hz : IsPGroup 2 (Subgroup.zpowers x) := by
    apply IsPGroup.of_card (n := 2)
    rw [Nat.card_zpowers, hxo]
  obtain ⟨Q, hQ⟩ := IsPGroup.exists_le_sylow hz
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq (Perm (Fin 6)) Q P
  have hxQ : x ∈ (Q : Subgroup (Perm (Fin 6))) := hQ (Subgroup.mem_zpowers x)
  have hmem : g * x * g⁻¹ ∈ (P : Subgroup (Perm (Fin 6))) := by
    have h1 : (g * x * g⁻¹ : Perm (Fin 6)) ∈
        ((g • Q : Sylow 2 (Perm (Fin 6))) : Set (Perm (Fin 6))) := by
      rw [Sylow.coe_smul]
      exact ⟨x, hxQ, by simp [MulAut.smul_def, MulAut.conj_apply]⟩
    rw [hg] at h1
    exact h1
  have h2 := hR _ (hRP ▸ hmem)
  apply hx2
  have : (g * x * g⁻¹) * (g * x * g⁻¹) = g * (x * x) * g⁻¹ := by group
  rw [this] at h2
  have := mul_inv_eq_one.1 h2
  simpa using this


variable {K : Type} [Field K] [Finite K]

theorem sp44_card_le_eight (hK : Nat.card K = 4)
    (a' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (hinv : ∀ v, a' (a' v) = v)
    (hsq : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a' (t • w) = t ^ 2 • a' w)
    (hform : ∀ v w, sp44ω (a' v) (a' w) = sp44ω v w ^ 2)
    (C : Subgroup (Equiv.Perm (Fin 2 ⊕ Fin 2 → K)))
    (hC : ∀ c : Equiv.Perm (Fin 2 ⊕ Fin 2 → K), c ∈ C → (∀ v w, c (v + w) = c v + c w) ∧
      (∀ (t : K) v, c (t • v) = t • c v) ∧
      c * c = 1 ∧ (∀ v, c (a' v) = a' (c v)) ∧ (∀ v w, sp44ω (c v) (c w) = sp44ω v w)) :
    Nat.card C ≤ 8 := by
  obtain ⟨φ, hφ⟩ := sp44_embed hK a' hinv hsq hform C hC
  have hinj : Function.Injective (omegaPerm.comp φ) := omegaPerm_injective.comp hφ
  have hcard : Nat.card C = Nat.card (omegaPerm.comp φ).range :=
    Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv
  rw [hcard]
  apply sp44_elemAbelian_S6
  rintro _ ⟨c, rfl⟩
  have h := (hC c.1 c.2).2.2.1
  have : c * c = 1 := Subtype.ext h
  show (omegaPerm.comp φ) c * (omegaPerm.comp φ) c = 1
  rw [← map_mul, this, map_one]


theorem sp44_core (hK : Nat.card K = 4)
    (A : Subgroup (Equiv.Perm (Fin 2 ⊕ Fin 2 → K)))
    (hadd : ∀ a : Equiv.Perm (Fin 2 ⊕ Fin 2 → K), a ∈ A → ∀ v w, a (v + w) = a v + a w)
    (hA2 : ∀ a : Equiv.Perm (Fin 2 ⊕ Fin 2 → K), a ∈ A → a * a = 1)
    (hAc : ∀ a b : Equiv.Perm (Fin 2 ⊕ Fin 2 → K), a ∈ A → b ∈ A → a * b = b * a)
    (hAn : ∀ a : Equiv.Perm (Fin 2 ⊕ Fin 2 → K), a ∈ A →
      ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K →
        ∃ g' : GL (Fin 2 ⊕ Fin 2) K, g' ∈ StatedSp 2 K ∧ ∀ v,
          a ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
            (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a v)
    (a₀ : Equiv.Perm (Fin 2 ⊕ Fin 2 → K)) (ha₀ : a₀ ∈ A)
    (f : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K))
    (hf : ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K → ∀ v,
      f ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
        (g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ f v)
    (hne : ∃ v, a₀ (f v) ≠ f (a₀ v)) : Nat.card A ≤ 16 := by
  have hSp : ∀ a : Equiv.Perm (Fin 2 ⊕ Fin 2 → K), a ∈ A →
      ∀ g : GL (Fin 2 ⊕ Fin 2) K, g ∈ StatedSp 2 K →
        ∃ g' : GL (Fin 2 ⊕ Fin 2) K, g' ∈ StatedSp 2 K ∧ ∀ v,
          a⁻¹ ((g : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ v) =
            (g' : Matrix (Fin 2 ⊕ Fin 2) (Fin 2 ⊕ Fin 2) K) *ᵥ a⁻¹ v :=
    fun a ha g hg => hAn a⁻¹ (A.inv_mem ha) g hg
  have hdich : ∀ a : Equiv.Perm (Fin 2 ⊕ Fin 2 → K), a ∈ A →
      (∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a (t • w) = t • a w) ∨
      (∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a (t • w) = t ^ 2 • a w) := by
    intro a ha
    exact sp44_lin_or_frob hK { a with map_add' := hadd a ha } (hSp a ha)
  obtain ⟨p, hp⟩ := sp44_commutant f hf
  have hfrob₀ : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a₀ (t • w) = t ^ 2 • a₀ w := by
    rcases hdich a₀ ha₀ with h | h
    · exfalso
      obtain ⟨v, hv⟩ := hne
      apply hv
      rw [hp, hp, h]
    · exact h
  have : Finite A := inferInstance
  obtain ⟨C, hCmem, hcard⟩ := sp44_card_le_two_mul A hK hdich a₀ ha₀ hfrob₀
  have ha02 : ∀ v, a₀ (a₀ v) = v := fun v => by
    have := congrArg (fun m : Equiv.Perm (Fin 2 ⊕ Fin 2 → K) => m v) (hA2 a₀ ha₀)
    simpa using this
  obtain ⟨ν, hν0, hν⟩ := sp44_frob_normalize hK { a₀ with map_add' := hadd a₀ ha₀ } hfrob₀
    (hAn a₀ ha₀)
  have hν3 : ν ^ 3 = 1 := sp44_pow_three hK ν hν0
  let a' : (Fin 2 ⊕ Fin 2 → K) →+ (Fin 2 ⊕ Fin 2 → K) :=
    AddMonoidHom.mk' (fun v => ν • a₀ v) (fun v w => by rw [hadd a₀ ha₀, smul_add])
  have ha'apply : ∀ v, a' v = ν • a₀ v := fun v => rfl
  have hinv : ∀ v, a' (a' v) = v := by
    intro v
    rw [ha'apply, ha'apply, hfrob₀, smul_smul, ha02]
    have : ν * ν ^ 2 = 1 := by rw [← pow_succ']; exact hν3
    rw [this, one_smul]
  have hsq : ∀ (t : K) (w : Fin 2 ⊕ Fin 2 → K), a' (t • w) = t ^ 2 • a' w := by
    intro t w
    rw [ha'apply, ha'apply, hfrob₀, smul_comm]
  have hform : ∀ v w, sp44ω (a' v) (a' w) = sp44ω v w ^ 2 := fun v w => hν v w
  let Cp : Subgroup (Equiv.Perm (Fin 2 ⊕ Fin 2 → K)) := C.map A.subtype
  have hCp : ∀ c : Equiv.Perm (Fin 2 ⊕ Fin 2 → K), c ∈ Cp → (∀ v w, c (v + w) = c v + c w) ∧
      (∀ (t : K) v, c (t • v) = t • c v) ∧ c * c = 1 ∧ (∀ v, c (a' v) = a' (c v)) ∧
      (∀ v w, sp44ω (c v) (c w) = sp44ω v w) := by
    intro c hc
    obtain ⟨a, haC, rfl⟩ := Subgroup.mem_map.1 hc
    have haA : a.1 ∈ A := a.2
    have hlin : ∀ (t : K) (v : Fin 2 ⊕ Fin 2 → K), a.1 (t • v) = t • a.1 v := (hCmem a).1 haC
    have hc2 : a.1 * a.1 = 1 := hA2 a.1 haA
    refine ⟨hadd a.1 haA, hlin, hc2, ?_, ?_⟩
    · intro v
      show a.1 (ν • a₀ v) = ν • a₀ (a.1 v)
      rw [hlin]
      congr 1
      have := congrArg (fun m : Equiv.Perm (Fin 2 ⊕ Fin 2 → K) => m v) (hAc a.1 a₀ haA ha₀)
      exact this
    · exact sp44_lin_isometry hK { a.1 with map_add' := hadd a.1 haA } hlin
        (fun v => by
          have := congrArg (fun m : Equiv.Perm (Fin 2 ⊕ Fin 2 → K) => m v) hc2
          simpa using this)
        (hAn a.1 haA)
  have h8 := sp44_card_le_eight hK a' hinv hsq hform Cp hCp
  have hcardC : Nat.card C = Nat.card Cp :=
    Nat.card_congr (Subgroup.equivMapOfInjective C A.subtype A.subtype_injective).toEquiv
  omega

end G118

end G11

end CFSG.Quasithin

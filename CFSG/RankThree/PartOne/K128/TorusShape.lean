module

public import CFSG.RankThree.PartOne.K1214.SylowShape
public import CFSG.Quasithin.SteinbergBMCenterlessComponentNormal
public import CFSG.LieType.SteinbergBRTwoRankBound

public section

namespace CFSG.RankThree.PartOne.K128

open Subgroup CFSG.RankThree.PartOne.K1214

theorem sylowShape_of_injective {p e : ℕ} (hp : p.Prime) {Γ : Type*} [Group Γ] [Finite Γ]
    (Ψ : (Fin 2 → Multiplicative (ZMod (p ^ e))) →* Γ) (hΨ : Function.Injective Ψ)
    (hord : (Nat.card Γ).factorization p = 2 * e) : SylowShape p 2 e Γ := by
  have : NeZero (p ^ e) := ⟨pow_ne_zero _ hp.ne_zero⟩
  have hM : Nat.card (Multiplicative (ZMod (p ^ e))) = p ^ e := by
    rw [Nat.card_congr (Multiplicative.toAdd : Multiplicative (ZMod (p ^ e)) ≃ ZMod (p ^ e)),
      Nat.card_zmod]
  have hcard : Nat.card Ψ.range = p ^ (2 * e) := by
    rw [← Nat.card_congr (MonoidHom.ofInjective hΨ).toEquiv, Nat.card_pi,
      Finset.prod_const, Finset.card_univ, Fintype.card_fin, hM, ← pow_mul, mul_comm]
  have hS : IsPGroup p Ψ.range := IsPGroup.of_card hcard
  have hidx : ¬ p ∣ Ψ.range.index := by
    intro hdvd
    have hmul := Subgroup.card_mul_index Ψ.range
    have hidx0 : Ψ.range.index ≠ 0 := Subgroup.index_ne_zero_of_finite
    have h2 := congrArg (fun n => n.factorization p) hmul
    rw [Nat.factorization_mul (by rw [hcard]; exact pow_ne_zero _ hp.ne_zero) hidx0,
      hcard, Nat.Prime.factorization_pow hp] at h2
    have h3 : 1 ≤ Ψ.range.index.factorization p :=
      (hp.dvd_iff_one_le_factorization hidx0).1 hdvd
    simp only [Finsupp.add_apply, Finsupp.single_eq_same] at h2
    omega
  exact SylowShape.of_witness hp hS hidx (MonoidHom.ofInjective hΨ).symm

@[expose] noncomputable def zmodInclAdd (d m : ℕ) (h : d ∣ m) : ZMod d →+ ZMod m :=
  ZMod.lift d ⟨zmultiplesHom (ZMod m) ((m / d : ℕ) : ZMod m), by
    simp only [zmultiplesHom_apply, zsmul_eq_mul, Int.cast_natCast]
    rw [← Nat.cast_mul, Nat.mul_div_cancel' h, ZMod.natCast_self]⟩

theorem zmodInclAdd_natCast (d m : ℕ) (h : d ∣ m) (k : ℕ) :
    zmodInclAdd d m h (k : ZMod d) = (((m / d) * k : ℕ) : ZMod m) := by
  have := ZMod.lift_coe d (⟨zmultiplesHom (ZMod m) ((m / d : ℕ) : ZMod m), by
    simp only [zmultiplesHom_apply, zsmul_eq_mul, Int.cast_natCast]
    rw [← Nat.cast_mul, Nat.mul_div_cancel' h, ZMod.natCast_self]⟩ :
      {f : ℤ →+ ZMod m // f d = 0}) (k : ℤ)
  simp only [Int.cast_natCast, zmultiplesHom_apply, zsmul_eq_mul] at this
  rw [zmodInclAdd]
  rw [this]
  push_cast
  ring

theorem zmodInclAdd_injective {d m : ℕ} (h : d ∣ m) (hm : m ≠ 0) :
    Function.Injective (zmodInclAdd d m h) := by
  have hd : d ≠ 0 := fun h0 => hm (by rw [h0] at h; exact Nat.eq_zero_of_zero_dvd h)
  have : NeZero d := ⟨hd⟩
  rw [injective_iff_map_eq_zero]
  intro x hx
  have hx' : x = ((x.val : ℕ) : ZMod d) := (ZMod.natCast_zmod_val x).symm
  rw [hx', zmodInclAdd_natCast, ZMod.natCast_eq_zero_iff] at hx
  have hdm : 0 < m / d :=
    Nat.div_pos (Nat.le_of_dvd (Nat.pos_of_ne_zero hm) h) (Nat.pos_of_ne_zero hd)
  have h1 : d * (m / d) ∣ (m / d) * x.val := by rwa [Nat.mul_div_cancel' h]
  have h2 : d ∣ x.val := by
    have h1' : (m / d) * d ∣ (m / d) * x.val := by rwa [mul_comm (m / d) d]
    exact (Nat.mul_dvd_mul_iff_left hdm).1 h1'
  have h3 : x.val = 0 := by
    rcases h2 with ⟨c, hc⟩
    have : x.val < d := ZMod.val_lt x
    rcases Nat.eq_zero_or_pos c with hc0 | hc0
    · simp [hc, hc0]
    · nlinarith
  rw [hx']
  rw [h3]
  simp

@[expose] noncomputable def zmodIncl (d m : ℕ) (h : d ∣ m) :
    Multiplicative (ZMod d) →* Multiplicative (ZMod m) :=
  AddMonoidHom.toMultiplicative (zmodInclAdd d m h)

theorem zmodIncl_injective {d m : ℕ} (h : d ∣ m) (hm : m ≠ 0) :
    Function.Injective (zmodIncl d m h) := zmodInclAdd_injective h hm

theorem exists_injective_of_dvd {m₁ m₂ d : ℕ} (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (h₁ : d ∣ m₁)
    (h₂ : d ∣ m₂) :
    ∃ Ψ : (Fin 2 → Multiplicative (ZMod d)) →* Multiplicative (ZMod m₁) × Multiplicative (ZMod m₂),
      Function.Injective Ψ := by
  refine ⟨((zmodIncl d m₁ h₁).comp (Pi.evalMonoidHom (fun _ : Fin 2 => Multiplicative (ZMod d))
      0)).prod
    ((zmodIncl d m₂ h₂).comp (Pi.evalMonoidHom (fun _ : Fin 2 => Multiplicative (ZMod d)) 1)), ?_⟩
  rw [injective_iff_map_eq_one]
  intro v hv
  have h1 : zmodIncl d m₁ h₁ (v 0) = 1 := congrArg Prod.fst hv
  have h2 : zmodIncl d m₂ h₂ (v 1) = 1 := congrArg Prod.snd hv
  have h1' : v 0 = 1 := (injective_iff_map_eq_one _).1 (zmodIncl_injective h₁ hm₁) _ h1
  have h2' : v 1 = 1 := (injective_iff_map_eq_one _).1 (zmodIncl_injective h₂ hm₂) _ h2
  funext i
  fin_cases i
  · exact h1'
  · exact h2'

theorem exists_injective_of_torus {Γ : Type*} [Group Γ] {m₁ m₂ d : ℕ} (hm₁ : m₁ ≠ 0)
    (hm₂ : m₂ ≠ 0) (h₁ : d ∣ m₁) (h₂ : d ∣ m₂) (T₀ : Subgroup Γ)
    (ψ : T₀ ≃* Multiplicative (ZMod m₁) × Multiplicative (ZMod m₂)) :
    ∃ Ψ : (Fin 2 → Multiplicative (ZMod d)) →* Γ, Function.Injective Ψ := by
  obtain ⟨Ψ₀, hΨ₀⟩ := exists_injective_of_dvd hm₁ hm₂ h₁ h₂
  exact ⟨T₀.subtype.comp (ψ.symm.toMonoidHom.comp Ψ₀),
    T₀.subtype_injective.comp (ψ.symm.injective.comp hΨ₀)⟩

theorem sylowShape_of_torus {p e : ℕ} (hp : p.Prime) {Γ : Type*} [Group Γ] [Finite Γ]
    {m₁ m₂ : ℕ} (hm₁ : m₁ ≠ 0) (hm₂ : m₂ ≠ 0) (h₁ : p ^ e ∣ m₁) (h₂ : p ^ e ∣ m₂)
    (T₀ : Subgroup Γ) (ψ : T₀ ≃* Multiplicative (ZMod m₁) × Multiplicative (ZMod m₂))
    (hord : (Nat.card Γ).factorization p = 2 * e) : SylowShape p 2 e Γ := by
  obtain ⟨Ψ, hΨ⟩ := exists_injective_of_torus hm₁ hm₂ h₁ h₂ T₀ ψ
  exact sylowShape_of_injective hp Ψ hΨ hord

theorem dvd_card_of_pRank_pos {p : ℕ} (hp : p.Prime) {Γ : Type*} [Group Γ] [Finite Γ]
    (h : 1 ≤ CFSG.pRank p Γ) : p ∣ Nat.card Γ := by
  obtain ⟨B, -, hB⟩ := CFSG.Quasithin.SteinbergBM.exists_card_eq_pow_pRank (X := Γ) hp.one_lt
  have h1 : p ∣ p ^ CFSG.pRank p Γ := dvd_pow_self p (by omega)
  rw [← hB] at h1
  exact h1.trans (Subgroup.card_subgroup_dvd_card B)

theorem pRank_le_one_of_cyclic_pSubgroups {T : Type*} [Group T] [Finite T] {p : ℕ} (hp : p.Prime)
    (h : ∀ P : Subgroup T, IsPGroup p P → IsCyclic P) : CFSG.pRank p T ≤ 1 := by
  refine CFSG.LieType.SteinbergBR.pRank_le_of_card_le hp.one_lt fun A hA => ?_
  have hpow : ∀ x : A, x ^ p = 1 := fun x =>
    Subtype.ext (CFSG.elemPow_eq_one_of_isElementaryAbelian (x : T) x.2)
  have hAp : IsPGroup p A := fun x => ⟨1, by simpa using hpow x⟩
  have : IsCyclic A := h A hAp
  have hexp : Monoid.exponent A ∣ p := Monoid.exponent_dvd_of_forall_pow_eq_one hpow
  rw [pow_one, ← IsCyclic.exponent_eq_card]
  exact Nat.le_of_dvd hp.pos hexp

theorem pRank_le_one_of_cyclic_sylow {T : Type*} [Group T] [Finite T] {p : ℕ} [Fact p.Prime]
    (h : ∀ P : Sylow p T, IsCyclic P) : CFSG.pRank p T ≤ 1 := by
  refine pRank_le_one_of_cyclic_pSubgroups Fact.out fun P hP => ?_
  obtain ⟨Q, hQ⟩ := hP.exists_le_sylow
  have : IsCyclic (Q : Subgroup T) := h Q
  exact Subgroup.isCyclic_of_le hQ

theorem charP_two_of_card_eq_two_pow {K : Type} [Field K] [Finite K] {f : ℕ}
    (h : Nat.card K = 2 ^ f) : CharP K 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fintype K := Fintype.ofFinite K
  exact charP_of_card_eq_prime_pow (f := f) (by rw [← Nat.card_eq_fintype_card]; exact h)

theorem exists_injective_units {K : Type} [Field K] [Finite K] {d : ℕ} (hd : d ∣ Nat.card K - 1) :
    ∃ ι : Multiplicative (ZMod d) →* Kˣ, Function.Injective ι := by
  have hc : IsCyclic Kˣ := inferInstance
  have hcard : Nat.card Kˣ = Nat.card K - 1 := Nat.card_units K
  have h1 : d ∣ Nat.card Kˣ := by rw [hcard]; exact hd
  have h0 : Nat.card Kˣ ≠ 0 := Nat.card_pos.ne'
  exact ⟨(zmodCyclicMulEquiv hc).toMonoidHom.comp (zmodIncl d (Nat.card Kˣ) h1),
    (zmodCyclicMulEquiv hc).injective.comp (zmodIncl_injective h1 h0)⟩

end CFSG.RankThree.PartOne.K128

module

public import CFSG.Blueprint.Catalog
import CFSG.LocalAnalysis.WeakClosure81.Asc80BExcC4Sp
import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open (StatedProj StatedSp)

theorem exists_fixed_pElement_of_center_quotient {S : Type*} [Group S] [Finite S] {p : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (β : MulAut S) (hβ : β ^ 2 = 1)
    (a : S ⧸ Subgroup.center S) (ha : a ≠ 1) (hap : ∃ n : ℕ, a ^ (p ^ n) = 1)
    (hfix : ∀ x : S, (x : S ⧸ Subgroup.center S) = a → (β x : S ⧸ Subgroup.center S) = a) :
    ∃ u : S, u ≠ 1 ∧ (∃ n : ℕ, u ^ (p ^ n) = 1) ∧ β u = u := by
  classical
  obtain ⟨x₀, hx₀⟩ := QuotientGroup.mk'_surjective (Subgroup.center S) a
  obtain ⟨k, m, hm, hkm⟩ :=
    Nat.exists_eq_pow_mul_and_not_dvd (orderOf_pos x₀).ne' p hp.ne_one
  obtain ⟨n, hn⟩ := hap
  have hcop : Nat.Coprime m (orderOf a) := by
    rcases n with _ | n
    · have ha1 : a = 1 := by simpa using hn
      simp [ha1]
    · exact Nat.Coprime.of_dvd_right (orderOf_dvd_of_pow_eq_one hn)
        (hp.coprime_pow_of_not_dvd (m := n + 1) hm)
  obtain ⟨r, hr⟩ := exists_pow_eq_self_of_coprime (x := a) (n := m) hcop
  let x : S := x₀ ^ (m * r)
  have hxQ : (x : S ⧸ Subgroup.center S) = a := by
    show ((x₀ ^ (m * r) : S) : S ⧸ Subgroup.center S) = a
    rw [QuotientGroup.mk_pow, show (x₀ : S ⧸ Subgroup.center S) = a from hx₀, pow_mul, hr]
  have hxpow : x ^ (p ^ k) = 1 := by
    have hpk : x₀ ^ (p ^ k * m) = 1 := by
      rw [← hkm]
      exact pow_orderOf_eq_one x₀
    calc x ^ (p ^ k) = (x₀ ^ (m * r)) ^ (p ^ k) := rfl
      _ = x₀ ^ ((m * r) * (p ^ k)) := (pow_mul x₀ (m * r) (p ^ k)).symm
      _ = (x₀ ^ (p ^ k * m)) ^ r := by
            rw [show (m * r) * (p ^ k) = (p ^ k * m) * r by ring]
            exact pow_mul x₀ (p ^ k * m) r
      _ = 1 := by rw [hpk, one_pow]
  have hfixx : (β x : S ⧸ Subgroup.center S) = a := hfix x hxQ
  have hz : x⁻¹ * β x ∈ Subgroup.center S := by
    have h1 : (β x : S ⧸ Subgroup.center S) = (x : S ⧸ Subgroup.center S) := by
      rw [hfixx, hxQ]
    have h2 : (β x)⁻¹ * x ∈ Subgroup.center S := QuotientGroup.eq.1 h1
    simpa using Subgroup.inv_mem _ h2
  have hcent : ∀ g : S, g * (x⁻¹ * β x) = (x⁻¹ * β x) * g :=
    Subgroup.mem_center_iff.1 hz
  have hβx : β x = x * (x⁻¹ * β x) := by group
  have hcomm : Commute x (β x) := by
    rw [hβx]
    exact (Commute.refl x).mul_right (hcent x)
  let y : S := x * β x
  have hyfix : β y = y := by
    have hββ : β (β x) = x := by
      have h := DFunLike.congr_fun hβ x
      simpa [pow_two, MulAut.mul_apply] using h
    show β (x * β x) = x * β x
    rw [map_mul, hββ]
    exact hcomm.symm
  have hypow : y ^ (p ^ k) = 1 := by
    have hβpow : (β x) ^ (p ^ k) = 1 := by
      rw [← map_pow, hxpow, map_one]
    show (x * β x) ^ (p ^ k) = 1
    rw [Commute.mul_pow hcomm, hxpow, hβpow, mul_one]
  have hyQ : (y : S ⧸ Subgroup.center S) = a * a := by
    show ((x * β x : S) : S ⧸ Subgroup.center S) = a * a
    rw [QuotientGroup.mk_mul, hxQ, hfixx]
  have hy1 : y ≠ 1 := by
    intro hy
    have h2 : a ^ 2 = 1 := by
      rw [pow_two]
      have h : (y : S ⧸ Subgroup.center S) = 1 := by rw [hy]; rfl
      rw [hyQ] at h
      exact h
    have hdvd2 : orderOf a ∣ 2 := orderOf_dvd_of_pow_eq_one h2
    rcases (Nat.dvd_prime Nat.prime_two).1 hdvd2 with h1 | h1
    · exact ha (orderOf_eq_one_iff.1 h1)
    · exfalso
      have hdvdp : 2 ∣ p ^ n := h1 ▸ orderOf_dvd_of_pow_eq_one hn
      have h2p : 2 ∣ p := Nat.prime_two.dvd_of_dvd_pow hdvdp
      exact hp2 ((Nat.prime_dvd_prime_iff_eq Nat.prime_two hp).1 h2p).symm
  exact ⟨y, hy1, ⟨k, hypow⟩, hyfix⟩

private theorem exists_fixed_pElement_of_lieModel_psp_aux {S : Type} [Group S] [Finite S]
    {r p f : ℕ} (hp2 : p ≠ 2) (K : Type) [Field K] [Finite K] (hp : p.Prime) (hf : 1 ≤ f)
    (hr : 2 ≤ r) (hKcard : Nat.card K = p ^ f)
    (e : S ⧸ Subgroup.center S ≃* StatedProj (StatedSp r K))
    (β : MulAut S) (hβ : β ^ 2 = 1) :
    ∃ u : S, u ≠ 1 ∧ (∃ n : ℕ, u ^ (p ^ n) = 1) ∧ β u = u := by
  classical
  have hchar : CharP K p :=
    CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic hp hf hKcard
  have hK2 : ringChar K ≠ 2 := by
    rw [ringChar.eq K p]
    exact hp2
  have hZmap : (Subgroup.center S).map β.toMonoidHom = Subgroup.center S := by
    simpa only [MulEquiv.toMonoidHom_eq_coe] using Subgroup.map_center_eq β
  let βbar : MulAut (S ⧸ Subgroup.center S) :=
    QuotientGroup.congr (Subgroup.center S) (Subgroup.center S) β hZmap
  have hβbar_mk : ∀ x : S, βbar (x : S ⧸ Subgroup.center S) =
      (β x : S ⧸ Subgroup.center S) := fun x => rfl
  have hβbar : βbar ^ 2 = 1 := by
    refine MulEquiv.ext fun q => ?_
    rw [pow_two, MulAut.mul_apply, MulAut.one_apply]
    induction q using QuotientGroup.induction_on with
    | H x =>
      have hββ : β (β x) = x := by
        have h := DFunLike.congr_fun hβ x
        simpa [pow_two, MulAut.mul_apply] using h
      rw [hβbar_mk, hβbar_mk, hββ]
  let β' : MulAut (StatedProj (StatedSp r K)) := MulAut.congr e βbar
  have hβ' : β' ^ 2 = 1 := by
    calc β' ^ 2 = (MulAut.congr e βbar) ^ 2 := rfl
      _ = MulAut.congr e (βbar ^ 2) := (map_pow (MulAut.congr e) βbar 2).symm
      _ = MulAut.congr e 1 := by rw [hβbar]
      _ = 1 := map_one _
  obtain ⟨u', hu'1, hu'pow, hu'fix⟩ := exists_fixed_pElement_statedProj_sp hK2 hr β' hβ'
  let a : S ⧸ Subgroup.center S := e.symm u'
  have ha : a ≠ 1 := by
    intro h
    apply hu'1
    have h1 : e a = 1 := by rw [h, map_one]
    rwa [show e a = u' from e.apply_symm_apply u'] at h1
  have hKp : ringChar K = p := ringChar.eq K p
  have hap : ∃ n : ℕ, a ^ (p ^ n) = 1 := by
    refine ⟨1, ?_⟩
    have hu'p : u' ^ p = 1 := by rw [← hKp]; exact hu'pow
    show (e.symm u') ^ (p ^ 1) = 1
    rw [pow_one, ← map_pow, hu'p, map_one]
  have hfix : ∀ x : S, (x : S ⧸ Subgroup.center S) = a →
      (β x : S ⧸ Subgroup.center S) = a := by
    intro x hx
    have h2 : βbar (e.symm u') = e.symm u' := by
      have h3 : e (βbar (e.symm u')) = u' := by
        simpa [β', MulAut.congr_apply] using hu'fix
      exact e.injective (by rw [h3, e.apply_symm_apply])
    calc (β x : S ⧸ Subgroup.center S) = βbar (x : S ⧸ Subgroup.center S) :=
          (hβbar_mk x).symm
      _ = βbar (e.symm u') := by rw [hx]
      _ = e.symm u' := h2
  exact exists_fixed_pElement_of_center_quotient hp hp2 β hβ a ha hap hfix

theorem exists_fixed_pElement_of_lieModel_psp {S : Type} [Group S] [Finite S] {r p f : ℕ}
    (hp2 : p ≠ 2) (hS : CFSG.Blueprint.LieModel (S ⧸ Subgroup.center S) .PSp r p f)
    (β : MulAut S) (hβ : β ^ 2 = 1) :
    ∃ u : S, u ≠ 1 ∧ (∃ n : ℕ, u ^ (p ^ n) = 1) ∧ β u = u := by
  have hCM : CFSG.Open.StatedClassicalModel (S ⧸ Subgroup.center S) .PSp r p f :=
    CFSG.Blueprint.LieModel.statedClassicalModel hS (by decide)
  obtain ⟨hadm, K, hKfield, hKfin, hKcard, ⟨e⟩⟩ := hCM
  obtain ⟨hp, hf, hr, -⟩ := hadm
  exact @exists_fixed_pElement_of_lieModel_psp_aux S _ _ r p f hp2 K hKfield hKfin hp hf hr
    hKcard e β hβ

end CFSG.LocalAnalysis.WeakClosure81

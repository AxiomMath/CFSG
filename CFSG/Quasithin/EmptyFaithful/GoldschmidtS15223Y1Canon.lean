module

public import CFSG.Quasithin.EmptyFaithful.GoldschmidtS15223Y1Base

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique
open scoped commutatorElement

namespace S15223

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem commutator_le_inf_of_normalizes {A B : Subgroup G}
    (hA : A ≤ Subgroup.normalizer (B : Set G)) (hB : B ≤ Subgroup.normalizer (A : Set G)) :
    ⁅A, B⁆ ≤ A ⊓ B := by
  rw [Subgroup.commutator_le]
  intro a ha b hb
  have h1 : a * b * a⁻¹ ∈ B := (Subgroup.mem_normalizer_iff.mp (hA ha) b).mp hb
  have h2 : b * a⁻¹ * b⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp (hB hb) a⁻¹).mp (A.inv_mem ha)
  refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
  · have e : ⁅a, b⁆ = a * (b * a⁻¹ * b⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact A.mul_mem ha h2
  · have e : ⁅a, b⁆ = (a * b * a⁻¹) * b⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact B.mul_mem h1 (B.inv_mem hb)

omit [Finite G] in
theorem ne_bot_of_quot_perm {Y S : Subgroup G} (hS : IsPGroup 2 S)
    (h : Nonempty (OTwoQuot (Y ⊔ S) ≃* Equiv.Perm (Fin 3))) : Y ≠ ⊥ := by
  rintro rfl
  obtain ⟨e⟩ := h
  have hX : IsPGroup 2 ↥((⊥ : Subgroup G) ⊔ S) := by
    rw [bot_sup_eq]
    exact hS
  have hP : IsPGroup 2 (Equiv.Perm (Fin 3)) :=
    (hX.to_quotient (CFSG.Open.pCore 2 ↥((⊥ : Subgroup G) ⊔ S))).of_equiv e
  obtain ⟨n, hn⟩ := (IsPGroup.iff_card (p := 2)).mp hP
  have h3 : 3 ∣ Nat.card (Equiv.Perm (Fin 3)) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_perm, Fintype.card_fin]
    decide
  rw [hn] at h3
  have := (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3)
  omega

omit [Finite G] in
theorem autOn_oPrimeResidual_ne_bot {M V N : Subgroup G}
    (hMV : M ≤ Subgroup.normalizer (V : Set G)) (hNM : N ≤ M)
    (h3p : ¬ 3 ∣ Nat.card ↥(M ⊓ Subgroup.centralizer (V : Set G)))
    (hne : oPrimeResidualOf 3 N ≠ ⊥) : autOn (oPrimeResidualOf 3 N) V ≠ ⊥ := by
  intro h0
  apply hne
  rw [eq_bot_iff]
  refine (Subgroup.closure_le _).mpr ?_
  rintro g ⟨hgN, k, hk⟩
  have hgM : g ∈ M := hNM hgN
  have hgY : g ∈ oPrimeResidualOf 3 N := Subgroup.subset_closure ⟨hgN, k, hk⟩
  have h1 : conjAct V ⟨g, hMV hgM⟩ = 1 := by
    have := mem_autOn_of_mem (hMV hgM) hgY
    rw [h0, Subgroup.mem_bot] at this
    exact this
  have hgC : g ∈ Subgroup.centralizer (V : Set G) := A4.conjAct_eq_one_iff.mp h1
  have hdvd := Subgroup.orderOf_dvd_natCard _ (Subgroup.mem_inf.mpr ⟨hgM, hgC⟩)
  rw [hk] at hdvd
  rcases k with _ | k
  · rw [pow_zero, orderOf_eq_one_iff] at hk
    exact Subgroup.mem_bot.mpr hk
  · exact absurd (dvd_trans (dvd_pow_self 3 (Nat.succ_ne_zero k)) hdvd) h3p

theorem dvd_nine {n : ℕ} (hn : n ∣ 9) : n = 1 ∨ n = 3 ∨ n = 9 := by
  have h1 : n ∈ Nat.divisors 9 := Nat.mem_divisors.mpr ⟨hn, by norm_num⟩
  have h9 : Nat.divisors 9 = {1, 3, 9} := by decide
  rw [h9] at h1
  simpa using h1

theorem abstract_step {M V N : Subgroup G} (hMV : M ≤ Subgroup.normalizer (V : Set G))
    (hNM : N ≤ M) (hC : M ⊓ Subgroup.centralizer (V : Set G) ≤ N)
    (hEc : ∀ a ∈ oTwoUpper (autOn M V), ∀ b ∈ oTwoUpper (autOn M V), a * b = b * a)
    (hE9 : Nat.card (oTwoUpper (autOn M V)) = 9) {t : G} (htM : t ∈ M)
    (hD0 : autOn (oPrimeResidualOf 3 N) V ≠ ⊥)
    (hnle : ¬ autOn (oPrimeResidualOf 3 N) V ≤ autOn (conjSub t (oPrimeResidualOf 3 N)) V) :
    ⁅oPrimeResidualOf 3 N, conjSub t (oPrimeResidualOf 3 N)⁆ ≤
        oPrimeResidualOf 3 N ⊓ conjSub t (oPrimeResidualOf 3 N) ∧
      autOn (oPrimeResidualOf 3 N ⊔ conjSub t (oPrimeResidualOf 3 N)) V =
        oTwoUpper (autOn M V) := by
  set Y := oPrimeResidualOf 3 N with hYdef
  set E := oTwoUpper (autOn M V) with hEdef
  have hYM : Y ≤ M := oPrimeResidual_le.trans hNM
  have hDE : autOn Y V ≤ E := autOn_oPrimeResidual_le hMV hNM
  have hct : conjAct V ⟨t, hMV htM⟩ ∈ autOn M V := mem_autOn_of_mem (hMV htM) htM
  have hcE : ∀ e ∈ E, conjAct V ⟨t, hMV htM⟩ * e * (conjAct V ⟨t, hMV htM⟩)⁻¹ ∈ E :=
    fun e he => (Subgroup.mem_normalizer_iff.mp (le_normalizer_oTwoUpper _ hct) e).mp he
  have hYtM : conjSub t Y ≤ M := by
    intro x hx
    have h1 := mem_conjSub.mp hx
    have e : x = t * (t⁻¹ * x * t) * t⁻¹ := by group
    rw [e]
    exact M.mul_mem (M.mul_mem htM (hYM h1)) (M.inv_mem htM)
  have hDtE : autOn (conjSub t Y) V ≤ E := by
    rw [autOn_conjSub_eq hMV htM hYM]
    rintro _ ⟨d, hd, rfl⟩
    exact hcE d (hDE hd)
  have hYtN : conjSub t Y ≤ Subgroup.normalizer (Y : Set G) := fun b hb =>
    mem_normalizer_oPrimeResidual_of_comm hMV hNM hC hEc hDE (hYtM hb)
      (hDtE (mem_autOn_of_mem (hMV (hYtM hb)) hb))
  have hYN : Y ≤ Subgroup.normalizer (conjSub t Y : Set G) := by
    intro a ha
    have haM : a ∈ M := hYM ha
    have htiM : t⁻¹ ∈ M := M.inv_mem htM
    have hx : t⁻¹ * a * t⁻¹⁻¹ ∈ M := M.mul_mem (M.mul_mem htiM haM) (M.inv_mem htiM)
    have hxN : t⁻¹ * a * t⁻¹⁻¹ ∈ Subgroup.normalizer (Y : Set G) := by
      refine mem_normalizer_oPrimeResidual_of_comm hMV hNM hC hEc hDE hx ?_
      rw [conjAct_conj (hMV htiM) (hMV haM) (hMV hx)]
      exact (Subgroup.mem_normalizer_iff.mp
        (le_normalizer_oTwoUpper _ (mem_autOn_of_mem (hMV htiM) htiM)) _).mp
        (hDE (mem_autOn_of_mem (hMV haM) ha))
    have e : a * t = t * (t⁻¹ * a * t⁻¹⁻¹) := by group
    apply mem_normalizer_of_conjSub_eq152
    rw [← conjSub_mul, e, conjSub_mul, conjSub_eq_self152 hxN]
  refine ⟨commutator_le_inf_of_normalizes hYN hYtN, ?_⟩
  rw [autOn_sup (hYM.trans hMV) (hYtM.trans hMV)]
  have hcard : Nat.card (autOn (conjSub t Y) V) = Nat.card (autOn Y V) := by
    rw [autOn_conjSub_eq hMV htM hYM]
    exact Subgroup.card_map_of_injective (MulAut.conj _).injective
  have hD1 : Nat.card (autOn Y V) ≠ 1 := fun h => hD0 (Subgroup.card_eq_one.mp h)
  have hJE : autOn Y V ⊔ autOn (conjSub t Y) V ≤ E := sup_le hDE hDtE
  have hJ9 : Nat.card ↥(autOn Y V ⊔ autOn (conjSub t Y) V) ∣ 9 :=
    hE9 ▸ Subgroup.card_dvd_of_le hJE
  have hD'J : Nat.card (autOn (conjSub t Y) V) ∣
      Nat.card ↥(autOn Y V ⊔ autOn (conjSub t Y) V) := Subgroup.card_dvd_of_le le_sup_right
  have hfE : Finite E := Nat.finite_of_card_ne_zero (by omega)
  have hfJ : Finite ↥(autOn Y V ⊔ autOn (conjSub t Y) V) :=
    Finite.of_injective (Subgroup.inclusion hJE) (Subgroup.inclusion_injective hJE)
  have hne : Nat.card (autOn (conjSub t Y) V) ≠
      Nat.card ↥(autOn Y V ⊔ autOn (conjSub t Y) V) := by
    intro h
    apply hnle
    have := Subgroup.eq_of_le_of_card_ge
      (le_sup_right : autOn (conjSub t Y) V ≤ autOn Y V ⊔ autOn (conjSub t Y) V) h.ge
    rw [this]
    exact le_sup_left
  have h9 : Nat.card ↥(autOn Y V ⊔ autOn (conjSub t Y) V) = 9 := by
    have hD'9 := dvd_nine (dvd_trans hD'J hJ9)
    rcases dvd_nine hJ9 with h | h | h <;> rcases hD'9 with h' | h' | h' <;>
      rw [h, h'] at hD'J <;> omega
  exact Subgroup.eq_of_le_of_card_ge hJE (by omega)

end S15223

end CFSG.Quasithin

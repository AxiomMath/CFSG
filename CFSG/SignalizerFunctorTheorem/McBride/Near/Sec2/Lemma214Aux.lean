module

public import CFSG.SignalizerFunctorTheorem.McBride.Near.Sec2.Lemma212Aux

public section

namespace CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma214

variable {Γ : Type*} [Group Γ]

theorem mem_normalizer_of_map_conj_eq {J : Subgroup Γ} {a b : Γ}
    (h : J.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj b).toMonoidHom) :
    b⁻¹ * a ∈ Subgroup.normalizer (J : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  have h1 := Thm210.map_conj_map_conj J a b⁻¹
  rw [h, Lemma212.map_conj_map_conj_inv] at h1
  exact h1.symm

theorem exists_equivariant_fn {A J : Subgroup Γ} {x : Γ} (hxJ : x ∈ J)
    (hx : x ∈ Subgroup.centralizer ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ)) :
    ∃ f : Subgroup Γ → Γ, (∀ K, f K ∈ K) ∧ f J = x ∧
      (∀ c ∈ A, ∀ K, f (K.map (MulAut.conj c).toMonoidHom) = c * f K * c⁻¹) ∧
      ∀ K, f K = 1 ∨ ∃ a ∈ A, f K = a * x * a⁻¹ := by
  classical
  have key : ∀ a ∈ A, ∀ b ∈ A,
      J.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj b).toMonoidHom →
        a * x * a⁻¹ = b * x * b⁻¹ := by
    intro a ha b hb hab
    have hmem : b⁻¹ * a ∈ A ⊓ Subgroup.normalizer (J : Set Γ) :=
      Subgroup.mem_inf.mpr ⟨mul_mem (inv_mem hb) ha, mem_normalizer_of_map_conj_eq hab⟩
    have hc := Subgroup.mem_centralizer_iff.mp hx (b⁻¹ * a) hmem
    calc a * x * a⁻¹ = b * (b⁻¹ * a * x) * a⁻¹ := by group
      _ = b * (x * (b⁻¹ * a)) * a⁻¹ := by rw [hc]
      _ = b * x * b⁻¹ := by group
  let f : Subgroup Γ → Γ := fun K =>
    if h : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom then h.choose * x * h.choose⁻¹ else 1
  have f_orbit : ∀ a ∈ A, f (J.map (MulAut.conj a).toMonoidHom) = a * x * a⁻¹ := by
    intro a ha
    have h : ∃ b ∈ A, J.map (MulAut.conj a).toMonoidHom = J.map (MulAut.conj b).toMonoidHom :=
      ⟨a, ha, rfl⟩
    simp only [f, dite_eq_left h]
    exact key _ h.choose_spec.1 a ha h.choose_spec.2.symm
  have f_not : ∀ K, (¬ ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom) → f K = 1 := by
    intro K hK
    simp only [f, dite_eq_right hK]
  refine ⟨f, ?_, ?_, ?_, ?_⟩
  · intro K
    by_cases h : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom
    · obtain ⟨a, ha, rfl⟩ := h
      rw [f_orbit a ha]
      exact ⟨x, hxJ, rfl⟩
    · rw [f_not K h]
      exact one_mem K
  · have := f_orbit 1 (one_mem A)
    rwa [Thm210.map_conj_one, one_mul, inv_one, mul_one] at this
  · intro c hc K
    by_cases h : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom
    · obtain ⟨a, ha, rfl⟩ := h
      rw [Thm210.map_conj_map_conj, f_orbit a ha, f_orbit (c * a) (mul_mem hc ha)]
      group
    · have h' : ¬ ∃ a ∈ A,
          K.map (MulAut.conj c).toMonoidHom = J.map (MulAut.conj a).toMonoidHom := by
        rintro ⟨b, hb, hKb⟩
        refine h ⟨c⁻¹ * b, mul_mem (inv_mem hc) hb, ?_⟩
        rw [← Thm210.map_conj_map_conj, ← hKb, Lemma212.map_conj_map_conj_inv]
      rw [f_not K h, f_not _ h']
      group
  · intro K
    by_cases h : ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom
    · obtain ⟨a, ha, rfl⟩ := h
      exact Or.inr ⟨a, ha, f_orbit a ha⟩
    · exact Or.inl (f_not K h)

section Finite

variable [Finite Γ]

theorem exists_coord_eq {S : Set (Subgroup Γ)} {L A : Subgroup Γ} (hL : IsDirectProduct S L)
    (hA : ∀ a ∈ A, ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S) {J : Subgroup Γ} (hJ : J ∈ S)
    {x : Γ} (hxJ : x ∈ J)
    (hx : x ∈ Subgroup.centralizer ((A ⊓ Subgroup.normalizer (J : Set Γ) : Subgroup Γ) : Set Γ)) :
    ∃ y : L, (y : Γ) ∈ Subgroup.centralizer (A : Set Γ) ∧ ((hL.coord hJ y : J) : Γ) = x ∧
      ∀ M : Subgroup Γ, (∀ a ∈ A, a * x * a⁻¹ ∈ M) → (y : Γ) ∈ M := by
  obtain ⟨f, hfK, hfJ, hfc, hfv⟩ := exists_equivariant_fn hxJ hx
  let z : (K : S) → (K : Subgroup Γ) := fun K => ⟨f K, hfK K⟩
  let y : L := hL.equiv z
  have hcoord : ∀ (K : Subgroup Γ) (hK : K ∈ S), ((hL.coord hK y : K) : Γ) = f K :=
    fun K hK => congrArg Subtype.val (hL.coord_equiv hK z)
  refine ⟨y, ?_, ?_, ?_⟩
  · rw [Subgroup.mem_centralizer_iff]
    intro c hc
    have hc' := hA c hc
    have hy : (⟨c * (y : Γ) * c⁻¹, hL.conj_mem hc' y.2⟩ : L) = y := by
      refine hL.ext_coord fun K hK => Subtype.ext ?_
      have hK₀ : K.map (MulAut.conj c⁻¹).toMonoidHom ∈ S := hA c⁻¹ (inv_mem hc) K hK
      have hK₀c : (K.map (MulAut.conj c⁻¹).toMonoidHom).map (MulAut.conj c).toMonoidHom = K := by
        simpa using Lemma212.map_conj_map_conj_inv K c⁻¹
      have h1 := hL.coord_conj hc' hK₀ y.2
      have h2 := hL.coord_val_congr hK (hc' _ hK₀) hK₀c.symm
        ⟨c * (y : Γ) * c⁻¹, hL.conj_mem hc' y.2⟩
      rw [h2, h1, hcoord _ hK₀, hcoord K hK, ← hfc c hc, hK₀c]
    have h : c * (y : Γ) * c⁻¹ = y := congrArg Subtype.val hy
    calc c * (y : Γ) = c * (y : Γ) * c⁻¹ * c := by group
      _ = (y : Γ) * c := by rw [h]
  · rw [hcoord J hJ, hfJ]
  · intro M hM
    refine hL.equiv_mem z fun K => ?_
    rcases hfv K with h | ⟨a, ha, h⟩
    · show f K ∈ M
      rw [h]
      exact one_mem M
    · show f K ∈ M
      rw [h]
      exact hM a ha

end Finite

theorem mem_zpowers_of_mem_zpowers {p : ℕ} (hp : p.Prime) [Finite Γ] {a b : Γ} (ha : a ^ p = 1)
    (ha1 : a ≠ 1) (hb : b ∈ Subgroup.zpowers a) (hb1 : b ≠ 1) : a ∈ Subgroup.zpowers b := by
  have := Fact.mk hp
  have hord : orderOf a = p := orderOf_eq_prime ha ha1
  have hordb : orderOf b = p := by
    rcases (Nat.dvd_prime hp).mp (hord ▸ orderOf_dvd_of_mem_zpowers hb) with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hb1
    · exact h
  have hzeq : Subgroup.zpowers b = Subgroup.zpowers a :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb)
      (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hordb])
  rw [hzeq]
  exact Subgroup.mem_zpowers a

theorem pow_apply_eq_of_apply_eq {X : Type*} [Group X] {f : MulAut X} {x : X} (hx : f x = x)
    (n : ℕ) : (f ^ n) x = x := by
  induction n with
  | zero => simp
  | succ n ih => rw [pow_succ, MulAut.mul_apply, hx, ih]

theorem apply_eq_of_pow_apply_eq {X : Type*} [Group X] {p : ℕ} (hp : p.Prime) {f : MulAut X}
    (hf : orderOf f = p) {k : ℕ} (hk : ¬ p ∣ k) {x : X} (hx : (f ^ k) x = x) : f x = x := by
  have hcop : Nat.Coprime k p := ((Nat.Prime.coprime_iff_not_dvd hp).2 hk).symm
  obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hp.one_lt
  have hfp : f ^ p = 1 := hf ▸ pow_orderOf_eq_one f
  have e : (f ^ k) ^ m = f := by
    rw [← pow_mul, pow_eq_pow_mod (k * m) hfp, hm, pow_one]
  rw [← e]
  exact pow_apply_eq_of_apply_eq hx m

end CFSG.SignalizerFunctorTheorem.McBride.Near.Lemma214

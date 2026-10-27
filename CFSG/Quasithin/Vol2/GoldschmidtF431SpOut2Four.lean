module

public import CFSG.Quasithin.Vol2.GoldschmidtF431SpOut2Lie

public section

namespace CFSG.Quasithin.H13.F431

open Matrix CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  CFSG.QuasithinUnique.Setup.X7b CFSG.RankThree.PartOne.KCRootAxis CFSG.Quasithin.H13.F431.SpModel
  CFSG.QuasithinUnique CFSG.Open CFSG.Quasithin CFSG.LieType.BorelTits CFSG.Blueprint

universe u

section Four

variable {Mb : Type u} [Group Mb]

structure F431SpOut4 (T S : Subgroup Mb) (f : Mb) (N1 N2 : Subgroup Mb) (I : Finset Mb)
    (i0 i1 : Mb) : Prop where
  core : F431SpOutCore T S f N1 N2 I
  i0_mem : i0 ∈ I
  i1_mem : i1 ∈ I
  i0_ne : i0 ≠ i1
  i0_Z : i0 ∈ spZ N1 N2 0
  i1_Z : i1 ∈ spZ N1 N2 1
  Zf : ∀ z ∈ centerOf (spTf T f), (z = 1 ∨ z ∈ I) ∨ (f * z = 1 ∨ f * z ∈ I)
  fconj : ∀ k ∈ I, ∃ t ∈ T, t * f * t⁻¹ = f * k

end Four

namespace SpOut2

section XFour

variable {F : Type} [Field F] [Finite F] [CharP F 2]

structure SpOutFourData (U : Subgroup (antiSp F)) (i : Fin 3 → antiSp F) : Prop where
  central_fixed : ∀ u ∈ centerOf U, (frobAut F ^ 1) u = u → u = 1 ∨ ∃ k, u = i k
  conj_wit : ∀ k, ∃ x ∈ U, x * ((frobAut F ^ 1) x)⁻¹ = i k

omit [Finite F] in
theorem iRep_zero : iRep F 0 = uElt 0 1 0 0 := rfl
omit [Finite F] in
theorem iRep_one : iRep F 1 = uElt 0 0 1 0 := rfl
omit [Finite F] in
theorem iRep_two : iRep F 2 = uElt 0 1 1 0 := rfl

omit [Finite F] [CharP F 2] in
theorem eq_zero_or_one_of_sq {x : F} (h : x ^ 2 = x) : x = 0 ∨ x = 1 := by
  have : x * (x - 1) = 0 := by linear_combination h
  rcases mul_eq_zero.mp this with h | h
  · exact Or.inl h
  · exact Or.inr (sub_eq_zero.mp h)

theorem exists_omega_four (hK : Nat.card F = 2 ^ (2 * 1)) : ∃ ω : F, ω ^ 2 + ω = 1 := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hn : 1 ≤ 2 * 1 := by norm_num
  have hne : frobAut F ^ 1 ≠ 1 := by
    rw [Ne, frobAut_pow_eq_one_iff hn hK]
    norm_num
  have hex : ∃ x : F, x ^ 2 ^ 1 ≠ x := by
    by_contra hcon
    push Not at hcon
    exact hne (frobAut_pow_eq_one_of_fix hcon)
  obtain ⟨x, hx⟩ := hex
  rw [pow_one] at hx
  have hx4 : x ^ 4 = x := by
    have : Fintype F := Fintype.ofFinite F
    have h := FiniteField.pow_card x
    rw [← Nat.card_eq_fintype_card, hK] at h
    simpa using h
  have hy0 : x ^ 2 + x ≠ 0 := by
    intro h
    apply hx
    linear_combination h - x * h2
  have hy2 : (x ^ 2 + x) ^ 2 = x ^ 2 + x := by
    linear_combination hx4 + x ^ 3 * h2
  have hy1 : x ^ 2 + x = 1 := by
    have : (x ^ 2 + x) * (x ^ 2 + x - 1) = 0 := by linear_combination hy2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hy0
    · exact sub_eq_zero.mp h
  exact ⟨x, hy1⟩

theorem central_fixed_four {u : antiSp F} (hu : u ∈ centerOf (antiUnipotent F))
    (hfix : (frobAut F ^ 1) u = u) : u = 1 ∨ ∃ k, u = iRep F k := by
  rw [centerOf_antiUnipotent] at hu
  obtain ⟨b, c, rfl⟩ := hu
  rw [frobAut_pow_uElt] at hfix
  obtain ⟨-, hb, hc, -⟩ := uElt_inj hfix
  rw [pow_one] at hb hc
  rcases eq_zero_or_one_of_sq hb with rfl | rfl <;> rcases eq_zero_or_one_of_sq hc with rfl | rfl
  · exact Or.inl uElt_zero_eq_one
  · exact Or.inr ⟨1, rfl⟩
  · exact Or.inr ⟨0, rfl⟩
  · exact Or.inr ⟨2, rfl⟩

theorem conj_wit_four (hK : Nat.card F = 2 ^ (2 * 1)) (k : Fin 3) :
    ∃ x ∈ antiUnipotent F, x * ((frobAut F ^ 1) x)⁻¹ = iRep F k := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  obtain ⟨ω, hω⟩ := exists_omega_four hK
  have key : ∀ b c : F, uElt 0 b c 0 * ((frobAut F ^ 1) (uElt 0 b c 0))⁻¹ =
      uElt 0 (b + b ^ 2) (c + c ^ 2) 0 := by
    intro b c
    rw [frobAut_pow_uElt, uElt_inv, uElt_mul]
    simp only [pow_one, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true, zero_pow, mul_zero,
      add_zero, zero_mul]
  have hω' : ω + ω ^ 2 = 1 := by rw [add_comm]; exact hω
  have h0 : ∃ x ∈ antiUnipotent F, x * ((frobAut F ^ 1) x)⁻¹ = uElt 0 1 0 0 := by
    refine ⟨uElt 0 ω 0 0, ⟨0, ω, 0, 0, rfl⟩, ?_⟩
    rw [key, hω']
    simp
  have h1 : ∃ x ∈ antiUnipotent F, x * ((frobAut F ^ 1) x)⁻¹ = uElt 0 0 1 0 := by
    refine ⟨uElt 0 0 ω 0, ⟨0, 0, ω, 0, rfl⟩, ?_⟩
    rw [key, hω']
    simp
  have h2' : ∃ x ∈ antiUnipotent F, x * ((frobAut F ^ 1) x)⁻¹ = uElt 0 1 1 0 := by
    refine ⟨uElt 0 ω ω 0, ⟨0, ω, ω, 0, rfl⟩, ?_⟩
    rw [key, hω']
  exact forall_fin3 (P := fun x => ∃ y ∈ antiUnipotent F, y * ((frobAut F ^ 1) y)⁻¹ = x) h0 h1 h2' k

theorem spOutFourData_antiSp (hK : Nat.card F = 2 ^ (2 * 1)) :
    SpOutFourData (antiUnipotent F) (iRep F) :=
  ⟨fun _ hu hfix => central_fixed_four hu hfix, conj_wit_four hK⟩

theorem SpOutFourData.swap {U : Subgroup (antiSp F)} {i : Fin 3 → antiSp F}
    (h : SpOutFourData U i) : SpOutFourData U ![i 1, i 0, i 2] := by
  refine ⟨fun u hu hfix => ?_, forall_swap3 (P := fun x => ∃ y ∈ U, y * ((frobAut F ^ 1) y)⁻¹ = x)
    (h.conj_wit 0) (h.conj_wit 1) (h.conj_wit 2)⟩
  rcases h.central_fixed u hu hfix with h1 | ⟨k, hk⟩
  · exact Or.inl h1
  · refine Or.inr ?_
    fin_cases k
    · exact ⟨1, hk⟩
    · exact ⟨0, hk⟩
    · exact ⟨2, hk⟩

end XFour

section FourAbs

variable {F : Type} [Field F] [Finite F] [CharP F 2] {H : Type u} [Group H] [Finite H]
  {Φ : antiSp F →* H} {ψ : H} {k₀ : ℕ}
  {U : Subgroup (antiSp F)} {R : Fin 2 → Subgroup (antiSp F)} {i : Fin 3 → antiSp F}
  {N : Fin 2 → Subgroup H}

theorem frobAut_pow_fixed {t : antiSp F} (ht : (frobAut F ^ 1) t = t) (j : ℕ) :
    (frobAut F ^ j) t = t := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', MulAut.mul_apply, ih]
    simpa using ht

theorem OutCtx.psi2_pow_four (C : OutCtx 1 Φ ψ k₀ U R i N) (hev : Even (orderOf ψ)) (s : ℕ) :
    psi2 ψ ^ s = 1 ∨ psi2 ψ ^ s = spf ψ := by
  have h1 : orderOf ψ = 2 := by
    have hle := C.orderOf_le
    have hpos := orderOf_pos ψ
    obtain ⟨c, hc⟩ := hev
    omega
  have h2 : twoExp ψ = 1 := by
    unfold twoExp
    rw [h1]
    exact Nat.prime_two.factorization_self
  have h3 : orderOf (psi2 ψ) = 2 := by rw [orderOf_psi2, h2]; norm_num
  have h4 : spf ψ = psi2 ψ := by
    unfold spf
    rw [h2]
    simp
  rw [h4, ← pow_mod_orderOf, h3]
  have : s % 2 = 0 ∨ s % 2 = 1 := Nat.mod_two_eq_zero_or_one s
  rcases this with h | h
  · left; rw [h, pow_zero]
  · right; rw [h, pow_one]

theorem OutCtx.four (C : OutCtx 1 Φ ψ k₀ U R i N) (hev : Even (orderOf ψ))
    (D4 : SpOutFourData U i) :
    F431SpOut4 (spT Φ ψ U) (U.map Φ) (spf ψ) (N 0) (N 1) (spI Φ i) (Φ (i 0)) (Φ (i 1)) where
  core := C.core hev
  i0_mem := mem_spI.mpr ⟨0, rfl⟩
  i1_mem := mem_spI.mpr ⟨1, rfl⟩
  i0_ne := fun h => by
    have := C.nonconj (k := 0) (k' := 1) (by rw [h])
    exact absurd this (by decide)
  i0_Z := by
    rw [C.spZ_eq 0]
    exact Subgroup.mem_map_of_mem Φ C.hD.i0
  i1_Z := by
    rw [C.spZ_eq 1]
    exact Subgroup.mem_map_of_mem Φ C.hD.i1
  Zf := by
    intro z hz
    have hzT := (mem_centerOf_iff.mp hz).1
    obtain ⟨u, ⟨hu, hfix⟩, s, rfl⟩ := (C.mem_spTf_iff hev).mp hzT
    have hfix' : (frobAut F ^ 1) u = u := hfix
    obtain ⟨a, d, ha, hd, hafix, hdfix, hgen⟩ := C.X.gens
    have hcomm : ∀ t : antiSp F, t ∈ U → (∀ k, (frobAut F ^ k) t = t) → t * u = u * t := by
      intro t ht htfix
      have hT : Φ t ∈ spTf (spT Φ ψ U) (spf ψ) :=
        (C.mem_spTf_iff hev).mpr ⟨t, ⟨ht, htfix 1⟩, 0, by simp⟩
      have h1 := (mem_centerOf_iff.mp hz).2 _ hT
      have h2 : Φ t * Φ u * psi2 ψ ^ s = Φ u * Φ t * psi2 ψ ^ s := by
        calc Φ t * Φ u * psi2 ψ ^ s = Φ t * (Φ u * psi2 ψ ^ s) := mul_assoc _ _ _
          _ = Φ u * psi2 ψ ^ s * Φ t := h1
          _ = Φ u * (psi2 ψ ^ s * Φ t) := mul_assoc _ _ _
          _ = Φ u * (Φ t * psi2 ψ ^ s) := by rw [C.P.psi2_pow_commute htfix s]
          _ = Φ u * Φ t * psi2 ψ ^ s := (mul_assoc _ _ _).symm
      have h3 := mul_right_cancel h2
      exact C.P.inj (by rw [map_mul, map_mul]; exact h3)
    have hu0 : u ∈ centerOf U :=
      hgen u hu (hcomm a ha hafix).symm (hcomm d hd hdfix).symm
    have hspf : ∀ x : antiSp F, (frobAut F ^ 1) x = x → spf ψ * Φ x = Φ x * spf ψ := by
      intro x hx
      rw [C.spf_conj hev x, hx]
    have hf2 : spf ψ * spf ψ = 1 := by rw [← sq]; exact spf_sq hev
    rcases D4.central_fixed u hu0 hfix' with hu1 | ⟨k, hk⟩
    · rcases C.psi2_pow_four hev s with hs | hs
      · left; left; rw [hs, hu1, map_one, mul_one]
      · right; left
        rw [hs, hu1, map_one, one_mul, hf2]
    · rcases C.psi2_pow_four hev s with hs | hs
      · left; right
        rw [hs, hk, mul_one]
        exact mem_spI.mpr ⟨k, rfl⟩
      · right; right
        have : spf ψ * (Φ u * spf ψ) = Φ u := by
          rw [← mul_assoc, hspf u hfix', mul_assoc, hf2, mul_one]
        rw [hs, this, hk]
        exact mem_spI.mpr ⟨k, rfl⟩
  fconj := by
    intro k' hk'
    obtain ⟨k, rfl⟩ := mem_spI.mp hk'
    obtain ⟨x, hxU, hx⟩ := D4.conj_wit k
    refine ⟨Φ x, (C.P.mem_spT_iff C.X.U_fr).mpr ⟨x, hxU, 0, by simp⟩, ?_⟩
    have e1 : spf ψ * Φ x⁻¹ = Φ ((frobAut F ^ 1) x⁻¹) * spf ψ := C.spf_conj hev x⁻¹
    have e2 : spf ψ * Φ (i k) = Φ (i k) * spf ψ := by
      rw [C.spf_conj hev (i k), C.X.i_fr 1 k]
    calc Φ x * spf ψ * (Φ x)⁻¹ = Φ x * (spf ψ * Φ x⁻¹) := by rw [map_inv, mul_assoc]
      _ = Φ x * (Φ ((frobAut F ^ 1) x⁻¹) * spf ψ) := by rw [e1]
      _ = Φ (x * ((frobAut F ^ 1) x)⁻¹) * spf ψ := by
        rw [← mul_assoc, ← map_mul, map_inv]
      _ = Φ (i k) * spf ψ := by rw [hx]
      _ = spf ψ * Φ (i k) := e2.symm

end FourAbs

end SpOut2

open SpOut2 in
theorem f431SpOut4Lie :
    ∀ (D : Type) [Group D], LieModel D .PSp 2 2 2 → ∀ A : LieAmalgamExt D,
      ¬ Odd (Nat.card ↥A.K / Nat.card D) →
      ∃ (T S : Subgroup ↥A.K) (g : ↥A.K) (I : Finset ↥A.K) (i0 i1 : ↥A.K),
        F431SpOut4 T S g A.Mb1 A.Mb2 I i0 i1 := by
  intro D _ hD A hev
  have : Finite D := finite_of_lieModel_psp hD
  have : Finite (MulAut D) := finite_mulAut_of_finite
  have : Finite ↥A.K := inferInstance
  obtain ⟨m, F, hFf, hFfin, hFchar, Φ, ψ, k₀, R, i, hm, C, hevψ, hRi⟩ := exists_outCtx hD A hev
  have hm1 : m = 1 := by omega
  subst hm1
  have hK : Nat.card F = 2 ^ (2 * 1) := C.hF
  refine ⟨spT Φ ψ (antiUnipotent F), (antiUnipotent F).map Φ, spf ψ, spI Φ i, Φ (i 0), Φ (i 1),
    ?_⟩
  have D4 : SpOutFourData (antiUnipotent F) i := by
    rcases hRi with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact spOutFourData_antiSp hK
    · exact (spOutFourData_antiSp hK).swap
  exact C.four hevψ D4

end CFSG.Quasithin.H13.F431

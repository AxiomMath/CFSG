module

public import CFSG.Quasithin.EmptyFaithful.S151S4A
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.Quasithin.S151S4

open CFSG.Open CFSG.Assembly.LowTwoRank

theorem center_sl2_eq_bot (K : Type) [Field K] [CharP K 2] :
    Subgroup.center (SL2 K) = ⊥ := by
  rw [eq_bot_iff]
  intro g hg
  rw [Matrix.SpecialLinearGroup.mem_center_iff] at hg
  obtain ⟨z, hz, hzg⟩ := hg
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  have hz2 : z ^ 2 = 1 := by simpa using hz
  have : (z - 1) ^ 2 = 0 := by linear_combination hz2 + (1 - z) * h2
  have hz1 : z = 1 := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
    linear_combination this
  subst hz1
  rw [Subgroup.mem_bot]
  apply Subtype.ext
  rw [← hzg]
  simp

@[expose] def uUHom (K : Type) [Field K] : Multiplicative K →* SL2 K where
  toFun t := uU (Multiplicative.toAdd t)
  map_one' := by
    apply Subtype.ext
    simp [uU, Matrix.one_fin_two]
  map_mul' s t := by
    simp only [toAdd_mul]
    exact (uU_mul _ _).symm

@[expose] def Usub (K : Type) [Field K] : Subgroup (SL2 K) := (uUHom K).range

theorem uU_mem_Usub {K : Type} [Field K] (t : K) : uU t ∈ Usub K :=
  ⟨Multiplicative.ofAdd t, rfl⟩

theorem mem_Usub {K : Type} [Field K] {x : SL2 K} : x ∈ Usub K ↔ ∃ t : K, uU t = x :=
  ⟨fun ⟨t, ht⟩ => ⟨Multiplicative.toAdd t, ht⟩, fun ⟨t, ht⟩ => ⟨Multiplicative.ofAdd t, ht⟩⟩

theorem uU_sq {K : Type} [Field K] [CharP K 2] (t : K) : uU t * uU t = 1 := by
  rw [uU_mul]
  have h2 : (2 : K) = 0 := by
    have := CharP.cast_eq_zero K 2
    simpa using this
  have : t + t = 0 := by linear_combination t * h2
  rw [this]
  apply Subtype.ext
  simp [uU, Matrix.one_fin_two]

theorem Usub_isPGroup (K : Type) [Field K] [CharP K 2] : IsPGroup 2 (Usub K) := by
  intro x
  refine ⟨1, ?_⟩
  obtain ⟨t, ht⟩ := mem_Usub.mp x.2
  apply Subtype.ext
  show (x : SL2 K) ^ 2 ^ 1 = 1
  rw [← ht, pow_one, pow_two]
  exact uU_sq t

@[expose] def dD {K : Type} [Field K] (a : K) (ha : a ≠ 0) : SL2 K :=
  ⟨!![a, 0; 0, a⁻¹], by simp [Matrix.det_fin_two, ha]⟩

theorem dD_pow {K : Type} [Field K] (a : K) (ha : a ≠ 0) (m : ℕ) :
    (((dD a ha) ^ m : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![a ^ m, 0; 0, (a ^ m)⁻¹] := by
  induction m with
  | zero => simp [Matrix.one_fin_two]
  | succ m ih =>
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, ih]
    simp only [dD, Matrix.mul_fin_two]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [pow_succ, mul_comm]

theorem sl2_not_isPGroup (K : Type) [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K) :
    ¬ IsPGroup 2 (SL2 K) := by
  classical
  intro h
  have : Fintype K := Fintype.ofFinite K
  have hex : ∃ a : K, a ≠ 0 ∧ a ≠ 1 := by
    by_contra hne
    push Not at hne
    have hsub : (Finset.univ : Finset K) ⊆ {0, 1} := by
      intro a _
      by_cases ha : a = 0
      · simp [ha]
      · simp [hne a ha]
    have := Finset.card_le_card hsub
    have h2 : ({0, 1} : Finset K).card ≤ 2 := Finset.card_le_two
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card] at this
    omega
  obtain ⟨a, ha0, ha1⟩ := hex
  obtain ⟨k, hk⟩ := h (dD a ha0)
  have h00 : a ^ 2 ^ k = 1 := by
    have h1 : (((dD a ha0) ^ 2 ^ k : SL2 K) : Matrix (Fin 2) (Fin 2) K) = 1 := by
      rw [hk]; simp
    rw [dD_pow] at h1
    have := congrFun (congrFun h1 0) 0
    simpa using this
  have hcp : (a - 1) ^ 2 ^ k = a ^ 2 ^ k - 1 ^ 2 ^ k := sub_pow_char_pow a 1 k
  rw [h00, one_pow, sub_self] at hcp
  exact ha1 (sub_eq_zero.mp (pow_eq_zero_iff (by positivity) |>.mp hcp))

@[expose] def wW (K : Type) [Field K] : SL2 K := ⟨!![0, 1; -1, 0], by simp [Matrix.det_fin_two]⟩

@[simp] theorem coe_wW (K : Type) [Field K] :
    ((wW K : SL2 K) : Matrix (Fin 2) (Fin 2) K) = !![0, 1; -1, 0] := rfl

theorem wW_mul_uU_mul_inv {K : Type} [Field K] (t : K) : wW K * uU t * (wW K)⁻¹ = lU (-t) := by
  rw [mul_inv_eq_iff_eq_mul]
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_wW, coe_uU, coe_lU]
  simp only [Matrix.mul_fin_two]
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem exists_equiv_sl2 {X : Type} [Group X] {n : ℕ} (h : IsPSL 2 2 n X) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K), CharP K 2 ∧ Nat.card K = 2 ^ n ∧
      Nonempty (X ≃* SL2 K) := by
  obtain ⟨-, K, hF, hfin, hcard, ⟨e⟩⟩ := h
  have hchar : CharP K 2 := by
    obtain ⟨p, hp⟩ := CharP.exists K
    have := hp
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨m, hpr, hm⟩ := FiniteField.card K p
    have hpow : 2 ^ n = p ^ (m : ℕ) := by
      rw [← hcard, Nat.card_eq_fintype_card, hm]
    have hn : n ≠ 0 := by
      rintro rfl
      have : p ^ (m : ℕ) = 1 := by rw [← hpow]; simp
      have := (Nat.pow_eq_one.mp this).resolve_right (by exact_mod_cast m.pos.ne')
      exact hpr.one_lt.ne' this
    have hp2 : p ∣ 2 := hpr.dvd_of_dvd_pow (n := n) (by rw [hpow]; exact dvd_pow_self p (by exact_mod_cast m.pos.ne'))
    have : p = 2 := (Nat.prime_dvd_prime_iff_eq hpr Nat.prime_two).mp hp2
    rwa [this] at hp
  have := hchar
  have hc : Subgroup.center (SL2 K) = ⊥ := center_sl2_eq_bot K
  exact ⟨K, hF, hfin, hchar, hcard, ⟨e.trans ((projectiveSpecialLinearGroupEquivStatedProj 2 K).symm.trans
    ((QuotientGroup.quotientMulEquivOfEq hc).trans QuotientGroup.quotientBot))⟩⟩

theorem sl2_sylow_borel (K : Type) [Field K] [Finite K] [CharP K 2] (hK : 4 ≤ Nat.card K)
    (P : Sylow 2 (SL2 K)) :
    ∃ Bor : Subgroup (SL2 K), Bor ≠ ⊤ ∧ (P : Subgroup (SL2 K)) ≤ Bor ∧
      (∀ H : Subgroup (SL2 K), (P : Subgroup (SL2 K)) ≤ H → H ≤ Bor ∨ H = ⊤) ∧
      ¬ (P : Subgroup (SL2 K)).Normal := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨g, hg⟩ := CFSG.LieType.BorelTits.exists_conj_mem_sylow P (Usub_isPGroup K)
  have hP2 : IsPGroup 2 ↥(P : Subgroup (SL2 K)) := P.isPGroup'
  have hnotP : (P : Subgroup (SL2 K)) ≠ ⊤ := by
    intro h
    apply sl2_not_isPGroup K hK
    have h' : IsPGroup 2 ↥(⊤ : Subgroup (SL2 K)) := h ▸ hP2
    exact h'.of_equiv Subgroup.topEquiv
  have hconj : ∀ h : SL2 K, (MulAut.conj g⁻¹) (g * h * g⁻¹) = h := by
    intro h
    simp
    group
  have key : ∀ H : Subgroup (SL2 K), (P : Subgroup (SL2 K)) ≤ H →
      H.comap (MulAut.conj g⁻¹).toMonoidHom ≤ Bsub K ∨ H = ⊤ := by
    intro H hPH
    have hu : ∀ t : K, uU t ∈ H.comap (MulAut.conj g⁻¹).toMonoidHom := by
      intro t
      have := hPH (hg (uU t) (uU_mem_Usub t))
      simpa [MulAut.conj_apply] using this
    rcases borel_or_top hu with h1 | h1
    · exact Or.inl h1
    · refine Or.inr (eq_top_iff.mpr fun h _ => ?_)
      have : g * h * g⁻¹ ∈ H.comap (MulAut.conj g⁻¹).toMonoidHom := h1 ▸ Subgroup.mem_top _
      have h2 : (MulAut.conj g⁻¹) (g * h * g⁻¹) ∈ H := this
      rwa [hconj] at h2
  refine ⟨(Bsub K).comap (MulAut.conj g).toMonoidHom, ?_, ?_, ?_, ?_⟩
  · intro h
    apply Bsub_ne_top (K := K)
    refine eq_top_iff.mpr fun y _ => ?_
    have : g⁻¹ * y * g ∈ (Bsub K).comap (MulAut.conj g).toMonoidHom := h ▸ Subgroup.mem_top _
    have h2 : (MulAut.conj g) (g⁻¹ * y * g) ∈ Bsub K := this
    simpa [mul_assoc] using h2
  · rcases key _ le_rfl with h1 | h1
    · intro x hx
      have h2 : g * x * g⁻¹ ∈ (P : Subgroup (SL2 K)).comap (MulAut.conj g⁻¹).toMonoidHom := by
        show (MulAut.conj g⁻¹) (g * x * g⁻¹) ∈ (P : Subgroup (SL2 K))
        rwa [hconj]
      exact h1 h2
    · exact absurd h1 hnotP
  · intro H hPH
    rcases key H hPH with h1 | h1
    · refine Or.inl fun x hx => ?_
      have h2 : g * x * g⁻¹ ∈ H.comap (MulAut.conj g⁻¹).toMonoidHom := by
        show (MulAut.conj g⁻¹) (g * x * g⁻¹) ∈ H
        rwa [hconj]
      exact h1 h2
    · exact Or.inr h1
  · intro hnorm
    have hu : ∀ t : K, uU t ∈ (P : Subgroup (SL2 K)) := by
      intro t
      have h1 := hnorm.conj_mem _ (hg (uU t) (uU_mem_Usub t)) g
      simpa [mul_assoc] using h1
    have hl : ∀ s : K, lU s ∈ (P : Subgroup (SL2 K)) := by
      intro s
      have h1 := hnorm.conj_mem _ (hu (-s)) (wW K)
      rwa [wW_mul_uU_mul_inv, neg_neg] at h1
    exact hnotP (eq_top_iff.mpr fun x _ => mem_of_uU_lU hu hl x)

end CFSG.Quasithin.S151S4

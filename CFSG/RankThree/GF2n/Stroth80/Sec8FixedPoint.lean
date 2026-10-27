module

public import CFSG.RankThree.GF2n.Stroth80.Sec8SecComm

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.CGT.Timmesfeld75 (conjSubgroup mem_conjSubgroup)
open CFSG.ClassicalGroups.F2Fixed (comm comm_apply exists_card_eq_two_pow)
open scoped commutatorElement

theorem exists_ne_zero_fixed_of_two_pow {X M : Type*} [Group X] [AddCommGroup M] [Finite M]
    [DistribMulAction X M] (h2 : ∀ a : M, a + a = 0) {x : X} {k : ℕ} (hx : x ^ (2 ^ k) = 1)
    (hM : ∃ a : M, a ≠ 0) : ∃ a : M, a ≠ 0 ∧ x • a = a := by
  classical
  have hG : IsPGroup 2 (Subgroup.zpowers x) := by
    intro g
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp g.2
    refine ⟨k, Subtype.ext ?_⟩
    rw [Subgroup.coe_pow, ← hn, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hx,
      one_zpow]
    rfl
  have hmod := hG.card_modEq_card_fixedPoints M
  obtain ⟨j, hj⟩ := exists_card_eq_two_pow h2
  obtain ⟨a₀, ha₀⟩ := hM
  have hj1 : 1 ≤ j := by
    by_contra h0
    have hj0 : j = 0 := by omega
    rw [hj0, pow_zero] at hj
    haveI : Subsingleton M := Finite.card_le_one_iff_subsingleton.mp (le_of_eq hj)
    exact ha₀ (Subsingleton.elim _ _)
  by_contra hcon
  push Not at hcon
  have hfp : (MulAction.fixedPoints (Subgroup.zpowers x) M) = {0} := by
    ext a
    simp only [MulAction.mem_fixedPoints, Set.mem_singleton_iff]
    constructor
    · intro ha
      by_contra hne
      exact hcon a hne (ha ⟨x, Subgroup.mem_zpowers x⟩)
    · rintro rfl g
      exact smul_zero _
  rw [hfp, hj, Nat.card_coe_set_eq, Set.ncard_singleton] at hmod
  obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
  unfold Nat.ModEq at hmod
  rw [pow_succ] at hmod
  omega


theorem linearMap_sub_one_pow_two_pow {K E : Type*} [Field K] [CharP K 2] [AddCommGroup E]
    [Module K E] (T : E →ₗ[K] E) {k : ℕ} (hT : T ^ (2 ^ k) = 1) : (T - 1) ^ (2 ^ k) = 0 := by
  have h1 : ((Polynomial.X - 1 : Polynomial K) ^ (2 ^ k)) = Polynomial.X ^ (2 ^ k) - 1 := by
    have := sub_pow_char_pow (R := Polynomial K) (p := 2) (Polynomial.X) (1 : Polynomial K) (n := k)
    simpa using this
  have h2 := congrArg (Polynomial.aeval T) h1
  simp only [map_pow, map_sub, Polynomial.aeval_X, map_one] at h2
  rw [h2, hT, sub_self]

theorem nilp_hyperplane {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    [Module.Finite K E] (N : E →ₗ[K] E) {j : ℕ} (hN : N ^ j = 0)
    (A₀ A : Submodule K E) (hle : A₀ ≤ A)
    (hdim : Module.finrank K A = Module.finrank K A₀ + 1)
    (hA : ∀ a ∈ A, N a ∈ A) (h0 : ∀ a ∈ A₀, N a = 0) :
    ∃ a₀ ∈ A₀, ∀ a ∈ A, ∃ r : K, N a = r • a₀ := by
  classical
  have hne : A₀ ≠ A := by
    intro h
    rw [h] at hdim
    omega
  obtain ⟨w, hwA, hw⟩ : ∃ w ∈ A, w ∉ A₀ := by
    by_contra hcon
    push Not at hcon
    exact hne (le_antisymm hle hcon)
  have hw0 : w ≠ 0 := by
    intro h
    exact hw (h ▸ A₀.zero_mem)
  have hle' : A₀ ⊔ Submodule.span K {w} ≤ A :=
    sup_le hle ((Submodule.span_singleton_le_iff_mem _ _).mpr hwA)
  have hinf : A₀ ⊓ Submodule.span K {w} = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    obtain ⟨hxA₀, hxs⟩ := Submodule.mem_inf.mp hx
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hxs
    by_cases hc : c = 0
    · rw [hc, zero_smul]
      exact Submodule.zero_mem _
    · exfalso
      apply hw
      have h' := A₀.smul_mem c⁻¹ hxA₀
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h'
  have hfin := Submodule.finrank_sup_add_finrank_inf_eq A₀ (Submodule.span K {w})
  rw [hinf, finrank_bot, finrank_span_singleton hw0] at hfin
  have hsup : A₀ ⊔ Submodule.span K {w} = A :=
    Submodule.eq_of_le_of_finrank_eq hle' (by omega)
  have hNw : N w ∈ A₀ ⊔ Submodule.span K {w} := by
    rw [hsup]
    exact hA w hwA
  obtain ⟨a₀, ha₀, z, hz, hsum⟩ := Submodule.mem_sup.mp hNw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have hiter : ∀ i : ℕ, (N ^ (i + 1)) w = c ^ i • a₀ + c ^ (i + 1) • w := by
    intro i
    induction i with
    | zero => simpa using hsum.symm
    | succ i ih =>
      rw [pow_succ', Module.End.mul_apply, ih, map_add, map_smul, map_smul, h0 a₀ ha₀,
        smul_zero, zero_add, ← hsum, smul_add, smul_smul, ← pow_succ]
  have hzero : (N ^ (j + 1)) w = 0 := by
    rw [pow_succ, hN, zero_mul]
    rfl
  have h1 := hiter j
  rw [hzero] at h1
  have hcw : c ^ (j + 1) • w ∈ A₀ := by
    have : c ^ (j + 1) • w = -(c ^ j • a₀) := eq_neg_of_add_eq_zero_right h1.symm
    rw [this]
    exact A₀.neg_mem (A₀.smul_mem _ ha₀)
  have hc0 : c = 0 := by
    by_contra hc
    apply hw
    have h' := A₀.smul_mem (c ^ (j + 1))⁻¹ hcw
    rwa [smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hc), one_smul] at h'
  refine ⟨a₀, ha₀, fun v hv => ?_⟩
  rw [← hsup] at hv
  obtain ⟨a₁, ha₁, z', hz', hsum2⟩ := Submodule.mem_sup.mp hv
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hz'
  subst hsum2
  refine ⟨r, ?_⟩
  rw [map_add, map_smul, h0 a₁ ha₁, zero_add, ← hsum, hc0, zero_smul, add_zero]

variable {G : Type} [Group G] [Finite G]

theorem sec8_isol {R P I N : Subgroup G} {x : G} (hsec : SecHyp R P I)
    (hxP : ∀ y ∈ P, x * y * x⁻¹ ∈ P) (hxI : ∀ y ∈ I, x * y * x⁻¹ ∈ I)
    (hxR : ∀ ρ ∈ R, ρ * x * ρ⁻¹ * x⁻¹ ∈ N)
    (hN : ∀ n ∈ N, ∀ y ∈ P, ⁅n, y⁆ ∈ I) {k : ℕ} (hxk : x ^ (2 ^ k) = 1)
    (hirr : ∀ U : Subgroup G, I ≤ U → U ≤ P → (∀ ρ ∈ R, conjSubgroup ρ U = U) →
      U = I ∨ U = P) :
    ∀ w ∈ P, ⁅x, w⁆ ∈ I := by
  classical
  obtain ⟨U, hIU, hUP, hUinv, hUx, hUcov⟩ := sec8_exists_comm_section hsec hxP hxR hN
  rcases hirr U hIU hUP hUinv with h | h
  · intro w hw
    exact h ▸ hUx w hw
  · have hcP : ∀ w ∈ P, ⁅x, w⁆ ∈ P := fun w hw => by
      rw [commutatorElement_def]
      exact P.mul_mem (hxP w hw) (P.inv_mem hw)
    have hxN : x ∈ Subgroup.normalizer (P : Set G) := Subgroup.mem_normalizer_fintype hxP
    have hzN : Subgroup.zpowers x ≤ Subgroup.normalizer (P : Set G) :=
      Subgroup.zpowers_le.mpr hxN
    have hxIN : x ∈ Subgroup.normalizer (I : Set G) := Subgroup.mem_normalizer_fintype hxI
    have hzI : Subgroup.zpowers x ≤ Subgroup.normalizer (I : Set G) :=
      Subgroup.zpowers_le.mpr hxIN
    have hsec0 : SecHyp (Subgroup.zpowers x) P I :=
      ⟨hsec.le, hsec.comm, hsec.sq,
        fun r hr y hy => (Subgroup.mem_normalizer_iff.mp (hzN hr) y).mp hy,
        fun r hr y hy => (Subgroup.mem_normalizer_iff.mp (hzI hr) y).mp hy⟩
    obtain ⟨Mo, iMo, iAct, κ, hκ⟩ := exists_sectionModule hsec0
    haveI : Finite Mo := hκ.finite
    set g : ↥(Subgroup.zpowers x) := ⟨x, Subgroup.mem_zpowers x⟩ with hg
    have hgk : g ^ (2 ^ k) = 1 := Subtype.ext (by simpa [hg] using hxk)
    have hsurj : Function.Surjective (comm Mo g) := by
      intro b
      obtain ⟨y, hy⟩ := hκ.surj (Multiplicative.ofAdd b)
      obtain ⟨w, hw, hyw⟩ := hUcov (y : G) (h ▸ y.2)
      have hwP : w ∈ P := hw
      refine ⟨Multiplicative.toAdd (κ ⟨w, hwP⟩), ?_⟩
      have h1 : κ y = κ ⟨⁅x, w⁆, hcP w hwP⟩ := (hκ.eq_iff _ _).mpr hyw
      have h2 := hκ.act g ⟨w, hwP⟩ ⟨x * w * x⁻¹, hxP w hwP⟩ rfl
      have e : (⟨⁅x, w⁆, hcP w hwP⟩ : ↥P) = ⟨x * w * x⁻¹, hxP w hwP⟩ * ⟨w, hwP⟩⁻¹ :=
        Subtype.ext (by simp [commutatorElement_def])
      rw [e, map_mul, map_inv, h2] at h1
      rw [comm_apply]
      have h3 : Multiplicative.toAdd (κ y) = b := by rw [hy]; rfl
      rw [← h3, h1]
      simp [toAdd_mul, toAdd_inv, sub_eq_add_neg]
    have hinj : Function.Injective (comm Mo g) := Finite.injective_iff_surjective.mpr hsurj
    have hzero : ∀ a : Mo, a = 0 := by
      by_contra hne
      push Not at hne
      obtain ⟨a, ha0, hga⟩ := exists_ne_zero_fixed_of_two_pow hκ.two hgk hne
      apply ha0
      apply hinj
      rw [comm_apply, hga, sub_self, map_zero]
    intro w hw
    have hwI : ∀ y ∈ P, y ∈ I := fun y hy =>
      (hκ.ker ⟨y, hy⟩).mp (Multiplicative.toAdd.injective (hzero _))
    exact hwI _ (hcP w hw)

end CFSG.RankThree.GF2n.Stroth80

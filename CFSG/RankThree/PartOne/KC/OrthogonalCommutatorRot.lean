module

public import CFSG.RankThree.PartOne.KC.OrthogonalBinaryDickson
public import CFSG.RankThree.PartOne.KC.OrthogonalSupportedScalarConj

public section

namespace CFSG.RankThree.PartOne.KCOrthComm

open Module CFSG.RankThree.OrthogonalInvolutions CFSG.RankThree.PartOne.KCOrthogonal

section Rot

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W] [FiniteDimensional K W]
  {Q : QuadraticForm K W}

@[expose] noncomputable def rotGroup (Q : QuadraticForm K W) (hQ : Q.polarBilin.Nondegenerate) :
    Subgroup (W ≃ₗ[K] W) :=
  (dicksonHom Q hQ).ker.map (TauCeti.QuadraticMap.orthogonalGroup Q).subtype

theorem mem_rotGroup {hQ : Q.polarBilin.Nondegenerate} {y : W ≃ₗ[K] W} :
    y ∈ rotGroup Q hQ ↔ ∃ hy : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q,
      dicksonHom Q hQ ⟨y, hy⟩ = 1 := by
  constructor
  · rintro ⟨g, hg, rfl⟩
    exact ⟨g.2, hg⟩
  · rintro ⟨hy, hδ⟩
    exact ⟨⟨y, hy⟩, hδ, rfl⟩

theorem rotGroup_le_orthogonalGroup (hQ : Q.polarBilin.Nondegenerate) :
    rotGroup Q hQ ≤ TauCeti.QuadraticMap.orthogonalGroup Q := fun _ hy => (mem_rotGroup.mp hy).1

theorem commute_of_mem_rotGroup {hQ : Q.polarBilin.Nondegenerate} (h2 : finrank K W = 2)
    {y z : W ≃ₗ[K] W} (hy : y ∈ rotGroup Q hQ) (hz : z ∈ rotGroup Q hQ) : y * z = z * y := by
  obtain ⟨hyO, hyδ⟩ := mem_rotGroup.mp hy
  obtain ⟨hzO, hzδ⟩ := mem_rotGroup.mp hz
  exact commute_of_dicksonHom_eq_one hQ h2 hyO hzO hyδ hzδ

theorem mem_rotGroup_iff {hQ : Q.polarBilin.Nondegenerate} (h2 : finrank K W = 2)
    {y : W ≃ₗ[K] W} (hy : y ∈ TauCeti.QuadraticMap.orthogonalGroup Q) :
    y ∈ rotGroup Q hQ ↔ y = 1 ∨ ∀ w, y w = w → w = 0 := by
  have hsum : finrank K (commSpace y) + finrank K (fixSpace y) = 2 := by
    have := finrank_commSpace_add_finrank_fixSpace y
    rwa [h2] at this
  rw [mem_rotGroup]
  constructor
  · rintro ⟨_, hδ⟩
    obtain ⟨m, hm⟩ := even_finrank_commSpace_of_dicksonHom_eq_one hQ hδ
    have hm' : finrank K (commSpace y) = m + m := hm
    have hcases : finrank K (commSpace y) = 0 ∨ finrank K (commSpace y) = 2 := by omega
    rcases hcases with h0 | h2'
    · left
      have hbot : commSpace y = ⊥ := Submodule.finrank_eq_zero.mp h0
      ext v
      have hv : y v - v ∈ commSpace y := sub_mem_commSpace y v
      rw [hbot, Submodule.mem_bot, sub_eq_zero] at hv
      rw [hv, LinearEquiv.coe_one, id]
    · right
      have hfix0 : finrank K (fixSpace y) = 0 := by omega
      have hbot : fixSpace y = ⊥ := Submodule.finrank_eq_zero.mp hfix0
      intro w hw
      have : w ∈ fixSpace y := mem_fixSpace.mpr hw
      rwa [hbot, Submodule.mem_bot] at this
  · rintro (rfl | hinj)
    · exact ⟨hy, by rw [show (⟨1, hy⟩ : TauCeti.QuadraticMap.orthogonalGroup Q) = 1 from rfl,
        map_one]⟩
    · refine ⟨hy, ?_⟩
      rw [dicksonHom_apply, ← ofAdd_zero, Multiplicative.ofAdd.injective.eq_iff,
        ZMod.natCast_eq_zero_iff_even]
      have hbot : fixSpace y = ⊥ := by
        refine (Submodule.eq_bot_iff _).mpr fun w hw => hinj w (mem_fixSpace.mp hw)
      have h0 : finrank K (fixSpace y) = 0 := by rw [hbot]; exact finrank_bot K W
      have h2' : finrank K (commSpace y) = 2 := by omega
      show Even (finrank K (commSpace y))
      rw [h2']
      exact even_two

theorem eq_one_or_eq_neg_of_sq {hQ : Q.polarBilin.Nondegenerate} (h2 : finrank K W = 2)
    {y : W ≃ₗ[K] W} (hy : y ∈ rotGroup Q hQ) (hsq : y * y = 1) :
    y = 1 ∨ ∀ w, y w = -w := by
  have hyO := (mem_rotGroup.mp hy).1
  rcases (mem_rotGroup_iff h2 hyO).mp hy with h1 | hinj
  · exact Or.inl h1
  · refine Or.inr fun w => ?_
    have hyy : y (y w) = w := by
      have := LinearEquiv.congr_fun hsq w
      simpa using this
    have h3 : y (y w + w) = y w + w := by
      rw [map_add, hyy, add_comm]
    exact eq_neg_of_add_eq_zero_left (hinj _ h3)

theorem semilinConj_mem_rotGroup {hQ : Q.polarBilin.Nondegenerate} (h2 : finrank K W = 2)
    (F : W ≃+ W) (σ : K ≃+* K) (hF : ∀ (c : K) (v : W), F (c • v) = σ c • F v) (μ : K)
    (hFQ : ∀ v, Q (F v) = μ * σ (Q v)) {y : W ≃ₗ[K] W} (hy : y ∈ rotGroup Q hQ) :
    semilinConj F σ hF y ∈ rotGroup Q hQ := by
  have hyO := (mem_rotGroup.mp hy).1
  have hO := semilinConj_mem_orthogonalGroup F σ hF μ hFQ hyO
  rw [mem_rotGroup_iff h2 hO]
  rcases (mem_rotGroup_iff h2 hyO).mp hy with h1 | hinj
  · left
    rw [h1, map_one]
  · right
    intro w hw
    rw [semilinConj_apply] at hw
    have h3 : y (F.symm w) = F.symm w := by
      have := congrArg F.symm hw
      rwa [AddEquiv.symm_apply_apply] at this
    have h4 := hinj _ h3
    have h5 := congrArg F h4
    rwa [AddEquiv.apply_symm_apply, map_zero] at h5

end Rot

section TwoPower

theorem apply_eq_of_pow_two_pow_eq_one {G : Type*} [Group G] (Z : Subgroup G)
    (hZ : ∀ a ∈ Z, ∀ b ∈ Z, a * b = b * a) (τ : G →* G) (hτZ : ∀ z ∈ Z, τ z ∈ Z) {N : ℕ}
    (hN : Odd N) (hτ : ∀ z ∈ Z, τ^[N] z = z) (hinv : ∀ z ∈ Z, z * z = 1 → τ z = z) :
    ∀ (t : ℕ) (y : G), y ∈ Z → y ^ 2 ^ t = 1 → τ y = y := by
  intro t
  induction t with
  | zero =>
    intro y _ hy
    rw [pow_zero, pow_one] at hy
    rw [hy, map_one]
  | succ t ih =>
    intro y hyZ hy
    have hy2Z : y ^ 2 ∈ Z := Z.pow_mem hyZ 2
    have hy2 : (y ^ 2) ^ 2 ^ t = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact hy
    have h1 : τ (y ^ 2) = y ^ 2 := ih (y ^ 2) hy2Z hy2
    have haa : τ y * τ y = y * y := by
      rw [← map_mul, ← pow_two, h1, pow_two]
    have hτyZ : τ y ∈ Z := hτZ y hyZ
    have hwZ : τ y * y⁻¹ ∈ Z := Z.mul_mem hτyZ (Z.inv_mem hyZ)
    have hcomm : τ y * y⁻¹ = y⁻¹ * τ y := hZ _ hτyZ _ (Z.inv_mem hyZ)
    have hw2 : (τ y * y⁻¹) * (τ y * y⁻¹) = 1 := by
      calc (τ y * y⁻¹) * (τ y * y⁻¹) = τ y * (y⁻¹ * τ y) * y⁻¹ := by simp only [mul_assoc]
        _ = τ y * (τ y * y⁻¹) * y⁻¹ := by rw [hcomm]
        _ = (τ y * τ y) * (y⁻¹ * y⁻¹) := by simp only [mul_assoc]
        _ = (y * y) * (y⁻¹ * y⁻¹) := by rw [haa]
        _ = 1 := by group
    have hτw : τ (τ y * y⁻¹) = τ y * y⁻¹ := hinv _ hwZ hw2
    have hτ2 : τ (τ y) = y := by
      have h3 : τ y = (τ y * y⁻¹) * y := by group
      have h4 : τ (τ y) = τ (τ y * y⁻¹) * τ y := by
        conv_lhs => rw [h3]
        rw [map_mul]
      rw [h4, hτw]
      calc τ y * y⁻¹ * τ y = τ y * y⁻¹ * ((τ y * y⁻¹) * y) := by rw [← h3]
        _ = (τ y * y⁻¹) * (τ y * y⁻¹) * y := by simp only [mul_assoc]
        _ = y := by rw [hw2, one_mul]
    have hiter : ∀ j : ℕ, τ^[2 * j] y = y := by
      intro j
      induction j with
      | zero => rfl
      | succ j ihj =>
        have h2 : τ^[2] y = y := hτ2
        rw [Nat.mul_succ, Function.iterate_add_apply, h2, ihj]
    obtain ⟨k, hk⟩ := hN
    have := hτ y hyZ
    rw [hk, add_comm, Function.iterate_add_apply, hiter k] at this
    exact this

end TwoPower

end CFSG.RankThree.PartOne.KCOrthComm

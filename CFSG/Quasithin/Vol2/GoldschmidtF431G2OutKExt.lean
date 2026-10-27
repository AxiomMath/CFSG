module

public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutKTheta
public import CFSG.Quasithin.Vol2.GoldschmidtF431TSLift
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2Aut
public import CFSG.Quasithin.Vol2.GoldschmidtF431G2OutKGen

public noncomputable section

namespace CFSG.Quasithin.H13.F431.G2.OutK

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Quasithin
  CFSG.Quasithin.H13.Sec53F.G2 CFSG.QuasithinUnique.Vol2Native.L239.Lie.G2
  CFSG.Quasithin.H13.F431 CFSG.Quasithin.H13.F431.Lift CFSG.Quasithin.H13.F431.F45
  CFSG.GH74.GLS.Stage4.Hex

section Generic

theorem range_conj_le_K_of_sup {D : Type} [Group D] (A : LieAmalgamExt D)
    (hsup : A.P1 ⊔ A.P2 = ⊤) : (MulAut.conj : D →* MulAut D).range ≤ A.K := by
  have h1 : A.P1.map (MulAut.conj : D →* MulAut D) ≤ A.N1 := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨A.inn_le ⟨p, rfl⟩, inn_mem_autStab hp⟩
  have h2 : A.P2.map (MulAut.conj : D →* MulAut D) ≤ A.N2 := by
    rintro _ ⟨p, hp, rfl⟩
    exact ⟨A.inn_le ⟨p, rfl⟩, inn_mem_autStab hp⟩
  have h : (⊤ : Subgroup D).map (MulAut.conj : D →* MulAut D) ≤ A.K := by
    rw [← hsup, Subgroup.map_sup]
    exact sup_le (h1.trans A.N1_le_K) (h2.trans A.N2_le_K)
  rintro _ ⟨d, rfl⟩
  exact h ⟨d, Subgroup.mem_top d, rfl⟩

end Generic

section Finite

variable {K : Type} [Field K]

theorem finite_C [Finite K] : Finite (C K) := by
  have : Finite (ModGL Tag.G2 K) := finite_modGL
  infer_instance

theorem finite_mulAut_C [Finite K] : Finite (MulAut (C K)) := by
  have := finite_C (K := K)
  exact Finite.of_injective (fun φ : MulAut (C K) => (φ : C K → C K)) DFunLike.coe_injective

end Finite

section Plain

variable {K : Type} [Field K]

structure IsNormalized (A : LieAmalgamExt (C K)) : Prop where
  TD_eq : A.TD = U K
  pair : (A.P1 = Pmin K ⟨1, by decide⟩ ∧ A.P2 = Pmin K ⟨0, by decide⟩) ∨
    (A.P1 = Pmin K ⟨0, by decide⟩ ∧ A.P2 = Pmin K ⟨1, by decide⟩)

theorem U_le_Pmin (i : Fin Tag.G2.rank) : U K ≤ Pmin K i := by
  intro u hu
  exact Subgroup.mem_subgroupOf.2 (borelGroup_le_parabolicSubgroup _
    (Subgroup.mem_sup_right (mem_U_iff.1 hu)))

end Plain

section Fz

variable {K : Type} [Field K] {A : LieAmalgamExt (C K)}

@[expose] def Fz (A : LieAmalgamExt (C K)) : Subgroup (K ≃+* K) := A.Mbar.comap (fieldAut K)

variable [Finite K] [CharP K 2]

theorem fieldAut_mem_autStab_P1_P2 (h : IsNormalized A) (σ : K ≃+* K) :
    fieldAut K σ ∈ autStab A.P1 ∧ fieldAut K σ ∈ autStab A.P2 := by
  rcases h.pair with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact ⟨fieldAut_mem_autStab_Pmin σ _, fieldAut_mem_autStab_Pmin σ _⟩
  · rw [h1, h2]
    exact ⟨fieldAut_mem_autStab_Pmin σ _, fieldAut_mem_autStab_Pmin σ _⟩

theorem fieldAut_mem_N (h : IsNormalized A) {σ : K ≃+* K} (hσ : σ ∈ Fz A) :
    fieldAut K σ ∈ A.N1 ⊓ A.N2 :=
  ⟨⟨hσ, (fieldAut_mem_autStab_P1_P2 h σ).1⟩, ⟨hσ, (fieldAut_mem_autStab_P1_P2 h σ).2⟩⟩

theorem fieldAut_mem_K (h : IsNormalized A) {σ : K ≃+* K} (hσ : σ ∈ Fz A) :
    fieldAut K σ ∈ A.K :=
  A.N1_le_K (fieldAut_mem_N h hσ).1

end Fz

section Full

variable {K : Type} [Field K] [Finite K] [CharP K 2] {A : LieAmalgamExt (C K)}

omit [CharP K 2] in
theorem Pr_ne_Pa (hK : 3 ≤ Nat.card K) :
    Pmin K ⟨1, by decide⟩ ≠ Pmin K ⟨0, by decide⟩ := by
  intro h
  have h1 := map_Pmin_one hK
  have h0 := map_Pmin_zero hK
  rw [h, h0] at h1
  exact BN.P₁_ne_P₂ (g2ModelSystem K hK) h1.symm

omit [CharP K 2] in
theorem Pr_sup_Pa (hK : 3 ≤ Nat.card K) :
    Pmin K ⟨1, by decide⟩ ⊔ Pmin K ⟨0, by decide⟩ = ⊤ :=
  (isCoatom_Pmin hK _).sup_eq_top_of_ne (isCoatom_Pmin hK _) (Pr_ne_Pa hK)

omit [CharP K 2] in
theorem IsNormalized.inn_le_K {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n)
    (h : IsNormalized A) : (MulAut.conj : C K →* MulAut (C K)).range ≤ A.K := by
  refine range_conj_le_K_of_sup A ?_
  have h3 := three_le_card_of_pow hn hK
  rcases h.pair with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rw [h1, h2]
    exact Pr_sup_Pa h3
  · rw [h1, h2, sup_comm]
    exact Pr_sup_Pa h3

theorem exists_decomp_N {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {φ : MulAut (C K)} (hφ : φ ∈ A.N1 ⊓ A.N2) :
    ∃ b ∈ Pmin K ⟨1, by decide⟩ ⊓ Pmin K ⟨0, by decide⟩, ∃ σ ∈ Fz A,
      φ = MulAut.conj b * fieldAut K σ := by
  have hst : φ ∈ autStab (Pmin K ⟨1, by decide⟩) ⊓ autStab (Pmin K ⟨0, by decide⟩) := by
    have a1 : φ ∈ autStab A.P1 := hφ.1.2
    have a2 : φ ∈ autStab A.P2 := hφ.2.2
    rcases h.pair with ⟨h1, h2⟩ | ⟨h1, h2⟩
    · rw [h1] at a1
      rw [h2] at a2
      exact ⟨a1, a2⟩
    · rw [h1] at a1
      rw [h2] at a2
      exact ⟨a2, a1⟩
  obtain ⟨b, hb, σ, hφσ, -, -⟩ := exists_of_autStab_Pr_Pa hn hK hst
  refine ⟨b, hb, σ, ?_, hφσ⟩
  show fieldAut K σ ∈ A.Mbar
  have h1 : fieldAut K σ = (MulAut.conj b)⁻¹ * φ := by
    rw [hφσ]
    group
  rw [h1]
  exact A.Mbar.mul_mem (A.Mbar.inv_mem (A.inn_le ⟨b, rfl⟩)) hφ.1.1

theorem exists_decomp_K {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    (k : ↥A.K) : ∃ (g : C K) (σ : K ≃+* K), σ ∈ Fz A ∧
      (k : MulAut (C K)) = MulAut.conj g * fieldAut K σ := by
  have := finite_C (K := K)
  obtain ⟨d, φ, hφ, hk⟩ := exists_inn_mul A k
  obtain ⟨b, -, σ, hσ, rfl⟩ := exists_decomp_N hn hK h hφ
  exact ⟨d * b, σ, hσ, by rw [hk, map_mul, mul_assoc]⟩

theorem mem_Nj_iff {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {i : Fin Tag.G2.rank} {P : Subgroup (C K)} (hP : P = Pmin K i) (x : ↥A.K) :
    (x : MulAut (C K)) ∈ A.Mbar ⊓ autStab P ↔
      ∃ g ∈ P, ∃ σ ∈ Fz A, (x : MulAut (C K)) = MulAut.conj g * fieldAut K σ := by
  subst hP
  constructor
  · intro hx
    obtain ⟨g, σ, hσ, hxg⟩ := exists_decomp_K hn hK h x
    refine ⟨g, ?_, σ, hσ, hxg⟩
    refine mem_Pmin_of_conj_mul_mem_autStab (three_le_card_of_pow hn hK) (σ := σ) ?_
    rw [← hxg]
    exact hx.2
  · rintro ⟨g, hg, σ, hσ, hxg⟩
    rw [hxg]
    refine ⟨A.Mbar.mul_mem (A.inn_le ⟨g, rfl⟩) hσ,
      (autStab _).mul_mem (inn_mem_autStab hg) (fieldAut_mem_autStab_Pmin σ i)⟩

omit
  [CharP K 2] in
theorem center_C_eq_bot' : Subgroup.center (C K) = ⊥ := center_adjointGroup_eq_bot

@[expose] def psiK (h : IsNormalized A) {σ : K ≃+* K} (hσ : σ ∈ Fz A) : ↥A.K :=
  ⟨fieldAut K σ, fieldAut_mem_K h hσ⟩

theorem psiK_coe (h : IsNormalized A) {σ : K ≃+* K} (hσ : σ ∈ Fz A) :
    ((psiK h hσ : ↥A.K) : MulAut (C K)) = fieldAut K σ := rfl

omit
  [Finite K] [CharP K 2] in
theorem exists_gen_Fz {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (A : LieAmalgamExt (C K)) :
    ∃ σ₁ : K ≃+* K, σ₁ ∈ Fz A ∧ ∀ σ ∈ Fz A, σ ∈ Subgroup.zpowers σ₁ := by
  have := isCyclic_ringAut (by omega : 1 ≤ n) hK
  obtain ⟨g, hg⟩ := IsCyclic.exists_generator (α := ↥(Fz A))
  refine ⟨g.1, g.2, fun σ hσ => ?_⟩
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.1 (hg ⟨σ, hσ⟩)
  exact Subgroup.mem_zpowers_iff.2 ⟨m, by simpa using congrArg Subtype.val hm⟩

theorem outProps_of_gen {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {σ₁ : K ≃+* K} (hσ₁ : σ₁ ∈ Fz A) (hgen : ∀ σ ∈ Fz A, σ ∈ Subgroup.zpowers σ₁) :
    OutProps (iK A (h.inn_le_K hn hK)) (psiK h hσ₁) (fieldAut K σ₁) where
  inj := iK_injective A _ center_C_eq_bot'
  act x := by
    apply Subtype.ext
    have := aut_conj_conj (fieldAut K σ₁) x
    simpa [iK_coe, psiK] using this
  cen k hk := by
    have hinj : Function.Injective (MulAut.conj : C K →* MulAut (C K)) :=
      conj_injective_of_center center_C_eq_bot'
    apply Subtype.ext
    refine MulEquiv.ext fun x => ?_
    have h1 := congrArg (fun y : ↥A.K => (y : MulAut (C K))) (hk x)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, iK_coe] at h1
    rw [aut_conj_conj] at h1
    have := hinj h1
    simpa using this
  gen k := by
    have := finite_ringAut (by omega : 1 ≤ n) hK
    obtain ⟨g, σ, hσ, hk⟩ := exists_decomp_K hn hK h k
    obtain ⟨s, hs⟩ := (mem_zpowers_iff_nat σ₁ σ).1 (hgen σ hσ)
    refine ⟨g, s, Subtype.ext ?_⟩
    rw [hk, ← hs, map_pow]
    rfl
  outer s g hs := by
    have h1 : fieldAut K (σ₁ ^ s) = MulAut.conj g := by
      rw [map_pow]
      exact hs
    have := fieldAut_eq_one_of_eq_conj hn hK h1
    rw [← map_pow, this, map_one]

theorem pow_psiK_eq_one_iff {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {σ₁ : K ≃+* K} (hσ₁ : σ₁ ∈ Fz A) (hgen : ∀ σ ∈ Fz A, σ ∈ Subgroup.zpowers σ₁) (s : ℕ) :
    psiK h hσ₁ ^ s = 1 ↔ σ₁ ^ s = 1 := by
  rw [(outProps_of_gen hn hK h hσ₁ hgen).pow_eq_one_iff s, ← map_pow]
  exact ⟨fun h1 => fieldAut_injective hn hK (by rw [h1, map_one]), fun h1 => by rw [h1, map_one]⟩

theorem orderOf_psiK {n : ℕ} (hn : 2 ≤ n) (hK : Nat.card K = 2 ^ n) (h : IsNormalized A)
    {σ₁ : K ≃+* K} (hσ₁ : σ₁ ∈ Fz A) (hgen : ∀ σ ∈ Fz A, σ ∈ Subgroup.zpowers σ₁) :
    orderOf (psiK h hσ₁) = orderOf σ₁ :=
  orderOf_eq_orderOf_iff.2 (pow_psiK_eq_one_iff hn hK h hσ₁ hgen)

end Full

end CFSG.Quasithin.H13.F431.G2.OutK

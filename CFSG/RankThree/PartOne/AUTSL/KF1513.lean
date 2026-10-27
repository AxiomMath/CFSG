module

public import CFSG.RankThree.PartOne.AUTSL.KF1513Shell
public import CFSG.RankThree.PartOne.AUTSL.OmegaOut
public import CFSG.RankThree.PartOne.AUTSL.OmegaStab
public import CFSG.RankThree.PartOne.AUTSL.OmegaFixed
public import CFSG.RankThree.PartOne.S15K.OrthModel

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG CFSG.ABGLocalTools CFSG.Assembly.LowTwoRank
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ComponentClassification Matrix

section Orth

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

omit [Finite K] in
theorem reflAut_eq_self_iff (hnd : Q.polarBilin.Nondegenerate) {w : Fin d → K} (hw : Q w = 1)
    (hw0 : Q w ≠ 0) (γ : matrixDerived Q) : reflAut Q w hw0 γ = γ ↔ γ.val *ᵥ w = w := by
  have hγO : γ.val ∈ matrixIsometries Q := matrixDerived_le_isometries Q γ.2
  rw [← comm_reflMat_iff hnd hγO hw hw0]
  constructor
  · intro h
    have h1 := congrArg Subtype.val h
    rw [reflAut_apply_val] at h1
    calc γ.val * reflMat Q w hw0 = (reflMat Q w hw0 * γ.val * (reflMat Q w hw0)⁻¹) *
          reflMat Q w hw0 := by rw [h1]
      _ = reflMat Q w hw0 * γ.val := by group
  · intro h
    refine Subtype.ext ?_
    rw [reflAut_apply_val]
    calc reflMat Q w hw0 * γ.val * (reflMat Q w hw0)⁻¹ =
          γ.val * reflMat Q w hw0 * (reflMat Q w hw0)⁻¹ := by rw [← h]
      _ = γ.val := by group

omit [Finite K] in
theorem reflAut_fix_of_fix (hnd : Q.polarBilin.Nondegenerate) {w : Fin d → K} (hw : Q w = 1)
    (hw0 : Q w ≠ 0) {s : GL (Fin d) K} (hs : s ∈ matrixDerived Q) (hsw : s.val *ᵥ w = w) :
    reflAut Q w hw0 ⟨s, hs⟩ = ⟨s, hs⟩ :=
  (reflAut_eq_self_iff hnd hw hw0 ⟨s, hs⟩).2 hsw

omit [Finite K] [CharP K 2] in
theorem map_subtype_normalized (R : Subgroup (matrixDerived Q)) {s : GL (Fin d) K}
    (hs : s ∈ matrixDerived Q)
    (hRs : ∀ r ∈ R, (⟨s, hs⟩ : matrixDerived Q) * r * (⟨s, hs⟩ : matrixDerived Q)⁻¹ ∈ R)
    (r : GL (Fin d) K) (hr : r ∈ R.map (matrixDerived Q).subtype) :
    s * r * s⁻¹ ∈ R.map (matrixDerived Q).subtype := by
  rw [Subgroup.mem_map] at hr ⊢
  obtain ⟨r', hr', hrr⟩ := hr
  refine ⟨(⟨s, hs⟩ : matrixDerived Q) * r' * (⟨s, hs⟩ : matrixDerived Q)⁻¹, hRs r' hr', ?_⟩
  rw [← hrr]
  simp only [Subgroup.coe_subtype, Subgroup.coe_mul, Subgroup.coe_inv]

theorem eq_bot_of_fixed_normal_two (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), Module.finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0)
    {w : Fin d → K} (hw : Q w = 1) (hw0 : Q w ≠ 0) (hd : 3 ≤ d)
    (R : Subgroup (matrixDerived Q)) (hRfix : ∀ r ∈ R, reflAut Q w hw0 r = r)
    (hRnorm : ∀ s : matrixDerived Q, reflAut Q w hw0 s = s → ∀ r ∈ R, s * r * s⁻¹ ∈ R)
    (hR2 : IsPGroup 2 R) : R = ⊥ := by
  have hfixw : ∀ r ∈ R, (r : GL (Fin d) K).val *ᵥ w = w := fun r hr =>
    (reflAut_eq_self_iff hnd hw hw0 r).1 (hRfix r hr)
  have hnorm : ∀ s ∈ matrixDerived Q, s.val *ᵥ w = w →
      ∀ r ∈ R.map (matrixDerived Q).subtype, s * r * s⁻¹ ∈ R.map (matrixDerived Q).subtype :=
    fun s hs hsw => map_subtype_normalized R hs
      (hRnorm ⟨s, hs⟩ (reflAut_fix_of_fix hnd hw hw0 hs hsw))
  have hRG : R.map (matrixDerived Q).subtype = ⊥ :=
    eq_bot_of_normal_two_subgroup hnd hT hw hd _ (hR2.map _) (Subgroup.map_subtype_le R)
      (by rintro _ ⟨r, hr, rfl⟩; exact hfixw r hr) hnorm
  refine (Subgroup.eq_bot_iff_forall R).2 fun r hr => ?_
  have hmem : (r : GL (Fin d) K) ∈ R.map (matrixDerived Q).subtype := ⟨r, hr, rfl⟩
  rw [hRG, Subgroup.mem_bot] at hmem
  exact Subtype.ext hmem

end Orth

section Model

variable {G : Type} [Group G] [Finite G] {p : ℕ} {I H T A₀ : Subgroup G}
  {K : Type} [Field K] [Finite K] [CharP K 2]

theorem kf1513_of_model (hcfg : Config1514 p I H T A₀) (hTI : ¬ T ≤ I) {f : ℕ}
    (hf : Nat.card K = 2 ^ f) (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hpq : p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) (Ψ : I ≃* matrixDerived (Qm 4 (le_refl 4) b c)) :
    ∃ t ∈ T, t ^ 2 = 1 ∧ t ∉ I ∧ I ⊓ Subgroup.centralizer ({t} : Set G) ≠ ⊥ ∧
      (∀ Q : Subgroup G, Q ≤ I ⊓ Subgroup.centralizer ({t} : Set G) →
        I ⊓ Subgroup.centralizer ({t} : Set G) ≤ Subgroup.normalizer (Q : Set G) →
        IsPGroup 2 Q → Q = ⊥) ∧
      ∃ h ∈ H, ∃ B : Subgroup G, B ≤ A₀ ∧ Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
        B.map (MulAut.conj h).toMonoidHom ≤ I ⊓ Subgroup.centralizer ({t} : Set G) := by
  classical
  have : Fintype K := Fintype.ofFinite K
  have hfc : Fintype.card K = 2 ^ f := by rw [← Nat.card_eq_fintype_card]; exact hf
  have : Fact p.Prime := ⟨hcfg.prime⟩
  obtain ⟨hnd, hT⟩ := regular_coordinateQuadMinus 4 K b c (le_refl 4) hirr
  let Θ : I →* GL (Fin (2 * 4)) K := (matrixDerived (Qm 4 (le_refl 4) b c)).subtype.comp
    Ψ.toMonoidHom
  let A : Subgroup (GL (Fin (2 * 4)) K) := (A₀.subgroupOf I).map Θ
  have hA₀p : IsPGroup p A₀ := by
    have := hcfg.A_elem
    exact IsElementaryAbelian.isPGroup p A₀
  have hAp : IsPGroup p A := (hA₀p.comap_subtype (K := I)).map Θ
  have hAQ : ∀ g ∈ A, ∀ v : Fin (2 * 4) → K,
      Qm 4 (le_refl 4) b c ((g : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *ᵥ v) =
        Qm 4 (le_refl 4) b c v := by
    rintro _ ⟨i, -, rfl⟩ v
    exact map_mulVec_of_mem (matrixDerived_le_isometries _ (Ψ i).2) v
  obtain ⟨w, hwQ, hwfix⟩ := exists_fixed_norm_one hcfg.five_le b c hirr
    (by rw [hfc]; exact hpq) A hAp hAQ
  have hw0 : Qm 4 (le_refl 4) b c w ≠ 0 := by rw [hwQ]; exact one_ne_zero
  refine kf1513_shell hcfg hTI Ψ (reflAut (Qm 4 (le_refl 4) b c) w hw0) (reflAut_mul_self w hw0)
    (reflAut_not_mem_inner 4 (le_refl 4) b c hirr hf w hw0)
    (fun Hb hHb x hx hxn hxa => ?_) ?_ ?_
  · obtain ⟨a, ha⟩ := hxa
    exact reflAut_mem_of_two_power 4 (le_refl 4) b c hirr hf Hb hHb hx hxn ha w hw0
  · intro R hRfix hRnorm hR2
    exact eq_bot_of_fixed_normal_two hnd hT hwQ hw0 (by norm_num) R hRfix hRnorm hR2
  · intro a ha
    have hγA : ((Ψ ⟨a, hcfg.A_le ha⟩ : matrixDerived (Qm 4 (le_refl 4) b c)) :
        GL (Fin (2 * 4)) K) ∈ A :=
      ⟨⟨a, hcfg.A_le ha⟩, Subgroup.mem_subgroupOf.2 ha, rfl⟩
    exact (reflAut_eq_self_iff hnd hwQ hw0 _).2 (hwfix _ hγA)

end Model

theorem kf1513_holds : KF1513 := by
  intro r hr3 hr4 G _ _ p I H T A₀ hcfg hlie hTI
  obtain ⟨f, hf1, hpf, b, c, hirr, ⟨e⟩⟩ : ∃ f : ℕ, 1 ≤ f ∧ (p ∣ 2 ^ f - 1 ∨ p ∣ 2 ^ f + 1) ∧
      ∃ b c : GaloisField 2 f, (∀ s : GaloisField 2 f, s ^ 2 + b * s + c ≠ 0) ∧
        Nonempty (I ≃* CFSG.Assembly.RankThreeEven.projOmegaMinus 3 (GaloisField 2 f) b c) := by
    interval_cases r
    · obtain ⟨f, hf, hp, b, c, hirr, he⟩ := hlie
      exact ⟨f, hf, Or.inl hp, b, c, hirr, he⟩
    · obtain ⟨f, hf, hp, b, c, hirr, he⟩ := hlie
      exact ⟨f, hf, Or.inr hp, b, c, hirr, he⟩
  have hcl := CFSG.RankThree.PartOne.S15K.statedClassicalModel_of_projOmegaMinus hf1 hirr e
  obtain ⟨-, K, hF, hFin, hcard, b', c', hirr', ⟨e₀⟩⟩ := hcl
  have hchar : CharP K 2 := by
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨n, hp, hn⟩ := FiniteField.card K (ringChar K)
    have h1 : ringChar K ∣ 2 ^ f := by
      rw [← hcard, Nat.card_eq_fintype_card, hn]
      exact dvd_pow_self _ n.ne_zero
    have h3 : ringChar K = 2 :=
      (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h1)
    exact CharP.congr (ringChar K) h3
  have h14 : (1 : ℕ) ≤ 4 := by norm_num
  have hreg := regular_coordinateQuadMinus 4 K b' c' (le_refl 4) hirr'
  have hQ : ∃ v, coordinateQuadMinus 4 K h14 b' c' v ≠ 0 :=
    exists_ne_zero_of_polar_nondegenerate (by norm_num) _ hreg.1
  let Ψ : I ≃* matrixDerived (Qm 4 (le_refl 4) b' c') :=
    (coordinateMinusWitnessEquiv K h14 b' c' e₀).trans (derivedProjEquiv _ hQ).symm
  exact kf1513_of_model hcfg hTI hcard b' c' hirr' hpf Ψ

end CFSG.RankThree.PartOne.AUTSL

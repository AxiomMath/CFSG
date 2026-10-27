module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALabel
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeATorus
public import CFSG.LocalAnalysis.StandardType.GGNbrLangTypeALift
public import CFSG.RankThree.SteinbergR3ELinearFieldDescent
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly Matrix CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag CFSG.ComponentClassification

@[expose] def GGTypeASplitFrame (p d : ℕ) (F : Type) [Field F] : Prop :=
  ∀ E : Subgroup (MulAut (projectiveSL d F)), (∀ φ ∈ E, ∀ ψ ∈ E, φ * ψ = ψ * φ) →
    (∀ φ ∈ E, φ ^ p = 1) → E ≤ semilinearAutGroup d F →
    ∃ (M : GL (Fin d) F) (σ : F ≃+* F), σ ^ p = 1 ∧
      (∀ φ ∈ E, ∃ (D₁ : GL (Fin d) F) (k : ℕ), (D₁ : Matrix (Fin d) (Fin d) F).IsDiag ∧
        (∀ i, σ ((D₁ : Matrix (Fin d) (Fin d) F) i i) = (D₁ : Matrix (Fin d) (Fin d) F) i i) ∧
        φ = conjAut d F M * conjAut d F D₁ * fieldAut d F (σ ^ k) * (conjAut d F M)⁻¹) ∧
      ∃ ω : Fˣ, σ ω = ω ∧ ω ^ p = 1 ∧ ω ≠ 1

@[expose] def GGTypeASplitFrameInput : Prop :=
  ∀ (p d : ℕ) (F : Type) [Field F] [Finite F], p.Prime → p ≠ 2 → 3 ≤ d →
    p ∣ Nat.card F - 1 → ¬ p ∣ d → GGTypeASplitFrame p d F

namespace NbrLangTypeA

variable {G : Type} [Group G] {d : ℕ} {F : Type} [Field F]

theorem eq_one_of_frame_mem_linear [Finite F] (hd : 3 ≤ d) {M D₁ : GL (Fin d) F}
    {τ : F ≃+* F}
    (h : conjAut d F M * conjAut d F D₁ * fieldAut d F τ * (conjAut d F M)⁻¹ ∈
      linearAutGroup d F) : τ = 1 := by
  obtain ⟨A, hA⟩ := mem_linearAutGroup_iff.mp h
  have h1 : conjAut d F (D₁⁻¹ * M⁻¹ * A * M) * fieldAut d F τ⁻¹ = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hA, map_inv]
    group
  have h2 := (eq_one_of_conjAut_mul_fieldAut_eq_one hd _ τ⁻¹ h1).1
  exact inv_eq_one.mp h2

theorem exists_inner_hyperplane [Finite G] [Finite F] {p : ℕ} (hp : p.Prime) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs) {m : ℕ} (hm : 1 ≤ m) (hF : Nat.card F = 2 ^ m) (hd : 3 ≤ d)
    (α : ↥Bs →* MulAut (projectiveSL d F)) (hα : ∀ b, α b ∈ semilinearAutGroup d F) {b₀ : G}
    (hb₀ : b₀ ∈ Bs) (hb₀D : α ⟨b₀, hb₀⟩ ∉ linearAutGroup d F) :
    ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
      ∀ (b : G) (hb : b ∈ Bs), b ∈ B₀ ↔ α ⟨b, hb⟩ ∈ linearAutGroup d F := by
  classical
  have := Fintype.ofFinite F
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP F 2 := charP_of_card_eq_prime_pow (by rw [← Nat.card_eq_fintype_card, hF])
  obtain ⟨-, -, hDE, -, -, -, -, -⟩ :=
    CFSG.RankThree.LinearDescent.higher_linear_prime_semilinear_field_descent (K := F) (n := d)
      Nat.prime_two hm hd hF
  set Dq := (linearAutGroup d F).subgroupOf (semilinearAutGroup d F) with hDq
  let αE : ↥Bs →* semilinearAutGroup d F := α.codRestrict _ hα
  let χ : ↥Bs →* semilinearAutGroup d F ⧸ Dq := (QuotientGroup.mk' Dq).comp αE
  have hcyc : IsCyclic (semilinearAutGroup d F ⧸ Dq) := by
    obtain ⟨φ₁, -, -, htop, -, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_two hm hF
    have : IsCyclic (F ≃+* F) := isCyclic_iff_exists_zpowers_eq_top.mpr ⟨φ₁, htop⟩
    let fE : (F ≃+* F) →* semilinearAutGroup d F :=
      (fieldAut d F).codRestrict _ fieldAut_mem_semilinearAutGroup
    refine isCyclic_of_surjective ((QuotientGroup.mk' Dq).comp fE) ?_
    intro q
    obtain ⟨⟨a, ha⟩, rfl⟩ := QuotientGroup.mk'_surjective Dq q
    obtain ⟨A, τ, rfl⟩ := mem_semilinearAutGroup_iff.mp ha
    refine ⟨τ, ?_⟩
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    have hcA : (⟨conjAut d F A, linearAutGroup_le_semilinearAutGroup
        (conjAut_mem_linearAutGroup A)⟩ : semilinearAutGroup d F) ∈ Dq := by
      rw [hDq, Subgroup.mem_subgroupOf]
      exact conjAut_mem_linearAutGroup A
    have h1 := hDE.conj_mem _ hcA (fE τ)⁻¹
    rw [inv_inv] at h1
    convert h1 using 1
    rw [mul_assoc]
    rfl
  have hχ : ∀ (b : G) (hb : b ∈ Bs), χ ⟨b, hb⟩ = 1 ↔ α ⟨b, hb⟩ ∈ linearAutGroup d F := by
    intro b hb
    rw [MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, hDq,
      Subgroup.mem_subgroupOf]
    rfl
  obtain ⟨B₀, h1, h2, h3, h4⟩ :=
    exists_index_prime_of_hom_cyclic hp hBs χ hb₀ (fun h => hb₀D ((hχ b₀ hb₀).mp h))
  exact ⟨B₀, h1, h2, h3, fun b hb => (h4 b hb).trans (hχ b hb)⟩

theorem mem_conjImage_iff {K : Subgroup G}
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    (g : Subgroup.normalizer (K : Set G)) :
    ggLAut K θ g ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ ↔
      ggLAut K (θ.trans (TypeA.recipeEquiv d F)) g ∈ linearAutGroup d F := by
  rw [ggLAut_trans θ _ g, mem_linearAutGroup_iff]
  constructor
  · intro h
    obtain ⟨A, hA⟩ := TypeA.congr_recipeEquiv_mem h
    exact ⟨A, hA⟩
  · rintro ⟨A, hA⟩
    have h1 := NbrGraphLinear.symm_congr_conjAut_mem (d := d) (K := F) A
    rwa [hA, MulEquiv.symm_apply_apply] at h1

theorem mem_semilinear_of_eq_mul {K : Subgroup G}
    (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    (g : Subgroup.normalizer (K : Set G))
    (hg : ∃ u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ,
      ∃ f ∈ Subgroup.closure
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F))),
        ggLAut K θ g = u * f) :
    ggLAut K (θ.trans (TypeA.recipeEquiv d F)) g ∈ semilinearAutGroup d F := by
  obtain ⟨u, hu, f, hf, huf⟩ := hg
  rw [ggLAut_trans θ _ g, huf, map_mul]
  refine Subgroup.mul_mem _ ?_ ?_
  · obtain ⟨A, hA⟩ := TypeA.congr_recipeEquiv_mem hu
    rw [← hA]
    exact linearAutGroup_le_semilinearAutGroup (conjAut_mem_linearAutGroup A)
  · have hle : Subgroup.closure
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F))) ≤
        (semilinearAutGroup d F).comap (MulAut.congr (TypeA.recipeEquiv d F)).toMonoidHom := by
      rw [Subgroup.closure_le]
      intro f' hf'
      obtain ⟨σ, hσ⟩ := congr_recipeEquiv_field_mem hf'
      change MulAut.congr (TypeA.recipeEquiv d F) f' ∈ semilinearAutGroup d F
      rw [← hσ]
      exact fieldAut_mem_semilinearAutGroup σ
    exact hle hf

theorem lang_axis_of_linear (hframe : GGTypeASplitFrameInput) [Finite G] {p : ℕ}
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hC : GGConfig p B Bs x L D J)
    {K : Subgroup G} (hN : Bs ≤ Subgroup.normalizer (K : Set G)) (hperf : commutator K = ⊤)
    (hd : 3 ≤ d) [Finite F] {m : ℕ} (hF : Nat.card F = 2 ^ m) (hpF : p ∣ 2 ^ m - 1)
    (hpd : ¬ p ∣ d) (θ : K ⧸ Subgroup.center K ≃* LargeEvenProj (LargeEvenSLGroup (Fin d) F))
    (hgr : ∀ (b : G) (hb : b ∈ Bs),
      ∃ u ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ,
      ∃ f ∈ Subgroup.closure
        (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F))),
        ggLAut K θ ⟨b, hN hb⟩ = u * f)
    (b₀ : G) (hb₀ : b₀ ∈ Bs)
    (hb₀I : ggLAut K θ ⟨b₀, hN hb₀⟩ ∉
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ) :
    ∃ B₀ : Subgroup G, B₀ ≤ Bs ∧ Nat.card B₀ * p = Nat.card Bs ∧ b₀ ∉ B₀ ∧
      (∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈
        LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ → b ∈ B₀) ∧
      ∃ T : Subgroup G, T ≤ Subgroup.centralizer (B₀ : Set G) ∧
        (∀ a ∈ T, ∀ c ∈ T, a * c = c * a) ∧ b₀ ∈ Subgroup.normalizer (T : Set G) ∧
        (∀ t ∈ T, b₀ * t * b₀⁻¹ = t → ∃ s ∈ T,
          t = ((List.range p).map fun i => b₀ ^ i * s * (b₀ ^ i)⁻¹).prod) ∧
        ∃ e ∈ B₀ ⊓ T, e ≠ 1 := by
  classical
  have hp : p.Prime := hC.1.2.2.2.2.2.1.1
  have hp2 : p ≠ 2 := hC.1.2.2.2.2.2.1.2.1
  have hBs : IsElemAbelian p Bs := hC.2.1.2.1
  have hSC := hC.2.1.2.2.2
  have hm : 1 ≤ m := by
    rcases Nat.eq_zero_or_pos m with h0 | h0
    · have h1 := Finite.one_lt_card (α := F)
      rw [hF, h0, pow_zero] at h1
      omega
    · exact h0
  set θ₁ := θ.trans (TypeA.recipeEquiv d F) with hθ₁
  have hIiff : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ ⟨b, hN hb⟩ ∈
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) F)) Set.univ ↔
      ggLAut K θ₁ ⟨b, hN hb⟩ ∈ linearAutGroup d F := fun b hb => mem_conjImage_iff θ _
  have hsemi : ∀ (b : G) (hb : b ∈ Bs), ggLAut K θ₁ ⟨b, hN hb⟩ ∈ semilinearAutGroup d F :=
    fun b hb => mem_semilinear_of_eq_mul θ _ (hgr b hb)
  set αB : ↥Bs →* MulAut (projectiveSL d F) := (ggLAut K θ₁).comp (Subgroup.inclusion hN)
    with hαB
  obtain ⟨M, σ, hσp, hfr, ω, hωσ, hωp, hω1⟩ := hframe p d F hp hp2 hd (by rw [hF]; exact hpF)
    hpd αB.range
    (by
      rintro _ ⟨a, rfl⟩ _ ⟨c, rfl⟩
      rw [← map_mul, ← map_mul, hBs.1.is_comm.comm a c])
    (by
      rintro _ ⟨a, rfl⟩
      have ha : a ^ p = 1 := Subtype.ext (by simpa using hBs.2 a a.2)
      rw [← map_pow, ha, map_one])
    (by
      rintro _ ⟨a, rfl⟩
      exact hsemi a a.2)
  obtain ⟨D₀, k₀, hD₀, -, hfr₀⟩ := hfr _ ⟨⟨b₀, hb₀⟩, rfl⟩
  have hfr₀' : ggLAut K θ₁ ⟨b₀, hN hb₀⟩ = conjAut d F M * conjAut d F D₀ *
      fieldAut d F (σ ^ k₀) * (conjAut d F M)⁻¹ := hfr₀
  have hσ'1 : σ ^ k₀ ≠ 1 := by
    intro h1
    apply hb₀I
    rw [hIiff b₀ hb₀, hfr₀', h1, map_one, mul_one]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (conjAut_mem_linearAutGroup M)
      (conjAut_mem_linearAutGroup D₀)) (Subgroup.inv_mem _ (conjAut_mem_linearAutGroup M))
  have hσ'p : (σ ^ k₀) ^ p = 1 := by rw [← pow_mul, mul_comm, pow_mul, hσp, one_pow]
  have : Fact p.Prime := ⟨hp⟩
  have hσ'o : orderOf (σ ^ k₀) = p := orderOf_eq_prime hσ'p hσ'1
  have hωσ' : (σ ^ k₀) (ω : F) = ω :=
    Subgroup.pow_mem (fixingSubgroup (ω : F)) (show σ ∈ fixingSubgroup (ω : F) from hωσ) k₀
  have hF5 : 5 ≤ Nat.card F := by
    obtain ⟨φ₁, -, -, -, hcardAut, -⟩ :=
      finite_field_automorphism_fixed_field_cardinality Nat.prime_two hm hF
    have h1 : p ∣ m := hcardAut ▸ hσ'o ▸ orderOf_dvd_natCard (σ ^ k₀)
    have h2 : p ≤ m := Nat.le_of_dvd (by omega) h1
    have h3 : 3 ≤ p := by
      have := hp.two_le
      omega
    rw [hF]
    calc 5 ≤ 2 ^ 3 := by norm_num
      _ ≤ 2 ^ m := Nat.pow_le_pow_right (by norm_num) (by omega)
  obtain ⟨φ₀, -, hφker, hlift⟩ := exists_lift hd (by omega) (by omega) (by omega) hperf θ₁
  have hSL : commutator (Matrix.SpecialLinearGroup (Fin d) F) = ⊤ :=
    (CFSG.LinearGroups.special_linear_isPerfect (by omega) (Or.inl hd)).commutator_eq_top
  set φ' : Matrix.SpecialLinearGroup (Fin d) F →* G := (K.subtype.comp φ₀).comp
    (CatalogueBHigherLinearAction.slConjugation d F M).toMonoidHom with hφ'
  have hφ'ker : φ'.ker ≤ Subgroup.center (Matrix.SpecialLinearGroup (Fin d) F) := by
    refine ker_comp_slConjugation_le (K.subtype.comp φ₀) ?_ M
    intro h hh
    apply hφker
    rw [MonoidHom.mem_ker] at hh ⊢
    exact K.subtype_injective (by rw [← MonoidHom.comp_apply, hh, map_one])
  have hact : ∀ (b : G) (hb : b ∈ Bs) (D₁ : GL (Fin d) F) (τ : F ≃+* F),
      ggLAut K θ₁ ⟨b, hN hb⟩ =
        conjAut d F M * conjAut d F D₁ * fieldAut d F τ * (conjAut d F M)⁻¹ →
      ∀ h, b * φ' h * b⁻¹ = φ' (CatalogueBHigherLinearAction.slConjugation d F D₁
        (Matrix.SpecialLinearGroup.map τ.toRingHom h)) :=
    fun b hb D₁ τ hbD h => conj_frame_eq hSL θ₁ φ₀ hlift (hN hb) M D₁ τ hbD h
  obtain ⟨B₀, hB₀s, hcard, hb₀B₀, hB₀iff⟩ := exists_inner_hyperplane hp hBs hm hF hd αB
    (fun b => hsemi b b.2) hb₀ (fun h => hb₀I ((hIiff b₀ hb₀).mpr h))
  have hB₀act : ∀ b ∈ B₀, ∃ D₁ : GL (Fin d) F, (D₁ : Matrix (Fin d) (Fin d) F).IsDiag ∧
      ∀ h, b * φ' h * b⁻¹ = φ' (CatalogueBHigherLinearAction.slConjugation d F D₁ h) := by
    intro b hb
    have hbs := hB₀s hb
    obtain ⟨D₁, k, hD₁, -, hbfr⟩ := hfr _ ⟨⟨b, hbs⟩, rfl⟩
    have hbfr' : ggLAut K θ₁ ⟨b, hN hbs⟩ = conjAut d F M * conjAut d F D₁ *
        fieldAut d F (σ ^ k) * (conjAut d F M)⁻¹ := hbfr
    have hlin : ggLAut K θ₁ ⟨b, hN hbs⟩ ∈ linearAutGroup d F := (hB₀iff b hbs).mp hb
    rw [hbfr'] at hlin
    have hk : σ ^ k = 1 := eq_one_of_frame_mem_linear hd hlin
    rw [hk] at hbfr'
    exact ⟨D₁, hD₁, fun h => (hact b hbs D₁ 1 hbfr' h).trans rfl⟩
  have hij : (⟨0, by omega⟩ : Fin d) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
  have hil : (⟨0, by omega⟩ : Fin d) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  have hjl : (⟨1, by omega⟩ : Fin d) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
  obtain ⟨T, hTr, hTC, hTab, hb₀T, hnorm, e, heT, he1, heb, hep⟩ :=
    exists_lang_torus hp hij hil hjl φ' hφ'ker hσ'o hD₀ (hact b₀ hb₀ D₀ _ hfr₀') hB₀act hωσ'
      hωp hω1
  have heK : e ∈ K := by
    obtain ⟨h, rfl⟩ := hTr heT
    exact (φ₀ _).2
  have heb' : b₀ * e = e * b₀ := by
    calc b₀ * e = b₀ * e * b₀⁻¹ * b₀ := by group
      _ = e * b₀ := by rw [heb]
  have heBs : e ∈ Bs := mem_of_lang_torus hp hBs hSC hB₀s hcard hb₀ hb₀B₀ (hTC heT) heb' hep
  have heB₀ : e ∈ B₀ := by
    rw [hB₀iff e heBs]
    exact (hIiff e heBs).mp (ggLAut_mem_conjImage_of_mem θ heK (hN heBs))
  exact ⟨B₀, hB₀s, hcard, hb₀B₀, fun b hb hbI => (hB₀iff b hb).mpr ((hIiff b hb).mp hbI), T,
    hTC, hTab, hb₀T, hnorm, e, ⟨heB₀, heT⟩, he1⟩

end NbrLangTypeA

open NbrLangTypeA

@[expose] def GGTypeASplitCoprimeLabel (p : ℕ) (lab : LargeEvenLabel) : Prop :=
  (lab.tag = .A ∧ 2 ≤ lab.rank ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ lab.rank + 1) ∨
    (lab.tag = .D ∧ lab.rank = 3 ∧ p ∣ 2 ^ lab.n - 1 ∧ ¬ p ∣ 4)

theorem ggNbrLangTorusAxisOn_typeASplit (hframe : GGTypeASplitFrameInput) :
    GGNbrLangTorusAxisOn GGTypeASplitCoprimeLabel := by
  intro G _ _ p B Bs x L D J hC y K hK hN P hP
  obtain ⟨hperf, lab, hlab, hraw⟩ := hP
  refine ⟨hperf, lab, hlab, ?_⟩
  by_cases hS : GGTypeASplitCoprimeLabel p lab
  · obtain ⟨t, l, n⟩ := lab
    rcases hS with ⟨ht, hl, hpn, hpd⟩ | ⟨ht, hl, hpn, hpd⟩ <;> dsimp only at ht hl hpn hpd <;>
      subst ht
    · dsimp only [LargeEvenRawDatum] at hraw ⊢
      obtain ⟨F, _, _, hF, hs, hna, θ, hPθ⟩ := hraw
      refine ⟨F, inferInstance, inferInstance, hF, hs, hna, θ, hPθ,
        fun _ hgr b₀ hb₀ hb₀I => ?_⟩
      exact lang_axis_of_linear hframe hC hN hperf (by omega) hF hpn hpd θ hgr b₀ hb₀ hb₀I
    · subst hl
      simp only [LargeEvenRawDatum, ↓reduceIte] at hraw ⊢
      obtain ⟨F, _, _, hF, hs, hna, θ, hPθ⟩ := hraw
      refine ⟨F, inferInstance, inferInstance, hF, hs, hna, θ, hPθ,
        fun _ hgr b₀ hb₀ hb₀I => ?_⟩
      exact lang_axis_of_linear hframe hC hN hperf (by omega) hF hpn hpd θ hgr b₀ hb₀ hb₀I
  · exact largeEvenRawDatum_mono
      (fun R _ I F ⟨hs, hna, θ, hθ⟩ => ⟨hs, hna, θ, hθ, fun h => absurd h hS⟩) hraw

theorem ggNbrLangTorusAxisInput_of_typeASplit (hframe : GGTypeASplitFrameInput)
    (hrest : GGNbrLangTorusAxisOn fun p lab => ¬ GGTypeASplitCoprimeLabel p lab) :
    GGNbrLangTorusAxisInput :=
  ggNbrLangTorusAxisInput_of_on
    (ggNbrLangTorusAxisOn_true_of (ggNbrLangTorusAxisOn_typeASplit hframe) hrest)

end CFSG.StandardType

end

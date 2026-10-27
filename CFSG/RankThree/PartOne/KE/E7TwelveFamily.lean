module

public import CFSG.RankThree.PartOne.KE.ThreeA1Group

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.RankThree.Chevalley
open CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open CFSG.RankThree.Classical (conjSL conjSL_one diagUnitOne)
open scoped Pointwise MatrixGroups commutatorElement

theorem commutator_mul_central {G : Type*} [Group G] {z₁ z₂ : G} (h₁ : z₁ ∈ Subgroup.center G)
    (h₂ : z₂ ∈ Subgroup.center G) (a b : G) : ⁅z₁ * a, z₂ * b⁆ = ⁅a, b⁆ := by
  have e1 : ∀ (z g : G), z ∈ Subgroup.center G → z * g * z⁻¹ = g := fun z g hz => by
    rw [mul_inv_eq_iff_eq_mul]
    exact (Subgroup.mem_center_iff.1 hz g).symm
  calc ⁅z₁ * a, z₂ * b⁆ = z₁ * (a * z₂ * b * a⁻¹) * z₁⁻¹ * (b⁻¹ * z₂⁻¹) := by
        simp only [commutatorElement_def]
        group
    _ = (a * z₂ * b * a⁻¹) * (b⁻¹ * z₂⁻¹) := by rw [e1 z₁ _ h₁]
    _ = a * (z₂ * (b * a⁻¹ * b⁻¹) * z₂⁻¹) := by group
    _ = a * (b * a⁻¹ * b⁻¹) := by rw [e1 z₂ _ h₂]
    _ = ⁅a, b⁆ := by
        simp only [commutatorElement_def]
        group

theorem perfect_le_of_commutator_mem {G : Type*} [Group G] {S : Subgroup G}
    (hS : Group.IsPerfect S) {K : Subgroup G} (h : ∀ a ∈ S, ∀ b ∈ S, ⁅a, b⁆ ∈ K) : S ≤ K := by
  have h1 : commutator S ≤ K.comap S.subtype := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    exact h a a.2 b b.2
  rw [hS.commutator_eq_top] at h1
  intro x hx
  exact h1 (Subgroup.mem_top (⟨x, hx⟩ : S))

section Generic

variable {τ : Tag} {L : Type} [Field L] {r₁ r₂ r₃ : Fin τ.rank → ℤ}

theorem exists_central_of_mu_eq {M : Type*} [Group M] (μ : SL2 L × SL2 L × SL2 L →* M)
    (hker : ∀ A B C : SL2 L, μ (A, B, C) = 1 → ∃ l : L, l ^ 2 = 1 ∧
      (A : Matrix (Fin 2) (Fin 2) L) = Matrix.scalar (Fin 2) l ∧
      (B : Matrix (Fin 2) (Fin 2) L) = Matrix.scalar (Fin 2) l ∧
      (C : Matrix (Fin 2) (Fin 2) L) = Matrix.scalar (Fin 2) l)
    {P₁ P₂ P₃ Q₁ Q₂ Q₃ : SL2 L} (h : μ (P₁, P₂, P₃) = μ (Q₁, Q₂, Q₃)) :
    ∃ z ∈ Subgroup.center (SL2 L), P₁ = z * Q₁ ∧ P₂ = z * Q₂ ∧ P₃ = z * Q₃ := by
  have h1 : μ (P₁ * Q₁⁻¹, P₂ * Q₂⁻¹, P₃ * Q₃⁻¹) = 1 := by
    have e : (P₁ * Q₁⁻¹, P₂ * Q₂⁻¹, P₃ * Q₃⁻¹) = (P₁, P₂, P₃) * (Q₁, Q₂, Q₃)⁻¹ := rfl
    rw [e, map_mul, map_inv, h, mul_inv_cancel]
  obtain ⟨l, hl, h₁, h₂, h₃⟩ := hker _ _ _ h1
  have hz : P₁ * Q₁⁻¹ ∈ Subgroup.center (SL2 L) := by
    rw [Matrix.SpecialLinearGroup.mem_center_iff]
    exact ⟨l, by simpa using hl, h₁.symm⟩
  have e2 : P₂ * Q₂⁻¹ = P₁ * Q₁⁻¹ := Subtype.ext (h₂.trans h₁.symm)
  have e3 : P₃ * Q₃⁻¹ = P₁ * Q₁⁻¹ := Subtype.ext (h₃.trans h₁.symm)
  refine ⟨P₁ * Q₁⁻¹, hz, by group, ?_, ?_⟩
  · rw [← e2]
    group
  · rw [← e3]
    group

theorem three_A1_cyclic_family [IsAlgClosed L]
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    (μ : SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C, μ (A, B, C) =
      rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
    (hker : ∀ A B C : SL2 L, μ (A, B, C) = 1 → ∃ l : L, l ^ 2 = 1 ∧
      (A : Matrix (Fin 2) (Fin 2) L) = Matrix.scalar (Fin 2) l ∧
      (B : Matrix (Fin 2) (Fin 2) L) = Matrix.scalar (Fin 2) l ∧
      (C : Matrix (Fin 2) (Fin 2) L) = Matrix.scalar (Fin 2) l)
    (Fr : L →+* L) (n : ModGL τ L)
    (hΘ : ∀ A B C : SL2 L, n * Units.map (entrywiseHom Fr) (μ (A, B, C)) * n⁻¹ =
      μ (Matrix.SpecialLinearGroup.map Fr C, Matrix.SpecialLinearGroup.map Fr A,
        Matrix.SpecialLinearGroup.map Fr B))
    (S₃ : Subgroup (SL2 L)) [Finite S₃]
    (hS₃ : ∀ B : SL2 L, B ∈ S₃ ↔ Matrix.SpecialLinearGroup.map Fr
      (Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr B)) = B)
    (hq₃ : CFSG.IsQuasisimple S₃)
    (hz₃ : Subgroup.centralizer ((S₃.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) :
    ∃ P : Subgroup (ModGL τ L), Finite P ∧ CFSG.IsQuasisimple P ∧
      P ≤ rootSpan τ L (threeRootSet r₁ r₂ r₃) ∧
      P ≤ twistedFixedPoints n (Units.map (entrywiseHom Fr)) ∧ P ≤ adjointGroup τ L ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃),
        y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) → ∀ u ∈ P, y * u * y⁻¹ ∈ P) ∧
      (∀ y ∈ torusGroup τ L ⊔ rootSpan τ L (threeRootSet r₁ r₂ r₃),
        y ∈ twistedFixedPoints n (Units.map (entrywiseHom Fr)) →
        (∀ u ∈ P, y * u = u * y) →
        y ∈ subtorusSigma n (Units.map (entrywiseHom Fr)) (threeRootSet r₁ r₂ r₃)) ∧
      (∀ g : ModGL τ L, g ∈ P ↔ ∃ X ∈ S₃, μ (X, Matrix.SpecialLinearGroup.map Fr X,
        Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map Fr X)) = g) := by
  classical
  set Φ : ModGL τ L →* ModGL τ L := Units.map (entrywiseHom Fr) with hΦ
  set Rs := twistedFixedPoints n Φ with hRs
  set F : SL2 L →* SL2 L := Matrix.SpecialLinearGroup.map Fr with hF
  have hρadj : ∀ r (A : SL2 L), rootSL2 τ L r A ∈ adjointGroup τ L := fun r A =>
    (exceptional_Lang_root_rank_one_data τ L r).2.2.2.2.1 A
  have hQS : rootSpan τ L (threeRootSet r₁ r₂ r₃) =
      rootRankOneGroup τ L r₁ ⊔ rootRankOneGroup τ L r₂ ⊔ rootRankOneGroup τ L r₃ :=
    rootSpan_threeRootSet h₁ h₂ h₃
  have hF3 : ∀ X ∈ S₃, F (F (F X)) = X := fun X hX => (hS₃ X).1 hX
  have hF1 : ∀ X ∈ S₃, F X ∈ S₃ := fun X hX => (hS₃ _).2 (congrArg F (hF3 X hX))
  have hF2 : ∀ X ∈ S₃, F (F X) ∈ S₃ := fun X hX => hF1 _ (hF1 _ hX)
  set ν : SL2 L →* ModGL τ L := μ.comp ((MonoidHom.id (SL2 L)).prod (F.prod (F.comp F))) with hνdef
  have hν : ∀ X, ν X = μ (X, F X, F (F X)) := fun X => rfl
  set Γ : Subgroup (ModGL τ L) := rootSpan τ L (threeRootSet r₁ r₂ r₃) ⊓ Rs with hΓ
  have hνQ : ∀ X, ν X ∈ rootSpan τ L (threeRootSet r₁ r₂ r₃) := fun X => by
    rw [hν, hμ, hQS]
    exact mul_mem (mul_mem (Subgroup.mem_sup_left (Subgroup.mem_sup_left ⟨X, rfl⟩))
      (Subgroup.mem_sup_left (Subgroup.mem_sup_right ⟨F X, rfl⟩)))
      (Subgroup.mem_sup_right ⟨F (F X), rfl⟩)
  have hνΓ : ∀ X ∈ S₃, ν X ∈ Γ := fun X hX => by
    refine ⟨hνQ X, ?_⟩
    show n * Φ (ν X) * n⁻¹ = ν X
    rw [hν, hΘ, hF3 X hX]
  have hcomm_le : ⁅Γ, Γ⁆ ≤ S₃.map ν := by
    refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    obtain ⟨A₁, B₁, C₁, rfl⟩ := mem_sup_three hc12 hc13 hc23 (by rw [← hQS]; exact hg₁.1)
    obtain ⟨A₂, B₂, C₂, rfl⟩ := mem_sup_three hc12 hc13 hc23 (by rw [← hQS]; exact hg₂.1)
    rw [← hμ A₁ B₁ C₁] at hg₁ ⊢
    rw [← hμ A₂ B₂ C₂] at hg₂ ⊢
    have e₁ : μ (F C₁, F A₁, F B₁) = μ (A₁, B₁, C₁) := by
      have h := (mem_twistedFixedPoints.1 hg₁.2 : n * Φ (μ (A₁, B₁, C₁)) * n⁻¹ = _)
      rwa [hΘ] at h
    have e₂ : μ (F C₂, F A₂, F B₂) = μ (A₂, B₂, C₂) := by
      have h := (mem_twistedFixedPoints.1 hg₂.2 : n * Φ (μ (A₂, B₂, C₂)) * n⁻¹ = _)
      rwa [hΘ] at h
    obtain ⟨z₁, hz₁, h1a, h1b, h1c⟩ := exists_central_of_mu_eq μ hker e₁
    obtain ⟨z₂, hz₂, h2a, h2b, h2c⟩ := exists_central_of_mu_eq μ hker e₂
    have hA₁ : A₁ = z₁⁻¹ * F C₁ := eq_inv_mul_of_mul_eq h1a.symm
    have hA₂ : A₂ = z₂⁻¹ * F C₂ := eq_inv_mul_of_mul_eq h2a.symm
    have hB₁ : B₁ = z₁⁻¹ * F A₁ := eq_inv_mul_of_mul_eq h1b.symm
    have hB₂ : B₂ = z₂⁻¹ * F A₂ := eq_inv_mul_of_mul_eq h2b.symm
    have hC₁ : C₁ = z₁⁻¹ * F B₁ := eq_inv_mul_of_mul_eq h1c.symm
    have hC₂ : C₂ = z₂⁻¹ * F B₂ := eq_inv_mul_of_mul_eq h2c.symm
    have hiz₁ := inv_mem hz₁
    have hiz₂ := inv_mem hz₂
    have hB : ⁅B₁, B₂⁆ = F ⁅A₁, A₂⁆ := by
      rw [hB₁, hB₂, commutator_mul_central hiz₁ hiz₂, map_commutatorElement]
    have hC : ⁅C₁, C₂⁆ = F ⁅B₁, B₂⁆ := by
      rw [hC₁, hC₂, commutator_mul_central hiz₁ hiz₂, map_commutatorElement]
    have hA : ⁅A₁, A₂⁆ = F ⁅C₁, C₂⁆ := by
      rw [hA₁, hA₂, commutator_mul_central hiz₁ hiz₂, map_commutatorElement]
    have hmem : ⁅A₁, A₂⁆ ∈ S₃ := by
      refine (hS₃ _).2 ?_
      change F (F (F ⁅A₁, A₂⁆)) = ⁅A₁, A₂⁆
      rw [← hB, ← hC, ← hA]
    refine ⟨⁅A₁, A₂⁆, hmem, ?_⟩
    have hc : ⁅μ (A₁, B₁, C₁), μ (A₂, B₂, C₂)⁆ = μ (⁅A₁, A₂⁆, ⁅B₁, B₂⁆, ⁅C₁, C₂⁆) := by
      rw [← map_commutatorElement]
      rfl
    rw [hν, hc, hC, hB]
  have hperf_le : S₃.map ν ≤ ⁅Γ, Γ⁆ := by
    rintro _ ⟨X, hX, rfl⟩
    refine perfect_le_of_commutator_mem hq₃.1 (K := (⁅Γ, Γ⁆).comap ν) (fun a ha b hb => ?_) hX
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hνΓ a ha) (hνΓ b hb)
  have hPeq : ⁅Γ, Γ⁆ = S₃.map ν := le_antisymm hcomm_le hperf_le
  let φ : S₃ →* S₃.map ν :=
    (ν.comp S₃.subtype).codRestrict (S₃.map ν) (fun x => ⟨x, x.2, rfl⟩)
  have hφs : Function.Surjective φ := by
    rintro ⟨_, X, hX, rfl⟩
    exact ⟨⟨X, hX⟩, Subtype.ext rfl⟩
  have hPfin : Finite (S₃.map ν) := Finite.of_surjective φ hφs
  have hφ1 : ∃ k, φ k ≠ 1 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨-, -, a, b, hab⟩ := hq₃
    obtain ⟨a', rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b', rfl⟩ := QuotientGroup.mk_surjective b
    apply hab
    have hsc : ∀ k : S₃, ∃ l : L,
        ((k : SL2 L) : Matrix (Fin 2) (Fin 2) L) = Matrix.scalar (Fin 2) l := fun k => by
      have h1 : ν k = 1 := congrArg Subtype.val (hcon k)
      rw [hν] at h1
      obtain ⟨l, -, h1', -, -⟩ := hker _ _ _ h1
      exact ⟨l, h1'⟩
    obtain ⟨l₁, h1⟩ := hsc a'
    obtain ⟨l₂, h2⟩ := hsc b'
    have hab' : a' * b' = b' * a' := by
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subgroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, h1, h2]
      rw [← map_mul, ← map_mul, mul_comm]
    rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, hab']
  have hPq : CFSG.IsQuasisimple (S₃.map ν) :=
    CFSG.LieType.CurtisTits.isQuasisimple_of_surjective hq₃ hφs hφ1
  have hS3 : ∀ α ∈ threeRootSet r₁ r₂ r₃, IsRoot τ α := by
    intro α hα
    rcases hα with rfl | rfl | rfl | rfl | rfl | rfl
    exacts [h₁, IsRoot.neg h₁, h₂, IsRoot.neg h₂, h₃, IsRoot.neg h₃]
  refine ⟨S₃.map ν, hPfin, hPq, ?_, ?_, ?_, ?_, ?_, fun g => Iff.rfl⟩
  · rintro _ ⟨X, -, rfl⟩
    exact hνQ X
  · rintro _ ⟨X, hX, rfl⟩
    exact (hνΓ X hX).2
  · rintro _ ⟨X, -, rfl⟩
    rw [hν, hμ]
    exact mul_mem (mul_mem (hρadj _ _) (hρadj _ _)) (hρadj _ _)
  ·
    intro y hy hyR u hu
    rw [← hPeq] at hu ⊢
    have hN : y ∈ Subgroup.normalizer
        (rootSpan τ L (threeRootSet r₁ r₂ r₃) : Set (ModGL τ L)) :=
      (sup_le (torusGroup_le_normalizer_rootSpan hS3) Subgroup.le_normalizer) hy
    have hΓn : ∀ g ∈ Γ, y * g * y⁻¹ ∈ Γ := fun g hg =>
      Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hN g).1 (Subgroup.mem_inf.1 hg).1,
        mul_mem (mul_mem hyR (Subgroup.mem_inf.1 hg).2) (inv_mem hyR)⟩
    have h1 : ⁅Γ, Γ⁆ ≤ (⁅Γ, Γ⁆).comap (MulAut.conj y).toMonoidHom := by
      refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
      rw [Subgroup.mem_comap, map_commutatorElement]
      exact Subgroup.commutator_mem_commutator (hΓn g₁ hg₁) (hΓn g₂ hg₂)
    have h2 := h1 hu
    simpa [MulAut.conj_apply] using h2
  ·
    intro y hy hyR hcomm
    obtain ⟨b, A, B, C, rfl⟩ := exists_decomp hc12 hc13 hc23 h₁ h₂ h₃ hy
    obtain ⟨hc1', hc2', hc3'⟩ := conj_three_rootSL2 hc12 hc13 hc23 h₁ h₂ h₃ b A B C
    set t := rootDiagUnit τ b with ht
    have htH : t ∈ torusGroup τ L := rootDiagUnit_mem_torusGroup b
    set y := t * (rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C) with hydef
    set X₁ : GL (Fin 2) L := diagUnitOne (rootChar b r₁) * Matrix.SpecialLinearGroup.toGL A
      with hX₁
    set X₂ : GL (Fin 2) L := diagUnitOne (rootChar b r₂) * Matrix.SpecialLinearGroup.toGL B
      with hX₂
    set X₃ : GL (Fin 2) L := diagUnitOne (rootChar b r₃) * Matrix.SpecialLinearGroup.toGL C
      with hX₃
    have hcen : ∀ U ∈ S₃, ∃ z ∈ Subgroup.center (SL2 L), conjSL X₁ U = z * U ∧
        conjSL X₂ (F U) = z * F U ∧ conjSL X₃ (F (F U)) = z * F (F U) := by
      intro U hU
      have hmem : ν U ∈ S₃.map ν := ⟨U, hU, rfl⟩
      have h := hcomm _ hmem
      have h2 : y * ν U * y⁻¹ = ν U := by rw [h, mul_inv_cancel_right]
      have h3 : y * ν U * y⁻¹ =
          μ (conjSL X₁ U, conjSL X₂ (F U), conjSL X₃ (F (F U))) := by
        rw [hν, hμ, hμ]
        calc y * (rootSL2 τ L r₁ U * rootSL2 τ L r₂ (F U) * rootSL2 τ L r₃ (F (F U))) * y⁻¹
            = (y * rootSL2 τ L r₁ U * y⁻¹) * (y * rootSL2 τ L r₂ (F U) * y⁻¹) *
                (y * rootSL2 τ L r₃ (F (F U)) * y⁻¹) := by group
          _ = _ := by rw [hc1' U, hc2' (F U), hc3' (F (F U))]
      rw [h3, hν] at h2
      obtain ⟨z, hz, e1, e2, e3⟩ := exists_central_of_mu_eq μ hker h2
      exact ⟨z, hz, e1, e2, e3⟩
    have hcen1 : ∀ V ∈ S₃, ∃ z ∈ Subgroup.center (SL2 L), conjSL X₁ V = z * V := fun V hV => by
      obtain ⟨z, hz, e1, -, -⟩ := hcen V hV
      exact ⟨z, hz, e1⟩
    have hcen2 : ∀ V ∈ S₃, ∃ z ∈ Subgroup.center (SL2 L), conjSL X₂ V = z * V := fun V hV => by
      obtain ⟨z, hz, -, e2, -⟩ := hcen (F (F V)) (hF2 V hV)
      rw [hF3 V hV] at e2
      exact ⟨z, hz, e2⟩
    have hcen3 : ∀ V ∈ S₃, ∃ z ∈ Subgroup.center (SL2 L), conjSL X₃ V = z * V := fun V hV => by
      obtain ⟨z, hz, -, -, e3⟩ := hcen (F V) (hF1 V hV)
      rw [hF3 V hV] at e3
      exact ⟨z, hz, e3⟩
    have hfixed : ∀ (X : GL (Fin 2) L), (∀ V ∈ S₃, ∃ z ∈ Subgroup.center (SL2 L),
        conjSL X V = z * V) → ∀ U ∈ S₃, conjSL X U = U := by
      intro X hX U hU
      have hle : S₃ ≤ (conjSL X).eqLocus (MonoidHom.id (SL2 L)) := by
        refine perfect_le_of_commutator_mem hq₃.1 fun a ha b hb => ?_
        obtain ⟨za, hza, ea⟩ := hX a ha
        obtain ⟨zb, hzb, eb⟩ := hX b hb
        show conjSL X ⁅a, b⁆ = ⁅a, b⁆
        rw [map_commutatorElement, ea, eb, commutator_mul_central hza hzb]
      exact hle hU
    have hU₁ := hfixed X₁ hcen1
    have hU₂ := hfixed X₂ hcen2
    have hU₃ := hfixed X₃ hcen3
    have hfac : ∀ (r : Fin τ.rank → ℤ) (hr : IsRoot τ r) (M : SL2 L) (X : GL (Fin 2) L)
        (hX : X = diagUnitOne (rootChar b r) * Matrix.SpecialLinearGroup.toGL M)
        (hSX : ∀ U ∈ S₃, conjSL X U = U),
        t * rootSL2 τ L r M ∈ torusGroup τ L ∧
          ∀ A' : SL2 L, rootSL2 τ L r (conjSL X A') = rootSL2 τ L r A' := by
      intro r hr M X hX hSX
      have hconj := conj_rootSL2_torus_mul hr b M
      rw [← hX] at hconj
      have hc : ∀ U ∈ S₃, (t * rootSL2 τ L r M) * rootSL2 τ L r U =
          rootSL2 τ L r U * (t * rootSL2 τ L r M) := fun U hU => by
        have h := hconj U
        rw [hSX U hU] at h
        exact mul_inv_eq_iff_eq_mul.1 h
      have hyH : t * rootSL2 τ L r M ∈
          (torusGroup τ L : Set (ModGL τ L)) * (rootRankOneGroup τ L r : Set (ModGL τ L)) :=
        ⟨t, htH, rootSL2 τ L r M, ⟨M, rfl⟩, rfl⟩
      have hall := commute_rootSL2_of_commute_fixed hr hz₃ hyH hc
      refine ⟨mem_torusGroup_of_centralizes_rootSL2 hr hyH hall, fun A' => ?_⟩
      have h := hconj A'
      rw [hall A', mul_inv_cancel_right] at h
      exact h.symm
    obtain ⟨hT₁, hF₁⟩ := hfac r₁ h₁ A X₁ hX₁ hU₁
    obtain ⟨hT₂, hF₂⟩ := hfac r₂ h₂ B X₂ hX₂ hU₂
    obtain ⟨hT₃, hF₃⟩ := hfac r₃ h₃ C X₃ hX₃ hU₃
    have hA : rootSL2 τ L r₁ A ∈ torusGroup τ L := by
      have := mul_mem (inv_mem htH) hT₁
      rwa [inv_mul_cancel_left] at this
    have hB : rootSL2 τ L r₂ B ∈ torusGroup τ L := by
      have := mul_mem (inv_mem htH) hT₂
      rwa [inv_mul_cancel_left] at this
    have hC : rootSL2 τ L r₃ C ∈ torusGroup τ L := by
      have := mul_mem (inv_mem htH) hT₃
      rwa [inv_mul_cancel_left] at this
    have hyH : y ∈ torusGroup τ L := mul_mem htH (mul_mem (mul_mem hA hB) hC)
    have hcZ : y ∈ Subgroup.centralizer
        ((rootSpan τ L (threeRootSet r₁ r₂ r₃) : Subgroup (ModGL τ L)) : Set (ModGL τ L)) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      rw [SetLike.mem_coe, hQS] at hg
      obtain ⟨A', B', C', rfl⟩ := mem_sup_three hc12 hc13 hc23 hg
      have f₁ : Commute y (rootSL2 τ L r₁ A') := by
        have h := hc1' A'
        rw [hF₁ A'] at h
        exact mul_inv_eq_iff_eq_mul.1 h
      have f₂ : Commute y (rootSL2 τ L r₂ B') := by
        have h := hc2' B'
        rw [hF₂ B'] at h
        exact mul_inv_eq_iff_eq_mul.1 h
      have f₃ : Commute y (rootSL2 τ L r₃ C') := by
        have h := hc3' C'
        rw [hF₃ C'] at h
        exact mul_inv_eq_iff_eq_mul.1 h
      exact ((f₁.mul_right f₂).mul_right f₃).eq.symm
    exact ⟨mem_twistedTorusOf.2 ⟨hyH, hyR⟩, hcZ⟩

end Generic

end CFSG.RankThree.PartOne.KE

module

public import CFSG.RankThree.PartOne.KE.E7ThreeNodes
public import CFSG.RankThree.PartOne.KE.SigmaFactorTransport
public import CFSG.RankThree.PartOne.KE.A1Fixed

public noncomputable section

namespace CFSG.RankThree.PartOne.KE

open Matrix CFSG CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.RankThree.Chevalley CFSG.RankThree.Classical CFSG.RankThree.PartOne.KGD
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
open scoped Matrix MatrixGroups Pointwise commutatorElement

section Frob

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem exists_frob_three (hf : 1 ≤ f) :
    ∃ (k : Type) (_ : Field k) (_ : Finite k) (_ : Algebra k L) (Fr₃ : L →+* L),
      4 ≤ Nat.card k ∧ (∀ c, Fr₃ c = c ^ Nat.card k) ∧
        (iterateFrobenius L ℓ f).comp ((iterateFrobenius L ℓ f).comp (iterateFrobenius L ℓ f)) =
          Fr₃ := by
  have hℓ : ℓ.Prime := Fact.out
  obtain ⟨k, _, _, _, hk⟩ := exists_finite_field_into ℓ (3 * f) (by omega) L
  refine ⟨k, inferInstance, inferInstance, inferInstance, iterateFrobenius L ℓ (3 * f), ?_,
    fun c => ?_, ?_⟩
  · rw [hk]
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ ℓ ^ 2 := Nat.pow_le_pow_left hℓ.two_le 2
      _ ≤ ℓ ^ (3 * f) := Nat.pow_le_pow_right hℓ.pos (by omega)
  · rw [hk]
    exact iterateFrobenius_def ℓ (3 * f) c
  · refine RingHom.ext fun c => ?_
    simp only [RingHom.comp_apply, iterateFrobenius_def]
    rw [← pow_mul, ← pow_mul]
    congr 1
    ring

end Frob

section Generic

variable {τ : Tag} {L : Type} [Field L] {r₁ r₂ r₃ : Fin τ.rank → ℤ}

theorem three_A1_theta
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (μ : SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C, μ (A, B, C) = rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
    (Fr : L →+* L) (n : ModGL τ L) (M₁ M₂ M₃ : GL (Fin 2) L)
    (e₁ : ∀ A : SL2 L, n * rootSL2 τ L r₁ A * n⁻¹ = rootSL2 τ L r₂ (conjSL M₁ A))
    (e₂ : ∀ B : SL2 L, n * rootSL2 τ L r₂ B * n⁻¹ = rootSL2 τ L r₃ (conjSL M₂ B))
    (e₃ : ∀ C : SL2 L, n * rootSL2 τ L r₃ C * n⁻¹ = rootSL2 τ L r₁ (conjSL M₃ C))
    (A B C : SL2 L) :
    n * Units.map (entrywiseHom Fr) (μ (A, B, C)) * n⁻¹ =
      μ (twHom Fr M₃ C, twHom Fr M₁ A, twHom Fr M₂ B) := by
  rw [hμ, hμ, map_mul, map_mul, entrywise_rootSL2_of_field, entrywise_rootSL2_of_field,
    entrywise_rootSL2_of_field]
  have f₁ : n * rootSL2 τ L r₁ (Matrix.SpecialLinearGroup.map Fr A) * n⁻¹ =
      rootSL2 τ L r₂ (twHom Fr M₁ A) := e₁ _
  have f₂ : n * rootSL2 τ L r₂ (Matrix.SpecialLinearGroup.map Fr B) * n⁻¹ =
      rootSL2 τ L r₃ (twHom Fr M₂ B) := e₂ _
  have f₃ : n * rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr C) * n⁻¹ =
      rootSL2 τ L r₁ (twHom Fr M₃ C) := e₃ _
  have c12 := (hc12 (twHom Fr M₃ C) (twHom Fr M₁ A)).eq
  have c13 := (hc13 (twHom Fr M₃ C) (twHom Fr M₂ B)).eq
  calc n * (rootSL2 τ L r₁ (Matrix.SpecialLinearGroup.map Fr A) *
        rootSL2 τ L r₂ (Matrix.SpecialLinearGroup.map Fr B) *
          rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr C)) * n⁻¹
      = (n * rootSL2 τ L r₁ (Matrix.SpecialLinearGroup.map Fr A) * n⁻¹) *
          (n * rootSL2 τ L r₂ (Matrix.SpecialLinearGroup.map Fr B) * n⁻¹) *
            (n * rootSL2 τ L r₃ (Matrix.SpecialLinearGroup.map Fr C) * n⁻¹) := by group
    _ = rootSL2 τ L r₂ (twHom Fr M₁ A) * rootSL2 τ L r₃ (twHom Fr M₂ B) *
          rootSL2 τ L r₁ (twHom Fr M₃ C) := by rw [f₁, f₂, f₃]
    _ = rootSL2 τ L r₂ (twHom Fr M₁ A) * (rootSL2 τ L r₃ (twHom Fr M₂ B) *
          rootSL2 τ L r₁ (twHom Fr M₃ C)) := mul_assoc _ _ _
    _ = rootSL2 τ L r₂ (twHom Fr M₁ A) * (rootSL2 τ L r₁ (twHom Fr M₃ C) *
          rootSL2 τ L r₃ (twHom Fr M₂ B)) := by rw [c13]
    _ = (rootSL2 τ L r₂ (twHom Fr M₁ A) * rootSL2 τ L r₁ (twHom Fr M₃ C)) *
          rootSL2 τ L r₃ (twHom Fr M₂ B) := (mul_assoc _ _ _).symm
    _ = (rootSL2 τ L r₁ (twHom Fr M₃ C) * rootSL2 τ L r₂ (twHom Fr M₁ A)) *
          rootSL2 τ L r₃ (twHom Fr M₂ B) := by rw [c12]

theorem three_A1_lang_data {Fr : L →+* L} (hFr : Function.Bijective Fr)
    (M₁ M₂ M₃ : GL (Fin 2) L) {k : Type} [Field k] [Finite k] [Algebra k L]
    (hk4 : 4 ≤ Nat.card k) {Fr₃ : L →+* L} (hFr₃ : ∀ c, Fr₃ c = c ^ Nat.card k)
    (hFr3eq : Fr.comp (Fr.comp Fr) = Fr₃) (Pm : GL (Fin 2) L)
    (hPm : Pm * Matrix.GeneralLinearGroup.map Fr₃ Pm⁻¹ =
      M₃ * Matrix.GeneralLinearGroup.map Fr (M₂ * Matrix.GeneralLinearGroup.map Fr M₁)) :
    ∃ S₃ : Subgroup (SL2 L), Finite S₃ ∧
      (∀ B : SL2 L, B ∈ S₃ ↔ twHom Fr M₃ (twHom Fr M₂ (twHom Fr M₁ B)) = B) ∧
      CFSG.IsQuasisimple S₃ ∧ CFSG.IsQuasisimple (S₃.map (twHom Fr M₁)) ∧
      CFSG.IsQuasisimple ((S₃.map (twHom Fr M₁)).map (twHom Fr M₂)) ∧
      Subgroup.centralizer ((S₃.map Matrix.SpecialLinearGroup.toGL :
        Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range ∧
      Subgroup.centralizer (((S₃.map (twHom Fr M₁)).map Matrix.SpecialLinearGroup.toGL :
        Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range ∧
      Subgroup.centralizer ((((S₃.map (twHom Fr M₁)).map (twHom Fr M₂)).map
        Matrix.SpecialLinearGroup.toGL : Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
          (Matrix.GeneralLinearGroup.scalar (Fin 2)).range := by
  classical
  refine ⟨(Matrix.SpecialLinearGroup.map (algebraMap k L)).range.map (conjSL Pm), ?_⟩
  obtain ⟨hfin₃, hq₃⟩ := sl2_conj_range_quasisimple (K := k) (L := L) hk4 Pm
  have hz₃ := sl2_conj_range_centralizer (K := k) (L := L) Pm
  have hq₂ := isQuasisimple_map_twHom (Fr := Fr) M₁ hq₃
  have hq₁ := isQuasisimple_map_twHom (Fr := Fr) M₂ hq₂
  have hz₂ := centralizer_map_twHom hFr M₁ hz₃
  have hz₁ := centralizer_map_twHom hFr M₂ hz₂
  refine ⟨hfin₃, fun B => ?_, hq₃, hq₂, hq₁, hz₃, hz₂, hz₁⟩
  rw [twHom_comp_three, hFr3eq, ← hPm]
  exact (sl2_twistedFixed_iff Fr₃ (frobenius_fixed_iff Fr₃ hFr₃) Pm B).symm

theorem conj_mem_commutator_inf {G : Type*} [Group G] {Q R : Subgroup G} {y : G}
    (hy : y ∈ Subgroup.normalizer (Q : Set G)) (hyR : y ∈ R) {u : G}
    (hu : u ∈ ⁅Q ⊓ R, Q ⊓ R⁆) : y * u * y⁻¹ ∈ ⁅Q ⊓ R, Q ⊓ R⁆ := by
  have hΓn : ∀ g ∈ Q ⊓ R, y * g * y⁻¹ ∈ Q ⊓ R := fun g hg =>
    Subgroup.mem_inf.2 ⟨(Subgroup.mem_normalizer_iff.1 hy g).1 (Subgroup.mem_inf.1 hg).1,
      mul_mem (mul_mem hyR (Subgroup.mem_inf.1 hg).2) (inv_mem hyR)⟩
  have h1 : ⁅Q ⊓ R, Q ⊓ R⁆ ≤ (⁅Q ⊓ R, Q ⊓ R⁆).comap (MulAut.conj y).toMonoidHom := by
    refine Subgroup.commutator_le.2 fun g₁ hg₁ g₂ hg₂ => ?_
    rw [Subgroup.mem_comap, map_commutatorElement]
    exact Subgroup.commutator_mem_commutator (hΓn g₁ hg₁) (hΓn g₂ hg₂)
  have h2 := h1 hu
  simpa [MulAut.conj_apply] using h2

theorem three_A1_twisted_sigma_factor [IsAlgClosed L]
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    (μ : SL2 L × SL2 L × SL2 L →* ModGL τ L)
    (hμ : ∀ A B C, μ (A, B, C) = rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C)
    (Fr : L →+* L) (n : ModGL τ L) (G₁ G₂ G₃ : SL2 L →* SL2 L)
    (hΘ : ∀ A B C : SL2 L, n * Units.map (entrywiseHom Fr) (μ (A, B, C)) * n⁻¹ =
      μ (G₃ C, G₁ A, G₂ B))
    (S₁ S₂ S₃ : Subgroup (SL2 L)) [Finite S₃]
    (hS₂ : S₂ = S₃.map G₁) (hS₁ : S₁ = S₂.map G₂)
    (hS₃ : ∀ B : SL2 L, B ∈ S₃ ↔ G₃ (G₂ (G₁ B)) = B)
    (hq₁ : CFSG.IsQuasisimple S₁) (hq₂ : CFSG.IsQuasisimple S₂) (hq₃ : CFSG.IsQuasisimple S₃)
    (hz₁ : Subgroup.centralizer ((S₁.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₂ : Subgroup.centralizer ((S₂.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range)
    (hz₃ : Subgroup.centralizer ((S₃.map Matrix.SpecialLinearGroup.toGL :
      Subgroup (GL (Fin 2) L)) : Set (GL (Fin 2) L)) =
        (Matrix.GeneralLinearGroup.scalar (Fin 2)).range) :
    ∃ P : Subgroup (ModGL τ L),
      SigmaFactor n Fr (threeRootSet r₁ r₂ r₃) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan τ L (threeRootSet r₁ r₂ r₃) : Set (ModGL τ L))) := by
  classical
  have hker : ∀ A B C : SL2 L, μ (A, B, C) = 1 → A ∈ Subgroup.center (SL2 L) ∧
      B ∈ Subgroup.center (SL2 L) ∧ C ∈ Subgroup.center (SL2 L) := fun A B C h =>
    threeA1Tw_mem_center_of_mul_eq_one hc12 hc13 hc23 (by rw [← hμ]; exact h)
  obtain ⟨ν, hν⟩ : ∃ ν : SL2 L →* ModGL τ L, ∀ X, ν X = μ (X, G₁ X, G₂ (G₁ X)) :=
    ⟨μ.comp ((MonoidHom.id (SL2 L)).prod (G₁.prod (G₂.comp G₁))), fun X => rfl⟩
  have hPeq := threeA1Tw_commutator_eq_map hc12 hc13 hc23 h₁ h₂ h₃ μ hμ hker
    (Units.map (entrywiseHom Fr)) n G₁ G₂ G₃ hΘ S₃ hS₃ hq₃.1 ν hν
  obtain ⟨hPfin, hPq⟩ := threeA1Tw_map_isQuasisimple μ hker G₁ G₂ S₃ hq₃ ν hν
  have hρadj : ∀ r (A : SL2 L), rootSL2 τ L r A ∈ adjointGroup τ L := fun r A =>
    (exceptional_Lang_root_rank_one_data τ L r).2.2.2.2.1 A
  refine ⟨S₃.map ν, ⟨fun _ => hPfin, fun _ => hPq, fun _ => ?_, fun _ => ?_, fun _ => ?_,
    fun _ y hy hyR u hu => ?_, fun y hy hcomm => ?_⟩⟩
  · rintro _ ⟨X, -, rfl⟩
    rw [hν]
    exact threeA1Tw_diag_mem_rootSpan h₁ h₂ h₃ μ hμ G₁ G₂ X
  · rintro _ ⟨X, hX, rfl⟩
    rw [hν]
    exact threeA1Tw_diag_mem_fixed μ (Units.map (entrywiseHom Fr)) n G₁ G₂ G₃ hΘ ((hS₃ X).1 hX)
  · rintro _ ⟨X, -, rfl⟩
    rw [hν, hμ]
    exact mul_mem (mul_mem (hρadj _ _) (hρadj _ _)) (hρadj _ _)
  · rw [← hPeq] at hu ⊢
    exact conj_mem_commutator_inf hy hyR hu
  · exact threeA1Tw_centralizer hc12 hc13 hc23 h₁ h₂ h₃ μ hμ hker G₁ G₂ S₁ S₂ S₃ hS₂ hS₁
      hq₁.1 hq₂.1 hq₃.1 hz₁ hz₂ hz₃ hy (fun U hU => by
        rw [← hν]
        exact hcomm () _ ⟨U, hU, rfl⟩)

theorem three_A1_cyclic_sigma_factor [IsAlgClosed L]
    (hc12 : ∀ A B : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₂ B))
    (hc13 : ∀ A C : SL2 L, Commute (rootSL2 τ L r₁ A) (rootSL2 τ L r₃ C))
    (hc23 : ∀ B C : SL2 L, Commute (rootSL2 τ L r₂ B) (rootSL2 τ L r₃ C))
    (h₁ : IsRoot τ r₁) (h₂ : IsRoot τ r₂) (h₃ : IsRoot τ r₃)
    {Fr : L →+* L} (hFr : Function.Bijective Fr) (n : ModGL τ L) (M₁ M₂ M₃ : GL (Fin 2) L)
    (e₁ : ∀ A : SL2 L, n * rootSL2 τ L r₁ A * n⁻¹ = rootSL2 τ L r₂ (conjSL M₁ A))
    (e₂ : ∀ B : SL2 L, n * rootSL2 τ L r₂ B * n⁻¹ = rootSL2 τ L r₃ (conjSL M₂ B))
    (e₃ : ∀ C : SL2 L, n * rootSL2 τ L r₃ C * n⁻¹ = rootSL2 τ L r₁ (conjSL M₃ C))
    {k : Type} [Field k] [Finite k] [Algebra k L] (hk4 : 4 ≤ Nat.card k) {Fr₃ : L →+* L}
    (hFr₃ : ∀ c, Fr₃ c = c ^ Nat.card k) (hFr3eq : Fr.comp (Fr.comp Fr) = Fr₃)
    (Pm : GL (Fin 2) L)
    (hPm : Pm * Matrix.GeneralLinearGroup.map Fr₃ Pm⁻¹ =
      M₃ * Matrix.GeneralLinearGroup.map Fr (M₂ * Matrix.GeneralLinearGroup.map Fr M₁)) :
    ∃ P : Subgroup (ModGL τ L),
      SigmaFactor n Fr (threeRootSet r₁ r₂ r₃) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan τ L (threeRootSet r₁ r₂ r₃) : Set (ModGL τ L))) := by
  classical
  obtain ⟨μ, hμ⟩ : ∃ μ : SL2 L × SL2 L × SL2 L →* ModGL τ L, ∀ A B C,
      μ (A, B, C) = rootSL2 τ L r₁ A * rootSL2 τ L r₂ B * rootSL2 τ L r₃ C :=
    ⟨(rootSL2 τ L r₁).noncommCoprod ((rootSL2 τ L r₂).noncommCoprod (rootSL2 τ L r₃) hc23)
      fun A BC => (hc12 A BC.1).mul_right (hc13 A BC.2), fun A B C => (mul_assoc _ _ _).symm⟩
  obtain ⟨S₃, hfin₃, hS₃, hq₃, hq₂, hq₁, hz₃, hz₂, hz₁⟩ :=
    three_A1_lang_data hFr M₁ M₂ M₃ hk4 hFr₃ hFr3eq Pm hPm
  exact three_A1_twisted_sigma_factor hc12 hc13 hc23 h₁ h₂ h₃ μ hμ Fr n (twHom Fr M₁)
    (twHom Fr M₂) (twHom Fr M₃) (three_A1_theta hc12 hc13 μ hμ Fr n M₁ M₂ M₃ e₁ e₂ e₃) _ _ S₃
    rfl rfl hS₃ hq₁ hq₂ hq₃ hz₁ hz₂ hz₃

end Generic

section Roots

theorem e7_a1_support_check : ∀ l ∈ Tag.E7.artifactRoots,
    l.getD 0 0 = 0 → l.getD 2 0 = 0 → l.getD 3 0 = 0 → l.getD 5 0 = 0 →
      l ∈ [List.ofFn (Pi.single (1 : Fin Tag.E7.rank) (1 : ℤ)),
        List.ofFn (-Pi.single (1 : Fin Tag.E7.rank) (1 : ℤ)),
        List.ofFn (Pi.single (4 : Fin Tag.E7.rank) (1 : ℤ)),
        List.ofFn (-Pi.single (4 : Fin Tag.E7.rank) (1 : ℤ)),
        List.ofFn (Pi.single (6 : Fin Tag.E7.rank) (1 : ℤ)),
        List.ofFn (-Pi.single (6 : Fin Tag.E7.rank) (1 : ℤ))] := by
  decide +kernel

theorem getD_ofFn_e7 (r : Fin Tag.E7.rank → ℤ) (i : Fin Tag.E7.rank) :
    (List.ofFn r).getD i.val 0 = r i := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_ofFn]
  simp

theorem parabolicRoots_a1Nodes_eq :
    parabolicRoots Tag.E7 (a1Nodes Tag.E7) =
      threeRootSet (Pi.single (1 : Fin Tag.E7.rank) 1) (Pi.single 4 1) (Pi.single 6 1) := by
  have hs : ∀ j : Fin Tag.E7.rank, j ∈ a1Nodes Tag.E7 →
      (Pi.single j 1 : Fin Tag.E7.rank → ℤ) ∈ parabolicRoots Tag.E7 (a1Nodes Tag.E7) ∧
        (-Pi.single j 1 : Fin Tag.E7.rank → ℤ) ∈ parabolicRoots Tag.E7 (a1Nodes Tag.E7) :=
    fun j hj => ⟨⟨isRoot_single _ _, fun i hi => Pi.single_eq_of_ne (fun h : i = j => hi (h ▸ hj)) 1⟩,
      ⟨IsRoot.neg (isRoot_single _ _), fun i hi => by
        rw [Pi.neg_apply, Pi.single_eq_of_ne (fun h : i = j => hi (h ▸ hj)) 1, neg_zero]⟩⟩
  have hmem : ∀ j : Fin Tag.E7.rank, j.val ∈ ({1, 4, 6} : Set ℕ) → j ∈ a1Nodes Tag.E7 :=
    fun _ hj => hj
  ext r
  constructor
  · rintro ⟨hr, hsupp⟩
    have hz : ∀ i : Fin Tag.E7.rank, i.val ∉ ({1, 4, 6} : Set ℕ) → r i = 0 := fun i hi =>
      hsupp i (fun h => hi h)
    have key := e7_a1_support_check (List.ofFn r) (isRoot_iff_mem_artifactRoots.1 hr)
      (by rw [show (0 : ℕ) = (0 : Fin Tag.E7.rank).val from rfl, getD_ofFn_e7]; exact hz 0 (by decide))
      (by rw [show (2 : ℕ) = (2 : Fin Tag.E7.rank).val from rfl, getD_ofFn_e7]; exact hz 2 (by decide))
      (by rw [show (3 : ℕ) = (3 : Fin Tag.E7.rank).val from rfl, getD_ofFn_e7]; exact hz 3 (by decide))
      (by rw [show (5 : ℕ) = (5 : Fin Tag.E7.rank).val from rfl, getD_ofFn_e7]; exact hz 5 (by decide))
    simp only [List.mem_cons, List.not_mem_nil, or_false] at key
    rcases key with h | h | h | h | h | h
    · exact Or.inl (List.ofFn_injective h)
    · exact Or.inr (Or.inl (List.ofFn_injective h))
    · exact Or.inr (Or.inr (Or.inl (List.ofFn_injective h)))
    · exact Or.inr (Or.inr (Or.inr (Or.inl (List.ofFn_injective h))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl (List.ofFn_injective h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (List.ofFn_injective h)))))
  · rintro (rfl | rfl | rfl | rfl | rfl | rfl)
    · exact (hs 1 (hmem 1 (by decide))).1
    · exact (hs 1 (hmem 1 (by decide))).2
    · exact (hs 4 (hmem 4 (by decide))).1
    · exact (hs 4 (hmem 4 (by decide))).2
    · exact (hs 6 (hmem 6 (by decide))).1
    · exact (hs 6 (hmem 6 (by decide))).2

theorem threeRootSet_swap₂₃ {τ : Tag} (r₁ r₂ r₃ : Fin τ.rank → ℤ) :
    threeRootSet r₁ r₂ r₃ = threeRootSet r₁ r₃ r₂ := by
  ext x
  simp only [threeRootSet, Set.mem_insert_iff, Set.mem_singleton_iff]
  tauto

theorem e7_a1_orth_check : ∀ a b : Fin Tag.E7.rank, a.val ∈ ([1, 4, 6] : List ℕ) →
    b.val ∈ ([1, 4, 6] : List ℕ) → a ≠ b →
      (Pi.single a 1 : Fin Tag.E7.rank → ℤ) ⬝ᵥ
        (Tag.E7.symmetrizedCartan *ᵥ (Pi.single b 1 : Fin Tag.E7.rank → ℤ)) = 0 := by
  decide +kernel

end Roots

section Conj

variable {L : Type} [Field L]

theorem e7_commute_of_orth {r r' : Fin Tag.E7.rank → ℤ} (hr : IsRoot Tag.E7 r)
    (hr' : IsRoot Tag.E7 r') (h : r ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ r') = 0) (A B : SL2 L) :
    Commute (rootSL2 Tag.E7 L r A) (rootSL2 Tag.E7 L r' B) := by
  have hτ : Tag.E7 = .D4 ∨ Tag.E7 = .E6 ∨ Tag.E7 = .E7 ∨ Tag.E7 = .E8 :=
    Or.inr (Or.inr (Or.inl rfl))
  have hS : ∀ s : Fin Tag.E7.rank → ℤ, IsRoot Tag.E7 s →
      ∀ α ∈ ({s, -s} : Set (Fin Tag.E7.rank → ℤ)), IsRoot Tag.E7 α := by
    intro s hs α hα
    rcases hα with rfl | rfl
    exacts [hs, IsRoot.neg hs]
  have hmem : ∀ s : Fin Tag.E7.rank → ℤ, IsRoot Tag.E7 s → ∀ A : SL2 L,
      rootSL2 Tag.E7 L s A ∈ rootSpan Tag.E7 L ({s, -s} : Set (Fin Tag.E7.rank → ℤ)) :=
    fun s hs A => rootRankOneGroup_le_rootSpan hs (by simp) (by simp) ⟨A, rfl⟩
  have horth : ∀ α ∈ ({r, -r} : Set (Fin Tag.E7.rank → ℤ)),
      ∀ β ∈ ({r', -r'} : Set (Fin Tag.E7.rank → ℤ)),
        α ⬝ᵥ (Tag.E7.symmetrizedCartan *ᵥ β) = 0 := by
    intro α hα β hβ
    rcases hα with rfl | rfl <;> rcases hβ with rfl | rfl <;>
      simp [Matrix.mulVec_neg, dotProduct_neg, neg_dotProduct, h]
  exact rootSpan_commute_of_orth hτ (hS r hr) (hS r' hr') horth _ (hmem r hr A) _ (hmem r' hr' B)

theorem exists_conj_rootSL2_eq_neg {τ : Tag} {n : ModGL τ L} (hn : n ∈ monomialSubgroup τ L)
    {β γ : Fin τ.rank → ℤ} (hβ : IsRoot τ β) (hγ : IsRoot τ γ)
    (hW : weylQuotientHom τ L ⟨n, hn⟩ • β = -γ) :
    ∃ s : Lˣ, ∀ A : SL2 L, n * rootSL2 τ L β A * n⁻¹ =
      rootSL2 τ L γ (conjSL (swapGL * diagUnitOne s) A) := by
  obtain ⟨s, hs⟩ := exists_conj_rootSL2_eq hn (mapsRootLines_weylQuotientHom ⟨n, hn⟩) hβ hW
  obtain ⟨a, ha⟩ := exists_rootSL2_neg_eq (L := L) hγ
  refine ⟨a * s, fun A => ?_⟩
  rw [hs A, ha, ← conjSL_mul, mul_assoc, diagUnitOne_mul]

theorem coe_antidiag_triple (a₁ a₂ a₃ : Lˣ) :
    ((((swapGL * diagUnitOne a₃ : GL (Fin 2) L) *
        ((swapGL * diagUnitOne a₂ : GL (Fin 2) L) * (swapGL * diagUnitOne a₁ : GL (Fin 2) L)) :
          GL (Fin 2) L)) : Matrix (Fin 2) (Fin 2) L) =
      !![0, (a₂ : L); ((a₃ * a₁ : Lˣ) : L), 0] := by
  rw [Units.val_mul, Units.val_mul (swapGL * diagUnitOne a₂), coe_swapGL_mul_diagUnitOne,
    coe_swapGL_mul_diagUnitOne, coe_swapGL_mul_diagUnitOne]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

end Conj

section Std

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem e7_a1_std_factor (hf : 1 ≤ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1) {n : ModGL Tag.E7 L}
    (hn : n ∈ monomialSubgroup Tag.E7 L) {a b c : Fin Tag.E7.rank}
    (ha : a.val ∈ ([1, 4, 6] : List ℕ)) (hb : b.val ∈ ([1, 4, 6] : List ℕ))
    (hc : c.val ∈ ([1, 4, 6] : List ℕ)) (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (h₁ : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • (Pi.single a 1 : Fin Tag.E7.rank → ℤ) =
      ε • Pi.single b 1)
    (h₂ : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • (Pi.single b 1 : Fin Tag.E7.rank → ℤ) =
      ε • Pi.single c 1)
    (h₃ : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • (Pi.single c 1 : Fin Tag.E7.rank → ℤ) =
      ε • Pi.single a 1) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      SigmaFactor n (iterateFrobenius L ℓ f)
        (threeRootSet (Pi.single a 1) (Pi.single b 1) (Pi.single c 1)) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E7 L
          (threeRootSet (Pi.single a 1) (Pi.single b 1) (Pi.single c 1)) : Set (ModGL Tag.E7 L))) := by
  classical
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFrbij : Function.Bijective Fr := iterateFrobenius_bijective
  have hr₁ : IsRoot Tag.E7 (Pi.single a 1) := isRoot_single _ _
  have hr₂ : IsRoot Tag.E7 (Pi.single b 1) := isRoot_single _ _
  have hr₃ : IsRoot Tag.E7 (Pi.single c 1) := isRoot_single _ _
  have hc12 := e7_commute_of_orth (L := L) hr₁ hr₂ (e7_a1_orth_check a b ha hb hab)
  have hc13 := e7_commute_of_orth (L := L) hr₁ hr₃
    (e7_a1_orth_check a c ha hc (fun h => hca h.symm))
  have hc23 := e7_commute_of_orth (L := L) hr₂ hr₃ (e7_a1_orth_check b c hb hc hbc)
  obtain ⟨k, _, _, _, Fr₃, hk4, hFr₃, hFr3eq⟩ := exists_frob_three (L := L) (ℓ := ℓ) (f := f) hf
  have hmw := mapsRootLines_weylQuotientHom (τ := .E7) (R := L) ⟨n, hn⟩
  rcases hε with rfl | rfl
  · obtain ⟨s₁, e₁⟩ := exists_conj_rootSL2_eq hn hmw hr₁ (γ := Pi.single b 1) (by rw [h₁, one_smul])
    obtain ⟨s₂, e₂⟩ := exists_conj_rootSL2_eq hn hmw hr₂ (γ := Pi.single c 1) (by rw [h₂, one_smul])
    obtain ⟨s₃, e₃⟩ := exists_conj_rootSL2_eq hn hmw hr₃ (γ := Pi.single a 1) (by rw [h₃, one_smul])
    obtain ⟨Pm, hPm⟩ := exists_twist_diag (K := k) Fr₃ hFr₃
      (s₃ * Units.map Fr.toMonoidHom (s₂ * Units.map Fr.toMonoidHom s₁))
    refine three_A1_cyclic_sigma_factor hc12 hc13 hc23 hr₁ hr₂ hr₃ hFrbij n _ _ _ e₁ e₂ e₃ hk4 hFr₃
      hFr3eq Pm ?_
    rw [hPm]
    simp only [glMap_diagUnitOne, diagUnitOne_mul]
  · have h₁' : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • (Pi.single a 1 : Fin Tag.E7.rank → ℤ) =
        -Pi.single b 1 := by rw [h₁, neg_one_smul]
    have h₂' : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • (Pi.single b 1 : Fin Tag.E7.rank → ℤ) =
        -Pi.single c 1 := by rw [h₂, neg_one_smul]
    have h₃' : weylQuotientHom Tag.E7 L ⟨n, hn⟩ • (Pi.single c 1 : Fin Tag.E7.rank → ℤ) =
        -Pi.single a 1 := by rw [h₃, neg_one_smul]
    obtain ⟨s₁, e₁⟩ := exists_conj_rootSL2_eq_neg hn hr₁ hr₂ h₁'
    obtain ⟨s₂, e₂⟩ := exists_conj_rootSL2_eq_neg hn hr₂ hr₃ h₂'
    obtain ⟨s₃, e₃⟩ := exists_conj_rootSL2_eq_neg hn hr₃ hr₁ h₃'
    obtain ⟨Pm, hPm⟩ := exists_twist_antidiag (K := k) Fr₃ hFr₃ (Units.map Fr.toMonoidHom s₂)
      (s₃ * Units.map Fr.toMonoidHom (Units.map Fr.toMonoidHom s₁)) _
      (coe_antidiag_triple (Units.map Fr.toMonoidHom (Units.map Fr.toMonoidHom s₁))
        (Units.map Fr.toMonoidHom s₂) s₃)
    refine three_A1_cyclic_sigma_factor hc12 hc13 hc23 hr₁ hr₂ hr₃ hFrbij n _ _ _ e₁ e₂ e₃ hk4 hFr₃
      hFr3eq Pm ?_
    rw [hPm]
    simp only [map_mul, glMap_swapGL, glMap_diagUnitOne]

end Std

section Transport

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem e7_a1_factor_of_cycle (hf : 1 ≤ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (v : WeylGroup Tag.E7) (n : ModGL Tag.E7 L) (hnm : n ∈ monomialSubgroup Tag.E7 L)
    {a b c : Fin Tag.E7.rank} (ha : a.val ∈ ([1, 4, 6] : List ℕ))
    (hb : b.val ∈ ([1, 4, 6] : List ℕ)) (hc : c.val ∈ ([1, 4, 6] : List ℕ))
    (hab : a ≠ b) (hbc : b ≠ c) (hca : c ≠ a)
    (hset : parabolicRoots Tag.E7 (a1Nodes Tag.E7) =
      threeRootSet (Pi.single a 1) (Pi.single b 1) (Pi.single c 1))
    (h₁ : (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) •
      (Pi.single a 1 : Fin Tag.E7.rank → ℤ) = ε • Pi.single b 1)
    (h₂ : (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) •
      (Pi.single b 1 : Fin Tag.E7.rank → ℤ) = ε • Pi.single c 1)
    (h₃ : (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) •
      (Pi.single c 1 : Fin Tag.E7.rank → ℤ) = ε • Pi.single a 1) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      SigmaFactor n (iterateFrobenius L ℓ f)
        ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a1Nodes Tag.E7)) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E7 L
          ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a1Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) := by
  classical
  set Fr : L →+* L := iterateFrobenius L ℓ f with hFrdef
  have hFrbij : Function.Bijective Fr := iterateFrobenius_bijective
  set Φ : ModGL Tag.E7 L →* ModGL Tag.E7 L := Units.map (entrywiseHom Fr) with hΦ
  set V : ModGL Tag.E7 L := canonicalRep (coxeterSystem Tag.E7) L v with hV
  have hVm : V ∈ monomialSubgroup Tag.E7 L := canonicalRep_mem_monomialSubgroup L v
  have hΦV : Φ V = V := by
    have h1 := entrywise_canonicalRep (RingEquiv.ofBijective Fr hFrbij) v
    have h2 : (RingEquiv.ofBijective Fr hFrbij).toRingHom = Fr := RingHom.ext fun _ => rfl
    rw [h2] at h1
    exact h1
  set n' : ModGL Tag.E7 L := V⁻¹ * n * V with hn'
  have hn'm : n' ∈ monomialSubgroup Tag.E7 L := mul_mem (mul_mem (inv_mem hVm) hnm) hVm
  have hπV : weylQuotientHom Tag.E7 L ⟨V, hVm⟩ = v :=
    weylQuotientHom_eq (mapsRootLines_canonicalRep v)
  have hπn' : weylQuotientHom Tag.E7 L ⟨n', hn'm⟩ =
      v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v := by
    have : (⟨n', hn'm⟩ : monomialSubgroup Tag.E7 L) = ⟨V, hVm⟩⁻¹ * ⟨n, hnm⟩ * ⟨V, hVm⟩ :=
      Subtype.ext rfl
    rw [this, map_mul, map_mul, map_inv, hπV]
  obtain ⟨P', hstd'⟩ := e7_a1_std_factor (L := L) (ℓ := ℓ) hf hε hn'm ha hb hc hab hbc hca
    (by rw [hπn']; exact h₁) (by rw [hπn']; exact h₂) (by rw [hπn']; exact h₃)
  have hroots : ∀ r ∈ parabolicRoots Tag.E7 (a1Nodes Tag.E7), IsRoot Tag.E7 r := fun r hr => hr.1
  have hstd : SigmaFactor n' Fr (parabolicRoots Tag.E7 (a1Nodes Tag.E7)) (fun _ : Unit => P')
      (Subgroup.normalizer
        (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a1Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) := by
    rw [hset]
    exact hstd'
  have htr := SigmaFactor.transport Fr hFrbij v n hroots hstd
  set c₀ : ModGL Tag.E7 L →* ModGL Tag.E7 L := (MulAut.conj V).toMonoidHom with hc₀
  have hcapp : ∀ x, c₀ x = V * x * V⁻¹ := fun x => by simp [hc₀, MulAut.conj_apply]
  have hcinj : Function.Injective c₀ := (MulAut.conj V).injective
  have hQmap : (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a1Nodes Tag.E7))).map c₀ =
      rootSpan Tag.E7 L ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a1Nodes Tag.E7)) :=
    map_conj_rootSpan v hroots
  have hRiff : ∀ x, x ∈ twistedFixedPoints n' Φ ↔ c₀ x ∈ twistedFixedPoints n Φ := fun x => by
    rw [hcapp]
    exact mem_twistedFixedPoints_conj hΦV
  refine ⟨P'.map c₀, htr.finite, htr.quasi, htr.le_root, htr.le_fix, htr.le_adj,
    fun _ y hy hyR u hu => ?_, htr.thetaFree⟩
  obtain ⟨u', hu', rfl⟩ := hu
  have hw : V⁻¹ * y * V ∈ Subgroup.normalizer
      (rootSpan Tag.E7 L (parabolicRoots Tag.E7 (a1Nodes Tag.E7)) : Set (ModGL Tag.E7 L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro h
    have h1 := Subgroup.mem_normalizer_iff.1 hy (c₀ h)
    rw [← hQmap] at h1
    have e2 : y * c₀ h * y⁻¹ = c₀ (V⁻¹ * y * V * h * (V⁻¹ * y * V)⁻¹) := by
      rw [hcapp, hcapp]
      group
    rw [e2, Subgroup.mem_map_iff_mem hcinj, Subgroup.mem_map_iff_mem hcinj] at h1
    exact h1
  have hwR : V⁻¹ * y * V ∈ twistedFixedPoints n' Φ := by
    rw [hRiff, hcapp]
    have e : V * (V⁻¹ * y * V) * V⁻¹ = y := by group
    rw [e]
    exact hyR
  have h3 := hstd.norm () (V⁻¹ * y * V) hw hwR u' hu'
  refine ⟨V⁻¹ * y * V * u' * (V⁻¹ * y * V)⁻¹, h3, ?_⟩
  simp only [hcapp]
  group

end Transport

section Final

variable {L : Type} [Field L] [IsAlgClosed L] {ℓ f : ℕ} [Fact ℓ.Prime] [CharP L ℓ]

theorem e7_a1_factor (hf : 1 ≤ f) {ε : ℤ} (hε : ε = 1 ∨ ε = -1)
    (v : WeylGroup Tag.E7) (n : ModGL Tag.E7 L) (hnm : n ∈ monomialSubgroup Tag.E7 L)
    (rot : Bool)
    (hcert : ∀ α ∈ parabolicRoots Tag.E7 (a1Nodes Tag.E7),
      (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) • α =
        ε • permLattice (if rot then List.formPerm [(1 : Fin Tag.E7.rank), 6, 4]
          else List.formPerm [(1 : Fin Tag.E7.rank), 4, 6]) α) :
    ∃ P : Subgroup (ModGL Tag.E7 L),
      SigmaFactor n (iterateFrobenius L ℓ f)
        ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a1Nodes Tag.E7)) (fun _ : Unit => P)
        (Subgroup.normalizer (rootSpan Tag.E7 L
          ((fun γ => v • γ) '' parabolicRoots Tag.E7 (a1Nodes Tag.E7)) : Set (ModGL Tag.E7 L))) := by
  have hset := parabolicRoots_a1Nodes_eq
  have hmem : ∀ x : Fin Tag.E7.rank → ℤ, x ∈ threeRootSet (Pi.single (1 : Fin Tag.E7.rank) 1)
      (Pi.single 4 1) (Pi.single 6 1) → x ∈ parabolicRoots Tag.E7 (a1Nodes Tag.E7) :=
    fun x hx => hset ▸ hx
  have m1 := hmem (Pi.single 1 1) (by simp [threeRootSet])
  have m4 := hmem (Pi.single 4 1) (by simp [threeRootSet])
  have m6 := hmem (Pi.single 6 1) (by simp [threeRootSet])
  cases rot
  · change ∀ α ∈ parabolicRoots Tag.E7 (a1Nodes Tag.E7),
      (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) • α =
        ε • permLattice (List.formPerm [(1 : Fin Tag.E7.rank), 4, 6]) α at hcert
    refine e7_a1_factor_of_cycle (a := 1) (b := 4) (c := 6) hf hε v n hnm (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) hset ?_ ?_ ?_
    · rw [hcert _ m1, permLattice_single, show (List.formPerm [(1 : Fin Tag.E7.rank), 4, 6]) 1 = 4
        from by decide]
    · rw [hcert _ m4, permLattice_single, show (List.formPerm [(1 : Fin Tag.E7.rank), 4, 6]) 4 = 6
        from by decide]
    · rw [hcert _ m6, permLattice_single, show (List.formPerm [(1 : Fin Tag.E7.rank), 4, 6]) 6 = 1
        from by decide]
  · change ∀ α ∈ parabolicRoots Tag.E7 (a1Nodes Tag.E7),
      (v⁻¹ * weylQuotientHom Tag.E7 L ⟨n, hnm⟩ * v) • α =
        ε • permLattice (List.formPerm [(1 : Fin Tag.E7.rank), 6, 4]) α at hcert
    refine e7_a1_factor_of_cycle (a := 1) (b := 6) (c := 4) hf hε v n hnm (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)
      (by rw [hset, threeRootSet_swap₂₃]) ?_ ?_ ?_
    · rw [hcert _ m1, permLattice_single, show (List.formPerm [(1 : Fin Tag.E7.rank), 6, 4]) 1 = 6
        from by decide]
    · rw [hcert _ m6, permLattice_single, show (List.formPerm [(1 : Fin Tag.E7.rank), 6, 4]) 6 = 4
        from by decide]
    · rw [hcert _ m4, permLattice_single, show (List.formPerm [(1 : Fin Tag.E7.rank), 6, 4]) 4 = 1
        from by decide]

end Final

end CFSG.RankThree.PartOne.KE

module

public import CFSG.Quasithin.Vol2.Ch12Sec8OneStatements
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilySmallLieModel

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Blueprint

variable {G : Type} [Group G]

abbrev l32nH (T V : Subgroup G) : Subgroup G :=
  Subgroup.normalizer (fsuV1 T V : Set G)

abbrev l32nCHat (T V : Subgroup G) : Subgroup G :=
  centralizerMod (centerOf (fsuU T V)) (l32nH T V) (fsuU T V)

@[expose] def IsL32NPlane (T V V₂ : Subgroup G) : Prop :=
  IsTSub T V V₂ 2 ∧ fsuV1 T V ≤ V₂

@[expose] def IsIndecOnSection (K U D : Subgroup G) : Prop :=
  ∀ A B : Subgroup G, D ≤ A → D ≤ B → A ≤ U → B ≤ U →
    K ≤ Subgroup.normalizer (A : Set G) → K ≤ Subgroup.normalizer (B : Set G) →
    A ⊓ B = D → A ⊔ B = U → A = D ∨ B = D

@[expose] def IsQ8CentralPow (k : ℕ) (P : Type*) [Group P] : Prop :=
  Nat.card P = 2 ^ (2 * k + 1) ∧ ∃ Q : Fin k → Subgroup P,
    (∀ i j, i ≠ j → Q i ≤ Subgroup.centralizer (Q j : Set P)) ∧ (⨆ i, Q i) = ⊤ ∧
    ∀ i, Nonempty (↥(Q i) ≃* QuaternionGroup 2)

theorem l32n_card_centerOf (R : Subgroup G) :
    Nat.card ↥(centerOf R) = Nat.card ↥(Subgroup.center ↥R) := by
  have h : (Subgroup.center ↥R).map R.subtype = centerOf R := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact Subgroup.mem_inf.mpr ⟨y.2, Subgroup.mem_centralizer_iff.mpr fun g hg =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hy ⟨g, hg⟩)⟩
    · intro hx
      exact ⟨⟨x, hx.1⟩, Subgroup.mem_center_iff.mpr fun g =>
        Subtype.ext (Subgroup.mem_centralizer_iff.mp hx.2 g g.2), rfl⟩
  rw [← h]
  exact Nat.card_congr ((Subgroup.center ↥R).equivMapOfInjective _ R.subtype_injective).symm

theorem normalizer_eq_centralizer_of_card_two {A : Subgroup G} (hA : Nat.card A = 2) {z : G}
    (hzA : z ∈ A) (hz : z ≠ 1) :
    Subgroup.normalizer (A : Set G) = Subgroup.centralizer ({z} : Set G) := by
  have hmem : ∀ a ∈ A, a = 1 ∨ a = z := by
    intro a ha
    obtain ⟨y, -, huniq⟩ := (Nat.card_eq_two_iff' (1 : A)).mp hA
    by_cases ha1 : a = 1
    · exact Or.inl ha1
    · right
      have h1 := huniq ⟨a, ha⟩ (fun h => ha1 (congrArg Subtype.val h))
      have h2 := huniq ⟨z, hzA⟩ (fun h => hz (congrArg Subtype.val h))
      exact congrArg Subtype.val (h1.trans h2.symm)
  apply le_antisymm
  · intro g hg
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    rw [Set.mem_singleton_iff] at hx
    subst hx
    have hgx : g * x * g⁻¹ ∈ A := (Subgroup.mem_normalizer_iff.mp hg x).mp hzA
    rcases hmem _ hgx with h1 | h1
    · exfalso
      apply hz
      calc x = g⁻¹ * (g * x * g⁻¹) * g := by group
        _ = 1 := by rw [h1]; group
    · calc x * g = (g * x * g⁻¹) * g := by rw [h1]
        _ = g * x := by group
  · intro g hg
    rw [Subgroup.mem_normalizer_iff]
    have hgz : g * z = z * g := (Subgroup.mem_centralizer_iff.mp hg z rfl).symm
    have hconj : ∀ a ∈ A, g * a * g⁻¹ = a := by
      intro a ha
      rcases hmem a ha with rfl | rfl
      · group
      · rw [hgz, mul_inv_cancel_right]
    intro a
    constructor
    · intro ha
      rw [hconj a ha]
      exact ha
    · intro ha
      rcases hmem _ ha with h1 | h1
      · have ha1 : a = 1 := by
          calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
            _ = 1 := by rw [h1]; group
        rw [ha1]
        exact A.one_mem
      · have haz : a = z := by
          calc a = g⁻¹ * (g * a * g⁻¹) * g := by group
            _ = g⁻¹ * (g * z * g⁻¹) * g := by rw [h1, hgz, mul_inv_cancel_right]
            _ = z := by group
        rw [haz]
        exact hzA

theorem nonempty_equiv_SL32_of_lieModel {X : Type} [Group X] (h : LieModel X .PSL 3 2 1) :
    Nonempty (X ≃* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)) :=
  CFSG.Blueprint.LieModel.nonempty_mulEquiv_SL_three_two h

theorem pCoreOf_subgroupOf_self (L : Subgroup G) :
    (pCoreOf 2 L).subgroupOf L = CFSG.Open.pCore 2 ↥L :=
  Subgroup.comap_map_eq_self_of_injective L.subtype_injective _

theorem exists_surj_SL32_of_lieModel {L : Subgroup G}
    (h : LieModel (↥L ⧸ CFSG.pCore 2 ↥L) .PSL 3 2 1) :
    ∃ θ : ↥L →* Matrix.SpecialLinearGroup (Fin 3) (ZMod 2), Function.Surjective θ ∧
      θ.ker = (pCoreOf 2 L).subgroupOf L := by
  obtain ⟨e⟩ := nonempty_equiv_SL32_of_lieModel h
  refine ⟨e.toMonoidHom.comp (QuotientGroup.mk' (CFSG.pCore 2 ↥L)),
    e.surjective.comp (QuotientGroup.mk'_surjective _), ?_⟩
  rw [pCoreOf_subgroupOf_self]
  ext x
  rw [MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
    MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]

end CFSG.Quasithin.H13

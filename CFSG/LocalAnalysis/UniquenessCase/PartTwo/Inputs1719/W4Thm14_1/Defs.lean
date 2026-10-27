module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF2RepsC
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps128Sum
public import CFSG.Quasithin.Background.HL42Aut
public import CFSG.LocalAnalysis.UniquenessCase.UC6R77E3
public import CFSG.Quasithin.Background.F918J3
public import CFSG.Quasithin.Background.Asc81cPfTrans1
public import CFSG.Quasithin.Background.SmithB57C
public import CFSG.Quasithin.Background.RonanH163Tiso

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Quasithin CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.Quasithin.F6
open CFSG.LocalAnalysis.WeakClosure81

open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

@[expose] def W4Thm14_1Used : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L H M : Subgroup (MulAut W),
      IsKGroup ↥Y → O2Trivial Y → IsBasicModule Y →
      IsComponentOf L Y → IsL3 ↥L 1 →
      H = ⨆ g ∈ Y, L.map (MulAut.conj g).toMonoidHom →
      fixV H = ⊥ → normIn Y L = L ⊔ M → M = centGroupIn Y L → E3.mParam Y = 4 →
      (∀ g : MulAut W, g ∈ Y → g ∉ normIn Y L →
          commSub (commSub (⊤ : Subgroup W) L) (L.map (MulAut.conj g).toMonoidHom) = ⊥) ∧
        (commSub (⊤ : Subgroup W) L = ⊤ →
          IsSubgroupOfAlt ↥M 8 ∧
            (7 ∣ Nat.card M → (IsAlt ↥M 7 ∨ IsAlt ↥M 8 ∨ IsL3 ↥M 1)) ∧
            (IsL3 ↥M 1 → fixV M ≠ ⊥))

@[expose] def KL32PairRank : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ (H X X' : Subgroup (MulAut W)) (I : Subgroup W),
      IsIrrOn H I ⊥ → X ≤ H → X' ≤ H →
      (∀ h ∈ H, ∀ x ∈ X, h * x * h⁻¹ ∈ X) → (∀ h ∈ H, ∀ x ∈ X', h * x * h⁻¹ ∈ X') →
      (∀ x ∈ X, ∀ x' ∈ X', x * x' = x' * x) → IsL3 ↥X 1 → IsL3 ↥X' 1 →
      commSub I X ≠ ⊥ → commSub I X' ≠ ⊥ →
      9 ≤ rk ↥I ∧
        (rk ↥I ≤ 16 → ∀ s ∈ X, orderOf s = 2 → rk ↥(commSub I (Subgroup.zpowers s)) = 3)

@[expose] def KInvolGen : Prop :=
  ∀ (G : Type) [Group G] (X : Subgroup G) (t : G), (IsL3 ↥X 1 ∨ IsAlt ↥X 5) → t ^ 2 = 1 →
    (∀ x ∈ X, t * x * t⁻¹ ∈ X) → (∃ x ∈ X, t * x ≠ x * t) →
    ∃ y₁ ∈ X, ∃ y₂ ∈ X, ∃ y₃ ∈ X,
      X ≤ Subgroup.closure {t, y₁ * t * y₁⁻¹, y₂ * t * y₂⁻¹, y₃ * t * y₃⁻¹}

@[expose] def KSimpleGen2 : Prop :=
  ∀ (G : Type) [Group G] (X : Subgroup G), (IsL3 ↥X 1 ∨ IsAlt ↥X 5) →
    ∃ y₁ ∈ X, ∃ y₂ ∈ X, Subgroup.closure {y₁, y₂} = X ∧ y₁ * y₂ ≠ y₂ * y₁

@[expose] def K141MultSpace : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ Y L M : Subgroup (MulAut W),
      IsL3 ↥L 1 → L ≤ Y → M = centGroupIn Y L → Y = L ⊔ M → fixV L = ⊥ →
      IrrSpanTrans Y L → IsBasicModule Y → E3.mParam Y = 4 →
      M = ⊥ ∨ ∃ U : Subgroup W, Nat.card ↥U = 16 ∧ M ≤ stabSub U ∧ M ⊓ centSub U = ⊥ ∧
        IsBasicModule (autSub M U)

@[expose] def KGL42Seven : Prop :=
  ∀ (U : Type) [CommGroup U] [Finite U], (∀ u : U, u ^ 2 = 1) → Nat.card U = 16 →
    ∀ M : Subgroup (MulAut U), O2Trivial M → IsBasicModule M → 7 ∣ Nat.card ↥M →
      IsAlt ↥M 7 ∨ IsAlt ↥M 8 ∨ (IsL3 ↥M 1 ∧ fixV M ≠ ⊥)

theorem isSubgroupOfAlt_eight_of_card {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) (U : Subgroup W) (hU : Nat.card ↥U = 16)
    (M : Subgroup (MulAut ↥U)) : IsSubgroupOfAlt ↥M 8 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hE : CFSG.Open.IsElemAbelian 2 U := ⟨inferInstance, fun x _ => hW x⟩
  obtain ⟨e⟩ := CFSG.LocalAnalysis.UniquenessCase.UC6R77.nonempty_mulAut_mulEquiv_GL_pow hE
    (n := 4) (by rw [hU]; norm_num)
  let f : ↥M →* ↥(alternatingGroup (Fin 8)) :=
    (CFSG.Quasithin.H.L4.alpha8.symm.toMonoidHom.comp e.toMonoidHom).comp M.subtype
  have hf : Function.Injective f := by
    intro a b hab
    apply Subtype.ext
    apply e.injective
    apply CFSG.Quasithin.H.L4.alpha8.symm.injective
    exact hab
  exact ⟨f.range, ⟨MonoidHom.ofInjective hf⟩⟩

theorem isSubgroupOfAlt_eight_of_faithful {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {M : Subgroup (MulAut W)} {U : Subgroup W}
    (hU : Nat.card ↥U = 16) (hMU : M ≤ stabSub U) (hfaith : M ⊓ centSub U = ⊥) :
    IsSubgroupOfAlt ↥M 8 := by
  obtain ⟨A, ⟨e⟩⟩ := isSubgroupOfAlt_eight_of_card hW U hU (autSub M U)
  exact ⟨A, ⟨(autSubEquivOfFaithful hMU hfaith).trans e⟩⟩

theorem rk_commSub_le_of_le_closure {W : Type} [CommGroup W] [Finite W]
    {X : Subgroup (MulAut W)} {t g₁ g₂ g₃ : MulAut W}
    (hX : X ≤ Subgroup.closure {t, g₁ * t * g₁⁻¹, g₂ * t * g₂⁻¹, g₃ * t * g₃⁻¹}) :
    rk ↥(commSub (⊤ : Subgroup W) X) ≤ 4 * rk ↥(commV (Subgroup.zpowers t)) := by
  have hconj : ∀ g : MulAut W, Subgroup.zpowers (g * t * g⁻¹) =
      (Subgroup.zpowers t).map (MulAut.conj g).toMonoidHom := by
    intro g
    rw [MonoidHom.map_zpowers]
    simp [MulAut.conj_apply]
  have hrk : ∀ g : MulAut W,
      rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers (g * t * g⁻¹))) =
      rk ↥(commV (Subgroup.zpowers t)) := by
    intro g
    rw [hconj g, Asc81c.commSub_map_conj, commV_eq_commSub]
    exact RonanH163.rk_map g _
  have hcl : Subgroup.closure
      ({t, g₁ * t * g₁⁻¹, g₂ * t * g₂⁻¹, g₃ * t * g₃⁻¹} : Set (MulAut W)) =
      Subgroup.zpowers t ⊔ (Subgroup.zpowers (g₁ * t * g₁⁻¹) ⊔
        (Subgroup.zpowers (g₂ * t * g₂⁻¹) ⊔ Subgroup.zpowers (g₃ * t * g₃⁻¹))) := by
    simp only [Set.insert_eq, Subgroup.closure_union, ← Subgroup.zpowers_eq_closure]
  have h1 := rk_mono (commSub_mono (le_refl (⊤ : Subgroup W)) hX)
  rw [hcl, Asc81c.Pf.commSub_sup, Asc81c.Pf.commSub_sup, Asc81c.Pf.commSub_sup] at h1
  have e1 := SmithB57.rk_sup_le (commSub (⊤ : Subgroup W) (Subgroup.zpowers t))
    (commSub (⊤ : Subgroup W) (Subgroup.zpowers (g₁ * t * g₁⁻¹)) ⊔
      (commSub (⊤ : Subgroup W) (Subgroup.zpowers (g₂ * t * g₂⁻¹)) ⊔
        commSub (⊤ : Subgroup W) (Subgroup.zpowers (g₃ * t * g₃⁻¹))))
  have e2 := SmithB57.rk_sup_le (commSub (⊤ : Subgroup W) (Subgroup.zpowers (g₁ * t * g₁⁻¹)))
    (commSub (⊤ : Subgroup W) (Subgroup.zpowers (g₂ * t * g₂⁻¹)) ⊔
      commSub (⊤ : Subgroup W) (Subgroup.zpowers (g₃ * t * g₃⁻¹)))
  have e3 := SmithB57.rk_sup_le (commSub (⊤ : Subgroup W) (Subgroup.zpowers (g₂ * t * g₂⁻¹)))
    (commSub (⊤ : Subgroup W) (Subgroup.zpowers (g₃ * t * g₃⁻¹)))
  have e0 : rk ↥(commSub (⊤ : Subgroup W) (Subgroup.zpowers t)) =
      rk ↥(commV (Subgroup.zpowers t)) := by rw [commV_eq_commSub]
  rw [hrk g₁] at e2
  rw [hrk g₂, hrk g₃] at e3
  rw [e0] at e1
  omega

theorem commSub_commSub_eq_bot_of_unique {W : Type} [CommGroup W] [Finite W]
    (hW : ∀ w : W, w ^ 2 = 1) {Y L H : Subgroup (MulAut W)}
    (hO : O2Trivial Y) (hB : IsBasicModule Y) (hL : IsComponentOf L Y)
    (hH : H = ⨆ X ∈ conjSet L Y, X) (hfix : fixV H = ⊥)
    (huniq : ∀ I ∈ irrSet H, ∀ X ∈ conjSet L Y, ∀ X' ∈ conjSet L Y,
      ¬ commSub I X ≤ fixV H → ¬ commSub I X' ≤ fixV H → X = X')
    {X X' : Subgroup (MulAut W)} (hX : X ∈ conjSet L Y) (hX' : X' ∈ conjSet L Y)
    (hne : X ≠ X') :
    commSub (commSub (⊤ : Subgroup W) X) X' = ⊥ := by
  have h := commV_le_trivMod hW hO hB hL hH huniq hX hX' hne
  rw [commSub_eq_bot_iff]
  intro w hw x hx
  have hw' : w ∈ commV X := by rwa [commV_eq_commSub]
  have h1 := (mem_trivMod.mp (h hw')) x hx
  rw [hfix, Subgroup.mem_bot, mul_inv_eq_one] at h1
  exact h1

theorem sup_map_conj_le_closure {G : Type} [Group G] {X : Subgroup G}
    (hX : IsSimpleGroup ↥X)
    {t y₁ y₂ : G} (hy₁ : y₁ ∈ X) (hy₂ : y₂ ∈ X) (hgen : Subgroup.closure {y₁, y₂} = X)
    (hnc : y₁ * y₂ ≠ y₂ * y₁)
    (hcomm : ∀ x ∈ X, ∀ x' ∈ X.map (MulAut.conj t).toMonoidHom, x * x' = x' * x) :
    X ⊔ X.map (MulAut.conj t).toMonoidHom ≤
      Subgroup.closure {t, y₁ * t * y₁⁻¹, y₂ * t * y₂⁻¹, (y₁ * y₂) * t * (y₁ * y₂)⁻¹} := by
  obtain ⟨D, hD⟩ : ∃ D : Subgroup G, D = Subgroup.closure
      ({t, y₁ * t * y₁⁻¹, y₂ * t * y₂⁻¹, (y₁ * y₂) * t * (y₁ * y₂)⁻¹} : Set G) := ⟨_, rfl⟩
  rw [← hD]
  have hsub : ∀ x ∈ ({t, y₁ * t * y₁⁻¹, y₂ * t * y₂⁻¹, (y₁ * y₂) * t * (y₁ * y₂)⁻¹} : Set G),
      x ∈ D := by
    intro x hx
    rw [hD]
    exact Subgroup.subset_closure hx
  have htD : t ∈ D := hsub _ (by simp)
  have hc1 : y₁ * t * y₁⁻¹ * t⁻¹ ∈ D := D.mul_mem (hsub _ (by simp)) (D.inv_mem htD)
  have hc2 : y₂ * t * y₂⁻¹ * t⁻¹ ∈ D := D.mul_mem (hsub _ (by simp)) (D.inv_mem htD)
  have hc12 : (y₁ * y₂) * t * (y₁ * y₂)⁻¹ * t⁻¹ ∈ D :=
    D.mul_mem (hsub _ (by simp)) (D.inv_mem htD)
  have hc : ∀ x ∈ X, ∀ z ∈ X, x * (t * z * t⁻¹) = t * z * t⁻¹ * x := fun x hx z hz =>
    hcomm x hx _ (Subgroup.mem_map.mpr ⟨z, hz, by simp [MulAut.conj_apply]⟩)
  have hcl : ∀ x ∈ X, ∀ z ∈ X, x⁻¹ * (t * z * t⁻¹) * x = t * z * t⁻¹ := by
    intro x hx z hz
    calc x⁻¹ * (t * z * t⁻¹) * x = x⁻¹ * (t * z * t⁻¹ * x) := mul_assoc _ _ _
      _ = x⁻¹ * (x * (t * z * t⁻¹)) := by rw [hc x hx z hz]
      _ = t * z * t⁻¹ := inv_mul_cancel_left x _
  have hcr : ∀ x ∈ X, ∀ z ∈ X, x * (t * z * t⁻¹) * x⁻¹ = t * z * t⁻¹ := by
    intro x hx z hz
    calc x * (t * z * t⁻¹) * x⁻¹ = t * z * t⁻¹ * x * x⁻¹ := by rw [hc x hx z hz]
      _ = t * z * t⁻¹ := mul_inv_cancel_right _ x
  obtain ⟨K, hK⟩ : ∃ K : Subgroup G, ∀ h, h ∈ K ↔ h ∈ X ∧ t * h * t⁻¹ ∈ D :=
    ⟨X ⊓ D.comap (MulAut.conj t).toMonoidHom, fun h => by simp [MulAut.conj_apply]⟩
  have hKX : K ≤ X := fun h hh => ((hK h).mp hh).1
  have hnorm : ∀ y ∈ X, y * t * y⁻¹ * t⁻¹ ∈ D → y ∈ Subgroup.normalizer (K : Set G) := by
    intro y hy hcy
    rw [Subgroup.mem_normalizer_iff]
    intro h
    constructor
    · intro hh
      obtain ⟨hhX, hhD⟩ := (hK h).mp hh
      refine (hK _).mpr ⟨X.mul_mem (X.mul_mem hy hhX) (X.inv_mem hy), ?_⟩
      have e : t * (y * h * y⁻¹) * t⁻¹ =
          (y * t * y⁻¹ * t⁻¹)⁻¹ * (t * h * t⁻¹) * (y * t * y⁻¹ * t⁻¹) := by
        calc t * (y * h * y⁻¹) * t⁻¹
            = (t * y * t⁻¹) * (t * h * t⁻¹) * (t * y * t⁻¹)⁻¹ := by group
          _ = (t * y * t⁻¹) * (y⁻¹ * (t * h * t⁻¹) * y) * (t * y * t⁻¹)⁻¹ := by
              rw [hcl y hy h hhX]
          _ = (y * t * y⁻¹ * t⁻¹)⁻¹ * (t * h * t⁻¹) * (y * t * y⁻¹ * t⁻¹) := by group
      rw [e]
      exact D.mul_mem (D.mul_mem (D.inv_mem hcy) hhD) hcy
    · intro hh
      obtain ⟨hhX, hhD⟩ := (hK _).mp hh
      have hX' : h ∈ X := by
        have e : h = y⁻¹ * (y * h * y⁻¹) * y := by group
        rw [e]
        exact X.mul_mem (X.mul_mem (X.inv_mem hy) hhX) hy
      refine (hK h).mpr ⟨hX', ?_⟩
      have e : t * h * t⁻¹ =
          (y * t * y⁻¹ * t⁻¹) * (t * (y * h * y⁻¹) * t⁻¹) * (y * t * y⁻¹ * t⁻¹)⁻¹ := by
        calc t * h * t⁻¹ = y * (t * h * t⁻¹) * y⁻¹ := (hcr y hy h hX').symm
          _ = (y * t * y⁻¹ * t⁻¹) * (t * (y * h * y⁻¹) * t⁻¹) * (y * t * y⁻¹ * t⁻¹)⁻¹ := by
              group
      rw [e]
      exact D.mul_mem (D.mul_mem hcy hhD) (D.inv_mem hcy)
  have hXN : X ≤ Subgroup.normalizer (K : Set G) := by
    refine hgen.symm.le.trans ((Subgroup.closure_le _).mpr ?_)
    intro y hy
    rcases hy with rfl | rfl
    · exact hnorm _ hy₁ hc1
    · exact hnorm _ hy₂ hc2
  haveI hn : (K.subgroupOf X).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKX).mpr hXN
  have hcX : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ X :=
    X.mul_mem (X.mul_mem (X.mul_mem hy₁ hy₂) (X.inv_mem hy₁)) (X.inv_mem hy₂)
  have hcommK : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ ∈ K := by
    refine (hK _).mpr ⟨hcX, ?_⟩
    have e : t * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * t⁻¹ =
        ((y₁ * y₂) * t * (y₁ * y₂)⁻¹ * t⁻¹)⁻¹ * (y₁ * t * y₁⁻¹ * t⁻¹) *
          (y₂ * t * y₂⁻¹ * t⁻¹) := by
      calc t * (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * t⁻¹
          = (t * (y₁ * y₂) * t⁻¹) * (t * y₁⁻¹ * t⁻¹) * (t * y₂⁻¹ * t⁻¹) := by group
        _ = (t * (y₁ * y₂) * t⁻¹) * (y₂⁻¹ * (t * y₁⁻¹ * t⁻¹) * y₂) * (t * y₂⁻¹ * t⁻¹) := by
            rw [hcl y₂ hy₂ y₁⁻¹ (X.inv_mem hy₁)]
        _ = ((y₁ * y₂) * t * (y₁ * y₂)⁻¹ * t⁻¹)⁻¹ * (y₁ * t * y₁⁻¹ * t⁻¹) *
              (y₂ * t * y₂⁻¹ * t⁻¹) := by group
    rw [e]
    exact D.mul_mem (D.mul_mem (D.inv_mem hc12) hc1) hc2
  haveI := hX
  have hXK : X ≤ K := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (K.subgroupOf X) with h | h
    · exfalso
      rw [Subgroup.subgroupOf_eq_bot] at h
      have h1 : y₁ * y₂ * y₁⁻¹ * y₂⁻¹ = 1 := Subgroup.disjoint_def.mp h hcommK hcX
      apply hnc
      calc y₁ * y₂ = (y₁ * y₂ * y₁⁻¹ * y₂⁻¹) * (y₂ * y₁) := by group
        _ = y₂ * y₁ := by rw [h1, one_mul]
    · exact Subgroup.subgroupOf_eq_top.mp h
  have hX'D : X.map (MulAut.conj t).toMonoidHom ≤ D := by
    rw [Subgroup.map_le_iff_le_comap]
    intro x hx
    simpa [MulAut.conj_apply] using ((hK x).mp (hXK hx)).2
  have key : ∀ y ∈ X, y * t * y⁻¹ * t⁻¹ ∈ D → y ∈ D := by
    intro y hy hcy
    have e : y = (y * t * y⁻¹ * t⁻¹) * (t * y * t⁻¹) := by group
    rw [e]
    exact D.mul_mem hcy ((hK y).mp (hXK hy)).2
  have hXD : X ≤ D := by
    refine hgen.symm.le.trans ((Subgroup.closure_le _).mpr ?_)
    intro y hy
    rcases hy with rfl | rfl
    · exact key _ hy₁ hc1
    · exact key _ hy₂ hc2
  exact sup_le hXD hX'D

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

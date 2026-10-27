module

public import CFSG.Quasithin.Vol2.Ch1Sec3Basic
public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3323C45

public section

namespace CFSG.Quasithin.H13.MSY

open CFSG.Open (pCoreOf quasithinOmegaOneCenter)
open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {T Y : Subgroup G}

omit [Finite G] in
theorem c134Q_le_pCoreOf : c134Q (Y ⊔ T) Y ≤ pCoreOf 2 (Y ⊔ T) :=
  Ch1Sec3.commutator_le_left_of_le_normalizer fun _ hx =>
    CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ T) (Subgroup.mem_sup_left hx)

omit [Finite G] in
theorem le_normalizer_c134Q (hTY : T ≤ Subgroup.normalizer (Y : Set G)) :
    Y ⊔ T ≤ Subgroup.normalizer (c134Q (Y ⊔ T) Y : Set G) := fun _ hx =>
  Ch1Sec3.commutator_le_normalizer (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 (Y ⊔ T) hx)
    (sup_le Subgroup.le_normalizer hTY hx)

omit [Finite G] in
theorem le_centralizer_of_case5 (h5 : IsC134Case5 (Y ⊔ T) T Y) (hT : IsSylowTwoOf T (Y ⊔ T)) :
    Y ≤ Subgroup.centralizer (quasithinOmegaOneCenter T : Set G) := by
  have h := (h5.2 T hT le_rfl).1
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  have hz' := (h (by rw [omegaOneCenterOf_eq]; exact hz)).2
  exact (Subgroup.mem_centralizer_iff.mp hz' y (Subgroup.mem_sup_left hy)).symm

theorem card_le_two (hT : IsSylowTwoOf T (Y ⊔ T)) (hTY : T ≤ Subgroup.normalizer (Y : Set G))
    {F : Type} [Field F] [Fintype F] (hF : Fintype.card F = 2)
    {α : ↥Y →* ↥(StatedSL 3 F)} (hα : IsModO2Surj Y α)
    {U : Subgroup G} (β : ↥U →* Multiplicative (Fin 1 → Fin 3 → F))
    (hβi : Function.Injective β)
    (hβe : ∀ (a : ↥Y) (u v : ↥U), (v : G) = a * u * a⁻¹ → ∀ i : Fin 1,
      Multiplicative.toAdd (β v) i =
        ((α a : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F).mulVec (Multiplicative.toAdd (β u) i))
    {X : Subgroup G} (hXU : X ≤ U) (hXC : X ≤ Subgroup.centralizer (T : Set G)) :
    Nat.card X ≤ 2 := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let e := (specialLinearGroupEquivStatedSL 3 F).symm
  let f : ↥Y →* L3.Γ := (Mod3323.toL3 hF).comp (e.toMonoidHom.comp α)
  have hf : Function.Surjective f := by
    intro γ
    let γ' : Matrix.SpecialLinearGroup (Fin 3) F :=
      Matrix.SpecialLinearGroup.map (Mod3323.toZ2 hF).symm.toRingHom γ
    obtain ⟨l, hl⟩ := hα.1 (e.symm γ')
    refine ⟨l, ?_⟩
    have h1 : e (α l) = γ' := by rw [hl, MulEquiv.apply_symm_apply]
    show Mod3323.toL3 hF (e (α l)) = γ
    rw [h1]
    apply Subtype.ext
    ext i j
    rw [Mod3323.toL3_apply, Matrix.SpecialLinearGroup.map_apply_coe]
    simp
  set I := (T.subgroupOf Y).map f with hI
  have hT2 : IsPGroup 2 T := hT.2.1
  have hI2 : IsPGroup 2 I := (hT2.comap_of_injective Y.subtype Y.subtype_injective).map _
  have hidx : ¬ 2 ∣ I.index := by
    intro h2
    have h1 := Subgroup.index_map_dvd (T.subgroupOf Y) hf
    have h3 : (T.subgroupOf Y).index = T.relIndex (Y ⊔ T) := by
      rw [← C45.relIndex_eq hTY]
      rfl
    rw [h3] at h1
    exact hT.2.2 (h2.trans h1)
  obtain ⟨v₀, hv₀⟩ := Mod3323.exists_fix hI2 hidx
  let φ : ↥X → L3.Vec := fun y =>
    Mod3323.toZ2 hF ∘ Multiplicative.toAdd (β ⟨y, hXU y.2⟩) 0
  have hφ : ∀ y : ↥X, φ y = 0 ∨ φ y = v₀ := by
    intro y
    refine hv₀ _ ?_
    rintro _ ⟨s, hs, rfl⟩
    have hsy : (s : G) * y * (s : G)⁻¹ = y := by
      have := Subgroup.mem_centralizer_iff.mp (hXC y.2) s hs
      rw [this]
      group
    have h1 := hβe s ⟨y, hXU y.2⟩ ⟨y, hXU y.2⟩ hsy.symm 0
    have hm : ((e (α s) : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((α s : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      have := CFSG.Assembly.LowTwoRank.specialLinearGroupEquivStatedSL_coe 3 F (e (α s))
      rw [MulEquiv.apply_symm_apply] at this
      exact this.symm
    show L3.act (Mod3323.toL3 hF (e (α s)))
      (Mod3323.toZ2 hF ∘ Multiplicative.toAdd (β ⟨y, hXU y.2⟩) 0) = _
    rw [Mod3323.act_toL3, hm, ← h1]
  have hinj : Function.Injective φ := by
    intro y y' hyy
    have h1 : Multiplicative.toAdd (β ⟨y, hXU y.2⟩) 0 =
        Multiplicative.toAdd (β ⟨y', hXU y'.2⟩) 0 := by
      funext i
      exact (Mod3323.toZ2 hF).injective (congrFun hyy i)
    have h2 : β ⟨y, hXU y.2⟩ = β ⟨y', hXU y'.2⟩ := by
      apply Multiplicative.toAdd.injective
      funext j
      have hj : j = 0 := Subsingleton.elim _ _
      subst hj
      exact h1
    have h3 := congrArg Subtype.val (hβi h2)
    exact Subtype.ext h3
  let ψ : ↥X → ↥({0, v₀} : Finset L3.Vec) := fun y =>
    ⟨φ y, by rcases hφ y with h0 | h0 <;> simp [h0]⟩
  have hψ : Function.Injective ψ := fun y y' hyy => hinj (congrArg Subtype.val hyy)
  calc Nat.card X ≤ Nat.card ↥({0, v₀} : Finset L3.Vec) := Nat.card_le_card_of_injective ψ hψ
    _ = ({0, v₀} : Finset L3.Vec).card := by rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    _ ≤ 2 := Finset.card_le_two

end CFSG.Quasithin.H13.MSY

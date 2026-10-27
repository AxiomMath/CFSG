module

public import CFSG.Monster.B.Recog.GenericGoldschmidtApp
public import CFSG.LocalAnalysis.ComponentClassification.Asc76XFinalLayer
import CFSG.Adapters.WholeGroupLayer
public import CFSG.GroupTheory.Fitting.CharacteristicP

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.RankThree.PartOne.SEITZ6

open CFSG.Open CFSG.ComponentClassification CFSG.Monster.B.Recog.GoldschmidtApp

theorem goldschmidtLayer_eq_layer (Y : Type*) [Group Y] :
    goldschmidtLayer Y = CFSG.layer Y :=
  CFSG.Adapters.goldschmidtLayer_eq_foundations Y

theorem exists_layer_model (hgold : CFSG.Goldschmidt.TopStatement) {X : Type} [Group X] [Finite X]
    (S : Sylow 2 X) (hSab : IsMulCommutative (S : Subgroup X))
    (hO : ∀ N : Subgroup X, N.Normal → Odd (Nat.card N) → N = ⊥)
    (hO2 : ∀ R : Subgroup X, R.Normal → IsPGroup 2 R → R = ⊥) :
    ∃ (Y : Type) (_ : Group Y) (_ : Finite Y) (ι : Y →* X), Function.Injective ι ∧
      ι.range = Subgroup.normalClosure ((S : Subgroup X) : Set X) ∧ CFSG.layer Y = ⊤ ∧
      Subgroup.center Y = ⊥ ∧ ∀ K : Subgroup Y, CFSG.IsComponent K → goldschmidtSimpleType ↥K := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hOX : componentClassificationOddCore X = ⊥ :=
    le_bot_iff.1 (sSup_le fun N hN => le_bot_iff.2 (hO N hN.1 hN.2))
  obtain ⟨hpc, -, hGc⟩ := CFSG.Goldschmidt.milestone_of_topStatement hgold X S (S : Subgroup X)
    le_rfl hSab (fun a _ g hg => hg)
  set M : Subgroup X := Subgroup.normalClosure ((S : Subgroup X) : Set X) with hM
  have hOM : goldschmidtOddCore M = ⊥ := by
    have h := OddCore.normal_intersection X M
    rw [hOX, inf_bot_eq] at h
    exact (Subgroup.map_eq_bot_iff_of_injective _ (Subgroup.subtype_injective _)).1 h
  have hπ : Function.Injective (QuotientGroup.mk' (goldschmidtOddCore M)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hOM]
  obtain ⟨φ, hφ⟩ : ∃ φ : M ≃* M ⧸ goldschmidtOddCore M,
      ∀ m, φ m = QuotientGroup.mk' (goldschmidtOddCore M) m :=
    ⟨MulEquiv.ofBijective _ ⟨hπ, QuotientGroup.mk'_surjective _⟩, fun _ => rfl⟩
  obtain ⟨ι, hιdef⟩ : ∃ ι : M ⧸ goldschmidtOddCore M →* X,
      ι = M.subtype.comp φ.symm.toMonoidHom := ⟨_, rfl⟩
  have hι : Function.Injective ι := by
    rw [hιdef]
    exact M.subtype_injective.comp φ.symm.injective
  have hιrange : ι.range = M := by
    ext x
    constructor
    · rintro ⟨y, rfl⟩
      rw [hιdef]
      exact (φ.symm y).2
    · intro hx
      refine ⟨φ ⟨x, hx⟩, ?_⟩
      rw [hιdef]
      simp
  have hYcore : goldschmidtOddCore (M ⧸ goldschmidtOddCore M) = ⊥ := OddCore.quotient_corefree M
  have hPc : CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M) = ⊥ := by
    have hP := normal_map_of_characteristic φ
      (openPCore_characteristic (M ⧸ goldschmidtOddCore M))
    have h2 : IsPGroup 2 ((CFSG.Open.pCore 2 (M ⧸ goldschmidtOddCore M)).map
        (M.subtype.comp φ.symm.toMonoidHom)) := by
      have h := CFSG.pCore_isPGroup (p := 2) (G := M ⧸ goldschmidtOddCore M)
      exact h.map _
    have h3 := hO2 _ hP h2
    rw [← hιdef] at h3
    exact (Subgroup.map_eq_bot_iff_of_injective _ hι).1 h3
  rw [hPc, bot_sup_eq] at hpc
  have hL : CFSG.layer (M ⧸ goldschmidtOddCore M) = ⊤ := by
    rw [← goldschmidtLayer_eq_layer]
    exact hpc
  have hZ : Subgroup.center (M ⧸ goldschmidtOddCore M) = ⊥ := by
    refine Asc76X.center_eq_bot_of (fun N hN hodd => ?_) (fun N hN hP => ?_)
    · have hle : N ≤ componentClassificationOddCore (M ⧸ goldschmidtOddCore M) :=
        OddCore.maximal _ N hN hodd
      exact le_bot_iff.1 (hle.trans hYcore.le)
    · have hle : N ≤ CFSG.pCore 2 (M ⧸ goldschmidtOddCore M) := le_sSup ⟨hN, hP⟩
      rw [hPc] at hle
      exact le_bot_iff.1 hle
  refine ⟨M ⧸ goldschmidtOddCore M, inferInstance, inferInstance, ι, hι, hιrange, hL, hZ,
    fun K hK => ?_⟩
  have hcen := Asc76X.center_component_eq_bot hL hZ hK
  have e : ↥K ⧸ Subgroup.center ↥K ≃* ↥K :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  exact Asc76X.goldschmidtSimpleType_of_mulEquiv e.symm
    (hGc K ((CFSG.isComponent_iff_open K).1 hK))

open CFSG.LocalCores Asc76X in
theorem card_eq_prod_components {Y : Type} [Group Y] [Finite Y] (hL : CFSG.layer Y = ⊤)
    (hZ : Subgroup.center Y = ⊥) [Fintype (ComponentIndex Y)] :
    Nat.card Y = ∏ K : ComponentIndex Y, Nat.card K.1 := by
  rw [← Nat.card_pi, Nat.card_congr (layerEquiv hL hZ).toEquiv.symm]

theorem card_dvd_of_injective_hom {B C : Type*} [Group B] [Group C] [Finite C] (r : B →* C)
    (hr : Function.Injective r) : Nat.card B ∣ Nat.card C := by
  rw [Nat.card_congr (MonoidHom.ofInjective hr).toEquiv]
  exact Subgroup.card_subgroup_dvd_card _

open CFSG.LocalCores Asc76X in
theorem exists_proj_injective {Y B : Type} [Group Y] [Finite Y] [Group B] [IsSimpleGroup B]
    (hL : CFSG.layer Y = ⊤) (hZ : Subgroup.center Y = ⊥) (f : B →* Y)
    (hf : Function.Injective f) :
    ∃ K : ComponentIndex Y, Function.Injective ((layerProj hL hZ K).comp f) := by
  obtain ⟨a, ha⟩ := exists_ne (1 : B)
  have hfa : f a ≠ 1 := fun h => ha (hf (by rw [h, map_one]))
  obtain ⟨K, hK⟩ := exists_layerProj_ne_one hL hZ hfa
  refine ⟨K, (MonoidHom.ker_eq_bot_iff _).1 ?_⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal ((layerProj hL hZ K).comp f).ker with h | h
  · exact h
  · exfalso
    have : a ∈ ((layerProj hL hZ K).comp f).ker := by rw [h]; exact Subgroup.mem_top _
    exact hK (by simpa using this)

open CFSG.LocalCores Asc76X in
theorem exists_carrier {Y B₁ B₂ : Type} [Group Y] [Finite Y] [Group B₁] [Group B₂]
    [IsSimpleGroup B₁] [IsSimpleGroup B₂] (hL : CFSG.layer Y = ⊤) (hZ : Subgroup.center Y = ⊥)
    (f₁ : B₁ →* Y) (f₂ : B₂ →* Y) (hf₁ : Function.Injective f₁) (hf₂ : Function.Injective f₂)
    (hc₁ : Subgroup.center B₁ = ⊥) (hcomm : ∀ a b, f₁ a * f₂ b = f₂ b * f₁ a) :
    (∃ K : ComponentIndex Y, Nat.card B₁ * Nat.card B₂ ∣ Nat.card K.1) ∨
      (∃ K₁ K₂ : ComponentIndex Y, K₁ ≠ K₂ ∧ Nat.card B₁ ∣ Nat.card K₁.1 ∧
        Nat.card B₂ ∣ Nat.card K₂.1) := by
  obtain ⟨K₁, h₁⟩ := exists_proj_injective hL hZ f₁ hf₁
  obtain ⟨K₂, h₂⟩ := exists_proj_injective hL hZ f₂ hf₂
  by_cases hK : K₁ = K₂
  · subst hK
    left
    refine ⟨K₁, ?_⟩
    set r₁ := (layerProj hL hZ K₁).comp f₁ with hr₁
    set r₂ := (layerProj hL hZ K₁).comp f₂ with hr₂
    have hcm : ∀ (a : B₁) (b : B₂), Commute (r₁ a) (r₂ b) := fun a b => by
      show r₁ a * r₂ b = r₂ b * r₁ a
      have e1 : r₁ a * r₂ b = layerProj hL hZ K₁ (f₁ a * f₂ b) := by
        rw [map_mul]; rfl
      have e2 : r₂ b * r₁ a = layerProj hL hZ K₁ (f₂ b * f₁ a) := by
        rw [map_mul]; rfl
      rw [e1, e2, hcomm a b]
    have hρ : Function.Injective (MonoidHom.noncommCoprod r₁ r₂ hcm) := by
      refine (injective_iff_map_eq_one _).2 fun ⟨a, b⟩ h => ?_
      rw [MonoidHom.noncommCoprod_apply] at h
      have hab : r₁ a = (r₂ b)⁻¹ := eq_inv_of_mul_eq_one_left h
      have ha1 : a ∈ Subgroup.center B₁ := by
        rw [Subgroup.mem_center_iff]
        intro a'
        apply h₁
        have hc : Commute (r₁ a') (r₁ a) := by rw [hab]; exact (hcm a' b).inv_right
        rw [map_mul, map_mul]
        exact hc.eq
      rw [hc₁, Subgroup.mem_bot] at ha1
      subst ha1
      rw [map_one, one_mul] at h
      have hb1 : b = 1 := h₂ (by rw [h, map_one])
      rw [hb1]
      rfl
    rw [← Nat.card_prod]
    exact card_dvd_of_injective_hom _ hρ
  · exact Or.inr ⟨K₁, K₂, hK, card_dvd_of_injective_hom _ h₁, card_dvd_of_injective_hom _ h₂⟩

end CFSG.RankThree.PartOne.SEITZ6

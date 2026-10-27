module

public import CFSG.Quasithin.Background.A1cTransfer
public import CFSG.Quasithin.Background.C3Defs
public import CFSG.Quasithin.H13.Statements

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13
open CFSG.Assembly.LowTwoRank (StatedSL)

section SL2

variable {k : Type*} [Field k]

theorem exists_sl2_mulVec_single (u : Fin 2 → k) (hu : u ≠ 0) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) k,
      (s : Matrix (Fin 2) (Fin 2) k).mulVec (Pi.single 0 1) = u := by
  by_cases h0 : u 0 = 0
  · have h1 : u 1 ≠ 0 := fun h1 => hu (funext fun i => by fin_cases i <;> simp [h0, h1])
    refine ⟨⟨!![u 0, -(u 1)⁻¹; u 1, 0], by simp [Matrix.det_fin_two, h1]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]
  · refine ⟨⟨!![u 0, 0; u 1, (u 0)⁻¹], by simp [Matrix.det_fin_two, h0]⟩, ?_⟩
    funext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two]

theorem exists_sl2_mulVec_eq (u w : Fin 2 → k) (hu : u ≠ 0) (hw : w ≠ 0) :
    ∃ s : Matrix.SpecialLinearGroup (Fin 2) k, (s : Matrix (Fin 2) (Fin 2) k).mulVec u = w := by
  obtain ⟨a, ha⟩ := exists_sl2_mulVec_single u hu
  obtain ⟨b, hb⟩ := exists_sl2_mulVec_single w hw
  refine ⟨b * a⁻¹, ?_⟩
  have h1 : ((b * a⁻¹ * a : Matrix.SpecialLinearGroup (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) =
      (b : Matrix (Fin 2) (Fin 2) k) := by rw [inv_mul_cancel_right]
  rw [← ha, Matrix.mulVec_mulVec, ← Matrix.SpecialLinearGroup.coe_mul, h1, hb]

end SL2

theorem mem_statedSL_of_det {n : ℕ} {F : Type} [Field F] {A : GL (Fin n) F}
    (h : (A : Matrix (Fin n) (Fin n) F).det = 1) : A ∈ StatedSL n F :=
  CFSG.Open.StatedAPI.mem_statedSL_of_det h

variable {G : Type} [Group G]

theorem isNaturalSection_irred {A V Z : Subgroup G} {N : Subgroup ↥A} {F : Type} [Field F]
    (h : IsNaturalSection A V Z N (StatedSL 2 F)) {X : Subgroup G} (hZX : Z ≤ X) (hXV : X ≤ V)
    (hAX : A ≤ Subgroup.normalizer (X : Set G)) : X = Z ∨ X = V := by
  obtain ⟨hAV, α, hα, -, β, -, hβker, hequiv⟩ := h
  have hβ1 : ∀ v : ↥V, β v = 1 ↔ (v : G) ∈ Z := fun v => by
    rw [← MonoidHom.mem_ker, hβker, Subgroup.mem_subgroupOf]
  by_cases hXZ : X ≤ Z
  · exact Or.inl (le_antisymm hXZ hZX)
  right
  obtain ⟨x, hxX, hxZ⟩ := Set.not_subset.mp hXZ
  refine le_antisymm hXV fun v hv => ?_
  by_cases hvZ : v ∈ Z
  · exact hZX hvZ
  have hu : Multiplicative.toAdd (β ⟨x, hXV hxX⟩) ≠ 0 := fun h0 =>
    hxZ ((hβ1 _).mp (by simpa using h0))
  have hw : Multiplicative.toAdd (β ⟨v, hv⟩) ≠ 0 := fun h0 =>
    hvZ ((hβ1 _).mp (by simpa using h0))
  obtain ⟨s, hs⟩ := exists_sl2_mulVec_eq _ _ hu hw
  have hγ : (Matrix.SpecialLinearGroup.toGL s : GL (Fin 2) F) ∈ StatedSL 2 F :=
    mem_statedSL_of_det (by simp)
  obtain ⟨a, ha⟩ := hα ⟨_, hγ⟩
  have hyX : (a : G) * x * (a : G)⁻¹ ∈ X := (Subgroup.mem_normalizer_iff.mp (hAX a.2) x).mp hxX
  have hyV : (a : G) * x * (a : G)⁻¹ ∈ V := hXV hyX
  have heq := hequiv a ⟨x, hXV hxX⟩ ⟨_, hyV⟩ rfl
  rw [ha] at heq
  have hβeq : β ⟨_, hyV⟩ = β ⟨v, hv⟩ := by
    apply Multiplicative.toAdd.injective
    rw [heq, ← hs]
    rfl
  have hZ : (⟨_, hyV⟩ : ↥V)⁻¹ * ⟨v, hv⟩ ∈ β.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hβeq, inv_mul_cancel]
  rw [hβker, Subgroup.mem_subgroupOf] at hZ
  have : v = ((a : G) * x * (a : G)⁻¹) * (((a : G) * x * (a : G)⁻¹)⁻¹ * v) := by group
  rw [this]
  exact X.mul_mem hyX (hZX (by simpa using hZ))

theorem pCore_characteristic' (p : ℕ) (X : Type*) [Group X] :
    (CFSG.pCore p X).Characteristic := by
  exact CFSG.LieType.BorelTits.pCore_characteristic p

theorem isNaturalSection_conj {A V Z : Subgroup G} {ι : Type} [Fintype ι] [DecidableEq ι]
    {F : Type} [Field F] {Γ : Subgroup (Matrix.GeneralLinearGroup ι F)}
    (h : IsNaturalSection A V Z (CFSG.pCore 2 ↥A) Γ) {g : G}
    (hgA : g ∈ Subgroup.normalizer (A : Set G)) (hgZ : g ∈ Subgroup.normalizer (Z : Set G)) :
    IsNaturalSection A (conjSubgroup V g) Z (CFSG.pCore 2 ↥A) Γ := by
  obtain ⟨hAV, α, hα, hker, β, hβ, hβker, hequiv⟩ := h
  have hgA' : ∀ a ∈ A, g * a * g⁻¹ ∈ A := fun a ha => (Subgroup.mem_normalizer_iff.mp hgA a).mp ha
  have hgA'' : ∀ a ∈ A, g⁻¹ * a * g ∈ A := fun a ha => by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ hgA) a).mp ha
    simpa using this
  let φe : ↥A ≃* ↥A :=
    { toFun := fun a => ⟨g * a * g⁻¹, hgA' a a.2⟩
      invFun := fun a => ⟨g⁻¹ * a * g, hgA'' a a.2⟩
      left_inv := fun a => Subtype.ext (by simp [mul_assoc])
      right_inv := fun a => Subtype.ext (by simp [mul_assoc])
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hφ : ∀ a : ↥A, ((φe a : ↥A) : G) = g * a * g⁻¹ := fun a => rfl
  let ψ : ↥(conjSubgroup V g) →* ↥V :=
    { toFun := fun w => ⟨g * w * g⁻¹, mem_conjSubgroup_iff.mp w.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp [mul_assoc]) }
  have hψ : ∀ w : ↥(conjSubgroup V g), ((ψ w : ↥V) : G) = g * w * g⁻¹ := fun w => rfl
  refine ⟨fun a ha => ?_, α.comp φe.toMonoidHom, hα.comp φe.surjective, ?_, β.comp ψ, ?_, ?_,
    fun a u v huv => ?_⟩
  · rw [Subgroup.mem_normalizer_iff]
    intro w
    rw [mem_conjSubgroup_iff, mem_conjSubgroup_iff,
      Subgroup.mem_normalizer_iff.mp (hAV (hgA' a ha)) (g * w * g⁻¹)]
    constructor <;> intro hx <;> convert hx using 1 <;> group
  · rw [← MonoidHom.comap_ker, hker]
    exact (Subgroup.characteristic_iff_comap_eq.mp (pCore_characteristic' 2 _)) φe
  · intro y
    obtain ⟨v, rfl⟩ := hβ y
    refine ⟨⟨g⁻¹ * v * g, mem_conjSubgroup_iff.mpr (by simp [mul_assoc])⟩, ?_⟩
    change β (ψ _) = β v
    congr 1
    exact Subtype.ext (by rw [hψ]; group)
  · ext w
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, ← MonoidHom.mem_ker, hβker,
      Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, hψ]
    exact (Subgroup.mem_normalizer_iff.mp hgZ w).symm
  · have hv : ((ψ v : ↥V) : G) = ((φe a : ↥A) : G) * ψ u * ((φe a : ↥A) : G)⁻¹ := by
      rw [hψ, hψ, hφ, huv, InvMemClass.coe_inv]
      group
    exact hequiv (φe a) (ψ u) (ψ v) hv

end CFSG.Quasithin.Vol2.Ch11.SecD

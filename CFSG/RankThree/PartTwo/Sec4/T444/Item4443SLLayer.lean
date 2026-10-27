module

public import CFSG.GroupTheory.LocalCores.Layer
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.PrimeSetCore

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item4443SL

open CFSG CFSG.LocalCores

variable {X : Type*} [Group X] [Finite X]

theorem le_sSup_components_of_inner {Y : Subgroup X} (hYp : ⁅Y, Y⁆ = Y)
    (hF : Y ≤ Subgroup.centralizer (fittingSubgroup X : Set X))
    (hinner : ∀ K : Subgroup X, IsComponent K → ∀ y ∈ Y,
      ∃ c ∈ K, ∀ z ∈ K, y * z * y⁻¹ = c * z * c⁻¹) :
    Y ≤ sSup {K : Subgroup X | IsComponent K ∧ ¬ Y ≤ Subgroup.centralizer (K : Set X)} := by
  classical
  set E₁ := sSup {K : Subgroup X | IsComponent K ∧ ¬ Y ≤ Subgroup.centralizer (K : Set X)}
    with hE₁
  set Z₀ := generalizedFitting X ⊓ Subgroup.centralizer (generalizedFitting X : Set X) with hZ₀
  have hdec : ∀ y ∈ Y, ∃ z ∈ Z₀, ∃ e ∈ E₁, y = z * e := by
    intro y hy
    let c : ∀ K : ComponentIndex X, K.1 := fun K =>
      if hK : Y ≤ Subgroup.centralizer (K.1 : Set X) then 1
      else ⟨Classical.choose (hinner K.1 K.2 y hy), (Classical.choose_spec (hinner K.1 K.2 y hy)).1⟩
    have hc : ∀ K : ComponentIndex X, ∀ z ∈ K.1, y * z * y⁻¹ = (c K : X) * z * (c K : X)⁻¹ := by
      intro K z hz
      by_cases hK : Y ≤ Subgroup.centralizer (K.1 : Set X)
      · have h1 : (c K : X) = 1 := by simp [c, hK]
        rw [h1, (Subgroup.mem_centralizer_iff.mp (hK hy) z hz).symm]
        group
      · have h1 : (c K : X) = Classical.choose (hinner K.1 K.2 y hy) := by simp [c, hK]
        rw [h1]
        exact (Classical.choose_spec (hinner K.1 K.2 y hy)).2 z hz
    set e := layerMul X c with he
    have heE : e ∈ E₁ := by
      refine layerMul_mem c fun K => ?_
      by_cases hK : Y ≤ Subgroup.centralizer (K.1 : Set X)
      · have h1 : (c K : X) = 1 := by simp [c, hK]
        rw [h1]
        exact one_mem _
      · have hmem : K.1 ∈ {K : Subgroup X | IsComponent K ∧
            ¬ Y ≤ Subgroup.centralizer (K : Set X)} := ⟨K.2, hK⟩
        exact (le_sSup hmem : K.1 ≤ E₁) (c K).2
    have hek : ∀ K : ComponentIndex X, ∀ z ∈ K.1, e⁻¹ * z * e = (c K : X)⁻¹ * z * (c K : X) := by
      intro K z hz
      have hdec' := layerMul_eq_mul_update c K
      set r := layerMul X (Function.update c K 1) with hr
      have hz' : (c K : X)⁻¹ * z * (c K : X) ∈ K.1 :=
        K.1.mul_mem (K.1.mul_mem (K.1.inv_mem (c K).2) hz) (c K).2
      have hrz := (commute_layerMul_update c K hz').eq
      rw [he, hdec']
      calc ((c K : X) * r)⁻¹ * z * ((c K : X) * r) = r⁻¹ * ((c K : X)⁻¹ * z * (c K : X) * r) := by
            group
        _ = r⁻¹ * (r * ((c K : X)⁻¹ * z * (c K : X))) := by rw [hrz]
        _ = (c K : X)⁻¹ * z * (c K : X) := by group
    have hyeE : y * e⁻¹ ∈ Subgroup.centralizer (layer X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro z hz
      have hle : layer X ≤ Subgroup.centralizer ({y * e⁻¹} : Set X) := by
        refine sSup_le fun K hK z hz => ?_
        rw [Subgroup.mem_centralizer_singleton_iff]
        have h1 := hek ⟨K, hK⟩ z hz
        have h2 := hc ⟨K, hK⟩ ((c ⟨K, hK⟩ : X)⁻¹ * z * (c ⟨K, hK⟩ : X))
          (K.mul_mem (K.mul_mem (K.inv_mem (c ⟨K, hK⟩).2) hz) (c ⟨K, hK⟩).2)
        have h3 : y * e⁻¹ * z * (y * e⁻¹)⁻¹ = z := by
          calc y * e⁻¹ * z * (y * e⁻¹)⁻¹ = y * (e⁻¹ * z * e) * y⁻¹ := by group
            _ = y * ((c ⟨K, hK⟩ : X)⁻¹ * z * (c ⟨K, hK⟩ : X)) * y⁻¹ := by rw [h1]
            _ = z := by rw [h2]; group
        calc z * (y * e⁻¹) = (y * e⁻¹ * z * (y * e⁻¹)⁻¹) * (y * e⁻¹) := by rw [h3]
          _ = y * e⁻¹ * z := by group
      exact (Subgroup.mem_centralizer_singleton_iff.mp (hle hz))
    have heF : e ∈ Subgroup.centralizer (fittingSubgroup X : Set X) := by
      have h := fitting_layer_commute (G := X)
      have hle : layer X ≤ Subgroup.centralizer (fittingSubgroup X : Set X) := by
        rw [Subgroup.commutator_comm] at h
        exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp h
      exact hle (layerMul_mem c fun K => component_le_layer K.2 (c K).2)
    have hyeF : y * e⁻¹ ∈ Subgroup.centralizer (fittingSubgroup X : Set X) :=
      Subgroup.mul_mem _ (hF hy) (Subgroup.inv_mem _ heF)
    have hyeC : y * e⁻¹ ∈ Subgroup.centralizer (generalizedFitting X : Set X) := by
      rw [Subgroup.mem_centralizer_iff]
      intro w hw
      have hle : generalizedFitting X ≤ Subgroup.centralizer ({y * e⁻¹} : Set X) := by
        refine sup_le (fun f hf => ?_) (fun l hl => ?_)
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hyeF f hf
        · rw [Subgroup.mem_centralizer_singleton_iff]
          exact Subgroup.mem_centralizer_iff.mp hyeE l hl
      exact Subgroup.mem_centralizer_singleton_iff.mp (hle hw)
    refine ⟨y * e⁻¹, ⟨centralizer_generalizedFitting_le X hyeC, hyeC⟩, e, heE, by group⟩
  have hE₁F : E₁ ≤ generalizedFitting X :=
    sSup_le fun K hK => (component_le_layer hK.1).trans le_sup_right
  have hcommZE : ∀ (z : Z₀) (e : E₁), Commute (z : X) (e : X) := fun z e =>
    ((Subgroup.mem_centralizer_iff.mp z.2.2 (e : X) (hE₁F e.2)).symm : (z : X) * e = e * z)
  set φ : Z₀ × E₁ →* X := Z₀.subtype.noncommCoprod E₁.subtype hcommZE with hφ
  have hφapp : ∀ u : Z₀ × E₁, φ u = (u.1 : X) * u.2 := fun u => rfl
  have hZ₀c : ∀ z z' : Z₀, z * z' = z' * z := fun z z' => Subtype.ext
    ((Subgroup.mem_centralizer_iff.mp z.2.2 (z' : X) z'.2.1).symm :
      (z : X) * z' = z' * z)
  rw [← hYp, Subgroup.commutator_le]
  intro g hg g' hg'
  obtain ⟨z, hz, e, he, rfl⟩ := hdec g hg
  obtain ⟨z', hz', e', he', rfl⟩ := hdec g' hg'
  set u : Z₀ × E₁ := (⟨z, hz⟩, ⟨e, he⟩) with hu
  set v : Z₀ × E₁ := (⟨z', hz'⟩, ⟨e', he'⟩) with hv
  have hg1 : z * e = φ u := rfl
  have hg2 : z' * e' = φ v := rfl
  rw [commutatorElement_def, hg1, hg2, ← map_inv, ← map_inv, ← map_mul, ← map_mul, ← map_mul,
    hφapp]
  have hz1 : (u * v * u⁻¹ * v⁻¹).1 = 1 := by
    simp only [Prod.fst_mul, Prod.fst_inv]
    rw [hZ₀c u.1 v.1]
    group
  rw [hz1, Subgroup.coe_one, one_mul]
  exact (u * v * u⁻¹ * v⁻¹).2.2

end CFSG.RankThree.PartTwo.Sec4.Item4443SL

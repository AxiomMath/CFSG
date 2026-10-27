module

public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Layer

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open scoped commutatorElement

theorem uc22p22u_acts_inner {Q : Type*} [Group Q] (C H : Subgroup Q) (hH : H ≤ normalizer (C : Set Q))
    (hout : ∀ σ τ : MulAut ↥C, ∃ y : ↥C, σ * τ * σ⁻¹ * τ⁻¹ = MulAut.conj y) :
    ∀ y ∈ ⁅H, H⁆, ∃ c ∈ C, ∀ x ∈ C, y * x * y⁻¹ = c * x * c⁻¹ := by
  let φ : H →* MulAut ↥C := C.normalizerMonoidHom.comp (Subgroup.inclusion hH)
  let K : Subgroup Q := ((MulAut.conj : ↥C →* MulAut ↥C).range.comap φ).map H.subtype
  have hK : ⁅H, H⁆ ≤ K := by
    rw [commutator_le]
    intro a ha b hb
    obtain ⟨c, hc⟩ := hout (φ ⟨a, ha⟩) (φ ⟨b, hb⟩)
    refine ⟨⁅(⟨a, ha⟩ : H), ⟨b, hb⟩⁆, ⟨c, ?_⟩, rfl⟩
    rw [map_commutatorElement, commutatorElement_def]
    exact hc.symm
  intro y hy
  obtain ⟨h, ⟨c, hc⟩, rfl⟩ := hK hy
  refine ⟨c, c.2, fun x hx => ?_⟩
  have := congrArg (fun σ : MulAut ↥C => (σ ⟨x, hx⟩ : Q)) hc
  simpa [φ, MulAut.conj_apply] using this.symm

theorem uc22p22u_exists_layer_implementer {G : Type*} [Group G] [Finite G] (σ : G →* G)
    (hσ : ∀ K : Subgroup G, CFSG.IsComponent K → ∃ c ∈ K, ∀ x ∈ K, σ x = c * x * c⁻¹) :
    ∃ e ∈ CFSG.layer G, ∀ x ∈ CFSG.layer G, σ x = e * x * e⁻¹ := by
  choose! c hcK hc using hσ
  let x₀ : ∀ K : CFSG.LocalCores.ComponentIndex G, ↥K.1 := fun K => ⟨c K.1, hcK K.1 K.2⟩
  have hcomp : ∀ (K : CFSG.LocalCores.ComponentIndex G), ∀ k ∈ K.1,
      σ k = CFSG.LocalCores.layerMul G x₀ * k * (CFSG.LocalCores.layerMul G x₀)⁻¹ := by
    intro K k hk
    have hcomm := CFSG.LocalCores.commute_layerMul_update x₀ K hk
    have h1 : CFSG.LocalCores.layerMul G (Function.update x₀ K 1) * k *
        (CFSG.LocalCores.layerMul G (Function.update x₀ K 1))⁻¹ = k := by
      rw [← hcomm.eq]
      group
    rw [hc K.1 K.2 k hk, CFSG.LocalCores.layerMul_eq_mul_update x₀ K]
    calc c K.1 * k * (c K.1)⁻¹
        = c K.1 * (CFSG.LocalCores.layerMul G (Function.update x₀ K 1) * k *
          (CFSG.LocalCores.layerMul G (Function.update x₀ K 1))⁻¹) * (c K.1)⁻¹ := by rw [h1]
      _ = _ := by simp only [x₀, mul_inv_rev]; group
  refine ⟨CFSG.LocalCores.layerMul G x₀, ?_, ?_⟩
  · rw [← CFSG.LocalCores.layerMul_range]
    exact MonoidHom.mem_range.mpr ⟨x₀, rfl⟩
  · have hle : CFSG.layer G ≤ σ.eqLocus (MulAut.conj (CFSG.LocalCores.layerMul G x₀)).toMonoidHom := by
      refine sSup_le fun K hK k hk => ?_
      exact hcomp ⟨K, hK⟩ k hk
    exact fun x hx => hle hx

theorem uc22p22u_sub_le_cent_layer {Q : Type*} [Group Q] [Finite Q] (N : Subgroup Q) [N.Normal]
    (S : Subgroup Q)
    (hF : S ≤ centralizer (((CFSG.fittingSubgroup ↥N).map N.subtype : Subgroup Q) : Set Q))
    (hC : ∀ C : Subgroup ↥N, IsComponentOf C (⊤ : Subgroup ↥N) → ∀ y : Q, y ∈ S →
      ∃ c ∈ C, ∀ x ∈ C, y * (x : Q) * y⁻¹ = (c : Q) * (x : Q) * (c : Q)⁻¹) :
    S ≤ centralizer ((((CFSG.fittingSubgroup ↥N).map N.subtype) ⊔ ((CFSG.layer ↥N).map N.subtype) :
      Subgroup Q) : Set Q) ⊔ (CFSG.layer ↥N).map N.subtype := by
  intro y hy
  let σ : ↥N →* ↥N := (MulAut.conjNormal y : MulAut ↥N).toMonoidHom
  have hσ : ∀ x : ↥N, ((σ x : ↥N) : Q) = y * x * y⁻¹ := fun x => MulAut.conjNormal_apply y x
  obtain ⟨e, he, hxe⟩ := uc22p22u_exists_layer_implementer σ (fun K hK => by
    obtain ⟨c, hcK, hc⟩ := hC K ((CFSG.isComponent_iff_open K).mp hK) y hy
    refine ⟨c, hcK, fun x hx => Subtype.ext ?_⟩
    rw [hσ, hc x hx]
    simp)
  have hlayer : ∀ x ∈ CFSG.layer ↥N, (x : Q) * ((e : Q)⁻¹ * y) = ((e : Q)⁻¹ * y) * x := by
    intro x hx
    have h := congrArg Subtype.val (hxe x hx)
    rw [hσ] at h
    have h' : y * (x : Q) * y⁻¹ = (e : Q) * x * (e : Q)⁻¹ := by simpa using h
    calc (x : Q) * ((e : Q)⁻¹ * y) = (e : Q)⁻¹ * ((e : Q) * x * (e : Q)⁻¹) * y := by group
      _ = (e : Q)⁻¹ * (y * x * y⁻¹) * y := by rw [h']
      _ = ((e : Q)⁻¹ * y) * x := by group
  have hfit : ∀ x ∈ CFSG.fittingSubgroup ↥N,
      (x : Q) * ((e : Q)⁻¹ * y) = ((e : Q)⁻¹ * y) * x := by
    intro x hx
    have h1 : Commute (x : Q) y := mem_centralizer_iff.mp (hF hy) x ⟨x, hx, rfl⟩
    have hxe' : x ∈ centralizer (CFSG.layer ↥N : Set ↥N) :=
      commutator_eq_bot_iff_le_centralizer.mp CFSG.LocalCores.fitting_layer_commute hx
    have h2 : Commute (x : Q) (e : Q) :=
      (congrArg Subtype.val (mem_centralizer_iff.mp hxe' e he)).symm
    exact (h2.inv_right.mul_right h1).eq
  have hz : (e : Q)⁻¹ * y ∈ centralizer ((((CFSG.fittingSubgroup ↥N).map N.subtype) ⊔
      ((CFSG.layer ↥N).map N.subtype) : Subgroup Q) : Set Q) := by
    have hle : (CFSG.fittingSubgroup ↥N).map N.subtype ⊔ (CFSG.layer ↥N).map N.subtype ≤
        centralizer ({(e : Q)⁻¹ * y} : Set Q) := by
      refine sup_le ?_ ?_
      · rintro _ ⟨x, hx, rfl⟩
        exact mem_centralizer_singleton_iff.mpr (hfit x hx)
      · rintro _ ⟨x, hx, rfl⟩
        exact mem_centralizer_singleton_iff.mpr (hlayer x hx)
    exact mem_centralizer_iff.mpr fun h hh => mem_centralizer_singleton_iff.mp (hle hh)
  have hmem := mul_mem_sup (mem_map_of_mem N.subtype he) hz
  rw [sup_comm]
  simpa using hmem

theorem uc22p22u_layer_eq_top_of_central_ext {Y A : Type*} [Group Y] [Finite Y] [Group A] (f : Y →* A)
    (hf : Function.Surjective f) (hker : f.ker ≤ Subgroup.center Y)
    (hY : ⁅(⊤ : Subgroup Y), ⊤⁆ = (⊤ : Subgroup Y)) (hA : CFSG.layer A = (⊤ : Subgroup A)) :
    CFSG.layer Y = (⊤ : Subgroup Y) := by
  have : (CFSG.layer Y).Characteristic := CFSG.LocalCores.layer_characteristic
  have hmap : (CFSG.layer Y).map f = ⊤ := by
    rw [CFSG.layer_eq_componentClassification,
      CFSG.ComponentClassification.CentralComponentQuotients.layer_map f hf hker,
      ← CFSG.layer_eq_componentClassification, hA]
  have hsup : CFSG.layer Y ⊔ f.ker = ⊤ := by
    rw [← comap_map_eq, hmap, comap_top]
  have hK : ∀ T : Subgroup Y, ⁅f.ker, T⁆ = ⊥ := fun T =>
    le_bot_iff.mp ((commutator_mono hker le_rfl).trans (commutator_center_left T).le)
  have h1 : ⁅CFSG.layer Y ⊔ f.ker, (⊤ : Subgroup Y)⁆ = ⁅CFSG.layer Y, ⊤⁆ := by
    rw [commutator_sup_right, hK, sup_bot_eq]
  have h2 : ⁅CFSG.layer Y, CFSG.layer Y ⊔ f.ker⁆ = CFSG.layer Y := by
    rw [commutator_sup_left, commutator_comm (CFSG.layer Y) f.ker, hK, sup_bot_eq,
      CFSG.LocalCores.layer_perfect]
  calc CFSG.layer Y = ⁅CFSG.layer Y, CFSG.layer Y ⊔ f.ker⁆ := h2.symm
    _ = ⁅CFSG.layer Y, ⊤⁆ := by rw [hsup]
    _ = ⁅CFSG.layer Y ⊔ f.ker, ⊤⁆ := h1.symm
    _ = ⁅(⊤ : Subgroup Y), ⊤⁆ := by rw [hsup]
    _ = ⊤ := hY

end CFSG.LocalAnalysis.UniquenessCase.UC22

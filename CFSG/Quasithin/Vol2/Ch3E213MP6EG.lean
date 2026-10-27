module

import all CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.QuasithinUnique.Unconstrained.L2_5_2BorelA6
public import CFSG.Quasithin.Vol2.Ch3E213MP6EB

public section

namespace CFSG.Quasithin.Ch3E213M.P6E

open CFSG.QuasithinUnique CFSG.QuasithinUnique.Borel252.A6

variable {A : Type} [Group A] {K S E : Subgroup A} {e : ↥K ≃* M6}
  {χ : ↥(K ⊔ E) ≃* Equiv.Perm (Fin 6)}

theorem map_SK (hχ : ∀ (k : A) (hk : k ∈ K),
      (χ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ : Equiv.Perm (Fin 6)) = (e ⟨k, hk⟩ : P6))
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = U6) :
    ((S ⊓ K).subgroupOf (K ⊔ E)).map χ.toMonoidHom = D0 := by
  ext y
  constructor
  · rintro ⟨f, hf, rfl⟩
    have hfK : (f : A) ∈ K := hf.2
    have h1 : χ f = (e ⟨f, hfK⟩ : P6) := by
      rw [← hχ]
    have h2 : e ⟨f, hfK⟩ ∈ U6 := he ▸ ⟨⟨f, hfK⟩, hf, rfl⟩
    show χ f ∈ D0
    rw [h1]
    exact h2
  · intro hy
    have hyU : (⟨y, D0_le_A6 hy⟩ : M6) ∈ U6 := hy
    rw [← he] at hyU
    obtain ⟨k, hk, hky⟩ := hyU
    refine ⟨⟨k, (le_sup_left : K ≤ K ⊔ E) k.2⟩, hk, ?_⟩
    show χ _ = y
    rw [hχ]
    exact congrArg Subtype.val hky

theorem mem_S06 (hχ : ∀ (k : A) (hk : k ∈ K),
      (χ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ : Equiv.Perm (Fin 6)) = (e ⟨k, hk⟩ : P6))
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = U6) {s : ↥(K ⊔ E)}
    (hs : (s : A) ∈ Subgroup.normalizer ((S ⊓ K : Subgroup A) : Set A)) : χ s ∈ S06 := by
  apply normalizer_D0_le
  rw [← map_SK hχ he, Subgroup.mem_normalizer_iff]
  intro y
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine ⟨s * f * s⁻¹, ?_, by simp [map_mul, map_inv]⟩
    show ((s : A) * f * (s : A)⁻¹) ∈ S ⊓ K
    exact (Subgroup.mem_normalizer_iff.1 hs _).1 hf
  · rintro ⟨f, hf, hfy⟩
    refine ⟨s⁻¹ * f * s, ?_, ?_⟩
    · have h1 := (Subgroup.mem_normalizer_iff.1 (Subgroup.inv_mem _ hs) _).1 hf
      show ((s : A)⁻¹ * f * (s : A)) ∈ S ⊓ K
      simpa using h1
    · have hfy' : χ f = χ s * y * (χ s)⁻¹ := hfy
      show χ (s⁻¹ * f * s) = y
      rw [map_mul, map_mul, map_inv, hfy']
      group

theorem mem_K_of_mem (hχ : ∀ (k : A) (hk : k ∈ K),
      (χ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ : Equiv.Perm (Fin 6)) = (e ⟨k, hk⟩ : P6))
    {f : ↥(K ⊔ E)} (hf : χ f ∈ A6s) : (f : A) ∈ K := by
  have h1 : χ ⟨_, (le_sup_left : K ≤ K ⊔ E) (e.symm ⟨_, hf⟩).2⟩ = χ f := by
    rw [hχ _ (e.symm ⟨_, hf⟩).2]
    simp
  have h2 : ((e.symm ⟨_, hf⟩ : K) : A) = f := congrArg Subtype.val (χ.injective h1)
  exact h2 ▸ (e.symm ⟨_, hf⟩).2

variable [K.Normal]

theorem map_SF (hχ : ∀ (k : A) (hk : k ∈ K),
      (χ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ : Equiv.Perm (Fin 6)) = (e ⟨k, hk⟩ : P6))
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = U6) {v₀ : A} (hv₀ : v₀ ∈ S)
    (hv₀F : v₀ ∈ K ⊔ E) (hv₀K : v₀ ∉ K) :
    ((S ⊓ (K ⊔ E)).subgroupOf (K ⊔ E)).map χ.toMonoidHom = S06 := by
  have hle : ((S ⊓ (K ⊔ E)).subgroupOf (K ⊔ E)).map χ.toMonoidHom ≤ S06 := by
    rintro _ ⟨f, hf, rfl⟩
    refine mem_S06 hχ he (Subgroup.inf_normalizer_le_normalizer_inf
      ⟨Subgroup.le_normalizer hf.1, ?_⟩)
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top _
  have hD0 : D0 ≤ ((S ⊓ (K ⊔ E)).subgroupOf (K ⊔ E)).map χ.toMonoidHom := by
    rw [← map_SK hχ he]
    exact Subgroup.map_mono fun f hf => ⟨hf.1, (le_sup_left : K ≤ K ⊔ E) hf.2⟩
  have hv : χ ⟨v₀, hv₀F⟩ ∈ ((S ⊓ (K ⊔ E)).subgroupOf (K ⊔ E)).map χ.toMonoidHom :=
    ⟨⟨v₀, hv₀F⟩, ⟨hv₀, hv₀F⟩, rfl⟩
  have hvA : χ ⟨v₀, hv₀F⟩ ∉ A6s := fun h => hv₀K (mem_K_of_mem hχ h)
  have hzB : zB ∈ ((S ⊓ (K ⊔ E)).subgroupOf (K ⊔ E)).map χ.toMonoidHom := by
    have h1 := hD0 (mul_mem_of_mem_extZ_of_not_mem (hle hv) hvA)
    have h2 := Subgroup.mul_mem _ (Subgroup.inv_mem _ hv) h1
    rwa [inv_mul_cancel_left] at h2
  refine le_antisymm hle fun x hx => ?_
  rcases hx with hx | hx
  · exact hD0 hx
  · have h3 := Subgroup.mul_mem _ (hD0 hx) hzB
    rwa [mul_assoc, zB_mul_self, mul_one] at h3

theorem inf_eq_of_inf_eq (hχ : ∀ (k : A) (hk : k ∈ K),
      (χ ⟨k, (le_sup_left : K ≤ K ⊔ E) hk⟩ : Equiv.Perm (Fin 6)) = (e ⟨k, hk⟩ : P6))
    (he : ((S ⊓ K).subgroupOf K).map e.toMonoidHom = U6) {B : Subgroup A}
    (hBK : B ⊓ K = S ⊓ K) (hSB : S ≤ B)
    (hSF : ((S ⊓ (K ⊔ E)).subgroupOf (K ⊔ E)).map χ.toMonoidHom = S06) :
    B ⊓ (K ⊔ E) = S ⊓ (K ⊔ E) := by
  refine le_antisymm (fun b hb => ⟨?_, hb.2⟩) (inf_le_inf_right _ hSB)
  have hn : b ∈ Subgroup.normalizer ((S ⊓ K : Subgroup A) : Set A) := by
    rw [← hBK]
    refine Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hb.1, ?_⟩
    rw [Subgroup.normalizer_eq_top_iff.mpr inferInstance]
    exact Subgroup.mem_top _
  have h1 : χ ⟨b, hb.2⟩ ∈ S06 := mem_S06 hχ he (s := ⟨b, hb.2⟩) hn
  rw [← hSF] at h1
  obtain ⟨f, hf, hfb⟩ := h1
  have h2 : f = ⟨b, hb.2⟩ := χ.injective hfb
  have h3 : (f : A) ∈ S := hf.1
  rw [h2] at h3
  exact h3

end CFSG.Quasithin.Ch3E213M.P6E

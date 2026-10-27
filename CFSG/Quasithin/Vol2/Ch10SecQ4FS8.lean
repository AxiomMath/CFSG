module

public import CFSG.Quasithin.Vol2.Ch10SecQ4FS6

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique

variable {G : Type} [Group G]

theorem conj_mem_normalizer_map {X : Subgroup G} {r : G}
    (hr : r ∈ Subgroup.normalizer (X : Set G)) (y : G) :
    y * r * y⁻¹ ∈ Subgroup.normalizer ((X.map (MulAut.conj y).toMonoidHom : Subgroup G) :
      Set G) := by
  rw [Subgroup.mem_normalizer_iff]
  intro z
  have hmem : ∀ w : G, w ∈ X.map (MulAut.conj y).toMonoidHom ↔ y⁻¹ * w * y ∈ X := by
    intro w
    constructor
    · rintro ⟨x, hx, rfl⟩
      simpa [MulAut.conj_apply, mul_assoc] using hx
    · intro hw
      exact ⟨y⁻¹ * w * y, hw, by simp [MulAut.conj_apply, mul_assoc]⟩
  rw [hmem, hmem]
  have e : y⁻¹ * (y * r * y⁻¹ * z * (y * r * y⁻¹)⁻¹) * y = r * (y⁻¹ * z * y) * r⁻¹ := by group
  rw [e]
  exact Subgroup.mem_normalizer_iff.mp hr _

theorem map_conj_map_conj (K : Subgroup G) (y s : G) :
    (K.map (MulAut.conj (y⁻¹ * s)).toMonoidHom).map (MulAut.conj y).toMonoidHom =
      K.map (MulAut.conj s).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

variable [Finite G]

theorem relIndex_centralizer_T0_le {H T K : Subgroup G} (hTH : T ≤ H) (hK : K ∈ cComp H)
    (hKs : IsShort2 K) (hKa : IsAltType K 5) {q : G} (hqK : q ∈ K) (hq3 : orderOf q = 3)
    {T₀ : Subgroup G} (hT₀T : T₀ ≤ T) (hT₀2 : IsPGroup 2 T₀)
    (hqT₀ : q ∈ Subgroup.normalizer (T₀ : Set G)) :
    (Subgroup.centralizer ({q} : Set G)).relIndex T₀ ≤ 16 := by
  have hq3' : q ^ 3 = 1 := by rw [← hq3]; exact pow_orderOf_eq_one q
  have hKsc : ∀ s ∈ T, K.map (MulAut.conj s).toMonoidHom ∈ cComp H := fun s hs =>
    H13.LocDbl.map_conj_mem_cComp hK (Subgroup.le_normalizer (hTH hs))
  set R₀ := T₀ ⊓ ⨅ s ∈ T, Subgroup.normalizer ((K.map (MulAut.conj s).toMonoidHom :
    Subgroup G) : Set G) with hR₀
  have hmemR : ∀ {r : G}, r ∈ R₀ ↔ r ∈ T₀ ∧ ∀ s ∈ T,
      r ∈ Subgroup.normalizer ((K.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) := by
    intro r
    simp only [hR₀, Subgroup.mem_inf, Subgroup.mem_iInf]
  have hR₀N : T₀ ≤ Subgroup.normalizer (R₀ : Set G) := by
    have key : ∀ y ∈ T₀, ∀ r ∈ R₀, y * r * y⁻¹ ∈ R₀ := by
      intro y hy r hr
      obtain ⟨hrT, hrN⟩ := hmemR.mp hr
      refine hmemR.mpr ⟨T₀.mul_mem (T₀.mul_mem hy hrT) (T₀.inv_mem hy), fun s hs => ?_⟩
      have h1 := conj_mem_normalizer_map (hrN _ (T.mul_mem (T.inv_mem (hT₀T hy)) hs)) y
      rwa [map_conj_map_conj] at h1
    intro y hy
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨key y hy r, fun h => ?_⟩
    have := key y⁻¹ (T₀.inv_mem hy) _ h
    simpa [mul_assoc] using this
  have hqKs : ∀ s ∈ T,
      q ∈ Subgroup.normalizer ((K.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G) :=
    fun s hs => le_normalizer_of_mem_cComp (hKsc s hs) hK hqK
  have hqR₀ : q ∈ Subgroup.normalizer (R₀ : Set G) := by
    have key : ∀ g : G, g ∈ Subgroup.normalizer (T₀ : Set G) → (∀ s ∈ T,
        g ∈ Subgroup.normalizer ((K.map (MulAut.conj s).toMonoidHom : Subgroup G) : Set G)) →
        ∀ r ∈ R₀, g * r * g⁻¹ ∈ R₀ := by
      intro g hg hgK r hr
      obtain ⟨hrT, hrN⟩ := hmemR.mp hr
      refine hmemR.mpr ⟨(Subgroup.mem_normalizer_iff.mp hg r).mp hrT, fun s hs => ?_⟩
      exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (hgK s hs) (hrN s hs))
        (Subgroup.inv_mem _ (hgK s hs))
    rw [Subgroup.mem_normalizer_iff]
    intro r
    refine ⟨key q hqT₀ hqKs r, fun h => ?_⟩
    have := key q⁻¹ (Subgroup.inv_mem _ hqT₀) (fun s hs => Subgroup.inv_mem _ (hqKs s hs)) _ h
    simpa [mul_assoc] using this
  have hc1 : ∀ y ∈ T₀, q * y * q⁻¹ * y⁻¹ ∈ R₀ := by
    intro y hy
    refine hmemR.mpr ⟨T₀.mul_mem ((Subgroup.mem_normalizer_iff.mp hqT₀ y).mp hy)
      (T₀.inv_mem hy), fun s hs => ?_⟩
    have hyK : y * q⁻¹ * y⁻¹ ∈ K.map (MulAut.conj y).toMonoidHom :=
      ⟨q⁻¹, K.inv_mem hqK, by simp [MulAut.conj_apply]⟩
    have h1 := le_normalizer_of_mem_cComp (hKsc s hs) (hKsc y (hT₀T hy)) hyK
    have e : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
    rw [e]
    exact Subgroup.mul_mem _ (hqKs s hs) h1
  have hR₀T : R₀ ≤ T₀ := inf_le_left
  have hR₀2 : IsPGroup 2 R₀ := hT₀2.to_le hR₀T
  have h1 := relIndex_centralizer_eq_of_commutator hq3' hT₀2 hR₀T hR₀N hqR₀ hc1
  have hR₀K : R₀ ≤ Subgroup.normalizer (K : Set G) := by
    intro r hr
    have := (hmemR.mp hr).2 1 T.one_mem
    have hK1 : K.map (MulAut.conj (1 : G)).toMonoidHom = K := by
      ext x
      simp
    rwa [hK1] at this
  have hc2 : ∀ y ∈ R₀, q * y * q⁻¹ * y⁻¹ ∈ R₀ ⊓ K := by
    intro y hy
    refine ⟨hc1 y (hR₀T hy), ?_⟩
    have h2 : y * q⁻¹ * y⁻¹ ∈ K :=
      (Subgroup.mem_normalizer_iff.mp (hR₀K hy) _).mp (K.inv_mem hqK)
    have e : q * y * q⁻¹ * y⁻¹ = q * (y * q⁻¹ * y⁻¹) := by group
    rw [e]
    exact K.mul_mem hqK h2
  have hNK : R₀ ≤ Subgroup.normalizer ((R₀ ⊓ K : Subgroup G) : Set G) := fun y hy =>
    Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hy, hR₀K hy⟩
  have hqRK : q ∈ Subgroup.normalizer ((R₀ ⊓ K : Subgroup G) : Set G) :=
    Subgroup.inf_normalizer_le_normalizer_inf ⟨hqR₀, Subgroup.le_normalizer hqK⟩
  have h2 := relIndex_centralizer_eq_of_commutator hq3' hR₀2 inf_le_left hNK hqRK hc2
  rw [h1, h2]
  exact relIndex_centralizer_le_sixteen hKs hKa hqK hq3 inf_le_right (hR₀2.to_le inf_le_left)

end CFSG.Quasithin.Vol2.Ch10.SecF.C10P4F

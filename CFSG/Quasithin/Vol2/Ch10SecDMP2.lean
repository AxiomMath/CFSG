module

public import CFSG.Quasithin.Vol2.Ch10SecDMP
public import CFSG.Quasithin.Vol2.Ch10SecDFacts211b

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecD

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped Pointwise

theorem factMaxP (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat) :
    FactMaxP := by
  intro G _ _ T L I h h3 hc t v₁ v₂ hd
  have hd' := hd
  obtain ⟨ht, htn, hv1, hv11, hv2, -⟩ := hd'
  have hTz := T_le_centralizer_z h37 h38 h h3 hc hd
  have hTP : T ≤ (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G) :=
    le_inf le_sup_right hTz
  have hfix : ∀ a ∈ L, a ∈ Subgroup.centralizer ({v₁ * v₂} : Set G) → a * v₁ * a⁻¹ = v₁ := by
    intro a haL haz
    have hav2 : a * v₂ = v₂ * a :=
      (Subgroup.mem_centralizer_iff.mp (V2_le_centralizer_L h37 h38 h ht htn hv2.1)) a haL
    have h1 := Subgroup.mem_centralizer_singleton_iff.mp haz
    have hav2' : a * v₂ * a⁻¹ = v₂ := by rw [hav2, mul_inv_cancel_right]
    calc a * v₁ * a⁻¹ = a * (v₁ * v₂) * a⁻¹ * (a * v₂ * a⁻¹)⁻¹ := by group
      _ = v₁ := by rw [h1, hav2']; group
  refine ⟨lt_of_le_of_ne inf_le_left fun heq => ?_, fun K hPK hKL => ?_⟩
  · obtain ⟨a, haL, hav⟩ := exists_mem_L_ne h3 hc hv1.1 hv11
    have haP : a ∈ (fsuL0 T L ⊔ T) ⊓ Subgroup.centralizer ({v₁ * v₂} : Set G) := by
      rw [heq]
      exact Subgroup.mem_sup_left (SecA.le_fsuL0 T L haL)
    exact hav (hfix a haL haP.2)
  obtain ⟨k, hkK, hkP⟩ := IsConcreteLE.exists_of_lt hPK
  have hk : k ∈ ((T : Set G) * (fsuL0 T L : Set G)) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right T (fsuL0 T L) (SecA.le_fsuM T L),
      sup_comm]
    exact hKL hkK
  obtain ⟨s, hs, l, hl, rfl⟩ := Set.mem_mul.mp hk
  have hsK : s ∈ K := hPK.le (hTP hs)
  have hlK : l ∈ K := by
    have := K.mul_mem (K.inv_mem hsK) hkK
    rwa [inv_mul_cancel_left] at this
  have hlz : l ∉ Subgroup.centralizer ({v₁ * v₂} : Set G) := fun hlz =>
    hkP ⟨hKL hkK, Subgroup.mul_mem _ (hTz hs) hlz⟩
  obtain ⟨hN1, hN2⟩ := fsuL0_le_normalizer_V12 h37 h38 h ht htn
  have htK : t ∈ K := hPK.le (hTP ht)
  obtain ⟨l', hl'K, hl'L0, hl'v⟩ : ∃ l' ∈ K, l' ∈ fsuL0 T L ∧ l' * v₁ * l'⁻¹ ≠ v₁ := by
    by_cases h1 : l * v₁ * l⁻¹ = v₁
    · have h2 : l * v₂ * l⁻¹ ≠ v₂ := fun h2 => hlz (by
        rw [Subgroup.mem_centralizer_singleton_iff]
        calc l * (v₁ * v₂) = (l * v₁ * l⁻¹) * (l * v₂ * l⁻¹) * l := by group
          _ = v₁ * v₂ * l := by rw [h1, h2])
      have hv12 : t * v₂ * t⁻¹ = v₁ := conj_v2 h37 h38 h h3 hc hd
      refine ⟨t * l * t⁻¹, K.mul_mem (K.mul_mem htK hlK) (K.inv_mem htK),
        (Subgroup.mem_normalizer_iff.mp (SecA.le_fsuM T L ht) l).mp hl, fun h3' => h2 ?_⟩
      calc l * v₂ * l⁻¹ = t⁻¹ * ((t * l * t⁻¹) * (t * v₂ * t⁻¹) * (t * l * t⁻¹)⁻¹) * t := by
            group
        _ = t⁻¹ * v₁ * t := by rw [hv12, h3']
        _ = v₂ := by rw [← hv12]; group
    · exact ⟨l, hlK, hl, h1⟩
  obtain ⟨g, hgK, hgL, hgv⟩ := exists_conj_ne h37 h38 h h3 hc hd hPK.le hl'K hl'L0 hl'v
  have hLK := L_le_of_mem_ne h37 h38 h h3 hc hd hPK.le hgK hgL hgv
  have hL0K : fsuL0 T L ≤ K := conjClosure_le fun s hs a ha =>
    K.mul_mem (K.mul_mem (hPK.le (hTP hs)) (hLK ha)) (K.inv_mem (hPK.le (hTP hs)))
  exact le_antisymm hKL (sup_le hL0K (hTP.trans hPK.le))

end CFSG.Quasithin.Vol2.Ch10.SecD

module

public import CFSG.Quasithin.Vol2.Ch11SecSX1b

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13 SecA

variable {G : Type} [Group G] [Finite G]

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

omit [Finite G] in
theorem inf_le_normalizer_map_conj' {A : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G))
    (hA : T ⊓ K ≤ Subgroup.normalizer (A : Set G)) :
    T ⊓ K ≤ Subgroup.normalizer (A.map (MulAut.conj t : G →* G) : Set G) := by
  intro s hs
  have hs' : t⁻¹ * s * t ∈ T ⊓ K := by
    have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ ht) s).mp hs
    simpa [mul_assoc] using this
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
  have heq : (MulAut.conj s : G →* G).comp (MulAut.conj t : G →* G) =
      (MulAut.conj t : G →* G).comp (MulAut.conj (t⁻¹ * s * t) : G →* G) := by
    ext x
    simp [mul_assoc]
  rw [heq, ← Subgroup.map_map, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hs')]

theorem mem_normalizer_k0Of (h : StarHyp G T L I V₁ V₂ X K)
    (hP : ParData T K (LOf L V₁) P₁ P₂) {t : G} (htK : t ∈ Subgroup.normalizer (K : Set G))
    (htL : t ∈ Subgroup.normalizer (LOf L V₁ : Set G))
    (htS : t ∈ Subgroup.normalizer ((T ⊓ K : Subgroup G) : Set G)) :
    t ∈ Subgroup.normalizer (k0Of K P₂ : Set G) := by
  set c := (MulAut.conj t : G →* G) with hc
  have hK0K := k0Of_le K P₂
  have hK0p := k0Of_perfect K P₂
  have hK0bar := modO2Image_k0Of K hP.c₂.2.1
  have hK0n := hP.inf_le_normalizer_k0Of
  have hKc : K.map c = K := Subgroup.mem_normalizer_iff_map_conj_eq.mp htK
  have hK0tK : (k0Of K P₂).map c ≤ K := (Subgroup.map_mono hK0K).trans hKc.le
  have hK0tp : ⁅(k0Of K P₂).map c, (k0Of K P₂).map c⁆ = (k0Of K P₂).map c := by
    rw [← Subgroup.map_commutator, hK0p]
  have hK0tne : (k0Of K P₂).map c ≠ ⊥ := by
    rw [Ne, Subgroup.map_eq_bot_iff_of_injective _ (MulAut.conj t).injective]
    exact hP.k0Of_ne_bot
  have hK0tn := inf_le_normalizer_map_conj' htS hK0n
  have hQ := fun {A : Subgroup G} (hA : T ⊓ K ≤ Subgroup.normalizer (A : Set G)) =>
    (h.pCoreOf_le_inf.trans hA)
  have hinj : ∀ B : Subgroup G, B ≤ K → t ∈ Subgroup.normalizer (B : Set G) →
      modO2Image K ((k0Of K P₂).map c) = modO2Image K B →
        k0Of K P₂ ⊔ pCoreOf 2 K = B ⊔ pCoreOf 2 K := by
    intro B hBK htB heq
    have h1 := sup_eq_of_modO2Image_eq hK0tK hBK heq
    rw [← map_conj_sup_pCoreOf htK] at h1
    have h2 : (B ⊔ pCoreOf 2 K).map c = B ⊔ pCoreOf 2 K := by
      rw [map_conj_sup_pCoreOf htK, Subgroup.mem_normalizer_iff_map_conj_eq.mp htB]
    rw [← h2] at h1
    exact Subgroup.map_injective (MulAut.conj t).injective h1
  rcases hP.cases _ (modO2Image_ne_bot hK0tK hK0tp hK0tne) (modO2Image_perfect hK0tK hK0tp)
      (modO2Image_le_normalizer hK0tn) with h1 | h1 | h1
  · exfalso
    have := hinj _ h.L₁_le_K htL (h1.trans hP.l₁.symm)
    have h3 := congrArg (modO2Image K) this
    rw [modO2Image_sup_pCoreOf hK0K, modO2Image_sup_pCoreOf h.L₁_le_K, hK0bar, hP.l₁] at h3
    exact hP.ne h3.symm
  · rw [Subgroup.mem_normalizer_iff_map_conj_eq]
    have h2 := sup_eq_of_modO2Image_eq hK0tK hK0K (h1.trans hK0bar.symm)
    calc (k0Of K P₂).map c = perfectCore ((k0Of K P₂).map c ⊔ pCoreOf 2 K) :=
          (perfectCore_sup_eq hK0tp (isSolvable_pCoreOf_two K) (hQ hK0tn)).symm
      _ = perfectCore (k0Of K P₂ ⊔ pCoreOf 2 K) := by rw [h2]
      _ = k0Of K P₂ := perfectCore_sup_eq hK0p (isSolvable_pCoreOf_two K) (hQ hK0n)
  · exfalso
    have := hinj _ le_rfl htK (h1.trans (modO2Image_self K).symm)
    have h3 := congrArg (modO2Image K) this
    rw [modO2Image_sup_pCoreOf hK0K, modO2Image_sup_pCoreOf le_rfl, hK0bar,
      modO2Image_self] at h3
    exact hP.ne_top₂ h3

theorem cartan_le_normalizer_k0Of (hN : NatFacts) (h1102 : Stmt11_0_2)
    (h : StarHyp G T L I V₁ V₂ X K) (hP : ParData T K (LOf L V₁) P₁ P₂) :
    X ≤ Subgroup.normalizer (k0Of K P₂ : Set G) := fun _ hx =>
  h.mem_normalizer_k0Of hP (h.cartan_le_normalizer_K hN h1102 hx)
    (cartan_le_normalizer_lOf hN h1102 h.hyp (Or.inl rfl) h.v₁ h.cartan hx)
    (h.cartan_le_normalizer_inf hN h1102 hP hx)

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS

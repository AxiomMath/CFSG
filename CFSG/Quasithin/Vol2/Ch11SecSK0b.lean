module

public import CFSG.Quasithin.Vol2.Ch11SecSK0
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Quasithin.Vol2.Ch11.SecS

open CFSG.Open CFSG.Blueprint CFSG.Quasithin.H13

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem pCoreOf_le_self (K : Subgroup G) : pCoreOf 2 K ≤ K := CFSG.openPCoreOf_le 2 K

omit [Finite G] in
theorem modO2Image_pCoreOf (K : Subgroup G) : modO2Image K (pCoreOf 2 K) = ⊥ := by
  unfold modO2Image
  have hc : (pCoreOf 2 K).subgroupOf K = CFSG.pCore 2 ↥K := by
    rw [pCoreOf_two_eq_map]
    exact Subgroup.comap_map_eq_self_of_injective K.subtype_injective _
  rw [hc, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']

omit [Finite G] in
theorem modO2Image_sup {K A B : Subgroup G} (hA : A ≤ K) (hB : B ≤ K) :
    modO2Image K (A ⊔ B) = modO2Image K A ⊔ modO2Image K B := by
  unfold modO2Image
  rw [Subgroup.subgroupOf_sup hA hB, Subgroup.map_sup]

omit [Finite G] in
theorem modO2Image_sup_pCoreOf {K A : Subgroup G} (hA : A ≤ K) :
    modO2Image K (A ⊔ pCoreOf 2 K) = modO2Image K A := by
  rw [modO2Image_sup hA (pCoreOf_le_self K), modO2Image_pCoreOf, sup_bot_eq]

omit [Finite G] in
theorem map_conj_sup_pCoreOf {K A : Subgroup G} {t : G}
    (ht : t ∈ Subgroup.normalizer (K : Set G)) :
    (A ⊔ pCoreOf 2 K).map (MulAut.conj t : G →* G) =
      A.map (MulAut.conj t : G →* G) ⊔ pCoreOf 2 K := by
  rw [Subgroup.map_sup, Subgroup.mem_normalizer_iff_map_conj_eq.mp
    (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 K ht)]

namespace ParData

variable {T L V₁ K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem k0Of_ne_bot (hP : ParData T K (LOf L V₁) P₁ P₂) : k0Of K P₂ ≠ ⊥ := by
  intro hbot
  have := modO2Image_k0Of K hP.c₂.2.1
  rw [hbot] at this
  apply hP.c₂.1
  rw [← this]
  unfold modO2Image
  simp

omit [Finite G] in
theorem inf_le_normalizer_k0Of (hP : ParData T K (LOf L V₁) P₁ P₂) :
    T ⊓ K ≤ Subgroup.normalizer (k0Of K P₂ : Set G) :=
  le_normalizer_k0Of inf_le_right hP.n₂

end ParData

namespace StarHyp

variable {T L I V₁ V₂ X K : Subgroup G} {P₁ P₂ : Subgroup (↥K ⧸ CFSG.pCore 2 ↥K)}

theorem inf_le_normalizer_map_conj (h : StarHyp G T L I V₁ V₂ X K) {A : Subgroup G} {t : G}
    (ht : t ∈ T) (hA : T ⊓ K ≤ Subgroup.normalizer (A : Set G)) :
    T ⊓ K ≤ Subgroup.normalizer (A.map (MulAut.conj t : G →* G) : Set G) := by
  intro s hs
  have hs' : t⁻¹ * s * t ∈ T ⊓ K := by
    refine ⟨T.mul_mem (T.mul_mem (T.inv_mem ht) hs.1) ht, ?_⟩
    have := (Subgroup.mem_normalizer_iff.mp (h.T_le_normalizer_K (T.inv_mem ht)) s).mp hs.2
    simpa [mul_assoc] using this
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Subgroup.map_map]
  have heq : (MulAut.conj s : G →* G).comp (MulAut.conj t : G →* G) =
      (MulAut.conj t : G →* G).comp (MulAut.conj (t⁻¹ * s * t) : G →* G) := by
    ext x
    simp [mul_assoc]
  rw [heq, ← Subgroup.map_map, Subgroup.mem_normalizer_iff_map_conj_eq.mp (hA hs')]

theorem T_le_normalizer_k0Of (h : StarHyp G T L I V₁ V₂ X K)
    (hP : ParData T K (LOf L V₁) P₁ P₂) : T ≤ Subgroup.normalizer (k0Of K P₂ : Set G) := by
  intro t ht
  set c := (MulAut.conj t : G →* G) with hc
  have htK := h.T_le_normalizer_K ht
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
  have hK0tn := h.inf_le_normalizer_map_conj ht hK0n
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
    have := hinj _ h.L₁_le_K (h.T_le_normalizer_L₁ ht) (h1.trans hP.l₁.symm)
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

end StarHyp

end CFSG.Quasithin.Vol2.Ch11.SecS

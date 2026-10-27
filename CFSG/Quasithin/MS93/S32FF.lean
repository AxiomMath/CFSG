module

public import CFSG.Quasithin.MS93.S32Dict

public section

namespace CFSG.Quasithin.MS93

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86.Univ

variable {G : Type} [Group G] [Finite G] {M T L : Subgroup G}

omit [Finite G] in
theorem imM_relIndex (hTM : T ≤ M) (K : Subgroup G) {K' : Subgroup G} (hK' : K' ≤ M) :
    (imM hTM K).relIndex (imM hTM K') = K.relIndex K' := by
  rw [imM, imM, Subgroup.relIndex_map_map_of_injective _ _ (puAmalgam hTM).ofA_injective,
    Subgroup.relIndex_subgroupOf hK']

omit [Finite G] in
theorem pull_offender (hTM : T ≤ M) {E' : Subgroup (puAmalgam hTM).Universal}
    {Q W : Subgroup G} (hWM : W ≤ M) (hET : E' ≤ imM hTM T)
    (hE : IsElemAbelian 2 E') (hEQ : ¬ E' ≤ imM hTM Q)
    (hrel : (Subgroup.centralizer (E' : Set (puAmalgam hTM).Universal)).relIndex (imM hTM W) ≤
      (imM hTM Q).relIndex E') :
    ∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian 2 E ∧ ¬ E ≤ Q ∧
      (Subgroup.centralizer (E : Set G)).relIndex W ≤ Q.relIndex E := by
  set f := (puAmalgam hTM).ofA
  set E : Subgroup G := (E'.comap f).map M.subtype with hEdef
  have hEM : E ≤ M := Subgroup.map_subtype_le _
  have hrange : E' ≤ f.range := hET.trans (Subgroup.map_le_range _ _)
  have himE : imM hTM E = E' := by
    rw [hEdef, imM_map_subtype, Subgroup.map_comap_eq, inf_eq_right.2 hrange]
  have hmem : ∀ x ∈ E, ∃ a : ↥M, (a : G) = x ∧ f a ∈ E' := by
    rintro x ⟨a, ha, rfl⟩
    exact ⟨a, rfl, ha⟩
  refine ⟨E, (imM_le_imM_iff hTM hEM).mp (himE ▸ hET), ⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩,
    fun hle => hEQ (himE ▸ imM_mono hTM hle), ?_⟩
  · obtain ⟨a, ha, haE⟩ := hmem x x.2
    obtain ⟨b, hb, hbE⟩ := hmem y y.2
    have hcomm : f a * f b = f b * f a := by
      have := hE.1.1.1 ⟨f a, haE⟩ ⟨f b, hbE⟩
      exact congrArg Subtype.val this
    rw [← map_mul, ← map_mul] at hcomm
    have := (puAmalgam hTM).ofA_injective hcomm
    apply Subtype.ext
    show (x : G) * y = y * x
    rw [← ha, ← hb]
    exact congrArg Subtype.val this
  · obtain ⟨a, rfl, haE⟩ := hmem x hx
    have h1 : f (a ^ 2) = 1 := by rw [map_pow]; exact hE.2 _ haE
    have h2 : a ^ 2 = 1 := (puAmalgam hTM).ofA_injective (h1.trans (map_one f).symm)
    exact congrArg Subtype.val h2
  · have hc : Subgroup.centralizer (E' : Set (puAmalgam hTM).Universal) ⊓ imM hTM W =
        imM hTM (W ⊓ Subgroup.centralizer (E : Set G)) := by
      rw [imM_inf_centralizer hTM W hEM, himE, inf_comm]
    rw [← Subgroup.inf_relIndex_right, hc, imM_relIndex hTM _ hWM, ← himE,
      imM_relIndex hTM _ hEM] at hrel
    rwa [inf_comm, Subgroup.inf_relIndex_right] at hrel

theorem PUHyp.exists_offender (h : PUHyp M T L) :
    (∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian 2 E ∧ ¬ E ≤ pCoreOf 2 M ∧
      (Subgroup.centralizer (E : Set G)).relIndex (Z0q M T) ≤ (pCoreOf 2 M).relIndex E) ∧
    (∃ E : Subgroup G, E ≤ T ∧ IsElemAbelian 2 E ∧ ¬ E ≤ pCoreOf 2 M ∧
      (Subgroup.centralizer (E : Set G)).relIndex (Xq M) ≤ (pCoreOf 2 M).relIndex E) := by
  obtain ⟨⟨E₁, hE₁T, hE₁, hE₁Q, hE₁r⟩, ⟨E₂, hE₂T, hE₂, hE₂Q, hE₂r⟩⟩ :=
    ms22_vi (puAmalgam h.le) h.hyp20 h.critDist_pos h.centHyp (PU.isMVtx_baseA _)
      (adj_baseA_baseB _)
  rw [puAmalgam.qv_baseB] at hE₁T hE₂T
  rw [puAmalgam.qv_baseA_eq_pCoreOf h.le h.isPGroup h.pCore_le] at hE₁Q hE₁r hE₂Q hE₂r
  rw [puAmalgam.zm_baseA] at hE₁r
  rw [puAmalgam.xm_baseA, h.normalCoreIn_eq] at hE₂r
  exact ⟨pull_offender h.le (Z0q_le M T) hE₁T hE₁ hE₁Q hE₁r,
    pull_offender h.le (Xq_le M) hE₂T hE₂ hE₂Q hE₂r⟩

theorem PUHyp.isFFModule_of_le_Z0q (h : PUHyp M T L) {W : Subgroup G} (hs : IsSecW M L W)
    (hWZ : W ≤ Z0q M T) : IsFFModule (autI (hs.isElemAbelian h) M) := by
  obtain ⟨⟨E, hET, hE, hEQ, hrel⟩, -⟩ := h.exists_offender
  exact hs.isFFModule h hET hE hEQ hWZ hrel

theorem PUHyp.isFFModule_of_le_Xq (h : PUHyp M T L) {W : Subgroup G} (hs : IsSecW M L W) :
    IsFFModule (autI (hs.isElemAbelian h) M) := by
  obtain ⟨-, ⟨E, hET, hE, hEQ, hrel⟩⟩ := h.exists_offender
  exact hs.isFFModule h hET hE hEQ hs.le_Xq hrel

end CFSG.Quasithin.MS93

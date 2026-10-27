module

public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovS7Blk
public import CFSG.Quasithin.Vol2.Ch3Sec1L319Seven

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Ch3z RegularWreathProduct

section Chief

variable {G : Type} [Group G] [Finite G] {H T M₂ U A L N : Subgroup G}

theorem Setting.cover_dichotomy_cv (hB69 : B69Struct) (hB1 : B69One) (h : Setting H T M₂ U A)
    {L₀ N₀ : Subgroup G} (hstep₀ : IsChiefStep H U L₀ N₀) (hnc₀ : ¬ IsCentralStep H L₀ N₀)
    {χ₀ : ↥H →* ℤˣ} (hχC : ∀ g : ↥H, (g : G) ∈ centralizerMod L₀ H N₀ → χ₀ g = 1)
    {a : G} (haA : a ∈ A) (haH : a ∈ H) (hχa : χ₀ ⟨a, haH⟩ = -1)
    (hstep : IsChiefStep H U L N) (hnc : ¬ IsCentralStep H L N)
    {V : Subgroup G} (hAV : A ≤ Subgroup.centralizer (V : Set G))
    (hMV : ∀ g ∈ M₂, g ∈ Subgroup.normalizer (V : Set G))
    (hg5 : ∃ g : ↥H, orderOf (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) g) = 5) :
    (∀ g : ↥H, chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) g = 1 ↔ (g : G) ∈ centralizerMod L H N) ∧
    ((∃ θ : ↥H →* Equiv.Perm (Fin 5), Function.Surjective θ ∧
        (∀ g : ↥H, θ g = 1 ↔ (g : G) ∈ centralizerMod L H N) ∧
        ∃ d : ↥H, (d : G) ∈ M₂ ∧ (d : G) ∈ Subgroup.centralizer (V : Set G) ∧ orderOf (θ d) = 3) ∨
    (∃ d t : ↥H, (d : G) ∈ M₂ ∧ (d : G) ∈ Subgroup.centralizer (V : Set G) ∧ (t : G) ∈ T ∧
        orderOf (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) d) = 3 ∧
        Commute (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) d)
          (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) (t * d * t⁻¹)) ∧
        chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) (t * d * t⁻¹) ∉
          Subgroup.zpowers (chiefPsi (Setting.hHL hstep) (Setting.hHN hstep) d))) := by
  obtain ⟨g, hg5⟩ := hg5
  have hHL := Setting.hHL hstep
  have hHN := Setting.hHN hstep
  have hE := h.hE hstep
  have hNL := h.hNL hstep
  let _ : CommGroup ↥(chiefMod L N) := chiefCG hE
  obtain ⟨𝓗, hctx⟩ := h.blkCtx hB69 hstep hnc
  have hsym := h.symBlk_all hB1 hstep₀ hnc₀ hχC haA haH hχa hstep hnc hctx
  have hstrong := h.noStrong hB1 hstep hnc
  obtain ⟨hAe, hA1, hoff⟩ := h.offender hstep hnc
  set D : Subgroup (MulAut ↥(chiefMod L N)) :=
    chiefImg hHL hHN (M₂ ⊓ Subgroup.centralizer (V : Set G)) with hD
  have hAT : chiefImg hHL hHN A ≤ chiefImg hHL hHN T := chiefImg_mono' hHL hHN h.AT.1
  have hAD : chiefImg hHL hHN A ≤ D :=
    chiefImg_mono' hHL hHN (le_inf (h.AT.1.trans h.mp.le) hAV)
  have hDM : ∀ x ∈ chiefImg hHL hHN M₂, ∀ d ∈ D, x * d * x⁻¹ ∈ D := by
    intro x hx d hd
    obtain ⟨g₀, hg₀, rfl⟩ := Subgroup.mem_map.mp hx
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.mp hd
    have hg₀' : (g₀ : G) ∈ M₂ := Subgroup.mem_subgroupOf.mp hg₀
    have hd₀' := Subgroup.mem_subgroupOf.mp hd₀
    refine Subgroup.mem_map.mpr ⟨g₀ * d₀ * g₀⁻¹, Subgroup.mem_subgroupOf.mpr ?_, by simp⟩
    refine ⟨M₂.mul_mem (M₂.mul_mem hg₀' hd₀'.1) (M₂.inv_mem hg₀'), ?_⟩
    exact conj_mem_centralizer (hMV _ hg₀') hd₀'.2
  have h5 : ∃ x ∈ ffJ (chiefAut H L N), orderOf x = 5 :=
    ⟨chiefPsi hHL hHN g, Ch3w.odd_mem_ffJ hctx (chiefPsi_mem hHL hHN g) (by rw [hg5]; decide), hg5⟩
  have key := BlkCtx.cover_dichotomy_cv hctx (h.rank hstep) hsym hstrong hAT hAe hA1 hoff hAD hDM h5
  have hDlift : ∀ x ∈ D, ∃ d : ↥H, (d : G) ∈ M₂ ∧ (d : G) ∈ Subgroup.centralizer (V : Set G) ∧
      chiefPsi hHL hHN d = x := by
    intro x hx
    obtain ⟨d₀, hd₀, rfl⟩ := Subgroup.mem_map.mp hx
    have hd₀' := Subgroup.mem_subgroupOf.mp hd₀
    exact ⟨d₀, hd₀'.1, hd₀'.2, rfl⟩
  have hkerψ : ∀ g : ↥H, chiefPsi hHL hHN g = 1 ↔ (g : G) ∈ centralizerMod L H N := fun g =>
    ⟨fun hh => (chiefHom_eq_one_iff hHL hHN hNL g).mp (Subtype.ext hh),
      fun hh => congrArg Subtype.val ((chiefHom_eq_one_iff hHL hHN hNL g).mpr hh)⟩
  refine ⟨hkerψ, ?_⟩
  rcases key with ⟨θX, x, hxX, hxD, hx3⟩ | ⟨x, t, hxX, hxD, hx3, htT, hcomm, hnot⟩
  · left
    obtain ⟨d, hdM, hdC, hdx⟩ := hDlift x hxD
    refine ⟨θX.toMonoidHom.comp (chiefHom hHL hHN), ?_, ?_, d, hdM, hdC, ?_⟩
    · exact θX.surjective.comp (chiefHom_surjective hHL hHN)
    · intro g'
      change θX (chiefHom hHL hHN g') = 1 ↔ _
      rw [MulEquiv.map_eq_one_iff]
      exact chiefHom_eq_one_iff hHL hHN hNL g'
    · change orderOf (θX (chiefHom hHL hHN d)) = 3
      rw [MulEquiv.orderOf_eq]
      have : (chiefHom hHL hHN d : ↥(chiefAut H L N)) = ⟨x, hxX⟩ := Subtype.ext hdx
      rw [this, Subgroup.orderOf_mk]
      exact hx3
  · right
    obtain ⟨d, hdM, hdC, hdx⟩ := hDlift x hxD
    obtain ⟨t₀, ht₀, ht₀x⟩ := Subgroup.mem_map.mp htT
    have ht₀T : (t₀ : G) ∈ T := Subgroup.mem_subgroupOf.mp ht₀
    have hconj : chiefPsi hHL hHN (t₀ * d * t₀⁻¹) = t * x * t⁻¹ := by
      rw [map_mul, map_mul, map_inv, ht₀x, hdx]
    refine ⟨d, t₀, hdM, hdC, ht₀T, by rw [hdx]; exact hx3, ?_, ?_⟩
    · rw [hconj, hdx]
      exact hcomm
    · rw [hconj, hdx]
      exact hnot

end Chief

end CFSG.Quasithin.H13.L319

module

public import CFSG.Quasithin.Vol2.Ch3Sec1Aux
public import CFSG.Quasithin.Vol2.Ch3Sec1Inputs
public import CFSG.Quasithin.Vol2.Ch3Sec1Thm311

public section

open CFSG.QuasithinUnique (quasithinIsQTKECat)

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits

variable {G : Type} [Group G] [Finite G] {T M M₀ H V : Subgroup G}

omit [Finite G] in
theorem le_normalizer_of_le_centralizer {X R : Subgroup G}
    (h : R ≤ Subgroup.centralizer (X : Set G)) : X ≤ Subgroup.normalizer (R : Set G) := by
  intro x hx
  refine B6.mem_normalizer_of_forall_mem (fun y hy => ?_) (fun y hy => ?_)
  · have e : x * y = y * x := Subgroup.mem_centralizer_iff.mp (h hy) x hx
    have : x * y * x⁻¹ = y := by rw [e, mul_inv_cancel_right]
    rw [this]; exact hy
  · have e : x⁻¹ * y = y * x⁻¹ := Subgroup.mem_centralizer_iff.mp (h hy) x⁻¹ (X.inv_mem hx)
    have : x⁻¹ * y * x = y := by rw [e, inv_mul_cancel_right]
    rw [this]; exact hy

theorem lemma317 (hC58 : TheoremC58) (h317 : AS317Sylow) (hs : IsSimpleGroup G)
    (hnab : ∃ a b : G, a * b ≠ b * a) (hK : quasithinIsQTKECat G) (hT : quasithinIsSylowTwo T)
    (hM : InM T M) (h : Hyp315 T M M₀ H V) (hJ : thompsonJ T ≤ pCoreOf 2 M₀) :
    (quasithinOmegaOneCenter T ≤ centerOf H ∧ centerOf M₀ = ⊥) ∨
      ∃ R₀ : Subgroup G, R₀ ≠ ⊥ ∧ R₀ ≤ pCoreOf 2 M₀ ∧
        M₀ ⊔ H ≤ Subgroup.normalizer (R₀ : Set G) := by
  have hinH : InH T M₀ := h.inH_M₀ hT hM
  have hRT : pCoreOf 2 M₀ ≤ T := h.pCoreOf_le_T
  have hT0 : T ≠ ⊥ := fun hb => hinH.2 (le_bot_iff.mp (hb ▸ hRT))
  have hJne : thompsonJ T ≠ ⊥ := thompsonJ_ne_bot_of_isPGroup hT.1 hT0
  have hJR : thompsonJ (pCoreOf 2 M₀) = thompsonJ T := B6.thompsonJ_eq_of_le hJ hRT
  have hM₀J : M₀ ≤ Subgroup.normalizer (thompsonJ T : Set G) := by
    rw [← hJR]
    exact (le_normalizer_pCoreOf 2 M₀).trans (normalizer_le_normalizer_thompsonJ _)
  by_cases hJn : H ≤ Subgroup.normalizer (thompsonJ T : Set G)
  ·
    exact Or.inr ⟨thompsonJ T, hJne, hJ, sup_le hM₀J hJn⟩
  by_cases hZ : quasithinOmegaOneCenter T ≤ centerOf H
  · by_cases hZ0 : centerOf M₀ = ⊥
    · exact Or.inl ⟨hZ, hZ0⟩
    ·
      right
      have hCT : CharTwo M₀ := charTwo_of_inH' hK hT hinH
      have hZM : centerOf M₀ ≤ pCoreOf 2 M₀ := fun x hx =>
        hCT ⟨hx.1, Subgroup.mem_centralizer_iff.mpr fun g hg =>
          Subgroup.mem_centralizer_iff.mp hx.2 g ((pCoreOf_le 2 M₀) hg)⟩
      obtain ⟨y, hyZ, hy⟩ := exists_mem_orderOf_two_of_isPGroup
        ((pCoreOf_isPGroup 2 M₀).to_le hZM) hZ0
      have hyR₀ : y ∈ omegaOneCenterOf M₀ :=
        Subgroup.subset_closure ⟨hyZ, by rw [← hy]; exact pow_orderOf_eq_one y⟩
      have hR₀ne : omegaOneCenterOf M₀ ≠ ⊥ := by
        intro hb
        rw [hb, Subgroup.mem_bot] at hyR₀
        rw [hyR₀, orderOf_one] at hy
        omega
      have hR₀R : omegaOneCenterOf M₀ ≤ pCoreOf 2 M₀ := by
        refine (Subgroup.closure_le _).mpr fun x hx => hZM hx.1
      have hR₀Z : omegaOneCenterOf M₀ ≤ quasithinOmegaOneCenter T := by
        refine (Subgroup.closure_le _).mpr fun x hx => Subgroup.subset_closure ?_
        have hxT : x ∈ T := hRT (hZM hx.1)
        exact ⟨⟨hxT, Subgroup.mem_centralizer_iff.mpr fun t ht =>
          Subgroup.mem_centralizer_iff.mp hx.1.2 t (h.T_le ht)⟩, hx.2⟩
      have hR₀C : omegaOneCenterOf M₀ ≤ Subgroup.centralizer (M₀ : Set G) :=
        (Subgroup.closure_le _).mpr fun x hx => hx.1.2
      refine ⟨omegaOneCenterOf M₀, hR₀ne, hR₀R, sup_le ?_ ?_⟩
      · exact le_normalizer_of_le_centralizer hR₀C
      · exact le_normalizer_of_le_centralizer fun x hx => (hZ (hR₀Z hx)).2
  ·
    exact Or.inr (h.toHyp315Base.exists_normal_of_sylow hC58 hs hnab hK hT hM
      (h317 G T M M₀ H V hs hnab hK hT hM h hJ hJn hZ))

end CFSG.Quasithin

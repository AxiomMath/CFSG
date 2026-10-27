module

public import CFSG.Quasithin.EmptyFaithful.S143WGeo
public import CFSG.Quasithin.Background.G11Defs
public import CFSG.Quasithin.EmptyFaithful.S143Five
public import CFSG.Quasithin.Recognition.CertSzZero

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.G11
open scoped commutatorElement

namespace S143W

variable {G : Type} [Group G] [Finite G] {T M : Subgroup G}

section Aux

variable (h : Hyp1281Two G T M (yOfL22 T M)) (hU : ¬ IsMulCommutative ↥(uOfL22 T M)) {g : G}
  (hg : GoodElt128 T (yOfL22 T M) g) (D : HatModel T M)

include h hU hg in
theorem exists_y₀ (hlt : quasithinOmegaOneCenter T < centerOf (uOfL22 T M)) :
    ∃ y : G, y ∈ rconj (centerOf (uOfL22 T M)) g ∧
      ∃ hyH : y ∈ mcOf T, S143V.rhoH h D ⟨y, hyH⟩ ≠ 1 := by
  have hlt' := h.lemma_12_8_13_four hU hg hlt
  obtain ⟨-, y, hy, hyn⟩ := IsConcreteLE.lt_iff_le_and_exists.mp hlt'
  have hyT : y ∈ T := rconj_centerOf_le_T h hU hg hy
  have hyH : y ∈ mcOf T := h.almostSpecialHyp_g1.T_le_H hyT
  refine ⟨y, hy, hyH, fun h1 => hyn ?_⟩
  have hyN : y ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 hyH
  have h2 : D.rho ⟨y, hyN⟩ = 1 := by
    rw [← S143V.rhoH_apply h D ⟨y, hyH⟩ hyN]
    exact h1
  exact ⟨hy, normalizer_le_normalizer_centerOf _ hyN, (D.rho_eq_one_iff ⟨y, hyN⟩).mp h2⟩

include h hU hg in
theorem exists_commutator_vec (Tm : TildeModel T M) {a : G} (haV : a ∈ VZ T M)
    (haZ : a ∉ quasithinOmegaOneCenter T)
    (hperp : ∀ γ ∈ D.img (mcOf T), (∀ x : D.V, D.B x (D.π a) = 0 → γ x = x) → γ = 1)
    (hlt : quasithinOmegaOneCenter T < centerOf (uOfL22 T M))
    {z : G} (hzZ : z ∈ quasithinOmegaOneCenter T) (hz1 : z ≠ 1) (hzz : z * z = 1)
    (hall : ∀ w ∈ quasithinOmegaOneCenter T, w = 1 ∨ w = z) :
    ∃ (y : G) (hyH : y ∈ mcOf T), y ∈ rconj (centerOf (uOfL22 T M)) g ∧
      ∃ (w : ↥(uOfL22 T M)) (hzgU : g⁻¹ * z * g ∈ uOfL22 T M),
        Tm.ρ ⟨y, hyH⟩ (Tm.c w) - Tm.c w = Tm.c ⟨g⁻¹ * z * g, hzgU⟩ := by
  obtain ⟨y, hyX, hyH, hy1⟩ := exists_y₀ h hU hg D hlt
  have hyN : y ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 hyH
  have hyΓ : S143V.rhoH h D ⟨y, hyH⟩ ∈ D.img (mcOf T) := by
    rw [← S143V.range_rhoH h D]
    exact ⟨_, rfl⟩
  have hnot : ¬ ∀ x : D.V, D.B x (D.π a) = 0 → S143V.rhoH h D ⟨y, hyH⟩ x = x :=
    fun hall' => hy1 (hperp _ hyΓ hall')
  push Not at hnot
  obtain ⟨xh, hxperp, hxne⟩ := hnot
  obtain ⟨w, hwU, rfl⟩ := D.π_surj xh
  have haU : a ∈ uOfL22 T M := Hyp1281Two.VZ_le_uOfL22 T M haV
  have hwW : w ∈ Hyp1281Two.wOfU T M := by
    refine ⟨hwU, Subgroup.mem_centralizer_iff.mpr fun v hv => ?_⟩
    have hzc : w * z = z * w :=
      Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hzZ).2 w hwU
    have hac : w * a = a * w := by
      have h1 := (D.B_spec w hwU a haU).mp hxperp
      calc w * a = (w * a * w⁻¹ * a⁻¹) * a * w := by group
        _ = a * w := by rw [h1]; group
    rcases h.VZ_cases hzZ hz1 haV haZ v hv with rfl | rfl | rfl | rfl
    · simp
    · exact hzc.symm
    · exact hac.symm
    · calc (z * a) * w = z * (a * w) := by group
        _ = z * (w * a) := by rw [hac]
        _ = (z * w) * a := by group
        _ = (w * z) * a := by rw [hzc]
        _ = w * (z * a) := by group
  have hcw : ⁅w, y⁆ ∈ rconj (centerOf (uOfL22 T M)) g ⊓ uOfL22 T M :=
    h.commutator_wOfU_rconj_centerOf_le hU hg (Subgroup.commutator_mem_commutator hwW hyX)
  obtain ⟨-, -, -, e4, -, -⟩ := h.lemma_12_8_10_six hU hg
  have hV1g : ⁅w, y⁆ ∈ rconj (quasithinOmegaOneCenter T) g := by
    have := hcw
    rw [e4, h.centerOf_inf_rconj_centerOf_eq_bot hU hg, bot_sup_eq] at this
    exact this
  have hmem : g * ⁅w, y⁆ * g⁻¹ ∈ quasithinOmegaOneCenter T := mem_rconj.mp hV1g
  have hcomm_def : ⁅w, y⁆ = w * y * w⁻¹ * y⁻¹ := commutatorElement_def w y
  rcases hall _ hmem with h0 | h0
  · exfalso
    apply hxne
    have h1 : ⁅w, y⁆ = 1 := by
      have : g * ⁅w, y⁆ * g⁻¹ = 1 := h0
      calc ⁅w, y⁆ = g⁻¹ * (g * ⁅w, y⁆ * g⁻¹) * g := by group
        _ = 1 := by rw [this]; group
    have h2 : y * w * y⁻¹ = w := by
      rw [hcomm_def] at h1
      calc y * w * y⁻¹ = (w * y * w⁻¹ * y⁻¹)⁻¹ * w := by group
        _ = w := by rw [h1]; group
    rw [S143V.rhoH_apply h D ⟨y, hyH⟩ hyN, D.rho_π ⟨y, hyN⟩ hwU]
    show D.π (y * w * y⁻¹) = D.π w
    rw [h2]
  · have hzg : ⁅w, y⁆ = g⁻¹ * z * g := by
      calc ⁅w, y⁆ = g⁻¹ * (g * ⁅w, y⁆ * g⁻¹) * g := by group
        _ = g⁻¹ * z * g := by rw [h0]
    have hzgU : g⁻¹ * z * g ∈ uOfL22 T M := hzg ▸ hcw.2
    refine ⟨y, hyH, hyX, ⟨w, hwU⟩, hzgU, ?_⟩
    have hywy : y * w * y⁻¹ = (g⁻¹ * z * g) * w := by
      have hzg2 : (g⁻¹ * z * g) * (g⁻¹ * z * g) = 1 := by
        calc (g⁻¹ * z * g) * (g⁻¹ * z * g) = g⁻¹ * (z * z) * g := by group
          _ = 1 := by rw [hzz]; group
      rw [hcomm_def] at hzg
      calc y * w * y⁻¹ = (w * y * w⁻¹ * y⁻¹)⁻¹ * w := by group
        _ = (g⁻¹ * z * g)⁻¹ * w := by rw [hzg]
        _ = (g⁻¹ * z * g) * w := by
            rw [inv_eq_of_mul_eq_one_right hzg2]
    have hywyU : y * w * y⁻¹ ∈ uOfL22 T M := HatModel.conj_mem_uOfL22 hyN hwU
    have e1 := Tm.ρ_c ⟨y, hyH⟩ ⟨w, hwU⟩ hywyU
    have e2 : (⟨y * w * y⁻¹, hywyU⟩ : ↥(uOfL22 T M)) =
        ⟨g⁻¹ * z * g, hzgU⟩ * ⟨w, hwU⟩ := Subtype.ext hywy
    rw [e1, e2, Tm.c_mul, add_sub_cancel_right]

theorem tilde_rho_eq_one_of_mem_pCore {L : Subgroup G} (h : Hyp1281Two G T M L) (Tm : TildeModel T M)
    (x : ↥(mcOf T)) (hx : (x : G) ∈ pCoreOf 2 (mcOf T)) : Tm.ρ x = 1 := by
  have hx' : (x : G) ∈ centralizerMod (quasithinOmegaOneCenter T) (mcOf T)
      (conjClosure (VZ T M) (mcOf T)) := by
    rw [Hyp1281Two.lemma_12_8_4_four h h.isHz_centralizer]
    exact hx
  ext v
  obtain ⟨u, rfl⟩ := Tm.c_surj v
  have hxN : (x : G) ∈ Subgroup.normalizer (uOfL22 T M : Set G) := h.g1_le_normalizer_uOfL22 x.2
  have hxu : (x : G) * (u : G) * (x : G)⁻¹ ∈ uOfL22 T M := HatModel.conj_mem_uOfL22 hxN u.2
  show Tm.ρ x (Tm.c u) = Tm.c u
  rw [Tm.ρ_c x u hxu, Tm.c_eq_iff]
  have hc : (x : G) * (u : G) * (x : G)⁻¹ * (u : G)⁻¹ ∈ quasithinOmegaOneCenter T := hx'.2.2 u u.2
  set c := (x : G) * (u : G) * (x : G)⁻¹ * (u : G)⁻¹ with hcdef
  have hcc : (u : G) * c = c * (u : G) :=
    Subgroup.mem_centralizer_iff.mp (h.omegaOneCenter_le_centerOf_uOfL22 hc).2 u u.2
  have h1 : (x : G) * (u : G) * (x : G)⁻¹ = c * (u : G) := by rw [hcdef]; group
  have h2 : (u : G) * c⁻¹ = c⁻¹ * (u : G) := (show Commute (u : G) c from hcc).inv_right.eq
  show ((x : G) * (u : G) * (x : G)⁻¹)⁻¹ * (u : G) ∈ quasithinOmegaOneCenter T
  rw [h1]
  have h3 : (c * (u : G))⁻¹ * (u : G) = c⁻¹ := by
    calc (c * (u : G))⁻¹ * (u : G) = (u : G)⁻¹ * (c⁻¹ * (u : G)) := by group
      _ = (u : G)⁻¹ * ((u : G) * c⁻¹) := by rw [h2]
      _ = c⁻¹ := by group
  rw [h3]
  exact (quasithinOmegaOneCenter T).inv_mem hc

end Aux

end S143W

@[expose] def Lemma1435 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (T M : Subgroup G), Hyp1421 G T M → ¬ SixModels G →
    ∀ H : Subgroup G, InH T H → (T.relIndex H = 3 ∨ T.relIndex H = 5) → H ≤ M

theorem lemma1435_of_14220 (h14220 : StageTheorem14220) : Lemma1435 :=
  fun _ _ _ _ _ h hnot _ hH hidx => lemma_14_3_5 h14220 card_sz_zero_eq_twenty
      pCore_two_sz_zero_eq_bot h hnot hH hidx

end CFSG.Quasithin

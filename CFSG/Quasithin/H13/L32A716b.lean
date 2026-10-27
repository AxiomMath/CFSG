module

public import CFSG.Quasithin.H13.L32A716a
public import CFSG.Quasithin.EmptyFaithful.S146zHWsub

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

omit hF in
theorem fsuU_eq : fsuU T V = conjClosure V (hz T V) :=
  fsuU_eq_conjClosure_hz (stmtL32NModule_of_inputs E.h1332 E.h1334) E.S.hyp

theorem card_u : (fsuV1 T V).relIndex (fsuU T V) = 64 := by
  have hV1U : fsuV1 T V ≤ conjClosure V (hz T V) :=
    (inf_le_left.trans (le_conjClosure V _))
  have hUN : conjClosure V (hz T V) ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    U_le_normalizer hF.toHypF91
  have h1 := relIndex_secImg (A := Subgroup.normalizer (fsuV1 T V : Set G)) (B := fsuV1 T V)
    (T := fsuV1 T V) (H := conjClosure V (hz T V)) le_rfl hV1U hUN
  have h2 : secImg (Subgroup.normalizer (fsuV1 T V : Set G)) (fsuV1 T V) (fsuV1 T V) = ⊥ :=
    tildeOf_eq_bot_of_le le_rfl
  rw [h2, Subgroup.relIndex_bot_left] at h1
  rw [E.fsuU_eq, ← h1]
  exact E.card_umod hF

theorem faithful_u : ∀ x ∈ oTwoUpper H,
    (∀ u ∈ fsuU T V, x * u * x⁻¹ * u⁻¹ ∈ fsuV1 T V) → x ∈ pCoreOf 2 (oTwoUpper H) := by
  intro x hx hxu
  have hxhz : x ∈ hz T V := E.k_le_hz hx
  have h1 : C1Pack.rhoH hF.toHypF91 ⟨x, hxhz⟩ = 1 := by
    ext w
    obtain ⟨u, hu, rfl⟩ := exists_clsU hF.toHypF91 w
    rw [MulAut.one_apply, rhoH_clsU_eq_iff]
    exact hxu u (E.fsuU_eq ▸ hu)
  have h2 := (C1Pack.rhoH_eq_one_iff hF.toHypF91 ⟨x, hxhz⟩).mp h1
  rw [pCoreOf_eq_inf_pCoreOf E.k_le_hz E.hz_le_normalizer_K]
  exact ⟨hx, h2⟩

theorem irred_u : ∀ W : Subgroup G, fsuV1 T V ≤ W → W ≤ fsuU T V →
    oTwoUpper H ≤ Subgroup.normalizer (W : Set G) → W = fsuV1 T V ∨ W = fsuU T V := by
  intro W hVW hWU hKW
  set h := hF.toHypF91 with hh
  have hWU' : W ≤ conjClosure V (hz T V) := E.fsuU_eq ▸ hWU
  have hinv : ∀ g ∈ modO2Image (hz T V) (oTwoUpper H), ∀ w ∈ Wsub h W,
      rhoDot h g w ∈ Wsub h W := by
    intro g hg w hw
    obtain ⟨x, hxK, rfl⟩ := mem_modO2Image_iff.mp hg
    rw [QuotientGroup.mk'_apply, rhoDot_mk]
    refine rhoH_mem_Wsub h x hWU' ?_ hw
    exact conjSub_eq_self_iff.mpr (hKW hxK)
  rcases E.irreducible hF (Wsub h W) hinv with hb | ht
  · left
    refine le_antisymm (fun w hw => ?_) hVW
    have hwU := hWU' hw
    have h1 : clsU h hwU ∈ Wsub h W := clsU_mem_Wsub h hwU hw
    rw [hb, Subgroup.mem_bot] at h1
    exact (clsU_eq_one_iff h hwU).mp h1
  · right
    refine le_antisymm hWU fun u hu => ?_
    have huU : u ∈ conjClosure V (hz T V) := E.fsuU_eq ▸ hu
    have h1 : clsU h huU ∈ Wsub h W := ht ▸ Subgroup.mem_top _
    obtain ⟨w, hwU, hwW, hwe⟩ := exists_clsU_of_mem_Wsub h hWU' h1
    have h2 : w⁻¹ * u ∈ fsuV1 T V := (clsU_eq_iff h hwU huU).mp hwe
    have e : u = w * (w⁻¹ * u) := by group
    rw [e]
    exact W.mul_mem hwW (hVW h2)

theorem fpf_u : ∀ u ∈ fsuU T V, (∀ l ∈ l1 T L V, l * u * l⁻¹ * u⁻¹ ∈ fsuV1 T V) →
    u ∈ fsuV1 T V := by
  intro u hu hlu
  set h := hF.toHypF91 with hh
  obtain ⟨-, -, c, -, -, -, hcL, -, -, -, -, -, -, -, -, -, -, hfpf, -⟩ := E.exists_frame hF
  obtain ⟨l, hlL, rfl⟩ := mem_modO2Image_iff.mp hcL
  have huU : u ∈ conjClosure V (hz T V) := E.fsuU_eq ▸ hu
  have h1 : rhoDot h (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) l) (clsU h huU) = clsU h huU := by
    rw [QuotientGroup.mk'_apply, rhoDot_mk, rhoH_clsU_eq_iff]
    exact hlu l hlL
  exact (clsU_eq_one_iff h huU).mp (hfpf _ h1)

omit hF in
theorem u_comm : ⁅fsuU T V, l1 T L V⁆ ⊔ fsuV1 T V = fsuU T V := by
  have h5 := (E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal).2.2.2.2.2.2
  rw [← E.fsuU_eq] at h5
  exact h5

end Ctx7153

end CFSG.Quasithin.H13.L32A

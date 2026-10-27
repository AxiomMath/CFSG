module

public import CFSG.Quasithin.H13.L32A769b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem false_of_hyperplane (h : Hyp147 G T L V) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) {H₀ : Subgroup G}
    (hH₀V : H₀ ≤ V) (hne : ¬ V ≤ H₀)
    (hidx : ∀ a ∈ V, a ∉ H₀ → ∀ b ∈ V, b ∉ H₀ → a * b ∈ H₀)
    (hN : L₁Of L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer (H₀ : Set G)) : False := by
  have h13322 := stmt13_3_2_two_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis
  by_cases hV1 : fsuV1 T V ≤ H₀
  · rcases hF.irred H₀ hV1 hH₀V hN with e | e
    · have haH : a ∉ H₀ := e ▸ haV
      have hbH : b ∉ H₀ := e ▸ fun hb' => hbV (hV2.1 hb')
      have hab := hidx a (hV2.2.1 ha) haH b hb hbH
      rw [e] at hab
      apply hbV
      rw [show b = a⁻¹ * (a * b) by group]
      exact mul_mem (inv_mem ha) (hV2.1 hab)
    · exact hne e.ge
  · have hzH : z ∉ H₀ := fun hz' => hV1 fun v hv => by
      rcases S14.eq_of_mem_V1 hz0 hz1 hv with rfl | rfl
      · exact one_mem _
      · exact hz'
    have hL1H : L₁Of L (fsuV1 T V) ≤ hz T V := le_sup_left.trans hF.L₁T_le_H
    have hcomm : ⁅V, pCoreOf 2 (L₁Of L (fsuV1 T V))⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro v hv p hp
      have hpL : p ∈ L₁Of L (fsuV1 T V) := pCoreOf_le 2 _ hp
      have hpH : p ∈ hz T V := hL1H hpL
      have hpN : p ∈ Subgroup.normalizer (H₀ : Set G) := hN (Subgroup.mem_sup_left hpL)
      have key : ∀ w ∈ V, w ∈ H₀ → w * p * w⁻¹ * p⁻¹ = 1 := by
        intro w hw hwH
        have h1 : ⁅w, p⁆ ∈ fsuV1 T V := by
          rw [← S14.comm3]
          exact Subgroup.commutator_mem_commutator hw hp
        have h2 : w * p * w⁻¹ * p⁻¹ ∈ H₀ := by
          rw [show w * p * w⁻¹ * p⁻¹ = w * (p * w⁻¹ * p⁻¹) by group]
          exact mul_mem hwH ((Subgroup.mem_normalizer_iff.mp hpN _).mp (inv_mem hwH))
        rw [commutatorElement_def] at h1
        rcases S14.eq_of_mem_V1 hz0 hz1 h1 with e | e
        · exact e
        · exact absurd (e ▸ h2) hzH
      have hzp : z * p = p * z :=
        (Subgroup.mem_centralizer_iff.mp hpH z hz0)
      rw [commutatorElement_def, Subgroup.mem_bot]
      by_cases hvH : v ∈ H₀
      · exact key v hv hvH
      · have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
        have hzv := hidx z hzV hzH v hv hvH
        have h1 := key (z * v) (mul_mem hzV hv) hzv
        have e : z * v * p * (z * v)⁻¹ * p⁻¹ = z * (v * p * v⁻¹ * p⁻¹) * z⁻¹ := by
          calc z * v * p * (z * v)⁻¹ * p⁻¹ = z * v * p * v⁻¹ * (p * z)⁻¹ := by group
            _ = z * v * p * v⁻¹ * (z * p)⁻¹ := by rw [hzp]
            _ = z * (v * p * v⁻¹ * p⁻¹) * z⁻¹ := by group
        rw [e] at h1
        calc v * p * v⁻¹ * p⁻¹ = z⁻¹ * (z * (v * p * v⁻¹ * p⁻¹) * z⁻¹) * z := by group
          _ = 1 := by rw [h1]; group
    have := S14.comm3
    rw [hcomm] at this
    have hc := hF.card_V₁
    rw [← this, Subgroup.card_bot] at hc
    omega

namespace Conf69

variable {x : G} (C : Conf69 G T L V x)
include C

omit [Finite G] C in
theorem GW_eq : conjSub x (hz T V) = Subgroup.centralizer (conjSub x (fsuV1 T V) : Set G) := by
  rw [conjSub_centralizer]

theorem GW_le_normalizer_W :
    conjSub x (hz T V) ≤ Subgroup.normalizer (conjSub x (fsuU T V) : Set G) := by
  rw [conjSub_normalizer]
  refine conjSub_mono x ?_
  rw [fsuU_eq_conjClosure_hz C.hMod C.hyp]
  exact le_normalizer_conjClosure V _

theorem not_V1_le (h13314 : A6.Stmt13_3_14) : ¬ fsuV1 T V ≤ conjSub x (fsuU T V) := by
  intro hV1W
  have h := C.hyp
  have hMod := C.hMod
  have hF := C.hF
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz C.h63⟩
  obtain ⟨-, hR4⟩ := R1_le_kz_sup S0 hF C.h63 C.h1222 C.h1332 C.h1334
  obtain ⟨-, -, hF1⟩ := C.cent
  have hcomm := C.cent.2.1
  have hUeq : fsuU T V = conjClosure V (hz T V) := fsuU_eq_conjClosure_hz hMod h
  have hV1U : fsuV1 T V ≤ fsuU T V := inf_le_left.trans (le_conjClosure V _)
  have hVU : V ≤ fsuU T V := le_conjClosure V _
  have hUQ : fsuU T V ≤ pCoreOf 2 (hz T V) := by
    rw [hUeq]
    exact hF.conjClosure_Vp_le_pCoreOf
  have hUH : fsuU T V ≤ hz T V := hUQ.trans (pCoreOf_le 2 _)
  have hQC : ∀ q ∈ pCoreOf 2 (hz T V), ∀ u ∈ fsuU T V, q * u * q⁻¹ * u⁻¹ ∈ fsuV1 T V := by
    intro q hq u hu
    have hqC : q ∈ centralizerMod (fsuV1 T V) (hz T V) (conjClosure V (hz T V)) := by
      rw [← hF.pCoreOf_eq_centralizerMod]
      exact hq
    exact hqC.2.2 u (hUeq ▸ hu)
  have hV1c : ∀ v ∈ fsuV1 T V, ∀ g ∈ hz T V, v * g = g * v := fun v hv g hg =>
    (Subgroup.mem_centralizer_iff.mp hg v hv)
  have hUc : ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V, a * b = b * a := fun a ha b hb =>
    F7.isElemAbelian_comm (isElemAbelian_fsuU_of h hMod) ha hb
  have hFeq : fsuU T V ⊓ conjSub x (fsuU T V) = V ⊔ u0 T V := by
    rw [← hF1]
    exact (sup_eq_left.mpr (le_inf hV1U hV1W)).symm
  have hWQ : conjSub x (fsuU T V) ⊓ pCoreOf 2 (hz T V) =
      fsuU T V ⊓ conjSub x (fsuU T V) := by
    symm
    refine Subgroup.eq_of_le_of_card_ge (le_inf inf_le_right (inf_le_left.trans hUQ)) ?_
    have hWN : conjSub x (fsuU T V) ≤ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
      (C.le_R1.trans ((pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H)).trans
        (le_normalizer_pCoreOf 2 _)
    have h1 : (pCoreOf 2 (hz T V)).relIndex (conjSub x (fsuU T V)) = 4 := by
      rw [← A4.relIndex_sup_eq_of_le_normalizer' hWN, C.sup_eq, hR4]
    have h2 := Subgroup.relIndex_mul_card (pCoreOf 2 (hz T V)) (conjSub x (fsuU T V))
    rw [h1, inf_comm] at h2
    have h3 := Subgroup.relIndex_mul_card (V ⊔ u0 T V) (fsuU T V)
    rw [(relIndex_sup_u0 h hMod C.h63 hF).2, inf_eq_left.mpr (sup_le hVU
      (centralizerMod_le_left _ _ _) : V ⊔ u0 T V ≤ fsuU T V)] at h3
    have h4 : Nat.card ↥(conjSub x (fsuU T V)) = Nat.card ↥(fsuU T V) := by
      rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj x).injective]
    rw [hFeq]
    omega
  have hZQ : conjSub x (fsuV1 T V) ≤ pCoreOf 2 (hz T V) := by
    intro z hzZ
    have hzc : ∀ u ∈ fsuU T V, z * u = u * z := fun u hu => by
      have := C.U_le hu
      rw [GW_eq, Subgroup.mem_centralizer_iff] at this
      exact this z hzZ
    have hzH : z ∈ hz T V := Subgroup.mem_centralizer_iff.mpr fun v hv =>
      (hzc v (hV1U hv)).symm
    rw [hF.pCoreOf_eq_centralizerMod]
    refine ⟨hzH, hF.H_normalizes_V₁ hzH, fun u hu => ?_⟩
    rw [hzc u (hUeq ▸ hu), mul_inv_cancel_right, mul_inv_cancel]
    exact one_mem _
  have hZU : conjSub x (fsuV1 T V) ≤ fsuU T V := fun z hzZ => by
    have hmem : z ∈ conjSub x (fsuU T V) ⊓ pCoreOf 2 (hz T V) := ⟨Conf69.Z_le hzZ, hZQ hzZ⟩
    rw [hWQ] at hmem
    exact hmem.1
  obtain ⟨⟨z', hz'⟩, hz'1, hz'u⟩ := (Nat.card_eq_two_iff' (1 : ↥(conjSub x (fsuV1 T V)))).mp
    C.card_Z
  have hz'1' : z' ≠ 1 := fun e => hz'1 (Subtype.ext e)
  have hZcases : ∀ y ∈ conjSub x (fsuV1 T V), y = 1 ∨ y = z' := fun y hy => by
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (congrArg Subtype.val (hz'u ⟨y, hy⟩ fun e => hy1 (congrArg Subtype.val e)))
  have hz'U : z' ∈ fsuU T V := hZU hz'
  have hcentV : ∀ c ∈ pCoreOf 2 (hz T V), c * z' = z' * c → ∀ v ∈ V, c * v = v * c := by
    intro c hc hcz v hv
    have hcH : c ∈ hz T V := pCoreOf_le 2 _ hc
    have hcG : c ∈ conjSub x (hz T V) := by
      rw [GW_eq, Subgroup.mem_centralizer_iff]
      intro y hy
      rcases hZcases y hy with rfl | rfl
      · group
      · exact hcz.symm
    have hcw : ∀ u ∈ fsuU T V, ∀ w ∈ conjSub x (fsuU T V),
        c * (u * w * u⁻¹ * w⁻¹) = (u * w * u⁻¹ * w⁻¹) * c := by
      intro u hu w hw
      have hwH : w ∈ hz T V :=
        C.le_R1.trans ((pCoreOf_le_of_le h le_sup_right).trans hF.T_le_H) hw
      set a := c * w * c⁻¹ * w⁻¹ with ha
      have haW : a ∈ conjSub x (fsuU T V) :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp (C.GW_le_normalizer_W hcG) w).mp hw)
          (inv_mem hw)
      have haQ : a ∈ pCoreOf 2 (hz T V) := by
        rw [ha, show c * w * c⁻¹ * w⁻¹ = c * (w * c⁻¹ * w⁻¹) by group]
        exact mul_mem hc ((Subgroup.mem_normalizer_iff.mp (le_normalizer_pCoreOf 2 _ hwH)
          _).mp (inv_mem hc))
      have haU : a ∈ fsuU T V := by
        have hmem : a ∈ conjSub x (fsuU T V) ⊓ pCoreOf 2 (hz T V) := ⟨haW, haQ⟩
        rw [hWQ] at hmem
        exact hmem.1
      set b := c * u * c⁻¹ * u⁻¹ with hb
      have hbV : b ∈ fsuV1 T V := hQC c hc u hu
      have hwu : w * u * w⁻¹ ∈ fsuU T V := (Subgroup.mem_normalizer_iff.mp
        ((le_normalizer_conjClosure V (hz T V)) hwH) u).mp (hUeq ▸ hu) |> fun h' => hUeq ▸ h'
      have e1 : c * u * c⁻¹ = b * u := by rw [hb]; group
      have e2 : c * (w * u * w⁻¹) * c⁻¹ = b * (w * u * w⁻¹) := by
        calc c * (w * u * w⁻¹) * c⁻¹ = a * w * (c * u * c⁻¹) * w⁻¹ * a⁻¹ := by rw [ha]; group
          _ = a * w * (b * u) * w⁻¹ * a⁻¹ := by rw [e1]
          _ = b * (a * (w * u * w⁻¹) * a⁻¹) := by
              have hbw := hV1c b hbV w hwH
              have hba := hV1c b hbV a (hUH haU)
              calc a * w * (b * u) * w⁻¹ * a⁻¹ = a * (w * b) * u * w⁻¹ * a⁻¹ := by group
                _ = a * (b * w) * u * w⁻¹ * a⁻¹ := by rw [hbw]
                _ = (a * b) * (w * u * w⁻¹) * a⁻¹ := by group
                _ = (b * a) * (w * u * w⁻¹) * a⁻¹ := by rw [hba]
                _ = b * (a * (w * u * w⁻¹) * a⁻¹) := by group
          _ = b * (w * u * w⁻¹) := by
              rw [hUc a haU _ hwu, mul_inv_cancel_right]
      have hbu := hV1c b hbV u (hUH hu)
      calc c * (u * w * u⁻¹ * w⁻¹) = (c * u * c⁻¹) * (c * (w * u * w⁻¹) * c⁻¹)⁻¹ * c := by
            group
        _ = (b * u) * (b * (w * u * w⁻¹))⁻¹ * c := by rw [e1, e2]
        _ = (u * w * u⁻¹ * w⁻¹) * c := by
            rw [mul_inv_rev, show (w * u * w⁻¹)⁻¹ = w * u⁻¹ * w⁻¹ by group]
            calc b * u * (w * u⁻¹ * w⁻¹ * b⁻¹) * c = u * b * (w * u⁻¹ * w⁻¹) * b⁻¹ * c := by
                  rw [hbu]; group
              _ = u * (b * (w * u⁻¹ * w⁻¹)) * b⁻¹ * c := by group
              _ = u * ((w * u⁻¹ * w⁻¹) * b) * b⁻¹ * c := by
                  rw [hV1c b hbV _ (hUH (by
                    have := inv_mem hwu
                    rwa [show (w * u * w⁻¹)⁻¹ = w * u⁻¹ * w⁻¹ by group] at this))]
              _ = (u * w * u⁻¹ * w⁻¹) * c := by group
    have hle : ⁅fsuU T V, conjSub x (fsuU T V)⁆ ⊔ fsuV1 T V ≤
        Subgroup.centralizer ({c} : Set G) := by
      refine sup_le ?_ fun v hv => Subgroup.mem_centralizer_singleton_iff.mpr ?_
      · rw [Subgroup.commutator_le]
        intro u hu w hw
        rw [Subgroup.mem_centralizer_singleton_iff, commutatorElement_def]
        exact (hcw u hu w hw).symm
      · exact hV1c v hv c hcH
    have hv' : v ∈ ⁅fsuU T V, conjSub x (fsuU T V)⁆ ⊔ fsuV1 T V := by
      rw [hcomm]
      exact Subgroup.mem_sup_left hv
    have hvc := hle hv'
    exact (Subgroup.mem_centralizer_singleton_iff.mp hvc).symm
  have hβmul : ∀ q ∈ pCoreOf 2 (hz T V), ∀ a ∈ fsuU T V, ∀ b ∈ fsuU T V,
      q * (a * b) * q⁻¹ * (a * b)⁻¹ = (q * a * q⁻¹ * a⁻¹) * (q * b * q⁻¹ * b⁻¹) := by
    intro q hq a ha b hb
    have h1 := hV1c _ (hQC q hq b hb) a (hUH ha)
    calc q * (a * b) * q⁻¹ * (a * b)⁻¹ = (q * a * q⁻¹ * a⁻¹) * (a * (q * b * q⁻¹ * b⁻¹)) *
          a⁻¹ := by group
      _ = (q * a * q⁻¹ * a⁻¹) * ((q * b * q⁻¹ * b⁻¹) * a) * a⁻¹ := by rw [h1]
      _ = _ := by group
  obtain ⟨v₁, hv₁, hv₁1, hV1cases⟩ : ∃ v₁ ∈ fsuV1 T V, v₁ ≠ 1 ∧
      ∀ y ∈ fsuV1 T V, y = 1 ∨ y = v₁ := by
    obtain ⟨⟨v₁, hv₁⟩, hv₁1, hu⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hF.card_V₁
    refine ⟨v₁, hv₁, fun e => hv₁1 (Subtype.ext e), fun y hy => ?_⟩
    by_cases hy1 : y = 1
    · exact Or.inl hy1
    · exact Or.inr (congrArg Subtype.val (hu ⟨y, hy⟩ fun e => hy1 (congrArg Subtype.val e)))
  have hcommiff : ∀ q ∈ pCoreOf 2 (hz T V), ∀ u ∈ fsuU T V,
      q * u = u * q ↔ q * u * q⁻¹ * u⁻¹ = 1 := fun q _ u _ => by
    constructor
    · intro e; rw [e]; group
    · intro e
      have := congrArg (· * u) e
      simp only [inv_mul_cancel_right, one_mul] at this
      calc q * u = q * u * q⁻¹ * q := by group
        _ = u * q := by rw [this]
  set H₀ := V ⊓ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) with hH₀
  have hidx : ∀ a ∈ V, a ∉ H₀ → ∀ b ∈ V, b ∉ H₀ → a * b ∈ H₀ := by
    intro a ha haH b hb hbH
    obtain ⟨q₁, hq₁, hq₁a⟩ : ∃ q₁ ∈ pCoreOf 2 (hz T V), q₁ * a ≠ a * q₁ := by
      by_contra hcon
      push Not at hcon
      exact haH ⟨ha, Subgroup.mem_centralizer_iff.mpr fun q hq => hcon q hq⟩
    have hq₁z : ¬ q₁ * z' = z' * q₁ := fun e => hq₁a (hcentV q₁ hq₁ e a ha)
    have hdiv : ∀ q ∈ pCoreOf 2 (hz T V), ¬ q * z' = z' * q →
        q₁⁻¹ * q * z' = z' * (q₁⁻¹ * q) := by
      intro q hq hqz
      have hb1 := hQC q₁ hq₁ z' hz'U
      have hb2 := hQC q hq z' hz'U
      have e1 : q₁ * z' * q₁⁻¹ * z'⁻¹ = v₁ := (hV1cases _ hb1).resolve_left
        fun e => hq₁z ((hcommiff q₁ hq₁ z' hz'U).mpr e)
      have e2 : q * z' * q⁻¹ * z'⁻¹ = v₁ := (hV1cases _ hb2).resolve_left
        fun e => hqz ((hcommiff q hq z' hz'U).mpr e)
      have hqz' : q * z' * q⁻¹ = v₁ * z' := by rw [← e2]; group
      have hq₁z' : q₁ * z' * q₁⁻¹ = v₁ * z' := by rw [← e1]; group
      have hv₁q₁ := hV1c v₁ hv₁ q₁ (pCoreOf_le 2 _ hq₁)
      calc q₁⁻¹ * q * z' = q₁⁻¹ * (q * z' * q⁻¹) * q := by group
        _ = q₁⁻¹ * (q₁ * z' * q₁⁻¹) * q := by rw [hqz', hq₁z']
        _ = z' * (q₁⁻¹ * q) := by group
    refine ⟨mul_mem ha hb, Subgroup.mem_centralizer_iff.mpr fun q hq => ?_⟩
    have hq₁b : q₁ * b ≠ b * q₁ := by
      intro e
      apply hbH
      refine ⟨hb, Subgroup.mem_centralizer_iff.mpr fun q' hq' => ?_⟩
      by_cases hq'z : q' * z' = z' * q'
      · exact hcentV q' hq' hq'z b hb
      · have hc := hdiv q' hq' hq'z
        have hcb := hcentV _ (mul_mem (inv_mem hq₁) hq') hc b hb
        calc q' * b = q₁ * ((q₁⁻¹ * q') * b) := by group
          _ = q₁ * (b * (q₁⁻¹ * q')) := by rw [hcb]
          _ = (q₁ * b) * (q₁⁻¹ * q') := by group
          _ = (b * q₁) * (q₁⁻¹ * q') := by rw [e]
          _ = b * q' := by group
    have hq₁ab : q₁ * (a * b) = (a * b) * q₁ := by
      have ea : q₁ * a * q₁⁻¹ * a⁻¹ = v₁ := (hV1cases _ (hQC q₁ hq₁ a (hVU ha))).resolve_left
        fun e => hq₁a ((hcommiff q₁ hq₁ a (hVU ha)).mpr e)
      have eb : q₁ * b * q₁⁻¹ * b⁻¹ = v₁ := (hV1cases _ (hQC q₁ hq₁ b (hVU hb))).resolve_left
        fun e => hq₁b ((hcommiff q₁ hq₁ b (hVU hb)).mpr e)
      have hv₁2 : v₁ * v₁ = 1 := by
        have h1 := orderOf_dvd_natCard (⟨v₁, hv₁⟩ : ↥(fsuV1 T V))
        rw [hF.card_V₁] at h1
        have h2 := orderOf_dvd_iff_pow_eq_one.mp h1
        have h3 : v₁ ^ 2 = 1 := by simpa using congrArg Subtype.val h2
        rwa [pow_two] at h3
      apply (hcommiff q₁ hq₁ (a * b) (mul_mem (hVU ha) (hVU hb))).mpr
      rw [hβmul q₁ hq₁ a (hVU ha) b (hVU hb), ea, eb, hv₁2]
    by_cases hqz : q * z' = z' * q
    · exact hcentV q hq hqz _ (mul_mem ha hb)
    · have hc := hdiv q hq hqz
      have hcab := hcentV _ (mul_mem (inv_mem hq₁) hq) hc _ (mul_mem ha hb)
      calc q * (a * b) = q₁ * ((q₁⁻¹ * q) * (a * b)) := by group
        _ = q₁ * ((a * b) * (q₁⁻¹ * q)) := by rw [hcab]
        _ = (q₁ * (a * b)) * (q₁⁻¹ * q) := by group
        _ = ((a * b) * q₁) * (q₁⁻¹ * q) := by rw [hq₁ab]
        _ = a * b * q := by group
  have hne : ¬ V ≤ H₀ := by
    intro hle
    have h13322 := stmt13_3_2_two_of C.h1332
    obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod C.h1222
    have h1 := lemma14_7_4_one h h13322 hMod h13314 hV2
    have hg1 : A6.g1 T V = hz T V := normalizer_eq_centralizer_of_card_eq_two hF.card_V₁
    rw [hg1] at h1
    have h2 : ⁅V₂, pCoreOf 2 (hz T V)⁆ = ⊥ := by
      rw [eq_bot_iff, Subgroup.commutator_le]
      intro v hv q hq
      have hc' : v ∈ Subgroup.centralizer (pCoreOf 2 (hz T V) : Set G) :=
        (Subgroup.mem_inf.mp (hle (hV2.2.1 hv))).2
      rw [Subgroup.mem_bot, commutatorElement_def, ← Subgroup.mem_centralizer_iff.mp hc' q hq,
        mul_inv_cancel_right, mul_inv_cancel]
    rw [h1] at h2
    have hc := hF.card_V₁
    rw [h2, Subgroup.card_bot] at hc
    omega
  have hN : L₁Of L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer (H₀ : Set G) := by
    obtain ⟨-, -, hLTV, -, -⟩ := hMod G T L V h.hyp h.fsu
    intro g hg
    have hgV : g ∈ Subgroup.normalizer (V : Set G) :=
      hLTV (sup_le_sup_right (L32NSet14.Setting.L1_le.trans inf_le_left) T hg)
    have hgQ : g ∈ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
      le_normalizer_pCoreOf 2 _ (hF.L₁T_le_H hg)
    rw [← conjSub_eq_self_iff, hH₀, conjSub_inf, ← conjSub_centralizer,
      conjSub_eq_self_iff.mpr hgV, conjSub_eq_self_iff.mpr hgQ]
  exact false_of_hyperplane h C.h1222 C.h1332 C.h1334 hF inf_le_left hne hidx hN

end Conf69

end CFSG.Quasithin.H13.L32A

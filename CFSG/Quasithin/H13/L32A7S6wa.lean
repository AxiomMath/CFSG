module

public import CFSG.Quasithin.H13.L32A767a
public import CFSG.Quasithin.H13.L32NLem1434
public import CFSG.Quasithin.Background.E3Weak

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
private theorem conjSubgroup_eq_conjSub_inv' (A : Subgroup G) (g : G) :
    conjSubgroup A g = conjSub g⁻¹ A := by
  ext x
  rw [mem_conjSubgroup_iff, mem_conjSub, inv_inv]

theorem centralizer_le_normalizer_conjSub_of_centralizer_V2 (h : Hyp147 G T L V)
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {V₂ : Subgroup G}
    (hV2 : A6.IsV2 T V V₂)
    (hCV : Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G)) {g : G}
    {A : Subgroup G} (hA : A ≤ conjSub g V) (hA4 : Nat.card A = 4) :
    Subgroup.centralizer (A : Set G) ≤ Subgroup.normalizer (conjSub g V : Set G) := by
  have hF : conjSub g⁻¹ A ≤ V := by
    intro x hx
    rw [mem_conjSub, inv_inv] at hx
    have := hA hx
    rw [mem_conjSub] at this
    simpa [mul_assoc] using this
  have hF4 : Nat.card (conjSub g⁻¹ A) = 4 := by
    rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hA4]
  obtain ⟨l, hlL, hl⟩ := exists_conj_V2 h h1222 h1332 h1334 hV2 hF hF4
  have hF1 : conjSub g⁻¹ A ≠ ⊥ := by
    intro h0
    rw [h0, Subgroup.card_bot] at hF4
    omega
  have hCF : Subgroup.centralizer (conjSub g⁻¹ A : Set G) ≤ Subgroup.normalizer (V : Set G) := by
    intro c hc
    have hcL : c ∈ Subgroup.normalizer (L : Set G) := by
      have hc' : l⁻¹ * c * l ∈ Subgroup.centralizer (V₂ : Set G) := by
        rw [Subgroup.mem_centralizer_iff]
        intro v hv
        have hlv : l * v * l⁻¹ ∈ conjSub g⁻¹ A := by
          rw [← hl]
          exact mul_mem_conjSub hv
        have e := Subgroup.mem_centralizer_iff.mp hc _ hlv
        calc v * (l⁻¹ * c * l) = l⁻¹ * ((l * v * l⁻¹) * c) * l := by group
          _ = l⁻¹ * (c * (l * v * l⁻¹)) * l := by rw [e]
          _ = l⁻¹ * c * l * v := by group
      have h1 := hCV hc'
      have hlN : l ∈ Subgroup.normalizer (L : Set G) := Subgroup.le_normalizer hlL
      have e : c = l * (l⁻¹ * c * l) * l⁻¹ := by group
      rw [e]
      exact mul_mem (mul_mem hlN h1) (inv_mem hlN)
    have h6 := lemma1433Six_of_inputs h1332 h1334 h1222 G T L V h.hyp h.fsu (conjSub g⁻¹ A)
      (Subgroup.centralizer (conjSub g⁻¹ A : Set G)) hF hF1
      (Subgroup.centralizer_le_normalizer _)
    have h2 : c ∈ Subgroup.centralizer (conjSub g⁻¹ A : Set G) ⊓
        Subgroup.normalizer (L : Set G) := ⟨hc, hcL⟩
    rw [h6] at h2
    exact h2.2
  intro c hc
  have hc' : g⁻¹ * c * g ∈ Subgroup.centralizer (conjSub g⁻¹ A : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro x hx
    have hx' : g * x * g⁻¹ ∈ A := by
      have := mem_conjSub.mp hx
      simpa using this
    have e := Subgroup.mem_centralizer_iff.mp hc _ hx'
    calc x * (g⁻¹ * c * g) = g⁻¹ * ((g * x * g⁻¹) * c) * g := by group
      _ = g⁻¹ * (c * (g * x * g⁻¹)) * g := by rw [e]
      _ = g⁻¹ * c * g * x := by group
  have hN := hCF hc'
  rw [Subgroup.mem_normalizer_iff] at hN ⊢
  intro y
  rw [mem_conjSub, mem_conjSub]
  have e1 := hN (g⁻¹ * y * g)
  rw [show g⁻¹ * c * g * (g⁻¹ * y * g) * (g⁻¹ * c * g)⁻¹ = g⁻¹ * (c * y * c⁻¹) * g by group]
    at e1
  exact e1

theorem conjSub_le_pCoreOf_of_centralizer_V2 (h : Hyp147 G T L V) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂)
    (hCV : Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G))
    {Y TY VY : Subgroup G} (hS : IsSylowTwoOf TY Y) (hidx : (pCoreOf 2 Y).relIndex TY ≤ 2)
    (hYV : Y ≤ Subgroup.normalizer (VY : Set G))
    (hO : pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (VY : Set G))
    (hU : ∀ g : G, conjSub g (fsuV1 T V) ≤ VY →
      conjSub g (fsuU T V) ≤ Subgroup.centralizer (VY : Set G))
    {g : G} (hg : conjSub g V ≤ TY) : conjSub g V ≤ pCoreOf 2 Y := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨-, hV8, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  set P := conjSub g V with hP
  set O := pCoreOf 2 Y with hOdef
  have hOT : O ≤ TY := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
  have hOV : O ≤ Subgroup.centralizer (VY : Set G) := by
    rw [hO]
    exact inf_le_right
  have hP8 : Nat.card P = 8 := by
    rw [hP, conjSub, Subgroup.card_map_of_injective (MulAut.conj g).injective, hV8]
  by_contra hPO
  have hPN : P ≤ Subgroup.normalizer (O : Set G) :=
    (hg.trans hS.1).trans (le_normalizer_pCoreOf 2 Y)
  have e1 := L32NSet14.card_sup_mul_card_inf hPN
  have i1 := Subgroup.relIndex_mul_card O TY
  rw [inf_eq_left.mpr hOT] at i1
  have hle := Subgroup.card_le_of_le (sup_le hg hOT)
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hA4 : Nat.card ↥(P ⊓ O) = 4 := by
    have hge : 8 ≤ 2 * Nat.card ↥(P ⊓ O) := by
      have h1 : Nat.card ↥P * Nat.card ↥O ≤ 2 * Nat.card ↥(P ⊓ O) * Nat.card ↥O := by
        rw [← e1]
        calc Nat.card ↥(P ⊔ O) * Nat.card ↥(P ⊓ O) ≤ Nat.card ↥TY * Nat.card ↥(P ⊓ O) :=
              Nat.mul_le_mul_right _ hle
          _ = O.relIndex TY * Nat.card ↥O * Nat.card ↥(P ⊓ O) := by rw [i1]
          _ ≤ 2 * Nat.card ↥O * Nat.card ↥(P ⊓ O) :=
              Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hidx)
          _ = 2 * Nat.card ↥(P ⊓ O) * Nat.card ↥O := by ring
      rw [hP8] at h1
      exact Nat.le_of_mul_le_mul_right h1 hOpos
    have hlt : Nat.card ↥(P ⊓ O) < 8 := by
      rw [← hP8]
      refine Subgroup.card_lt_of_lt (lt_of_le_of_ne inf_le_left fun e => hPO ?_)
      rw [← e]
      exact inf_le_right
    have hdvd : Nat.card ↥(P ⊓ O) ∣ 2 ^ 3 := by
      rw [show (2 : ℕ) ^ 3 = 8 by norm_num, ← hP8]
      exact Subgroup.card_dvd_of_le inf_le_left
    rcases (Nat.dvd_prime_pow Nat.prime_two).mp hdvd with ⟨k, hk, e⟩
    rw [e] at hge hlt ⊢
    interval_cases k <;> simp_all
  have hVYA : VY ≤ Subgroup.centralizer ((P ⊓ O : Subgroup G) : Set G) := by
    intro w hw
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hOV (Subgroup.mem_inf.mp ha).2) w hw).symm
  have hVYN := hVYA.trans (centralizer_le_normalizer_conjSub_of_centralizer_V2 h h1222 h1332
    h1334 hV2 hCV inf_le_left hA4)
  have hnc : ¬ P ≤ Subgroup.centralizer (VY : Set G) := fun hc => hPO (by
    have h1 : P ≤ Y ⊓ Subgroup.centralizer (VY : Set G) := le_inf (hg.trans hS.1) hc
    rw [← hO] at h1
    exact h1)
  obtain ⟨p, hp, hpc⟩ := Set.not_subset.mp hnc
  rw [SetLike.mem_coe, Subgroup.mem_centralizer_iff] at hpc
  push Not at hpc
  obtain ⟨w, hw, hwp⟩ := hpc
  have hcY : w * p * w⁻¹ * p⁻¹ ∈ VY := by
    rw [show w * p * w⁻¹ * p⁻¹ = w * (p * w⁻¹ * p⁻¹) by group]
    exact mul_mem hw ((Subgroup.mem_normalizer_iff.mp (hYV (hS.1 (hg hp))) _).mp (inv_mem hw))
  have hcP : w * p * w⁻¹ * p⁻¹ ∈ P :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp (hVYN hw) p).mp hp) (inv_mem hp)
  have hc1 : w * p * w⁻¹ * p⁻¹ ≠ 1 := fun e => hwp (by
    calc w * p = w * p * w⁻¹ * p⁻¹ * (p * w) := by group
      _ = p * w := by rw [e, one_mul])
  obtain ⟨⟨z, hzV1⟩, hz1, huniq⟩ := (Nat.card_eq_two_iff' (1 : ↥(fsuV1 T V))).mp hV1
  have hz1' : z ≠ 1 := fun e => hz1 (Subtype.ext e)
  have hzV : z ∈ V := (inf_le_left : fsuV1 T V ≤ V) hzV1
  have hcV : g⁻¹ * (w * p * w⁻¹ * p⁻¹) * g ∈ V := by
    have := hcP
    rw [hP, mem_conjSub] at this
    exact this
  have hcV1 : g⁻¹ * (w * p * w⁻¹ * p⁻¹) * g ≠ 1 := fun e => hc1 (by
    calc w * p * w⁻¹ * p⁻¹ = g * (g⁻¹ * (w * p * w⁻¹ * p⁻¹) * g) * g⁻¹ := by group
      _ = 1 := by rw [e]; group)
  obtain ⟨l, hl, hlz⟩ := exists_conj_eq_of_mem (h.hyp1281One h13322 hMod) hzV hcV hz1' hcV1
  have hlV : l ∈ Subgroup.normalizer (V : Set G) := (h.hyp1223 h13322).irrPlus.2.2.1 hl
  have hPl : conjSub (g * l) V = P := by
    ext x
    rw [mem_conjSub, hP, mem_conjSub]
    constructor
    · intro hx
      have := (Subgroup.mem_normalizer_iff.mp hlV _).mp hx
      rwa [show l * ((g * l)⁻¹ * x * (g * l)) * l⁻¹ = g⁻¹ * x * g by group] at this
    · intro hx
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hlV) _).mp hx
      rwa [show l⁻¹ * (g⁻¹ * x * g) * l⁻¹⁻¹ = (g * l)⁻¹ * x * (g * l) by group] at this
  have hV1Y : conjSub (g * l) (fsuV1 T V) ≤ VY := by
    intro x hx
    rw [mem_conjSub] at hx
    by_cases hx1 : (g * l)⁻¹ * x * (g * l) = 1
    · have : x = 1 := by
        calc x = (g * l) * ((g * l)⁻¹ * x * (g * l)) * (g * l)⁻¹ := by group
          _ = 1 := by rw [hx1]; group
      rw [this]
      exact one_mem _
    · have hxz : (g * l)⁻¹ * x * (g * l) = z :=
        congrArg Subtype.val ((huniq ⟨_, hx⟩ fun e => hx1 (congrArg Subtype.val e)).trans
          (huniq ⟨z, hzV1⟩ hz1).symm)
      have : x = w * p * w⁻¹ * p⁻¹ := by
        calc x = (g * l) * ((g * l)⁻¹ * x * (g * l)) * (g * l)⁻¹ := by group
          _ = g * (l * z * l⁻¹) * g⁻¹ := by rw [hxz]; group
          _ = w * p * w⁻¹ * p⁻¹ := by rw [hlz]; group
      rw [this]
      exact hcY
  have hPC : conjSub (g * l) V ≤ Subgroup.centralizer (VY : Set G) :=
    (conjSub_mono (g * l) (le_conjClosure V _ : V ≤ fsuU T V)).trans (hU (g * l) hV1Y)
  rw [hPl] at hPC
  exact hwp (Subgroup.mem_centralizer_iff.mp (hPC hp) w hw)

theorem lemma14_7_31_two (h : Hyp147 G T L V) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) {V₂ : Subgroup G} (hV2 : A6.IsV2 T V V₂)
    (hCV : Subgroup.centralizer (V₂ : Set G) ≤ Subgroup.normalizer (L : Set G))
    {Y TY VY : Subgroup G} (hS : IsSylowTwoOf TY Y) (hidx : (pCoreOf 2 Y).relIndex TY ≤ 2)
    (hYV : Y ≤ Subgroup.normalizer (VY : Set G))
    (hO : pCoreOf 2 Y = Y ⊓ Subgroup.centralizer (VY : Set G))
    (hU : ∀ g : G, conjSub g (fsuV1 T V) ≤ VY →
      conjSub g (fsuU T V) ≤ Subgroup.centralizer (VY : Set G)) :
    Y ≤ Subgroup.normalizer (E3.wClos V 0 TY : Set G) := by
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  obtain ⟨hVel, -, -, -, -⟩ := hMod G T L V h.hyp h.fsu
  have hW : E3.wClos V 0 TY ≤ pCoreOf 2 Y := by
    refine E3.wClos_le_of_forall fun A hA => ?_
    obtain ⟨hAT, g, hAg, hm⟩ := hA
    have hAeq : A = conjSubgroup V g :=
      (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hVel) g)
        hAg).1 hm
    rw [hAeq, conjSubgroup_eq_conjSub_inv'] at hAT ⊢
    exact conjSub_le_pCoreOf_of_centralizer_V2 h h1222 h1332 h1334 hV2 hCV hS hidx hYV hO hU hAT
  rw [E3.e3_15 hS (pCoreOf_le 2 Y) (pCoreOf_isPGroup 2 Y) hW]
  exact (le_normalizer_pCoreOf 2 Y).trans (E3.normalizer_le_normalizer_wClos _)

end CFSG.Quasithin.H13.L32A

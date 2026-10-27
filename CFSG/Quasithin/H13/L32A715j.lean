module

public import CFSG.Quasithin.H13.L32A715i
public import CFSG.Quasithin.H13.L32A705a
public import CFSG.Quasithin.H13.L32A715h

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E hF

omit [Finite G] E hF in
theorem l1_eq_L₁Of : L₁Of L (fsuV1 T V) = l1 T L V := by
  rw [L₁Of, oTwoRes_eq_oTwoUpper]

omit hF in
theorem r1_le_hz : pCoreOf 2 (l1 T L V ⊔ T) ≤ hz T V :=
  (pCoreOf_le_of_le E.S.hyp le_sup_right).trans E.t_le_hz

theorem sq_eq_one_of_mem {w : G} {x : G} (hx : x ∈ Quasithin.conjSub w (fsuU T V)) : x * x = 1 := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have hU := hF.F911_3
  rw [← fsuU_eq_conjClosure_hz hMod E.S.hyp] at hU
  have h1 := hU.2 _ (Quasithin.mem_conjSub.mp hx)
  have h2 : w⁻¹ * (x * x) * w = 1 := by
    rw [← h1, sq]
    group
  calc x * x = w * (w⁻¹ * (x * x) * w) * w⁻¹ := by group
    _ = 1 := by rw [h2]; group

theorem relIndex_uα {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
    (N : Not1471 T L V (hz T V) γ γ' g k) :
    (pCoreOf 2 (hz T V)).relIndex (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2 := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h := E.S.hyp
  rw [A4.relIndex_sup_eq_of_le_normalizer' (N.uα_le_normalizer h hF)]
  have hAR : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤ pCoreOf 2 (l1 T L V ⊔ T) := by
    rw [← l1_eq_L₁Of]
    exact N.uα_le hF
  have hAhz : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤ hz T V :=
    hAR.trans E.r1_le_hz
  rw [← card_modO2Image' hAhz]
  obtain ⟨-, y, -, -, hy2, hy4, huniq, -⟩ := E.exists_y
  obtain ⟨-, -, -, -, hR1C, -⟩ := E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal
  have hsub : modO2Image (hz T V) (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G))) ≤
      Subgroup.zpowers (y ^ 2) := by
    intro x hx
    obtain ⟨u, huA, rfl⟩ := mem_modO2Image_iff.mp hx
    have hR1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) u ∈
        modO2Image (hz T V) (pCoreOf 2 (l1 T L V ⊔ T)) :=
      mem_modO2Image_iff.mpr ⟨u, hAR huA, rfl⟩
    rw [hR1C] at hR1
    by_cases h1 : QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) u = 1
    · rw [h1]
      exact Subgroup.one_mem _
    · have hu2 : u * u = 1 := Subtype.ext (by
        rw [Subgroup.coe_mul, Subgroup.coe_one]
        exact E.sq_eq_one_of_mem hF (by rw [Not1471.uα_eq h hMod] at huA; exact huA))
      have hsq : (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) u) ^ 2 = 1 := by
        rw [← map_pow, sq, hu2, map_one]
      rw [huniq _ hR1.1 hR1.2 hsq h1]
      exact Subgroup.mem_zpowers _
  have hord : Nat.card (Subgroup.zpowers (y ^ 2)) = 2 := by
    have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    rw [Nat.card_zpowers, orderOf_eq_prime (p := 2) (by rw [← pow_mul]; exact hy4) hy2]
  have hle := Subgroup.card_le_of_le hsub
  rw [hord] at hle
  have hne1 : Nat.card (modO2Image (hz T V)
      (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)))) ≠ 1 := by
    rw [card_modO2Image' hAhz]
    intro h1
    have hAQ : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤ pCoreOf 2 (hz T V) :=
      Subgroup.relIndex_eq_one.mp h1
    have hkN : (k : G) ∈ Subgroup.normalizer (pCoreOf 2 (hz T V) : Set G) :=
      le_normalizer_pCoreOf 2 _ N.mem
    have hUQ : F8.Uγ V (hz T V) (g : G) ≤ pCoreOf 2 (hz T V) := fun x hx =>
      (Subgroup.mem_normalizer_iff.mp hkN x).mpr (hAQ (Quasithin.mul_mem_conjSub hx))
    have hlt := N.dγ_lt
    rw [hF.Dγ_eq_inf_pCoreOf N.setup, inf_eq_left.mpr hUQ] at hlt
    exact lt_irrefl _ hlt
  have hpos : 0 < Nat.card (modO2Image (hz T V)
      (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)))) :=
    Nat.card_pos
  omega

theorem exists_s : ∃ s ∈ pCoreOf 2 (l1 T L V ⊔ T), s ∉ pCoreOf 2 (hz T V) ∧ s * s = 1 ∧
    ((Subgroup.centralizer ({s} : Set G)).subgroupOf (conjClosure V (hz T V))).index ≤ 4 := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h := E.S.hyp
  obtain ⟨γ, γ', g, hs⟩ := hF.exists_F8Setup
  obtain ⟨hlt, -⟩ := (E.h75 G T L V (hz T V) E.setting_hz E.l1dot_normal).1 γ γ' g hs
  obtain ⟨δ, δ', g', k', N⟩ := exists_not1471 hF hs hlt
  have h2 := E.relIndex_uα hF N
  obtain ⟨s, hsA, hsQ, -⟩ := N.exists_mem_not_mem h hMod hF h2
  have hD := N.relIndex_D h hMod hF h2
  have hZ2 : Nat.card (Quasithin.conjSub ((k' : G) * g') (fsuV1 T V)) = 2 := by
    rw [Quasithin.conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact E.card_v1
  have hidx := relIndex_centralizer_le hD hZ2 hsA
  rw [fsuU_eq_conjClosure_hz hMod h] at hidx
  have hsR : s ∈ pCoreOf 2 (l1 T L V ⊔ T) := by
    rw [← l1_eq_L₁Of]
    exact N.uα_le hF (by rw [Not1471.uα_eq h hMod]; exact hsA)
  exact ⟨s, hsR, hsQ, E.sq_eq_one_of_mem hF hsA, hidx⟩

end Ctx7153

end CFSG.Quasithin.H13.L32A

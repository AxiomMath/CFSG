module

public import CFSG.Quasithin.H13.L32A767i

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem conjSub_le_pCoreOf_of (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h13322 : Stmt13_3_2_two)
    (h672 : ∀ F : Subgroup G, F ≤ V → Nat.card F = 4 → ∀ g : G, F ≤ conjSub g V →
      conjSub g V = V)
    {Y VY : Subgroup G} (hS : IsSylowTwoOf (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) Y)
    (hidx : (pCoreOf 2 Y).relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ 2)
    (hYV : Y ≤ Subgroup.normalizer (VY : Set G))
    (hOV : pCoreOf 2 Y ≤ Subgroup.centralizer (VY : Set G))
    (hCV : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ Subgroup.centralizer (VY : Set G) ≤ pCoreOf 2 Y)
    (hU : ∀ g : G, conjSub g (fsuV1 T V) ≤ VY → conjSub g V ≤ Subgroup.centralizer (VY : Set G))
    {g : G} (hg : conjSub g V ≤ pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) :
    conjSub g V ≤ pCoreOf 2 Y := by
  obtain ⟨-, hV8, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
  set R := pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) with hR
  set P := conjSub g V with hP
  set O := pCoreOf 2 Y with hO
  have hOR : O ≤ R := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hS
  have hP8 : Nat.card P = 8 := by rw [hP, card_conjSub, hV8]
  by_contra hPO
  have hPN : P ≤ Subgroup.normalizer (O : Set G) :=
    (hg.trans hS.1).trans (le_normalizer_pCoreOf 2 Y)
  have e1 := L32NSet14.card_sup_mul_card_inf hPN
  have i1 := Subgroup.relIndex_mul_card O R
  rw [inf_eq_left.mpr hOR] at i1
  have hle := Subgroup.card_le_of_le (sup_le hg hOR)
  have hOpos : 0 < Nat.card O := Nat.card_pos
  have hA4 : Nat.card ↥(P ⊓ O) = 4 := by
    have hge : 8 ≤ 2 * Nat.card ↥(P ⊓ O) := by
      have h1 : Nat.card ↥P * Nat.card ↥O ≤ 2 * Nat.card ↥(P ⊓ O) * Nat.card ↥O := by
        rw [← e1]
        calc Nat.card ↥(P ⊔ O) * Nat.card ↥(P ⊓ O) ≤ Nat.card ↥R * Nat.card ↥(P ⊓ O) :=
              Nat.mul_le_mul_right _ hle
          _ = O.relIndex R * Nat.card ↥O * Nat.card ↥(P ⊓ O) := by rw [i1]
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
  have hVYN := hVYA.trans (centralizer_le_normalizer_conjSub h672 inf_le_left hA4)
  have hnc : ¬ P ≤ Subgroup.centralizer (VY : Set G) := fun hc => hPO ((le_inf hg hc).trans hCV)
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
  have hPC := hU (g * l) hV1Y
  rw [hPl] at hPC
  exact hwp (Subgroup.mem_centralizer_iff.mp (hPC hp) w hw)

theorem le_normalizer_wClos_R1_of (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h13322 : Stmt13_3_2_two)
    (h672 : ∀ F : Subgroup G, F ≤ V → Nat.card F = 4 → ∀ g : G, F ≤ conjSub g V →
      conjSub g V = V)
    {Y VY : Subgroup G} (hS : IsSylowTwoOf (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) Y)
    (hidx : (pCoreOf 2 Y).relIndex (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ 2)
    (hYV : Y ≤ Subgroup.normalizer (VY : Set G))
    (hOV : pCoreOf 2 Y ≤ Subgroup.centralizer (VY : Set G))
    (hCV : pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) ⊓ Subgroup.centralizer (VY : Set G) ≤ pCoreOf 2 Y)
    (hU : ∀ g : G, conjSub g (fsuV1 T V) ≤ VY →
      conjSub g V ≤ Subgroup.centralizer (VY : Set G)) :
    Y ≤ Subgroup.normalizer (E3.wClos V 0 (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) : Set G) := by
  obtain ⟨hVel, -, -, -, -⟩ := hMod G T L V h.hyp h.fsu
  have hW : E3.wClos V 0 (pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)) ≤ pCoreOf 2 Y := by
    refine E3.wClos_le_of_forall fun A hA => ?_
    obtain ⟨hAR, g, hAg, hm⟩ := hA
    have hAeq : A = conjSubgroup V g :=
      (E3.mQuot_eq_zero_iff (E3.isPGroup_conjSubgroup (B2F.isPGroup_of_isElemAbelian hVel) g)
        hAg).1 hm
    rw [hAeq, conjSubgroup_eq_conjSub_inv] at hAR ⊢
    exact conjSub_le_pCoreOf_of h hMod h13322 h672 hS hidx hYV hOV hCV hU hAR
  rw [E3.e3_15 hS (pCoreOf_le 2 Y) (pCoreOf_isPGroup 2 Y) hW]
  exact (le_normalizer_pCoreOf 2 Y).trans (E3.normalizer_le_normalizer_wClos _)

end CFSG.Quasithin.H13.L32A

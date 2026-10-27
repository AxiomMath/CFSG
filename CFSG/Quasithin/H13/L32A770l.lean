module

public import CFSG.Quasithin.Recognition.GoldschmidtStatement
public import CFSG.Quasithin.H13.L32A770h

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem exists_normal_of_edgeBound (hedge : GoldschmidtEdgeBoundSubgroups.{0})
    {A B C : Subgroup G} (hC : A ⊓ B = C) (hA : C.relIndex A = 3) (hB : C.relIndex B = 3)
    (hcard : 2 ^ 7 < Nat.card ↥C) :
    ∃ N : Subgroup G, N ≠ ⊥ ∧ N ≤ C ∧ A ⊔ B ≤ Subgroup.normalizer (N : Set G) := by
  set I := A ⊔ B with hI
  have hAI : A ≤ I := le_sup_left
  have hBI : B ≤ I := le_sup_right
  have hCI : C ≤ I := hC ▸ inf_le_left.trans hAI
  have hinf : A.subgroupOf I ⊓ B.subgroupOf I = C.subgroupOf I := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf, ← hC]
  by_contra hno
  push Not at hno
  have hle := hedge ↥I (A.subgroupOf I) (B.subgroupOf I)
    (by rw [← Subgroup.subgroupOf_sup hAI hBI, Subgroup.subgroupOf_self])
    (by rw [hinf, Subgroup.relIndex_subgroupOf hAI]; exact hA)
    (by rw [hinf, Subgroup.relIndex_subgroupOf hBI]; exact hB) ?_
  · rw [hinf, Nat.card_congr (Subgroup.subgroupOfEquivOfLe hCI).toEquiv] at hle
    omega
  · intro N hN hNle
    by_contra hN1
    refine hno (N.map I.subtype) ?_ ?_ ?_
    · intro hb
      apply hN1
      rw [eq_bot_iff]
      intro x hx
      have : (x : G) ∈ N.map I.subtype := ⟨x, hx, rfl⟩
      rw [hb, Subgroup.mem_bot] at this
      exact Subtype.ext this
    · rintro _ ⟨x, hx, rfl⟩
      have := hNle hx
      rw [hinf, Subgroup.mem_subgroupOf] at this
      exact this
    · intro i hi
      rw [Subgroup.mem_normalizer_iff]
      intro y
      constructor
      · rintro ⟨n, hn, rfl⟩
        exact ⟨⟨i, hi⟩ * n * ⟨i, hi⟩⁻¹, hN.conj_mem n hn _, rfl⟩
      · rintro ⟨n, hn, hny⟩
        refine ⟨⟨i, hi⟩⁻¹ * n * (⟨i, hi⟩⁻¹)⁻¹, hN.conj_mem n hn _, ?_⟩
        simp only [Subgroup.subtype_apply, Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
        rw [show (n : G) = i * y * i⁻¹ from hny]
        group

omit [Finite G] in
theorem eq_one_or_eq_of_card_two {A : Subgroup G} (hA : Nat.card A = 2) {a : G} (ha : a ∈ A)
    (ha1 : a ≠ 1) : ∀ x ∈ A, x = 1 ∨ x = a := by
  obtain ⟨b, hb, -, hgen⟩ := exists_gen_of_card_two hA
  have hab : a = b := (hgen a ha).resolve_left ha1
  rw [hab]
  exact hgen

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

omit N [Finite G] in
theorem card_zα (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) :
    Nat.card ↥(conjSub ((k : G) * g) (fsuV1 T V)) = 2 := by
  rw [conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
  exact hF.card_V₁

theorem exists_q (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) {z zα : G} (hz0 : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (hzα : zα ∈ conjSub ((k : G) * g) (fsuV1 T V)) (hzα1 : zα ≠ 1) :
    ∃ q ∈ pCoreOf 2 (hz T V), q * zα * q⁻¹ = z * zα := by
  have he := N.commutator_zα_eq h hMod h63 hF h1222 h1332 h1334 h13314 h68 h2
  have hZU := N.zα_le_U h hMod h63 hF h1222 h1332 h1334 h2
  have hgen := eq_one_or_eq_of_card_two hF.card_V₁ hz0 hz1
  have hgenα := eq_one_or_eq_of_card_two (card_zα (g := g) (k := k) hF) hzα hzα1
  by_contra hno
  push Not at hno
  have hfix : ∀ q ∈ pCoreOf 2 (hz T V), q * zα = zα * q := by
    intro q hq
    rcases hgen _ (comm_mem_of_pCoreOf h hMod hF hq (hZU hzα)) with e | e
    · calc q * zα = q * zα * q⁻¹ * zα⁻¹ * (zα * q) := by group
        _ = zα * q := by rw [e, one_mul]
    · exact absurd (by
        calc q * zα * q⁻¹ = q * zα * q⁻¹ * zα⁻¹ * zα := by group
          _ = z * zα := by rw [e]) (hno q hq)
  have hb : ⁅conjSub ((k : G) * g) (fsuV1 T V), pCoreOf 2 (hz T V)⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw q hq
    rw [Subgroup.mem_bot, commutatorElement_def]
    rcases hgenα w hw with rfl | rfl
    · group
    · rw [← hfix q hq, mul_inv_cancel_right, mul_inv_cancel]
  rw [he] at hb
  have := hF.card_V₁
  rw [hb, Subgroup.card_bot] at this
  omega

theorem exists_a (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h68 : Lemma14_7_68)
    (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) {z zα : G} (hz0 : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (hzα : zα ∈ conjSub ((k : G) * g) (fsuV1 T V)) (hzα1 : zα ≠ 1) :
    ∃ a ∈ conjSub ((k : G) * g) (pCoreOf 2 (hz T V)), a * z * a⁻¹ = zα * z := by
  have he := N.commutator_v1_eq h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2
  have hzW : z ∈ conjSub ((k : G) * g) (fsuU T V) :=
    N.F_le_Uα h hMod hF h2 (N.v1_le h hMod h63 hF h1222 h1332 h1334 h69 h2 hz0)
  have hgen := eq_one_or_eq_of_card_two hF.card_V₁ hz0 hz1
  have hgenα := eq_one_or_eq_of_card_two (card_zα (g := g) (k := k) hF) hzα hzα1
  by_contra hno
  push Not at hno
  have hfix : ∀ a ∈ conjSub ((k : G) * g) (pCoreOf 2 (hz T V)), a * z = z * a := by
    intro a ha
    rcases hgenα _ (comm_mem_zα h hMod hF ha hzW) with e | e
    · calc a * z = a * z * a⁻¹ * z⁻¹ * (z * a) := by group
        _ = z * a := by rw [e, one_mul]
    · exact absurd (by
        calc a * z * a⁻¹ = a * z * a⁻¹ * z⁻¹ * z := by group
          _ = zα * z := by rw [e]) (hno a ha)
  have hb : ⁅fsuV1 T V, conjSub ((k : G) * g) (pCoreOf 2 (hz T V))⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro w hw a ha
    rw [Subgroup.mem_bot, commutatorElement_def]
    rcases hgen w hw with rfl | rfl
    · group
    · rw [← hfix a ha, mul_inv_cancel_right, mul_inv_cancel]
  rw [he] at hb
  have := card_zα (g := g) (k := k) hF
  rw [hb, Subgroup.card_bot] at this
  omega

theorem mem_E (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) {z zα : G} (hz0 : z ∈ fsuV1 T V) (hz1 : z ≠ 1)
    (hzα : zα ∈ conjSub ((k : G) * g) (fsuV1 T V)) (hzα1 : zα ≠ 1) :
    ∀ e ∈ fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V),
      e = 1 ∨ e = z ∨ e = zα ∨ e = z * zα := by
  have hZU := N.zα_le_U h hMod h63 hF h1222 h1332 h1334 h2
  have hUH : fsuU T V ≤ hz T V := by
    rw [fsuU_eq_conjClosure_hz hMod h]
    exact hF.conjClosure_Vp_le_pCoreOf.trans (pCoreOf_le 2 _)
  have hZN : conjSub ((k : G) * g) (fsuV1 T V) ≤ Subgroup.normalizer (fsuV1 T V : Set G) :=
    (hZU.trans hUH).trans hF.H_normalizes_V₁
  have hgen := eq_one_or_eq_of_card_two hF.card_V₁ hz0 hz1
  have hgenα := eq_one_or_eq_of_card_two (card_zα (g := g) (k := k) hF) hzα hzα1
  intro e he
  rw [← SetLike.mem_coe, Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZN] at he
  obtain ⟨c, hc, d, hd, rfl⟩ := he
  rcases hgen c hc with rfl | rfl <;> rcases hgenα d hd with rfl | rfl
  · left; simp
  · right; right; left; simp
  · right; left; simp
  · right; right; right; rfl

end Not1471

end CFSG.Quasithin.H13.L32A

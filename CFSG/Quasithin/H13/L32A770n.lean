module

public import CFSG.Quasithin.H13.L32A770m
public import CFSG.Quasithin.EmptyFaithful.S1422Basic
public import CFSG.Quasithin.H13.L32A770j

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open CFSG.Quasithin.CosetGeom
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

theorem normalizer_le_normalizer_L (h : Hyp147 G T L V) (h13322 : Stmt13_3_2_two)
    {P : Subgroup G} (hP1 : P ≠ ⊥) (hP2 : IsPGroup 2 ↥P)
    (hLT : L ⊔ T ≤ Subgroup.normalizer (P : Set G)) :
    Subgroup.normalizer (P : Set G) ≤ Subgroup.normalizer (L : Set G) := by
  have hloc : IsTwoLocal (Subgroup.normalizer (P : Set G)) := ⟨P, hP1, hP2, rfl⟩
  obtain ⟨M', hM', hNM'⟩ := exists_quasithinIsMaxTwoLocal_ge hloc
  have hM'' : quasithinIsMaxTwoLocal M' := ⟨hM'.1, fun H hH hMH => hM'.2 H hH hMH⟩
  have he := (h13322 G T L h.hyp.h13 L h.fsu.faithful).2.2.2 M' hM'' (hLT.trans hNM')
  exact he ▸ hNM'

namespace Not1471

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include N

theorem exists_r (h : Hyp147 G T L V) (hMod : StmtL32NModule) (h63 : Thm14_7_63)
    (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2)
    (h1334 : A6.Stmt13_3_4) (h68 : Lemma14_7_68)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) {zα : G} (hzα : zα ∈ conjSub ((k : G) * g) (fsuV1 T V))
    (hzα1 : zα ≠ 1) :
    ∃ r ∈ pCoreOf 2 (L₁Of L (fsuV1 T V)), r * zα * r⁻¹ ≠ zα := by
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  by_contra hno
  push Not at hno
  set P := pCoreOf 2 (L₁Of L (fsuV1 T V)) with hP
  have hPL : P ≤ L₁Of L (fsuV1 T V) := pCoreOf_le 2 _
  have hPH : P ≤ hz T V := hPL.trans (le_sup_left.trans hF.L₁T_le_H)
  have hPN : L₁Of L (fsuV1 T V) ⊔ T ≤ Subgroup.normalizer (P : Set G) := by
    refine sup_le (le_normalizer_pCoreOf 2 _) ?_
    exact S14.T_Lp.trans (normalizer_le_normalizer_pCoreOf 2 _)
  obtain ⟨s, hsW, hsQ, -⟩ := N.exists_mem_not_mem h hMod hF h2
  have hzαVU : zα ∈ V ⊔ u0 T V := by
    rw [← N.sup_u0 h hMod h63 hF h1222 h1332 h1334 hsW hsQ]
    exact Subgroup.mem_sup_left (N.zα_le h hMod h63 hF h1222 h1332 h1334 h2 hzα)
  have hPV := le_centralizer_V h hMod hF h1222 h1332 h1334 hPH hPN hzαVU
    (N.gen_not_mem_u0 h hF h68 hzα hzα1) fun p hp => by
      calc p * zα = p * zα * p⁻¹ * p := by group
        _ = zα * p := by rw [hno p hp]
  have hc := S14.comm3
  have hb : ⁅V, P⁆ = ⊥ := by
    rw [eq_bot_iff, Subgroup.commutator_le]
    intro v hv p hp
    rw [Subgroup.mem_bot, commutatorElement_def,
      show v * p = p * v from Subgroup.mem_centralizer_iff.mp (hPV hp) v hv,
      mul_inv_cancel_right, mul_inv_cancel]
  rw [hb] at hc
  have := hF.card_V₁
  rw [← hc, Subgroup.card_bot] at this
  omega

theorem exists_not_mem_normalizer_L (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h63 : Thm14_7_63) (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h64 : Remark14_7_64)
    (h68 : Lemma14_7_68) (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) (h8 : Nat.card ↥(u0 T V) = 8)
    (hTE : T ≤ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G)) :
    ∃ y ∈ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G),
      y ∉ Subgroup.normalizer (L : Set G) := by
  have h13322 := stmt13_3_2_two_of h1332
  obtain ⟨V₂, hV2⟩ := h.exists_V2 h13322 hMod h1222
  have : IsMulCommutative ↥V := (hMod G T L V h.hyp h.fsu).1.1
  have S14 := h.set14 h1222 h1332 h1334 hV2
  set E := fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) with hE
  obtain ⟨z, hz0, hz1, -⟩ := exists_gen_of_card_two hF.card_V₁
  obtain ⟨zα, hzα, hzα1, -⟩ := exists_gen_of_card_two (card_zα (g := g) (k := k) hF)
  have hzαu := N.gen_not_mem_u0 h hF h68 hzα hzα1
  have hzu : z ∈ u0 T V := fsuV1_le_u0 h hMod hz0
  have hne : zα ≠ z := fun e => hzαu (e ▸ hzu)
  have hZU := N.zα_le_U h hMod h63 hF h1222 h1332 h1334 h2
  have hzU : z ∈ fsuU T V := centralizerMod_le_left _ _ _ hzu
  obtain ⟨hUc, hUe⟩ := F7.isElemAbelian_iff.mp (isElemAbelian_fsuU_of h hMod)
  have hzz : z * z = 1 := by rw [← sq]; exact hUe z hzU
  have hcom : z * zα = zα * z := hUc z hzU zα (hZU hzα)
  have hFV := N.inf_V_eq h hMod h63 hF h1222 h1332 h1334 h64 h69 h2 h8
  have hzαF := N.zα_le h hMod h63 hF h1222 h1332 h1334 h2 hzα
  have hzzαV : z * zα ∉ V := by
    intro hm
    have hzαV : zα ∈ V := by
      rw [show zα = z⁻¹ * (z * zα) by group]
      exact mul_mem (inv_mem (hF.V₁_le_Vp hz0)) hm
    have : zα ∈ fsuV1 T V := by rw [← hFV]; exact Subgroup.mem_inf.mpr ⟨hzαF, hzαV⟩
    rcases eq_one_or_eq_of_card_two hF.card_V₁ hz0 hz1 zα this with e | e
    · exact hzα1 e
    · exact hne e
  obtain ⟨q, hqQ, hqzα⟩ := N.exists_q h hMod h63 hF h1222 h1332 h1334 h13314 h68 h2 hz0 hz1
    hzα hzα1
  obtain ⟨a, haQ, haz⟩ := N.exists_a h hMod h63 hF h1222 h1332 h1334 h13314 h68 h69 h2 hz0 hz1
    hzα hzα1
  have hqH : q ∈ hz T V := pCoreOf_le 2 _ hqQ
  have hqz : q * z * q⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp hqH z hz0
    rw [← this, mul_inv_cancel_right]
  have haα : a * zα * a⁻¹ = zα := by
    have haG : a ∈ conjSub ((k : G) * g) (hz T V) := conjSub_mono _ (pCoreOf_le 2 _) haQ
    rw [← conjSub_centralizer] at haG
    have := Subgroup.mem_centralizer_iff.mp haG zα hzα
    rw [← this, mul_inv_cancel_right]
  have hzE : z ∈ E := Subgroup.mem_sup_left hz0
  have hzαE : zα ∈ E := Subgroup.mem_sup_right hzα
  have hzzαE : z * zα ∈ E := mul_mem hzE hzαE
  have hqX : q ∈ Subgroup.normalizer (E : Set G) := mem_normalizer_E (g := g) (k := k) hF hz0
    hz1 hzα hzα1 (by rw [hqz]; exact hzE) (by rw [hqzα]; exact hzzαE)
  have haX : a ∈ Subgroup.normalizer (E : Set G) := mem_normalizer_E (g := g) (k := k) hF hz0
    hz1 hzα hzα1 (by rw [haz, ← hcom]; exact hzzαE) (by rw [haα]; exact hzαE)
  have hqc : q * z = z * q := by
    calc q * z = q * z * q⁻¹ * q := by group
      _ = z * q := by rw [hqz]
  have hqz' : q⁻¹ * z * q = z := by rw [mul_assoc, ← hqc]; group
  have hqα' : q⁻¹ * zα * q = z * zα := by
    calc q⁻¹ * zα * q = q⁻¹ * (z * (z * zα)) * q := by
          rw [show z * (z * zα) = zα by rw [← mul_assoc, hzz, one_mul]]
      _ = q⁻¹ * (z * (q * zα * q⁻¹)) * q := by rw [hqzα]
      _ = (q⁻¹ * z * q) * zα := by group
      _ = z * zα := by rw [hqz']
  set y := q⁻¹ * a with hy
  have hyz : y * z * y⁻¹ = zα := by
    calc y * z * y⁻¹ = q⁻¹ * (a * z * a⁻¹) * q := by rw [hy]; group
      _ = q⁻¹ * (zα * z) * q := by rw [haz]
      _ = (q⁻¹ * zα * q) * (q⁻¹ * z * q) := by group
      _ = z * zα * z := by rw [hqα', hqz']
      _ = zα := by rw [mul_assoc, ← hcom, ← mul_assoc, hzz, one_mul]
  have hyzα : y * zα * y⁻¹ = z * zα := by
    calc y * zα * y⁻¹ = q⁻¹ * (a * zα * a⁻¹) * q := by rw [hy]; group
      _ = z * zα := by rw [haα, hqα']
  have hzαzα : zα * zα = 1 := by rw [← sq]; exact hUe zα (hZU hzα)
  have hyzzα : y * (z * zα) * y⁻¹ = z := by
    calc y * (z * zα) * y⁻¹ = (y * z * y⁻¹) * (y * zα * y⁻¹) := by group
      _ = zα * (z * zα) := by rw [hyz, hyzα]
      _ = z := by rw [← mul_assoc, ← hcom, mul_assoc, hzαzα, mul_one]
  have hyinv : y⁻¹ * z * y = z * zα := by
    calc y⁻¹ * z * y = y⁻¹ * (y * (z * zα) * y⁻¹) * y := by rw [hyzzα]
      _ = z * zα := by group
  obtain ⟨r, hrP, hrzα1⟩ := N.exists_r h hMod h63 hF h1222 h1332 h1334 h68 h2 hzα hzα1
  have hPT : pCoreOf 2 (L₁Of L (fsuV1 T V)) ≤ T :=
    le_of_isPGroup_of_le_normalizer h (pCoreOf_isPGroup 2 _)
      (S14.T_Lp.trans (normalizer_le_normalizer_pCoreOf 2 _))
  have hrT := hPT hrP
  have hrL : r ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) (pCoreOf_le 2 _ hrP)
  have hrz : r * z * r⁻¹ = z := by
    have := Subgroup.mem_centralizer_iff.mp (hF.T_le_H hrT) z hz0
    rw [← this, mul_inv_cancel_right]
  have hrz' : r⁻¹ * z * r = z := by
    calc r⁻¹ * z * r = r⁻¹ * (r * z * r⁻¹) * r := by rw [hrz]
      _ = z := by group
  have hrzα : r * zα * r⁻¹ = z * zα := by
    have h1 := (Subgroup.mem_normalizer_iff.mp (hTE hrT) zα).mp hzαE
    rcases N.mem_E h hMod h63 hF h1222 h1332 h1334 h2 hz0 hz1 hzα hzα1 _ h1 with
      e | e | e | e
    · exfalso; apply hzα1
      calc zα = r⁻¹ * (r * zα * r⁻¹) * r := by group
        _ = 1 := by rw [e]; group
    · exfalso; apply hne
      calc zα = r⁻¹ * (r * zα * r⁻¹) * r := by group
        _ = r⁻¹ * z * r := by rw [e]
        _ = z := hrz'
    · exact absurd e hrzα1
    · exact e
  have hcomm : (y * r * y⁻¹ * r⁻¹) * z * (y * r * y⁻¹ * r⁻¹)⁻¹ = z * zα := by
    calc (y * r * y⁻¹ * r⁻¹) * z * (y * r * y⁻¹ * r⁻¹)⁻¹ =
        y * (r * (y⁻¹ * (r⁻¹ * z * r) * y) * r⁻¹) * y⁻¹ := by group
      _ = y * (r * (z * zα) * r⁻¹) * y⁻¹ := by rw [hrz', hyinv]
      _ = y * ((r * z * r⁻¹) * (r * zα * r⁻¹)) * y⁻¹ := by group
      _ = y * (z * (z * zα)) * y⁻¹ := by rw [hrz, hrzα]
      _ = y * zα * y⁻¹ := by rw [show z * (z * zα) = zα by rw [← mul_assoc, hzz, one_mul]]
      _ = z * zα := hyzα
  refine ⟨y, mul_mem (inv_mem hqX) haX, fun hyL => hzzαV ?_⟩
  have hc : y * r * y⁻¹ * r⁻¹ ∈ L :=
    mul_mem ((Subgroup.mem_normalizer_iff.mp hyL r).mp hrL) (inv_mem hrL)
  rw [← hcomm]
  exact (Subgroup.mem_normalizer_iff.mp (S14.LV hc) z).mp (hF.V₁_le_Vp hz0)

theorem false_of_normal (h : Hyp147 G T L V) (hMod : StmtL32NModule)
    (h63 : Thm14_7_63) (hF : HypF98 T V L (fsuV1 T V) V (hz T V)) (h1222 : Stmt12_2_2)
    (h1332 : Stmt13_3_2) (h1334 : A6.Stmt13_3_4) (h13314 : A6.Stmt13_3_14) (h64 : Remark14_7_64)
    (h68 : Lemma14_7_68) (h69 : Lemma14_7_69)
    (h2 : (pCoreOf 2 (hz T V)).relIndex (conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ⊔
      pCoreOf 2 (hz T V)) = 2) (h8 : Nat.card ↥(u0 T V) = 8)
    (hTE : T ≤ Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G))
    {P : Subgroup G} (hP1 : P ≠ ⊥) (hPT : P ≤ T)
    (hLT : L ⊔ T ≤ Subgroup.normalizer (P : Set G))
    (hX : Subgroup.normalizer
      ((fsuV1 T V ⊔ conjSub ((k : G) * g) (fsuV1 T V) : Subgroup G) : Set G) ≤
        Subgroup.normalizer (P : Set G)) : False := by
  obtain ⟨y, hyX, hyL⟩ := N.exists_not_mem_normalizer_L h hMod h63 hF h1222 h1332 h1334 h13314
    h64 h68 h69 h2 h8 hTE
  exact hyL (normalizer_le_normalizer_L h (stmt13_3_2_two_of h1332) hP1
    (h.fsu.sylow.1.to_le hPT) hLT (hX hyX))

end Not1471

end CFSG.Quasithin.H13.L32A

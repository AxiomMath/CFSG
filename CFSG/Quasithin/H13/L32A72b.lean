module

public import CFSG.Quasithin.H13.L32A72a
public import CFSG.Quasithin.H13.L32AL24

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

structure Ctx72 (G : Type) [Group G] [Finite G] (T L V : Subgroup G) (l₀ : G) : Prop where
  hyp : Hyp147 G T L V
  h1222 : Stmt12_2_2
  h1332 : Stmt13_3_2
  h1334 : A6.Stmt13_3_4
  h63 : Thm14_7_63
  hF : HypF98 T V L (fsuV1 T V) V (hz T V)
  card_u0 : Nat.card ↥(u0 T V) ≤ 4
  mem : l₀ ∈ L
  ne : conjSub l₀ (fsuU T V) ≠ fsuU T V
  norm : fsuU T V ≤ Subgroup.normalizer (conjSub l₀ (fsuU T V) : Set G)
  cap : fsuU T V ⊓ conjSub l₀ (fsuU T V) = V ⊔ u0 T V
  rel : V ⊔ u0 T V = ⁅fsuU T V, conjSub l₀ (fsuU T V)⁆ ⊔ V
  b3 : F8.b T V L (hz T V) = 3
  h71 : ⁅pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G), kz T V⁆ ≤ fsuU T V

omit [Finite G] in
theorem v_le_fsuU {T V : Subgroup G} : V ≤ fsuU T V := le_conjClosure V _

omit [Finite G] in
theorem u0_le_fsuU {T V : Subgroup G} : u0 T V ≤ fsuU T V := centralizerMod_le_left _ _ _

omit [Finite G] in
theorem sup_u0_le_fsuU {T V : Subgroup G} : V ⊔ u0 T V ≤ fsuU T V :=
  sup_le v_le_fsuU u0_le_fsuU

namespace Ctx72

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx72 G T L V l₀)
include C

theorem h13322 : Stmt13_3_2_two := stmt13_3_2_two_of_stmt13_3_2 C.h1332

theorem hMod : StmtL32NModule := stmtL32NModule_of_inputs C.h1332 C.h1334

theorem setting : Setting147 G T L V (hz T V) := ⟨C.hyp, C.hyp.isHzOne_hz C.h63⟩

theorem normalizer_sup {m : G} (hm : m ∈ L) (hmU : m ∈ Subgroup.normalizer (fsuU T V : Set G)) :
    m ∈ Subgroup.normalizer ((V ⊔ u0 T V : Subgroup G) : Set G) := by
  obtain ⟨-, -, hLTV, hV1, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hmV : m ∈ Subgroup.normalizer (V : Set G) := hLTV (Subgroup.mem_sup_left hm)
  have hmN : m ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := by
    rw [← inf_normalizer_fsuU C.setting C.hF C.h13322 C.hMod]
    exact Subgroup.mem_inf.mpr ⟨hm, hmU⟩
  have hmH : m ∈ hz T V := by
    have := (Subgroup.mem_inf.mp hmN).2
    rwa [normalizer_eq_centralizer_of_card_two hV1] at this
  rw [← conjSub_eq_self_iff, conjSub, Subgroup.map_sup,
    show V.map (MulAut.conj m).toMonoidHom = V from conjSub_eq_self_iff.mpr hmV,
    show (u0 T V).map (MulAut.conj m).toMonoidHom = u0 T V from
      conjSub_eq_self_iff.mpr (hz_le_normalizer_u0 C.hyp C.hMod hmH)]

theorem le_centerOf : conjClosure (V ⊔ u0 T V) L ≤ centerOf (sL T L V) := by
  refine conjClosure_le_centerOf C.setting C.hF C.h13322 C.hMod C.mem C.ne sup_u0_le_fsuU
    (fun m hm hmU => C.normalizer_sup hm hmU) fun x hx y hy => ?_
  have hxα : x ∈ conjSub l₀ (fsuU T V) := by
    rw [← C.cap] at hx
    exact (Subgroup.mem_inf.mp hx).2
  exact F7.isElemAbelian_comm
    (F7.isElemAbelian_conjSub (isElemAbelian_fsuU_of C.hyp C.hMod)) hxα hy

theorem commutator_eq :
    frattiniOf (sL T L V) = ⁅sL T L V, sL T L V⁆ ∧
      ⁅sL T L V, sL T L V⁆ = conjClosure ⁅fsuU T V, conjSub l₀ (fsuU T V)⁆ L ∧
      ⁅sL T L V, sL T L V⁆ ≤ conjClosure (V ⊔ u0 T V) L := by
  obtain ⟨h1, h2⟩ := lemma14_7_13_four C.setting C.hF C.h13322 C.hMod C.mem C.ne C.norm
  refine ⟨h1, h2, ?_⟩
  rw [h2]
  exact conjClosure_mono (C.rel ▸ le_sup_left) le_rfl

theorem not_comm : ¬ ∀ x ∈ sL T L V, ∀ y ∈ sL T L V, x * y = y * x := by
  intro hc
  have h1 := (lemma14_7_3_three C.hF).mp (by
    rw [← fsuU_eq_conjClosure_hz C.hMod C.hyp]
    exact hc)
  rw [C.b3] at h1
  exact lt_irrefl _ h1

theorem not_le : ¬ fsuU T V ≤ conjClosure (V ⊔ u0 T V) L := by
  intro hU
  apply C.not_comm
  have hUZ := hU.trans C.le_centerOf
  have hSZ : sL T L V ≤ centerOf (sL T L V) := by
    refine conjClosure_le fun l hl u hu => ?_
    have hlS : l ∈ Subgroup.normalizer (sL T L V : Set G) := le_normalizer_conjClosure _ _ hl
    have hu' := Subgroup.mem_inf.mp (hUZ hu)
    refine Subgroup.mem_inf.mpr ⟨mem_conjClosure hl hu, ?_⟩
    rw [Subgroup.mem_centralizer_iff]
    intro s hs
    have hs' : l⁻¹ * s * l ∈ sL T L V := by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hlS) s).mp hs
      simpa using this
    have h1 := Subgroup.mem_centralizer_iff.mp hu'.2 _ hs'
    calc s * (l * u * l⁻¹) = l * ((l⁻¹ * s * l) * u) * l⁻¹ := by group
      _ = l * (u * (l⁻¹ * s * l)) * l⁻¹ := by rw [h1]
      _ = l * u * l⁻¹ * s := by group
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (hSZ hy)).2 x hx)

theorem exists_x3 : ∃ x ∈ L₁Of L (fsuV1 T V), x ^ 3 = 1 ∧ x ≠ 1 ∧
    x ∉ Subgroup.centralizer (V : Set G) := by
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 C.h13322 C.hMod C.h1222
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  have S14 := C.hyp.set14 C.h1222 C.h1332 C.h1334 hV2
  obtain ⟨z, a, b, hz0, hz1, ha, haV, hb, hbV⟩ := S14.exists_basis
  have hzV₂ : z ∈ V₂ := hV2.1 hz0
  have hzV : z ∈ V := (Subgroup.mem_inf.mp hz0).1
  have haV' : a ∈ V := hV2.2.1 ha
  obtain ⟨x, hxL0, hx3, hxz, hxa, -⟩ := S14.exists_rot hzV haV' hb
    (fun h => haV (h ▸ one_mem _)) (fun h => hbV (h ▸ one_mem _))
    (fun h => haV (h ▸ hz0)) (fun h => hbV (h ▸ hzV₂)) (fun h => hbV (h ▸ ha))
    (fun h => hbV (h ▸ mul_mem hzV₂ ha))
  have hxa' : x * a * x⁻¹ ≠ a := by
    rw [hxa]
    exact fun h => hbV (h ▸ ha)
  refine ⟨x, Subgroup.subset_closure ⟨⟨hxL0, S14.mem_g1 hz0 hz1 hxz⟩, 3, by decide, hx3⟩, hx3,
    fun h => hxa' (by rw [h]; group), fun hc => hxa' ?_⟩
  rw [← Subgroup.mem_centralizer_iff.mp hc a haV', mul_inv_cancel_right]

theorem inf_eq : conjClosure (V ⊔ u0 T V) L ⊓ fsuU T V = V ⊔ u0 T V := by
  set R := conjClosure (V ⊔ u0 T V) L with hR
  have hle : V ⊔ u0 T V ≤ R ⊓ fsuU T V := le_inf (le_conjClosure _ _) sup_u0_le_fsuU
  obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hxU : x ∈ Subgroup.normalizer (fsuU T V : Set G) := by
    have hxH : x ∈ hz T V := oTwoUpper_le _ (l1_le_kz C.hyp C.hMod hxL1)
    exact le_normalizer_conjClosure V _ (by
      rwa [normalizer_eq_centralizer_of_card_two (C.hMod G T L V C.hyp.hyp C.hyp.fsu).2.2.2.1])
  have hxR : x ∈ Subgroup.normalizer (R : Set G) := le_normalizer_conjClosure _ _ hxL
  have hxN := C.normalizer_sup hxL hxU
  have h4 := (relIndex_sup_u0 C.hyp C.hMod C.h63 C.hF).2
  have hmul := Subgroup.relIndex_mul_relIndex (V ⊔ u0 T V) (R ⊓ fsuU T V) (fsuU T V) hle
    inf_le_right
  rw [h4] at hmul
  have hdvd : (V ⊔ u0 T V).relIndex (R ⊓ fsuU T V) ∣ 4 := Dvd.intro _ hmul
  have hcases : (V ⊔ u0 T V).relIndex (R ⊓ fsuU T V) = 1 ∨
      (V ⊔ u0 T V).relIndex (R ⊓ fsuU T V) = 2 ∨ (V ⊔ u0 T V).relIndex (R ⊓ fsuU T V) = 4 := by
    have : (V ⊔ u0 T V).relIndex (R ⊓ fsuU T V) ∈ Nat.divisors 4 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at this
    simpa using this
  rcases hcases with h1 | h2 | h4'
  · exact le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle
  · exfalso
    obtain ⟨w, hw, hwS⟩ : ∃ w ∈ R ⊓ fsuU T V, w ∉ V ⊔ u0 T V := by
      by_contra hne
      push Not at hne
      exact absurd (Subgroup.relIndex_eq_one.mpr hne) (by rw [h2]; norm_num)
    have hwU := (Subgroup.mem_inf.mp hw).2
    have hxw : x * w * x⁻¹ ∈ R ⊓ fsuU T V := Subgroup.mem_inf.mpr
      ⟨(Subgroup.mem_normalizer_iff.mp hxR w).mp (Subgroup.mem_inf.mp hw).1,
        (Subgroup.mem_normalizer_iff.mp hxU w).mp hwU⟩
    have hxwS : x * w * x⁻¹ ∉ V ⊔ u0 T V := fun h => hwS (by
      have := (Subgroup.mem_normalizer_iff.mp (inv_mem hxN) _).mp h
      simpa [mul_assoc] using this)
    have hcard : Nat.card ↥(R ⊓ fsuU T V) = 2 * Nat.card ↥(V ⊔ u0 T V) := by
      have := Subgroup.relIndex_mul_card (V ⊔ u0 T V) (R ⊓ fsuU T V)
      rw [inf_eq_left.mpr hle, h2] at this
      omega
    have hprod := L32NSet14.mul_mem_of_card_eq_two_mul hle hcard Nat.card_pos.ne' hxw hw hxwS
      hwS
    have hw2 : w * w = 1 := by
      rw [← pow_two]
      exact F7.isElemAbelian_pow_eq_one (isElemAbelian_fsuU_of C.hyp C.hMod) hwU
    have hww : w⁻¹ = w := inv_eq_of_mul_eq_one_right hw2
    exact hwS (mem_sup_u0_of_comm C.hyp C.hMod C.h63 hxL1 hx3 hx1 hwU (by rwa [hww]))
  · exfalso
    have h1 : (R ⊓ fsuU T V).relIndex (fsuU T V) = 1 := by
      rw [h4'] at hmul
      omega
    exact C.not_le ((Subgroup.relIndex_eq_one.mp h1).trans inf_le_left)

theorem le_pCoreOf_inf : conjClosure (V ⊔ u0 T V) L ≤
    pCoreOf 2 (hz T V) ⊓ Subgroup.centralizer (fsuU T V : Set G) := by
  intro r hr
  have hrZ := Subgroup.mem_inf.mp (C.le_centerOf hr)
  have hrC : r ∈ Subgroup.centralizer (fsuU T V : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    exact Subgroup.mem_centralizer_iff.mp hrZ.2 u (le_conjClosure _ _ hu)
  have hrH : r ∈ hz T V :=
    le_sup_right.trans C.hF.L₁T_le_H ((pCoreOf_sup_le C.hyp)
      (sL_le_pCoreOf C.setting C.hF C.hMod hrZ.1))
  refine Subgroup.mem_inf.mpr ⟨?_, hrC⟩
  rw [C.hF.pCoreOf_eq_centralizerMod, ← fsuU_eq_conjClosure_hz C.hMod C.hyp]
  refine ⟨hrH, C.hF.H_normalizes_V₁ hrH, fun u hu => ?_⟩
  rw [← Subgroup.mem_centralizer_iff.mp hrC u hu, mul_inv_cancel_right, mul_inv_cancel]
  exact one_mem _

theorem l1_le_trivSub :
    L₁Of L (fsuV1 T V) ≤ L32NSet14.trivSub (conjClosure (V ⊔ u0 T V) L) V := by
  set R := conjClosure (V ⊔ u0 T V) L with hR
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have hRc : ∀ a ∈ R, ∀ b ∈ R, a * b = b * a := fun a ha b hb =>
    (Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (C.le_centerOf hb)).2 a
      (Subgroup.mem_inf.mp (C.le_centerOf ha)).1)
  have hVN : V ≤ Subgroup.normalizer (u0 T V : Set G) := by
    intro v hv
    rw [Subgroup.mem_normalizer_iff]
    intro x
    constructor
    · intro hx
      rw [F7.isElemAbelian_comm hUe (v_le_fsuU hv) (u0_le_fsuU hx), mul_inv_cancel_right]
      exact hx
    · intro hx
      have hxU : x ∈ fsuU T V := by
        have := mul_mem (mul_mem (inv_mem (v_le_fsuU hv)) (u0_le_fsuU hx)) (v_le_fsuU hv)
        rwa [show v⁻¹ * (v * x * v⁻¹) * v = x by group] at this
      rwa [F7.isElemAbelian_comm hUe (v_le_fsuU hv) hxU, mul_inv_cancel_right] at hx
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨hyLN, m, hm, hym⟩
  have hyL : y ∈ L := (Subgroup.mem_inf.mp hyLN).1
  have hyK : y ∈ kz T V := l1_le_kz C.hyp C.hMod (Subgroup.subset_closure ⟨hyLN, m, hm, hym⟩)
  have hyV : y ∈ Subgroup.normalizer (V : Set G) := hLTV (Subgroup.mem_sup_left hyL)
  have hyR : y ∈ Subgroup.normalizer (R : Set G) := le_normalizer_conjClosure _ _ hyL
  refine ⟨hyR, hyV, fun r hr => ?_⟩
  refine comm_mem_of_two_step hm hym hRc le_sup_left (le_conjClosure _ _) hyV
    (fun a ha => by rw [F7.isElemAbelian_pow_eq_one hUe (sup_u0_le_fsuU ha)]; exact one_mem _)
    (fun x hx => ?_) (fun a ha => ?_) hr
  ·
    rw [← C.inf_eq]
    refine Subgroup.mem_inf.mpr ⟨?_, ?_⟩
    · exact mul_mem ((Subgroup.mem_normalizer_iff.mp hyR x).mp hx) (inv_mem hx)
    · have := C.h71 (Subgroup.commutator_mem_commutator (C.le_pCoreOf_inf hx) hyK)
      have := inv_mem this
      rwa [show ⁅x, y⁆⁻¹ = y * x * y⁻¹ * x⁻¹ by simp only [commutatorElement_def]; group]
        at this
  ·
    have ha' : a ∈ ((V : Set G) * (u0 T V : Set G)) := by
      rw [← Subgroup.coe_mul_of_left_le_normalizer_right _ _ hVN]
      exact ha
    obtain ⟨v, hv, u, hu, rfl⟩ := ha'
    have hyu : y * u * y⁻¹ * u⁻¹ ∈ fsuV1 T V := ((mem_u0_iff C.hyp C.hMod).mp hu).2 y hyK
    have hyv : y * v * y⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp hyV v).mp hv
    have hc := (Subgroup.mem_inf.mp hyu).1
    have hyuU : y * u * y⁻¹ ∈ fsuU T V :=
      (Subgroup.mem_normalizer_iff.mp (le_normalizer_conjClosure V _ (by
        rw [normalizer_eq_centralizer_of_card_two
          (C.hMod G T L V C.hyp.hyp C.hyp.fsu).2.2.2.1]
        exact oTwoUpper_le _ hyK)) u).mp (u0_le_fsuU hu)
    show y * (v * u) * y⁻¹ * (v * u)⁻¹ ∈ V
    have e : y * (v * u) * y⁻¹ * (v * u)⁻¹ =
        (y * v * y⁻¹) * ((y * u * y⁻¹ * u⁻¹) * v⁻¹) := by
      have h1 : u * v = v * u := F7.isElemAbelian_comm hUe (u0_le_fsuU hu) (v_le_fsuU hv)
      have h2 := F7.isElemAbelian_comm hUe hyuU (v_le_fsuU hv)
      calc y * (v * u) * y⁻¹ * (v * u)⁻¹ = (y * v * y⁻¹) * (y * u * y⁻¹) * u⁻¹ * v⁻¹ := by
            group
        _ = (y * v * y⁻¹) * ((y * u * y⁻¹ * u⁻¹) * v⁻¹) := by group
    rw [e]
    exact mul_mem hyv (mul_mem hc (inv_mem hv))

theorem eq : conjClosure (V ⊔ u0 T V) L = V ⊔ u0 T V ∧
    ∀ l ∈ L, ∀ r ∈ conjClosure (V ⊔ u0 T V) L, l * r * l⁻¹ * r⁻¹ ∈ V := by
  set R := conjClosure (V ⊔ u0 T V) L with hR
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  obtain ⟨x, hxL1, -, -, hxV⟩ := C.exists_x3
  have hN : L ⊓ L32NSet14.trivSub R V = L := by
    refine normal_eq_of_not_mem_centralizer C.hyp C.h13322 C.hMod C.h1222 C.h1332 C.h1334
      inf_le_left (fun l hl n hn => Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      (Subgroup.mem_inf.mpr ⟨(L32NSet14.Setting.L1_le.trans inf_le_left) hxL1,
        C.l1_le_trivSub hxL1⟩) hxV
    · exact mul_mem (mul_mem hl (Subgroup.mem_inf.mp hn).1) (inv_mem hl)
    · exact L32NSet14.conj_mem_trivSub (le_normalizer_conjClosure _ _ hl)
        (hLTV (Subgroup.mem_sup_left hl)) (Subgroup.mem_inf.mp hn).2
  have hall : ∀ l ∈ L, ∀ r ∈ R, l * r * l⁻¹ * r⁻¹ ∈ V := fun l hl r hr => by
    rw [← hN] at hl
    exact ((Subgroup.mem_inf.mp hl).2).2.2 r hr
  refine ⟨le_antisymm (conjClosure_le fun l hl w hw => ?_) (le_conjClosure _ _), hall⟩
  have h1 := hall l hl w (le_conjClosure _ _ hw)
  rw [show l * w * l⁻¹ = (l * w * l⁻¹ * w⁻¹) * w by group]
  exact mul_mem (Subgroup.mem_sup_left h1) hw

end Ctx72

end CFSG.Quasithin.H13.L32A

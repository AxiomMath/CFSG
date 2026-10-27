module

public import CFSG.Quasithin.H13.L32A716c
public import CFSG.Quasithin.H13.L32AC50d
public import CFSG.Quasithin.EmptyFaithful.SzN22Basic

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped commutatorElement

namespace Ctx7153

variable {G : Type} [Group G] [Finite G] {T L V H : Subgroup G} (E : Ctx7153 G T L V H)
  (hF : HypF98 T V L (fsuV1 T V) V (hz T V))
include E

theorem inf_normalizer_v1_le :
    L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) ≤ l1 T L V ⊔ T := by
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 E.h1332
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have hTL : T ≤ Subgroup.normalizer (L : Set G) := E.S.hyp.normalizes h13322
  have hTV1 : T ≤ Subgroup.normalizer (fsuV1 T V : Set G) := (E.S.hyp.isTSub_V1 hMod).2.2
  have hT : IsSylowTwoOf T (⊤ : Subgroup G) := by
    refine ⟨le_top, E.S.hyp.fsu.sylow.1, ?_⟩
    rw [← Subgroup.relIndex, Subgroup.relIndex_top_right]
    exact E.S.hyp.fsu.sylow.2
  have hTLs : IsSylowTwoOf (T ⊓ L) L := SzN22.isSylowTwoOf_inf_normalized hT le_top hTL
  have hTLX : T ⊓ L ≤ Subgroup.normalizer
      ((L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) : Subgroup G) : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have hL := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer ht.2) x
    have hV := Subgroup.mem_normalizer_iff.mp (Subgroup.le_normalizer (hTV1 ht.1)) x
    simp only [Subgroup.mem_inf]
    rw [hL, hV]
  have hS := SzN22.isSylowTwoOf_inf_normalized hTLs inf_le_left hTLX
  have hsup := C.oTwoUpper_sup_of_sylow hS
  rw [← hsup]
  exact sup_le le_sup_left (inf_le_left.trans (inf_le_left.trans le_sup_right))

variable {γ γ' : F8.Geom T L (hz T V)} {g k : ↥((L ⊔ T) ⊔ hz T V)}
  (N : Not1471 T L V (hz T V) γ γ' g k)
include hF N

theorem ualpha_ne : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≠ fsuU T V := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  intro e
  obtain ⟨s, hsA, hsQ, -⟩ := N.exists_mem_not_mem E.S.hyp hMod hF (E.relIndex_uα hF N)
  rw [← Not1471.uα_eq E.S.hyp hMod, e, E.fsuU_eq] at hsA
  exact hsQ (hF.toHypF91.conjClosure_Vp_le_pCoreOf hsA)

theorem conj_cases : ∀ l ∈ L, Quasithin.conjSub l (fsuU T V) = fsuU T V ∨
    ∃ x ∈ l1 T L V ⊔ T, Quasithin.conjSub l (fsuU T V) =
      Quasithin.conjSub x (Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G))) := by
  intro l hl
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 E.h1332
  by_cases hU : Quasithin.conjSub l (fsuU T V) = fsuU T V
  · exact Or.inl hU
  right
  obtain ⟨-, l₀, hl₀, hl₀U⟩ := E.lemma14_7_16_four_five hF N
  have hne : Quasithin.conjSub 1 (fsuU T V) ≠ Quasithin.conjSub l₀ (fsuU T V) := by
    rw [Quasithin.conjSub_one, ← hl₀U]
    exact (E.ualpha_ne hF N).symm
  have hne2 : Quasithin.conjSub 1 (fsuU T V) ≠ Quasithin.conjSub l (fsuU T V) := by
    rw [Quasithin.conjSub_one]
    exact Ne.symm hU
  obtain ⟨l', hl', h1, h2⟩ := lemma14_7_12_one E.setting_hz hF h13322 hMod (one_mem L) hl₀
    (one_mem L) hl hne hne2
  rw [mul_one, Quasithin.conjSub_one] at h1
  have hl'N : l' ∈ L ⊓ Subgroup.normalizer (fsuV1 T V : Set G) := by
    rw [← inf_normalizer_fsuU E.setting_hz hF h13322 hMod]
    exact ⟨hl', conjSub_eq_self_iff.mp h1⟩
  refine ⟨l', E.inf_normalizer_v1_le hl'N, ?_⟩
  rw [← h2, Quasithin.conjSub_mul, hl₀U]

theorem ualpha_le_q : Quasithin.conjSub (k : G) (F8.Uγ V (hz T V) (g : G)) ≤
    pCoreOf 2 (L ⊔ T) := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  obtain ⟨-, l₀, hl₀, hl₀U⟩ := E.lemma14_7_16_four_five hF N
  rw [hl₀U]
  refine le_trans ?_ (sL_le_pCoreOf E.setting_hz hF hMod)
  rintro _ ⟨u, hu, rfl⟩
  exact mem_conjClosure hl₀ hu

theorem v1_le_e : fsuV1 T V ≤ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 E.h1332
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨hV, hZ⟩ := E.comm_ualpha hF N
  have hZE : Quasithin.conjSub ((k : G) * g) (fsuV1 T V) ≤ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ :=
    hZ.trans (Subgroup.commutator_mono le_rfl (E.ualpha_le_q hF N))
  have hZV : Quasithin.conjSub ((k : G) * g) (fsuV1 T V) ≤ V := hZ.trans (le_sup_left.trans hV.le)
  have hVT : V ≤ T := (V_le_pCoreOf_LT E.S.hyp h13322).trans (pCoreOf_le_of_le E.S.hyp le_sup_right)
  have hcardZ : Nat.card ↥(Quasithin.conjSub ((k : G) * g) (fsuV1 T V)) = 2 := by
    rw [Quasithin.conjSub, Subgroup.card_map_of_injective (MulAut.conj _).injective]
    exact E.card_v1
  have hTU : T ≤ Subgroup.normalizer (fsuU T V : Set G) :=
    E.t_le_hz.trans (hz_le_normalizer_U E.S.hyp hMod)
  have hTQ : T ≤ Subgroup.normalizer (pCoreOf 2 (L ⊔ T) : Set G) :=
    le_sup_right.trans (le_normalizer_pCoreOf 2 _)
  have hTE : T ≤ Subgroup.normalizer
      ((⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ : Subgroup G) : Set G) := by
    intro t ht
    rw [← conjSub_eq_self_iff, Quasithin.conjSub, Subgroup.map_commutator]
    change ⁅Quasithin.conjSub t (fsuU T V), Quasithin.conjSub t (pCoreOf 2 (L ⊔ T))⁆ = _
    rw [conjSub_eq_self_iff.mpr (hTU ht), conjSub_eq_self_iff.mpr (hTQ ht)]
  have hTV : T ≤ Subgroup.normalizer (V : Set G) := by
    obtain ⟨-, -, hLTV, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
    exact le_sup_right.trans hLTV
  set X := ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ ⊓ V with hX
  have hXT : X ≤ T := inf_le_right.trans hVT
  have hTX : T ≤ Subgroup.normalizer (X : Set G) := by
    intro t ht
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (hTE ht) x
    have h2 := Subgroup.mem_normalizer_iff.mp (hTV ht) x
    simp only [hX, Subgroup.mem_inf]
    rw [h1, h2]
  have hT2 : IsPGroup 2 ↥T := E.S.hyp.fsu.sylow.1
  have : Group.IsNilpotent ↥T := hT2.isNilpotent
  have : (X.subgroupOf T).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hTX
  have hne : X.subgroupOf T ≠ ⊥ := by
    intro hb
    have hZX : Quasithin.conjSub ((k : G) * g) (fsuV1 T V) ≤ X := le_inf hZE hZV
    have : X = ⊥ := by
      rw [eq_bot_iff]
      intro x hx
      have : (⟨x, hXT hx⟩ : ↥T) ∈ X.subgroupOf T := Subgroup.mem_subgroupOf.mpr hx
      rw [hb, Subgroup.mem_bot] at this
      exact Subgroup.mem_bot.mpr (congrArg Subtype.val this)
    have hc := Subgroup.card_le_of_le hZX
    rw [this, Subgroup.card_bot, hcardZ] at hc
    omega
  obtain ⟨⟨x, hxNZ⟩, hx1⟩ := (Subgroup.ne_bot_iff_exists_ne_one.mp
    (Group.IsNilpotent.inf_center_ne_bot_of_normal hne))
  obtain ⟨hxX, hxZ⟩ := hxNZ
  have hxX' : (x : G) ∈ X := Subgroup.mem_subgroupOf.mp hxX
  have hx1' : (x : G) ≠ 1 := fun e => hx1 (Subtype.ext (Subtype.ext e))
  have hxV1 : (x : G) ∈ fsuV1 T V := by
    refine ⟨hxX'.2, Subgroup.subset_closure ⟨⟨x.2, ?_⟩, ?_⟩⟩
    · exact Subgroup.mem_centralizer_iff.mpr fun t ht =>
        congrArg Subtype.val (Subgroup.mem_center_iff.mp hxZ ⟨t, ht⟩)
    · obtain ⟨hVe, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
      exact hVe.2 _ hxX'.2
  refine le_of_card_eq_two_of_inf_ne_bot E.card_v1 ?_
  intro hb
  apply hx1'
  have : (x : G) ∈ fsuV1 T V ⊓ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := ⟨hxV1, hxX'.1⟩
  rw [hb] at this
  exact this

theorem v_le_e : V ≤ ⁅fsuU T V, pCoreOf 2 (L ⊔ T)⁆ := by
  have h := (E.comm_ualpha hF N).1
  intro v hv
  rw [← h] at hv
  exact (sup_le (Subgroup.commutator_mono le_rfl (E.ualpha_le_q hF N)) (E.v1_le_e hF N)) hv

omit N in
theorem fpf_mod_v : ∀ u ∈ fsuU T V, (∀ l ∈ l1 T L V, l * u * l⁻¹ * u⁻¹ ∈ V) → u ∈ V := by
  intro u hu hlu
  have hMod := stmtL32NModule_of_inputs E.h1332 E.h1334
  set hh := hF.toHypF91 with hhdef
  obtain ⟨-, -, c, -, -, -, hcL, -, hc3, -, -, -, -, -, -, -, -, hfpf, -⟩ := E.exists_frame hF
  obtain ⟨l₀, hl₀L, rfl⟩ := mem_modO2Image_iff.mp hcL
  have huU : u ∈ conjClosure V (hz T V) := E.fsuU_eq ▸ hu
  have hVU : V ≤ conjClosure V (hz T V) := le_conjClosure V _
  set φ := rhoDot hh (QuotientGroup.mk' (CFSG.pCore 2 ↥(hz T V)) l₀) with hφdef
  have hφ3 : φ ^ 3 = 1 := by rw [hφdef, ← map_pow, hc3, map_one]
  have h1 : (l₀ : G) * u * (l₀ : G)⁻¹ ∈ conjClosure V (hz T V) := conj_mem_UH l₀.2 huU
  have hx : clsU hh h1 * (clsU hh huU)⁻¹ ∈ Wsub hh V := by
    rw [clsU_inv, clsU_mul]
    exact clsU_mem_Wsub hh _ (hlu l₀ hl₀L)
  have hV : ∀ w ∈ Wsub hh V, φ w ∈ Wsub hh V := by
    intro w hw
    obtain ⟨-, -, hLTV, -⟩ := hMod G T L V E.S.hyp.hyp E.S.hyp.fsu
    refine rhoH_mem_Wsub hh l₀ hVU ?_ hw
    exact conjSub_eq_self_iff.mpr (le_sup_left.trans hLTV ((oTwoUpper_le _).trans inf_le_left hl₀L))
  have hcls : φ (clsU hh huU) = clsU hh h1 := rhoH_clsU hh l₀ huU
  have horb := HeisMod.orbit_prod hφ3 hfpf (clsU hh huU)
  have hW2 := umod_sq hh
  have hinv : ∀ w : UMod hh, w⁻¹ = w := fun w => inv_eq_of_mul_eq_one_left (hW2 w)
  have hkey : φ (clsU hh h1 * (clsU hh huU)⁻¹) = clsU hh huU := by
    rw [← hcls, map_mul, map_inv, hinv]
    have h3 : φ (φ (clsU hh huU)) = (clsU hh huU * φ (clsU hh huU))⁻¹ :=
      eq_inv_of_mul_eq_one_right horb
    rw [h3, hinv, mul_assoc, hW2, mul_one]
  have hmem : clsU hh huU ∈ Wsub hh V := hkey ▸ hV _ hx
  obtain ⟨v, hvU, hvV, hve⟩ := exists_clsU_of_mem_Wsub hh hVU hmem
  have h2 : v⁻¹ * u ∈ fsuV1 T V := (clsU_eq_iff _ hvU huU).mp hve
  have e : u = v * (v⁻¹ * u) := by group
  rw [e]
  exact V.mul_mem hvV (Subgroup.mem_inf.mp h2).1

end Ctx7153

end CFSG.Quasithin.H13.L32A

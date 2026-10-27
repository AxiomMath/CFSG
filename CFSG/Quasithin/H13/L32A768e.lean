module

public import CFSG.Quasithin.H13.L32A768d
public import CFSG.Quasithin.Background.C1CampbellConnect
public import CFSG.Quasithin.H13.U3L134

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.RuType

variable {G : Type} [Group G] [Finite G] {T L V : Subgroup G}

omit [Finite G] in
theorem le_normalizer_of_le_centerOf {C X : Subgroup G} (h : C ≤ centerOf X) :
    X ≤ Subgroup.normalizer (C : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff]
  intro c
  constructor
  · intro hc
    rw [Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h hc)).2 x hx,
      mul_inv_cancel_right]
    exact hc
  · intro hc
    have e := Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (h hc)).2 x hx
    rw [show x * c * x⁻¹ * x = x * c by group] at e
    rwa [← mul_left_cancel e]

theorem isSylowTwoOf_of_inf_normalizer_le {S Y X : Subgroup G} (hS : IsSylowTwoOf S Y)
    (hYX : Y ≤ X) (hN : X ⊓ Subgroup.normalizer (S : Set G) ≤ Y) : IsSylowTwoOf S X := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨P, hSP, hP⟩ := exists_isSylowTwoOf_of_le (hS.1.trans hYX) hS.2.1
  by_cases hSP' : S = P
  · rw [hSP']
    exact hP
  exfalso
  obtain ⟨x, hx, hxS⟩ := exists_mem_inf_normalizer_of_ne hP.2.1 hSP hSP'
  obtain ⟨hxP, hxN⟩ := Subgroup.mem_inf.mp hx
  have hxY : x ∈ Y := hN (Subgroup.mem_inf.mpr ⟨hP.1 hxP, hxN⟩)
  have hW := hS.eq_of_le (le_sup_left : S ≤ S ⊔ Subgroup.zpowers x)
    (sup_le hS.1 ((Subgroup.zpowers_le).mpr hxY))
    (hP.2.1.to_le (sup_le hSP ((Subgroup.zpowers_le).mpr hxP)))
  exact hxS (hW ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers x))

namespace Ctx764

variable (C : Ctx764 G T L V)
include C

theorem isSylowTwoOf_tU_centralizer (h13314 : A6.Stmt13_3_14) (h674 : Lemma14_7_67_four)
    (h118 : TheoremC118) (h126 : TheoremC126) {u : G} (hu : u ∈ u0 T V)
    (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    QuasithinUnique.IsSylowTwoOf (tU T u) (Subgroup.centralizer ({u} : Set G)) := by
  have h := C.hyp
  have hMod := C.hMod
  have h63 := C.h63
  obtain ⟨C₁, C₂, hGN⟩ := exists_isGNChoice (G := G) h118
  have hSyl := isSylowTwoOf_tU h hMod h63 hu hT
  have hc := h126 G C₁ C₂ hGN (yU T V u) (tU T u) (isSQTKTC_yU h hMod h63 hu) hSyl
    (charTwo_yU h h63 hT) (isMinParabolicOf_yU h hMod h63 hu hT)
  have htU2 : IsPGroup 2 (tU T u) := hSyl.2.1
  have htU1 : tU T u ≠ ⊥ := by
    obtain ⟨-, -, -, hV1, -⟩ := hMod G T L V h.hyp h.fsu
    have hV1U : fsuV1 T V ≤ fsuU T V := inf_le_left.trans (le_conjClosure V _)
    have huU : u ∈ fsuU T V := centralizerMod_le_left _ _ _ hu
    have hV1T : fsuV1 T V ≤ T :=
      inf_le_right.trans ((Subgroup.closure_le T).mpr fun _ hx => hx.1.1)
    have hle : fsuV1 T V ≤ tU T u := fun z hz => Subgroup.mem_inf.mpr ⟨hV1T hz,
      Subgroup.mem_centralizer_singleton_iff.mpr (fsuU_comm h (hV1U hz) huU)⟩
    intro hb
    rw [hb, le_bot_iff] at hle
    rw [hle, Subgroup.card_bot] at hV1
    omega
  obtain ⟨hC1, hC1Z, hC1c, hC2, hC2B, hC2c, -⟩ := hGN.pair (tU T u) htU2 htU1
  obtain ⟨Cs, hCs1, hCsT, hCsY, hCsN⟩ : ∃ Cs : Subgroup G, Cs ≠ ⊥ ∧ Cs ≤ tU T u ∧
      yU T V u ≤ Subgroup.normalizer (Cs : Set G) ∧
      Subgroup.normalizer (tU T u : Set G) ≤ Subgroup.normalizer (Cs : Set G) := by
    have hC1T : C₁ (tU T u) ≤ tU T u := hC1Z.trans (C1GN.omegaOneCenterOf_le_self _)
    have hC2T : C₂ (tU T u) ≤ tU T u := hC2B.trans (C1GN.baum_le _)
    rcases hc with h1 | h2 | ⟨r, Kb, hr, hb, hcomm, hsup, -, -⟩
    · refine ⟨C₁ (tU T u), hC1, hC1T, le_normalizer_of_le_centerOf h1, ?_⟩
      have := normalizer_le_normalizer_map_of_characteristic ((C₁ (tU T u)).subgroupOf (tU T u))
      rwa [Subgroup.map_subgroupOf_eq_of_le hC1T] at this
    · refine ⟨C₂ (tU T u), hC2, hC2T, h2, ?_⟩
      have hch : ((C₂ (tU T u)).subgroupOf (tU T u)).Characteristic :=
        C1GN.characteristic_subgroupOf_trans (C1GN.baum_le _) hC2B (C1GN.characteristic_baum _)
          hC2c
      have := normalizer_le_normalizer_map_of_characteristic ((C₂ (tU T u)).subgroupOf (tU T u))
      rwa [Subgroup.map_subgroupOf_eq_of_le hC2T] at this
    · exact (C.false_of_blocks h13314 hr (fun i => (hb i).1) hcomm hsup).elim
  have hHC : hz T V ≤ Subgroup.normalizer (Cs : Set G) := by
    rw [(h63 G T L V h).2.2.1]
    exact sup_le (le_sup_left.trans hCsY) ((T_le_normalizer_tU hT).trans hCsN)
  have hNC : Subgroup.normalizer (Cs : Set G) = hz T V :=
    (h674 G T L V h).2.2 _ ⟨Cs, hCs1, htU2.to_le hCsT, rfl⟩ hHC
  refine isSylowTwoOf_of_inf_normalizer_le hSyl (yU_le_centralizer h hMod hu) ?_
  intro x hx
  obtain ⟨hxu, hxN⟩ := Subgroup.mem_inf.mp hx
  have hxH : x ∈ hz T V := hNC ▸ hCsN hxN
  exact inf_centralizer_le_yU h hMod h63 hu (Subgroup.mem_inf.mpr ⟨hxH, hxu⟩)

theorem centralizer_le_hz
    (h13314 : A6.Stmt13_3_14) (h674 : Lemma14_7_67_four) (h118 : TheoremC118)
    (h126 : TheoremC126) (h68b : Lemma14_7_68_b) {u : G} (hu : u ∈ u0 T V) (hu1 : u ≠ 1)
    (hT : ∀ t ∈ T, t * u * t⁻¹ * u⁻¹ ∈ fsuV1 T V) :
    Subgroup.centralizer ({u} : Set G) ≤ hz T V := by
  have h := C.hyp
  have := h.fsu.simple
  have hS := C.isSylowTwoOf_tU_centralizer h13314 h674 h118 h126 hu hT
  have hK := kz_le_centralizer_of_mem_u0 h C.hMod hu
  have hu2 : u * u = 1 := by
    rw [← pow_two]
    exact C.hUe u (centralizerMod_le_left _ _ _ hu)
  obtain ⟨-, -, -, hC, -⟩ := C.h63 G T L V h
  have hKY : kz T V ∈ cComp (yU T V u) := cComp_mem_of_le hC le_sup_left (yU_le_hz h C.h63)
  have hloc : quasithinIsLocal (tU T u) (kz T V) :=
    Vol2Native.isLocal_of_mem_cComp (pCoreOf_yU_ne_bot h C.hMod C.h63 hu)
      (isSylowTwoOf_tU h C.hMod C.h63 hu hT) hKY
  have htK : tU T u ≤ Subgroup.normalizer (kz T V : Set G) :=
    inf_le_left.trans ((T_le_hz h C.h63).trans (le_normalizer_oTwoUpper _))
  obtain ⟨⟨Lu, hLu, hKLu, hLun, -⟩, -⟩ := Vol2Native.normal_containing_cComp_of_le_normalizer
    h.fsu.nonabelian h.fsu.qtke (pCoreOf_centralizer_ne_bot hu1 hu2) hS hK hloc htK
  have hLK := h68b G T L V h u hu hu1 hT hS Lu hLu hLun hKLu
  rw [hLK] at hLun
  have hle := (Subgroup.normal_subgroupOf_iff_le_normalizer hK).mp hLun
  rwa [(h674 G T L V h).1] at hle

end Ctx764

theorem lemma14_7_68_of
    (h1222 : Stmt12_2_2) (h1332 : Stmt13_3_2) (h13314 : A6.Stmt13_3_14) (h63 : Thm14_7_63)
    (h674 : Lemma14_7_67_four) (h118 : TheoremC118) (h126 : TheoremC126)
    (h68b : Lemma14_7_68_b) : Lemma14_7_68 := by
  have h1334 : A6.Stmt13_3_4 := U3.stmt13_3_4_of h1332
  have hMod := stmtL32NModule_of_inputs h1332 h1334
  have h13322 := stmt13_3_2_two_of_stmt13_3_2 h1332
  refine lemma14_7_68_of_centralizer_le hMod h674 fun G _ _ T L V h u hu hu1 hT => ?_
  have S0 : Setting147 G T L V (hz T V) := ⟨h, h.isHzOne_hz h63⟩
  have hF : HypF98 T V L (fsuV1 T V) V (hz T V) := Setting147.hypF98 S0 h13322 hMod h1222
  have C : Ctx764 G T L V := ⟨h, hMod, h63, hF, h1222, h1332, h1334⟩
  exact C.centralizer_le_hz h13314 h674 h118 h126 h68b hu hu1 hT

end CFSG.Quasithin.H13.L32A

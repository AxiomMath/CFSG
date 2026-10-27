module

public import CFSG.Quasithin.H13.NQCatA314M23Iso
public import CFSG.Quasithin.H13.NQCatA314M22
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtA312M23Members
public import CFSG.Sporadic.Mathieu.M23
public import CFSG.Sporadic.Schreier.M23
public import CFSG.Assembly.OrderReductions.LinearOrders
public import CFSG.Adapters.ProjectiveSpecialLinear
import CFSG.Quasithin.Background.HSporLatMathieu
import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Dihedral.FourgroupCycleControl
public import CFSG.Dihedral.OriginalCentralizerOddCore
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Quasithin.Background.A3Structure314Defs
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.B1More13A
public import CFSG.Quasithin.Background.B1More13Defs
public import CFSG.Quasithin.Background.B1MoreEleven
public import CFSG.Quasithin.Background.B5Basic
public import CFSG.Quasithin.Background.B5CompA
public import CFSG.Quasithin.Background.B5CompB
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.Vol2.Ch10SecKRefA312
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch1Faithful

public section

namespace CFSG.Quasithin.H13.NQCat.A314D

open CFSG.Open CFSG.QuasithinUnique Equiv
open CFSG.QuasithinUnique.Vol2Native.A312L PermLat
open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
open CFSG.Quasithin.H.MathieuLat CFSG.Quasithin.A312M23
open CFSG.QuasithinUnique.Unc25K1.Six (IsEnc)
open CFSG.Assembly.LowTwoRank (projectiveSpecialLinearGroupEquivStatedProj)
open CFSG.Sporadic.Schreier (m23GenA m23GenB m23PermA m23PermB)
open CFSG.Quasithin hiding lemma_1_2_1_one lemma_1_2_1_two lemma_1_2_4_exists lemma_1_2_4_unique
  lemma_1_2_4_existsUnique normal_conjClosure_of_pCoreOf_ne_bot

theorem card_of_isAlt' {X : Type} [Group X] {k : ℕ} (hk : 2 ≤ k) (h : IsAlt k X) :
    Nat.card X = Nat.factorial k / 2 := by
  obtain ⟨e⟩ := h
  have : Nontrivial (Fin k) := Fin.nontrivial_iff_two_le.mpr hk
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup, Nat.card_fin]

theorem card_of_isExt_e16_alt {X : Type} [Group X] {k : ℕ} (hk : 2 ≤ k)
    (h : IsExt X (fun V _ => IsE2 4 V) (fun Y _ => IsAlt k Y)) :
    Nat.card X = Nat.factorial k / 2 * 16 := by
  obtain ⟨V, _, ⟨eV⟩, hA⟩ := h
  have hV : Nat.card V = 16 := by
    rw [Nat.card_congr (eV.toEquiv.trans Multiplicative.toAdd), Nat.card_fun, Nat.card_zmod,
      Nat.card_fin]
    norm_num
  have h1 := Subgroup.card_eq_card_quotient_mul_card_subgroup V
  rw [card_of_isAlt' hk hA, hV] at h1
  exact h1

theorem card_of_isPSL_three_four {X : Type} [Group X] (h : IsPSL 3 2 2 X) :
    Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_four h

theorem card_of_isSporadic_m22 {X : Type} [Group X]
    (h : IsSporadic .M22 X) : Nat.card X = 443520 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv]
  exact CFSG.Sporadic.Mathieu.card_M22

theorem isQuasisimple_m23 :
    CFSG.IsQuasisimple ↥CFSG.Blueprint.NativeSporadic.M23 := by
  have := (CFSG.Sporadic.Mathieu.fam_m23_simplicity).2.2
  exact (CFSG.LocalCores.isQuasisimple_of_isSimpleGroup
    (nonabelian_of_simple_card (by rw [CFSG.Sporadic.Schreier.m23_card]; norm_num))).1

theorem isEnc_coe_m23 : IsEnc (Subtype.val : ↥CFSG.Blueprint.NativeSporadic.M23 → Perm (Fin 23)) :=
  ⟨Subtype.val_injective, fun _ _ => rfl, rfl⟩

theorem map_closure_list {G H : Type*} [Group G] [Group H] (f : G →* H) (l : List G) :
    (Subgroup.closure {g | g ∈ l}).map f = Subgroup.closure {g | g ∈ l.map f} := by
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  simp [List.mem_map]

theorem tabP_injective : Function.Injective M23Asl.tabP := by
  intro g h hgh
  have h1 : (List.finRange 23).map (fun i => (g i).val) =
      (List.finRange 23).map (fun i => (h i).val) := by
    have := congrArg Array.toList hgh
    simpa [M23Asl.tabP] using this
  rw [List.map_inj_left] at h1
  ext i
  exact h1 i (List.mem_finRange i)

theorem coe_m23Sg :
    m23Sg.map Subtype.val = M23Asl.sgPerms := by
  have h1 : genTabs 23 m23Sg = m23STabs := m23_sGens.1
  have h2 : genTabs 23 m23Sg = (m23Sg.map Subtype.val).map M23Asl.tabP := by
    rw [genTabs, List.map_map]
    rfl
  have h3 := m23Asl_facts.1
  rw [h2, ← h3] at h1
  exact List.map_injective_iff.mpr tabP_injective h1

@[expose] def m23xa : ↥CFSG.Blueprint.NativeSporadic.M23 := evalW [m23GenA, m23GenB] M23Asl.wa

@[expose] def m23xb : ↥CFSG.Blueprint.NativeSporadic.M23 := evalW [m23GenA, m23GenB] M23Asl.wb

theorem coe_m23xa : (m23xa : Perm (Fin 23)) = evalW [m23PermA, m23PermB] M23Asl.wa := by
  have h : [m23GenA, m23GenB].map Subtype.val = [m23PermA, m23PermB] := rfl
  rw [m23xa, enc_evalW isEnc_coe_m23, h]

theorem coe_m23xb : (m23xb : Perm (Fin 23)) = evalW [m23PermA, m23PermB] M23Asl.wb := by
  have h : [m23GenA, m23GenB].map Subtype.val = [m23PermA, m23PermB] := rfl
  rw [m23xb, enc_evalW isEnc_coe_m23, h]

noncomputable def m23Ya : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23 :=
  Subgroup.closure {g | g ∈ m23Sg ++ [m23xa]}

noncomputable def m23Yb : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23 :=
  Subgroup.closure {g | g ∈ m23Sg ++ [m23xb]}

theorem map_m23Ya :
    m23Ya.map CFSG.Blueprint.NativeSporadic.M23.subtype =
      Subgroup.closure {g | g ∈ M23Asl.yaGens} := by
  have hl : (m23Sg ++ [m23xa]).map CFSG.Blueprint.NativeSporadic.M23.subtype =
      M23Asl.yaGens := by
    rw [List.map_append, List.map_singleton, Subgroup.coe_subtype, coe_m23Sg, coe_m23xa]
    rfl
  rw [m23Ya, map_closure_list, hl]

theorem map_m23Yb :
    m23Yb.map CFSG.Blueprint.NativeSporadic.M23.subtype =
      Subgroup.closure {g | g ∈ M23Asl.ybGens} := by
  have hl : (m23Sg ++ [m23xb]).map CFSG.Blueprint.NativeSporadic.M23.subtype =
      M23Asl.ybGens := by
    rw [List.map_append, List.map_singleton, Subgroup.coe_subtype, coe_m23Sg, coe_m23xb]
    rfl
  rw [m23Yb, map_closure_list, hl]

theorem card_m23Ya :
    Nat.card m23Ya = 1920 := by
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _), map_m23Ya]
  exact m23Asl_facts.2.1

theorem card_m23Yb :
    Nat.card m23Yb = 1920 := by
  rw [← Subgroup.card_map_of_injective (Subgroup.subtype_injective _), map_m23Yb]
  exact m23Asl_facts.2.2.1

theorem S_le_m23Ya :
    m23Ctx.S ≤ m23Ya := by
  rw [← m23Ctx.hSeq]
  exact Subgroup.closure_mono fun x hx => List.mem_append_left _ hx

theorem S_le_m23Yb :
    m23Ctx.S ≤ m23Yb := by
  rw [← m23Ctx.hSeq]
  exact Subgroup.closure_mono fun x hx => List.mem_append_left _ hx

theorem m23Ya_ne_m23Yb :
    m23Ya ≠ m23Yb := by
  intro h
  have hb : m23xb ∈ m23Ya := h ▸ Subgroup.subset_closure (List.mem_append_right _
    (List.mem_singleton_self _))
  apply m23Asl_facts.2.2.2.1
  rw [← coe_m23xb, ← map_m23Ya]
  exact ⟨m23xb, hb, rfl⟩

noncomputable def m23Aa : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23 :=
  (Subgroup.closure {g | g ∈ M23Asl.aaGens}).subgroupOf CFSG.Blueprint.NativeSporadic.M23

noncomputable def m23Ab : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23 :=
  (Subgroup.closure {g | g ∈ M23Asl.abGens}).subgroupOf CFSG.Blueprint.NativeSporadic.M23

theorem closure_aaGens_le :
    Subgroup.closure {g | g ∈ M23Asl.aaGens} ≤ CFSG.Blueprint.NativeSporadic.M23 := by
  refine m23Asl_facts.2.2.2.2.1.trans ?_
  rw [← map_m23Ya]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem closure_abGens_le :
    Subgroup.closure {g | g ∈ M23Asl.abGens} ≤ CFSG.Blueprint.NativeSporadic.M23 := by
  refine m23Asl_facts.2.2.2.2.2.1.trans ?_
  rw [← map_m23Yb]
  rintro _ ⟨x, -, rfl⟩
  exact x.2

theorem m23Aa_le :
    m23Aa ≤ m23Ya := by
  intro x hx
  have h1 : (x : Perm (Fin 23)) ∈ m23Ya.map CFSG.Blueprint.NativeSporadic.M23.subtype := by
    rw [map_m23Ya]
    exact m23Asl_facts.2.2.2.2.1 (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨y, hy, hyx⟩ := h1
  rwa [Subtype.ext hyx] at hy

theorem m23Ab_le :
    m23Ab ≤ m23Yb := by
  intro x hx
  have h1 : (x : Perm (Fin 23)) ∈ m23Yb.map CFSG.Blueprint.NativeSporadic.M23.subtype := by
    rw [map_m23Yb]
    exact m23Asl_facts.2.2.2.2.2.1 (Subgroup.mem_subgroupOf.mp hx)
  obtain ⟨y, hy, hyx⟩ := h1
  rwa [Subtype.ext hyx] at hy

theorem k4_equiv_m23Aa :
    Nonempty (↥K4 ≃* ↥m23Aa) := by
  obtain ⟨e⟩ := m23Asl_facts.2.2.2.2.2.2.1
  exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe closure_aaGens_le).symm⟩

theorem k4_equiv_m23Ab :
    Nonempty (↥K4 ≃* ↥m23Ab) := by
  obtain ⟨e⟩ := m23Asl_facts.2.2.2.2.2.2.2
  exact ⟨e.trans (Subgroup.subgroupOfEquivOfLe closure_abGens_le).symm⟩

theorem card_m23Aa :
    Nat.card m23Aa = 960 := by
  obtain ⟨e⟩ := k4_equiv_m23Aa
  rw [← Nat.card_congr e.toEquiv, card_K4]

theorem card_m23Ab :
    Nat.card m23Ab = 960 := by
  obtain ⟨e⟩ := k4_equiv_m23Ab
  rw [← Nat.card_congr e.toEquiv, card_K4]

theorem card_memberOrTop
    {j : ℕ} (hj : j ≤ 16) :
    Nat.card (memberOrTop 16 m23Ctx.Y j) =
      #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9, 79695][j]! * 128 := by
  by_cases hj16 : j < 16
  · rw [memberOrTop, ite_eq_left hj16, m23_member_card j hj16]
    interval_cases j <;> rfl
  · have : j = 16 := by omega
    subst this
    rw [memberOrTop, ite_eq_right (by norm_num), Subgroup.card_top,
      CFSG.Sporadic.Schreier.m23_card]
    rfl

theorem eq_Y79_of_card
    {Z : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23} (hSZ : m23Ctx.S ≤ Z)
    (hZ : Nat.card Z = 1920) : Z = m23Ctx.Y 7 ∧ Z ≠ m23Ctx.Y 9 ∨ Z = m23Ctx.Y 9 ∧ Z ≠ m23Ctx.Y 7 ∨
      (Z = m23Ctx.Y 7 ∧ Z = m23Ctx.Y 9) := by
  obtain ⟨j, hj, rfl⟩ := m23_complete Z hSZ
  have hc := card_memberOrTop hj
  rw [hZ] at hc
  have h79 : j = 7 ∨ j = 9 := by
    interval_cases j <;> simp_all
  have h7 : memberOrTop 16 m23Ctx.Y 7 = m23Ctx.Y 7 := by
    rw [memberOrTop, ite_eq_left (by norm_num)]
  have h9 : memberOrTop 16 m23Ctx.Y 9 = m23Ctx.Y 9 := by
    rw [memberOrTop, ite_eq_left (by norm_num)]
  rcases h79 with rfl | rfl
  · rw [h7]
    by_cases h : m23Ctx.Y 7 = m23Ctx.Y 9
    · exact Or.inr (Or.inr ⟨rfl, h⟩)
    · exact Or.inl ⟨rfl, h⟩
  · rw [h9]
    by_cases h : m23Ctx.Y 9 = m23Ctx.Y 7
    · exact Or.inr (Or.inr ⟨h, rfl⟩)
    · exact Or.inr (Or.inl ⟨rfl, h⟩)

theorem Y79_eq
    {j : ℕ} (hj : j = 7 ∨ j = 9) :
    m23Ctx.Y j = m23Ya ∨ m23Ctx.Y j = m23Yb := by
  have ha := eq_Y79_of_card S_le_m23Ya card_m23Ya
  have hb := eq_Y79_of_card S_le_m23Yb card_m23Yb
  have hne := m23Ya_ne_m23Yb
  rcases hj with rfl | rfl
  · rcases ha with ⟨ha, -⟩ | ⟨ha, ha'⟩ | ⟨ha, -⟩
    · exact Or.inl ha.symm
    · rcases hb with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨hb, -⟩
      · exact Or.inr hb.symm
      · exact absurd (ha.trans hb.symm) hne
      · exact Or.inr hb.symm
    · exact Or.inl ha.symm
  · rcases ha with ⟨ha, ha'⟩ | ⟨ha, -⟩ | ⟨-, ha⟩
    · rcases hb with ⟨hb, -⟩ | ⟨hb, -⟩ | ⟨-, hb⟩
      · exact absurd (ha.trans hb.symm) hne
      · exact Or.inr hb.symm
      · exact Or.inr hb.symm
    · exact Or.inl ha.symm
    · exact Or.inl ha.symm

theorem eq_of_sup_eq_of_index_two {G : Type} [Group G] [Finite G] {S B Y A : Subgroup G}
    (hB : B ∈ lFamily S) (hY : B ⊔ S = Y) (hAY : A ≤ Y) (hcard : Nat.card Y = 2 * Nat.card A)
    (hc : Nat.card B = Nat.card A) : B = A := by
  have hBp : ⁅B, B⁆ = B := perfect_of_mem_cComp (show B ∈ cComp (B ⊔ S) from hB)
  have hcomm : ⁅Y, Y⁆ ≤ A := commutator_le_of_card_eq_two_mul hAY hcard
  have hBY : B ≤ Y := hY ▸ le_sup_left
  have hBA : B ≤ A := by
    calc B = ⁅B, B⁆ := hBp.symm
      _ ≤ ⁅Y, Y⁆ := Subgroup.commutator_mono hBY hBY
      _ ≤ A := hcomm
  exact Subgroup.eq_of_le_of_card_ge hBA hc.ge

theorem m23_block_equiv
    {B : Subgroup ↥CFSG.Blueprint.NativeSporadic.M23}
    (hB : B ∈ lFamily m23Ctx.S) (hc : Nat.card B = 960) : Nonempty (↥K4 ≃* ↥B) := by
  have hS : IsPGroup 2 m23Ctx.S := m23Ctx.S_isPGroup
  obtain ⟨j, hj, hjZ⟩ := m23_complete (B ⊔ m23Ctx.S) le_sup_right
  have hdvd : 960 ∣ #[1, 3465, 315, 45, 21, 315, 21, 15, 45, 15, 3, 3, 3, 3, 3, 9, 79695][j]! *
      128 := by
    rw [← card_memberOrTop hj, ← hjZ, ← hc]
    exact Subgroup.card_dvd_of_le le_sup_left
  by_cases hj16 : j < 16
  · have hY : B ⊔ m23Ctx.S = m23Ctx.Y j := by rw [hjZ, memberOrTop, ite_eq_left hj16]
    have h79 : j = 7 ∨ j = 9 → Nonempty (↥K4 ≃* ↥B) := by
      intro h79
      rcases Y79_eq h79 with h | h
      · have hBA := eq_of_sup_eq_of_index_two hB (hY.trans h) m23Aa_le
          (by rw [card_m23Ya, card_m23Aa]) (by rw [hc, card_m23Aa])
        rw [hBA]
        exact k4_equiv_m23Aa
      · have hBA := eq_of_sup_eq_of_index_two hB (hY.trans h) m23Ab_le
          (by rw [card_m23Yb, card_m23Ab]) (by rw [hc, card_m23Ab])
        rw [hBA]
        exact k4_equiv_m23Ab
    interval_cases j
    · exact absurd hdvd (by decide)
    · exfalso
      have := card_of_isSporadic_m22 (m23_shape_y1 hB hY)
      omega
    · exfalso
      have := card_of_isPSL_three_four (m23_shape_y2 hS hB hY)
      omega
    · exfalso
      have := card_of_isExt_e16_alt (by norm_num) (m23_shape_y3 hS hB hY)
      rw [hc] at this
      exact absurd this (by decide)
    · exact absurd hdvd (by decide)
    · exfalso
      have := card_of_isExt_e16_alt (by norm_num) (m23_shape_y5 hS hB hY)
      rw [hc] at this
      exact absurd this (by decide)
    · exact absurd hdvd (by decide)
    · exact h79 (Or.inl rfl)
    · exact (m23_not_y8 hS hB hY).elim
    · exact h79 (Or.inr rfl)
    · exact absurd hdvd (by decide)
    · exact absurd hdvd (by decide)
    · exact absurd hdvd (by decide)
    · exact absurd hdvd (by decide)
    · exact absurd hdvd (by decide)
    · exact absurd hdvd (by decide)
  · exfalso
    have hjt : B ⊔ m23Ctx.S = ⊤ := by rw [hjZ, memberOrTop, ite_eq_right hj16]
    have hB' : B ∈ cComp (B ⊔ m23Ctx.S) := hB
    rw [hjt] at hB'
    have h1 := A321.cComp_eq_top_of_quasisimple isQuasisimple_m23 hB'
    rw [h1, Subgroup.card_top, CFSG.Sporadic.Schreier.m23_card] at hc
    omega

theorem m23_block_equiv_of
    {X : Type} [Group X]
    (φ : X ≃* CFSG.Blueprint.NativeSporadic.Carrier .M23) {T B : Subgroup X}
    (hT : IsSylowTwoOf T ⊤) (hB : B ∈ lFamily T) (hc : Nat.card B = 960) :
    Nonempty (↥K4 ≃* ↥B) := by
  let ψ : X ≃* ↥CFSG.Blueprint.NativeSporadic.M23 := φ
  have : Finite X := Finite.of_equiv _ ψ.symm.toEquiv
  have hT' : IsSylowTwoOf (T.map ψ.toMonoidHom) ⊤ :=
    A312.isSylowTwoOf_top_map ψ.toMonoidHom ψ.surjective hT
  obtain ⟨c, hcS⟩ := exists_conj_of_isSylowTwoOf hT' m23_S_sylow
  let α : X ≃* ↥CFSG.Blueprint.NativeSporadic.M23 := ψ.trans (MulAut.conj c)
  have hTS : T.map α.toMonoidHom = m23Ctx.S := by
    rw [← hcS, Subgroup.map_map]
    rfl
  have hB' : B.map α.toMonoidHom ∈ lFamily m23Ctx.S := by
    have h1 := cComp_map_mulEquiv α (show B ∈ cComp (B ⊔ T) from hB)
    rw [Subgroup.map_sup, hTS] at h1
    exact h1
  have hc' : Nat.card (B.map α.toMonoidHom) = 960 := by
    rw [Subgroup.card_map_of_injective α.injective, hc]
  obtain ⟨θ⟩ := m23_block_equiv hB' hc'
  exact ⟨θ.trans (B.equivMapOfInjective α.toMonoidHom α.injective).symm⟩

theorem mathieu_m23
    {G : Type} [Group G] [Finite G] {L T B : Subgroup G}
    (hT : IsSylowTwoOf T L) (hB : B ∈ lFamily T) (hBL : B ≤ L) (hL : IsSporadic .M23 ↥L)
    (hext : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y)) :
    IsShort2 B ∧ IsLin2Type B 2 := by
  obtain ⟨φ⟩ := hL
  have hc : Nat.card (B.subgroupOf L) = 960 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv]
    exact card_of_isExt_e16_a5 hext
  obtain ⟨θ⟩ := m23_block_equiv_of φ (isSylowTwoOf_top_subgroupOf hT)
    (subgroupOf_mem_lFamily' hT.1 hBL hB) hc
  exact isShort2_isLin2Type_of_mulEquiv (θ.trans (Subgroup.subgroupOfEquivOfLe hBL))

theorem desc_mathieu
    (G : Type) [Group G] [Finite G] (L T B : Subgroup G)
    (hT : IsSylowTwoOf T L) (hB : B ∈ lFamily T) (hBL : B ≤ L) (_hne : B ≠ L)
    (hL : IsSporadic .M22 ↥L ∨ IsHat ↥L (CFSG.Blueprint.NativeSporadic.Carrier .M22) ∨
      IsSporadic .M23 ↥L)
    (hext : IsExt ↥B (fun V _ => IsE2 4 V) (fun Y _ => IsAlt 5 Y)) :
    IsShort2 B ∧ IsLin2Type B 2 := by
  rcases hL with h | h | h
  · exact mathieu_m22 hT hB hBL h hext
  · exact mathieu_hatM22 hT hB hBL h hext
  · exact mathieu_m23 hT hB hBL h hext

end CFSG.Quasithin.H13.NQCat.A314D

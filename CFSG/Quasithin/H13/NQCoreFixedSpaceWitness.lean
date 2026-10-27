module

public import CFSG.Quasithin.H13.NQCoreFixedSpaceGlue
public import CFSG.Quasithin.SteinbergCFOutsideCoreCubicWitness
public import CFSG.Quasithin.SteinbergCAStrictFixedSpaceNormalClosure
public import CFSG.Quasithin.Background.C1PackSolvBasic
public import CFSG.Quasithin.Background.D15Chief
public import CFSG.Quasithin.H13.NQBlockTwoPrimeCapture
public import CFSG.Quasithin.H13.NQCoreFixedSpaceStmt
public import CFSG.Quasithin.H13.NQCoreFixedSpaceThreeFree

public section

namespace CFSG.Quasithin.H13.NQCore

open Subgroup Module CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique
open CFSG.Quasithin.SteinbergCD (glFixedSpace)
open CFSG.QuasithinUnique.Setup.Campbell (elemThompsonIn)
open scoped IsMulCommutative

theorem stmtSolvableFixedSpaceWitness_of (hle1 : StmtCoreContainedAtMostOneNoncentral)
    (hge2 : StmtCoreContainedAtLeastTwoNoncentral) : StmtSolvableFixedSpaceWitness := by
  intro G _ _ hev he2 T F J hT hTF hFJ V _ _ _ hV1 hV2 hVJ hRn hsolv hO2 h3 hS
  obtain ⟨S, hSs, hTS, hS2, hSJ⟩ := hS
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set Vg : Subgroup G := V.map F.subtype with hVg
  set R : Subgroup G := T ⊓ centralizer (Vg : Set G) with hR
  have hTJ : T ≤ J := hTF.trans hFJ.2.1
  have hsylJ : IsSylowTwoOf T J :=
    ⟨hTJ, hT.1, fun h2 => hT.2 (h2.trans (relIndex_dvd_index_of_le hTJ))⟩
  have hVT : Vg ≤ T := hVJ.trans (EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylJ)
  have hVF : Vg ≤ F := map_subtype_le V
  have hVFn : (Vg.subgroupOf F).Normal := by
    have h1 : Vg.subgroupOf F = V := comap_map_eq_self_of_injective F.subtype_injective V
    rw [h1]
    infer_instance
  have hFV : F ≤ normalizer (Vg : Set G) := (normal_subgroupOf_iff_le_normalizer hVF).mp hVFn
  have hTV : T ≤ normalizer (Vg : Set G) := hTF.trans hFV
  have hVg1 : Vg ≠ ⊥ := fun h => hV1 ((map_eq_bot_iff_of_injective V F.subtype_injective).mp h)
  have hVgab : IsElemAbelian 2 Vg := by
    refine ⟨(V.equivMapOfInjective F.subtype F.subtype_injective).surjective.isMulCommutative
      inferInstance, ?_⟩
    rintro _ ⟨v, hv, rfl⟩
    rw [← map_pow, hV2 v hv, map_one]
  have hVe : IsElementaryAbelian 2 ↥V :=
    { toIsMulCommutative := inferInstance
      exponent_dvd_p := Monoid.exponent_dvd_of_forall_pow_eq_one fun v =>
        Subtype.ext (by simpa using hV2 _ v.2) }
  have hfinV : Finite (Additive ↥V) := inferInstanceAs (Finite ↥V)
  have : FiniteDimensional (ZMod 2) (Additive ↥V) := Module.Finite.of_finite
  have : Finite (LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)) :=
    SteinbergBQ.finite_generalLinearGroup
  have hΓT : (T.subgroupOf F).map (conjGL V) ≤ (conjGL V).range := map_le_range _ _
  have hG1 : ∀ A ≤ (T.subgroupOf F).map (conjGL V), A ≠ ⊥ → IsElementaryAbelian 2 ↥A →
      Nat.card A ^ 1 * Nat.card (glFixedSpace A) < Nat.card (Additive ↥V) :=
    fun A hA hA1 hAe => by
      rw [pow_one]
      exact card_mul_card_glFixedSpace_lt hsolv hO2 h3 (hA.trans hΓT) hAe hA1
  have hG2 := fun (A : Subgroup (LinearMap.GeneralLinearGroup (ZMod 2) (Additive ↥V)))
      (hA : A ≤ (T.subgroupOf F).map (conjGL V)) (hA1 : A ≠ ⊥)
      (hAe : IsElementaryAbelian 2 ↥A) =>
    card_mul_card_invariant_dual_lt hsolv hO2 h3 (hA.trans hΓT) hAe hA1
  obtain ⟨H, hTH, hHS, hHJ, hmin⟩ := C1Pack.exists_minimal_not_le hTS hSJ
  have hHsolv : Group.IsSolvable ↥H :=
    Group.isSolvable_of_isSolvable_injective (inclusion_injective hHS)
  have hsylH : IsSylowTwoOf T H :=
    ⟨hTH, hT.1, fun h2 => hT.2 (h2.trans (relIndex_dvd_index_of_le hTH))⟩
  have hsylS : IsSylowTwoOf T S :=
    ⟨hTS, hT.1, fun h2 => hT.2 (h2.trans (relIndex_dvd_index_of_le hTS))⟩
  have hSH : pCoreOf 2 S ≤ pCoreOf 2 H :=
    LieType.BorelTits.le_pCoreOf_of_le_normalizer 2
      ((EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylS).trans hTH)
      (hHS.trans (LieType.BorelTits.le_normalizer_pCoreOf 2 S))
      (LieType.BorelTits.pCoreOf_isPGroup 2 S)
  have hH2 : pCoreOf 2 H ≠ ⊥ := fun h => hS2 (le_bot_iff.mp (h ▸ hSH))
  have hsylTop : IsSylowTwoOf T ⊤ := by
    refine ⟨le_top, hT.1, ?_⟩
    rw [show (T.subgroupOf ⊤).index = T.index from relIndex_top_right T]
    exact hT.2
  have hHchar : CharTwo H := charTwo_of_isSylowTwoOf_le_of_pCore_ne_bot hev hsylTop hTH hH2
  set MH := H ⊓ J with hMH
  have hMHlt : MH < H := lt_of_le_of_ne inf_le_left fun h => hHJ (h ▸ (inf_le_right : H ⊓ J ≤ J))
  have hTMH : T ≤ MH := le_inf hTH hTJ
  have hMHmax : ∀ Y : Subgroup G, MH < Y → Y ≤ H → Y = H := by
    intro Y hY hYH
    by_contra hne
    have hYJ := hmin Y (hTMH.trans hY.le) (lt_of_le_of_ne hYH hne)
    exact absurd (le_inf hYH hYJ) hY.not_ge
  have hMHu : ∀ Y : Subgroup G, Y < H → (∀ Z : Subgroup G, Y < Z → Z ≤ H → Z = H) → T ≤ Y →
      Y = MH := by
    intro Y hYH hYmax hTY
    rcases (le_inf hYH.le (hmin Y hTY hYH) : Y ≤ MH).lt_or_eq with hlt | heq
    · exact absurd (hYmax MH hlt inf_le_left) hMHlt.ne
    · exact heq
  have hobs : ∀ X : Subgroup G, X ≤ R → X ≠ ⊥ → ¬ F ⊔ H ≤ normalizer (X : Set G) :=
    fun X hXR hX1 hFH =>
      false_of_le_normalizer hFJ hHJ (hT.1.to_le (hXR.trans inf_le_left)) hX1 hFH
  set V₀ : Subgroup ↥T := Vg.subgroupOf T with hV₀
  have hV₀n : V₀.Normal := (normal_subgroupOf_iff_le_normalizer hVT).mpr hTV
  have hV₀map : V₀.map T.subtype = Vg := by
    rw [hV₀, subgroupOf_map_subtype, inf_eq_left.mpr hVT]
  have hV₀e : IsElementaryAbelian 2 ↥V₀ :=
    isElementaryAbelian_of_mulEquiv' (isoOfMap V T.subtype T.subtype_injective V₀ hV₀map).symm hVe
  have hstrictBQ : ∀ E : Subgroup (MulAut ↥V₀),
      E ≤ (MulAut.conjNormal : ↥T →* MulAut ↥V₀).range → E ≠ ⊥ → IsElementaryAbelian 2 ↥E →
        Nat.card E < (FixedPoints.subgroup ↥E ↥V₀).index := by
    intro E hE hE1 hEe
    have h := card_pow_mul_card_fixedPoints_lt V hTF T.subtype T.subtype_injective V₀ hV₀map 1
      hG1 (E := E) (fun σ hσ => by
        obtain ⟨p, hp⟩ := exists_conj_of_mem_range T.subtype (hE hσ)
        exact ⟨T.subtype p, p.2, hp⟩) hE1 hEe
    rw [pow_one] at h
    exact index_lt_of_card_mul_lt h
  obtain ⟨-, -, -, hJC⟩ :=
    SteinbergBQ.strict_fixed_space_inequality_centralizes_elementary_thompson_subgroup hT.1 V₀
      hV₀e hstrictBQ
  have hJR : elemThompsonIn 2 T ≤ R := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨x.2, mem_centralizer_iff.mpr fun v hv => ?_⟩
    exact congrArg Subtype.val (mem_centralizer_iff.mp (hJC hx) ⟨v, hVT hv⟩ hv)
  have hRT : R ≤ T := inf_le_left
  have hJeq : elemThompsonIn 2 R = elemThompsonIn 2 T :=
    Setup.Campbell.elemThompsonIn_eq_of_le 2 hJR hRT
  have hTnt : Nontrivial ↥T :=
    (nontrivial_iff_ne_bot T).mpr fun h => hVg1 (le_bot_iff.mp (h ▸ hVT))
  have hJne : elemThompsonIn 2 T ≠ ⊥ := fun h =>
    NQBlock.elemThompson_two_ne_bot hT.1
      ((map_eq_bot_iff_of_injective _ T.subtype_injective).mp h)
  have hFR : F ≤ normalizer (R : Set G) :=
    (normal_subgroupOf_iff_le_normalizer (hRT.trans hTF)).mp hRn
  have hFJe : F ≤ normalizer (elemThompsonIn 2 T : Set G) := by
    rw [← hJeq]
    exact le_normalizer_elemThompsonIn 2 hFR
  have hTn : ¬ (T.subgroupOf H).Normal := fun hn =>
    hobs _ hJR hJne (sup_le hFJe (le_normalizer_elemThompsonIn 2
      ((normal_subgroupOf_iff_le_normalizer hTH).mp hn)))
  set Q := (CFSG.pCore 2 ↥H).map H.subtype with hQ
  have hQeq : Q = pCoreOf 2 H := by rw [hQ, pCoreOf]
  have hQT : Q ≤ T := hQeq ▸ EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylH
  have hHQ : H ≤ normalizer (Q : Set G) := hQeq ▸ LieType.BorelTits.le_normalizer_pCoreOf 2 H
  have hJQ : ¬ elemThompsonIn 2 T ≤ Q := fun hle => by
    have h1 := Setup.Campbell.elemThompsonIn_eq_of_le 2 hle hQT
    refine hobs _ hJR hJne (sup_le hFJe ?_)
    rw [← h1]
    exact le_normalizer_elemThompsonIn 2 hHQ
  have hT2H : IsPGroup 2 ↥(T.subgroupOf H) := hT.1.of_equiv (subgroupOfEquivOfLe hTH).symm
  set Ts : Sylow 2 ↥H := hT2H.toSylow hsylH.2.2 with hTs
  set VH : Subgroup ↥H := Vg.subgroupOf H with hVH
  have hVHmap : VH.map H.subtype = Vg := by
    rw [hVH, subgroupOf_map_subtype, inf_eq_left.mpr (hVT.trans hTH)]
  have hVHT : VH ≤ (Ts : Subgroup ↥H) := fun x hx => hVT hx
  have hTsVH : (Ts : Subgroup ↥H) ≤ normalizer (VH : Set ↥H) := by
    intro t ht
    rw [mem_normalizer_iff]
    intro x
    exact mem_normalizer_iff.mp (hTV (show (t : G) ∈ T from ht)) (x : G)
  by_cases hVQ : Vg ≤ Q
  ·
    by_contra hcon
    have hG3 : ∀ A ≤ (T.subgroupOf F).map (conjGL V), A ≠ ⊥ → IsElementaryAbelian 2 ↥A →
        Nat.card A ^ 2 * Nat.card (glFixedSpace A) < Nat.card (Additive ↥V) := by
      intro A hA hA1 hAe
      have hApow := Monoid.exponent_dvd_iff_forall_pow_eq_one.mp hAe.exponent_dvd_p
      have hA2 : IsPGroup 2 ↥A := fun x => ⟨1, by rw [pow_one]; exact hApow x⟩
      obtain ⟨r, hr⟩ := hA2.exists_card_eq
      have hlt : 2 * r < finrank (ZMod 2) (Additive ↥V ⧸ glFixedSpace A) := by
        by_contra hle
        exact hcon ⟨A, hA, hAe, hA1, r, hr, not_lt.mp hle⟩
      have h1 := Submodule.card_eq_card_quotient_mul_card (glFixedSpace A)
      rw [card_quotient_eq_two_pow_finrank] at h1
      rw [h1, hr, ← pow_mul, mul_comm (2 ^ (r * 2))]
      exact mul_lt_mul_of_pos_left (Nat.pow_lt_pow_right (by norm_num) (by omega)) Nat.card_pos
    have hstrict2 : ∀ E : Subgroup (MulAut ↥Vg),
        (∀ σ ∈ E, ∃ t ∈ T, ∀ v : ↥Vg, ((σ v : ↥Vg) : G) = t * v * t⁻¹) → E ≠ ⊥ →
          IsElementaryAbelian 2 ↥E →
            Nat.card ↥E ^ 2 * Nat.card ↥(FixedPoints.subgroup ↥E ↥Vg) < Nat.card ↥Vg :=
      fun E hE hE1 hEe => card_pow_mul_card_fixedPoints_lt V hTF (MonoidHom.id G)
        Function.injective_id Vg (map_id Vg) 2 hG3 hE hE1 hEe
    have hstrictB : ∀ E : Subgroup (MulAut ↥Vg),
        (∀ σ ∈ E, ∃ t ∈ T, ∀ v : ↥Vg, ((σ v : ↥Vg) : G) = t * v * t⁻¹) → E ≠ ⊥ →
          IsElementaryAbelian 2 ↥E →
            Nat.card ↥E * Nat.card ↥(FixedPoints.subgroup ↥E ↥Vg) < Nat.card ↥Vg ∧
            Nat.card ↥E * Nat.card {φ : ↥Vg →* Multiplicative (ZMod 2) //
              ∀ σ ∈ E, ∀ v, φ (σ v) = φ v} < Nat.card (↥Vg →* Multiplicative (ZMod 2)) := by
      intro E hE hE1 hEe
      have h1 := card_pow_mul_card_fixedPoints_lt V hTF (MonoidHom.id G) Function.injective_id
        Vg (map_id Vg) 1 hG1 hE hE1 hEe
      rw [pow_one] at h1
      exact ⟨h1, card_mul_card_invariant_hom_lt V hTF (MonoidHom.id G) Function.injective_id
        Vg (map_id Vg) hG2 hE hE1 hEe⟩
    set V'' : Subgroup ↥(Ts : Subgroup ↥H) := VH.subgroupOf (Ts : Subgroup ↥H) with hV''
    have hV''n : V''.Normal := (normal_subgroupOf_iff_le_normalizer hVHT).mpr hTsVH
    have hV''map : V''.map (Ts : Subgroup ↥H).subtype = VH := by
      rw [hV'', subgroupOf_map_subtype, inf_eq_left.mpr hVHT]
    have hK'' : V''.map (H.subtype.comp (Ts : Subgroup ↥H).subtype) = Vg := by
      rw [← map_map, hV''map, hVHmap]
    have hι'' : Function.Injective (H.subtype.comp (Ts : Subgroup ↥H).subtype) :=
      H.subtype_injective.comp (Ts : Subgroup ↥H).subtype_injective
    have hV''e : IsElementaryAbelian 2 ↥V'' :=
      isElementaryAbelian_of_mulEquiv' (isoOfMap V _ hι'' V'' hK'').symm hVe
    have hstrictCA : ∀ E : Subgroup (MulAut ↥V''),
        E ≤ (MulAut.conjNormal : ↥(Ts : Subgroup ↥H) →* MulAut ↥V'').range → E ≠ ⊥ →
          IsElementaryAbelian 2 ↥E → Nat.card E < (FixedPoints.subgroup ↥E ↥V'').index := by
      intro E hE hE1 hEe
      have h := card_pow_mul_card_fixedPoints_lt V hTF (H.subtype.comp (Ts : Subgroup ↥H).subtype)
        hι'' V'' hK'' 1 hG1 (E := E) (fun σ hσ => by
          obtain ⟨p, hp⟩ := exists_conj_of_mem_range (H.subtype.comp (Ts : Subgroup ↥H).subtype)
            (hE hσ)
          exact ⟨(H.subtype.comp (Ts : Subgroup ↥H).subtype) p,
            (show ((p : ↥H) : G) ∈ T from p.2), hp⟩) hE1 hEe
      rw [pow_one] at h
      exact index_lt_of_card_mul_lt h
    have hVO : V''.map (Ts : Subgroup ↥H).subtype ≤ CFSG.pCore 2 ↥H := by
      rw [hV''map]
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hVQ (show (x : G) ∈ Vg from hx)
      rwa [← H.subtype_injective hyx]
    obtain ⟨hUe, -, -⟩ :=
      SteinbergCA.strict_fixed_space_inequality_makes_core_contained_normal_closure_elementary
        Ts V'' hV''e hVO hstrictCA
    rw [hV''map] at hUe
    have hUab := isElemAbelian_map_subtype hUe
    rw [map_normalClosure_eq_iSup (hVT.trans hTH)] at hUab
    have hUn : IsNormalIn H (⨆ (h : G) (_ : h ∈ H), Vg.map (MulAut.conj h).toMonoidHom)
        (⨆ (h : G) (_ : h ∈ H), Vg.map (MulAut.conj h).toMonoidHom) :=
      ⟨le_rfl, fun g hg x hx =>
        (mem_normalizer_iff.mp (SteinbergCD.le_normalizer_iSup_conj hg) x).mp hx⟩
    obtain ⟨n, hn⟩ := D15Proof.exists_isChiefSeriesFrom _ hUn
    have h1 := hle1 G H T MH Vg hHsolv hsylH hTn hMHlt hMHmax hTMH hMHu hVT hTV hVgab hVg1 hVQ
      hUab hstrict2 hJQ n hn
    have h2 := hge2 G hev he2 F H T MH Vg R hT hTF hTH hHsolv hHchar hTn hMHlt hMHmax hTMH hMHu
      hVF hVFn hVgab hVg1 hVQ rfl hRn
      (fun X hXR hX1 hXn => hobs X hXR hX1 ((normal_subgroupOf_iff_le_normalizer
        (hXR.trans (hRT.trans (hTF.trans le_sup_left)))).mp hXn))
      hstrictB hUab n hn
    omega
  ·
    have hVHe : IsElementaryAbelian 2 ↥VH :=
      isElementaryAbelian_of_mulEquiv' (isoOfMap V H.subtype H.subtype_injective VH hVHmap).symm
        hVe
    have hmapH : ∀ b : Subgroup ↥H, b.map H.subtype = H → b = ⊤ := by
      intro b hb
      rw [eq_top_iff]
      intro x _
      obtain ⟨y, hy, hyx⟩ : (x : G) ∈ b.map H.subtype := by
        rw [hb]
        exact x.2
      rwa [← H.subtype_injective hyx]
    have hTb : ∀ b : Subgroup ↥H, (Ts : Subgroup ↥H) ≤ b → T ≤ b.map H.subtype :=
      fun b hb t ht => ⟨⟨t, hTH ht⟩, hb (show t ∈ T from ht), rfl⟩
    have hbJ : ∀ b : Subgroup ↥H, b ≠ ⊤ → (Ts : Subgroup ↥H) ≤ b → b ≤ J.subgroupOf H := by
      intro b hb hTsb x hx
      have hlt : b.map H.subtype < H :=
        lt_of_le_of_ne (map_subtype_le b) fun h => hb (hmapH b h)
      exact hmin _ (hTb b hTsb) hlt ⟨x, hx, rfl⟩
    have hM'top : J.subgroupOf H ≠ ⊤ := fun h =>
      hHJ fun x hx => by
        have h1 : (⟨x, hx⟩ : ↥H) ∈ J.subgroupOf H := h ▸ mem_top _
        exact h1
    have hTsM' : (Ts : Subgroup ↥H) ≤ J.subgroupOf H := fun t ht => hTJ ht
    have hM' : IsCoatom (J.subgroupOf H) := by
      refine ⟨hM'top, fun b hb => ?_⟩
      by_contra hbt
      exact absurd (hbJ b hbt (hTsM'.trans hb.le)) hb.not_ge
    have huniq : ∀ Y : Subgroup ↥H, IsCoatom Y → (Ts : Subgroup ↥H) ≤ Y → Y = J.subgroupOf H :=
      fun Y hY hTsY => ((hY.le_iff.mp (hbJ Y hY.1 hTsY)).resolve_left hM'top).symm
    have hVHQ : ¬ VH ≤ CFSG.pCore 2 ↥H := fun h => hVQ (by
      rw [← hVHmap]
      exact map_mono h)
    obtain ⟨g, -, -, -, -, hAT, hAN, -, hA1, hAe, -, d, r, hd, hr, hdr⟩ :=
      SteinbergCF.solvable_minimal_parabolic_outside_core_seed_cubic_witness hHsolv
        (EscapingLocal.isCharacteristicP_of_charTwo hHchar) Ts hTn hM' hTsM' huniq (V := VH)
        hVHT hTsVH hVHQ
    exact exists_witness_of_autOn V hTF hVHmap hAT hAN hA1 hAe hd hr hdr

end CFSG.Quasithin.H13.NQCore

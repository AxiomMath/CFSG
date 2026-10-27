module

public import CFSG.Quasithin.Vol2.Ch3Sec3Lem3320S7d

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Blueprint CFSG.Quasithin.ChiefCount
open CFSG.Quasithin.H13.Ch3Sec3 CFSG.Quasithin.ASInputs
open scoped commutatorElement

namespace S3320

variable {G : Type} [Group G] [Finite G]

namespace Hyp3320

variable {T M L D X : Subgroup G} (H : Hyp3320 G T M L D X)

include H

variable {B₀ : Subgroup G}

theorem relIndex_T_eq_four (hL2s : FactL2pSylowFour) [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal]
    (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤) {p : ℕ} (hp : p.Prime)
    (hp24 : p % 24 = 11 ∨ p % 24 = 13)
    (hL : F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D))) : B₀.relIndex T = 4 := by
  have hp8 : p % 8 = 3 ∨ p % 8 = 5 := by omega
  rw [← card_star (B := X ⊔ T ⊔ D) (N := B₀) (le_sup_right.trans le_sup_left)]
  have hsyl := H.isSylowTwoOf_star_T (B₀ := B₀)
  have hTQ : star (X ⊔ T ⊔ D) B₀ T ≤ star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := htop ▸ le_top
  have hsyl' : IsSylowTwoOf ((star (X ⊔ T ⊔ D) B₀ T).subgroupOf
      (star (X ⊔ T ⊔ D) B₀ (conjClosure X D))) ⊤ := by
    refine ⟨le_top, hsyl.2.1.of_equiv (Subgroup.subgroupOfEquivOfLe hTQ).symm, fun h2 => ?_⟩
    apply hsyl.2.2
    have h3 : (((star (X ⊔ T ⊔ D) B₀ T).subgroupOf
        (star (X ⊔ T ⊔ D) B₀ (conjClosure X D))).subgroupOf ⊤).index =
        (star (X ⊔ T ⊔ D) B₀ T).relIndex (star (X ⊔ T ⊔ D) B₀ (conjClosure X D)) :=
      Subgroup.relIndex_top_right _
    rw [h3, htop] at h2
    exact h2
  rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe hTQ).toEquiv]
  exact hL2s p hp hp8 _ hL _ hsyl'

theorem concl5 (hL2s : FactL2pSylowFour) (hA : AS_A_1_31) (hB : IsB₀ X T D B₀)
    [(B₀.subgroupOf (X ⊔ T ⊔ D)).Normal] (hY : conjClosure X D ∈ cComp (X ⊔ T ⊔ D))
    (hYB₀ : ¬ conjClosure X D ≤ B₀) (htop : star (X ⊔ T ⊔ D) B₀ (conjClosure X D) = ⊤)
    (hle : conjClosure X D ⊓ B₀ ≤ pCoreOf 2 (X ⊔ T ⊔ D))
    (hP : pCoreOf 2 (conjClosure X D ⊔ T) = (conjClosure X D ⊔ T) ⊓ B₀) {g : G} (hg : g ∈ D)
    (hK₀top : star (X ⊔ T ⊔ D) B₀ (perfectCore (gZero X T g)) = ⊤)
    (hO2 : pCoreOf 2 X ≤ pCoreOf 2 (conjClosure X D)) {p : ℕ} (hp : p.Prime)
    (hp24 : p % 24 = 11 ∨ p % 24 = 13)
    (hL : F6.IsL2 p 1 ↥(star (X ⊔ T ⊔ D) B₀ (conjClosure X D)))
    (hX5 : ¬ HasNoncentralTwoChief X 5) :
    (HasNoncentralTwoChief (conjClosure X D) 1 ∧ ¬ HasNoncentralTwoChief (conjClosure X D) 2 ∧
      (∀ A B : Subgroup G, IsTwoChiefFactor (conjClosure X D) A B →
        ¬ ⁅A, conjClosure X D⁆ ≤ B → 2 ^ 10 ≤ B.relIndex A) ∧
      2 ^ 12 ≤ Nat.card T) ∧
    (frattini ↥(pCoreOf 2 X)).map (pCoreOf 2 X).subtype ≤
      (Subgroup.center ↥(conjClosure X D)).map (conjClosure X D).subtype ∧
    (Subgroup.center ↥(conjClosure X D ⊔ T) ≠ ⊥ → 2 ^ 12 < Nat.card T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hY1 := H.hasNoncentralTwoChief_Y hB hY hYB₀
  have h3 := fun {U V : Subgroup G} (hc : IsTwoChiefFactor (conjClosure X D) U V)
    (hn : ¬ ⁅U, conjClosure X D⁆ ≤ V) =>
    H.hasSecNC_three hA hB hY hYB₀ htop hle hg hK₀top hO2 hp hp24 hL hc hn
  have hY2 : ¬ HasNoncentralTwoChief (conjClosure X D) 2 := by
    rintro ⟨A, B', hAB, hle'⟩
    have hle01 : A 0 ≤ B' 1 := hle' 0 1 (by decide)
    have h6 := (h3 (hAB 0).1 (hAB 0).2).append ((h3 (hAB 1).1 (hAB 1).2).mono_left hle01)
      (hAB 0).1.1.le (hle01.trans (hAB 1).1.1.le)
    have h6' := hasNoncentralTwoChief_of_hasSecNC h6
      (H.le_normalizer_X_of_chief hA hB hY hYB₀ htop hle (hAB 1).1)
    apply hX5
    exact Chief3323.hasNoncentralTwoChief_iff.mpr
      ((Chief3323.hasNoncentralTwoChief_iff.mp h6').of_le (by norm_num))
  have h10 : ∀ A B : Subgroup G, IsTwoChiefFactor (conjClosure X D) A B →
      ¬ ⁅A, conjClosure X D⁆ ≤ B → 2 ^ 10 ≤ B.relIndex A := fun A B hc hn =>
    H.two_pow_ten_le hA hB hY hYB₀ htop hle hp hp24 hL hc hn
  obtain ⟨Ua, Va, hUVa, -⟩ := hY1
  obtain ⟨hc, hn⟩ := hUVa 0
  set U := Ua 0 with hUdef
  set V := Va 0 with hVdef
  have hUQ := H.le_pCoreOf_of_chief hA hB hY hYB₀ htop hle hc
  obtain ⟨-, hT₀, -⟩ := H.T₀_eq hB.le hB.nor hB.inf hB.max
  have hUTB : U ≤ T ⊓ B₀ := by
    rw [hT₀]
    exact hUQ.trans (pCoreOf_Y_le H.hBY)
  have hT4 := H.relIndex_T_eq_four hL2s htop hp hp24 hL
  have hcardT : Nat.card T = Nat.card ↥(B₀.subgroupOf T) * 4 := by
    rw [← hT4]
    exact (Subgroup.card_mul_index (B₀.subgroupOf T)).symm
  have hcardU : Nat.card U ≤ Nat.card ↥(B₀.subgroupOf T) := by
    rw [← Nat.card_congr (Subgroup.subgroupOfEquivOfLe (hUTB.trans inf_le_left)).toEquiv]
    exact Subgroup.card_le_of_le fun u hu => (hUTB hu).2
  have hUV := h10 U V hc hn
  have hcardUV : Nat.card U = Nat.card ↥(V.subgroupOf U) * V.relIndex U :=
    (Subgroup.card_mul_index (V.subgroupOf U)).symm
  have hV1 : 1 ≤ Nat.card ↥(V.subgroupOf U) := Nat.card_pos
  have hT12 : 2 ^ 12 ≤ Nat.card T := by
    rw [hcardT]
    nlinarith
  have hbot : conjClosure X D ≤ Subgroup.normalizer ((⊥ : Subgroup G) : Set G) := fun _ _ =>
    Subgroup.mem_normalizer_iff.mpr fun z => by simp
  have hV2 : IsPGroup 2 ↥V :=
    (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _).to_le (hc.1.le.trans hUQ)
  have hVY : ⁅V, conjClosure X D⁆ ≤ ⊥ := by
    refine Gen3324.commutator_le_of_ncAtMost H.oTwoUpper_Y bot_le (hc.1.le.trans hc.2.1) hbot
      hc.2.2.2.1 hV2 fun h => hY2 ?_
    obtain ⟨A', B', hAB', -⟩ := h
    obtain ⟨hc', hn', -, hA'⟩ := hAB' 0
    exact Chief3323.hasNoncentralTwoChief_two ⟨hc', hn'⟩ ⟨hc, hn⟩ hA'
  have hQY : ⁅pCoreOf 2 (conjClosure X D), conjClosure X D⁆ ≤ U := by
    refine Gen3324.commutator_le_of_ncAtMost H.oTwoUpper_Y hUQ
      (CFSG.LieType.BorelTits.pCoreOf_le 2 _) hc.2.2.1
      (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 _)
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 _) fun h => hY2 ?_
    obtain ⟨A', B', hAB', -⟩ := h
    obtain ⟨hc', hn', hB', -⟩ := hAB' 0
    exact Chief3323.hasNoncentralTwoChief_two ⟨hc, hn⟩ ⟨hc', hn'⟩ hB'
  refine ⟨⟨⟨Ua, Va, hUVa, fun i j hij => absurd hij (by
    rw [Subsingleton.elim i j]; exact lt_irrefl j)⟩, hY2, h10, hT12⟩, ?_, ?_⟩
  ·
    have hPU : pCoreOf 2 X ≤ U := H.pCoreOf_le_commutator.trans
      ((Subgroup.commutator_mono hO2 (le_conjClosure X D)).trans hQY)
    have hcomm := commutator_le_of_chief hc
    have hsq := sq_mem_of_chief hc
    have : Fact (IsPGroup 2 ↥(pCoreOf 2 X)) := ⟨CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X⟩
    have hΦ : frattini ↥(pCoreOf 2 X) ≤ V.comap (pCoreOf 2 X).subtype := by
      rw [CFSG.frattini_eq_closure_commutator_union_powers (p := 2), Subgroup.closure_le]
      rintro z (hz | ⟨w, rfl⟩)
      · have hz' : (pCoreOf 2 X).subtype z ∈ ⁅pCoreOf 2 X, pCoreOf 2 X⁆ := by
          have : (pCoreOf 2 X).subtype z ∈ (commutator ↥(pCoreOf 2 X)).map (pCoreOf 2 X).subtype :=
            Subgroup.mem_map_of_mem _ hz
          rwa [commutator_def, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
            Subgroup.range_subtype] at this
        exact hcomm ((Subgroup.commutator_mono hPU hPU) hz')
      · show ((w ^ 2 : ↥(pCoreOf 2 X)) : G) ∈ V
        rw [Subgroup.coe_pow, sq]
        exact hsq w (hPU w.2)
    rintro _ ⟨z, hz, rfl⟩
    have hzV : ((z : ↥(pCoreOf 2 X)) : G) ∈ V := hΦ hz
    refine ⟨⟨z, hc.1.le.trans hc.2.1 hzV⟩, Subgroup.mem_center_iff.mpr fun y => ?_, rfl⟩
    have h1 : ⁅(z : G), (y : G)⁆ = 1 := (Subgroup.mem_bot).mp
      (hVY (Subgroup.commutator_mem_commutator hzV y.2))
    apply Subtype.ext
    rw [commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  ·
    intro hZ
    by_contra hT
    push Not at hT
    have hT' : Nat.card T = 2 ^ 12 := le_antisymm hT hT12
    have hcard10 : Nat.card ↥(B₀.subgroupOf T) = 2 ^ 10 := by omega
    have hUeq : Nat.card U = 2 ^ 10 := by
      have h2 : 2 ^ 10 ≤ Nat.card U := by
        rw [hcardUV]
        nlinarith
      have := hcardU.trans hcard10.le
      omega
    have hVbot : V = ⊥ := by
      have h1 : Nat.card ↥(V.subgroupOf U) = 1 := by
        rw [hcardUV] at hUeq
        exact le_antisymm (by nlinarith) hV1
      rw [eq_bot_iff]
      intro v hv
      have h3 : (⟨v, hc.1.le hv⟩ : ↥U) ∈ V.subgroupOf U := hv
      rw [Subgroup.card_eq_one.mp h1, Subgroup.mem_bot] at h3
      exact (Subgroup.mem_bot).mpr (congrArg Subtype.val h3)
    have hUeqTB : T ⊓ B₀ = U := by
      symm
      refine Subgroup.eq_of_le_of_card_ge hUTB (le_of_eq ?_)
      have h1 : Nat.card ↥(T ⊓ B₀) = Nat.card ↥(B₀.subgroupOf T) := by
        rw [← Subgroup.inf_subgroupOf_left B₀ T]
        exact (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv).symm
      rw [h1, hcard10, hUeq]
    apply hZ
    rw [eq_bot_iff]
    intro z hz
    rw [Subgroup.mem_bot]
    have hYTB : conjClosure X D ⊔ T ≤ X ⊔ T ⊔ D := sup_le Y_le_B (le_sup_right.trans le_sup_left)
    set Zc := (Subgroup.center ↥(conjClosure X D ⊔ T)).map (conjClosure X D ⊔ T).subtype
      with hZc
    have hZcB : Zc ≤ X ⊔ T ⊔ D := (Subgroup.map_subtype_le _).trans hYTB
    obtain ⟨hsB, hnabB⟩ := H.simple_quot hA hB hY hYB₀ htop
    have hYTZ : conjClosure X D ⊔ T ≤ Subgroup.normalizer (Zc : Set G) := by
      refine Main3324.le_normalizer_of_conj fun y hy c hc' => ?_
      obtain ⟨c', hc'', rfl⟩ := hc'
      have h1 := Subgroup.mem_center_iff.mp hc'' ⟨y, hy⟩
      have h2 : y * (c' : G) = (c' : G) * y := congrArg Subtype.val h1
      have e : y * (c' : G) * y⁻¹ = c' := by
        rw [h2]
        group
      rw [Subgroup.coe_subtype, e]
      exact ⟨c', hc'', rfl⟩
    have hZcn : (star (X ⊔ T ⊔ D) B₀ Zc).Normal := by
      refine ⟨fun n hn q => ?_⟩
      have hq : q ∈ star (X ⊔ T ⊔ D) B₀ (conjClosure X D) := by
        rw [htop]
        exact Subgroup.mem_top q
      obtain ⟨y, hyB, hy, rfl⟩ := mem_star_iff.mp hq
      exact (Subgroup.mem_normalizer_iff.mp
        (mk_mem_normalizer_star hyB (hYTZ (Subgroup.mem_sup_left hy))) n).mp hn
    have hZcs : Group.IsSolvable ↥Zc :=
      Group.isSolvable_of_surjective ((conjClosure X D ⊔ T).subtype.subgroupMap_surjective _)
    have hstar := eq_bot_of_isSolvable hnabB _ (isSolvable_star hZcB hZcs)
    rw [star_eq_bot_iff hZcB] at hstar
    have hzB₀ : (z : G) ∈ B₀ := hstar ⟨z, hz, rfl⟩
    have hzO : (z : G) ∈ pCoreOf 2 (conjClosure X D ⊔ T) := by
      rw [hP]
      exact ⟨z.2, hzB₀⟩
    have hsylYT : IsSylowTwoOf T (conjClosure X D ⊔ T) :=
      ⟨le_sup_right, H.h.sylow.1, fun h2 => H.h.sylow.2
        (h2.trans (Subgroup.relIndex_dvd_index_of_le le_sup_right))⟩
    have hzT : (z : G) ∈ T := EscapingLocal.pCoreOf_le_of_isSylowTwoOf hsylYT hzO
    have hzU : (z : G) ∈ U := hUeqTB ▸ ⟨hzT, hzB₀⟩
    have hUV' : U ≤ Subgroup.normalizer (V : Set G) := hc.2.1.trans hc.2.2.2.1
    have hfix : (z : G) ∈ fixSub U V (conjClosure X D) hUV' := mem_fixSub.mpr ⟨hzU, fun y hy => by
      have h1 := Subgroup.mem_center_iff.mp hz ⟨y, Subgroup.mem_sup_left hy⟩
      have h2 : y * (z : G) = (z : G) * y := congrArg Subtype.val h1
      have e : (z : G)⁻¹ * (y * z * y⁻¹) = 1 := by
        rw [h2]
        group
      rw [e]
      exact V.one_mem⟩
    have heq : fixSub U V (conjClosure X D) hUV' = V := by
      by_contra hne
      apply hn
      exact commutator_le_of_fixSub_eq (chief_eq hc (le_fixSub hUV' hc.1.le hc.2.2.2.1)
        (fixSub_le hUV') ((le_inf (le_inf hc.2.2.1 hc.2.2.2.1) Subgroup.le_normalizer).trans
          (le_normalizer_fixSub hUV')) hne)
    rw [heq, hVbot] at hfix
    exact Subtype.ext ((Subgroup.mem_bot).mp hfix)

end Hyp3320

end S3320

theorem step3_3_20_of (hF : F6.TheoremF618Cat) (hIF : F6.InspF618Rest)
    (hIW : S3320.InspWalter3320) (hA21 : AsA21SQTKSection) (h36 : Vol2Native.A36ForSQTKCat)
    (h37 : Vol2Native.A37ForSQTKCat) (h38 : Vol2Native.A38ForSQTKCat)
    (h39 : Vol2Native.A39ForSQTKCat) (hA : AS_A_1_31) (h312 : Vol2Native.A312ForSQTKCat)
    (hI : InspA312F618)
    (hA6 : ∀ (Q : Type) [Group Q] [Finite Q], (IsAlt 6 Q ∨ F6.IsL2 3 2 Q) → AutOddNormCent Q)
    (hA7 : ∀ (Q : Type) [Group Q] [Finite Q], IsAlt 7 Q → AutOddNormCent Q)
    (hM12 : ∀ (Q : Type) [Group Q] [Finite Q], F6.IsM12 Q → AutOddNormCent Q)
    (hL2Sq : ∀ p : ℕ, p.Prime → 3 < p → ∀ (Q : Type) [Group Q] [Finite Q], IsPSL 2 p 2 Q →
      AutOddNormCent Q)
    (hL2p : FactAutOddL2pPlus) (hL3 : FactAutL3Eps) (hL2o : FactAutL2pOuter)
    (hL2s : FactL2pSylowFour) (hL2n : FactL2pSylowNorm) : Step3_3_20 := by
  intro G _ _ T M L D X h hXX hTX hS3 hD hInH hBY hBeq
  have H : S3320.Hyp3320 G T M L D X := ⟨h, hXX, hTX, hS3, hD, hInH, hBY, hBeq⟩
  obtain ⟨B₀, hB⟩ := S3320.Hyp3320.exists_isB₀ (X := X) (T := T) (D := D)
  have : (B₀.subgroupOf (X ⊔ T ⊔ D)).Normal := Subgroup.normal_subgroupOf_of_le_normalizer hB.nor
  obtain ⟨g, hg, -, hcase, hsimp, hnab, -, -, hK₀top, hY, hYB₀, htop, hle, hP, p, hp, hp24, hL⟩ :=
    H.exists_data hF hIF hIW hA21 h36 h37 h38 h39 hA h312 hI hA6 hA7 hM12 hL2Sq hL2p hL3 hL2o
      hL2s hB
  obtain ⟨hn3, ⟨e⟩⟩ := H.dih_XT hA hB hY hYB₀ htop hg hcase hsimp hnab hK₀top hP
  have hO2 := H.pCoreOf_X_le hle hP e
  exact ⟨⟨p, hp, hp24, H.isPSL_YT hA hB hY hYB₀ htop hle hL⟩,
    ⟨hO2, ⟨hn3, ⟨e⟩⟩, H.relIndex_normalizer_X hL2n hB hle htop hp hp24 hL⟩,
    H.concl4 hA hB hY hYB₀ htop hle hg hK₀top hO2 hp hp24 hL,
    fun hX5 => H.concl5 hL2s hA hB hY hYB₀ htop hle hP hg hK₀top hO2 hp hp24 hL hX5⟩

end CFSG.Quasithin.H13

module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Hypotheses
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Inputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.TwelveShort
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs15
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8Fin
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenThreeY2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven3Close16CoverKer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven10Case2Ord
import CFSG.Open.StatedZModTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.ComponentInitial.BinarySymplecticSix
open CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag (stabilizer)

variable {G : Type} [Group G] [Finite G]

theorem c8_isSimpleGroup_of_isSpn {X : Type} [Group X] (h : IsSpn X 6 1) :
    IsSimpleGroup X ∧ Group.IsPerfect X := by
  obtain ⟨-, K, instK, instFin, hKcard, ⟨e⟩⟩ := h
  letI : Field K := instK
  letI : Finite K := instFin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  haveI : IsSimpleGroup (StatedProj (StatedSp (6 / 2) K)) :=
    CFSG.ClassicalGroups.Symplectic.isSimpleGroup_statedProj_statedSp K (6 / 2) (by norm_num)
      (Or.inr (Or.inr ⟨hK2, by norm_num⟩))
  have hscal : (StatedScalars (Fin (6 / 2) ⊕ Fin (6 / 2)) K).subgroupOf
      (StatedSp (6 / 2) K) = ⊥ := by
    rw [CFSG.Open.StatedAPI.statedScalars_eq_bot_of_card_two hK2, Subgroup.bot_subgroupOf]
  let eP : StatedProj (StatedSp (6 / 2) K) ≃* StatedSp (6 / 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hscal).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (StatedSp (6 / 2) K) := eP.symm.isSimpleGroup
  have hP : Group.IsPerfect (StatedSp (6 / 2) K) :=
    CFSG.ClassicalGroups.Symplectic.isPerfect_statedSp (6 / 2) K
      (Or.inr (Or.inr ⟨hK2, by norm_num⟩))
  exact ⟨e.isSimpleGroup,
    Group.IsPerfect.ofSurjective (f := e.symm.toMonoidHom) e.symm.surjective⟩

theorem c8_isQuasisimple_of_isSpn {X : Type} [Group X] (h : IsSpn X 6 1) :
    CFSG.Open.IsQuasisimple X := by
  obtain ⟨hs, hPX⟩ := c8_isSimpleGroup_of_isSpn h
  haveI := hs
  have hZ : Subgroup.center X = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center X) with h | h
    · exact h
    · exfalso
      haveI := hPX
      exact Group.IsPerfect.not_isMulCommutative X
        (IsMulCommutative.of_comm fun x y => by
          have hy : y ∈ Subgroup.center X := by rw [h]; exact Subgroup.mem_top y
          exact Subgroup.mem_center_iff.mp hy x)
  refine ⟨hPX.commutator_eq_top, ?_⟩
  exact ((QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot).isSimpleGroup

theorem c8_exists_Y (D : Data G) (h127 : R127 D) (h119 : F11.R119 D) (h1217 : R1217 D)
    (hSpA : RSp6SmallMod) (hSpC : RSp6SpinCent) {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (hS : Sect16 D V₀ V L hV) (h8 : Case167_8 D V₀ V hV L) :
    ∃ Y : Subgroup G, Y ≤ D.M ∧ D.M ≤ normalizer (Y : Set G) ∧ ⁅Y, Y⁆ = Y ∧ F11.O2E Y = Y ∧
      Y ⊓ F11.CTilde D.M V₀ V ≤ OInf Y ∧ barSub V₀ V hV Y = lBar V₀ V hV L := by
  have hP := hS.setting.hyp16.hyp125.pairFacts
  have hMs : D.M ≤ stabTil V₀ V := le_stabTil hP.le_normalizer hP.le_normalizer₀
  have hM : Mbar D.M V₀ V hV = lBar V₀ V hV L := c8_mbar_eq_lbar D h1217 hSpA hSpC hS h8
  let inst₀ : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := s15_Three_cTilde_normal hV hMs
  haveI := inst₀
  have hCX : F11.CTilde D.M V₀ V ≤ D.M := by
    rw [cTilde_eq_preBarSub_bot hV hP.le_normalizer]
    exact inf_le_left
  obtain ⟨e, he⟩ := s15_Three_barImage_equiv (D := D) (V₀ := V₀) (V := V) hV hMs
  have hlayer : rankThreeLayer (F11.barImage11 D.M V₀ V D.M) = F11.barImage11 D.M V₀ V D.M := by
    set B : Subgroup (F11.MBar11 D.M V₀ V) := F11.barImage11 D.M V₀ V D.M with hBdef
    have hmap : B.map e.toMonoidHom = (lBar V₀ V hV L).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [hBdef, he D.M le_rfl, ← hM]
    let eB : ↥B ≃* ↥(lBar V₀ V hV L) :=
      ((Subgroup.equivMapOfInjective B e.toMonoidHom e.injective).trans
        (MulEquiv.subgroupCongr hmap)).trans
        (Subgroup.subgroupOfEquivOfLe hM.symm.le)
    have hqB : CFSG.Open.IsQuasisimple ↥B :=
      CFSG.Open.IsQuasisimple.of_mulEquiv eB (c8_isQuasisimple_of_isSpn h8.1)
    exact le_antisymm (sSup_le fun _ hK => hK.1)
      (le_sSup ⟨le_rfl, CFSG.Open.IsSubnormal.refl B, hqB⟩)
  obtain ⟨Y, hY, -⟩ :=
    h119 V₀ V (Hyp125.hyp11 h127 hS.setting.hyp16.hyp125) D.M hCX le_rfl hlayer
  have hY_le : Y ≤ D.M := hY.1
  have hYbar : F11.barImage11 D.M V₀ V Y = F11.barImage11 D.M V₀ V D.M := hY.2.2.2.2.2
  have hbarY : barSub V₀ V hV Y = lBar V₀ V hV L := by
    have hsub : (barSub V₀ V hV Y).subgroupOf (Mbar D.M V₀ V hV) =
        (barSub V₀ V hV D.M).subgroupOf (Mbar D.M V₀ V hV) := by
      rw [← he Y hY_le, ← he D.M le_rfl, hYbar]
    have h2 := congrArg (Subgroup.map (Subgroup.subtype (Mbar D.M V₀ V hV))) hsub
    simp only [Subgroup.subgroupOf_map_subtype] at h2
    rw [inf_eq_left.2 (barSub_mono V₀ V hV hY_le), inf_eq_left.2 le_rfl] at h2
    exact h2.trans hM
  exact ⟨Y, hY_le, hY.2.2.2.1, hY.2.1, hY.2.2.1, hY.2.2.2.2.1, hbarY⟩

theorem c8_exists_hom_barSub {D : Data G} {V₀ V : Subgroup G} {hV : IsElemAbelian 2 V}
    (hM : D.M ≤ stabTil V₀ V) {X : Subgroup G} (hXM : X ≤ D.M) :
    ∃ φ : ↥X →* ↥(barSub V₀ V hV X), Function.Surjective φ ∧
      φ.ker = (X ⊓ F11.CTilde D.M V₀ V).subgroupOf X := by
  have hXs : X ≤ stabTil V₀ V := hXM.trans hM
  let ψ : ↥X →* ↥(stabTil V₀ V) := Subgroup.inclusion hXs
  let φ : ↥X →* ↥(barSub V₀ V hV X) :=
    MonoidHom.codRestrict ((actTil V₀ V hV).comp ψ) (barSub V₀ V hV X)
      (fun g => (mem_barSub V₀ V hV X _).2 ⟨ψ g, g.2, rfl⟩)
  refine ⟨φ, ?_, ?_⟩
  · rintro ⟨_, hφ⟩
    obtain ⟨g, hg, rfl⟩ := (mem_barSub V₀ V hV X _).1 hφ
    exact ⟨⟨(g : G), hg⟩, rfl⟩
  · ext g
    have hMn : D.M ≤ normalizer (V : Set G) := hM.trans (stabTil_le_normalizer V₀ V)
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, Subgroup.mem_inf, mem_cTilde_iff hV hMn]
    have hgX : (g : G) ∈ X := g.2
    constructor
    · intro h1
      exact ⟨hgX, hXM hgX, hXs hgX, congrArg Subtype.val h1⟩
    · rintro ⟨-, -, h, h1⟩
      exact Subtype.ext h1

theorem c8_pCore_le_of_simple_quot {Q S : Type} [Group Q] [Finite Q] [Group S] [IsSimpleGroup S]
    (hS2 : ¬ IsPGroup 2 S) (N : Subgroup Q) [N.Normal] (e : Q ⧸ N ≃* S) :
    CFSG.pCore 2 Q ≤ N := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : IsSimpleGroup (Q ⧸ N) := MulEquiv.isSimpleGroup e
  let π : Q →* Q ⧸ N := QuotientGroup.mk' N
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective N
  haveI hPn : ((CFSG.pCore 2 Q).map π).Normal :=
    Subgroup.Normal.map inferInstance π hπ
  have hP2 : IsPGroup 2 ↥((CFSG.pCore 2 Q).map π) :=
    (CFSG.pCore_isPGroup).map π
  rcases (IsSimpleGroup.eq_bot_or_eq_top_of_normal ((CFSG.pCore 2 Q).map π)) with h | h
  · intro x hx
    have : π x ∈ (CFSG.pCore 2 Q).map π := Subgroup.mem_map_of_mem π hx
    rw [h, Subgroup.mem_bot] at this
    exact (QuotientGroup.eq_one_iff x).mp this
  · exfalso
    have hq2 : IsPGroup 2 (Q ⧸ N) := by
      rw [h] at hP2
      exact hP2.of_equiv Subgroup.topEquiv
    exact hS2 (hq2.of_equiv e)

theorem c8_le_pCore_of_simple_quot {Q S : Type} [Group Q] [Finite Q] [Group S] [IsSimpleGroup S]
    (hS2 : ¬ IsPGroup 2 S)
    (hSchur : ∀ (Q' : Type) [Group Q'] [Finite Q'], Group.IsPerfect Q' →
      ∀ q : Q' →* S, Function.Surjective q → q.ker ≤ Subgroup.center Q' → Nat.card q.ker ∣ 2)
    (hQ : Group.IsPerfect Q)
    (hL : CFSG.Open.rankThreeLayer (⊤ : Subgroup (Q ⧸ CFSG.pCore 2 Q)) = ⊤)
    (N : Subgroup Q) [N.Normal] (hN : Group.IsSolvable ↥N)
    (e : Q ⧸ N ≃* S) : N ≤ CFSG.pCore 2 Q := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Group.IsPerfect Q := hQ
  set R := CFSG.pCore 2 Q with hR
  have hRN : R ≤ N := c8_pCore_le_of_simple_quot hS2 N e
  let π : Q →* Q ⧸ R := QuotientGroup.mk' R
  have hπ : Function.Surjective π := QuotientGroup.mk'_surjective R
  let f : Q →* S := e.toMonoidHom.comp (QuotientGroup.mk' N)
  have hfR : ∀ x ∈ R, f x = 1 := by
    intro x hx
    have h1 : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr (hRN hx)
    simp only [f, MonoidHom.comp_apply, h1, map_one]
  let q : Q ⧸ R →* S := QuotientGroup.lift R f hfR
  have hqπ : ∀ x : Q, q (π x) = f x := fun x => rfl
  have hq : Function.Surjective q := by
    intro a
    obtain ⟨x, hx⟩ := e.surjective a |>.imp fun y hy => hy
    obtain ⟨x, rfl⟩ := QuotientGroup.mk'_surjective N x
    exact ⟨π x, by rw [hqπ]; exact hx⟩
  have hkerS : q.ker = N.map π := by
    ext y
    obtain ⟨x, rfl⟩ := hπ y
    rw [MonoidHom.mem_ker, hqπ, Subgroup.mem_map]
    constructor
    · intro hfx
      refine ⟨x, ?_, rfl⟩
      have : QuotientGroup.mk' N x = 1 := by
        apply e.injective
        simpa [f] using hfx
      exact (QuotientGroup.eq_one_iff x).mp this
    · rintro ⟨x', hx', hxx'⟩
      have hx'' : x'⁻¹ * x ∈ R := (QuotientGroup.eq).mp hxx'
      have hxN : x ∈ N := by
        have := N.mul_mem hx' (hRN hx'')
        simpa using this
      have : QuotientGroup.mk' N x = 1 := (QuotientGroup.eq_one_iff x).mpr hxN
      simp only [f, MonoidHom.comp_apply, this, map_one]
  have hSsolv : Group.IsSolvable ↥q.ker := by
    rw [hkerS]
    exact Group.isSolvable_of_surjective (f := π.subgroupMap N)
      (MonoidHom.subgroupMap_surjective π N)
  haveI : q.ker.Normal := MonoidHom.normal_ker q
  have hSc : q.ker ≤ Subgroup.center (Q ⧸ R) := close16_le_center_of_isSolvable hL hSsolv
  have hQb : Group.IsPerfect (Q ⧸ R) := Group.IsPerfect.ofSurjective hπ
  have hdvd := hSchur (Q ⧸ R) hQb q hq hSc
  have hS2' : IsPGroup 2 ↥q.ker := by
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_two (m := 1)).mp (by simpa using hdvd)
    exact IsPGroup.of_card (n := k) hk'
  have hSle : q.ker ≤ CFSG.pCore 2 (Q ⧸ R) := le_sSup ⟨inferInstance, hS2'⟩
  rw [CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot] at hSle
  intro x hx
  have hmem : π x ∈ q.ker := by rw [hkerS]; exact Subgroup.mem_map_of_mem π hx
  have h1 : π x = 1 := by simpa using hSle hmem
  exact (QuotientGroup.eq_one_iff x).mp h1

theorem c8_layer_top_of_O2E_eq {Y : Subgroup G} (hYE : F11.O2E Y = Y) :
    CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)) = ⊤ := by
  have hπ : Function.Surjective (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) :=
    QuotientGroup.mk'_surjective _
  have hTop : (⊤ : Subgroup ↥Y).map Y.subtype = Y := by
    rw [Subgroup.map_top, Subgroup.range_subtype]
  have hcomap : (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y))).comap
      (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)) = ⊤ := by
    apply Subgroup.map_injective Y.subtype_injective
    change F11.O2E Y = (⊤ : Subgroup ↥Y).map Y.subtype
    rw [hYE, hTop]
  have h := Subgroup.map_comap_eq_self_of_surjective hπ
    (CFSG.Open.rankThreeLayer (⊤ : Subgroup (Bar2 Y)))
  rw [hcomap, Subgroup.map_top_of_surjective _ hπ] at h
  exact h.symm

theorem c8_cTilde_isPGroup (D : Data G) (hSchur : C8SchurSp6) {V₀ V Y : Subgroup G}
    {hV : IsElemAbelian 2 V} (hMs : D.M ≤ stabTil V₀ V) (hYM : Y ≤ D.M) (hperf : ⁅Y, Y⁆ = Y)
    (hE : F11.O2E Y = Y) (hinf : Y ⊓ F11.CTilde D.M V₀ V ≤ OInf Y)
    (hsp : IsSpn ↥(barSub V₀ V hV Y) 6 1) : IsPGroup 2 ↥(Y ⊓ F11.CTilde D.M V₀ V) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨φ, hφ, hker⟩ := c8_exists_hom_barSub (hV := hV) hMs hYM
  obtain ⟨hsimp, -⟩ := c8_isSimpleGroup_of_isSpn hsp
  haveI := hsimp
  have hS2 : ¬ IsPGroup 2 ↥(barSub V₀ V hV Y) := by
    intro h2
    obtain ⟨n, hn⟩ := h2.exists_card_eq
    rw [s16c1610_card_of_isSpn_six hsp] at hn
    have h3 : 3 ∣ 2 ^ n := hn ▸ (by norm_num : 3 ∣ 1451520)
    have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3
    omega
  set N : Subgroup ↥Y := (Y ⊓ F11.CTilde D.M V₀ V).subgroupOf Y with hNdef
  haveI : N.Normal := by rw [← hker]; exact MonoidHom.normal_ker φ
  have e : ↥Y ⧸ N ≃* ↥(barSub V₀ V hV Y) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective φ hφ)
  have hP : Group.IsPerfect ↥Y := Subgroup.isPerfect_iff.mpr hperf
  have hL := c8_layer_top_of_O2E_eq hE
  have hN : Group.IsSolvable ↥N := by
    have hle : N ≤ CFSG.solvableRadical ↥Y := by
      intro x hx
      obtain ⟨y, hy, hyx⟩ := hinf (Subgroup.mem_subgroupOf.mp hx)
      have hyx' : y = x := Subtype.ext hyx
      exact hyx' ▸ hy
    haveI := CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical (G := ↥Y)
    exact Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hle)
      (Subgroup.inclusion_injective hle)
  have h2 := c8_le_pCore_of_simple_quot hS2
    (fun Q' _ _ hQ' q hq hc => hSchur _ Q' hsp hQ' q hq hc) hP hL N hN e
  have hNp : IsPGroup 2 ↥N := CFSG.pCore_isPGroup.to_le h2
  have hle : Y ⊓ F11.CTilde D.M V₀ V ≤ Y := inf_le_left
  exact hNp.of_equiv (Subgroup.subgroupOfEquivOfLe hle)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

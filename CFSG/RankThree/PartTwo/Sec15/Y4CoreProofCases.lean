module

public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofSeven
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofDelta
import CFSG.RankThree.PartTwo.Sec17.Item171StepsProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148StepQuot
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKTypeTheta
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri
import CFSG.RankThree.PartTwo.KFacts.K72SylowL3
import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
import CFSG.Sporadic.ON
public import CFSG.RankThree.PartTwo.Sec15.Item15Type
public import CFSG.RankThree.PartTwo.Sec15.Y4CoreProofRead

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G]

@[expose] noncomputable def Read148PerfR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → ∀ Y ∈ scriptY A,
      Group.IsPerfect ↥(((deltaZero A (lB A) Y).subgroupOf Y).map
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)))

namespace Y4Core

omit [Finite G] in
theorem nonempty_img148_equiv_map {A Y X : Subgroup G} (hY : A ≤ Subgroup.normalizer (Y : Set G))
    (hXY : X ≤ Y) :
    letI := ker148_normal hY
    Nonempty (↥(img148 A Y X) ≃*
      ↥((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)))) := by
  let := ker148_normal hY
  set f₁ : ↥X →* ↥(Y ⊔ A) ⧸ ker148 A Y :=
    (QuotientGroup.mk' (ker148 A Y)).comp (Subgroup.inclusion (hXY.trans le_sup_left)) with hf₁
  set f₂ : ↥X →* ↥Y ⧸ CFSG.pPrimeCore 3 ↥Y :=
    (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)).comp (Subgroup.inclusion hXY) with hf₂
  have hr₁ : f₁.range = img148 A Y X := by
    rw [hf₁, MonoidHom.range_comp, Subgroup.inclusion_range]
    rfl
  have hr₂ : f₂.range = (X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)) := by
    rw [hf₂, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hk : f₁.ker = f₂.ker := by
    ext x
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker, hf₁, hf₂, MonoidHom.comp_apply,
      MonoidHom.comp_apply, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff,
      QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, ker148, Subgroup.mem_subgroupOf,
      Subgroup.coe_inclusion, pPrimeCoreOf, Subgroup.mem_map]
    constructor
    · rintro ⟨z, hz, hzx⟩
      have : z = Subgroup.inclusion hXY x := Subtype.ext hzx
      exact this ▸ hz
    · intro hx
      exact ⟨Subgroup.inclusion hXY x, hx, rfl⟩
  exact ⟨(((MulEquiv.subgroupCongr hr₁).symm.trans
    (QuotientGroup.quotientKerEquivRange f₁).symm).trans
    (QuotientGroup.quotientMulEquivOfEq hk)).trans
    ((QuotientGroup.quotientKerEquivRange f₂).trans (MulEquiv.subgroupCongr hr₂))⟩

theorem alternatingGroup_five_nonabelian :
    ∃ a b : alternatingGroup (Fin 5), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    fun h => ?_⟩
  have := congrArg Subtype.val h
  revert this
  decide

theorem alternatingGroup_six_nonabelian :
    ∃ a b : alternatingGroup (Fin 6), a * b ≠ b * a := by
  refine ⟨⟨Equiv.swap 0 1 * Equiv.swap 1 2, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    ⟨Equiv.swap 1 2 * Equiv.swap 2 3, by rw [Equiv.Perm.mem_alternatingGroup]; decide⟩,
    fun h => ?_⟩
  have := congrArg Subtype.val h
  revert this
  decide

theorem isSimpleGroup_alternatingGroup (n : ℕ) (hn : 5 ≤ n) :
    IsSimpleGroup (alternatingGroup (Fin n)) :=
  alternatingGroup.isSimpleGroup (by rw [Nat.card_eq_fintype_card, Fintype.card_fin]; exact hn)

theorem three_dvd_card_alternatingGroup (n : ℕ) (hn : 3 ≤ n) :
    3 ∣ Nat.card (alternatingGroup (Fin n)) := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.mpr (by omega)
  have h2 := two_mul_card_alternatingGroup (α := Fin n)
  rw [Fintype.card_perm, Fintype.card_fin] at h2
  have h3 : 3 ∣ 2 * Fintype.card (alternatingGroup (Fin n)) := by
    rw [h2]
    exact Nat.dvd_factorial (by norm_num) hn
  rw [Nat.card_eq_fintype_card]
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num) h3)

theorem good3_alternatingGroup_five : Good3 (alternatingGroup (Fin 5)) :=
  have := isSimpleGroup_alternatingGroup 5 le_rfl
  good3_of_isSimpleGroup alternatingGroup_five_nonabelian (three_dvd_card_alternatingGroup 5
    (by norm_num))

theorem good3_alternatingGroup_six : Good3 (alternatingGroup (Fin 6)) :=
  have := isSimpleGroup_alternatingGroup 6 (by norm_num)
  good3_of_isSimpleGroup alternatingGroup_six_nonabelian (three_dvd_card_alternatingGroup 6
    (by norm_num))

theorem prodComp_of_mulEquiv_simple {X T : Type*} [Group X] [Group T] [Finite X] [Finite T]
    [IsSimpleGroup T] (hX : Group.IsPerfect X) (φ : X ≃* T) (h3 : 3 ∣ Nat.card T) :
    ProdComp X := by
  have : IsSimpleGroup X := φ.isSimpleGroup
  have : Nontrivial X := IsSimpleGroup.toNontrivial
  refine ProdComp.of_good3 (good3_of_isSimpleGroup (exists_ne_comm_of_isPerfect hX) ?_)
  rwa [Nat.card_congr φ.toEquiv]

theorem prodComp_of_isTripleCover {X S : Type*} [Group X] [Group S] [Finite X] [Finite S]
    [IsSimpleGroup S] (hX : Group.IsPerfect X) (h : Sec4.IsTripleCover X S)
    (h3 : 3 ∣ Nat.card S) : ProdComp X := by
  obtain ⟨hz, ⟨φ⟩⟩ := h
  have hSp : Group.IsPerfect S :=
    Group.IsPerfect.ofSurjective (f := φ.toMonoidHom.comp (QuotientGroup.mk' _))
      (φ.surjective.comp (QuotientGroup.mk'_surjective _))
  have : Nontrivial S := IsSimpleGroup.toNontrivial
  have hS := exists_ne_comm_of_isPerfect hSp
  exact ProdComp.of_isQuasisimple (isQuasisimple_of_isTripleCover hS hX ⟨hz, ⟨φ⟩⟩)
    (Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isTripleCover ⟨hz, ⟨φ⟩⟩
      (Sec17.Proof171Steps.oPrimeResidual_eq_top_of_isSimpleGroup h3))

theorem prodComp_case7 {M : Type} [Group M] [Finite M] {X J₁ J₂ B : Subgroup M}
    (hX : Group.IsPerfect ↥X) (hsup : J₁ ⊔ J₂ = X) (hinf : J₁ ⊓ J₂ = ⊥) (hcomm : ⁅J₁, J₂⁆ = ⊥)
    (hB : IsMulCommutative B) (hBX : B ≤ Subgroup.normalizer (X : Set M)) {p₁ f₁ p₂ f₂ : ℕ}
    (hZ₁ : Sec14.IsZ3PGLThreeAt ↥(J₁ ⊔ B) p₁ f₁) (hZ₂ : Sec14.IsZ3PGLThreeAt ↥(J₂ ⊔ B) p₂ f₂) :
    ProdComp ↥X := by
  have hJ₁X : J₁ ≤ X := hsup ▸ le_sup_left
  have hJ₂X : J₂ ≤ X := hsup ▸ le_sup_right
  have hC₁ : J₂ ≤ Subgroup.centralizer (J₁ : Set M) := by
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_comm]
    exact hcomm
  have hC₂ : J₁ ≤ Subgroup.centralizer (J₂ : Set M) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm
  have hN₁ : X ≤ Subgroup.normalizer (J₁ : Set M) := by
    rw [← hsup]
    exact sup_le Subgroup.le_normalizer (hC₁.trans (Subgroup.centralizer_le_normalizer _))
  have hN₂ : X ≤ Subgroup.normalizer (J₂ : Set M) := by
    rw [← hsup]
    exact sup_le (hC₂.trans (Subgroup.centralizer_le_normalizer _)) Subgroup.le_normalizer
  set U := J₁.subgroupOf X with hU
  set V := J₂.subgroupOf X with hV
  have hUn : U.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₁X).mpr hN₁
  have hVn : V.Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hJ₂X).mpr hN₂
  have hsup' : U ⊔ V = ⊤ := by
    rw [hU, hV, ← Subgroup.subgroupOf_sup hJ₁X hJ₂X, hsup, Subgroup.subgroupOf_self]
  have hinf' : U ⊓ V = ⊥ := by
    rw [eq_bot_iff]
    intro x hx
    have h1 : (x : M) ∈ J₁ ⊓ J₂ := ⟨hx.1, hx.2⟩
    rw [hinf] at h1
    exact (Subgroup.mem_bot).mpr (Subtype.ext ((Subgroup.mem_bot).mp h1))
  have hcomm' : ⁅U, V⁆ = ⊥ := le_bot_iff.mp (hinf' ▸ Subgroup.commutator_le_inf U V)
  have hUp : ⁅U, U⁆ = U := commutator_eq_self_of_inf_eq_bot hX hsup' hinf'
  have hVp : ⁅V, V⁆ = V :=
    commutator_eq_self_of_inf_eq_bot hX (by rw [sup_comm]; exact hsup')
      (by rw [inf_comm]; exact hinf')
  have hJ₁p : ⁅J₁, J₁⁆ = J₁ := by
    have := congrArg (Subgroup.map X.subtype) hUp
    rwa [Subgroup.map_commutator, hU, Subgroup.map_subgroupOf_eq_of_le hJ₁X] at this
  have hJ₂p : ⁅J₂, J₂⁆ = J₂ := by
    have := congrArg (Subgroup.map X.subtype) hVp
    rwa [Subgroup.map_commutator, hV, Subgroup.map_subgroupOf_eq_of_le hJ₂X] at this
  have hG₁ : Good3 ↥J₁ := good3_of_isZ3PGLThreeAt hJ₁X hN₁ hJ₁p hB hBX hZ₁
  have hG₂ : Good3 ↥J₂ := good3_of_isZ3PGLThreeAt hJ₂X hN₂ hJ₂p hB hBX hZ₂
  exact ProdComp.of_central hX hsup' hcomm'
    (hG₁.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ₁X).symm).quot_center
    (hG₂.of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJ₂X).symm).quot_center

section Cases


theorem prodComp_img148
    {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hperf : letI := ker148_normal hY.2
      Group.IsPerfect ↥(img148 A Y (deltaZero A (lB A) Y)))
    (h1 : ¬ deltaZero A (lB A) Y ≤ pPrimeCoreOf 3 Y) :
    letI := ker148_normal hY.2
    ProdComp ↥(img148 A Y (deltaZero A (lB A) Y)) := by
  let := ker148_normal hY.2
  have hAab : IsMulCommutative A := h.isElemAbelian.1
  rcases (h148 Y hY).2 with h1' | h2 | h3 | h4 | h5 | h6 | h7
  · exact absurd h1' h1
  ·
    obtain ⟨c', hc', -, L', hL', hcases⟩ := h2
    rcases hcases with hφ | ⟨-, hφ⟩ | ⟨p, f, e, hp, hf, he, -, hε⟩ | ⟨-, h6' | hφ⟩
    · obtain ⟨φ⟩ := hφ
      have hLc : L' ∈ thetaComponentsAt 3 c' := hL'.1
      have hT := (h.chosen136.2 c' hc' L' hL').1
      exact ProdComp.of_mulEquiv φ.symm (ProdComp.of_isQuasisimple
        (Sec6.isQuasisimple_of_mem_thetaComponentsAt hLc)
        (Sec17.Proof171Steps.oPrimeResidual_quot_eq_top_of_types hLc hT))
    · obtain ⟨φ⟩ := hφ
      have := isSimpleGroup_alternatingGroup 7 (by norm_num)
      exact prodComp_of_mulEquiv_simple hperf φ (three_dvd_card_alternatingGroup 7 (by norm_num))
    · have := Main148.isSimpleGroup_of_isLThreeEpsAt148 hf hε
      exact prodComp_of_mulEquiv_simple hperf (MulEquiv.refl _)
        (Main148.three_dvd_card_of_isLThreeEpsAt148 hf hε)
    · have := isSimpleGroup_alternatingGroup 6 (by norm_num)
      exact prodComp_of_isTripleCover hperf h6' (three_dvd_card_alternatingGroup 6 (by norm_num))
    · obtain ⟨φ⟩ := hφ
      have := isSimpleGroup_alternatingGroup 5 le_rfl
      exact prodComp_of_mulEquiv_simple hperf φ (three_dvd_card_alternatingGroup 5 (by norm_num))
  ·
    obtain ⟨c', d, L', -, -, -, -, -, -, -, hcases⟩ := h3
    rcases hcases with hON | hCP | hA6A5 | hφ | hφ | ⟨h7', hφ⟩
    · have := CFSG.Sporadic.ON.fam_on_simplicity.1
      have := CFSG.Sporadic.ON.fam_on_simplicity.2.2
      exact prodComp_of_isTripleCover hperf hON (by rw [CFSG.Sporadic.ON.card_ON]; norm_num)
    · obtain ⟨U, V, hU, hV, hsup, hcomm, -, hU6, hV6⟩ := hCP
      exact ProdComp.of_central hperf hsup hcomm
        (good3_alternatingGroup_six.of_isTripleCover hU6)
        (good3_alternatingGroup_six.of_isTripleCover hV6)
    · obtain ⟨U, V, hU, hV, hUV, hsup, hU6, ⟨eV⟩⟩ := hA6A5
      have hcomm : ⁅U, V⁆ = ⊥ := le_bot_iff.mp (hUV ▸ Subgroup.commutator_le_inf U V)
      exact ProdComp.of_central hperf hsup hcomm
        (good3_alternatingGroup_six.of_isTripleCover hU6)
        (good3_alternatingGroup_five.of_mulEquiv eV.symm).quot_center
    · obtain ⟨φ⟩ := hφ
      exact ProdComp.of_mulEquiv φ.symm
        (ProdComp.prod good3_alternatingGroup_five good3_alternatingGroup_five)
    · obtain ⟨φ⟩ := hφ
      have := isSimpleGroup_alternatingGroup 7 (by norm_num)
      exact prodComp_of_mulEquiv_simple hperf φ (three_dvd_card_alternatingGroup 7 (by norm_num))
    · obtain ⟨φ⟩ := hφ
      have := Sec19.Step1914TriProof.isSimpleGroup_projSL_three_of_field (GaloisField 7 1)
      have : IsSimpleGroup ↥(img148 A Y (deltaZero A (lB A) Y)) := φ.isSimpleGroup
      exact prodComp_of_mulEquiv_simple hperf (MulEquiv.refl _)
        (KFacts.three_dvd_card_of_mulEquiv_projSL φ)
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h4
    have := isSimpleGroup_alternatingGroup 10 (by norm_num)
    exact prodComp_of_mulEquiv_simple hperf φ (three_dvd_card_alternatingGroup 10 (by norm_num))
  ·
    obtain ⟨c', -, L', n, m, -, -, hn, -, hiso, -⟩ := h5
    have : Group.IsPerfect ↥(img148 A Y (deltaZero A (lB A) Y)) := hperf
    have := (Sec19.Step1914TriProof.isSimpleGroup_of_isoLThreePi (by omega : 1 ≤ 3 * n) hiso).1
    exact prodComp_of_mulEquiv_simple hperf (MulEquiv.refl _)
      (Main148.three_dvd_card_of_isoLThreePi148 (by omega) hiso)
  ·
    obtain ⟨⟨φ⟩, -, -⟩ := h6
    have := CFSG.Sporadic.J2.isSimpleGroup_J2
    have : Group.IsPerfect ↥(img148 A Y (deltaZero A (lB A) Y)) := hperf
    have hJ2p : Group.IsPerfect CFSG.Blueprint.NativeSporadic.J2 :=
      Group.IsPerfect.ofSurjective (f := (MonoidHom.snd _ _).comp φ.toMonoidHom)
        (Prod.snd_surjective.comp φ.surjective)
    have : Nontrivial CFSG.Blueprint.NativeSporadic.J2 := IsSimpleGroup.toNontrivial
    exact ProdComp.of_mulEquiv φ.symm (ProdComp.prod good3_alternatingGroup_five
      (good3_of_isSimpleGroup (exists_ne_comm_of_isPerfect hJ2p)
        (by rw [KFacts.KS14.card_nativeJ2]; norm_num)))
  ·
    obtain ⟨a₁, a₂, L₁, L₂, J₁, J₂, p₁, f₁, e₁, p₂, f₂, e₂, hp₁, hp₂, -, -, -, -, hJ₁, hJ₂,
      hsup, hinf, hcomm, -, -, -, -, hZ₁, hZ₂, -, -⟩ := h7
    have hB : IsMulCommutative ↥(img148 A Y A) := ⟨⟨img148_comm hAab⟩⟩
    have hAD : A ≤ Subgroup.normalizer ((deltaZero A (lB A) Y : Subgroup G) : Set G) :=
      le_normalizer_sSup fun _ hQ => hQ.1.1.1.2.2
    have hBX := Sec14.img148_le_normalizer (A := A) (Y := Y) hAD
    rw [Sec14.img148_sup ((hJ₁.trans inf_le_right).trans le_sup_left) le_sup_right] at hZ₁
    rw [Sec14.img148_sup ((hJ₂.trans inf_le_right).trans le_sup_left) le_sup_right] at hZ₂
    exact prodComp_case7 hperf hsup hinf hcomm hB hBX hZ₁ hZ₂

theorem read148_of_item148
    {A L : Subgroup G} {c : G}
    (h : Sec14Std G A c L) (h148 : Item148 A (lB A)) {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hperf : Group.IsPerfect ↥(((deltaZero A (lB A) Y).subgroupOf Y).map
      (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥Y)))) :
    Read148 A (lB A) Y := by
  let := ker148_normal hY.2
  by_cases h1 : deltaZero A (lB A) Y ≤ pPrimeCoreOf 3 Y
  · refine ⟨⊥, ⊥, Or.inl rfl, Or.inl rfl, ?_⟩
    rw [sup_bot_eq, le_bot_iff, Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk']
    intro x hx
    obtain ⟨z, hz, hzx⟩ := h1 (Subgroup.mem_subgroupOf.mp hx)
    have : z = x := Subtype.ext hzx
    exact this ▸ hz
  · obtain ⟨e₀⟩ := nonempty_img148_equiv_map hY.2 (deltaZero_le Y)
    have hXp : Group.IsPerfect ↥(img148 A Y (deltaZero A (lB A) Y)) :=
      Group.IsPerfect.ofSurjective (f := e₀.symm.toMonoidHom) e₀.symm.surjective
    have hPC := (prodComp_img148 h h148 hY hXp h1).of_mulEquiv e₀
    exact hPC.read (h148 Y hY).1.isSubnormal

theorem read148R_of_item148R
    (h148 : Item148R)
    (hperf : Read148PerfR) : Read148R :=
  fun G _ _ A c L h Y hY => read148_of_item148 h.toSec14Std (h148 G A c L h) hY
    (hperf G A c L h Y hY)

theorem y4CoreReadR_of_item148R
    (hSz : KFacts.KPSz)
    (hbot : Item145BotS14) (h148 : Item148R) (hperf : Read148PerfR) : Y4CoreReadR :=
  y4CoreReadR_of_read148R hSz hbot (read148R_of_item148R h148 hperf)

end Cases

end Y4Core

end CFSG.RankThree.PartTwo.Sec15

module

public import CFSG.RankThree.PartTwo.Sec19.Item1923Defs
import CFSG.RankThree.PartTwo.Sec18.SylowPlane
import CFSG.RankThree.PartTwo.Sec18.Item185Count
import CFSG.RankThree.PartTwo.Sec20.Item20Res8ProofAutQ8
import CFSG.RankThree.PartTwo.Sec20.Item203OneProof
import CFSG.RankThree.PartTwo.Sec20.OneBasics
import CFSG.RankThree.PartTwo.Sec4.Item423Res4ProofHeis
import CFSG.RankThree.PartTwo.Sec13.Item132
import CFSG.RankThree.PartTwo.Sec13.Item133Mono
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Basic
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Frattini
import CFSG.RankThree.PartTwo.Sec19.Hyp1921Quot
import CFSG.RankThree.PartTwo.KFacts.L34Automizer
import CFSG.RankThree.PartTwo.KFacts.L34Sections
import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
public import CFSG.LocalAnalysis.AGLEmbedding.Extremal
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.RankThree.PartOne.KC.LinearSubfieldPointwise
public import CFSG.RankThree.PartTwo.Sec18.SylowWStar
public import CFSG.RankThree.PartTwo.Sec19.Item194Five
public import CFSG.RankThree.PartTwo.Sec19.Item194Used
public import CFSG.RankThree.PartTwo.Sec20.Alt20
public import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofNormal
public import CFSG.RankThree.PartTwo.Sec20.OneSteps
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import Certificates.Certificate43
import CFSG.Milestones.CL_LIT_Gorenstein_Walter_L_balance
import CFSG.RankThree.PartTwo.Sec11.Item118
import CFSG.RankThree.PartTwo.Sec11.Theorem1134
import CFSG.RankThree.PartTwo.Sec21.Item211ProofListOf
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
import CFSG.RankThree.PartTwo.Sec6.Item612

public section

namespace CFSG.RankThree.PartTwo.Late

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.Assembly.RankThreeEven (projSL)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec19 (starIm IsList194 IsSmall194 IsTripleA6 IsProperParabolic
  Item194UsedWide3 Item316)

variable {G : Type} [Group G] [Finite G] {A M N L K : Subgroup G} {c : G}

private theorem mem_planeGroup_iff {x : G} :
    x ∈ planeGroup A L c ↔ x ∈ L ∧ x ∈ Subgroup.normalizer ((A ⊓ L : Subgroup G) : Set G) ∧
      x * c = c * x := by
  simp only [planeGroup, Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff, and_assoc]

private theorem autIn_planeGroup_eq :
    Sec4.autIn (planeGroup A L c) (A ⊓ L) =
      Sec4.autIn (L ⊓ Subgroup.centralizer ({c} : Set G)) (A ⊓ L) := by
  ext σ
  rw [Sec4.mem_autIn_iff, Sec4.mem_autIn_iff]
  constructor
  · rintro ⟨x, hxN, hxW, rfl⟩
    obtain ⟨hxL, -, hxc⟩ := mem_planeGroup_iff.mp hxW
    exact ⟨x, hxN, ⟨hxL, Subgroup.mem_centralizer_singleton_iff.mpr hxc⟩, rfl⟩
  · rintro ⟨x, hxN, hxW, rfl⟩
    exact ⟨x, hxN, mem_planeGroup_iff.mpr
      ⟨hxW.1, hxN, Subgroup.mem_centralizer_singleton_iff.mp hxW.2⟩, rfl⟩

private theorem autIn_le_autIn_planeGroup (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) :
    Sec4.autIn L (A ⊓ L) ≤ Sec4.autIn (planeGroup A L c) (A ⊓ L) := by
  have hc : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    rw [hF.centralizer_eq]
    exact Subgroup.mem_zpowers c
  have hc' : c ∈ A ∧ ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L := hc
  have hc3 : c ^ 3 = 1 := by
    have h3 := pow_orderOf_eq_one c
    rwa [hF.orderOf_c] at h3
  have hcL : c ∈ Subgroup.normalizer (L : Set G) := hF.normal (h.le_N hc'.1)
  have hcB : ∀ b ∈ A ⊓ L, c * b = b * c := fun b hb =>
    congrArg Subtype.val (h.isE27.1.1.is_comm.comm ⟨c, hc'.1⟩ ⟨b, hb.1⟩)
  rw [autIn_planeGroup_eq]
  exact Sec20.Res8.autIn_le_autIn_inf_centralizer hc3 hcL hcB hc'.2

private theorem exists_quaternion_autIn_planeGroup (h : Hyp1921 G A M N L)
    (hF : Facts1922 G A M N L c) :
    ∃ f : QuaternionGroup 2 →* Sec4.autIn (planeGroup A L c) (A ⊓ L), Function.Injective f := by
  obtain ⟨e⟩ := h.quotient_iso
  obtain ⟨f₀, hf₀⟩ := Sec18.exists_quaternion_autIn e (inf_le_right : A ⊓ L ≤ L)
    (h.isE27.isPGroup.to_le inf_le_left) hF.card
  have hle := autIn_le_autIn_planeGroup h hF
  exact ⟨(Subgroup.inclusion hle).comp f₀, (Subgroup.inclusion_injective hle).comp hf₀⟩

private theorem card_autIn_le_eight {X B : Subgroup G}
    (e : X ⧸ CFSG.pCore 2 X ≃* projSL 3 (GaloisField 2 2)) (hBX : B ≤ X) (hB3 : IsPGroup 3 B)
    (hB9 : Nat.card B = 9) : Nat.card (Sec4.autIn X B) ≤ 8 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set π := QuotientGroup.mk' (CFSG.pCore 2 ↥X) with hπ
  have hB3' : IsPGroup 3 (B.subgroupOf X) := hB3.comap_subtype
  have hinj : Function.Injective (π.comp (B.subgroupOf X).subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro x hx
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, hπ, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hx
    have h1 : (x : ↥X) ∈ B.subgroupOf X ⊓ CFSG.pCore 2 ↥X := ⟨x.2, hx⟩
    have hbot : B.subgroupOf X ⊓ CFSG.pCore 2 ↥X = ⊥ :=
      Subgroup.eq_bot_of_card_eq _ (Sec20.card_inf_eq_one_of_isPGroup hB3' CFSG.pCore_isPGroup)
    rw [hbot, Subgroup.mem_bot] at h1
    exact Subgroup.mem_bot.mpr (Subtype.ext h1)
  set Bb := (B.subgroupOf X).map π with hBb
  set β := Sec20.quotientRestrictEquiv hBX hinj with hβ
  have hBb9 : Nat.card Bb = 9 := by
    rw [← Nat.card_congr β.toEquiv, hB9]
  set e' := e.trans (KFacts.L34.projSLEquivProjectiveSL 3 (GaloisField 2 2)) with he'
  have hBb' : Nat.card (Bb.map e'.toMonoidHom) = 9 := by
    rw [Subgroup.card_map_of_injective (f := e'.toMonoidHom) e'.injective, hBb9]
  obtain ⟨q⟩ := KFacts.L34.nonempty_automizer_of_card_eq_nine
    KFacts.L34.card_galoisField_two_two hBb'
  let qB : Sec4.autIn ⊤ Bb ≃* QuaternionGroup 2 :=
    (KFacts.L34.automizerEquivAutIn Bb).symm.trans
      ((CFSG.RankThree.Asc83Table.automizerCongr e' Bb).trans q)
  have hcardBb : Nat.card (Sec4.autIn ⊤ Bb) = 8 := by
    rw [Nat.card_congr qB.toEquiv, Nat.card_eq_fintype_card, QuaternionGroup.card]
  have hle : Sec4.autIn X B ≤ (Sec4.autIn ⊤ Bb).map (MulAut.congr β.symm).toMonoidHom := by
    intro σ hσ
    obtain ⟨x, hxN, hxX, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    have hzN : π ⟨x, hxX⟩ ∈ Subgroup.normalizer (Bb : Set (↥X ⧸ CFSG.pCore 2 ↥X)) := by
      refine Subgroup.mem_normalizer_fintype fun y hy => ?_
      obtain ⟨b, hb, rfl⟩ := hy
      refine ⟨⟨x, hxX⟩ * b * ⟨x, hxX⟩⁻¹, ?_, by simp only [map_mul, map_inv]⟩
      have hb' : (b : G) ∈ B := Subgroup.mem_subgroupOf.mp hb
      have hxb := (Subgroup.mem_normalizer_iff.mp hxN (b : G)).mp hb'
      exact Subgroup.mem_subgroupOf.mpr (by simpa using hxb)
    refine ⟨Bb.normalizerMonoidHom ⟨π ⟨x, hxX⟩, hzN⟩,
      Sec4.mem_autIn_iff.mpr ⟨π ⟨x, hxX⟩, hzN, Subgroup.mem_top _, rfl⟩, ?_⟩
    symm
    apply MulEquiv.ext
    intro w
    apply β.injective
    rw [MulEquiv.coe_toMonoidHom, MulAut.congr_apply, MulEquiv.symm_symm, MulEquiv.trans_apply,
      MulEquiv.trans_apply, MulEquiv.apply_symm_apply]
    apply Subtype.ext
    rw [Sec4.normalizerMonoidHom_apply_coe, Sec20.quotientRestrictEquiv_apply,
      Sec20.quotientRestrictEquiv_apply]
    have hval : (⟨((B.normalizerMonoidHom ⟨x, hxN⟩ w : B) : G),
        hBX (B.normalizerMonoidHom ⟨x, hxN⟩ w).2⟩ : ↥X) =
        (⟨x, hxX⟩ : ↥X) * ⟨w, hBX w.2⟩ * (⟨x, hxX⟩ : ↥X)⁻¹ := by
      apply Subtype.ext
      rw [Sec4.normalizerMonoidHom_apply_coe]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    rw [hval, map_mul, map_mul, map_inv]
  calc Nat.card (Sec4.autIn X B)
      ≤ Nat.card ((Sec4.autIn ⊤ Bb).map (MulAut.congr β.symm).toMonoidHom) :=
        Subgroup.card_le_of_le hle
    _ = Nat.card (Sec4.autIn ⊤ Bb) :=
        Subgroup.card_map_of_injective (MulAut.congr β.symm).injective
    _ = 8 := hcardBb

theorem step1923_W (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) :
    Sec18.PlaneQ8 A (A ⊓ L) (planeGroup A L c) c := by
  set B : Subgroup G := A ⊓ L with hB
  set W : Subgroup G := planeGroup A L c with hW
  have hA := h.isE27
  have hc : c ∈ sectionCentralizer A L (CFSG.Open.pCoreOf 2 L) := by
    rw [hF.centralizer_eq]
    exact Subgroup.mem_zpowers c
  have hc' : c ∈ A ∧ ∀ x ∈ L, c * x * c⁻¹ * x⁻¹ ∈ CFSG.Open.pCoreOf 2 L := hc
  have hc1 : c ≠ 1 := by
    intro e
    have h3 := hF.orderOf_c
    rw [e, orderOf_one] at h3
    omega
  have hcL : c ∉ L := h.not_mem_of_mem_sectionCentralizer_of
    (fun _ hx hx' => h.mem_pCoreOf_of_commutator_mem hx hx') hc hc1
  have hcB : c ∉ B := fun hb => hcL hb.2
  have hB9 : Nat.card B = 9 := hF.card
  have hBe : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_of_le hA.1 inf_le_left
  have hcomm : ∀ b ∈ B, c * b = b * c := fun b hb =>
    congrArg Subtype.val (hA.1.1.is_comm.comm ⟨c, hc'.1⟩ ⟨b, hb.1⟩)
  have hWL : W ≤ L := fun x hx => (mem_planeGroup_iff.mp hx).1
  have hWB : W ≤ Subgroup.normalizer (B : Set G) := fun x hx => (mem_planeGroup_iff.mp hx).2.1
  have hWc : ∀ k ∈ W, k * c = c * k := fun k hk => (mem_planeGroup_iff.mp hk).2.2
  have hBW : B ≤ W := fun b hb =>
    mem_planeGroup_iff.mpr ⟨hb.2, Subgroup.le_normalizer hb, (hcomm b hb).symm⟩
  have hWA : W ≤ Subgroup.normalizer (A : Set G) := by
    intro x hx
    obtain ⟨-, hxN, hxc⟩ := mem_planeGroup_iff.mp hx
    have hx' := Sec18.mem_normalizer_zpowers_sup hxc hxN
    rwa [← hF.eq_sup] at hx'
  have hAW : A ⊓ W = B := by
    apply le_antisymm
    · intro x hx
      exact ⟨hx.1, hWL hx.2⟩
    · intro x hx
      exact ⟨hx.1, hBW hx⟩
  have hcW : c ∈ Subgroup.centralizer (W : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun k hk => hWc k hk
  obtain ⟨fB, hfBi⟩ := exists_quaternion_autIn_planeGroup h hF
  have hρ4 : ((fB (QuaternionGroup.a 1) : Sec4.autIn W B) : MulAut B) ^ 4 = 1 := by
    rw [← Subgroup.coe_pow, ← map_pow,
      show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 4 = 1 by decide, map_one, Subgroup.coe_one]
  have hρ2 : ((fB (QuaternionGroup.a 1) : Sec4.autIn W B) : MulAut B) ^ 2 ≠ 1 := by
    intro h2
    have h2' : fB (QuaternionGroup.a 1 ^ 2) = fB 1 := by
      rw [map_pow, map_one]
      exact Subtype.ext (by rw [Subgroup.coe_pow, h2, Subgroup.coe_one])
    exact (show (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 by decide) (hfBi h2')
  have hirr : Sec21.IsIrreducibleOn (Sec4.autIn W B) :=
    Sec13.isIrreducibleOn_of_order_four hBe hB9 (fB _).2 hρ4 hρ2
  obtain ⟨φ⟩ : Nonempty (Sec4.autIn W A ≃* Sec4.autIn W B) := by
    have hAeq' : A = A ⊓ W ⊔ Subgroup.zpowers c := by
      rw [hAW, sup_comm]
      exact hF.eq_sup
    have h' := Sec4.Res423Four.nonempty_autIn_inf_equiv hcW hAeq'
    rwa [hAW] at h'
  exact ⟨hA.1, hA.2, hc'.1, hF.eq_sup, hcB, hB9, hWc, hirr, hWA, hWB,
    ⟨φ.symm.toMonoidHom.comp fB, φ.symm.injective.comp hfBi⟩⟩

theorem step1923_W_le (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) :
    planeGroup A L c ≤ N ⊓ M ⊓ Subgroup.normalizer (A : Set G) := by
  intro x hx
  obtain ⟨hxL, hxN, hxc⟩ := mem_planeGroup_iff.mp hx
  have hxA : x ∈ Subgroup.normalizer (A : Set G) := by
    have hx' := Sec18.mem_normalizer_zpowers_sup hxc hxN
    rwa [← hF.eq_sup] at hx'
  exact ⟨⟨h.L_le_N hxL, hF.normalizer_le_M hxN⟩, hxA⟩

theorem step1923_card_autIn_W (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c) :
    Nat.card (Sec4.autIn (planeGroup A L c) (A ⊓ L)) = 8 := by
  obtain ⟨e⟩ := h.quotient_iso
  have hWL : planeGroup A L c ≤ L := fun x hx => (mem_planeGroup_iff.mp hx).1
  have hq : Nat.card (QuaternionGroup 2) = 8 := by
    rw [Nat.card_eq_fintype_card, QuaternionGroup.card]
  refine le_antisymm ?_ ?_
  · calc Nat.card (Sec4.autIn (planeGroup A L c) (A ⊓ L))
        ≤ Nat.card (Sec4.autIn L (A ⊓ L)) := Subgroup.card_le_of_le (Sec13.autIn_mono hWL)
      _ ≤ 8 := card_autIn_le_eight e (inf_le_right : A ⊓ L ≤ L)
        (h.isE27.isPGroup.to_le inf_le_left) hF.card
  · obtain ⟨f, hf⟩ := exists_quaternion_autIn_planeGroup h hF
    calc 8 = Nat.card (QuaternionGroup 2) := hq.symm
      _ ≤ Nat.card (Sec4.autIn (planeGroup A L c) (A ⊓ L)) :=
        Nat.card_le_card_of_injective f hf

private theorem plane_map_conj_mul (K : Subgroup G) (a b : G) :
    K.map (MulAut.conj (a * b)).toMonoidHom =
      (K.map (MulAut.conj b).toMonoidHom).map (MulAut.conj a).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

private theorem plane_map_conj_eq_iff_mem (K : Subgroup G) (a b : G) :
    K.map (MulAut.conj b).toMonoidHom = K.map (MulAut.conj a).toMonoidHom ↔
      a⁻¹ * b ∈ Subgroup.normalizer (K : Set G) := by
  have key := plane_map_conj_mul K a (a⁻¹ * b)
  rw [mul_inv_cancel_left] at key
  have hinj : Function.Injective (MulAut.conj a).toMonoidHom :=
    fun x y h => (MulAut.conj a).injective h
  rw [key, (Subgroup.map_injective hinj).eq_iff]
  constructor
  · intro h
    exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr h
  · intro h
    exact map_conj_eq_of_mem_normalizer h

private theorem plane_index_inf_normalizer_le {M K U : Subgroup G} (hUM : U ≤ M) :
    ((U ⊓ Subgroup.normalizer (K : Set G)).subgroupOf U).index ≤
      {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom}.ncard := by
  have hmem : ∀ a b : U, a⁻¹ * b ∈ (U ⊓ Subgroup.normalizer (K : Set G)).subgroupOf U ↔
      (a : G)⁻¹ * (b : G) ∈ Subgroup.normalizer (K : Set G) := by
    intro a b
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf]
    exact ⟨fun h => h.2, fun h => ⟨U.mul_mem (U.inv_mem a.2) b.2, h⟩⟩
  let f : U → {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom} :=
    fun u => ⟨K.map (MulAut.conj (u : G)).toMonoidHom, (u : G), hUM u.2, rfl⟩
  have hf : ∀ a b : U, a⁻¹ * b ∈ (U ⊓ Subgroup.normalizer (K : Set G)).subgroupOf U →
      f a = f b := by
    intro a b hab
    exact Subtype.ext ((plane_map_conj_eq_iff_mem K (a : G) (b : G)).mpr ((hmem a b).mp hab)).symm
  let F : U ⧸ (U ⊓ Subgroup.normalizer (K : Set G)).subgroupOf U →
      {K' : Subgroup G | ∃ g ∈ M, K' = K.map (MulAut.conj g).toMonoidHom} :=
    Quotient.lift f (fun a b hab => hf a b (QuotientGroup.leftRel_apply.mp hab))
  have hF : Function.Injective F := by
    rintro x y hxy
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective x
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective y
    have h1 : K.map (MulAut.conj (a : G)).toMonoidHom =
        K.map (MulAut.conj (b : G)).toMonoidHom :=
      congrArg Subtype.val hxy
    exact QuotientGroup.eq.mpr
      ((hmem a b).mpr ((plane_map_conj_eq_iff_mem K (a : G) (b : G)).mp h1.symm))
  rw [Subgroup.index, ← Nat.card_coe_set_eq]
  exact Nat.card_le_card_of_injective F hF

private theorem plane_three_le_index {Γ : Type} [Group Γ] [Finite Γ] {S : Subgroup Γ}
    {a b d : Γ} (hab : a⁻¹ * b ∉ S) (had : a⁻¹ * d ∉ S) (hbd : b⁻¹ * d ∉ S) : 3 ≤ S.index := by
  let F : Fin 3 → Γ ⧸ S := ![(a : Γ ⧸ S), (b : Γ ⧸ S), (d : Γ ⧸ S)]
  have hF : Function.Injective F := by
    intro i j hij
    fin_cases i <;> fin_cases j
    · rfl
    · exact absurd (QuotientGroup.eq.mp hij) hab
    · exact absurd (QuotientGroup.eq.mp hij) had
    · exact absurd (QuotientGroup.eq.mp hij.symm) hab
    · rfl
    · exact absurd (QuotientGroup.eq.mp hij) hbd
    · exact absurd (QuotientGroup.eq.mp hij.symm) had
    · exact absurd (QuotientGroup.eq.mp hij.symm) hbd
    · rfl
  have h := Nat.card_le_card_of_injective F hF
  simpa [Subgroup.index] using h

private theorem plane_dichotomy {Kc R : Subgroup G} (hR : (R.subgroupOf Kc).index ≤ 2)
    {k₀ k : G} (hk₀ : k₀ ∈ Kc) (hk : k ∈ Kc) (hk₀R : k₀ ∉ R) : k ∈ R ∨ k₀⁻¹ * k ∈ R := by
  by_contra hcon
  rw [not_or] at hcon
  obtain ⟨hkR, hk₀kR⟩ := hcon
  have h3 : 3 ≤ (R.subgroupOf Kc).index :=
    plane_three_le_index (a := (1 : Kc)) (b := ⟨k₀, hk₀⟩) (d := ⟨k, hk⟩)
      (by simpa [Subgroup.mem_subgroupOf] using hk₀R)
      (by simpa [Subgroup.mem_subgroupOf] using hkR)
      (by simpa [Subgroup.mem_subgroupOf] using hk₀kR)
  omega

private theorem plane_quaternion_exists {Γ : Type} [Group Γ] {Φ ΦR : Subgroup Γ}
    (g : QuaternionGroup 2 →* Γ) (hg : Function.Injective g) (hΦ : ∀ x, g x ∈ Φ)
    (hdich : ∀ σ ∈ Φ, ∀ τ ∈ Φ, σ ∉ ΦR → τ ∈ ΦR ∨ σ⁻¹ * τ ∈ ΦR) :
    ∃ x : QuaternionGroup 2, g x ∈ ΦR ∧ g x ^ 2 ≠ 1 := by
  by_contra hcon
  have hcon' : ∀ x : QuaternionGroup 2, g x ∈ ΦR → g x ^ 2 = 1 := fun x hx => by
    by_contra hne
    exact hcon ⟨x, hx, hne⟩
  have hsq : ∀ x : QuaternionGroup 2, x ^ 2 ≠ 1 → g x ^ 2 ≠ 1 := by
    intro x hx h
    apply hx
    apply hg
    rw [map_pow, h, map_one]
  have hi2 : (QuaternionGroup.a 1 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
  have hj2 : (QuaternionGroup.xa 0 : QuaternionGroup 2) ^ 2 ≠ 1 := by decide
  have hij2 : ((QuaternionGroup.a 1 : QuaternionGroup 2) * QuaternionGroup.xa 0) ^ 2 ≠ 1 := by
    decide
  have hgi : g (QuaternionGroup.a 1) ∉ ΦR := fun h => hsq _ hi2 (hcon' _ h)
  have hgj : g (QuaternionGroup.xa 0) ∉ ΦR := fun h => hsq _ hj2 (hcon' _ h)
  have hgij : g (QuaternionGroup.a 1 * QuaternionGroup.xa 0) ∉ ΦR :=
    fun h => hsq _ hij2 (hcon' _ h)
  have hr : (g (QuaternionGroup.a 1))⁻¹ * g (QuaternionGroup.xa 0) ∈ ΦR := by
    rcases hdich _ (hΦ (QuaternionGroup.a 1)) _ (hΦ (QuaternionGroup.xa 0)) hgi with h | h
    · exact absurd h hgj
    · exact h
  have hii : g (QuaternionGroup.a 1) * g (QuaternionGroup.a 1) ∈ ΦR := by
    rcases hdich _ (hΦ (QuaternionGroup.a 1)) _
        (Φ.mul_mem (hΦ (QuaternionGroup.a 1)) (hΦ (QuaternionGroup.a 1))) hgi with h | h
    · exact h
    · rw [inv_mul_cancel_left] at h
      exact absurd h hgi
  have hprod : g (QuaternionGroup.a 1 * QuaternionGroup.xa 0) ∈ ΦR := by
    rw [map_mul]
    have e : g (QuaternionGroup.a 1) * g (QuaternionGroup.xa 0) =
        (g (QuaternionGroup.a 1) * g (QuaternionGroup.a 1)) *
          ((g (QuaternionGroup.a 1))⁻¹ * g (QuaternionGroup.xa 0)) := by group
    rw [e]
    exact ΦR.mul_mem hii hr
  exact hgij hprod

private theorem plane_pow_apply {X : Subgroup G} {k : G}
    (hN : k ∈ Subgroup.normalizer (X : Set G)) (n : ℕ) (x : X) :
    ((X.normalizerMonoidHom ⟨k, hN⟩ ^ n) x : G) = k ^ n * x * (k ^ n)⁻¹ := by
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', MulAut.mul_apply, Sec4.normalizerMonoidHom_apply_coe, ih]
    group

private theorem plane_pow_eq_one_iff {X : Subgroup G} {k : G}
    (hN : k ∈ Subgroup.normalizer (X : Set G)) (n : ℕ) :
    X.normalizerMonoidHom ⟨k, hN⟩ ^ n = 1 ↔ ∀ x : X, k ^ n * x * (k ^ n)⁻¹ = x := by
  constructor
  · intro h x
    have hx := plane_pow_apply hN n x
    rw [h, MulAut.one_apply] at hx
    exact hx.symm
  · intro h
    apply MulEquiv.ext
    intro y
    apply Subtype.ext
    rw [plane_pow_apply hN n y, MulAut.one_apply]
    exact h y

theorem step1923_irreducible (h : Hyp1921 G A M N L) (hF : Facts1922 G A M N L c)
    (hK : K ∈ oTwoComponentsIn M) :
    Sec21.IsIrreducibleOn
      (Sec4.autIn (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)) (A ⊓ L)) ∧
    (planeGroup A L c ⊓ Subgroup.normalizer (K : Set G)).relIndex (planeGroup A L c) ≤ 2 := by
  have hP := step1923_W h hF
  set Kc : Subgroup G := planeGroup A L c with hKc
  set B : Subgroup G := A ⊓ L with hB
  set R : Subgroup G := Kc ⊓ Subgroup.normalizer (K : Set G) with hR
  have hBA : B ≤ A := inf_le_left
  have hKcM : Kc ≤ M := fun x hx => (step1923_W_le h hF hx).1.2
  have hidx : (R.subgroupOf Kc).index ≤ 2 :=
    (plane_index_inf_normalizer_le (K := K) hKcM).trans
      (Sec18.Item185Proof.ncard_conj_le_two h.toSec18Std hK)
  refine ⟨?_, hidx⟩
  have hBab : CFSG.Assembly.IsElemAbelian 3 B := isElemAbelian_of_le hP.isElemAbelian inf_le_left
  have hB9 : Nat.card B = 9 := hP.card_plane
  obtain ⟨f, hf⟩ := hP.quaternion
  set g : QuaternionGroup 2 →* MulAut A := (Sec4.autIn Kc A).subtype.comp f with hg
  have hΦ : ∀ y, g y ∈ Sec4.autIn Kc A := fun y => (f y).2
  have hginj : Function.Injective g := Subtype.val_injective.comp hf
  have hdich : ∀ σ ∈ Sec4.autIn Kc A, ∀ τ ∈ Sec4.autIn Kc A, σ ∉ Sec4.autIn R A →
      τ ∈ Sec4.autIn R A ∨ σ⁻¹ * τ ∈ Sec4.autIn R A := by
    intro σ hσ τ hτ hσR
    obtain ⟨k₀, hk₀N, hk₀Kc, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    obtain ⟨k, hkN, hkKc, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
    have hk₀R : k₀ ∉ R := fun hr => hσR (Sec4.mem_autIn_iff.mpr ⟨k₀, hk₀N, hr, rfl⟩)
    rcases plane_dichotomy hidx hk₀Kc hkKc hk₀R with hr | hr
    · exact Or.inl (Sec4.mem_autIn_iff.mpr ⟨k, hkN, hr, rfl⟩)
    · refine Or.inr (Sec4.mem_autIn_iff.mpr ⟨k₀⁻¹ * k, ?_, hr, ?_⟩)
      · exact (Subgroup.normalizer (A : Set G)).mul_mem
          ((Subgroup.normalizer (A : Set G)).inv_mem hk₀N) hkN
      · rw [← map_inv, ← map_mul]
        rfl
  obtain ⟨x, hxR, hx2⟩ := plane_quaternion_exists g hginj hΦ hdich
  have hx4all : ∀ y : QuaternionGroup 2, y ^ 4 = 1 := by decide
  have h4x : g x ^ 4 = 1 := by rw [← map_pow, hx4all x, map_one]
  obtain ⟨r, hrN, hrR, hrx⟩ := Sec4.mem_autIn_iff.mp hxR
  have hrKc : r ∈ Kc := (Subgroup.mem_inf.mp hrR).1
  have hrB : r ∈ Subgroup.normalizer (B : Set G) := hP.le_normalizer_plane hrKc
  have hrc : Commute r c := hP.commute r hrKc
  have hcomm2 : Commute (r ^ 2) c := hrc.pow_left 2
  have h4 : (B.normalizerMonoidHom ⟨r, hrB⟩) ^ 4 = 1 := by
    rw [plane_pow_eq_one_iff hrB 4]
    have hA4 : ∀ a : A, r ^ 4 * a * (r ^ 4)⁻¹ = a := by
      rw [← hrx] at h4x
      exact (plane_pow_eq_one_iff hrN 4).mp h4x
    intro b
    exact hA4 ⟨b, hBA b.2⟩
  have h2 : (B.normalizerMonoidHom ⟨r, hrB⟩) ^ 2 ≠ 1 := by
    intro h2eq
    rw [plane_pow_eq_one_iff hrB 2] at h2eq
    have hAZ : A ≤ Subgroup.centralizer ({r ^ 2} : Set G) := by
      rw [hP.eq_sup]
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le, Subgroup.mem_centralizer_iff]
        intro h' hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        exact hcomm2.eq
      · intro b hb
        rw [Subgroup.mem_centralizer_iff]
        intro h' hh
        rw [Set.mem_singleton_iff] at hh
        subst hh
        have hb2 : r ^ 2 * b * (r ^ 2)⁻¹ = b := h2eq ⟨b, hb⟩
        calc r ^ 2 * b = r ^ 2 * b * (r ^ 2)⁻¹ * r ^ 2 := by group
          _ = b * r ^ 2 := by rw [hb2]
    have hA2 : ∀ a : A, r ^ 2 * a * (r ^ 2)⁻¹ = a := by
      intro a
      have h' := Subgroup.mem_centralizer_iff.mp (hAZ a.2) (r ^ 2) (Set.mem_singleton _)
      rw [h', mul_inv_cancel_right]
    apply hx2
    rw [← hrx]
    exact (plane_pow_eq_one_iff hrN 2).mpr hA2
  exact Sec13.isIrreducibleOn_of_order_four hBab hB9
    (show B.normalizerMonoidHom ⟨r, hrB⟩ ∈ Sec4.autIn R B from
      Sec4.mem_autIn_iff.mpr ⟨r, hrB, hrR, rfl⟩) h4 h2

end CFSG.RankThree.PartTwo.Late

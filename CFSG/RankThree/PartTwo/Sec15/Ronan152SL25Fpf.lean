module

import CFSG.RankThree.PartTwo.Sec15.Item152ConfBProofWE
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec13.Ronan138SMain
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.SeitzReduction.EPilotPosition
public import CFSG.RankThree.PartTwo.Sec14.Item143DescProofOne
public import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Conf
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ronan152SL25

section Theta

theorem mem_sectionCentralizer_of_le_centralizer {A : Subgroup G}
    {LB : Subgroup G → Subgroup G} {M X : Subgroup G} (hctx : Ctx152J A LB M X) {p : ℕ}
    {P : Subgroup G} (hP : PData152 A X p P) (hp3 : p ≠ 3) {y : G} (hyA : y ∈ A)
    (hyP : P ≤ Subgroup.centralizer ({y} : Set G)) :
    y ∈ Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) := by
  have : Fact p.Prime := ⟨hP.prime⟩
  set θ := (aschbacherSolvableCore 3 ↥X).map X.subtype with hθ
  have : (aschbacherSolvableCore 3 ↥X).Characteristic :=
    (solvable_prime_complement_core_characterization (H := ↥X) Nat.prime_three).2.1
  have hXθ : X ≤ Subgroup.normalizer (θ : Set G) :=
    Subgroup.le_normalizer.trans
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _)
  have hyθ : y ∈ Subgroup.normalizer (θ : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic _ (hctx.norm_x hyA)
  obtain ⟨hs, h60⟩ := isSimpleGroup_theta_quotJ hctx
  have hOθ : oTwoOddIn X ≤ θ := Proof152F.oTwoOddIn_le_theta hs (by rw [h60]; norm_num)
  have hRθ : (Sec4.oTwoP p ↥X).map X.subtype ≤ θ :=
    Subgroup.map_mono (Proof152F.oTwoP_le_theta hp3 ↥X)
  have hyC : y ∈ Subgroup.centralizer (P : Set G) :=
    Subgroup.mem_centralizer_iff.mpr fun u hu =>
      Subgroup.mem_centralizer_singleton_iff.mp (hyP hu)
  obtain ⟨R, hR, hPR, hPc⟩ := hP.char_p
  obtain ⟨Q, hQ⟩ := Proof152FX.exists_sylow_of_isSylowOf hR
  have hOn : (Sec4.oTwoP p ↥X).Normal := Subgroup.Normal.comap (CFSG.pCore_normal (p := p)) _
  have hF := Sylow.normalizer_sup_eq_top Q
  have hNRP : Subgroup.normalizer (R : Set G) ≤ Subgroup.normalizer (P : Set G) := by
    have h := CFSG.LieType.BorelTits.normalizer_le_normalizer_map_of_characteristic (H := R)
      (P.subgroupOf R)
    rwa [Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hPR] at h
  refine ⟨hyA, fun x hx => ?_⟩
  have hx' : (⟨x, hx⟩ : ↥X) ∈ Subgroup.normalizer
      ((Q : Subgroup ↥(Sec4.oTwoP p ↥X)).map (Sec4.oTwoP p ↥X).subtype : Set ↥X) ⊔
        Sec4.oTwoP p ↥X :=
    hF ▸ Subgroup.mem_top _
  obtain ⟨n, hn, o, ho, hno⟩ := Subgroup.mem_sup_of_normal_right.mp hx'
  have hnR : (n : G) ∈ Subgroup.normalizer (R : Set G) := by
    rw [← hQ]
    exact Subgroup.le_normalizer_map X.subtype ⟨n, hn, rfl⟩
  have hnP : (n : G) ∈ Subgroup.normalizer (P : Set G) := hNRP hnR
  have hxe : x = (n : G) * (o : G) := by
    have h1 : (n : G) * (o : G) = x := by simpa using congrArg Subtype.val hno
    exact h1.symm
  have hc1X : y * (n : G) * y⁻¹ * (n : G)⁻¹ ∈ X :=
    X.mul_mem ((Subgroup.mem_normalizer_iff.mp (hctx.norm_x hyA) _).mp n.2) (X.inv_mem n.2)
  have hnyC : (n : G) * y⁻¹ * (n : G)⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro u hu
    have hv : (n : G)⁻¹ * u * (n : G) ∈ P := by
      have h1 := (Subgroup.mem_normalizer_iff.mp (inv_mem hnP) u).mp hu
      rwa [inv_inv] at h1
    have hc : Commute ((n : G)⁻¹ * u * (n : G)) y⁻¹ :=
      (show Commute ((n : G)⁻¹ * u * (n : G)) y from
        Subgroup.mem_centralizer_singleton_iff.mp (hyP hv)).inv_right
    calc u * ((n : G) * y⁻¹ * (n : G)⁻¹)
        = (n : G) * (((n : G)⁻¹ * u * (n : G)) * y⁻¹) * (n : G)⁻¹ := by group
      _ = (n : G) * (y⁻¹ * ((n : G)⁻¹ * u * (n : G))) * (n : G)⁻¹ := by rw [hc.eq]
      _ = (n : G) * y⁻¹ * (n : G)⁻¹ * u := by group
  have hc1C : y * (n : G) * y⁻¹ * (n : G)⁻¹ ∈ Subgroup.centralizer (P : Set G) := by
    have e : y * (n : G) * y⁻¹ * (n : G)⁻¹ = y * ((n : G) * y⁻¹ * (n : G)⁻¹) := by group
    rw [e]
    exact mul_mem hyC hnyC
  have hc1 : y * (n : G) * y⁻¹ * (n : G)⁻¹ ∈ θ := hOθ (hP.cent_p ⟨hc1X, hc1C⟩)
  have hoθ : (o : G) ∈ θ := hRθ ⟨o, ho, rfl⟩
  have hc2 : y * (o : G) * y⁻¹ * (o : G)⁻¹ ∈ θ :=
    θ.mul_mem ((Subgroup.mem_normalizer_iff.mp hyθ _).mp hoθ) (θ.inv_mem hoθ)
  have hc2' : (n : G) * (y * (o : G) * y⁻¹ * (o : G)⁻¹) * (n : G)⁻¹ ∈ θ :=
    (Subgroup.mem_normalizer_iff.mp (hXθ n.2) _).mp hc2
  have e : y * x * y⁻¹ * x⁻¹ = (y * (n : G) * y⁻¹ * (n : G)⁻¹) *
      ((n : G) * (y * (o : G) * y⁻¹ * (o : G)⁻¹) * (n : G)⁻¹) := by
    rw [hxe]
    group
  rw [e]
  exact θ.mul_mem hc1 hc2'

theorem mem_of_le_centralizer {A : Subgroup G} {LB : Subgroup G → Subgroup G} {M X : Subgroup G}
    (hctx : Ctx152J A LB M X) {B : Subgroup G}
    (hcent : Late.sectionCentralizer A X ((aschbacherSolvableCore 3 ↥X).map X.subtype) =
      (B : Set G))
    {p : ℕ} {P : Subgroup G} (hP : PData152 A X p P) (hp3 : p ≠ 3) {y : G} (hyA : y ∈ A)
    (hyP : P ≤ Subgroup.centralizer ({y} : Set G)) : y ∈ B := by
  have h := mem_sectionCentralizer_of_le_centralizer hctx hP hp3 hyA hyP
  rw [hcent] at h
  exact h

end Theta

theorem exists_mem_oThreeWPre {A : Subgroup G} {τ : MulAut ↥A} (hτ : τ ∈ oThreeWStar A) :
    ∃ (π : G) (hπ : π ∈ Subgroup.normalizer (A : Set G)), π ∈ oThreeWPre A ∧
      A.normalizerMonoidHom ⟨π, hπ⟩ = τ := by
  have hτW : τ ∈ Sec4.autIn ⊤ A := Subgroup.map_subtype_le _ hτ
  obtain ⟨π, hπ, -, hπτ⟩ := Sec4.mem_autIn_iff.mp hτW
  refine ⟨π, hπ, ⟨⟨π, hπ⟩, ?_, rfl⟩, hπτ⟩
  show A.normalizerMonoidHom ⟨π, hπ⟩ ∈ oThreeWStar A
  rw [hπτ]
  exact hτ

theorem exists_fix_of_ncard_lt {A : Subgroup G} (hA : Late.IsE27 A) {d x : G} (hdA : d ∈ A)
    (hxA : x ∈ A)
    (hWd : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hPi : CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A)) (hPi9 : Nat.card (oThreeWStar A) = 9)
    {Ω : Set (Subgroup G)} (hΩ : Ω.ncard < 9)
    (horb : orbitIn (oThreeWPre A) (Subgroup.zpowers x) ⊆ Ω) :
    ∃ σ ∈ oThreeWStar A, σ ≠ 1 ∧ σ ⟨x, hxA⟩ = ⟨x, hxA⟩ ∧ σ ⟨d, hdA⟩ = ⟨d, hdA⟩ := by
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hfΩ : ∀ τ ∈ (oThreeWStar A : Set (MulAut ↥A)),
      Subgroup.zpowers ((τ ⟨x, hxA⟩ : ↥A) : G) ∈ Ω := by
    intro τ hτ
    obtain ⟨π, hπ, hπPi, hπτ⟩ := exists_mem_oThreeWPre hτ
    refine horb ⟨π, hπPi, ?_⟩
    rw [MonoidHom.map_zpowers]
    congr 1
    rw [← hπτ, Subgroup.normalizerMonoidHom_apply_apply_coe]
    rfl
  have h9 : (oThreeWStar A : Set (MulAut ↥A)).ncard = 9 := by
    rw [← Nat.card_coe_set_eq]
    exact hPi9
  have hlt : Ω.ncard < (oThreeWStar A : Set (MulAut ↥A)).ncard := by
    rw [h9]
    exact hΩ
  obtain ⟨τ₁, hτ₁, τ₂, hτ₂, hne, hfeq⟩ :=
    Set.exists_ne_map_eq_of_ncard_lt_of_maps_to hlt
      (f := fun τ : MulAut ↥A => Subgroup.zpowers ((τ ⟨x, hxA⟩ : ↥A) : G)) hfΩ (Set.toFinite Ω)
  have hτ₁' : τ₁ ∈ oThreeWStar A := hτ₁
  have hτ₂' : τ₂ ∈ oThreeWStar A := hτ₂
  have hfeq' : Subgroup.zpowers ((τ₁ ⟨x, hxA⟩ : ↥A) : G) =
      Subgroup.zpowers ((τ₂ ⟨x, hxA⟩ : ↥A) : G) := hfeq
  set σ := τ₁⁻¹ * τ₂ with hσdef
  have hσPi : σ ∈ oThreeWStar A := mul_mem (inv_mem hτ₁') hτ₂'
  have hσ3 : σ ^ 3 = 1 := hPi.2 σ hσPi
  refine ⟨σ, hσPi, fun h1 => hne (inv_mul_eq_one.mp h1), ?_, ?_⟩
  ·
    have hmem : ((τ₂ ⟨x, hxA⟩ : ↥A) : G) ∈ Subgroup.zpowers ((τ₁ ⟨x, hxA⟩ : ↥A) : G) := by
      rw [hfeq']
      exact Subgroup.mem_zpowers _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hτ₂x : τ₂ ⟨x, hxA⟩ = (τ₁ ⟨x, hxA⟩) ^ k := Subtype.ext (by rw [Subgroup.coe_zpow, hk])
    have hk' : σ ⟨x, hxA⟩ = ⟨x, hxA⟩ ^ k := by
      rw [hσdef, MulAut.mul_apply, hτ₂x, map_zpow, MulAut.inv_apply_self]
    exact Ronan138S.apply_eq_of_mem_zpowers_of_pow_three σ hσ3 (Subtype.ext (hA.1.2 x hxA))
      (Subgroup.mem_zpowers_iff.mpr ⟨k, hk'.symm⟩)
  ·
    obtain ⟨s, hs, -, hsσ⟩ := exists_mem_oThreeWPre hσPi
    have hmem : s * d * s⁻¹ ∈ Subgroup.zpowers d :=
      (Subgroup.mem_normalizer_iff.mp (hWd hs) d).mp (Subgroup.mem_zpowers d)
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hmem
    have hk' : σ ⟨d, hdA⟩ = ⟨d, hdA⟩ ^ k := by
      apply Subtype.ext
      rw [← hsσ, Subgroup.normalizerMonoidHom_apply_apply_coe, Subgroup.coe_zpow]
      exact hk.symm
    exact Ronan138S.apply_eq_of_mem_zpowers_of_pow_three σ hσ3 (Subtype.ext (hA.1.2 d hdA))
      (Subgroup.mem_zpowers_iff.mpr ⟨k, hk'.symm⟩)

theorem mem_closure_of_apply_eq {A : Subgroup G} (hA : Late.IsE27 A) {σ : MulAut ↥A}
    (hσ1 : σ ≠ 1) {x d : G} (hxA : x ∈ A) (hdA : d ∈ A) (hd1 : d ≠ 1)
    (hxd : x ∉ Subgroup.zpowers d) (hσx : σ ⟨x, hxA⟩ = ⟨x, hxA⟩)
    (hσd : σ ⟨d, hdA⟩ = ⟨d, hdA⟩) {y : ↥A} (hy : σ y = y) :
    (y : G) ∈ Subgroup.closure ({x, d} : Set G) := by
  have hd3 := Proof152WE.card_zpowers_eq_three hA hdA hd1
  have hx1 : x ≠ 1 := fun h1 => hxd (h1 ▸ Subgroup.one_mem _)
  have hx3 := Proof152WE.card_zpowers_eq_three hA hxA hx1
  have hDA : Subgroup.closure ({x, d} : Set G) ≤ A := by
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact hxA
    · exact hdA
  have hD9 : Nat.card (Subgroup.closure ({x, d} : Set G)) = 9 := by
    have h1 := Proof152WE.card_closure_pair hA hxA hdA
    rw [inf_comm, Proof152WE.zpowers_inf_eq_bot hx3 hxd, Subgroup.card_bot, mul_one, hx3,
      hd3] at h1
    exact h1
  have hDh : IsHyperplane A (Subgroup.closure ({x, d} : Set G)) := ⟨hDA, by rw [hA.2, hD9]⟩
  by_contra hyD
  have hle : Subgroup.closure ({x, d} : Set G) ⊔ Subgroup.zpowers (y : G) ≤
      (MonoidHom.eqLocus σ.toMonoidHom (MonoidHom.id ↥A)).map A.subtype := by
    refine sup_le ?_ (Subgroup.zpowers_le.mpr ⟨y, hy, rfl⟩)
    rw [Subgroup.closure_le]
    rintro z (rfl | rfl)
    · exact ⟨⟨_, hxA⟩, hσx, rfl⟩
    · exact ⟨⟨_, hdA⟩, hσd, rfl⟩
  rw [Item148HJ.sup_zpowers_eq_of_isHyperplane hDh y.2 hyD] at hle
  apply hσ1
  refine MulEquiv.ext fun a => ?_
  obtain ⟨a', ha', haa'⟩ := hle a.2
  have e : a' = a := Subtype.ext haa'
  subst e
  exact ha'

theorem conj_mem_closure_of_ncard_lt {A : Subgroup G} (hA : Late.IsE27 A) {d x : G}
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hxA : x ∈ A) (hxd : x ∉ Subgroup.zpowers d)
    (hWd : Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G))
    (hPi : CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A)) (hPi9 : Nat.card (oThreeWStar A) = 9)
    {Ω : Set (Subgroup G)} (hΩ : Ω.ncard < 9)
    (horb : orbitIn (oThreeWPre A) (Subgroup.zpowers x) ⊆ Ω) {π : G} (hπ : π ∈ oThreeWPre A) :
    π * x * π⁻¹ ∈ Subgroup.closure ({x, d} : Set G) := by
  obtain ⟨σ, hσPi, hσ1, hσx, hσd⟩ := exists_fix_of_ncard_lt hA hdA hxA hWd hPi hPi9 hΩ horb
  obtain ⟨⟨π', hπN⟩, hπ', rfl⟩ := hπ
  have hτPi : A.normalizerMonoidHom ⟨π', hπN⟩ ∈ oThreeWStar A := hπ'
  have hστ : σ * A.normalizerMonoidHom ⟨π', hπN⟩ = A.normalizerMonoidHom ⟨π', hπN⟩ * σ :=
    congrArg Subtype.val (hPi.1.is_comm.comm ⟨σ, hσPi⟩ ⟨_, hτPi⟩)
  have hfix : σ (A.normalizerMonoidHom ⟨π', hπN⟩ ⟨x, hxA⟩) =
      A.normalizerMonoidHom ⟨π', hπN⟩ ⟨x, hxA⟩ := by
    rw [← MulAut.mul_apply, hστ, MulAut.mul_apply, hσx]
  have h := mem_closure_of_apply_eq hA hσ1 hxA hdA hd1 hxd hσx hσd hfix
  rw [Subgroup.normalizerMonoidHom_apply_apply_coe] at h
  exact h

theorem omegaA_cases
    (h134 : Item134)
    (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L) {B Lb : Subgroup G}
    {b d : G} (hB : IsHyperplane A B) (hc : IsLBConfig A B b d Lb) :
    omegaA A = {Subgroup.zpowers b} ∨
      (Subgroup.normalizer (A : Set G) ≤ Subgroup.normalizer (Subgroup.zpowers d : Set G) ∧
        CFSG.Assembly.IsElemAbelian 3 (oThreeWStar A) ∧ Nat.card (oThreeWStar A) = 9 ∧
        ((omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers b) ∧ (omegaA A).ncard = 3) ∨
          ∃ a ∈ A, a ∉ Subgroup.zpowers d ∧
            omegaA A = orbitIn (oThreeWPre A) (Subgroup.zpowers b) ∪
              orbitIn (oThreeWPre A) (Subgroup.zpowers a) ∧ (omegaA A).ncard = 6)) ∨
      (omegaA A).ncard = 12 := by
  have hA := h.isE27'
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  obtain ⟨-, hLb, hJ, -, -, -, hdA, hd1, -, hdb⟩ := lbConfig_facts hA hB hc
  have hdB : d ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
  obtain ⟨K, hK, hDK⟩ := Desc143X.exists_mem_le_residual h48 h hB hc hdB hd1 hdb
  have hdata : Sec13Data G A b Lb :=
    { h.toSec13Data with zpowers_mem_omegaA := hc.2.1, mem_lA := hLb }
  obtain ⟨hdL, S, hdS, hSd⟩ := hc.2.2.2.2
  obtain ⟨-, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have hSz := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  rcases h134 G A b Lb hdata hJ d hdA hd1 ⟨_, hSz⟩ K hK hDK with
    ⟨-, -, hΩ1⟩ | ⟨-, -, hWd, hPi, hPi9, -, hΩ⟩ | ⟨-, -, -, h12⟩
  · exact Or.inl hΩ1
  · refine Or.inr (Or.inl ⟨hWd, hPi, hPi9, ?_⟩)
    rcases hΩ with h3 | ⟨I, -, -, -, a, ha, had, hΩ, h6, -⟩
    · exact Or.inl h3
    · exact Or.inr ⟨a, ha.1, had, hΩ, h6⟩
  · exact Or.inr (Or.inr h12)

theorem zpowers_eq_of_ncard_twelve
    (h134 : Item134)
    (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    (h12 : (omegaA A).ncard = 12) {e : G} (heA : e ∈ A) (he1 : e ≠ 1)
    (heΩ : Subgroup.zpowers e ∉ omegaA A) {D L' : Subgroup G} {b' d' : G}
    (hD : IsHyperplane A D) (hc' : IsLBConfig A D b' d' L') :
    Subgroup.zpowers e = Subgroup.zpowers d' := by
  have hA := h.isE27'
  obtain ⟨-, -, hJ', -, -, -, hd'A, hd'1, hd'c, -⟩ := lbConfig_facts hA hD hc'
  have hd'Ω := Proof1523Res3.zpowers_not_mem_omegaA_of_j2 h134 h48
    (Item148HJ.sec14Std_of_isLBConfig h hc') hJ' hd'A hd'1 hd'c
  by_contra hne
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  set T := {F : Subgroup G | F ≤ A ∧ Nat.card F = 3} with hTdef
  have hsub : omegaA A ⊆ T \ {Subgroup.zpowers e, Subgroup.zpowers d'} := by
    intro F hF
    refine ⟨⟨hF.1, hF.2.1⟩, ?_⟩
    rintro (rfl | rfl)
    · exact heΩ hF
    · exact hd'Ω hF
  have hpair : ({Subgroup.zpowers e, Subgroup.zpowers d'} : Set (Subgroup G)) ⊆ T := by
    rintro F (rfl | rfl)
    · exact ⟨Subgroup.zpowers_le.mpr heA, Proof152WE.card_zpowers_eq_three hA heA he1⟩
    · exact ⟨Subgroup.zpowers_le.mpr hd'A, Proof152WE.card_zpowers_eq_three hA hd'A hd'1⟩
  have h1 := Set.ncard_le_ncard hsub
  have h2 := Set.ncard_sdiff_add_ncard_of_subset hpair
  rw [Set.ncard_pair hne] at h2
  have h3 := Item148PtRes.ncard_subgroups_card_three_le (A := A) hA.2
  rw [← hTdef] at h3
  omega

end Ronan152SL25

end CFSG.RankThree.PartTwo.Sec15

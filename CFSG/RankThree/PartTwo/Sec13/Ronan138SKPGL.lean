module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SMain
import CFSG.RankThree.PartTwo.Sec13.Ronan138SNorm
import CFSG.RankThree.PartTwo.Sec13.Item138ProofTools
import CFSG.RankThree.PartTwo.Sec13.Ronan138S131
import CFSG.RankThree.PartTwo.Sec13.Ronan138SPGL
import CFSG.RankThree.PartTwo.KFacts.KS14MathieuAutCore
import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item138ProofExists
import CFSG.RankThree.PartTwo.Sec17.Item1730Conj
import CFSG.GroupTheory.ABGLocalTools.CoreLemmas
import CFSG.RankThree.PartTwo.Sec13.Item138ProofOmega
public import CFSG.RankThree.PartTwo.Sec13.Ronan138SP

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec13.Item138Proof
open Matrix (ProjGenLinGroup)
open CFSG.Assembly.RankThreeEven (projImage)
open CFSG.RankThree.PartTwo.Sec4 (slPi glPi PiField ModThree Type123)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open scoped commutatorElement

section Sylow

variable {G : Type} [Group G] [Finite G] {E F : Subgroup G} {x y : G}

theorem eq_of_isPGroup_le_centralizer (hframe : HeisFrame (E ⊓ F) x y) (hd1 : ⁅x, y⁆ ≠ 1)
    (hxE : x ∈ E) (hyF : y ∈ F) (hE27 : Nat.card E = 27) (hF27 : Nat.card F = 27)
    (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) (hFN : F ≤ Subgroup.normalizer (E : Set G))
    {c : G} (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ F)
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
    {e : G} {α β : ℕ} (hce : c = e ^ α * ⁅x, y⁆ ^ β) {T : Subgroup G} (hT : IsPGroup 3 T)
    (hPT : E ⊔ F ≤ T) (hTe : T ≤ Subgroup.centralizer ({e} : Set G)) : T = E ⊔ F := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set P := E ⊔ F with hP
  set d := ⁅x, y⁆ with hd
  by_contra hne
  have hPT' : P.subgroupOf T < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => hne ?_
    refine le_antisymm (fun z hz => ?_) hPT
    have : (⟨z, hz⟩ : T) ∈ P.subgroupOf T := htop ▸ Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp this
  haveI : Group.IsNilpotent ↥T := IsPGroup.isNilpotent hT
  have hlt := Group.normalizerCondition_of_isNilpotent (G := ↥T) (P.subgroupOf T) hPT'
  obtain ⟨g₀, hg₀N, hg₀P⟩ :
      ∃ g₀ ∈ Subgroup.normalizer ((P.subgroupOf T : Subgroup T) : Set T), g₀ ∉ P.subgroupOf T :=
    SetLike.not_le_iff_exists.mp (fun h => lt_irrefl _ (lt_of_lt_of_le hlt h))
  set g : G := (g₀ : G) with hgdef
  have hgT : g ∈ T := g₀.2
  have hgP : g ∉ P := fun h' => hg₀P (Subgroup.mem_subgroupOf.mpr h')
  have hgN : g ∈ Subgroup.normalizer (P : Set G) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      have h1 := (Subgroup.mem_normalizer_iff.mp hg₀N ⟨z, hPT hz⟩).mp
        (Subgroup.mem_subgroupOf.mpr hz)
      exact Subgroup.mem_subgroupOf.mp h1
    · intro hz
      have hzT : z ∈ T := by
        have h1 : g⁻¹ * (g * z * g⁻¹) * g ∈ T :=
          T.mul_mem (T.mul_mem (T.inv_mem hgT) (hPT hz)) hgT
        rwa [show g⁻¹ * (g * z * g⁻¹) * g = z by group] at h1
      have h2 := (Subgroup.mem_normalizer_iff.mp hg₀N ⟨z, hzT⟩).mpr
        (Subgroup.mem_subgroupOf.mpr hz)
      exact Subgroup.mem_subgroupOf.mp h2
  obtain ⟨k, hk⟩ : ∃ k : ℕ, g ^ 3 ^ k = 1 := by
    obtain ⟨k, hk⟩ := hT ⟨g, hgT⟩
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hgd : g * d * g⁻¹ = d := by
    obtain ⟨a, b, hab⟩ := isNF_of_mem_sup hframe hxE hyF hE27 hF27 h9 hFN
      ((Subgroup.mem_normalizer_iff.mp hgN x).mp (Subgroup.mem_sup_left hxE))
    obtain ⟨a', b', hab'⟩ := isNF_of_mem_sup hframe hxE hyF hE27 hF27 h9 hFN
      ((Subgroup.mem_normalizer_iff.mp hgN y).mp (Subgroup.mem_sup_right hyF))
    have h1 := IsNF.commutator hframe hab hab'
    have h2 : ⁅g * x * g⁻¹, g * y * g⁻¹⁆ = g * d * g⁻¹ := by
      rw [hd, commutatorElement_def, commutatorElement_def]
      group
    rw [h2] at h1
    have hmem : g * d * g⁻¹ ∈ Subgroup.zpowers d := by
      rw [h1]
      exact pow_mem (Subgroup.mem_zpowers _) _
    exact conj_eq_of_mem_zpowers_of_pow_three_pow hframe.comm_pow_three hmem hk
  have hge : g * e = e * g := Subgroup.mem_centralizer_singleton_iff.mp (hTe hgT)
  have hgd' : Commute g d := by
    show g * d = d * g
    calc g * d = g * d * g⁻¹ * g := by group
      _ = d * g := by rw [hgd]
  have hgc : Commute g c := by
    rw [hce]
    exact ((show Commute g e from hge).pow_right α).mul_right (hgd'.pow_right β)
  have hgH : g ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    centralizer_le_normalizer_zpowers c (Subgroup.mem_centralizer_singleton_iff.mpr hgc.eq)
  have hQ3 : IsPGroup 3 (P ⊔ Subgroup.zpowers g : Subgroup G) :=
    hT.to_le (sup_le hPT (Subgroup.zpowers_le.mpr hgT))
  have hQH : P ⊔ Subgroup.zpowers g ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) :=
    sup_le hSyl.le (Subgroup.zpowers_le.mpr hgH)
  have heq := hSyl.eq_of_le le_sup_left hQH hQ3
  exact hgP (heq ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers g))

theorem eq_of_isElemAbelian_le_right (hframe : HeisFrame (E ⊓ F) x y) (hd1 : ⁅x, y⁆ ≠ 1)
    (hxE : x ∈ E) (hyF : y ∈ F) (hE27 : Nat.card E = 27) (hF27 : Nat.card F = 27)
    (h9 : Nat.card (E ⊓ F : Subgroup G) = 9) (hFN : F ≤ Subgroup.normalizer (E : Set G))
    (hEN' : E ≤ Subgroup.normalizer (F : Set G)) {c : G} (hcF : c ∈ F)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ F)
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
    {B : Subgroup G} (hB : CFSG.Assembly.IsElemAbelian 3 B) (hFB : F ≤ B) : B = F := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set H := Subgroup.normalizer (Subgroup.zpowers c : Set G) with hH
  set N := H ⊓ Subgroup.normalizer (F : Set G) with hN
  have hBab : ∀ a ∈ B, ∀ b ∈ B, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hB.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hB3 : IsPGroup 3 B := fun g => ⟨1, Subtype.ext (by simpa using hB.2 g g.2)⟩
  have hBH : B ≤ H := fun b hb => centralizer_le_normalizer_zpowers c
    (Subgroup.mem_centralizer_singleton_iff.mpr (hBab b hb c (hFB hcF)))
  have hBN : B ≤ Subgroup.normalizer (F : Set G) := by
    intro b hb
    apply mem_normalizer_of_map_le
    rintro _ ⟨f, hf, rfl⟩
    change b * f * b⁻¹ ∈ F
    rw [hBab b hb f (hFB hf), mul_inv_cancel_right]
    exact hf
  have hPN : E ⊔ F ≤ N := le_inf hSyl.le (sup_le hEN' Subgroup.le_normalizer)
  have hPsyl : CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ F) N := hSyl.of_le hPN inf_le_left
  obtain ⟨Q, hQ⟩ := (hB3.comap_subtype (K := N)).exists_le_sylow
  have hQsyl : CFSG.ABGLocalTools.IsSylowOf 3 ((Q : Subgroup N).map N.subtype) N := ⟨Q, rfl⟩
  have hBQ : B ≤ (Q : Subgroup N).map N.subtype := fun b hb =>
    ⟨⟨b, le_inf hBH hBN hb⟩, hQ (show (⟨b, _⟩ : N) ∈ B.subgroupOf N from hb), rfl⟩
  obtain ⟨k, hkN, hk⟩ := hPsyl.exists_mem_conj hQsyl
  have hkF : k ∈ Subgroup.normalizer (F : Set G) := (Subgroup.mem_inf.mp hkN).2
  have hkB : ∀ b ∈ B, k⁻¹ * b * k ∈ F := by
    intro b hb
    have hbP : k⁻¹ * b * k ∈ E ⊔ F := (hk b).mp (hBQ hb)
    obtain ⟨i, j, hij⟩ := isNF_of_mem_sup hframe hxE hyF hE27 hF27 h9 hFN hbP
    have hky : k * y * k⁻¹ ∈ F := (Subgroup.mem_normalizer_iff.mp hkF y).mp hyF
    have hcomm : (k⁻¹ * b * k) * y = y * (k⁻¹ * b * k) := by
      have h1 := hBab b hb _ (hFB hky)
      calc k⁻¹ * b * k * y = k⁻¹ * (b * (k * y * k⁻¹)) * k := by group
        _ = k⁻¹ * ((k * y * k⁻¹) * b) * k := by rw [h1]
        _ = y * (k⁻¹ * b * k) := by group
    have h1 := IsNF.commutator hframe hij IsNF.gen_y
    have h2 : ⁅k⁻¹ * b * k, y⁆ = 1 := by rw [commutatorElement_def, hcomm]; group
    rw [h2] at h1
    have hi : 3 ∣ i := by
      have := orderOf_dvd_of_pow_eq_one h1.symm
      rw [hframe.orderOf_comm hd1] at this
      simpa using this
    exact (mem_right_iff hframe hyF hF27 h9 hij).mpr ((ZMod.natCast_eq_zero_iff i 3).mpr hi)
  have hcard : Nat.card B ≤ Nat.card F := by
    have hle : B.map (MulAut.conj k⁻¹).toMonoidHom ≤ F := by
      rintro _ ⟨b, hb, rfl⟩
      change k⁻¹ * b * k⁻¹⁻¹ ∈ F
      rw [inv_inv]
      exact hkB b hb
    have := Subgroup.card_le_of_le hle
    rwa [Subgroup.card_map_of_injective (MulAut.conj k⁻¹).injective] at this
  exact (Subgroup.eq_of_le_of_card_ge hFB hcard).symm

end Sylow

section Inner

variable {G : Type} [Group G] [Finite G]

theorem mem_sup_zpowers_of_inner_of_le {K P : Subgroup G} {e : G}
    (hZ : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥)
    (hP3 : IsPGroup 3 P) (hPN : P ≤ Subgroup.normalizer (K : Set G))
    (hCT : ∀ T : Subgroup G, IsPGroup 3 T → P ≤ T → T ≤ P ⊔ K →
      ∀ r ∈ T, r ∈ Sec4.thetaQuotCentralizer K → r ∈ Subgroup.zpowers e)
    {x : G} (hxP : x ∈ P) {k : G} (hk : k ∈ K)
    (hkx : k⁻¹ * x ∈ Sec4.thetaQuotCentralizer K) :
    x ∈ K ⊔ Subgroup.zpowers e := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := Subgroup.normalizer (K : Set G) with hNdef
  have hxk : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hPN hxP⟩) =
      MulAut.conj ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) := by
    obtain ⟨⟨w, hwN⟩, hker, hw⟩ := Subgroup.mem_map.mp hkx
    change w = k⁻¹ * x at hw
    have hkN : k ∈ N := Subgroup.le_normalizer hk
    have e1 : (⟨x, hPN hxP⟩ : N) = ⟨k, hkN⟩ * ⟨w, hwN⟩ := Subtype.ext (by
      change x = k * w
      rw [hw, mul_inv_cancel_left])
    have h1 : Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨w, hwN⟩) = 1 := hker
    rw [e1, map_mul, map_mul, h1, mul_one]
    exact Sec17.thetaQuotMulAut_normalizerMonoidHom_of_mem ⟨k, hk⟩
  set ρ : N →* MulAut (K ⧸ aschbacherSolvableCore 3 K) :=
    (Sec4.thetaQuotMulAut K).comp K.normalizerMonoidHom with hρ
  set X := P ⊔ K with hX
  have hXN : X ≤ N := sup_le hPN Subgroup.le_normalizer
  obtain ⟨Q, hQ⟩ := (hP3.comap_subtype (K := X)).exists_le_sylow
  set T : Subgroup G := (Q : Subgroup X).map X.subtype with hTdef
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T X := ⟨Q, rfl⟩
  have hPT : P ≤ T := fun y hy =>
    ⟨⟨y, (le_sup_left : P ≤ X) hy⟩, hQ (show (⟨y, _⟩ : X) ∈ P.subgroupOf X from hy), rfl⟩
  have hT3 : IsPGroup 3 T := hTsyl.isPGroup
  obtain ⟨SK, hSK⟩ := hTsyl.inf_of_le_normalizer (le_sup_right : K ≤ X) hXN
  have hSKmem : ∀ q : K, q ∈ (SK : Subgroup K) ↔ (q : G) ∈ T ⊓ K := by
    intro q
    constructor
    · intro hq
      rw [← hSK]
      exact ⟨q, hq, rfl⟩
    · intro hq
      rw [← hSK] at hq
      obtain ⟨q', hq', hqq'⟩ := hq
      rwa [← Subtype.ext hqq']
  set Qb : Sylow 3 (K ⧸ aschbacherSolvableCore 3 K) :=
    SK.mapSurjective (QuotientGroup.mk'_surjective _) with hQbdef
  have hQb : (Qb : Subgroup _) =
      (SK : Subgroup K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) :=
    Sylow.coe_mapSurjective _ _
  have hconj : Function.Injective
      (MulAut.conj : (K ⧸ aschbacherSolvableCore 3 K) →* MulAut _) :=
    KFacts.KS14.conj_injective_of_center_eq_bot hZ
  set Sh : Subgroup (K ⧸ aschbacherSolvableCore 3 K) :=
    ((T.subgroupOf N).map ρ).comap MulAut.conj with hShdef
  have hSh3 : IsPGroup 3 Sh :=
    ((hT3.comap_subtype (K := N)).map ρ).comap_of_injective _ hconj
  have hQbSh : (Qb : Subgroup _) ≤ Sh := by
    rw [hQb]
    rintro _ ⟨q, hq, rfl⟩
    refine ⟨⟨q, Subgroup.le_normalizer q.2⟩, ?_, ?_⟩
    · exact ((hSKmem q).mp hq).1
    · exact Sec17.thetaQuotMulAut_normalizerMonoidHom_of_mem q
  have hShQb : Sh = Qb := Qb.3 hSh3 hQbSh
  have hkSh : ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) ∈ Sh :=
    ⟨⟨x, hPN hxP⟩, hPT hxP, hxk⟩
  rw [hShQb, hQb] at hkSh
  obtain ⟨q, hqSK, hqk⟩ := hkSh
  have hqTK : (q : G) ∈ T ⊓ K := (hSKmem q).mp hqSK
  set r := (q : G)⁻¹ * x with hrdef
  have hqN : (q : G) ∈ N := Subgroup.le_normalizer q.2
  have hrN : r ∈ N := mul_mem (inv_mem hqN) (hPN hxP)
  have hrD : r ∈ Sec4.thetaQuotCentralizer K := by
    refine Subgroup.mem_map.mpr ⟨⟨r, hrN⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    have he : (⟨r, hrN⟩ : N) = (⟨q, hqN⟩ : N)⁻¹ * ⟨x, hPN hxP⟩ := rfl
    rw [he, map_mul, map_inv]
    change (Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨q, hqN⟩))⁻¹ *
      Sec4.thetaQuotMulAut K (K.normalizerMonoidHom ⟨x, hPN hxP⟩) = 1
    rw [Sec17.thetaQuotMulAut_normalizerMonoidHom_of_mem q, hxk]
    have : (q : K ⧸ aschbacherSolvableCore 3 K) =
        ((⟨k, hk⟩ : K) : K ⧸ aschbacherSolvableCore 3 K) := hqk
    rw [this, inv_mul_cancel]
  have hrT : r ∈ T := mul_mem (inv_mem hqTK.1) (hPT hxP)
  have hre : r ∈ Subgroup.zpowers e := hCT T hT3 hPT hTsyl.le r hrT hrD
  have hxqr : x = (q : G) * r := by rw [hrdef, mul_inv_cancel_left]
  rw [hxqr]
  exact mul_mem (Subgroup.mem_sup_left q.2) (Subgroup.mem_sup_right hre)

end Inner

theorem multiplicative_zmod3_pow_three : ∀ m : Multiplicative (ZMod 3), m ^ 3 = 1 := by decide

section Main


variable {G : Type} [Group G] [Finite G]

theorem exists_s_of_pgl (h131 : Item131) (hspor : SporadicModels131)
    {A L E F : Subgroup G} {c : G} (hH : Hyp138 A c L E) (hF : IsF138N L E F)
    (hSyl : CFSG.ABGLocalTools.IsSylowOf 3 (E ⊔ F)
      (Subgroup.normalizer (Subgroup.zpowers c : Set G)))
    {x y : G} (hframe : HeisFrame (E ⊓ F) x y) (hxE : x ∈ E) (hyF : y ∈ F) (hd1 : ⁅x, y⁆ ≠ 1)
    (hdL : ⁅x, y⁆ ∈ L) (hcF : c ∈ F) (h81 : Nat.card (E ⊔ F : Subgroup G) = 81)
    (h9 : Nat.card (E ⊓ F : Subgroup G) = 9)
    {e : G} {K : Subgroup G} (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e)
    (heF : e ∈ F) (heL : e ∉ L) {α β : ℕ} (hce : c = e ^ α * ⁅x, y⁆ ^ β)
    (hPGLK : Sec8.IsZ3PGLThreePi (lBarA e K E)) :
    ∃ s : G, s ∈ K ∧ s ∈ Subgroup.normalizer ((E ⊔ F : Subgroup G) : Set G) ∧
      s * ⁅x, y⁆ * s⁻¹ = ⁅x, y⁆⁻¹ ∧ s ∉ Subgroup.normalizer (E : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set d := ⁅x, y⁆ with hd
  set P := E ⊔ F with hP
  obtain ⟨h, -, -, hE3, hE27, -, -, hST, -⟩ := hH
  obtain ⟨⟨-, hF3, hF27, -, hFN⟩, -⟩ := hF
  have hXE : E ∈ partTwoE G ∧ E ∉ partTwoT G := by
    rcases hST with hS | hT
    · exact ⟨hS.1, hS.2.1⟩
    · exact ⟨hT.1, hT.2.1⟩
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hXF : E ∈ partTwoF G := hFE ▸ hXE.1
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF
      not_mem_partTwoT := hXE.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have hEmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → E ≤ B → B = E := hXF.2.1
  have hEab : ∀ a ∈ E, ∀ b ∈ E, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hE3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hFab : ∀ a ∈ F, ∀ b ∈ F, a * b = b * a := fun a ha b hb =>
    congrArg Subtype.val (hF3.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩)
  have hEN' : E ≤ Subgroup.normalizer (F : Set G) :=
    le_sup_left.trans (le_normalizer_of_card le_sup_right hF27 h81)
  have hPNE : P ≤ Subgroup.normalizer (E : Set G) := le_normalizer_of_card le_sup_left hE27 h81
  have hP3 : IsPGroup 3 P := IsPGroup.of_card (n := 4) (by rw [h81]; norm_num)
  have heE : e ∈ E := hD.mem_A
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have he1 : e ≠ 1 := hD.ne_one
  have hd3 : d ^ 3 = 1 := hframe.comm_pow_three
  have hdZ : d ∈ E ⊓ F := hframe.comm_mem
  have hdP : d ∈ P := Subgroup.mem_sup_left (Subgroup.mem_inf.mp hdZ).1
  have hPC : P ≤ Subgroup.centralizer ({e} : Set G) := sup_le
    (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hEab a ha e heE))
    (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hFab a ha e heF))
  have hPe : ∀ p ∈ P, p * e = e * p := fun p hp =>
    Subgroup.mem_centralizer_singleton_iff.mp (hPC hp)
  have hKC : K ≤ Subgroup.centralizer ({e} : Set G) := hD.le_centralizer
  obtain ⟨heK, ⟨φaut⟩, x₀, hx₀E, hx₀type⟩ := facts131_of_isZ3PGLThreePi h131 hspor hD hPGLK
  obtain ⟨b, hbE, hbK, hb1⟩ : ∃ b ∈ E, b ∈ K ∧ b ≠ 1 := by
    set σ := φaut.symm (Multiplicative.ofAdd (1 : ZMod 3)) with hσ
    have hσ1 : (σ : MulAut E) ≠ 1 := by
      intro h1
      have h2 : σ = 1 := Subtype.ext h1
      have h3 : Multiplicative.ofAdd (1 : ZMod 3) = φaut 1 := by
        rw [← h2, hσ, MulEquiv.apply_symm_apply]
      rw [map_one φaut, ofAdd_eq_one] at h3
      exact absurd h3 one_ne_zero
    obtain ⟨k, hkN, hkK, hkσ⟩ := Sec4.mem_autIn_iff.mp σ.2
    obtain ⟨a, ha⟩ : ∃ a : E, (σ : MulAut E) a ≠ a := by
      by_contra hall
      push Not at hall
      exact hσ1 (MulEquiv.ext hall)
    rw [← hkσ] at ha
    have ha' : k * (a : G) * k⁻¹ ≠ a := fun h' => ha (Subtype.ext (by
      rw [Sec4.normalizerMonoidHom_apply_coe]; exact h'))
    refine ⟨k * a * k⁻¹ * (a : G)⁻¹, ?_, ?_, ?_⟩
    · exact mul_mem ((Subgroup.mem_normalizer_iff.mp hkN a).mp a.2) (inv_mem a.2)
    · have haK : (a : G) * k⁻¹ * (a : G)⁻¹ ∈ K :=
        (Subgroup.mem_normalizer_iff.mp (hK.2.1 a.2) _).mp (inv_mem hkK)
      rw [show k * a * k⁻¹ * (a : G)⁻¹ = k * ((a : G) * k⁻¹ * (a : G)⁻¹) by group]
      exact mul_mem hkK haK
    · intro h1
      exact ha' (mul_inv_eq_one.mp h1)
  have hPNK : P ≤ Subgroup.normalizer (K : Set G) := fun p hp =>
    mem_normalizer_of_mem_lA hK he3 heK hbE hbK hb1 (hPNE hp) (hPe p hp)
  have hCEset := sectionCentralizer_eq_inf hK.2.1
  rw [hK.2.2.1] at hCEset
  have hCE : E ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers e :=
    SetLike.coe_injective hCEset.symm
  have hCK : ∀ a ∈ E, a ∈ Sec4.thetaQuotCentralizer K → a ∈ Subgroup.zpowers e :=
    fun a ha ha' => hCE ▸ Subgroup.mem_inf.mpr ⟨ha, ha'⟩
  have heC : e ∈ Sec4.thetaQuotCentralizer K :=
    (Subgroup.mem_inf.mp (hCE.symm ▸ Subgroup.mem_zpowers e : e ∈ E ⊓ _)).2
  have hde : Subgroup.zpowers d ⊓ Subgroup.zpowers e = ⊥ := by
    rw [inf_comm, eq_bot_iff]
    intro z hz
    rw [← zpowers_inf_eq_bot he3 heL]
    exact Subgroup.mem_inf.mpr ⟨(Subgroup.mem_inf.mp hz).1,
      Subgroup.zpowers_le.mpr hdL (Subgroup.mem_inf.mp hz).2⟩
  have hCP : ∀ r ∈ P, r ∈ Sec4.thetaQuotCentralizer K → r ∈ Subgroup.zpowers e := by
    intro r hr hrC
    by_cases hrE : r ∈ E
    · exact hCK r hrE hrC
    exfalso
    apply hrE
    have hrcomm : ∀ a ∈ E, a * r = r * a := by
      intro a ha
      have h1 : r * a * r⁻¹ * a⁻¹ ∈ E :=
        mul_mem ((Subgroup.mem_normalizer_iff.mp (hPNE hr) a).mp ha) (inv_mem ha)
      have h2 : r * a * r⁻¹ * a⁻¹ ∈ Sec4.thetaQuotCentralizer K := by
        rw [show r * a * r⁻¹ * a⁻¹ = r * (a * r⁻¹ * a⁻¹) by group]
        exact mul_mem hrC (Sec6.conj_mem_thetaQuotCentralizer (inv_mem hrC) (hK.2.1 ha))
      have h3 : r * a * r⁻¹ * a⁻¹ ∈ Subgroup.zpowers d := by
        obtain ⟨i, j, hij⟩ := isNF_of_mem_sup hframe hxE hyF hE27 hF27 h9 hFN hr
        obtain ⟨i', hi'⟩ := isNF_of_mem_left hframe hxE hE27 h9 ha
        have h4 := IsNF.commutator hframe hij hi'
        rw [commutatorElement_def] at h4
        rw [h4]
        exact pow_mem (Subgroup.mem_zpowers _) _
      have h4 : r * a * r⁻¹ * a⁻¹ ∈ Subgroup.zpowers d ⊓ Subgroup.zpowers e :=
        Subgroup.mem_inf.mpr ⟨h3, hCK _ h1 h2⟩
      rw [hde, Subgroup.mem_bot] at h4
      have h5 : r * a = a * r := by
        calc r * a = r * a * r⁻¹ * a⁻¹ * (a * r) := by group
          _ = a * r := by rw [h4, one_mul]
      exact h5.symm
    have hsup := Sec15.isElemAbelian_sup_zpowers hE3 (pow_three_of_mem_sup hFN hEN' hE3 hF3 hr)
      hrcomm
    rw [← hEmax _ hsup le_sup_left]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers r)
  have hTP : ∀ T : Subgroup G, IsPGroup 3 T → P ≤ T →
      T ≤ Subgroup.centralizer ({e} : Set G) → T = P := fun T hT hPT hTe =>
    eq_of_isPGroup_le_centralizer hframe hd1 hxE hyF hE27 hF27 h9 hFN hSyl hce hT hPT hTe
  have hFmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → F ≤ B → B = F :=
    fun B hB hFB =>
      eq_of_isElemAbelian_le_right hframe hd1 hxE hyF hE27 hF27 h9 hFN hEN' hcF hSyl hB hFB
  obtain ⟨hx₀N, π, p, f, Fld, _, hPi, hq, ψ, y₀, hy₀, hy₀3, hx₀act⟩ := hx₀type
  have hx₀ψ : ActsPGL ψ x₀ y₀ := ⟨hx₀N, hy₀, hx₀act⟩
  have hπ : π = false → UnitaryFieldData p f Fld := fun h => by subst h; exact hPi.unitary
  have hKq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hK.1
  have hZK : Subgroup.center (K ⧸ aschbacherSolvableCore 3 K) = ⊥ :=
    (facts_of_isZ3PGLThreePi hD hPGLK).2.1
  have hq2 : 2 < p ^ f := Item138Proof.two_lt_of_mulEquiv hKq hPi hq ψ
  haveI : Group.IsPerfect (K ⧸ aschbacherSolvableCore 3 K) := hKq.1
  haveI : Group.IsPerfect (projImage (slPi π 3 (p ^ f) Fld)) :=
    Group.IsPerfect.ofSurjective (f := ψ.toMonoidHom) ψ.surjective
  have hKact : ∀ k ∈ K, ∃ s ∈ slPi π 3 (p ^ f) Fld, ActsPGL ψ k s := by
    intro k hk
    obtain ⟨s, hs, hse⟩ := Subgroup.mem_map.mp (ψ ((⟨k, hk⟩ : K) :
      K ⧸ aschbacherSolvableCore 3 K)).2
    exact ⟨s, hs, actsPGL_of_mem hπ hk hs hse.symm⟩
  have hCF : F ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers e := by
    refine le_antisymm (fun z hz => hCP z (Subgroup.mem_sup_right (Subgroup.mem_inf.mp hz).1)
      (Subgroup.mem_inf.mp hz).2) ?_
    rw [Subgroup.zpowers_le]
    exact Subgroup.mem_inf.mpr ⟨heF, heC⟩
  have hEact := actsPGL_of_maximal hKq hE3 hEmax hE27 hK.2.1 heE he1 hCE hPi hq hq2 ψ
  have hFact := actsPGL_of_maximal hKq hF3 hFmax hF27 ((le_sup_right : F ≤ P).trans hPNK) heF
    he1 hCF hPi hq hq2 ψ
  have hPact : ∀ z ∈ P, ∃ w, ActsPGL ψ z w := by
    intro z hz
    have hz' : z ∈ ((F ⊔ E : Subgroup G) : Set G) := by rw [sup_comm]; exact hz
    rw [Subgroup.coe_mul_of_left_le_normalizer_right F E hFN] at hz'
    obtain ⟨f', hf', ε, hε, rfl⟩ := hz'
    obtain ⟨yf, hyf⟩ := hFact f' hf'
    obtain ⟨yε, hyε⟩ := hEact ε hε
    exact ⟨yf * yε, hyf.mul hyε⟩
  have hy₀n := mk_not_mem_projImage_slPi_of_type3 hPi hq hy₀ hy₀3
  have hCT : ∀ T : Subgroup G, IsPGroup 3 T → P ≤ T → T ≤ P ⊔ K →
      ∀ r ∈ T, r ∈ Sec4.thetaQuotCentralizer K → r ∈ Subgroup.zpowers e := by
    intro T hT hPT hTPK r hr hrC
    have hTe : T ≤ Subgroup.centralizer ({e} : Set G) := hTPK.trans (sup_le hPC hKC)
    rw [hTP T hT hPT hTe] at hr
    exact hCP r hr hrC
  have hPKE : P ≤ K ⊔ E := by
    intro z hz
    obtain ⟨w, hw⟩ := hPact z hz
    obtain ⟨jj, s, hs, hws⟩ := exists_zpow_mul_of_mem_glPi hPi hq hq2 hy₀ hy₀n hw.2.1
    obtain ⟨u, hu⟩ := ψ.surjective ⟨ProjGenLinGroup.mk s, Subgroup.mem_map_of_mem _ hs⟩
    obtain ⟨⟨k, hk⟩, rfl⟩ := QuotientGroup.mk_surjective u
    have hkact : ActsPGL ψ k s := actsPGL_of_mem hπ hk hs (by rw [hu])
    have hz'act := (hx₀ψ.zpow hπ (-jj)).mul hw
    have hcls : ProjGenLinGroup.mk (y₀ ^ (-jj) * w) = ProjGenLinGroup.mk s := by
      rw [map_mul, map_zpow, hws, ← mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, one_mul]
    have hkz := hkact.inv_mul_mem_thetaQuotCentralizer hz'act hcls.symm
    have hz'P : x₀ ^ (-jj) * z ∈ P :=
      mul_mem (P.zpow_mem (Subgroup.mem_sup_left hx₀E) _) hz
    have hmem := mem_sup_zpowers_of_inner_of_le (K := K) (P := P) (e := e) hZK hP3 hPNK hCT
      hz'P hk hkz
    have hz0 : z = x₀ ^ jj * (x₀ ^ (-jj) * z) := by
      rw [← mul_assoc, ← zpow_add, add_neg_cancel, zpow_zero, one_mul]
    rw [hz0]
    refine mul_mem (Subgroup.mem_sup_right (Subgroup.zpow_mem _ hx₀E _)) ?_
    exact (sup_le le_sup_left (Subgroup.zpowers_le.mpr (Subgroup.mem_sup_right heE)) :
      K ⊔ Subgroup.zpowers e ≤ K ⊔ E) hmem
  have hKEC : K ⊔ E ≤ Subgroup.centralizer ({e} : Set G) := sup_le hKC
    (fun a ha => Subgroup.mem_centralizer_singleton_iff.mpr (hEab a ha e heE))
  obtain ⟨Q, hQ⟩ := (hP3.comap_subtype (K := K ⊔ E)).exists_le_sylow
  set T : Subgroup G := (Q : Subgroup ↥(K ⊔ E)).map (K ⊔ E).subtype with hTdef
  have hTsyl : CFSG.ABGLocalTools.IsSylowOf 3 T (K ⊔ E) := ⟨Q, rfl⟩
  have hPT : P ≤ T := fun z hz =>
    ⟨⟨z, hPKE hz⟩, hQ (show (⟨z, _⟩ : ↥(K ⊔ E)) ∈ P.subgroupOf (K ⊔ E) from hz), rfl⟩
  have hTeq : T = P := hTP T hTsyl.isPGroup hPT (hTsyl.le.trans hKEC)
  have hW : (Nat.card ↥(K ⊔ E)).factorization 3 = 4 := by
    have hcardT := hTsyl.card_eq
    rw [hTeq, h81, show (81 : ℕ) = 3 ^ 4 by norm_num] at hcardT
    exact (Nat.pow_right_injective (le_refl 2 |>.trans (by norm_num : 2 ≤ 3)) hcardT).symm
  have hPH : P ≤ Subgroup.normalizer (Subgroup.zpowers e : Set G) :=
    hPC.trans (centralizer_le_normalizer_zpowers e)
  obtain ⟨π', p', f', Kf, _, hKf, hq', ⟨φ⟩⟩ := hPGLK
  obtain ⟨s, hs, hsinv⟩ := RonanItem137.main_aux hD hPH le_sup_left hPKE hP3 h81 hW hKf hq' φ
  have hsK : s ∈ K := (Subgroup.mem_inf.mp hs).1
  have hsN : s ∈ Subgroup.normalizer (P : Set G) := (Subgroup.mem_inf.mp hs).2
  have hsd : s * d * s⁻¹ = d⁻¹ := hsinv d
    (Subgroup.commutator_mem_commutator (Subgroup.mem_sup_left hxE) (Subgroup.mem_sup_right hyF))
  have hsE : s ∉ Subgroup.normalizer (E : Set G) := by
    intro hsNE
    have hσ : E.normalizerMonoidHom ⟨s, hsNE⟩ ∈ Sec4.autIn K E :=
      Sec4.mem_autIn_iff.mpr ⟨s, hsNE, hsK, rfl⟩
    have hσ3 : (⟨_, hσ⟩ : Sec4.autIn K E) ^ 3 = 1 := by
      apply φaut.injective
      rw [map_pow, map_one]
      exact multiplicative_zmod3_pow_three _
    have hdE : d ∈ E := (Subgroup.mem_inf.mp hdZ).1
    have h1 := congrArg (fun τ : Sec4.autIn K E => (((τ : MulAut E) ⟨d, hdE⟩ : E) : G)) hσ3
    simp only [Subgroup.coe_pow, Subgroup.coe_one, MulAut.one_apply] at h1
    rw [normalizerMonoidHom_pow_coe] at h1
    have h2 : s ^ 3 * d * (s ^ 3)⁻¹ = d⁻¹ := by
      calc s ^ 3 * d * (s ^ 3)⁻¹ = s * (s * (s * d * s⁻¹) * s⁻¹) * s⁻¹ := by
            rw [pow_three]; group
        _ = d⁻¹ := by rw [hsd, show s * d⁻¹ * s⁻¹ = (s * d * s⁻¹)⁻¹ by group, hsd, inv_inv, hsd]
    rw [h2] at h1
    apply hd1
    have h3 : d * d = 1 := by
      calc d * d = d⁻¹ * d := by rw [h1]
        _ = 1 := inv_mul_cancel d
    calc d = d ^ 3 * (d * d)⁻¹ := by rw [pow_three]; group
      _ = 1 := by rw [hd3, h3]; group
  exact ⟨s, hsK, hsN, hsd, hsE⟩

end Main

end CFSG.RankThree.PartTwo.Sec13.Ronan138S

module

public import CFSG.RankThree.PartTwo.Sec15.Ronan152SL25Fpf
public import CFSG.RankThree.PartTwo.Sec15.Gagen155W315xFacts
import CFSG.RankThree.PartTwo.Sec15.Ronan155W315QLift
import CFSG.RankThree.PartTwo.Sec15.Item1523Res3ProofRead
import CFSG.RankThree.PartTwo.Sec15.Item152ResProofW
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec12.Gap128OTwoHJ
public import CFSG.RankThree.PartTwo.Sec16.Item162Proof
public import CFSG.RankThree.PartTwo.Sec6.Item612Core

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Ronan155W315

theorem eq_closure_pair_of_mem {A B : Subgroup G} (hA : Late.IsE27 A) (hB : IsHyperplane A B)
    {x z : G} (hxB : x ∈ B) (hzB : z ∈ B) (hx1 : x ≠ 1) (hzx : z ∉ Subgroup.zpowers x) :
    B = Subgroup.closure {x, z} := by
  have hH := Main148.isHyperplane_closure_pair148 hA (hB.1 hxB) (hB.1 hzB) hx1 hzx
  have hle : Subgroup.closure ({x, z} : Set G) ≤ B := by
    rw [Subgroup.closure_le]
    rintro w (rfl | rfl)
    · exact hxB
    · exact hzB
  refine (Subgroup.eq_of_le_of_card_ge hle ?_).symm
  have h1 := hB.2
  have h2 := hH.2
  omega

theorem zpowers_mem_omegaA_of_cases (h134 : Item134) (h48 : Sec4.Item4_8) {A L : Subgroup G}
    {c : G} (h : Sec14Std G A c L) {B Lb : Subgroup G} {b d : G} (hB : IsHyperplane A B)
    (hc : IsLBConfig A B b d Lb) {C : Subgroup G} {y d₀ : G} (hyB : y ∈ B) (hy1 : y ≠ 1)
    (hyC : y ∉ C) (hd₀B : d₀ ∈ B) (hd₀1 : d₀ ≠ 1) (hd₀C : d₀ ∈ C)
    (hd₀Ω : Subgroup.zpowers d₀ ∉ omegaA A) {b₁ : G} (hb₁C : b₁ ∈ C)
    (hb₁Ω : Subgroup.zpowers b₁ ∈ omegaA A) : Subgroup.zpowers y ∈ omegaA A := by
  classical
  have : Finite (Subgroup G) :=
    Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
  have hA := h.isE27'
  obtain ⟨hbΩ, -, hJ, -, hbA, hb1, hdA, hd1, hdc, hdb⟩ := Ronan152SL25.lbConfig_facts hA hB hc
  have hyA : y ∈ A := hB.1 hyB
  have hd₀A : d₀ ∈ A := hB.1 hd₀B
  have hy3 := Proof152WE.card_zpowers_eq_three hA hyA hy1
  have hd₀3 := Proof152WE.card_zpowers_eq_three hA hd₀A hd₀1
  have hyd₀ : y ∉ Subgroup.zpowers d₀ := fun h' => hyC (Subgroup.zpowers_le.mpr hd₀C h')
  have hyne : Subgroup.zpowers d₀ ≠ Subgroup.zpowers y := fun h' =>
    hyd₀ (h' ▸ Subgroup.mem_zpowers y)
  have hdΩ : Subgroup.zpowers d ∉ omegaA A :=
    Proof1523Res3.zpowers_not_mem_omegaA_of_j2 h134 h48 (Item148HJ.sec14Std_of_isLBConfig h hc)
      hJ hdA hd1 hdc
  by_contra hyΩ
  rcases Ronan152SL25.omegaA_cases h134 h48 h hB hc with hΩ1 | ⟨hWd, hPi, hPi9, hΩ⟩ | h12
  ·
    have hb₁b : Subgroup.zpowers b₁ = Subgroup.zpowers b := by
      rw [hΩ1] at hb₁Ω
      exact hb₁Ω
    have hbC : b ∈ C := Subgroup.zpowers_le.mpr hb₁C (hb₁b ▸ Subgroup.mem_zpowers b)
    have hbB : b ∈ B := hc.1 ▸ Subgroup.subset_closure (Set.mem_insert b _)
    have hd₀b : d₀ ∉ Subgroup.zpowers b := by
      intro h'
      have hzeq : Subgroup.zpowers d₀ = Subgroup.zpowers b :=
        Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr h')
          (by rw [hd₀3, Proof152WE.card_zpowers_eq_three hA hbA hb1])
      exact hd₀Ω (hzeq ▸ hbΩ)
    have hBeq := eq_closure_pair_of_mem hA hB hbB hd₀B hb1 hd₀b
    apply hyC
    have hle : B ≤ C := by
      rw [hBeq, Subgroup.closure_le]
      rintro w (rfl | rfl)
      · exact hbC
      · exact hd₀C
    exact hle hyB
  ·
    have hΩ9 : (omegaA A).ncard < 9 := by
      rcases hΩ with ⟨-, h3⟩ | ⟨a, -, -, -, h6⟩ <;> omega
    have hΩb : orbitIn (oThreeWPre A) (Subgroup.zpowers b) ⊆ omegaA A := by
      rcases hΩ with ⟨hΩe, -⟩ | ⟨a, -, -, hΩe, -⟩
      · rw [hΩe]
      · rw [hΩe]
        exact Set.subset_union_left
    have hbd : b ∉ Subgroup.zpowers d := Proof152ResW.not_mem_zpowers_symm hA hb1 hdA hdb
    have horb : ∀ x : G, x ∈ A → x ∉ Subgroup.zpowers d →
        orbitIn (oThreeWPre A) (Subgroup.zpowers x) ⊆ omegaA A →
        orbitIn (oThreeWPre A) (Subgroup.zpowers x) ⊆
          {F : Subgroup G | F ≤ Subgroup.closure {x, d} ∧ Nat.card F = 3} \ {F | F ∉ omegaA A} := by
      intro x hxA hxd hΩx F hF
      obtain ⟨π, hπ, rfl⟩ := hF
      have hx1 : x ≠ 1 := fun h1 => hxd (h1 ▸ Subgroup.one_mem _)
      have hπx := Ronan152SL25.conj_mem_closure_of_ncard_lt hA hdA hd1 hxA hxd hWd hPi hPi9 hΩ9
        hΩx hπ
      refine ⟨⟨?_, ?_⟩, fun hFΩ => hFΩ (hΩx ⟨π, hπ, rfl⟩)⟩
      · rw [MonoidHom.map_zpowers]
        exact Subgroup.zpowers_le.mpr hπx
      · rw [Subgroup.card_map_of_injective (MulAut.conj π).injective,
          Proof152WE.card_zpowers_eq_three hA hxA hx1]
    have hBcl : Subgroup.closure ({b, d} : Set G) = B := hc.1.symm
    have hB9 : Nat.card B = 9 := by
      have h1 := hB.2
      rw [hA.2] at h1
      omega
    have hTb : ({F : Subgroup G | F ≤ B ∧ Nat.card F = 3} \ {F | F ∉ omegaA A}).ncard ≤ 2 := by
      have hsub : ({F : Subgroup G | F ≤ B ∧ Nat.card F = 3} \ {F | F ∉ omegaA A}) ⊆
          {F : Subgroup G | F ≤ B ∧ Nat.card F = 3} \
            {Subgroup.zpowers d₀, Subgroup.zpowers y} := by
        rintro F ⟨hF, hFΩ⟩
        refine ⟨hF, ?_⟩
        rintro (rfl | rfl)
        · exact hFΩ hd₀Ω
        · exact hFΩ hyΩ
      have hpair : ({Subgroup.zpowers d₀, Subgroup.zpowers y} : Set (Subgroup G)) ⊆
          {F : Subgroup G | F ≤ B ∧ Nat.card F = 3} := by
        rintro F (rfl | rfl)
        · exact ⟨Subgroup.zpowers_le.mpr hd₀B, hd₀3⟩
        · exact ⟨Subgroup.zpowers_le.mpr hyB, hy3⟩
      have h1 := Set.ncard_le_ncard hsub
      rw [Set.ncard_diff hpair, Set.ncard_pair hyne] at h1
      have h2 := ncard_subgroups_card_three_le_four hB9
      omega
    have hOb : (orbitIn (oThreeWPre A) (Subgroup.zpowers b)).ncard ≤ 2 := by
      have h1 := horb b hbA hbd hΩb
      rw [hBcl] at h1
      exact (Set.ncard_le_ncard h1).trans hTb
    rcases hΩ with ⟨hΩe, h3⟩ | ⟨a, haA, had, hΩe, h6⟩
    ·
      rw [hΩe] at h3
      omega
    ·
      have hΩa : orbitIn (oThreeWPre A) (Subgroup.zpowers a) ⊆ omegaA A := by
        rw [hΩe]
        exact Set.subset_union_right
      have ha1 : a ≠ 1 := fun h1 => had (h1 ▸ Subgroup.one_mem _)
      have hda : d ∉ Subgroup.zpowers a := Proof152ResW.not_mem_zpowers_symm hA hd1 haA
        (fun h' => had h')
      have hHa := Main148.isHyperplane_closure_pair148 hA haA hdA ha1 hda
      have hHa9 : Nat.card (Subgroup.closure ({a, d} : Set G)) = 9 := by
        have h1 := hHa.2
        rw [hA.2] at h1
        omega
      have hTa : ({F : Subgroup G | F ≤ Subgroup.closure {a, d} ∧ Nat.card F = 3} \
          {F | F ∉ omegaA A}).ncard ≤ 3 := by
        have hsub : ({F : Subgroup G | F ≤ Subgroup.closure {a, d} ∧ Nat.card F = 3} \
            {F | F ∉ omegaA A}) ⊆
            {F : Subgroup G | F ≤ Subgroup.closure {a, d} ∧ Nat.card F = 3} \
              {Subgroup.zpowers d} := by
          rintro F ⟨hF, hFΩ⟩
          refine ⟨hF, ?_⟩
          rintro rfl
          exact hFΩ hdΩ
        have hone : ({Subgroup.zpowers d} : Set (Subgroup G)) ⊆
            {F : Subgroup G | F ≤ Subgroup.closure {a, d} ∧ Nat.card F = 3} := by
          rintro F rfl
          exact ⟨Subgroup.zpowers_le.mpr (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)),
            Proof152WE.card_zpowers_eq_three hA hdA hd1⟩
        have h1 := Set.ncard_le_ncard hsub
        rw [Set.ncard_diff hone, Set.ncard_singleton] at h1
        have h2 := ncard_subgroups_card_three_le_four hHa9
        omega
      have hOa : (orbitIn (oThreeWPre A) (Subgroup.zpowers a)).ncard ≤ 3 :=
        (Set.ncard_le_ncard (horb a haA had hΩa)).trans hTa
      have hU := Set.ncard_union_le (orbitIn (oThreeWPre A) (Subgroup.zpowers b))
        (orbitIn (oThreeWPre A) (Subgroup.zpowers a))
      rw [← hΩe] at hU
      omega
  ·
    have h1 := Ronan152SL25.zpowers_eq_of_ncard_twelve h134 h48 h h12 hyA hy1 hyΩ hB hc
    have h2 := Ronan152SL25.zpowers_eq_of_ncard_twelve h134 h48 h h12 hd₀A hd₀1 hd₀Ω hB hc
    exact hyne (h2.trans h1.symm)

theorem false_of_le_centralizer_of_mem_omegaA
    (h142 : Item142AllS14)
    {A L : Subgroup G} {c : G}
    (h : Sec15R G A c L) (hHJ : AllPointsHJ A) {M W : Subgroup G}
    (hctx : Ctx152J A (lB A) M W) {B : Subgroup G} (hB : IsHyperplane A B)
    (hcent : Late.sectionCentralizer A W ((aschbacherSolvableCore 3 ↥W).map W.subtype) =
      (B : Set G))
    {y d₀ : G} (hyB : y ∈ B) (hd₀B : d₀ ∈ B) (hy1 : y ≠ 1) (hd₀y : d₀ ∉ Subgroup.zpowers y)
    (hyΩ : Subgroup.zpowers y ∈ omegaA A) {p : ℕ} {P : Subgroup G} (hP : PData152 A W p P)
    (hp3 : p ≠ 3) (hPy : P ≤ Subgroup.centralizer ({y} : Set G)) : False := by
  obtain ⟨Ly, hLy, hJy⟩ := hHJ y hyΩ
  have hRy : Sec15R G A y Ly := Sec16.sec15R_of_point h hyΩ hLy
  have hDy := hRy.toSec13Data
  have hLytop : Ly ≠ ⊤ := fun htop => Sec6.centralizer_ne_top_of_ne_one hRy.toTheoremFourHyp
    hDy.ne_one (top_le_iff.mp (htop ▸ hDy.le_centralizer))
  have hperf := Sec6.isPerfect_of_mem_thetaComponentsAt hDy.mem_thetaComponentsAt
  obtain ⟨eJ⟩ := Sec12.gap128OTwoHJ ↥Ly (hRy.toTheoremFourHyp.sectionFourHyp hLytop) hperf hJy
  have hθL : IsPGroup 2 (aschbacherSolvableCore 3 ↥Ly) := by
    rw [Ronan152SL25.theta_eq_pCore_two_of_j2 eJ]
    exact CFSG.pCore_isPGroup
  have hBeq := eq_closure_pair_of_mem h.isE27 hB hyB hd₀B hy1 hd₀y
  have hcent' : Late.sectionCentralizer A W ((aschbacherSolvableCore 3 ↥W).map W.subtype) =
      (Subgroup.closure {y, d₀} : Set G) := by
    rw [hcent, ← hBeq]
  exact Ronan152SL25.not_le_centralizer_ofJ h142 h.toSec14Std hctx hyΩ hLy hJy hθL (hB.1 hd₀B)
    hcent' hP hp3 hPy

end Ronan155W315

namespace Ronan155W315

theorem le_centralizer_of_mem_x {A M X P : Subgroup G} {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hPW : P ≤ w155 A M X) (hPp : IsPGroup p P) {y : G} (hyX : y ∈ X)
    (hyP : y ∈ Subgroup.normalizer (P : Set G)) :
    P ≤ Subgroup.centralizer ({y} : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  intro π hπ
  have hπU : π ∈ u155 A M X := Proof155Wx.w155_le_u155 A M X (hPW hπ)
  have hc2 : ⁅y, π⁆ ∈ CFSG.Open.pCoreOf 2 X := hπU.2.2.2 y hyX
  have hcP : ⁅y, π⁆ ∈ P := by
    rw [commutatorElement_def]
    exact P.mul_mem ((Subgroup.mem_normalizer_iff.mp hyP π).mp hπ) (P.inv_mem hπ)
  have hdisj : Disjoint P (CFSG.Open.pCoreOf 2 X) :=
    IsPGroup.disjoint_of_ne p 2 hp2 P _ hPp (CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 X)
  have h1 : ⁅y, π⁆ = 1 := Subgroup.disjoint_def.mp hdisj hcP hc2
  rw [commutatorElement_eq_one_iff_mul_comm] at h1
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact h1.symm

end Ronan155W315

end CFSG.RankThree.PartTwo.Sec15

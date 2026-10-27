module

public import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofCases
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProof
import CFSG.RankThree.PartTwo.Sec15.Item158CartanProofPair
import CFSG.RankThree.PartTwo.Sec13.Item131Facts
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item13K410
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.RankThree.PartTwo.Sec14.Item142ResProofPGL
import CFSG.RankThree.PartTwo.Sec16.Item1613StepsProofFix
import CFSG.RankThree.PartTwo.Sec19.Step1914Tri

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck158

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec15.Proof158Cartan

variable {G : Type} [Group G] [Finite G]

theorem exists_split_of_card_nine {A L P : Subgroup G} {c : G} (hR : Sec15R G A c L)
    (hAP : A ≤ P) (hcL : c ∉ L) (h9AL : Nat.card (A ⊓ L : Subgroup G) = 9)
    (hΩ : A ≠ omegaOneThree P) :
    ∃ F : Subgroup G, F ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧
      F = Subgroup.zpowers c ⊔ (F ⊓ L) ∧ Nat.card (F ⊓ L : Subgroup G) = 9 ∧
      (∀ a ∈ F, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c) ∧
      F ≠ omegaOneThree P := by
  have hD := hR.toSec13Data
  have hA := hD.isElemAbelian
  have hA27 := hD.card_eq
  have hcA := hD.mem_A
  refine ⟨A, hAP, hA, hA27,
    Sec19.Step1914TriProof.eq_zpowers_sup_of_nine_le ⟨hA, hA27⟩ hcA hcL (by rw [h9AL]), h9AL,
    ?_, hΩ⟩
  intro a haA haC
  have h1 := hD.mem_lA.2.2.1
  rw [sectionCentralizer_eq_inf hD.le_normalizer] at h1
  have h2 : a ∈ ((A ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) := ⟨haA, haC⟩
  rw [h1] at h2
  exact h2

section Certs


theorem exists_split_of_pgl (h134 : Item134) (h48 : Sec4.Item4_8) (h148 : Item148R)
    {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {p e : ℕ} [Fact p.Prime] (he : 1 ≤ e)
    (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e) {Y : Subgroup G}
    (hmeet : MeetsY4 A (lB A) L Y) {P : Subgroup G} (hAP : A ≤ P)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)))
    (hcL : c ∉ L) (hPGL : Sec8.IsZ3PGLThreePi (lBarA c L A))
    (hx : ∃ x ∈ A, Sec4.InducesTypeOn L x 3) :
    ∃ F : Subgroup G, F ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧
      F = Subgroup.zpowers c ⊔ (F ⊓ L) ∧ Nat.card (F ⊓ L : Subgroup G) = 9 ∧
      (∀ a ∈ F, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c) ∧
      F ≠ omegaOneThree P := by
  have hD := hR.toSec13Data
  have hA := hD.isElemAbelian
  have hcA := hD.mem_A
  have hc3 : c ^ 3 = 1 := hA.2 c hcA
  have hc1 : c ≠ 1 := fun h1 => hcL (h1 ▸ L.one_mem)
  have hLc : ∀ l ∈ L, l * c = c * l := fun l hl =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hl)
  obtain ⟨X, hX4, hXLY⟩ := hmeet
  obtain ⟨B, hBX, hB, hB9⟩ := step158InnerRank_of_route h134 h48 h148 G A c L hR p e he hL3 hPGL
    hx X hX4 (hXLY.trans inf_le_left)
  have h3L : 3 ∣ Nat.card L :=
    (show 3 ∣ 9 by norm_num).trans (hB9 ▸ Subgroup.card_dvd_of_le (hBX.trans
      (hXLY.trans inf_le_left)))
  have hP3 : IsPGroup 3 P := hP.isPGroup
  have hB3 : IsPGroup 3 B := IsPGroup.of_card (n := 2) (by rw [hB9]; norm_num)
  have hBK : B ≤ Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓
      Subgroup.normalizer (Y : Set G) := by
    intro b hb
    have hbc : Commute b c := hLc b (hXLY (hBX hb)).1
    refine Subgroup.mem_inf.mpr ⟨Subgroup.centralizer_le_normalizer _ ?_,
      Subgroup.le_normalizer (hXLY (hBX hb)).2⟩
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hh
    exact (hbc.zpow_right k).eq.symm
  obtain ⟨k, hkK, hBk⟩ := Proof158Inner.exists_conj_le_of_isSylowOf hP hB3 hBK
  set D := B.map (MulAut.conj k).toMonoidHom with hDdef
  have hDL : D ≤ L := by
    rintro _ ⟨b, hb, rfl⟩
    have hkN : k ∈ Subgroup.normalizer (L : Set G) :=
      Sec16.normalizer_zpowers_le_normalizer_L hR h3L hkK.1
    exact (Subgroup.mem_normalizer_iff.mp hkN b).mp (hXLY (hBX hb)).1
  have hDe : CFSG.Assembly.IsElemAbelian 3 D := isElemAbelian_map hB _
  have hD9 : Nat.card D = 9 := by
    rw [hDdef, Subgroup.card_map_of_injective (MulAut.conj k).injective, hB9]
  have hDP : D ≤ P := hBk
  have hDc : ∀ d ∈ D, d * c = c * d := fun d hd => hLc d (hDL hd)
  have hcD : ∀ t ∈ D, c * t * c⁻¹ ∈ D := fun t ht => by
    rw [← hDc t ht, mul_inv_cancel_right]
    exact ht
  set F := D ⊔ Subgroup.zpowers c with hFdef
  have hF : CFSG.Assembly.IsElemAbelian 3 F := isElemAbelian_sup_zpowers hDe hc3 hDc
  have hFP : F ≤ P := sup_le hDP (Subgroup.zpowers_le.mpr (hAP hcA))
  have hF27 : Nat.card F = 27 := by
    have hcN : Subgroup.zpowers c ≤ Subgroup.normalizer (D : Set G) := by
      rw [Subgroup.zpowers_le]
      refine Subgroup.centralizer_le_normalizer _ ?_
      rw [Subgroup.mem_centralizer_iff]
      exact hDc
    have h1 := Sec6.card_sup_mul_card_inf hcN
    have hinf : Subgroup.zpowers c ⊓ D = ⊥ := by
      rw [eq_bot_iff]
      intro g hg
      have h2 : g ∈ Subgroup.zpowers c ⊓ L := ⟨hg.1, hDL hg.2⟩
      rw [zpowers_inf_eq_bot hc3 hcL] at h2
      exact h2
    rw [hinf, Subgroup.card_bot, mul_one, card_zpowers_of_pow_three hc3 hc1, hD9] at h1
    rw [hFdef, sup_comm]
    omega
  have hFL : F ⊓ L = D := by
    refine le_antisymm (fun g hg => ?_) (le_inf le_sup_left hDL)
    obtain ⟨t, htD, m, -, hgt⟩ := exists_mul_pow_of_mem_sup hc3 hcD hg.1
    have hcm : c ^ m ∈ L := by
      have h1 : c ^ m = t⁻¹ * g := by rw [hgt]; group
      rw [h1]
      exact L.mul_mem (L.inv_mem (hDL htD)) hg.2
    have hcm1 : c ^ m = 1 := by
      have h2 : c ^ m ∈ Subgroup.zpowers c ⊓ L := ⟨Subgroup.npow_mem_zpowers c m, hcm⟩
      rw [zpowers_inf_eq_bot hc3 hcL] at h2
      exact h2
    rw [hgt, hcm1, mul_one]
    exact htD
  have hFeq : F = Subgroup.zpowers c ⊔ (F ⊓ L) := by
    rw [hFL, hFdef, sup_comm]
  have hZ := (facts_of_isZ3PGLThreePi hD hPGL).2.1
  have hsecF : ∀ a ∈ F, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c := by
    intro a haF haC
    obtain ⟨t, htD, m, -, rfl⟩ := exists_mul_pow_of_mem_sup hc3 hcD haF
    have htL : t ∈ L := hDL htD
    have hcmT : c ^ m ∈ Sec4.thetaQuotCentralizer L := by
      have hcN : c ^ m ∈ Subgroup.normalizer (L : Set G) :=
        Subgroup.pow_mem _ (hD.le_normalizer hcA) m
      have h1 := actBar_eq_one_of_commute hcN fun l hl => (Commute.pow_right (hLc l hl) m).eq
      exact (actBar_eq_one_iff ⟨c ^ m, hcN⟩).mp h1
    have htT : t ∈ Sec4.thetaQuotCentralizer L := by
      have h1 : t = (t * c ^ m) * (c ^ m)⁻¹ := by group
      rw [h1]
      exact Subgroup.mul_mem _ haC (Subgroup.inv_mem _ hcmT)
    obtain ⟨-, htθ⟩ := Sec6.mem_thetaQuotCentralizer_iff.mp htT
    have hcen : (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥L) ⟨t, htL⟩) ∈
        Subgroup.center (↥L ⧸ aschbacherSolvableCore 3 ↥L) := by
      rw [Subgroup.mem_center_iff]
      intro z
      induction z using QuotientGroup.induction_on with
      | H l =>
        have h1 := htθ l l.2
        obtain ⟨u, hu, hul⟩ := h1
        rw [QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul,
          QuotientGroup.eq]
        have hu' : (l : G)⁻¹ * (t * l * t⁻¹) = (u : G) := hul.symm
        have h2 : (⟨l, l.2⟩ * ⟨t, htL⟩ : ↥L)⁻¹ * (⟨t, htL⟩ * ⟨l, l.2⟩) =
            ⟨t, htL⟩⁻¹ * u * ⟨t, htL⟩ := by
          apply Subtype.ext
          simp only [Subgroup.coe_mul, Subgroup.coe_inv]
          rw [← hu']
          group
        rw [h2]
        have h3 := (aschbacherSolvableCore_normal 3 ↥L).conj_mem _ hu (⟨t, htL⟩⁻¹)
        rwa [inv_inv] at h3
    rw [hZ, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
    have ht1 : t = 1 := eq_one_of_mem_theta_of_isPGroup (hP3.to_le hDP) htD
      ⟨⟨t, htL⟩, hcen, rfl⟩
    rw [ht1, one_mul]
    exact Subgroup.npow_mem_zpowers c m
  obtain ⟨x, hxA, hx3⟩ := hx
  have hΩF : F ≠ omegaOneThree P := by
    intro hFΩ
    have hxΩ : x ∈ omegaOneThree P := Subgroup.subset_closure ⟨hAP hxA, hA.2 x hxA⟩
    rw [← hFΩ] at hxΩ
    obtain ⟨t, htD, m, -, hxt⟩ := exists_mul_pow_of_mem_sup hc3 hcD hxΩ
    have hcN : c ∈ Subgroup.normalizer (L : Set G) := hD.le_normalizer hcA
    have hx' := Proof142Res.inducesTypeOn_mul_of_eq_one hx3
      (Subgroup.zpow_mem _ hcN (-(m : ℤ)))
      (actBar_zpow_eq_one hLc (-(m : ℤ)) (Subgroup.zpow_mem _ hcN (-(m : ℤ))))
    apply Sec16.Proof1613Fix.not_mem_of_inducesTypeOn_three hD.mem_thetaComponentsAt hx'
    have h1 : x * c ^ (-(m : ℤ)) = t := by
      rw [hxt, zpow_neg, zpow_natCast]
      group
    rw [h1]
    exact hDL htD
  exact ⟨F, hFP, hF, hF27, hFeq, by rw [hFL, hD9], hsecF, hΩF⟩

theorem exists_split_pair (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h148 : Item148R) {A L : Subgroup G} {c : G} (hR : Sec15R G A c L) {p e : ℕ} [Fact p.Prime]
    (he : 1 ≤ e) (hL3 : Sec4.IsoLThreePi (↥L ⧸ aschbacherSolvableCore 3 ↥L) p e)
    {Y : Subgroup G} (_hY : Y ∈ scriptY0 A (lB A)) (hmeet : MeetsY4 A (lB A) L Y)
    {P : Subgroup G} (hAP : A ≤ P)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P
      (Subgroup.normalizer (Subgroup.zpowers c : Set G) ⊓ Subgroup.normalizer (Y : Set G)))
    (hΩ : A ≠ omegaOneThree P) :
    ∃ F : Subgroup G, F ≤ P ∧ CFSG.Assembly.IsElemAbelian 3 F ∧ Nat.card F = 27 ∧
      F = Subgroup.zpowers c ⊔ (F ⊓ L) ∧ Nat.card (F ⊓ L : Subgroup G) = 9 ∧
      (∀ a ∈ F, a ∈ Sec4.thetaQuotCentralizer L → a ∈ Subgroup.zpowers c) ∧
      F ≠ omegaOneThree P := by
  have hD := hR.toSec13Data
  rcases cases131 h131 sporadicModels131 slTwoCenter hD with
      ⟨hcL, h9AL, -, -⟩ | ⟨hcL, h9AL, -, -⟩ | ⟨hcL, hPGL, -, hx⟩ | ⟨hcL, -⟩
  · exact exists_split_of_card_nine hR hAP hcL h9AL hΩ
  · exact exists_split_of_card_nine hR hAP hcL h9AL hΩ
  · exact exists_split_of_pgl h134 h48 h148 hR he hL3 hmeet hAP hP hcL hPGL hx
  · exact (hR.hypS.2.2 c hR.zpowers_mem_omegaA L hR.mem_lA hcL).elim

end Certs

end CFSG.RankThree.PartTwo.Sec15.Liebeck158

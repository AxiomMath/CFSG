module

public import CFSG.RankThree.PartTwo.Sec14.Item148PointProofHJ
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofA6
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
import CFSG.RankThree.PartTwo.Sec14.Concl143Std
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.Sporadic.ON

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement Pointwise

namespace Item148PtRes

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem thetaComponentsAt_eq_of_zpowers_eq {b d : G}
    (h : Subgroup.zpowers b = Subgroup.zpowers d) :
    thetaComponentsAt 3 b = thetaComponentsAt 3 d := by
  have hC : Subgroup.centralizer ({b} : Set G) = Subgroup.centralizer ({d} : Set G) :=
    centralizer_singleton_eq_of_zpowers_eq h
  have key : ∀ C₁ C₂ : Subgroup G, C₁ = C₂ →
      (fun L : Subgroup ↥C₁ => L.map C₁.subtype) '' thetaComponents 3 ↥C₁ =
        (fun L : Subgroup ↥C₂ => L.map C₂.subtype) '' thetaComponents 3 ↥C₂ := by
    rintro _ _ rfl
    rfl
  exact key _ _ hC


theorem false_of_ne_member {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    {B : Subgroup G} (hB : IsHyperplane A B) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A))
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hQb : ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) {b' : G}
    {Lb : Subgroup G} (hb'Ω : Subgroup.zpowers b' ∈ omegaA A) (hLb : Lb ∈ lA A b')
    (hJ2 : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    {X : Subgroup G}
    (hCX : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G))
    (hX : X ∈ thetaComponentsAt 3 b)
    (hQX : Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 b) (hKX : K ≠ X) (hALK : A ⊓ Lb ≤ K) : False := by
  have hD := h.toSec13Data
  have hbA : b ∈ A := hB.1 hb
  set Cb := Subgroup.centralizer ({b} : Set G) with hCb
  set N := pPrimeCoreOf 3 Cb with hN
  have hAab : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy => hD.commute hx hy
  have hAC : A ≤ Cb := fun x hx =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAab x hx b hbA)
  have hCbN : Cb ≤ Subgroup.normalizer (N : Set G) := le_normalizer_pPrimeCoreOf 3 Cb
  have hN3 : Nat.Coprime 3 (Nat.card N) := coprime_card_pPrimeCoreOf 3 Cb
  have hXCb : X ≤ Cb := le_centralizer_of_mem_thetaComponentsAt hX
  have hXN : X ≤ Subgroup.normalizer (N : Set G) := hXCb.trans hCbN
  have hQYC : Q ≤ Y ⊓ Cb := le_inf (hQY.trans inf_le_left)
    (hQY.trans (inf_le_right.trans (Subgroup.centralizer_le (Set.singleton_subset_iff.mpr hb))))
  have hcontra : Q ≤ N → False := fun hQN =>
    hQb ((le_inf hQN hQYC).trans (inf_le_pPrimeCoreOf148 (inf_le_right.trans hCbN) hN3))
  have hcomm : ⁅K, X⁆ ≤ N :=
    (Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK hX hKX).trans
      (inSubgroup_theta_le_pPrimeCoreOf Cb)
  have hw : ∀ w ∈ A ⊓ Lb, ∀ m ∈ N ⊔ X, ⁅m, w⁆ ∈ N := by
    intro w hw m hm
    refine commutator_mem_of_mem_sup hXN (hCbN (hAC hw.1)) (fun x hx => ?_) hm
    have h1 : ⁅x, w⁆ ∈ ⁅X, K⁆ := Subgroup.commutator_mem_commutator hx (hALK hw)
    rw [Subgroup.commutator_comm] at h1
    exact hcomm h1
  have hdata : Sec13Data G A b' Lb := { hD with zpowers_mem_omegaA := hb'Ω, mem_lA := hLb }
  obtain ⟨-, h9, -⟩ := j2_point_facts hdata hJ2
  obtain ⟨u, huB, hub⟩ := exists_mem_not_mem_zpowers hD.card_eq hD.isElemAbelian.2 hB hbA
  have huA : u ∈ A := hB.1 huB
  have hu3 : u ^ 3 = 1 := hD.isElemAbelian.2 u huA
  have hu1 : u ≠ 1 := fun h1 => hub (h1 ▸ one_mem _)
  have hne : Subgroup.zpowers b ≠ Subgroup.zpowers u := fun he =>
    hub (he ▸ Subgroup.mem_zpowers u)
  have huCb : u ∈ Cb := hAC huA
  by_cases huL : u ∈ Lb
  ·
    have hCB : Cb ⊓ Subgroup.centralizer ({u} : Set G) ≤ Subgroup.centralizer (B : Set G) :=
      Item148HJ.centralizer_inf_le_of_mem_hyperplane hD.isElemAbelian hD.card_eq hB hb huB hb1
        hu1 hne
    have hR : Y ⊓ Cb ⊓ Subgroup.centralizer ({u} : Set G) ≤
        Subgroup.normalizer (pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) : Set G) := by
      intro g hg
      obtain ⟨hgYC, hgu⟩ := Subgroup.mem_inf.mp hg
      obtain ⟨hgY, hgb⟩ := Subgroup.mem_inf.mp hgYC
      exact le_normalizer_pPrimeCoreOf 3 _
        (Subgroup.mem_inf.mpr ⟨hgY, hCB (Subgroup.mem_inf.mpr ⟨hgb, hgu⟩)⟩)
    have hQR : Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer (B : Set G)) :=
      (le_sSup ⟨hQ, hQY⟩ : Q ≤ deltaZero A (lB A) (Y ⊓ Subgroup.centralizer (B : Set G))).trans
        (hYB B hB)
    exact hQb (le_pPrimeCoreOf_of_trivial_on hu3 le_sup_left le_rfl
      (sup_le (pPrimeCoreOf_le 3 Cb) hXCb) Subgroup.le_normalizer hCX (hCX huCb) (hY.2 huA)
      huCb (hw u ⟨huA, huL⟩) hR (coprime_card_pPrimeCoreOf 3 _) hQR hQYC hQX)
  ·
    apply hcontra
    have hH : IsHyperplane A (A ⊓ Lb) := ⟨inf_le_left, by rw [hD.card_eq, h9]⟩
    have hAeq : (A ⊓ Lb) ⊔ Subgroup.zpowers u = A :=
      Item148HJ.sup_zpowers_eq_of_isHyperplane hH huA (fun h1 => huL h1.2)
    have hZN : Subgroup.zpowers u ≤ Subgroup.normalizer ((A ⊓ Lb : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_le, Subgroup.mem_normalizer_iff]
      intro x
      constructor
      · intro hx
        rw [hAab u huA x hx.1, mul_assoc, mul_inv_cancel, mul_one]
        exact hx
      · intro hx
        have h1 : u⁻¹ * (u * x * u⁻¹) * u = u * x * u⁻¹ := by
          rw [mul_assoc, hAab _ hx.1 u huA, ← mul_assoc, inv_mul_cancel, one_mul]
        have h2 : x = u⁻¹ * (u * x * u⁻¹) * u := by group
        rw [h2, h1]
        exact hx
    rw [hQ.2, Subgroup.commutator_le]
    intro q hq a ha
    rw [← hAeq] at ha
    have ha' : a ∈ (((A ⊓ Lb : Subgroup G) : Set G) * (Subgroup.zpowers u : Set G)) := by
      rw [← Subgroup.coe_mul_of_right_le_normalizer_left _ _ hZN]
      exact ha
    obtain ⟨w, hwAL, y, hy, rfl⟩ := ha'
    have hqu : u * q = q * u :=
      (Subgroup.mem_centralizer_iff.mp ((hQY hq).2) u huB).symm.symm
    have hyq : y * q = q * y := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact (Commute.zpow_left hqu k)
    have hyq' : y * q⁻¹ = q⁻¹ * y := by
      calc y * q⁻¹ = q⁻¹ * (q * y) * q⁻¹ := by group
        _ = q⁻¹ * (y * q) * q⁻¹ := by rw [hyq]
        _ = q⁻¹ * y := by group
    have h1 : ⁅q, w * y⁆ = ⁅q, w⁆ := by
      simp only [commutatorElement_def]
      calc q * (w * y) * q⁻¹ * (w * y)⁻¹ = q * w * (y * q⁻¹) * y⁻¹ * w⁻¹ := by group
        _ = q * w * (q⁻¹ * y) * y⁻¹ * w⁻¹ := by rw [hyq']
        _ = q * w * q⁻¹ * w⁻¹ := by group
    rw [h1]
    exact hw w hwAL q (hQX hq)

theorem exists_hj_point_of_on (h134 : Item134)
    (h48 : Sec4.Item4_8) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {Y : Subgroup G} (hY : Y ∈ scriptY A)
    (hYB : ∀ B' : Subgroup G, IsHyperplane A B' → YBOne A (lB A) Y B')
    {B : Subgroup G} (hB : IsHyperplane A B) {Q : Subgroup G} (hQ : Q ∈ scriptQZero A (lB A))
    (hQY : Q ≤ Y ⊓ Subgroup.centralizer (B : Set G)) {b : G} (hb : b ∈ B) (hb1 : b ≠ 1)
    (hbΩ : Subgroup.zpowers b ∉ omegaA A)
    (hQb : ¬ Q ≤ pPrimeCoreOf 3 (Y ⊓ Subgroup.centralizer ({b} : Set G))) {b' d : G}
    {Lb : Subgroup G} (hb'Ω : Subgroup.zpowers b' ∈ omegaA A) (hLb : Lb ∈ lA A b')
    (hJ2 : Nonempty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn Lb d)
    (hbd : Subgroup.zpowers b = Subgroup.zpowers d) {X : Subgroup G}
    (hCX : Subgroup.centralizer ({b} : Set G) ≤ Subgroup.normalizer
      ((pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X : Subgroup G) : Set G))
    (hX : X ∈ thetaComponentsAt 3 b)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X) CFSG.Blueprint.NativeSporadic.ON)
    (hQX : Q ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({b} : Set G)) ⊔ X) :
    ∃ (c' : G) (L' : Subgroup G), Subgroup.zpowers c' ∈ omegaA A ∧ c' ∈ B ∧
      L' ∈ lA A c' ∧
      Nonempty (↥L' ⧸ aschbacherSolvableCore 3 ↥L' ≃* CFSG.Blueprint.NativeSporadic.J2) ∧
      IsThreeCentralIn L' b := by
  have hD := h.toSec13Data
  have hA : Late.IsE27 A := h.isE27
  have hbd' : b ∈ Subgroup.zpowers d := hbd ▸ Subgroup.mem_zpowers b
  by_cases hb'B : b' ∈ B
  · exact ⟨b', Lb, hb'Ω, hb'B, hLb, hJ2, isThreeCentralIn_of_mem_zpowers hdc hbd'⟩
  have hb'A : b' ∈ A := (zpowers_mem_omegaA_iff.mp hb'Ω).1
  have hb'1 : b' ≠ 1 := by
    intro h1
    have h3 := (zpowers_mem_omegaA_iff.mp hb'Ω).2.1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    exact absurd h3 (by norm_num)
  have hdc' := hdc
  obtain ⟨hdL, S, hdS, hSd⟩ := hdc'
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb) Nat.prime_three
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ2 hdL hd1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ2 hdL hd1
    ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hRK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hb'A hdA hb'1 hLb.1 hJq
  have hdata : Sec13Data G A b' Lb := { hD with zpowers_mem_omegaA := hb'Ω, mem_lA := hLb }
  have hKb : K ∈ thetaComponentsAt 3 b := (thetaComponentsAt_eq_of_zpowers_eq hbd) ▸ hK
  have hπbc : ∃ P : Sylow 3 (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb),
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb) ⟨d, hdL⟩ ∈ (P : Subgroup _) ∧
        (P : Subgroup _) ≤ Subgroup.centralizer
          {QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb) ⟨d, hdL⟩} := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥Lb)), ?_,
      ?_⟩
    · change _ ∈ (S : Subgroup ↥Lb).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb))
      exact ⟨_, hdS, rfl⟩
    · change (S : Subgroup ↥Lb).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb)) ≤ _
      rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp (hSd hs)]
  have hALK : A ⊓ Lb ≤ K :=
    (inf_le_residual_of_central hA.1 hJ2 hdA hdL hd1 hπbc).trans hRK
  rcases h134 G A b' Lb hdata hJ2 d hdA hd1 ⟨_, hS⟩ K hK hRK with
    ⟨-, hKA6, -⟩ | ⟨-, hKA6, -⟩ | ⟨-, hWd, hΩ, hΩ12⟩
  ·
    exfalso
    refine false_of_ne_member h hY hYB hB hQ hQY hb hb1 hQb hb'Ω hLb hJ2 hCX hX hQX hKb ?_ hALK
    rintro rfl
    obtain ⟨-, ⟨e₁⟩⟩ := hKA6
    obtain ⟨-, ⟨e₂⟩⟩ := hT
    have h1 := Nat.card_congr (e₁.symm.trans e₂).toEquiv
    rw [Item148HJ.card_alternatingGroup_six, CFSG.Sporadic.ON.card_ON] at h1
    norm_num at h1
  ·
    exfalso
    refine false_of_ne_member h hY hYB hB hQ hQY hb hb1 hQb hb'Ω hLb hJ2 hCX hX hQX hKb ?_ hALK
    rintro rfl
    obtain ⟨-, ⟨e₁⟩⟩ := hKA6
    obtain ⟨-, ⟨e₂⟩⟩ := hT
    have h1 := Nat.card_congr (e₁.symm.trans e₂).toEquiv
    rw [Item148HJ.card_alternatingGroup_six, CFSG.Sporadic.ON.card_ON] at h1
    norm_num at h1
  ·
    obtain ⟨u, huB, hud⟩ := exists_mem_not_mem_zpowers hD.card_eq hD.isElemAbelian.2 hB hdA
    have huA : u ∈ A := hB.1 huB
    have hu1 : u ≠ 1 := fun h1 => hud (h1 ▸ one_mem _)
    set T := {F : Subgroup G | F ≤ A ∧ Nat.card F = 3} with hTdef
    have hΩT : omegaA A ⊆ T := fun F hF => ⟨hF.1, hF.2.1⟩
    have hdT : Subgroup.zpowers d ∈ T :=
      ⟨Subgroup.zpowers_le.mpr hdA, card_zpowers_eq_three hA.1 hdA hd1⟩
    have huT : Subgroup.zpowers u ∈ T :=
      ⟨Subgroup.zpowers_le.mpr huA, card_zpowers_eq_three hA.1 huA hu1⟩
    have hdu : Subgroup.zpowers d ≠ Subgroup.zpowers u := fun he =>
      hud (he ▸ Subgroup.mem_zpowers u)
    have hdΩ : Subgroup.zpowers d ∉ omegaA A := hbd ▸ hbΩ
    have huΩ : Subgroup.zpowers u ∈ omegaA A := by
      by_contra huΩ
      have hsub : omegaA A ⊆ T \ {Subgroup.zpowers d, Subgroup.zpowers u} := by
        intro F hF
        refine ⟨hΩT hF, ?_⟩
        rintro (rfl | rfl)
        · exact hdΩ hF
        · exact huΩ hF
      have hpair : ({Subgroup.zpowers d, Subgroup.zpowers u} : Set (Subgroup G)) ⊆ T := by
        rintro F (rfl | rfl)
        · exact hdT
        · exact huT
      have : Finite (Subgroup G) :=
        Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
      have h1 := Set.ncard_le_ncard hsub
      have h2 := Set.ncard_sdiff_add_ncard_of_subset hpair
      rw [Set.ncard_pair hdu] at h2
      have h3 := ncard_subgroups_card_three_le (A := A) hD.card_eq
      rw [← hTdef] at h3
      omega
    have huΩ' := huΩ
    rw [hΩ] at huΩ'
    obtain ⟨w, hw, hwu⟩ := huΩ'
    refine ⟨u, Lb.map (MulAut.conj w).toMonoidHom, huΩ, huB, ?_, ?_, ?_⟩
    · have h1 : Lb.map (MulAut.conj w).toMonoidHom ∈ lA A (w * b' * w⁻¹) :=
        (map_conj_mem_lA_iff hw).mpr hLb
      have h2 : Subgroup.zpowers (w * b' * w⁻¹) = Subgroup.zpowers u := by
        rw [hwu, MonoidHom.map_zpowers]
        rfl
      rwa [lA_eq_of_zpowers_eq h2] at h1
    · obtain ⟨φ⟩ := hJ2
      exact ⟨(quotThetaEquiv (Lb.equivMapOfInjective _ (MulAut.conj w).injective)).symm.trans φ⟩
    · have hc1 := isThreeCentralIn_map_conj hdc w
      have hwd : w * d * w⁻¹ ∈ Subgroup.zpowers d :=
        (Subgroup.mem_normalizer_iff.mp (hWd hw) d).mp (Subgroup.mem_zpowers d)
      have hzz : Subgroup.zpowers (w * d * w⁻¹) = Subgroup.zpowers d := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hwd) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers]
        exact (orderOf_injective (MulAut.conj w).toMonoidHom (MulAut.conj w).injective d).ge
      exact isThreeCentralIn_of_mem_zpowers hc1 (hzz ▸ hbd')

end Item148PtRes

theorem step148PointHJdONPoint_of
    (h134 : Item134) (h48 : Sec4.Item4_8) : Step148PointHJdONPoint := by
  intro G _ _ A c L h Y hY _ hYB B hB Q hQ hQY b hb hb1 hbΩ hQb b' d Lb hb'Ω hLb hJ2 hdA hd1
    hdc _ hbd X _ hCX hX hT hQX
  exact Or.inl (Item148PtRes.exists_hj_point_of_on h134 h48 h hY hYB hB hQ hQY hb hb1 hbΩ hQb
    hb'Ω hLb hJ2 hdA hd1 hdc hbd hCX hX hT hQX)

end CFSG.RankThree.PartTwo.Sec14

module

public import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofON
public import CFSG.RankThree.PartTwo.Sec14.Item14Res9ProofONModel
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofONPoint
import CFSG.RankThree.PartTwo.Sec14.Item148PtResProofTools
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofLB
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofA6
import CFSG.RankThree.PartTwo.Sec14.Item148MainProofKType
import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec13.OmegaNonempty
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.Sporadic.ON
public import CFSG.RankThree.PartTwo.Sec14.Item1411HJ
public import CFSG.RankThree.PartTwo.Sec14.Item148PointProofHJ
public import CFSG.Sporadic.ON.Simple

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

namespace Res9Fix

variable {G : Type} [Group G] [Finite G] {A X : Subgroup G} {a : G}

theorem Base.sig_eq_self_of_commutator_mem (hC : Base A a X) {g : G}
    (hg : g ∈ Subgroup.centralizer ({a} : Set G))
    (hgX : ∀ y ∈ X, ⁅g, y⁆ ∈ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)))
    (γ : ↥X ⧸ aschbacherSolvableCore 3 ↥X) : sig X g γ = γ := by
  obtain ⟨⟨y, hy⟩, rfl⟩ := QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥X) γ
  rw [sig_mk (hC.le_normalizer hg) hy, mk_eq_mk_iff]
  refine hC.inf_le_theta (Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
  · simpa only [commutatorElement_def] using hgX y hy
  · exact mul_mem ((Subgroup.mem_normalizer_iff.mp (hC.le_normalizer hg) y).mp hy) (inv_mem hy)

theorem Base.false_of_hyperplane_le (hC : Base A a X)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
      CFSG.Blueprint.NativeSporadic.ON)
    (hAmax : Maximal (fun B : Subgroup G => CFSG.Assembly.IsElemAbelian 3 B) A) (ha1 : a ≠ 1)
    (hX : X ∈ thetaComponentsAt 3 a) {K : Subgroup G} (hK : K ∈ thetaComponentsAt 3 a)
    (hKX : K ≠ X) {H : Subgroup G} (hH : IsHyperplane A H) (hHK : H ≤ K)
    {D : Subgroup G} (hD : IsHyperplane A D) (haD : a ∈ D)
    (hα : ∀ B' : Subgroup G, IsHyperplane A B' → a ∈ B' → B' ≠ D →
      ¬ ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) : False := by
  have hKXc : ⁅K, X⁆ ≤ pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) :=
    (Sec6.commutator_le_theta_of_ne_mem_thetaComponentsAt hK hX hKX).trans
      (inSubgroup_theta_le_pPrimeCoreOf _)
  have hall : ∀ δ ∈ H, ∀ γ, sig X δ γ = γ := fun δ hδ =>
    hC.sig_eq_self_of_commutator_mem (hC.le_centralizer (hH.1 hδ))
      (fun y hy => hKXc (Subgroup.commutator_mem_commutator (hHK hδ) hy))
  obtain ⟨δ₀, hδ₀D, γ₀, hγ₀⟩ := hC.exists_nontrivial hT hAmax ha1 hD haD hα
  have hAH : ¬ A ≤ H := fun hle => by
    have h1 := Subgroup.card_le_of_le hle
    have h2 := hH.2
    have h3 := hC.isE27.2
    omega
  obtain ⟨x, hxA, hxH⟩ := Set.not_subset.mp hAH
  have hAD := le_sup_zpowers_of_not_mem hC.isE27 hH hxA hxH
  by_cases hx : ∃ γ, sig X x γ ≠ γ
  · exact hC.false_of_trivial hT hAmax hH.1 hxA hAD hall hx
  · push Not at hx
    obtain ⟨i, hi⟩ := hC.exists_zpow_of_trivial hH.1 hxA hAD hall (hD.1 hδ₀D)
    exact hγ₀ ((hi γ₀).trans (zpow_apply_eq_of_apply_eq (hx γ₀) i))

theorem exists_isLBConfig_on
    (h134 : Item134)
    (h48 : Sec4.Item4_8) {L : Subgroup G} {c : G} (h : Sec14Std G A c L) (hC : Base A a X)
    (hT : Sec4.IsTripleCover (↥X ⧸ aschbacherSolvableCore 3 ↥X)
      CFSG.Blueprint.NativeSporadic.ON)
    (hX : X ∈ thetaComponentsAt 3 a) (ha1 : a ≠ 1) (hΩ : Subgroup.zpowers a ∉ omegaA A)
    {B : Subgroup G} {b d : G} {Lb : Subgroup G} (hB : IsHyperplane A B) (haB : a ∈ B)
    (hc : IsLBConfig A B b d Lb) {b' d' : G} {Lb' : Subgroup G}
    (hb'Ω : Subgroup.zpowers b' ∈ omegaA A) (hLb' : Lb' ∈ lA A b')
    (hJ2 : Nonempty (↥Lb' ⧸ aschbacherSolvableCore 3 ↥Lb' ≃* CFSG.Blueprint.NativeSporadic.J2))
    (hd'A : d' ∈ A) (hd'1 : d' ≠ 1) (hd'3 : IsThreeCentralIn Lb' d')
    (hda : Subgroup.zpowers a = Subgroup.zpowers d')
    {D : Subgroup G} (hD : IsHyperplane A D) (haD : a ∈ D)
    (hα : ∀ B' : Subgroup G, IsHyperplane A B' → a ∈ B' → B' ≠ D →
      ¬ ⁅pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G)) ⊔ X, B'⁆ ≤
        pPrimeCoreOf 3 (Subgroup.centralizer ({a} : Set G))) :
    ∃ (e f : G) (Le : Subgroup G), IsLBConfig A D e f Le := by
  have hD13 := h.toSec13Data
  have hA : Late.IsE27 A := h.isE27
  have hAmax := h.maximal_isElemAbelian
  have ha : a ∈ A := hC.mem
  have hb'A : b' ∈ A := (zpowers_mem_omegaA_iff.mp hb'Ω).1
  have hb'1 : b' ≠ 1 := by
    intro h1
    have h3 := (zpowers_mem_omegaA_iff.mp hb'Ω).2.1
    rw [h1, Subgroup.zpowers_one_eq_bot, Subgroup.card_bot] at h3
    exact absurd h3 (by norm_num)
  obtain ⟨hdL, S, hdS, hSd⟩ := hd'3
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥Lb') Nat.prime_three
  have h415 : Sec4.Item4_15 := Sec4.Sporadic.rank3II_4_15
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ2 hdL hd'1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d'} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd'1)
  have hJq := residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hJ2 hdL hd'1
    ⟨S, hdS, hSd⟩
  obtain ⟨K, hK, hRK⟩ :=
    exists_mem_thetaComponentsAt_le_residual h48 hG4 hA hb'A hd'A hb'1 hLb'.1 hJq
  have hdata : Sec13Data G A b' Lb' :=
    { hD13 with zpowers_mem_omegaA := hb'Ω, mem_lA := hLb' }
  have hπbc : ∃ P : Sylow 3 (↥Lb' ⧸ aschbacherSolvableCore 3 ↥Lb'),
      QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb') ⟨d', hdL⟩ ∈ (P : Subgroup _) ∧
        (P : Subgroup _) ≤ Subgroup.centralizer
          {QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb') ⟨d', hdL⟩} := by
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    refine ⟨S.mapSurjective (QuotientGroup.mk'_surjective (aschbacherSolvableCore 3 ↥Lb')), ?_,
      ?_⟩
    · change _ ∈ (S : Subgroup ↥Lb').map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb'))
      exact ⟨_, hdS, rfl⟩
    · change (S : Subgroup ↥Lb').map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥Lb')) ≤ _
      rintro _ ⟨s, hs, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff, ← map_mul, ← map_mul,
        Subgroup.mem_centralizer_singleton_iff.mp (hSd hs)]
  have hALK : A ⊓ Lb' ≤ K :=
    (inf_le_residual_of_central hA.1 hJ2 hd'A hdL hd'1 hπbc).trans hRK
  obtain ⟨-, h9, -⟩ := j2_point_facts hdata hJ2
  have hH : IsHyperplane A (A ⊓ Lb') := ⟨inf_le_left, by rw [hD13.card_eq, h9]⟩
  have hKa : K ∈ thetaComponentsAt 3 a := by
    rw [Item148PtRes.thetaComponentsAt_eq_of_zpowers_eq hda]
    exact hK
  have hA6 : Sec4.IsTripleCover (↥K ⧸ aschbacherSolvableCore 3 ↥K)
      (alternatingGroup (Fin 6)) → False := by
    intro hKA6
    refine hC.false_of_hyperplane_le hT hAmax ha1 hX hKa ?_ hH hALK hD haD hα
    rintro rfl
    obtain ⟨-, ⟨e₁⟩⟩ := hKA6
    obtain ⟨-, ⟨e₂⟩⟩ := hT
    have h1 := Nat.card_congr (e₁.symm.trans e₂).toEquiv
    rw [Item148HJ.card_alternatingGroup_six, CFSG.Sporadic.ON.card_ON] at h1
    norm_num at h1
  rcases h134 G A b' Lb' hdata hJ2 d' hd'A hd'1 ⟨_, hS⟩ K hK hRK with
    ⟨-, hKA6, -⟩ | ⟨-, hKA6, -⟩ | ⟨-, hWd, hΩeq, hΩ12⟩
  · exact (hA6 hKA6).elim
  · exact (hA6 hKA6).elim
  obtain ⟨u, huD, hua⟩ :=
    Item148PtRes.exists_mem_not_mem_zpowers hD13.card_eq hD13.isElemAbelian.2 hD ha
  have huA : u ∈ A := hD.1 huD
  have hu1 : u ≠ 1 := fun h1 => hua (h1 ▸ one_mem _)
  set T := {F : Subgroup G | F ≤ A ∧ Nat.card F = 3} with hTdef
  have hΩT : omegaA A ⊆ T := fun F hF => ⟨hF.1, hF.2.1⟩
  have haT : Subgroup.zpowers a ∈ T :=
    ⟨Subgroup.zpowers_le.mpr ha, card_zpowers_eq_three hA.1 ha ha1⟩
  have huT : Subgroup.zpowers u ∈ T :=
    ⟨Subgroup.zpowers_le.mpr huA, card_zpowers_eq_three hA.1 huA hu1⟩
  have hau : Subgroup.zpowers a ≠ Subgroup.zpowers u := fun he =>
    hua (he ▸ Subgroup.mem_zpowers u)
  have huΩ : Subgroup.zpowers u ∈ omegaA A := by
    by_contra huΩ
    have hsub : omegaA A ⊆ T \ {Subgroup.zpowers a, Subgroup.zpowers u} := by
      intro F hF
      refine ⟨hΩT hF, ?_⟩
      rintro (rfl | rfl)
      · exact hΩ hF
      · exact huΩ hF
    have hpair : ({Subgroup.zpowers a, Subgroup.zpowers u} : Set (Subgroup G)) ⊆ T := by
      rintro F (rfl | rfl)
      · exact haT
      · exact huT
    have : Finite (Subgroup G) :=
      Finite.of_injective (fun H : Subgroup G => (H : Set G)) SetLike.coe_injective
    have h1 := Set.ncard_le_ncard hsub
    have h2 := Set.ncard_sdiff_add_ncard_of_subset hpair
    rw [Set.ncard_pair hau] at h2
    have h3 := Item148PtRes.ncard_subgroups_card_three_le (A := A) hD13.card_eq
    rw [← hTdef] at h3
    omega
  have hbΩ : Subgroup.zpowers b ∈ omegaA A := hc.2.1
  have hbA : b ∈ A := (zpowers_mem_omegaA_iff.mp hbΩ).1
  have hb3 : Nat.card (Subgroup.zpowers b) = 3 := (zpowers_mem_omegaA_iff.mp hbΩ).2.1
  rw [hΩeq] at hbΩ huΩ
  obtain ⟨w₁, hw₁, hbw⟩ := hbΩ
  obtain ⟨w₂, hw₂, huw⟩ := huΩ
  have hwN : w₂ * w₁⁻¹ ∈ Subgroup.normalizer (A : Set G) := mul_mem hw₂ (inv_mem hw₁)
  have hwb : MulAut.conj (w₂ * w₁⁻¹) b ∈ D := by
    have hb : b ∈ Subgroup.zpowers b := Subgroup.mem_zpowers b
    rw [hbw] at hb
    obtain ⟨x, hx, hxb⟩ := hb
    have h1 : MulAut.conj (w₂ * w₁⁻¹) b = MulAut.conj w₂ x := by
      rw [← hxb]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    have h2 : MulAut.conj w₂ x ∈ Subgroup.zpowers u := by
      rw [huw]
      exact ⟨x, hx, rfl⟩
    rw [h1]
    exact Subgroup.zpowers_le.mpr huD h2
  have hwa : MulAut.conj (w₂ * w₁⁻¹) a ∈ D := by
    have h1 : w₂ * w₁⁻¹ ∈ Subgroup.normalizer (Subgroup.zpowers a : Set G) := by
      rw [hda]
      exact hWd hwN
    rw [MulAut.conj_apply]
    exact Subgroup.zpowers_le.mpr haD
      ((Subgroup.mem_normalizer_iff.mp h1 a).mp (Subgroup.mem_zpowers a))
  have hbB : b ∈ B := by
    rw [hc.1]
    exact Subgroup.subset_closure (Set.mem_insert b {d})
  have hba : b ∉ Subgroup.zpowers a := by
    intro hb
    apply hΩ
    have h1 : Subgroup.zpowers b = Subgroup.zpowers a :=
      Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hb)
        ((card_zpowers_eq_three hA.1 ha ha1).trans hb3.symm).le
    rw [← h1]
    exact hc.2.1
  have hab : IsHyperplane A (Subgroup.closure {a, b}) :=
    Main148.isHyperplane_closure_pair148 hA ha hbA ha1 hba
  have hBab : Subgroup.closure {a, b} = B := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact haB
      · exact hbB
    · have h1 := hab.2
      have h2 := hB.2
      omega
  have hBw : B.map (MulAut.conj (w₂ * w₁⁻¹)).toMonoidHom = D := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rw [← hBab, MonoidHom.map_closure, Set.image_pair, Subgroup.closure_le]
      rintro x (rfl | rfl)
      · exact hwa
      · exact hwb
    · have h1 := (hB.map_conj hwN).2
      have h2 := hD.2
      omega
  have hc' := hc.map (MulAut.conj (w₂ * w₁⁻¹))
  rw [Sec13.map_conj_eq_of_mem_normalizer hwN, hBw] at hc'
  exact ⟨_, _, _, hc'⟩

end Res9Fix

section Provers

theorem step143HJMemFixON_of (h134 : Item134) (h48 : Sec4.Item4_8) : Step143HJMemFixON := by
  intro G _ _ A c L h a ha ha1 hΩ B b d Lb hB haB hc b' d' Lb' X hb'Ω hLb' hJ2 hd'A hd'1 hd'3
    _ _ _ hLD _ hN hda h𝒳 hT D hD haD hα _ R hRN hR3 _ _
  obtain ⟨𝒳, h𝒳a, h𝒳ne, hX𝒳⟩ := h𝒳
  have : IsSimpleGroup CFSG.Blueprint.NativeSporadic.ON := CFSG.Sporadic.ON.isSimpleGroup_ON
  have hXa : X ∈ thetaComponentsAt 3 a :=
    h𝒳a (Item148Point.mem_of_eq_sSup148 h𝒳a h𝒳ne hX𝒳 hT.2.some)
  have hq := Sec6.isQuasisimple_of_mem_thetaComponentsAt hXa
  have hC : Res9Fix.Base A a X := Res9Fix.base_of h ha h𝒳a hX𝒳 hN
    (fun P hPn hP3 => Item148HJ.eq_bot_of_normal_of_quasisimple hq hT.1 hPn hP3)
  exact hC.le_qBound_on hT h ha1 hD haD hα (hLD D hD haD)
    (Res9Fix.exists_isLBConfig_on h134 h48 h hC hT hXa ha1 hΩ hB haB hc hb'Ω hLb' hJ2 hd'A hd'1
      hd'3 hda hD haD hα) hRN hR3

end Provers

end CFSG.RankThree.PartTwo.Sec14

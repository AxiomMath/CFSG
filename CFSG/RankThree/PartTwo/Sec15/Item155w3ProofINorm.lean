module

public import CFSG.RankThree.PartTwo.Sec15.Item155w2ProofBFix
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.RankThree.Theta.ThreeCoreComponentNormalization

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def HasE9KerThree (X : Subgroup G) : Prop :=
  ∃ E : Subgroup G, E ≤ X ∧ CFSG.Assembly.IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
    ∃ e₀ ∈ E, Late.sectionCentralizer E X ((aschbacherSolvableCore 3 ↥X).map X.subtype) ⊆
      (Subgroup.zpowers e₀ : Set G)

omit [Finite G] in
theorem hasE9KerThree_of_hasFaithfulE9 {X : Subgroup G} (hX : HasFaithfulE9 X) :
    HasE9KerThree X := by
  obtain ⟨E, hEX, hEab, hE9, hEc⟩ := hX
  refine ⟨E, hEX, hEab, hE9, 1, E.one_mem, fun z hz => ?_⟩
  rw [Set.mem_singleton_iff.mp (hEc hz)]
  exact Subgroup.one_mem _

namespace Proof155w3

theorem map_conj_eq_of_hasE9KerThree_of_mem {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {S : Set G} {X M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining S) (hXM : X ∈ thetaComponentsIn M)
    (hE : HasE9KerThree X) {t : G} (ht : t ∈ M) {k : ℕ} (htk : t ^ 3 ^ k = 1) :
    X.map (MulAut.conj t).toMonoidHom = X := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  by_contra hne
  obtain ⟨hXM', hY'⟩ := mem_thetaComponentsIn_iff.mp hXM
  set Y' := X.subgroupOf M with hY'def
  have hYY' : Y'.map M.subtype = X := by
    rw [hY'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXM']
  set t₀ : ↥M := ⟨t, ht⟩ with ht₀
  have ht₀N : t₀ ∉ Subgroup.normalizer (Y' : Set ↥M) := by
    intro hN
    apply hne
    have h1 : Y'.map (MulAut.conj t₀).toMonoidHom = Y' :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp hN
    calc X.map (MulAut.conj t).toMonoidHom
        = (Y'.map (MulAut.conj t₀).toMonoidHom).map M.subtype := by
          rw [← hYY', Subgroup.map_map, Subgroup.map_map]
          congr 1
      _ = X := by rw [h1, hYY']
  have hodd : Odd (orderOf t₀) := by
    have hdvd : orderOf t₀ ∣ 3 ^ k := orderOf_dvd_of_pow_eq_one (Subtype.ext (by
      rw [Subgroup.coe_pow, Subgroup.coe_one]
      exact htk))
    exact (Odd.pow (by decide)).of_dvd_nat hdvd
  obtain ⟨m, hm⟩ := hodd
  have ht₀sq : (t₀ ^ 2) ^ (m + 1) = t₀ := by
    rw [← pow_mul, show 2 * (m + 1) = orderOf t₀ + 1 by omega, pow_succ, pow_orderOf_eq_one,
      one_mul]
  have ht₀2N : t₀ ^ 2 ∉ Subgroup.normalizer (Y' : Set ↥M) := fun hN => by
    have := pow_mem hN (m + 1)
    rw [ht₀sq] at this
    exact ht₀N this
  set Y₂ := Y'.map (MulAut.conj t₀).toMonoidHom with hY₂def
  set Y₃ := Y'.map (MulAut.conj (t₀ ^ 2)).toMonoidHom with hY₃def
  have hY₂ : Y₂ ∈ thetaComponents 3 ↥M :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj t₀) hY'
  have hY₃ : Y₃ ∈ thetaComponents 3 ↥M :=
    map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj (t₀ ^ 2)) hY'
  have h12 : Y' ≠ Y₂ := fun he =>
    ht₀N (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have h13 : Y' ≠ Y₃ := fun he =>
    ht₀2N (Subgroup.mem_normalizer_iff_map_conj_eq.mpr he.symm)
  have h23 : Y₂ ≠ Y₃ := by
    intro he
    have h1 := CFSG.RankThree.Theta.mem_normalizer_of_map_conj_eq he
    rw [show (t₀ ^ 2)⁻¹ * t₀ = t₀⁻¹ by group] at h1
    exact ht₀N (by simpa using inv_mem h1)
  have c12 := commutator_le_of_mem_thetaComponents hY' hY₂ h12
  have c13 := commutator_le_of_mem_thetaComponents hY' hY₃ h13
  have c23 := commutator_le_of_mem_thetaComponents hY₂ hY₃ h23
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have hθn : (aschbacherSolvableCore 3 ↥M).Normal := Subgroup.normal_of_characteristic _
  set θ := aschbacherSolvableCore 3 ↥M with hθ
  obtain ⟨E, hEX, hEab, hE9, e₀, he₀, hker⟩ := hE
  obtain ⟨f, hfE, hfe⟩ : ∃ f ∈ E, f ∉ Subgroup.zpowers e₀ := by
    by_contra hall
    push Not at hall
    have h1 := Subgroup.card_le_of_le (show E ≤ Subgroup.zpowers e₀ from hall)
    rw [hE9, Nat.card_zpowers] at h1
    have h2 : orderOf e₀ ≤ 3 :=
      Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one (hEab.2 e₀ he₀))
    omega
  obtain ⟨x, hxX, hfx⟩ : ∃ x ∈ X,
      f * x * f⁻¹ * x⁻¹ ∉ (aschbacherSolvableCore 3 ↥X).map X.subtype := by
    by_contra hall
    push Not at hall
    exact hfe (hker ⟨hfE, hall⟩)
  set f₁ : ↥M := ⟨f, hXM' (hEX hfE)⟩ with hf₁def
  set x₁ : ↥M := ⟨x, hXM' hxX⟩ with hx₁def
  have hf₁ : f₁ ∈ Y' := Subgroup.mem_subgroupOf.mpr (hEX hfE)
  have hx₁ : x₁ ∈ Y' := Subgroup.mem_subgroupOf.mpr hxX
  obtain ⟨hθN, hθs, hθ3'⟩ := map_aschbacherSolvableCore_facts M
  have hfx₁ : ⁅f₁, x₁⁆ ∉ θ := by
    intro hc
    apply hfx
    have e1 : ((⁅f₁, x₁⁆ : ↥M) : G) = f * x * f⁻¹ * x⁻¹ := by
      rw [commutatorElement_def]
      rfl
    have hmem : ((⁅f₁, x₁⁆ : ↥M) : G) ∈ θ.map M.subtype ⊓ X := by
      refine ⟨Subgroup.mem_map_of_mem _ hc, ?_⟩
      rw [e1]
      exact X.mul_mem (X.mul_mem (X.mul_mem (hEX hfE) hxX) (X.inv_mem (hEX hfE)))
        (X.inv_mem hxX)
    have := inf_le_map_aschbacherSolvableCore (hXM'.trans hθN) hθs hθ3' hmem
    rwa [e1] at this
  have hθmem : ∀ s y : ↥M, MulAut.conj s y ∈ θ → y ∈ θ := by
    intro s y hy
    have h1 := hθn.conj_mem _ hy s⁻¹
    rwa [MulAut.conj_apply, show s⁻¹ * (s * y * s⁻¹) * s⁻¹⁻¹ = y by group] at h1
  have hfx₂ : ⁅MulAut.conj t₀ f₁, MulAut.conj t₀ x₁⁆ ∉ θ := fun hc =>
    hfx₁ (hθmem t₀ _ (by rw [map_commutatorElement]; exact hc))
  have hfx₃ : ⁅MulAut.conj (t₀ ^ 2) f₁, MulAut.conj (t₀ ^ 2) x₁⁆ ∉ θ := fun hc =>
    hfx₁ (hθmem (t₀ ^ 2) _ (by rw [map_commutatorElement]; exact hc))
  have hf₂ : MulAut.conj t₀ f₁ ∈ Y₂ := Subgroup.mem_map_of_mem _ hf₁
  have hx₂ : MulAut.conj t₀ x₁ ∈ Y₂ := Subgroup.mem_map_of_mem _ hx₁
  have hf₃ : MulAut.conj (t₀ ^ 2) f₁ ∈ Y₃ := Subgroup.mem_map_of_mem _ hf₁
  have hx₃ : MulAut.conj (t₀ ^ 2) x₁ ∈ Y₃ := Subgroup.mem_map_of_mem _ hx₁
  set π := QuotientGroup.mk' θ with hπ
  have hcent : ∀ {U V : Subgroup ↥M}, ⁅U, V⁆ ≤ θ →
      U.map π ≤ Subgroup.centralizer ((V.map π : Subgroup (↥M ⧸ θ)) : Set (↥M ⧸ θ)) := by
    intro U V hUV
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have h1 : π ⁅a, b⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (hUV (Subgroup.commutator_mem_commutator ha hb))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hnot : ∀ {V : Subgroup ↥M} {a b : ↥M}, b ∈ V → ⁅a, b⁆ ∉ θ →
      π a ∉ Subgroup.centralizer ((V.map π : Subgroup (↥M ⧸ θ)) : Set (↥M ⧸ θ)) := by
    intro V a b hb hab ha
    apply hab
    have h1 := Subgroup.mem_centralizer_iff.mp ha (π b) (Subgroup.mem_map_of_mem _ hb)
    have h2 : π ⁅a, b⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact h1.symm
    exact (QuotientGroup.eq_one_iff _).mp h2
  set E₁ : Subgroup ↥M := E.subgroupOf M with hE₁
  have hE₁Y' : E₁ ≤ Y' := fun a ha =>
    Subgroup.mem_subgroupOf.mpr (hEX (Subgroup.mem_subgroupOf.mp ha))
  have hE₁card : Nat.card E₁ = 9 := by
    have hmap : E₁.map M.subtype = E := by
      rw [hE₁, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (hEX.trans hXM')]
    rw [← hE9, ← hmap, Subgroup.card_map_of_injective M.subtype_injective]
  have hE₁ab : CFSG.Open.IsElemAbelian 3 E₁ := by
    refine ⟨⟨⟨fun a b => ?_⟩⟩, fun y hy => ?_⟩
    · have ha : ((a : ↥M) : G) ∈ E := Subgroup.mem_subgroupOf.mp a.2
      have hb : ((b : ↥M) : G) ∈ E := Subgroup.mem_subgroupOf.mp b.2
      have hab : ((a : ↥M) : G) * ((b : ↥M) : G) = ((b : ↥M) : G) * ((a : ↥M) : G) :=
        congrArg Subtype.val (hEab.1.is_comm.comm (⟨_, ha⟩ : E) ⟨_, hb⟩)
      apply Subtype.ext
      apply Subtype.ext
      exact hab
    · exact Subtype.ext (hEab.2 _ (Subgroup.mem_subgroupOf.mp hy))
  set Ē := E₁.map π with hĒ
  have hĒab : CFSG.Open.IsElemAbelian 3 Ē := CFSG.SectionRank.isElemAbelian_map hE₁ab π
  have hinj : Function.Injective (π.comp E₁.subtype) := by
    rw [← MonoidHom.ker_eq_bot_iff, eq_bot_iff]
    intro a ha
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply] at ha
    have haθ : (a : ↥M) ∈ θ := (QuotientGroup.eq_one_iff _).mp ha
    exact Subgroup.mem_bot.mpr
      (Subtype.ext (eq_one_of_mem_of_pow_three hθ3 haθ (hE₁ab.2 _ a.2)))
  have hĒcard : Nat.card Ē = 9 := by
    have h1 : Ē = (π.comp E₁.subtype).range := by
      rw [hĒ, MonoidHom.range_comp, Subgroup.range_subtype]
    rw [h1, ← hE₁card]
    exact (Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv).symm
  have hf₁3 : f₁ ^ 3 = 1 := Subtype.ext (by
    rw [Subgroup.coe_pow, Subgroup.coe_one]
    exact hEab.2 f hfE)
  set u := π (MulAut.conj t₀ f₁) with hu
  set v := π (MulAut.conj (t₀ ^ 2) f₁) with hv
  set C₂ := Subgroup.centralizer ((Y₂.map π : Subgroup (↥M ⧸ θ)) : Set (↥M ⧸ θ)) with hC₂
  set C₃ := Subgroup.centralizer ((Y₃.map π : Subgroup (↥M ⧸ θ)) : Set (↥M ⧸ θ)) with hC₃
  have hĒC₂ : Ē ≤ C₂ := (Subgroup.map_mono hE₁Y').trans (hcent c12)
  have hĒC₃ : Ē ≤ C₃ := (Subgroup.map_mono hE₁Y').trans (hcent c13)
  have huY₂ : u ∈ Y₂.map π := Subgroup.mem_map_of_mem _ hf₂
  have hvY₃ : v ∈ Y₃.map π := Subgroup.mem_map_of_mem _ hf₃
  have huC₃ : u ∈ C₃ := hcent c23 huY₂
  have huC₂ : u ∉ C₂ := hnot hx₂ hfx₂
  have hvC₃ : v ∉ C₃ := hnot hx₃ hfx₃
  have hu3 : u ^ 3 = 1 := by rw [hu, ← map_pow, ← map_pow, hf₁3, map_one, map_one]
  have hv3 : v ^ 3 = 1 := by rw [hv, ← map_pow, ← map_pow, hf₁3, map_one, map_one]
  have huo : orderOf u = 3 := orderOf_eq_prime hu3 fun h1 => huC₂ (by
    rw [h1]
    exact C₂.one_mem)
  have hvo : orderOf v = 3 := orderOf_eq_prime hv3 fun h1 => hvC₃ (by
    rw [h1]
    exact C₃.one_mem)
  have huĒ : u ∈ Subgroup.centralizer (Ē : Set (↥M ⧸ θ)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hĒC₂ ha) u huY₂).symm
  have hdisj₁ : Ē ⊓ Subgroup.zpowers u = ⊥ := by
    rw [inf_comm]
    exact CFSG.RankThree.zpowers_inf_eq_bot_of_not_mem Nat.prime_three huo
      fun h1 => huC₂ (hĒC₂ h1)
  obtain ⟨hF₁card, hF₁c, hF₁e⟩ :=
    CFSG.RankThree.card_sup_zpowers_of_disjoint huĒ hĒab.1 hĒab.2 huo hdisj₁
  have hF₁C₃ : Ē ⊔ Subgroup.zpowers u ≤ C₃ := sup_le hĒC₃ (Subgroup.zpowers_le.mpr huC₃)
  have hvF₁ : v ∈ Subgroup.centralizer ((Ē ⊔ Subgroup.zpowers u : Subgroup (↥M ⧸ θ)) :
      Set (↥M ⧸ θ)) := by
    rw [Subgroup.mem_centralizer_iff]
    intro a ha
    exact (Subgroup.mem_centralizer_iff.mp (hF₁C₃ ha) v hvY₃).symm
  have hdisj₂ : (Ē ⊔ Subgroup.zpowers u) ⊓ Subgroup.zpowers v = ⊥ := by
    rw [inf_comm]
    exact CFSG.RankThree.zpowers_inf_eq_bot_of_not_mem Nat.prime_three hvo
      fun h1 => hvC₃ (hF₁C₃ h1)
  obtain ⟨hF₂card, hF₂c, hF₂e⟩ :=
    CFSG.RankThree.card_sup_zpowers_of_disjoint hvF₁ hF₁c hF₁e hvo hdisj₂
  have h4Q : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ θ)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top ⟨hF₂c, hF₂e⟩ (by
      rw [hF₂card, hF₁card, hĒcard]
      norm_num)
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) := by
    rwa [CFSG.SectionRank.pRank_quotient_eq θ hθ3] at h4Q
  have h4' : 4 ≤ CFSG.Open.pRank 3 M := by
    refine h4.trans ?_
    have := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three M.subtype M.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have h3 : CFSG.Open.pRank 3 M ≤ 3 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) M hM.1.1).trans h.toTheoremFourHyp.evenRank_eq.le
  omega

theorem oPrimeResidualOf_le_normalizer_of_hasE9KerThree {A : Subgroup G} {c : G}
    {L : Subgroup G} (h : Sec14Std G A c L) {S : Set G} {X M H : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining S) (hXM : X ∈ thetaComponentsIn M)
    (hE : HasE9KerThree X) (hHM : H ≤ M) :
    oPrimeResidualOf 3 H ≤ Subgroup.normalizer (X : Set G) := by
  rw [oPrimeResidualOf_eq_closure, Subgroup.closure_le]
  rintro t ⟨htH, k, htk⟩
  exact Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (map_conj_eq_of_hasE9KerThree_of_mem h hM hXM hE (hHM htH) htk)

end Proof155w3

open Proof155w3

@[expose] noncomputable def Step155INormX2RkW (A : Subgroup G) (c : G) (L : Subgroup G) : Prop :=
  Sec14Std G A c L → ∀ X K Y M T P : Subgroup G, Ctx155 A X K Y M T → MaxT155 A X K T →
    Above155w A X → End155N A X K Y M T P → w155 A M X ≠ ⊥ →
      IsScriptLBlock ⊤ (oResidual 2 ↥(CFSG.Open.pCoreOf 2 Y ⊔ w155 A M X)) →
      ¬ HasE9KerThree X →
        oPrimeResidualOf 3 (delta A (lB A) M) ≤ Subgroup.normalizer (X : Set G)

@[expose] noncomputable def Step155INormX2RkWR : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
    Sec15R G A c L → Step155INormX2RkW A c L

theorem step155INormX2W_of_rk {A : Subgroup G} {c : G} {L : Subgroup G}
    (hres : Step155INormX2RkW A c L) : Step155INormX2W A c L := by
  intro h X K Y M T P hC hmax hab hE hW1 hbl
  by_cases hF : HasE9KerThree X
  · exact oPrimeResidualOf_le_normalizer_of_hasE9KerThree h hC.mem_m hE.mem_x hF (delta_le M)
  · exact hres h X K Y M T P hC hmax hab hE hW1 hbl hF

theorem step155INormX2WR_of_rk (hres : Step155INormX2RkWR) : Step155INormX2WR :=
  fun G _ _ A c L hR => step155INormX2W_of_rk (hres G A c L hR)

end CFSG.RankThree.PartTwo.Sec15

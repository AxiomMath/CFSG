module

public import CFSG.RankThree.PartOne.S12.BaseNodes
public import CFSG.RankThree.PartOne.S12.Sec12Two
public import CFSG.RankThree.PartOne.S11.SecTenEight
import CFSG.RankThree.PartOne.S12.Sec13Zero
import CFSG.RankThree.PartOne.S10.AmbientTheta

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement

namespace Sec12TwoAssembly

section Abstract

variable {G : Type*} [Group G]

theorem not_isSimpleGroup_quotient_theta {L : Type*} [Group L] [Finite L] {p : ℕ}
    (hp : p.Prime) (hqs : CFSG.IsQuasisimple L) (hdvd : p ∣ Nat.card (Subgroup.center L)) :
    ¬ IsSimpleGroup (L ⧸ aschbacherSolvableCore p L) := by
  intro hsimple
  obtain ⟨hsolv, -, hpn, -⟩ := solvable_prime_complement_core_characterization (H := L) hp
  set θ := aschbacherSolvableCore p L
  have hnt : Nontrivial L := CFSG.LocalCores.isQuasisimple_nontrivial hqs
  have hperf : Group.IsPerfect L := hqs.1
  have hθZ : θ ≤ Subgroup.center L := by
    rcases CFSG.LocalCores.quasisimple_normal_subgroups hqs (inferInstance : θ.Normal) with
      htop | hcen
    · exfalso
      have hLsol : Group.IsSolvable L := by
        rw [htop] at hsolv
        exact Group.isSolvable_of_isSolvable_injective
          (f := (Subgroup.topEquiv (G := L)).symm.toMonoidHom) (MulEquiv.injective _)
      exact Group.IsPerfect.not_isSolvable L hLsol
    · exact hcen
  have hnormal : ((Subgroup.center L).map (QuotientGroup.mk' θ)).Normal :=
    (inferInstance : (Subgroup.center L).Normal).map _ (QuotientGroup.mk'_surjective θ)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal
    ((Subgroup.center L).map (QuotientGroup.mk' θ)) with hbot | htop
  · have hle : Subgroup.center L ≤ θ := by
      rwa [Subgroup.map_eq_bot_iff, QuotientGroup.ker_mk'] at hbot
    exact hpn (hdvd.trans (Subgroup.card_dvd_of_le hle))
  · have hsup : Subgroup.center L ⊔ θ = ⊤ := by
      have := Subgroup.comap_map_eq (QuotientGroup.mk' θ) (Subgroup.center L)
      rw [htop, Subgroup.comap_top, QuotientGroup.ker_mk'] at this
      exact this.symm
    rw [sup_eq_left.mpr hθZ] at hsup
    have : IsSimpleGroup (L ⧸ Subgroup.center L) := hqs.2.1
    obtain ⟨a, b, hab⟩ := exists_pair_ne (L ⧸ Subgroup.center L)
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    exact hab (QuotientGroup.eq.mpr (hsup ▸ Subgroup.mem_top _))

theorem normalizer_zpowers_le_normalizer_centralizer (c : G) :
    Subgroup.normalizer (Subgroup.zpowers c : Set G) ≤
      Subgroup.normalizer (Subgroup.centralizer ({c} : Set G) : Set G) := by
  have key : ∀ a ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G),
      ∀ g ∈ Subgroup.centralizer ({c} : Set G),
        a * g * a⁻¹ ∈ Subgroup.centralizer ({c} : Set G) := by
    intro a ha g hg
    have h1 : a⁻¹ * c * a ∈ Subgroup.zpowers c := by
      have := (Subgroup.mem_normalizer_iff.mp ((Subgroup.normalizer _).inv_mem ha) c).mp
        (Subgroup.mem_zpowers c)
      simpa using this
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.mp h1
    have hgc : Commute g c := Subgroup.mem_centralizer_singleton_iff.mp hg
    have hgj : g * (a⁻¹ * c * a) = (a⁻¹ * c * a) * g := by
      rw [← hj]
      exact (Commute.zpow_right hgc j).eq
    rw [Subgroup.mem_centralizer_singleton_iff]
    calc a * g * a⁻¹ * c = a * (g * (a⁻¹ * c * a)) * a⁻¹ := by group
      _ = a * ((a⁻¹ * c * a) * g) * a⁻¹ := by rw [hgj]
      _ = c * (a * g * a⁻¹) := by group
  intro a ha
  rw [Subgroup.mem_normalizer_iff]
  intro g
  refine ⟨key a ha g, fun hg => ?_⟩
  have h2 := key a⁻¹ ((Subgroup.normalizer _).inv_mem ha) _ hg
  have e : a⁻¹ * (a * g * a⁻¹) * a⁻¹⁻¹ = g := by group
  rwa [e] at h2

theorem conj_mem_thetaComponentsAt [Finite G] {p : ℕ} (hp : p.Prime) {c x : G}
    (hx : x ∈ Subgroup.normalizer (Subgroup.zpowers c : Set G)) {L : Subgroup G}
    (hL : L ∈ thetaComponentsAt p c) :
    L.map (MulAut.conj x).toMonoidHom ∈ thetaComponentsAt p c := by
  set H := Subgroup.centralizer ({c} : Set G)
  have hxH : x ∈ Subgroup.normalizer (H : Set G) :=
    normalizer_zpowers_le_normalizer_centralizer c hx
  obtain ⟨hLH, hL0⟩ := mem_thetaComponentsAt_iff.mp hL
  let σ : MulAut H := H.normalizerMonoidHom ⟨x, hxH⟩
  have hσ : ∀ y : H, ((σ y : H) : G) = x * y * x⁻¹ := fun y => by
    simp [σ, Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hσ' : ∀ y : H, ((σ.toMonoidHom y : H) : G) = x * y * x⁻¹ := hσ
  have hconj : ∀ g : G, (MulAut.conj x).toMonoidHom g = x * g * x⁻¹ := fun g => rfl
  have hmap := map_mulEquiv_mem_thetaComponents hp σ hL0
  rw [mem_thetaComponentsAt_iff]
  have hle : L.map (MulAut.conj x).toMonoidHom ≤ H := by
    rintro _ ⟨l, hl, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hxH l).mp (hLH hl)
  refine ⟨hle, ?_⟩
  convert hmap using 1
  ext y
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_map, Subgroup.mem_map]
  constructor
  · rintro ⟨l, hl, hly⟩
    refine ⟨⟨l, hLH hl⟩, ?_, ?_⟩
    · rw [Subgroup.mem_subgroupOf]
      exact hl
    · apply Subtype.ext
      rw [hσ', ← hconj]
      exact hly
  · rintro ⟨z, hz, hzy⟩
    refine ⟨z, hz, ?_⟩
    have := congrArg Subtype.val hzy
    rw [hσ'] at this
    rw [hconj]
    exact this

theorem commutator_mem_theta_of_ne {H : Type*} [Group H] [Finite H] {p : ℕ} (hp : p.Prime)
    {L₁ L₂ : Subgroup H} (h₁ : L₁ ∈ thetaComponents p H) (h₂ : L₂ ∈ thetaComponents p H)
    (hne : L₁ ≠ L₂) {a b : H} (ha : a ∈ L₁) (hb : b ∈ L₂) :
    ⁅a, b⁆ ∈ aschbacherSolvableCore p H := by
  set N := aschbacherSolvableCore p H
  set π := QuotientGroup.mk' N
  obtain ⟨hbij, -, -⟩ := theta_component_quotient_correspondence (H := H) hp
  have hK₁ := isComponent_map_of_mem_thetaComponents hp h₁
  have hK₂ := isComponent_map_of_mem_thetaComponents hp h₂
  have hKne : L₁.map π ≠ L₂.map π := fun h => hne (hbij.injOn h₁ h₂ h)
  have hcomm := (LocalCores.distinct_components_commute hK₁ hK₂).resolve_left hKne
  have h1 : ⁅π a, π b⁆ ∈ ⁅L₁.map π, L₂.map π⁆ :=
    Subgroup.commutator_mem_commutator (Subgroup.mem_map_of_mem π ha) (Subgroup.mem_map_of_mem π hb)
  rw [hcomm, Subgroup.mem_bot, ← map_commutatorElement, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at h1
  exact h1

theorem commutator_le_theta_of_ne [Finite G] {p : ℕ} (hp : p.Prime) {a : G}
    {L₁ L₂ : Subgroup G} (h₁ : L₁ ∈ thetaComponentsAt p a) (h₂ : L₂ ∈ thetaComponentsAt p a)
    (hne : L₁ ≠ L₂) :
    ⁅L₁, L₂⁆ ≤ inSubgroup (aschbacherSolvableCore p) (Subgroup.centralizer ({a} : Set G)) := by
  set H := Subgroup.centralizer ({a} : Set G)
  obtain ⟨hL₁H, hL₁⟩ := mem_thetaComponentsAt_iff.mp h₁
  obtain ⟨hL₂H, hL₂⟩ := mem_thetaComponentsAt_iff.mp h₂
  have hne' : L₁.subgroupOf H ≠ L₂.subgroupOf H := fun h => hne (by
    rw [← Subgroup.map_subgroupOf_eq_of_le hL₁H, ← Subgroup.map_subgroupOf_eq_of_le hL₂H, h])
  rw [Subgroup.commutator_le]
  intro g₁ hg₁ g₂ hg₂
  have h := commutator_mem_theta_of_ne hp hL₁ hL₂ hne' (a := ⟨g₁, hL₁H hg₁⟩)
    (b := ⟨g₂, hL₂H hg₂⟩) (by rwa [Subgroup.mem_subgroupOf]) (by rwa [Subgroup.mem_subgroupOf])
  exact Subgroup.mem_map.mpr ⟨_, h, rfl⟩

theorem le_centralizer_of_mem_thetaComponentsAt_ne [Finite G] {p : ℕ} (hp : p.Prime) {c : G}
    {L L' B : Subgroup G} (hL : L ∈ thetaComponentsAt p c) (hL' : L' ∈ thetaComponentsAt p c)
    (hqs : CFSG.IsQuasisimple L') (hne : L ≠ L') (hBL : B ≤ L)
    (hBN : B ≤ Subgroup.normalizer (L' : Set G)) : B ≤ Subgroup.centralizer (L' : Set G) := by
  have hcomm := commutator_le_theta_of_ne hp hL hL' hne
  have hθ := theta_eq_inf_of_mem_thetaComponentsAt hp hL'
  have hBc : ⁅L', B⁆ = ⊥ := by
    refine CFSG.LocalCores.perfect_double_commutator hqs.1 ?_
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
    intro l' hl' b hb
    have hmem : ⁅b, l'⁆ ∈ inSubgroup (aschbacherSolvableCore p) L' := by
      rw [hθ]
      refine ⟨?_, hcomm (Subgroup.commutator_mem_commutator (hBL hb) hl')⟩
      rw [commutatorElement_def]
      exact L'.mul_mem ((Subgroup.mem_normalizer_iff.mp (hBN hb) l').mp hl') (L'.inv_mem hl')
    rw [← commutatorElement_inv]
    refine Subgroup.inv_mem _ ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact (commute_of_mem_theta_of_isQuasisimple hp hqs hmem hl).symm
  exact Subgroup.le_centralizer_iff.mp (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hBc)

end Abstract

section Setup

variable {G : Type} [Group G] [Finite G] {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem not_E_le_zpowers (h : Sec12Hyp G p A c L E) : ¬ E ≤ Subgroup.zpowers c := by
  intro hle
  have hdvd : Nat.card E ∣ Nat.card (Subgroup.zpowers c) := Subgroup.card_dvd_of_le hle
  rw [Nat.card_zpowers, Sec12Two.orderOf_c h] at hdvd
  have h4 : p ^ 3 ∣ p := h.pow_three_dvd_card_E.trans hdvd
  have h5 := Nat.le_of_dvd h.prime.pos h4
  have h3 := h.three_lt
  nlinarith [Nat.mul_pos h.prime.pos h.prime.pos]

theorem not_E_le_centralizer_of_generic (h : Sec12Hyp G p A c L E)
    (hgen : Sec12TwoGeneric p c L E) : ¬ E ≤ Subgroup.centralizer (L : Set G) := by
  intro hEc
  have : IsElementaryAbelian p E := h.E_elem
  have hEL : E ⊓ L = ⊥ := by
    rw [eq_bot_iff]
    rintro y ⟨hyE, hyL⟩
    rw [Subgroup.mem_bot]
    exact Sec12Two.eq_one_of_mem_center_of_pow_eq_one h.prime hgen.center_pPrime hyL (hEc hyE)
      (elemPow_eq_one_of_isElementaryAbelian (p := p) (A := E) y hyE)
  have hE : E = Subgroup.zpowers c := hgen.E_eq.trans (by rw [hEL, bot_sup_eq])
  exact not_E_le_zpowers h hE.le

theorem not_E_le_centralizer_of_su5 (h : Sec12Hyp G p A c L E)
    (hsu5 : Sec12TwoSU5 p c L E) : ¬ E ≤ Subgroup.centralizer (L : Set G) := by
  intro hEc
  refine not_E_le_zpowers h ?_
  rw [← hsu5.center_eq]
  intro e he
  refine ⟨⟨e, hsu5.E_le he⟩, Subgroup.mem_center_iff.mpr fun g => ?_, rfl⟩
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp (hEc he) g g.2)

theorem mem_normalizer_of_structure (h : Sec12Hyp G p A c L E)
    (h81 : SelectedPrimeElementsNormalizeThetaComponents) (hqs : CFSG.IsQuasisimple L)
    {B : Subgroup G} (hBE : B ≤ E) (hBL : B ≤ L) (hEB : E ≤ B ⊔ Subgroup.zpowers c)
    (hnot : ¬ E ≤ Subgroup.centralizer (L : Set G)) {x : G}
    (hxc : x ∈ cNormalizer c) (hxE : x ∈ torusNormalizer E) :
    x ∈ Subgroup.normalizer (L : Set G) := by
  by_contra hxL
  have hp := h.prime
  have hcE : c ∈ E := h.A_le_E h.c_mem
  set L' : Subgroup G := L.map (MulAut.conj x).toMonoidHom
  have hL'c : L' ∈ thetaComponentsAt p c := conj_mem_thetaComponentsAt hp hxc h.L_mem.2
  have hL'q : CFSG.IsQuasisimple L' := CFSG.LocalCores.isQuasisimple_of_mulEquiv
    (L.equivMapOfInjective (MulAut.conj x).toMonoidHom (MulAut.conj x).injective) hqs
  have hne : L ≠ L' := fun heq => hxL (Subgroup.mem_normalizer_iff_map_conj_eq.mpr heq.symm)
  have hEN : E ≤ Subgroup.normalizer (L' : Set G) :=
    h.E_normalizes_thetaComponentsAt h81 hcE hL'c
  have hB : B ≤ Subgroup.centralizer (L' : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt_ne hp h.L_mem.2 hL'c hL'q hne hBL (hBE.trans hEN)
  have hc : Subgroup.zpowers c ≤ Subgroup.centralizer (L' : Set G) := by
    refine Subgroup.zpowers_le.mpr ?_
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp ((mem_thetaComponentsAt_iff.mp hL'c).1 hl)
  have hE : E ≤ Subgroup.centralizer (L' : Set G) := hEB.trans (sup_le hB hc)
  refine hnot fun e he l hl => ?_
  have he' : x * e * x⁻¹ ∈ E := (Subgroup.mem_normalizer_iff.mp hxE e).mp he
  have hl' : x * l * x⁻¹ ∈ L' := Subgroup.mem_map.mpr ⟨l, hl, rfl⟩
  have hcomm := Subgroup.mem_centralizer_iff.mp (hE he') _ hl'
  have key : x * (l * e) * x⁻¹ = x * (e * l) * x⁻¹ :=
    calc x * (l * e) * x⁻¹ = (x * l * x⁻¹) * (x * e * x⁻¹) := by group
      _ = (x * e * x⁻¹) * (x * l * x⁻¹) := hcomm
      _ = x * (e * l) * x⁻¹ := by group
  exact mul_left_cancel (mul_right_cancel key)

end Setup

end Sec12TwoAssembly

theorem node122_of_inputs (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h81 : SelectedPrimeElementsNormalizeThetaComponents)
    (h104 : SectionTenMaximalComponentQuotientActorKernelCyclic)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple) (h107 : InSec10Seven)
    (h108 : InSec10EightMoving) (hKF : KF122) (hSU5 : InSU5Contained) : Node122 := by
  intro G _ _ p A c L E h
  by_cases hZ : p ∣ Nat.card (Subgroup.center L)
  · right
    have hqs : CFSG.IsQuasisimple L :=
      h106 hSchreier hTwoAction G p A h.setup L (Sec12Two.L_mem_zeroStar h)
    have hns := Sec12TwoAssembly.not_isSimpleGroup_quotient_theta h.prime hqs hZ
    rcases h108 G p A h.setup c h.c_mem h.c_ne_one L ⟨h.L_mem.1.1, h.L_mem.2⟩ with
      hs | ⟨hp5, hcen, hcard, hmodel, hcont⟩
    · exact absurd hs hns
    · exact ⟨hp5, hqs, hcen, hcard, hmodel, hSU5 G p A c L E h hZ, hcont⟩
  · left
    obtain ⟨hqs, hrank, hCrank, hmem, hE⟩ := node122_of_prime_to_center hSchreier hTwoAction h81
      h104 h106 h107 hKF h hZ
    exact ⟨hZ, hqs, hrank, hCrank, hmem, hE⟩

theorem node122b_of_inputs (h81 : SelectedPrimeElementsNormalizeThetaComponents)
    (h122 : Node122) : Node122b := by
  intro G _ _ p A c L E h x hx
  obtain ⟨hxc, hxE⟩ := Subgroup.mem_inf.mp hx
  rcases h122 G p A c L E h with hgen | hsu5
  · exact Sec12TwoAssembly.mem_normalizer_of_structure h h81 hgen.quasisimple (B := E ⊓ L)
      inf_le_left inf_le_right hgen.E_eq.le
      (Sec12TwoAssembly.not_E_le_centralizer_of_generic h hgen) hxc hxE
  · exact Sec12TwoAssembly.mem_normalizer_of_structure h h81 hsu5.quasisimple (B := E)
      le_rfl hsu5.E_le le_sup_left (Sec12TwoAssembly.not_E_le_centralizer_of_su5 h hsu5) hxc hxE

end CFSG.RankThree.PartOne

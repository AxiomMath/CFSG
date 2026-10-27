module

public import CFSG.RankThree.PartOne.S12.Sec12A
public import CFSG.RankThree.PartOne.S12.InputsBase
import CFSG.RankThree.PartOne.S10.AmbientTheta
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Commutator.Core

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)
open scoped commutatorElement Pointwise

namespace Sec125

theorem exists_maximal_above {α : Type*} [Finite α] (r : α → α → Prop) (F : Set α)
    (hrefl : ∀ a ∈ F, r a a)
    (htrans : ∀ a ∈ F, ∀ b ∈ F, ∀ c ∈ F, r a b → r b c → r a c) {a₀ : α} (ha₀ : a₀ ∈ F) :
    ∃ b ∈ F, r a₀ b ∧ ∀ b' ∈ F, r b b' → r b' b := by
  obtain ⟨b, ⟨hbF, hab⟩, hmax⟩ := Set.Finite.exists_maximalFor
    (fun b : α => {x : α | x ∈ F ∧ r x b}) {b : α | b ∈ F ∧ r a₀ b} (Set.toFinite _)
    ⟨a₀, ha₀, hrefl a₀ ha₀⟩
  refine ⟨b, hbF, hab, fun b' hb'F hbb' => ?_⟩
  have hle : {x : α | x ∈ F ∧ r x b} ≤ {x : α | x ∈ F ∧ r x b'} := fun x hx =>
    ⟨hx.1, htrans x hx.1 b hbF b' hb'F hx.2 hbb'⟩
  exact (hmax ⟨hb'F, htrans a₀ ha₀ b hbF b' hb'F hab hbb'⟩ hle) ⟨hb'F, hrefl b' hb'F⟩ |>.2

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem ne_bot_of_isQuasisimple {K : Subgroup G} (hK : CFSG.IsQuasisimple K) : K ≠ ⊥ := by
  have : Nontrivial (K ⧸ Subgroup.center K) := hK.2.1.toNontrivial
  have : Nontrivial K := (QuotientGroup.mk'_surjective (Subgroup.center K)).nontrivial
  exact (Subgroup.nontrivial_iff_ne_bot K).1 this

theorem not_sectionTenRel_of_moved {p : ℕ} (hp : p.Prime) {A : Subgroup G} {c : G} (hcA : c ∈ A)
    {K₀ K' : Subgroup G} (hK₀ : K₀ ∈ thetaComponentFamily p A)
    (hAK₀ : A ≤ Subgroup.normalizer (K₀ : Set G)) (hK₀c : ⁅K₀, Subgroup.zpowers c⁆ = K₀)
    (hK'c : K' ≤ Subgroup.centralizer ({c} : Set G)) : ¬ sectionTenRel p K₀ K' := by
  intro hrel
  set θ := inSubgroup (aschbacherSolvableCore p) K₀ with hθ
  obtain ⟨hθK₀, hθnormal⟩ := theta_le_and_normal p K₀
  have hK₀N : K₀ ≤ Subgroup.normalizer (θ : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hθK₀).mp hθnormal
  have hAθ : A ≤ Subgroup.normalizer (θ : Set G) := le_normalizer_theta_of_le_normalizer hp hAK₀
  have hzA : Subgroup.zpowers c ≤ A := Subgroup.zpowers_le.2 hcA
  have hle : K₀ ≤ θ := by
    calc K₀ = ⁅K₀, Subgroup.zpowers c⁆ := hK₀c.symm
      _ ≤ θ := by
        rw [Subgroup.commutator_le]
        intro k hk a ha
        have hk' : k ∈ ((K₀ ⊓ K' : Subgroup G) : Set G) * (θ : Set G) := by
          rw [← sectionTenRel_iff.mp hrel]
          exact hk
        obtain ⟨m, hm, t, ht, rfl⟩ := hk'
        have hma : m * a = a * m := by
          obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
          have hmc : m * c = c * m :=
            Subgroup.mem_centralizer_singleton_iff.mp (hK'c (Subgroup.mem_inf.mp hm).2)
          exact (Commute.zpow_right (show Commute m c from hmc) i).eq
        have hta : a * t⁻¹ * a⁻¹ ∈ θ :=
          (Subgroup.mem_normalizer_iff.mp (hAθ (hzA ha)) t⁻¹).mp (θ.inv_mem ht)
        have h1 : ⁅t, a⁆ ∈ θ := by
          have e : ⁅t, a⁆ = t * (a * t⁻¹ * a⁻¹) := by simp [commutatorElement_def, mul_assoc]
          rw [e]
          exact θ.mul_mem ht hta
        have h2 : m * ⁅t, a⁆ * m⁻¹ ∈ θ :=
          (Subgroup.mem_normalizer_iff.mp (hK₀N (Subgroup.mem_inf.mp hm).1) _).mp h1
        have e : ⁅m * t, a⁆ = m * ⁅t, a⁆ * m⁻¹ * ⁅m, a⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e, Commute.commutator_eq (show Commute m a from hma), mul_one]
        exact h2
  obtain ⟨a, -, -, hKa⟩ := mem_thetaComponentFamily_iff.mp hK₀
  have hq := isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hKa
  have hcore : θ.subgroupOf K₀ = aschbacherSolvableCore p K₀ :=
    Subgroup.comap_map_eq_self_of_injective K₀.subtype_injective _
  have htop : aschbacherSolvableCore p K₀ = ⊤ := hcore ▸ Subgroup.subgroupOf_eq_top.mpr hle
  have hsub : Subsingleton (K₀ ⧸ aschbacherSolvableCore p K₀) :=
    (Nat.card_eq_one_iff_unique.1 ((Subgroup.index_eq_card _).symm.trans
      (Subgroup.index_eq_one.2 htop))).1
  have hsub2 : Subsingleton ((K₀ ⧸ aschbacherSolvableCore p K₀) ⧸
      Subgroup.center (K₀ ⧸ aschbacherSolvableCore p K₀)) :=
    (QuotientGroup.mk'_surjective _).subsingleton
  exact (not_nontrivial_iff_subsingleton.2 hsub2) hq.2.1.toNontrivial

omit [Finite G] in
theorem commutator_eq_of_ne_bot {K X : Subgroup G} (hK : CFSG.IsQuasisimple K)
    (hX : X ≤ Subgroup.normalizer (K : Set G)) (hne : ⁅K, X⁆ ≠ ⊥) : ⁅K, X⁆ = K := by
  have hle : ⁅K, X⁆ ≤ K := by
    rw [Subgroup.commutator_le]
    intro k hk a ha
    have h1 := K.mul_mem hk ((Subgroup.mem_normalizer_iff.mp (hX ha) k⁻¹).mp (K.inv_mem hk))
    simpa [commutatorElement_def, mul_assoc] using h1
  have hnorm : (⁅K, X⁆.subgroupOf K).Normal := by
    rw [Subgroup.normal_subgroupOf_iff_le_normalizer hle]
    have h1 := (Subgroup.normal_subgroupOf_iff_le_normalizer (CFSG.commutator_le_sup K X)).mp
      (CFSG.commutator_normal_in_sup K X)
    exact le_sup_left.trans h1
  rcases CFSG.LocalAnalysis.ComponentInitial.quasisimple_normal_subgroups hK hnorm with htop | hcen
  · exact le_antisymm hle (Subgroup.subgroupOf_eq_top.mp htop)
  · exfalso
    refine hne (CFSG.LocalAnalysis.ComponentInitial.perfect_double_commutator
      (Subgroup.isPerfect_iff.mp hK.1) ?_)
    rw [Subgroup.commutator_eq_bot_iff_le_centralizer]
    intro n hn k hk
    have hz : (⟨n, hle hn⟩ : K) ∈ Subgroup.center K := hcen (Subgroup.mem_subgroupOf.mpr hn)
    exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨k, hk⟩)

theorem exists_moved_component (hSchreier : SchreierFor InCatalog) (hTwoAction : TwoActionInputs)
    (h81 : SelectedPrimeElementsNormalizeThetaComponents)
    (h106 : SectionTenMaximalMovingThetaComponentsQuasisimple)
    (hTrans : SectionTenComponentSupplementTransitivity)
    (hSupp : SectionTenTrivialActorComponentSupplement)
    (hUp : SectionTenMovingTwoStratumUpwardClosure) (h105 : InSec10FivePlus)
    {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} (h : Sec12Hyp G p A c L E) :
    ∃ K : Subgroup G, K ∈ sectionTenZeroStar p A ∧ K ≠ ⊥ ∧ ⁅K, Subgroup.zpowers c⁆ = K := by
  have hp := h.prime
  have h3 := h.three_lt
  have : IsSimpleGroup G := h.setup.1
  have hev : evenRank G ≤ 3 := h.evenRank_eq.le
  have hAel := h.A_elem
  obtain ⟨K₀, hK₀z, hAK₀, hK₀c⟩ := h105 G p A h.setup c h.c_mem h.c_ne_one
  have hK₀F : K₀ ∈ thetaComponentFamily p A := hK₀z.1
  have htr : ∀ J ∈ thetaComponentFamily p A, ∀ K ∈ thetaComponentFamily p A,
      ∀ K' ∈ thetaComponentFamily p A, sectionTenRel p J K → sectionTenRel p K K' →
      sectionTenRel p J K' := fun J hJ K hK K' hK' =>
    hTrans hSchreier G h.setup.2.1 h.setup.2.2.1 hev p hp h3 A hAel J hJ K hK K' hK'
  obtain ⟨K, hKF, hK₀K, hstar⟩ := exists_maximal_above (sectionTenRel p)
    (thetaComponentFamily p A) (fun a _ => sectionTenRel_refl p a) htr hK₀F
  have hKz : K ∈ sectionTenZero p A :=
    hUp G hev p hp h3 (sectionTenSetup_vanishing h.setup) A hAel h.A_card K₀ hK₀F K hKF hK₀K hK₀z
  have hKzs : K ∈ sectionTenZeroStar p A := ⟨hKz, hKF, hstar⟩
  have hq : CFSG.IsQuasisimple K := h106 hSchreier hTwoAction G p A h.setup K hKzs
  have hAK : A ≤ Subgroup.normalizer (K : Set G) := h81.2 G hev p hp h3 A hAel K hKF
  have hzK : Subgroup.zpowers c ≤ Subgroup.normalizer (K : Set G) :=
    (Subgroup.zpowers_le.2 h.c_mem).trans hAK
  have hnot : ¬ ⁅K, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore p) K := by
    intro hle
    obtain ⟨K', hK'c, hKK'⟩ := hSupp hSchreier G h.setup.2.1 h.setup.2.2.1 hev p hp h3 A hAel c
      h.c_mem h.c_ne_one K hKF hle
    have hK'F : K' ∈ thetaComponentFamily p A :=
      mem_thetaComponentFamily_iff.mpr ⟨c, h.c_mem, h.c_ne_one, hK'c⟩
    exact not_sectionTenRel_of_moved hp h.c_mem hK₀F hAK₀ hK₀c
      (mem_thetaComponentsAt_iff.mp hK'c).1 (htr K₀ hK₀F K hKF K' hK'F hK₀K hKK')
  have hne : ⁅K, Subgroup.zpowers c⁆ ≠ ⊥ := fun hb => hnot (hb ▸ bot_le)
  exact ⟨K, hKzs, ne_bot_of_isQuasisimple hq, commutator_eq_of_ne_bot hq hzK hne⟩

end Sec125

end CFSG.RankThree.PartOne

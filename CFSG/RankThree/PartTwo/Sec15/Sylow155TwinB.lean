module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155B1
public import CFSG.RankThree.PartTwo.Sec15.Sylow155Twin
import CFSG.RankThree.PartTwo.Sec15.Sylow155TwinGrp
import CFSG.RankThree.PartTwo.Sec15.F153L3C2Local
import CFSG.RankThree.PartTwo.Sec14.Item14Tools
import CFSG.RankThree.GroupTheory.ComponentCubeObstruction
import CFSG.RankThree.Theta.ThreeCoreComponentNormalization
import CFSG.Quasithin.Vol2.Ch11SKFIto
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.RankThree.PartTwo.Sec15.Item153ClaimsTools

public section

namespace CFSG.RankThree.PartTwo.Sec15

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

namespace Sylow155T

theorem step_sup_zpowers {Q : Type*} [Group Q] [Finite Q] {E V : Subgroup Q} {f : Q}
    (hEc : IsMulCommutative E) (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hEV : E ≤ Subgroup.centralizer (V : Set Q)) (hfV : f ∈ V) (hf3 : f ^ 3 = 1)
    (hfC : f ∉ Subgroup.centralizer (V : Set Q)) :
    Nat.card ↥(E ⊔ Subgroup.zpowers f) = Nat.card E * 3 ∧
      IsMulCommutative ↥(E ⊔ Subgroup.zpowers f) ∧ ∀ x ∈ E ⊔ Subgroup.zpowers f, x ^ 3 = 1 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfo : orderOf f = 3 := orderOf_eq_prime hf3 fun h1 => hfC (by
    rw [h1]
    exact Subgroup.one_mem _)
  have hfE : f ∈ Subgroup.centralizer (E : Set Q) := by
    rw [Subgroup.mem_centralizer_iff]
    intro e he
    exact (Subgroup.mem_centralizer_iff.mp (hEV he) f hfV).symm
  have hdisj : E ⊓ Subgroup.zpowers f = ⊥ := by
    rw [inf_comm]
    exact CFSG.RankThree.zpowers_inf_eq_bot_of_not_mem Nat.prime_three hfo fun h1 => hfC (hEV h1)
  exact CFSG.RankThree.card_sup_zpowers_of_disjoint hfE hEc hE3 hfo hdisj

theorem exists_elemAbelian_card_eighty_one {Q : Type*} [Group Q] [Finite Q]
    {W₁ W₂ W₃ W₄ : Subgroup Q} {f₁ f₂ f₃ f₄ : Q}
    (hf₁ : f₁ ∈ W₁) (hf₂ : f₂ ∈ W₂) (hf₃ : f₃ ∈ W₃) (hf₄ : f₄ ∈ W₄)
    (h₁ : f₁ ^ 3 = 1) (h₂ : f₂ ^ 3 = 1) (h₃ : f₃ ^ 3 = 1) (h₄ : f₄ ^ 3 = 1)
    (hC₁ : f₁ ∉ Subgroup.centralizer (W₁ : Set Q)) (hC₂ : f₂ ∉ Subgroup.centralizer (W₂ : Set Q))
    (hC₃ : f₃ ∉ Subgroup.centralizer (W₃ : Set Q)) (hC₄ : f₄ ∉ Subgroup.centralizer (W₄ : Set Q))
    (c12 : W₁ ≤ Subgroup.centralizer (W₂ : Set Q)) (c13 : W₁ ≤ Subgroup.centralizer (W₃ : Set Q))
    (c14 : W₁ ≤ Subgroup.centralizer (W₄ : Set Q)) (c23 : W₂ ≤ Subgroup.centralizer (W₃ : Set Q))
    (c24 : W₂ ≤ Subgroup.centralizer (W₄ : Set Q)) (c34 : W₃ ≤ Subgroup.centralizer (W₄ : Set Q)) :
    ∃ E : Subgroup Q, IsMulCommutative E ∧ (∀ x ∈ E, x ^ 3 = 1) ∧ Nat.card E = 81 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfo : orderOf f₁ = 3 := orderOf_eq_prime h₁ fun h => hC₁ (by
    rw [h]
    exact Subgroup.one_mem _)
  have hE₁3 : ∀ x ∈ Subgroup.zpowers f₁, x ^ 3 = 1 := fun x hx => by
    rw [← hfo]
    exact CFSG.RankThree.pow_orderOf_eq_one_of_mem_zpowers hx
  have hE₁card : Nat.card (Subgroup.zpowers f₁) = 3 := by rw [Nat.card_zpowers, hfo]
  have hE₁W : Subgroup.zpowers f₁ ≤ W₁ := Subgroup.zpowers_le.mpr hf₁
  obtain ⟨hE₂card, hE₂c, hE₂3⟩ :=
    step_sup_zpowers inferInstance hE₁3 (hE₁W.trans c12) hf₂ h₂ hC₂
  have hE₂C₃ : Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ≤ Subgroup.centralizer (W₃ : Set Q) :=
    sup_le (hE₁W.trans c13) (Subgroup.zpowers_le.mpr (c23 hf₂))
  obtain ⟨hE₃card, hE₃c, hE₃3⟩ := step_sup_zpowers hE₂c hE₂3 hE₂C₃ hf₃ h₃ hC₃
  have hE₃C₄ : Subgroup.zpowers f₁ ⊔ Subgroup.zpowers f₂ ⊔ Subgroup.zpowers f₃ ≤
      Subgroup.centralizer (W₄ : Set Q) :=
    sup_le (sup_le (hE₁W.trans c14) (Subgroup.zpowers_le.mpr (c24 hf₂)))
      (Subgroup.zpowers_le.mpr (c34 hf₃))
  obtain ⟨hE₄card, hE₄c, hE₄3⟩ := step_sup_zpowers hE₃c hE₃3 hE₃C₄ hf₄ h₄ hC₄
  exact ⟨_, hE₄c, hE₄3, by omega⟩

theorem false_of_card_eighty_one {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {S : Set G} {M : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining S)
    {E : Subgroup (↥M ⧸ aschbacherSolvableCore 3 ↥M)} (hEc : IsMulCommutative E)
    (hE3 : ∀ x ∈ E, x ^ 3 = 1) (hE : Nat.card E = 81) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨-, -, hθ3, -⟩ :=
    solvable_prime_complement_core_characterization (H := ↥M) Nat.prime_three
  have h4Q : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (↥M ⧸ aschbacherSolvableCore 3 ↥M)) :=
    CFSG.SectionRank.le_pRank (by norm_num) le_top ⟨hEc, hE3⟩ (by rw [hE]; norm_num)
  have h4 : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥M) := by
    rwa [CFSG.SectionRank.pRank_quotient_eq _ hθ3] at h4Q
  have h4' : 4 ≤ CFSG.Open.pRank 3 M := by
    refine h4.trans ?_
    have := CFSG.RankThreeEvenClassification.Helpers.pRank_le_map_of_injective 3
      Nat.prime_three M.subtype M.subtype_injective ⊤
    rwa [← MonoidHom.range_eq_map, Subgroup.range_subtype] at this
  have h3 : CFSG.Open.pRank 3 M ≤ 3 :=
    (CFSG.RankThreeEvenClassification.Helpers.pRank_le_evenRank 3 Nat.prime_three
      (by norm_num) M hM.1.1).trans h.toTheoremFourHyp.evenRank_eq.le
  omega

theorem exists_pow_three_not_mem_centralizer {M X : Subgroup G} (hXM : X ∈ thetaComponentsIn M)
    (hX3 : X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ 3 ^ k = 1}) :
    ∃ f ∈ (X.subgroupOf M).map (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M)), f ^ 3 = 1 ∧
      f ∉ Subgroup.centralizer (((X.subgroupOf M).map
        (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥M)) :
          Subgroup (↥M ⧸ aschbacherSolvableCore 3 ↥M)) :
        Set (↥M ⧸ aschbacherSolvableCore 3 ↥M)) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXM', hY'⟩ := mem_thetaComponentsIn_iff.mp hXM
  set Y' := X.subgroupOf M with hY'def
  set θ := aschbacherSolvableCore 3 ↥M with hθ
  set π := QuotientGroup.mk' θ with hπ
  obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map Nat.prime_three hY'.2.1
  have hWq : CFSG.IsQuasisimple ↥(Y'.map π) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv η hY'.2.2
  have h3W : 3 ∣ Nat.card ↥(Y'.map π) := by
    by_contra h3
    have hcop : Nat.Coprime 3 (Nat.card ↥(Y'.map π)) :=
      (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr h3
    have hXθ : X ≤ θ.map M.subtype := by
      refine hX3.trans ((Subgroup.closure_le _).mpr ?_)
      rintro x ⟨hxX, k, hxk⟩
      have hxM := hXM' hxX
      have hy : π ⟨x, hxM⟩ ∈ Y'.map π :=
        Subgroup.mem_map_of_mem π (Subgroup.mem_subgroupOf.mpr hxX)
      have hxk' : (⟨x, hxM⟩ : ↥M) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hxk)
      have h1 : orderOf (π ⟨x, hxM⟩) ∣ 3 ^ k :=
        orderOf_dvd_of_pow_eq_one (by rw [← map_pow, hxk', map_one])
      have h2 : orderOf (π ⟨x, hxM⟩) ∣ Nat.card ↥(Y'.map π) :=
        Subgroup.orderOf_dvd_natCard _ hy
      have hg : Nat.gcd (3 ^ k) (Nat.card ↥(Y'.map π)) = 1 := Nat.Coprime.pow_left k hcop
      have h3' := Nat.dvd_gcd h1 h2
      rw [hg] at h3'
      have h4 : π ⟨x, hxM⟩ = 1 := orderOf_eq_one_iff.mp (Nat.dvd_one.mp h3')
      exact ⟨⟨x, hxM⟩, (QuotientGroup.eq_one_iff _).mp h4, rfl⟩
    have hWbot : ∀ w ∈ Y'.map π, w = 1 := by
      rintro _ ⟨y, hy, rfl⟩
      obtain ⟨t, ht, hty⟩ := hXθ (Subgroup.mem_subgroupOf.mp hy)
      rw [← (Subtype.ext hty : t = y)]
      exact (QuotientGroup.eq_one_iff t).mpr ht
    obtain ⟨-, -, a, b, hab⟩ := hWq
    obtain ⟨a, rfl⟩ := QuotientGroup.mk_surjective a
    obtain ⟨b, rfl⟩ := QuotientGroup.mk_surjective b
    have ha : a = 1 := Subtype.ext (hWbot _ a.2)
    have hb : b = 1 := Subtype.ext (hWbot _ b.2)
    exact hab (by rw [ha, hb])
  haveI : Group.IsPerfect ↥(Y'.map π) := hWq.1
  obtain ⟨f, hf3, hfc⟩ :=
    CFSG.Quasithin.Vol2.Ch11.SecS.KF.exists_pow_eq_one_not_mem_center (p := 3) (by norm_num) h3W
  refine ⟨f, f.2, by simpa using congrArg Subtype.val hf3, fun hfC => hfc ?_⟩
  rw [Subgroup.mem_center_iff]
  intro g
  exact Subtype.ext (Subgroup.mem_centralizer_iff.mp hfC g g.2)

theorem false_of_four_conj {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {S : Set G} {M X : Subgroup G} (hM : M ∈ CFSG.maximalTwoLocalsContaining S)
    (hXM : X ∈ thetaComponentsIn M)
    (hX3 : X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ 3 ^ k = 1}) {g₁ g₂ g₃ : ↥M}
    (h1 : (g₁ : G) ∉ Subgroup.normalizer (X : Set G))
    (h2 : (g₂ : G) ∉ Subgroup.normalizer (X : Set G))
    (h3 : (g₃ : G) ∉ Subgroup.normalizer (X : Set G))
    (h12 : (g₁ : G)⁻¹ * g₂ ∉ Subgroup.normalizer (X : Set G))
    (h13 : (g₁ : G)⁻¹ * g₃ ∉ Subgroup.normalizer (X : Set G))
    (h23 : (g₂ : G)⁻¹ * g₃ ∉ Subgroup.normalizer (X : Set G)) : False := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hXM', hY'⟩ := mem_thetaComponentsIn_iff.mp hXM
  set Y' := X.subgroupOf M with hY'def
  set θ := aschbacherSolvableCore 3 ↥M with hθ
  set π := QuotientGroup.mk' θ with hπ
  obtain ⟨f, hfW, hf3, hfC⟩ : ∃ f ∈ Y'.map π, f ^ 3 = 1 ∧
      f ∉ Subgroup.centralizer ((Y'.map π : Subgroup (↥M ⧸ θ)) : Set (↥M ⧸ θ)) :=
    exists_pow_three_not_mem_centralizer hXM hX3
  have hYY' : Y'.map M.subtype = X := by
    rw [hY'def, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hXM']
  have hmapc : ∀ g : ↥M, (Y'.map (MulAut.conj g).toMonoidHom).map M.subtype =
      X.map (MulAut.conj (g : G)).toMonoidHom := by
    intro g
    rw [← hYY', Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hconj : ∀ (g : ↥M) (K : Subgroup ↥M),
      (K.map π).map (MulAut.conj (π g)).toMonoidHom =
        (K.map (MulAut.conj g).toMonoidHom).map π := by
    intro g K
    rw [Subgroup.map_map, Subgroup.map_map]
    congr 1
  have hYc : ∀ g : ↥M, Y'.map (MulAut.conj g).toMonoidHom ∈ thetaComponents 3 ↥M := fun g =>
    map_mulEquiv_mem_thetaComponents Nat.prime_three (MulAut.conj g) hY'
  have hcW : ∀ g g' : ↥M, (g : G)⁻¹ * g' ∉ Subgroup.normalizer (X : Set G) →
      (Y'.map (MulAut.conj g).toMonoidHom).map π ≤ Subgroup.centralizer
        (((Y'.map (MulAut.conj g').toMonoidHom).map π : Subgroup (↥M ⧸ θ)) :
          Set (↥M ⧸ θ)) := by
    intro g g' hgg'
    have hne : Y'.map (MulAut.conj g).toMonoidHom ≠ Y'.map (MulAut.conj g').toMonoidHom := by
      intro he
      apply hgg'
      have h1 : X.map (MulAut.conj (g' : G)).toMonoidHom =
          X.map (MulAut.conj (g : G)).toMonoidHom := by
        rw [← hmapc, ← hmapc, he]
      exact CFSG.RankThree.Theta.mem_normalizer_of_map_conj_eq h1
    have cc := commutator_le_of_mem_thetaComponents (hYc g) (hYc g') hne
    rintro _ ⟨a, ha, rfl⟩
    rw [Subgroup.mem_centralizer_iff]
    rintro _ ⟨b, hb, rfl⟩
    have h1 : π ⁅a, b⁆ = 1 :=
      (QuotientGroup.eq_one_iff _).mpr (cc (Subgroup.commutator_mem_commutator ha hb))
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm
  have hfg : ∀ g : ↥M, π g * f * (π g)⁻¹ ∈ (Y'.map (MulAut.conj g).toMonoidHom).map π := by
    intro g
    rw [← hconj]
    exact ⟨f, hfW, by simp⟩
  have hf3g : ∀ g : ↥M, (π g * f * (π g)⁻¹) ^ 3 = 1 := fun g => by
    rw [conj_pow, hf3, mul_one, mul_inv_cancel]
  have hfCg : ∀ g : ↥M, π g * f * (π g)⁻¹ ∉ Subgroup.centralizer
      (((Y'.map (MulAut.conj g).toMonoidHom).map π : Subgroup (↥M ⧸ θ)) : Set (↥M ⧸ θ)) := by
    intro g
    rw [← hconj, CFSG.RankThree.conj_mem_centralizer_map_conj_iff]
    exact hfC
  obtain ⟨E, hEc, hE3, hE81⟩ := exists_elemAbelian_card_eighty_one
    (hfg 1) (hfg g₁) (hfg g₂) (hfg g₃) (hf3g 1) (hf3g g₁) (hf3g g₂) (hf3g g₃)
    (hfCg 1) (hfCg g₁) (hfCg g₂) (hfCg g₃)
    (hcW 1 g₁ (by simpa using h1)) (hcW 1 g₂ (by simpa using h2)) (hcW 1 g₃ (by simpa using h3))
    (hcW g₁ g₂ h12) (hcW g₁ g₃ h13) (hcW g₂ g₃ h23)
  exact false_of_card_eighty_one h hM hEc hE3 hE81

theorem exists_three_of_four_le_index {H : Type*} [Group H] [Finite H] {K : Subgroup H}
    (h4 : 4 ≤ K.index) :
    ∃ v₁ v₂ v₃ : H, v₁ ∉ K ∧ v₂ ∉ K ∧ v₃ ∉ K ∧ v₁⁻¹ * v₂ ∉ K ∧ v₁⁻¹ * v₃ ∉ K ∧
      v₂⁻¹ * v₃ ∉ K := by
  classical
  haveI : Fintype (H ⧸ K) := Fintype.ofFinite _
  obtain ⟨e⟩ : Nonempty (Fin 4 ↪ H ⧸ K) := Function.Embedding.nonempty_of_card_le (by
    rw [Fintype.card_fin, ← Nat.card_eq_fintype_card]
    exact h4)
  have hw : ∀ i j, ((e i).out)⁻¹ * (e j).out ∈ K ↔ i = j := by
    intro i j
    rw [← QuotientGroup.eq, QuotientGroup.out_eq', QuotientGroup.out_eq', e.injective.eq_iff]
  have hw' : ∀ i j k, ((e i).out⁻¹ * (e j).out)⁻¹ * ((e i).out⁻¹ * (e k).out) =
      (e j).out⁻¹ * (e k).out := fun i j k => by group
  refine ⟨(e 0).out⁻¹ * (e 1).out, (e 0).out⁻¹ * (e 2).out, (e 0).out⁻¹ * (e 3).out,
    ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hw]; decide
  · rw [hw]; decide
  · rw [hw]; decide
  · rw [hw', hw]; decide
  · rw [hw', hw]; decide
  · rw [hw', hw]; decide

theorem false_of_index_two {A M X V : Subgroup G} (hA : A ∈ partTwoF G) (hAM : A ≤ M)
    (hXM : X ∈ thetaComponentsIn M) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hX3 : X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ 3 ^ k = 1})
    (hZ : Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) ≤ 3)
    (hVM : V ≤ M) (hV3 : ¬ 3 ∣ Nat.card V) (hAV : A ≤ Subgroup.normalizer (V : Set G))
    (h2 : ((Subgroup.normalizer (X : Set G)).subgroupOf V).index = 2) : False := by
  classical
  obtain ⟨y, hyV, hyN⟩ : ∃ y ∈ V, y ∉ Subgroup.normalizer (X : Set G) := by
    by_contra hall
    push Not at hall
    have htop : (Subgroup.normalizer (X : Set G)).subgroupOf V = ⊤ :=
      eq_top_iff.mpr fun v _ => Subgroup.mem_subgroupOf.mpr (hall v v.2)
    rw [htop, Subgroup.index_top] at h2
    exact absurd h2 (by norm_num)
  have hAN : A ≤ Subgroup.normalizer
      ((V ⊓ Subgroup.normalizer (X : Set G) : Subgroup G) : Set G) :=
    le_normalizer_inf_of_le hAV (hAX.trans Subgroup.le_normalizer)
  have hN3 : ¬ 3 ∣ Nat.card ↥(V ⊓ Subgroup.normalizer (X : Set G)) := fun h3 =>
    hV3 (h3.trans (Subgroup.card_dvd_of_le inf_le_left))
  have hAp : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hA.1.2 _ a.2)⟩
  have hmul : ∀ u ∈ V, ∀ v ∈ V, u * v ∈ Subgroup.normalizer (X : Set G) ↔
      (u ∈ Subgroup.normalizer (X : Set G) ↔ v ∈ Subgroup.normalizer (X : Set G)) := by
    intro u hu v hv
    have := Subgroup.mul_mem_iff_of_index_two h2 (a := ⟨u, hu⟩) (b := ⟨v, hv⟩)
    simpa [Subgroup.mem_subgroupOf] using this
  have hy : ∀ a ∈ A, y⁻¹ * (a * y * a⁻¹) ∈ V ⊓ Subgroup.normalizer (X : Set G) := by
    intro a ha
    have hayV : a * y * a⁻¹ ∈ V := (Subgroup.mem_normalizer_iff.mp (hAV ha) y).mp hyV
    have hayN : a * y * a⁻¹ ∉ Subgroup.normalizer (X : Set G) := fun h' =>
      hyN ((Subgroup.mem_normalizer_iff.mp ((hAX.trans Subgroup.le_normalizer) ha) y).mpr h')
    refine ⟨V.mul_mem (V.inv_mem hyV) hayV, (hmul _ (V.inv_mem hyV) _ hayV).mpr ?_⟩
    exact ⟨fun h' => absurd (by simpa using (Subgroup.normalizer (X : Set G)).inv_mem h') hyN,
      fun h' => absurd h' hayN⟩
  obtain ⟨n, hnN, hcA⟩ := F153L3C2.aux_exists_fixed_mem_coset Nat.prime_three hAp hAN hN3 hy
  have hcV : y * n ∈ V := V.mul_mem hyV hnN.1
  have hcN : y * n ∉ Subgroup.normalizer (X : Set G) := fun h' => hyN (by
    have := (Subgroup.normalizer (X : Set G)).mul_mem h'
      ((Subgroup.normalizer (X : Set G)).inv_mem hnN.2)
    simpa using this)
  have hc2 : (y * n) ^ 2 ∈ Subgroup.normalizer (X : Set G) := by
    rw [pow_two]
    exact (hmul _ hcV _ hcV).mpr Iff.rfl
  exact hcN (Subgroup.mem_normalizer_iff_map_conj_eq.mpr
    (map_conj_eq_of_sq hA hAM hXM hAX hX3 hZ (hVM hcV) hcA
      (Subgroup.mem_normalizer_iff_map_conj_eq.mp hc2)))

theorem le_normalizer_of_invariant {A : Subgroup G} {c : G} {L : Subgroup G}
    (h : Sec14Std G A c L) {S : Set G} {M X V : Subgroup G}
    (hM : M ∈ CFSG.maximalTwoLocalsContaining S) (hAM : A ≤ M)
    (hXM : X ∈ thetaComponentsIn M) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hX3 : X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ 3 ^ k = 1})
    (hZ : Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) ≤ 3)
    (hVM : V ≤ M) (hV3 : ¬ 3 ∣ Nat.card V) (hAV : A ≤ Subgroup.normalizer (V : Set G)) :
    V ≤ Subgroup.normalizer (X : Set G) := by
  classical
  have hA : A ∈ partTwoF G := h.mem_partTwoF
  have hidx3 : ¬ 3 ∣ ((Subgroup.normalizer (X : Set G)).subgroupOf V).index := fun h3 =>
    hV3 (h3.trans (Subgroup.index_dvd_card _))
  have hidx0 : 0 < ((Subgroup.normalizer (X : Set G)).subgroupOf V).index :=
    Nat.pos_of_dvd_of_pos (Subgroup.index_dvd_card _) Nat.card_pos
  by_cases h1 : ((Subgroup.normalizer (X : Set G)).subgroupOf V).index = 1
  · intro v hv
    rw [Subgroup.index_eq_one] at h1
    have hv' : (⟨v, hv⟩ : ↥V) ∈ (Subgroup.normalizer (X : Set G)).subgroupOf V := by
      rw [h1]
      exact Subgroup.mem_top _
    exact Subgroup.mem_subgroupOf.mp hv'
  exfalso
  by_cases h2 : ((Subgroup.normalizer (X : Set G)).subgroupOf V).index = 2
  · exact false_of_index_two hA hAM hXM hAX hX3 hZ hVM hV3 hAV h2
  · have h4 : 4 ≤ ((Subgroup.normalizer (X : Set G)).subgroupOf V).index := by omega
    obtain ⟨v₁, v₂, v₃, h1K, h2K, h3K, h12K, h13K, h23K⟩ := exists_three_of_four_le_index h4
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h1K h2K h3K
    simp only [Subgroup.mem_subgroupOf, Subgroup.coe_mul, Subgroup.coe_inv] at h12K h13K h23K
    exact false_of_four_conj h hM hXM hX3 (g₁ := ⟨v₁, hVM v₁.2⟩) (g₂ := ⟨v₂, hVM v₂.2⟩)
      (g₃ := ⟨v₃, hVM v₃.2⟩) h1K h2K h3K h12K h13K h23K

theorem delta_le_normalizer {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {S : Set G} {M X : Subgroup G} (hM : M ∈ CFSG.maximalTwoLocalsContaining S) (hAM : A ≤ M)
    (hXM : X ∈ thetaComponentsIn M) (hAX : A ≤ Subgroup.normalizer (X : Set G))
    (hX3 : X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ 3 ^ k = 1})
    (hZ : Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) ≤ 3) :
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) :=
  sSup_le fun V hV => le_normalizer_of_invariant h hM hAM hXM hAX hX3 hZ hV.2
    ((isPiSubgroup_piCompl_iff Nat.prime_three V).mp hV.1.1.2.1) hV.1.1.2.2

theorem le_closure_of_ctx155 {A X K Y M T : Subgroup G} (hC : Ctx155 A X K Y M T) :
    X ≤ Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} := by
  have hX : X = Subgroup.closure {x | x ∈ Y ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} := by
    rw [← hC.res, oPrimeResidualOf_eq_closure]
  calc X = Subgroup.closure {x | x ∈ Y ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} := hX
    _ ≤ Subgroup.closure {x | x ∈ X ∧ ∃ k : ℕ, x ^ 3 ^ k = 1} :=
      Subgroup.closure_mono fun x hx => ⟨hX ▸ Subgroup.subset_closure hx, hx.2⟩

theorem delta_le_normalizer_x {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec14Std G A c L)
    {X K Y M T P : Subgroup G} (hC : Ctx155 A X K Y M T) (hE : End155N A X K Y M T P)
    (hZ : Nat.card (Subgroup.center (↥X ⧸ aschbacherSolvableCore 3 ↥X)) ≤ 3) :
    delta A (lB A) M ≤ Subgroup.normalizer (X : Set G) :=
  delta_le_normalizer h hC.mem_m (fun _ ha => hC.mem_m.2 (Subgroup.mem_sup_left ha)) hE.mem_x
    (Sylow155B1.le_normalizer_x hC) (le_closure_of_ctx155 hC) hZ

end Sylow155T

end CFSG.RankThree.PartTwo.Sec15

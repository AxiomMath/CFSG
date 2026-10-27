module

public import CFSG.GroupTheory.ThreeTranspositions.FischerResidualConj
public import CFSG.RankThree.GF2n.Stroth78.Sec2Six
public import CFSG.RankThree.GF2n.Stroth78.Sec4PSURigid
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeLift
public import CFSG.RankThree.GF2n.Stroth78.Sec4ThreeZQ

import CFSG.GroupTheory.ThreeTranspositions.FischerResidualConjBase
import CFSG.RankThree.GF2n.Stroth78.Sec4PSUFix
import CFSG.RankThree.GF2n.Stroth78.Sec4Two

public section

namespace CFSG.RankThree.GF2n.Stroth78

open CFSG CFSG.Open CFSG.RankThree.GF2n.Tim79a CFSG.LargeExtraspecial.Timmesfeld
open CFSG.Timmesfeld
open CFSG.RankThree.OrthogonalInvolutions Module
open CFSG.GroupTheory.ThreeTranspositions
open CFSG.Fischer.Classification CFSG.Fischer.Classification.Unitary

namespace Sec4PSU

theorem exists_lift_oddOrderClosure {X : Type*} [Group X] [Finite X]
    (hZ : Odd (Nat.card (Subgroup.center X)))
    {Y : Subgroup X} {d : X} (hdY : d ∈ Y) (hd : d * d = 1)
    {W₁ : Subgroup (X ⧸ Subgroup.center X)}
    (hW₁ : W₁ ≤ ⁅⁅Y.map (QuotientGroup.mk' (Subgroup.center X)) ⊓
        Subgroup.centralizer {QuotientGroup.mk' (Subgroup.center X) d},
      Y.map (QuotientGroup.mk' (Subgroup.center X)) ⊓
        Subgroup.centralizer {QuotientGroup.mk' (Subgroup.center X) d}⁆,
      ⁅Y.map (QuotientGroup.mk' (Subgroup.center X)) ⊓
        Subgroup.centralizer {QuotientGroup.mk' (Subgroup.center X) d},
      Y.map (QuotientGroup.mk' (Subgroup.center X)) ⊓
        Subgroup.centralizer {QuotientGroup.mk' (Subgroup.center X) d}⁆⁆)
    (hodd : CFSG.GroupTheory.oddOrderClosure W₁ = W₁) :
    ∃ J : Subgroup X,
      J ≤ ⁅⁅Y ⊓ Subgroup.centralizer {d}, Y ⊓ Subgroup.centralizer {d}⁆,
        ⁅Y ⊓ Subgroup.centralizer {d}, Y ⊓ Subgroup.centralizer {d}⁆⁆ ∧
      CFSG.GroupTheory.oddOrderClosure J = J ∧
      J.map (QuotientGroup.mk' (Subgroup.center X)) = W₁ := by
  classical
  set π := QuotientGroup.mk' (Subgroup.center X) with hπ
  set C := Y ⊓ Subgroup.centralizer {d} with hC
  have hker : ∀ ζ : X, π ζ = 1 → ζ ∈ Subgroup.center X := fun ζ h =>
    (QuotientGroup.eq_one_iff ζ).1 h
  have hCmap : Y.map π ⊓ Subgroup.centralizer {π d} = C.map π := by
    apply le_antisymm
    · rintro _ ⟨⟨y, hyY, rfl⟩, hyc0⟩
      have hyc : π y * π d = π d * π y := Subgroup.mem_centralizer_singleton_iff.1 hyc0
      set ζ := y * d * y⁻¹ * d⁻¹ with hζdef
      have hζ : ζ ∈ Subgroup.center X := hker ζ (by
        rw [hζdef, map_mul, map_mul, map_mul, map_inv, map_inv, hyc]
        group)
      have hzζ : d * ζ = ζ * d := Subgroup.mem_center_iff.1 hζ d
      have hyd : y * d * y⁻¹ = ζ * d := by rw [hζdef]; group
      have hsq : ζ ^ 2 = 1 := by
        have e1 : (y * d * y⁻¹) * (y * d * y⁻¹) = 1 := by
          calc (y * d * y⁻¹) * (y * d * y⁻¹) = y * (d * d) * y⁻¹ := by group
            _ = 1 := by rw [hd]; group
        rw [hyd] at e1
        calc ζ ^ 2 = ζ * ζ * (d * d) := by rw [hd, mul_one, sq]
          _ = ζ * (d * ζ) * d := by rw [hzζ]; group
          _ = ζ * d * (ζ * d) := by group
          _ = 1 := e1
      have hζ1 : ζ = 1 := by
        have hdvd : orderOf ζ ∣ 2 := orderOf_dvd_of_pow_eq_one hsq
        have hoddζ : Odd (orderOf ζ) := by
          have := orderOf_dvd_natCard (⟨ζ, hζ⟩ : Subgroup.center X)
          rw [Subgroup.orderOf_mk] at this
          exact Odd.of_dvd_nat hZ this
        rcases (Nat.dvd_prime Nat.prime_two).1 hdvd with h1 | h2
        · exact orderOf_eq_one_iff.1 h1
        · rw [h2] at hoddζ
          exact absurd hoddζ (by decide)
      have hydc : y * d = d * y := by
        have : y * d * y⁻¹ = d := by rw [hyd, hζ1, one_mul]
        calc y * d = y * d * y⁻¹ * y := by group
          _ = d * y := by rw [this]
      exact ⟨y, ⟨hyY, Subgroup.mem_centralizer_singleton_iff.2 hydc⟩, rfl⟩
    · rintro _ ⟨y, ⟨hyY, hyc0⟩, rfl⟩
      refine ⟨⟨y, hyY, rfl⟩, ?_⟩
      have hyc : y * d = d * y := Subgroup.mem_centralizer_singleton_iff.1 hyc0
      exact Subgroup.mem_centralizer_singleton_iff.2 (by rw [← map_mul, hyc, map_mul])
  rw [hCmap, ← Subgroup.map_commutator, ← Subgroup.map_commutator] at hW₁
  set J₀ := ⁅⁅C, C⁆, ⁅C, C⁆⁆ ⊓ W₁.comap π with hJ₀
  refine ⟨CFSG.GroupTheory.oddOrderClosure J₀,
    (CFSG.GroupTheory.oddOrderClosure_le _).trans inf_le_left,
    CFSG.GroupTheory.oddOrderClosure_oddOrderClosure _, le_antisymm ?_ ?_⟩
  · exact (Subgroup.map_mono (CFSG.GroupTheory.oddOrderClosure_le _)).trans
      (Subgroup.map_le_iff_le_comap.2 inf_le_right)
  · rw [← hodd, CFSG.GroupTheory.oddOrderClosure_le_iff]
    rintro xb ⟨hxW, hxodd⟩
    obtain ⟨x, hxC, rfl⟩ := hW₁ hxW
    refine ⟨x, CFSG.GroupTheory.mem_oddOrderClosure_of_mem_of_odd ⟨hxC, hxW⟩ ?_, rfl⟩
    set o := orderOf (π x) with ho
    have hxo : x ^ o ∈ Subgroup.center X := hker _ (by rw [map_pow, ho, pow_orderOf_eq_one])
    have hz1 : (x ^ o) ^ Nat.card (Subgroup.center X) = 1 := by
      have h := pow_card_eq_one' (G := Subgroup.center X) (x := ⟨x ^ o, hxo⟩)
      have h2 := congrArg Subtype.val h
      rwa [SubgroupClass.coe_pow, OneMemClass.coe_one] at h2
    rw [← pow_mul] at hz1
    exact Odd.of_dvd_nat (Nat.odd_mul.2 ⟨hxodd, hZ⟩) (orderOf_dvd_of_pow_eq_one hz1)

theorem fischerCentralQuotientModel_of_isConj {X : Type} [Group X] {d d₀ : X}
    (hc : IsConj d d₀) {ι F : Type*} [Fintype ι] [DecidableEq ι] [CommRing F]
    {H : Subgroup (GL ι F)} {T : Set (GL ι F)}
    (h : CFSG.Open.fischerCentralQuotientModel (threeResidualClass d) H T) :
    CFSG.Open.fischerCentralQuotientModel (threeResidualClass d₀) H T := by
  obtain ⟨c, rfl⟩ := isConj_iff.1 hc
  exact fischerCentralQuotientModel_conj h

variable {G : Type} [Group G] [Finite G] {z : G} {E F : Subgroup G}

theorem exists_mem_Rbar_mulEquiv_U2 (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    (h217 : ∀ Y : Subgroup (Hbar z), CFSG.GroupTheory.oddOrderClosure Y = Y →
      (∀ P : Subgroup (Hbar z), P ≤ Y → IsPGroup 2 P →
        Y ≤ Subgroup.normalizer (P : Set (Hbar z)) → P = ⊥) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, y * r = r * y) →
      (∀ y ∈ Y, ∀ r ∈ Rbar S a, ∀ v ∈ commSpace (rhoLin S r), rhoLin S y v = v) →
      aVec S h.mem_Q ∉ (⨆ y ∈ Y, commSpace (rhoLin S y)) →
      Lbar S a ≤ Subgroup.normalizer (Y : Set (Hbar z)) →
      Rbar S a = ⊥ ∨ Y = ⊥)
    (h3 : ∀ α ∈ Eset S a, ∀ α' ∈ Eset S a, orderOf (α * α') ≤ 3)
    {α : Hbar z} (hα : α ∈ Tset S a) {m : ℕ}
    (hpsu : CFSG.Open.fischerCentralQuotientModel
      (threeResidualClass
        (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)))
      (SUm m) (TU m)) :
    ∃ d₀ : ↥(Xsub S a), (d₀ : Hbar z) ∈ Rbar S a ∧ (d₀ : Hbar z) ≠ 1 ∧
      ∃ φ : ↥(threeResidualQuot d₀) ≃* U2 m, φ '' threeResidualClass d₀ = DU m := by
  obtain ⟨⟨α₀, hα₀R⟩, hα₀1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp h.Rbar_ne_bot
  have hα₀1' : α₀ ≠ 1 := fun h1 => hα₀1 (Subtype.ext h1)
  have hα₀E : α₀ ∈ Eset S a :=
    Tset_subset_Eset S a (h.mem_Tset_of_mem_Rbar hα₀R hα₀1')
  set d₀ : ↥(Xsub S a) := ⟨α₀, subset_Xsub S a hα₀E⟩ with hd₀
  obtain ⟨-, ⟨e, hE⟩, -, -, -⟩ := pair_Xsub S h h217 h3
  have hd : (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)) ∈
      (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) := Tset_subset_Eset S a hα
  have hd₀E : d₀ ∈ (Subtype.val ⁻¹' Eset S a : Set ↥(Xsub S a)) := hα₀E
  rw [hE] at hd hd₀E
  have hc : IsConj (⟨α, subset_Xsub S a (Tset_subset_Eset S a hα)⟩ : ↥(Xsub S a)) d₀ :=
    (isConj_comm.1 hd).trans hd₀E
  obtain ⟨φ, hφ⟩ := fischerCentralQuotientModel_iff_U2.1
    (fischerCentralQuotientModel_of_isConj hc hpsu)
  exact ⟨d₀, hα₀R, hα₀1', φ, hφ⟩

theorem mk_self_mem_threeResidualClass {X : Type} [Group X] (d : X) :
    (⟨QuotientGroup.mk d, Subgroup.mem_map_of_mem _
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers d))⟩ : ↥(threeResidualQuot d)) ∈
      threeResidualClass d :=
  ⟨1, Subgroup.one_mem _, by simp⟩

theorem map_oddOrderClosure_of_injective {X Y : Type*} [Group X] [Group Y] {f : X →* Y}
    (hf : Function.Injective f) (K : Subgroup X) :
    (CFSG.GroupTheory.oddOrderClosure K).map f =
      CFSG.GroupTheory.oddOrderClosure (K.map f) := by
  apply le_antisymm (CFSG.GroupTheory.map_oddOrderClosure_le f K)
  rw [CFSG.GroupTheory.oddOrderClosure_le_iff]
  rintro _ ⟨⟨x, hx, rfl⟩, hodd⟩
  refine ⟨x, CFSG.GroupTheory.mem_oddOrderClosure_of_mem_of_odd hx ?_, rfl⟩
  rwa [orderOf_injective f hf] at hodd

attribute [local instance] Xsub_normal

theorem exists_lift_mem_CH (S : Setting z E F) {a : G} {w : ℕ} (h : Sec3Hyp S a w)
    {d₀ : ↥(Xsub S a)} (hd₀R : (d₀ : Hbar z) ∈ Rbar S a) (hd₀1 : (d₀ : Hbar z) ≠ 1)
    (hA : ∀ j ∈ ⁅⁅threeResidualJoin d₀, threeResidualJoin d₀⁆,
        ⁅threeResidualJoin d₀, threeResidualJoin d₀⁆⁆, rhoZ S (j : Hbar z) = 1)
    {W' : Subgroup ↥(threeResidualQuot d₀)}
    (hW' : W' ≤ ⁅⁅Subgroup.centralizer {(⟨QuotientGroup.mk d₀,
          mk_mem_threeResidualQuot_self d₀⟩ : ↥(threeResidualQuot d₀))},
        Subgroup.centralizer {(⟨QuotientGroup.mk d₀,
          mk_mem_threeResidualQuot_self d₀⟩ : ↥(threeResidualQuot d₀))}⁆,
      ⁅Subgroup.centralizer {(⟨QuotientGroup.mk d₀,
          mk_mem_threeResidualQuot_self d₀⟩ : ↥(threeResidualQuot d₀))},
        Subgroup.centralizer {(⟨QuotientGroup.mk d₀,
          mk_mem_threeResidualQuot_self d₀⟩ : ↥(threeResidualQuot d₀))}⁆⁆)
    (hodd : CFSG.GroupTheory.oddOrderClosure W' = W') :
    ∀ x ∈ W', ∃ j : ↥(Xsub S a), j ∈ threeResidualJoin d₀ ∧ j * d₀ = d₀ * j ∧
      (j : Hbar z) ∈ CH a ∧
      (QuotientGroup.mk j : ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) = x := by
  classical
  set Y := threeResidualJoin d₀ with hY
  set π := QuotientGroup.mk' (Subgroup.center ↥(Xsub S a)) with hπ
  set dY : ↥(threeResidualQuot d₀) :=
    ⟨QuotientGroup.mk d₀, mk_mem_threeResidualQuot_self d₀⟩ with hdY
  have hdYY : d₀ ∈ Y := Subgroup.mem_sup_right (Subgroup.mem_zpowers d₀)
  have hd : d₀ * d₀ = 1 := by
    apply Subtype.ext
    have := sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj (Rbar_le_Lbar S a hd₀R)
    rw [Subgroup.coe_mul, OneMemClass.coe_one]
    rwa [pow_two] at this
  set W₁ := W'.map (threeResidualQuot d₀).subtype with hW₁
  have hCmap : (Subgroup.centralizer {dY}).map (threeResidualQuot d₀).subtype ≤
      Y.map π ⊓ Subgroup.centralizer {π d₀} := by
    rintro _ ⟨y, hy, rfl⟩
    refine ⟨y.2, Subgroup.mem_centralizer_singleton_iff.2 ?_⟩
    exact congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hy)
  have hW₁le : W₁ ≤ ⁅⁅Y.map π ⊓ Subgroup.centralizer {π d₀},
        Y.map π ⊓ Subgroup.centralizer {π d₀}⁆,
      ⁅Y.map π ⊓ Subgroup.centralizer {π d₀}, Y.map π ⊓ Subgroup.centralizer {π d₀}⁆⁆ := by
    refine (Subgroup.map_mono hW').trans ?_
    simp only [Subgroup.map_commutator]
    exact Subgroup.commutator_mono (Subgroup.commutator_mono hCmap hCmap)
      (Subgroup.commutator_mono hCmap hCmap)
  have hW₁odd : CFSG.GroupTheory.oddOrderClosure W₁ = W₁ := by
    rw [hW₁, ← map_oddOrderClosure_of_injective (Subgroup.subtype_injective _), hodd]
  obtain ⟨J, hJle, hJodd, hJmap⟩ :=
    exists_lift_oddOrderClosure (odd_card_center_Xsub S a) hdYY hd hW₁le hW₁odd
  set J' := J.map (Xsub S a).subtype with hJ'
  obtain ⟨hA2, haV⟩ := mem_A2set_and_aVec_mem_of_mem_Rbar h hd₀R hd₀1
  have hYC : (Y ⊓ Subgroup.centralizer {d₀}).map (Xsub S a).subtype ≤
      Subgroup.centralizer {(d₀ : Hbar z)} := by
    rintro _ ⟨y, ⟨-, hyc⟩, rfl⟩
    exact Subgroup.mem_centralizer_singleton_iff.2
      (congrArg Subtype.val (Subgroup.mem_centralizer_singleton_iff.1 hyc))
  have hJ'C : J' ≤ ⁅⁅Subgroup.centralizer {(d₀ : Hbar z)}, Subgroup.centralizer {(d₀ : Hbar z)}⁆,
      ⁅Subgroup.centralizer {(d₀ : Hbar z)}, Subgroup.centralizer {(d₀ : Hbar z)}⁆⁆ := by
    refine (Subgroup.map_mono hJle).trans ?_
    simp only [Subgroup.map_commutator]
    exact Subgroup.commutator_mono (Subgroup.commutator_mono hYC hYC)
      (Subgroup.commutator_mono hYC hYC)
  have hfix : ∀ y ∈ J', rhoLin S y (aVec S h.mem_Q) = aVec S h.mem_Q := fun y hy =>
    (mem_commSpaceFixer S _).1
      (commutator_commutator_centralizer_le_commSpaceFixer S hA2 (hJ'C hy)) _ haV
  have hJY : J ≤ ⁅⁅Y, Y⁆, ⁅Y, Y⁆⁆ := hJle.trans
    (Subgroup.commutator_mono (Subgroup.commutator_mono inf_le_left inf_le_left)
      (Subgroup.commutator_mono inf_le_left inf_le_left))
  have hPZ : ∀ x : ↥(H z), QuotientGroup.mk x ∈ J' → ∀ v ∈ ZQ z,
      (x : G) * v * (x : G)⁻¹ = v := by
    rintro x ⟨j, hjJ, hjx⟩ v hv
    have h1 : rhoZ S (QuotientGroup.mk x) = 1 := by
      rw [← hjx]
      exact hA j (hJY hjJ)
    have h2 := rhoZ_mk S x ⟨v, hv⟩
    rw [h1, MulAut.one_apply] at h2
    exact h2.symm
  have hJ'odd : CFSG.GroupTheory.oddOrderClosure J' = J' := by
    rw [hJ', ← map_oddOrderClosure_of_injective (Subgroup.subtype_injective _), hJodd]
  have hJ'CH : J' ≤ CH a := le_CH_of_oddOrderClosure h.mem_Q hfix hPZ hJ'odd
  intro x hx
  have hx₁ : (x : ↥(Xsub S a) ⧸ Subgroup.center ↥(Xsub S a)) ∈ J.map π := by
    rw [hJmap]
    exact Subgroup.mem_map_of_mem _ hx
  obtain ⟨j, hjJ, hjx⟩ := hx₁
  have hjK : j ∈ Y ⊓ Subgroup.centralizer {d₀} :=
    Subgroup.commutator_le_self _ (Subgroup.commutator_le_self _ (hJle hjJ))
  exact ⟨j, hjK.1, Subgroup.mem_centralizer_singleton_iff.1 hjK.2,
    hJ'CH (Subgroup.mem_map_of_mem _ hjJ), hjx⟩

theorem residualConj_eq_one_or_conj_of_mem_Lbar (S : Setting z E F) {a : G} {w : ℕ}
    (h : Sec3Hyp S a w) {d₀ : ↥(Xsub S a)} (hd₀R : (d₀ : Hbar z) ∈ Rbar S a)
    (hd₀1 : (d₀ : Hbar z) ≠ 1)
    (hA : ∀ j ∈ ⁅⁅threeResidualJoin d₀, threeResidualJoin d₀⁆,
        ⁅threeResidualJoin d₀, threeResidualJoin d₀⁆⁆, rhoZ S (j : Hbar z) = 1)
    {m : ℕ} (hm : 5 ≤ m) (φ : ↥(threeResidualQuot d₀) ≃* U2 m)
    (hφ : φ '' threeResidualClass d₀ = DU m)
    (c : ↥(Subgroup.centralizer {(d₀ : Hbar z)})) (hc : (c : Hbar z) ∈ Lbar S a) :
    residualConj d₀ c = 1 ∨
      residualConj d₀ c = MulAut.conj (⟨QuotientGroup.mk d₀,
        mk_mem_threeResidualQuot_self d₀⟩ : ↥(threeResidualQuot d₀)) := by
  classical
  set dY : ↥(threeResidualQuot d₀) :=
    ⟨QuotientGroup.mk d₀, mk_mem_threeResidualQuot_self d₀⟩ with hdY
  have hdU : φ dY ∈ DU m := by
    rw [← hφ]
    exact Set.mem_image_of_mem φ (mk_self_mem_threeResidualClass d₀)
  obtain ⟨W', hW', hodd, hrig⟩ := exists_rigid_core_of_mulEquiv_U2 φ hm hdU
  have hlift := exists_lift_mem_CH S h hd₀R hd₀1 hA hW' hodd
  set A : Subgroup (MulAut ↥(threeResidualQuot d₀)) :=
    ((Lbar S a).subgroupOf (Subgroup.centralizer {(d₀ : Hbar z)})).map (residualConj d₀)
    with hAdef
  have hLcomm : ∀ c₁ c₂ : ↥(Subgroup.centralizer {(d₀ : Hbar z)}),
      (c₁ : Hbar z) ∈ Lbar S a → (c₂ : Hbar z) ∈ Lbar S a → c₁ * c₂ = c₂ * c₁ :=
    fun c₁ c₂ h₁ h₂ => Subtype.ext (commute_of_mem_Lbar S h.mem_Q h.isConj h₁ h₂)
  refine hrig A ?_ ?_ ?_ ?_ ?_ _ (Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 hc))
  · rintro _ ⟨c₁, hc₁, rfl⟩ _ ⟨c₂, hc₂, rfl⟩
    rw [← map_mul, ← map_mul,
      hLcomm c₁ c₂ (Subgroup.mem_subgroupOf.1 hc₁) (Subgroup.mem_subgroupOf.1 hc₂)]
  · rintro _ ⟨c₁, hc₁, rfl⟩
    have h1 : c₁ * c₁ = 1 := by
      apply Subtype.ext
      have := sq_eq_one_of_mem_Lbar S h.mem_Q h.isConj (Subgroup.mem_subgroupOf.1 hc₁)
      rw [Subgroup.coe_mul, OneMemClass.coe_one]
      rwa [pow_two] at this
    rw [← map_mul, h1, map_one]
  · rintro _ ⟨c₁, -, rfl⟩
    exact residualConj_fix_self c₁
  · have hd₀C : (d₀ : Hbar z) ∈ Subgroup.centralizer {(d₀ : Hbar z)} :=
      Subgroup.mem_centralizer_singleton_iff.2 rfl
    refine ⟨⟨d₀, hd₀C⟩, Subgroup.mem_subgroupOf.2 (Rbar_le_Lbar S a hd₀R), ?_⟩
    exact residualConj_eq_conj (d := d₀) ⟨(d₀ : Hbar z), hd₀C⟩ d₀.2
      (show d₀ ∈ threeResidualJoin d₀ from Subgroup.mem_sup_right (Subgroup.mem_zpowers d₀))
  · intro x hx
    obtain ⟨j, hjY, hjd, hjCH, hjx⟩ := hlift x hx
    have hjC : (j : Hbar z) ∈ Subgroup.centralizer {(d₀ : Hbar z)} :=
      Subgroup.mem_centralizer_singleton_iff.2 (congrArg Subtype.val hjd)
    have e1 : MulAut.conj x = residualConj d₀ ⟨j, hjC⟩ := by
      have e2 := residualConj_eq_conj (d := d₀) ⟨(j : Hbar z), hjC⟩ j.2 hjY
      rw [e2]
      congr 1
      exact Subtype.ext hjx.symm
    have hN := CH_le_normalizer_Lbar S a hjCH
    rintro _ ⟨c₁, hc₁, rfl⟩
    rw [e1, ← map_inv, ← map_mul, ← map_mul]
    refine Subgroup.mem_map_of_mem _ (Subgroup.mem_subgroupOf.2 ?_)
    exact (Subgroup.mem_normalizer_iff.1 hN _).1 (Subgroup.mem_subgroupOf.1 hc₁)

end Sec4PSU

end CFSG.RankThree.GF2n.Stroth78

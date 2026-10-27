module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofTools
import CFSG.RankThree.Classical2.TwoLocalRankCoprimeQuotient
import CFSG.RankThree.PartOne.S10.PlaneAuxiliary

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.RankThreeEven (localRank projSp)

namespace Item812Res3

variable {G : Type} [Group G] [Finite G]

theorem normalizer_zpowers_le_normalizer_of_isYModel (h3 : localRank 3 G ≤ 3) {a : G}
    (ha3 : a ^ 3 = 1) (ha1 : a ≠ 1) {Y : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a)
    {M : Type} [Group M] (hM : IsYModel M) (e : Y ⧸ aschbacherSolvableCore 3 Y ≃* M) :
    Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
  classical
  obtain ⟨hZ, s₁, s₂, V, hs₁, hs₁', hs₂, hs₂', hs, hV3, hV2, hV₁, hV₂⟩ := hM
  have hp : Nat.Prime 3 := Nat.prime_three
  intro g hg
  set H := Subgroup.centralizer ({a} : Set G) with hH
  obtain ⟨Y₀, hY₀, rfl⟩ := hY
  have hgH : g ∈ Subgroup.normalizer (H : Set G) :=
    Item812Res2.mem_normalizer_centralizer_of_mem_normalizer_zpowers hg
  set σ : MulAut H := H.normalizerMonoidHom ⟨g, hgH⟩ with hσ
  set Y₀' := Y₀.map σ.toMonoidHom with hY₀'
  have hY₀'mem : Y₀' ∈ thetaComponents 3 H := map_mulEquiv_mem_thetaComponents hp σ hY₀
  have hconj : (Y₀.map H.subtype).map (MulAut.conj g).toMonoidHom = Y₀'.map H.subtype := by
    rw [hY₀', Subgroup.map_map, Subgroup.map_map]
    congr 1
  rw [Subgroup.mem_normalizer_iff_map_conj_eq]
  change (Y₀.map H.subtype).map (MulAut.conj g).toMonoidHom = Y₀.map H.subtype
  rw [hconj]
  by_contra hne
  have hne₀ : Y₀' ≠ Y₀ := fun h => hne (by rw [h])
  set N := aschbacherSolvableCore 3 H with hN
  obtain ⟨-, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := H) hp
  set π := QuotientGroup.mk' N with hπ
  have hK := isComponent_map_of_mem_thetaComponents hp hY₀
  have hK' := isComponent_map_of_mem_thetaComponents hp hY₀'mem
  have hKne : Y₀.map π ≠ Y₀'.map π := fun h =>
    hne₀ ((theta_component_quotient_correspondence (H := H) hp).1.injOn hY₀'mem hY₀ h.symm)
  have hcomm := (CFSG.LocalCores.distinct_components_commute hK hK').resolve_left hKne
  have hKK' : ∀ x ∈ Y₀.map π, ∀ y ∈ Y₀'.map π, x * y = y * x := by
    intro x hx y hy
    have hxc := Subgroup.commutator_eq_bot_iff_le_centralizer.mp hcomm hx
    exact (Subgroup.mem_centralizer_iff.mp hxc y hy).symm
  obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map hp hY₀.2.1
  obtain ⟨η', -⟩ := exists_thetaQuotient_mulEquiv_map hp hY₀'mem.2.1
  set ι := Y₀.equivMapOfInjective H.subtype H.subtype_injective with hι
  set ι' := Y₀.equivMapOfInjective σ.toMonoidHom σ.injective with hι'
  set ψ : M ≃* Y₀.map π := e.symm.trans ((Item812Res2.thetaQuotEquiv ι).symm.trans η) with hψ
  set ψ' : M ≃* Y₀'.map π :=
    e.symm.trans ((Item812Res2.thetaQuotEquiv ι).symm.trans
      ((Item812Res2.thetaQuotEquiv ι').trans η')) with hψ'
  have haH : a ∈ H := Subgroup.mem_centralizer_singleton_iff.mpr rfl
  set z := π ⟨a, haH⟩ with hz
  have hzc : ∀ y, z * y = y * z := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H y =>
      rw [hz, hπ, QuotientGroup.mk'_apply, ← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul]
      congr 1
      apply Subtype.ext
      exact (Subgroup.mem_centralizer_singleton_iff.mp y.2).symm
  have ha3' : (⟨a, haH⟩ : H) ^ 3 = 1 := Subtype.ext (by simpa using ha3)
  have hz3 : z ^ 3 = 1 := by rw [hz, ← map_pow, ha3', map_one]
  have hz1 : z ≠ 1 := by
    intro h1
    have hmem : (⟨a, haH⟩ : H) ∈ N := by
      rwa [hz, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    have hord : orderOf (⟨a, haH⟩ : H) = 3 :=
      orderOf_eq_prime ha3' (fun h => ha1 (by simpa using congrArg Subtype.val h))
    have hdvd := Subgroup.orderOf_dvd_natCard N hmem
    rw [hord] at hdvd
    exact hN3 hdvd
  set w : H ⧸ N := (ψ' s₁ : H ⧸ N) with hw
  have hwK' : w ∈ Y₀'.map π := (ψ' s₁).2
  have hw3 : w ^ 3 = 1 := by
    rw [hw, ← Subgroup.coe_pow, ← map_pow, hs₁, map_one, OneMemClass.coe_one]
  have hw1 : w ≠ 1 := by
    rw [hw, Ne, OneMemClass.coe_eq_one, map_eq_one_iff _ ψ'.injective]
    exact hs₁'
  have hwz : w ∉ Subgroup.zpowers z := by
    rintro ⟨k, hk⟩
    apply hw1
    refine Item812Res2.eq_one_of_forall_mul_comm hZ ψ' hwK' fun y _ => ?_
    rw [← hk]
    exact (Commute.zpow_left (hzc y) k).eq
  have hzw : z * w = w * z := hzc w
  have hF9 : Nat.card (Subgroup.zpowers z ⊔ Subgroup.zpowers w : Subgroup (H ⧸ N)) = 9 := by
    rw [card_sup_zpowers_eq_sq Nat.prime_three hz3 hz1 hw3 hwz hzw]
    norm_num
  have hFab := isElemAbelian_sup_zpowers hz3 hw3 hzw
  have hFK : ∀ f ∈ (Subgroup.zpowers z ⊔ Subgroup.zpowers w : Subgroup (H ⧸ N)),
      ∀ k ∈ Y₀.map π, f * k = k * f := by
    have hle : (Subgroup.zpowers z ⊔ Subgroup.zpowers w : Subgroup (H ⧸ N)) ≤
        Subgroup.centralizer (Y₀.map π : Set (H ⧸ N)) := by
      refine sup_le ((Subgroup.zpowers_le).mpr ?_) ((Subgroup.zpowers_le).mpr ?_)
      · rw [Subgroup.mem_centralizer_iff]
        intro k _
        exact (hzc k).symm
      · rw [Subgroup.mem_centralizer_iff]
        intro k hk
        exact hKK' k hk w hwK'
    intro f hf k hk
    exact (Subgroup.mem_centralizer_iff.mp (hle hf) k hk).symm
  have h4 := four_le_localRank_of_centralizes hZ ψ hs₁ hs₁' hs₂ hs₂' hs hV3 hV2 hV₁ hV₂ hFab hF9
    hFK
  have h5 := CFSG.RankThree.Classical2.localRank_quotient_le hp (by norm_num) N hN3
  have h6 := CFSG.RankThree.PartOne.PlaneAux.localRank_le_of_injective hp H.subtype
    H.subtype_injective
  omega

end Item812Res3

section Final


open Item812Res3 in
theorem Sec8Final.normalizer_zpowers_le_normalizer_Y {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {c : G} {L : Subgroup G} {a b : G} {X Y : Subgroup G} {n : ℕ}
    (h : Sec8Final G A c L a b X Y n) :
    Subgroup.normalizer (Subgroup.zpowers a : Set G) ≤ Subgroup.normalizer (Y : Set G) := by
  have h3 := h.toTheoremFourHyp.localRank_three.le
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  rcases h.item89_Y with h9 | h6
  · obtain ⟨e⟩ := h9
    exact normalizer_zpowers_le_normalizer_of_isYModel h3 ha3 h.a_ne_one
      h.mem_thetaComponentsAt_Y isYModel_alternatingGroup_nine e
  · obtain ⟨e⟩ := h6
    exact normalizer_zpowers_le_normalizer_of_isYModel h3 ha3 h.a_ne_one
      h.mem_thetaComponentsAt_Y isYModel_projSp_three_two e

end Final

end CFSG.RankThree.PartTwo.Sec8

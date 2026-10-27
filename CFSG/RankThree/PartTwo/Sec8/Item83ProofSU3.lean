module

public import CFSG.RankThree.PartTwo.Sec8.Item83ProofDefs
public import CFSG.RankThree.PartTwo.Sec8.Item83ProofLift
public import CFSG.RankThree.PartTwo.Sec8.Item82OneProofMax
public import CFSG.RankThree.PartTwo.Sec8.Standing
public import CFSG.RankThree.PartTwo.KFacts.K71SU3TwoFree
public import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
public import CFSG.RankThree.GroupTheory.SteinbergBYSectionNineResidual

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item83Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 CFSG.RankThree.PartTwo.KFacts
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank (StatedSU)
open CFSG.RankThree.GroupTheory

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem mem_center_of_conj_eq_one {M : Type*} [Group M] {y : M} (hy : MulAut.conj y = 1) :
    y ∈ Subgroup.center M := by
  rw [Subgroup.mem_center_iff]
  intro z
  have h1 := congrArg (fun φ : MulAut M => φ z) hy
  simp only [MulAut.conj_apply, MulAut.one_apply] at h1
  calc z * y = y * z * y⁻¹ * y := by rw [h1]
    _ = y * z := by group

theorem invTwoBarNontrivial_of_invariant {E U : Subgroup G}
    (hθ : Odd (Nat.card (aschbacherSolvableCore 3 L)))
    (hU : U ∈ invariantPiSubgroups L E (piOf 2)) (hU1 : U ≠ ⊥) : InvTwoBarNontrivial E L := by
  obtain ⟨hUL, hU2, hEU⟩ := hU
  have hU2' : IsPGroup 2 U := (isPiSubgroup_piOf_iff Nat.prime_two U).mp hU2
  set X := imageModTheta L U with hX
  refine ⟨X, ?_, ?_, ?_⟩
  ·
    intro hXbot
    apply hU1
    rw [eq_bot_iff]
    intro u hu
    have huL : u ∈ L := hUL hu
    have hmk : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨u, huL⟩ = 1 := by
      have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 L) ⟨u, huL⟩ ∈ X :=
        ⟨⟨u, huL⟩, hu, rfl⟩
      rw [hXbot, Subgroup.mem_bot] at h1
      exact h1
    have hθu : (⟨u, huL⟩ : L) ∈ aschbacherSolvableCore 3 L := by
      rw [← QuotientGroup.ker_mk' (aschbacherSolvableCore 3 L), MonoidHom.mem_ker]
      exact hmk
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.mp hU2') ⟨u, hu⟩
    have h1 : orderOf (⟨⟨u, huL⟩, hθu⟩ : aschbacherSolvableCore 3 L) = 2 ^ k := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk, ← Subgroup.orderOf_mk u hu, hk]
    have h2 := orderOf_dvd_natCard (⟨⟨u, huL⟩, hθu⟩ : aschbacherSolvableCore 3 L)
    rw [h1] at h2
    have hk0 : k = 0 := by
      by_contra hk0
      have h3 : 2 ∣ Nat.card (aschbacherSolvableCore 3 L) :=
        (dvd_pow_self 2 hk0).trans h2
      exact (Nat.not_even_iff_odd.mpr hθ) (even_iff_two_dvd.mpr h3)
    rw [hk0, pow_zero, orderOf_eq_one_iff] at h1
    rw [Subgroup.mem_bot]
    have := congrArg (fun w : aschbacherSolvableCore 3 L => ((w : L) : G)) h1
    simpa using this
  · exact (hU2'.of_equiv (Subgroup.subgroupOfEquivOfLe hUL).symm).map _
  · intro τ hτ x hx
    obtain ⟨g, hgN, hgE, rfl⟩ := mem_autThetaQuot_iff.mp hτ
    obtain ⟨u, hu, rfl⟩ := hx
    refine ⟨L.normalizerMonoidHom ⟨g, hgN⟩ u, ?_, rfl⟩
    have hu' : (u : G) ∈ U := hu
    change g * (u : G) * g⁻¹ ∈ U
    exact (Subgroup.mem_normalizer_iff.mp (hEU hgE) u).mp hu'


theorem exists_data83_of_su3 (h45 : Item4_5) (hKF : KF83SUThree) {A : Subgroup G} {c a : G}
    (h : Hyp81 G A c L a) (hA : 27 < Nat.card A) (hA81 : Nat.card A = 81) {n : ℕ} (hn : Odd n)
    (hL : IsSLThreePiAt (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n))) :
    ∃ (A₀ : Subgroup G) (d : G), Data83 G c L a A₀ d n := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hn1 : 1 ≤ n := hn.pos
  have h3n : Odd (3 * n) := Odd.mul (by decide) hn
  have hmod : 2 ^ (3 * n) % 3 = 2 := by
    have := three_dvd_two_pow_three_mul_add_one hn
    omega
  obtain ⟨K, _, _, ⟨-, h1, -⟩ | ⟨hK, -, ⟨e⟩⟩⟩ := id hL
  · omega
  have hLSU : IsoSUThree (L ⧸ aschbacherSolvableCore 3 L) (2 ^ (3 * n)) :=
    ⟨K, inferInstance, inferInstance, hK, ⟨e⟩⟩
  have hU : UnitaryFieldData 2 (3 * n) K :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have hq8 : 2 < 2 ^ (3 * n) := by
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ x ∈ A, ∀ y ∈ A, x * y = y * x := fun x hx y hy =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩)
  have hAN : A ≤ Subgroup.normalizer (L : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 h.toTheoremFourHyp hAe h.mem_A h.ne_one L
      h.mem_thetaComponentsAt
  have hθ : Odd (Nat.card (aschbacherSolvableCore 3 L)) := by
    have h1 := odd_card_of_le_normalizer h.toTheoremFourHyp.localRank_three.le hAe hA81
      (X := inSubgroup (aschbacherSolvableCore 3) L) ?_ (hAN.trans
        (SteinbergBY.normalizer_le_normalizer_inSubgroup_aschbacherSolvableCore 3 L))
    · rwa [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective] at h1
    · rw [inSubgroup, Subgroup.card_map_of_injective L.subtype_injective]
      exact not_three_dvd_card_aschbacherSolvableCore L
  obtain ⟨E, hE, hEA, U, hUmem, hU1⟩ := h.exists_invariant_two hA
  have hEe : CFSG.Assembly.IsElemAbelian 3 E := hE.1
  have hEN : E ≤ Subgroup.normalizer (L : Set G) := hEA.trans hAN
  have hInv := invTwoBarNontrivial_of_invariant hθ hUmem hU1
  have hAC : A ⊓ thetaQuotCentralizer L = Subgroup.zpowers c := by
    have hset := Sec13.sectionCentralizer_eq_inf hAN
    rw [h.sectionCentralizer_eq] at hset
    exact SetLike.coe_injective hset.symm
  have hc3 : Nat.card (Subgroup.zpowers c) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hAe.2 c h.mem_A) h.ne_one
  have hEC : Nat.card (E ⊓ thetaQuotCentralizer L : Subgroup G) ≤ 3 := by
    rw [← hc3, ← hAC]
    exact Subgroup.card_le_of_le (inf_le_inf_right _ hEA)
  have hF9 : 9 ≤ Nat.card (autThetaQuot E L) := by
    have hmul := Sec13.card_inf_mul_card_autThetaQuot hEN
    rw [hE.2.1] at hmul
    by_contra hlt
    rw [not_le] at hlt
    have : Nat.card (E ⊓ thetaQuotCentralizer L : Subgroup G) * Nat.card (autThetaQuot E L) ≤
        3 * 8 := Nat.mul_le_mul hEC (by omega)
    omega
  have hqs := Sec6.isQuasisimple_of_mem_thetaComponentsAt h.mem_thetaComponentsAt
  have hcyc : OutThreeCyclic (L ⧸ aschbacherSolvableCore 3 L) :=
    outThreeCyclic_of_isSLThreePiAt hqs (by omega) hL
  have hFI : 3 ≤ Nat.card (autThetaQuot E L ⊓
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* _).range : Subgroup _) := by
    by_cases hall : ∀ β ∈ autThetaQuot E L, IsInnerAut β
    · have h1 : autThetaQuot E L ⊓ (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* _).range =
          autThetaQuot E L := inf_eq_left.mpr hall
      rw [h1]
      omega
    · obtain ⟨α, hαF, hαout⟩ : ∃ α ∈ autThetaQuot E L, ¬ IsInnerAut α := by
        by_contra hno
        exact hall fun β hβ => by
          by_contra hβin
          exact hno ⟨β, hβ, hβin⟩
      have h1 := card_le_three_mul_card_inf_of_forall_pow_mul_mem hαF fun β hβ =>
        hcyc α β (Item82OneProof.commute_of_mem_autThetaQuot hEe hαF hβ)
          (Item82OneProof.pow_three_of_mem_autThetaQuot hEe hαF)
          (Item82OneProof.pow_three_of_mem_autThetaQuot hEe hβ) hαout
      omega
  obtain ⟨⟨β, hβF, hβI⟩, hβ1⟩ : ∃ β : (autThetaQuot E L ⊓
      (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* _).range : Subgroup _), β ≠ 1 := by
    have : Nontrivial (autThetaQuot E L ⊓
        (MulAut.conj : L ⧸ aschbacherSolvableCore 3 L →* _).range : Subgroup _) :=
      Finite.one_lt_card_iff_nontrivial.mp (by omega)
    exact exists_ne 1
  have hβ1' : β ≠ 1 := fun h1 => hβ1 (Subtype.ext h1)
  obtain ⟨d, hdN, hdE, hdβ⟩ := mem_autThetaQuot_iff.mp hβF
  obtain ⟨x, hxβ⟩ := hβI
  have hdA : d ∈ A := hEA hdE
  have hd3 : d ^ 3 = 1 := hEe.2 d hdE
  have hdg : inducedAutHom L e ⟨d, hdN⟩ = MulAut.conj (e x) := by
    rw [inducedAutHom_apply, ← congr_mulAutConj, hxβ, ← hdβ]
    rfl
  have hg3c : e x ^ 3 ∈ Subgroup.center (StatedSU 3 (2 ^ (3 * n)) K) := by
    apply mem_center_of_conj_eq_one
    rw [map_pow, ← hdg]
    exact inducedAutHom_pow_eq_one L e hdN hd3
  have hgc : e x ∉ Subgroup.center (StatedSU 3 (2 ^ (3 * n)) K) := by
    intro hgc
    apply hβ1'
    rw [← hxβ]
    have h1 : MulAut.conj (e x) = 1 := by
      ext z
      rw [MulAut.conj_apply, MulAut.one_apply, (Subgroup.mem_center_iff.mp hgc z).symm,
        mul_inv_cancel_right]
    have h2 : MulAut.congr e (MulAut.conj x) = MulAut.congr e 1 := by
      rw [congr_mulAutConj, h1, map_one]
    exact (MulAut.congr e).injective h2
  have hgs : ∀ c : K, ((e x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ≠ c • 1 := by
    intro c' hc'
    apply hgc
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    apply Units.ext
    change ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((e x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((e x : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((z : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [hc', Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, Matrix.one_mul]
  have hg3 : e x ^ 3 ≠ 1 := by
    intro hg3
    have hPi : PiField false 2 (3 * n) K := ⟨Nat.prime_two, by omega, hK⟩
    exact not_invTwoBarNontrivial_of_inducedAutHom_eq_conj hPi hmod e hdE hdN (e x) hg3 hgs hdg
      hInv
  obtain ⟨ι⟩ := hKF K n hn hK (e x) hg3c hg3
  have hKbar := nonempty_imageModTheta_mulEquiv_of_conj e hdN ⟨1, by rw [pow_one]; exact hd3⟩
    hdg
  obtain ⟨κ⟩ := hKbar
  have := nontrivial_projSL_two (m := 3 * n) (by omega)
  have hKne : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer {d}) ≠ ⊥ :=
    ne_bot_of_imageModTheta_mulEquiv (κ.trans ι)
  have hd1 : d ≠ 1 := by
    rintro rfl
    apply hβ1'
    rw [← hdβ]
    have h1 : (⟨1, hdN⟩ : Subgroup.normalizer (L : Set G)) = 1 := rfl
    rw [h1, map_one, map_one]
  have hnot : ¬ InducesOuterTheta d L := by
    rintro ⟨hdN', hout⟩
    exact hout ⟨x, by rw [hxβ, ← hdβ]; rfl⟩
  have ha3 : a ^ 3 = 1 := hAe.2 a h.a_mem
  have hfield : InducesStdKind L a .field := by
    rcases h.inducesStdKind with hf | hgf
    · exact hf
    · exact absurd hgf (not_inducesStdKind_graphField_of_isoSUThree (by omega)
        (three_dvd_two_pow_three_mul_add_one hn) hLSU)
  have hCa := isoSUThree_barCentralizer_of_inducesStdKind hn hLSU ha3 hfield
  refine ⟨A, d, ⟨fun y hy => Subgroup.centralizer_le_normalizer _
    (Subgroup.mem_centralizer_iff.mpr fun z hz =>
      hcomm z ((Subgroup.zpowers_le.mpr h.mem_A) hz) y hy), h.mem_A, h.a_mem, hAe, hA81,
    h.sectionCentralizer_eq, hdA, hd1, Or.inl (InducesStdKind.su3 hU hq8
      ((inducesKindSU3_inner_iff L hU hq8 e d).mpr ⟨hdN, hnot⟩)), hn, hKne,
    Or.inr (Or.inr (Or.inl ⟨hLSU, hCa, ⟨κ.trans ι⟩⟩))⟩⟩

end CFSG.RankThree.PartTwo.Sec8.Item83Proof

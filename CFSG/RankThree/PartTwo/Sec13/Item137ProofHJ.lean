module

import CFSG.RankThree.PartTwo.Sec13.Item137Delta
import CFSG.RankThree.PartTwo.Sec13.Item136Moreover
import CFSG.RankThree.PartTwo.Sec13.Item136Pair
import CFSG.RankThree.PartTwo.Sec17.Item1730Chosen
public import CFSG.RankThree.PartTwo.Sec13.Item13Inputs
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

theorem false_of_lBarA_j2 (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) (hspor : SporadicModels131) {A L E K : Subgroup G} {c e u : G}
    (h : Sec13Data G A c L)
    (hM : Nonempty (L ⧸ aschbacherSolvableCore 3 L ≃* CFSG.Blueprint.NativeSporadic.M12))
    (hXF : E ∈ partTwoF G) (hXT : E ∉ partTwoT G)
    (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e) (hec : e ∉ Subgroup.zpowers c)
    (huE : u ∈ Subgroup.normalizer (E : Set G))
    (hτ : ∀ v ∈ E, u * v * u⁻¹ ∈ Subgroup.zpowers v → v ∈ Subgroup.zpowers c)
    (hφ : Nonempty (lBarA e K E ≃*
      Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.J2)) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨φ⟩ := hφ
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF
      not_mem_partTwoT := hXT
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have hFE := (h.toTheoremFourHyp.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hspor' := hspor
  obtain ⟨-, ⟨-, hM12z⟩, ⟨hJ2p, -⟩⟩ := hspor'
  obtain ⟨φK⟩ := nonempty_thetaQuot_equiv hD hJ2p φ
  have hKJ : Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.J2) :=
    ⟨φK⟩
  have h9 := card_inf_eq_nine hD hJ2p φ
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥K)
      Nat.prime_three
  obtain ⟨d, hdB, hd1, hdc⟩ := Sec17.exists_threeCentral_of_card_nine h415 hθ3 hKJ
    (inf_le_right : E ⊓ K ≤ K) (fun x hx => hD.isElemAbelian.2 x hx.1) h9
  have hdE : d ∈ E := hdB.1
  have hdc' := hdc
  obtain ⟨hdK, S, hdS, hSd⟩ := hdc'
  have hS := Sec14.center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hKJ hdK hd1 S hdS hSd
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({d} : Set G)) :=
    h.toTheoremFourHyp.sectionFourHyp
      (Sec14.centralizer_singleton_ne_top h.isSimpleGroup h.nonabelian hd1)
  have hJq := Sec14.residual_inf_centralizer_quasisimple_of_quot h415 hθ3 hθs hKJ hdK hd1
    ⟨S, hdS, hSd⟩
  have hEE : Late.IsE27 E := Late.isE27_of_mem_partTwoE (hFE ▸ hXF)
  obtain ⟨K', hK', hJK'⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4 hEE
    hD.mem_A hdE hD.ne_one hK.1 hJq
  have hc3 : c ^ 3 = 1 := h.isElemAbelian.2 c h.mem_A
  have hcd : ∀ {Y : Type} [Group Y], Sec4.IsTripleCover (K' ⧸ aschbacherSolvableCore 3 K') Y →
      u ∈ Subgroup.normalizer (Subgroup.zpowers d : Set G) → False := by
    intro Y _ hY hud
    have hdc : d ∈ Subgroup.zpowers c :=
      hτ d hdE ((Subgroup.mem_normalizer_iff.mp hud d).mp (Subgroup.mem_zpowers d))
    have hzd : Subgroup.zpowers d = Subgroup.zpowers c := by
      refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hdc) ?_
      have hd3 : d ^ 3 = 1 := hD.isElemAbelian.2 d hdE
      have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
      rw [Nat.card_zpowers, Nat.card_zpowers, orderOf_eq_prime hd3 hd1]
      exact Nat.le_of_dvd (by norm_num) (orderOf_dvd_of_pow_eq_one hc3)
    have hTC : thetaComponentsAt 3 d = thetaComponentsAt 3 c := by
      unfold thetaComponentsAt
      rw [centralizer_singleton_eq_of_zpowers_eq hzd]
    have hK'c : K' ∈ thetaComponentsAt 3 c := hTC ▸ hK'
    have h3K' : 3 ∣ Nat.card K' := by
      have h1 : 3 ∣ Nat.card (K' ⧸ aschbacherSolvableCore 3 K') := by
        have := Subgroup.card_subgroup_dvd_card
          (Subgroup.center (K' ⧸ aschbacherSolvableCore 3 K'))
        rwa [hY.1] at this
      exact h1.trans (Subgroup.card_quotient_dvd_card _)
    obtain ⟨hcL, h9L, -⟩ := facts_of_m12 h131 hspor h hM
    obtain ⟨φL⟩ := hM
    have hZL : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥ :=
      center_eq_bot_of_mulEquiv φL hM12z
    have hAcL : A ≤ Subgroup.zpowers c ⊔ L := by
      have hBL : A ⊓ L ≤ L := inf_le_right
      have hle : Subgroup.zpowers c ⊔ (A ⊓ L) ≤ A :=
        sup_le (Subgroup.zpowers_le.mpr h.mem_A) inf_le_left
      have hcard := (isElemAbelian_zpowers_sup_of_card_nine hc3
        (fun hcB : c ∈ A ⊓ L => hcL hcB.2) le_rfl h9L
        (fun b hb => h.isElemAbelian.2 b hb.1) (fun b hb => h.commute h.mem_A hb.1)).2
      have hAB : A = Subgroup.zpowers c ⊔ (A ⊓ L) :=
        (Subgroup.eq_of_le_of_card_ge hle (by rw [h.card_eq, hcard])).symm
      rw [hAB]
      exact sup_le_sup_left hBL _
    have hKL := eq_of_mem_thetaComponentsAt_of_maximal h.orderOf_eq h.mem_thetaComponentsAt hZL
      hAcL h.isElemAbelian (fun F' hF' hAF' => (h.eq_of_le hF' hAF') ▸ le_rfl) hK'c h3K'
    subst hKL
    have := hY.1
    rw [hZL, Subgroup.card_bot] at this
    omega
  rcases h134 G E e K hD hKJ d hdE hd1 ⟨_, hS⟩ K' hK' hJK' with
    ⟨-, -, hΩ⟩ | ⟨-, hA6, hEd, -⟩ | ⟨hON, hEd, -⟩
  ·
    have hmem : (Subgroup.zpowers e).map (MulAut.conj u).toMonoidHom ∈ omegaA E :=
      (map_conj_mem_omegaA_iff huE).mpr heΩ
    rw [hΩ, Set.mem_singleton_iff, MonoidHom.map_zpowers] at hmem
    have hue : u * e * u⁻¹ ∈ Subgroup.zpowers e := by
      rw [← hmem]
      exact Subgroup.mem_zpowers _
    exact hec (hτ e hD.mem_A hue)
  · exact hcd hA6 (hEd huE)
  · exact hcd hON (hEd huE)

end CFSG.RankThree.PartTwo.Sec13

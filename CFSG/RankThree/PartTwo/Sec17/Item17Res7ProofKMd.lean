module

import CFSG.RankThree.PartTwo.Sec14.Item1417
import CFSG.RankThree.PartTwo.Sec6.Item68
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec13.Item13Basic
public import CFSG.RankThree.PartTwo.Sec14.Item145Bot
public import CFSG.RankThree.PartTwo.Sec15.Item15Statements
public import CFSG.RankThree.PartTwo.Sec17.Item17Setup

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS
open scoped commutatorElement

namespace Proof17Res7

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem three_dvd_card_of_j2 {L : Subgroup G}
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2)) :
    3 ∣ Nat.card L := by
  obtain ⟨φ⟩ := hJ
  have h1 := Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 ↥L)
  rw [Nat.card_congr φ.toEquiv, KFacts.KS14.card_nativeJ2] at h1
  exact (show 3 ∣ 604800 by norm_num).trans h1

theorem isEmpty_j2_of_trans {A L : Subgroup G} {c : G} (hD : Sec14Std G A c L)
    (hT : TransOmegaThree A c)
    (hA7 : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* alternatingGroup (Fin 7)))
    {b : G} (hb : Subgroup.zpowers b ∈ omegaA A) {Lb : Subgroup G} (hLb : Lb ∈ lA A b) :
    IsEmpty (↥Lb ⧸ aschbacherSolvableCore 3 ↥Lb ≃* CFSG.Blueprint.NativeSporadic.J2) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨x, hx, hbx⟩ := hT.2 _ hb
  rw [MonoidHom.map_zpowers] at hbx
  have hbx' : Subgroup.zpowers b = Subgroup.zpowers (x * c * x⁻¹) := hbx
  have hLb' : Lb ∈ lA A (x * c * x⁻¹) := by
    rw [← lA_eq_of_zpowers_eq hbx']
    exact hLb
  have hLc : Lb.map (MulAut.conj x⁻¹).toMonoidHom ∈ lA A c := by
    have := (map_conj_mem_lA_iff (inv_mem hx)).mpr hLb'
    rwa [show x⁻¹ * (x * c * x⁻¹) * x⁻¹⁻¹ = c by group] at this
  have h3 : 3 ∣ Nat.card (Lb.map (MulAut.conj x⁻¹).toMonoidHom) := by
    rw [Subgroup.card_map_of_injective (MulAut.conj x⁻¹).injective]
    exact three_dvd_card_of_j2 ⟨φ⟩
  have heq : Lb.map (MulAut.conj x⁻¹).toMonoidHom = L :=
    (hD.chosen136.2 c hD.zpowers_mem_omegaA L hD.mem_lA).2 _ hLc.1 h3
  have ψ : ↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2 := by
    have e := thetaQuotEquiv (MulAut.conj x⁻¹) Lb
    rw [heq] at e
    exact e.symm.trans φ
  obtain ⟨χ⟩ := hA7
  exact KFacts.KS14.isEmpty_mulEquiv_j2_alternating.2.1.false (ψ.symm.trans χ)

omit [Finite G] in
theorem commutator_sup_zpowers_le {P T : Subgroup G} {z : G}
    (hPz : P ≤ Subgroup.centralizer ({z} : Set G)) (hzT : z ∈ Subgroup.normalizer (T : Set G))
    (hPT : P ≤ Subgroup.normalizer (T : Set G)) :
    ⁅P ⊔ T, Subgroup.zpowers z⁆ ≤ T := by
  rw [Subgroup.commutator_le]
  intro k hk y hy
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
  have hyT : z ^ n ∈ Subgroup.normalizer (T : Set G) := zpow_mem hzT n
  let F : Subgroup G :=
    { carrier := {g | g ∈ Subgroup.normalizer (T : Set G) ∧ ⁅g, z ^ n⁆ ∈ T}
      one_mem' := ⟨one_mem _, by simp [commutatorElement_def]⟩
      mul_mem' := by
        rintro g h ⟨hg, hgc⟩ ⟨hh, hhc⟩
        refine ⟨mul_mem hg hh, ?_⟩
        have e : ⁅g * h, z ^ n⁆ = (g * ⁅h, z ^ n⁆ * g⁻¹) * ⁅g, z ^ n⁆ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact mul_mem ((Subgroup.mem_normalizer_iff.mp hg _).mp hhc) hgc
      inv_mem' := by
        rintro g ⟨hg, hgc⟩
        refine ⟨inv_mem hg, ?_⟩
        have e : ⁅g⁻¹, z ^ n⁆ = g⁻¹ * ⁅g, z ^ n⁆⁻¹ * g⁻¹⁻¹ := by
          simp only [commutatorElement_def]
          group
        rw [e]
        exact (Subgroup.mem_normalizer_iff.mp (inv_mem hg) _).mp (inv_mem hgc) }
  have hPF : P ≤ F := fun p hp => by
    refine ⟨hPT hp, ?_⟩
    have hpz : p * z ^ n = z ^ n * p :=
      Commute.zpow_right (Subgroup.mem_centralizer_singleton_iff.mp (hPz hp)) n
    have : ⁅p, z ^ n⁆ = 1 := by
      rw [commutatorElement_def, hpz]
      group
    rw [this]
    exact one_mem _
  have hTF : T ≤ F := fun t ht => by
    refine ⟨Subgroup.le_normalizer ht, ?_⟩
    have h1 : z ^ n * t⁻¹ * (z ^ n)⁻¹ ∈ T :=
      (Subgroup.mem_normalizer_iff.mp hyT _).mp (inv_mem ht)
    have e : ⁅t, z ^ n⁆ = t * (z ^ n * t⁻¹ * (z ^ n)⁻¹) := by
      simp only [commutatorElement_def]
      group
    rw [e]
    exact mul_mem ht h1
  exact (sup_le hPF hTF hk).2

theorem eq_sup_theta_of_le (h134 : Item134) (h415 : Sec4.Item4_15) {A L Y₀ : Subgroup G} {c : G}
    (hs : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) {K : Subgroup G}
    (hK : K ∈ thetaComponentsAt 3 d)
    (hLK : inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K) :
    K = inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ⊔
      inSubgroup (aschbacherSolvableCore 3) K := by
  obtain ⟨hdL, S, hdS, hSd⟩ := hdc
  obtain ⟨-, -, hθ3, -, -⟩ :=
    CFSG.RankThree.LocalRank.solvable_prime_complement_core_characterization (H := ↥L)
      Nat.prime_three
  have hS := center_sylow_eq_zpowers_of_quot_j2 h415 hθ3 hJ hdL hd1 S hdS hSd
  have hn1 : (omegaA A).ncard = 1 := by rw [hΩ, Set.ncard_singleton]
  rcases h134 G A c L hs.toSec13Data hJ d hdA hd1 ⟨_, hS⟩ K hK hLK with
    ⟨hKeq, -, -⟩ | ⟨-, -, -, -, -, -, h2⟩ | ⟨-, -, -, h12⟩
  · exact hKeq
  · rcases h2 with ⟨-, h3⟩ | ⟨I, -, -, -, a, -, -, -, h6, -⟩
    · omega
    · omega
  · omega

theorem trivial_of_forall_le (h134 : Item134) (h415 : Sec4.Item4_15) {A L Y₀ : Subgroup G}
    {c : G} (hs : Sec17Std G A c L Y₀) (hΩ : omegaA A = {Subgroup.zpowers c})
    (hJ : Nonempty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* CFSG.Blueprint.NativeSporadic.J2))
    {d : G} (hdA : d ∈ A) (hd1 : d ≠ 1) (hdc : IsThreeCentralIn L d) {𝒳 : Set (Subgroup G)}
    (h𝒳 : 𝒳 ⊆ thetaComponentsAt 3 d) (h𝒳n : 𝒳.Nonempty)
    (hall : ∀ K ∈ 𝒳, inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) ≤ K) :
    c ∈ Subgroup.normalizer ((sSup 𝒳 : Subgroup G) : Set G) ∧
      ⁅sSup 𝒳, Subgroup.zpowers c⁆ ≤ inSubgroup (aschbacherSolvableCore 3) (sSup 𝒳) := by
  set Ld := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hLd
  obtain ⟨K₀, hK₀⟩ := h𝒳n
  have hK₀eq := eq_sup_theta_of_le h134 h415 hs hΩ hJ hdA hd1 hdc (h𝒳 hK₀) (hall K₀ hK₀)
  have hP : Group.IsPerfect Ld := Sec6.isPerfect_inSubgroup_perfectResidual _
  have hP1 : Ld ≠ ⊥ := by
    intro h
    apply Sec6.theta_ne_of_mem_thetaComponentsAt (h𝒳 hK₀)
    conv_rhs => rw [hK₀eq, ← hLd, h, bot_sup_eq]
  have huniq : ∀ K ∈ thetaComponentsAt 3 d, Ld ≤ K → K = K₀ := fun K hK hLK =>
    Sec6.eq_of_mem_thetaComponentsIn_of_le hK (h𝒳 hK₀) hP hP1 hLK (hall K₀ hK₀)
  have hX : sSup 𝒳 = K₀ :=
    le_antisymm (sSup_le fun K hK => (huniq K (h𝒳 hK) (hall K hK)).le) (le_sSup hK₀)
  rw [hX]
  have hLdL : Ld ≤ L := (Subgroup.map_subtype_le _).trans inf_le_left
  have hLdc : Ld ≤ Subgroup.centralizer ({c} : Set G) := hLdL.trans hs.toSec13Data.le_centralizer
  have hcd : c ∈ Subgroup.centralizer ({d} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr
      (hs.toSec13Data.commute hdA hs.toSec13Data.mem_A).symm
  have hK₀c : K₀.map (MulAut.conj c).toMonoidHom = K₀ := by
    refine huniq _ (Sec6.map_conj_mem_thetaComponentsAt hcd (h𝒳 hK₀)) fun l hl => ?_
    refine ⟨l, hall K₀ hK₀ hl, ?_⟩
    have hlc : c * l = l * c := (Subgroup.mem_centralizer_singleton_iff.mp (hLdc hl)).symm
    change c * l * c⁻¹ = l
    rw [hlc, mul_inv_cancel_right]
  have hcN : c ∈ Subgroup.normalizer (K₀ : Set G) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr hK₀c
  refine ⟨hcN, ?_⟩
  have hcT := Sec6.normalizer_le_normalizer_theta K₀ hcN
  have hLdT : Ld ≤ Subgroup.normalizer (inSubgroup (aschbacherSolvableCore 3) K₀ : Set G) :=
    (hall K₀ hK₀).trans (Sec6.le_normalizer_theta K₀)
  have hcomm := commutator_sup_zpowers_le hLdc hcT hLdT
  rw [← hK₀eq] at hcomm
  exact hcomm

end Proof17Res7

end CFSG.RankThree.PartTwo.Sec17

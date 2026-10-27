module

import CFSG.RankThree.PartTwo.Sec12.Item125Act
import CFSG.RankThree.PartTwo.Sec5.Tools
import CFSG.RankThree.PartTwo.Sec4.Item413A9
import CFSG.ThirdParty.QiuzhenCFSG.Theory.AutAlternating
import CFSG.GroupTheory.ElementaryAbelianTransport
import CFSG.FeitThompson.OddOrderTheorem
import CFSG.RankThree.PartTwo.Sec11.FieldCentRigidProof
public import CFSG.LocalAnalysis.RankThreeEvenClassification.InvariantSylow
public import CFSG.RankThree.PartTwo.Sec4.Vocabulary
public import CFSG.RankThree.PartTwo.Sec6.Item612Local
public import CFSG.RankThree.PartTwo.Sec8.Hering611Defs
import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering611

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

section Rank


variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L E T : Subgroup G} {d : G}
  {S K : Subgroup G}

theorem card_le_of_centralizes_quot (C : Cfg611 G A c L E T d S K)
    (hKev : 2 ∣ Nat.card (K ⧸ aschbacherSolvableCore 3 K)) {Z : Subgroup G}
    (hZe : CFSG.Assembly.IsElemAbelian 3 Z) (hZc : Z ≤ Sec4.thetaQuotCentralizer K) :
    Nat.card Z ≤ 27 := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hst := C.standing
  set θK := inSubgroup (aschbacherSolvableCore 3) K with hθK
  obtain ⟨-, hθ3⟩ := Sec6.theta_solvable_and_not_dvd K
  have hK2 : 2 ∣ Nat.card K :=
    hKev.trans (Subgroup.card_quotient_dvd_card (aschbacherSolvableCore 3 K))
  obtain ⟨x, hx2⟩ := exists_prime_orderOf_dvd_card' (G := K) 2 hK2
  set R₀ : Subgroup G := Subgroup.zpowers (x : G) with hR₀
  have hxord : orderOf (x : G) = 2 := by rw [Subgroup.orderOf_coe]; exact hx2
  have hR₀2 : IsPGroup 2 R₀ :=
    IsPGroup.of_card (n := 1) (by rw [hR₀, Nat.card_zpowers, hxord, pow_one])
  have hR₀K : R₀ ≤ K := Subgroup.zpowers_le.mpr x.2
  have hR₀θ : R₀ ≤ Subgroup.normalizer (θK : Set G) := hR₀K.trans (Sec6.le_normalizer_theta K)
  set N := R₀ ⊔ θK with hN
  have hN3 : ¬ 3 ∣ Nat.card N :=
    Sec6.not_dvd_card_sup_of_isPGroup Nat.prime_three (by norm_num) hR₀2 hR₀θ hθ3
  have hZK : Z ≤ Subgroup.normalizer (K : Set G) := fun z hz =>
    ((Sec6.mem_thetaQuotCentralizer_iff).mp (hZc hz)).1
  have hZN : Z ≤ Subgroup.normalizer (N : Set G) := by
    apply Sec6.le_normalizer_sup_of_conj
    · intro z hz y hy
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hzx : (x : G)⁻¹ * (z * (x : G) * z⁻¹) ∈ θK :=
        ((Sec6.mem_thetaQuotCentralizer_iff).mp (hZc hz)).2 x x.2
      have hxz : z * (x : G) * z⁻¹ ∈ N := by
        have : z * (x : G) * z⁻¹ = (x : G) * ((x : G)⁻¹ * (z * (x : G) * z⁻¹)) := by group
        rw [this]
        exact N.mul_mem (Subgroup.mem_sup_left (Subgroup.mem_zpowers _))
          (Subgroup.mem_sup_right hzx)
      have : z * (x : G) ^ k * z⁻¹ = (z * (x : G) * z⁻¹) ^ k := by
        rw [← MulAut.conj_apply, ← MulAut.conj_apply, map_zpow]
      rw [this]
      exact zpow_mem hxz k
    · intro z hz y hy
      exact Subgroup.mem_sup_right
        ((Subgroup.mem_normalizer_iff.mp (Sec6.normalizer_le_normalizer_theta K (hZK hz)) y).mp hy)
  obtain ⟨R, hZR⟩ :=
    CFSG.RankThreeEvenClassification.Helpers.exists_normalized_sylow_in_prime_complement_subgroup
      3 Nat.prime_three Z N (Sec5.isPGroup_of_isElemAbelian hZe) hN3 hZN 2 Nat.prime_two
  set RG := (R : Subgroup N).map N.subtype with hRG
  have hRG2 : IsPGroup 2 RG := R.isPGroup'.map N.subtype
  have hRG1 : RG ≠ ⊥ := by
    intro hbot
    have hxN : (x : G) ∈ N := Subgroup.mem_sup_left (Subgroup.mem_zpowers _)
    have h2N : 2 ∣ Nat.card N := by
      have : orderOf (⟨(x : G), hxN⟩ : N) = 2 := by rw [← Subgroup.orderOf_coe]; exact hxord
      rw [← this]
      exact orderOf_dvd_natCard _
    have hcard := Sylow.card_eq_multiplicity R
    have h2f : 0 < (Nat.card N).factorization 2 :=
      Nat.Prime.factorization_pos_of_dvd Nat.prime_two (Nat.card_pos.ne') h2N
    have hbot' : (R : Subgroup N) = ⊥ :=
      (Subgroup.map_eq_bot_iff_of_injective (R : Subgroup N) N.subtype_injective).mp hbot
    rw [hbot', Subgroup.card_bot] at hcard
    have : 2 ^ (Nat.card N).factorization 2 ≥ 2 ^ 1 :=
      Nat.pow_le_pow_right (by norm_num) h2f
    omega
  exact Sec5.card_le_of_le_normalizer hst.evenRank_eq hRG1 hRG2 hZe hZR

theorem card_le_of_aut_bound (h45 : Sec4.Item4_5) (C : Cfg611 G A c L E T d S K)
    (hKev : 2 ∣ Nat.card (K ⧸ aschbacherSolvableCore 3 K))
    (hAut : ∀ Y : Subgroup (MulAut (K ⧸ aschbacherSolvableCore 3 K)),
      CFSG.Assembly.IsElemAbelian 3 Y → Nat.card Y ≤ 27)
    {X : Subgroup G} (hXe : CFSG.Assembly.IsElemAbelian 3 X)
    (hXd : X ≤ Subgroup.centralizer ({d} : Set G)) : Nat.card X ≤ 3 ^ 6 := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hst := C.standing
  have hAe : CFSG.Assembly.IsElemAbelian 3 A := C.mem_S.1.1
  have hdA : d ∈ A := C.mem_E.2 C.d_mem.1
  have hd1 : d ≠ 1 := fun h => C.d_not_mem (h ▸ Subgroup.one_mem _)
  have hd3 : d ^ 3 = 1 := hAe.2 d hdA
  have hKd : K ∈ thetaComponentsAt 3 d := lZeroStarAt_subset A d C.mem_K
  suffices key : ∀ X : Subgroup G, CFSG.Assembly.IsElemAbelian 3 X →
      X ≤ Subgroup.centralizer ({d} : Set G) → d ∈ X → Nat.card X ≤ 3 ^ 6 by
    by_cases hdX : d ∈ X
    · exact key X hXe hXd hdX
    · have hcomm : ∀ u ∈ X, u * d = d * u := fun u hu =>
        Subgroup.mem_centralizer_singleton_iff.mp (hXd hu)
      obtain ⟨hXe', -⟩ := Sec5.isElemAbelian_sup_zpowers hXe hdX hd3 hcomm
      exact (Subgroup.card_le_of_le le_sup_left).trans (key _ hXe'
        (sup_le hXd (Subgroup.zpowers_le.mpr (Subgroup.mem_centralizer_singleton_iff.mpr rfl)))
        (Subgroup.mem_sup_right (Subgroup.mem_zpowers d)))
  intro X hXe hXd hdX
  have hXN : X ≤ Subgroup.normalizer (K : Set G) :=
    Sec6.le_normalizer_of_mem_thetaComponentsAt h45 hst.toTheoremFourHyp hXe hdX hd1 K hKd
  set ρ : X →* MulAut (K ⧸ aschbacherSolvableCore 3 K) :=
    (Sec12.thetaBarAct K).comp (Subgroup.inclusion hXN) with hρ
  have hXtop : CFSG.Assembly.IsElemAbelian 3 (⊤ : Subgroup X) := by
    have := CFSG.Open.IsElemAbelian.subgroupOf hXe X
    rwa [Subgroup.subgroupOf_self] at this
  have hYe : CFSG.Assembly.IsElemAbelian 3 ρ.range := by
    rw [MonoidHom.range_eq_map]
    exact CFSG.Open.IsElemAbelian.map hXtop ρ
  have h2 : Nat.card ρ.range ≤ 27 := hAut _ hYe
  set Z : Subgroup G := ρ.ker.map X.subtype with hZ
  have hZX : Z ≤ X := Subgroup.map_subtype_le _
  have hZe : CFSG.Assembly.IsElemAbelian 3 Z := Sec5.isElemAbelian_of_le hXe hZX
  have hZc : Z ≤ Sec4.thetaQuotCentralizer K := by
    rintro _ ⟨w, hw, rfl⟩
    exact (Sec12.mem_thetaQuotCentralizer_iff_thetaBarAct (hXN w.2)).mpr (MonoidHom.mem_ker.mp hw)
  have h1 : Nat.card Z ≤ 27 := card_le_of_centralizes_quot C hKev hZe hZc
  have hZcard : Nat.card Z = Nat.card ρ.ker := Subgroup.card_map_of_injective X.subtype_injective
  have hcard : Nat.card ρ.ker * Nat.card ρ.range = Nat.card X := Subgroup.card_ker_mul_card_range ρ
  calc Nat.card X = Nat.card ρ.ker * Nat.card ρ.range := hcard.symm
    _ ≤ 27 * 27 := Nat.mul_le_mul (by rw [← hZcard]; exact h1) h2
    _ = 3 ^ 6 := by norm_num

end Rank

theorem aut_bound_alt9 {M : Type} [Group M] (e : M ≃* alternatingGroup (Fin 9))
    (Y : Subgroup (MulAut M)) (hY : CFSG.Assembly.IsElemAbelian 3 Y) : Nat.card Y ≤ 27 := by
  have hbij := CFSG.GroupTheory.AutAlternating.aut_alternatingGroup_bijective_conj 9
    (by norm_num) (by norm_num)
  set ψe : Equiv.Perm (Fin 9) ≃* MulAut (alternatingGroup (Fin 9)) :=
    MulEquiv.ofBijective _ hbij with hψe
  set Y' : Subgroup (MulAut (alternatingGroup (Fin 9))) := Y.map (MulAut.congr e).toMonoidHom
  have hY'e : CFSG.Assembly.IsElemAbelian 3 Y' := CFSG.Open.IsElemAbelian.map hY _
  have hY'card : Nat.card Y' = Nat.card Y :=
    Subgroup.card_map_of_injective (MulAut.congr e).injective
  set W : Subgroup (Equiv.Perm (Fin 9)) := Y'.map ψe.symm.toMonoidHom with hW
  have hWe : CFSG.Assembly.IsElemAbelian 3 W := CFSG.Open.IsElemAbelian.map hY'e _
  have hWcard : Nat.card W = Nat.card Y' := Subgroup.card_map_of_injective ψe.symm.injective
  have hbound := CFSG.RankThree.PartTwo.Sec4.card_pow_three_le_of_faithful 9 W Set.univ
    (by simp) (fun a ha b hb => congrArg Subtype.val (hWe.1.is_comm.comm ⟨a, ha⟩ ⟨b, hb⟩))
    (fun a ha => hWe.2 a ha) (fun a _ x _ => Set.mem_univ _)
    (fun a _ ha => Equiv.ext fun x => ha x (Set.mem_univ x))
  have hnc : (Set.univ : Set (Fin 9)).ncard = 9 := by simp
  rw [hnc] at hbound
  by_contra hle
  have hlt : 27 < Nat.card Y := not_le.mp hle
  have h28 : 28 ≤ Nat.card W := by rw [hWcard, hY'card]; exact hlt
  have : 28 ^ 3 ≤ Nat.card W ^ 3 := Nat.pow_le_pow_left h28 3
  have h3 : (3 : ℕ) ^ 9 = 19683 := by norm_num
  omega

section Narrow


theorem kF611RankA9_of (h45 : Sec4.Item4_5) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E T : Subgroup G) (d : G)
      (S K : Subgroup G), Cfg611 G A c L E T d S K →
      Nonempty (K ⧸ aschbacherSolvableCore 3 K ≃* alternatingGroup (Fin 9)) →
      ∀ X : Subgroup G, CFSG.Assembly.IsElemAbelian 3 X →
        X ≤ Subgroup.centralizer ({d} : Set G) → Nat.card X ≤ 3 ^ 6 := by
  intro G _ _ A c L E T d S K C ⟨e⟩ X hXe hXd
  refine card_le_of_aut_bound h45 C ?_ (fun Y hY => aut_bound_alt9 e Y hY) hXe hXd
  rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
  decide

@[expose] def AutJ3CoverRank : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
    Sec4.IsTripleCover X Blueprint.NativeSporadic.J3 →
    ∀ Y : Subgroup (MulAut X), CFSG.Assembly.IsElemAbelian 3 Y → Nat.card Y ≤ 27

theorem two_dvd_card_of_isQuasisimple {Q : Type*} [Group Q] [Finite Q] (hQ : IsQuasisimple Q) :
    2 ∣ Nat.card Q := by
  by_contra h
  exact Sec11.fieldCent_not_isSolvable hQ
    (CFSG.FeitThompson.isSolvable_of_odd_natCard _ (Nat.odd_iff.mpr (by omega)))

theorem kF611RankJ3Cover_of (h45 : Sec4.Item4_5) (hAut : AutJ3CoverRank) :
    ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E T : Subgroup G) (d : G)
      (S K : Subgroup G), Cfg611 G A c L E T d S K →
      Sec4.IsTripleCover (K ⧸ aschbacherSolvableCore 3 K) Blueprint.NativeSporadic.J3 →
      ∀ X : Subgroup G, CFSG.Assembly.IsElemAbelian 3 X →
        X ≤ Subgroup.centralizer ({d} : Set G) → Nat.card X ≤ 3 ^ 6 := by
  intro G _ _ A c L E T d S K C hcov X hXe hXd
  have hKd : K ∈ thetaComponentsAt 3 d := lZeroStarAt_subset A d C.mem_K
  have hKq : IsQuasisimple (K ⧸ aschbacherSolvableCore 3 K) :=
    Sec6.isQuasisimple_of_mem_thetaComponentsAt hKd
  exact card_le_of_aut_bound h45 C (two_dvd_card_of_isQuasisimple hKq)
    (fun Y hY => hAut _ hKq.1 hcov Y hY) hXe hXd

end Narrow

end CFSG.RankThree.PartTwo.Sec8.Hering611

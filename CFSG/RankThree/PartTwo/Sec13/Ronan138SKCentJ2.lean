module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SKNoComp
public import CFSG.RankThree.PartTwo.Sec4.StatementsSporadic
import CFSG.RankThree.PartTwo.Sec13.Ronan138SKTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Prod
import CFSG.RankThree.PartTwo.Sec13.Item136Lift
import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item134Residual
import CFSG.RankThree.PartTwo.Sec13.Item134SylowBarSetup
import CFSG.RankThree.PartTwo.Sec18.Components
import CFSG.RankThree.PartTwo.Sec14.Item143StepsProofBalTools
import CFSG.RankThree.PartTwo.KFacts.K71Lift
import CFSG.RankThree.PartTwo.Sec4.Item424ProofInner
import CFSG.RankThree.PartTwo.Sec4.Census.Item44ThreeGL
import CFSG.GroupTheory.QuasisimpleCommutingProductBound

public section

namespace CFSG.RankThree.PartTwo.Sec13.Ronan138S

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

theorem isSolvable_centralizer_j2 (h415 : Sec4.Item4_15) {X : Type} [Group X] [Finite X]
    (hX : Nonempty (X ≃* CFSG.Blueprint.NativeSporadic.J2)) (P : Sylow 3 X) {A : Subgroup X}
    (hAP : A ≤ (P : Subgroup X)) (hA9 : Nat.card A = 9) {a : X} (haA : a ∈ A)
    (haZ : a ∉ (P : Subgroup X) ⊓ Subgroup.centralizer ((P : Subgroup X) : Set X)) :
    Group.IsSolvable (Subgroup.centralizer ({a} : Set X)) := by
  obtain ⟨-, -, -, h4, -⟩ := h415 X hX P _ rfl _ rfl
  have hAΔ : A ∈ {B : Subgroup X | B ≤ (P : Subgroup X) ∧ Nat.card B = 9} := ⟨hAP, hA9⟩
  obtain ⟨-, ⟨eN⟩, -⟩ := h4 A hAΔ a haA haZ
  have hN72 : Nat.card (Subgroup.normalizer (Subgroup.zpowers a : Set X)) = 72 := by
    rw [Nat.card_congr eN.toEquiv, Nat.card_prod, Nat.card_perm, nat_card_alternatingGroup]
    simp only [Nat.card_eq_fintype_card, Fintype.card_fin]
    decide
  have hdvd := Subgroup.card_dvd_of_le (centralizer_le_normalizer_zpowers a)
  rw [hN72] at hdvd
  exact Sec4.Census.isSolvable_of_card_dvd_two_pow_mul_three_pow (a := 3) (b := 2)
    (by norm_num; exact hdvd)

theorem false_of_threeCentral (h415 : Sec4.Item4_15) (h48 : Sec4.Item4_8)
    {G : Type} [Group G] [Finite G] {A L E F : Subgroup G} {c x y t : G}
    (hfr : Frame138 A L E F c x y t) {e : G} {K : Subgroup G}
    (heΩ : Subgroup.zpowers e ∈ omegaA E) (hK : K ∈ lA E e) (heF : e ∉ F)
    (φK : K ⧸ aschbacherSolvableCore 3 K ≃* CFSG.Blueprint.NativeSporadic.J2)
    {b : G} (hbE : b ∈ E) (hbK : b ∈ K) (hb1 : b ≠ 1) (hbd : b ∉ Subgroup.zpowers ⁅x, y⁆)
    {n : ℕ} (hab : e ^ n * b = c)
    (hc : ∃ S : Sylow 3 ↥K, (⟨b, hbK⟩ : ↥K) ∈ (S : Subgroup ↥K) ∧
      (S : Subgroup ↥K) ≤ Subgroup.centralizer ({(⟨b, hbK⟩ : ↥K)} : Set ↥K)) : False := by
  have hH := hfr.hH
  obtain ⟨h, -, hcE, hE3, hE27, hEN, hEC, -, -⟩ := hfr.hH
  have hXF := mem_partTwoF_of_hyp138 hfr.hH
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
  have he1 : e ≠ 1 := hD.ne_one
  have hKe : ∀ k ∈ K, k * e = e * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hk)
  set d := ⁅x, y⁆ with hd
  have hdEL : d ∈ E ⊓ L := hfr.hEL ▸ Subgroup.mem_zpowers _
  obtain ⟨hJq, -, hbJ, -⟩ := residual_facts h415 ⟨φK⟩ hbK hb1 hc
  have hKcb : K ⊓ Subgroup.centralizer ({c} : Set G) =
      K ⊓ Subgroup.centralizer ({b} : Set G) := by
    ext k
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hk, hkc⟩
      refine ⟨hk, ?_⟩
      have hb' : b = (e ^ n)⁻¹ * c := by rw [← hab]; group
      rw [hb']
      exact ((Commute.pow_right (show Commute k e from hKe k hk) n).inv_right.mul_right
        (show Commute k c from hkc)).eq
    · rintro ⟨hk, hkb⟩
      refine ⟨hk, ?_⟩
      rw [← hab]
      exact ((Commute.pow_right (show Commute k e from hKe k hk) n).mul_right
        (show Commute k b from hkb)).eq
  have hJK := residual_le_of_not_mem h48 kf138TypeTwo hfr heΩ hK heF
  have hcLF : Subgroup.zpowers c ⊔ (E ⊓ L) ≤ F := by
    refine sup_le (Subgroup.zpowers_le.mpr hfr.hcF) ?_
    rw [hfr.hEL]
    exact Subgroup.zpowers_le.mpr (Subgroup.mem_inf.mp hfr.hdZ).2
  obtain ⟨hdJ, -⟩ := kf138TypeTwo G A c L E hH hfr.hPGL e heE (fun h' => heF (hcLF h'))
  set J := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({e} : Set G)) with hJ
  have hJL : J ≤ L ⊓ Subgroup.centralizer ({e} : Set G) := Sec6.inSubgroup_perfectResidual_le _
  have hJc : J ≤ Subgroup.centralizer ({c} : Set G) := fun j hj =>
    h.le_centralizer (Subgroup.mem_inf.mp (hJL hj)).1
  have hdI : d ∈ inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({b} : Set G)) := by
    rw [← hKcb]
    exact Sec18.le_inSubgroup_perfectResidual (Sec18.commutator_inSubgroup_perfectResidual _)
      (le_inf hJK hJc) (hdJ hdEL)
  have hG4 : SectionFourHyp ↥(Subgroup.centralizer ({c} : Set G)) :=
    h.toPartTwoStanding.toTheoremFourHyp.sectionFourHyp
      (Sec6.centralizer_ne_top_of_ne_one h.toPartTwoStanding.toTheoremFourHyp hfr.hc1)
  have hE27' : Late.IsE27 E := ⟨hE3, hE27⟩
  have hJq' : IsQuasisimple (↥(inSubgroup perfectResidual
      (K ⊓ Subgroup.centralizer ({c} : Set G))) ⧸ aschbacherSolvableCore 3
        ↥(inSubgroup perfectResidual (K ⊓ Subgroup.centralizer ({c} : Set G)))) := by
    rw [hKcb]
    exact hJq
  obtain ⟨K'', hK'', hJK''⟩ := Sec14.exists_mem_thetaComponentsAt_le_residual h48 hG4 hE27'
    heE hfr.hcE he1 hK.1 hJq'
  rw [hKcb] at hJK''
  have hL := h.mem_thetaComponentsAt
  have hK''L : K'' = L := by
    by_contra hne
    have hK''C : K'' ≤ Sec4.thetaQuotCentralizer L := by
      have h1 := hK''
      have h2 := hL
      rw [thetaComponentsAt_eq_thetaComponentsIn] at h1 h2
      exact Sec14.BalTools.le_thetaQuotCentralizer_of_ne_in h1 h2 hne
    have hdC : d ∈ Sec4.thetaQuotCentralizer L := hK''C (hJK'' hdI)
    have hCEL := sectionCentralizer_eq_inf hEN
    rw [hEC] at hCEL
    have hd' : d ∈ ((E ⊓ Sec4.thetaQuotCentralizer L : Subgroup G) : Set G) :=
      Subgroup.mem_inf.mpr ⟨hfr.hdE, hdC⟩
    rw [← hCEL] at hd'
    exact hfr.hdc hd'
  subst hK''L
  apply hbd
  rw [← hfr.hEL]
  exact Subgroup.mem_inf.mpr ⟨hbE, hJK'' hbJ⟩

theorem step138CentJ2_of (hspor : SporadicModels131) (h415 : Sec4.Item4_15)
    (h48 : Sec4.Item4_8) : Step138CentJ2 := by
  intro G _ _ A c L E hH hPGL F hF e K heΩ hK heF hELK hφ hcN
  obtain ⟨x, y, t, hfr⟩ := exists_frame138_t hH hF hPGL
  have hH' := hH
  obtain ⟨h, -, hcE, hE3, hE27, hEN, hEC, -, -⟩ := hH'
  have hXF := mem_partTwoF_of_hyp138 hfr.hH
  have hD : Sec13Data G E e K :=
    { h.toPartTwoStanding with
      partTwoS_eq := h.partTwoS_eq
      mem_partTwoF := hXF.1
      not_mem_partTwoT := hXF.2
      zpowers_mem_omegaA := heΩ
      mem_lA := hK }
  have heE : e ∈ E := (zpowers_mem_omegaA_iff.mp heΩ).1
  have he3 : e ^ 3 = 1 := hE3.2 e heE
  have he1 : e ≠ 1 := hD.ne_one
  have hc3 : c ^ 3 = 1 := hE3.2 c hcE
  obtain ⟨φ⟩ := hφ
  have hspor' := hspor
  obtain ⟨-, -, ⟨hJ2p, hJ2z⟩⟩ := hspor'
  obtain ⟨φK⟩ := nonempty_thetaQuot_equiv hD hJ2p φ
  have heK : e ∉ K := not_mem_of_center_inf_commutator hD φ (by rw [hJ2z, bot_inf_eq])
  have hB9 : Nat.card (E ⊓ K : Subgroup G) = 9 := card_inf_eq_nine hD hJ2p φ
  set B := E ⊓ K with hBdef
  have heB : e ∉ B := fun h' => heK (Subgroup.mem_inf.mp h').2
  have hKe : ∀ k ∈ K, k * e = e * k := fun k hk =>
    Subgroup.mem_centralizer_singleton_iff.mp (hD.le_centralizer hk)
  have hCEset := sectionCentralizer_eq_inf hK.2.1
  rw [hK.2.2.1] at hCEset
  have hCE : E ⊓ Sec4.thetaQuotCentralizer K = Subgroup.zpowers e :=
    SetLike.coe_injective hCEset.symm
  have heC : e ∈ Sec4.thetaQuotCentralizer K :=
    (Subgroup.mem_inf.mp (hCE.symm ▸ Subgroup.mem_zpowers e : e ∈ E ⊓ _)).2
  have hcomm : ∀ a ∈ Subgroup.zpowers e, ∀ b ∈ B, a * b = b * a := by
    intro a ha b hb
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp ha
    exact (Commute.zpow_left (hfr.hEab e heE b (Subgroup.mem_inf.mp hb).1) k).eq
  obtain ⟨hcard, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcomm
  rw [zpowers_inf_eq_bot he3 heB, Subgroup.card_bot, mul_one,
    card_zpowers_of_pow_three he3 he1, hB9] at hcard
  have heq : Subgroup.zpowers e ⊔ B = E :=
    Subgroup.eq_of_le_of_card_ge (sup_le (Subgroup.zpowers_le.mpr heE) inf_le_left)
      (by rw [hE27, hcard])
  have hc' : c ∈ ((Subgroup.zpowers e ⊔ B : Subgroup G) : Set G) := by
    rw [heq]
    exact hcE
  rw [hset] at hc'
  obtain ⟨a, ha, b, hbB, hab⟩ := hc'
  obtain ⟨n, rfl⟩ := exists_pow_eq_of_mem_zpowers ha
  change e ^ n * b = c at hab
  have hbE : b ∈ E := (Subgroup.mem_inf.mp hbB).1
  have hbK : b ∈ K := (Subgroup.mem_inf.mp hbB).2
  have hb3 : b ^ 3 = 1 := hE3.2 b hbE
  set d := ⁅x, y⁆ with hd
  have hdEL : d ∈ E ⊓ L := hfr.hEL ▸ Subgroup.mem_zpowers _
  have hdK : d ∈ K := hELK hdEL
  have hbd : b ∉ Subgroup.zpowers d := by
    intro hbd
    obtain ⟨k, rfl⟩ := exists_pow_eq_of_mem_zpowers hbd
    by_cases hn : 3 ∣ n
    · obtain ⟨m, rfl⟩ := hn
      apply hfr.hcL
      rw [← hab, pow_mul, he3, one_pow, one_mul]
      exact pow_mem hfr.hdL k
    · apply heF
      have hen : e ^ n ∈ F := by
        have : e ^ n = c * (d ^ k)⁻¹ := by rw [← hab]; group
        rw [this]
        exact mul_mem hfr.hcF (inv_mem (pow_mem (Subgroup.mem_inf.mp hfr.hdZ).2 k))
      exact Subgroup.zpowers_le.mpr hen (mem_zpowers_pow_of_not_dvd he3 hn)
  have hb1 : b ≠ 1 := fun h1 => hbd (h1 ▸ one_mem _)
  set bb := QuotientGroup.mk' (aschbacherSolvableCore 3 K) (⟨b, hbK⟩ : K) with hbb
  have hτ : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨c, hcN⟩) = MulAut.conj bb := by
    have heN : e ^ n ∈ Subgroup.normalizer (K : Set G) := hK.2.1 (pow_mem heE n)
    have hbN : b ∈ Subgroup.normalizer (K : Set G) := Subgroup.le_normalizer hbK
    have h1 : (⟨c, hcN⟩ : Subgroup.normalizer (K : Set G)) = ⟨e ^ n, heN⟩ * ⟨b, hbN⟩ :=
      Subtype.ext hab.symm
    have h2 : Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨e ^ n, heN⟩) = 1 :=
      (Sec4.Item424Proof.mem_thetaQuotCentralizer_iff_eq_one.mp
        (pow_mem heC n)).choose_spec
    rw [h1, map_mul, map_mul, h2, one_mul, KFacts.thetaQuotMulAut_compAction_of_mem hbK hbN]
  have hfix : (MulAut.conj bb).toMonoidHom.eqLocus (MonoidHom.id _) =
      Subgroup.centralizer ({bb} : Set (K ⧸ aschbacherSolvableCore 3 K)) := by
    ext z
    show (MulAut.conj bb).toMonoidHom z = MonoidHom.id _ z ↔ _
    rw [Subgroup.mem_centralizer_singleton_iff]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, MonoidHom.id_apply]
    constructor
    · intro h1
      calc z * bb = bb * z * bb⁻¹ * bb := by rw [h1]
        _ = bb * z := by group
    · intro h1
      calc bb * z * bb⁻¹ = z * bb * bb⁻¹ := by rw [h1]
        _ = z := by group
  rw [hτ, hfix]
  have hBK : B ≤ K := inf_le_right
  have hBK9 : Nat.card (B.subgroupOf K) = 9 := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBK).toEquiv, hB9]
  have hB3 : IsPGroup 3 (B.subgroupOf K) := by
    refine IsPGroup.of_card (n := 2) ?_
    rw [hBK9]
    norm_num
  obtain ⟨S, hBS⟩ := hB3.exists_le_sylow
  set Qb : Sylow 3 (K ⧸ aschbacherSolvableCore 3 K) :=
    S.mapSurjective (QuotientGroup.mk'_surjective _) with hQbdef
  have hQb : (Qb : Subgroup _) =
      (S : Subgroup K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) :=
    Sylow.coe_mapSurjective _ _
  set Bb := (B.subgroupOf K).map (QuotientGroup.mk' (aschbacherSolvableCore 3 K)) with hBbdef
  have hBbQ : Bb ≤ (Qb : Subgroup _) := by
    rw [hQb]
    exact Subgroup.map_mono hBS
  have hBb9 : Nat.card Bb = 9 := by
    rw [hBbdef, card_map_eq_of_injOn _ (injOn_mk_of_isPGroup Nat.prime_three hB3), hBK9]
  have hbbB : bb ∈ Bb := ⟨⟨b, hbK⟩, Subgroup.mem_subgroupOf.mpr hbB, rfl⟩
  obtain ⟨-, -, -, h4, -⟩ := h415 _ ⟨φK⟩ Qb _ rfl _ rfl
  by_cases hbZ : bb ∈ (Qb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) ⊓
      Subgroup.centralizer ((Qb : Subgroup (K ⧸ aschbacherSolvableCore 3 K)) :
        Set (K ⧸ aschbacherSolvableCore 3 K))
  ·
    exfalso
    have hc : ∃ S : Sylow 3 ↥K, (⟨b, hbK⟩ : ↥K) ∈ (S : Subgroup ↥K) ∧
        (S : Subgroup ↥K) ≤ Subgroup.centralizer ({(⟨b, hbK⟩ : ↥K)} : Set ↥K) := by
      refine ⟨S, hBS (Subgroup.mem_subgroupOf.mpr hbB), fun s hs => ?_⟩
      rw [Subgroup.mem_centralizer_singleton_iff]
      have hsb : QuotientGroup.mk' (aschbacherSolvableCore 3 K) s * bb =
          bb * QuotientGroup.mk' (aschbacherSolvableCore 3 K) s := by
        have hsQ : QuotientGroup.mk' (aschbacherSolvableCore 3 K) s ∈ (Qb : Subgroup _) := by
          rw [hQb]
          exact Subgroup.mem_map_of_mem _ hs
        exact Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp hbZ).2 _ hsQ
      have hbS : (⟨b, hbK⟩ : K) ∈ (S : Subgroup K) := hBS (Subgroup.mem_subgroupOf.mpr hbB)
      obtain ⟨w, hw⟩ : ∃ w : K, w = s * ⟨b, hbK⟩ * s⁻¹ * (⟨b, hbK⟩ : K)⁻¹ := ⟨_, rfl⟩
      have hwθ : w ∈ aschbacherSolvableCore 3 K := by
        have h1 : QuotientGroup.mk' (aschbacherSolvableCore 3 K) w = 1 := by
          rw [hw, map_mul, map_mul, map_mul, map_inv, map_inv, ← hbb, hsb]
          group
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
        exact h1
      have hwS : w ∈ (S : Subgroup K) := by
        rw [hw]
        exact mul_mem (mul_mem (mul_mem hs hbS) (inv_mem hs)) (inv_mem hbS)
      obtain ⟨k, hk⟩ := S.isPGroup' ⟨w, hwS⟩
      have hk' : w ^ 3 ^ k = 1 := by
        have h2 := congrArg (fun z : (S : Subgroup K) => (z : K)) hk
        rw [Subgroup.coe_pow, Subgroup.coe_one] at h2
        exact h2
      have hw1 : w = 1 := Item134SylowBarProof.eq_one_of_mem_theta_of_pow hwθ hk'
      rw [hw] at hw1
      calc s * ⟨b, hbK⟩ = s * ⟨b, hbK⟩ * s⁻¹ * (⟨b, hbK⟩ : K)⁻¹ * (⟨b, hbK⟩ * s) := by group
        _ = ⟨b, hbK⟩ * s := by rw [hw1, one_mul]
    exact false_of_threeCentral h415 h48 hfr heΩ hK heF φK hbE hbK hb1 hbd hab hc
  ·
    exact isSolvable_centralizer_j2 h415 ⟨φK⟩ Qb hBbQ hBb9 hbbB hbZ

end CFSG.RankThree.PartTwo.Sec13.Ronan138S

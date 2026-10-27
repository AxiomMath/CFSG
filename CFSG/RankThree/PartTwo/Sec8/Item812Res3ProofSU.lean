module

public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGen
import CFSG.RankThree.PartTwo.Sec8.Item812Res3ProofTools
import CFSG.RankThree.PartOne.KF.ClsSUUpper

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj StatedSU)
open CFSG.Assembly.RankThreeEven (localRank projSp projSL projSU)

namespace Item812Res3

theorem seven_dvd_card_projSL_two {m : ℕ} (hm : 1 ≤ m) :
    7 ∣ Nat.card (projSL 2 (GaloisField 2 (3 * m))) := by
  rw [Item812Res2.card_projSL_two (by omega)]
  apply Dvd.dvd.mul_left
  have h : (2 ^ (3 * m)) % 7 = 1 := by
    rw [pow_mul, Nat.pow_mod]
    norm_num
  have h2 : ((2 ^ (3 * m)) ^ 2) % 7 = 1 := by rw [Nat.pow_mod, h]
  have h3 : 1 ≤ (2 ^ (3 * m)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
  omega

theorem seven_dvd_card_of_isoSUThree {X : Type} [Group X] {m : ℕ} (hm : 1 ≤ m)
    (hX : IsoSUThree X (2 ^ (3 * m))) : 7 ∣ Nat.card X := by
  obtain ⟨K, _, _, hK, ⟨e⟩⟩ := hX
  have hU : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 2 (3 * m) K :=
    ⟨Nat.prime_two, by omega, by rw [hK, ← pow_mul, mul_comm]⟩
  have : CharP K 2 := hU.charP
  have hc := CFSG.RankThree.PartOne.KFU.card_statedSU_eq hU (n := 3) (by norm_num)
  rw [show Finset.Icc 2 3 = {2, 3} by decide, Finset.prod_pair (by norm_num)] at hc
  rw [Nat.card_congr e.toEquiv]
  have h7 : (7 : ℤ) ∣ ((2 ^ (3 * m) : ℕ) : ℤ) ^ 2 - (-1) ^ 2 := by
    have h : (2 ^ (3 * m)) % 7 = 1 := by
      rw [pow_mul, Nat.pow_mod]
      norm_num
    have h2 : ((2 ^ (3 * m)) ^ 2) % 7 = 1 := by rw [Nat.pow_mod, h]
    have h3 : 1 ≤ (2 ^ (3 * m)) ^ 2 := Nat.one_le_pow _ _ (by positivity)
    have h4 : 7 ∣ (2 ^ (3 * m)) ^ 2 - 1 := by omega
    have h5 := Int.natCast_dvd_natCast.mpr h4
    rw [Nat.cast_sub h3, Nat.cast_pow, Nat.cast_one] at h5
    simpa using h5
  have h8 : (7 : ℤ) ∣ (Nat.card (StatedSU 3 (2 ^ (3 * m)) K) : ℤ) := by
    rw [hc]
    exact Dvd.dvd.mul_left (Dvd.dvd.mul_right h7 _) _
  exact Int.natCast_dvd_natCast.mp h8

theorem card_sec8B_eq_of_projSp {G : Type} [Group G] [Finite G] (h3 : localRank 3 G ≤ 3)
    {A : Subgroup G} (hAF : A ∈ partTwoF G) (hA81 : Nat.card A = 81) {f : G} (hfA : f ∈ A)
    (hf1 : f ≠ 1) {Lf : Subgroup G} (hLf : Lf ∈ thetaComponentsAt 3 f)
    (hX : Nonempty (Lf ⧸ aschbacherSolvableCore 3 Lf ≃* projSp 2 (GaloisField 2 3)))
    {x : G} (hxA : x ∈ A) (hxout : InducesOuterTheta x Lf) : Nat.card (sec8B A Lf) = 27 := by
  classical
  obtain ⟨S₀, hS₀A, hS₀card, hdisj, -, -, hBeq⟩ :=
    Item812Res2.sec8B_structure_of_projSp h3 hAF hA81 hfA hf1 hLf hX hxA hxout
  have hAab := hAF.1
  have hAc : ∀ y ∈ A, ∀ y' ∈ A, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  set S' := S₀.map Lf.subtype with hS'
  have hS'card : Nat.card S' = 9 := by
    rw [hS', Subgroup.card_map_of_injective Lf.subtype_injective, hS₀card]
  set F := GaloisField 2 3 with hF
  set e : Lf ⧸ aschbacherSolvableCore 3 Lf ≃* StatedProj (StatedSp 2 F) :=
    hX.some.trans (Sec4.projSpEquivStatedProj 2 F) with he
  have hZ : Subgroup.center (StatedProj (StatedSp 2 F)) = ⊥ :=
    Item812Res2.center_statedProj_eq_bot
  have hinf : Subgroup.zpowers f ⊓ S' = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzf, hzS⟩
    obtain ⟨z₀, hz₀, rfl⟩ := hzS
    have hcen : e (QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) z₀) ∈
        Subgroup.center (StatedProj (StatedSp 2 F)) := by
      rw [Subgroup.mem_center_iff]
      intro w
      obtain ⟨w', rfl⟩ := e.surjective w
      rw [← map_mul, ← map_mul]
      congr 1
      induction w' using QuotientGroup.induction_on with
      | H w =>
        change QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) w *
            QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) z₀ =
          QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) z₀ *
            QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) w
        rw [← map_mul, ← map_mul]
        congr 1
        apply Subtype.ext
        obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hzf
        have hwf : (w : G) * f = f * w := Subgroup.mem_centralizer_singleton_iff.mp
          (le_centralizer_of_mem_thetaComponentsAt_three hLf w.2)
        simp only [Subgroup.coe_mul, Subgroup.coe_subtype] at hk ⊢
        rw [← hk]
        exact (Commute.zpow_right (show Commute (w : G) f from hwf) k).eq
    rw [hZ, Subgroup.mem_bot, map_eq_one_iff _ e.injective, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hcen
    have h2 : z₀ ∈ S₀ ⊓ aschbacherSolvableCore 3 Lf := ⟨hz₀, hcen⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h2
    rw [h2]
    exact Subgroup.one_mem _
  have hcommfS : ∀ z ∈ Subgroup.zpowers f, ∀ s ∈ S', z * s = s * z := by
    intro z hz s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact hAc _ (A.zpow_mem hfA k) _ (hS₀A hs)
  have hfo : orderOf f = 3 := orderOf_eq_prime (hAab.2 f hfA) hf1
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommfS
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hfo, hS'card] at hcard
  rw [hBeq, hcard]

end Item812Res3

section SU

@[expose] def KF811UnitaryInner : Prop :=
  ∀ (M : Type) [Group M], IsUnitaryTwo M 3 → ∀ τ : MulAut M, τ ^ 3 = 1 →
    7 ∣ Nat.card (τ.toMonoidHom.eqLocus (MonoidHom.id M)) → KFacts.IsInnerAut τ

open Item812Res2 Item812Res3 in
theorem pair811GenSU_of
    (hK : KF811UnitaryInner) : Pair811GenSU := by
  intro G _ _ A c L a b X n h hX e Le hrel hrel' hLe
  classical
  have h3 := h.toTheoremFourHyp.localRank_three.le
  have hAab := h.mem_partTwoF.1
  have hAc : ∀ y ∈ A, ∀ y' ∈ A, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  have hbA : b ∈ A := h.mem_pairOmega.1
  have hb1 : b ≠ 1 := h.mem_pairOmega.2.1
  have hb3 : b ^ 3 = 1 := hAab.2 b hbA
  have hXb : X ∈ thetaComponentsAt 3 b := h.mem_pairOmega.2.2.1
  obtain ⟨x, hxA, hxout⟩ := exists_inducesOuterTheta_of_mem_pairOmega h.mem_pairOmega
  have heA : e ∈ A := hrel.1.1
  have hLe_mem : Le ∈ thetaComponentsAt 3 e := hrel.1.2.2.1
  have hBX := sec8B_eq_of_projSp h3 h.mem_partTwoF h.card_eq hbA hb1 hXb hX hxA hxout hrel'.2.1
  have hXcb : X ≤ Subgroup.centralizer ({b} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt_three hXb
  have hLce : Le ≤ Subgroup.centralizer ({e} : Set G) :=
    le_centralizer_of_mem_thetaComponentsAt_three hLe_mem
  have hKeq := perfectResidual_inf_centralizer_eq hXcb hLce hrel.2.2.2.1 hrel'.2.2.2.1
  have hRHS : Subgroup.closure {e, b} ⊔
      (A ⊓ inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({b} : Set G))) =
        sec8B A X := by
    rw [hBX, ← hKeq, Set.pair_comm]
  rw [hRHS]
  have hBXcard : Nat.card (sec8B A X) = 27 :=
    card_sec8B_eq_of_projSp h3 h.mem_partTwoF h.card_eq hbA hb1 hXb hX hxA hxout
  set K := inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({b} : Set G)) with hKdef
  have hKLe : K ≤ Le :=
    (Subgroup.map_subtype_le _).trans (inf_le_left : Le ⊓ Subgroup.centralizer {b} ≤ Le)
  have hKb : ∀ y ∈ K, b * y = y * b := by
    intro y hy
    have hy' : y ∈ Le ⊓ Subgroup.centralizer ({b} : Set G) := Subgroup.map_subtype_le _ hy
    exact (Subgroup.mem_centralizer_singleton_iff.mp hy'.2).symm
  obtain ⟨m, hm⟩ := hrel.2.1
  have hm1 : 1 ≤ m := hm.2.2.1
  have h7 : 7 ∣ Nat.card (imageModTheta Le K) := by
    rcases hm.2.2.2 with ⟨-, -, -, -, hSU⟩ | ⟨-, ⟨ι⟩⟩
    · exact seven_dvd_card_of_isoSUThree hm1 hSU
    · rw [Nat.card_congr ι.toEquiv]
      exact seven_dvd_card_projSL_two hm1
  have hKne : K ≠ ⊥ := by
    intro hK0
    rw [hK0, imageModTheta, Subgroup.bot_subgroupOf, Subgroup.map_bot,
      Subgroup.card_bot] at h7
    norm_num at h7
  have hbe : b ∈ Subgroup.centralizer ({e} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc b hbA e heA)
  have hbN : b ∈ Subgroup.normalizer (Le : Set G) :=
    mem_normalizer_of_commute_perfect hLe_mem hbe hKne
      (isPerfect_inSubgroup_perfectResidual_sec8 _) hKLe hKb
  set τ := thetaQuotMulAut Le (compAction Le ⟨b, hbN⟩) with hτ
  have hτ3 : τ ^ 3 = 1 := by
    have hb3' : (⟨b, hbN⟩ : Subgroup.normalizer (Le : Set G)) ^ 3 = 1 :=
      Subtype.ext (by simpa using hb3)
    rw [hτ, ← map_pow, ← map_pow, hb3', map_one, map_one]
  have hfix : barCentralizer (Subgroup.zpowers b) Le = τ.toMonoidHom.eqLocus (MonoidHom.id _) := by
    ext z
    rw [KFacts.mem_barCentralizer_zpowers_iff hbN]
    rfl
  have hτ7 : 7 ∣ Nat.card (τ.toMonoidHom.eqLocus (MonoidHom.id _)) := by
    rw [← hfix]
    have himg : imageModTheta Le K =
        inSubgroup perfectResidual (barCentralizer (Subgroup.zpowers b) Le) :=
      KFacts.imageModTheta_perfectResidual_centralizer_eq hbN ⟨1, by simpa using hb3⟩
    rw [himg] at h7
    exact h7.trans (Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _))
  have hinner : KFacts.IsInnerAut τ := hK _ hLe τ hτ3 hτ7
  have heN : e ∈ Subgroup.normalizer (Le : Set G) :=
    mem_normalizer_of_forall_commute fun y hy =>
      (Subgroup.mem_centralizer_singleton_iff.mp (hLce hy)).symm
  have heB : e ∈ sec8B A Le := by
    refine ⟨heA, (mem_sup_thetaQuotCentralizer_iff heN).mpr ?_⟩
    have h1 : compAction Le ⟨e, heN⟩ = 1 := by
      refine MulEquiv.ext fun l => Subtype.ext ?_
      change e * (l : G) * e⁻¹ = (l : G)
      have hle : (l : G) * e = e * l :=
        Subgroup.mem_centralizer_singleton_iff.mp (hLce l.2)
      rw [← hle, mul_inv_cancel_right]
    rw [h1, map_one]
    exact ⟨1, map_one _⟩
  have hbB : b ∈ sec8B A Le := ⟨hbA, (mem_sup_thetaQuotCentralizer_iff hbN).mpr hinner⟩
  have hle : sec8B A X ≤ sec8B A Le := by
    rw [← hRHS]
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact heB
      · exact hbB
    · rintro w ⟨hwA, hwK⟩
      exact ⟨hwA, Subgroup.mem_sup_left (hKLe hwK)⟩
  obtain ⟨x', hx'A, hx'out⟩ := exists_inducesOuterTheta_of_mem_pairOmega hrel.1
  have hx'B : x' ∉ sec8B A Le := by
    rintro ⟨-, hx'⟩
    obtain ⟨hx'N, hx'o⟩ := hx'out
    exact hx'o ((mem_sup_thetaQuotCentralizer_iff hx'N).mp hx')
  have hBeA : sec8B A Le ≤ A := inf_le_left
  have hBe : Nat.card (sec8B A Le) ≤ 27 := by
    have hdvd : Nat.card (sec8B A Le) ∣ 81 := h.card_eq ▸ Subgroup.card_dvd_of_le hBeA
    have hne : Nat.card (sec8B A Le) ≠ 81 := by
      intro h81
      have heq : sec8B A Le = A :=
        Subgroup.eq_of_le_of_card_ge hBeA (by rw [h81, h.card_eq])
      exact hx'B (by rw [heq]; exact hx'A)
    have h81 : (81 : ℕ) = 3 ^ 4 := by norm_num
    rw [h81] at hdvd hne
    obtain ⟨k, hk, hk'⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp hdvd
    rw [hk'] at hne ⊢
    interval_cases k <;> simp_all
  exact (Subgroup.eq_of_le_of_card_ge hle (by omega)).symm

end SU

end CFSG.RankThree.PartTwo.Sec8

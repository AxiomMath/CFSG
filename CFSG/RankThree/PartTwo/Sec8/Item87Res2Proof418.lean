module

public import CFSG.RankThree.PartTwo.Sec8.Item87ProofGamma
import CFSG.RankThree.PartTwo.KFacts.K71Residual
import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
import CFSG.RankThree.PartTwo.Sec6.Item65Tools
import CFSG.RankThree.LocalRank.ThetaCoreQuotients

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

namespace Item87Res2Proof

variable {G : Type} [Group G] [Finite G]

omit [Finite G] in
theorem isPGroup_zpowers_of_pow_three {x : G} (hx : x ^ 3 = 1) :
    IsPGroup 3 (Subgroup.zpowers x) := by
  rw [IsPGroup.iff_orderOf]
  rintro ⟨g, hg⟩
  obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hg
  have h1 : (⟨x ^ k, hg⟩ : Subgroup.zpowers x) ^ 3 = 1 := by
    apply Subtype.ext
    rw [SubmonoidClass.coe_pow, Subgroup.coe_one, ← zpow_natCast, ← zpow_mul, mul_comm,
      zpow_mul, zpow_natCast, hx, one_zpow]
  obtain ⟨i, -, hi⟩ := (Nat.dvd_prime_pow Nat.prime_three).mp
    (orderOf_dvd_of_pow_eq_one (by rw [show (3 : ℕ) = 3 ^ 1 by norm_num] at h1; exact h1))
  exact ⟨i, hi⟩

theorem pCore_three_ne_bot (h : 3 ∣ Nat.card (Subgroup.center G)) : CFSG.pCore 3 G ≠ ⊥ := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center G) 3 h
  have hz3 : (z : G) ^ 3 = 1 := by
    rw [← Subgroup.coe_pow, ← hz, pow_orderOf_eq_one, Subgroup.coe_one]
  have hz1 : (z : G) ≠ 1 := by
    intro h1
    have : z = 1 := Subtype.ext h1
    rw [this, orderOf_one] at hz
    norm_num at hz
  have hN : (Subgroup.zpowers (z : G)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr z.2)
  have hle : Subgroup.zpowers (z : G) ≤ CFSG.pCore 3 G :=
    le_sSup ⟨hN, isPGroup_zpowers_of_pow_three hz3⟩
  intro hbot
  rw [hbot, le_bot_iff, Subgroup.zpowers_eq_bot] at hle
  exact hz1 hle

theorem noThetaNormal_quot (L : Subgroup G) : NoThetaNormal (L ⧸ aschbacherSolvableCore 3 L) := by
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  have h := (solvable_prime_complement_core_quotient_centralizers (G := L) Nat.prime_three
    (aschbacherSolvableCore 3 L) hθs hθ3).2.2.1
  obtain ⟨-, -, -, hmax, -⟩ := solvable_prime_complement_core_characterization
    (H := L ⧸ aschbacherSolvableCore 3 L) Nat.prime_three
  intro N hN hNs hN3
  have := hmax N hN hNs hN3
  rwa [h, le_bot_iff] at this

section QuotEquiv

variable {L K : Subgroup G}

noncomputable abbrev toQuot (hKL : K ≤ L) : K →* L ⧸ aschbacherSolvableCore 3 L :=
  (QuotientGroup.mk' (aschbacherSolvableCore 3 L)).comp (Subgroup.inclusion hKL)

omit [Finite G] in
theorem toQuot_apply [Finite G] (hKL : K ≤ L) (k : K) :
    toQuot hKL k = ((⟨k, hKL k.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) :=
  rfl

theorem range_toQuot (hKL : K ≤ L) : (toQuot hKL).range = imageModTheta L K := by
  rw [MonoidHom.range_comp, imageModTheta]
  congr 1
  ext z
  constructor
  · rintro ⟨k, rfl⟩
    exact Subgroup.mem_subgroupOf.mpr k.2
  · intro hz
    exact ⟨⟨z, Subgroup.mem_subgroupOf.mp hz⟩, rfl⟩

noncomputable def kerToQuotEmb (hKL : K ≤ L) :
    (toQuot hKL).ker →* aschbacherSolvableCore 3 L where
  toFun k := ⟨Subgroup.inclusion hKL k, by
    have h1 : toQuot hKL k = 1 := k.2
    rwa [toQuot_apply, QuotientGroup.eq_one_iff] at h1⟩
  map_one' := rfl
  map_mul' _ _ := rfl

theorem kerToQuotEmb_injective (hKL : K ≤ L) : Function.Injective (kerToQuotEmb hKL) := by
  intro u v huv
  have h := congrArg (fun w : aschbacherSolvableCore 3 L => ((w : L) : G)) huv
  exact Subtype.ext (Subtype.ext h)

theorem ker_toQuot_le (hKL : K ≤ L) : (toQuot hKL).ker ≤ aschbacherSolvableCore 3 K := by
  obtain ⟨-, -, -, hθmax, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := L) Nat.prime_three
  refine hθmax _ (MonoidHom.normal_ker _) ?_ ?_
  · have := hθs
    exact Group.isSolvable_of_isSolvable_injective (kerToQuotEmb_injective hKL)
  · exact fun h3 => hθ3 (h3.trans (Subgroup.card_dvd_of_injective _ (kerToQuotEmb_injective hKL)))

theorem ker_toQuot_eq (hKL : K ≤ L) (h : imageModTheta L K = ⊤) :
    (toQuot hKL).ker = aschbacherSolvableCore 3 K := by
  obtain ⟨hθs, -, hθ3, -, -⟩ :=
    solvable_prime_complement_core_characterization (H := K) Nat.prime_three
  set ρ := toQuot hKL with hρ
  have hρs : Function.Surjective ρ := by
    rw [← MonoidHom.range_eq_top, range_toQuot, h]
  refine le_antisymm (ker_toQuot_le hKL) ?_
  set M := (aschbacherSolvableCore 3 K).map ρ with hM
  have hMn : M.Normal := by
    have : (aschbacherSolvableCore 3 K).Normal := inferInstance
    exact this.map ρ hρs
  have hMs : Group.IsSolvable M := by
    have := hθs
    exact Group.isSolvable_of_surjective (ρ.subgroupMap_surjective _)
  have hM3 : ¬ 3 ∣ Nat.card M := fun h3 => hθ3 (h3.trans (Subgroup.card_map_dvd _ _))
  have hM1 : M = ⊥ := noThetaNormal_quot L M hMn hMs hM3
  intro k hk
  rw [MonoidHom.mem_ker]
  have : ρ k ∈ M := Subgroup.mem_map_of_mem ρ hk
  rwa [hM1, Subgroup.mem_bot] at this

theorem toQuot_surjective (hKL : K ≤ L) (h : imageModTheta L K = ⊤) :
    Function.Surjective (toQuot hKL) := by
  rw [← MonoidHom.range_eq_top, range_toQuot, h]

@[expose] noncomputable def quotEquivOfImageEqTop (hKL : K ≤ L) (h : imageModTheta L K = ⊤) :
    K ⧸ aschbacherSolvableCore 3 K ≃* L ⧸ aschbacherSolvableCore 3 L :=
  (QuotientGroup.quotientMulEquivOfEq (ker_toQuot_eq hKL h).symm).trans
    (QuotientGroup.quotientKerEquivOfSurjective _ (toQuot_surjective hKL h))

theorem quotEquivOfImageEqTop_mk (hKL : K ≤ L) (h : imageModTheta L K = ⊤) (k : K) :
    quotEquivOfImageEqTop hKL h (k : K ⧸ aschbacherSolvableCore 3 K) =
      ((⟨k, hKL k.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) :=
  rfl

theorem quotEquivOfImageEqTop_thetaQuotMulAut (hKL : K ≤ L) (h : imageModTheta L K = ⊤) {x : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G))
    (q : K ⧸ aschbacherSolvableCore 3 K) :
    quotEquivOfImageEqTop hKL h (Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨x, hxK⟩) q) =
      Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨x, hxL⟩) (quotEquivOfImageEqTop hKL h q) := by
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [Sec4.thetaQuotMulAut_mk, quotEquivOfImageEqTop_mk, quotEquivOfImageEqTop_mk,
      Sec4.thetaQuotMulAut_mk]
    rfl

theorem inducedAutHom_quotEquiv (hKL : K ≤ L) (h : imageModTheta L K = ⊤) {M : Type*} [Group M]
    (e : K ⧸ aschbacherSolvableCore 3 K ≃* M) {x : G}
    (hxK : x ∈ Subgroup.normalizer (K : Set G)) (hxL : x ∈ Subgroup.normalizer (L : Set G)) :
    KFacts.inducedAutHom L ((quotEquivOfImageEqTop hKL h).symm.trans e) ⟨x, hxL⟩ =
      KFacts.inducedAutHom K e ⟨x, hxK⟩ := by
  ext m
  rw [KFacts.inducedAutHom_apply, KFacts.inducedAutHom_apply]
  simp only [MulAut.congr_apply, MulEquiv.symm_trans_apply, MulEquiv.trans_apply]
  congr 1
  rw [MulEquiv.symm_symm, ← quotEquivOfImageEqTop_thetaQuotMulAut hKL h hxK hxL,
    MulEquiv.symm_apply_apply]

end QuotEquiv

theorem imageModTheta_eq_top_of_trivial {L : Subgroup G} (hL : L ∈ thetaComponents 3 G) {b : G}
    (hbN : b ∈ Subgroup.normalizer (L : Set G)) (hb3 : b ^ 3 = 1)
    (hτ : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨b, hbN⟩) = 1) {K : Subgroup G}
    (hK : K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b})) : imageModTheta L K = ⊤ := by
  set M := L ⊓ Subgroup.centralizer ({b} : Set G) with hMdef
  set W := inSubgroup perfectResidual M with hW
  have hbar : barCentralizer (Subgroup.zpowers b) L = ⊤ := by
    rw [eq_top_iff]
    intro w _
    rw [KFacts.mem_barCentralizer_zpowers_iff hbN, hτ]
    rfl
  have hLq : IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) := hL.2.2
  have : Group.IsPerfect (L ⧸ aschbacherSolvableCore 3 L) := hLq.1
  have himg : imageModTheta L W = ⊤ := by
    rw [KFacts.imageModTheta_perfectResidual_centralizer_eq hbN ⟨1, by rwa [pow_one]⟩, hbar]
    refine eq_top_iff.mpr (KFacts.le_inSubgroup_perfectResidual ?_ le_rfl)
    exact Group.IsPerfect.ofSurjective (f := (Subgroup.topEquiv.symm :
      L ⧸ aschbacherSolvableCore 3 L ≃* (⊤ : Subgroup _)).toMonoidHom) (MulEquiv.surjective _)
  have hWM : W ≤ M := Item87Proof.residual_le M
  have hWL : W ≤ L := hWM.trans inf_le_left
  have hWq : IsQuasisimple (W ⧸ aschbacherSolvableCore 3 W) :=
    Item87Proof.isQuasisimple_quot_of_imageModTheta hWL (by
      rw [himg]
      exact LocalCores.isQuasisimple_of_mulEquiv Subgroup.topEquiv.symm hLq)
  have hWmem : W ∈ thetaComponentsIn M :=
    Sec6.mem_thetaComponentsIn_of hWM (Item87Proof.isPerfect_residual M)
      (Item87Proof.normal_subgroupOf_residual M).isSubnormal hWq
  have hKp : Group.IsPerfect K := (mem_thetaComponentsIn_iff.mp hK).2.1.ofSurjective
    (f := (Subgroup.subgroupOfEquivOfLe (le_of_mem_thetaComponentsIn hK)).toMonoidHom)
    (MulEquiv.surjective _)
  have hKW : K ≤ W := KFacts.le_inSubgroup_perfectResidual hKp (le_of_mem_thetaComponentsIn hK)
  have hKW' : K = W := Sec6.eq_of_mem_thetaComponentsIn_of_le hK hWmem hKp
    (Item87Proof.ne_bot_of_mem_thetaComponentsIn hK) le_rfl hKW
  rw [hKW']
  exact himg

end Item87Res2Proof

namespace Item87Res2Proof

variable {G : Type} [Group G] [Finite G]

theorem InducesStdKind.of_quotEquiv {L K : Subgroup G} (hKL : K ≤ L) (h : imageModTheta L K = ⊤)
    {x : G} (hxL : x ∈ Subgroup.normalizer (L : Set G)) {k : KFacts.AutKind}
    (hk : KFacts.InducesStdKind K x k) : KFacts.InducesStdKind L x k := by
  cases hk with
  | psl2 K' hK =>
    obtain ⟨e, hx, hP⟩ := hK
    exact .psl2 K' ⟨_, hxL, by rwa [inducedAutHom_quotEquiv hKL h e hx hxL]⟩
  | psl n K' hn hK =>
    obtain ⟨e, hx, hP⟩ := hK
    exact .psl n K' hn ⟨_, hxL, by rwa [inducedAutHom_quotEquiv hKL h e hx hxL]⟩
  | sl n K' hn hK =>
    obtain ⟨e, hx, hP⟩ := hK
    exact .sl n K' hn ⟨_, hxL, by rwa [inducedAutHom_quotEquiv hKL h e hx hxL]⟩
  | psu3 hK hq hK' =>
    obtain ⟨e, hx, hP⟩ := hK'
    exact .psu3 hK hq ⟨_, hxL, by rwa [inducedAutHom_quotEquiv hKL h e hx hxL]⟩
  | su3 hK hq hK' =>
    obtain ⟨e, hx, hP⟩ := hK'
    exact .su3 hK hq ⟨_, hxL, by rwa [inducedAutHom_quotEquiv hKL h e hx hxL]⟩
  | psp r K' hr hK =>
    obtain ⟨e, hx, hP⟩ := hK
    exact .psp r K' hr ⟨_, hxL, by rwa [inducedAutHom_quotEquiv hKL h e hx hxL]⟩
  | psp4even F hK =>
    obtain ⟨e, hx, hP⟩ := hK
    exact .psp4even F ⟨_, hxL, by rwa [inducedAutHom_quotEquiv hKL h e hx hxL]⟩
  | g2 K' hK3 hK4 hK =>
    obtain ⟨e, hx, hP⟩ := hK
    exact .g2 K' hK3 hK4 ⟨_, hxL, by rwa [inducedAutHom_quotEquiv hKL h e hx hxL]⟩
  | sz a K' ha hK hK' =>
    obtain ⟨e, hx, hP⟩ := hK'
    exact .sz a K' ha hK ⟨_, hxL, by rwa [inducedAutHom_quotEquiv hKL h e hx hxL]⟩
  | triality f hf K' hK σ hσ hK' =>
    obtain ⟨e, hx, hP⟩ := hK'
    exact .triality f hf K' hK σ hσ ⟨_, hxL, by rwa [inducedAutHom_quotEquiv hKL h e hx hxL]⟩
  | largeRee a ha K' hK hK' =>
    obtain ⟨e, hx, hP⟩ := hK'
    exact .largeRee a ha K' hK ⟨_, hxL, by rwa [inducedAutHom_quotEquiv hKL h e hx hxL]⟩

theorem false_of_mul_zpow_mem {L K : Subgroup G} {a b : G} (hKL : K ≤ L)
    (hKb : K ≤ Subgroup.centralizer ({b} : Set G)) {j : ℤ}
    (hab : a * b ^ j ∈ Sec4.thetaQuotCentralizer L) (hKa : KFacts.InducesStdKind K a .field) :
    False := by
  obtain ⟨haK, hout⟩ := KFacts.InducesStdKind.inducesOuterTheta K hKa (by decide)
  obtain ⟨⟨y, hyN⟩, hy, rfl⟩ := hab
  have hy1 : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a * b ^ j, hyN⟩) = 1 := hy
  apply hout
  refine ⟨1, ?_⟩
  rw [map_one]
  symm
  ext q
  induction q using QuotientGroup.induction_on with
  | H k =>
    rw [Sec4.thetaQuotMulAut_mk, MulAut.one_apply]
    have hk : ((⟨(k : G), hKL k.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L) =
        ((⟨a * (k : G) * a⁻¹, hKL (Sec4.compAction K ⟨a, haK⟩ k).2⟩ : L) :
          L ⧸ aschbacherSolvableCore 3 L) := by
      have h1 := congrArg (fun τ : MulAut (L ⧸ aschbacherSolvableCore 3 L) =>
        τ ((⟨(k : G), hKL k.2⟩ : L) : L ⧸ aschbacherSolvableCore 3 L)) hy1
      simp only [Sec4.thetaQuotMulAut_mk, MulAut.one_apply] at h1
      rw [← h1]
      congr 1
      apply Subtype.ext
      have hkb : (b ^ j) * (k : G) * (b ^ j)⁻¹ = k := by
        have hc : (k : G) * b = b * k :=
          (Subgroup.mem_centralizer_singleton_iff.mp (hKb k.2))
        rw [(Commute.zpow_left hc.symm j).eq, mul_inv_cancel_right]
      change a * b ^ j * (k : G) * (a * b ^ j)⁻¹ = a * (k : G) * a⁻¹
      rw [mul_inv_rev, show a * b ^ j * (k : G) * ((b ^ j)⁻¹ * a⁻¹) =
        a * ((b ^ j) * (k : G) * (b ^ j)⁻¹) * a⁻¹ by group, hkb]
    have hρ : toQuot hKL (Sec4.compAction K ⟨a, haK⟩ k) = toQuot hKL k := hk.symm
    have hmem : (Sec4.compAction K ⟨a, haK⟩ k)⁻¹ * k ∈ aschbacherSolvableCore 3 K :=
      ker_toQuot_le hKL (by rw [MonoidHom.mem_ker, map_mul, map_inv, hρ, inv_mul_cancel])
    exact QuotientGroup.eq.mpr hmem

end Item87Res2Proof

@[expose] def KF418Faithful : Prop :=
  ∀ (G : Type) [Group G] [Finite G], SectionFourHyp G → 3 ∣ Nat.card (Subgroup.center G) →
    ∀ a b : G, a ^ 3 = 1 → b ^ 3 = 1 → a * b = b * a → b ≠ 1 → a ∉ Subgroup.zpowers b →
    ∀ L ∈ thetaComponents 3 G, a ∈ Subgroup.normalizer (L : Set G) →
      b ∈ Subgroup.normalizer (L : Set G) → b ∉ Sec4.thetaQuotCentralizer L →
      (∀ j : ℤ, a * b ^ j ∉ Sec4.thetaQuotCentralizer L) →
    ∀ K ∈ thetaComponentsIn (L ⊓ Subgroup.centralizer {b}),
    ∀ n : ℕ, 1 ≤ n → IsType418 (K ⧸ aschbacherSolvableCore 3 K) n →
      KFacts.InducesStdKind K a .field →
      (KFacts.InducesStdKind L a .field ∨ KFacts.InducesStdKind L a .graphField) ∧
        ¬ (KFacts.InducesStdKind L b .field ∨ KFacts.InducesStdKind L b .graphField)

theorem item418Theta_of (h45 : Sec4.Item4_5) (hF : KF418Faithful) : Item418Theta := by
  intro G _ _ hS4 hZ a b ha3 hb3 hab hb1 habz L hL K hK n hn htype hKa
  have hO3 := Item87Res2Proof.pCore_three_ne_bot hZ
  have haN : a ∈ Subgroup.normalizer (L : Set G) :=
    h45 G hS4 (Subgroup.zpowers a) (Item87Res2Proof.isPGroup_zpowers_of_pow_three ha3)
      (Or.inl hO3) L hL (Subgroup.mem_zpowers a)
  have hbN : b ∈ Subgroup.normalizer (L : Set G) :=
    h45 G hS4 (Subgroup.zpowers b) (Item87Res2Proof.isPGroup_zpowers_of_pow_three hb3)
      (Or.inl hO3) L hL (Subgroup.mem_zpowers b)
  have hKM := le_of_mem_thetaComponentsIn hK
  have hKL : K ≤ L := hKM.trans inf_le_left
  have hKb : K ≤ Subgroup.centralizer ({b} : Set G) := hKM.trans inf_le_right
  by_cases hbC : b ∈ Sec4.thetaQuotCentralizer L
  ·
    obtain ⟨y, hy, hyb⟩ := hbC
    have hτ : Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨b, hbN⟩) = 1 := by
      rw [show (⟨b, hbN⟩ : Subgroup.normalizer (L : Set G)) = y from Subtype.ext hyb.symm]
      exact hy
    have himg := Item87Res2Proof.imageModTheta_eq_top_of_trivial hL hbN hb3 hτ hK
    refine ⟨Or.inl (Item87Res2Proof.InducesStdKind.of_quotEquiv hKL himg haN hKa), ?_⟩
    have hbout : ¬ Sec4.InducesOuterTheta b L := by
      rintro ⟨hb', hnot⟩
      apply hnot
      rw [show (⟨b, hb'⟩ : Subgroup.normalizer (L : Set G)) = ⟨b, hbN⟩ from rfl, hτ]
      exact ⟨1, map_one _⟩
    rintro (h | h)
    · exact KFacts.not_inducesStdKind_of_not_inducesOuterTheta L hbout (by decide) h
    · exact KFacts.not_inducesStdKind_of_not_inducesOuterTheta L hbout (by decide) h
  · by_cases haC : ∃ j : ℤ, a * b ^ j ∈ Sec4.thetaQuotCentralizer L
    · obtain ⟨j, hj⟩ := haC
      exact (Item87Res2Proof.false_of_mul_zpow_mem hKL hKb hj hKa).elim
    · push Not at haC
      exact hF G hS4 hZ a b ha3 hb3 hab hb1 habz L hL haN hbN hbC haC K hK n hn htype hKa

end CFSG.RankThree.PartTwo.Sec8

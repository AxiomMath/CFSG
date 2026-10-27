module

public import CFSG.RankThree.PartTwo.Sec8.Item812Proof811
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofGenTools
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofRee
import CFSG.RankThree.PartTwo.KFacts.K71Sp48Index
import CFSG.RankThree.PartTwo.Sec4.Census.WiringInputs
import CFSG.RankThree.PartOne.S10.AmbientTheta
public import CFSG.RankThree.PartTwo.Sec8.Item812Res2ProofCenter

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj)
open CFSG.Assembly.RankThreeEven (localRank projSp projSL)

namespace Item812Res2

theorem not_nonempty_reeF4_of_projSp
    {M : Type} [Group M] (hM : Nonempty (M ≃* projSp 2 (GaloisField 2 3))) (k : ℕ)
    (hk : (TauCeti.LieTypeIndex.reeF4 k).Valid) :
    ¬ Nonempty (M ≃* (TauCeti.CFSGIndex.lie ⟨.reeF4 k, hk⟩).Group) := by
  rintro ⟨eR⟩
  have hR := (Sec4.Census.bridgeExceptional46).reeF4 k hk
  obtain ⟨-, k', hk'1, -, K, _, _, _, hK, ⟨e₁⟩⟩ := Sec4.exists_mulEquiv_reeGamma hR
  have hc1 : Nat.card M = Nat.card (CFSG.LieType.Ree.ReeTag.F4.reeGamma K k') :=
    Nat.card_congr (eR.trans e₁).toEquiv
  have hc2 : Nat.card M = 1056706560 := by
    rw [Nat.card_congr hM.some.toEquiv, card_projSp_two_three]
  have hc3 := card_reeGamma_ge_pow hK
  have hq : 2 ^ 36 ≤ (2 ^ (2 * k' + 1)) ^ 12 := by
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by norm_num) (by omega)
  have : (2 : ℕ) ^ 36 = 68719476736 := by norm_num
  omega

end Item812Res2

namespace Item812Res2

theorem sec8B_structure_of_projSp {G : Type} [Group G] [Finite G] (h3 : localRank 3 G ≤ 3)
    {A : Subgroup G} (hAF : A ∈ partTwoF G) (hA81 : Nat.card A = 81) {f : G} (hfA : f ∈ A)
    (hf1 : f ≠ 1) {Lf : Subgroup G} (hLf : Lf ∈ thetaComponentsAt 3 f)
    (hX : Nonempty (Lf ⧸ aschbacherSolvableCore 3 Lf ≃* projSp 2 (GaloisField 2 3)))
    {x : G} (hxA : x ∈ A) (hxout : InducesOuterTheta x Lf) :
    ∃ S₀ : Subgroup Lf, S₀.map Lf.subtype ≤ A ∧ Nat.card S₀ = 9 ∧
      Disjoint S₀ (aschbacherSolvableCore 3 Lf) ∧
      CFSG.Assembly.IsElemAbelian 3 (S₀.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Lf))) ∧
      Nat.card (S₀.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Lf))) = 9 ∧
      sec8B A Lf = Subgroup.zpowers f ⊔ S₀.map Lf.subtype := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hAab, hAmax, -⟩ := hAF
  have hAN := le_normalizer_of_projSp h3 hAab hfA hf1 hLf hX
  set F := GaloisField 2 3 with hFdef
  set P := StatedProj (StatedSp 2 F) with hPdef
  set e : Lf ⧸ aschbacherSolvableCore 3 Lf ≃* P := hX.some.trans (projSpEquivStatedProj 2 F)
    with he
  set ρ : A →* MulAut P := (KFacts.inducedAutHom Lf e).comp (Subgroup.inclusion hAN) with hρ
  have hρapply : ∀ y : A, ρ y =
      MulAut.congr e (thetaQuotMulAut Lf (compAction Lf ⟨y, hAN y.2⟩)) := fun y => rfl
  have hZ : Subgroup.center P = ⊥ := center_statedProj_eq_bot
  have hconjinj := mulAutConj_injective hZ
  have hAc : ∀ y y' : A, y * y' = y' * y := fun y y' => hAab.1.is_comm.comm y y'
  have hCf := inf_thetaQuotCentralizer_le_zpowers_of_projSp h3 hAab hA81 hfA hf1 hLf hX hxA
    hxout
  have hfker : ρ ⟨f, hfA⟩ = 1 := by
    rw [hρapply]
    have h1 : compAction Lf ⟨f, hAN hfA⟩ = 1 := by
      refine MulEquiv.ext fun l => Subtype.ext ?_
      change f * (l : G) * f⁻¹ = (l : G)
      have hlf : (l : G) * f = f * l :=
        Subgroup.mem_centralizer_singleton_iff.mp
          (le_centralizer_of_mem_thetaComponentsAt_three hLf l.2)
      rw [← hlf, mul_inv_cancel_right]
    rw [h1, map_one, map_one]
  have hker_iff : ∀ y : A, ρ y = 1 ↔ (y : G) ∈ Subgroup.zpowers f := by
    intro y
    constructor
    · intro hy
      refine hCf ⟨y.2, ?_⟩
      refine ⟨⟨y, hAN y.2⟩, ?_, rfl⟩
      have h1 : MulAut.congr e (thetaQuotMulAut Lf (compAction Lf ⟨y, hAN y.2⟩)) = 1 := by
        rw [← hρapply]
        exact hy
      have h2 : thetaQuotMulAut Lf (compAction Lf ⟨y, hAN y.2⟩) = 1 := by
        rwa [map_eq_one_iff _ (MulAut.congr e).injective] at h1
      exact h2
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      have hy' : y = ⟨f, hfA⟩ ^ k := Subtype.ext (by simpa using hk.symm)
      rw [hy', map_zpow, hfker, one_zpow]
  have hfo : orderOf (⟨f, hfA⟩ : A) = 3 :=
    orderOf_eq_prime (Subtype.ext (by simpa using hAab.2 f hfA))
      (fun h1 => hf1 (by simpa using congrArg Subtype.val h1))
  have hkerEq : ρ.ker = Subgroup.zpowers (⟨f, hfA⟩ : A) := by
    ext y
    rw [MonoidHom.mem_ker, hker_iff]
    constructor
    · intro hy
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hy
      exact ⟨k, Subtype.ext (by simpa using hk)⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have hkercard : Nat.card ρ.ker = 3 := by rw [hkerEq, Nat.card_zpowers, hfo]
  have hrangecard : Nat.card ρ.range = 27 := by
    have h1 := Subgroup.card_mul_index ρ.ker
    rw [Subgroup.index_ker, hA81, hkercard] at h1
    omega
  have hρx : ¬ KFacts.IsInnerAut (ρ ⟨x, hxA⟩) :=
    (KFacts.not_isInnerAut_inducedAutHom_iff Lf e (hAN hxA)).mpr hxout
  have hcommR : ∀ β ∈ ρ.range, ∀ γ ∈ ρ.range, β * γ = γ * β := by
    rintro _ ⟨y, rfl⟩ _ ⟨y', rfl⟩
    rw [← map_mul, ← map_mul, hAc y y']
  have h3R : ∀ β ∈ ρ.range, β ^ 3 = 1 := by
    rintro _ ⟨y, rfl⟩
    rw [← map_pow, show y ^ 3 = 1 from Subtype.ext (by simpa using hAab.2 y y.2), map_one]
  obtain ⟨-, hK1⟩ := outer_image_eq_zpowers (m := 3) (by norm_num)
    (GaloisField.card 2 3 (by norm_num)) ρ.range h3R ⟨⟨x, hxA⟩, rfl⟩ hρx
  rw [hrangecard] at hK1
  set I := CFSG.ComponentClassification.OuterAutomorphisms.inner P with hI
  have hK1' : Nat.card ((QuotientGroup.mk' I).comp ρ.range.subtype).ker * 3 = 27 := hK1
  have hInn : Nat.card (ρ.range ⊓ I : Subgroup (MulAut P)) = 9 := by
    have hmap : ((QuotientGroup.mk' I).comp ρ.range.subtype).ker.map ρ.range.subtype =
        ρ.range ⊓ I := by
      ext β
      constructor
      · rintro ⟨β', hβ', rfl⟩
        refine ⟨β'.2, ?_⟩
        have h1 : QuotientGroup.mk' I (β' : MulAut P) = 1 := hβ'
        rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
      · rintro ⟨hβR, hβI⟩
        refine ⟨⟨β, hβR⟩, ?_, rfl⟩
        change QuotientGroup.mk' I β = 1
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        exact hβI
    rw [← hmap, Subgroup.card_map_of_injective ρ.range.subtype_injective]
    omega
  set H := I.comap ρ with hH
  have hBiff : ∀ y : A, (y : G) ∈ Lf ⊔ thetaQuotCentralizer Lf ↔ y ∈ H := by
    intro y
    rw [mem_sup_thetaQuotCentralizer_iff (hAN y.2)]
    change _ ↔ ρ y ∈ (MulAut.conj : P →* MulAut P).range
    rw [hρapply]
    exact (KFacts.isInnerAut_congr e _).symm
  have hB : sec8B A Lf = H.map A.subtype := by
    ext z
    constructor
    · rintro ⟨hzA, hz⟩
      exact ⟨⟨z, hzA⟩, (hBiff ⟨z, hzA⟩).mp hz, rfl⟩
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, (hBiff y).mpr hy⟩
  have hkerH : ρ.ker ≤ H := fun y hy => by
    change ρ y ∈ I
    rw [MonoidHom.mem_ker.mp hy]
    exact Subgroup.one_mem _
  have hHcard : Nat.card H = 27 := by
    rw [card_eq_card_ker_mul_card_map ρ H hkerH, hkercard, hH, Subgroup.map_comap_eq, hInn]
  have hBcard : Nat.card (sec8B A Lf) = 27 := by
    rw [hB, Subgroup.card_map_of_injective A.subtype_injective, hHcard]
  set Yb := ρ.range.comap (MulAut.conj : P →* MulAut P) with hYb
  have hYbcard : Nat.card Yb = 9 := by
    have h1 : Yb.map (MulAut.conj : P →* MulAut P) = ρ.range ⊓ I := by
      rw [hYb, Subgroup.map_comap_eq, inf_comm]
      rfl
    rw [← hInn, ← h1, Subgroup.card_map_of_injective hconjinj]
  have hYbfix : ∀ a : A, ∀ y ∈ Yb, ρ a y = y := by
    intro a y hy
    obtain ⟨d, hd⟩ := hy
    have hcomm : ρ a * ρ d = ρ d * ρ a := by rw [← map_mul, ← map_mul, hAc a d]
    have h1 : ρ a * MulAut.conj y * (ρ a)⁻¹ = MulAut.conj y := by
      rw [← hd, hcomm]
      group
    rw [KFacts.mul_mulAutConj_mul_inv] at h1
    exact hconjinj h1
  have hYbab : CFSG.Assembly.IsElemAbelian 3 Yb := by
    refine ⟨⟨⟨fun y y' => Subtype.ext (hconjinj ?_)⟩⟩, fun y hy => hconjinj ?_⟩
    · obtain ⟨d, hd⟩ := y.2
      obtain ⟨d', hd'⟩ := y'.2
      simp only [Subgroup.coe_mul, map_mul]
      rw [← hd, ← hd', ← map_mul, ← map_mul, hAc d d']
    · obtain ⟨d, hd⟩ := hy
      rw [map_pow, ← hd, ← map_pow, show d ^ 3 = 1 from Subtype.ext (by simpa using hAab.2 d d.2),
        map_one, map_one]
  set Y' := Yb.map e.symm.toMonoidHom with hY'
  have hY'ab : CFSG.Assembly.IsElemAbelian 3 Y' := by
    refine ⟨⟨⟨fun y y' => Subtype.ext ?_⟩⟩, fun y hy => ?_⟩
    · obtain ⟨z, hz, hzy⟩ := y.2
      obtain ⟨z', hz', hzy'⟩ := y'.2
      simp only [Subgroup.coe_mul]
      rw [← hzy, ← hzy', ← map_mul, ← map_mul]
      exact congrArg _ (congrArg Subtype.val (hYbab.1.is_comm.comm ⟨z, hz⟩ ⟨z', hz'⟩))
    · obtain ⟨z, hz, rfl⟩ := hy
      rw [← map_pow, hYbab.2 z hz, map_one]
  have hY'fix : ∀ (a : G) (ha : a ∈ A), ∀ y ∈ Y',
      thetaQuotMulAut Lf (compAction Lf ⟨a, hAN ha⟩) y = y := by
    intro a ha y hy
    obtain ⟨z, hz, rfl⟩ := hy
    have h1 := hYbfix ⟨a, ha⟩ z hz
    rw [hρapply, MulAut.congr_apply] at h1
    apply e.injective
    change e (thetaQuotMulAut Lf (compAction Lf ⟨a, hAN ha⟩) (e.symm z)) = e (e.symm z)
    rw [MulEquiv.apply_symm_apply]
    exact h1
  have hY'card : Nat.card Y' = 9 := by
    rw [hY', Subgroup.card_map_of_injective e.symm.injective, hYbcard]
  obtain ⟨S₀, hS₀A, hS₀Y, hdisj⟩ := exists_le_of_fixed hAab hAmax hAN hY'ab hY'fix
  have hqinj : ∀ s ∈ S₀, ∀ t ∈ S₀, QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) s =
      QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) t → s = t := by
    intro s hs t ht hst
    have h1 : t⁻¹ * s ∈ aschbacherSolvableCore 3 Lf := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hst
      have := (aschbacherSolvableCore 3 Lf).inv_mem hst
      rwa [mul_inv_rev, inv_inv] at this
    have h2 : t⁻¹ * s ∈ S₀ ⊓ aschbacherSolvableCore 3 Lf :=
      ⟨S₀.mul_mem (S₀.inv_mem ht) hs, h1⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h2
    exact (eq_of_inv_mul_eq_one h2).symm
  have hS₀card : Nat.card S₀ = 9 := by
    rw [← hY'card, ← hS₀Y]
    refine le_antisymm ?_ ?_
    · refine Nat.card_le_card_of_injective
        (fun s : S₀ => (⟨QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) s,
          Subgroup.mem_map_of_mem _ s.2⟩ :
            S₀.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Lf)))) ?_
      intro s t hst
      exact Subtype.ext (hqinj s s.2 t t.2 (congrArg Subtype.val hst))
    · refine Nat.card_le_card_of_surjective
        (fun s : S₀ => (⟨QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) s,
          Subgroup.mem_map_of_mem _ s.2⟩ :
            S₀.map (QuotientGroup.mk' (aschbacherSolvableCore 3 Lf)))) ?_
      rintro ⟨_, s, hs, rfl⟩
      exact ⟨⟨s, hs⟩, rfl⟩
  refine ⟨S₀, hS₀A, hS₀card, hdisj, hS₀Y ▸ hY'ab, hS₀Y ▸ hY'card, ?_⟩
  set S' := S₀.map Lf.subtype with hS'
  have hS'card : Nat.card S' = 9 := by
    rw [hS', Subgroup.card_map_of_injective Lf.subtype_injective, hS₀card]
  have hS'B : S' ≤ sec8B A Lf := fun s hs =>
    ⟨hS₀A hs, Subgroup.mem_sup_left (Subgroup.map_subtype_le S₀ hs)⟩
  have hfB : Subgroup.zpowers f ≤ sec8B A Lf := by
    rw [Subgroup.zpowers_le]
    refine ⟨hfA, (hBiff ⟨f, hfA⟩).mpr ?_⟩
    exact hkerH (MonoidHom.mem_ker.mpr hfker)
  have hcommfS : ∀ z ∈ Subgroup.zpowers f, ∀ s ∈ S', z * s = s * z := by
    intro z hz s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    have hzA : f ^ k ∈ A := A.zpow_mem hfA k
    exact congrArg Subtype.val (hAc ⟨f ^ k, hzA⟩ ⟨s, hS₀A hs⟩)
  have hinf : Subgroup.zpowers f ⊓ S' = ⊥ := by
    rw [eq_bot_iff]
    rintro z ⟨hzf, hzS⟩
    obtain ⟨z₀, hz₀, rfl⟩ := hzS
    have hcen : QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) z₀ ∈
        Subgroup.center (Lf ⧸ aschbacherSolvableCore 3 Lf) := by
      rw [Subgroup.mem_center_iff]
      intro w
      induction w using QuotientGroup.induction_on with
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
    have hZL : Subgroup.center (Lf ⧸ aschbacherSolvableCore 3 Lf) = ⊥ :=
      center_eq_bot_of_mulEquiv e hZ
    rw [hZL, Subgroup.mem_bot, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hcen
    have h2 : z₀ ∈ S₀ ⊓ aschbacherSolvableCore 3 Lf := ⟨hz₀, hcen⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h2
    rw [h2]
    exact Subgroup.one_mem _
  have hfo' : orderOf f = 3 := by
    have := hfo
    rwa [Subgroup.orderOf_mk] at this
  obtain ⟨hcard, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommfS
  rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, hfo', hS'card] at hcard
  exact (Subgroup.eq_of_le_of_card_ge (sup_le hfB hS'B) (by rw [hBcard, hcard])).symm

theorem mem_normalizer_inf_centralizer {G : Type} [Group G] {L : Subgroup G} {d y : G}
    (hd : d ∈ Subgroup.normalizer (L : Set G)) (hdy : d * y = y * d) :
    d ∈ Subgroup.normalizer ((L ⊓ Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) := by
  have hdC : d ∈ Subgroup.normalizer
      ((Subgroup.centralizer ({y} : Set G) : Subgroup G) : Set G) :=
    Subgroup.le_normalizer (Subgroup.mem_centralizer_singleton_iff.mpr hdy)
  rw [Subgroup.mem_normalizer_iff] at hd hdC ⊢
  intro z
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hd z, hdC z]

end Item812Res2

section SU

@[expose] def Pair811GenSU : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G) (a b : G)
    (X : Subgroup G) (n : ℕ), Sec8Pair G A c L a b X n →
    Nonempty (X ⧸ aschbacherSolvableCore 3 X ≃* projSp 2 (GaloisField 2 3)) →
    ∀ (e : G) (Le : Subgroup G), PairRel A e Le b X → PairRel A b X e Le →
      IsUnitaryTwo (Le ⧸ aschbacherSolvableCore 3 Le) 3 →
        sec8B A Le = Subgroup.closure {e, b} ⊔
          (A ⊓ inSubgroup perfectResidual (Le ⊓ Subgroup.centralizer ({b} : Set G)))

theorem exists_inducesOuterTheta_of_mem_pairOmega {G : Type} [Group G] [Finite G]
    {A : Subgroup G} {f : G} {Lf : Subgroup G} (h : (f, Lf) ∈ pairOmega A) :
    ∃ x ∈ A, InducesOuterTheta x Lf := by
  obtain ⟨x, hxA, hxk⟩ := h.2.2.2.1
  refine ⟨x, hxA, ?_⟩
  rcases hxk with h' | h'
  · exact KFacts.InducesStdKind.inducesOuterTheta Lf h' (by decide)
  · exact KFacts.InducesStdKind.inducesOuterTheta Lf h' (by decide)

end SU

section Final

open Item812Res2 in
theorem sec8B_eq_of_projSp {G : Type} [Group G] [Finite G] (h3 : localRank 3 G ≤ 3)
    {A : Subgroup G} (hAF : A ∈ partTwoF G) (hA81 : Nat.card A = 81) {f : G} (hfA : f ∈ A)
    (hf1 : f ≠ 1) {Lf : Subgroup G} (hLf : Lf ∈ thetaComponentsAt 3 f)
    (hX : Nonempty (Lf ⧸ aschbacherSolvableCore 3 Lf ≃* projSp 2 (GaloisField 2 3)))
    {x : G} (hxA : x ∈ A) (hxout : InducesOuterTheta x Lf) {g : G}
    (hg : g ∈ gammaSet A Lf) :
    sec8B A Lf = Subgroup.closure {f, g} ⊔
      (A ⊓ inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer ({g} : Set G))) := by
  classical
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨S₀, hS₀A, hS₀card, hdisj, hEab, hEcard, hBeq⟩ :=
    sec8B_structure_of_projSp h3 hAF hA81 hfA hf1 hLf hX hxA hxout
  have hAab := hAF.1
  have hAc : ∀ y ∈ A, ∀ y' ∈ A, y * y' = y' * y := fun y hy y' hy' =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨y, hy⟩ ⟨y', hy'⟩)
  have hAN := le_normalizer_of_projSp h3 hAab hfA hf1 hLf hX
  obtain ⟨-, -, hN3, -⟩ := solvable_prime_complement_core_characterization (H := Lf)
    Nat.prime_three
  set q := QuotientGroup.mk' (aschbacherSolvableCore 3 Lf) with hq
  set S' := S₀.map Lf.subtype with hS'
  have hS'card : Nat.card S' = 9 := by
    rw [hS', Subgroup.card_map_of_injective Lf.subtype_injective, hS₀card]
  have hqinj : ∀ s ∈ S₀, ∀ t ∈ S₀, q s = q t → s = t := by
    intro s hs t ht hst
    have h1 : t⁻¹ * s ∈ aschbacherSolvableCore 3 Lf := by
      rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hst
      have := (aschbacherSolvableCore 3 Lf).inv_mem hst
      rwa [mul_inv_rev, inv_inv] at this
    have h2 : t⁻¹ * s ∈ S₀ ⊓ aschbacherSolvableCore 3 Lf :=
      ⟨S₀.mul_mem (S₀.inv_mem ht) hs, h1⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h2
    exact (eq_of_inv_mul_eq_one h2).symm
  obtain ⟨m, hgm⟩ := hg
  have hgA : g ∈ A := hgm.1
  have hg3 : g ^ 3 = 1 := hAab.2 g hgA
  have hgB : g ∈ sec8B A Lf := by
    refine ⟨hgA, ?_⟩
    show g ∈ Lf ⊔ thetaQuotCentralizer Lf
    rw [mem_sup_thetaQuotCentralizer_iff (hAN hgA)]
    by_contra hout
    have hgout : InducesOuterTheta g Lf := ⟨hAN hgA, hout⟩
    have hX' : Nonempty (Lf ⧸ aschbacherSolvableCore 3 Lf ≃*
        projSp 2 (GaloisField 2 (3 * 1))) := by simpa using hX
    obtain ⟨-, ⟨ι⟩⟩ := KFacts.barCentralizer_mulEquiv_projSp one_ne_zero hg3 hgout hX'
    have hC720 : Nat.card (barCentralizer (Subgroup.zpowers g) Lf) = 720 := by
      rw [Nat.card_congr ι.toEquiv, card_projSp_two_one]
    have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq (hAN hgA)
      ⟨1, by simpa using hg3⟩
    have hdvd : Nat.card (imageModTheta Lf
        (inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer {g}))) ∣ 720 := by
      rw [himg, ← hC720]
      exact Subgroup.card_dvd_of_le (Subgroup.map_subtype_le _)
    rcases hgm.2.2.2 with ⟨k, hk, -, hRee, -⟩ | ⟨-, ⟨hL2⟩⟩
    · exact not_nonempty_reeF4_of_projSp hX k hk hRee
    · rw [Nat.card_congr hL2.toEquiv, card_projSL_two (by have := hgm.2.2.1; omega)] at hdvd
      exact not_dvd_seven_twenty hgm.2.2.1 hdvd
  have hcommfS : ∀ z ∈ Subgroup.zpowers f, ∀ s ∈ S', z * s = s * z := by
    intro z hz s hs
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
    exact hAc _ (A.zpow_mem hfA k) _ (hS₀A hs)
  obtain ⟨-, hset⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommfS
  have hgdec : g ∈ ((Subgroup.zpowers f ⊔ S' : Subgroup G) : Set G) := by
    rw [← hBeq]
    exact hgB
  rw [hset] at hgdec
  obtain ⟨z, hz, y, hyS, hzy⟩ := hgdec
  obtain ⟨i, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
  have hfB : Subgroup.zpowers f ≤ sec8B A Lf := hBeq ▸ le_sup_left
  set K := inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer ({g} : Set G)) with hK
  have hKL : K ≤ Lf :=
    (Subgroup.map_subtype_le _).trans (inf_le_left : Lf ⊓ Subgroup.centralizer {g} ≤ Lf)
  have hyLf : y ∈ Lf := Subgroup.map_subtype_le S₀ hyS
  have hLC : Lf ⊓ Subgroup.centralizer ({g} : Set G) =
      Lf ⊓ Subgroup.centralizer ({y} : Set G) := by
    ext l
    simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
    constructor
    · rintro ⟨hl, hlg⟩
      refine ⟨hl, ?_⟩
      have hlf : l * f = f * l := Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_mem_thetaComponentsAt_three hLf hl)
      have hlfi : l * f ^ i = f ^ i * l := (Commute.zpow_right (show Commute l f from hlf) i).eq
      rw [← hzy] at hlg
      calc l * y = (f ^ i)⁻¹ * (f ^ i * (l * y)) := by group
        _ = (f ^ i)⁻¹ * ((l * f ^ i) * y) := by rw [hlfi]; group
        _ = (f ^ i)⁻¹ * (l * (f ^ i * y)) := by group
        _ = (f ^ i)⁻¹ * (f ^ i * y * l) := by rw [hlg]
        _ = y * l := by group
    · rintro ⟨hl, hly⟩
      refine ⟨hl, ?_⟩
      have hlf : l * f = f * l := Subgroup.mem_centralizer_singleton_iff.mp
        (le_centralizer_of_mem_thetaComponentsAt_three hLf hl)
      have hlfi : l * f ^ i = f ^ i * l := (Commute.zpow_right (show Commute l f from hlf) i).eq
      rw [← hzy]
      calc l * (f ^ i * y) = f ^ i * (l * y) := by rw [← mul_assoc, hlfi, mul_assoc]
        _ = f ^ i * (y * l) := by rw [hly]
        _ = f ^ i * y * l := by group
  apply le_antisymm
  ·
    rw [hBeq]
    have hfcl : f ∈ Subgroup.closure ({f, g} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert _ _)
    have hgcl : g ∈ Subgroup.closure ({f, g} : Set G) :=
      Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)
    refine sup_le ((Subgroup.zpowers_le).mpr (Subgroup.mem_sup_left hfcl)) ?_
    have hycl : y ∈ Subgroup.closure ({f, g} : Set G) := by
      have h1 := Subgroup.mul_mem _ (Subgroup.inv_mem _ (Subgroup.zpow_mem _ hfcl i)) hgcl
      have h2 : (f ^ i)⁻¹ * g = y := by rw [← hzy]; group
      rwa [h2] at h1
    by_cases hy1 : y = 1
    ·
      have hKeq : K = Lf := by
        rw [hK, hLC, hy1]
        have hLC1 : Lf ⊓ Subgroup.centralizer ({1} : Set G) = Lf := by
          rw [inf_eq_left]
          intro l _
          exact Subgroup.mem_centralizer_singleton_iff.mpr (by group)
        rw [hLC1]
        exact CFSG.RankThree.inSubgroup_perfectResidual_of_isPerfect
          (CFSG.RankThree.PartOne.isPerfect_of_mem_thetaComponentsAt hLf)
      intro s hs
      refine Subgroup.mem_sup_right ⟨hS₀A hs, ?_⟩
      rw [hKeq]
      exact Subgroup.map_subtype_le S₀ hs
    ·
      obtain ⟨y₀, hy₀, rfl⟩ := hyS
      set yb := q y₀ with hyb
      have hyb1 : yb ≠ 1 := by
        intro h
        apply hy1
        have := hqinj y₀ hy₀ 1 S₀.one_mem (by rw [← hyb, h, map_one])
        rw [this]
        rfl
      have hybE : yb ∈ S₀.map q := ⟨y₀, hy₀, rfl⟩
      have hyb3 : yb ^ 3 = 1 := hEab.2 _ hybE
      have hEC : S₀.map q ≤ Subgroup.centralizer {yb} := by
        intro w hw
        rw [Subgroup.mem_centralizer_singleton_iff]
        exact congrArg Subtype.val (hEab.1.is_comm.comm ⟨w, hw⟩ ⟨yb, hybE⟩)
      set ψ : StatedSp 2 (GaloisField 2 3) ≃* (Lf ⧸ aschbacherSolvableCore 3 Lf) :=
        (KFacts.statedSpEquivProjSpOfCharTwo _).trans hX.some.symm with hψ
      have hF4 : 4 ≤ Nat.card (GaloisField 2 3) := by
        rw [GaloisField.card 2 3 (by norm_num)]
        norm_num
      have hcard3 := KFacts.card_inf_perfectResidual_eq_three hF4 ψ hyb3 hyb1 hEC hEab.2 hEcard
        hybE
      have hne : (S₀.map q ⊓ inSubgroup perfectResidual (Subgroup.centralizer {yb}) :
          Subgroup (Lf ⧸ aschbacherSolvableCore 3 Lf)) ≠ ⊥ := by
        intro hbot
        rw [hbot, Subgroup.card_bot] at hcard3
        omega
      obtain ⟨⟨db, hdbmem⟩, hdb1⟩ := (Subgroup.ne_bot_iff_exists_ne_one).mp hne
      have hdb1' : db ≠ 1 := fun h => hdb1 (Subtype.ext h)
      have hdbC := hdbmem.2
      obtain ⟨d₀, hd₀, hd₀q⟩ := hdbmem.1
      have hdby : db ∉ Subgroup.zpowers yb := by
        intro hmem
        have hdb3 : db ^ 3 = 1 := hEab.2 _ hdbmem.1
        have hord : orderOf db = 3 := orderOf_eq_prime hdb3 hdb1'
        have hordy : orderOf yb = 3 := orderOf_eq_prime hyb3 hyb1
        have heq : Subgroup.zpowers db = Subgroup.zpowers yb :=
          Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).mpr hmem)
            (by rw [Nat.card_zpowers, Nat.card_zpowers, hord, hordy])
        have hyC : yb ∈ inSubgroup perfectResidual (Subgroup.centralizer {yb}) := by
          have : yb ∈ Subgroup.zpowers db := heq ▸ Subgroup.mem_zpowers yb
          exact (Subgroup.zpowers_le.mpr hdbC) this
        exact KFacts.not_mem_perfectResidual_centralizer hF4 ψ hyb3 hyb1 hyC
      have hyA : (y₀ : G) ∈ A := hS₀A ⟨y₀, hy₀, rfl⟩
      have hdA : (d₀ : G) ∈ A := hS₀A ⟨d₀, hd₀, rfl⟩
      have hbar := barCentralizer_zpowers_eq_centralizer y₀.2
      have himg := KFacts.imageModTheta_perfectResidual_centralizer_eq (hAN hyA)
        ⟨1, by simpa using hAab.2 _ hyA⟩
      have hdbimg : db ∈ imageModTheta Lf
          (inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer {(y₀ : G)})) := by
        rw [himg, hbar]
        exact hdbC
      obtain ⟨k₀, hk₀, hk₀q⟩ := hdbimg
      have ht₀ : k₀⁻¹ * d₀ ∈ aschbacherSolvableCore 3 Lf := by
        have h1 : q k₀ = q d₀ := hk₀q.trans hd₀q.symm
        rw [hq, QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h1
        exact h1
      have htcop : Nat.Coprime (orderOf ((k₀⁻¹ * d₀ : Lf) : G)) 3 := by
        rw [Subgroup.orderOf_coe]
        have hdvd := Subgroup.orderOf_dvd_natCard _ ht₀
        exact Nat.Coprime.coprime_dvd_left hdvd
          (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN3))
      have hdN : (d₀ : G) ∈ Subgroup.normalizer
          (inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer {(y₀ : G)}) : Set G) :=
        mem_normalizer_inSubgroup_perfectResidual
          (mem_normalizer_inf_centralizer (hAN hdA) (hAc _ hdA _ hyA))
      have hd3 : (d₀ : G) ^ 3 = 1 := hAab.2 _ hdA
      have hdK : (d₀ : G) ∈ inSubgroup perfectResidual (Lf ⊓ Subgroup.centralizer {(y₀ : G)}) :=
        mem_of_mul_mem_of_coprime hd3 hdN (Subgroup.mem_subgroupOf.mp hk₀)
          (by simp only [Subgroup.coe_mul, Subgroup.coe_inv]; group) htcop
      have hdy : (d₀ : G) ∉ Subgroup.zpowers (y₀ : G) := by
        rintro ⟨j, hj⟩
        apply hdby
        refine ⟨j, ?_⟩
        have hj' : y₀ ^ j = d₀ := Subtype.ext (by simpa using hj)
        show yb ^ j = db
        rw [hyb, ← map_zpow, hj', hd₀q]
      have hord3 : ∀ w ∈ A, w ≠ 1 → orderOf w = 3 := fun w hw hw1 =>
        orderOf_eq_prime (hAab.2 w hw) hw1
      have hd1 : (d₀ : G) ≠ 1 := fun h => hdy (h ▸ Subgroup.one_mem _)
      have hy1' : (y₀ : G) ≠ 1 := hy1
      have hinf : Subgroup.zpowers (y₀ : G) ⊓ Subgroup.zpowers (d₀ : G) = ⊥ := by
        have hcard : Nat.card (Subgroup.zpowers (d₀ : G)) = 3 := by
          rw [Nat.card_zpowers, hord3 _ hdA hd1]
        have : Fact (Nat.card (Subgroup.zpowers (d₀ : G))).Prime := ⟨by rw [hcard]; norm_num⟩
        rcases Subgroup.eq_bot_or_eq_top_of_prime_card ((Subgroup.zpowers (y₀ : G) ⊓
            Subgroup.zpowers (d₀ : G)).subgroupOf (Subgroup.zpowers (d₀ : G))) with h | h
        · rw [Subgroup.subgroupOf_eq_bot] at h
          have h' := disjoint_iff.1 h
          rwa [inf_assoc, inf_idem] at h'
        · exfalso
          have hmem : (⟨(d₀ : G), Subgroup.mem_zpowers _⟩ : Subgroup.zpowers (d₀ : G)) ∈
              (Subgroup.zpowers (y₀ : G) ⊓ Subgroup.zpowers (d₀ : G)).subgroupOf
                (Subgroup.zpowers (d₀ : G)) := by
            rw [h]
            exact Subgroup.mem_top _
          exact hdy (Subgroup.mem_subgroupOf.1 hmem).1
      have hcommyd : ∀ u ∈ Subgroup.zpowers (y₀ : G), ∀ v ∈ Subgroup.zpowers (d₀ : G),
          u * v = v * u := by
        intro u hu v hv
        exact hAc u ((Subgroup.zpowers_le (H := A)).mpr hyA hu) v
          ((Subgroup.zpowers_le (H := A)).mpr hdA hv)
      obtain ⟨hcardyd, -⟩ := CFSG.GroupTheory.card_sup_mul_card_inf_of_commute _ _ hcommyd
      rw [hinf, Subgroup.card_bot, mul_one, Nat.card_zpowers, Nat.card_zpowers,
        hord3 _ hyA hy1', hord3 _ hdA hd1] at hcardyd
      have hydS : Subgroup.zpowers (y₀ : G) ⊔ Subgroup.zpowers (d₀ : G) ≤ S' :=
        sup_le ((Subgroup.zpowers_le).mpr ⟨y₀, hy₀, rfl⟩)
          ((Subgroup.zpowers_le).mpr ⟨d₀, hd₀, rfl⟩)
      have hSeq : Subgroup.zpowers (y₀ : G) ⊔ Subgroup.zpowers (d₀ : G) = S' :=
        Subgroup.eq_of_le_of_card_ge hydS (by rw [hS'card, hcardyd])
      rw [← hSeq]
      refine sup_le ((Subgroup.zpowers_le).mpr (Subgroup.mem_sup_left hycl))
        ((Subgroup.zpowers_le).mpr (Subgroup.mem_sup_right ⟨hdA, ?_⟩))
      rw [hK, hLC]
      exact hdK
  ·
    refine sup_le ?_ ?_
    · rw [Subgroup.closure_le]
      intro w hw
      rcases hw with rfl | rfl
      · exact hfB (Subgroup.mem_zpowers _)
      · exact hgB
    · rintro w ⟨hwA, hwK⟩
      exact ⟨hwA, Subgroup.mem_sup_left (hKL hwK)⟩

theorem pair811Gen_of (hSU : Pair811GenSU) : Pair811Gen := by
  intro G _ _ A c L a b X n h hX e Le hrel hrel' hLe
  have h3 := h.toTheoremFourHyp.localRank_three.le
  obtain ⟨x, hxA, hxout⟩ := exists_inducesOuterTheta_of_mem_pairOmega h.mem_pairOmega
  refine ⟨sec8B_eq_of_projSp h3 h.mem_partTwoF h.card_eq h.mem_pairOmega.1 h.mem_pairOmega.2.1
    h.mem_pairOmega.2.2.1 hX hxA hxout hrel'.2.1, ?_⟩
  rcases hLe with hU | hSp
  · exact hSU G A c L a b X n h hX e Le hrel hrel' hU
  · obtain ⟨x', hx'A, hx'out⟩ := exists_inducesOuterTheta_of_mem_pairOmega hrel.1
    exact sec8B_eq_of_projSp h3 h.mem_partTwoF h.card_eq hrel.1.1 hrel.1.2.1 hrel.1.2.2.1 hSp
      hx'A hx'out hrel.2.1

end Final

end CFSG.RankThree.PartTwo.Sec8

module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFacts3ProofPairNL
import CFSG.RankThree.PartTwo.Sec8.Item812Res7ProofD4N
import CFSG.RankThree.PartTwo.Sec8.Item812Res11ProofOmegaG2
import CFSG.RankThree.PartTwo.Sec8.Item8KFacts2ProofRee
import CFSG.RankThree.PartTwo.Sec21.LangTwisted2ProofD4
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofACent
import CFSG.RankThree.PartTwo.Sec11.KS11Lie6ProofBCent
import CFSG.RankThree.PartTwo.Sec11.KS11Lie4ProofTwist

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8KFacts3

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec8.Item83Proof CFSG.RankThree.PartTwo.Sec8.Item86ResProof
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut inducedAutHom)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley

section KFacts


@[expose] def KF84G2E9 : Prop :=
  ∀ (K : Type) [Field K] [Finite K], ringChar K = 2 → 4 ≤ Nat.card K →
    ∀ u v : adjointGroup .G2 K, u ^ 3 = 1 → v ^ 3 = 1 → u * v = v * u → u ≠ 1 →
      v ∉ Subgroup.zpowers u →
        ∃ z ∈ Subgroup.closure ({u, v} : Set (adjointGroup .G2 K)), z ≠ 1 ∧
          ∀ g : adjointGroup .G2 K, g * z * g⁻¹ ∉ Sec11.KS11Lie4Proof.g2ShortSL2 K

@[expose] def KF84D4OuterSU3 : Prop :=
  ∀ (m : ℕ) (K : Type) [Field K] [Finite K] (σ : K ≃+* K), Nat.card K = (2 ^ m) ^ 3 →
    (∀ c, σ c = c ^ 2 ^ m) →
    ∀ τ : MulAut (graphFixedRootGroup TwistTag.D4 K σ.toRingHom), τ ^ 3 = 1 → ¬ IsInnerAut τ →
    ∀ w ∈ Sec11.KS11Lie4Proof.d4ShortSL2 K σ.toRingHom, w ^ 3 = 1 → w ≠ 1 → τ w = w →
      (∀ x ∈ inSubgroup perfectResidual
          (Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
        τ x = x) ∨
      ∀ x ∈ inSubgroup perfectResidual
          (Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 K σ.toRingHom))),
        τ x = x → (∃ e : ℕ, x ^ 2 ^ e = 1) → x ^ 2 = 1

end KFacts

section Tools

variable {G : Type} [Group G] [Finite G]

theorem mem_centralizer_iff_conj_apply {M₀ : Type*} [Group M₀] (w z : M₀) :
    z ∈ Subgroup.centralizer ({w} : Set M₀) ↔ MulAut.conj w z = z := by
  rw [MulAut.conj_apply, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · intro h
    rw [← h, mul_assoc, mul_inv_cancel, mul_one]
  · intro h
    calc z * w = w * z * w⁻¹ * w := by rw [h]
      _ = w * z := by group

theorem map_residual_eq_of_conj {X : Subgroup G} {M₀ : Type*} [Group M₀]
    (E : X ⧸ aschbacherSolvableCore 3 X ≃* M₀) {c : G}
    (hcN : c ∈ Subgroup.normalizer (X : Set G)) (hc3 : c ^ 3 = 1) {w : M₀}
    (hw : MulAut.conj w = inducedAutHom X E ⟨c, hcN⟩) :
    (imageModTheta X (inSubgroup perfectResidual
      (X ⊓ Subgroup.centralizer ({c} : Set G)))).map E.toMonoidHom =
      inSubgroup perfectResidual (Subgroup.centralizer ({w} : Set M₀)) := by
  rw [KFacts.imageModTheta_perfectResidual_centralizer_eq hcN ⟨1, by rw [pow_one]; exact hc3⟩,
    KFacts.map_inSubgroup_perfectResidual,
    KFacts.map_barCentralizer_eq hcN E _ fun z => by
      rw [← hw]
      exact mem_centralizer_iff_conj_apply w z]

theorem inducedAutHom_apply_mk {X : Subgroup G} {M₀ : Type*} [Group M₀]
    (E : X ⧸ aschbacherSolvableCore 3 X ≃* M₀) {x : G}
    (hxN : x ∈ Subgroup.normalizer (X : Set G)) (κ : X) :
    inducedAutHom X E ⟨x, hxN⟩ (E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) κ)) =
      E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) (Sec4.compAction X ⟨x, hxN⟩ κ)) := by
  rw [KFacts.inducedAutHom_apply, MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.trans_apply,
    MulEquiv.symm_apply_apply, QuotientGroup.mk'_apply, Sec4.thetaQuotMulAut_mk]
  rfl

theorem exists_two_part {M N : Type*} [Monoid M] [Monoid N] [Finite M] (f : M →* N) (t : M)
    (h4 : f t ^ 4 = 1) (h2 : f t ^ 2 ≠ 1) (ht : IsOfFinOrder t) :
    ∃ o : ℕ, Odd o ∧ (∃ e : ℕ, (t ^ o) ^ 2 ^ e = 1) ∧ f (t ^ o) ^ 2 ≠ 1 := by
  obtain ⟨e, o, ho, hto⟩ := Nat.exists_eq_two_pow_mul_odd ht.orderOf_pos.ne'
  refine ⟨o, ho, ⟨e, ?_⟩, ?_⟩
  · rw [← pow_mul, mul_comm, ← hto, pow_orderOf_eq_one]
  · obtain ⟨j, rfl⟩ := ho
    rw [map_pow, ← pow_mul, show (2 * j + 1) * 2 = 4 * j + 2 by ring, pow_add, pow_mul, h4,
      one_pow, one_mul]
    exact h2

end Tools

section Ree


variable {G : Type} [Group G] [Finite G]

theorem exists_moved_fixed_of_ree {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    (h : Sec8Std G A c L a d n)
    (hRL : IsoReeF4 (L ⧸ aschbacherSolvableCore 3 L) (3 * n))
    (hKSU : IsoSUThree (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G)))) (2 ^ (3 * n))) :
    (∃ κ ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)),
        κ⁻¹ * (a * κ * a⁻¹) ∉ (aschbacherSolvableCore 3 L).map L.subtype) ∧
      ∃ t ∈ inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)),
        t * a = a * t ∧ (∃ e : ℕ, t ^ 2 ^ e = 1) ∧
          t ^ 2 ∉ (aschbacherSolvableCore 3 L).map L.subtype := by
  classical
  have hd := h.data83
  have hn1 : 1 ≤ n := hd.odd.pos
  obtain ⟨k, Kf, _, _, _, hkn, hKf, ⟨e⟩⟩ := hRL
  have hk : 1 ≤ k := by omega
  have hKf' : Nat.card Kf = 2 ^ (2 * k + 1) := by rw [hKf, hkn]
  have ha3 : a ^ 3 = 1 := h.mem_partTwoF.1.2 a h.a_mem
  have haL := h.a_mem_normalizer
  have hout : Sec4.InducesOuterTheta a L := by
    rcases h.inducesStdKind with hk' | hk'
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk' (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta L hk' (by decide)
  set α := Sec4.thetaQuotMulAut L (Sec4.compAction L ⟨a, haL⟩) with hαdef
  have hα3 : α ^ 3 = 1 := by
    rw [hαdef, ← map_pow, ← map_pow]
    have : (⟨a, haL⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := Subtype.ext (by simpa)
    rw [this, map_one, map_one]
  have hα1 : α ≠ 1 := by
    obtain ⟨hN, hnot⟩ := hout
    intro h1
    apply hnot
    rw [show (⟨a, hN⟩ : Subgroup.normalizer (L : Set G)) = ⟨a, haL⟩ from rfl, ← hαdef, h1]
    exact ⟨1, map_one _⟩
  obtain ⟨b, k', _, _, _, hk', ⟨φ₀⟩⟩ :=
    Item812Res2.exists_barCentralizer_mulEquiv_reeGamma hk hKf' e ha3 hout
  have hfixeq : barCentralizer (Subgroup.zpowers a) L = Sec4.autFix α :=
    Sec4.barCentralizer_zpowers_eq_autFix haL
  set φ : Sec4.autFix α ≃* CFSG.LieType.Ree.ReeTag.F4.reeGamma k' b :=
    (MulEquiv.subgroupCongr hfixeq.symm).trans φ₀ with hφ
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hKdef
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have haK : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_residual_of_data83 h.toHyp81 hd
  set S := imageModTheta L K with hS
  have hSinv : ∀ s ∈ S, α s ∈ S := by
    rintro _ ⟨x, hx, rfl⟩
    refine ⟨Sec4.compAction L ⟨a, haL⟩ x, ?_, rfl⟩
    have hx' : (x : G) ∈ K := Subgroup.mem_subgroupOf.mp hx
    show a * (x : G) * a⁻¹ ∈ K
    exact (Subgroup.mem_normalizer_iff.mp haK _).mp hx'
  obtain ⟨F, _, _, hF, ⟨ψ⟩⟩ := hKSU
  rw [← hkn] at hF ψ
  obtain ⟨⟨s, hsS, hsα⟩, u, huS, hαu, hu4, hu2⟩ :=
    Item8KFacts2Proof.exists_fixed_pow_four_of_ree hk hKf' e hα3 hα1 hk' φ hSinv hF ψ
  refine ⟨?_, ?_⟩
  ·
    obtain ⟨κ, hκ, rfl⟩ := hsS
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at hκ
    refine ⟨κ, hκ, fun hmem => hsα ?_⟩
    obtain ⟨w, hw, hwe⟩ := hmem
    rw [QuotientGroup.mk'_apply, hαdef, Sec4.thetaQuotMulAut_mk, QuotientGroup.eq]
    have e2 : (Sec4.compAction L ⟨a, haL⟩ κ)⁻¹ * κ = w⁻¹ := by
      apply Subtype.ext
      change (a * (κ : G) * a⁻¹)⁻¹ * κ = (w : G)⁻¹
      have hwe' : (w : G) = (κ : G)⁻¹ * (a * κ * a⁻¹) := hwe
      rw [hwe']
      group
    rw [e2]
    exact (aschbacherSolvableCore 3 L).inv_mem hw
  ·
    have hθS : NoThetaNormal S := Item87Proof.NoThetaNormal.of_mulEquiv ψ
      (Item87Proof.noThetaNormal_statedSU hF (by omega))
    obtain ⟨χ, hχ⟩ := Item8KFacts2Proof.exists_quotEquiv_imageModTheta hKL hθS
    set β := Sec4.thetaQuotMulAut K (Sec4.compAction K ⟨a, haK⟩) with hβdef
    have hequiv : ∀ y, (χ (β y) : L ⧸ aschbacherSolvableCore 3 L) = α (χ y) := by
      intro y
      induction y using QuotientGroup.induction_on with
      | H x =>
        rw [hβdef, Sec4.thetaQuotMulAut_mk, hχ, hχ, hαdef, Sec4.thetaQuotMulAut_mk]
        rfl
    set y := χ.symm ⟨u, huS⟩ with hy
    have hβy : β y = y := by
      apply χ.injective
      apply Subtype.ext
      rw [hequiv, hy, MulEquiv.apply_symm_apply]
      exact hαu
    have hymem : y ∈ barCentralizer (Subgroup.zpowers a) K :=
      (KFacts.mem_barCentralizer_zpowers_iff haK y).mpr hβy
    rw [← KFacts.imageModTheta_centralizer_eq haK ⟨1, by rw [pow_one]; exact ha3⟩] at hymem
    obtain ⟨t, ht, hty⟩ := hymem
    rw [SetLike.mem_coe, Subgroup.mem_subgroupOf] at ht
    have htu : ((Subgroup.inclusion hKL t : L) : L ⧸ aschbacherSolvableCore 3 L) = u := by
      rw [← hχ t]
      have h1 : (t : K ⧸ aschbacherSolvableCore 3 K) = y := hty
      rw [h1, hy, MulEquiv.apply_symm_apply]
    set f := QuotientGroup.mk' (aschbacherSolvableCore 3 L) with hf
    have hfu : f (Subgroup.inclusion hKL t) = u := htu
    obtain ⟨o, -, ⟨e₂, he₂⟩, ho2⟩ := exists_two_part f (Subgroup.inclusion hKL t)
      (by rw [hfu]; exact hu4) (by rw [hfu]; exact hu2) (isOfFinOrder_of_finite _)
    have hta : (t : G) * a = a * t :=
      Subgroup.mem_centralizer_singleton_iff.mp (Subgroup.mem_inf.mp ht).2
    refine ⟨(t : G) ^ o, K.pow_mem t.2 o, (Commute.pow_left hta o).eq, ⟨e₂, ?_⟩, ?_⟩
    · have h1 := congrArg (fun z : L => (z : G)) he₂
      simpa using h1
    · rintro ⟨w, hw, hwe⟩
      apply ho2
      have hw' : w = ((Subgroup.inclusion hKL t) ^ o) ^ 2 := Subtype.ext (by simpa using hwe)
      rw [← map_pow, ← hw', hf, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hw


theorem false_of_d4_short (hD4 : KF84D4OuterSU3) (h45 : Sec4.Item4_5) (h418 : Item418Theta)
    (hF : KF84FieldStd) {A : Subgroup G} {c : G} {L : Subgroup G} {a d : G} {n : ℕ}
    (h : Sec8Std G A c L a d n)
    (hRL : IsoReeF4 (L ⧸ aschbacherSolvableCore 3 L) (3 * n))
    (hKSU : IsoSUThree (imageModTheta L (inSubgroup perfectResidual
      (L ⊓ Subgroup.centralizer ({d} : Set G)))) (2 ^ (3 * n)))
    {b : G} (hb : b ∈ Subgroup.closure ({c, d} : Set G)) {X : Subgroup G}
    (hrel : PairRel A c L b X) {m : ℕ} {Kf : Type} [Field Kf] [Finite Kf] {σ : Kf ≃+* Kf}
    (hK : Nat.card Kf = (2 ^ m) ^ 3) (hσ : ∀ c, σ c = c ^ 2 ^ m)
    (E : X ⧸ aschbacherSolvableCore 3 X ≃* graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom)
    (hcN : c ∈ Subgroup.normalizer (X : Set G))
    {w : graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom}
    (hw : MulAut.conj w = inducedAutHom X E ⟨c, hcN⟩)
    (hwS : w ∈ Sec11.KS11Lie4Proof.d4ShortSL2 Kf σ.toRingHom) (hw3 : w ^ 3 = 1) (hw1 : w ≠ 1)
    (hq : IsQuasisimple (imageModTheta X
      (inSubgroup perfectResidual (X ⊓ Subgroup.centralizer ({c} : Set G))))) : False := by
  have hd := h.data83
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hAN := le_normalizer_of_partner h45 h hb hrel
  have haN := hAN h.a_mem
  have hc3 : c ^ 3 = 1 := hAe.2 c h.mem_A
  have ha3 : a ^ 3 = 1 := hAe.2 a h.a_mem
  obtain ⟨hkind, -⟩ := kinds_of_partner h418 hF h hb hrel
  have haout : Sec4.InducesOuterTheta a X := by
    rcases hkind with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  obtain ⟨-, -, hLb⟩ := partner_data h hb hrel
  have heq := residual_eq_of_isQuasisimple h hb hrel hq
  rw [hLb] at heq
  set K := inSubgroup perfectResidual (L ⊓ Subgroup.centralizer ({d} : Set G)) with hKdef
  have hKL : K ≤ L := (Item87Proof.residual_le _).trans inf_le_left
  have hKX : K ≤ X := by
    rw [heq]
    exact (Item87Proof.residual_le _).trans inf_le_left
  have hθ := theta_inf_le_theta_of_noThetaNormal hKL hKX (noThetaNormal_of_data83 hd)
  have haK : a ∈ Subgroup.normalizer (K : Set G) := mem_normalizer_residual_of_data83 h.toHyp81 hd
  obtain ⟨⟨κ, hκK, hκ⟩, t, htK, hta, ⟨e₂, he₂⟩, ht2⟩ := exists_moved_fixed_of_ree h hRL hKSU
  have hZ := exceptional_fixed_center_trivial TwistTag.D4 Kf σ
  have hinj := Item812Res7.conj_injective_of_center_trivial hZ
  set τ := inducedAutHom X E ⟨a, haN⟩ with hτdef
  have hτ3 : τ ^ 3 = 1 := KFacts.inducedAutHom_pow_eq_one X E haN ha3
  have hτin : ¬ IsInnerAut τ := (KFacts.not_isInnerAut_inducedAutHom_iff X E haN).mpr haout
  have hac' : (⟨a, haN⟩ : Subgroup.normalizer (X : Set G)) * ⟨c, hcN⟩ =
      ⟨c, hcN⟩ * ⟨a, haN⟩ := Subtype.ext (hcomm a h.a_mem c h.mem_A)
  have hττc : τ * MulAut.conj w = MulAut.conj w * τ := by
    have h1 := congrArg (inducedAutHom X E) hac'
    rw [map_mul, map_mul, ← hw] at h1
    exact h1
  have hτw : τ w = w := Item812Res7.apply_eq_of_commute_conj hinj hττc
  have hmap := map_residual_eq_of_conj E hcN hc3 hw
  have hP : ∀ z : X, (z : G) ∈ K →
      E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) z) ∈ inSubgroup perfectResidual
        (Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom))) := by
    intro z hz
    rw [← hmap]
    refine ⟨QuotientGroup.mk' (aschbacherSolvableCore 3 X) z, ?_, rfl⟩
    rw [← heq]
    exact ⟨z, Subgroup.mem_subgroupOf.mpr hz, rfl⟩
  rcases hD4 m Kf σ hK hσ τ hτ3 hτin w hwS hw3 hw1 hτw with hcent | h2
  ·
    apply hκ
    have hκX : κ ∈ X := hKX hκK
    have h1 := hcent _ (hP ⟨κ, hκX⟩ hκK)
    rw [hτdef, inducedAutHom_apply_mk] at h1
    have h2 := E.injective h1
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at h2
    have hmemX : κ⁻¹ * (a * κ * a⁻¹) ∈ (aschbacherSolvableCore 3 X).map X.subtype := by
      refine ⟨((Sec4.compAction X ⟨a, haN⟩ ⟨κ, hκX⟩)⁻¹ * ⟨κ, hκX⟩)⁻¹,
        (aschbacherSolvableCore 3 X).inv_mem h2, ?_⟩
      change ((a * κ * a⁻¹)⁻¹ * κ)⁻¹ = κ⁻¹ * (a * κ * a⁻¹)
      group
    exact hθ ⟨hmemX, K.mul_mem (K.inv_mem hκK) ((Subgroup.mem_normalizer_iff.mp haK κ).mp hκK)⟩
  ·
    have htX : t ∈ X := hKX htK
    have hfix : τ (E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨t, htX⟩)) =
        E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨t, htX⟩) := by
      rw [hτdef, inducedAutHom_apply_mk]
      congr 2
      apply Subtype.ext
      change a * t * a⁻¹ = t
      rw [← hta, mul_inv_cancel_right]
    have h2e : (E (QuotientGroup.mk' (aschbacherSolvableCore 3 X) ⟨t, htX⟩)) ^ 2 ^ e₂ = 1 := by
      rw [← map_pow, ← map_pow]
      have h1 : (⟨t, htX⟩ : X) ^ 2 ^ e₂ = 1 := Subtype.ext (by simpa using he₂)
      rw [h1, map_one, map_one]
    have hsq := h2 _ (hP ⟨t, htX⟩ htK) hfix ⟨e₂, h2e⟩
    apply ht2
    rw [← map_pow, ← map_pow, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff] at hsq
    have hmemX : t ^ 2 ∈ (aschbacherSolvableCore 3 X).map X.subtype := ⟨_, hsq, by simp⟩
    exact hθ ⟨hmemX, K.pow_mem htK 2⟩


theorem gammaSet_nonempty_of_g2 (hE9 : KF84G2E9) (hC : Sec11.KS11Lie4Proof.G2ThreeConjSL2Minus)
    (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hF : KF84FieldStd) (hKB : KF83KBarTwo)
    (hInd : KF83Indep) (hG2 : KF83IndepGTwo) {A : Subgroup G} {c : G} {L : Subgroup G}
    {a d : G} {n : ℕ} (h : Sec8Std G A c L a d n) {b : G}
    (hb : b ∈ Subgroup.closure ({c, d} : Set G)) {X : Subgroup G} (hrel : PairRel A c L b X)
    {m : ℕ} (hm1 : 1 ≤ m) {q : TauCeti.PrimePower} (hq2 : q.p = 2) (hqe : q.exponent = 3 * m)
    (hG : Sec4.IsoGTwo (X ⧸ aschbacherSolvableCore 3 X) q) : (gammaSet A X).Nonempty := by
  classical
  obtain ⟨Kf, _, _, hKc, ⟨E⟩⟩ := Item8KFactsProof.isoGTwoEven_of_isoGTwo hq2 hqe hG
  have hK2 : ringChar Kf = 2 := ringChar_eq_two_of_card hKc
  have hK3 : ringChar Kf ≠ 3 := by rw [hK2]; decide
  have hK4 : 4 ≤ Nat.card Kf := hKc ▸ four_le_two_pow (by omega)
  have : Finite (adjointGroup .G2 Kf) := Finite.of_equiv _ E.toEquiv
  have hZ : Subgroup.center (adjointGroup .G2 Kf) = ⊥ := center_adjointGroup_eq_bot
  have hinj := Item812Res7.conj_injective_of_center_trivial hZ
  have hd := h.data83
  have hAe := h.mem_partTwoF.1
  have hcomm : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have h3 : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hAN := le_normalizer_of_partner h45 h hb hrel
  set ρ : A →* MulAut (adjointGroup .G2 Kf) :=
    (inducedAutHom X E).comp (Subgroup.inclusion hAN) with hρ
  have hρapply : ∀ y : A, ρ y = inducedAutHom X E ⟨y, hAN y.2⟩ := fun y => rfl
  have hρ3 : ∀ y : A, ρ y ^ 3 = 1 := by
    intro y
    rw [← map_pow, show y ^ 3 = 1 from Subtype.ext (by simpa using h3 y y.2), map_one]
  have hsub := sectionCentralizer_subset_of_partner h45 hKB hG2 h hb hrel
  have hsec := Sec13.sectionCentralizer_eq_inf hAN
  have hker : ∀ y : A, ρ y = 1 → (y : G) ∈ Subgroup.zpowers b := by
    intro y hy
    apply hsub
    rw [hsec]
    refine ⟨y.2, ⟨y, hAN y.2⟩, MonoidHom.mem_ker.mpr ?_, rfl⟩
    apply (MulAut.congr E).injective
    rw [map_one]
    exact hy
  have hcN := hAN h.mem_A
  obtain ⟨hkind, hck⟩ := kinds_of_partner h418 hF h hb hrel
  have hne := Item812Res7.ne_one_of_partner h hb hrel hcN
  have hin_c : IsInnerAut (ρ ⟨c, h.mem_A⟩) := by
    by_contra hnot
    have hout : Sec4.InducesOuterTheta c X :=
      (KFacts.not_isInnerAut_inducedAutHom_iff X E hcN).mp hnot
    exact hck (Or.inl (KFacts.InducesStdKind.g2 Kf hK3 hK4
      (KFacts.inducesKindG2_field X hK3 hK4 (h3 c h.mem_A) hout E)))
  obtain ⟨w, hw⟩ := hin_c
  have hw3 : w ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hw, map_one]
    exact hρ3 _
  have hw1 : w ≠ 1 := by
    rintro rfl
    apply hne
    apply (MulAut.congr E).injective
    rw [map_one]
    exact (hw.symm.trans (map_one MulAut.conj)).symm.symm
  have haout : Sec4.InducesOuterTheta a X := by
    rcases hkind with hk | hk
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
    · exact KFacts.InducesStdKind.inducesOuterTheta X hk (by decide)
  have hαout : ¬ IsInnerAut (ρ ⟨a, h.a_mem⟩) :=
    (KFacts.not_isInnerAut_inducedAutHom_iff X E (hAN h.a_mem)).mpr haout
  set E₃ := Subgroup.closure ({c, a, d} : Set G) with hE₃
  have hE₃card : Nat.card E₃ = 27 := card_closure_of_sec8Std hInd h
  obtain ⟨x₀, hx₀A, hx₀E⟩ : ∃ x₀ ∈ A, x₀ ∉ E₃ := by
    by_contra hall
    push Not at hall
    have hle := Subgroup.card_le_of_le (show A ≤ E₃ from hall)
    rw [hE₃card, hd.card_eq] at hle
    omega
  have haE : a ∈ E₃ := Subgroup.subset_closure (by simp)
  have hcE : c ∈ E₃ := Subgroup.subset_closure (by simp)
  have hbE : b ∈ E₃ := Subgroup.closure_mono (by intro z hz; rcases hz with rfl | rfl <;> simp) hb
  obtain ⟨y, hyE, hyin⟩ : ∃ y : A, (y : G) ∉ E₃ ∧ IsInnerAut (ρ y) := by
    rcases Item812Res11.g2_trichotomy hK3 hK4 (hρ3 ⟨a, h.a_mem⟩) hαout (hρ3 ⟨x₀, hx₀A⟩) with
      h0 | h1 | h2
    · exact ⟨⟨x₀, hx₀A⟩, hx₀E, h0⟩
    · refine ⟨⟨x₀, hx₀A⟩ * ⟨a, h.a_mem⟩⁻¹, fun hmem => hx₀E ?_, by rwa [map_mul, map_inv]⟩
      have e1 : x₀ = (x₀ * a⁻¹) * a := by group
      rw [e1]
      exact E₃.mul_mem hmem haE
    · refine ⟨⟨x₀, hx₀A⟩ * ⟨a, h.a_mem⟩, fun hmem => hx₀E ?_, by rwa [map_mul]⟩
      have e1 : x₀ = (x₀ * a) * a⁻¹ := by group
      rw [e1]
      exact E₃.mul_mem hmem (E₃.inv_mem haE)
  obtain ⟨v, hv⟩ := hyin
  have hv3 : v ^ 3 = 1 := by
    apply hinj
    rw [map_pow, hv, map_one]
    exact hρ3 _
  have hwv : w * v = v * w := by
    apply hinj
    rw [map_mul, map_mul, hw, hv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (hcomm c h.mem_A y y.2)
  have hvw : v ∉ Subgroup.zpowers w := by
    rintro ⟨k, hk⟩
    apply hyE
    have h1 : ρ (y * ⟨c, h.mem_A⟩ ^ (-k)) = 1 := by
      rw [map_mul, map_zpow, ← hw, ← hv, ← hk, ← map_zpow, ← map_mul, ← zpow_add,
        add_neg_cancel, zpow_zero, map_one]
    obtain ⟨j, hj⟩ := hker _ h1
    have hj' : b ^ j = (y : G) * c ^ (-k) := by
      have hj2 : b ^ j = ((y * ⟨c, h.mem_A⟩ ^ (-k) : A) : G) := hj
      rw [hj2]
      simp
    have e1 : (y : G) = b ^ j * c ^ k := by
      rw [hj']
      group
    rw [e1]
    exact E₃.mul_mem (E₃.zpow_mem hbE j) (E₃.zpow_mem hcE k)
  obtain ⟨z, hz, hz1, hzS⟩ := hE9 Kf hK2 hK4 w v hw3 hv3 hwv hw1 hvw
  obtain ⟨i, j, -, -, rfl⟩ := KFacts.exists_pow_mul_pow_of_mem_closure_pair hwv hw3 hv3 hz
  set eA : A := ⟨c, h.mem_A⟩ ^ i * y ^ j with heA
  have hρe : ρ eA = MulAut.conj (w ^ i * v ^ j) := by
    rw [heA, map_mul, map_pow, map_pow, ← hw, ← hv, ← map_pow, ← map_pow, ← map_mul]
  have hz3 : (w ^ i * v ^ j) ^ 3 = 1 := by
    rw [(Commute.pow_pow hwv i j).mul_pow, ← pow_mul, ← pow_mul, mul_comm i 3, mul_comm j 3,
      pow_mul, pow_mul, hw3, hv3, one_pow, one_pow, one_mul]
  obtain ⟨g, hg⟩ := Sec11.KS11Lie4Proof.g2ThreeConjSL2_of_minus hC Kf hK3 hK4 _ hz3 hz1
  have hgM := hg.resolve_left (hzS g)
  set z' := g * (w ^ i * v ^ j) * g⁻¹ with hz'
  have hz'3 : z' ^ 3 = 1 := by
    rw [hz', ← MulAut.conj_apply, ← map_pow, hz3, map_one]
  have hz'1 : z' ≠ 1 := by
    rw [hz', ← MulAut.conj_apply]
    intro h1
    exact hz1 ((MulAut.conj g).injective (h1.trans (map_one _).symm))
  set E' := E.trans (MulAut.conj g) with hE'
  have heN : (eA : G) ∈ Subgroup.normalizer (X : Set G) := hAN eA.2
  have hcE' : inducedAutHom X E' ⟨eA, heN⟩ = MulAut.conj z' := by
    rw [hE', inducedAutHom_trans_conj, ← hρapply eA, hρe, KFacts.mul_mulAutConj_mul_inv,
      MulAut.conj_apply]
  have he3 : (eA : G) ^ 3 = 1 := h3 _ eA.2
  have hne_e : Sec4.thetaQuotMulAut X (Sec4.compAction X ⟨eA, heN⟩) ≠ 1 := by
    intro h1
    apply hz1
    apply hinj
    rw [← hρe, hρapply, KFacts.inducedAutHom_apply, h1, map_one, map_one]
  obtain ⟨w', hw', -, -, ⟨eW⟩⟩ := exists_conj_residual E' hZ heN he3 ⟨z', hcE'.symm⟩ hne_e
  have hw'z : w' = z' := hinj (hw'.trans hcE')
  obtain ⟨eS⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_g2ShortSL2 (K := Kf)
  obtain ⟨eP⟩ := residual_projSL_of_threeB (z := z')
    (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
      (Sec11.KS11Lie4Proof.g2Short_commute_g2Long hs hgM))
    (Sec11.KS11Lie4Proof.g2ThreeBCent_holds Kf hK3 hK4 z' hgM hz'3 hz'1).1 hKc (by omega) eS
  have hCeq : inSubgroup perfectResidual (Subgroup.centralizer ({w'} : Set
      (adjointGroup .G2 Kf))) = inSubgroup perfectResidual (Subgroup.centralizer ({z'} : Set
        (adjointGroup .G2 Kf))) := by rw [hw'z]
  have he1 : (eA : G) ≠ 1 := by
    intro h1
    apply hz1
    apply hinj
    rw [← hρe, show eA = 1 from Subtype.ext h1, map_one, map_one]
  exact ⟨eA, m, eA.2, he1, hm1, Or.inr ⟨Or.inr (Or.inl ⟨q, hq2, hqe, hG⟩),
    ⟨(eW.trans (MulEquiv.subgroupCongr hCeq)).trans eP⟩⟩⟩

end Ree

theorem pair84GammaRee_of (h45 : Sec4.Item4_5) (h418 : Item418Theta) (hL : Item82TwoList)
    (hC : Sec11.KS11Lie4Proof.G2ThreeConjSL2Minus) (hE9 : KF84G2E9) (hD4 : KF84D4OuterSU3)
    (hSp : KF84Sp4ThreeCent) : Pair84GammaRee := by
  intro G _ _ A c L a d n h hKSU b X hb hrel hXU
  have hR : KF84FieldReeStd := kF84FieldReeStd_holds
  have hO : KF84OuterL2 :=
    kF84OuterL2_of (inputs47ClassesD4_of_lang kF82D4LangCoset_holds kF82D4SecondCent_holds)
  have hF : KF84FieldStd := kF84FieldStd_of hO hR
  have hKB : KF83KBarTwo := kF83KBarTwo_of_even (kF83KBarEven_of hO hR)
  have hG2 : KF83IndepGTwo := kF83IndepGTwo_holds
  have hInd : KF83Indep := kF83Indep_of hG2
  have hd := h.data83
  have hn1 : 1 ≤ n := hd.odd.pos
  have hRL : IsoReeF4 (L ⧸ aschbacherSolvableCore 3 L) (3 * n) := by
    obtain ⟨-, x, hxc, hx1, hx3⟩ := isQuasisimple_central_of_isoSUThree hd.odd hKSU
    have hL2 : ∀ φ : imageModTheta L (inSubgroup perfectResidual
        (L ⊓ Subgroup.centralizer ({d} : Set G))) ≃* projSL 2 (GaloisField 2 (3 * n)), False := by
      intro φ
      have hZ := center_projSL_two_eq_bot (k := 3 * n) (by omega)
      have hφx : φ x ∈ Subgroup.center (projSL 2 (GaloisField 2 (3 * n))) := by
        rw [Subgroup.mem_center_iff]
        intro y
        rw [← MulEquiv.apply_symm_apply φ y, ← map_mul, ← map_mul, hxc]
      rw [hZ, Subgroup.mem_bot, MulEquiv.map_eq_one_iff] at hφx
      exact hx1 hφx
    rcases hd.cases with ⟨-, ⟨φ⟩, -⟩ | ⟨hR', -, -⟩ | ⟨-, -, ⟨φ⟩⟩ | ⟨-, -, ⟨φ⟩⟩ | ⟨-, -, ⟨φ⟩⟩
    · exact (hL2 φ).elim
    · exact hR'
    · exact (hL2 φ).elim
    · exact (hL2 φ).elim
    · exact (hL2 φ).elim
  have hcN := le_normalizer_of_partner h45 h hb hrel h.mem_A
  have hc3 : c ^ 3 = 1 := h.mem_partTwoF.1.2 c h.mem_A
  obtain ⟨-, hck⟩ := kinds_of_partner h418 hF h hb hrel
  have hne := Item812Res7.ne_one_of_partner h hb hrel hcN
  obtain ⟨m, hm, hD | ⟨q, hq2, hqe, hG⟩ | hRee | hSpX⟩ :=
    nonUnitary_cases (isList82Two_of_partner hL h45 h418 hF hKB hInd hG2 h hb hrel) hXU
  ·
    obtain ⟨hm1, Kf, _, _, σ, hKc, hσ, ⟨E⟩⟩ := Item812Res7.exists_trialityD4_model hD
    have hin : IsInnerAut (inducedAutHom X E ⟨c, hcN⟩) := by
      by_contra hnot
      have hout : Sec4.InducesOuterTheta c X :=
        (KFacts.not_isInnerAut_inducedAutHom_iff X E hcN).mp hnot
      exact hck (Or.inr (KFacts.InducesStdKind.triality m hm1 Kf hKc σ hσ
        (KFacts.inducesKindTriality_graphField hm1 hKc hσ X hc3 hout E)))
    have : Finite (graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom) := Finite.of_equiv _ E.toEquiv
    have hq3 : ¬ 3 ∣ 2 ^ m := fun h3 => by
      have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).mp
        (Nat.prime_three.dvd_of_dvd_pow h3)
      omega
    obtain ⟨E', w, hw, hw3, hw1, hP, ⟨eW⟩⟩ := exists_conj_residual_class E
      (exceptional_fixed_center_trivial TwistTag.D4 Kf σ) hcN hc3 hin hne
      (P := fun w => w ∈ Sec11.KS11Lie4Proof.d4ShortSL2 Kf σ.toRingHom ∨
        w ∈ Subgroup.centralizer ((Sec11.KS11Lie4Proof.d4ShortSL2 Kf σ.toRingHom : Subgroup
          (graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom)) :
            Set (graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom)))
      (fun w hw3 hw1 => Sec11.KS11Lie6Proof.d4ThreeConj_holds Kf (2 ^ m) σ hKc hσ hq3 w hw3 hw1)
    rcases hP with hS | hCS
    ·
      exfalso
      rcases Sec11.KS11Lie6Proof.d4ThreeACent_holds Kf (2 ^ m) σ hKc hσ hq3 w hS hw3 hw1 with
        hsol | ⟨N, hNC, hcomm, hNq, -⟩
      · have hbot := Sec11.KS11Lie4Proof.eq_bot_of_isPerfect_of_isSolvable
          (Item87Proof.isPerfect_residual _)
          (Group.isSolvable_of_isSolvable_injective
            (f := Subgroup.inclusion (Item87Proof.residual_le
              (Subgroup.centralizer ({w} : Set (graphFixedRootGroup TwistTag.D4 Kf
                σ.toRingHom)))))
            (Subgroup.inclusion_injective _))
        have hs : ∀ x : inSubgroup perfectResidual (Subgroup.centralizer
            ({w} : Set (graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom))), x = 1 := by
          intro x
          apply Subtype.ext
          have hx : (x : graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom) ∈
              (⊥ : Subgroup (graphFixedRootGroup TwistTag.D4 Kf σ.toRingHom)) := by
            rw [← hbot]
            exact x.2
          exact Subgroup.mem_bot.mp hx
        exact false_of_residual_subsingleton h hb hrel
          ⟨fun u v => eW.injective ((hs _).trans (hs _).symm)⟩
      · have hq := LocalCores.isQuasisimple_of_mulEquiv eW.symm
          (isQuasisimple_residual_of_le hNC hcomm hNq)
        exact false_of_d4_short hD4 h45 h418 hF h hRL hKSU hb hrel hKc hσ E' hcN hw hS hw3 hw1 hq
    ·
      obtain ⟨e⟩ := Sec11.KS11Lie4Proof.nonempty_mulEquiv_d4ShortSL2
        (ringEquiv_pow_three_eq_one hKc hσ)
      have : Finite (orbitField TwistTag.D4 Kf σ.toRingHom Sec11.KS11Lie4Proof.d4Outer) :=
        Subtype.finite
      have hF' : Nat.card (orbitField TwistTag.D4 Kf σ.toRingHom Sec11.KS11Lie4Proof.d4Outer) =
          2 ^ (3 * m) := by
        rw [Sec11.KS11Lie4Proof.natCard_orbitField_d4Outer (ringEquiv_pow_three_eq_one hKc hσ),
          hKc, ← pow_mul, mul_comm]
      obtain ⟨eP⟩ := residual_projSL_of_threeB
        (fun s hs => Subgroup.mem_centralizer_singleton_iff.mpr
          ((Subgroup.mem_centralizer_iff.mp hCS) s hs))
        (Sec11.KS11Lie6Proof.d4ThreeBCent_holds Kf (2 ^ m) σ hKc hσ hq3 w hCS hw3 hw1).1 hF'
        (by omega) e
      exact ⟨c, m, h.mem_A, h.ne_one, hm1, Or.inr ⟨Or.inl hD, ⟨eW.trans eP⟩⟩⟩
  ·
    exact gammaSet_nonempty_of_g2 hE9 hC h45 h418 hF hKB hInd hG2 h hb hrel hm.pos hq2 hqe hG
  ·
    obtain ⟨k, hk, hkm, he⟩ := hRee
    exact ⟨c, m, h.mem_A, h.ne_one, hm.pos, Or.inl ⟨k, hk, hkm, he,
      ree_residual hcN hc3 hck hne ⟨k, hk, hkm, he⟩⟩⟩
  ·
    obtain ⟨eSp⟩ := hSpX
    have hm1 : 1 ≤ m := hm.pos
    exact ⟨c, m, h.mem_A, h.ne_one, hm1, Or.inr ⟨Or.inr (Or.inr (Or.inr (Or.inr ⟨eSp⟩))),
      sp4_residual hSp hcN hc3 hck hne (f := 3 * m) (by omega) eSp⟩⟩

end CFSG.RankThree.PartTwo.Sec8.Item8KFacts3

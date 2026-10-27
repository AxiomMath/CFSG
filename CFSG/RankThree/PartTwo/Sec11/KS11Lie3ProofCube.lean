module

public import CFSG.RankThree.PartTwo.Sec11.KS11Lie2ProofExc
public import CFSG.RankThree.PartTwo.Sec11.Item1117StepsProofCube
import CFSG.RankThree.PartTwo.Sec11.KS11LieProofCore
import CFSG.RankThree.PartTwo.Sec11.SetUp1118ProofCarrier

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4

namespace KS11Lie3Proof

theorem false_of_normCentJ1117For {F : ∀ (X : Type) [Group X], Prop}
    (hN : NormCentJ1117For F) {Z : Type} [Group Z] [Finite Z]
    (hZ : ∃ (X : Type) (_ : Group X), F X ∧ Nonempty (Z ≃* _root_.commutator X))
    {α : MulAut Z} (hin : α ∈ (MulAut.conj : Z →* MulAut Z).range) {J : Subgroup Z}
    {y δ g : Z} (hα3 : α ^ 3 = 1) (hJ : J ∈ thetaComponentsIn (Item426.fixSub α))
    (hJT : IsType424 (J ⧸ aschbacherSolvableCore 3 J)) (hyJ : y ∈ J)
    (hyk : ∃ k : ℕ, y ^ 3 ^ k = 1) (hy3 : y ^ 3 ≠ 1) (hδy : δ ∈ Subgroup.zpowers y)
    (hgk : ∃ k : ℕ, g ^ 3 ^ k = 1) (hgy : g * y * g⁻¹ ∈ Subgroup.zpowers y)
    (hgα : MulAut.conj g * α * (MulAut.conj g)⁻¹ * α⁻¹ ∈
      Subgroup.zpowers (MulAut.conj δ))
    (hgα' : MulAut.conj g * α ≠ α * MulAut.conj g) : False := by
  obtain ⟨z, rfl⟩ := hin
  have hgN := hN Z hZ z J y g hα3 hJ hJT hyJ hyk hy3 hgk hgy
  set M := Subgroup.centralizer (J : Set Z) with hM
  have hJz : J ≤ Item426.fixSub (MulAut.conj z) := le_of_mem_thetaComponentsIn hJ
  have hzM : z ∈ M := by
    rw [hM, Subgroup.mem_centralizer_iff]
    intro j hj
    exact KS11Lie2Proof.mul_comm_of_mem_fixSub (hJz hj)
  set w := g * z * g⁻¹ * z⁻¹ with hw
  have hwM : w ∈ M :=
    M.mul_mem ((Subgroup.mem_normalizer_iff.mp hgN z).mp hzM) (M.inv_mem hzM)
  obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgα
  have hcw : MulAut.conj (δ ^ n) = MulAut.conj w := by
    rw [map_zpow, hn, hw, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hζ : (δ ^ n)⁻¹ * w ∈ Subgroup.center Z := by
    rw [Subgroup.mem_center_iff]
    intro u
    have h1 := congrArg (fun φ : MulAut Z => φ u) hcw
    simp only [MulAut.conj_apply] at h1
    calc u * ((δ ^ n)⁻¹ * w) = (δ ^ n)⁻¹ * (δ ^ n * u * (δ ^ n)⁻¹) * w := by group
      _ = (δ ^ n)⁻¹ * (w * u * w⁻¹) * w := by rw [h1]
      _ = (δ ^ n)⁻¹ * w * u := by group
  have hδJ : δ ^ n ∈ J := J.zpow_mem ((Subgroup.zpowers_le.mpr hyJ) hδy) n
  have hδc : ∀ k ∈ J, δ ^ n * k = k * δ ^ n := by
    intro k hk
    have hwk : w * k = k * w := (Subgroup.mem_centralizer_iff.mp hwM k hk).symm
    have hζk : k * ((δ ^ n)⁻¹ * w) = (δ ^ n)⁻¹ * w * k :=
      Subgroup.mem_center_iff.mp hζ k
    have e : δ ^ n = w * ((δ ^ n)⁻¹ * w)⁻¹ := by group
    rw [e]
    calc w * ((δ ^ n)⁻¹ * w)⁻¹ * k = w * (((δ ^ n)⁻¹ * w)⁻¹ * k) := by group
      _ = w * (k * ((δ ^ n)⁻¹ * w)⁻¹) := by
        congr 1
        rw [inv_mul_eq_iff_eq_mul, ← mul_assoc, ← hζk, mul_assoc, mul_inv_cancel, mul_one]
      _ = (w * k) * ((δ ^ n)⁻¹ * w)⁻¹ := by group
      _ = k * (w * ((δ ^ n)⁻¹ * w)⁻¹) := by rw [hwk]; group
  have hδθ := KS11Lie2Proof.mem_theta_of_central hJT hδJ hδc
  obtain ⟨⟨u, hu⟩, huθ, hue⟩ := hδθ
  have hu' : (⟨u, hu⟩ : J) = ⟨δ ^ n, hδJ⟩ := Subtype.ext hue
  rw [hu'] at huθ
  obtain ⟨k, hk⟩ := hyk
  obtain ⟨m, hm⟩ := Subgroup.mem_zpowers_iff.mp hδy
  have hδk : (⟨δ ^ n, hδJ⟩ : J) ^ 3 ^ k = 1 := by
    apply Subtype.ext
    simp only [Subgroup.coe_pow, Subgroup.coe_one]
    rw [← hm, ← zpow_mul, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_mul,
      zpow_natCast, hk, one_zpow, one_zpow]
  have hδ1 := congrArg Subtype.val (eq_one_of_mem_theta_of_pow_eq_one huθ hδk)
  simp only [Subgroup.coe_one] at hδ1
  apply hgα'
  have hc1 : MulAut.conj w = 1 := by rw [← hcw, hδ1, map_one]
  have hc2 : MulAut.conj g * MulAut.conj z * (MulAut.conj g)⁻¹ * (MulAut.conj z)⁻¹ = 1 := by
    rw [← hc1, hw, map_mul, map_mul, map_mul, map_inv, map_inv]
  calc MulAut.conj g * MulAut.conj z
      = MulAut.conj g * MulAut.conj z * (MulAut.conj g)⁻¹ * (MulAut.conj z)⁻¹ *
          (MulAut.conj z * MulAut.conj g) := by group
    _ = MulAut.conj z * MulAut.conj g := by rw [hc2, one_mul]

theorem one_prod_mem_commutator {X : Type} [Group X] (hX : Group.IsPerfect X) (x : X) :
    ((1 : Multiplicative (ZMod 3)), x) ∈ _root_.commutator (Multiplicative (ZMod 3) × X) := by
  have : IsMulCommutative (Multiplicative (ZMod 3)) := ⟨⟨mul_comm⟩⟩
  have hPc : _root_.commutator (Multiplicative (ZMod 3) × X) =
      (⊥ : Subgroup (Multiplicative (ZMod 3))).prod (_root_.commutator X) := by
    rw [commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod, ← commutator_def,
      ← commutator_def, commutator_eq_bot]
  rw [hPc, Subgroup.mem_prod, Subgroup.mem_bot]
  refine ⟨rfl, ?_⟩
  change x ∈ _root_.commutator X
  rw [hX.commutator_eq_top]
  exact Subgroup.mem_top x

theorem prod_mul_inv_mk_one {P Q : Type*} [Group P] [Group Q] (p : P × Q) :
    p * ((1 : P), p.2)⁻¹ = (p.1, (1 : Q)) := by
  ext <;> simp

theorem prod_mk_one_mul_comm {P Q : Type*} [CommGroup P] [Group Q] (u : P) (m : P × Q) :
    (u, (1 : Q)) * m = m * (u, 1) := by
  ext
  · exact mul_comm _ _
  · simp

theorem conj_inv_mul_eq_one {H : Type*} [Group H] {P Q R : H}
    (h : P * Q⁻¹ * (Q * R * Q⁻¹) = Q * R * Q⁻¹ * (P * Q⁻¹)) :
    (Q * R * Q⁻¹)⁻¹ * (P * R * P⁻¹) = 1 := by
  have h1 : P * R * Q⁻¹ = Q * R * Q⁻¹ * (P * Q⁻¹) := by
    calc P * R * Q⁻¹ = P * Q⁻¹ * (Q * R * Q⁻¹) := by group
      _ = Q * R * Q⁻¹ * (P * Q⁻¹) := h
  have h3 : P * R * P⁻¹ = Q * R * Q⁻¹ := by
    calc P * R * P⁻¹ = P * R * Q⁻¹ * (P * Q⁻¹)⁻¹ := by group
      _ = Q * R * Q⁻¹ * (P * Q⁻¹) * (P * Q⁻¹)⁻¹ := by rw [h1]
      _ = Q * R * Q⁻¹ := by group
  rw [h3, inv_mul_cancel]

variable {G : Type} [Group G] [Finite G]

theorem thetaAut_mem_range_conj {a : G} {Y A : Subgroup G} (hY : Y ∈ thetaComponentsAt 3 a)
    (hAC : A ≤ Subgroup.centralizer ({a} : Set G))
    (hAY : A ≤ Subgroup.normalizer (Y : Set G)) (hA : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u)
    {X : Type} [Group X] (hX : Group.IsPerfect X)
    (e : sec11YA a Y A ≃* Multiplicative (ZMod 3) × X) {c : G} (hcA : c ∈ A) :
    Item426.thetaAut Y (hAY hcA) ∈
      (MulAut.conj : (Y ⧸ aschbacherSolvableCore 3 Y) →* MulAut _).range := by
  set C := Subgroup.centralizer ({a} : Set G) with hC
  set π : C →* C ⧸ aschbacherSolvableCore 3 C := QuotientGroup.mk' _ with hπ
  have hYC : Y ≤ C := Sec6.le_centralizer_of_mem_thetaComponentsAt hY
  set Y' := Y.subgroupOf C with hY'
  set A' := A.subgroupOf C with hA'
  have hM : sec11YA a Y A = (Y' ⊔ A').map π := by
    rw [sec11YA, Subgroup.subgroupOf_sup hYC hAC]
  have hA'Y' : A' ≤ Subgroup.normalizer (Y' : Set C) := by
    intro u hu
    rw [Subgroup.mem_normalizer_iff]
    intro z
    exact Subgroup.mem_normalizer_iff.mp (hAY (Subgroup.mem_subgroupOf.mp hu)) (z : G)
  have hA'c : ∀ u ∈ A', ∀ v ∈ A', u * v = v * u := fun u hu v hv =>
    Subtype.ext (hA _ (Subgroup.mem_subgroupOf.mp hu) _ (Subgroup.mem_subgroupOf.mp hv))
  have hcommle : ⁅sec11YA a Y A, sec11YA a Y A⁆ ≤ Y'.map π := by
    rw [hM, ← Subgroup.map_commutator]
    exact Subgroup.map_mono (Item1116Proof.commutator_sup_le_of_comm hA'Y' hA'c)
  have hcC : c ∈ C := hAC hcA
  have hcM : π ⟨c, hcC⟩ ∈ sec11YA a Y A := by
    rw [hM]
    exact ⟨⟨c, hcC⟩, Subgroup.mem_sup_right (Subgroup.mem_subgroupOf.mpr hcA), rfl⟩
  set c' : sec11YA a Y A := ⟨π ⟨c, hcC⟩, hcM⟩ with hc'
  set w : sec11YA a Y A := e.symm ((1 : Multiplicative (ZMod 3)), (e c').2) with hw
  have hwc : w ∈ _root_.commutator (sec11YA a Y A) := by
    have h1 := one_prod_mem_commutator hX (e c').2
    have hec : (_root_.commutator (Multiplicative (ZMod 3) × X)).map e.symm.toMonoidHom =
        _root_.commutator (sec11YA a Y A) := by
      rw [map_commutator_eq, MonoidHom.range_eq_top_of_surjective _ e.symm.surjective,
        commutator_def]
    rw [← hec]
    exact ⟨_, h1, rfl⟩
  have hwY : (w : C ⧸ aschbacherSolvableCore 3 C) ∈ Y'.map π := by
    apply hcommle
    rw [← Subgroup.map_subtype_commutator]
    exact ⟨w, hwc, rfl⟩
  obtain ⟨y₀', hy₀', hy₀e⟩ := hwY
  have hy₀Y : (y₀' : G) ∈ Y := Subgroup.mem_subgroupOf.mp hy₀'
  have hcent : ∀ m : sec11YA a Y A, c' * w⁻¹ * m = m * (c' * w⁻¹) := by
    intro m
    apply e.injective
    have h1 : e (c' * w⁻¹) = ((e c').1, 1) := by
      rw [map_mul, map_inv, hw, MulEquiv.apply_symm_apply]
      exact prod_mul_inv_mk_one (e c')
    rw [map_mul e (c' * w⁻¹) m, map_mul e m (c' * w⁻¹), h1]
    exact prod_mk_one_mul_comm _ _
  refine ⟨((⟨y₀', hy₀Y⟩ : Y) : Y ⧸ aschbacherSolvableCore 3 Y), ?_⟩
  ext q
  induction q using QuotientGroup.induction_on with
  | H y =>
    rw [MulAut.conj_apply, Item426.thetaAut_mk, ← QuotientGroup.mk_inv, ← QuotientGroup.mk_mul,
      ← QuotientGroup.mk_mul, QuotientGroup.eq]
    have hyC : (y : G) ∈ C := hYC y.2
    set s : G := (y₀' : G) * y * (y₀' : G)⁻¹ with hs
    have hsY : s ∈ Y := Y.mul_mem (Y.mul_mem hy₀Y y.2) (Y.inv_mem hy₀Y)
    have hsC : s ∈ C := hYC hsY
    have hsM : π ⟨s, hsC⟩ ∈ sec11YA a Y A := by
      rw [hM]
      exact ⟨⟨s, hsC⟩, Subgroup.mem_sup_left (Subgroup.mem_subgroupOf.mpr hsY), rfl⟩
    have h2 := congrArg Subtype.val (hcent ⟨π ⟨s, hsC⟩, hsM⟩)
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h2
    rw [hc', ← hy₀e] at h2
    have hcy : c * y * c⁻¹ ∈ Y := (Subgroup.mem_normalizer_iff.mp (hAY hcA) y).mp y.2
    set t : G := s⁻¹ * (c * y * c⁻¹) with ht
    have htY : t ∈ Y := Y.mul_mem (Y.inv_mem hsY) hcy
    have htC : t ∈ C := hYC htY
    have htπ : π ⟨t, htC⟩ = 1 := by
      have e1 : (⟨t, htC⟩ : C) = (⟨s, hsC⟩ : C)⁻¹ *
          (⟨c, hcC⟩ * ⟨y, hyC⟩ * (⟨c, hcC⟩ : C)⁻¹) := Subtype.ext rfl
      have e2 : (⟨s, hsC⟩ : C) = y₀' * ⟨y, hyC⟩ * y₀'⁻¹ := Subtype.ext rfl
      have hS : π ⟨s, hsC⟩ = π y₀' * π ⟨y, hyC⟩ * (π y₀')⁻¹ := by
        rw [e2, map_mul, map_mul, map_inv]
      rw [hS] at h2
      rw [e1, map_mul, map_inv, map_mul, map_mul, map_inv, hS]
      exact conj_inv_mul_eq_one h2
    have htθC : t ∈ inSubgroup (aschbacherSolvableCore 3) C :=
      ⟨⟨t, htC⟩, (QuotientGroup.eq_one_iff _).mp (by rw [← QuotientGroup.mk'_apply]; exact htπ),
        rfl⟩
    have hθ : t ∈ inSubgroup (aschbacherSolvableCore 3) Y := by
      rw [Sec6.theta_eq_inf_of_mem_thetaComponentsAt hY]
      exact ⟨htY, htθC⟩
    obtain ⟨t', ht', ht'e⟩ := hθ
    have heq : t' = ⟨t, htY⟩ := Subtype.ext ht'e
    rw [heq] at ht'
    exact ht'

end KS11Lie3Proof

section Cube


theorem kFact1117CubeG2_of_normCent (hNG : NormCentJ1117G2) (hND : NormCentJ1117D4) :
    KFact1117CubeG2 := by
  have hN := KS11Lie2Proof.normCentJ1117For_or hNG hND
  intro G _ _ A a c d Y K g y hAe hA27 hAcl hYa hAY hCA hK hT hYA _ hyK hyk hy3 hdy hgYW hg3 hgy
    hgc hgc'
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAc : ∀ u ∈ A, ∀ v ∈ A, u * v = v * u := fun u hu v hv =>
    congrArg Subtype.val (hAe.1.is_comm.comm ⟨u, hu⟩ ⟨v, hv⟩)
  have hA3 : ∀ u ∈ A, u ^ 3 = 1 := hAe.2
  have hcA : c ∈ A := by rw [hAcl]; exact Subgroup.subset_closure (by simp)
  have haA : a ∈ A := by rw [hAcl]; exact Subgroup.subset_closure (by simp)
  have hdA : d ∈ A := by rw [hAcl]; exact Subgroup.subset_closure (by simp)
  have hAC : A ≤ Subgroup.centralizer ({a} : Set G) := fun u hu =>
    Subgroup.mem_centralizer_singleton_iff.mpr (hAc u hu a haA)
  have hcN := hAY hcA
  have hc3 := hA3 c hcA
  have hZ : ∃ (X : Type) (_ : Group X), ((∃ (q : TauCeti.PrimePower)
      (hq : (TauCeti.LieTypeIndex.G2 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.G2 q, hq⟩).Group)) ∨
      ∃ (q : TauCeti.PrimePower) (hq : (TauCeti.LieTypeIndex.trialityD4 q).Valid),
        Nonempty (X ≃* (TauCeti.CFSGIndex.lie ⟨.trialityD4 q, hq⟩).Group)) ∧
      Nonempty (Y ⧸ aschbacherSolvableCore 3 Y ≃* _root_.commutator X) := by
    rcases hYA with ⟨q, hq, ⟨e⟩⟩ | ⟨q, hq, ⟨e⟩⟩
    · exact ⟨_, _, Or.inl ⟨q, hq, ⟨MulEquiv.refl _⟩⟩,
        Item1116Proof.nonempty_thetaQuot_equiv_commutator hYa hAC hAY hAc e⟩
    · exact ⟨_, _, Or.inr ⟨q, hq, ⟨MulEquiv.refl _⟩⟩,
        Item1116Proof.nonempty_thetaQuot_equiv_commutator hYa hAC hAY hAc e⟩
  have hin : Item426.thetaAut Y hcN ∈
      (MulAut.conj : (Y ⧸ aschbacherSolvableCore 3 Y) →* MulAut _).range := by
    rcases hYA with ⟨q, hq, ⟨e⟩⟩ | ⟨q, hq, ⟨e⟩⟩
    · exact KS11Lie3Proof.thetaAut_mem_range_conj hYa hAC hAY hAc
        (SetUp1118Proof.isPerfect_lie_G2 q hq) e hcA
    · exact KS11Lie3Proof.thetaAut_mem_range_conj hYa hAC hAY hAc
        (SetUp1118Proof.isPerfect_lie_trialityD4 q hq) e hcA
  set π := QuotientGroup.mk' (aschbacherSolvableCore 3 Y) with hπ
  set τ := (thetaQuotMulAut Y).comp (compAction Y) with hτ
  have hKY : K ≤ Y := (le_of_mem_thetaComponentsIn hK).trans inf_le_left
  have hJ := Item426.map_mem_thetaComponentsIn_fixSub Y hcN hc3 hK
  obtain ⟨eK⟩ := Item426.nonempty_quotTheta_map_equiv Y hKY
  have hJT := isType424_of_mulEquiv eK.symm hT
  have hyY : y ∈ Y := hKY hyK
  have hdK : d ∈ K := (Subgroup.zpowers_le.mpr hyK) hdy
  have hdY : d ∈ Y := hKY hdK
  have hgY : g ∈ Y := hgYW.1
  have hconj : ∀ (x : G) (hx : x ∈ Y), MulAut.conj (π ⟨x, hx⟩) =
      τ ⟨x, Subgroup.le_normalizer hx⟩ := fun x hx =>
    (KS11LieProof.thetaQuotMulAut_of_mem hx (Subgroup.le_normalizer hx)).symm
  have hα : Item426.thetaAut Y hcN = τ ⟨c, hcN⟩ := rfl
  have hcent : ∀ z ∈ A, z ∈ Sec4.thetaQuotCentralizer Y → z ∈ Subgroup.zpowers a := by
    intro z hzA hz
    have h1 := mem_sectionCentralizer_of_mem_thetaQuotCentralizer hzA hz
    rw [hCA] at h1
    exact h1
  have hcard9 : ∀ u v : G, u ∈ A → v ∈ A → A ≤ Subgroup.closure ({u, v} : Set G) → False := by
    intro u v hu hv hle
    have h1 := Subgroup.card_le_of_le hle
    have h2 := Sec10.card_closure_pair_le (hAc u hu v hv) (hA3 u hu) (hA3 v hv)
    omega
  refine KS11Lie3Proof.false_of_normCentJ1117For hN hZ hin
    (Item426.thetaAut_pow_eq_one Y hcN hc3) hJ hJT (y := π ⟨y, hyY⟩) (δ := π ⟨d, hdY⟩)
    (g := π ⟨g, hgY⟩) ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_
  · exact ⟨⟨y, hyY⟩, Subgroup.mem_subgroupOf.mpr hyK, rfl⟩
  · obtain ⟨k, hk⟩ := hyk
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨y, hyY⟩ : Y) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  · intro h1
    apply hy3
    rw [← map_pow, hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    obtain ⟨k, hk⟩ := hyk
    have h2 := eq_one_of_mem_theta_of_pow_eq_one h1 (k := k) (by
      rw [← pow_mul, mul_comm, pow_mul]
      have : (⟨y, hyY⟩ : Y) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
      rw [this, one_pow])
    simpa using congrArg Subtype.val h2
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hdy
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [← map_zpow]
    congr 1
    exact Subtype.ext (by simpa using hn)
  · obtain ⟨k, hk⟩ := hg3
    refine ⟨k, ?_⟩
    rw [← map_pow]
    have : (⟨g, hgY⟩ : Y) ^ 3 ^ k = 1 := Subtype.ext (by simpa using hk)
    rw [this, map_one]
  · obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgy
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [← map_zpow, ← map_inv, ← map_mul, ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hn)
  ·
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hgc
    refine Subgroup.mem_zpowers_iff.mpr ⟨n, ?_⟩
    rw [hconj g hgY, hconj d hdY, hα, ← map_zpow, ← map_inv, ← map_inv, ← map_mul, ← map_mul,
      ← map_mul]
    congr 1
    exact Subtype.ext (by simpa using hn)
  ·
    intro hcomm
    rw [hconj g hgY, hα] at hcomm
    have h1 : g * c * g⁻¹ * c⁻¹ ∈ Sec4.thetaQuotCentralizer Y :=
      commutator_mem_thetaQuotCentralizer_of_commute (Subgroup.le_normalizer hgY) hcN hcomm
    set x := g * c * g⁻¹ * c⁻¹ with hx
    have hxA : x ∈ A := Subgroup.zpowers_le.mpr hdA hgc
    have hxa := hcent x hxA h1
    have hx1 : x = 1 := by
      by_contra hx1
      have hxo : orderOf x = 3 := orderOf_eq_prime (hA3 x hxA) hx1
      have ha1 : a ≠ 1 := by
        rintro rfl
        exact hx1 (by simpa using hxa)
      have hao : orderOf a = 3 := orderOf_eq_prime (hA3 a haA) ha1
      have hza : Subgroup.zpowers x = Subgroup.zpowers a := by
        refine Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hxa) ?_
        rw [Nat.card_zpowers, Nat.card_zpowers, hxo, hao]
      have hacd : a ∈ Subgroup.closure ({c, d} : Set G) := by
        have h2 : a ∈ Subgroup.zpowers x := hza ▸ Subgroup.mem_zpowers a
        have h3 : Subgroup.zpowers x ≤ Subgroup.zpowers d := Subgroup.zpowers_le.mpr hgc
        exact (Subgroup.zpowers_le.mpr (Subgroup.subset_closure (by simp))) (h3 h2)
      apply hcard9 c d hcA hdA
      rw [hAcl, Subgroup.closure_le]
      intro u hu
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hu
      rcases hu with rfl | rfl | rfl
      · exact Subgroup.subset_closure (by simp)
      · exact hacd
      · exact Subgroup.subset_closure (by simp)
    apply hgc'
    calc g * c * g⁻¹ = x * c := by rw [hx]; group
      _ = c := by rw [hx1, one_mul]

end Cube

end CFSG.RankThree.PartTwo.Sec11

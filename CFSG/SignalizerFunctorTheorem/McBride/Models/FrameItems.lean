module

public import CFSG.SignalizerFunctorTheorem.McBride.Models.Frame
import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.ChiefFactors.Proposition12
import CFSG.ThirdParty.BrauerInduction.Background.Group.PDecomposition
import CFSG.ClassicalInvolution.LBalance.Glauberman.CoprimeAction

public section

open CFSG.Open
open scoped Pointwise

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {p ℓ : ℕ} {X : Type*} [Group X]

namespace FrameItems

theorem conj_mem_centralizer {f : MulAut X} {x z : X} (hx : x ∈ fixedNormalizer f)
    (hz : z ∈ Subgroup.centralizer (fixedFitting f : Set X)) :
    x * z * x⁻¹ ∈ Subgroup.centralizer (fixedFitting f : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro k hk
  have hk' : x⁻¹ * k * x ∈ fixedFitting f := (Subgroup.mem_normalizer_iff''.mp hx k).mp hk
  have hz' := hz _ hk'
  calc k * (x * z * x⁻¹) = x * ((x⁻¹ * k * x) * z) * x⁻¹ := by group
    _ = x * (z * (x⁻¹ * k * x)) * x⁻¹ := by rw [hz']
    _ = x * z * x⁻¹ * k := by group

theorem fixedFitting_subgroupOf_normal (f : MulAut X) :
    ((fixedFitting f).subgroupOf (signalizerFixedSubgroup f)).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using fixedFitting_conj_mem g.2 hn⟩

theorem centralizer_le_fixedNormalizer (f : MulAut X) :
    Subgroup.centralizer (fixedFitting f : Set X) ≤ fixedNormalizer f :=
  Subgroup.centralizer_le_normalizer _

theorem centralizer_subgroupOf_normal (f : MulAut X) :
    ((Subgroup.centralizer (fixedFitting f : Set X)).subgroupOf (fixedNormalizer f)).Normal :=
  ⟨fun n hn g => by
    rw [Subgroup.mem_subgroupOf] at hn ⊢
    simpa using conj_mem_centralizer g.2 hn⟩

theorem le_fittingSubgroupOf_of_normal_subgroupOf {G : Type*} [Group G] {H N : Subgroup G}
    (hNH : N ≤ H) (hN : (N.subgroupOf H).Normal) (hnil : Group.IsNilpotent N) :
    N ≤ CFSG.fittingSubgroupOf H := by
  have : Group.IsNilpotent (N.subgroupOf H) :=
    Group.nilpotent_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hNH).symm
  have hle : N.subgroupOf H ≤ CFSG.fittingSubgroup H := le_sSup ⟨hN, this⟩
  have hmap := Subgroup.map_mono (f := H.subtype) hle
  simpa [CFSG.fittingSubgroupOf, Subgroup.subgroupOf_map_subtype, inf_eq_left.2 hNH] using hmap

theorem apply_mem_centralizer {f g : MulAut X} (hg : ∀ k ∈ fixedFitting f, g k = k) {z : X}
    (hz : z ∈ Subgroup.centralizer (fixedFitting f : Set X)) :
    g z ∈ Subgroup.centralizer (fixedFitting f : Set X) := by
  rw [Subgroup.mem_centralizer_iff] at hz ⊢
  intro k hk
  calc k * g z = g k * g z := by rw [hg k hk]
    _ = g (k * z) := (map_mul g k z).symm
    _ = g (z * k) := by rw [hz k hk]
    _ = g z * k := by rw [map_mul, hg k hk]

theorem fixedFitting_apply {f : MulAut X} {k : X} (hk : k ∈ fixedFitting f) : f k = k :=
  fixedFitting_le f hk

theorem fixedFitting_inv_apply {f : MulAut X} {k : X} (hk : k ∈ fixedFitting f) : f⁻¹ k = k := by
  have e := MulAut.inv_apply_self X f k
  rwa [fixedFitting_apply hk] at e

private def centralizerAut (f : MulAut X) :
    MulAut (Subgroup.centralizer (fixedFitting f : Set X)) where
  toFun w := ⟨f w, apply_mem_centralizer (fun _ hk => fixedFitting_apply hk) w.2⟩
  invFun w := ⟨f⁻¹ w, apply_mem_centralizer (fun _ hk => fixedFitting_inv_apply hk) w.2⟩
  left_inv w := Subtype.ext (MulAut.inv_apply_self X f (w : X))
  right_inv w := Subtype.ext (MulAut.apply_inv_self X f (w : X))
  map_mul' a b := Subtype.ext (map_mul f (a : X) (b : X))

private theorem coe_centralizerAut_pow (f : MulAut X) (i : ℕ)
    (w : Subgroup.centralizer (fixedFitting f : Set X)) :
    ((centralizerAut f ^ i) w : X) = (f ^ i) w := by
  induction i generalizing w with
  | zero => rfl
  | succ i ih =>
    rw [pow_succ, pow_succ, MulAut.mul_apply, MulAut.mul_apply, ih]
    rfl

theorem autCommutator_centralizer_le (f : MulAut X) :
    autCommutator f (Subgroup.centralizer (fixedFitting f : Set X)) ≤
      Subgroup.centralizer (fixedFitting f : Set X) := by
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨x, hx, rfl⟩
  exact Subgroup.mul_mem _ (Subgroup.inv_mem _ hx)
    (apply_mem_centralizer (fun _ hk => fixedFitting_apply hk) hx)

theorem conj_mem_autCommutator {f : MulAut X} {c w : X} (hc : c ∈ signalizerFixedSubgroup f)
    (hw : w ∈ autCommutator f (Subgroup.centralizer (fixedFitting f : Set X))) :
    c * w * c⁻¹ ∈ autCommutator f (Subgroup.centralizer (fixedFitting f : Set X)) := by
  have hle : autCommutator f (Subgroup.centralizer (fixedFitting f : Set X)) ≤
      (autCommutator f (Subgroup.centralizer (fixedFitting f : Set X))).comap
        (MulAut.conj c).toMonoidHom := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro y ⟨u, hu, rfl⟩
    simp only [SetLike.mem_coe, Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    refine Subgroup.subset_closure ⟨c * u * c⁻¹, ?_, ?_⟩
    · exact conj_mem_centralizer (fixed_le_fixedNormalizer f hc) hu
    · have hfc : f c = c := hc
      simp only [map_mul, map_inv, hfc]
      group
  simpa using hle hw

end FrameItems

theorem Frame.fixedFitting_le_centralizer {f : MulAut X} (h : Frame p ℓ f) :
    fixedFitting f ≤ Subgroup.centralizer (fixedFitting f : Set X) :=
  Subgroup.le_centralizer_iff_isMulCommutative.mpr h.C0_comm

theorem Frame.mem_fixedFitting_of_mem_centralizer {f : MulAut X} (h : Frame p ℓ f) {z : X}
    (hzC : z ∈ signalizerFixedSubgroup f)
    (hzZ : z ∈ Subgroup.centralizer (fixedFitting f : Set X)) : z ∈ fixedFitting f := by
  by_contra hz
  exact hz (h.fpf z hzC hz z hzZ rfl ▸ Subgroup.one_mem _)

theorem Frame.not_isSolvable {f : MulAut X} (h : Frame p ℓ f) : ¬ Group.IsSolvable X := by
  have := h.simple
  intro hs
  obtain ⟨a, b, hab⟩ := h.nonabelian
  exact hab (IsSimpleGroup.comm_iff_isSolvable.mpr hs a b)

theorem Frame.fixed_ne_top {f : MulAut X} (h : Frame p ℓ f) : signalizerFixedSubgroup f ≠ ⊤ := by
  intro htop
  apply h.not_isSolvable
  have := h.fixed_solvable
  rw [htop] at this
  exact Group.isSolvable_of_surjective (f := (Subgroup.topEquiv (G := X)).toMonoidHom)
    Subgroup.topEquiv.surjective

theorem Frame.le_fixedNormalizer {f : MulAut X} (h : Frame p ℓ f) {Y : Subgroup X} (hY : Y ≠ ⊤)
    (hC : signalizerFixedSubgroup f ≤ Subgroup.normalizer (Y : Set X)) :
    Y ≤ fixedNormalizer f := by
  have hne : Y ⊔ signalizerFixedSubgroup f ≠ ⊤ := by
    intro htop
    have hnorm : Y.Normal := by
      rw [← Subgroup.normalizer_eq_top_iff, eq_top_iff, ← htop]
      exact sup_le Subgroup.le_normalizer hC
    have := h.simple
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Y with hbot | hT
    · apply h.fixed_ne_top
      rwa [hbot, bot_sup_eq] at htop
    · exact hY hT
  exact le_sup_left.trans (h.overgroup _ le_sup_right hne)

theorem Frame.mem_fixedFitting_of_orderOf {f : MulAut X} (h : Frame p ℓ f) {x : X}
    (hx : x ∈ fixedNormalizer f) {n : ℕ} (hn : orderOf x = ℓ ^ n) : x ∈ fixedFitting f := by
  have := Fact.mk h.prime_ℓ
  have hz : IsPGroup ℓ (Subgroup.zpowers x) :=
    IsPGroup.of_card (n := n) (by rw [Nat.card_zpowers, hn])
  have hle : Subgroup.zpowers x ≤ Subgroup.normalizer (fixedFitting f : Set X) :=
    Subgroup.zpowers_le.mpr hx
  have hsup := h.C0_sylow _ (IsPGroup.to_sup_of_normal_left' h.C0_pgroup hz hle) le_sup_left
  have hmem : x ∈ fixedFitting f ⊔ Subgroup.zpowers x :=
    Subgroup.mem_sup_right (Subgroup.mem_zpowers x)
  rwa [hsup] at hmem

theorem Frame.le_centralizer_of_nilpotent [Finite X] {f : MulAut X} (h : Frame p ℓ f)
    {Y : Subgroup X} (hY : Group.IsNilpotent Y) (hYM : Y ≤ fixedNormalizer f)
    (hCY : fixedFitting f ≤ Y) : Y ≤ Subgroup.centralizer (fixedFitting f : Set X) := by
  have := Fact.mk h.prime_ℓ
  have := h.C0_comm
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro k hk
  have hfin : IsOfFinOrder y := isOfFinOrder_of_finite y
  have hdec : Group.pRegular ℓ y * Group.pSingular ℓ y = y := Group.pDecomp' ℓ hfin
  have haY : Group.pSingular ℓ y ∈ Y := Subgroup.zpow_mem Y hy _
  have hbY : Group.pRegular ℓ y ∈ Y := Subgroup.zpow_mem Y hy _
  have ha : Group.pSingular ℓ y ∈ fixedFitting f := by
    obtain ⟨n, hn⟩ := Group.isPSingular_pSingular ℓ y
    exact h.mem_fixedFitting_of_orderOf (hYM haY) hn
  have hbk : Commute (Group.pRegular ℓ y) k := by
    obtain ⟨t, ht⟩ := h.C0_pgroup ⟨k, hk⟩
    have hdvd : orderOf k ∣ ℓ ^ t := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val ht)
    have hcop : (orderOf (⟨Group.pRegular ℓ y, hbY⟩ : Y)).Coprime
        (orderOf (⟨k, hCY hk⟩ : Y)) := by
      rw [Subgroup.orderOf_mk, Subgroup.orderOf_mk]
      exact Nat.Coprime.coprime_dvd_right hdvd
        ((Group.isPRegular_pRegular ℓ hfin).pow_right t)
    exact (commute_iff_eq _ _).mpr
      (congrArg Subtype.val (Group.IsNilpotent.commute_of_orderOf_coprime hcop).eq)
  have hak : Commute (Group.pSingular ℓ y) k :=
    (commute_iff_eq _ _).mpr (setLike_mul_comm ha hk)
  have hcomm := (hbk.mul_left hak).eq
  rw [hdec] at hcomm
  exact hcomm.symm

open scoped IsMulCommutative in
theorem Frame.centralizer_le_fitting [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    Subgroup.centralizer (fixedFitting f : Set X) ≤
      CFSG.fittingSubgroupOf (fixedNormalizer f) := by
  have := h.centralizer_comm
  exact FrameItems.le_fittingSubgroupOf_of_normal_subgroupOf
    (FrameItems.centralizer_le_fixedNormalizer f) (FrameItems.centralizer_subgroupOf_normal f)
    inferInstance

theorem Frame.fitting_le_centralizer [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    CFSG.fittingSubgroupOf (fixedNormalizer f) ≤
      Subgroup.centralizer (fixedFitting f : Set X) :=
  h.le_centralizer_of_nilpotent (CFSG.fittingSubgroupOf_isNilpotent _)
    (CFSG.fittingSubgroupOf_le _) (h.fixedFitting_le_centralizer.trans h.centralizer_le_fitting)

theorem Frame.fittingSubgroupOf_eq_centralizer [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    CFSG.fittingSubgroupOf (fixedNormalizer f) = Subgroup.centralizer (fixedFitting f : Set X) :=
  le_antisymm h.fitting_le_centralizer h.centralizer_le_fitting

theorem Frame.fixedNormalizer_ne_top {f : MulAut X} (h : Frame p ℓ f) :
    fixedNormalizer f ≠ ⊤ := by
  intro htop
  have := h.simple
  have hnorm : (fixedFitting f).Normal := Subgroup.normalizer_eq_top_iff.mp htop
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (fixedFitting f) with hbot | hT
  · exact h.C0_ne_bot hbot
  · obtain ⟨a, b, hab⟩ := h.nonabelian
    have := h.C0_comm
    exact hab (setLike_mul_comm (hT ▸ Subgroup.mem_top a) (hT ▸ Subgroup.mem_top b))

open scoped IsMulCommutative in
theorem Frame.fixedNormalizer_solvable [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    Group.IsSolvable (fixedNormalizer f) := by
  have := h.centralizer_comm
  have := h.fixed_solvable
  have hZM := FrameItems.centralizer_le_fixedNormalizer f
  have hnorm := FrameItems.centralizer_subgroupOf_normal f
  let π : fixedNormalizer f →* fixedNormalizer f ⧸
      (Subgroup.centralizer (fixedFitting f : Set X)).subgroupOf (fixedNormalizer f) :=
    QuotientGroup.mk' _
  let ι : signalizerFixedSubgroup f →* fixedNormalizer f :=
    Subgroup.inclusion (fixed_le_fixedNormalizer f)
  have hsurj : Function.Surjective (π.comp ι) := by
    intro q
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective q
    obtain ⟨z, hz, c, hc, hxc⟩ := h.normalizer_le x x.2
    refine ⟨⟨c, hc⟩, ?_⟩
    show QuotientGroup.mk (ι ⟨c, hc⟩) = QuotientGroup.mk x
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    have hc' : c⁻¹ ∈ fixedNormalizer f := Subgroup.inv_mem _ (fixed_le_fixedNormalizer f hc)
    have := FrameItems.conj_mem_centralizer hc' hz
    simpa [ι, hxc, mul_assoc] using this
  have : Group.IsSolvable (fixedNormalizer f ⧸
      (Subgroup.centralizer (fixedFitting f : Set X)).subgroupOf (fixedNormalizer f)) :=
    Group.isSolvable_of_surjective hsurj
  exact Group.isSolvable_of_ker_le_range (Subgroup.inclusion hZM) π
    (by rw [QuotientGroup.ker_mk', Subgroup.inclusion_range])

theorem Frame.exists_complement [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    ∃ V : Subgroup X, V ≠ ⊥ ∧ V ≤ signalizerFixedSubgroup f ∧ Disjoint (fixedFitting f) V ∧
      (∀ c ∈ signalizerFixedSubgroup f, ∃ k ∈ fixedFitting f, ∃ v ∈ V, c = k * v) ∧
      ∀ v ∈ V, v ≠ 1 → ∀ z ∈ Subgroup.centralizer (fixedFitting f : Set X),
        v * z = z * v → z = 1 := by
  have := Fact.mk h.prime_ℓ
  have hnorm := FrameItems.fixedFitting_subgroupOf_normal f
  let S : Sylow ℓ (signalizerFixedSubgroup f) :=
    { toSubgroup := (fixedFitting f).subgroupOf (signalizerFixedSubgroup f)
      isPGroup' := h.C0_pgroup.comap_subtype
      is_maximal' := fun {Q} hQ hle => by
        have hQ' : IsPGroup ℓ (Q.map (signalizerFixedSubgroup f).subtype) := hQ.map _
        have hge : fixedFitting f ≤ Q.map (signalizerFixedSubgroup f).subtype := fun x hx =>
          ⟨⟨x, fixedFitting_le f hx⟩, hle hx, rfl⟩
        have heq := h.C0_sylow _ hQ' hge
        calc Q = (Q.map (signalizerFixedSubgroup f).subtype).comap
              (signalizerFixedSubgroup f).subtype :=
            (Subgroup.comap_map_eq_self_of_injective
              (signalizerFixedSubgroup f).subtype_injective Q).symm
          _ = _ := by rw [heq]; rfl }
  have hnd : ¬ ℓ ∣ ((fixedFitting f).subgroupOf (signalizerFixedSubgroup f)).index :=
    S.not_dvd_index
  have hcop : (Nat.card ((fixedFitting f).subgroupOf (signalizerFixedSubgroup f))).Coprime
      ((fixedFitting f).subgroupOf (signalizerFixedSubgroup f)).index := by
    obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp S.isPGroup'
    rw [show Nat.card ((fixedFitting f).subgroupOf (signalizerFixedSubgroup f)) = ℓ ^ n from hn]
    exact Nat.Coprime.pow_left n ((Nat.Prime.coprime_iff_not_dvd h.prime_ℓ).mpr hnd)
  obtain ⟨V', hV'⟩ := Subgroup.exists_right_complement'_of_coprime hcop
  have hdisj : Disjoint (fixedFitting f) (V'.map (signalizerFixedSubgroup f).subtype) := by
    rw [Subgroup.disjoint_def]
    rintro x hx ⟨v, hv, rfl⟩
    have := Subgroup.disjoint_def.mp hV'.disjoint (Subgroup.mem_subgroupOf.mpr hx) hv
    simp [this]
  have hdec : ∀ c ∈ signalizerFixedSubgroup f, ∃ k ∈ fixedFitting f,
      ∃ v ∈ V'.map (signalizerFixedSubgroup f).subtype, c = k * v := by
    intro c hc
    have hmem : (⟨c, hc⟩ : signalizerFixedSubgroup f) ∈
        (fixedFitting f).subgroupOf (signalizerFixedSubgroup f) ⊔ V' := by
      rw [hV'.sup_eq_top]
      exact Subgroup.mem_top _
    rw [← SetLike.mem_coe, Subgroup.normal_mul] at hmem
    obtain ⟨n, hn, v, hv, hnv⟩ := hmem
    exact ⟨n, hn, v, ⟨v, hv, rfl⟩, congrArg Subtype.val hnv.symm⟩
  have hVC : V'.map (signalizerFixedSubgroup f).subtype ≤ signalizerFixedSubgroup f :=
    Subgroup.map_subtype_le V'
  have hne : V'.map (signalizerFixedSubgroup f).subtype ≠ ⊥ := by
    intro hbot
    apply h.C0_ne
    refine le_antisymm (fixedFitting_le f) (fun c hc => ?_)
    obtain ⟨k, hk, v, hv, rfl⟩ := hdec c hc
    rw [hbot, Subgroup.mem_bot] at hv
    rwa [hv, mul_one]
  refine ⟨_, hne, hVC, hdisj, hdec, ?_⟩
  intro v hv hv1 z hz hcomm
  have hvC0 : v ∉ fixedFitting f := fun hvk => hv1 (Subgroup.disjoint_def.mp hdisj hvk hv)
  exact h.fpf v (hVC hv) hvC0 z hz hcomm

theorem Frame.frobenius_fixed [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    IsFrobeniusWithKernel (signalizerFixedSubgroup f) (fixedFitting f) := by
  obtain ⟨V, hne, hVC, hdisj, hdec, hfpf⟩ := h.exists_complement
  unfold IsFrobeniusWithKernel
  refine ⟨h.C0_ne_bot, fixedFitting_le f, FrameItems.fixedFitting_subgroupOf_normal f, V, hne, hVC,
    hdisj, ?_, fun v hv hv1 k hk hcomm =>
      hfpf v hv hv1 k (h.fixedFitting_le_centralizer hk) hcomm⟩
  refine le_antisymm (sup_le (fixedFitting_le f) hVC) (fun c hc => ?_)
  obtain ⟨k, hk, v, hv, rfl⟩ := hdec c hc
  exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hv)

theorem Frame.frobenius_core1 [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    IsFrobeniusWithKernel (fixedCore1 f) (fixedFitting f) := by
  obtain ⟨V, hne, hVC, hdisj, hdec, hfpf⟩ := h.exists_complement
  have hC0C1 : fixedFitting f ≤ fixedCore1 f := by
    intro k hk
    refine ⟨fixedFitting_le f hk, fun x hx => ?_⟩
    have := fixedFitting_conj_mem hx (Subgroup.inv_mem _ hk)
    rw [commutatorElement_def]
    simpa [mul_assoc] using Subgroup.mul_mem _ hk this
  have hnorm : ((fixedFitting f).subgroupOf (fixedCore1 f)).Normal :=
    ⟨fun n hn g => by
      rw [Subgroup.mem_subgroupOf] at hn ⊢
      simpa using fixedFitting_conj_mem g.2.1 hn⟩
  have hdec1 : ∀ x ∈ fixedCore1 f, ∃ k ∈ fixedFitting f, ∃ v ∈ V ⊓ fixedCore1 f, x = k * v := by
    intro x hx
    obtain ⟨k, hk, v, hv, rfl⟩ := hdec x hx.1
    refine ⟨k, hk, v, ⟨hv, ?_⟩, rfl⟩
    simpa using Subgroup.mul_mem _ (Subgroup.inv_mem _ (hC0C1 hk)) hx
  unfold IsFrobeniusWithKernel
  refine ⟨h.C0_ne_bot, hC0C1, hnorm, V ⊓ fixedCore1 f, ?_, inf_le_right,
    hdisj.mono_right inf_le_left, ?_, fun v hv hv1 k hk hcomm =>
      hfpf v hv.1 hv1 k (h.fixedFitting_le_centralizer hk) hcomm⟩
  · intro hbot
    apply h.C1_ne
    refine le_antisymm (fun x hx => ?_) hC0C1
    obtain ⟨k, hk, v, hv, rfl⟩ := hdec1 x hx
    rw [hbot, Subgroup.mem_bot] at hv
    rwa [hv, mul_one]
  · refine le_antisymm (sup_le hC0C1 inf_le_right) (fun x hx => ?_)
    obtain ⟨k, hk, v, hv, rfl⟩ := hdec1 x hx
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_left hk) (Subgroup.mem_sup_right hv)

theorem Frame.frobenius_normalizer [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    IsFrobeniusWithKernel (fixedNormalizer f) (CFSG.fittingSubgroupOf (fixedNormalizer f)) := by
  obtain ⟨V, hne, hVC, hdisj, hdec, hfpf⟩ := h.exists_complement
  rw [h.fittingSubgroupOf_eq_centralizer]
  have hC0Z := h.fixedFitting_le_centralizer
  unfold IsFrobeniusWithKernel
  refine ⟨?_, FrameItems.centralizer_le_fixedNormalizer f,
    FrameItems.centralizer_subgroupOf_normal f, V, hne, hVC.trans (fixed_le_fixedNormalizer f),
    ?_, ?_, fun v hv hv1 z hz hcomm => hfpf v hv hv1 z hz hcomm⟩
  · intro hbot
    exact h.C0_ne_bot (le_bot_iff.mp (hC0Z.trans hbot.le))
  · rw [Subgroup.disjoint_def]
    intro x hxZ hxV
    exact Subgroup.disjoint_def.mp hdisj (h.mem_fixedFitting_of_mem_centralizer (hVC hxV) hxZ) hxV
  · refine le_antisymm (sup_le (FrameItems.centralizer_le_fixedNormalizer f)
      (hVC.trans (fixed_le_fixedNormalizer f))) (fun x hx => ?_)
    obtain ⟨z, hz, c, hc, rfl⟩ := h.normalizer_le x hx
    obtain ⟨k, hk, v, hv, rfl⟩ := hdec c hc
    rw [← mul_assoc]
    exact Subgroup.mul_mem _ (Subgroup.mul_mem _ (Subgroup.mem_sup_left hz)
      (Subgroup.mem_sup_left (hC0Z hk))) (Subgroup.mem_sup_right hv)

open scoped IsMulCommutative in
theorem Frame.exists_mul_of_mem_centralizer [Finite X] {f : MulAut X} (h : Frame p ℓ f) {z : X}
    (hz : z ∈ Subgroup.centralizer (fixedFitting f : Set X)) :
    ∃ b ∈ fixedFitting f,
      ∃ a ∈ autCommutator f (Subgroup.centralizer (fixedFitting f : Set X)), z = b * a := by
  have := h.centralizer_comm
  have hφp : FrameItems.centralizerAut f ^ p = 1 := by
    ext w
    show ((FrameItems.centralizerAut f ^ p) w : X) = w
    rw [FrameItems.coe_centralizerAut_pow, ← h.ord, pow_orderOf_eq_one]
    rfl
  have hcop : Nat.Coprime p (Nat.card (Subgroup.centralizer (fixedFitting f : Set X))) :=
    Nat.Coprime.coprime_dvd_right (Subgroup.card_subgroup_dvd_card _) h.coprime
  have hmem : (⟨z, hz⟩ : Subgroup.centralizer (fixedFitting f : Set X)) ∈
      ClassicalInvolution.GlaubermanAut.fixedSubgroup (FrameItems.centralizerAut f) ⊔
        ClassicalInvolution.GlaubermanAut.commutatorSubgroup (FrameItems.centralizerAut f) := by
    rw [ClassicalInvolution.GlaubermanAut.fixedSubgroup_sup_commutatorSubgroup hφp hcop]
    exact Subgroup.mem_top _
  obtain ⟨b, hb, a, ha, hba⟩ := Subgroup.mem_sup.mp hmem
  obtain ⟨u, rfl⟩ := (ClassicalInvolution.GlaubermanAut.mem_commutatorSubgroup _).mp ha
  have hbC : (b : X) ∈ signalizerFixedSubgroup f :=
    congrArg Subtype.val ((ClassicalInvolution.GlaubermanAut.mem_fixedSubgroup _).mp hb)
  refine ⟨b, h.mem_fixedFitting_of_mem_centralizer hbC b.2, _, ?_, (congrArg Subtype.val hba).symm⟩
  refine Subgroup.subset_closure ⟨(u : X)⁻¹, Subgroup.inv_mem _ u.2, ?_⟩
  simp [FrameItems.centralizerAut]

theorem Frame.unique_maximal [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    signalizerFixedSubgroup f ≤ fixedNormalizer f ∧ fixedNormalizer f ≠ ⊤ ∧
      Group.IsSolvable (fixedNormalizer f) ∧
      ∀ H : Subgroup X, signalizerFixedSubgroup f ≤ H → H ≠ ⊤ → H ≤ fixedNormalizer f :=
  ⟨fixed_le_fixedNormalizer f, h.fixedNormalizer_ne_top, h.fixedNormalizer_solvable, h.overgroup⟩

theorem Frame.frobenius [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    IsFrobeniusWithKernel (fixedCore1 f) (fixedFitting f) ∧
      IsFrobeniusWithKernel (signalizerFixedSubgroup f) (fixedFitting f) ∧
      IsFrobeniusWithKernel (fixedNormalizer f) (CFSG.fittingSubgroupOf (fixedNormalizer f)) ∧
      IsMulCommutative (fixedFitting f) ∧
      IsMulCommutative (CFSG.fittingSubgroupOf (fixedNormalizer f)) := by
  refine ⟨h.frobenius_core1, h.frobenius_fixed, h.frobenius_normalizer, h.C0_comm, ?_⟩
  rw [h.fittingSubgroupOf_eq_centralizer]
  exact h.centralizer_comm

theorem Frame.fitting_eq_centralizer [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    CFSG.fittingSubgroupOf (fixedNormalizer f) = Subgroup.centralizer (fixedFitting f : Set X) ∧
      (CFSG.fittingSubgroupOf (fixedNormalizer f) : Set X) *
        (signalizerFixedSubgroup f : Set X) = (fixedNormalizer f : Set X) := by
  have hFM := h.fittingSubgroupOf_eq_centralizer
  refine ⟨hFM, ?_⟩
  ext x
  constructor
  · rintro ⟨a, ha, c, hc, rfl⟩
    exact Subgroup.mul_mem _ (CFSG.fittingSubgroupOf_le _ ha) (fixed_le_fixedNormalizer f hc)
  · intro hx
    obtain ⟨z, hz, c, hc, rfl⟩ := h.normalizer_le x hx
    exact ⟨z, hFM ▸ hz, c, hc, rfl⟩

theorem Frame.minimal_normal [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    fixedFitting f ≠ ⊥ ∧ ((fixedFitting f).subgroupOf (signalizerFixedSubgroup f)).Normal ∧
      ∀ N : Subgroup X, N ≤ signalizerFixedSubgroup f →
        (N.subgroupOf (signalizerFixedSubgroup f)).Normal → N ≠ ⊥ → fixedFitting f ≤ N :=
  ⟨h.C0_ne_bot, FrameItems.fixedFitting_subgroupOf_normal f, h.minimal⟩

theorem Frame.invariant_subgroup [Finite X] {f : MulAut X} (h : Frame p ℓ f) (Y : Subgroup X)
    (hY : Y ≠ ⊤) (hC : signalizerFixedSubgroup f ≤ Subgroup.normalizer (Y : Set X)) :
    fixedFitting f ≤ Y ∨ Y ≤ autCommutator f (CFSG.fittingSubgroupOf (fixedNormalizer f)) := by
  by_cases hC0Y : fixedFitting f ≤ Y
  · exact Or.inl hC0Y
  right
  rw [h.fittingSubgroupOf_eq_centralizer]
  have := Fact.mk h.prime_ℓ
  have hcomm := h.centralizer_comm
  have hYC0 : ∀ x ∈ Y, x ∈ fixedFitting f → x = 1 := by
    have hnorm : ((Y ⊓ fixedFitting f).subgroupOf (signalizerFixedSubgroup f)).Normal :=
      ⟨fun n hn g => by
        rw [Subgroup.mem_subgroupOf, Subgroup.mem_inf] at hn ⊢
        refine ⟨?_, by simpa using fixedFitting_conj_mem g.2 hn.2⟩
        simpa using (Subgroup.mem_normalizer_iff.mp (hC g.2) _).mp hn.1⟩
    have hbot : Y ⊓ fixedFitting f = ⊥ := by
      by_contra hne
      exact hC0Y ((h.minimal _ (inf_le_right.trans (fixedFitting_le f)) hnorm hne).trans
        inf_le_left)
    intro x hx hx'
    exact Subgroup.mem_bot.mp (hbot ▸ (⟨hx, hx'⟩ : x ∈ Y ⊓ fixedFitting f))
  have hYM : Y ≤ fixedNormalizer f := h.le_fixedNormalizer hY hC
  have hYZ : Y ≤ Subgroup.centralizer (fixedFitting f : Set X) := by
    intro y hy
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have h1 : k * y * k⁻¹ * y⁻¹ ∈ Y :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp (hC (fixedFitting_le f hk)) y).mp hy)
        (Subgroup.inv_mem _ hy)
    have h2 : k * y * k⁻¹ * y⁻¹ ∈ fixedFitting f := by
      have : y * k⁻¹ * y⁻¹ ∈ fixedFitting f :=
        (Subgroup.mem_normalizer_iff.mp (hYM hy) _).mp (Subgroup.inv_mem _ hk)
      simpa [mul_assoc] using Subgroup.mul_mem _ hk this
    have h3 := hYC0 _ h1 h2
    calc k * y = (k * y * k⁻¹ * y⁻¹) * (y * k) := by group
      _ = y * k := by rw [h3, one_mul]
  intro y hy
  obtain ⟨b, hb, a, ha, hyba⟩ := h.exists_mul_of_mem_centralizer (hYZ hy)
  have hord : (orderOf y).Coprime ℓ := by
    by_contra hnc
    have hdvd : ℓ ∣ orderOf y := by
      rwa [Nat.coprime_comm, Nat.Prime.coprime_iff_not_dvd h.prime_ℓ, not_not] at hnc
    have hx : orderOf (y ^ (orderOf y / ℓ)) = ℓ :=
      orderOf_pow_orderOf_div (orderOf_pos y).ne' hdvd
    have hxY : y ^ (orderOf y / ℓ) ∈ Y := Subgroup.pow_mem Y hy _
    have hxC0 : y ^ (orderOf y / ℓ) ∈ fixedFitting f :=
      h.mem_fixedFitting_of_orderOf (hYM hxY) (n := 1) (by rw [hx, pow_one])
    rw [hYC0 _ hxY hxC0, orderOf_one] at hx
    exact h.prime_ℓ.ne_one hx.symm
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp h.C0_pgroup
  have hcop : (Nat.card (fixedFitting f)).Coprime (orderOf y) := by
    rw [hn]
    exact (Nat.Coprime.pow_right n hord).symm
  have hb1 : b ^ Nat.card (fixedFitting f) = 1 :=
    congrArg Subtype.val (pow_card_eq_one' (x := (⟨b, hb⟩ : fixedFitting f)))
  have hbZ : b ∈ Subgroup.centralizer (fixedFitting f : Set X) :=
    h.fixedFitting_le_centralizer hb
  have haZ := FrameItems.autCommutator_centralizer_le f ha
  have hbaC : Commute b a := (commute_iff_eq _ _).mpr (setLike_mul_comm hbZ haZ)
  have hpow : y ^ Nat.card (fixedFitting f) = a ^ Nat.card (fixedFitting f) := by
    rw [hyba, hbaC.mul_pow, hb1, one_mul]
  have hmem : y ^ Nat.card (fixedFitting f) ∈
      autCommutator f (Subgroup.centralizer (fixedFitting f : Set X)) := by
    rw [hpow]
    exact Subgroup.pow_mem _ ha _
  by_cases hone : orderOf y = 1
  · rw [orderOf_eq_one_iff.mp hone]
    exact Subgroup.one_mem _
  · have hlt : 1 < orderOf y := by
      have := orderOf_pos y
      omega
    obtain ⟨u, -, hu⟩ := Nat.exists_mul_mod_eq_one_of_coprime hcop hlt
    have hyy : y = (y ^ Nat.card (fixedFitting f)) ^ u := by
      calc y = y ^ 1 := (pow_one y).symm
        _ = y ^ (Nat.card (fixedFitting f) * u % orderOf y) := by rw [hu]
        _ = y ^ (Nat.card (fixedFitting f) * u) := pow_mod_orderOf y _
        _ = (y ^ Nat.card (fixedFitting f)) ^ u := pow_mul y _ u
    rw [hyy]
    exact Subgroup.pow_mem _ hmem _

theorem Frame.autCommutator_fitting_eq [Finite X] {f : MulAut X} (h : Frame p ℓ f) :
    autCommutator f (CFSG.fittingSubgroupOf (fixedNormalizer f)) =
      autCommutator f (fixedNormalizer f) := by
  rw [h.fittingSubgroupOf_eq_centralizer]
  refine le_antisymm (Subgroup.closure_mono fun y ⟨x, hx, hy⟩ =>
    ⟨x, FrameItems.centralizer_le_fixedNormalizer f hx, hy⟩) ?_
  refine (Subgroup.closure_le _).mpr ?_
  rintro y ⟨x, hx, rfl⟩
  obtain ⟨z, hz, c, hc, rfl⟩ := h.normalizer_le x hx
  have hfc : f c = c := hc
  have e : (z * c)⁻¹ * f (z * c) = c⁻¹ * (z⁻¹ * f z) * c := by
    rw [map_mul, hfc]
    group
  rw [e]
  simpa using FrameItems.conj_mem_autCommutator (Subgroup.inv_mem _ hc)
    (Subgroup.subset_closure ⟨z, hz, rfl⟩)

theorem Frame.nilpotent_le_fitting [Finite X] {f : MulAut X} (h : Frame p ℓ f) (Y : Subgroup X)
    (hY : Group.IsNilpotent Y)
    (hC : signalizerFixedSubgroup f ≤ Subgroup.normalizer (Y : Set X)) :
    Y ≤ CFSG.fittingSubgroupOf (fixedNormalizer f) := by
  have hYtop : Y ≠ ⊤ := by
    intro htop
    rw [htop] at hY
    have : Group.IsNilpotent X := Group.nilpotent_of_mulEquiv Subgroup.topEquiv
    exact h.not_isSolvable inferInstance
  rw [h.fittingSubgroupOf_eq_centralizer]
  rcases h.invariant_subgroup Y hYtop hC with hC0Y | hYc
  · exact h.le_centralizer_of_nilpotent hY (h.le_fixedNormalizer hYtop hC) hC0Y
  · rw [h.fittingSubgroupOf_eq_centralizer] at hYc
    exact hYc.trans (FrameItems.autCommutator_centralizer_le f)

theorem Frame.conj_class [Finite X] {f : MulAut X} (h : Frame p ℓ f) (M' : Subgroup X)
    (hM' : Nonempty (M' ≃* fixedNormalizer f)) :
    ∃ g : X, M' = (fixedNormalizer f).map (MulAut.conj g).toMonoidHom := by
  obtain ⟨φ⟩ := hM'
  have := Fact.mk h.prime_ℓ
  have hC0M : fixedFitting f ≤ fixedNormalizer f :=
    (fixedFitting_le f).trans (fixed_le_fixedNormalizer f)
  have hC0norm : ((fixedFitting f).subgroupOf (fixedNormalizer f)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hC0M).mpr le_rfl
  let P' : Subgroup M' := ((fixedFitting f).subgroupOf (fixedNormalizer f)).map φ.symm.toMonoidHom
  have hP'norm : P'.Normal := hC0norm.map φ.symm.toMonoidHom φ.symm.surjective
  let P : Subgroup X := P'.map M'.subtype
  have hPM' : P ≤ M' := Subgroup.map_subtype_le P'
  have hPnorm : (P.subgroupOf M').Normal := by
    have : P.subgroupOf M' = P' := Subgroup.comap_map_eq_self_of_injective M'.subtype_injective P'
    rw [this]
    exact hP'norm
  have hM'P : M' ≤ Subgroup.normalizer (P : Set X) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hPM').mp hPnorm
  have hcardP : Nat.card P = Nat.card (fixedFitting f) := by
    calc Nat.card P = Nat.card P' := Subgroup.card_map_of_injective M'.subtype_injective
      _ = Nat.card ((fixedFitting f).subgroupOf (fixedNormalizer f)) :=
          Subgroup.card_map_of_injective φ.symm.injective
      _ = Nat.card (fixedFitting f) :=
          Nat.card_congr (Subgroup.subgroupOfEquivOfLe hC0M).toEquiv
  let S0 : Sylow ℓ X :=
    { toSubgroup := fixedFitting f
      isPGroup' := h.C0_pgroup
      is_maximal' := fun {Q} hQ hle => h.C0_sylow Q hQ hle }
  let SP : Sylow ℓ X := Sylow.ofCard P (hcardP.trans (Sylow.card_eq_multiplicity S0))
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq X S0 SP
  have hPeq : P = MulAut.conj g • fixedFitting f :=
    calc P = (SP : Subgroup X) := rfl
      _ = ((g • S0 : Sylow ℓ X) : Subgroup X) := by rw [hg]
      _ = MulAut.conj g • (S0 : Subgroup X) := Sylow.coe_subgroup_smul
      _ = MulAut.conj g • fixedFitting f := rfl
  have hPmem : ∀ y, y ∈ P ↔ g⁻¹ * y * g ∈ fixedFitting f := by
    intro y
    rw [hPeq, Subgroup.mem_pointwise_smul_iff_inv_smul_mem]
    simp
  have hle : M' ≤ (fixedNormalizer f).map (MulAut.conj g).toMonoidHom := by
    intro x hx
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * x * g, ?_, ?_⟩
    swap
    · simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      group
    refine Subgroup.mem_normalizer_iff.mpr fun k => ?_
    have h1 := hPmem (g * k * g⁻¹)
    have h2 := Subgroup.mem_normalizer_iff.mp (hM'P hx) (g * k * g⁻¹)
    have h3 := hPmem (x * (g * k * g⁻¹) * x⁻¹)
    have e1 : g⁻¹ * (g * k * g⁻¹) * g = k := by group
    have e2 : g⁻¹ * (x * (g * k * g⁻¹) * x⁻¹) * g = (g⁻¹ * x * g) * k * (g⁻¹ * x * g)⁻¹ := by
      group
    rw [e1] at h1
    rw [e2] at h3
    exact h1.symm.trans (h2.trans h3)
  refine ⟨g, Subgroup.eq_of_le_of_card_ge hle ?_⟩
  rw [Subgroup.card_map_of_injective (MulAut.conj g).injective]
  exact (Nat.card_congr φ.toEquiv).ge

end CFSG.SignalizerFunctorTheorem.McBride

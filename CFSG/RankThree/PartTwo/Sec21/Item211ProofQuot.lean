module

public import CFSG.RankThree.PartTwo.Sec21.Item211ProofTransport
public import CFSG.RankThree.PartTwo.Sec13.Item137Tools
import CFSG.RankThree.PartTwo.Sec13.Item13Theta
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
import CFSG.RankThree.PartTwo.Sec4.Census.Transfer
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.LocalAnalysis.SectionRank.PRank
public import CFSG.RankThree.PartTwo.Sec13.Item131Transport

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item211Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo

variable {G : Type} [Group G] [Finite G]

abbrev QuotX (L A : Subgroup G) : Type :=
  ↥(L ⊔ A) ⧸ aschbacherSolvableCore 3 ↥(L ⊔ A)

noncomputable abbrev piX (L A : Subgroup G) : ↥(L ⊔ A) →* QuotX L A :=
  QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(L ⊔ A))

noncomputable abbrev lOne (L A : Subgroup G) : Subgroup (QuotX L A) :=
  (L.subgroupOf (L ⊔ A)).map (piX L A)

noncomputable abbrev aOne (L A : Subgroup G) : Subgroup (QuotX L A) :=
  (A.subgroupOf (L ⊔ A)).map (piX L A)

variable {L A : Subgroup G}

omit [Finite G] in
theorem normal_subgroupOf (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    (L.subgroupOf (L ⊔ A)).Normal :=
  (Subgroup.normal_subgroupOf_iff_le_normalizer le_sup_left).mpr
    (sup_le Subgroup.le_normalizer hAL)

omit [Finite G] in
theorem normal_lOne (hAL : A ≤ Subgroup.normalizer (L : Set G)) : (lOne L A).Normal :=
  (normal_subgroupOf hAL).map _ (QuotientGroup.mk'_surjective _)

omit [Finite G] in
theorem mem_normalizer_lOne (hAL : A ≤ Subgroup.normalizer (L : Set G)) (x : QuotX L A) :
    x ∈ Subgroup.normalizer ((lOne L A : Subgroup (QuotX L A)) : Set (QuotX L A)) := by
  rw [(Subgroup.normalizer_eq_top_iff).mpr (normal_lOne hAL)]
  exact Subgroup.mem_top x

theorem theta_le_subgroupOf (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    aschbacherSolvableCore 3 ↥(L ⊔ A) ≤ L.subgroupOf (L ⊔ A) := by
  have := normal_subgroupOf hAL
  set N := L.subgroupOf (L ⊔ A) with hN
  have hpg : IsPGroup 3 (↥(L ⊔ A) ⧸ N) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x =>
      have hx : (x : G) ∈ ((L ⊔ A : Subgroup G) : Set G) := x.2
      rw [Subgroup.coe_mul_of_right_le_normalizer_left L A hAL] at hx
      obtain ⟨l, hl, a, ha, hla⟩ := hx
      obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
      refine ⟨k, ?_⟩
      have heq : (QuotientGroup.mk x : ↥(L ⊔ A) ⧸ N) =
          QuotientGroup.mk ⟨a, Subgroup.mem_sup_right ha⟩ := by
        rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
        change (x : G)⁻¹ * a ∈ L
        rw [← hla]
        have h1 : (l * a)⁻¹ * a = a⁻¹ * l⁻¹ * a⁻¹⁻¹ := by group
        rw [h1]
        exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hAL ha)) l⁻¹).mp
          (L.inv_mem hl)
      rw [heq, ← QuotientGroup.mk_pow]
      have h3 : (⟨a, Subgroup.mem_sup_right ha⟩ : ↥(L ⊔ A)) ^ 3 ^ k = 1 := by
        apply Subtype.ext
        have := congrArg Subtype.val hk
        simpa using this
      rw [h3, QuotientGroup.mk_one]
  intro t ht
  have hθ3 : ¬ 3 ∣ Nat.card (aschbacherSolvableCore 3 ↥(L ⊔ A)) :=
    (solvable_prime_complement_core_characterization (H := ↥(L ⊔ A)) Nat.prime_three).2.2.1
  have hcop : Nat.Coprime (orderOf t) 3 := by
    have h1 : orderOf t ∣ Nat.card (aschbacherSolvableCore 3 ↥(L ⊔ A)) := by
      have := orderOf_dvd_natCard (⟨t, ht⟩ : aschbacherSolvableCore 3 ↥(L ⊔ A))
      rwa [Subgroup.orderOf_mk] at this
    exact Nat.Coprime.coprime_dvd_left h1
      (Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hθ3))
  obtain ⟨j, hj⟩ := hpg (QuotientGroup.mk t)
  have h1 : orderOf (QuotientGroup.mk t : ↥(L ⊔ A) ⧸ N) ∣ orderOf t :=
    orderOf_map_dvd (QuotientGroup.mk' N) t
  have h2 : orderOf (QuotientGroup.mk t : ↥(L ⊔ A) ⧸ N) ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hj
  have h3 : orderOf (QuotientGroup.mk t : ↥(L ⊔ A) ⧸ N) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_right j hcop)) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

theorem inSubgroup_theta_sup (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    inSubgroup (aschbacherSolvableCore 3) (L ⊔ A) = inSubgroup (aschbacherSolvableCore 3) L := by
  have := normal_subgroupOf hAL
  set LM := L.subgroupOf (L ⊔ A) with hLMdef
  have h1 := aschbacherSolvableCore_eq_subgroupOf Nat.prime_three
    ((normal_subgroupOf hAL).isSubnormal : LM.IsSubnormal)
  have h2 : aschbacherSolvableCore 3 ↥(L ⊔ A) = (aschbacherSolvableCore 3 LM).map LM.subtype := by
    rw [h1, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr (theta_le_subgroupOf hA hAL)]
  have hLM : LM.map (L ⊔ A).subtype = L := by
    rw [hLMdef, Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr le_sup_left]
  calc inSubgroup (aschbacherSolvableCore 3) (L ⊔ A)
      = (inSubgroup (aschbacherSolvableCore 3) LM).map (L ⊔ A).subtype := by
        rw [inSubgroup, h2]
        rfl
    _ = inSubgroup (aschbacherSolvableCore 3) (LM.map (L ⊔ A).subtype) :=
        (inSubgroup_theta_map_subtype LM).symm
    _ = inSubgroup (aschbacherSolvableCore 3) L := by rw [hLM]

theorem exists_lEquiv (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    ∃ Φ₀ : lBar L ≃* lOne L A, ∀ l : L,
      (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩ := by
  have := normal_subgroupOf hAL
  set LM := L.subgroupOf (L ⊔ A) with hLMdef
  obtain ⟨η, hη⟩ := exists_thetaQuotient_mulEquiv_map Nat.prime_three
    ((normal_subgroupOf hAL).isSubnormal : LM.IsSubnormal)
  set e1 : L ≃* LM := (Subgroup.subgroupOfEquivOfLe (le_sup_left : L ≤ L ⊔ A)).symm with he1
  let e2 : lBar L ≃* LM ⧸ aschbacherSolvableCore 3 LM :=
    QuotientGroup.congr _ _ e1 (aschbacherSolvableCore_map_mulEquiv Nat.prime_three e1)
  refine ⟨e2.trans η, fun l => ?_⟩
  rw [MulEquiv.trans_apply]
  have he2 : e2 (l : lBar L) = ((e1 l : LM) : LM ⧸ aschbacherSolvableCore 3 LM) := rfl
  rw [he2, hη]
  rfl

theorem theta_lOne_eq_bot (Φ₀ : lBar L ≃* lOne L A) :
    aschbacherSolvableCore 3 ↥(lOne L A) = ⊥ := by
  have h1 : aschbacherSolvableCore 3 (lBar L) = ⊥ := (theta_quotient_core_and_ranks (G := ↥L)).1
  rw [← aschbacherSolvableCore_map_mulEquiv Nat.prime_three Φ₀, h1, Subgroup.map_bot]

@[expose] noncomputable def lEquivTheta (Φ₀ : lBar L ≃* lOne L A) :
    lBar L ≃* ↥(lOne L A) ⧸ aschbacherSolvableCore 3 ↥(lOne L A) :=
  Φ₀.trans ((QuotientGroup.quotientBot (G := ↥(lOne L A))).symm.trans
    (QuotientGroup.quotientMulEquivOfEq (theta_lOne_eq_bot Φ₀).symm))

theorem lEquivTheta_apply (Φ₀ : lBar L ≃* lOne L A) (z : lBar L) :
    lEquivTheta Φ₀ z =
      ((Φ₀ z : lOne L A) : ↥(lOne L A) ⧸ aschbacherSolvableCore 3 ↥(lOne L A)) :=
  rfl

theorem lEquiv_conj {Φ₀ : lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {a : G} (haA : a ∈ A) (ha : a ∈ Subgroup.normalizer (L : Set G))
    (ha₁ : piX L A ⟨a, Subgroup.mem_sup_right haA⟩ ∈
      Subgroup.normalizer ((lOne L A : Subgroup (QuotX L A)) : Set (QuotX L A)))
    (z : lBar L) :
    Φ₀ (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, ha⟩) z) =
      (lOne L A).normalizerMonoidHom ⟨_, ha₁⟩ (Φ₀ z) := by
  induction z using QuotientGroup.induction_on with
  | H l =>
    apply Subtype.ext
    have hR : (((lOne L A).normalizerMonoidHom ⟨_, ha₁⟩ (Φ₀ (l : lBar L)) : lOne L A) :
        QuotX L A) = piX L A ⟨a, Subgroup.mem_sup_right haA⟩ *
          piX L A ⟨l, Subgroup.mem_sup_left l.2⟩ * (piX L A ⟨a, Subgroup.mem_sup_right haA⟩)⁻¹ := by
      rw [Sec4.normalizerMonoidHom_apply_coe, hΦ₀]
    rw [hR, Sec4.thetaQuotMulAut_mk, hΦ₀, ← map_inv, ← map_mul, ← map_mul]
    rfl

theorem lEquivTheta_conj {Φ₀ : lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {a : G} (haA : a ∈ A) (ha : a ∈ Subgroup.normalizer (L : Set G))
    (ha₁ : piX L A ⟨a, Subgroup.mem_sup_right haA⟩ ∈
      Subgroup.normalizer ((lOne L A : Subgroup (QuotX L A)) : Set (QuotX L A)))
    (z : lBar L) :
    lEquivTheta Φ₀ (Sec4.thetaQuotMulAut L (L.normalizerMonoidHom ⟨a, ha⟩) z) =
      Sec4.thetaQuotMulAut (lOne L A) ((lOne L A).normalizerMonoidHom ⟨_, ha₁⟩)
        (lEquivTheta Φ₀ z) := by
  rw [lEquivTheta_apply, lEquivTheta_apply, lEquiv_conj hΦ₀ haA ha ha₁ z,
    Sec4.thetaQuotMulAut_mk]

omit [Finite G] in
theorem piX_mem_aOne {a : G} (haA : a ∈ A) :
    piX L A ⟨a, Subgroup.mem_sup_right haA⟩ ∈ aOne L A :=
  ⟨⟨a, Subgroup.mem_sup_right haA⟩, Subgroup.mem_subgroupOf.mpr haA, rfl⟩

omit [Finite G] in
theorem exists_eq_piX_of_mem_aOne {x : QuotX L A} (hx : x ∈ aOne L A) :
    ∃ (a : G) (haA : a ∈ A), x = piX L A ⟨a, Subgroup.mem_sup_right haA⟩ := by
  obtain ⟨a', ha', rfl⟩ := hx
  exact ⟨a', Subgroup.mem_subgroupOf.mp ha', rfl⟩

theorem inducesStdKind_of_lOne
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) {Φ₀ : lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    {a : G} (haA : a ∈ A) {k : KFacts.AutKind}
    (h : KFacts.InducesStdKind (lOne L A) (piX L A ⟨a, Subgroup.mem_sup_right haA⟩) k) :
    KFacts.InducesStdKind L a k :=
  inducesStdKind_of_intertwine (lEquivTheta Φ₀) (hAL haA)
    (fun ha₁ z => lEquivTheta_conj hΦ₀ haA (hAL haA) ha₁ z) h

theorem isTypeCOn_of_lOne (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {Φ₀ : lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    (h : Sec4.IsTypeCOn (aOne L A) (lOne L A)) : Sec4.IsTypeCOn A L := by
  refine isTypeCOn_of_intertwine (lEquivTheta Φ₀) (fun τ hτ => ?_) (fun τ₁ hτ₁ => ?_) h
  · obtain ⟨a, ha, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    have ha₁ := mem_normalizer_lOne hAL (piX L A ⟨a, Subgroup.mem_sup_right haA⟩)
    exact ⟨_, Sec4.mem_autThetaQuot_iff.mpr ⟨_, ha₁, piX_mem_aOne haA, rfl⟩,
      fun z => lEquivTheta_conj hΦ₀ haA ha ha₁ z⟩
  · obtain ⟨x, hx, hxA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ₁
    obtain ⟨a, haA, rfl⟩ := exists_eq_piX_of_mem_aOne hxA
    exact ⟨_, Sec4.mem_autThetaQuot_iff.mpr ⟨a, hAL haA, haA, rfl⟩,
      fun z => lEquivTheta_conj hΦ₀ haA (hAL haA) hx z⟩

theorem isTypeCOnBarSL_of_lOne (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {Φ₀ : lBar L ≃* lOne L A}
    (hΦ₀ : ∀ l : L, (Φ₀ (l : lBar L) : QuotX L A) = piX L A ⟨l, Subgroup.mem_sup_left l.2⟩)
    (h : Sec4.IsTypeCOnSL (aOne L A) (lOne L A)) : IsTypeCOnBarSL A L := by
  refine isTypeCOnBarSL_of_intertwine Φ₀ (fun τ hτ => ?_) (fun x hxA hx => ?_) h
  · obtain ⟨a, ha, haA, rfl⟩ := Sec4.mem_autThetaQuot_iff.mp hτ
    have ha₁ := mem_normalizer_lOne hAL (piX L A ⟨a, Subgroup.mem_sup_right haA⟩)
    exact ⟨_, piX_mem_aOne haA, ha₁, fun z => lEquiv_conj hΦ₀ haA ha ha₁ z⟩
  · obtain ⟨a, haA, rfl⟩ := exists_eq_piX_of_mem_aOne hxA
    exact ⟨_, Sec4.mem_autThetaQuot_iff.mpr ⟨a, hAL haA, haA, rfl⟩,
      fun z => lEquiv_conj hΦ₀ haA (hAL haA) hx z⟩

omit [Finite G] in
theorem isPGroup_subgroupOf (hA : IsPGroup 3 A) : IsPGroup 3 (A.subgroupOf (L ⊔ A)) :=
  hA.comap_of_injective (L ⊔ A).subtype (L ⊔ A).subtype_injective

@[expose] noncomputable def aEquiv (hA : IsPGroup 3 A) : ↥A ≃* ↥(aOne L A) :=
  (Subgroup.subgroupOfEquivOfLe (le_sup_right : A ≤ L ⊔ A)).symm.trans
    (Sec13.mkEquivOfIsPGroup (isPGroup_subgroupOf (L := L) hA))

theorem aEquiv_apply (hA : IsPGroup 3 A) (a : A) :
    (aEquiv (L := L) hA a : QuotX L A) = piX L A ⟨a, Subgroup.mem_sup_right a.2⟩ :=
  rfl

theorem autIn_eq_starOf {G : Type*} [Group G] (A L : Subgroup G) :
    Sec4.autIn L A = starOf A L := by
  rw [Sec4.autIn, starOf, Subgroup.inf_subgroupOf_right]

theorem map_autIn_lOne (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    (Sec4.autIn (L.subgroupOf (L ⊔ A)) (A.subgroupOf (L ⊔ A))).map
        (MulAut.congr (Sec13.mkEquivOfIsPGroup (isPGroup_subgroupOf (L := L) hA))).toMonoidHom =
      Sec4.autIn (lOne L A) (aOne L A) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hAM := isPGroup_subgroupOf (L := L) hA
  have : Fact (IsPGroup 3 (A.subgroupOf (L ⊔ A))) := ⟨hAM⟩
  set N := aschbacherSolvableCore 3 ↥(L ⊔ A) with hNdef
  set π := QuotientGroup.mk' N with hπ
  set AM := A.subgroupOf (L ⊔ A) with hAMdef
  set LM := L.subgroupOf (L ⊔ A) with hLMdef
  set e := Sec13.mkEquivOfIsPGroup hAM with he
  have hcop : Nat.Coprime 3 (Nat.card N) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
      (solvable_prime_complement_core_characterization (H := ↥(L ⊔ A)) Nat.prime_three).2.2.1
  have hNorm : Subgroup.normalizer ((AM.map π : Subgroup _) : Set _) =
      (Subgroup.normalizer (AM : Set ↥(L ⊔ A))).map π :=
    CFSG.normalizer_map_quotient_eq_map_normalizer 3 AM N inferInstance hcop
  have hcongr : ∀ (h : ↥(L ⊔ A)) (hh : h ∈ Subgroup.normalizer (AM : Set ↥(L ⊔ A)))
      (hh' : π h ∈ Subgroup.normalizer ((AM.map π : Subgroup _) : Set _)),
      MulAut.congr e (AM.normalizerMonoidHom ⟨h, hh⟩) =
        (AM.map π).normalizerMonoidHom ⟨π h, hh'⟩ := by
    intro h hh hh'
    ext y
    obtain ⟨x, rfl⟩ := e.surjective y
    change ((e (AM.normalizerMonoidHom ⟨h, hh⟩ (e.symm (e x))) : _) : QuotX L A) =
      π h * (e x : QuotX L A) * (π h)⁻¹
    rw [MulEquiv.symm_apply_apply, he, Sec13.mkEquivOfIsPGroup_apply,
      Sec13.mkEquivOfIsPGroup_apply, Sec4.normalizerMonoidHom_apply_coe, map_mul, map_mul,
      map_inv]
  have hθL := theta_le_subgroupOf hA hAL
  ext σ
  constructor
  · rintro ⟨τ, hτ, rfl⟩
    obtain ⟨h, hh, hL, rfl⟩ := Sec4.mem_autIn_iff.mp hτ
    have hh' : π h ∈ Subgroup.normalizer ((AM.map π : Subgroup _) : Set _) := by
      rw [hNorm]
      exact Subgroup.mem_map_of_mem π hh
    exact Sec4.mem_autIn_iff.mpr ⟨π h, hh', Subgroup.mem_map_of_mem π hL,
      (hcongr h hh hh').symm⟩
  · intro hσ
    obtain ⟨g, hg, hgL, rfl⟩ := Sec4.mem_autIn_iff.mp hσ
    have hg' := hg
    rw [hNorm] at hg'
    obtain ⟨h, hh, rfl⟩ := hg'
    have hhL : h ∈ LM := by
      obtain ⟨l, hl, hlh⟩ := hgL
      have hlt : l⁻¹ * h ∈ N := by
        rw [← QuotientGroup.eq]
        exact hlh
      have := LM.mul_mem hl (hθL hlt)
      simpa using this
    exact ⟨AM.normalizerMonoidHom ⟨h, hh⟩, Sec4.mem_autIn_iff.mpr ⟨h, hh, hhL, rfl⟩,
      hcongr h hh hg⟩

theorem nonempty_autIn_lOne_equiv (hA : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    Nonempty (Sec4.autIn (lOne L A) (aOne L A) ≃* starOf A L) := by
  obtain ⟨e₂⟩ := Sec13.nonempty_autIn_subgroupOf_equiv (L ⊔ A) (le_sup_left : L ≤ L ⊔ A)
    (le_sup_right : A ≤ L ⊔ A)
  let e₁ : Sec4.autIn (L.subgroupOf (L ⊔ A)) (A.subgroupOf (L ⊔ A)) ≃*
      Sec4.autIn (lOne L A) (aOne L A) :=
    ((Sec4.autIn (L.subgroupOf (L ⊔ A)) (A.subgroupOf (L ⊔ A))).equivMapOfInjective _
      (MulAut.congr (Sec13.mkEquivOfIsPGroup (isPGroup_subgroupOf (L := L) hA))).injective).trans
      (MulEquiv.subgroupCongr (map_autIn_lOne hA hAL))
  exact ⟨e₁.symm.trans (e₂.trans (MulEquiv.subgroupCongr (autIn_eq_starOf A L)))⟩

theorem nonempty_quotX_equiv_lBarA {c : G} (hLc : L ∈ thetaComponentsAt 3 c)
    (hAC : A ≤ Subgroup.centralizer ({c} : Set G)) (hA : IsPGroup 3 A)
    (hAL : A ≤ Subgroup.normalizer (L : Set G)) :
    Nonempty (QuotX L A ≃* ↥(Sec13.lBarA c L A)) := by
  set C := Subgroup.centralizer ({c} : Set G) with hC
  set H := Subgroup.normalizer ((Subgroup.zpowers c : Subgroup G) : Set G) with hH
  have hLC : L ≤ C := Sec6.le_centralizer_of_mem_thetaComponentsAt hLc
  have hCH : C ≤ H := Sec13.centralizer_le_normalizer_zpowers c
  have hXH : L ⊔ A ≤ H := (sup_le hLC hAC).trans hCH
  have hθ := Sec13.inSubgroup_theta_centralizer c
  have hθLA := inSubgroup_theta_sup hA hAL
  have hθLC := theta_le_theta_centralizer hLc
  obtain ⟨e⟩ := Sec13.nonempty_map_mk_equiv (le_refl (L ⊔ A)) hXH
    (aschbacherSolvableCore 3 ↥(L ⊔ A)) (aschbacherSolvableCore 3 H) (fun x => by
      constructor
      · intro hx
        have h1 : (x : G) ∈ inSubgroup (aschbacherSolvableCore 3) (L ⊔ A) := ⟨_, hx, rfl⟩
        rw [hθLA] at h1
        have h2 := hθLC h1
        rw [hθ] at h2
        obtain ⟨y, hy, hyx⟩ := h2.2
        have : y = Subgroup.inclusion hXH x := Subtype.ext hyx
        rw [← this]
        exact hy
      · intro hx
        have h1 : (x : G) ∈ inSubgroup (aschbacherSolvableCore 3) H := ⟨_, hx, rfl⟩
        obtain ⟨y, hy, hyx⟩ := Sec13.inf_inSubgroup_theta_le hXH ⟨x.2, h1⟩
        have : y = Subgroup.inclusion (le_refl (L ⊔ A)) x := Subtype.ext hyx
        rw [← this]
        exact hy)
  have htop : ((L ⊔ A).subgroupOf (L ⊔ A)).map
      (QuotientGroup.mk' (aschbacherSolvableCore 3 ↥(L ⊔ A))) = ⊤ := by
    rw [Subgroup.subgroupOf_self, ← MonoidHom.range_eq_map, MonoidHom.range_eq_top]
    exact QuotientGroup.mk'_surjective _
  exact ⟨Subgroup.topEquiv.symm.trans ((MulEquiv.subgroupCongr htop.symm).trans e)⟩

theorem pCore_two_quotX : CFSG.pCore 2 (QuotX L A) = ⊥ := by
  have h1 : aschbacherSolvableCore 3 (QuotX L A) = ⊥ :=
    (theta_quotient_core_and_ranks (G := ↥(L ⊔ A))).1
  have h2 := (solvable_prime_complement_core_characterization (H := QuotX L A)
    Nat.prime_three).2.2.2.2.2.2 2 Nat.prime_two (by norm_num)
  rw [h1] at h2
  exact le_bot_iff.mp h2

omit [Finite G] in
theorem isComponent_lOne (hAL : A ≤ Subgroup.normalizer (L : Set G)) (Φ₀ : lBar L ≃* lOne L A)
    (hq : IsQuasisimple (lBar L)) : IsComponent (lOne L A) :=
  ⟨LocalCores.isQuasisimple_of_mulEquiv Φ₀ hq, (normal_lOne hAL).isSubnormal⟩

omit [Finite G] in
theorem mem_lOne_of_coprime (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    (x : QuotX L A) (hx : ¬ 3 ∣ orderOf x) : x ∈ lOne L A := by
  have := normal_lOne hAL
  set N := lOne L A with hN
  have hpg : IsPGroup 3 (QuotX L A ⧸ N) := by
    intro y
    induction y using QuotientGroup.induction_on with
    | H x' =>
      induction x' using QuotientGroup.induction_on with
      | H g =>
        have hg : (g : G) ∈ ((L ⊔ A : Subgroup G) : Set G) := g.2
        rw [Subgroup.coe_mul_of_right_le_normalizer_left L A hAL] at hg
        obtain ⟨l, hl, a, ha, hla⟩ := hg
        obtain ⟨k, hk⟩ := hA ⟨a, ha⟩
        refine ⟨k, ?_⟩
        have heq : (QuotientGroup.mk (QuotientGroup.mk g : QuotX L A) : QuotX L A ⧸ N) =
            QuotientGroup.mk (piX L A ⟨a, Subgroup.mem_sup_right ha⟩) := by
          rw [QuotientGroup.eq]
          refine ⟨g⁻¹ * ⟨a, Subgroup.mem_sup_right ha⟩, ?_, ?_⟩
          · rw [SetLike.mem_coe, Subgroup.mem_subgroupOf]
            change (g : G)⁻¹ * a ∈ L
            rw [← hla]
            have h1 : (l * a)⁻¹ * a = a⁻¹ * l⁻¹ * a⁻¹⁻¹ := by group
            rw [h1]
            exact (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ (hAL ha)) l⁻¹).mp
              (L.inv_mem hl)
          · rw [map_mul, map_inv]
            rfl
        rw [heq, ← QuotientGroup.mk_pow, ← map_pow]
        have h3 : (⟨a, Subgroup.mem_sup_right ha⟩ : ↥(L ⊔ A)) ^ 3 ^ k = 1 := by
          apply Subtype.ext
          have := congrArg Subtype.val hk
          simpa using this
        rw [h3, map_one, QuotientGroup.mk_one]
  obtain ⟨j, hj⟩ := hpg (QuotientGroup.mk x)
  have h1 : orderOf (QuotientGroup.mk x : QuotX L A ⧸ N) ∣ orderOf x :=
    orderOf_map_dvd (QuotientGroup.mk' N) x
  have hcop : Nat.Coprime (orderOf x) 3 :=
    Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hx)
  have h2 : orderOf (QuotientGroup.mk x : QuotX L A ⧸ N) ∣ 3 ^ j := orderOf_dvd_of_pow_eq_one hj
  have h3 : orderOf (QuotientGroup.mk x : QuotX L A ⧸ N) = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_right j hcop)) h2
  rw [orderOf_eq_one_iff, QuotientGroup.eq_one_iff] at h3
  exact h3

omit [Finite G] in
theorem isElemAbelian_subgroupOf {Y : Type*} [Group Y] {p : ℕ} {E K : Subgroup Y}
    (hE : CFSG.Assembly.IsElemAbelian p E) : CFSG.Assembly.IsElemAbelian p (E.subgroupOf K) :=
  CFSG.Open.IsElemAbelian.subgroupOf hE K

theorem localRank_le_of_forall_mem {Y : Type} [Group Y] [Finite Y] (K : Subgroup Y)
    (hK : ∀ y : Y, ¬ 3 ∣ orderOf y → y ∈ K) {r : ℕ} (hr : r.Prime) (hr3 : r ≠ 3) :
    CFSG.Assembly.RankThreeEven.localRank r Y ≤ CFSG.Assembly.RankThreeEven.localRank r K := by
  apply csSup_le'
  rintro k ⟨H, ⟨P, hP1, hP2, rfl⟩, rfl⟩
  obtain ⟨E, hEH, hE, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank hr.one_lt (Subgroup.normalizer (P : Set Y))
  have hPK : P ≤ K := fun x hx => hK x (by
    obtain ⟨n, hn⟩ := hP2 ⟨x, hx⟩
    have h1 : orderOf x ∣ 2 ^ n := by
      have := orderOf_dvd_of_pow_eq_one (congrArg Subtype.val hn)
      simpa using this
    intro h3
    have := (Nat.prime_three.dvd_of_dvd_pow (h3.trans h1))
    omega)
  have hEK : E ≤ K := fun x hx => hK x (by
    have h1 : orderOf x ∣ r := orderOf_dvd_of_pow_eq_one (hE.2 x hx)
    intro h3
    have := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hr).mp (h3.trans h1)
    omega)
  set P' := P.subgroupOf K with hP'
  set E' := E.subgroupOf K with hE'
  have hP'1 : P' ≠ ⊥ := by
    intro h0
    apply hP1
    rw [Subgroup.subgroupOf_eq_bot] at h0
    exact (disjoint_iff.mp h0 ▸ (inf_eq_left.mpr hPK)).symm
  have hP'2 : IsPGroup 2 P' := hP2.comap_of_injective K.subtype K.subtype_injective
  have hE'N : E' ≤ Subgroup.normalizer (P' : Set K) := by
    intro x hx
    rw [Subgroup.mem_normalizer_iff]
    intro y
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf]
    exact Subgroup.mem_normalizer_iff.mp (hEH (Subgroup.mem_subgroupOf.mp hx)) y
  have hE'e : CFSG.Open.IsElemAbelian r E' :=
    ⟨(isElemAbelian_subgroupOf (K := K) (⟨hE.1, hE.2⟩ : CFSG.Assembly.IsElemAbelian r E)).1,
      (isElemAbelian_subgroupOf (K := K) (⟨hE.1, hE.2⟩ : CFSG.Assembly.IsElemAbelian r E)).2⟩
  have hE'card : Nat.card E' = r ^ CFSG.Open.pRank r (Subgroup.normalizer (P : Set Y)) := by
    rw [hE', ← Subgroup.card_map_of_injective K.subtype_injective, Subgroup.subgroupOf_map_subtype,
      inf_eq_left.mpr hEK, hEcard]
  have h1 := CFSG.SectionRank.le_pRank hr.one_lt hE'N hE'e hE'card
  exact h1.trans (CFSG.RankThreeEvenClassification.Helpers.pRank_le_twoLocalRank r hr _
    ⟨P', hP'1, hP'2, rfl⟩)

theorem sectionFourHyp_quotX (h1 : Sec4.Item4_1LargePrime) (hΛ : SectionFourHyp ↥(L ⊔ A))
    (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G)) (Φ₀ : lBar L ≃* lOne L A)
    (hq : IsQuasisimple (lBar L)) : SectionFourHyp (QuotX L A) := by
  have := normal_subgroupOf hAL
  set LM := L.subgroupOf (L ⊔ A) with hLM
  obtain ⟨η, -⟩ := exists_thetaQuotient_mulEquiv_map Nat.prime_three
    ((normal_subgroupOf hAL).isSubnormal : LM.IsSubnormal)
  have hqLM : IsQuasisimple (LM ⧸ aschbacherSolvableCore 3 LM) :=
    LocalCores.isQuasisimple_of_mulEquiv (η.trans Φ₀.symm).symm hq
  have hS : SectionFourHyp (LM ⧸ aschbacherSolvableCore 3 LM) :=
    Sec4.Item41Narrow.sectionFourHyp_section h1 hΛ LM _ three_not_dvd_card_aschbacherSolvableCore
      hqLM
  have hlt1 : ∀ p : ℕ, p.Prime → 3 < p →
      CFSG.Assembly.RankThreeEven.localRank p ↥(lOne L A) < 3 := fun p hp hp3 => by
    rw [← Census.localRank_eq_of_mulEquiv η hp]
    exact hS.localRank_lt p hp hp3
  have hlt : ∀ p : ℕ, p.Prime → 3 < p →
      CFSG.Assembly.RankThreeEven.localRank p (QuotX L A) < 3 := fun p hp hp3 =>
    (localRank_le_of_forall_mem (lOne L A) (mem_lOne_of_coprime hA hAL) hp (by omega)).trans_lt
      (hlt1 p hp hp3)
  refine ⟨CFSG.SectionRank.K_group_section_closure_inCatalog hΛ.kGroup ⊤ _
      (Sec4.Item41Narrow.quotientTopEquiv (aschbacherSolvableCore 3 ↥(L ⊔ A))),
    Sec4.Census.evenRank_le_of_localRank_le fun p hp hp2 => ?_, hlt⟩
  rcases (show p = 3 ∨ 3 < p by have := hp.two_le; omega) with rfl | hp3
  · exact (theta_quotient_core_and_ranks (G := ↥(L ⊔ A))).2.2.1.2.1.trans
      ((OddKernel.localRank_le_evenRank Nat.prime_three (by norm_num)).trans hΛ.evenRank_le)
  · exact (hlt p hp hp3).le.trans (by norm_num)

theorem exists_lift_of_le {T : Subgroup ↥(L ⊔ A)} (hT : IsPGroup 3 T)
    {B : Subgroup (QuotX L A)} (hB : CFSG.Assembly.IsElemAbelian 3 B)
    (hTB : T.map (piX L A) ≤ B) :
    ∃ S : Subgroup ↥(L ⊔ A), T ≤ S ∧ S.map (piX L A) = B ∧ Nat.card S = Nat.card B ∧
      CFSG.Assembly.IsElemAbelian 3 S := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N := aschbacherSolvableCore 3 ↥(L ⊔ A) with hNdef
  have hN : ¬ 3 ∣ Nat.card N := three_not_dvd_card_aschbacherSolvableCore
  have hBp : IsPGroup 3 B := fun x => ⟨1, Subtype.ext (by
    rw [pow_one, Subgroup.coe_pow, OneMemClass.coe_one]
    exact hB.2 _ x.2)⟩
  obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hBp
  set P : Subgroup ↥(L ⊔ A) := B.comap (piX L A) with hP
  have hPcard : Nat.card P = Nat.card N * 3 ^ k := by
    rw [← hk]
    exact QuotientGroup.card_preimage_mk N (B : Set (QuotX L A))
  have hTP : T ≤ P := fun t ht => hTB ⟨t, ht, rfl⟩
  have hT' : IsPGroup 3 (T.subgroupOf P) := hT.comap_of_injective P.subtype P.subtype_injective
  obtain ⟨Q, hQ⟩ := hT'.exists_le_sylow
  have hQcard : Nat.card Q = 3 ^ k := by
    rw [Sylow.card_eq_multiplicity, hPcard, Nat.factorization_mul (Nat.card_pos.ne')
      (pow_ne_zero _ (by norm_num)), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hN, Nat.Prime.factorization_pow Nat.prime_three,
      Finsupp.single_eq_same, zero_add]
  set S : Subgroup ↥(L ⊔ A) := (Q : Subgroup P).map P.subtype with hS
  have hScard : Nat.card S = 3 ^ k := by
    rw [hS, Subgroup.card_map_of_injective Subtype.val_injective, hQcard]
  have hdisj : Disjoint S N := Subgroup.disjoint_of_coprime_natCard (by
    rw [hScard]
    exact Nat.Coprime.pow_left k ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).2 hN))
  have hSP : S ≤ P := Subgroup.map_subtype_le _
  have hinj : ∀ a b, a ∈ S → b ∈ S → piX L A a = piX L A b → a = b := by
    intro a b ha hb hab
    have h1 : b⁻¹ * a ∈ N := by
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq] at hab
      have := N.inv_mem hab
      rwa [mul_inv_rev, inv_inv] at this
    have h2 : b⁻¹ * a ∈ S ⊓ N := ⟨S.mul_mem (S.inv_mem hb) ha, h1⟩
    rw [hdisj.eq_bot, Subgroup.mem_bot] at h2
    exact (eq_of_inv_mul_eq_one h2).symm
  have hTS : T ≤ S := fun t ht => ⟨⟨t, hTP ht⟩, hQ (Subgroup.mem_subgroupOf.mpr ht), rfl⟩
  have hSB : S.map (piX L A) ≤ B := by
    rintro _ ⟨s, hs, rfl⟩
    exact hSP hs
  have hfinj : Function.Injective ((piX L A).comp S.subtype) := fun a b h =>
    Subtype.ext (hinj _ _ a.2 b.2 h)
  have hrange : ((piX L A).comp S.subtype).range = S.map (piX L A) := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  have hmapcard : Nat.card (S.map (piX L A)) = Nat.card S := by
    rw [← hrange]
    exact (Nat.card_congr (MonoidHom.ofInjective hfinj).toEquiv).symm
  have hSBeq : S.map (piX L A) = B :=
    Subgroup.eq_of_le_of_card_ge hSB (by rw [hmapcard, hScard, hk])
  refine ⟨S, hTS, hSBeq, by rw [hScard, hk], ⟨⟨⟨fun a b => Subtype.ext ?_⟩⟩, fun x hx => ?_⟩⟩
  · refine hinj _ _ (S.mul_mem a.2 b.2) (S.mul_mem b.2 a.2) ?_
    rw [Subgroup.coe_mul, Subgroup.coe_mul, map_mul, map_mul]
    have ha : piX L A a ∈ B := hSP a.2
    have hb : piX L A b ∈ B := hSP b.2
    exact congrArg Subtype.val (hB.1.is_comm.comm (⟨_, ha⟩ : B) ⟨_, hb⟩)
  · refine hinj _ _ (S.pow_mem hx 3) S.one_mem ?_
    rw [map_pow, map_one]
    exact hB.2 _ (hSP hx)

omit [Finite G] in
theorem isElemAbelian_map_subtype {S : Subgroup ↥(L ⊔ A)}
    (hS : CFSG.Assembly.IsElemAbelian 3 S) :
    CFSG.Assembly.IsElemAbelian 3 (S.map (L ⊔ A).subtype) := CFSG.Open.IsElemAbelian.map hS _

theorem maximal_aOne (hAe : CFSG.Assembly.IsElemAbelian 3 A)
    (hAmax : ∀ B : Subgroup G, CFSG.Assembly.IsElemAbelian 3 B → A ≤ B → B = A) :
    Maximal (fun B : Subgroup (QuotX L A) => CFSG.Assembly.IsElemAbelian 3 B) (aOne L A) := by
  have hA : IsPGroup 3 A := fun a => ⟨1, Subtype.ext (by simpa using hAe.2 a a.2)⟩
  refine ⟨⟨⟨⟨fun x y => ?_⟩⟩, fun x hx => ?_⟩, fun B hB hAB => ?_⟩
  · obtain ⟨a, rfl⟩ := (aEquiv (L := L) hA).surjective x
    obtain ⟨b, rfl⟩ := (aEquiv (L := L) hA).surjective y
    rw [← map_mul, ← map_mul, hAe.1.is_comm.comm a b]
  · obtain ⟨a, ha, rfl⟩ := hx
    rw [← map_pow]
    have h3 : a ^ 3 = 1 := Subtype.ext (hAe.2 _ (Subgroup.mem_subgroupOf.mp ha))
    rw [h3, map_one]
  · obtain ⟨S, hAS, -, hScard, hSe⟩ := exists_lift_of_le (isPGroup_subgroupOf (L := L) hA) hB hAB
    have hAS' : A ≤ S.map (L ⊔ A).subtype := fun a ha =>
      ⟨⟨a, Subgroup.mem_sup_right ha⟩, hAS (Subgroup.mem_subgroupOf.mpr ha), rfl⟩
    have heq := hAmax _ (isElemAbelian_map_subtype hSe) hAS'
    have hcardB : Nat.card B = Nat.card (aOne L A) := by
      rw [← hScard, ← Subgroup.card_map_of_injective (L ⊔ A).subtype_injective, heq]
      exact Nat.card_congr (aEquiv (L := L) hA).toEquiv
    exact (Subgroup.eq_of_le_of_card_ge hAB (by rw [hcardB])).symm.le

theorem aOne_inf_centralizer (hA : IsPGroup 3 A) (hAL : A ≤ Subgroup.normalizer (L : Set G))
    {c : G} (hcA : c ∈ A) (hCA : A ⊓ Sec4.thetaQuotCentralizer L = Subgroup.zpowers c) :
    aOne L A ⊓ Subgroup.centralizer (lOne L A : Set (QuotX L A)) =
      Subgroup.zpowers (piX L A ⟨c, Subgroup.mem_sup_right hcA⟩) := by
  have hθ := inSubgroup_theta_sup hA hAL
  have key : ∀ (a : G) (haA : a ∈ A), piX L A ⟨a, Subgroup.mem_sup_right haA⟩ ∈
      Subgroup.centralizer (lOne L A : Set (QuotX L A)) ↔ a ∈ Sec4.thetaQuotCentralizer L := by
    intro a haA
    rw [Sec6.mem_thetaQuotCentralizer_iff, Subgroup.mem_centralizer_iff]
    constructor
    · intro h
      refine ⟨hAL haA, fun l hl => ?_⟩
      have h1 := h _ ⟨⟨l, Subgroup.mem_sup_left hl⟩, Subgroup.mem_subgroupOf.mpr hl, rfl⟩
      have h2 : piX L A ((⟨l, Subgroup.mem_sup_left hl⟩ : ↥(L ⊔ A))⁻¹ *
          ((⟨a, Subgroup.mem_sup_right haA⟩ : ↥(L ⊔ A)) * ⟨l, Subgroup.mem_sup_left hl⟩ *
            (⟨a, Subgroup.mem_sup_right haA⟩ : ↥(L ⊔ A))⁻¹)) = 1 := by
        rw [map_mul, map_mul, map_mul, map_inv, map_inv, ← h1]
        group
      rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h2
      have h3 : l⁻¹ * (a * l * a⁻¹) ∈ inSubgroup (aschbacherSolvableCore 3) (L ⊔ A) :=
        ⟨_, h2, rfl⟩
      rwa [hθ] at h3
    · rintro ⟨-, h⟩ y ⟨l', hl', rfl⟩
      have hl : (l' : G) ∈ L := Subgroup.mem_subgroupOf.mp hl'
      have h3 := h _ hl
      rw [← hθ] at h3
      have hw : piX L A (l'⁻¹ * ((⟨a, Subgroup.mem_sup_right haA⟩ : ↥(L ⊔ A)) * l' *
          (⟨a, Subgroup.mem_sup_right haA⟩ : ↥(L ⊔ A))⁻¹)) = 1 := by
        rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
        obtain ⟨t, ht, hteq⟩ := h3
        have : l'⁻¹ * ((⟨a, Subgroup.mem_sup_right haA⟩ : ↥(L ⊔ A)) * l' *
            (⟨a, Subgroup.mem_sup_right haA⟩ : ↥(L ⊔ A))⁻¹) = t := Subtype.ext hteq.symm
        rw [this]
        exact ht
      rw [map_mul, map_mul, map_mul, map_inv, map_inv] at hw
      calc piX L A l' * piX L A ⟨a, Subgroup.mem_sup_right haA⟩
          = piX L A l' * ((piX L A l')⁻¹ * (piX L A ⟨a, Subgroup.mem_sup_right haA⟩ *
              piX L A l' * (piX L A ⟨a, Subgroup.mem_sup_right haA⟩)⁻¹)) *
              piX L A ⟨a, Subgroup.mem_sup_right haA⟩ := by rw [hw, mul_one]
        _ = piX L A ⟨a, Subgroup.mem_sup_right haA⟩ * piX L A l' := by group
  ext x
  constructor
  · rintro ⟨hxA, hxC⟩
    obtain ⟨a, haA, rfl⟩ := exists_eq_piX_of_mem_aOne hxA
    have hac : a ∈ A ⊓ Sec4.thetaQuotCentralizer L := ⟨haA, (key a haA).mp hxC⟩
    rw [hCA] at hac
    obtain ⟨k, rfl⟩ := hac
    refine ⟨k, ?_⟩
    beta_reduce
    rw [← map_zpow]
    rfl
  · rintro ⟨k, rfl⟩
    have hck : c ^ k ∈ A ⊓ Sec4.thetaQuotCentralizer L := by
      rw [hCA]
      exact ⟨k, rfl⟩
    have heq : piX L A ⟨c, Subgroup.mem_sup_right hcA⟩ ^ k =
        piX L A ⟨c ^ k, Subgroup.mem_sup_right hck.1⟩ := by
      rw [← map_zpow]
      rfl
    change piX L A ⟨c, Subgroup.mem_sup_right hcA⟩ ^ k ∈ _
    rw [heq]
    exact ⟨piX_mem_aOne hck.1, (key _ hck.1).mpr hck.2⟩

end CFSG.RankThree.PartTwo.Sec21.Item211Proof

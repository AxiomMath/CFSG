module

public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Setup
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Good
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.TripleCover
public import CFSG.Adapters.StatedSLPerfect
public import Certificates.Certificate188003
public import Certificates.Certificate188006
public import CFSG.Fischer.F4
import all CFSG.Fischer.F4

public section

namespace CFSG.RankThree.PartTwo.Sec10

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Fischer

theorem ks_perfectResidual_le_ker {G A : Type*} [Group G] [CommGroup A] (φ : G →* A) :
    perfectResidual G ≤ φ.ker := by
  refine (iInf_le _ 1).trans ?_
  rw [derivedSeries_one, commutator_def, Subgroup.commutator_le]
  intro g₁ _ g₂ _
  rw [MonoidHom.mem_ker, map_commutatorElement,
    commutatorElement_eq_one_iff_commute.mpr (Commute.all _ _)]

theorem ks_le_perfectResidual {G : Type*} [Group G] (K : Subgroup G) [Group.IsPerfect K] :
    K ≤ perfectResidual G := by
  unfold perfectResidual
  refine le_iInf fun n => ?_
  induction n with
  | zero => rw [derivedSeries_zero]; exact le_top
  | succ n ih =>
    rw [derivedSeries_succ]
    calc K = ⁅K, K⁆ := (Subgroup.commutator_eq_self).symm
      _ ≤ ⁅derivedSeries G n, derivedSeries G n⁆ := Subgroup.commutator_mono ih ih

theorem ks_map_perfectResidual {G G' : Type*} [Group G] [Group G'] (f : G →* G')
    (hf : Function.Bijective f) : (perfectResidual G).map f = perfectResidual G' := by
  unfold perfectResidual
  exact (Subgroup.map_iInf f hf.1 (derivedSeries G)).trans
    (iInf_congr fun n => map_derivedSeries_eq hf.2 n)

theorem ks_inSubgroup_equiv {M N : Type} [Group M] [Group N] (Y : Subgroup M) (ρ : Y →* N)
    (hρ : Function.Injective ρ) :
    Nonempty (↥(CFSG.inSubgroup perfectResidual Y) ≃*
      ↥(CFSG.inSubgroup perfectResidual ρ.range)) := by
  let e : Y ≃* ρ.range := MonoidHom.ofInjective hρ
  have hmap : (perfectResidual Y).map e.toMonoidHom = perfectResidual ρ.range :=
    ks_map_perfectResidual e.toMonoidHom ⟨e.injective, e.surjective⟩
  exact ⟨((Subgroup.equivMapOfInjective (perfectResidual Y) Y.subtype
      (Subgroup.subtype_injective Y)).symm.trans
    ((MulEquiv.subgroupMap e (perfectResidual Y)).trans (MulEquiv.subgroupCongr hmap))).trans
    (Subgroup.equivMapOfInjective (perfectResidual ρ.range) ρ.range.subtype
      (Subgroup.subtype_injective _))⟩

theorem ks_inSubgroup_le_SLsub (H : Subgroup (Matrix.GeneralLinearGroup (Fin 3) CFSG.Fischer.F4)) :
    CFSG.inSubgroup perfectResidual H ≤ CFSG.RankThree.PartTwo.Sec10.KS1012GL34.SLsub := by
  intro g hg
  obtain ⟨a, ha, rfl⟩ := Subgroup.mem_map.mp hg
  have h1 : Matrix.GeneralLinearGroup.det (H.subtype a) = 1 :=
    MonoidHom.mem_ker.mp (ks_perfectResidual_le_ker
      ((Matrix.GeneralLinearGroup.det :
        Matrix.GeneralLinearGroup (Fin 3) CFSG.Fischer.F4 →* (CFSG.Fischer.F4)ˣ).comp H.subtype) ha)
  rw [CFSG.RankThree.PartTwo.Sec10.KS1012GL34.mem_SLsub,
    ← Matrix.GeneralLinearGroup.val_det_apply, h1, Units.val_one]

theorem ks_le_inSubgroup_of_isPerfect {G : Type} [Group G] (H K : Subgroup G) (hKH : K ≤ H)
    [Group.IsPerfect K] : K ≤ CFSG.inSubgroup perfectResidual H := by
  intro g hg
  haveI : Group.IsPerfect (K.subgroupOf H) :=
    Group.IsPerfect.ofSurjective (f := (Subgroup.subgroupOfEquivOfLe hKH).symm.toMonoidHom)
      (Subgroup.subgroupOfEquivOfLe hKH).symm.surjective
  have hle := ks_le_perfectResidual (K.subgroupOf H)
  have hmem : (⟨g, hKH hg⟩ : ↥H) ∈ K.subgroupOf H := Subgroup.mem_subgroupOf.mpr hg
  unfold CFSG.inSubgroup
  exact Subgroup.mem_map.mpr ⟨⟨g, hKH hg⟩, hle hmem, rfl⟩

theorem ks_SLsub_eq :
    CFSG.RankThree.PartTwo.Sec10.KS1012GL34.SLsub = CFSG.Open.StatedSL 3 CFSG.Fischer.F4 :=
  CFSG.RankThree.PartTwo.Sec10.KS1012GL34.SLsub_eq_closure

theorem ks_isPerfect_SLsub :
    Group.IsPerfect ↥CFSG.RankThree.PartTwo.Sec10.KS1012GL34.SLsub := by
  haveI : Group.IsPerfect ↥(CFSG.Open.StatedSL 3 CFSG.Fischer.F4) :=
    CFSG.Open.StatedAPI.isPerfect_statedSL_of_three_le (by norm_num) CFSG.Fischer.F4
  exact Group.IsPerfect.ofSurjective
    (f := (MulEquiv.subgroupCongr ks_SLsub_eq).symm.toMonoidHom)
    (MulEquiv.subgroupCongr ks_SLsub_eq).symm.surjective

theorem ks_isSLThreePiAt_of_mulEquiv {X : Type} [Group X]
    (e : X ≃* ↥(CFSG.Open.StatedSL 3 CFSG.Fischer.F4)) :
    CFSG.RankThree.PartTwo.Sec4.IsSLThreePiAt X 4 := by
  unfold CFSG.RankThree.PartTwo.Sec4.IsSLThreePiAt
  exact ⟨CFSG.Fischer.F4, inferInstance, inferInstance,
    Or.inl ⟨Nat.card_eq_fintype_card.trans CFSG.Fischer.F4.card, by norm_num, ⟨e⟩⟩⟩

theorem ks_normalizer_map {G N : Type*} [Group G] [Group N] (ρ : G →* N)
    (hρ : Function.Injective ρ) (K : Subgroup G) {g : G}
    (hg : g ∈ Subgroup.normalizer (K : Set G)) :
    ρ g ∈ Subgroup.normalizer ((K.map ρ : Subgroup N) : Set N) := by
  rw [Subgroup.mem_normalizer_iff] at hg ⊢
  intro h
  constructor
  · intro hh
    obtain ⟨k, hk, rfl⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨g * k * g⁻¹, (hg k).mp hk, ?_⟩
    simp only [map_mul, map_inv]
  · intro hh
    obtain ⟨k, hk, hkeq⟩ := Subgroup.mem_map.mp hh
    refine Subgroup.mem_map.mpr ⟨g⁻¹ * k * g, ?_, ?_⟩
    · apply (hg (g⁻¹ * k * g)).mpr
      rw [show g * (g⁻¹ * k * g) * g⁻¹ = k by group]
      exact hk
    · rw [map_mul, map_mul, map_inv, hkeq]
      group

theorem ks_mem_normalizer_subgroupOf {M : Type} [Group M] (Y T : Subgroup M) {x : M}
    (hxY : x ∈ Y) (hxT : x ∈ Subgroup.normalizer (T : Set M)) :
    (⟨x, hxY⟩ : ↥Y) ∈ Subgroup.normalizer ((T.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
  rw [Subgroup.mem_normalizer_iff]
  intro h
  have key := Subgroup.mem_normalizer_iff.mp hxT (h : M)
  simpa [Subgroup.mem_subgroupOf] using key

theorem ks1012GL34_core
    (hc1 : ∀ (t x w z : Matrix.GeneralLinearGroup (Fin 3) CFSG.Fischer.F4) (μ : CFSG.Fischer.F4),
      (μ = 1 ∨ μ = CFSG.Fischer.F4.ω ∨ μ = CFSG.RankThree.PartTwo.Sec10.KS1012GL34.om2) →
      CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Good3 (t : Matrix (Fin 3) (Fin 3) CFSG.Fischer.F4) →
      (x : Matrix (Fin 3) (Fin 3) CFSG.Fischer.F4) = CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Xd →
      (w : Matrix (Fin 3) (Fin 3) CFSG.Fischer.F4) = CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Wm μ →
      (z : Matrix (Fin 3) (Fin 3) CFSG.Fischer.F4) = CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Zs →
      (∀ g ∈ CFSG.RankThree.PartTwo.Sec10.KS1012GL34.SLsub, g ∈ Subgroup.closure
        ({x, w, z, t} : Set (Matrix.GeneralLinearGroup (Fin 3) CFSG.Fischer.F4))) ∨
        (μ = 1 ∧ ∃ i : Fin 6, Subgroup.closure
          ({x, w, z, t} : Set (Matrix.GeneralLinearGroup (Fin 3) CFSG.Fischer.F4)) =
            CFSG.RankThree.PartTwo.Sec10.KS1012GL34.P i))
    (hc2 : ∀ (i : Fin 6) (Y : Subgroup (Matrix.GeneralLinearGroup (Fin 3) CFSG.Fischer.F4)),
      CFSG.RankThree.PartTwo.Sec10.KS1012GL34.P i < Y →
        Y ≤ CFSG.RankThree.PartTwo.Sec10.KS1012GL34.SLsub →
          Y = CFSG.RankThree.PartTwo.Sec10.KS1012GL34.SLsub)
    (hPperf : ∀ i : Fin 6, Group.IsPerfect ↥(CFSG.RankThree.PartTwo.Sec10.KS1012GL34.P i))
    (hTC : ∀ (i : Fin 6) (X : Type) [Group X],
      (X ≃* ↥(CFSG.RankThree.PartTwo.Sec10.KS1012GL34.P i)) →
        CFSG.RankThree.PartTwo.Sec4.IsTripleCover X (alternatingGroup (Fin 6))) :
    KS1012GL34 := by
  unfold KS1012GL34
  intro S _ _ hcomm hexp Y z x w hzY hxY hwY hzc hz3 hzfix hx3 hxfix hwx hT
  obtain ⟨T, hTY, hTne, hT2, hxT⟩ := hT
  obtain ⟨ρ, hρ, μ, hμ0, hx, hz, hw⟩ :=
    CFSG.RankThree.PartTwo.Sec10.KS1012GL34.exists_gl3_model S hcomm hexp Y z x w hzY hxY hwY
      hzc hz3 hzfix hx3 hxfix hwx
  have hK0ne : T.subgroupOf Y ≠ ⊥ := by
    obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hTne
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr
      ⟨⟨⟨a.1, hTY a.2⟩, Subgroup.mem_subgroupOf.mpr a.2⟩, ?_⟩
    intro h
    apply ha
    have h2 : (a.1 : MulAut S) = 1 := congrArg (fun b : ↥(T.subgroupOf Y) => (b : ↥Y).1) h
    exact Subtype.ext h2
  have hT'ne : (T.subgroupOf Y).map ρ ≠ ⊥ := by
    obtain ⟨b, hb⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hK0ne
    refine Subgroup.ne_bot_iff_exists_ne_one.mpr ⟨⟨ρ b.1, Subgroup.mem_map_of_mem ρ b.2⟩, ?_⟩
    intro h
    apply hb
    apply Subtype.ext
    apply hρ
    have h2 : ρ b.1 = 1 := congrArg Subtype.val h
    exact h2.trans (map_one ρ).symm
  have hT2' : IsPGroup 2 ((T.subgroupOf Y).map ρ) :=
    (hT2.comap_of_injective Y.subtype (Subgroup.subtype_injective Y)).map ρ
  have hXT' : ρ ⟨x, hxY⟩ ∈ Subgroup.normalizer
      (((T.subgroupOf Y).map ρ : Subgroup (Matrix.GeneralLinearGroup (Fin 3) CFSG.Fischer.F4)) :
        Set (Matrix.GeneralLinearGroup (Fin 3) CFSG.Fischer.F4)) :=
    ks_normalizer_map ρ hρ (T.subgroupOf Y) (ks_mem_normalizer_subgroupOf Y T hxY hxT)
  obtain ⟨t, htT, htG⟩ :=
    CFSG.RankThree.PartTwo.Sec10.KS1012GL34.exists_good_involution (ρ ⟨x, hxY⟩) hx
      ((T.subgroupOf Y).map ρ) hT'ne hT2' hXT'
  have key : ∀ m : CFSG.Fischer.F4, m ≠ 0 →
      m = 1 ∨ m = CFSG.Fischer.F4.ω ∨ m = CFSG.RankThree.PartTwo.Sec10.KS1012GL34.om2 := by
    decide
  have hμ := key μ hμ0
  have hT3 := hc1 t (ρ ⟨x, hxY⟩) (ρ ⟨w, hwY⟩) (ρ ⟨z, hzY⟩) μ hμ htG hx hw hz
  have hXH : ρ ⟨x, hxY⟩ ∈ ρ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hWH : ρ ⟨w, hwY⟩ ∈ ρ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hZH : ρ ⟨z, hzY⟩ ∈ ρ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have htH : t ∈ ρ.range := by
    obtain ⟨k, _, hk⟩ := Subgroup.mem_map.mp htT
    exact MonoidHom.mem_range.mpr ⟨k, hk⟩
  have hcl_le : Subgroup.closure
      ({ρ ⟨x, hxY⟩, ρ ⟨w, hwY⟩, ρ ⟨z, hzY⟩, t} :
        Set (Matrix.GeneralLinearGroup (Fin 3) CFSG.Fischer.F4)) ≤ ρ.range :=
    (Subgroup.closure_le _).mpr (Set.insert_subset_iff.mpr ⟨hXH, Set.insert_subset_iff.mpr
      ⟨hWH, Set.insert_subset_iff.mpr ⟨hZH, Set.singleton_subset_iff.mpr htH⟩⟩⟩)
  rcases hT3 with hSL | ⟨_, i, hPi⟩
  ·
    have hSLle : CFSG.RankThree.PartTwo.Sec10.KS1012GL34.SLsub ≤ ρ.range :=
      fun g hg => hcl_le (hSL g hg)
    haveI := ks_isPerfect_SLsub
    have hKeq : CFSG.inSubgroup perfectResidual ρ.range =
        CFSG.RankThree.PartTwo.Sec10.KS1012GL34.SLsub :=
      le_antisymm (ks_inSubgroup_le_SLsub ρ.range)
        (ks_le_inSubgroup_of_isPerfect ρ.range _ hSLle)
    obtain ⟨eI⟩ := ks_inSubgroup_equiv Y ρ hρ
    exact Or.inl (ks_isSLThreePiAt_of_mulEquiv
      (eI.trans (MulEquiv.subgroupCongr (hKeq.trans ks_SLsub_eq))))
  ·
    have hPle : CFSG.RankThree.PartTwo.Sec10.KS1012GL34.P i ≤ ρ.range := by
      rw [← hPi]
      exact hcl_le
    haveI := hPperf i
    have hPK := ks_le_inSubgroup_of_isPerfect ρ.range _ hPle
    have hKS := ks_inSubgroup_le_SLsub ρ.range
    obtain ⟨eI⟩ := ks_inSubgroup_equiv Y ρ hρ
    rcases eq_or_lt_of_le hPK with hEq | hLt
    · exact Or.inr (hTC i _ (eI.trans (MulEquiv.subgroupCongr hEq.symm)))
    ·
      have hKeq := hc2 i _ hLt hKS
      exact Or.inl (ks_isSLThreePiAt_of_mulEquiv
        (eI.trans (MulEquiv.subgroupCongr (hKeq.trans ks_SLsub_eq))))

theorem ks1012GL34_holds : KS1012GL34 := by
  refine ks1012GL34_core Certificates.certificate188003.1
    Certificates.certificate188003.2 ?_ ?_
  · intro i
    exact CFSG.RankThree.PartTwo.Sec10.KS1012GL34.isPerfect_P Certificates.certificate188006 i
  · intro i X _ e
    exact CFSG.RankThree.PartTwo.Sec10.KS1012GL34.isTripleCover_P
      Certificates.certificate188006 i e

end CFSG.RankThree.PartTwo.Sec10

end

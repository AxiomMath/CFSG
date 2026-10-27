module

public import CFSG.GroupTheory.LocalCores.FittingNormal
public import CFSG.LocalAnalysis.RankThreeCoreUniqueness.CanonicalLocalObstruction

public section

namespace CFSG.SignalizerFunctorTheorem.Nonsolvable

variable {G : Type*} [Group G]

instance instNormalSolvableRadical : (CFSG.solvableRadical G).Normal :=
  Subgroup.sSup_normal _ fun _ hN => hN.1

theorem isSolvable_of_mulEquiv {A B : Type*} [Group A] [Group B] (e : A ≃* B)
    [Group.IsSolvable A] : Group.IsSolvable B :=
  Group.isSolvable_of_surjective (f := e.toMonoidHom) e.surjective

theorem le_solvableRadical {N : Subgroup G} (hN : N.Normal) (hs : Group.IsSolvable N) :
    N ≤ CFSG.solvableRadical G :=
  le_sSup ⟨hN, hs⟩

private theorem isSolvable_sup_of_normal_solvable (N₁ N₂ : Subgroup G) [hN₁ : N₁.Normal]
    [N₂.Normal] [Group.IsSolvable N₁] [Group.IsSolvable N₂] :
    Group.IsSolvable (N₁ ⊔ N₂ : Subgroup G) := by
  let L : Subgroup G := N₁ ⊔ N₂
  let M : Subgroup L := N₁.subgroupOf L
  have hM : M.Normal := Subgroup.normal_subgroupOf
  have hMsolv : Group.IsSolvable M :=
    Group.isSolvable_of_isSolvable_injective (f := (Subgroup.subgroupOfEquivOfLe
      (le_sup_left : N₁ ≤ L)).toMonoidHom) (Subgroup.subgroupOfEquivOfLe le_sup_left).injective
  let f : N₂ →* L ⧸ M :=
    (QuotientGroup.mk' M).comp (Subgroup.inclusion (le_sup_right : N₂ ≤ L))
  have hf : Function.Surjective f := by
    intro y
    obtain ⟨⟨x, hx⟩, rfl⟩ := QuotientGroup.mk'_surjective M y
    obtain ⟨a, ha, b, hb, rfl⟩ := (Subgroup.mem_sup_of_normal_left (s := N₁) (t := N₂)).mp hx
    refine ⟨⟨b, hb⟩, ?_⟩
    simp only [f, MonoidHom.comp_apply]
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
      Subgroup.mem_subgroupOf]
    simpa [mul_assoc] using hN₁.conj_mem' a ha b
  have : Group.IsSolvable (L ⧸ M) := Group.isSolvable_of_surjective hf
  exact Group.isSolvable_of_subgroup_quotient M

theorem isSolvable_solvableRadical [Finite G] : Group.IsSolvable (CFSG.solvableRadical G) := by
  classical
  obtain ⟨M, -, hM⟩ := Finite.exists_le_maximal
    (p := fun N : Subgroup G => N.Normal ∧ Group.IsSolvable N) (a := ⊥)
    ⟨inferInstance, inferInstance⟩
  have hge : ∀ N : Subgroup G, N.Normal ∧ Group.IsSolvable N → N ≤ M := by
    rintro N ⟨hN, hNs⟩
    have : M.Normal := hM.1.1
    have : Group.IsSolvable M := hM.1.2
    have h := hM.eq_of_le ⟨inferInstance, isSolvable_sup_of_normal_solvable M N⟩ le_sup_left
    rw [h]
    exact le_sup_right
  have heq : CFSG.solvableRadical G = M := le_antisymm (sSup_le hge) (le_sSup hM.1)
  rw [heq]
  exact hM.1.2

theorem isSolvable_comap_mk' {R : Subgroup G} [R.Normal] [Group.IsSolvable R]
    {N : Subgroup (G ⧸ R)} [Group.IsSolvable N] :
    Group.IsSolvable (N.comap (QuotientGroup.mk' R)) := by
  have hRN : R ≤ N.comap (QuotientGroup.mk' R) := by
    intro x hx
    rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff x).mpr hx]
    exact one_mem _
  refine Group.isSolvable_of_ker_le_range (Subgroup.inclusion hRN)
    ((QuotientGroup.mk' R).subgroupComap N) fun x hx => ?_
  have hx1 : (QuotientGroup.mk' R) (x : G) = 1 :=
    congrArg Subtype.val (MonoidHom.mem_ker.mp hx)
  rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at hx1
  exact ⟨⟨x, hx1⟩, rfl⟩

theorem solvableRadical_quotient [Finite G] :
    CFSG.solvableRadical (G ⧸ CFSG.solvableRadical G) = ⊥ := by
  have hRs : Group.IsSolvable (CFSG.solvableRadical G) := isSolvable_solvableRadical
  have hNs : Group.IsSolvable (CFSG.solvableRadical (G ⧸ CFSG.solvableRadical G)) :=
    isSolvable_solvableRadical
  have hcs := isSolvable_comap_mk' (R := CFSG.solvableRadical G)
    (N := CFSG.solvableRadical (G ⧸ CFSG.solvableRadical G))
  have hle := le_solvableRadical
    (Subgroup.Normal.comap (inferInstance : (CFSG.solvableRadical
      (G ⧸ CFSG.solvableRadical G)).Normal) (QuotientGroup.mk' (CFSG.solvableRadical G))) hcs
  rw [eq_bot_iff]
  intro q hq
  obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
  have hg : g ∈ (CFSG.solvableRadical (G ⧸ CFSG.solvableRadical G)).comap
      (QuotientGroup.mk' (CFSG.solvableRadical G)) := hq
  rw [Subgroup.mem_bot]
  exact (QuotientGroup.eq_one_iff g).mpr (hle hg)

theorem centralizer_layer_eq_bot [Finite G] (h : CFSG.solvableRadical G = ⊥) :
    Subgroup.centralizer (CFSG.layer G : Set G) = ⊥ := by
  by_contra hne
  have hlayer : (CFSG.layer G).Characteristic := CFSG.LocalCores.layer_characteristic
  have hCn : (Subgroup.centralizer (CFSG.layer G : Set G)).Normal := inferInstance
  obtain ⟨N, ⟨hNn, hNne, hNC⟩, hNmin⟩ := (Set.toFinite {M : Subgroup G | M.Normal ∧ M ≠ ⊥ ∧
      M ≤ Subgroup.centralizer (CFSG.layer G : Set G)}).exists_minimal
    ⟨Subgroup.centralizer (CFSG.layer G : Set G), hCn, hne, le_rfl⟩
  have hmin : ∀ M : Subgroup G, M.Normal → M ≤ N → M = ⊥ ∨ M = N := fun M hM hle =>
    (em (M = ⊥)).imp id fun hM1 => le_antisymm hle (hNmin ⟨hM, hM1, hle.trans hNC⟩ hle)
  have hFit : CFSG.fittingSubgroup G = ⊥ := by
    have := (CFSG.LocalCores.fitting_nilpotent (G := G)).1
    rw [eq_bot_iff, ← h]
    exact le_solvableRadical inferInstance inferInstance
  have hNF : N ≤ CFSG.layer G := by
    have := CFSG.LocalCores.le_generalizedFitting_of_minimal hNn hNne hmin
    rwa [CFSG.generalizedFitting, hFit, bot_sup_eq] at this
  have hcomm : IsMulCommutative N := ⟨⟨fun x y => Subtype.ext
    (Subgroup.mem_centralizer_iff.mp (hNC y.2) (x : G) (hNF x.2))⟩⟩
  have hNs : Group.IsSolvable N := inferInstance
  exact hNne (by rw [eq_bot_iff, ← h]; exact le_solvableRadical hNn hNs)

theorem le_solvableRadical_of_isSubnormal [Finite G] {S : Subgroup G} (hS : S.IsSubnormal)
    (hs : Group.IsSolvable S) : S ≤ CFSG.solvableRadical G := by
  set π := QuotientGroup.mk' (CFSG.solvableRadical G) with hπ
  have hSb : (S.map π).IsSubnormal := hS.map (QuotientGroup.mk'_surjective _)
  have hSs : Group.IsSolvable (S.map π) :=
    Group.isSolvable_of_surjective (π.subgroupMap_surjective S)
  have hcomm := (CFSG.LocalCores.component_solvable_centralizer hSs hSb).2
  have hZ := centralizer_layer_eq_bot (G := G ⧸ CFSG.solvableRadical G) solvableRadical_quotient
  have hle : S.map π ≤ ⊥ := by
    rw [← hZ]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mp
      (by rw [Subgroup.commutator_comm]; exact hcomm)
  rw [le_bot_iff, Subgroup.map_eq_bot_iff, hπ, QuotientGroup.ker_mk'] at hle
  exact hle

theorem map_subtype_solvableRadical_eq_inf [Finite G] {K : Subgroup G} (hK : K.IsSubnormal) :
    (CFSG.solvableRadical K).map K.subtype = K ⊓ CFSG.solvableRadical G := by
  apply le_antisymm
  · refine le_inf (Subgroup.map_subtype_le _) ?_
    have hsol : Group.IsSolvable ((CFSG.solvableRadical K).map K.subtype) := by
      have := isSolvable_solvableRadical (G := K)
      exact isSolvable_of_mulEquiv (Subgroup.equivMapOfInjective (CFSG.solvableRadical K)
        K.subtype K.subtype_injective)
    exact le_solvableRadical_of_isSubnormal
      (Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal inferInstance) hK) hsol
  · intro x hx
    obtain ⟨hxK, hxR⟩ := Subgroup.mem_inf.mp hx
    have hRs : Group.IsSolvable (CFSG.solvableRadical G) := isSolvable_solvableRadical
    have hRKs : Group.IsSolvable ((CFSG.solvableRadical G).subgroupOf K) :=
      Group.isSolvable_of_isSolvable_injective
        (f := K.subtype.subgroupComap (CFSG.solvableRadical G))
        (MonoidHom.subgroupComap_injective _ _ K.subtype_injective)
    have hle : (CFSG.solvableRadical G).subgroupOf K ≤ CFSG.solvableRadical K :=
      le_solvableRadical Subgroup.normal_subgroupOf hRKs
    exact Subgroup.mem_map.mpr ⟨⟨x, hxK⟩, hle (Subgroup.mem_subgroupOf.mpr hxR), rfl⟩

instance solvableRadical_characteristic : (CFSG.solvableRadical G).Characteristic := by
  rw [Subgroup.characteristic_iff_map_eq]
  have key : ∀ ψ : G ≃* G, (CFSG.solvableRadical G).map ψ.toMonoidHom ≤
      CFSG.solvableRadical G := by
    intro ψ
    rw [Subgroup.map_le_iff_le_comap]
    refine sSup_le fun N hN => ?_
    rw [← Subgroup.map_le_iff_le_comap]
    have := hN.2
    exact le_solvableRadical (hN.1.map _ ψ.surjective)
      (Group.isSolvable_of_surjective (ψ.toMonoidHom.subgroupMap_surjective N))
  intro φ
  refine le_antisymm (key φ) ?_
  have h := Subgroup.map_mono (f := φ.toMonoidHom) (key φ.symm)
  rwa [Subgroup.map_map, show φ.toMonoidHom.comp φ.symm.toMonoidHom = MonoidHom.id G from
    MonoidHom.ext fun x => φ.apply_symm_apply x, Subgroup.map_id] at h

theorem isPerfect_perfectResidual_map [Finite G] (Y : Subgroup G) :
    Group.IsPerfect ((CFSG.perfectResidual Y).map Y.subtype) :=
  CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidualOf_isPerfect Y

theorem le_perfectResidual_map_of_isPerfect {P Y : Subgroup G} (hP : Group.IsPerfect P)
    (hPY : P ≤ Y) : P ≤ (CFSG.perfectResidual Y).map Y.subtype :=
  CFSG.RankThreeCoreUniqueness.Helpers.perfect_subgroup_le_perfectResidualOf P Y hP hPY

theorem perfectResidual_map_eq_of_isPerfect {P : Subgroup G} (hP : Group.IsPerfect P) :
    (CFSG.perfectResidual P).map P.subtype = P :=
  le_antisymm (Subgroup.map_subtype_le _) (le_perfectResidual_map_of_isPerfect hP le_rfl)

theorem map_perfectResidual_map [Finite G] {G' : Type*} [Group G'] (f : G →* G')
    (Y : Subgroup G) :
    ((CFSG.perfectResidual Y).map Y.subtype).map f =
      (CFSG.perfectResidual (Y.map f)).map (Y.map f).subtype := by
  have hsurj := f.subgroupMap_surjective Y
  have : Finite (Y.map f) := Finite.of_surjective _ hsurj
  have h := CFSG.RankThreeCoreUniqueness.Helpers.finite_perfectResidual_map_eq
    (f.subgroupMap Y) hsurj
  have h' : CFSG.perfectResidual (Y.map f) = (CFSG.perfectResidual Y).map (f.subgroupMap Y) :=
    h.symm
  rw [h', Subgroup.map_map, Subgroup.map_map]
  exact congrArg (fun g => Subgroup.map g (CFSG.perfectResidual Y)) (MonoidHom.ext fun x => rfl)

theorem isSubnormal_perfectResidual_map {S : Subgroup G} (hS : S.IsSubnormal) :
    ((CFSG.perfectResidual S).map S.subtype).IsSubnormal := by
  have : (CFSG.perfectResidual S).Characteristic :=
    CFSG.RankThreeCoreUniqueness.Helpers.perfectResidual_characteristic
  exact Subgroup.IsSubnormal.trans' (Subgroup.Normal.isSubnormal inferInstance) hS

theorem normalizer_le_normalizer_perfectResidual_map (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer (((CFSG.perfectResidual Y).map Y.subtype : Subgroup G) : Set G) :=
  CFSG.RankThreeCoreUniqueness.Helpers.perfectResidualOf_normalizer_contains Y

theorem eq_top_of_isSubnormal_of_sup_eq_top {P : Type*} [Group P] [Group.IsPerfect P]
    {K M : Subgroup P} (hK : K.IsSubnormal) (hM : M.Normal) (hMs : Group.IsSolvable M)
    (hKM : K ⊔ M = ⊤) : K = ⊤ := by
  revert hKM
  induction hK with
  | top => intro _; rfl
  | step K T hKT hT hN ih =>
    intro hKM
    have hTM : T ⊔ M = ⊤ := by
      rw [eq_top_iff, ← hKM]
      exact sup_le_sup_right hKT M
    have hT' : T = ⊤ := ih hTM
    subst hT'
    have hKn : K.Normal := by
      rw [Subgroup.normal_subgroupOf_iff_le_normalizer hKT, top_le_iff,
        Subgroup.normalizer_eq_top_iff] at hN
      exact hN
    have hf : Function.Surjective ((QuotientGroup.mk' K).comp M.subtype) := by
      intro q
      obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective q
      have hg : g ∈ K ⊔ M := by
        rw [hKM]
        exact Subgroup.mem_top g
      obtain ⟨k, hk, m, hm, rfl⟩ := (Subgroup.mem_sup_of_normal_right (s := K) (t := M)).mp hg
      refine ⟨⟨m, hm⟩, ?_⟩
      simp only [MonoidHom.comp_apply, Subgroup.coe_subtype, QuotientGroup.mk'_apply]
      rw [QuotientGroup.eq]
      simpa [mul_assoc] using hKn.conj_mem' k hk m
    have hsolv : Group.IsSolvable (P ⧸ K) := Group.isSolvable_of_surjective hf
    have hsub : Subsingleton (P ⧸ K) := by
      by_contra hns
      rw [not_subsingleton_iff_nontrivial] at hns
      exact Group.IsPerfect.not_isSolvable (P ⧸ K) hsolv
    refine top_le_iff.mp fun g _ => ?_
    have h1 : (g : P ⧸ K) = ((1 : P) : P ⧸ K) := Subsingleton.elim _ _
    rw [QuotientGroup.eq] at h1
    simpa using h1

theorem le_of_isSubnormal_subgroupOf_of_le_sup {K D R : Subgroup G} (hD : Group.IsPerfect D)
    (hKD : K ≤ D) (hKs : (K.subgroupOf D).IsSubnormal) (hR : R.Normal)
    (hRs : Group.IsSolvable R) (hDKR : D ≤ K ⊔ R) : D ≤ K := by
  have hRD : Group.IsSolvable (R.subgroupOf D) :=
    Group.isSolvable_of_isSolvable_injective (f := D.subtype.subgroupComap R)
      (MonoidHom.subgroupComap_injective _ _ D.subtype_injective)
  have hsup : K.subgroupOf D ⊔ R.subgroupOf D = ⊤ := by
    refine eq_top_iff.mpr fun x _ => ?_
    obtain ⟨k, hk, r, hr, hkr⟩ := (Subgroup.mem_sup_of_normal_right (s := K) (t := R)).mp
      (hDKR x.2)
    have hrD : r ∈ D := by
      have : r = k⁻¹ * (x : G) := by rw [← hkr]; group
      rw [this]
      exact mul_mem (inv_mem (hKD hk)) x.2
    have hx : x = ⟨k, hKD hk⟩ * ⟨r, hrD⟩ := Subtype.ext hkr.symm
    rw [hx]
    exact Subgroup.mul_mem_sup (Subgroup.mem_subgroupOf.mpr hk) (Subgroup.mem_subgroupOf.mpr hr)
  exact Subgroup.subgroupOf_eq_top.mp
    (eq_top_of_isSubnormal_of_sup_eq_top hKs Subgroup.normal_subgroupOf hRD hsup)

theorem perfectResidual_sup_eq [Finite G] {K R : Subgroup G} (hKp : Group.IsPerfect K)
    (hKs : K.IsSubnormal) (hR : R.Normal) (hRs : Group.IsSolvable R) :
    (CFSG.perfectResidual (K ⊔ R : Subgroup G)).map (K ⊔ R).subtype = K :=
  le_antisymm
    (le_of_isSubnormal_subgroupOf_of_le_sup (isPerfect_perfectResidual_map (K ⊔ R))
      (le_perfectResidual_map_of_isPerfect hKp le_sup_left) hKs.subgroupOf hR hRs
      (Subgroup.map_subtype_le _))
    (le_perfectResidual_map_of_isPerfect hKp le_sup_left)

theorem le_of_le_sup_of_isPerfect [Finite G] {K L R : Subgroup G} (hKp : Group.IsPerfect K)
    (hLp : Group.IsPerfect L) (hLs : L.IsSubnormal) (hR : R.Normal) (hRs : Group.IsSolvable R)
    (h : K ≤ L ⊔ R) : K ≤ L := by
  have := le_perfectResidual_map_of_isPerfect hKp h
  rwa [perfectResidual_sup_eq hLp hLs hR hRs] at this

theorem normalizer_sup_le_normalizer [Finite G] {K R : Subgroup G} (hKp : Group.IsPerfect K)
    (hKs : K.IsSubnormal) (hR : R.Normal) (hRs : Group.IsSolvable R) :
    Subgroup.normalizer ((K ⊔ R : Subgroup G) : Set G) ≤ Subgroup.normalizer (K : Set G) := by
  have h := normalizer_le_normalizer_perfectResidual_map (K ⊔ R)
  rwa [perfectResidual_sup_eq hKp hKs hR hRs] at h

theorem sup_le_normalizer [Finite G] {K R : Subgroup G} (hKp : Group.IsPerfect K)
    (hKs : K.IsSubnormal) (hR : R.Normal) (hRs : Group.IsSolvable R) :
    K ⊔ R ≤ Subgroup.normalizer (K : Set G) :=
  Subgroup.le_normalizer.trans (normalizer_sup_le_normalizer hKp hKs hR hRs)

end CFSG.SignalizerFunctorTheorem.Nonsolvable

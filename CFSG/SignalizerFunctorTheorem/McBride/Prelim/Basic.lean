module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Defs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.SolComponent.McBride

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

theorem sol_le (X : Subgroup G) : sol X ≤ X := Subgroup.map_subtype_le _

theorem subgroupOf_sol (X : Subgroup G) : (sol X).subgroupOf X = CFSG.solvableRadical ↥X :=
  Subgroup.comap_map_eq_self_of_injective X.subtype_injective _

theorem sol_eq_bot_iff (X : Subgroup G) : sol X = ⊥ ↔ CFSG.solvableRadical ↥X = ⊥ :=
  Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective

theorem kOf_le (X : Subgroup G) : kOf X ≤ X := Subgroup.map_subtype_le _

theorem subgroupOf_kOf (X : Subgroup G) :
    (kOf X).subgroupOf X = CFSG.SignalizerFunctorTheorem.Nonsolvable.oStar ↥X :=
  Subgroup.comap_map_eq_self_of_injective X.subtype_injective _

theorem sol_le_kOf (X : Subgroup G) : sol X ≤ kOf X :=
  Subgroup.map_mono CFSG.SignalizerFunctorTheorem.Nonsolvable.solvableRadical_le_oStar

theorem isSolvable_sol [Finite G] (X : Subgroup G) : Group.IsSolvable (sol X) := by
  have : Group.IsSolvable (CFSG.solvableRadical ↥X) :=
    CFSG.SignalizerFunctorTheorem.Nonsolvable.isSolvable_solvableRadical
  exact Group.isSolvable_of_surjective
    (f := X.subtype.subgroupMap (CFSG.solvableRadical ↥X))
    (MonoidHom.subgroupMap_surjective _ _)

theorem normal_sol_subgroupOf (X : Subgroup G) : ((sol X).subgroupOf X).Normal := by
  rw [subgroupOf_sol]
  infer_instance

theorem normal_kOf_subgroupOf [Finite G] (X : Subgroup G) : ((kOf X).subgroupOf X).Normal := by
  rw [subgroupOf_kOf]
  infer_instance

theorem map_conj_le_orbitClosure (X : Subgroup G) {A : Subgroup G} {a : G} (ha : a ∈ A) :
    X.map (MulAut.conj a).toMonoidHom ≤ orbitClosure X A :=
  le_iSup₂_of_le a ha le_rfl

theorem le_orbitClosure (X A : Subgroup G) : X ≤ orbitClosure X A := by
  have h1 : X ≤ X.map (MulAut.conj (1 : G)).toMonoidHom := fun x hx => ⟨x, hx, by simp⟩
  exact h1.trans (map_conj_le_orbitClosure X (one_mem A))

theorem orbitClosure_le {X A L : Subgroup G}
    (h : ∀ a ∈ A, X.map (MulAut.conj a).toMonoidHom ≤ L) : orbitClosure X A ≤ L :=
  iSup₂_le h

theorem smear_le_orbitClosure (X A : Subgroup G) : smear X A ≤ orbitClosure X A := inf_le_left

theorem smear_le_centralizer (X A : Subgroup G) : smear X A ≤ Subgroup.centralizer (A : Set G) :=
  inf_le_right

theorem mem_smear_iff {X A : Subgroup G} {x : G} :
    x ∈ smear X A ↔ x ∈ orbitClosure X A ∧ ∀ a ∈ A, a * x * a⁻¹ = x := by
  unfold smear
  rw [Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  refine and_congr_right fun _ => forall_congr' fun a => forall_congr' fun _ => ?_
  rw [mul_inv_eq_iff_eq_mul, eq_comm]

theorem smear_mono_left {X Y : Subgroup G} (h : X ≤ Y) (A : Subgroup G) :
    smear X A ≤ smear Y A :=
  inf_le_inf_right _ (iSup₂_mono fun _ _ => Subgroup.map_mono h)

theorem isMulCommutative_congr {A B : Type*} [Group A] [Group B] (e : A ≃* B) :
    IsMulCommutative A ↔ IsMulCommutative B := by
  rw [isMulCommutative_iff, isMulCommutative_iff]
  constructor
  · intro h a b
    apply e.symm.injective
    simp [h]
  · intro h a b
    apply e.injective
    simp [h]

theorem mem_lcal_iff {X J : Subgroup G} :
    J ∈ lcal X ↔ J ≤ X ∧ (J.subgroupOf X).IsSubnormal ∧ IsSimpleGroup J ∧
      ¬ IsMulCommutative J := by
  constructor
  · rintro ⟨hJX, hsub, hs, hnc⟩
    let e := Subgroup.subgroupOfEquivOfLe hJX
    exact ⟨hJX, hsub, e.symm.isSimpleGroup, fun h => hnc ((isMulCommutative_congr e).mpr h)⟩
  · rintro ⟨hJX, hsub, hs, hnc⟩
    let e := Subgroup.subgroupOfEquivOfLe hJX
    exact ⟨hJX, hsub, e.isSimpleGroup, fun h => hnc ((isMulCommutative_congr e).mp h)⟩

theorem lcal_le {X J : Subgroup G} (hJ : J ∈ lcal X) : J ≤ X := hJ.1

theorem map_conj_mem_lcal {X J : Subgroup G} (hJ : J ∈ lcal X) {g : G}
    (hg : g ∈ Subgroup.normalizer (X : Set G)) :
    J.map (MulAut.conj g).toMonoidHom ∈ lcal X := by
  obtain ⟨hJX, hsub, hs, hnc⟩ := mem_lcal_iff.mp hJ
  have hle : J.map (MulAut.conj g).toMonoidHom ≤ X := by
    rintro _ ⟨x, hx, rfl⟩
    exact (Subgroup.mem_normalizer_iff.mp hg x).mp (hJX hx)
  let φ : MulAut ↥X := X.normalizerMonoidHom ⟨g, hg⟩
  have hφ : ∀ t : X, ((φ t : X) : G) = g * t * g⁻¹ := fun t =>
    Subgroup.normalizerMonoidHom_apply_apply_coe X ⟨g, hg⟩ t
  have heq : (J.map (MulAut.conj g).toMonoidHom).subgroupOf X =
      (J.subgroupOf X).map φ.toMonoidHom := by
    ext ⟨x, hx⟩
    constructor
    · rintro ⟨j, hj, hjx⟩
      refine ⟨⟨j, hJX hj⟩, hj, Subtype.ext ?_⟩
      change ((φ ⟨j, hJX hj⟩ : X) : G) = x
      rw [hφ]
      exact hjx
    · rintro ⟨t, ht, hts⟩
      refine ⟨t, ht, ?_⟩
      have := congrArg Subtype.val hts
      change ((φ t : X) : G) = x at this
      rw [hφ] at this
      exact this
  let e := Subgroup.equivMapOfInjective J (MulAut.conj g).toMonoidHom (MulAut.conj g).injective
  refine mem_lcal_iff.mpr ⟨hle, ?_, e.symm.isSimpleGroup,
    fun h => hnc ((isMulCommutative_congr e).mpr h)⟩
  rw [heq]
  exact hsub.map (f := φ.toMonoidHom) φ.surjective

theorem map_mem_lcalOf_iff {H H' : Type*} [Group H] [Group H'] (e : H ≃* H') {J : Subgroup H} :
    J.map e.toMonoidHom ∈ lcalOf H' ↔ J ∈ lcalOf H := by
  have hmap : (J.map e.toMonoidHom).map e.symm.toMonoidHom = J := by
    rw [Subgroup.map_map]
    ext x
    simp
  let e' := Subgroup.equivMapOfInjective J e.toMonoidHom e.injective
  constructor
  · rintro ⟨hsub, hs, hnc⟩
    refine ⟨?_, e'.isSimpleGroup, fun h => hnc ((isMulCommutative_congr e').mp h)⟩
    have := hsub.map (f := e.symm.toMonoidHom) e.symm.surjective
    rwa [hmap] at this
  · rintro ⟨hsub, hs, hnc⟩
    exact ⟨hsub.map (f := e.toMonoidHom) e.surjective, e'.symm.isSimpleGroup,
      fun h => hnc ((isMulCommutative_congr e').mpr h)⟩

theorem mem_mcal_iff {X M : Subgroup G} :
    M ∈ mcal X ↔ M ≤ X ∧ sol X ≤ M ∧
      (M.subgroupOf X).map (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) ∈
        lcalOf (↥X ⧸ CFSG.solvableRadical ↥X) := Iff.rfl

theorem mcal_eq_lcal_of_sol_eq_bot {X : Subgroup G} (h : sol X = ⊥) : mcal X = lcal X := by
  have hR : CFSG.solvableRadical ↥X = ⊥ := (sol_eq_bot_iff X).mp h
  have hinj : Function.Injective (QuotientGroup.mk' (CFSG.solvableRadical ↥X)) := by
    rw [← MonoidHom.ker_eq_bot_iff, QuotientGroup.ker_mk', hR]
  let e : ↥X ≃* ↥X ⧸ CFSG.solvableRadical ↥X :=
    MulEquiv.ofBijective (QuotientGroup.mk' (CFSG.solvableRadical ↥X))
      ⟨hinj, QuotientGroup.mk'_surjective _⟩
  have he : e.toMonoidHom = QuotientGroup.mk' (CFSG.solvableRadical ↥X) := by
    ext x; rfl
  ext M
  constructor
  · rintro ⟨hMX, -, hM⟩
    refine ⟨hMX, ?_⟩
    rw [← he] at hM
    exact (map_mem_lcalOf_iff e).mp hM
  · rintro ⟨hMX, hM⟩
    refine ⟨hMX, h ▸ bot_le, ?_⟩
    rw [← he]
    exact (map_mem_lcalOf_iff e).mpr hM

theorem mcal_eq_empty_of_isSolvable {X : Subgroup G} (h : Group.IsSolvable X) : mcal X = ∅ := by
  ext M
  simp only [Set.mem_empty_iff_false, iff_false]
  rintro ⟨-, -, -, hs, hnc⟩
  apply hnc
  have h1 : Group.IsSolvable (↥X ⧸ CFSG.solvableRadical ↥X) :=
    Group.isSolvable_of_surjective (f := QuotientGroup.mk' (CFSG.solvableRadical ↥X))
      (QuotientGroup.mk'_surjective _)
  exact isMulCommutative_iff.mpr ((IsSimpleGroup.comm_iff_isSolvable).mpr inferInstance)

theorem mcal_le {X M : Subgroup G} (hM : M ∈ mcal X) : M ≤ X := hM.1

theorem sol_le_of_mem_mcal {X M : Subgroup G} (hM : M ∈ mcal X) : sol X ≤ M := hM.2.1

theorem khat_eq_of_isSolvable {X : Subgroup G} (h : Group.IsSolvable X) : khat X = X := by
  have : ltilde X = {X} := by
    ext M
    simp [ltilde, h]
  unfold khat
  rw [this]
  simp [Subgroup.le_normalizer]

theorem khat_eq_mcal (X : Subgroup G) :
    khat X = (X ⊓ ⨅ M ∈ mcal X, Subgroup.normalizer (M : Set G)) ⊔ sol X := by
  by_cases hX : Group.IsSolvable X
  · rw [khat_eq_of_isSolvable hX, mcal_eq_empty_of_isSolvable hX]
    simp [sol_le]
  · have : ltilde X = mcal X := by
      ext M
      simp [ltilde, hX]
    unfold khat
    rw [this]
    symm
    apply sup_eq_left.mpr
    refine le_inf (sol_le X) (le_iInf₂ fun M hM => ?_)
    exact (sol_le_of_mem_mcal hM).trans Subgroup.le_normalizer

theorem khat_le (X : Subgroup G) : khat X ≤ X := inf_le_left

theorem mcalA_subset (X A : Subgroup G) : mcalA X A ⊆ mcal X := fun _ hM => hM.1

theorem lcalA_subset (X A : Subgroup G) : lcalA X A ⊆ lcal X := fun _ hJ => hJ.1

theorem kUp_le (X A : Subgroup G) : kUp X A ≤ X :=
  iSup₂_le fun _ hM => (mcalA_subset X A hM).1

theorem mem_kDown_iff {X A : Subgroup G} {g : G} :
    g ∈ kDown X A ↔ g ∈ X ∧ ∀ k ∈ kUp X A, ⁅g, k⁆ ∈ sol X := by
  set R := CFSG.solvableRadical ↥X with hR
  unfold kDown
  constructor
  · rintro ⟨x, hx, rfl⟩
    refine ⟨x.2, fun k hk => ?_⟩
    have hkX : k ∈ X := kUp_le X A hk
    have hmem : QuotientGroup.mk' R ⟨k, hkX⟩ ∈
        ((kUp X A).subgroupOf X).map (QuotientGroup.mk' R) :=
      Subgroup.mem_map_of_mem _ hk
    have hcomm := Subgroup.mem_centralizer_iff.mp hx _ hmem
    have h1 : QuotientGroup.mk' R ⁅x, ⟨k, hkX⟩⁆ = 1 := by
      rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
      exact hcomm.symm
    have h2 : ⁅x, ⟨k, hkX⟩⁆ ∈ R := by
      rwa [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h1
    exact ⟨_, h2, rfl⟩
  · rintro ⟨hgX, hg⟩
    refine ⟨⟨g, hgX⟩, ?_, rfl⟩
    rw [SetLike.mem_coe, Subgroup.mem_comap, Subgroup.mem_centralizer_iff]
    rintro _ ⟨⟨k, hkX⟩, hk, rfl⟩
    have hk' : k ∈ kUp X A := hk
    obtain ⟨r, hr, hrk⟩ := hg k hk'
    have h2 : ⁅(⟨g, hgX⟩ : X), ⟨k, hkX⟩⁆ = r := Subtype.ext hrk.symm
    have h1 : QuotientGroup.mk' R ⁅(⟨g, hgX⟩ : X), ⟨k, hkX⟩⁆ = 1 := by
      rw [h2, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
      exact hr
    rw [map_commutatorElement, commutatorElement_eq_one_iff_mul_comm] at h1
    exact h1.symm

theorem kDown_le (X A : Subgroup G) : kDown X A ≤ X := Subgroup.map_subtype_le _

theorem sol_le_kDown (X A : Subgroup G) : sol X ≤ kDown X A := by
  intro s hs
  refine mem_kDown_iff.mpr ⟨sol_le X hs, fun k hk => ?_⟩
  have hkX : k ∈ X := kUp_le X A hk
  have hnorm : ((sol X).subgroupOf X).Normal := normal_sol_subgroupOf X
  have hsX : s ∈ X := sol_le X hs
  have : ⁅s, k⁆ = s * (k * s⁻¹ * k⁻¹) := by group
  rw [this]
  refine mul_mem hs ?_
  have h := hnorm.conj_mem ⟨s⁻¹, X.inv_mem hsX⟩ (inv_mem hs) ⟨k, hkX⟩
  exact h

theorem kDown_eq_of_mcalA_eq_empty {X A : Subgroup G} (h : mcalA X A = ∅) : kDown X A = X := by
  have hbot : kUp X A = ⊥ := by
    unfold kUp
    rw [h]
    simp
  refine le_antisymm (kDown_le X A) fun g hg => ?_
  refine mem_kDown_iff.mpr ⟨hg, fun k hk => ?_⟩
  rw [hbot, Subgroup.mem_bot] at hk
  subst hk
  simp [one_mem]

theorem IsDirectProduct.le {S : Set (Subgroup G)} {K : Subgroup G} (hK : IsDirectProduct S K)
    {J : Subgroup G} (hJ : J ∈ S) : J ≤ K :=
  hK.sSup_eq ▸ le_sSup hJ

theorem IsDirectProduct.sSup_diff_le {S : Set (Subgroup G)} {K : Subgroup G}
    (hK : IsDirectProduct S K) (T : Set (Subgroup G)) (hT : T ⊆ S) : sSup T ≤ K :=
  hK.sSup_eq ▸ sSup_le_sSup hT

theorem IsDirectProduct.commute_sSup_diff {S : Set (Subgroup G)} {K : Subgroup G}
    (hK : IsDirectProduct S K) {J : Subgroup G} (hJ : J ∈ S) :
    ∀ x ∈ J, ∀ y ∈ sSup (S \ {J}), Commute x y := by
  intro x hx y hy
  have : sSup (S \ {J}) ≤ Subgroup.centralizer ({x} : Set G) := by
    refine sSup_le fun J' hJ' y' hy' => ?_
    rw [Subgroup.mem_centralizer_singleton_iff]
    exact (hK.commute J' hJ'.1 J hJ hJ'.2 y' hy' x hx).eq
  exact (Subgroup.mem_centralizer_singleton_iff.mp (this hy)).symm

theorem IsDirectProduct.isDirectPair {S : Set (Subgroup G)} {K : Subgroup G}
    (hK : IsDirectProduct S K) {J : Subgroup G} (hJ : J ∈ S) :
    IsDirectPair J (sSup (S \ {J})) K where
  commute := hK.commute_sSup_diff hJ
  inf_eq_bot := disjoint_iff.mp (hK.indep hJ)
  sup_eq := by
    refine le_antisymm (sup_le (hK.le hJ) (hK.sSup_diff_le _ Set.sdiff_subset)) ?_
    rw [← hK.sSup_eq]
    refine sSup_le fun J' hJ' => ?_
    by_cases h : J' = J
    · exact h ▸ le_sup_left
    · exact le_sup_of_le_right (le_sSup ⟨hJ', h⟩)

theorem IsDirectProduct.le_normalizer {S : Set (Subgroup G)} {K : Subgroup G}
    (hK : IsDirectProduct S K) {J : Subgroup G} (hJ : J ∈ S) :
    K ≤ Subgroup.normalizer (J : Set G) := by
  rw [← hK.sSup_eq]
  refine sSup_le fun J' hJ' => ?_
  by_cases h : J' = J
  · subst h
    exact Subgroup.le_normalizer
  · intro x hx
    have hc := hK.commute J' hJ' J hJ h x hx
    have hxc : x ∈ Subgroup.centralizer (J : Set G) := fun y hy => (hc y hy).eq.symm
    exact Subgroup.centralizer_le_normalizer (J : Set G) hxc

theorem mem_proj_iff {J L X : Subgroup G} (hJL : ∀ j ∈ J, ∀ l ∈ L, Commute j l) {x : G} :
    x ∈ proj J L X ↔ x ∈ J ∧ ∃ l ∈ L, x * l ∈ X := by
  let P : Subgroup G :=
    { carrier := {j | j ∈ J ∧ ∃ l ∈ L, j * l ∈ X}
      one_mem' := ⟨one_mem _, 1, one_mem _, by simp⟩
      mul_mem' := by
        rintro a b ⟨ha, l₁, hl₁, hal⟩ ⟨hb, l₂, hl₂, hbl⟩
        refine ⟨mul_mem ha hb, l₁ * l₂, mul_mem hl₁ hl₂, ?_⟩
        have := (hJL b hb l₁ hl₁).eq
        have h : a * b * (l₁ * l₂) = (a * l₁) * (b * l₂) := by
          calc a * b * (l₁ * l₂) = a * (b * l₁) * l₂ := by group
            _ = a * (l₁ * b) * l₂ := by rw [this]
            _ = (a * l₁) * (b * l₂) := by group
        rw [h]
        exact mul_mem hal hbl
      inv_mem' := by
        rintro a ⟨ha, l, hl, hal⟩
        refine ⟨inv_mem ha, l⁻¹, inv_mem hl, ?_⟩
        have := (hJL a ha l hl).eq
        have h : a⁻¹ * l⁻¹ = (a * l)⁻¹ := by
          calc a⁻¹ * l⁻¹ = (l * a)⁻¹ := by group
            _ = (a * l)⁻¹ := by rw [← this]
        rw [h]
        exact inv_mem hal }
  have h : proj J L X = P := Subgroup.closure_eq P
  rw [h]
  rfl

theorem proj_le_left (J L X : Subgroup G) : proj J L X ≤ J :=
  (Subgroup.closure_le J).mpr fun _ h => h.1

theorem proj_mono {J L X Y : Subgroup G} (h : X ≤ Y) : proj J L X ≤ proj J L Y :=
  Subgroup.closure_mono fun _ ⟨hj, l, hl, hx⟩ => ⟨hj, l, hl, h hx⟩

theorem projIn_le {S : Set (Subgroup G)} (J X : Subgroup G) : projIn S J X ≤ J :=
  proj_le_left _ _ _

theorem mem_sectionCentralizer_iff {X Y : Subgroup G} {g : G} :
    g ∈ sectionCentralizer X Y ↔ g ∈ Subgroup.normalizer (X : Set G) ∧
      g ∈ Subgroup.normalizer (Y : Set G) ∧ ∀ y ∈ Y, ⁅g, y⁆ ∈ X := Iff.rfl

end CFSG.SignalizerFunctorTheorem.McBride

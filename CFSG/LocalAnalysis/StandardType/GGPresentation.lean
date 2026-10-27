module

public import CFSG.LieType.CurtisTits.Conclusion

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.CurtisTits CFSG.Blueprint

section Defs

variable {U : Type*} [Group U] (D : UniversalRootDatum U)

abbrev GGWeyl : Type := (coxeterMatrix D.isFiniteType).Group

@[expose] def ggSub (S : Set (Fin D.rank → ℤ)) : Subgroup U := ⨆ γ ∈ S, D.rootGroup γ

@[expose] def ggSupp (J : Finset (Fin D.rank)) : Set (Fin D.rank → ℤ) :=
  {γ | γ ∈ D.roots ∧ ∀ i ∉ J, γ i = 0}

structure GGWeylLift (ν : GGWeyl D →* U) : Prop where
  conj_mem : ∀ (w : GGWeyl D), ∀ γ ∈ D.roots, ∀ x ∈ D.rootGroup γ,
    ν w * x * (ν w)⁻¹ ∈ D.rootGroup (weylAction D.isFiniteType w γ)
  simple_mem : ∀ i, ν ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple i) ∈
    rankOne D.rootGroup i
  le_rankOne : ∀ i, ∀ γ ∈ D.roots, (∀ k, k ≠ i → γ k = 0) → D.rootGroup γ ≤ rankOne D.rootGroup i

variable {X : Type*} [Group X]

@[expose] noncomputable def ggExt {H : Subgroup U} (φ : H →* X) (u : U) : X :=
  open Classical in if h : u ∈ H then φ ⟨u, h⟩ else 1

variable {ι : Type*} (S : ι → Set (Fin D.rank → ℤ)) (φ : ∀ k, ggSub D (S k) →* X)

@[expose] def GGActsLike (ν : GGWeyl D →* U) (R : Subgroup X) (δ : R →* GGWeyl D) : Prop :=
  ∀ (r : R) (k l : ι), ∀ α ∈ S k, weylAction D.isFiniteType (δ r) α ∈ S l →
    ∀ z ∈ D.rootGroup α,
      (r : X) * ggExt (φ k) z * (r : X)⁻¹ = ggExt (φ l) (ν (δ r) * z * (ν (δ r))⁻¹)

@[expose] def GGWeylInR (ν : GGWeyl D →* U) (R : Subgroup X) (δ : R →* GGWeyl D) : Prop :=
  ∀ (k : ι) (w : GGWeyl D) (j : Fin D.rank),
    weylAction D.isFiniteType w (Pi.single j 1) ∈ S k →
      ∃ r : R, (r : X) = ggExt (φ k) (ν (w * (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j
          * w⁻¹)) ∧
        δ r = w * (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j * w⁻¹

@[expose] def GGOrbit : Prop :=
  ∀ J : Finset (Fin D.rank), J.card ≤ 2 →
    ∃ (w : GGWeyl D) (k : ι), ∀ γ ∈ ggSupp D J, weylAction D.isFiniteType w γ ∈ S k

@[expose] def ggClosure (R : Subgroup X) : Subgroup X :=
  ⨆ (r : R) (k : ι), (φ k).range.map (MulAut.conj (r : X)).toMonoidHom

end Defs

section Basic

variable {U : Type*} [Group U] {D : UniversalRootDatum U} {X : Type*} [Group X]

theorem rootGroup_le_ggSub {S : Set (Fin D.rank → ℤ)} {γ : Fin D.rank → ℤ} (hγ : γ ∈ S) :
    D.rootGroup γ ≤ ggSub D S :=
  le_iSup₂_of_le (f := fun γ (_ : γ ∈ S) => D.rootGroup γ) γ hγ le_rfl

theorem ggExt_of_mem {H : Subgroup U} (φ : H →* X) {u : U} (h : u ∈ H) :
    ggExt φ u = φ ⟨u, h⟩ := by
  simp [ggExt, h]

theorem ggExt_mul {H : Subgroup U} (φ : H →* X) {u v : U} (hu : u ∈ H) (hv : v ∈ H) :
    ggExt φ (u * v) = ggExt φ u * ggExt φ v := by
  rw [ggExt_of_mem φ hu, ggExt_of_mem φ hv, ggExt_of_mem φ (H.mul_mem hu hv), ← map_mul]
  rfl

theorem ggIsCTRootSystem (D : UniversalRootDatum U) :
    IsCTRootSystem (coxeterMatrix D.isFiniteType).toCoxeterSystem (weylAction D.isFiniteType)
      D.roots :=
  isCTRootSystem D.isFiniteType D.divisible

theorem single_mem_roots (j : Fin D.rank) : (Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots :=
  (ggIsCTRootSystem D).single_mem j

theorem neg_single_mem_roots (j : Fin D.rank) : (-Pi.single j 1 : Fin D.rank → ℤ) ∈ D.roots := by
  have h := (ggIsCTRootSystem D).smul_mem ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j)
    _ (single_mem_roots j)
  rwa [(ggIsCTRootSystem D).simple_single] at h

theorem single_mem_ggSupp {J : Finset (Fin D.rank)} {j : Fin D.rank} (hj : j ∈ J) :
    (Pi.single j 1 : Fin D.rank → ℤ) ∈ ggSupp D J :=
  ⟨single_mem_roots j, fun i hi => Pi.single_eq_of_ne (by rintro rfl; exact hi hj) _⟩

theorem neg_single_mem_ggSupp {J : Finset (Fin D.rank)} {j : Fin D.rank} (hj : j ∈ J) :
    (-Pi.single j 1 : Fin D.rank → ℤ) ∈ ggSupp D J :=
  ⟨neg_single_mem_roots j, fun i hi => by
    rw [Pi.neg_apply, Pi.single_eq_of_ne (by rintro rfl; exact hi hj), neg_zero]⟩

theorem levi_le_of_rootGroup_le {J : Finset (Fin D.rank)} {M : Subgroup U}
    (h : ∀ j ∈ J, D.rootGroup (Pi.single j 1) ≤ M ∧ D.rootGroup (-Pi.single j 1) ≤ M) :
    levi D.rootGroup J ≤ M :=
  iSup₂_le fun j hj => sup_le (h j hj).1 (h j hj).2

theorem hom_ext_levi {J : Finset (Fin D.rank)} {f g : levi D.rootGroup J →* X}
    (h : ∀ j ∈ J, ∀ γ ∈ ({Pi.single j 1, -Pi.single j 1} : Set (Fin D.rank → ℤ)),
      ∀ (u : U) (hu : u ∈ levi D.rootGroup J), u ∈ D.rootGroup γ → f ⟨u, hu⟩ = g ⟨u, hu⟩) :
    f = g := by
  have hle : levi D.rootGroup J ≤ (MonoidHom.eqLocus f g).map (levi D.rootGroup J).subtype := by
    refine levi_le_of_rootGroup_le fun j hj => ⟨fun u hu => ?_, fun u hu => ?_⟩
    · have hul : u ∈ levi D.rootGroup J :=
        rankOne_le_levi D.rootGroup hj (le_sup_left (b := D.rootGroup (-Pi.single j 1)) hu)
      exact ⟨⟨u, hul⟩, h j hj _ (Or.inl rfl) u hul hu, rfl⟩
    · have hul : u ∈ levi D.rootGroup J :=
        rankOne_le_levi D.rootGroup hj (le_sup_right (a := D.rootGroup (Pi.single j 1)) hu)
      exact ⟨⟨u, hul⟩, h j hj _ (Or.inr rfl) u hul hu, rfl⟩
  ext ⟨u, hu⟩
  obtain ⟨v, hv, hvu⟩ := hle hu
  have : v = ⟨u, hu⟩ := Subtype.ext hvu
  rw [← this]
  exact hv

theorem eq_of_levi {J J' : Finset (Fin D.rank)} {f : levi D.rootGroup J →* X}
    {g : levi D.rootGroup J' →* X}
    (h : ∀ j ∈ J, ∀ γ ∈ ({Pi.single j 1, -Pi.single j 1} : Set (Fin D.rank → ℤ)),
      ∀ (u : U) (hu : u ∈ levi D.rootGroup J) (hu' : u ∈ levi D.rootGroup J'),
        u ∈ D.rootGroup γ → f ⟨u, hu⟩ = g ⟨u, hu'⟩)
    (hJJ' : J ⊆ J') {u : U} (hu : u ∈ levi D.rootGroup J) (hu' : u ∈ levi D.rootGroup J') :
    f ⟨u, hu⟩ = g ⟨u, hu'⟩ := by
  have hsub : levi D.rootGroup J ≤ levi D.rootGroup J' := levi_mono D.rootGroup hJJ'
  let M : Subgroup U :=
    { carrier := {v | ∃ (hv : v ∈ levi D.rootGroup J), f ⟨v, hv⟩ = g ⟨v, hsub hv⟩}
      mul_mem' := by
        rintro a b ⟨ha, hfa⟩ ⟨hb, hfb⟩
        refine ⟨mul_mem ha hb, ?_⟩
        have e1 : (⟨a * b, mul_mem ha hb⟩ : levi D.rootGroup J) = ⟨a, ha⟩ * ⟨b, hb⟩ := rfl
        have e2 : (⟨a * b, hsub (mul_mem ha hb)⟩ : levi D.rootGroup J') =
            ⟨a, hsub ha⟩ * ⟨b, hsub hb⟩ := rfl
        rw [e1, e2, map_mul, map_mul, hfa, hfb]
      one_mem' := by
        refine ⟨one_mem _, ?_⟩
        have e1 : (⟨1, one_mem _⟩ : levi D.rootGroup J) = 1 := rfl
        have e2 : (⟨1, hsub (one_mem _)⟩ : levi D.rootGroup J') = 1 := rfl
        rw [e1, e2, map_one, map_one]
      inv_mem' := by
        rintro a ⟨ha, hfa⟩
        refine ⟨inv_mem ha, ?_⟩
        have e1 : (⟨a⁻¹, inv_mem ha⟩ : levi D.rootGroup J) = (⟨a, ha⟩)⁻¹ := rfl
        have e2 : (⟨a⁻¹, hsub (inv_mem ha)⟩ : levi D.rootGroup J') = (⟨a, hsub ha⟩)⁻¹ := rfl
        rw [e1, e2, map_inv, map_inv, hfa] }
  have hle : levi D.rootGroup J ≤ M := by
    refine levi_le_of_rootGroup_le fun j hj => ⟨fun v hv => ?_, fun v hv => ?_⟩
    · have hvl : v ∈ levi D.rootGroup J :=
        rankOne_le_levi D.rootGroup hj (le_sup_left (b := D.rootGroup (-Pi.single j 1)) hv)
      exact ⟨hvl, h j hj _ (Or.inl rfl) v hvl (hsub hvl) hv⟩
    · have hvl : v ∈ levi D.rootGroup J :=
        rankOne_le_levi D.rootGroup hj (le_sup_right (a := D.rootGroup (Pi.single j 1)) hv)
      exact ⟨hvl, h j hj _ (Or.inr rfl) v hvl (hsub hvl) hv⟩
  obtain ⟨hv, hfu⟩ := hle hu
  exact hfu

theorem hom_ext_ggSub {S : Set (Fin D.rank → ℤ)} {f g : ggSub D S →* X}
    (h : ∀ γ ∈ S, ∀ (u : U) (hu : u ∈ ggSub D S), u ∈ D.rootGroup γ → f ⟨u, hu⟩ = g ⟨u, hu⟩) :
    f = g := by
  have hle : ggSub D S ≤ (MonoidHom.eqLocus f g).map (ggSub D S).subtype := by
    refine iSup₂_le fun γ hγ u hu => ?_
    have hus : u ∈ ggSub D S := rootGroup_le_ggSub hγ hu
    exact ⟨⟨u, hus⟩, h γ hγ u hus hu, rfl⟩
  ext ⟨u, hu⟩
  obtain ⟨v, hv, hvu⟩ := hle hu
  have : v = ⟨u, hu⟩ := Subtype.ext hvu
  rw [← this]
  exact hv

end Basic

section Construction

variable {U : Type*} [Group U] {D : UniversalRootDatum U} {ν : GGWeyl D →* U}
  {X : Type*} [Group X] {ι : Type*} {S : ι → Set (Fin D.rank → ℤ)}
  (φ : ∀ k, ggSub D (S k) →* X) {R : Subgroup X} {δ : R →* GGWeyl D}

theorem conj_levi_mem (hν : GGWeylLift D ν) {J : Finset (Fin D.rank)} {w : GGWeyl D}
    {T : Set (Fin D.rank → ℤ)} (hw : ∀ γ ∈ ggSupp D J, weylAction D.isFiniteType w γ ∈ T)
    {u : U} (hu : u ∈ levi D.rootGroup J) : ν w * u * (ν w)⁻¹ ∈ ggSub D T := by
  have hle : levi D.rootGroup J ≤ (ggSub D T).comap (MulAut.conj (ν w)).toMonoidHom := by
    refine levi_le_of_rootGroup_le fun j hj => ⟨fun x hx => ?_, fun x hx => ?_⟩
    · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact rootGroup_le_ggSub (hw _ (single_mem_ggSupp hj))
        (hν.conj_mem w _ (single_mem_roots j) x hx)
    · simp only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact rootGroup_le_ggSub (hw _ (neg_single_mem_ggSupp hj))
        (hν.conj_mem w _ (neg_single_mem_roots j) x hx)
  have := hle hu
  simpa only [Subgroup.mem_comap, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using this

@[expose] noncomputable def ggLeviHom (hν : GGWeylLift D ν) (J : Finset (Fin D.rank)) (r : R)
    (k : ι) (h : ∀ γ ∈ ggSupp D J, weylAction D.isFiniteType (δ r) γ ∈ S k) :
    levi D.rootGroup J →* X :=
  (MulAut.conj ((r : X)⁻¹)).toMonoidHom.comp ((φ k).comp
    (((MulAut.conj (ν (δ r))).toMonoidHom.domRestrict (levi D.rootGroup J)).codRestrict
      (ggSub D (S k)) fun u => conj_levi_mem hν h u.2))

theorem ggLeviHom_apply (hν : GGWeylLift D ν) (J : Finset (Fin D.rank)) (r : R) (k : ι)
    (h : ∀ γ ∈ ggSupp D J, weylAction D.isFiniteType (δ r) γ ∈ S k) (u : levi D.rootGroup J) :
    ggLeviHom φ hν J r k h u =
      (r : X)⁻¹ * ggExt (φ k) (ν (δ r) * u * (ν (δ r))⁻¹) * r := by
  rw [ggExt_of_mem (φ k) (conj_levi_mem hν h u.2)]
  simp only [ggLeviHom, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    inv_inv]
  rfl

variable {φ}

theorem ggLeviHom_eq (hC : GGActsLike D S φ ν R δ) (hν : GGWeylLift D ν)
    {J : Finset (Fin D.rank)} {r : R} {k : ι}
    (h : ∀ γ ∈ ggSupp D J, weylAction D.isFiniteType (δ r) γ ∈ S k) {γ : Fin D.rank → ℤ}
    (hγ : γ ∈ ggSupp D J) {u : U} (hu : u ∈ D.rootGroup γ) (hul : u ∈ levi D.rootGroup J)
    (s : R) (l : ι) (hs : weylAction D.isFiniteType (δ s) γ ∈ S l) :
    ggLeviHom φ hν J r k h ⟨u, hul⟩ =
      (s : X)⁻¹ * ggExt (φ l) (ν (δ s) * u * (ν (δ s))⁻¹) * s := by
  rw [ggLeviHom_apply]
  have hα : weylAction D.isFiniteType (δ r) γ ∈ S k := h γ hγ
  have hz : ν (δ r) * u * (ν (δ r))⁻¹ ∈ D.rootGroup (weylAction D.isFiniteType (δ r) γ) :=
    hν.conj_mem _ γ hγ.1 u hu
  have hα' : weylAction D.isFiniteType (δ (s * r⁻¹)) (weylAction D.isFiniteType (δ r) γ) ∈
      S l := by
    rwa [show δ (s * r⁻¹) = δ s * (δ r)⁻¹ by simp, weylAction_mul_apply,
      weylAction_inv_apply_apply]
  have key := hC (s * r⁻¹) k l _ hα hα' _ hz
  have hconj : ν (δ (s * r⁻¹)) * (ν (δ r) * u * (ν (δ r))⁻¹) * (ν (δ (s * r⁻¹)))⁻¹ =
      ν (δ s) * u * (ν (δ s))⁻¹ := by
    simp only [map_mul, map_inv]
    group
  rw [hconj] at key
  rw [← key]
  simp only [Subgroup.coe_mul, Subgroup.coe_inv]
  group

theorem exists_ggChoice (hδ : Function.Surjective δ) (horb : GGOrbit D S) :
    ∃ (rJ : {J : Finset (Fin D.rank) // J.card ≤ 2} → R)
      (kJ : {J : Finset (Fin D.rank) // J.card ≤ 2} → ι),
      ∀ J, ∀ γ ∈ ggSupp D J.1, weylAction D.isFiniteType (δ (rJ J)) γ ∈ S (kJ J) := by
  choose w k hwk using fun J : {J : Finset (Fin D.rank) // J.card ≤ 2} => horb J.1 J.2
  choose r hr using fun J => hδ (w J)
  exact ⟨r, k, fun J γ hγ => by rw [hr J]; exact hwk J γ hγ⟩

variable (φ) in
@[expose] noncomputable def ggFamily (hν : GGWeylLift D ν)
    (rJ : {J : Finset (Fin D.rank) // J.card ≤ 2} → R)
    (kJ : {J : Finset (Fin D.rank) // J.card ≤ 2} → ι)
    (hJ : ∀ J, ∀ γ ∈ ggSupp D J.1, weylAction D.isFiniteType (δ (rJ J)) γ ∈ S (kJ J)) :
    ∀ J, D.leviAmalgam J →* X :=
  fun J => ggLeviHom φ hν J.1 (rJ J) (kJ J) (hJ J)

theorem ggFamily_apply (hν : GGWeylLift D ν)
    (rJ : {J : Finset (Fin D.rank) // J.card ≤ 2} → R)
    (kJ : {J : Finset (Fin D.rank) // J.card ≤ 2} → ι)
    (hJ : ∀ J, ∀ γ ∈ ggSupp D J.1, weylAction D.isFiniteType (δ (rJ J)) γ ∈ S (kJ J))
    (J : {J : Finset (Fin D.rank) // J.card ≤ 2}) (x : D.leviAmalgam J) :
    ggFamily φ hν rJ kJ hJ J x = ggLeviHom φ hν J.1 (rJ J) (kJ J) (hJ J) x :=
  rfl

theorem ggFamily_isCompatible (hC : GGActsLike D S φ ν R δ) (hν : GGWeylLift D ν)
    (rJ : {J : Finset (Fin D.rank) // J.card ≤ 2} → R)
    (kJ : {J : Finset (Fin D.rank) // J.card ≤ 2} → ι)
    (hJ : ∀ J, ∀ γ ∈ ggSupp D J.1, weylAction D.isFiniteType (δ (rJ J)) γ ∈ S (kJ J)) :
    IsCompatible D.leviAmalgam (ggFamily φ hν rJ kJ hJ) := by
  rintro A B hAB ⟨u, hu⟩ ⟨v, hv⟩ hxy
  obtain rfl : u = v := hxy
  rw [ggFamily_apply, ggFamily_apply]
  refine eq_of_levi (fun j hj γ hγ w hw hw' hwγ => ?_) hAB hu hv
  have hγA : γ ∈ ggSupp D A.1 := by
    rcases hγ with rfl | rfl
    exacts [single_mem_ggSupp hj, neg_single_mem_ggSupp hj]
  have hγB : γ ∈ ggSupp D B.1 := ⟨hγA.1, fun i hi => hγA.2 i fun hiA => hi (hAB hiA)⟩
  rw [ggLeviHom_eq hC hν (hJ B) hγB hwγ hw' (rJ A) (kJ A) (hJ A γ hγA), ggLeviHom_apply]

end Construction

section Main

open CFSG.Assembly.LowTwoRank

universe w

theorem exists_ggRootDecomp {U : Type*} [Group U] {D : UniversalRootDatum U} {ν : GGWeyl D →* U}
    (hν : GGWeylLift D ν) {γ : Fin D.rank → ℤ} (hγ : γ ∈ D.roots) :
    ∃ (v : GGWeyl D) (i : Fin D.rank) (β : Fin D.rank → ℤ),
      β ∈ ggSupp D {i} ∧ weylAction D.isFiniteType v β = γ ∧
      ∀ z ∈ D.rootGroup γ, ν v⁻¹ * z * (ν v⁻¹)⁻¹ ∈ D.rootGroup β ∧
        ν v⁻¹ * z * (ν v⁻¹)⁻¹ ∈ levi D.rootGroup {i} := by
  obtain ⟨v, i, c, -, hγc⟩ := (ggIsCTRootSystem D).exists_eq γ hγ
  have hβ : weylAction D.isFiniteType v⁻¹ γ = c • Pi.single i 1 := by
    rw [hγc, map_zsmul, weylAction_inv_apply_apply]
  have hβroot : weylAction D.isFiniteType v⁻¹ γ ∈ D.roots :=
    (ggIsCTRootSystem D).smul_mem _ _ hγ
  have hsupp : ∀ m, m ≠ i → weylAction D.isFiniteType v⁻¹ γ m = 0 := fun m hm => by
    rw [hβ, Pi.smul_apply, Pi.single_eq_of_ne hm, smul_zero]
  refine ⟨v, i, _, ⟨hβroot, fun m hm => hsupp m (by simpa using hm)⟩,
    weylAction_apply_inv_apply D.isFiniteType v γ, fun z hz => ?_⟩
  have h1 := hν.conj_mem v⁻¹ γ hγ z hz
  refine ⟨h1, ?_⟩
  rw [levi_singleton]
  exact hν.le_rankOne i _ hβroot hsupp h1

theorem ggPresentation {U : Type} [Group U] {D : UniversalRootDatum U} {t : StatedLieTag}
    {n p f : ℕ} (hCT : CurtisTitsConclusion.{w} D t n p f) {ν : GGWeyl D →* U}
    (hν : GGWeylLift D ν) {X : Type} [Group X] {ι : Type*} {S : ι → Set (Fin D.rank → ℤ)}
    (hS : ∀ k, S k ⊆ D.roots) (φ : ∀ k, ggSub D (S k) →* X) {R : Subgroup X}
    {δ : R →* GGWeyl D} (hδ : Function.Surjective δ) (hC : GGActsLike D S φ ν R δ)
    (hW : GGWeylInR D S φ ν R δ) (horb : GGOrbit D S)
    (hnt : ∃ k, ∃ γ ∈ S k, ∃ z ∈ D.rootGroup γ, ggExt (φ k) z ≠ 1) :
    ∃ ψ : U →* X,
      (∀ k (x : ggSub D (S k)), ψ x = φ k x) ∧
      (∀ (r : R) (u : U), ψ (ν (δ r) * u * (ν (δ r))⁻¹) = r * ψ u * (r : X)⁻¹) ∧
      (∀ w : GGWeyl D, ∃ r : R, (r : X) = ψ (ν w) ∧ δ r = w) ∧
      ψ.range = ggClosure D S φ R ∧ ψ.ker ≤ Subgroup.center U ∧
      IsQuasisimple (ggClosure D S φ R) ∧
      LieModel (ggClosure D S φ R ⧸ Subgroup.center (ggClosure D S φ R)) t n p f := by
  obtain ⟨rJ, kJ, hJ⟩ := exists_ggChoice hδ horb
  have hFcomp : IsCompatible D.leviAmalgam (ggFamily φ hν rJ kJ hJ) :=
    ggFamily_isCompatible hC hν rJ kJ hJ
  have hFeq : ∀ J {γ : Fin D.rank → ℤ}, γ ∈ ggSupp D J.1 → ∀ {u : U}
      (_ : u ∈ D.rootGroup γ) (hul : u ∈ D.leviAmalgam J) (s : R) (l : ι),
      weylAction D.isFiniteType (δ s) γ ∈ S l →
        ggFamily φ hν rJ kJ hJ J ⟨u, hul⟩ =
          (s : X)⁻¹ * ggExt (φ l) (ν (δ s) * u * (ν (δ s))⁻¹) * s := by
    intro J γ hγ u hu hul s l hs
    exact ggLeviHom_eq hC hν (hJ J) hγ hu hul s l hs
  have hFapp : ∀ J (u : U) (hul : u ∈ D.leviAmalgam J),
      ggFamily φ hν rJ kJ hJ J ⟨u, hul⟩ = ((rJ J : R) : X)⁻¹ *
        ggExt (φ (kJ J)) (ν (δ (rJ J)) * u * (ν (δ (rJ J)))⁻¹) * rJ J := by
    intro J u hul
    exact ggLeviHom_apply φ hν J.1 (rJ J) (kJ J) (hJ J) ⟨u, hul⟩
  generalize ggFamily φ hν rJ kJ hJ = F at hFcomp hFeq hFapp
  have hntF : ∃ J, ∃ x : D.leviAmalgam J, F J x ≠ 1 := by
    obtain ⟨k, γ, hγS, z, hz, hz1⟩ := hnt
    obtain ⟨v, i, β, hβ, hvβ, hu⟩ := exists_ggRootDecomp hν (hS k hγS)
    obtain ⟨hu1, hu2⟩ := hu z hz
    obtain ⟨s, hs⟩ := hδ v
    refine ⟨⟨{i}, by simp⟩, ⟨_, hu2⟩, fun h1 => hz1 ?_⟩
    rw [hFeq ⟨{i}, by simp⟩ hβ hu1 hu2 s k (by rw [hs, hvβ]; exact hγS)] at h1
    have hz' : ν (δ s) * (ν v⁻¹ * z * (ν v⁻¹)⁻¹) * (ν (δ s))⁻¹ = z := by
      rw [hs, map_inv]
      group
    rw [hz'] at h1
    calc ggExt (φ k) z = (s : X) * ((s : X)⁻¹ * ggExt (φ k) z * s) * (s : X)⁻¹ := by group
      _ = 1 := by rw [h1]; group
  obtain ⟨I', hI'⟩ : ∃ I' : Subgroup X, I' = ⨆ J, (F J).range := ⟨_, rfl⟩
  have hmemI : ∀ J x, F J x ∈ I' := fun J x => hI' ▸ Subgroup.mem_iSup_of_mem J ⟨x, rfl⟩
  let F' : ∀ J, D.leviAmalgam J →* I' := fun J => (F J).codRestrict I' (hmemI J)
  have hF'comp : IsCompatible D.leviAmalgam F' :=
    fun A B hAB x y hxy => Subtype.ext (hFcomp A B hAB x y hxy)
  have hF'gen : ⨆ J, (F' J).range = ⊤ := by
    rw [eq_top_iff]
    rintro ⟨g, hg⟩ -
    have hg' : g ∈ ⨆ J, (F J).range := hI' ▸ hg
    have key : ∀ (g : X) (hg' : g ∈ ⨆ J, (F J).range),
        (⟨g, hI' ▸ hg'⟩ : I') ∈ ⨆ J, (F' J).range := by
      intro g hg'
      refine Subgroup.iSup_induction' (fun J => (F J).range)
        (C := fun g hg' => (⟨g, hI' ▸ hg'⟩ : I') ∈ ⨆ J, (F' J).range) ?_ ?_ ?_ hg'
      · rintro J _ ⟨x, rfl⟩
        exact Subgroup.mem_iSup_of_mem J ⟨x, rfl⟩
      · exact Subgroup.one_mem _
      · intro a b ha hb hA hB
        exact Subgroup.mul_mem _ hA hB
    exact key g hg'
  have hntF' : ∃ J, ∃ x, F' J x ≠ 1 := by
    obtain ⟨J, x, hx⟩ := hntF
    exact ⟨J, x, fun h => hx (congrArg Subtype.val h)⟩
  obtain ⟨ψ', hψ', hsurj, hker, hq, -, -, hmodel⟩ := hCT.2.2.1 I' F' hF'comp hF'gen hntF'
  set ψ : U →* X := I'.subtype.comp ψ' with hψdef
  have hψJ : ∀ J (u : U) (hul : u ∈ D.leviAmalgam J), ψ u = F J ⟨u, hul⟩ := by
    intro J u hul
    exact congrArg Subtype.val (hψ' J ⟨u, hul⟩)
  have hrange : ψ.range = I' := by
    ext g
    constructor
    · rintro ⟨u, rfl⟩
      exact (ψ' u).2
    · intro hg
      obtain ⟨u, hu⟩ := hsurj ⟨g, hg⟩
      exact ⟨u, congrArg Subtype.val hu⟩
  have hgenU : ⨆ J, D.leviAmalgam J = ⊤ := hCT.1.1
  have hsimple : ∀ j, ∃ r : R,
      (r : X) = ψ (ν ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j)) ∧
        δ r = (coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j := by
    intro j
    have hmem : ν ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j) ∈
        D.leviAmalgam ⟨{j}, by simp⟩ := by
      show _ ∈ levi D.rootGroup {j}
      rw [levi_singleton]
      exact hν.simple_mem j
    have hj : weylAction D.isFiniteType (δ (rJ ⟨{j}, by simp⟩)) (Pi.single j 1) ∈
        S (kJ ⟨{j}, by simp⟩) :=
      hJ _ _ (single_mem_ggSupp (Finset.mem_singleton_self j))
    obtain ⟨t, ht, htδ⟩ := hW (kJ ⟨{j}, by simp⟩) (δ (rJ ⟨{j}, by simp⟩)) j hj
    refine ⟨(rJ ⟨{j}, by simp⟩)⁻¹ * t * rJ ⟨{j}, by simp⟩, ?_, ?_⟩
    · rw [hψJ _ _ hmem, hFapp _ _ hmem]
      simp only [map_mul, map_inv] at ht
      rw [← ht]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    · rw [map_mul, map_mul, map_inv, htδ]
      group
  have hWR : ∀ w : GGWeyl D, ψ (ν w) ∈ R := by
    intro w
    have hle : (⊤ : Subgroup (GGWeyl D)) ≤ R.comap (ψ.comp ν) := by
      rw [← (coxeterMatrix D.isFiniteType).toCoxeterSystem.subgroup_closure_range_simple,
        Subgroup.closure_le]
      rintro _ ⟨j, rfl⟩
      obtain ⟨r, hr, -⟩ := hsimple j
      show ψ (ν _) ∈ R
      rw [← hr]
      exact r.2
    exact hle (Subgroup.mem_top w)
  set θ : GGWeyl D →* R := (ψ.comp ν).codRestrict R hWR with hθdef
  have hθX : ∀ w, ((θ w : R) : X) = ψ (ν w) := fun w => rfl
  have hθ : ∀ w, δ (θ w) = w := by
    have h : δ.comp θ = MonoidHom.id _ := by
      apply (coxeterMatrix D.isFiniteType).toCoxeterSystem.ext_simple
      intro j
      obtain ⟨r, hr, hrδ⟩ := hsimple j
      have h1 : θ ((coxeterMatrix D.isFiniteType).toCoxeterSystem.simple j) = r :=
        Subtype.ext ((hθX _).trans hr.symm)
      rw [MonoidHom.comp_apply, h1, hrδ, MonoidHom.id_apply]
    intro w
    exact DFunLike.congr_fun h w
  have hcent : ∀ c : R, δ c = 1 → ∀ u : U, (c : X) * ψ u = ψ u * c := by
    intro c hc
    have key : ∀ J, ∀ γ ∈ ggSupp D J.1, ∀ x ∈ D.rootGroup γ, ∀ hxl : x ∈ D.leviAmalgam J,
        (c : X) * ψ x = ψ x * c := by
      intro J γ hγ x hx hxl
      have e2 : δ (rJ J * c) = δ (rJ J) := by rw [map_mul, hc, mul_one]
      have hs : weylAction D.isFiniteType (δ (rJ J * c)) γ ∈ S (kJ J) := by
        rw [e2]
        exact hJ J γ hγ
      have e1 := hFeq J hγ hx hxl (rJ J * c) (kJ J) hs
      rw [e2] at e1
      have e3 : F J ⟨x, hxl⟩ = (c : X)⁻¹ * F J ⟨x, hxl⟩ * c := by
        conv_lhs => rw [e1]
        rw [hFapp J x hxl]
        simp only [Subgroup.coe_mul, mul_inv_rev]
        group
      rw [hψJ J x hxl]
      calc (c : X) * F J ⟨x, hxl⟩ = c * ((c : X)⁻¹ * F J ⟨x, hxl⟩ * c) := by rw [← e3]
        _ = F J ⟨x, hxl⟩ * c := by group
    have hle : (⊤ : Subgroup U) ≤ (Subgroup.centralizer {(c : X)}).comap ψ := by
      rw [← hgenU]
      refine iSup_le fun J => ?_
      refine levi_le_of_rootGroup_le fun j hj => ⟨fun x hx => ?_, fun x hx => ?_⟩
      · have hxl : x ∈ D.leviAmalgam J :=
          rankOne_le_levi D.rootGroup hj (le_sup_left (b := D.rootGroup (-Pi.single j 1)) hx)
        exact Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          (key J _ (single_mem_ggSupp hj) x hx hxl).symm)
      · have hxl : x ∈ D.leviAmalgam J :=
          rankOne_le_levi D.rootGroup hj (le_sup_right (a := D.rootGroup (Pi.single j 1)) hx)
        exact Subgroup.mem_comap.mpr (Subgroup.mem_centralizer_singleton_iff.mpr
          (key J _ (neg_single_mem_ggSupp hj) x hx hxl).symm)
    intro u
    exact (Subgroup.mem_centralizer_singleton_iff.mp
      (Subgroup.mem_comap.mp (hle (Subgroup.mem_top u)))).symm
  have hequiv : ∀ (r : R) (u : U), ψ (ν (δ r) * u * (ν (δ r))⁻¹) = r * ψ u * (r : X)⁻¹ := by
    intro r u
    have hc : δ (r⁻¹ * θ (δ r)) = 1 := by rw [map_mul, map_inv, hθ, inv_mul_cancel]
    have h1 := hcent _ hc u
    have e : θ (δ r) = r * (r⁻¹ * θ (δ r)) := by group
    rw [map_mul, map_mul, map_inv, ← hθX, e]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv] at h1 ⊢
    calc (r : X) * ((r : X)⁻¹ * (θ (δ r) : X)) * ψ u * ((r : X) * ((r : X)⁻¹ * (θ (δ r) : X)))⁻¹
        = r * (((r : X)⁻¹ * (θ (δ r) : X)) * ψ u) * ((r : X)⁻¹ * (θ (δ r) : X))⁻¹ *
            (r : X)⁻¹ := by group
      _ = r * (ψ u * ((r : X)⁻¹ * (θ (δ r) : X))) * ((r : X)⁻¹ * (θ (δ r) : X))⁻¹ *
            (r : X)⁻¹ := by rw [h1]
      _ = r * ψ u * (r : X)⁻¹ := by group
  have hroot : ∀ k, ∀ γ ∈ S k, ∀ z ∈ D.rootGroup γ, ψ z = ggExt (φ k) z := by
    intro k γ hγS z hz
    obtain ⟨v, i, β, hβ, hvβ, hu⟩ := exists_ggRootDecomp hν (hS k hγS)
    obtain ⟨hu1, hu2⟩ := hu z hz
    obtain ⟨s, hs⟩ := hδ v
    have hz' : ν (δ s) * (ν v⁻¹ * z * (ν v⁻¹)⁻¹) * (ν (δ s))⁻¹ = z := by
      rw [hs, map_inv]
      group
    have e1 := hFeq ⟨{i}, by simp⟩ hβ hu1 hu2 s k (by rw [hs, hvβ]; exact hγS)
    rw [hz'] at e1
    have e2 := hequiv s (ν v⁻¹ * z * (ν v⁻¹)⁻¹)
    rw [hz', hψJ ⟨{i}, by simp⟩ _ hu2, e1] at e2
    rw [e2]
    group
  have hext : ∀ k (x : ggSub D (S k)), ψ x = φ k x := by
    intro k
    have h : ψ.domRestrict (ggSub D (S k)) = φ k := hom_ext_ggSub fun γ hγ u hu huγ => by
      rw [MonoidHom.domRestrict_apply, hroot k γ hγ u huγ, ggExt_of_mem (φ k) hu]
    intro x
    rw [← h, MonoidHom.domRestrict_apply]
  have hclos : ψ.range = ggClosure D S φ R := by
    apply le_antisymm
    · rw [hrange, hI']
      refine iSup_le fun J => ?_
      rintro _ ⟨⟨x, hx⟩, rfl⟩
      refine Subgroup.mem_iSup_of_mem ((rJ J)⁻¹) (Subgroup.mem_iSup_of_mem (kJ J) ?_)
      refine ⟨φ (kJ J) ⟨_, conj_levi_mem hν (hJ J) hx⟩, ⟨_, rfl⟩, ?_⟩
      rw [hFapp J x hx, ggExt_of_mem (φ (kJ J)) (conj_levi_mem hν (hJ J) hx)]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Subgroup.coe_inv, inv_inv]
    · refine iSup_le fun r => iSup_le fun k => ?_
      rintro _ ⟨_, ⟨x, rfl⟩, rfl⟩
      refine ⟨ν (δ r) * x * (ν (δ r))⁻¹, ?_⟩
      rw [hequiv r x, hext k x]
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have hIC : I' = ggClosure D S φ R := hrange.symm.trans hclos
  refine ⟨ψ, hext, hequiv, fun w => ⟨θ w, hθX w, hθ w⟩, hclos, ?_, hIC ▸ hq, hIC ▸ hmodel⟩
  intro u hu
  apply hker
  rw [MonoidHom.mem_ker] at hu ⊢
  exact Subtype.ext hu

end Main

end CFSG.StandardType

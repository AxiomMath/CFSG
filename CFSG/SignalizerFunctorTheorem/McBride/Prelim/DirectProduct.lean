module

public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Basic

public section

open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride

variable {G : Type*} [Group G]

theorem mem_sup_iff_of_commute {J L : Subgroup G} (h : ∀ x ∈ J, ∀ y ∈ L, Commute x y) {z : G} :
    z ∈ J ⊔ L ↔ ∃ j ∈ J, ∃ l ∈ L, j * l = z := by
  constructor
  · intro hz
    let P : Subgroup G :=
      { carrier := {z | ∃ j ∈ J, ∃ l ∈ L, j * l = z}
        one_mem' := ⟨1, one_mem _, 1, one_mem _, one_mul 1⟩
        mul_mem' := by
          rintro _ _ ⟨j₁, hj₁, l₁, hl₁, rfl⟩ ⟨j₂, hj₂, l₂, hl₂, rfl⟩
          refine ⟨j₁ * j₂, mul_mem hj₁ hj₂, l₁ * l₂, mul_mem hl₁ hl₂, ?_⟩
          have := (h j₂ hj₂ l₁ hl₁).eq
          calc j₁ * j₂ * (l₁ * l₂) = j₁ * (j₂ * l₁) * l₂ := by group
            _ = j₁ * (l₁ * j₂) * l₂ := by rw [this]
            _ = j₁ * l₁ * (j₂ * l₂) := by group
        inv_mem' := by
          rintro _ ⟨j, hj, l, hl, rfl⟩
          refine ⟨j⁻¹, inv_mem hj, l⁻¹, inv_mem hl, ?_⟩
          have := (h j hj l hl).eq
          calc j⁻¹ * l⁻¹ = (l * j)⁻¹ := by group
            _ = (j * l)⁻¹ := by rw [this] }
    have hle : J ⊔ L ≤ P := sup_le (fun j hj => ⟨j, hj, 1, one_mem _, mul_one j⟩)
      (fun l hl => ⟨1, one_mem _, l, hl, one_mul l⟩)
    exact hle hz
  · rintro ⟨j, hj, l, hl, rfl⟩
    exact mul_mem (Subgroup.mem_sup_left hj) (Subgroup.mem_sup_right hl)

namespace IsDirectProduct

variable {S : Set (Subgroup G)} {K : Subgroup G}

theorem iSupIndep' (hK : IsDirectProduct S K) : iSupIndep (fun J : S => (J : Subgroup G)) :=
  (sSupIndep_iff S).mp hK.indep

theorem iSup_eq (hK : IsDirectProduct S K) : (⨆ J : S, (J : Subgroup G)) = K := by
  rw [← sSup_eq_iSup', hK.sSup_eq]

theorem exists_mulEquiv [Finite G] (hK : IsDirectProduct S K) :
    ∃ e : ((J : S) → (J : Subgroup G)) ≃* K, ∀ (J : S) (x : (J' : S) → (J' : Subgroup G)),
      (∀ J', J' ≠ J → x J' = 1) → (e x : G) = x J := by
  have : Finite S := Set.toFinite S
  obtain ⟨e, he⟩ := CFSG.LocalCores.exists_mulEquiv_pi_iSup (fun J : S => (J : Subgroup G))
    (fun J L hJL x y hx hy => hK.commute J J.2 L L.2 (fun h => hJL (Subtype.ext h)) x hx y hy)
    hK.iSupIndep'
  refine ⟨e.trans (MulEquiv.subgroupCongr hK.iSup_eq), fun J x hx => ?_⟩
  exact he J x hx

noncomputable def equiv [Finite G] (hK : IsDirectProduct S K) :
    ((J : S) → (J : Subgroup G)) ≃* K :=
  hK.exists_mulEquiv.choose

theorem equiv_apply_of_eq_one [Finite G] (hK : IsDirectProduct S K) (J : S)
    (x : (J' : S) → (J' : Subgroup G)) (hx : ∀ J', J' ≠ J → x J' = 1) :
    (hK.equiv x : G) = x J :=
  hK.exists_mulEquiv.choose_spec J x hx

noncomputable def coord [Finite G] (hK : IsDirectProduct S K) {J : Subgroup G} (hJ : J ∈ S) :
    K →* J :=
  (Pi.evalMonoidHom (fun J' : S => (J' : Subgroup G)) ⟨J, hJ⟩).comp hK.equiv.symm.toMonoidHom

theorem coord_of_mem [Finite G] (hK : IsDirectProduct S K) {J : Subgroup G} (hJ : J ∈ S)
    {x : G} (hx : x ∈ J) : ((hK.coord hJ ⟨x, hK.le hJ hx⟩ : J) : G) = x := by
  classical
  have h : hK.equiv (Pi.mulSingle (⟨J, hJ⟩ : S) ⟨x, hx⟩) = ⟨x, hK.le hJ hx⟩ := by
    apply Subtype.ext
    rw [hK.equiv_apply_of_eq_one ⟨J, hJ⟩ _ (fun J' hJ' => Pi.mulSingle_eq_of_ne hJ' _)]
    simp
  have h2 : hK.equiv.symm ⟨x, hK.le hJ hx⟩ = Pi.mulSingle (⟨J, hJ⟩ : S) ⟨x, hx⟩ := by
    rw [MulEquiv.symm_apply_eq, h]
  simp [coord, h2]

theorem coord_of_mem_ne [Finite G] (hK : IsDirectProduct S K) {J J' : Subgroup G} (hJ : J ∈ S)
    (hJ' : J' ∈ S) (hne : J' ≠ J) {x : G} (hx : x ∈ J') :
    hK.coord hJ ⟨x, hK.le hJ' hx⟩ = 1 := by
  classical
  have h : hK.equiv (Pi.mulSingle (⟨J', hJ'⟩ : S) ⟨x, hx⟩) = ⟨x, hK.le hJ' hx⟩ := by
    apply Subtype.ext
    rw [hK.equiv_apply_of_eq_one ⟨J', hJ'⟩ _ (fun J'' hJ'' => Pi.mulSingle_eq_of_ne hJ'' _)]
    simp
  have h2 : hK.equiv.symm ⟨x, hK.le hJ' hx⟩ = Pi.mulSingle (⟨J', hJ'⟩ : S) ⟨x, hx⟩ := by
    rw [MulEquiv.symm_apply_eq, h]
  have hne' : (⟨J, hJ⟩ : S) ≠ ⟨J', hJ'⟩ := fun h => hne (congrArg Subtype.val h).symm
  simp [coord, h2, Pi.mulSingle_eq_of_ne hne']

theorem coord_mul [Finite G] (hK : IsDirectProduct S K) {J : Subgroup G} (hJ : J ∈ S) {x l : G}
    (hx : x ∈ J) (hl : l ∈ sSup (S \ {J})) :
    ((hK.coord hJ ⟨x * l, mul_mem (hK.le hJ hx) (hK.sSup_diff_le _ Set.sdiff_subset hl)⟩ : J) :
      G) = x := by
  have hker : l ∈ (hK.coord hJ).ker.map K.subtype := by
    have : sSup (S \ {J}) ≤ (hK.coord hJ).ker.map K.subtype := by
      refine sSup_le fun J' hJ' y hy => ?_
      refine ⟨⟨y, hK.le hJ'.1 hy⟩, ?_, rfl⟩
      exact hK.coord_of_mem_ne hJ hJ'.1 hJ'.2 hy
    exact this hl
  obtain ⟨k, hk, hkl⟩ := hker
  have hk1 : hK.coord hJ k = 1 := hk
  have hmul : (⟨x * l, mul_mem (hK.le hJ hx) (hK.sSup_diff_le _ Set.sdiff_subset hl)⟩ : K) =
      ⟨x, hK.le hJ hx⟩ * k := Subtype.ext (by simp only [Subgroup.coe_mul, ← hkl]; rfl)
  rw [hmul, map_mul, hk1, mul_one]
  exact hK.coord_of_mem hJ hx

end IsDirectProduct

namespace IsDirectProduct

variable {S : Set (Subgroup G)} {K : Subgroup G}

theorem coord_eq_one_iff [Finite G] (hK : IsDirectProduct S K) {J : Subgroup G} (hJ : J ∈ S)
    (y : K) : hK.coord hJ y = 1 ↔ (y : G) ∈ sSup (S \ {J}) := by
  constructor
  · intro h
    have hy : (y : G) ∈ J ⊔ sSup (S \ {J}) := (hK.isDirectPair hJ).sup_eq ▸ y.2
    obtain ⟨j, hj, l, hl, hjl⟩ := (mem_sup_iff_of_commute (hK.commute_sSup_diff hJ)).mp hy
    have h1 := hK.coord_mul hJ hj hl
    have hy' : (⟨j * l, mul_mem (hK.le hJ hj) (hK.sSup_diff_le _ Set.sdiff_subset hl)⟩ : K) = y :=
      Subtype.ext hjl
    rw [hy', h] at h1
    have hj1 : j = 1 := by simpa using h1.symm
    rw [← hjl, hj1, one_mul]
    exact hl
  · intro hy
    have h1 := hK.coord_mul hJ (one_mem J) hy
    have hy' : (⟨1 * (y : G), mul_mem (hK.le hJ (one_mem J))
        (hK.sSup_diff_le _ Set.sdiff_subset hy)⟩ : K) = y := Subtype.ext (one_mul _)
    rw [hy'] at h1
    exact Subtype.ext (by simpa using h1)

theorem coord_equiv [Finite G] (hK : IsDirectProduct S K) {J : Subgroup G} (hJ : J ∈ S)
    (z : (J' : S) → (J' : Subgroup G)) : hK.coord hJ (hK.equiv z) = z ⟨J, hJ⟩ := by
  simp [coord]

theorem ext_coord [Finite G] (hK : IsDirectProduct S K) {y y' : K}
    (h : ∀ (J : Subgroup G) (hJ : J ∈ S), hK.coord hJ y = hK.coord hJ y') : y = y' := by
  apply hK.equiv.symm.injective
  funext J
  exact h J J.2

theorem conj_mem (hK : IsDirectProduct S K) {a : G}
    (ha : ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S) {y : G} (hy : y ∈ K) :
    a * y * a⁻¹ ∈ K := by
  have : sSup S ≤ K.comap (MulAut.conj a).toMonoidHom :=
    sSup_le fun J hJ z hz => hK.le (ha J hJ) ⟨z, hz, rfl⟩
  rw [hK.sSup_eq] at this
  exact this hy

theorem map_conj_sSup_diff_le (a : G) (J : Subgroup G)
    (ha : ∀ J'' ∈ S, J''.map (MulAut.conj a).toMonoidHom ∈ S) :
    (sSup (S \ {J})).map (MulAut.conj a).toMonoidHom ≤
      sSup (S \ {J.map (MulAut.conj a).toMonoidHom}) := by
  rw [Subgroup.map_le_iff_le_comap]
  refine sSup_le fun J'' hJ'' z hz => ?_
  have hmem : J''.map (MulAut.conj a).toMonoidHom ∈
      S \ {J.map (MulAut.conj a).toMonoidHom} := by
    refine ⟨ha J'' hJ''.1, ?_⟩
    intro h
    exact hJ''.2 (Subgroup.map_injective (MulAut.conj a).injective (Set.mem_singleton_iff.mp h))
  exact le_sSup hmem ⟨z, hz, rfl⟩

theorem coord_conj [Finite G] (hK : IsDirectProduct S K) {a : G}
    (ha : ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S) {J : Subgroup G} (hJ : J ∈ S)
    {y : G} (hy : y ∈ K) :
    ((hK.coord (ha J hJ) ⟨a * y * a⁻¹, hK.conj_mem ha hy⟩ : J.map (MulAut.conj a).toMonoidHom) :
      G) = a * ((hK.coord hJ ⟨y, hy⟩ : J) : G) * a⁻¹ := by
  set x := hK.coord hJ ⟨y, hy⟩ with hx
  have hxK : ((x : J) : G) ∈ K := hK.le hJ x.2
  have hl : ((x : J) : G)⁻¹ * y ∈ sSup (S \ {J}) := by
    rw [← coord_eq_one_iff hK hJ ⟨((x : J) : G)⁻¹ * y, mul_mem (inv_mem hxK) hy⟩]
    have : (⟨((x : J) : G)⁻¹ * y, mul_mem (inv_mem hxK) hy⟩ : K) =
        ⟨((x : J) : G)⁻¹, inv_mem hxK⟩ * ⟨y, hy⟩ := rfl
    rw [this, map_mul]
    have h1 : hK.coord hJ ⟨((x : J) : G)⁻¹, inv_mem hxK⟩ = x⁻¹ := by
      apply Subtype.ext
      exact hK.coord_of_mem hJ (inv_mem x.2)
    rw [h1, ← hx, inv_mul_cancel]
  have hxJ' : a * ((x : J) : G) * a⁻¹ ∈ J.map (MulAut.conj a).toMonoidHom := ⟨x, x.2, rfl⟩
  have hlJ' : a * (((x : J) : G)⁻¹ * y) * a⁻¹ ∈
      sSup (S \ {J.map (MulAut.conj a).toMonoidHom}) :=
    map_conj_sSup_diff_le a J ha ⟨_, hl, rfl⟩
  have key := hK.coord_mul (ha J hJ) hxJ' hlJ'
  have hy' : (⟨a * y * a⁻¹, hK.conj_mem ha hy⟩ : K) = ⟨a * ((x : J) : G) * a⁻¹ *
      (a * (((x : J) : G)⁻¹ * y) * a⁻¹), mul_mem (hK.le (ha J hJ) hxJ')
        (hK.sSup_diff_le _ Set.sdiff_subset hlJ')⟩ := Subtype.ext (by group)
  rw [hy']
  exact key

theorem mem_projIn_iff [Finite G] (hK : IsDirectProduct S K) {J X : Subgroup G} (hJ : J ∈ S)
    {x : G} :
    x ∈ projIn S J X ↔ ∃ y : K, (y : G) ∈ X ∧ ((hK.coord hJ y : J) : G) = x := by
  rw [projIn, mem_proj_iff (hK.commute_sSup_diff hJ)]
  constructor
  · rintro ⟨hx, l, hl, hxl⟩
    refine ⟨⟨x * l, mul_mem (hK.le hJ hx) (hK.sSup_diff_le _ Set.sdiff_subset hl)⟩, hxl, ?_⟩
    exact hK.coord_mul hJ hx hl
  · rintro ⟨y, hyX, hyx⟩
    have hxJ : x ∈ J := hyx ▸ (hK.coord hJ y).2
    have hl : ((hK.coord hJ y : J) : G)⁻¹ * y ∈ sSup (S \ {J}) := by
      rw [← coord_eq_one_iff hK hJ ⟨((hK.coord hJ y : J) : G)⁻¹ * y,
        mul_mem (inv_mem (hK.le hJ (hK.coord hJ y).2)) y.2⟩]
      have : (⟨((hK.coord hJ y : J) : G)⁻¹ * y, mul_mem (inv_mem (hK.le hJ (hK.coord hJ y).2))
          y.2⟩ : K) = ⟨((hK.coord hJ y : J) : G)⁻¹, inv_mem (hK.le hJ (hK.coord hJ y).2)⟩ * y :=
        rfl
      rw [this, map_mul]
      have h1 : hK.coord hJ ⟨((hK.coord hJ y : J) : G)⁻¹, inv_mem (hK.le hJ (hK.coord hJ y).2)⟩ =
          (hK.coord hJ y)⁻¹ := Subtype.ext (hK.coord_of_mem hJ (inv_mem (hK.coord hJ y).2))
      rw [h1, inv_mul_cancel]
    refine ⟨hxJ, _, hyx ▸ hl, ?_⟩
    rw [← hyx]
    simpa using hyX

theorem coord_val_congr [Finite G] (hK : IsDirectProduct S K) {J J' : Subgroup G} (hJ : J ∈ S)
    (hJ' : J' ∈ S) (h : J = J') (y : K) :
    ((hK.coord hJ y : J) : G) = ((hK.coord hJ' y : J') : G) := by
  subst h
  rfl

theorem equiv_mem [Finite G] (hK : IsDirectProduct S K) {M : Subgroup G}
    (z : (J : S) → (J : Subgroup G)) (hz : ∀ J : S, ((z J : (J : Subgroup G)) : G) ∈ M) :
    ((hK.equiv z : K) : G) ∈ M := by
  classical
  have : Fintype S := Fintype.ofFinite S
  let f : ((J : S) → (J : Subgroup G)) →* G := K.subtype.comp hK.equiv.toMonoidHom
  have hf : ∀ (J : S) (j : (J : Subgroup G)), f (Pi.mulSingle J j) = j := fun J j =>
    hK.equiv_apply_of_eq_one J _ (fun J' hJ' => Pi.mulSingle_eq_of_ne hJ' _) |>.trans
      (by simp)
  have h : f z = ((hK.equiv z : K) : G) := rfl
  have hz' : z ∈ Submonoid.pi Set.univ
      (fun J : S => (M.comap (J : Subgroup G).subtype).toSubmonoid) := fun J _ => hz J
  rw [← Submonoid.iSup_map_mulSingle] at hz'
  have hle : (⨆ J : S, (M.comap (J : Subgroup G).subtype).toSubmonoid.map
      (MonoidHom.mulSingle (fun J : S => (J : Subgroup G)) J)) ≤ (M.comap f).toSubmonoid :=
    iSup_le fun J => by
      rintro _ ⟨j, hj, rfl⟩
      change f (MonoidHom.mulSingle (fun J : S => (J : Subgroup G)) J j) ∈ M
      rw [MonoidHom.mulSingle_apply, hf]
      exact hj
  rw [← h]
  exact hle hz'

theorem mem_of_coord_mem [Finite G] (hK : IsDirectProduct S K) {M : Subgroup G} {y : G}
    (hy : y ∈ K)
    (h : ∀ (J : Subgroup G) (hJ : J ∈ S), ((hK.coord hJ ⟨y, hy⟩ : J) : G) ∈ M) : y ∈ M := by
  have h1 := hK.equiv_mem (M := M) (hK.equiv.symm ⟨y, hy⟩) fun J : S => h J.1 J.2
  simpa using h1

end IsDirectProduct

end CFSG.SignalizerFunctorTheorem.McBride

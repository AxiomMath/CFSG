module

public import CFSG.Quasithin.Background.HL3NineModel

public section

namespace CFSG.Quasithin.RonanH44

open CFSG.Quasithin CFSG.Quasithin.H CFSG.Quasithin.H.L3Nine CFSG.Quasithin.H.SU3 Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {n : ℕ}

@[expose] def NineFaithSec {F : Type} [Field F] (scalar : F →+* K)
    (group : Subgroup (MulAut (HMod n K)))
    (upper lower : Subgroup (HMod n K)) (dimension : ℕ) : Prop :=
  lower ≤ upper ∧
    (∀ groupElement ∈ group, ∀ vector ∈ upper, groupElement vector ∈ upper) ∧
    (∀ groupElement ∈ group, ∀ vector ∈ lower, groupElement vector ∈ lower) ∧
    (∀ coefficient : F, ∀ vector scaled : HMod n K,
      vector ∈ upper → mat scaled = scalar coefficient • mat vector → scaled ∈ upper) ∧
    (∀ coefficient : F, ∀ vector scaled : HMod n K,
      vector ∈ lower → mat scaled = scalar coefficient • mat vector → scaled ∈ lower) ∧
    ∃ quotientMap : ↥upper →* Multiplicative (Fin dimension → F),
      Function.Surjective quotientMap ∧
      (∀ vector : ↥upper, quotientMap vector = 1 ↔ (vector : HMod n K) ∈ lower) ∧
      (∀ (coefficient : F) (vector scaled : ↥upper),
        mat (scaled : HMod n K) = scalar coefficient • mat (vector : HMod n K) →
        Multiplicative.toAdd (quotientMap scaled) =
          coefficient • Multiplicative.toAdd (quotientMap vector)) ∧
      ∃ action : ↥group →* ((Fin dimension → F) ≃ₗ[F] (Fin dimension → F)),
        Function.Injective action ∧
        ∀ (groupElement : ↥group) (vector image : ↥upper),
          (image : HMod n K) = (groupElement : MulAut (HMod n K)) vector →
          Multiplicative.toAdd (quotientMap image) =
            action groupElement (Multiplicative.toAdd (quotientMap vector))

@[expose] noncomputable def nfsSmul {F : Type} [Field F] (scalar : F →+* K)
    (hfix : ∀ c : F, bar n (scalar c) = scalar c) (c : F) (v : HMod n K) : HMod n K :=
  mkH (scalar c • mat v) (by
    have e : conjM n (scalar c • mat v) = scalar c • conjM n (mat v) := by
      ext i j
      simp [conjM, hfix c]
    rw [e, Matrix.transpose_smul, herm_mat])

theorem mat_nfsSmul {F : Type} [Field F] (scalar : F →+* K)
    (hfix : ∀ c : F, bar n (scalar c) = scalar c) (c : F) (v : HMod n K) :
    mat (nfsSmul scalar hfix c v) = scalar c • mat v := rfl

@[expose] def nfsTransp {G : Subgroup (MulAut (HMod n K))} {U : Subgroup (HMod n K)}
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (γ : ↥G) (u : ↥U) : ↥U :=
  ⟨γ.1 (u : HMod n K), hGU γ.1 γ.2 (u : HMod n K) u.2⟩

theorem coe_nfsTransp {G : Subgroup (MulAut (HMod n K))} {U : Subgroup (HMod n K)}
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (γ : ↥G) (u : ↥U) :
    ((nfsTransp hGU γ u : ↥U) : HMod n K) = γ.1 (u : HMod n K) := rfl

theorem nfsTransp_mul {G : Subgroup (MulAut (HMod n K))} {U : Subgroup (HMod n K)}
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (γ δ : ↥G) (u : ↥U) :
    nfsTransp hGU (γ * δ) u = nfsTransp hGU γ (nfsTransp hGU δ u) :=
  Subtype.ext (MulAut.mul_apply (HMod n K) γ.1 δ.1 (u : HMod n K))

theorem nfsTransp_one {G : Subgroup (MulAut (HMod n K))} {U : Subgroup (HMod n K)}
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (u : ↥U) : nfsTransp hGU 1 u = u :=
  Subtype.ext (MulAut.one_apply (HMod n K) (u : HMod n K))

theorem nfsTransp_mul_U {G : Subgroup (MulAut (HMod n K))} {U : Subgroup (HMod n K)}
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (γ : ↥G) (u v : ↥U) :
    nfsTransp hGU γ (u * v) = nfsTransp hGU γ u * nfsTransp hGU γ v :=
  Subtype.ext (map_mul γ.1 (u : HMod n K) (v : HMod n K))

theorem beta_nfsTransp {F : Type} [Field F] {G : Subgroup (MulAut (HMod n K))}
    {U Z : Subgroup (HMod n K)} {d : ℕ}
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (hGZ : ∀ g ∈ G, ∀ v ∈ Z, g v ∈ Z)
    (β : ↥U →* Multiplicative (Fin d → F))
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : HMod n K) ∈ Z) (γ : ↥G) {u u' : ↥U}
    (h : β u = β u') : β (nfsTransp hGU γ u) = β (nfsTransp hGU γ u') := by
  have h1 : ((u * u'⁻¹ : ↥U) : HMod n K) ∈ Z := (hβk _).mp (by
    rw [map_mul, map_inv, h, mul_inv_cancel])
  have h2 : β (nfsTransp hGU γ u * (nfsTransp hGU γ u')⁻¹) = 1 := (hβk _).mpr (by
    have e : ((nfsTransp hGU γ u * (nfsTransp hGU γ u')⁻¹ : ↥U) : HMod n K) =
        γ.1 ((u * u'⁻¹ : ↥U) : HMod n K) := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_nfsTransp, map_mul, map_inv]
    rw [e]
    exact hGZ γ.1 γ.2 _ h1)
  rw [map_mul, map_inv] at h2
  exact mul_inv_eq_one.mp h2

theorem exists_toAdd_eq {F : Type} [Field F] {U : Subgroup (HMod n K)} {d : ℕ}
    (β : ↥U →* Multiplicative (Fin d → F)) (hβs : Function.Surjective β) (x : Fin d → F) :
    ∃ u : ↥U, Multiplicative.toAdd (β u) = x := by
  obtain ⟨u, hu⟩ := hβs (Multiplicative.ofAdd x)
  exact ⟨u, by rw [hu, toAdd_ofAdd]⟩

@[expose] noncomputable def nfsCoord {F : Type} [Field F] {G : Subgroup (MulAut (HMod n K))}
    {U : Subgroup (HMod n K)} {d : ℕ} (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U)
    (β : ↥U →* Multiplicative (Fin d → F)) (hβs : Function.Surjective β)
    (γ : ↥G) (x : Fin d → F) : Fin d → F :=
  Multiplicative.toAdd (β (nfsTransp hGU γ (Function.surjInv hβs (Multiplicative.ofAdd x))))

theorem nfsCoord_spec {F : Type} [Field F] {G : Subgroup (MulAut (HMod n K))}
    {U Z : Subgroup (HMod n K)} {d : ℕ}
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (hGZ : ∀ g ∈ G, ∀ v ∈ Z, g v ∈ Z)
    (β : ↥U →* Multiplicative (Fin d → F)) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : HMod n K) ∈ Z) (γ : ↥G) (u : ↥U) :
    nfsCoord hGU β hβs γ (Multiplicative.toAdd (β u)) =
      Multiplicative.toAdd (β (nfsTransp hGU γ u)) := by
  unfold nfsCoord
  congr 1
  apply beta_nfsTransp hGU hGZ β hβk γ
  rw [Function.surjInv_eq hβs, ofAdd_toAdd]

theorem nfsCoord_comp {F : Type} [Field F] {G : Subgroup (MulAut (HMod n K))}
    {U Z : Subgroup (HMod n K)} {d : ℕ}
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (hGZ : ∀ g ∈ G, ∀ v ∈ Z, g v ∈ Z)
    (β : ↥U →* Multiplicative (Fin d → F)) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : HMod n K) ∈ Z) (γ δ : ↥G) (x : Fin d → F) :
    nfsCoord hGU β hβs γ (nfsCoord hGU β hβs δ x) = nfsCoord hGU β hβs (γ * δ) x := by
  obtain ⟨u, rfl⟩ := exists_toAdd_eq β hβs x
  rw [nfsCoord_spec hGU hGZ β hβs hβk δ u,
    nfsCoord_spec hGU hGZ β hβs hβk γ (nfsTransp hGU δ u),
    nfsCoord_spec hGU hGZ β hβs hβk (γ * δ) u, nfsTransp_mul hGU γ δ u]

theorem nfsCoord_one {F : Type} [Field F] {G : Subgroup (MulAut (HMod n K))}
    {U Z : Subgroup (HMod n K)} {d : ℕ}
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (hGZ : ∀ g ∈ G, ∀ v ∈ Z, g v ∈ Z)
    (β : ↥U →* Multiplicative (Fin d → F)) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : HMod n K) ∈ Z) (x : Fin d → F) :
    nfsCoord hGU β hβs 1 x = x := by
  obtain ⟨u, rfl⟩ := exists_toAdd_eq β hβs x
  rw [nfsCoord_spec hGU hGZ β hβs hβk 1 u, nfsTransp_one hGU u]

theorem nfsCoord_add {F : Type} [Field F] {G : Subgroup (MulAut (HMod n K))}
    {U Z : Subgroup (HMod n K)} {d : ℕ}
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (hGZ : ∀ g ∈ G, ∀ v ∈ Z, g v ∈ Z)
    (β : ↥U →* Multiplicative (Fin d → F)) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : HMod n K) ∈ Z) (γ : ↥G) (x y : Fin d → F) :
    nfsCoord hGU β hβs γ (x + y) = nfsCoord hGU β hβs γ x + nfsCoord hGU β hβs γ y := by
  obtain ⟨u, rfl⟩ := exists_toAdd_eq β hβs x
  obtain ⟨v, rfl⟩ := exists_toAdd_eq β hβs y
  have e : Multiplicative.toAdd (β u) + Multiplicative.toAdd (β v) =
      Multiplicative.toAdd (β (u * v)) := by
    rw [map_mul, toAdd_mul]
  rw [e, nfsCoord_spec hGU hGZ β hβs hβk γ (u * v), nfsCoord_spec hGU hGZ β hβs hβk γ u,
    nfsCoord_spec hGU hGZ β hβs hβk γ v, nfsTransp_mul_U hGU γ u v, map_mul, toAdd_mul]

theorem nfsCoord_smul {F : Type} [Field F] {G : Subgroup (MulAut (HMod n K))}
    {U Z : Subgroup (HMod n K)} {d : ℕ} (scalar : F →+* K)
    (hfix : ∀ c : F, bar n (scalar c) = scalar c)
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (hGZ : ∀ g ∈ G, ∀ v ∈ Z, g v ∈ Z)
    (hUs : ∀ (c : F) (v w : HMod n K), v ∈ U → mat w = scalar c • mat v → w ∈ U)
    (hlin : ∀ g ∈ G, ∀ (c : F) (v w : HMod n K), mat w = scalar c • mat v →
      mat (g w) = scalar c • mat (g v))
    (β : ↥U →* Multiplicative (Fin d → F)) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : HMod n K) ∈ Z)
    (hβc : ∀ (c : F) (v w : ↥U), mat (w : HMod n K) = scalar c • mat (v : HMod n K) →
      Multiplicative.toAdd (β w) = c • Multiplicative.toAdd (β v))
    (γ : ↥G) (c : F) (x : Fin d → F) :
    nfsCoord hGU β hβs γ (c • x) = c • nfsCoord hGU β hβs γ x := by
  obtain ⟨u, rfl⟩ := exists_toAdd_eq β hβs x
  obtain ⟨w, hwval⟩ : ∃ w : ↥U, (w : HMod n K) = nfsSmul scalar hfix c (u : HMod n K) :=
    ⟨⟨nfsSmul scalar hfix c (u : HMod n K),
      hUs c (u : HMod n K) (nfsSmul scalar hfix c (u : HMod n K)) u.2
        (mat_nfsSmul scalar hfix c (u : HMod n K))⟩, rfl⟩
  have hwmat : mat (w : HMod n K) = scalar c • mat (u : HMod n K) := by
    rw [hwval, mat_nfsSmul]
  have hw1 : Multiplicative.toAdd (β w) = c • Multiplicative.toAdd (β u) := hβc c u w hwmat
  rw [← hw1, nfsCoord_spec hGU hGZ β hβs hβk γ w, nfsCoord_spec hGU hGZ β hβs hβk γ u]
  exact hβc c (nfsTransp hGU γ u) (nfsTransp hGU γ w) (hlin γ.1 γ.2 c _ _ hwmat)

@[expose] noncomputable def nfsEquiv {F : Type} [Field F] {G : Subgroup (MulAut (HMod n K))}
    {U Z : Subgroup (HMod n K)} {d : ℕ} (scalar : F →+* K)
    (hfix : ∀ c : F, bar n (scalar c) = scalar c)
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (hGZ : ∀ g ∈ G, ∀ v ∈ Z, g v ∈ Z)
    (hUs : ∀ (c : F) (v w : HMod n K), v ∈ U → mat w = scalar c • mat v → w ∈ U)
    (hlin : ∀ g ∈ G, ∀ (c : F) (v w : HMod n K), mat w = scalar c • mat v →
      mat (g w) = scalar c • mat (g v))
    (β : ↥U →* Multiplicative (Fin d → F)) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : HMod n K) ∈ Z)
    (hβc : ∀ (c : F) (v w : ↥U), mat (w : HMod n K) = scalar c • mat (v : HMod n K) →
      Multiplicative.toAdd (β w) = c • Multiplicative.toAdd (β v))
    (γ : ↥G) : (Fin d → F) ≃ₗ[F] (Fin d → F) where
  toFun := nfsCoord hGU β hβs γ
  invFun := nfsCoord hGU β hβs γ⁻¹
  map_add' := nfsCoord_add hGU hGZ β hβs hβk γ
  map_smul' := nfsCoord_smul scalar hfix hGU hGZ hUs hlin β hβs hβk hβc γ
  left_inv x := (nfsCoord_comp hGU hGZ β hβs hβk γ⁻¹ γ x).trans
    ((congrArg (fun g : ↥G => nfsCoord hGU β hβs g x) (inv_mul_cancel γ)).trans
      (nfsCoord_one hGU hGZ β hβs hβk x))
  right_inv x := (nfsCoord_comp hGU hGZ β hβs hβk γ γ⁻¹ x).trans
    ((congrArg (fun g : ↥G => nfsCoord hGU β hβs g x) (mul_inv_cancel γ)).trans
      (nfsCoord_one hGU hGZ β hβs hβk x))

@[expose] noncomputable def nfsAction {F : Type} [Field F] {G : Subgroup (MulAut (HMod n K))}
    {U Z : Subgroup (HMod n K)} {d : ℕ} (scalar : F →+* K)
    (hfix : ∀ c : F, bar n (scalar c) = scalar c)
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (hGZ : ∀ g ∈ G, ∀ v ∈ Z, g v ∈ Z)
    (hUs : ∀ (c : F) (v w : HMod n K), v ∈ U → mat w = scalar c • mat v → w ∈ U)
    (hlin : ∀ g ∈ G, ∀ (c : F) (v w : HMod n K), mat w = scalar c • mat v →
      mat (g w) = scalar c • mat (g v))
    (β : ↥U →* Multiplicative (Fin d → F)) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : HMod n K) ∈ Z)
    (hβc : ∀ (c : F) (v w : ↥U), mat (w : HMod n K) = scalar c • mat (v : HMod n K) →
      Multiplicative.toAdd (β w) = c • Multiplicative.toAdd (β v)) :
    ↥G →* ((Fin d → F) ≃ₗ[F] (Fin d → F)) where
  toFun γ := nfsEquiv scalar hfix hGU hGZ hUs hlin β hβs hβk hβc γ
  map_one' := LinearEquiv.ext fun x => nfsCoord_one hGU hGZ β hβs hβk x
  map_mul' γ δ := LinearEquiv.ext fun x => (nfsCoord_comp hGU hGZ β hβs hβk γ δ x).symm

theorem nfs_of_data {F : Type} [Field F] (scalar : F →+* K)
    (hfix : ∀ c : F, bar n (scalar c) = scalar c)
    {G : Subgroup (MulAut (HMod n K))} {U Z : Subgroup (HMod n K)} {d : ℕ}
    (hZU : Z ≤ U)
    (hGU : ∀ g ∈ G, ∀ v ∈ U, g v ∈ U) (hGZ : ∀ g ∈ G, ∀ v ∈ Z, g v ∈ Z)
    (hUs : ∀ (c : F) (v w : HMod n K), v ∈ U → mat w = scalar c • mat v → w ∈ U)
    (hZs : ∀ (c : F) (v w : HMod n K), v ∈ Z → mat w = scalar c • mat v → w ∈ Z)
    (β : ↥U →* Multiplicative (Fin d → F)) (hβs : Function.Surjective β)
    (hβk : ∀ u : ↥U, β u = 1 ↔ (u : HMod n K) ∈ Z)
    (hβc : ∀ (c : F) (v w : ↥U), mat (w : HMod n K) = scalar c • mat (v : HMod n K) →
      Multiplicative.toAdd (β w) = c • Multiplicative.toAdd (β v))
    (hlin : ∀ g ∈ G, ∀ (c : F) (v w : HMod n K), mat w = scalar c • mat v →
      mat (g w) = scalar c • mat (g v))
    (hfaith : ∀ g ∈ G, (∀ u ∈ U, g u * u⁻¹ ∈ Z) → g = 1) :
    NineFaithSec scalar G U Z d := by
  unfold NineFaithSec
  refine ⟨hZU, hGU, hGZ, hUs, hZs, β, hβs, hβk, hβc,
    nfsAction scalar hfix hGU hGZ hUs hlin β hβs hβk hβc, ?_, ?_⟩
  · refine (injective_iff_map_eq_one _).mpr fun γ hγ => ?_
    have hid : ∀ x, nfsCoord hGU β hβs γ x = x := fun x =>
      congrArg (fun L : (Fin d → F) ≃ₗ[F] (Fin d → F) => L x) hγ
    have hbeta : ∀ w : ↥U, β (nfsTransp hGU γ w) = β w := by
      intro w
      have h1 := hid (Multiplicative.toAdd (β w))
      rw [nfsCoord_spec hGU hGZ β hβs hβk γ w] at h1
      exact Multiplicative.toAdd.injective h1
    refine Subtype.ext (hfaith γ.1 γ.2 fun u hu => ?_)
    have h1 : ((nfsTransp hGU γ ⟨u, hu⟩ * (⟨u, hu⟩ : ↥U)⁻¹ : ↥U) : HMod n K) ∈ Z :=
      (hβk _).mp (by rw [map_mul, map_inv, hbeta ⟨u, hu⟩, mul_inv_cancel])
    exact h1
  · intro γ v w hw
    have hwt : w = nfsTransp hGU γ v := Subtype.ext hw
    subst hwt
    exact (nfsCoord_spec hGU hGZ β hβs hβk γ v).symm

end CFSG.Quasithin.RonanH44

module

public import CFSG.LocalAnalysis.StandardType.GGRootPlaneOmFrame
public import CFSG.LocalAnalysis.StandardType.GGRootPlaneOmSpin
public import CFSG.LocalAnalysis.StandardType.GGSixBstarNoOffenderOmegaOrth
public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge
public import CFSG.LocalAnalysis.ComponentClassification.HarrisLit82T1P58b3LDFour

public section

namespace CFSG.StandardType

namespace RootPlaneOm

open Module QuadraticMap Multiplicative NoOffOm SUTB CFSG.Assembly
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear CFSG.ClassicalGroups.Orthogonal
open CFSG.RankThree.Classical2 (orthDerived)

section MatAct

variable {K : Type} [Field K] {d : ℕ} (Q : QuadraticForm K (Fin d → K))

noncomputable abbrev matAct : matrixDerived Q →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  (matrixLinearIso (d := d) (K := K)).toMonoidHom.comp (matrixDerived Q).subtype

variable {Q}

theorem matAct_apply (X : matrixDerived Q) (v : Fin d → K) :
    matAct Q X v = glin (X : GL (Fin d) K) v := by
  rw [glin_apply]
  rfl

theorem matAct_injective : Function.Injective (matAct Q) :=
  (matrixLinearIso (d := d) (K := K)).injective.comp Subtype.val_injective

theorem matAct_range : (matAct Q).range = ⁅TauCeti.QuadraticMap.orthogonalGroup Q,
    TauCeti.QuadraticMap.orthogonalGroup Q⁆ := by
  rw [MonoidHom.range_comp, Subgroup.range_subtype]
  exact CFSG.RankThree.PartOne.KCOrthComm.map_matrixDerived Q

theorem matAct_mem_orth (X : matrixDerived Q) :
    matAct Q X ∈ TauCeti.QuadraticMap.orthogonalGroup Q :=
  matrixDerived_le_isometries Q X.2

end MatAct

section Plane

variable {r p : ℕ}

@[expose] noncomputable def planeHom (i j : Fin r) :
    Multiplicative (ZMod p × ZMod p) →* Multiplicative (Fin r → ZMod p) where
  toFun x := ofAdd (Pi.single i (toAdd x).1 + Pi.single j (toAdd x).2)
  map_one' := by
    apply toAdd.injective
    simp
  map_mul' x y := by
    apply toAdd.injective
    simp only [toAdd_mul, Prod.fst_add, Prod.snd_add, toAdd_ofAdd, Pi.single_add]
    abel

theorem planeHom_apply (i j : Fin r) (x : Multiplicative (ZMod p × ZMod p)) :
    toAdd (planeHom (p := p) i j x) = Pi.single i (toAdd x).1 + Pi.single j (toAdd x).2 := rfl

theorem planeHom_injective {i j : Fin r} (hij : i ≠ j) :
    Function.Injective (planeHom (p := p) i j) := by
  rw [injective_iff_map_eq_one]
  intro x hx
  have h := congrArg toAdd hx
  rw [planeHom_apply, toAdd_one] at h
  have hi := congrFun h i
  have hj := congrFun h j
  simp only [Pi.add_apply, Pi.single_eq_same, Pi.single_eq_of_ne hij, Pi.single_eq_of_ne hij.symm,
    Pi.zero_apply, add_zero, zero_add] at hi hj
  apply toAdd.injective
  rw [toAdd_one]
  exact Prod.ext hi hj

theorem mem_range_planeHom {i j : Fin r} (hij : i ≠ j) {t : Fin r → ZMod p}
    (ht : ∀ k, t k ≠ 0 → k = i ∨ k = j) : ofAdd t ∈ (planeHom (p := p) i j).range := by
  refine ⟨ofAdd (t i, t j), toAdd.injective ?_⟩
  rw [planeHom_apply, toAdd_ofAdd, toAdd_ofAdd]
  funext k
  simp only [Pi.add_apply]
  by_cases hki : k = i
  · subst hki
    rw [Pi.single_eq_same, Pi.single_eq_of_ne hij, add_zero]
  · by_cases hkj : k = j
    · subst hkj
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hki, zero_add]
    · rw [Pi.single_eq_of_ne hki, Pi.single_eq_of_ne hkj, add_zero]
      by_contra hk
      rcases ht k (Ne.symm hk) with h | h
      · exact hki h
      · exact hkj h

theorem planeHom_supp (i j : Fin r) (x : Multiplicative (ZMod p × ZMod p)) (k : Fin r)
    (hk : toAdd (planeHom (p := p) i j x) k ≠ 0) : k = i ∨ k = j := by
  by_contra h
  push Not at h
  rw [planeHom_apply, Pi.add_apply, Pi.single_eq_of_ne h.1, Pi.single_eq_of_ne h.2,
    add_zero] at hk
  exact hk rfl

theorem card_planeHom_range [Fact p.Prime] {i j : Fin r} (hij : i ≠ j) :
    Nat.card (planeHom (p := p) i j).range = p ^ 2 := by
  rw [MonoidHom.range_eq_map, Subgroup.card_map_of_injective (planeHom_injective hij),
    Subgroup.card_top, Nat.card_congr
    (Multiplicative.toAdd : Multiplicative (ZMod p × ZMod p) ≃ (ZMod p × ZMod p)),
    Nat.card_prod, Nat.card_zmod, _root_.sq]

end Plane

section Core

variable {K : Type} [Field K] [Finite K] [CharP K 2] {d : ℕ} {Q : QuadraticForm K (Fin d → K)}

theorem exists_rootPlane_core (hnd : Q.polarBilin.Nondegenerate)
    (hT : ∃ T : Submodule K (Fin d → K), finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0) (hd : 9 ≤ d)
    {G : Type} [Group G] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) {Bs : Subgroup G}
    (hBs : IsElemAbelian p Bs)
    (hSC : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hcard : p ^ 4 ≤ Nat.card Bs)
    {φ : matrixDerived Q →* G} (hφ : Function.Injective φ) (hBφ : Bs ≤ φ.range)
    {a₀ a₁ w : Fin d → K} (ha₀ : Q a₀ = 0) (ha₁ : Q a₁ = 0) (ha : polar Q a₀ a₁ = 0)
    (hai : LinearIndependent K ![a₀, a₁]) (hw : Q w ≠ 0) (hw₀ : polar Q w a₀ = 0)
    (hw₁ : polar Q w a₁ = 0) :
    ∃ (E : Subgroup G) (g : matrixDerived Q), E ≤ Bs ∧ IsElemAbelian p E ∧ Nat.card E = p ^ 2 ∧
      (∀ e ∈ E, ∀ X : matrixDerived Q, (∃ c : K, ∀ y, glin (X : GL (Fin d) K) y =
          y + (c * polar Q y a₁) • a₀ - (c * polar Q y a₀) • a₁) →
        e * φ (g * X * g⁻¹) = φ (g * X * g⁻¹) * e) ∧
      ∀ e ∈ E, e ≠ 1 → ∃ L₁ : Subgroup G,
        IsComponentOf L₁ (φ.range ⊓ Subgroup.centralizer {e}) ∧
          Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ p ^ 2 := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hA := genMax_of_orth hnd hT hp hp2 hBs hSC φ hφ hBφ
  obtain ⟨r, ι₀, U, hinj, hrange, hUnd, hUne, horth, hfix, -⟩ := exists_blockFrame hA
  have hι₀A : ∀ s, ι₀ s ∈ (Bs.comap φ).map (matrixDerived Q).subtype := fun s =>
    hrange ▸ ⟨s, rfl⟩
  have hι₀Γ : ∀ s, ι₀ s ∈ matrixDerived Q := fun s => hA.le (hι₀A s)
  set ι₁ : Multiplicative (Fin r → ZMod p) →* matrixDerived Q := ι₀.codRestrict _ hι₀Γ with hι₁
  have hι₁v : ∀ s, ((ι₁ s : matrixDerived Q) : GL (Fin d) K) = ι₀ s := fun s => rfl
  have hι₁inj : Function.Injective ι₁ := fun s t h => hinj (by rw [← hι₁v, ← hι₁v, h])
  have hι₁B : ∀ s, φ (ι₁ s) ∈ Bs := by
    intro s
    obtain ⟨Y, hY, hYs⟩ := hι₀A s
    have hYι : Y = ι₁ s := Subtype.ext hYs
    rw [← hYι]
    exact hY
  have hBι : ∀ b ∈ Bs, ∃ t, φ (ι₁ t) = b := by
    intro b hb
    obtain ⟨Y, rfl⟩ := hBφ hb
    have hYA : (Y : GL (Fin d) K) ∈ ι₀.range := by rw [hrange]; exact ⟨Y, hb, rfl⟩
    obtain ⟨t, ht⟩ := hYA
    exact ⟨t, congrArg φ (Subtype.ext ht)⟩
  have hr : 4 ≤ r := by
    have hBeq : Bs = (φ.comp ι₁).range := by
      ext b
      constructor
      · intro hb
        obtain ⟨t, rfl⟩ := hBι b hb
        exact ⟨t, rfl⟩
      · rintro ⟨t, rfl⟩
        exact hι₁B t
    have hcardBs : Nat.card Bs = p ^ r := by
      have hinj' : Function.Injective (φ.comp ι₁) := hφ.comp hι₁inj
      rw [hBeq, MonoidHom.range_eq_map, Subgroup.card_map_of_injective hinj',
        Subgroup.card_top, Nat.card_congr
          (Multiplicative.toAdd : Multiplicative (Fin r → ZMod p) ≃ (Fin r → ZMod p)),
        Nat.card_fun, Nat.card_zmod, Nat.card_fin]
    rw [hcardBs] at hcard
    exact (Nat.pow_le_pow_iff_right hp.one_lt).mp hcard
  obtain ⟨i, j, hij, h5⟩ := exists_pair_five hr hUnd horth hd
  have hplanefix : ∀ (x : Multiplicative (ZMod p × ZMod p)) (v : Fin d → K),
      v ∈ (U i ⊔ U j).orthogonalBilin (polB Q) → glin (ι₀ (planeHom i j x)) v = v := by
    intro x v hv
    obtain ⟨hvi, hvj⟩ := mem_orth_sup_iff.mp hv
    refine (hfix (toAdd (planeHom i j x)) v).mpr fun k hk => ?_
    rcases planeHom_supp i j x k hk with rfl | rfl
    · exact hvi
    · exact hvj
  set E : Subgroup G := ((planeHom (p := p) i j).range.map ι₁).map φ with hE
  have hEB : E ≤ Bs := by
    rintro _ ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩
    exact hι₁B _
  have hEel : IsElemAbelian p E :=
    ⟨⟨⟨fun x y => Subtype.ext (TableB.IsElemAbelian.comm hBs (hEB x.2) (hEB y.2))⟩⟩,
      fun x hx => hBs.2 x (hEB hx)⟩
  have hEcard : Nat.card E = p ^ 2 := by
    rw [hE, Subgroup.card_map_of_injective hφ, Subgroup.card_map_of_injective hι₁inj,
      card_planeHom_range hij]
  obtain ⟨w₁, hw₁F, w₂, hw₂F, hQw₁, hQw₂, hw₁₂, hwi⟩ := exists_singular_pair (Q := Q) hnd h5
  obtain ⟨g, hg₁, hg₂⟩ := exists_conj_pair hnd hT (matAct Q) matAct_range ha₀ ha₁ ha hai hQw₁
    hQw₂ hw₁₂ hwi hw hw₀ hw₁
  refine ⟨E, g, hEB, hEel, hEcard, ?_, ?_⟩
  · rintro _ ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩ X ⟨c, hX⟩
    have ha₁₀ : polar Q a₁ (c • a₀) = 0 := by
      rw [polar_smul_right, QuadraticMap.polar_comm Q a₁ a₀, ha, smul_zero]
    have hXe : matAct Q X = eichler Q a₁ (c • a₀) := by
      refine LinearEquiv.ext fun y => ?_
      rw [matAct_apply, hX y, eichler_apply ha₁ ha₁₀ y, QuadraticMap.map_smul, ha₀, smul_zero,
        zero_mul, add_zero, polar_smul_right, smul_eq_mul, smul_smul, mul_comm (polar Q y a₁) c]
    have hconj : matAct Q (g * X * g⁻¹) = eichler Q w₂ (c • w₁) := by
      rw [map_mul, map_mul, map_inv, hXe, eichler_conj (matAct_mem_orth g), map_smul, hg₁, hg₂]
    have hfx : ∀ v ∈ (U i ⊔ U j).orthogonalBilin (polB Q), matAct Q (ι₁ (planeHom i j x)) v = v :=
      fun v hv => by rw [matAct_apply, hι₁v]; exact hplanefix x v hv
    have hcomm := eichler_commute_of_fix (matAct_mem_orth (ι₁ (planeHom i j x)))
      (u := w₂) (w := c • w₁) (hfx w₂ hw₂F) (by rw [map_smul, hfx w₁ hw₁F])
    have h1 : ι₁ (planeHom i j x) * (g * X * g⁻¹) = (g * X * g⁻¹) * ι₁ (planeHom i j x) :=
      matAct_injective (by
        rw [map_mul (matAct Q) (ι₁ (planeHom i j x)) (g * X * g⁻¹),
          map_mul (matAct Q) (g * X * g⁻¹) (ι₁ (planeHom i j x)), hconj]
        exact hcomm)
    rw [← map_mul, ← map_mul, h1]
  · rintro _ ⟨_, ⟨_, ⟨x, rfl⟩, rfl⟩, rfl⟩ -
    have hyp : ι₁ (planeHom i j x) ^ p = 1 :=
      Subtype.ext (by rw [SubgroupClass.coe_pow, hι₁v]; exact hA.pow _ (hι₀A _))
    obtain ⟨L₁, hL₁, hcen⟩ := exists_component_fixPart hnd matAct_injective matAct_range hφ hp
      hp2 hyp h5 fun v hv => by rw [matAct_apply, hι₁v]; exact hplanefix x v hv
    refine ⟨L₁, hL₁, ?_⟩
    have hle : Bs ⊓ Subgroup.centralizer (L₁ : Set G) ≤ E := by
      rintro b ⟨hbB, hbC⟩
      obtain ⟨t, rfl⟩ := hBι b hbB
      have hty : ι₁ t * ι₁ (planeHom i j x) = ι₁ (planeHom i j x) * ι₁ t :=
        hφ (by rw [map_mul, map_mul]; exact TableB.IsElemAbelian.comm hBs (hι₁B t) (hι₁B _))
      have h1 := hcen (ι₁ t) hty hbC
      have hsupp := suppLE_of_fix hUnd hUne horth hfix (s := toAdd (planeHom i j x))
        (t := toAdd t) fun v hv => by
          have h2 := h1 v (by rw [matAct_apply, hι₁v]; exact hv)
          rwa [matAct_apply, hι₁v] at h2
      have ht : ∀ k, toAdd t k ≠ 0 → k = i ∨ k = j := fun k hk =>
        planeHom_supp i j x k (hsupp k hk)
      obtain ⟨x', hx'⟩ := mem_range_planeHom hij ht
      exact ⟨_, ⟨_, ⟨x', rfl⟩, rfl⟩, by rw [hx']; rfl⟩
    have : Finite E := Nat.finite_of_card_ne_zero (by rw [hEcard]; exact pow_ne_zero 2 hp.ne_zero)
    calc Nat.card (Bs ⊓ Subgroup.centralizer (L₁ : Set G) : Subgroup G) ≤ Nat.card E :=
          Subgroup.card_le_of_le hle
      _ = p ^ 2 := hEcard

end Core

end RootPlaneOm

end CFSG.StandardType

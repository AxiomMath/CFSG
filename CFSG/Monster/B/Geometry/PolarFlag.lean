module

public import CFSG.Monster.B.Geometry.PolarCoxeter
public import CFSG.Monster.B.Geometry.ProductModel

public section

namespace CFSG.Monster.B.Geometry

open Module CoxeterSystem CFSG.LieType.Chevalley.CosetBuilding

section LinAlg

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]

theorem finrank_sup_span_of_not_mem {U : Submodule K V} {v : V} (hv : v ∉ U) :
    finrank K ↥(U ⊔ K ∙ v) = finrank K U + 1 := by
  have hv0 : v ≠ 0 := fun h => hv (h ▸ U.zero_mem)
  have h := Submodule.finrank_sup_add_finrank_inf_eq U (K ∙ v)
  have hinf : U ⊓ K ∙ v = ⊥ := by
    rw [eq_bot_iff]
    intro w hw
    obtain ⟨hwU, hwv⟩ := Submodule.mem_inf.mp hw
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hwv
    by_cases hc : c = 0
    · rw [hc, zero_smul]; exact Submodule.zero_mem _
    · exact absurd (by simpa [hc] using U.smul_mem c⁻¹ hwU) hv
  rw [hinf, finrank_bot, finrank_span_singleton hv0] at h
  omega

theorem exists_mem_not_mem_of_finrank_lt {U U' : Submodule K V}
    (h : finrank K U < finrank K U') : ∃ v ∈ U', v ∉ U := by
  by_contra hcon
  push Not at hcon
  have := Submodule.finrank_mono (show U' ≤ U from hcon)
  omega

theorem exists_between_finrank {U U' : Submodule K V} (hUU' : U ≤ U') {m : ℕ}
    (hm : finrank K U ≤ m) (hm' : m ≤ finrank K U') :
    ∃ L : Submodule K V, U ≤ L ∧ L ≤ U' ∧ finrank K L = m := by
  obtain ⟨k, rfl⟩ : ∃ k, m = finrank K U + k := ⟨m - finrank K U, by omega⟩
  induction k with
  | zero => exact ⟨U, le_rfl, hUU', by simp⟩
  | succ k ih =>
    obtain ⟨L, h1, h2, h3⟩ := ih (by omega) (by omega)
    obtain ⟨v, hv, hvL⟩ := exists_mem_not_mem_of_finrank_lt (U := L) (U' := U') (by omega)
    refine ⟨L ⊔ K ∙ v, h1.trans le_sup_left, sup_le h2 ((Submodule.span_singleton_le_iff_mem v
      U').mpr hv), ?_⟩
    rw [finrank_sup_span_of_not_mem hvL, h3]
    omega

theorem finrank_le_finrank_inf_ker_add_one (U : Submodule K V) (φ : V →ₗ[K] K) :
    finrank K U ≤ finrank K ↥(U ⊓ LinearMap.ker φ) + 1 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq U (LinearMap.ker φ)
  have hle := Submodule.finrank_le (U ⊔ LinearMap.ker φ)
  have hk := LinearMap.finrank_range_add_finrank_ker φ
  have hr := Submodule.finrank_le (LinearMap.range φ)
  rw [Module.finrank_self] at hr
  omega

theorem eq_of_le_of_finrank_le {U U' : Submodule K V} (h : U ≤ U')
    (h' : finrank K U' ≤ finrank K U) : U = U' :=
  Submodule.eq_of_le_of_finrank_eq h (le_antisymm (Submodule.finrank_mono h) h')

end LinAlg

structure PolarSpace (K V : Type*) [Field K] [AddCommGroup V] [Module K V] where
  Iso : V → Prop
  pair : V → V →ₗ[K] K
  pair_eq_zero_comm : ∀ u v, pair u v = 0 ↔ pair v u = 0
  pair_eq_zero_of_isTI : ∀ U : Submodule K V, (∀ v ∈ U, Iso v) → ∀ u ∈ U, ∀ v ∈ U, pair u v = 0
  isTI_sup : ∀ U : Submodule K V, (∀ v ∈ U, Iso v) → ∀ w, Iso w → (∀ u ∈ U, pair w u = 0) →
    ∀ v ∈ U ⊔ K ∙ w, Iso v
  finrank_le_three : ∀ U : Submodule K V, (∀ v ∈ U, Iso v) → finrank K U ≤ 3

variable {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

@[ext]
structure PFlag (P : PolarSpace K V) where
  V₁ : Submodule K V
  V₂ : Submodule K V
  V₃ : Submodule K V
  finrank₁ : finrank K V₁ = 1
  finrank₂ : finrank K V₂ = 2
  finrank₃ : finrank K V₃ = 3
  le₁₂ : V₁ ≤ V₂
  le₂₃ : V₂ ≤ V₃
  isTI : ∀ v ∈ V₃, P.Iso v

variable {ι : Type*} (P : PolarSpace K V)

@[expose] noncomputable def polarChamber (p l π : ι) : ChamberSystem ι (PFlag P) :=
  ChamberSystem.ofThree p l π (fun x y => x.V₂ = y.V₂ ∧ x.V₃ = y.V₃)
    (fun x y => x.V₁ = y.V₁ ∧ x.V₃ = y.V₃) (fun x y => x.V₁ = y.V₁ ∧ x.V₂ = y.V₂)
    ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩
    ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩
    ⟨fun _ => ⟨rfl, rfl⟩, fun h => ⟨h.1.symm, h.2.symm⟩,
      fun h h' => ⟨h.1.trans h'.1, h.2.trans h'.2⟩⟩

variable {P} {p l π : ι}

theorem polarChamber_adj_p :
    (polarChamber P p l π).adj p = fun x y => x.V₂ = y.V₂ ∧ x.V₃ = y.V₃ :=
  ChamberSystem.ofThree_adj₁

theorem polarChamber_adj_l (hpl : p ≠ l) :
    (polarChamber P p l π).adj l = fun x y => x.V₁ = y.V₁ ∧ x.V₃ = y.V₃ :=
  ChamberSystem.ofThree_adj₂ hpl.symm

theorem polarChamber_adj_π (hpπ : p ≠ π) (hlπ : l ≠ π) :
    (polarChamber P p l π).adj π = fun x y => x.V₁ = y.V₁ ∧ x.V₂ = y.V₂ :=
  ChamberSystem.ofThree_adj₃ hpπ.symm hlπ.symm

theorem PolarSpace.isTI_mono {U U' : Submodule K V} (hU : ∀ v ∈ U, P.Iso v) (h : U' ≤ U) :
    ∀ v ∈ U', P.Iso v := fun v hv => hU v (h hv)

theorem ChamberSystem.ofThree_mem_typeAut {F : Type*} {i₁ i₂ i₃ : ι} {r₁ r₂ r₃ : F → F → Prop}
    {h₁ : Equivalence r₁} {h₂ : Equivalence r₂} {h₃ : Equivalence r₃} {G : Equiv.Perm F}
    (hG₁ : ∀ x y, r₁ (G x) (G y) ↔ r₁ x y) (hG₂ : ∀ x y, r₂ (G x) (G y) ↔ r₂ x y)
    (hG₃ : ∀ x y, r₃ (G x) (G y) ↔ r₃ x y) :
    G ∈ (ChamberSystem.ofThree i₁ i₂ i₃ r₁ r₂ r₃ h₁ h₂ h₃).typeAut := by
  intro i x y
  simp only [ChamberSystem.ofThree]
  split_ifs
  · exact hG₁ x y
  · exact hG₂ x y
  · exact hG₃ x y
  · exact G.injective.eq_iff

section Map

variable {σ : K →+* K} [RingHomSurjective σ]

theorem finrank_map_of_injective_semilinear (φ : V →ₛₗ[σ] V) (hφ : Function.Injective φ)
    (U : Submodule K V) : finrank K (U.map φ) = finrank K U := by
  have hσ : Function.Bijective σ := ⟨σ.injective, RingHomSurjective.is_surjective⟩
  let j : U ≃+ U.map φ := AddEquiv.ofBijective (φ.submoduleMap U).toAddMonoidHom
    ⟨fun a b h => Subtype.ext (hφ (congrArg Subtype.val h)), φ.submoduleMap_surjective U⟩
  have h := rank_eq_of_equiv_equiv σ j hσ (fun r m => (φ.submoduleMap U).map_smulₛₗ r m)
  simp only [Module.finrank, h]

variable (φ : V →ₛₗ[σ] V) (hφ : Function.Bijective φ) (hiso : ∀ v, P.Iso (φ v) ↔ P.Iso v)

@[expose] def PFlag.map (x : PFlag P) : PFlag P where
  V₁ := x.V₁.map φ
  V₂ := x.V₂.map φ
  V₃ := x.V₃.map φ
  finrank₁ := (finrank_map_of_injective_semilinear φ hφ.1 _).trans x.finrank₁
  finrank₂ := (finrank_map_of_injective_semilinear φ hφ.1 _).trans x.finrank₂
  finrank₃ := (finrank_map_of_injective_semilinear φ hφ.1 _).trans x.finrank₃
  le₁₂ := Submodule.map_mono x.le₁₂
  le₂₃ := Submodule.map_mono x.le₂₃
  isTI := by
    rintro _ ⟨v, hv, rfl⟩
    exact (hiso v).mpr (x.isTI v hv)

theorem PFlag.map_bijective : Function.Bijective (PFlag.map φ hφ hiso) := by
  have hinj := Submodule.map_injective_of_injective (f := φ) hφ.1
  have hcm : ∀ U : Submodule K V, (U.comap φ).map φ = U := fun U =>
    Submodule.map_comap_eq_of_surjective hφ.2 U
  refine ⟨fun x y h => ?_, fun y => ?_⟩
  · exact PFlag.ext (hinj (congrArg PFlag.V₁ h)) (hinj (congrArg PFlag.V₂ h))
      (hinj (congrArg PFlag.V₃ h))
  · refine ⟨⟨y.V₁.comap φ, y.V₂.comap φ, y.V₃.comap φ, ?_, ?_, ?_, Submodule.comap_mono y.le₁₂,
      Submodule.comap_mono y.le₂₃, fun v hv => (hiso v).mp (y.isTI _ hv)⟩, ?_⟩
    · rw [← finrank_map_of_injective_semilinear φ hφ.1, hcm, y.finrank₁]
    · rw [← finrank_map_of_injective_semilinear φ hφ.1, hcm, y.finrank₂]
    · rw [← finrank_map_of_injective_semilinear φ hφ.1, hcm, y.finrank₃]
    · exact PFlag.ext (hcm _) (hcm _) (hcm _)

@[expose] noncomputable def polarFlagPerm : Equiv.Perm (PFlag P) :=
  Equiv.ofBijective _ (PFlag.map_bijective φ hφ hiso)

@[simp] theorem polarFlagPerm_V₁ (x : PFlag P) : (polarFlagPerm φ hφ hiso x).V₁ = x.V₁.map φ :=
  rfl

@[simp] theorem polarFlagPerm_V₂ (x : PFlag P) : (polarFlagPerm φ hφ hiso x).V₂ = x.V₂.map φ :=
  rfl

@[simp] theorem polarFlagPerm_V₃ (x : PFlag P) : (polarFlagPerm φ hφ hiso x).V₃ = x.V₃.map φ :=
  rfl

theorem polarFlagPerm_mem_typeAut (p l π : ι) :
    polarFlagPerm φ hφ hiso ∈ (polarChamber P p l π).typeAut := by
  have hinj : ∀ U U' : Submodule K V, U.map φ = U'.map φ ↔ U = U' := fun _ _ =>
    (Submodule.map_injective_of_injective hφ.1).eq_iff
  exact ChamberSystem.ofThree_mem_typeAut
    (fun x y => by simp only [polarFlagPerm_V₂, polarFlagPerm_V₃, hinj])
    (fun x y => by simp only [polarFlagPerm_V₁, polarFlagPerm_V₃, hinj])
    (fun x y => by simp only [polarFlagPerm_V₁, polarFlagPerm_V₂, hinj])

end Map

variable [FiniteDimensional K V]

theorem exists_line_between {Q S : Submodule K V} (hQ : finrank K Q = 1) (hS : finrank K S = 3)
    (hQS : Q ≤ S) : ∃ L : Submodule K V, Q ≤ L ∧ L ≤ S ∧ finrank K L = 2 :=
  exists_between_finrank hQS (by omega) (by omega)

theorem finrank_sup_of_ne' {Q Q' : Submodule K V} (hQ : finrank K Q = 1)
    (hQ' : finrank K Q' = 1) (hne : Q ≠ Q') : finrank K ↥(Q ⊔ Q') = 2 := by
  have h := Submodule.finrank_sup_add_finrank_inf_eq Q Q'
  have hle : finrank K ↥(Q ⊓ Q') ≤ 1 := hQ ▸ Submodule.finrank_mono inf_le_left
  have hne' : finrank K ↥(Q ⊓ Q') ≠ 1 := by
    intro h1
    have h₁ : Q ⊓ Q' = Q := Submodule.eq_of_le_of_finrank_eq inf_le_left (h1.trans hQ.symm)
    have h₂ : Q ⊓ Q' = Q' := Submodule.eq_of_le_of_finrank_eq inf_le_right (h1.trans hQ'.symm)
    exact hne (h₁.symm.trans h₂)
  omega

section Residues

variable (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π)
include hpl hlπ hpπ

theorem mem_residue_pl_iff {x y : PFlag P} :
    y ∈ (polarChamber P p l π).residue {p, l} x ↔ y.V₃ = x.V₃ := by
  constructor
  · rintro ⟨γ, hγ, hJ, rfl⟩
    induction γ generalizing x with
    | nil => rfl
    | cons q γ ih =>
      obtain ⟨h1, h2⟩ := hγ
      have hq : q.1 = p ∨ q.1 = l := by simpa using hJ q.1 (by simp)
      have h3 : q.2.V₃ = x.V₃ := by
        rcases hq with hq | hq
        · rw [hq, polarChamber_adj_p] at h1
          exact h1.2.symm
        · rw [hq, polarChamber_adj_l hpl] at h1
          exact h1.2.symm
      rw [galleryEnd_cons, ih h2 (fun i hi => hJ i (by simp [hi])), h3]
  · intro h
    have hstep : ∀ (i : ι) (a b : PFlag P), (polarChamber P p l π).adj i a b → (i = p ∨ i = l) →
        b ∈ (polarChamber P p l π).residue {p, l} a := fun i a b hab hi =>
      ChamberSystem.residue_mono (Set.singleton_subset_iff.mpr (by
        rcases hi with rfl | rfl <;> simp)) a (ChamberSystem.mem_residue_singleton.mpr hab)
    by_cases hxy : x.V₁ ≤ y.V₂
    ·
      let z : PFlag P := ⟨x.V₁, y.V₂, x.V₃, x.finrank₁, y.finrank₂, x.finrank₃, hxy,
        h ▸ y.le₂₃, x.isTI⟩
      refine ChamberSystem.mem_residue_trans (y := z) (hstep l x z ?_ (Or.inr rfl))
        (hstep p z y ?_ (Or.inl rfl))
      · rw [polarChamber_adj_l hpl]; exact ⟨rfl, rfl⟩
      · rw [polarChamber_adj_p]; exact ⟨rfl, h.symm⟩
    · have hne : x.V₁ ≠ y.V₁ := fun e => hxy (e ▸ y.le₁₂)
      set L := x.V₁ ⊔ y.V₁
      have hL : finrank K L = 2 := finrank_sup_of_ne' x.finrank₁ y.finrank₁ hne
      have hLS : L ≤ x.V₃ := sup_le (x.le₁₂.trans x.le₂₃) (h ▸ y.le₁₂.trans y.le₂₃)
      let z₁ : PFlag P := ⟨x.V₁, L, x.V₃, x.finrank₁, hL, x.finrank₃, le_sup_left, hLS, x.isTI⟩
      let z₂ : PFlag P := ⟨y.V₁, L, x.V₃, y.finrank₁, hL, x.finrank₃, le_sup_right, hLS, x.isTI⟩
      refine ChamberSystem.mem_residue_trans (y := z₁) (hstep l x z₁ ?_ (Or.inr rfl))
        (ChamberSystem.mem_residue_trans (y := z₂) (hstep p z₁ z₂ ?_ (Or.inl rfl))
          (hstep l z₂ y ?_ (Or.inr rfl)))
      · rw [polarChamber_adj_l hpl]; exact ⟨rfl, rfl⟩
      · rw [polarChamber_adj_p]; exact ⟨rfl, rfl⟩
      · rw [polarChamber_adj_l hpl]; exact ⟨rfl, h.symm⟩

omit [FiniteDimensional K V] hpl in
theorem mem_residue_pπ_iff {x y : PFlag P} :
    y ∈ (polarChamber P p l π).residue {p, π} x ↔ y.V₂ = x.V₂ := by
  constructor
  · rintro ⟨γ, hγ, hJ, rfl⟩
    induction γ generalizing x with
    | nil => rfl
    | cons q γ ih =>
      obtain ⟨h1, h2⟩ := hγ
      have hq : q.1 = p ∨ q.1 = π := by simpa using hJ q.1 (by simp)
      have h3 : q.2.V₂ = x.V₂ := by
        rcases hq with hq | hq
        · rw [hq, polarChamber_adj_p] at h1
          exact h1.1.symm
        · rw [hq, polarChamber_adj_π hpπ hlπ] at h1
          exact h1.2.symm
      rw [galleryEnd_cons, ih h2 (fun i hi => hJ i (by simp [hi])), h3]
  · intro h
    let z : PFlag P := ⟨y.V₁, x.V₂, x.V₃, y.finrank₁, x.finrank₂, x.finrank₃, h ▸ y.le₁₂,
      x.le₂₃, x.isTI⟩
    refine ChamberSystem.mem_residue_trans (y := z) ?_ ?_
    · refine ChamberSystem.residue_mono
        (Set.singleton_subset_iff.mpr (by simp : p ∈ ({p, π} : Set ι))) x
        (ChamberSystem.mem_residue_singleton.mpr ?_)
      rw [polarChamber_adj_p]; exact ⟨rfl, rfl⟩
    · refine ChamberSystem.residue_mono
        (Set.singleton_subset_iff.mpr (by simp : π ∈ ({p, π} : Set ι))) z
        (ChamberSystem.mem_residue_singleton.mpr ?_)
      rw [polarChamber_adj_π hpπ hlπ]; exact ⟨rfl, h.symm⟩

theorem mem_residue_lπ_iff {x y : PFlag P} :
    y ∈ (polarChamber P p l π).residue {l, π} x ↔ y.V₁ = x.V₁ := by
  constructor
  · rintro ⟨γ, hγ, hJ, rfl⟩
    induction γ generalizing x with
    | nil => rfl
    | cons q γ ih =>
      obtain ⟨h1, h2⟩ := hγ
      have hq : q.1 = l ∨ q.1 = π := by simpa using hJ q.1 (by simp)
      have h3 : q.2.V₁ = x.V₁ := by
        rcases hq with hq | hq
        · rw [hq, polarChamber_adj_l hpl] at h1
          exact h1.1.symm
        · rw [hq, polarChamber_adj_π hpπ hlπ] at h1
          exact h1.1.symm
      rw [galleryEnd_cons, ih h2 (fun i hi => hJ i (by simp [hi])), h3]
  · intro h
    have hl : ∀ a b : PFlag P, a.V₁ = b.V₁ → a.V₃ = b.V₃ →
        b ∈ (polarChamber P p l π).residue {l, π} a := fun a b h1 h3 =>
      ChamberSystem.residue_mono
        (Set.singleton_subset_iff.mpr (by simp : l ∈ ({l, π} : Set ι))) a
        (ChamberSystem.mem_residue_singleton.mpr
          (by rw [polarChamber_adj_l hpl]; exact ⟨h1, h3⟩))
    have hπ : ∀ a b : PFlag P, a.V₁ = b.V₁ → a.V₂ = b.V₂ →
        b ∈ (polarChamber P p l π).residue {l, π} a := fun a b h1 h2 =>
      ChamberSystem.residue_mono
        (Set.singleton_subset_iff.mpr (by simp : π ∈ ({l, π} : Set ι))) a
        (ChamberSystem.mem_residue_singleton.mpr
          (by rw [polarChamber_adj_π hpπ hlπ]; exact ⟨h1, h2⟩))
    have htrans := @ChamberSystem.mem_residue_trans ι (PFlag P) (polarChamber P p l π) {l, π}
    by_cases ha : x.V₂ ≤ y.V₃
    · let z : PFlag P := ⟨x.V₁, x.V₂, y.V₃, x.finrank₁, x.finrank₂, y.finrank₃, x.le₁₂, ha,
        y.isTI⟩
      exact htrans (hπ x z rfl rfl) (hl z y h.symm rfl)
    by_cases hb : y.V₂ ≤ x.V₃
    · let z : PFlag P := ⟨x.V₁, y.V₂, x.V₃, x.finrank₁, y.finrank₂, x.finrank₃, h ▸ y.le₁₂, hb,
        x.isTI⟩
      exact htrans (hl x z rfl rfl) (hπ z y h.symm rfl)
    obtain ⟨w, hw, hwQ⟩ := exists_mem_not_mem_of_finrank_lt (U := x.V₁) (U' := x.V₂)
      (by rw [x.finrank₁, x.finrank₂]; omega)
    have hx2 : x.V₂ = x.V₁ ⊔ K ∙ w := (eq_of_le_of_finrank_le (sup_le x.le₁₂
      ((Submodule.span_singleton_le_iff_mem w _).mpr hw)) (by
        rw [finrank_sup_span_of_not_mem hwQ, x.finrank₁, x.finrank₂])).symm
    have hQ : x.V₁ ≤ y.V₃ ⊓ LinearMap.ker (P.pair w) := by
      refine le_inf (h ▸ y.le₁₂.trans y.le₂₃) fun q hq => ?_
      exact LinearMap.mem_ker.mpr (P.pair_eq_zero_of_isTI _ x.isTI w (x.le₂₃ hw) q
        (x.le₂₃ (x.le₁₂ hq)))
    obtain ⟨L, hQL, hL, hL2⟩ := exists_between_finrank (m := 2) hQ (by rw [x.finrank₁]; omega)
      (by
      have := finrank_le_finrank_inf_ker_add_one y.V₃ (P.pair w)
      rw [y.finrank₃] at this
      omega)
    have hLS : L ≤ y.V₃ := hL.trans inf_le_left
    obtain ⟨w', hw', hw'Q⟩ := exists_mem_not_mem_of_finrank_lt (U := x.V₁) (U' := L)
      (by rw [x.finrank₁, hL2]; omega)
    have hLeq : L = x.V₁ ⊔ K ∙ w' := (eq_of_le_of_finrank_le (sup_le hQL
      ((Submodule.span_singleton_le_iff_mem w' _).mpr hw')) (by
        rw [finrank_sup_span_of_not_mem hw'Q, x.finrank₁, hL2])).symm
    have hw'x : w' ∉ x.V₂ := by
      intro hw'2
      apply ha
      have : L ≤ x.V₂ := hLeq ▸ sup_le x.le₁₂ ((Submodule.span_singleton_le_iff_mem w' _).mpr hw'2)
      have hLx : L = x.V₂ := eq_of_le_of_finrank_le this (by rw [hL2, x.finrank₂])
      rw [← hLx]
      exact hLS
    set S := x.V₂ ⊔ K ∙ w' with hSdef
    have hS3 : finrank K S = 3 := by rw [finrank_sup_span_of_not_mem hw'x, x.finrank₂]
    have hSTI : ∀ v ∈ S, P.Iso v := by
      refine P.isTI_sup _ (P.isTI_mono x.isTI x.le₂₃) w' (y.isTI w' (hLS hw')) fun u hu => ?_
      rw [hx2] at hu
      obtain ⟨q, hq, t, ht, rfl⟩ := Submodule.mem_sup.mp hu
      obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp ht
      rw [map_add, map_smul]
      have h1 : P.pair w' q = 0 := P.pair_eq_zero_of_isTI _ y.isTI w' (hLS hw') q
        (h ▸ y.le₁₂.trans y.le₂₃ |> fun hh => hh hq)
      have h2 : P.pair w' w = 0 := (P.pair_eq_zero_comm w w').mp
        (LinearMap.mem_ker.mp (hL hw').2)
      rw [h1, h2, smul_zero, add_zero]
    have hLS' : L ≤ S := hLeq ▸ sup_le (x.le₁₂.trans le_sup_left) le_sup_right
    let z₁ : PFlag P := ⟨x.V₁, x.V₂, S, x.finrank₁, x.finrank₂, hS3, x.le₁₂, le_sup_left, hSTI⟩
    let z₂ : PFlag P := ⟨x.V₁, L, S, x.finrank₁, hL2, hS3, hQL, hLS', hSTI⟩
    let z₃ : PFlag P := ⟨x.V₁, L, y.V₃, x.finrank₁, hL2, y.finrank₃, hQL, hLS, y.isTI⟩
    exact htrans (hπ x z₁ rfl rfl) (htrans (hl z₁ z₂ rfl rfl) (htrans (hπ z₂ z₃ rfl rfl)
      (hl z₃ y h.symm rfl)))

end Residues


section Frame

theorem eq_span_of_finrank_eq_one {U : Submodule K V} (hU : finrank K U = 1) {v : V} (hv : v ∈ U)
    (hv0 : v ≠ 0) : U = K ∙ v :=
  (eq_of_le_of_finrank_le ((Submodule.span_singleton_le_iff_mem v U).mpr hv)
    (by rw [hU, finrank_span_singleton hv0])).symm

omit [FiniteDimensional K V] in
theorem exists_ne_zero_of_finrank_pos {U : Submodule K V} (h : 0 < finrank K U) :
    ∃ v ∈ U, v ≠ 0 :=
  Submodule.exists_mem_ne_zero_of_ne_bot fun h' => by rw [h', finrank_bot] at h; omega

theorem sup_span_eq {U U' : Submodule K V} (hUU' : U ≤ U') {v : V} (hv : v ∈ U') (hvU : v ∉ U)
    (h : finrank K U' ≤ finrank K U + 1) : U ⊔ K ∙ v = U' :=
  eq_of_le_of_finrank_le (sup_le hUU' ((Submodule.span_singleton_le_iff_mem v U').mpr hv))
    (by rw [finrank_sup_span_of_not_mem hvU]; exact h)

omit [FiniteDimensional K V] in
theorem mem_sup_span_singleton {U : Submodule K V} {a v : V} :
    v ∈ U ⊔ K ∙ a ↔ ∃ u ∈ U, ∃ c : K, v = u + c • a := by
  rw [Submodule.mem_sup]
  constructor
  · rintro ⟨u, hu, w, hw, rfl⟩
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
    exact ⟨u, hu, c, rfl⟩
  · rintro ⟨u, hu, c, rfl⟩
    exact ⟨u, hu, c • a, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a), rfl⟩

omit [FiniteDimensional K V] in
theorem mem_span_singleton_sup_span_singleton {a b v : V} :
    v ∈ K ∙ a ⊔ K ∙ b ↔ ∃ α β : K, v = α • a + β • b := by
  rw [mem_sup_span_singleton]
  constructor
  · rintro ⟨u, hu, c, rfl⟩
    obtain ⟨α, rfl⟩ := Submodule.mem_span_singleton.mp hu
    exact ⟨α, c, rfl⟩
  · rintro ⟨α, β, rfl⟩
    exact ⟨α • a, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self a), β, rfl⟩

omit [FiniteDimensional K V] in
theorem mem_span_three {a b c v : V} :
    v ∈ K ∙ a ⊔ K ∙ b ⊔ K ∙ c ↔ ∃ α β γ : K, v = α • a + β • b + γ • c := by
  rw [mem_sup_span_singleton]
  constructor
  · rintro ⟨u, hu, γ, rfl⟩
    obtain ⟨α, β, rfl⟩ := mem_span_singleton_sup_span_singleton.mp hu
    exact ⟨α, β, γ, rfl⟩
  · rintro ⟨α, β, γ, rfl⟩
    exact ⟨α • a + β • b, mem_span_singleton_sup_span_singleton.mpr ⟨α, β, rfl⟩, γ, rfl⟩

omit [FiniteDimensional K V] in
theorem pair_inv_smul_self {w u : V} (h : P.pair w u ≠ 0) : P.pair w ((P.pair w u)⁻¹ • u) = 1 := by
  rw [map_smul, smul_eq_mul, inv_mul_cancel₀ h]

theorem exists_frame {x y : PFlag P} (h3 : x.V₃ ⊓ y.V₃ = ⊥)
    (h1 : ∀ u ∈ x.V₁, ∀ v ∈ y.V₁, u ≠ 0 → v ≠ 0 → P.pair v u ≠ 0)
    (h2 : ∀ w ∈ x.V₂, (∀ v ∈ y.V₂, P.pair v w = 0) → w = 0) :
    ∃ e f : Fin 3 → V, (∀ i j, P.pair (f j) (e i) = if i = j then 1 else 0) ∧
      x.V₁ = K ∙ e 0 ∧ x.V₂ = K ∙ e 0 ⊔ K ∙ e 1 ∧ x.V₃ = K ∙ e 0 ⊔ K ∙ e 1 ⊔ K ∙ e 2 ∧
      y.V₁ = K ∙ f 0 ∧ y.V₂ = K ∙ f 0 ⊔ K ∙ f 1 ∧ y.V₃ = K ∙ f 0 ⊔ K ∙ f 1 ⊔ K ∙ f 2 := by
  have comm := P.pair_eq_zero_comm
  have one_ne : (1 : K) ≠ 0 := one_ne_zero
  obtain ⟨u, hu, hu0⟩ := exists_ne_zero_of_finrank_pos (U := x.V₁) (by rw [x.finrank₁]; omega)
  obtain ⟨f₀, hf₀, hf₀0⟩ := exists_ne_zero_of_finrank_pos (U := y.V₁) (by rw [y.finrank₁]; omega)
  have hpu := h1 u hu f₀ hf₀ hu0 hf₀0
  set e₀ := (P.pair f₀ u)⁻¹ • u with he₀
  have hfe₀ : P.pair f₀ e₀ = 1 := pair_inv_smul_self hpu
  have he₀0 : e₀ ≠ 0 := fun h => by rw [h, map_zero] at hfe₀; exact one_ne hfe₀.symm
  have hx1 : x.V₁ = K ∙ e₀ := eq_span_of_finrank_eq_one x.finrank₁ (x.V₁.smul_mem _ hu) he₀0
  have hy1 : y.V₁ = K ∙ f₀ := eq_span_of_finrank_eq_one y.finrank₁ hf₀ hf₀0
  have hef₀ : P.pair e₀ f₀ ≠ 0 := fun h => one_ne (hfe₀.symm.trans ((comm _ _).mp h))
  clear_value e₀
  obtain ⟨w, hw, hw0⟩ := exists_ne_zero_of_finrank_pos
    (U := x.V₂ ⊓ LinearMap.ker (P.pair f₀)) (by
      have := finrank_le_finrank_inf_ker_add_one x.V₂ (P.pair f₀)
      rw [x.finrank₂] at this
      omega)
  obtain ⟨hwx, hwk⟩ := Submodule.mem_inf.mp hw
  rw [LinearMap.mem_ker] at hwk
  obtain ⟨f₁, hf₁', hf₁0⟩ := exists_ne_zero_of_finrank_pos
    (U := y.V₂ ⊓ LinearMap.ker (P.pair e₀)) (by
      have := finrank_le_finrank_inf_ker_add_one y.V₂ (P.pair e₀)
      rw [y.finrank₂] at this
      omega)
  obtain ⟨hf₁y, hf₁k⟩ := Submodule.mem_inf.mp hf₁'
  rw [LinearMap.mem_ker] at hf₁k
  have hwe₀ : w ∉ K ∙ e₀ := by
    intro h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
    rw [map_smul, hfe₀, smul_eq_mul, mul_one] at hwk
    exact hw0 (by rw [hwk, zero_smul])
  have hf₁f₀ : f₁ ∉ K ∙ f₀ := by
    intro h
    obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp h
    rw [map_smul, smul_eq_mul] at hf₁k
    rcases mul_eq_zero.mp hf₁k with hc | hc
    · exact hf₁0 (by rw [hc, zero_smul])
    · exact hef₀ hc
  have hx2 : x.V₂ = K ∙ e₀ ⊔ K ∙ w := (sup_span_eq (hx1 ▸ x.le₁₂) hwx hwe₀
    (by rw [x.finrank₂, finrank_span_singleton he₀0])).symm
  have hy2 : y.V₂ = K ∙ f₀ ⊔ K ∙ f₁ := (sup_span_eq (hy1 ▸ y.le₁₂) hf₁y hf₁f₀
    (by rw [y.finrank₂, finrank_span_singleton hf₀0])).symm
  have hpw : P.pair f₁ w ≠ 0 := by
    intro h
    refine hw0 (h2 w hwx fun v hv => ?_)
    rw [hy2] at hv
    obtain ⟨α, β, rfl⟩ := mem_span_singleton_sup_span_singleton.mp hv
    refine (comm w _).mp ?_
    rw [map_add, map_smul, map_smul, (comm _ _).mp hwk, (comm _ _).mp h, smul_zero, smul_zero,
      add_zero]
  set e₁ := (P.pair f₁ w)⁻¹ • w with he₁
  have hfe₁ : P.pair f₁ e₁ = 1 := pair_inv_smul_self hpw
  have hf₀e₁ : P.pair f₀ e₁ = 0 := by rw [he₁, map_smul, hwk, smul_zero]
  have hf₁e₀ : P.pair f₁ e₀ = 0 := (comm _ _).mp hf₁k
  have hspan₁ : K ∙ e₁ = K ∙ w := Submodule.span_singleton_smul_eq (inv_ne_zero hpw).isUnit w
  have hef₁ : P.pair e₁ f₁ ≠ 0 := fun h => one_ne (hfe₁.symm.trans ((comm _ _).mp h))
  have he₁0 : e₁ ≠ 0 := fun h => by rw [h, map_zero] at hfe₁; exact one_ne hfe₁.symm
  have hx2' : x.V₂ = K ∙ e₀ ⊔ K ∙ e₁ := by rw [hspan₁]; exact hx2
  clear_value e₁
  obtain ⟨z, hz, hz0⟩ := exists_ne_zero_of_finrank_pos
    (U := x.V₃ ⊓ LinearMap.ker (P.pair f₀) ⊓ LinearMap.ker (P.pair f₁)) (by
      have a1 := finrank_le_finrank_inf_ker_add_one x.V₃ (P.pair f₀)
      have a2 := finrank_le_finrank_inf_ker_add_one (x.V₃ ⊓ LinearMap.ker (P.pair f₀))
        (P.pair f₁)
      rw [x.finrank₃] at a1
      omega)
  obtain ⟨hz', hz₁⟩ := Submodule.mem_inf.mp hz
  obtain ⟨hzx, hz₀⟩ := Submodule.mem_inf.mp hz'
  rw [LinearMap.mem_ker] at hz₀ hz₁
  obtain ⟨f₂, hf₂', hf₂0⟩ := exists_ne_zero_of_finrank_pos
    (U := y.V₃ ⊓ LinearMap.ker (P.pair e₀) ⊓ LinearMap.ker (P.pair e₁)) (by
      have a1 := finrank_le_finrank_inf_ker_add_one y.V₃ (P.pair e₀)
      have a2 := finrank_le_finrank_inf_ker_add_one (y.V₃ ⊓ LinearMap.ker (P.pair e₀))
        (P.pair e₁)
      rw [y.finrank₃] at a1
      omega)
  obtain ⟨hf₂'', hf₂₁⟩ := Submodule.mem_inf.mp hf₂'
  obtain ⟨hf₂y, hf₂₀⟩ := Submodule.mem_inf.mp hf₂''
  rw [LinearMap.mem_ker] at hf₂₀ hf₂₁
  have hzE : z ∉ K ∙ e₀ ⊔ K ∙ e₁ := by
    intro h
    obtain ⟨α, β, rfl⟩ := mem_span_singleton_sup_span_singleton.mp h
    rw [map_add, map_smul, map_smul, hfe₀, hf₀e₁, smul_eq_mul, smul_eq_mul, mul_one, mul_zero,
      add_zero] at hz₀
    rw [map_add, map_smul, map_smul, hf₁e₀, hfe₁, smul_eq_mul, smul_eq_mul, mul_one, mul_zero,
      zero_add] at hz₁
    exact hz0 (by rw [hz₀, hz₁, zero_smul, zero_smul, add_zero])
  have he₁f₀ : P.pair e₁ f₀ = 0 := (comm _ _).mp hf₀e₁
  have hf₂F : f₂ ∉ K ∙ f₀ ⊔ K ∙ f₁ := by
    intro h
    obtain ⟨α, β, rfl⟩ := mem_span_singleton_sup_span_singleton.mp h
    rw [map_add, map_smul, map_smul, hf₁k, smul_eq_mul, smul_eq_mul, mul_zero, add_zero] at hf₂₀
    rw [map_add, map_smul, map_smul, he₁f₀, smul_eq_mul, smul_eq_mul, mul_zero, zero_add] at hf₂₁
    have hα : α = 0 := (mul_eq_zero.mp hf₂₀).resolve_right hef₀
    have hβ : β = 0 := (mul_eq_zero.mp hf₂₁).resolve_right hef₁
    exact hf₂0 (by rw [hα, hβ, zero_smul, zero_smul, add_zero])
  have hx3 : x.V₃ = K ∙ e₀ ⊔ K ∙ e₁ ⊔ K ∙ z := (sup_span_eq (hx2' ▸ x.le₂₃) hzx hzE (by
    rw [x.finrank₃, ← hx2', x.finrank₂])).symm
  have hy3 : y.V₃ = K ∙ f₀ ⊔ K ∙ f₁ ⊔ K ∙ f₂ := (sup_span_eq (hy2 ▸ y.le₂₃) hf₂y hf₂F (by
    rw [y.finrank₃, ← hy2, y.finrank₂])).symm
  have hpz : P.pair f₂ z ≠ 0 := by
    intro h
    have hperp : ∀ v ∈ y.V₃, P.pair z v = 0 := by
      intro v hv
      rw [hy3] at hv
      obtain ⟨α, β, γ, rfl⟩ := mem_span_three.mp hv
      rw [map_add, map_add, map_smul, map_smul, map_smul, (comm _ _).mp hz₀, (comm _ _).mp hz₁,
        (comm _ _).mp h, smul_zero, smul_zero, smul_zero, add_zero, add_zero]
    have hTI := P.isTI_sup y.V₃ y.isTI z (x.isTI z hzx) hperp
    by_cases hzy : z ∈ y.V₃
    · exact hz0 ((Submodule.mem_bot K).mp (h3 ▸ Submodule.mem_inf.mpr ⟨hzx, hzy⟩))
    · have := P.finrank_le_three _ hTI
      rw [finrank_sup_span_of_not_mem hzy, y.finrank₃] at this
      omega
  set e₂ := (P.pair f₂ z)⁻¹ • z with he₂
  have hfe₂ : P.pair f₂ e₂ = 1 := pair_inv_smul_self hpz
  have hf₀e₂ : P.pair f₀ e₂ = 0 := by rw [he₂, map_smul, hz₀, smul_zero]
  have hf₁e₂ : P.pair f₁ e₂ = 0 := by rw [he₂, map_smul, hz₁, smul_zero]
  have hf₂e₀ : P.pair f₂ e₀ = 0 := (comm _ _).mp hf₂₀
  have hf₂e₁ : P.pair f₂ e₁ = 0 := (comm _ _).mp hf₂₁
  have hspan₂ : K ∙ e₂ = K ∙ z := Submodule.span_singleton_smul_eq (inv_ne_zero hpz).isUnit z
  refine ⟨![e₀, e₁, e₂], ![f₀, f₁, f₂], ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro i j
    fin_cases i <;> fin_cases j <;>
      simp [hfe₀, hfe₁, hfe₂, hf₀e₁, hf₀e₂, hf₁e₀, hf₁e₂, hf₂e₀, hf₂e₁]
  · exact hx1
  · exact hx2'
  · simpa [hspan₂] using hx3
  · exact hy1
  · exact hy2
  · exact hy3

end Frame

section Opposite

variable {M : CoxeterMatrix ι} {W : Type*} [Group W] {cs : CoxeterSystem M W}
  {C : Type*} {δ : C → C → W}

theorem length_dist_le_add (hδ : IsWeylDistanceBuilding cs δ) (x y z : C) :
    cs.length (δ x z) ≤ cs.length (δ x y) + cs.length (δ y z) := by
  suffices key : ∀ (y : C) (γ : List (ι × C)), IsStrictGallery cs δ y γ →
      cs.length (δ x (galleryEnd y γ)) ≤ cs.length (δ x y) + γ.length by
    obtain ⟨ω, hω, hωp⟩ := cs.exists_isReduced (δ y z)
    obtain ⟨γ, hγ, ht, he⟩ := exists_strictGallery hδ hω hωp.symm
    have hlen : cs.length (δ y z) = γ.length := by
      rw [hωp, hω.eq, ← ht, length_galleryType]
    have := key y γ hγ
    rwa [he, ← hlen] at this
  intro y γ hγ
  induction γ generalizing y with
  | nil => simp
  | cons q γ ih =>
    obtain ⟨h1, h2⟩ := hγ
    have h3 := ih q.2 h2
    have h4 : cs.length (δ x q.2) ≤ cs.length (δ x y) + 1 := by
      rcases (hδ.mul_simple x y q.2 q.1 h1).1 with h | h
      · rw [h]; omega
      · rw [h]
        have := cs.length_mul_le (δ x y) (cs.simple q.1)
        rwa [cs.length_simple] at this
    simp only [galleryEnd_cons, List.length_cons]
    omega

variable {f : C → PFlag P} (hf : IsChamberModel cs δ (polarChamber P p l π) f)
  (hpl : p ≠ l) (hlπ : l ≠ π) (hpπ : p ≠ π)
include hf hpl hlπ hpπ

theorem polar_mem_residue_pl {x y : C} : y ∈ residue cs δ {p, l} x ↔ (f y).V₃ = (f x).V₃ :=
  hf.mem_residue_iff.trans (mem_residue_pl_iff hpl hlπ hpπ)

theorem polar_mem_residue_lπ {x y : C} : y ∈ residue cs δ {l, π} x ↔ (f y).V₁ = (f x).V₁ :=
  hf.mem_residue_iff.trans (mem_residue_lπ_iff hpl hlπ hpπ)

omit [FiniteDimensional K V] hpl in
theorem polar_mem_residue_pπ {x y : C} : y ∈ residue cs δ {p, π} x ↔ (f y).V₂ = (f x).V₂ :=
  hf.mem_residue_iff.trans (mem_residue_pπ_iff hlπ hpπ)

variable [Finite W] (hδ : IsWeylDistanceBuilding cs δ) (hι : ∀ i, i = p ∨ i = l ∨ i = π)
  (hMpl : M p l = 3) (hMlπ : M l π = 4) (hMpπ : M p π = 2)
include hδ hι hMpl hMlπ hMpπ

omit hf in
theorem polar_nine_le {c d : C} (hcd : δ c d = longest cs Set.univ) {J : Set ι} {a b : C}
    (ha : a ∈ residue cs δ J c) (hb : b ∈ residue cs δ J d) :
    9 ≤ cs.length (δ a b) + cs.length (longest cs J) :=
  (nine_le_length_longest_C3 hpl hlπ hpπ hι hMpl hMlπ hMpπ).trans
    (length_longest_le_of_mem_residue hδ (longest_comm_C3 hpl hlπ hpπ hι hMpl hMlπ hMpπ) hcd
      ha hb)

theorem polar_opposite_plane {c d : C} (hcd : δ c d = longest cs Set.univ) :
    (f c).V₃ ⊓ (f d).V₃ = ⊥ := by
  by_contra hne
  obtain ⟨q, hq, hq0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨hqc, hqd⟩ := Submodule.mem_inf.mp hq
  have hQ := finrank_span_singleton (K := K) hq0
  obtain ⟨L, hQL, hLS, hL⟩ := exists_line_between hQ (f c).finrank₃
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hqc)
  obtain ⟨L', hQL', hLS', hL'⟩ := exists_line_between hQ (f d).finrank₃
    ((Submodule.span_singleton_le_iff_mem _ _).mpr hqd)
  obtain ⟨a, ha⟩ := hf.1.2 ⟨K ∙ q, L, (f c).V₃, hQ, hL, (f c).finrank₃, hQL, hLS, (f c).isTI⟩
  obtain ⟨b, hb⟩ := hf.1.2 ⟨K ∙ q, L', (f d).V₃, hQ, hL', (f d).finrank₃, hQL', hLS',
    (f d).isTI⟩
  have haR : a ∈ residue cs δ {p, l} c := (polar_mem_residue_pl hf hpl hlπ hpπ).mpr (by rw [ha])
  have hbR : b ∈ residue cs δ {p, l} d := (polar_mem_residue_pl hf hpl hlπ hpπ).mpr (by rw [hb])
  have hab : b ∈ residue cs δ {l, π} a :=
    (polar_mem_residue_lπ hf hpl hlπ hpπ).mpr (by rw [ha, hb])
  have h1 := polar_nine_le hpl hlπ hpπ hδ hι hMpl hMlπ hMpπ hcd haR hbR
  have h2 := length_le_of_mem_parabolic_pair (cs := cs) (i := l) (j := π) (by omega)
    (mem_parabolic_of_mem_residue hδ (self_mem_residue _ a) hab)
  rw [length_longest_pair hpl (by omega), hMpl] at h1
  rw [hMlπ] at h2
  omega

theorem polar_opposite_point {c d : C} (hcd : δ c d = longest cs Set.univ) {u v : V}
    (hu : u ∈ (f c).V₁) (hv : v ∈ (f d).V₁) (hu0 : u ≠ 0) (hv0 : v ≠ 0) : P.pair v u ≠ 0 := by
  intro huv
  have hU1 : (f c).V₁ = K ∙ u := eq_span_of_finrank_eq_one (f c).finrank₁ hu hu0
  have hV1 : (f d).V₁ = K ∙ v := eq_span_of_finrank_eq_one (f d).finrank₁ hv hv0
  have hvd : v ∈ (f d).V₃ := (f d).le₂₃ ((f d).le₁₂ hv)
  have hQ : (f c).V₁ ≤ (f c).V₃ ⊓ LinearMap.ker (P.pair v) := by
    refine le_inf ((f c).le₁₂.trans (f c).le₂₃) ?_
    rw [hU1, Submodule.span_singleton_le_iff_mem, LinearMap.mem_ker]
    exact huv
  obtain ⟨L₀, hQL₀, hL₀, hL₀2⟩ := exists_between_finrank (m := 2) hQ
    (by rw [(f c).finrank₁]; omega) (by
      have := finrank_le_finrank_inf_ker_add_one (f c).V₃ (P.pair v)
      rw [(f c).finrank₃] at this
      omega)
  have hL₀3 : L₀ ≤ (f c).V₃ := hL₀.trans inf_le_left
  obtain ⟨S, hS3, hSTI, hcS, hdS⟩ : ∃ S : Submodule K V, finrank K S = 3 ∧
      (∀ w ∈ S, P.Iso w) ∧ (f c).V₁ ≤ S ∧ (f d).V₁ ≤ S := by
    by_cases hvL : v ∈ L₀
    · refine ⟨(f c).V₃, (f c).finrank₃, (f c).isTI, (f c).le₁₂.trans (f c).le₂₃, ?_⟩
      rw [hV1, Submodule.span_singleton_le_iff_mem]
      exact hL₀3 hvL
    · refine ⟨L₀ ⊔ K ∙ v, by rw [finrank_sup_span_of_not_mem hvL, hL₀2],
        P.isTI_sup L₀ (P.isTI_mono (f c).isTI hL₀3) v ((f d).isTI v hvd)
          (fun w hw => LinearMap.mem_ker.mp (hL₀ hw).2), hQL₀.trans le_sup_left, ?_⟩
      rw [hV1, Submodule.span_singleton_le_iff_mem]
      exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self v)
  obtain ⟨L₁, h11, h12, h13⟩ := exists_line_between (f c).finrank₁ hS3 hcS
  obtain ⟨L₂, h21, h22, h23⟩ := exists_line_between (f d).finrank₁ hS3 hdS
  obtain ⟨a, ha⟩ := hf.1.2 ⟨(f c).V₁, L₁, S, (f c).finrank₁, h13, hS3, h11, h12, hSTI⟩
  obtain ⟨b, hb⟩ := hf.1.2 ⟨(f d).V₁, L₂, S, (f d).finrank₁, h23, hS3, h21, h22, hSTI⟩
  have haR : a ∈ residue cs δ {l, π} c := (polar_mem_residue_lπ hf hpl hlπ hpπ).mpr (by rw [ha])
  have hbR : b ∈ residue cs δ {l, π} d := (polar_mem_residue_lπ hf hpl hlπ hpπ).mpr (by rw [hb])
  have hab : b ∈ residue cs δ {p, l} a :=
    (polar_mem_residue_pl hf hpl hlπ hpπ).mpr (by rw [ha, hb])
  have h1 := polar_nine_le hpl hlπ hpπ hδ hι hMpl hMlπ hMpπ hcd haR hbR
  have h2 := length_le_of_mem_parabolic_pair (cs := cs) (i := p) (j := l) (by omega)
    (mem_parabolic_of_mem_residue hδ (self_mem_residue _ a) hab)
  rw [length_longest_pair hlπ (by omega), hMlπ] at h1
  rw [hMpl] at h2
  omega

theorem polar_opposite_line {c d : C} (hcd : δ c d = longest cs Set.univ) {w : V}
    (hw : w ∈ (f c).V₂) (hperp : ∀ v ∈ (f d).V₂, P.pair v w = 0) : w = 0 := by
  by_contra hw0
  have hQ : finrank K (K ∙ w) = 1 := finrank_span_singleton hw0
  have hQc : K ∙ w ≤ (f c).V₂ := (Submodule.span_singleton_le_iff_mem _ _).mpr hw
  obtain ⟨a, ha⟩ := hf.1.2 ⟨K ∙ w, (f c).V₂, (f c).V₃, hQ, (f c).finrank₂, (f c).finrank₃, hQc,
    (f c).le₂₃, (f c).isTI⟩
  have haR : a ∈ residue cs δ {p, π} c := (polar_mem_residue_pπ hf hlπ hpπ).mpr (by rw [ha])
  have hJ : cs.length (longest cs {p, π}) = 2 := by
    rw [length_longest_pair hpπ (by omega), hMpπ]
  by_cases hwd : w ∈ (f d).V₂
  · have hQd : K ∙ w ≤ (f d).V₂ := (Submodule.span_singleton_le_iff_mem _ _).mpr hwd
    obtain ⟨b, hb⟩ := hf.1.2 ⟨K ∙ w, (f d).V₂, (f d).V₃, hQ, (f d).finrank₂, (f d).finrank₃,
      hQd, (f d).le₂₃, (f d).isTI⟩
    have hbR : b ∈ residue cs δ {p, π} d := (polar_mem_residue_pπ hf hlπ hpπ).mpr (by rw [hb])
    have hab : b ∈ residue cs δ {l, π} a :=
      (polar_mem_residue_lπ hf hpl hlπ hpπ).mpr (by rw [ha, hb])
    have h1 := polar_nine_le hpl hlπ hpπ hδ hι hMpl hMlπ hMpπ hcd haR hbR
    have h2 := length_le_of_mem_parabolic_pair (cs := cs) (i := l) (j := π) (by omega)
      (mem_parabolic_of_mem_residue hδ (self_mem_residue _ a) hab)
    rw [hJ] at h1
    rw [hMlπ] at h2
    omega
  · have hS3 : finrank K ↥((f d).V₂ ⊔ K ∙ w) = 3 := by
      rw [finrank_sup_span_of_not_mem hwd, (f d).finrank₂]
    have hSTI : ∀ v ∈ (f d).V₂ ⊔ K ∙ w, P.Iso v :=
      P.isTI_sup _ (P.isTI_mono (f d).isTI (f d).le₂₃) w ((f c).isTI w ((f c).le₂₃ hw))
        (fun u hu => (P.pair_eq_zero_comm _ _).mp (hperp u hu))
    have hw1 : w ∉ (f d).V₁ := fun h => hwd ((f d).le₁₂ h)
    have hL2 : finrank K ↥((f d).V₁ ⊔ K ∙ w) = 2 := by
      rw [finrank_sup_span_of_not_mem hw1, (f d).finrank₁]
    have hLS : (f d).V₁ ⊔ K ∙ w ≤ (f d).V₂ ⊔ K ∙ w :=
      sup_le ((f d).le₁₂.trans le_sup_left) le_sup_right
    obtain ⟨b, hb⟩ := hf.1.2 ⟨(f d).V₁, (f d).V₂, (f d).V₂ ⊔ K ∙ w, (f d).finrank₁,
      (f d).finrank₂, hS3, (f d).le₁₂, le_sup_left, hSTI⟩
    obtain ⟨b', hb'⟩ := hf.1.2 ⟨(f d).V₁, (f d).V₁ ⊔ K ∙ w, (f d).V₂ ⊔ K ∙ w, (f d).finrank₁,
      hL2, hS3, le_sup_left, hLS, hSTI⟩
    obtain ⟨a', ha'⟩ := hf.1.2 ⟨K ∙ w, (f d).V₁ ⊔ K ∙ w, (f d).V₂ ⊔ K ∙ w, hQ, hL2, hS3,
      le_sup_right, hLS, hSTI⟩
    have hbR : b ∈ residue cs δ {p, π} d := (polar_mem_residue_pπ hf hlπ hpπ).mpr (by rw [hb])
    have haa' : a' ∈ residue cs δ {l, π} a :=
      (polar_mem_residue_lπ hf hpl hlπ hpπ).mpr (by rw [ha, ha'])
    have hab : cs.length (δ a' b) ≤ 2 := by
      have hγ : (polarChamber P p l π).IsGallery (f a') [(p, f b'), (l, f b)] := by
        refine ⟨?_, ?_, trivial⟩
        · rw [polarChamber_adj_p, ha', hb']
          exact ⟨rfl, rfl⟩
        · rw [polarChamber_adj_l hpl, hb', hb]
          exact ⟨rfl, rfl⟩
      exact hf.length_le hδ hγ rfl
    have h1 := polar_nine_le hpl hlπ hpπ hδ hι hMpl hMlπ hMpπ hcd haR hbR
    have h2 := length_le_of_mem_parabolic_pair (cs := cs) (i := l) (j := π) (by omega)
      (mem_parabolic_of_mem_residue hδ (self_mem_residue _ a) haa')
    have h3 := length_dist_le_add hδ a a' b
    rw [hJ] at h1
    rw [hMlπ] at h2
    omega

end Opposite


end CFSG.Monster.B.Geometry

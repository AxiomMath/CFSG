module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.Y10R165Om3
public import CFSG.LocalAnalysis.GLTheoremA.CatA.S172CCentComp
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.RankThree.CentralCover CFSG.RankThree.Classical2
  CFSG.ClassicalGroups.Orthogonal

variable {K V R E : Type} [Field K] [AddCommGroup V] [Module K V]
  [AddCommGroup R] [Module K R] [AddCommGroup E] [Module K E] {m : ℕ}
  {Q : QuadraticForm K V} {QR : QuadraticForm K R} {QE : QuadraticForm K E}

@[expose] def coordAnchor (ψ : V ≃ₗ[K] R × (Fin m → E)) : Submodule K V :=
  LinearMap.range (ψ.symm.toLinearMap.comp (LinearMap.inl K R (Fin m → E)))

theorem mem_coordAnchor {ψ : V ≃ₗ[K] R × (Fin m → E)} {v : V} :
    v ∈ coordAnchor ψ ↔ ∃ r : R, ψ.symm (r, 0) = v := by
  constructor
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩
  · rintro ⟨r, rfl⟩
    exact ⟨r, rfl⟩

@[expose] def coordPlane (ψ : V ≃ₗ[K] R × (Fin m → E)) (i : Fin m) : Submodule K V :=
  LinearMap.range (ψ.symm.toLinearMap.comp
    ((LinearMap.inr K R (Fin m → E)).comp (LinearMap.single K (fun _ => E) i)))

theorem mem_coordPlane {ψ : V ≃ₗ[K] R × (Fin m → E)} {v : V} {i : Fin m} :
    v ∈ coordPlane ψ i ↔ ∃ e : E, ψ.symm (0, Pi.single i e) = v := by
  constructor
  · rintro ⟨e, rfl⟩
    exact ⟨e, rfl⟩
  · rintro ⟨e, rfl⟩
    exact ⟨e, rfl⟩

@[expose] def coordActive (ψ : V ≃ₗ[K] R × (Fin m → E)) : Submodule K V :=
  ⨆ i, coordPlane ψ i

@[expose] def coordSupport (ψ : V ≃ₗ[K] R × (Fin m → E)) (S : Finset (Fin m)) :
    Submodule K V :=
  coordAnchor ψ ⊔ S.sup (coordPlane ψ)

theorem coordSupport_univ (ψ : V ≃ₗ[K] R × (Fin m → E)) :
    coordSupport ψ Finset.univ = coordAnchor ψ ⊔ coordActive ψ := by
  rw [coordSupport, coordActive, Finset.sup_eq_iSup]
  simp

@[expose] noncomputable def coordPermHom (ψ : V ≃ₗ[K] R × (Fin m → E)) :
    Equiv.Perm (Fin m) →* (V ≃ₗ[K] V) :=
  (coordAut ψ).comp (permAut K E m)

theorem coordPermHom_apply (ψ : V ≃ₗ[K] R × (Fin m → E)) (σ : Equiv.Perm (Fin m)) :
    coordPermHom ψ σ = coordAut ψ (permAut K E m σ) := rfl

theorem coordPermHom_anchor (ψ : V ≃ₗ[K] R × (Fin m → E))
    (σ : Equiv.Perm (Fin m)) (r : R) :
    coordPermHom ψ σ (ψ.symm (r, 0)) = ψ.symm (r, 0) := by
  have h0 : permAut K E m σ (0 : Fin m → E) = 0 := by
    funext j
    rw [permAut_apply]
    rfl
  rw [coordPermHom_apply, coordAut_symm_apply, h0]

theorem coordPermHom_plane (ψ : V ≃ₗ[K] R × (Fin m → E))
    (σ : Equiv.Perm (Fin m)) (i : Fin m) (e : E) :
    coordPermHom ψ σ (ψ.symm (0, Pi.single i e)) =
      ψ.symm (0, Pi.single (σ i) e) := by
  rw [coordPermHom_apply, coordAut_symm_apply]
  congr 1
  apply Prod.ext
  · rfl
  · funext t
    change ((permAut K E m σ) (Pi.single i e : Fin m → E)) t =
      ((Pi.single (σ i) e : Fin m → E)) t
    rw [permAut_apply]
    exact congrFun (single_comp_perm_inv σ i e) t

theorem polar_coord (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i)) (v w : V) :
    polar Q v w = polar QR (ψ v).1 (ψ w).1 +
      ∑ i, polar QE ((ψ v).2 i) ((ψ w).2 i) := by
  rw [QuadraticMap.polar, QuadraticMap.polar, hψ (v + w), hψ v, hψ w]
  simp only [QuadraticMap.polar, map_add, Prod.fst_add, Prod.snd_add, Pi.add_apply,
    Finset.sum_add_distrib, Finset.sum_sub_distrib]
  abel

theorem polar_coordAnchor_plane (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    {w : V} (hw : w ∈ coordAnchor ψ) {i : Fin m} {u : V} (hu : u ∈ coordPlane ψ i) :
    polar Q w u = 0 := by
  obtain ⟨r, rfl⟩ := mem_coordAnchor.mp hw
  obtain ⟨e, rfl⟩ := mem_coordPlane.mp hu
  rw [polar_coord ψ hψ]
  simp [Pi.single_eq_same]

theorem polar_coordPlane_plane (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    {i j : Fin m} (hij : i ≠ j) {u : V} (hu : u ∈ coordPlane ψ i)
    {v : V} (hv : v ∈ coordPlane ψ j) : polar Q u v = 0 := by
  obtain ⟨x, rfl⟩ := mem_coordPlane.mp hu
  obtain ⟨y, rfl⟩ := mem_coordPlane.mp hv
  rw [polar_coord ψ hψ]
  simp only [LinearEquiv.apply_symm_apply]
  have hsum : (∑ t, polar QE ((Pi.single i x : Fin m → E) t)
      ((Pi.single j y : Fin m → E) t)) = 0 := by
    refine Finset.sum_eq_zero fun t _ => ?_
    by_cases hti : t = i
    · subst hti
      rw [Pi.single_eq_same, Pi.single_eq_of_ne hij, polar_zero_right]
    · by_cases htj : t = j
      · subst htj
        rw [Pi.single_eq_of_ne hij.symm, Pi.single_eq_same, polar_zero_left]
      · rw [Pi.single_eq_of_ne hti, Pi.single_eq_of_ne htj, polar_zero_left]
  rw [hsum]
  simp

theorem polar_coordAnchor_active (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    {w : V} (hw : w ∈ coordAnchor ψ) {s : V} (hs : s ∈ coordActive ψ) :
    polar Q w s = 0 := by
  refine Submodule.iSup_induction (fun i => coordPlane ψ i)
    (motive := fun s => polar Q w s = 0) hs ?_ ?_ ?_
  · intro i u hu
    exact polar_coordAnchor_plane ψ hψ hw hu
  · simp
  · intro a b ha hb
    rw [polar_add_right, ha, hb, add_zero]

theorem coordPlane_polarNondegOn (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (hQE : (polarBilin QE).Nondegenerate) (i : Fin m) :
    PolarNondegOn Q (coordPlane ψ i) := by
  intro u hu hup
  obtain ⟨x, rfl⟩ := mem_coordPlane.mp hu
  have hx : x = 0 := hQE.1 x fun y => by
    have hv : ψ.symm (0, Pi.single i y) ∈ coordPlane ψ i := mem_coordPlane.mpr ⟨y, rfl⟩
    have h := hup _ hv
    rw [polar_coord ψ hψ] at h
    simp only [LinearEquiv.apply_symm_apply] at h
    have hsum : (∑ t, polar QE ((Pi.single i x : Fin m → E) t)
      ((Pi.single i y : Fin m → E) t)) = polar QE x y := by
      rw [Finset.sum_eq_single i]
      · simp
      · intro t _ hti
        rw [Pi.single_eq_of_ne hti, Pi.single_eq_of_ne hti, polar_zero_left]
      · simp
    rw [hsum] at h
    simp only [polar_zero_right, zero_add] at h
    rw [polarBilin_apply_apply]
    exact h
  rw [hx]
  simp [mem_coordPlane]

theorem coordAnchor_sup_coordActive (ψ : V ≃ₗ[K] R × (Fin m → E)) :
    coordAnchor ψ ⊔ coordActive ψ = ⊤ := by
  rw [eq_top_iff]
  intro v _
  have hsum_pair : (∑ i, (0, Pi.single i ((ψ v).2 i)) : R × (Fin m → E)) =
      (0, (ψ v).2) := by
    apply Prod.ext
    · change (LinearMap.fst K R (Fin m → E))
          (∑ i, (0, Pi.single i ((ψ v).2 i))) =
        (LinearMap.fst K R (Fin m → E)) (0, (ψ v).2)
      rw [map_sum]
      simp
    · change (LinearMap.snd K R (Fin m → E))
          (∑ i, (0, Pi.single i ((ψ v).2 i))) =
        (LinearMap.snd K R (Fin m → E)) (0, (ψ v).2)
      rw [map_sum]
      simpa using Finset.univ_sum_single ((ψ v).2)
  have hcoord : ψ v = ((ψ v).1, 0) + ∑ i, (0, Pi.single i ((ψ v).2 i)) := by
    rw [hsum_pair]
    ext <;> simp
  have hdecomp : v = ψ.symm ((ψ v).1, 0) + ∑ i, ψ.symm (0, Pi.single i ((ψ v).2 i)) := by
    conv_lhs =>
      rw [← ψ.symm_apply_apply v]
      rw [hcoord]
    rw [map_add, map_sum]
  rw [hdecomp]
  refine (coordAnchor ψ ⊔ coordActive ψ).add_mem ?_ ?_
  · exact Submodule.mem_sup_left (mem_coordAnchor.mpr ⟨(ψ v).1, rfl⟩)
  · refine Submodule.mem_sup_right ?_
    refine (coordActive ψ).sum_mem ?_
    intro i _
    exact Submodule.mem_iSup_of_mem i (mem_coordPlane.mpr ⟨(ψ v).2 i, rfl⟩)

theorem coordAnchor_nondegenerate (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (hQ : (polarBilin Q).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate) :
    (polarBilin (Q.comp (coordAnchor ψ).subtype)).Nondegenerate := by
  have hspan : coordAnchor ψ ⊔ coordActive ψ = ⊤ := coordAnchor_sup_coordActive ψ
  have horth : ∀ w ∈ coordAnchor ψ, ∀ s ∈ coordActive ψ, polar Q w s = 0 :=
    fun w hw s hs => polar_coordAnchor_active ψ hψ hw hs
  constructor
  · intro w hw
    apply Subtype.ext
    apply eq_zero_of_polar_eq_zero hQ
    intro y
    have hy : y ∈ coordAnchor ψ ⊔ coordActive ψ := by rw [hspan]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_right, show polar Q (w : V) a = 0 from by
      have hwa := hw ⟨a, ha⟩
      rw [polarBilin_apply_apply] at hwa
      rwa [polar_comp_subtype_eq] at hwa, horth w w.2 b hb, add_zero]
  · intro w hw
    apply Subtype.ext
    apply eq_zero_of_polar_eq_zero hQ
    intro y
    have hy : y ∈ coordAnchor ψ ⊔ coordActive ψ := by rw [hspan]; trivial
    obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hy
    rw [polar_add_right, show polar Q (w : V) a = 0 from by
      rw [polar_comm]
      have hwa := hw ⟨a, ha⟩
      rw [polarBilin_apply_apply] at hwa
      rwa [polar_comp_subtype_eq] at hwa, horth w w.2 b hb, add_zero]

theorem coordSupport_empty (ψ : V ≃ₗ[K] R × (Fin m → E)) :
    coordSupport ψ ∅ = coordAnchor ψ := by
  simp [coordSupport]

theorem coordSupport_insert (ψ : V ≃ₗ[K] R × (Fin m → E))
    {i : Fin m} {S : Finset (Fin m)} (hi : i ∉ S) :
    coordSupport ψ (insert i S) = coordSupport ψ S ⊔ coordPlane ψ i := by
  rw [coordSupport, coordSupport, Finset.sup_insert]
  simp only [sup_assoc, sup_comm, sup_left_comm]

theorem polar_coordSupport_plane (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i)) :
    ∀ (S : Finset (Fin m)) {i : Fin m}, i ∉ S → ∀ {s : V}, s ∈ coordSupport ψ S →
      ∀ {u : V}, u ∈ coordPlane ψ i → polar Q s u = 0 := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      intro i _ s hs u hu
      rw [coordSupport_empty] at hs
      exact polar_coordAnchor_plane ψ hψ hs hu
  | insert j S hj ih =>
      intro i hi s hs u hu
      rw [coordSupport_insert ψ hj] at hs
      obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hs
      have h1 : polar Q a u = 0 :=
        ih (i := i) (fun hji => hi (Finset.mem_insert_of_mem hji)) ha hu
      have h2 : polar Q b u = 0 :=
        polar_coordPlane_plane ψ hψ (by
          intro hji
          apply hi
          rw [← hji]
          exact Finset.mem_insert_self j S) hb hu
      rw [polar_add_left, h1, h2, add_zero]

theorem coordSupport_polarNondegOn [FiniteDimensional K V]
    (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (hQ : (polarBilin Q).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate) :
    ∀ S : Finset (Fin m), PolarNondegOn Q (coordSupport ψ S) := by
  intro S
  induction S using Finset.induction_on with
  | empty =>
      rw [coordSupport_empty]
      exact polarNondegOn_of_nondegenerate (coordAnchor_nondegenerate ψ hψ hQ hQE)
  | insert i S hi ih =>
      rw [coordSupport_insert ψ hi]
      exact CFSG.LieType.SeitzGeneration.OrthBlk.polarNondegOn_sup
        (K := K) (V := V) (Q := Q) ih (coordPlane_polarNondegOn ψ hψ hQE i)
        (fun s hs u hu => show polar Q s u = 0 from
          polar_coordSupport_plane ψ hψ S hi hs hu)

theorem coordSupport_nondegenerate [FiniteDimensional K V]
    (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (hQ : (polarBilin Q).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate)
    (S : Finset (Fin m)) :
    (polarBilin (Q.comp (coordSupport ψ S).subtype)).Nondegenerate := by
  exact CFSG.LieType.SeitzGeneration.OrthBlk.nondegenerate_of_polarNondegOn
    (K := K) (V := V) (Q := Q) (U := coordSupport ψ S)
    (coordSupport_polarNondegOn ψ hψ hQ hQE S)

theorem coordPermHom_mem_orthDerived [Finite K] [FiniteDimensional K V] [CharP K 2]
    [Nontrivial E] (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hQ : (polarBilin Q).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate)
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (h8 : 8 ≤ finrank K V) :
    ∀ σ : Equiv.Perm (Fin m), coordPermHom ψ σ ∈ orthDerived Q := by
  have hcard : Nat.card (Abelianization (TauCeti.QuadraticMap.orthogonalGroup Q)) ≤ 2 := by
    obtain ⟨T, hT3, hT0⟩ :=
      CFSG.LocalAnalysis.GLTheoremA.Y10F.OmEngine.exists_threeSingular_of_eight_le
        (F := K) (V := V) (Q := Q) hQ h8
    have hT : ∃ T : Submodule K V, finrank K T = 3 ∧ ∀ x ∈ T, Q x = 0 :=
      ⟨T, hT3, hT0⟩
    obtain ⟨hΩE, hgen⟩ := CFSG.RankThree.Classical.orthDerived_eq_and_le_closure hQ hT
    obtain ⟨P, r, hr, hP, -, -⟩ :=
      CFSG.RankThree.Classical.exists_hypPair_tail_decomposition hQ hT
    have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
    exact (CFSG.LocalAnalysis.ComponentInitial.char_two_orthogonal_abelianization_bound h2 hQ
      (hP 0 1 (by omega) (by omega) (by omega)) hΩE.ge hgen).2
  intro σ
  refine σ.swap_induction_on ?_ ?_
  · rw [map_one]
    exact one_mem _
  · intro τ i j hij hτ
    rw [map_mul]
    exact mul_mem (coordAut_swap_mem_orthDerived hQ hQE hψ hcard hij) hτ

@[expose] noncomputable def codRestrictedρ [Finite K] [FiniteDimensional K V] [CharP K 2]
    [Nontrivial E] (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hQ : (polarBilin Q).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate)
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (h8 : 8 ≤ finrank K V) : Equiv.Perm (Fin m) →* orthDerived Q :=
  (coordPermHom ψ).codRestrict (orthDerived Q) fun σ =>
    coordPermHom_mem_orthDerived ψ hQ hQE hψ h8 σ

@[simp] theorem coe_codRestrictedρ_apply [Finite K] [FiniteDimensional K V] [CharP K 2]
    [Nontrivial E] (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hQ : (polarBilin Q).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate)
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (h8 : 8 ≤ finrank K V) (σ : Equiv.Perm (Fin m)) :
    ((codRestrictedρ ψ hQ hQE hψ h8 σ : orthDerived Q) : V ≃ₗ[K] V) =
      coordPermHom ψ σ := rfl

theorem map_coordAnchor (ψ : V ≃ₗ[K] R × (Fin m → E)) (σ : Equiv.Perm (Fin m)) :
    (coordAnchor ψ).map (coordPermHom ψ σ).toLinearMap = coordAnchor ψ := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨r, rfl⟩ := mem_coordAnchor.mp hv
    change coordPermHom ψ σ (ψ.symm (r, 0)) ∈ coordAnchor ψ
    rw [coordPermHom_anchor]
    exact mem_coordAnchor.mpr ⟨r, rfl⟩
  · intro v hv
    obtain ⟨r, rfl⟩ := mem_coordAnchor.mp hv
    refine ⟨ψ.symm (r, 0), mem_coordAnchor.mpr ⟨r, rfl⟩, ?_⟩
    change coordPermHom ψ σ (ψ.symm (r, 0)) = ψ.symm (r, 0)
    rw [coordPermHom_anchor]

theorem map_coordPlane (ψ : V ≃ₗ[K] R × (Fin m → E)) (σ : Equiv.Perm (Fin m))
    (i : Fin m) :
    (coordPlane ψ i).map (coordPermHom ψ σ).toLinearMap = coordPlane ψ (σ i) := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨e, rfl⟩ := mem_coordPlane.mp hv
    change coordPermHom ψ σ (ψ.symm (0, Pi.single i e)) ∈ coordPlane ψ (σ i)
    rw [coordPermHom_plane]
    exact mem_coordPlane.mpr ⟨e, rfl⟩
  · intro v hv
    obtain ⟨e, rfl⟩ := mem_coordPlane.mp hv
    refine ⟨ψ.symm (0, Pi.single i e), mem_coordPlane.mpr ⟨e, rfl⟩, ?_⟩
    change coordPermHom ψ σ (ψ.symm (0, Pi.single i e)) =
      ψ.symm (0, Pi.single (σ i) e)
    rw [coordPermHom_plane]

theorem map_coordSupport (ψ : V ≃ₗ[K] R × (Fin m → E)) (σ : Equiv.Perm (Fin m))
    (S : Finset (Fin m)) :
    (coordSupport ψ S).map (coordPermHom ψ σ).toLinearMap =
      coordSupport ψ (S.image σ) := by
  rw [coordSupport, coordSupport, Submodule.map_sup, map_coordAnchor, Finset.sup_image]
  rw [Finset.sup_eq_iSup, Finset.sup_eq_iSup, Submodule.map_iSup]
  simp_rw [Submodule.map_iSup, map_coordPlane]
  rfl

theorem map_supportedDerived_coordSupport
    (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (σ : Equiv.Perm (Fin m)) (S : Finset (Fin m)) :
    (supportedDerived Q (coordSupport ψ S)).map
        (MulAut.conj (coordPermHom ψ σ)).toMonoidHom =
      supportedDerived Q (coordSupport ψ (S.image σ)) :=
  map_supportedDerived_conj_of_map_eq (coordPermHom ψ σ)
    (coordAut_permAut_mem hψ σ) (map_coordSupport ψ σ S)

theorem map_coordSupport_subgroup [Finite K] [FiniteDimensional K V] [CharP K 2]
    [Nontrivial E] (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hQ : (polarBilin Q).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate)
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (h8 : 8 ≤ finrank K V) (σ : Equiv.Perm (Fin m)) (S : Finset (Fin m)) :
    ((supportedDerived Q (coordSupport ψ S)).subgroupOf (orthDerived Q)).map
        (MulAut.conj (codRestrictedρ ψ hQ hQE hψ h8 σ)).toMonoidHom =
      (supportedDerived Q (coordSupport ψ (S.image σ))).subgroupOf (orthDerived Q) := by
  let H := supportedDerived Q (coordSupport ψ S)
  let H' := supportedDerived Q (coordSupport ψ (S.image σ))
  have hH : H ≤ orthDerived Q :=
    supportedDerived_le_orthDerived_of_regular (coordSupport_nondegenerate ψ hψ hQ hQE S)
  have hH' : H' ≤ orthDerived Q :=
    supportedDerived_le_orthDerived_of_regular
      (coordSupport_nondegenerate ψ hψ hQ hQE (S.image σ))
  have hHK : H.map (MulAut.conj (coordPermHom ψ σ)).toMonoidHom = H' :=
    map_supportedDerived_coordSupport ψ hψ σ S
  have hcoe : ∀ x : orthDerived Q,
      (((MulAut.conj (codRestrictedρ ψ hQ hQE hψ h8 σ)) x : orthDerived Q) : V ≃ₗ[K] V) =
        MulAut.conj (coordPermHom ψ σ) (x : V ≃ₗ[K] V) := by
    intro x
    simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv,
      coe_codRestrictedρ_apply]
  apply le_antisymm
  · rintro x ⟨y, hy, rfl⟩
    change (y : V ≃ₗ[K] V) ∈ H at hy
    change ((MulAut.conj (codRestrictedρ ψ hQ hQE hψ h8 σ)) y : V ≃ₗ[K] V) ∈ H'
    have hmem := Subgroup.mem_map_of_mem (MulAut.conj (coordPermHom ψ σ)).toMonoidHom hy
    rw [hHK] at hmem
    simpa [hcoe y] using hmem
  · intro x hx
    change (x : V ≃ₗ[K] V) ∈ H' at hx
    let y : V ≃ₗ[K] V := MulAut.conj (coordPermHom ψ σ⁻¹) (x : V ≃ₗ[K] V)
    have hyH : y ∈ H := by
      have hback : H'.map (MulAut.conj (coordPermHom ψ σ⁻¹)).toMonoidHom = H := by
        have h := map_supportedDerived_coordSupport ψ hψ σ⁻¹ (S.image σ)
        simpa [H, H', Finset.image_image] using h
      exact hback ▸ Subgroup.mem_map_of_mem _ hx
    have hyK : y ∈ orthDerived Q := hH hyH
    let y' : orthDerived Q := ⟨y, hyK⟩
    have hy' : y' ∈ H.subgroupOf (orthDerived Q) :=
      Subgroup.mem_subgroupOf.mpr hyH
    refine Subgroup.mem_map.mpr ⟨y', hy', ?_⟩
    apply Subtype.ext
    change (((MulAut.conj (codRestrictedρ ψ hQ hQE hψ h8 σ)) y' : orthDerived Q) :
      V ≃ₗ[K] V) = (x : V ≃ₗ[K] V)
    rw [hcoe y']
    change MulAut.conj (coordPermHom ψ σ)
      (MulAut.conj (coordPermHom ψ σ⁻¹) (x : V ≃ₗ[K] V)) = (x : V ≃ₗ[K] V)
    have hinv : coordPermHom ψ σ⁻¹ = (coordPermHom ψ σ)⁻¹ := map_inv (coordPermHom ψ) σ
    rw [hinv]
    simp [MulAut.conj_apply, mul_assoc]

theorem codRestrictedρ_centralizes_pair [Finite K] [FiniteDimensional K V] [CharP K 2]
    [Nontrivial E] (ψ : V ≃ₗ[K] R × (Fin m → E))
    (hQ : (polarBilin Q).Nondegenerate) (hQE : (polarBilin QE).Nondegenerate)
    (hψ : ∀ v : V, Q v = QR (ψ v).1 + ∑ i, QE ((ψ v).2 i))
    (h8 : 8 ≤ finrank K V) {i j : Fin m} (hij : i ≠ j)
    (σ : Equiv.Perm (Fin m)) (hi : σ i = i) (hj : σ j = j) :
    ∀ x ∈ (supportedDerived Q (coordSupport ψ {i,j})).subgroupOf (orthDerived Q),
      codRestrictedρ ψ hQ hQE hψ h8 σ * x *
        (codRestrictedρ ψ hQ hQE hψ h8 σ)⁻¹ = x := by
  have hpair : coordSupport ψ {i,j} =
      coordAnchor ψ ⊔ (coordPlane ψ i ⊔ coordPlane ψ j) := by
    rw [coordSupport, Finset.sup_insert, Finset.sup_singleton]
  have hfixW : ∀ w ∈ coordAnchor ψ, coordPermHom ψ σ w = w := by
    intro w hw
    obtain ⟨r, rfl⟩ := mem_coordAnchor.mp hw
    exact coordPermHom_anchor ψ σ r
  have hfixUi : ∀ u ∈ coordPlane ψ i, coordPermHom ψ σ u = u := by
    intro u hu
    obtain ⟨e, rfl⟩ := mem_coordPlane.mp hu
    rw [coordPermHom_plane, hi]
  have hfixUj : ∀ u ∈ coordPlane ψ j, coordPermHom ψ σ u = u := by
    intro u hu
    obtain ⟨e, rfl⟩ := mem_coordPlane.mp hu
    rw [coordPermHom_plane, hj]
  have hfixA : ∀ x ∈ coordSupport ψ {i,j}, coordPermHom ψ σ x = x := by
    intro x hx
    rw [hpair] at hx
    obtain ⟨w, hw, y, hy, rfl⟩ := Submodule.mem_sup.mp hx
    obtain ⟨u, hu, v, hv, rfl⟩ := Submodule.mem_sup.mp hy
    rw [map_add, map_add, hfixW w hw, hfixUi u hu, hfixUj v hv]
  have hA : (polarBilin (Q.comp (coordSupport ψ {i,j}).subtype)).Nondegenerate :=
    coordSupport_nondegenerate ψ hψ hQ hQE {i,j}
  intro x hx
  have hxH : (x : V ≃ₗ[K] V) ∈ supportedDerived Q (coordSupport ψ {i,j}) :=
    Subgroup.mem_subgroupOf.mp hx
  have hcomm := CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.commute_of_apply_eq
    (Q := Q) (U := coordSupport ψ {i,j}) hA (coordAut_permAut_mem hψ σ) hfixA
    (fun v hv => show (x : V ≃ₗ[K] V) v ∈ coordSupport ψ {i,j} from
      supportedDerived_apply_mem hxH hv)
    (fun v hv => show (x : V ≃ₗ[K] V) v = v from by
      refine supportedDerived_apply_perp hxH ?_
      rw [mem_suppPerp]
      intro w hw
      exact (CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.mem_polarPerp_iff.mp hv) w hw)
  apply Subtype.ext
  change (((codRestrictedρ ψ hQ hQE hψ h8 σ * x *
      (codRestrictedρ ψ hQ hQE hψ h8 σ)⁻¹ : orthDerived Q) : V ≃ₗ[K] V)) =
    (x : V ≃ₗ[K] V)
  simp only [Subgroup.coe_mul, Subgroup.coe_inv, coe_codRestrictedρ_apply]
  have hcoord : (coordPermHom ψ) σ = coordAut ψ (permAut K E m σ) := rfl
  rw [hcoord, hcomm, mul_assoc, mul_inv_cancel, mul_one]

variable {V2 R2 E2 : Type} [AddCommGroup V2] [Module K V2]
  [AddCommGroup R2] [Module K R2] [AddCommGroup E2] [Module K E2]

@[expose] noncomputable def coordChange (psi1 : V ≃ₗ[K] R × (Fin m → E))
    (psi2 : V2 ≃ₗ[K] R2 × (Fin m → E2))
    (epsR : R ≃ₗ[K] R2) (epsE : E ≃ₗ[K] E2) : V ≃ₗ[K] V2 :=
  psi1.trans
    ((epsR.prodCongr (LinearEquiv.piCongrRight (fun _ : Fin m => epsE))).trans psi2.symm)

theorem psi2_coordChange (psi1 : V ≃ₗ[K] R × (Fin m → E))
    (psi2 : V2 ≃ₗ[K] R2 × (Fin m → E2))
    (epsR : R ≃ₗ[K] R2) (epsE : E ≃ₗ[K] E2) (v : V) :
    psi2 (coordChange psi1 psi2 epsR epsE v) =
      (epsR (psi1 v).1, fun i => epsE ((psi1 v).2 i)) := by
  simp [coordChange, LinearEquiv.prodCongr_apply, LinearEquiv.piCongrRight_apply]
  rfl

theorem coordChange_anchor (psi1 : V ≃ₗ[K] R × (Fin m → E))
    (psi2 : V2 ≃ₗ[K] R2 × (Fin m → E2))
    (epsR : R ≃ₗ[K] R2) (epsE : E ≃ₗ[K] E2) (r : R) :
    coordChange psi1 psi2 epsR epsE (psi1.symm (r, 0)) =
      psi2.symm (epsR r, 0) := by
  apply psi2.injective
  rw [psi2_coordChange]
  simp
  rfl

theorem coordChange_plane (psi1 : V ≃ₗ[K] R × (Fin m → E))
    (psi2 : V2 ≃ₗ[K] R2 × (Fin m → E2))
    (epsR : R ≃ₗ[K] R2) (epsE : E ≃ₗ[K] E2) (i : Fin m) (e : E) :
    coordChange psi1 psi2 epsR epsE (psi1.symm (0, Pi.single i e)) =
      psi2.symm (0, Pi.single i (epsE e)) := by
  apply psi2.injective
  rw [psi2_coordChange]
  simp only [LinearEquiv.apply_symm_apply]
  apply Prod.ext
  · simp
  · funext j
    change epsE ((Pi.single i e : Fin m → E) j) =
      (Pi.single i (epsE e) : Fin m → E2) j
    by_cases h : j = i
    · subst h
      simp
    · rw [Pi.single_eq_of_ne h, Pi.single_eq_of_ne h]
      simp

theorem map_coordAnchor_coordChange (psi1 : V ≃ₗ[K] R × (Fin m → E))
    (psi2 : V2 ≃ₗ[K] R2 × (Fin m → E2))
    (epsR : R ≃ₗ[K] R2) (epsE : E ≃ₗ[K] E2) :
    (coordAnchor psi1).map (coordChange psi1 psi2 epsR epsE).toLinearMap =
      coordAnchor psi2 := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨r, rfl⟩ := mem_coordAnchor.mp hv
    exact mem_coordAnchor.mpr ⟨epsR r, (coordChange_anchor psi1 psi2 epsR epsE r).symm⟩
  · intro v hv
    obtain ⟨r, rfl⟩ := mem_coordAnchor.mp hv
    refine ⟨psi1.symm (epsR.symm r, 0), mem_coordAnchor.mpr ⟨epsR.symm r, rfl⟩, ?_⟩
    simpa using coordChange_anchor psi1 psi2 epsR epsE (epsR.symm r)

theorem map_coordPlane_coordChange (psi1 : V ≃ₗ[K] R × (Fin m → E))
    (psi2 : V2 ≃ₗ[K] R2 × (Fin m → E2))
    (epsR : R ≃ₗ[K] R2) (epsE : E ≃ₗ[K] E2) (i : Fin m) :
    (coordPlane psi1 i).map (coordChange psi1 psi2 epsR epsE).toLinearMap =
      coordPlane psi2 i := by
  refine le_antisymm ?_ ?_
  · rintro _ ⟨v, hv, rfl⟩
    obtain ⟨e, rfl⟩ := mem_coordPlane.mp hv
    exact mem_coordPlane.mpr ⟨epsE e, (coordChange_plane psi1 psi2 epsR epsE i e).symm⟩
  · intro v hv
    obtain ⟨e, rfl⟩ := mem_coordPlane.mp hv
    refine ⟨psi1.symm (0, Pi.single i (epsE.symm e)),
      mem_coordPlane.mpr ⟨epsE.symm e, rfl⟩, ?_⟩
    simpa using coordChange_plane psi1 psi2 epsR epsE i (epsE.symm e)

theorem map_coordSupport_coordChange (psi1 : V ≃ₗ[K] R × (Fin m → E))
    (psi2 : V2 ≃ₗ[K] R2 × (Fin m → E2))
    (epsR : R ≃ₗ[K] R2) (epsE : E ≃ₗ[K] E2) (S : Finset (Fin m)) :
    (coordSupport psi1 S).map (coordChange psi1 psi2 epsR epsE).toLinearMap =
      coordSupport psi2 S := by
  rw [coordSupport, coordSupport, Submodule.map_sup, map_coordAnchor_coordChange,
    Finset.sup_eq_iSup, Finset.sup_eq_iSup, Submodule.map_iSup]
  simp_rw [Submodule.map_iSup, map_coordPlane_coordChange]

section Isometry

variable {Q1 : QuadraticForm K V} {QR1 : QuadraticForm K R} {QE1 : QuadraticForm K E}
  {Q2 : QuadraticForm K V2} {QR2 : QuadraticForm K R2} {QE2 : QuadraticForm K E2}

@[expose] noncomputable def coordChangeIsometry
    (psi1 : V ≃ₗ[K] R × (Fin m → E)) (psi2 : V2 ≃ₗ[K] R2 × (Fin m → E2))
    (epsR : QR1.IsometryEquiv QR2) (epsE : QE1.IsometryEquiv QE2)
    (hψ1 : ∀ v : V, Q1 v = QR1 (psi1 v).1 + ∑ i, QE1 ((psi1 v).2 i))
    (hψ2 : ∀ v : V2, Q2 v = QR2 (psi2 v).1 + ∑ i, QE2 ((psi2 v).2 i)) :
    Q1.IsometryEquiv Q2 where
  toLinearEquiv := coordChange psi1 psi2 epsR.toLinearEquiv epsE.toLinearEquiv
  map_app' v := by
    change Q2 (coordChange psi1 psi2 epsR.toLinearEquiv epsE.toLinearEquiv v) = Q1 v
    rw [hψ2]
    change QR2 (psi2 (coordChange psi1 psi2 epsR.toLinearEquiv epsE.toLinearEquiv v)).1 +
        ∑ i, QE2 ((psi2 (coordChange psi1 psi2 epsR.toLinearEquiv epsE.toLinearEquiv v)).2 i) =
      Q1 v
    rw [psi2_coordChange]
    have hR : QR2 (epsR.toLinearEquiv (psi1 v).1) = QR1 (psi1 v).1 :=
      epsR.map_app (psi1 v).1
    rw [hR]
    have hsum : (∑ i, QE2 (epsE.toLinearEquiv ((psi1 v).2 i))) =
        ∑ i, QE1 ((psi1 v).2 i) := by
      refine Finset.sum_congr rfl fun i _ => ?_
      exact epsE.map_app ((psi1 v).2 i)
    rw [hsum, ← hψ1]

@[simp] theorem coordChangeIsometry_toLinearEquiv
    (psi1 : V ≃ₗ[K] R × (Fin m → E)) (psi2 : V2 ≃ₗ[K] R2 × (Fin m → E2))
    (epsR : QR1.IsometryEquiv QR2) (epsE : QE1.IsometryEquiv QE2)
    (hψ1 : ∀ v : V, Q1 v = QR1 (psi1 v).1 + ∑ i, QE1 ((psi1 v).2 i))
    (hψ2 : ∀ v : V2, Q2 v = QR2 (psi2 v).1 + ∑ i, QE2 ((psi2 v).2 i)) :
    (coordChangeIsometry psi1 psi2 epsR epsE hψ1 hψ2).toLinearEquiv =
      coordChange psi1 psi2 epsR.toLinearEquiv epsE.toLinearEquiv := rfl

end Isometry

end CFSG.RankThree.PartOne.KCOrthogonal

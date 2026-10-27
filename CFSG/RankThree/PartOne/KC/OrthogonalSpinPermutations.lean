module

public import CFSG.RankThree.PartOne.KC.OrthogonalAnchoredSpin
public import CFSG.RankThree.PartOne.KC.OrthogonalPlanePermutations
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.FamilyEvenOrthogonal
public import CFSG.Mathlib.Perm.FixingSubgroupSwap

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module QuadraticMap CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.AGLEmbeddingD2.SquareSpinMinus

variable {n : ℕ} {F : Type} [Field F] {b c : F}

@[expose] noncomputable def minusPlaneCoordinates (n : ℕ) :
    Vm n F ≃ₗ[F] (Fin 2 → F) × (Fin (n - 1) → F × F) :=
  (CFSG.QuasithinUnique.Setup.Family.minusEquiv (K := F) (n - 1)).trans
    (LinearEquiv.prodComm F _ _)

theorem minusPlaneCoordinates_apply (v : Vm n F) :
    minusPlaneCoordinates (n := n) (F := F) v =
      (fun t => v (.inr (.inr t)), fun i => (v (.inl i), v (.inr (.inl i)))) :=
  rfl

theorem minusPlaneCoordinates_planeVec (p : Fin 2 → F) :
    minusPlaneCoordinates (n := n) (F := F) (planeVec n p) = (p, 0) := by
  rw [minusPlaneCoordinates_apply]
  apply Prod.ext
  · funext t
    simp [planeVec]
  · funext i
    simp [planeVec]

theorem minusPlaneCoordinates_eVec (i : Fin (n - 1)) :
    minusPlaneCoordinates (n := n) (F := F) (eVec n i) = (0, Pi.single i (1, 0)) := by
  rw [minusPlaneCoordinates_apply]
  apply Prod.ext
  · funext t
    simp [eVec]
  · funext j
    simp [eVec, Pi.single_apply]
    split_ifs <;> rfl

theorem minusPlaneCoordinates_fVec (i : Fin (n - 1)) :
    minusPlaneCoordinates (n := n) (F := F) (fVec n i) = (0, Pi.single i (0, 1)) := by
  rw [minusPlaneCoordinates_apply]
  apply Prod.ext
  · funext t
    simp [fVec]
  · funext j
    simp [fVec, Pi.single_apply]
    split_ifs <;> rfl

theorem minusPlaneCoordinates_minusVec_true (i : Fin (n - 1)) :
    minusPlaneCoordinates (n := n) (F := F) (minusVec n i true) = (0, Pi.single i (1, 0)) := by
  simpa only [minusVec_true] using minusPlaneCoordinates_eVec (n := n) (F := F) i

theorem minusPlaneCoordinates_minusVec_false (i : Fin (n - 1)) :
    minusPlaneCoordinates (n := n) (F := F) (minusVec n i false) = (0, Pi.single i (0, 1)) := by
  simpa only [minusVec_false] using minusPlaneCoordinates_fVec (n := n) (F := F) i

theorem minusPlaneCoordinates_symm_planeVec (p : Fin 2 → F) :
    (minusPlaneCoordinates (n := n) (F := F)).symm (p, 0) = planeVec n p := by
  rw [← minusPlaneCoordinates_planeVec (n := n) (F := F) (p := p),
    LinearEquiv.symm_apply_apply]

theorem minusPlaneCoordinates_symm_single_true (i : Fin (n - 1)) :
    (minusPlaneCoordinates (n := n) (F := F)).symm (0, Pi.single i (1, 0)) =
      minusVec n i true := by
  rw [← minusPlaneCoordinates_minusVec_true (n := n) (F := F) i,
    LinearEquiv.symm_apply_apply]

theorem minusPlaneCoordinates_symm_single_false (i : Fin (n - 1)) :
    (minusPlaneCoordinates (n := n) (F := F)).symm (0, Pi.single i (0, 1)) =
      minusVec n i false := by
  rw [← minusPlaneCoordinates_minusVec_false (n := n) (F := F) i,
    LinearEquiv.symm_apply_apply]

theorem planeVec_single (t : Fin 2) :
    planeVec n (Pi.single t 1) = (Pi.single (.inr (.inr t)) 1 : Vm n F) := by
  funext a
  rcases a with k | k | t' <;> simp [planeVec, Pi.single_apply]

theorem minusPlaneCoordinates_symm_single (i : Fin (n - 1)) (a b : F) :
    (minusPlaneCoordinates (n := n) (F := F)).symm (0, Pi.single i (a, b)) =
      a • minusVec n i true + b • minusVec n i false := by
  apply (minusPlaneCoordinates (n := n) (F := F)).injective
  rw [LinearEquiv.apply_symm_apply]
  simp only [map_add, map_smul, minusPlaneCoordinates_minusVec_true,
    minusPlaneCoordinates_minusVec_false]
  apply Prod.ext
  · simp
  · funext j
    by_cases h : j = i
    · subst h
      simp
    · simp [Pi.single_eq_of_ne h]

theorem coordAnchor_minusPlaneCoordinates :
    coordAnchor (minusPlaneCoordinates (n := n) (F := F)) = anchoredSupport F n ∅ := by
  ext v
  constructor
  · rw [mem_coordAnchor]
    rintro ⟨r, rfl⟩
    change ∀ a, a ∉ (activeCoords n ∅ : Set (Idx n)) →
      ((minusPlaneCoordinates (n := n) (F := F)).symm (r, 0) : Vm n F) a = 0
    intro a ha
    have ha' : a ∉ planeCoords n := by
      simpa [activeCoords, eCoords, fCoords] using ha
    rw [minusPlaneCoordinates_symm_planeVec]
    exact not_mem_planeCoords (F := F) ha' r
  · intro hv
    change ∀ a, a ∉ (activeCoords n ∅ : Set (Idx n)) → v a = 0 at hv
    rw [mem_coordAnchor]
    refine ⟨fun t => v (.inr (.inr t)), ?_⟩
    rw [minusPlaneCoordinates_symm_planeVec]
    funext a
    rcases a with k | k | t
    · have h0 : v (.inl k) = 0 :=
        hv _ (by simp [activeCoords, eCoords, fCoords, planeCoords])
      simp [planeVec, h0]
    · have h0 : v (.inr (.inl k)) = 0 :=
        hv _ (by simp [activeCoords, eCoords, fCoords, planeCoords])
      simp [planeVec, h0]
    · simp [planeVec]

theorem coordPlane_minusPlaneCoordinates (i : Fin (n - 1)) :
    coordPlane (minusPlaneCoordinates (n := n) (F := F)) i =
      supp F ({Sum.inl i, Sum.inr (Sum.inl i)} : Set (Idx n)) := by
  ext v
  constructor
  · rw [mem_coordPlane]
    rintro ⟨e, rfl⟩
    rw [minusPlaneCoordinates_symm_single]
    refine (supp F ({Sum.inl i, Sum.inr (Sum.inl i)} : Set (Idx n))).add_mem ?_ ?_
    · refine (supp F ({Sum.inl i, Sum.inr (Sum.inl i)} : Set (Idx n))).smul_mem e.1 ?_
      rw [minusVec_true, eVec]
      exact single_mem_supp (F := F) (by simp) 1
    · refine (supp F ({Sum.inl i, Sum.inr (Sum.inl i)} : Set (Idx n))).smul_mem e.2 ?_
      rw [minusVec_false, fVec]
      exact single_mem_supp (F := F) (by simp) 1
  · intro hv
    rw [mem_coordPlane]
    refine ⟨(v (Sum.inl i), v (Sum.inr (Sum.inl i))), ?_⟩
    rw [minusPlaneCoordinates_symm_single]
    funext a
    rcases a with k | k | t
    · by_cases h : k = i
      · subst h
        simp [minusVec, eVec, fVec]
      · have hv0 : v (Sum.inl k) = 0 := hv _ (by simp [h])
        simp [minusVec, eVec, fVec, Pi.single_apply, h, hv0]
    · by_cases h : k = i
      · subst h
        simp [minusVec, eVec, fVec]
      · have hv0 : v (Sum.inr (Sum.inl k)) = 0 := hv _ (by simp [h])
        simp [minusVec, eVec, fVec, Pi.single_apply, h, hv0]
    · have hv0 : v (Sum.inr (Sum.inr t)) = 0 := hv _ (by simp)
      simp [minusVec, eVec, fVec, hv0]

theorem mem_activeCoords_insert {i : Fin (n - 1)} {S : Finset (Fin (n - 1))} {a : Idx n} :
    a ∈ activeCoords n (insert i S) ↔
      a ∈ activeCoords n S ∨ a = Sum.inl i ∨ a = Sum.inr (Sum.inl i) := by
  rcases a with k | k | t <;>
    simp [activeCoords, eCoords, fCoords, planeCoords, Finset.mem_insert,
      inl_mem_eCoords, inr_inl_mem_fCoords, inl_not_mem_fCoords,
      inr_inl_not_mem_eCoords, inr_inr_mem_planeCoords] <;>
    tauto

theorem anchoredSupport_insert (i : Fin (n - 1)) (S : Finset (Fin (n - 1))) :
    anchoredSupport F n (insert i S) =
      anchoredSupport F n S ⊔
        supp F ({Sum.inl i, Sum.inr (Sum.inl i)} : Set (Idx n)) := by
  classical
  let pair : Set (Idx n) := {Sum.inl i, Sum.inr (Sum.inl i)}
  change anchoredSupport F n (insert i S) = anchoredSupport F n S ⊔ supp F pair
  ext v
  rw [Submodule.mem_sup]
  constructor
  · intro hv
    change ∀ a, a ∉ (activeCoords n (insert i S) : Set (Idx n)) → v a = 0 at hv
    let u : Vm n F := fun a => if a ∈ pair then 0 else v a
    let w : Vm n F := fun a => if a ∈ pair then v a else 0
    refine ⟨u, ?_, w, ?_, ?_⟩
    · change ∀ a, a ∉ (activeCoords n S : Set (Idx n)) → u a = 0
      intro a haS
      by_cases hp : a ∈ pair
      · simp [u, hp]
      · have hnot : a ∉ activeCoords n (insert i S) := by
          intro hmem
          rcases (mem_activeCoords_insert (i := i) (S := S) (a := a)).mp hmem with hS | h1 | h2
          · exact haS hS
          · exact hp (by rw [h1]; simp [pair])
          · exact hp (by rw [h2]; simp [pair])
        simp [u, hp, hv a hnot]
    · intro a ha
      simp [w, ha]
    · funext a
      by_cases hp : a ∈ pair <;> simp [u, w, hp]
  · rintro ⟨u, hu, w, hw, rfl⟩
    change ∀ a, a ∉ (activeCoords n S : Set (Idx n)) → u a = 0 at hu
    change ∀ a, a ∉ (activeCoords n (insert i S) : Set (Idx n)) → (u + w) a = 0
    intro a ha
    have haS : a ∉ activeCoords n S := fun hS =>
      ha ((mem_activeCoords_insert (i := i) (S := S) (a := a)).mpr (Or.inl hS))
    have hpair : pair ⊆ (activeCoords n (insert i S) : Set (Idx n)) := by
      intro x hx
      rcases hx with rfl | rfl
      · exact (mem_activeCoords_insert (i := i) (S := S) (a := Sum.inl i)).mpr
          (Or.inr (Or.inl rfl))
      · exact (mem_activeCoords_insert (i := i) (S := S) (a := Sum.inr (Sum.inl i))).mpr
          (Or.inr (Or.inr rfl))
    have hp : a ∉ pair := fun hp => ha (hpair hp)
    have hu0 : u a = 0 := hu a haS
    have hw0 : w a = 0 := hw a hp
    simp [hu0, hw0]

theorem coordSupport_minusPlaneCoordinates_eq_anchoredSupport
    (S : Finset (Fin (n - 1))) :
    coordSupport (minusPlaneCoordinates (n := n) (F := F)) S = anchoredSupport F n S := by
  induction S using Finset.induction_on with
  | empty =>
      rw [coordSupport_empty, coordAnchor_minusPlaneCoordinates]
  | insert i S hi ih =>
      rw [coordSupport_insert _ hi, anchoredSupport_insert i S, ih,
        coordPlane_minusPlaneCoordinates]

section CharTwo

variable [CharP F 2]

theorem spinAction_longWeyl_minusVec {i j : Fin (n - 1)} (hij : i ≠ j)
    (k : Fin (n - 1)) (s : Bool) :
    spinAction (quadMinus n F b c) ((minusFrame n b c).longWeyl hij true false) (minusVec n k s) =
      minusVec n (Equiv.swap i j k) s := by
  rw [show minusVec n k s = (minusFrame n b c).vec k s from rfl]
  rw [(minusFrame n b c).spinAction_longWeyl_vec hij true false k s, minusFrame_vec]
  have hsign : (longWeylSign i k : F) = 1 := by
    unfold longWeylSign
    split_ifs with h
    · exact CharTwo.neg_eq 1
    · rfl
  have hbool : longWeylBool i j true false k s = s := by
    unfold longWeylBool
    split_ifs <;> simp
  rw [hsign, hbool, one_smul]

theorem spinAction_longWeyl_eq_coordPermHom {i j : Fin (n - 1)} (hij : i ≠ j) :
    spinAction (quadMinus n F b c) ((minusFrame n b c).longWeyl hij true false) =
      coordPermHom (minusPlaneCoordinates (n := n) (F := F)) (Equiv.swap i j) := by
  apply LinearEquiv.toLinearMap_injective
  refine (Pi.basisFun F (Idx n)).ext fun a => ?_
  rcases a with k | k | t
  ·
    simp only [Pi.basisFun_apply]
    change spinAction (quadMinus n F b c) ((minusFrame n b c).longWeyl hij true false)
        (Pi.single (.inl k) 1) =
      coordPermHom (minusPlaneCoordinates (n := n) (F := F)) (Equiv.swap i j)
        (Pi.single (.inl k) 1)
    rw [show (Pi.single (.inl k) 1 : Vm n F) = minusVec n k true from rfl]
    rw [spinAction_longWeyl_minusVec hij k true]
    rw [← minusPlaneCoordinates_symm_single_true (n := n) (F := F) k,
      coordPermHom_plane, minusPlaneCoordinates_symm_single_true]
  ·
    simp only [Pi.basisFun_apply]
    change spinAction (quadMinus n F b c) ((minusFrame n b c).longWeyl hij true false)
        (Pi.single (.inr (.inl k)) 1) =
      coordPermHom (minusPlaneCoordinates (n := n) (F := F)) (Equiv.swap i j)
        (Pi.single (.inr (.inl k)) 1)
    rw [show (Pi.single (.inr (.inl k)) 1 : Vm n F) = minusVec n k false from rfl]
    rw [spinAction_longWeyl_minusVec hij k false]
    rw [← minusPlaneCoordinates_symm_single_false (n := n) (F := F) k,
      coordPermHom_plane, minusPlaneCoordinates_symm_single_false]
  ·
    simp only [Pi.basisFun_apply]
    change spinAction (quadMinus n F b c) ((minusFrame n b c).longWeyl hij true false)
        (Pi.single (.inr (.inr t)) 1) =
      coordPermHom (minusPlaneCoordinates (n := n) (F := F)) (Equiv.swap i j)
        (Pi.single (.inr (.inr t)) 1)
    rw [← planeVec_single (n := n) (F := F) t]
    rw [spinAction_longWeyl_planeVec (n := n) (b := b) (c := c) hij true false]
    rw [← minusPlaneCoordinates_symm_planeVec (n := n) (F := F) (p := Pi.single t 1),
      coordPermHom_anchor]

end CharTwo

section Finite

variable [Finite F] [CharP F 2]

theorem coordPermHom_swap_mem_supportedDerived
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    (S : Finset (Fin (n - 1))) {i j : Fin (n - 1)} (hi : i ∈ S) (hj : j ∈ S) :
    coordPermHom (minusPlaneCoordinates (n := n) (F := F)) (Equiv.swap i j) ∈
      supportedDerived (quadMinus n F b c) (anchoredSupport F n S) := by
  by_cases hij : i = j
  · subst hij
    rw [Equiv.swap_self]
    change coordPermHom (minusPlaneCoordinates (n := n) (F := F)) (1 : Equiv.Perm (Fin (n - 1))) ∈
      supportedDerived (quadMinus n F b c) (anchoredSupport F n S)
    rw [map_one]
    exact Subgroup.one_mem (H := supportedDerived (quadMinus n F b c) (anchoredSupport F n S))
  · rw [← spinAction_longWeyl_eq_coordPermHom (n := n) (F := F) (b := b) (c := c) hij]
    rw [(minusFrame n b c).longWeyl_eq hij true false]
    simp only [Bool.not_true, Bool.not_false, map_mul]
    have h1 : spinAction (quadMinus n F b c)
        ((minusFrame n b c).longRoot hij true false (.ofAdd 1)) ∈
        supportedDerived (quadMinus n F b c) (anchoredSupport F n S) :=
      spinAction_longRoot_mem_supportedDerived hirr hcard S hij hi hj true false 1
    have h2 : spinAction (quadMinus n F b c)
        ((minusFrame n b c).longRoot (Ne.symm hij) true false (.ofAdd (-1))) ∈
        supportedDerived (quadMinus n F b c) (anchoredSupport F n S) :=
      spinAction_longRoot_mem_supportedDerived hirr hcard S (Ne.symm hij) hj hi true false (-1)
    refine Subgroup.mul_mem (H := supportedDerived (quadMinus n F b c) (anchoredSupport F n S)) ?_ h1
    exact Subgroup.mul_mem (H := supportedDerived (quadMinus n F b c) (anchoredSupport F n S)) h1 h2

theorem coordPermHom_mem_supportedDerived_of_fixing_compl
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    (S : Finset (Fin (n - 1))) (σ : Equiv.Perm (Fin (n - 1)))
    (hσ : ∀ k : Fin (n - 1), k ∉ S → σ k = k) :
    coordPermHom (minusPlaneCoordinates (n := n) (F := F)) σ ∈
      supportedDerived (quadMinus n F b c) (anchoredSupport F n S) := by
  let H : Subgroup (Equiv.Perm (Fin (n - 1))) :=
    (supportedDerived (quadMinus n F b c) (anchoredSupport F n S)).comap
      (coordPermHom (minusPlaneCoordinates (n := n) (F := F)))
  have hfix : σ ∈ fixingSubgroup (Equiv.Perm (Fin (n - 1)))
      ((S : Set (Fin (n - 1)))ᶜ) := by
    rw [mem_fixingSubgroup_iff]
    intro k hk
    rw [Equiv.Perm.smul_def]
    exact hσ k (by simpa using hk)
  have hswap : ∀ a ∈ (S : Set (Fin (n - 1))), ∀ b ∈ (S : Set (Fin (n - 1))),
      Equiv.swap a b ∈ H := by
    intro a ha b hb
    exact Subgroup.mem_comap.mpr
      (coordPermHom_swap_mem_supportedDerived hirr hcard S ha hb)
  exact CFSG.Perm.fixingSubgroup_compl_le_of_swap_mem
    (S : Set (Fin (n - 1))) H hswap hfix

theorem coordPermHom_mem_supportedDerived_erase
    (hirr : ∀ s : F, s ^ 2 + b * s + c ≠ 0) (hcard : 2 < Nat.card F)
    (d : Fin (n - 1)) (σ : Equiv.Perm (Fin (n - 1))) (hσ : σ d = d) :
    coordPermHom (minusPlaneCoordinates (n := n) (F := F)) σ ∈
      supportedDerived (quadMinus n F b c) (anchoredSupport F n (Finset.univ.erase d)) := by
  refine coordPermHom_mem_supportedDerived_of_fixing_compl hirr hcard
    (Finset.univ.erase d) σ ?_
  intro k hk
  have hkd : k = d := by
    by_contra hne
    exact hk (Finset.mem_erase.mpr ⟨hne, Finset.mem_univ k⟩)
  rw [hkd, hσ]

end Finite

end CFSG.RankThree.PartOne.KCOrthogonal

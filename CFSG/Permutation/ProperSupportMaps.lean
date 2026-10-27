module

public import CFSG.LieType.CurtisTits.Amalgam
public import CFSG.Permutation.DeletionChart

public section

namespace CFSG.Permutation.ProperSupportMaps

open Subgroup

variable {I X H : Type*} [Fintype I] [DecidableEq I] [Group X] [Group H]

abbrev deletionSet (d : I) : Finset I := Finset.univ.erase d

@[simp] theorem mem_deletionSet {d x : I} : x ∈ deletionSet d ↔ x ≠ d := by
  simp [deletionSet]

theorem pair_subset_deletionSet {d u v : I} (hu : u ≠ d) (hv : v ≠ d) :
    ({u, v} : Finset I) ⊆ deletionSet d := by
  intro x hx
  simp only [Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with rfl | rfl
  · exact mem_deletionSet.mpr hu
  · exact mem_deletionSet.mpr hv

abbrev PairBelow (S : Finset I) := {P : Finset I // P ⊆ S ∧ P.card = 2}

variable {d : I} {B : Finset I → Subgroup X} {hB : Monotone B}
  {ρ : Equiv.Perm I →* X} {t : Equiv.Perm I →* H}
  {a : B (deletionSet d) →* H}

@[expose] def conjMapHom
    (hBmap : ∀ (σ : Equiv.Perm I) (S : Finset I),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ))
    (σ : Equiv.Perm I) (S : Finset I) : B S →* B (S.image σ) where
  toFun x := ⟨(MulAut.conj (ρ σ)).toMonoidHom (x : X), by
    rw [← hBmap σ S]
    exact Subgroup.mem_map.mpr ⟨(x : X), x.2, rfl⟩⟩
  map_one' := by ext; simp
  map_mul' x y := by ext; simp

@[simp] theorem conjMapHom_apply_coe
    (hBmap : ∀ (σ : Equiv.Perm I) (S : Finset I),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ))
    (σ : Equiv.Perm I) (S : Finset I) (x : B S) :
    (conjMapHom hBmap σ S x : X) = (MulAut.conj (ρ σ)).toMonoidHom (x : X) :=
  rfl

@[expose] def phiOf
    (hBmap : ∀ (σ : Equiv.Perm I) (S : Finset I),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ))
    (S : Finset I) (σ : Equiv.Perm I) (hσ : S.image σ ⊆ deletionSet d) : B S →* H :=
  (MulAut.conj ((t σ)⁻¹)).toMonoidHom.comp
    ((a.comp (Subgroup.inclusion (hB hσ))).comp (conjMapHom hBmap σ S))

@[simp] theorem phiOf_apply
    (hBmap : ∀ (σ : Equiv.Perm I) (S : Finset I),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ))
    (S : Finset I) (σ : Equiv.Perm I) (hσ : S.image σ ⊆ deletionSet d) (x : B S) :
    phiOf (hB := hB) (a := a) (t := t) hBmap S σ hσ x =
      (t σ)⁻¹ * a (Subgroup.inclusion (hB hσ) (conjMapHom hBmap σ S x)) * t σ := by
  simp [phiOf, MulAut.conj_apply]

theorem exists_perm_image_subset_deletionSet
    (S : Finset I) (hS : S ≠ Finset.univ) :
    ∃ σ : Equiv.Perm I, S.image σ ⊆ deletionSet d := by
  classical
  by_cases hSD : S = deletionSet d
  · refine ⟨1, ?_⟩
    simpa [hSD]
  · have hDnot : ¬ deletionSet d ⊆ S := by
      intro hDS
      apply hSD
      apply Finset.Subset.antisymm ?_ hDS
      intro x hx
      by_contra hxD
      have hxd : x = d := by simpa [deletionSet] using hxD
      have hxuniv : d ∈ S := hxd ▸ hx
      exfalso
      apply hS
      apply Finset.ext
      intro y
      simp only [Finset.mem_univ, iff_true]
      by_cases hy : y = d
      · simpa [hy] using hxuniv
      · exact hDS (Finset.mem_erase.mpr ⟨hy, Finset.mem_univ y⟩)
    obtain ⟨k, hkD, hkS⟩ := Finset.not_subset.mp hDnot
    refine ⟨Equiv.swap k d, ?_⟩
    intro y hy
    obtain ⟨s, hsS, rfl⟩ := Finset.mem_image.mp hy
    have hsk : s ≠ k := fun h => hkS (h ▸ hsS)
    rw [Equiv.swap_apply_def]
    by_cases hsd : s = d
    · rw [if_neg hsk, if_pos hsd]
      exact hkD
    · rw [if_neg hsk, if_neg hsd]
      exact Finset.mem_erase.mpr ⟨hsd, Finset.mem_univ s⟩

@[expose] noncomputable def properSupportPhi
    (hBmap : ∀ (σ : Equiv.Perm I) (S : Finset I),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ))
    (S : Finset I) (hS : S ≠ Finset.univ) : B S →* H :=
  phiOf (hB := hB) (a := a) (t := t) hBmap S
    (Classical.choose (exists_perm_image_subset_deletionSet (d := d) S hS))
    (Classical.choose_spec (exists_perm_image_subset_deletionSet (d := d) S hS))

theorem covariance_of_subset
    (hBmap : ∀ (σ : Equiv.Perm I) (S : Finset I),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ))
    (hgen : ∀ (S : Finset I), S ⊆ deletionSet d → 2 ≤ S.card →
      B S = ⨆ P : PairBelow S, B (P : Finset I))
    (hpair : ∀ (P : Finset I) (σ : Equiv.Perm I) (hPcard : P.card = 2)
      (hPD : P ⊆ deletionSet d) (hPσD : P.image σ ⊆ deletionSet d) (x : B P),
        a (Subgroup.inclusion (hB hPσD) (conjMapHom hBmap σ P x)) =
          t σ * a (Subgroup.inclusion (hB hPD) x) * (t σ)⁻¹)
    (hI : 4 ≤ Fintype.card I)
    (S : Finset I) (hS : S ⊆ deletionSet d)
    (σ : Equiv.Perm I) (hσ : S.image σ ⊆ deletionSet d) (x : B S) :
    a (Subgroup.inclusion (hB hσ) (conjMapHom hBmap σ S x)) =
      t σ * a (Subgroup.inclusion (hB hS) x) * (t σ)⁻¹ := by
  classical
  by_cases hcard : 2 ≤ S.card
  · let f : B S →* H :=
      (a.comp (Subgroup.inclusion (hB hσ))).comp (conjMapHom hBmap σ S)
    let g : B S →* H :=
      (MulAut.conj (t σ)).toMonoidHom.comp (a.comp (Subgroup.inclusion (hB hS)))
    have hfg : f = g := by
      let L : PairBelow S → Subgroup (B S) :=
        fun P => (B (P : Finset I)).subgroupOf (B S)
      have hgenL : (⨆ P, L P) = ⊤ := by
        apply Subgroup.map_injective (B S).subtype_injective
        rw [Subgroup.map_iSup]
        have htop : (⊤ : Subgroup (B S)).map (B S).subtype = B S := by
          simpa using Subgroup.map_subgroupOf_eq_of_le (le_refl (B S))
        rw [htop]
        have hL : ∀ P : PairBelow S,
            (L P).map (B S).subtype = B (P : Finset I) :=
          fun P => Subgroup.map_subgroupOf_eq_of_le (hB P.2.1)
        simp only [hL]
        exact (hgen S hS hcard).symm
      apply CFSG.LieType.CurtisTits.hom_ext_of_iSup_eq_top (L := L) hgenL
      intro P y
      have hy : Subgroup.inclusion (hB P.2.1) ⟨(y : B S), y.2⟩ = y := rfl
      have hσP : (P : Finset I).image σ ⊆ deletionSet d :=
        (Finset.image_subset_image P.2.1).trans hσ
      have hPD : (P : Finset I) ⊆ deletionSet d := P.2.1.trans hS
      have harg :
          Subgroup.inclusion (hB hσ) (conjMapHom hBmap σ S
              (Subgroup.inclusion (hB P.2.1) ⟨(y : B S), y.2⟩)) =
            Subgroup.inclusion (hB hσP) (conjMapHom hBmap σ (P : Finset I)
              ⟨(y : B S), y.2⟩) := by
        ext
        rfl
      have hbase :
          Subgroup.inclusion (hB hPD) ⟨(y : B S), y.2⟩ =
            Subgroup.inclusion (hB hS) y := by
        ext
        rfl
      calc
        f y = f (Subgroup.inclusion (hB P.2.1) ⟨(y : B S), y.2⟩) := by rw [hy]
        _ = a (Subgroup.inclusion (hB hσ) (conjMapHom hBmap σ S
              (Subgroup.inclusion (hB P.2.1) ⟨(y : B S), y.2⟩))) := by
            simp only [f, MonoidHom.comp_apply]
        _ = a (Subgroup.inclusion (hB hσP) (conjMapHom hBmap σ (P : Finset I)
              ⟨(y : B S), y.2⟩)) := by rw [harg]
        _ = t σ * a (Subgroup.inclusion (hB hPD) ⟨(y : B S), y.2⟩) * (t σ)⁻¹ :=
            hpair (P : Finset I) σ P.2.2 hPD hσP ⟨(y : B S), y.2⟩
        _ = t σ * a (Subgroup.inclusion (hB hS) y) * (t σ)⁻¹ := by rw [hbase]
        _ = g y := by simp [g, MulAut.conj_apply]
    simpa only [f, g, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply] using
      congrArg (fun φ : B S →* H => φ x) hfg
  · have hcardS : S.card ≤ 2 := by omega
    let Q : Finset I := (deletionSet d).erase (σ⁻¹ d)
    have hSQ : S ⊆ Q := by
      intro y hy
      have hyD : y ∈ deletionSet d := hS hy
      have hyne : y ≠ σ⁻¹ d := by
        intro hyeq
        have hmem : σ y ∈ deletionSet d :=
          hσ (Finset.mem_image.mpr ⟨y, hy, rfl⟩)
        have hyd : σ y = d := by
          rw [hyeq]
          exact Equiv.apply_symm_apply σ d
        exact (Finset.mem_erase.mp hmem).1 hyd
      exact Finset.mem_erase.mpr ⟨hyne, hyD⟩
    have hQcard : 2 ≤ Q.card := by
      have hI' : 4 ≤ (Finset.univ : Finset I).card := by simpa using hI
      have hcardD : (deletionSet d).card = (Finset.univ : Finset I).card - 1 := by
        simp [deletionSet, Finset.card_erase_of_mem (Finset.mem_univ d)]
      have hmem := Finset.mem_univ d
      change 2 ≤ ((deletionSet d).erase (σ⁻¹ d)).card
      by_cases h : σ⁻¹ d ∈ deletionSet d
      · rw [Finset.card_erase_of_mem h, hcardD]
        omega
      · rw [Finset.erase_eq_of_notMem h, hcardD]
        omega
    obtain ⟨P, hSP, hPQ, hPcard⟩ :=
      Finset.exists_subsuperset_card_eq hSQ hcardS hQcard
    have hPD : P ⊆ deletionSet d := hPQ.trans (Finset.erase_subset _ _)
    have hQσ : Q.image σ ⊆ deletionSet d := by
      intro y hy
      obtain ⟨z, hzQ, rfl⟩ := Finset.mem_image.mp hy
      have hzne : z ≠ σ⁻¹ d := (Finset.mem_erase.mp hzQ).1
      have hzD : z ∈ deletionSet d := (Finset.mem_erase.mp hzQ).2
      refine Finset.mem_erase.mpr ⟨?_, Finset.mem_univ _⟩
      intro hzd
      apply hzne
      rw [← hzd]
      exact (Equiv.symm_apply_apply σ z).symm
    have hPσD : P.image σ ⊆ deletionSet d :=
      (Finset.image_subset_image hPQ).trans hQσ
    let y : B P := Subgroup.inclusion (hB hSP) x
    have harg :
        Subgroup.inclusion (hB hσ) (conjMapHom hBmap σ S x) =
          Subgroup.inclusion (hB hPσD) (conjMapHom hBmap σ P y) := by
      ext
      rfl
    have hbase :
        Subgroup.inclusion (hB hS) x =
          Subgroup.inclusion (hB hPD) y := by
      ext
      rfl
    calc
      a (Subgroup.inclusion (hB hσ) (conjMapHom hBmap σ S x)) =
          a (Subgroup.inclusion (hB hPσD) (conjMapHom hBmap σ P y)) := by rw [harg]
      _ = t σ * a (Subgroup.inclusion (hB hPD) y) * (t σ)⁻¹ :=
          hpair P σ hPcard hPD hPσD y
      _ = t σ * a (Subgroup.inclusion (hB hS) x) * (t σ)⁻¹ := by rw [hbase]

theorem pairCovariance_of_cross
    (hBmap : ∀ (σ : Equiv.Perm I) (S : Finset I),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ))
    {u v c : I}
    (huv : u ≠ v) (hcu : c ≠ u) (hcv : c ≠ v)
    (hdu : d ≠ u) (hdv : d ≠ v) (hcd : c ≠ d)
    (hcommon : ∀ σ : Equiv.Perm I, σ d = d →
      ∃ h : (ρ σ : X) ∈ B (deletionSet d), a ⟨ρ σ, h⟩ = t σ)
    (hbase : ∀ (σ : Equiv.Perm I) (x : B ({u, v} : Finset I)),
      σ u = u → σ v = v → ρ σ * (x : X) = (x : X) * ρ σ)
    (hcross : ∀ x : B ({u, v} : Finset I),
      t (Equiv.swap c d) *
          a (Subgroup.inclusion (hB (pair_subset_deletionSet hdu.symm hdv.symm)) x) =
        a (Subgroup.inclusion (hB (pair_subset_deletionSet hdu.symm hdv.symm)) x) *
          t (Equiv.swap c d)) :
    ∀ (P : Finset I) (σ : Equiv.Perm I) (hPcard : P.card = 2)
      (hPD : P ⊆ deletionSet d) (hPσD : P.image σ ⊆ deletionSet d) (x : B P),
        a (Subgroup.inclusion (hB hPσD) (conjMapHom hBmap σ P x)) =
          t σ * a (Subgroup.inclusion (hB hPD) x) * (t σ)⁻¹ := by
  classical
  intro P σ hPcard hPD hPσD x
  obtain ⟨i, j, hij, rfl⟩ := Finset.card_eq_two.mp hPcard
  have hcontain : ∀ {i j : I}, i ≠ j → i ≠ d → j ≠ d →
      B ({i, j} : Finset I) ≤ B (deletionSet d) := by
    intro i j _ hid hjd
    exact hB (pair_subset_deletionSet hid hjd)
  have hequiv : ∀ (σ : Equiv.Perm I) (i j : I),
      (B ({i, j} : Finset I)).map (MulAut.conj (ρ σ)).toMonoidHom =
        B ({σ i, σ j} : Finset I) := by
    intro σ i j
    simpa [Finset.image_insert, Finset.image_singleton] using
      hBmap σ ({i, j} : Finset I)
  have hid : i ≠ d := mem_deletionSet.mp (hPD (by simp))
  have hjd : j ≠ d := mem_deletionSet.mp (hPD (by simp))
  have hσi : σ i ≠ d := by
    have hmem : σ i ∈ deletionSet d :=
      hPσD (Finset.mem_image.mpr ⟨i, by simp, rfl⟩)
    exact mem_deletionSet.mp hmem
  have hσj : σ j ≠ d := by
    have hmem : σ j ∈ deletionSet d :=
      hPσD (Finset.mem_image.mpr ⟨j, by simp, rfl⟩)
    exact mem_deletionSet.mp hmem
  have hcov := CFSG.Permutation.DeletionChart.deletionChart_covariance
    (A := B (deletionSet d)) ρ a t (fun i j => B ({i, j} : Finset I))
    huv hcu hcv hdu hdv hcd hequiv hcontain hcommon hbase hcross
    hij hid hjd σ hσi hσj x
  have hL :
      Subgroup.inclusion (hB hPσD) (conjMapHom hBmap σ ({i, j} : Finset I) x) =
        Subgroup.inclusion (hcontain (σ.injective.ne hij) hσi hσj)
          ⟨ρ σ * (x : X) * (ρ σ)⁻¹,
            CFSG.Permutation.DeletionChart.conj_mem_pair hequiv σ x⟩ := by
    ext
    rfl
  have hR :
      Subgroup.inclusion (hB hPD) x =
        Subgroup.inclusion (hcontain hij hid hjd) x := by
    ext
    rfl
  rw [hL, hR]
  exact hcov

theorem properSupportPhi_apply_of_image_subset
    (hBmap : ∀ (σ : Equiv.Perm I) (S : Finset I),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ))
    (hgen : ∀ (S : Finset I), S ⊆ deletionSet d → 2 ≤ S.card →
      B S = ⨆ P : PairBelow S, B (P : Finset I))
    (hpair : ∀ (P : Finset I) (σ : Equiv.Perm I) (hPcard : P.card = 2)
      (hPD : P ⊆ deletionSet d) (hPσD : P.image σ ⊆ deletionSet d) (x : B P),
        a (Subgroup.inclusion (hB hPσD) (conjMapHom hBmap σ P x)) =
          t σ * a (Subgroup.inclusion (hB hPD) x) * (t σ)⁻¹)
    (hI : 4 ≤ Fintype.card I)
    (S : Finset I) (hS : S ≠ Finset.univ)
    (σ : Equiv.Perm I) (hσ : S.image σ ⊆ deletionSet d) (x : B S) :
    properSupportPhi (hB := hB) (a := a) (t := t) hBmap S hS x =
      (t σ)⁻¹ * a (Subgroup.inclusion (hB hσ) (conjMapHom hBmap σ S x)) * t σ := by
  classical
  let σ₀ : Equiv.Perm I :=
    Classical.choose (exists_perm_image_subset_deletionSet (d := d) S hS)
  have hσ₀ : S.image σ₀ ⊆ deletionSet d :=
    Classical.choose_spec (exists_perm_image_subset_deletionSet (d := d) S hS)
  let R : Finset I := S.image σ₀
  let δ : Equiv.Perm I := σ * σ₀⁻¹
  have hδR : R.image δ ⊆ deletionSet d := by
    have himage : R.image δ = S.image σ := by
      dsimp [R, δ]
      rw [Finset.image_image]
      congr 1
      ext y
      simp [Equiv.Perm.mul_apply]
    rw [himage]
    exact hσ
  have hcov := covariance_of_subset hBmap hgen hpair hI R hσ₀ δ hδR
    (conjMapHom hBmap σ₀ S x)
  have hδ : t δ = t σ * (t σ₀)⁻¹ := by
    simp [δ]
  have hconj :
      Subgroup.inclusion (hB hδR)
          (conjMapHom hBmap δ R (conjMapHom hBmap σ₀ S x)) =
        Subgroup.inclusion (hB hσ) (conjMapHom hBmap σ S x) := by
    ext
    change (MulAut.conj (ρ (σ * σ₀⁻¹))).toMonoidHom
        ((MulAut.conj (ρ σ₀)).toMonoidHom (x : X)) =
      (MulAut.conj (ρ σ)).toMonoidHom (x : X)
    rw [map_mul]
    simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply, map_inv]
    group
  calc
    properSupportPhi (hB := hB) (a := a) (t := t) hBmap S hS x =
        (t σ₀)⁻¹ * a (Subgroup.inclusion (hB hσ₀)
          (conjMapHom hBmap σ₀ S x)) * t σ₀ := by
      change phiOf (hB := hB) (a := a) (t := t) hBmap S σ₀ hσ₀ x = _
      rw [phiOf_apply]
    _ = (t σ)⁻¹ * a (Subgroup.inclusion (hB hσ)
          (conjMapHom hBmap σ S x)) * t σ := by
      rw [← hconj, hcov, hδ]
      group

theorem properSupportPhi_apply_of_subset
    (hBmap : ∀ (σ : Equiv.Perm I) (S : Finset I),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ))
    (hgen : ∀ (S : Finset I), S ⊆ deletionSet d → 2 ≤ S.card →
      B S = ⨆ P : PairBelow S, B (P : Finset I))
    (hpair : ∀ (P : Finset I) (σ : Equiv.Perm I) (hPcard : P.card = 2)
      (hPD : P ⊆ deletionSet d) (hPσD : P.image σ ⊆ deletionSet d) (x : B P),
        a (Subgroup.inclusion (hB hPσD) (conjMapHom hBmap σ P x)) =
          t σ * a (Subgroup.inclusion (hB hPD) x) * (t σ)⁻¹)
    (hI : 4 ≤ Fintype.card I)
    (S : Finset I) (hS : S ≠ Finset.univ) (hSD : S ⊆ deletionSet d) (x : B S) :
    properSupportPhi (hB := hB) (a := a) (t := t) hBmap S hS x = a (Subgroup.inclusion (hB hSD) x) := by
  have hσ1 : S.image (1 : Equiv.Perm I) ⊆ deletionSet d := by simpa using hSD
  have h1 := properSupportPhi_apply_of_image_subset hBmap hgen hpair hI S hS
    (1 : Equiv.Perm I) hσ1 x
  rw [h1]
  have h2 :
      Subgroup.inclusion (hB hσ1) (conjMapHom hBmap (1 : Equiv.Perm I) S x) =
        Subgroup.inclusion (hB hSD) x := by
    ext
    change (MulAut.conj (ρ (1 : Equiv.Perm I))).toMonoidHom (x : X) = (x : X)
    simp
  simp only [map_one, inv_one, one_mul, mul_one]
  exact congrArg a h2

theorem properSupportPhi_comp_inclusion
    (hBmap : ∀ (σ : Equiv.Perm I) (S : Finset I),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ))
    (hgen : ∀ (S : Finset I), S ⊆ deletionSet d → 2 ≤ S.card →
      B S = ⨆ P : PairBelow S, B (P : Finset I))
    (hpair : ∀ (P : Finset I) (σ : Equiv.Perm I) (hPcard : P.card = 2)
      (hPD : P ⊆ deletionSet d) (hPσD : P.image σ ⊆ deletionSet d) (x : B P),
        a (Subgroup.inclusion (hB hPσD) (conjMapHom hBmap σ P x)) =
          t σ * a (Subgroup.inclusion (hB hPD) x) * (t σ)⁻¹)
    (hI : 4 ≤ Fintype.card I)
    (R S : Finset I) (hR : R ≠ Finset.univ) (hS : S ≠ Finset.univ) (hRS : R ⊆ S) :
    (properSupportPhi (hB := hB) (a := a) (t := t) hBmap S hS).comp
        (Subgroup.inclusion (hB hRS)) =
      properSupportPhi (hB := hB) (a := a) (t := t) hBmap R hR := by
  obtain ⟨σ, hσS⟩ := exists_perm_image_subset_deletionSet (d := d) S hS
  have hσR : R.image σ ⊆ deletionSet d :=
    (Finset.image_subset_image hRS).trans hσS
  ext x
  rw [MonoidHom.comp_apply,
    properSupportPhi_apply_of_image_subset hBmap hgen hpair hI S hS σ hσS
      (Subgroup.inclusion (hB hRS) x),
    properSupportPhi_apply_of_image_subset hBmap hgen hpair hI R hR σ hσR x]
  have harg :
      Subgroup.inclusion (hB hσS)
          (conjMapHom hBmap σ S (Subgroup.inclusion (hB hRS) x)) =
        Subgroup.inclusion (hB hσR) (conjMapHom hBmap σ R x) := by
    ext
    rfl
  rw [harg]

theorem properSupportPhi_apply_common
    (hBmap : ∀ (σ : Equiv.Perm I) (S : Finset I),
      (B S).map (MulAut.conj (ρ σ)).toMonoidHom = B (S.image σ))
    (hgen : ∀ (S : Finset I), S ⊆ deletionSet d → 2 ≤ S.card →
      B S = ⨆ P : PairBelow S, B (P : Finset I))
    (hpair : ∀ (P : Finset I) (σ : Equiv.Perm I) (hPcard : P.card = 2)
      (hPD : P ⊆ deletionSet d) (hPσD : P.image σ ⊆ deletionSet d) (x : B P),
        a (Subgroup.inclusion (hB hPσD) (conjMapHom hBmap σ P x)) =
          t σ * a (Subgroup.inclusion (hB hPD) x) * (t σ)⁻¹)
    (hI : 4 ≤ Fintype.card I)
    (S : Finset I) (hS : S ≠ Finset.univ)
    (π : Equiv.Perm I) (hfix : ∀ x, x ∉ S → π x = x)
    (hmemS : (ρ π : X) ∈ B S)
    (hcommon : ∀ (τ : Equiv.Perm I), τ d = d →
      ∃ hmem : (ρ τ : X) ∈ B (deletionSet d),
        a ⟨ρ τ, hmem⟩ = t τ) :
    properSupportPhi (hB := hB) (a := a) (t := t) hBmap S hS ⟨ρ π, hmemS⟩ = t π := by
  classical
  obtain ⟨σ, hσS⟩ := exists_perm_image_subset_deletionSet (d := d) S hS
  let τ : Equiv.Perm I := σ * π * σ⁻¹
  have hxnotS : σ⁻¹ d ∉ S := by
    intro hx
    have hmem : σ (σ⁻¹ d) ∈ deletionSet d :=
      hσS (Finset.mem_image.mpr ⟨σ⁻¹ d, hx, rfl⟩)
    have hd : d ∈ deletionSet d := by simpa using hmem
    exact (Finset.mem_erase.mp hd).1 rfl
  have hτd : τ d = d := by
    calc
      τ d = σ (π (σ⁻¹ d)) := by simp [τ, Equiv.Perm.mul_apply]
      _ = σ (σ⁻¹ d) := by rw [hfix _ hxnotS]
      _ = d := Equiv.apply_symm_apply σ d
  obtain ⟨hmemD, hval⟩ := hcommon τ hτd
  have hconj :
      Subgroup.inclusion (hB hσS)
          (conjMapHom hBmap σ S ⟨ρ π, hmemS⟩) =
        ⟨ρ τ, hmemD⟩ := by
    ext
    change (MulAut.conj (ρ σ)).toMonoidHom (ρ π) = ρ τ
    dsimp [τ]
    simp only [map_mul, map_inv, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  have htτ : t τ = t σ * t π * (t σ)⁻¹ := by
    dsimp [τ]
    simp only [map_mul, map_inv]
  rw [properSupportPhi_apply_of_image_subset hBmap hgen hpair hI S hS σ hσS
    ⟨ρ π, hmemS⟩]
  rw [hconj, hval, htτ]
  group

end CFSG.Permutation.ProperSupportMaps

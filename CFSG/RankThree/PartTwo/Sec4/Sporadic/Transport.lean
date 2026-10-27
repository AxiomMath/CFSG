module

public import CFSG.RankThree.Asc83Table.Automizer
public import CFSG.LocalAnalysis.ComponentClassification.OuterAutomorphisms
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec4.Notation

public section

namespace CFSG.RankThree.PartTwo.Sec4.Sporadic

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4 Subgroup

section Automizer

variable {G G' : Type*} [Group G] [Group G']

theorem autIn_top_eq_range (X : Subgroup G) : autIn ⊤ X = X.normalizerMonoidHom.range := by
  rw [autIn, MonoidHom.range_eq_map]
  congr 1
  ext g
  simp only [mem_subgroupOf, mem_inf, mem_top, true_and, SetLike.coe_mem]

noncomputable def automizerEquivAutIn (X : Subgroup G) :
    CFSG.RankThree.Asc83Table.Automizer X ≃* autIn ⊤ X :=
  (QuotientGroup.quotientMulEquivOfEq (normalizerMonoidHom_ker X).symm).trans
    ((QuotientGroup.quotientKerEquivRange X.normalizerMonoidHom).trans
      (MulEquiv.subgroupCongr (autIn_top_eq_range X).symm))

noncomputable def autInTopCongr (φ : G ≃* G') (X : Subgroup G) :
    autIn ⊤ X ≃* autIn ⊤ (X.map φ.toMonoidHom) :=
  (automizerEquivAutIn X).symm.trans
    ((CFSG.RankThree.Asc83Table.automizerCongr φ X).trans
      (automizerEquivAutIn (X.map φ.toMonoidHom)))

theorem card_autIn_top (X : Subgroup G) :
    Nat.card (autIn ⊤ X) = Nat.card (CFSG.RankThree.Asc83Table.Automizer X) :=
  (Nat.card_congr (automizerEquivAutIn X).toEquiv).symm

end Automizer

section Centre

variable {G G' : Type*} [Group G] [Group G']

theorem inf_centralizer_eq_map_center (P : Subgroup G) :
    P ⊓ centralizer (P : Set G) = (center P).map P.subtype := by
  ext g
  constructor
  · rintro ⟨hgP, hgC⟩
    exact ⟨⟨g, hgP⟩, Subgroup.mem_center_iff.mpr fun h =>
      Subtype.ext (mem_centralizer_iff.mp hgC h h.2), rfl⟩
  · rintro ⟨c, hc, rfl⟩
    refine ⟨c.2, mem_centralizer_iff.mpr fun h hh => ?_⟩
    have := congrArg Subtype.val (mem_center_iff.mp hc ⟨h, hh⟩)
    exact this

theorem map_inf_centralizer (φ : G ≃* G') (P : Subgroup G) :
    (P ⊓ centralizer (P : Set G)).map φ.toMonoidHom =
      P.map φ.toMonoidHom ⊓ centralizer ((P.map φ.toMonoidHom : Subgroup G') : Set G') := by
  rw [Subgroup.map_inf _ _ _ φ.injective,
    CFSG.RankThree.Asc83Table.map_equiv_centralizer_eq]

end Centre

section Conj

variable {G G' : Type*} [Group G] [Group G']

theorem conjugate_map (φ : G ≃* G') (X : Subgroup G) (x : G) :
    (conjugate X x).map φ.toMonoidHom = conjugate (X.map φ.toMonoidHom) (φ x) := by
  rw [conjugate, conjugate, Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp [map_mul, map_inv]

theorem map_map_conj (φ : G ≃* G') (X : Subgroup G) :
    (X.map φ.toMonoidHom).map (MulAut.conj : G' →* MulAut G') =
      (X.map (MulAut.conj : G →* MulAut G)).map (MulAut.congr φ).toMonoidHom := by
  rw [Subgroup.map_map, Subgroup.map_map]
  congr 1
  ext g
  simp only [MonoidHom.coe_comp, MulEquiv.coe_toMonoidHom, Function.comp_apply]
  rw [CFSG.ComponentClassification.OuterAutomorphisms.congr_conj]

end Conj

section Invariant

variable {G G' : Type*} [Group G] [Group G']

theorem map_symm_map (ψ : G ≃* G') (X : Subgroup G) :
    (X.map ψ.toMonoidHom).map ψ.symm.toMonoidHom = X := by
  rw [Subgroup.map_map]
  convert Subgroup.map_id X
  ext g
  simp

theorem map_map_symm (ψ : G ≃* G') (Y : Subgroup G') :
    (Y.map ψ.symm.toMonoidHom).map ψ.toMonoidHom = Y :=
  map_symm_map ψ.symm Y

theorem image_invariantPiSubgroups (ψ : G ≃* G') (H A : Subgroup G) (π : Set Nat.Primes) :
    (fun X : Subgroup G => X.map ψ.toMonoidHom) '' invariantPiSubgroups H A π =
      invariantPiSubgroups (H.map ψ.toMonoidHom) (A.map ψ.toMonoidHom) π := by
  ext Y
  constructor
  · rintro ⟨X, hX, rfl⟩
    exact map_mem_invariantPiSubgroups ψ hX
  · intro hY
    refine ⟨Y.map ψ.symm.toMonoidHom, ?_, map_map_symm ψ Y⟩
    have h := map_mem_invariantPiSubgroups ψ.symm hY
    rwa [map_symm_map, map_symm_map] at h

theorem map_mem_invariantPiSubgroups_iff (ψ : G ≃* G') {H A X : Subgroup G}
    {π : Set Nat.Primes} :
    X.map ψ.toMonoidHom ∈ invariantPiSubgroups (H.map ψ.toMonoidHom) (A.map ψ.toMonoidHom) π ↔
      X ∈ invariantPiSubgroups H A π := by
  rw [← image_invariantPiSubgroups]
  exact (Subgroup.map_injective ψ.injective).mem_set_image

theorem image_maxInvariantPiSubgroups (ψ : G ≃* G') (H A : Subgroup G) (π : Set Nat.Primes) :
    (fun X : Subgroup G => X.map ψ.toMonoidHom) '' maxInvariantPiSubgroups H A π =
      maxInvariantPiSubgroups (H.map ψ.toMonoidHom) (A.map ψ.toMonoidHom) π := by
  ext Y
  constructor
  · rintro ⟨X, hX, rfl⟩
    rw [mem_maxInvariantPiSubgroups_iff] at hX ⊢
    refine ⟨(map_mem_invariantPiSubgroups_iff ψ).2 hX.1, fun Z hZ hle => ?_⟩
    have hZ' : Z.map ψ.symm.toMonoidHom ∈ invariantPiSubgroups H A π := by
      rw [← map_mem_invariantPiSubgroups_iff ψ, map_map_symm]
      exact hZ
    have hle' : X ≤ Z.map ψ.symm.toMonoidHom := by
      have := Subgroup.map_mono (f := ψ.symm.toMonoidHom) hle
      rwa [map_symm_map] at this
    have := hX.2 _ hZ' hle'
    rw [← this]
    exact (map_map_symm ψ Z).symm
  · intro hY
    refine ⟨Y.map ψ.symm.toMonoidHom, ?_, map_map_symm ψ Y⟩
    rw [mem_maxInvariantPiSubgroups_iff] at hY ⊢
    refine ⟨?_, fun Z hZ hle => ?_⟩
    · rw [← map_mem_invariantPiSubgroups_iff ψ, map_map_symm]
      exact hY.1
    · have hZ' := (map_mem_invariantPiSubgroups_iff ψ).2 hZ
      have hle' : Y ≤ Z.map ψ.toMonoidHom := by
        have := Subgroup.map_mono (f := ψ.toMonoidHom) hle
        rwa [map_map_symm] at this
      have := hY.2 _ hZ' hle'
      rw [← this, map_symm_map]

end Invariant

theorem isKleinFour_of_isElementaryAbelian {Q : Type*} [Group Q]
    (h : IsElementaryAbelian 2 Q) (hc : Nat.card Q = 4) : IsKleinFour Q := by
  have hdvd : Monoid.exponent Q ∣ 2 := h.exponent_dvd_p
  refine { card_four := hc, exponent_two := ?_ }
  rcases (Nat.dvd_prime Nat.prime_two).mp hdvd with h1 | h2
  · exfalso
    have : Subsingleton Q := by
      refine ⟨fun a b => ?_⟩
      have ha := Monoid.pow_exponent_eq_one a
      have hb := Monoid.pow_exponent_eq_one b
      rw [h1, pow_one] at ha hb
      rw [ha, hb]
    have h1 : Nat.card Q = 1 := Nat.card_eq_one_iff_unique.mpr ⟨this, ⟨1⟩⟩
    omega
  · exact h2

end CFSG.RankThree.PartTwo.Sec4.Sporadic

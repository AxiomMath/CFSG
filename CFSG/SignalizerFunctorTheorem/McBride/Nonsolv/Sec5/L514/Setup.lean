module

public import CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.PairProj
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.Semisimple
import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.SignalizerFunctorTheorem.McBride.Prelim.SemisimpleFactors

public section

open CFSG.Open
open scoped commutatorElement

namespace CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

variable {Γ : Type*} [Group Γ]

theorem map_conj_map_conj (J : Subgroup Γ) (a b : Γ) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj b).toMonoidHom =
      J.map (MulAut.conj (b * a)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext y
  simp [mul_assoc]

theorem mem_map_conj_iff {J : Subgroup Γ} {a x : Γ} :
    x ∈ J.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ J := by
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [mul_assoc] using hy
  · intro h
    exact ⟨a⁻¹ * x * a, h, by simp [mul_assoc]⟩

theorem conj_mem_sSup {S : Set (Subgroup Γ)} {a : Γ}
    (ha : ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S) {y : Γ} (hy : y ∈ sSup S) :
    a * y * a⁻¹ ∈ sSup S := by
  have : sSup S ≤ (sSup S).comap (MulAut.conj a).toMonoidHom :=
    sSup_le fun J hJ z hz => le_sSup (ha J hJ) ⟨z, hz, rfl⟩
  exact this hy

theorem mem_normalizer_sSup {S : Set (Subgroup Γ)} {a : Γ}
    (ha : ∀ J ∈ S, J.map (MulAut.conj a).toMonoidHom ∈ S)
    (ha' : ∀ J ∈ S, J.map (MulAut.conj a⁻¹).toMonoidHom ∈ S) :
    a ∈ Subgroup.normalizer ((sSup S : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨conj_mem_sSup ha, fun hx => ?_⟩
  have := conj_mem_sSup ha' hx
  rwa [show a⁻¹ * (a * x * a⁻¹) * a⁻¹⁻¹ = x by group] at this

theorem commute_of_forall_commute_sSup {S T : Set (Subgroup Γ)}
    (h : ∀ J₁ ∈ S, ∀ J₂ ∈ T, ∀ x ∈ J₁, ∀ y ∈ J₂, Commute x y) :
    ∀ x ∈ sSup S, ∀ y ∈ sSup T, Commute x y := by
  have h1 : ∀ J₁ ∈ S, sSup T ≤ Subgroup.centralizer (J₁ : Set Γ) := fun J₁ hJ₁ =>
    sSup_le fun J₂ hJ₂ y hy => Subgroup.mem_centralizer_iff.mpr fun x hx =>
      (h J₁ hJ₁ J₂ hJ₂ x hx y hy).eq
  have h2 : sSup S ≤ Subgroup.centralizer ((sSup T : Subgroup Γ) : Set Γ) :=
    sSup_le fun J₁ hJ₁ => Subgroup.le_centralizer_iff.mpr (h1 J₁ hJ₁)
  intro x hx y hy
  exact (Subgroup.mem_centralizer_iff.mp (h2 hx) y hy).symm

@[expose] def conjOrbit (A J : Subgroup Γ) : Set (Subgroup Γ) :=
  {K | ∃ a ∈ A, K = J.map (MulAut.conj a).toMonoidHom}

@[expose] def outsideOrbit (G A J : Subgroup Γ) : Subgroup Γ :=
  sSup (lcal G \ conjOrbit A J)

theorem self_mem_conjOrbit (A J : Subgroup Γ) : J ∈ conjOrbit A J :=
  ⟨1, one_mem A, by ext y; simp [Subgroup.mem_map]⟩

theorem map_conj_mem_conjOrbit {A J K : Subgroup Γ} (hK : K ∈ conjOrbit A J) {a : Γ} (ha : a ∈ A) :
    K.map (MulAut.conj a).toMonoidHom ∈ conjOrbit A J := by
  obtain ⟨b, hb, rfl⟩ := hK
  exact ⟨a * b, mul_mem ha hb, map_conj_map_conj J b a⟩

theorem exists_conj_of_mem_conjOrbit {A J K K' : Subgroup Γ} (hK : K ∈ conjOrbit A J)
    (hK' : K' ∈ conjOrbit A J) : ∃ a ∈ A, K' = K.map (MulAut.conj a).toMonoidHom := by
  obtain ⟨b, hb, rfl⟩ := hK
  obtain ⟨b', hb', rfl⟩ := hK'
  refine ⟨b' * b⁻¹, mul_mem hb' (inv_mem hb), ?_⟩
  rw [map_conj_map_conj]
  simp

theorem conjOrbit_subset_lcal {A G J : Subgroup Γ} (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hJ : J ∈ lcal G) : conjOrbit A J ⊆ lcal G := by
  rintro _ ⟨a, ha, rfl⟩
  exact map_conj_mem_lcal hJ (hAG ha)

theorem orbitClosure_eq_sSup (A J : Subgroup Γ) : orbitClosure J A = sSup (conjOrbit A J) := by
  apply le_antisymm
  · exact iSup₂_le fun a ha => le_sSup ⟨a, ha, rfl⟩
  · refine sSup_le fun K hK => ?_
    obtain ⟨a, ha, rfl⟩ := hK
    exact le_iSup₂_of_le a ha le_rfl

theorem map_conj_map_conj_inv (J : Subgroup Γ) (a : Γ) :
    (J.map (MulAut.conj a).toMonoidHom).map (MulAut.conj a⁻¹).toMonoidHom = J := by
  rw [map_conj_map_conj]
  ext y
  simp

theorem mem_normalizer_inf {X Y : Subgroup Γ} {g : Γ} (hX : g ∈ Subgroup.normalizer (X : Set Γ))
    (hY : g ∈ Subgroup.normalizer (Y : Set Γ)) :
    g ∈ Subgroup.normalizer ((X ⊓ Y : Subgroup Γ) : Set Γ) := by
  rw [Subgroup.mem_normalizer_iff] at hX hY ⊢
  intro x
  rw [Subgroup.mem_inf, Subgroup.mem_inf, hX x, hY x]

theorem mem_normalizer_orbitClosure {A J : Subgroup Γ} {a : Γ} (ha : a ∈ A) :
    a ∈ Subgroup.normalizer ((orbitClosure J A : Subgroup Γ) : Set Γ) := by
  rw [orbitClosure_eq_sSup]
  exact mem_normalizer_sSup (fun K hK => map_conj_mem_conjOrbit hK ha)
    (fun K hK => map_conj_mem_conjOrbit hK (inv_mem ha))

theorem map_conj_mem_lcal_diff {A G J : Subgroup Γ} (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    {K : Subgroup Γ} (hK : K ∈ lcal G \ conjOrbit A J) {a : Γ} (ha : a ∈ A) :
    K.map (MulAut.conj a).toMonoidHom ∈ lcal G \ conjOrbit A J := by
  refine ⟨map_conj_mem_lcal hK.1 (hAG ha), fun hmem => hK.2 ?_⟩
  have := map_conj_mem_conjOrbit hmem (inv_mem ha)
  rwa [map_conj_map_conj_inv] at this

theorem mem_normalizer_outsideOrbit {A G J : Subgroup Γ}
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) {a : Γ} (ha : a ∈ A) :
    a ∈ Subgroup.normalizer ((outsideOrbit G A J : Subgroup Γ) : Set Γ) :=
  mem_normalizer_sSup (fun _ hK => map_conj_mem_lcal_diff hAG hK ha)
    (fun _ hK => map_conj_mem_lcal_diff hAG hK (inv_mem ha))

@[expose] def projX (G A J X : Subgroup Γ) : Subgroup Γ :=
  proj (orbitClosure J A) (outsideOrbit G A J) (X ⊓ kOf G)

theorem projX_le_orbitClosure (G A J X : Subgroup Γ) : projX G A J X ≤ orbitClosure J A :=
  proj_le_left _ _ _

theorem map_conj_eq_of_mem_normalizer {J : Subgroup Γ} {x : Γ}
    (hx : x ∈ Subgroup.normalizer (J : Set Γ)) : J.map (MulAut.conj x).toMonoidHom = J := by
  ext y
  rw [mem_map_conj_iff]
  have := Subgroup.mem_normalizer_iff.mp (inv_mem hx) y
  simpa using this.symm

theorem hypB_of_le {p : ℕ} {H Y : Subgroup Γ} [Finite Γ] (hH : signalizerMcBrideHypothesisB p H)
    (hYH : Y ≤ H) : signalizerMcBrideHypothesisB p Y :=
  ⟨hH.1, hH.2.1.coprime_dvd_right (Subgroup.card_dvd_of_le hYH),
    fun K L hK hL _ hs hnc => hH.2.2 K L (hK.trans hYH) hL hs hnc⟩

theorem isPGroup_of_isElemAbelian {p : ℕ} {A : Subgroup Γ} (hA : IsElemAbelian p A) :
    IsPGroup p A := CFSG.Open.IsElemAbelian.isPGroup hA

theorem eq_one_of_forall_commute {J : Subgroup Γ} [IsSimpleGroup J] (hnc : ¬ IsMulCommutative J)
    {j : Γ} (hj : j ∈ J) (hc : ∀ y ∈ J, y * j = j * y) : j = 1 := by
  have hcen : Subgroup.center ↥J = ⊥ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center ↥J) with h | h
    · exact h
    · exact absurd ((commutator_eq_bot_iff J).mp
        ((commutator_eq_bot_iff_center_eq_top (G := J)).mpr h)) hnc
  have hmem : (⟨j, hj⟩ : ↥J) ∈ Subgroup.center ↥J :=
    Subgroup.mem_center_iff.mpr fun g => Subtype.ext (hc g g.2)
  rw [hcen, Subgroup.mem_bot] at hmem
  simpa using congrArg Subtype.val hmem

theorem commutator_self_eq_of_isSimpleGroup {F : Subgroup Γ} [IsSimpleGroup F]
    (hnc : ¬ IsMulCommutative F) : ⁅F, F⁆ = F := by
  have h1 : _root_.commutator F = ⊤ := by
    rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (_root_.commutator F) with h | h
    · exact absurd ((commutator_eq_bot_iff F).mp h) hnc
    · exact h
  rw [← Subgroup.map_subtype_commutator, h1, Subgroup.map_top, Subgroup.range_subtype]

section Finite

variable [Finite Γ]

theorem mem_normalizer_kOf {G : Subgroup Γ} (hsol : sol G = ⊥) {g : Γ}
    (hg : g ∈ Subgroup.normalizer (G : Set Γ)) :
    g ∈ Subgroup.normalizer ((kOf G : Subgroup Γ) : Set Γ) := by
  have hK := isDirectProduct_lcal_kOf hsol
  rw [← hK.sSup_eq]
  exact mem_normalizer_sSup (fun _ hJ => map_conj_mem_lcal hJ hg)
    (fun _ hJ => map_conj_mem_lcal hJ (inv_mem hg))

theorem isDirectProduct_conjOrbit {A G J : Subgroup Γ} (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hJ : J ∈ lcal G) : IsDirectProduct (conjOrbit A J) (orbitClosure J A) :=
  isDirectProduct_orbit hAG hJ

theorem isDirectPair_orbitClosure_outsideOrbit {A G J : Subgroup Γ}
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G) :
    IsDirectPair (orbitClosure J A) (outsideOrbit G A J) (kOf G) := by
  have hK := isDirectProduct_lcal_kOf hsol
  have hL := isDirectProduct_conjOrbit hAG hJ
  have hsub : conjOrbit A J ⊆ lcal G := conjOrbit_subset_lcal hAG hJ
  have hLeq : sSup (conjOrbit A J) = orbitClosure J A := hL.sSup_eq
  refine ⟨?_, ?_, ?_⟩
  · rw [← hLeq]
    refine commute_of_forall_commute_sSup fun J₁ hJ₁ J₂ hJ₂ x hx y hy => ?_
    exact hK.commute J₁ (hsub hJ₁) J₂ hJ₂.1 (fun h => hJ₂.2 (h ▸ hJ₁)) x hx y hy
  · rw [eq_bot_iff]
    intro z hz
    obtain ⟨hzL, hzM⟩ := Subgroup.mem_inf.mp hz
    have hzL' : z ∈ sSup (conjOrbit A J) := hLeq ▸ hzL
    have hzK : z ∈ kOf G := hK.sSup_diff_le _ hsub hzL'
    have hone : (⟨z, hzK⟩ : kOf G) = 1 := by
      apply hK.ext_coord
      intro J'' hJ''
      rw [map_one, hK.coord_eq_one_iff hJ'']
      by_cases hmem : J'' ∈ conjOrbit A J
      · have hss : lcal G \ conjOrbit A J ⊆ lcal G \ {J''} :=
          Set.sdiff_subset_sdiff_right (Set.singleton_subset_iff.mpr hmem)
        exact sSup_le_sSup hss hzM
      · have hss : conjOrbit A J ⊆ lcal G \ {J''} := fun J₁ hJ₁ =>
          ⟨hsub hJ₁, fun h => hmem (h ▸ hJ₁)⟩
        exact sSup_le_sSup hss hzL'
    simpa using congrArg Subtype.val hone
  · rw [← hLeq, outsideOrbit, ← sSup_union, Set.union_sdiff_cancel hsub, hK.sSup_eq]

theorem orbitClosure_le_kOf {A G J : Subgroup Γ} (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hsol : sol G = ⊥) (hJ : J ∈ lcal G) : orbitClosure J A ≤ kOf G :=
  (isDirectPair_orbitClosure_outsideOrbit hAG hsol hJ).sup_eq ▸ le_sup_left

theorem outsideOrbit_le_centralizer {A G J : Subgroup Γ}
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G) :
    outsideOrbit G A J ≤ Subgroup.centralizer ((orbitClosure J A : Subgroup Γ) : Set Γ) := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  exact (isDirectPair_orbitClosure_outsideOrbit hAG hsol hJ).commute x hx y hy

theorem mem_normalizer_projX_of_mem {A G J X : Subgroup Γ}
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G)
    (hAX : A ≤ Subgroup.normalizer (X : Set Γ)) {a : Γ} (ha : a ∈ A) :
    a ∈ Subgroup.normalizer ((projX G A J X : Subgroup Γ) : Set Γ) :=
  mem_normalizer_proj_of_normalizes (isDirectPair_orbitClosure_outsideOrbit hAG hsol hJ).commute
    (mem_normalizer_orbitClosure ha) (mem_normalizer_outsideOrbit hAG ha)
    (mem_normalizer_inf (hAX ha) (mem_normalizer_kOf hsol (hAG ha)))

theorem smear_le_of_mem_lcal {A G J : Subgroup Γ} (hAG : A ≤ Subgroup.normalizer (G : Set Γ))
    (hsol : sol G = ⊥) (hJ : J ∈ lcal G) : smear J A ≤ G := fun _ hc =>
  kOf_le G (orbitClosure_le_kOf hAG hsol hJ (smear_le_orbitClosure J A hc))

theorem mem_normalizer_of_mem_smear {A G J X : Subgroup Γ}
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G)
    (hDX : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (X : Set Γ)) {c : Γ}
    (hc : c ∈ smear J A) : c ∈ Subgroup.normalizer (X : Set Γ) :=
  hDX (Subgroup.mem_inf.mpr ⟨smear_le_of_mem_lcal hAG hsol hJ hc, smear_le_centralizer J A hc⟩)

theorem commute_of_mem_orbitClosure {A G J : Subgroup Γ}
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G) {x y : Γ}
    (hx : x ∈ orbitClosure J A) (hy : y ∈ outsideOrbit G A J) : Commute x y :=
  (isDirectPair_orbitClosure_outsideOrbit hAG hsol hJ).commute x hx y hy

theorem mem_normalizer_projX_of_mem_smear {A G J X : Subgroup Γ}
    (hAG : A ≤ Subgroup.normalizer (G : Set Γ)) (hsol : sol G = ⊥) (hJ : J ∈ lcal G)
    (hDX : G ⊓ Subgroup.centralizer (A : Set Γ) ≤ Subgroup.normalizer (X : Set Γ)) {c : Γ}
    (hc : c ∈ smear J A) : c ∈ Subgroup.normalizer ((projX G A J X : Subgroup Γ) : Set Γ) := by
  have hcL : c ∈ orbitClosure J A := smear_le_orbitClosure J A hc
  have hcG : c ∈ G := smear_le_of_mem_lcal hAG hsol hJ hc
  have hcM : c ∈ Subgroup.centralizer ((outsideOrbit G A J : Subgroup Γ) : Set Γ) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (commute_of_mem_orbitClosure hAG hsol hJ hcL hy).symm.eq
  exact mem_normalizer_proj_of_normalizes
    (isDirectPair_orbitClosure_outsideOrbit hAG hsol hJ).commute
    (Subgroup.le_normalizer hcL) (Subgroup.centralizer_le_normalizer _ hcM)
    (mem_normalizer_inf (mem_normalizer_of_mem_smear hAG hsol hJ hDX hc)
      (mem_normalizer_kOf hsol (Subgroup.le_normalizer hcG)))

end Finite

end CFSG.SignalizerFunctorTheorem.McBride.Nonsolv.L514

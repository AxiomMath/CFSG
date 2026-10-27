module

public import CFSG.ClassicalGroups.Orthogonal.SixPlane.Basic
public import CFSG.LocalAnalysis.StandardType.GGQTwoDCells
public import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabDefs
public import CFSG.LocalAnalysis.StandardType.GGOrthFrameCore
public import CFSG.LocalAnalysis.StandardType.GGOrthRk1GenComb
import CFSG.ClassicalGroups.Orthogonal.SixPlane.Complete
import CFSG.ClassicalGroups.Orthogonal.SixPlane.Lift
import CFSG.ClassicalGroups.Orthogonal.SixPlane.Toral
public import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthChart
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameMain
import CFSG.LocalAnalysis.StandardType.GGLabelRigid
import CFSG.LocalAnalysis.StandardType.GGQTwoDCoxEven
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMSel
import CFSG.LocalAnalysis.StandardType.GGQTwoDTransport
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelModuleOfB2
import CFSG.LocalAnalysis.StandardType.GGQTwoDOrthBase
import CFSG.LocalAnalysis.StandardType.GGQTwoDRMStabSix
import CFSG.LocalAnalysis.StandardType.GGQTwoPThree
import CFSG.LocalAnalysis.StandardType.GGTypeANbrKappaBase
import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyAut
import CFSG.LocalAnalysis.StandardType.GGSecFiveKGPosBridge
import CFSG.LocalAnalysis.StandardType.GGQTwoDShared
import CFSG.LocalAnalysis.StandardType.GGQTwoDFrameStd
import CFSG.LocalAnalysis.StandardType.GGQTwoDFarSixChart
import CFSG.LocalAnalysis.StandardType.GGQTwoDSixPlaneGen
import CFSG.LocalAnalysis.StandardType.GGQTwoDSelBases

public section

namespace CFSG.StandardType.QTwo

open CFSG.ClassicalGroups.Orthogonal CFSG.StandardType.OrthTorus

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def GGQTwoSixPlaneGenInput : Prop :=
  ∀ S : Finset (Fin 6), S.card = 4 → SixPlane.supp 6 S ≤
    ⨆ (a : Fin 6) (b : Fin 6) (d : Fin 6) (_ : a ∈ S ∧ b ∈ S ∧ d ∈ S ∧ a ≠ b ∧ a ≠ d ∧ b ≠ d)
      (u : ℕ) (w : ℕ) (_ : (u = 1 ∨ u = 2) ∧ (w = 1 ∨ w = 2)),
      Subgroup.closure {z | z ∈ SixPlane.supp 6 {a, b, d} ∧ (∃ k : ℕ, z ^ 2 ^ k = 1) ∧
        Commute z (SixPlane.rot 6 a ^ u * SixPlane.rot 6 b * SixPlane.rot 6 d ^ w)}

theorem ggQTwoSixPlaneGenInput_holds : GGQTwoSixPlaneGenInput := fun _ hS =>
  supp_le_iSup_signedTriple hS

section Charts

variable {G : Type} [Group G]

@[expose] def sixEdgeSupp (i k : Fin 6) : Finset (Fin 6) :=
  {simpleLo i, simpleHi i, simpleLo k, simpleHi k}

theorem disjoint_sixEdgeSupp (i k j l : Fin 6) (hik : ggCoxeterMatrixD 6 i k = 3)
    (hjl : ggCoxeterMatrixD 6 j l = 3) (hij : ggCoxeterMatrixD 6 i j = 2)
    (hil : ggCoxeterMatrixD 6 i l = 2) (hkj : ggCoxeterMatrixD 6 k j = 2)
    (hkl : ggCoxeterMatrixD 6 k l = 2) : Disjoint (sixEdgeSupp i k) (sixEdgeSupp j l) := by
  have h : ∀ q : Fin 6 × Fin 6 × Fin 6 × Fin 6, ggCoxeterMatrixD 6 q.1 q.2.1 = 3 →
      ggCoxeterMatrixD 6 q.2.2.1 q.2.2.2 = 3 → ggCoxeterMatrixD 6 q.1 q.2.2.1 = 2 →
      ggCoxeterMatrixD 6 q.1 q.2.2.2 = 2 → ggCoxeterMatrixD 6 q.2.1 q.2.2.1 = 2 →
      ggCoxeterMatrixD 6 q.2.1 q.2.2.2 = 2 →
        Disjoint (sixEdgeSupp q.1 q.2.1) (sixEdgeSupp q.2.2.1 q.2.2.2) := by
    decide +kernel
  exact h (i, k, j, l) hik hjl hij hil hkj hkl

theorem card_sixEdgeSupp (i k : Fin 6) (hik : ggCoxeterMatrixD 6 i k = 3) :
    (sixEdgeSupp i k).card = 3 := by
  have h : ∀ q : Fin 6 × Fin 6, ggCoxeterMatrixD 6 q.1 q.2 = 3 →
      (sixEdgeSupp q.1 q.2).card = 3 := by
    decide +kernel
  exact h (i, k) hik

theorem ggRankTwo_le_range_supp {Bs : Subgroup G} {A T : Finset (Fin 6)}
    (ψ : ↥(SixPlane.supp 6 A) →* G) (hψ : Function.Injective ψ) (b : Fin 6 → G)
    (hb : ∀ j (hj : j ∈ A), ψ ⟨SixPlane.rot 6 j, SixPlane.rot_mem_supp hj⟩ = b j) (hTA : T ⊆ A)
    {r r' : MulAut ↥Bs} (hH : ∀ j ∈ A, j ∉ T → b j ∈ ggHyperplane Bs r ⊓ ggHyperplane Bs r')
    (hle : ggRankTwo Bs r r' ≤ ψ.range) :
    ggRankTwo Bs r r' ≤ (ψ.comp (Subgroup.inclusion (SixPlane.supp_mono hTA))).range := by
  rw [ggRankTwo, ggOTwoPrime, Subgroup.closure_le]
  rintro y ⟨hyC, k, hyk⟩
  obtain ⟨z, rfl⟩ := hle (Subgroup.subset_closure ⟨hyC, k, hyk⟩)
  have hz2 : (z : SixPlane.V 6 ≃ₗ[ZMod 2] SixPlane.V 6) ^ (2 ^ k) = 1 := by
    have h : z ^ (2 ^ k) = 1 := hψ (by rw [map_pow, hyk, map_one])
    simpa using congrArg Subtype.val h
  have hc : ∀ j ∈ A, j ∉ T →
      Commute (z : SixPlane.V 6 ≃ₗ[ZMod 2] SixPlane.V 6) (SixPlane.rot 6 j) := by
    intro j hjA hjT
    have h1 : b j * ψ z = ψ z * b j := Subgroup.mem_centralizer_iff.mp hyC (b j) (hH j hjA hjT)
    have h2 : z * ⟨SixPlane.rot 6 j, SixPlane.rot_mem_supp hjA⟩ =
        ⟨SixPlane.rot 6 j, SixPlane.rot_mem_supp hjA⟩ * z :=
      hψ (by rw [map_mul, map_mul, hb j hjA, h1])
    exact congrArg Subtype.val h2
  exact ⟨⟨z, SixPlane.mem_supp_of_two_of_commute_rot z.2 hz2 hc⟩, rfl⟩

theorem qtwoFar_six_of_charts {Bs : Subgroup G} (r : Fin 6 → MulAut ↥Bs)
    (ψ : ∀ A : Finset (Fin 6), A.card = 5 → ↥(SixPlane.supp 6 A) →* G)
    (hinj : ∀ (A : Finset (Fin 6)) (hA : A.card = 5), Function.Injective (ψ A hA))
    (himg : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : SixPlane.V 6 ≃ₗ[ZMod 2] SixPlane.V 6) (hgA : g ∈ SixPlane.supp 6 A),
        g ∈ SixPlane.supp 6 B →
          ∃ (g' : SixPlane.V 6 ≃ₗ[ZMod 2] SixPlane.V 6) (hg'B : g' ∈ SixPlane.supp 6 B),
            g' ∈ SixPlane.supp 6 A ∧ ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨g', hg'B⟩)
    (htor : ∀ (A B : Finset (Fin 6)) (hA : A.card = 5) (hB : B.card = 5)
      (g : SixPlane.V 6 ≃ₗ[ZMod 2] SixPlane.V 6) (hgA : g ∈ SixPlane.supp 6 A)
      (hgB : g ∈ SixPlane.supp 6 B),
        g ∈ SixPlane.torus 6 Finset.univ → ψ A hA ⟨g, hgA⟩ = ψ B hB ⟨g, hgB⟩)
    (hloc : ∀ i k : Fin 6, ggCoxeterMatrixD 6 i k = 3 → ∀ (A : Finset (Fin 6)) (hA : A.card = 5)
      (hT : sixEdgeSupp i k ⊆ A),
        qtwoW Bs r i k ≤ ((ψ A hA).comp (Subgroup.inclusion (SixPlane.supp_mono hT))).range)
    (i k j l : Fin 6) (hik : ggCoxeterMatrixD 6 i k = 3) (hjl : ggCoxeterMatrixD 6 j l = 3)
    (hij : ggCoxeterMatrixD 6 i j = 2) (hil : ggCoxeterMatrixD 6 i l = 2)
    (hkj : ggCoxeterMatrixD 6 k j = 2) (hkl : ggCoxeterMatrixD 6 k l = 2) :
    ∀ y ∈ qtwoW Bs r i k, ∀ z ∈ qtwoW Bs r j l, y * z = z * y := by
  classical
  have hdisj := disjoint_sixEdgeSupp i k j l hik hjl hij hil hkj hkl
  obtain ⟨c, hc⟩ : ∃ c, c ∈ sixEdgeSupp j l := ⟨simpleLo j, by simp [sixEdgeSupp]⟩
  obtain ⟨c', hc'⟩ : ∃ c', c' ∈ sixEdgeSupp i k := ⟨simpleLo i, by simp [sixEdgeSupp]⟩
  have hA : (Finset.univ.erase c).card = 5 := by simp
  have hB : (Finset.univ.erase c').card = 5 := by simp
  have hTA : sixEdgeSupp i k ⊆ Finset.univ.erase c := fun t ht =>
    Finset.mem_erase.mpr ⟨fun h => Finset.disjoint_left.mp hdisj (h ▸ ht) hc,
      Finset.mem_univ t⟩
  have hTB : sixEdgeSupp j l ⊆ Finset.univ.erase c' := fun t ht =>
    Finset.mem_erase.mpr ⟨fun h => Finset.disjoint_left.mp hdisj hc' (h ▸ ht),
      Finset.mem_univ t⟩
  intro y hy z hz
  obtain ⟨⟨x, hx⟩, rfl⟩ := MonoidHom.mem_range.mp (hloc i k hik _ hA hTA hy)
  obtain ⟨⟨x', hx'⟩, rfl⟩ := MonoidHom.mem_range.mp (hloc j l hjl _ hB hTB hz)
  exact (SixPlane.commute_of_charts ψ hinj himg htor hA hB hTA hTB hdisj hx hx').eq

end Charts

section Orth

variable {G : Type} [Group G]

@[expose] noncomputable def qtwoCoord {Bs : Subgroup G} {m : ℕ} (β : Additive ↥Bs ≃+ DVec m)
    (i : Fin m) : G :=
  ((Additive.toMul (β.symm (Pi.single i 1)) : ↥Bs) : G)

@[expose] noncomputable def qtwoFarY (Bs : Subgroup G) {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    (M : CoxeterMatrix ι) (e : M.Group ≃* ↥A) (β : Additive ↥Bs ≃+ DVec 6)
    (S : Finset (Fin 6)) : Subgroup G :=
  ⨆ (r : MulAut ↥Bs)
    (_ : r ∈ ggCoxRefl M e ∧ ∀ l ∉ S, ggLin (p := 3) β r (Pi.single l 1) = Pi.single l 1)
    (r' : MulAut ↥Bs)
    (_ : r' ∈ ggCoxRefl M e ∧ ∀ l ∉ S, ggLin (p := 3) β r' (Pi.single l 1) = Pi.single l 1)
    (_ : r * r' ≠ r' * r), ggRankTwo Bs r r'

private theorem qtwoFarY_mem_conj {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A} (β : Additive ↥Bs ≃+ DVec 6) {b : MulAut ↥Bs}
    (hbA : b ∈ A) (τ : Equiv.Perm (Fin 6)) (hτ : ggLin (p := 3) β b = dPerm 6 τ)
    {S : Finset (Fin 6)} {r : MulAut ↥Bs}
    (hr : r ∈ ggCoxRefl M e ∧ ∀ l ∉ S, ggLin (p := 3) β r (Pi.single l 1) = Pi.single l 1) :
    b * r * b⁻¹ ∈ ggCoxRefl M e ∧ ∀ l ∉ S.map τ.toEmbedding,
      ggLin (p := 3) β (b * r * b⁻¹) (Pi.single l 1) = Pi.single l 1 := by
  obtain ⟨⟨w, i, rfl⟩, hfix⟩ := hr
  refine ⟨⟨e.symm ⟨b, hbA⟩ * w, i, ?_⟩, fun l hl => ?_⟩
  · simp only [map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv, MulEquiv.apply_symm_apply,
      mul_inv_rev]
    group
  · have hD : ∀ k, dPerm 6 τ (Pi.single k 1) = Pi.single (τ k) 1 := fun k => by
      simpa using dPerm_apply 6 τ k
    have hDinv : (dPerm 6 τ)⁻¹ (Pi.single l 1) = Pi.single (τ.symm l) 1 := by
      have h := hD (τ.symm l)
      rw [Equiv.apply_symm_apply] at h
      rw [← h, ← LinearEquiv.mul_apply, inv_mul_cancel]
      rfl
    have hl' : τ.symm l ∉ S := fun h => hl (Finset.mem_map_equiv.mpr h)
    rw [map_mul, map_mul, map_inv, hτ, LinearEquiv.mul_apply, LinearEquiv.mul_apply, hDinv,
      hfix _ hl', hD, Equiv.apply_symm_apply]

private theorem qtwo_conj_mul_ne {H : Type} [Group H] (c : H) {r r' : H} (h : r * r' ≠ r' * r) :
    c * r * c⁻¹ * (c * r' * c⁻¹) ≠ c * r' * c⁻¹ * (c * r * c⁻¹) := by
  intro h'
  apply h
  have e1 : c * r * c⁻¹ * (c * r' * c⁻¹) = c * (r * r') * c⁻¹ := by group
  have e2 : c * r' * c⁻¹ * (c * r * c⁻¹) = c * (r' * r) * c⁻¹ := by group
  rw [e1, e2] at h'
  exact mul_left_cancel (mul_right_cancel h')

theorem qtwoFarY_map_conj [Finite G] {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥A} (β : Additive ↥Bs ≃+ DVec 6) {g : G}
    {a : MulAut ↥Bs} (haA : a ∈ A) (ha : ∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹)
    (σ : Equiv.Perm (Fin 6)) (hσ : ggLin (p := 3) β a = dPerm 6 σ) (S : Finset (Fin 6)) :
    (qtwoFarY Bs M e β S).map (MulAut.conj g).toMonoidHom =
      qtwoFarY Bs M e β (S.map σ.toEmbedding) := by
  classical
  have hσ' : ggLin (p := 3) β a⁻¹ = dPerm 6 σ⁻¹ := by
    rw [map_inv, hσ]
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← dPerm_mul, mul_inv_cancel, dPerm_one]
  have hSS : (S.map σ.toEmbedding).map σ⁻¹.toEmbedding = S := by
    rw [Finset.map_map]
    ext x
    simp
  rw [qtwoFarY, qtwoFarY]
  simp only [Subgroup.map_iSup, ggRankTwo_map_conj ha]
  apply le_antisymm
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun r' => iSup_le fun hr' =>
      iSup_le fun hne => ?_
    exact le_iSup_of_le (a * r * a⁻¹) (le_iSup_of_le (qtwoFarY_mem_conj β haA σ hσ hr)
      (le_iSup_of_le (a * r' * a⁻¹) (le_iSup_of_le (qtwoFarY_mem_conj β haA σ hσ hr')
        (le_iSup_of_le (qtwo_conj_mul_ne a hne) le_rfl))))
  · refine iSup_le fun r => iSup_le fun hr => iSup_le fun r' => iSup_le fun hr' =>
      iSup_le fun hne => ?_
    have h1 := qtwoFarY_mem_conj β (A.inv_mem haA) σ⁻¹ hσ' hr
    have h2 := qtwoFarY_mem_conj β (A.inv_mem haA) σ⁻¹ hσ' hr'
    rw [hSS] at h1 h2
    have hr0 : a * (a⁻¹ * r * a⁻¹⁻¹) * a⁻¹ = r := by group
    have hr0' : a * (a⁻¹ * r' * a⁻¹⁻¹) * a⁻¹ = r' := by group
    refine le_iSup_of_le (a⁻¹ * r * a⁻¹⁻¹) (le_iSup_of_le h1 (le_iSup_of_le (a⁻¹ * r' * a⁻¹⁻¹)
      (le_iSup_of_le h2 (le_iSup_of_le (qtwo_conj_mul_ne a⁻¹ hne) ?_))))
    rw [hr0, hr0']

theorem qtwoFarSix_exists_perm (i₀ : Fin 6) :
    ∃ σ : Finset (Fin 6) → Equiv.Perm (Fin 6), ∀ A : Finset (Fin 6), A.card = 5 →
      (Finset.univ.erase i₀).map (σ A).toEmbedding = A := by
  classical
  have h : ∀ A : Finset (Fin 6), ∃ τ : Equiv.Perm (Fin 6), A.card = 5 →
      (Finset.univ.erase i₀).map τ.toEmbedding = A := by
    intro A
    by_cases hA : A.card = 5
    · obtain ⟨a, -, ha⟩ : ∃ a, a ∈ (Finset.univ : Finset (Fin 6)) ∧ a ∉ A :=
        Finset.exists_mem_notMem_of_card_lt_card (by simp [hA])
      have hAa : A = Finset.univ.erase a :=
        Finset.eq_of_subset_of_card_le
          (fun x hx => Finset.mem_erase.mpr ⟨fun hxa => ha (hxa ▸ hx), Finset.mem_univ x⟩)
          (by simp [hA])
      refine ⟨Equiv.swap i₀ a, fun _ => ?_⟩
      rw [Finset.map_erase, Finset.map_univ_equiv, hAa]
      simp
    · exact ⟨1, fun h => absurd h hA⟩
  choose σ hσ using h
  exact ⟨σ, hσ⟩

theorem qtwoFarSix_exists_lift [Finite G] {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (e' : Fin 6 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 6).reindex e') (β : Additive ↥Bs ≃+ DVec 6)
    (hβ : ∀ (t : Fin 6) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau 6 (decide (t.val + 1 = 6)) (simpleLo t) (simpleHi t) (β (Additive.ofMul s)))
    (σ : Equiv.Perm (Fin 6)) :
    ∃ (g : G) (a : MulAut ↥Bs), a ∈ ggAutomizerJoin L Bs 𝒦 ∧
      g ∈ Subgroup.normalizer (Bs : Set G) ∧ (∀ b : ↥Bs, ((a b : ↥Bs) : G) = g * b * g⁻¹) ∧
      ggLin (p := 3) β a = dPerm 6 σ := by
  have hmem : dPerm 6 σ ∈ (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := 3) β) := by
    rw [qtwoD_image_eq (by norm_num) hM β hβ]
    exact dPerm_mem_dEven 6 σ
  obtain ⟨a, haJ, hlin⟩ := hmem
  obtain ⟨g, -, hgN, hga⟩ := exists_lift_of_mem_ggAutomizerJoin haJ
  exact ⟨g, a, haJ, hgN, hga, hlin⟩

private theorem qtwoFarSix_refl_fix {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} {e' : Fin 6 ≃ ι}
    (β : Additive ↥Bs ≃+ DVec 6)
    (hβ : ∀ (t : Fin 6) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau 6 (decide (t.val + 1 = 6)) (simpleLo t) (simpleHi t) (β (Additive.ofMul s)))
    {t l : Fin 6} (hlo : l ≠ simpleLo t) (hhi : l ≠ simpleHi t) :
    ggLin (p := 3) β (qtwoRefl e e' t) (Pi.single l 1) = Pi.single l 1 := by
  rw [ggLin_apply, qtwoRefl, hβ t, ofMul_toMul, AddEquiv.apply_symm_apply]
  simpa using dTau_apply_of_ne 6 (decide (t.val + 1 = 6)) hlo hhi

private theorem qtwoCoord_mem_hyperplane {Bs : Subgroup G} (β : Additive ↥Bs ≃+ DVec 6)
    {r : MulAut ↥Bs} {l : Fin 6}
    (h : ggLin (p := 3) β r (Pi.single l 1) = Pi.single l 1) :
    qtwoCoord β l ∈ ggHyperplane Bs r := by
  refine ⟨Additive.toMul (β.symm (Pi.single l 1)), ?_, rfl⟩
  rw [ggLin_apply] at h
  have h' := congrArg β.symm h
  rw [AddEquiv.symm_apply_apply] at h'
  exact congrArg Additive.toMul h'

private theorem qtwoRefl_mul_ne {Bs : Subgroup G} {A : Subgroup (MulAut ↥Bs)} {ι : Type}
    {M : CoxeterMatrix ι} (e : M.Group ≃* ↥A) (e' : Fin 6 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 6).reindex e') {i k : Fin 6}
    (hik : ggCoxeterMatrixD 6 i k = 3) :
    qtwoRefl e e' i * qtwoRefl e e' k ≠ qtwoRefl e e' k * qtwoRefl e e' i := by
  intro h
  have h1 : M.simple (e' i) * M.simple (e' k) = M.simple (e' k) * M.simple (e' i) := by
    apply e.injective
    apply Subtype.ext
    simpa [qtwoRefl] using h
  have hs : ∀ t, M.simple t * M.simple t = 1 := fun t => by
    simpa using M.toCoxeterSystem.simple_mul_simple_self t
  have h2 : (M.simple (e' i) * M.simple (e' k)) ^ 2 = 1 := by
    rw [pow_two, mul_assoc, ← mul_assoc (M.simple (e' k)), ← h1, ← mul_assoc, ← mul_assoc,
      hs, one_mul, hs]
  have hord := M.toCoxeterSystem.orderOf_simple_mul_simple (e' i) (e' k)
  rw [CoxeterMatrix.toCoxeterSystem_simple] at hord
  have hMik : M.M (e' i) (e' k) = 3 := by
    subst hM
    simpa [CoxeterMatrix.reindex] using hik
  have h3 : orderOf (M.simple (e' i) * M.simple (e' k)) ∣ 2 := orderOf_dvd_of_pow_eq_one h2
  rw [hord, hMik] at h3
  omega

private theorem qtwoFarSix_exists_perm_pair {x y a b : Fin 6} (hxy : x ≠ y) (hab : a ≠ b) :
    ∃ π : Equiv.Perm (Fin 6), π x = a ∧ π y = b := by
  refine ⟨Equiv.swap (Equiv.swap x a y) b * Equiv.swap x a, ?_, ?_⟩
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]
    refine Equiv.swap_apply_of_ne_of_ne (fun h => hxy ?_) hab
    have h' := congrArg (Equiv.swap x a) h
    rwa [Equiv.swap_apply_self, Equiv.swap_apply_right] at h'
  · rw [Equiv.Perm.mul_apply, Equiv.swap_apply_left]

private theorem qtwoFarSix_exists_refl {L Bs : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (e' : Fin 6 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 6).reindex e') (β : Additive ↥Bs ≃+ DVec 6)
    (hβ : ∀ (t : Fin 6) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau 6 (decide (t.val + 1 = 6)) (simpleLo t) (simpleHi t) (β (Additive.ofMul s)))
    (ε : Bool) {a b : Fin 6} (hab : a ≠ b) :
    ∃ r ∈ ggCoxRefl M e, ggLin (p := 3) β r = dTau 6 ε a b := by
  obtain ⟨t, hε, hlh⟩ : ∃ t : Fin 6, decide (t.val + 1 = 6) = ε ∧ simpleLo t ≠ simpleHi t := by
    cases ε
    · exact ⟨0, by decide⟩
    · exact ⟨5, by decide⟩
  obtain ⟨π, hπa, hπb⟩ := qtwoFarSix_exists_perm_pair hlh hab
  have hmem : dPerm 6 π ∈ (ggAutomizerJoin L Bs 𝒦).map (ggLin (p := 3) β) := by
    rw [qtwoD_image_eq (by norm_num) hM β hβ]
    exact dPerm_mem_dEven 6 π
  obtain ⟨g, hgA, hg⟩ := hmem
  have hs : ggLin (p := 3) β ((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) =
      dTau 6 ε (simpleLo t) (simpleHi t) := by
    refine LinearEquiv.ext fun v => ?_
    rw [ggLin_apply, hβ, ofMul_toMul, AddEquiv.apply_symm_apply, hε]
  have hw : ((e (e.symm ⟨g, hgA⟩) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) = g := by
    rw [MulEquiv.apply_symm_apply]
  refine ⟨_, ⟨e.symm ⟨g, hgA⟩, e' t, rfl⟩, ?_⟩
  rw [map_mul, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, hw,
    map_mul, map_mul, map_inv, hg, hs, dPerm_conj_dTau, hπa, hπb]

private theorem qtwoFarSix_dTau_mul_ne (ε ε' : Bool) {a b d : Fin 6} (hab : a ≠ b) (had : a ≠ d)
    (hbd : b ≠ d) : dTau 6 ε a b * dTau 6 ε' d b ≠ dTau 6 ε' d b * dTau 6 ε a b := by
  intro h
  have h1 := congrArg (fun f : DVec 6 ≃ₗ[ZMod 3] DVec 6 => f (dBasis 6 b) d) h
  simp only [LinearEquiv.mul_apply, dTau_apply_right 6 _ hab, dTau_apply_right 6 _ hbd.symm,
    map_smul, dTau_apply_of_ne 6 _ had.symm hbd.symm, dTau_apply_of_ne 6 _ had hab] at h1
  cases ε <;> cases ε' <;> simp [had] at h1

private def qtwoCommSub {Bs : Subgroup G} {m : ℕ} (β : Additive ↥Bs ≃+ DVec m) (y : G) :
    AddSubgroup (DVec m) where
  carrier := {v | Commute y ((Additive.toMul (β.symm v) : ↥Bs) : G)}
  add_mem' {v w} hv hw := by
    simp only [Set.mem_setOf_eq, map_add, toMul_add, Subgroup.coe_mul] at hv hw ⊢
    exact hv.mul_right hw
  zero_mem' := by simp
  neg_mem' {v} hv := by
    simp only [Set.mem_setOf_eq, map_neg, toMul_neg, Subgroup.coe_inv] at hv ⊢
    exact hv.inv_right

private theorem qtwoCommSub_smul_mem {Bs : Subgroup G} {m : ℕ} (β : Additive ↥Bs ≃+ DVec m)
    (y : G) (k : ZMod 3) {v : DVec m} (hv : v ∈ qtwoCommSub β y) : k • v ∈ qtwoCommSub β y := by
  rw [← ZMod.natCast_zmod_val k, Nat.cast_smul_eq_nsmul]
  exact AddSubgroup.nsmul_mem _ hv _

theorem le_centralizer_qtwoCoord {Bs Y : Subgroup G} {m : ℕ} (β : Additive ↥Bs ≃+ DVec m) {x : G}
    (hx : x ∈ Bs) {i₀ : Fin m} {c : ZMod 3} (hc : c ≠ 0)
    (hxc : β (Additive.ofMul ⟨x, hx⟩) = c • Pi.single i₀ 1)
    (hY : Y ≤ Subgroup.centralizer {x}) : Y ≤ Subgroup.centralizer {qtwoCoord β i₀} := by
  intro y hy
  rw [Subgroup.mem_centralizer_iff]
  rintro _ rfl
  have hxy : β (Additive.ofMul ⟨x, hx⟩) ∈ qtwoCommSub β y := by
    change Commute y ((Additive.toMul (β.symm (β (Additive.ofMul ⟨x, hx⟩))) : ↥Bs) : G)
    rw [AddEquiv.symm_apply_apply, toMul_ofMul]
    exact (Subgroup.mem_centralizer_iff.mp (hY hy) x (Set.mem_singleton x)).symm
  have hcc : ∀ c : ZMod 3, c ≠ 0 → c * c = 1 := by decide
  have h := qtwoCommSub_smul_mem β y c hxy
  rw [hxc, smul_smul, hcc c hc, one_smul] at h
  have h' : Commute y (qtwoCoord β i₀) := h
  exact h'.eq.symm

theorem qtwoFarSix_map_supp_eq {L Bs Y : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type}
    {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (e' : Fin 6 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 6).reindex e') (β : Additive ↥Bs ≃+ DVec 6)
    (hβ : ∀ (t : Fin 6) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau 6 (decide (t.val + 1 = 6)) (simpleLo t) (simpleHi t) (β (Additive.ofMul s)))
    {i₀ : Fin 6}
    (hAe : dEvenStab 6 (Pi.single i₀ 1) ≤ (ggAutomizer Y Bs).map (ggLin (p := 3) β))
    (hamb : ∀ r ∈ ggAutomizer Y Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer Y Bs,
      r' ∈ ggCoxRefl M e → r * r' ≠ r' * r → ggRankTwo Bs r r' ≤ Y)
    (hYc : Y ≤ Subgroup.centralizer {qtwoCoord β i₀})
    (φ₀ : ↥(SixPlane.supp 6 (Finset.univ.erase i₀)) →* G) (hφ₀ : Function.Injective φ₀)
    (hrange : φ₀.range = Y)
    (hrot : ∀ i (hi : i ∈ Finset.univ.erase i₀),
      φ₀ ⟨SixPlane.rot 6 i, SixPlane.rot_mem_supp hi⟩ = qtwoCoord β i)
    (hgen : GGQTwoSixPlaneGenInput)
    {S : Finset (Fin 6)} (hS : S ⊆ Finset.univ.erase i₀) (hS4 : S.card = 4) :
    ((SixPlane.supp 6 S).subgroupOf (SixPlane.supp 6 (Finset.univ.erase i₀))).map φ₀ =
      qtwoFarY Bs M e β S := by
  have hi₀S : i₀ ∉ S := fun h => (Finset.mem_erase.mp (hS h)).1 rfl
  refine le_antisymm ?_ ?_
  · rw [Subgroup.map_le_iff_le_comap]
    have hK : SixPlane.supp 6 S ≤ ((qtwoFarY Bs M e β S).comap φ₀).map
        (SixPlane.supp 6 (Finset.univ.erase i₀)).subtype := by
      refine (hgen S hS4).trans (iSup_le fun a => iSup_le fun b =>
        iSup_le fun d => iSup_le fun hT => iSup_le fun u => iSup_le fun w =>
        iSup_le fun huw => ?_)
      obtain ⟨haS, hbS, hdS, hab, had, hbd⟩ := hT
      rw [Subgroup.closure_le]
      rintro z ⟨hzT, ⟨k, hk⟩, hzt⟩
      have hTA : ({a, b, d} : Finset (Fin 6)) ⊆ Finset.univ.erase i₀ := by
        intro j hj
        simp only [Finset.mem_insert, Finset.mem_singleton] at hj
        rcases hj with rfl | rfl | rfl
        · exact hS haS
        · exact hS hbS
        · exact hS hdS
      have hzA : z ∈ SixPlane.supp 6 (Finset.univ.erase i₀) := SixPlane.supp_mono hTA hzT
      refine ⟨⟨z, hzA⟩, ?_, rfl⟩
      change φ₀ ⟨z, hzA⟩ ∈ qtwoFarY Bs M e β S
      obtain ⟨r, hr, hrl⟩ := qtwoFarSix_exists_refl e' hM β hβ (decide (u = 2)) hab
      obtain ⟨r', hr', hr'l⟩ := qtwoFarSix_exists_refl e' hM β hβ (decide (w = 2)) hbd.symm
      have hfixS : ∀ {x x' : Fin 6} {ε : Bool} {q : MulAut ↥Bs},
          ggLin (p := 3) β q = dTau 6 ε x x' → x ∈ S → x' ∈ S →
            ∀ l ∉ S, ggLin (p := 3) β q (Pi.single l 1) = Pi.single l 1 := by
        intro x x' ε q hq hx hx' l hl
        rw [hq]
        simpa using dTau_apply_of_ne 6 ε (a := x) (b := x') (i := l)
          (by rintro rfl; exact hl hx) (by rintro rfl; exact hl hx')
      have hne : r * r' ≠ r' * r := by
        intro h
        have h' := congrArg (ggLin (p := 3) β) h
        rw [map_mul, map_mul, hrl, hr'l] at h'
        exact qtwoFarSix_dTau_mul_ne _ _ hab had hbd h'
      have hW : ggRankTwo Bs r r' ≤ qtwoFarY Bs M e β S :=
        le_iSup_of_le r (le_iSup_of_le ⟨hr, hfixS hrl haS hbS⟩ (le_iSup_of_le r'
          (le_iSup_of_le ⟨hr', hfixS hr'l hdS hbS⟩ (le_iSup_of_le hne le_rfl))))
      refine hW (Subgroup.subset_closure ⟨?_, k, ?_⟩)
      · rw [Subgroup.mem_centralizer_iff]
        rintro h ⟨⟨s, hs, rfl⟩, ⟨s', hs', hss⟩⟩
        obtain rfl : s = s' := (Subtype.ext hss).symm
        have hfix : ∀ {q : MulAut ↥Bs} {x x' : Fin 6} {ε : Bool}, q s = s →
            ggLin (p := 3) β q = dTau 6 ε x x' → x ≠ x' →
              β (Additive.ofMul s) x = dSgn ε * β (Additive.ofMul s) x' := by
          intro q x x' ε hq hql hxx'
          have h1 := (ggLin_fix_iff (p := 3) β q s).mp hq
          rw [hql] at h1
          exact (dTau_apply_eq_self_iff 6 ε hxx' _).mp h1
        have hsgn : ∀ n : ℕ, n = 1 ∨ n = 2 → dSgn (decide (n = 2)) = (n : ZMod 3) := by
          rintro n (rfl | rfl) <;> decide
        obtain ⟨v, hv⟩ : ∃ v, v = β (Additive.ofMul s) := ⟨_, rfl⟩
        have hva : v a = (u : ZMod 3) * v b := by
          rw [hv, hfix hs hrl hab, hsgn u huw.1]
        have hvd : v d = (w : ZMod 3) * v b := by
          rw [hv, hfix hs' hr'l hbd.symm, hsgn w huw.2]
        have hsingle : ∀ l, l ≠ a → l ≠ b → l ≠ d →
            Pi.single l (1 : ZMod 3) ∈ qtwoCommSub β (φ₀ ⟨z, hzA⟩) := by
          intro l hla hlb hld
          by_cases hl0 : l = i₀
          · subst hl0
            have hzY : φ₀ ⟨z, hzA⟩ ∈ Y := by
              rw [← hrange]
              exact ⟨⟨z, hzA⟩, rfl⟩
            exact (Subgroup.mem_centralizer_iff.mp (hYc hzY) _ (Set.mem_singleton _)).symm
          · have hlA : l ∈ Finset.univ.erase i₀ := Finset.mem_erase.mpr ⟨hl0, Finset.mem_univ l⟩
            have hc : Commute z (SixPlane.rot 6 l) :=
              SixPlane.commute_of_mem_supp_of_disjoint
                (Finset.disjoint_singleton_right.mpr (by simp [hla, hlb, hld]))
                hzT (SixPlane.rot_mem_supp (Finset.mem_singleton_self l))
            have hc' : Commute (⟨z, hzA⟩ : ↥(SixPlane.supp 6 (Finset.univ.erase i₀)))
                ⟨SixPlane.rot 6 l, SixPlane.rot_mem_supp hlA⟩ := Subtype.ext hc.eq
            have h2 := hc'.map φ₀
            rw [hrot l hlA] at h2
            exact h2
        obtain ⟨s₀, hs₀⟩ : ∃ s₀ : DVec 6,
            s₀ = (u : ZMod 3) • Pi.single a 1 + Pi.single b 1 + (w : ZMod 3) • Pi.single d 1 :=
          ⟨_, rfl⟩
        have hs₀H : s₀ ∈ qtwoCommSub β (φ₀ ⟨z, hzA⟩) := by
          have he : ((Additive.toMul (β.symm s₀) : ↥Bs) : G) =
              φ₀ (⟨SixPlane.rot 6 a, SixPlane.rot_mem_supp (hS haS)⟩ ^ u *
                ⟨SixPlane.rot 6 b, SixPlane.rot_mem_supp (hS hbS)⟩ *
                ⟨SixPlane.rot 6 d, SixPlane.rot_mem_supp (hS hdS)⟩ ^ w) := by
            rw [map_mul, map_mul, map_pow, map_pow, hrot a (hS haS), hrot b (hS hbS),
              hrot d (hS hdS), hs₀]
            simp only [Nat.cast_smul_eq_nsmul, map_add, map_nsmul, toMul_add, toMul_nsmul,
              Subgroup.coe_mul, SubmonoidClass.coe_pow]
            rfl
          change Commute _ ((Additive.toMul (β.symm s₀) : ↥Bs) : G)
          rw [he]
          refine Commute.map ?_ φ₀
          apply Subtype.ext
          simp only [Subgroup.coe_mul, SubmonoidClass.coe_pow]
          exact hzt.eq
        have hrest : v - v b • s₀ ∈ qtwoCommSub β (φ₀ ⟨z, hzA⟩) := by
          rw [← Finset.univ_sum_single (v - v b • s₀)]
          refine AddSubgroup.sum_mem _ fun i _ => ?_
          by_cases hT : i = a ∨ i = b ∨ i = d
          · have h0 : (v - v b • s₀) i = 0 := by
              rcases hT with rfl | rfl | rfl
              · simp [hs₀, hab, had, hva, mul_comm]
              · simp [hs₀, hab.symm, hbd]
              · simp [hs₀, had.symm, hbd.symm, hvd, mul_comm]
            rw [h0, Pi.single_zero]
            exact AddSubgroup.zero_mem _
          · simp only [not_or] at hT
            have h1 : Pi.single i ((v - v b • s₀) i) =
                (v - v b • s₀) i • Pi.single i (1 : ZMod 3) := by
              ext j
              simp [Pi.single_apply]
            rw [h1]
            exact qtwoCommSub_smul_mem β _ _ (hsingle i hT.1 hT.2.1 hT.2.2)
        have hvH : v ∈ qtwoCommSub β (φ₀ ⟨z, hzA⟩) := by
          have h3 := AddSubgroup.add_mem _ (qtwoCommSub_smul_mem β _ (v b) hs₀H) hrest
          rwa [add_sub_cancel] at h3
        have hc : Commute (φ₀ ⟨z, hzA⟩) ((Additive.toMul (β.symm v) : ↥Bs) : G) := hvH
        rw [hv, AddEquiv.symm_apply_apply, toMul_ofMul] at hc
        exact hc.eq.symm
      · have h1 : (⟨z, hzA⟩ : ↥(SixPlane.supp 6 (Finset.univ.erase i₀))) ^ 2 ^ k = 1 :=
          Subtype.ext (by simpa using hk)
        rw [← map_pow, h1, map_one]
    intro y hy
    rw [Subgroup.mem_subgroupOf] at hy
    obtain ⟨y', hy', hyy⟩ := hK hy
    rwa [show y' = y from Subtype.ext hyy] at hy'
  · rw [qtwoFarY]
    refine iSup_le fun r => iSup_le fun hr => iSup_le fun r' => iSup_le fun hr' =>
      iSup_le fun hne => ?_
    have hrefl : ∀ q : MulAut ↥Bs, q ∈ ggCoxRefl M e →
        ggLin (p := 3) β q (Pi.single i₀ 1) = Pi.single i₀ 1 → q ∈ ggAutomizer Y Bs := by
      rintro q ⟨w, i, rfl⟩ hfix
      have hev : ggLin (p := 3) β ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) :
          MulAut ↥Bs) ∈ dEven 6 := by
        rw [← qtwoD_image_eq (by norm_num) hM β hβ]
        exact ⟨_, (e _).2, rfl⟩
      have hst : ggLin (p := 3) β ((e (w * M.simple i * w⁻¹) : ↥(ggAutomizerJoin L Bs 𝒦)) :
          MulAut ↥Bs) ∈ dEvenStab 6 (Pi.single i₀ 1) := ⟨hev, hfix⟩
      obtain ⟨q', hq', hlin⟩ := hAe hst
      rwa [ggLin_injective (p := 3) β hlin] at hq'
    have hle : ggRankTwo Bs r r' ≤ φ₀.range :=
      (hamb r (hrefl r hr.1 (hr.2 i₀ hi₀S)) hr.1 r' (hrefl r' hr'.1 (hr'.2 i₀ hi₀S)) hr'.1
        hne).trans hrange.ge
    have h := ggRankTwo_le_range_supp φ₀ hφ₀ (qtwoCoord β) hrot hS
      (fun j _ hj => ⟨qtwoCoord_mem_hyperplane β (hr.2 j hj),
        qtwoCoord_mem_hyperplane β (hr'.2 j hj)⟩) hle
    rwa [MonoidHom.range_comp, Subgroup.inclusion_range] at h

theorem qtwoFarSix_of_chart [Finite G] {L Bs Y : Subgroup G} {𝒦 : Finset (Subgroup G)}
    {ι : Type} {M : CoxeterMatrix ι} {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (e' : Fin 6 ≃ ι)
    (hM : M = (ggCoxeterMatrixD 6).reindex e') (β : Additive ↥Bs ≃+ DVec 6)
    (hβ : ∀ (t : Fin 6) (s : ↥Bs),
      β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
        dTau 6 (decide (t.val + 1 = 6)) (simpleLo t) (simpleHi t) (β (Additive.ofMul s)))
    {i₀ : Fin 6}
    (hAe : dEvenStab 6 (Pi.single i₀ 1) ≤ (ggAutomizer Y Bs).map (ggLin (p := 3) β))
    (hamb : ∀ r ∈ ggAutomizer Y Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer Y Bs,
      r' ∈ ggCoxRefl M e → r * r' ≠ r' * r → ggRankTwo Bs r r' ≤ Y)
    (hYc : Y ≤ Subgroup.centralizer {qtwoCoord β i₀})
    (φ₀ : ↥(SixPlane.supp 6 (Finset.univ.erase i₀)) →* G) (hφ₀ : Function.Injective φ₀)
    (hrange : φ₀.range = Y)
    (hrot : ∀ i (hi : i ∈ Finset.univ.erase i₀),
      φ₀ ⟨SixPlane.rot 6 i, SixPlane.rot_mem_supp hi⟩ = qtwoCoord β i)
    (hgen : GGQTwoSixPlaneGenInput)
    (i k j l : Fin 6) (hik : ggCoxeterMatrixD 6 i k = 3) (hjl : ggCoxeterMatrixD 6 j l = 3)
    (hij : ggCoxeterMatrixD 6 i j = 2) (hil : ggCoxeterMatrixD 6 i l = 2)
    (hkj : ggCoxeterMatrixD 6 k j = 2) (hkl : ggCoxeterMatrixD 6 k l = 2) :
    ∀ y ∈ qtwoW Bs (qtwoRefl e e') i k, ∀ z ∈ qtwoW Bs (qtwoRefl e e') j l, y * z = z * y := by
  classical
  obtain ⟨σ, hσ⟩ := qtwoFarSix_exists_perm i₀
  choose g a haJ hgN hga hβa using fun A => qtwoFarSix_exists_lift e' hM β hβ (σ A)
  have hg : ∀ A : Finset (Fin 6), A.card = 5 → ∀ i ∈ Finset.univ.erase i₀,
      g A * qtwoCoord β i * (g A)⁻¹ = qtwoCoord β (σ A i) := by
    intro A _ i _
    have h1 := congrArg (fun f => f (Pi.single i (1 : ZMod 3))) (hβa A)
    have h2 : dPerm 6 (σ A) (Pi.single i 1) = Pi.single (σ A i) 1 := by
      simpa using dPerm_apply 6 (σ A) i
    simp only [ggLin_apply, h2] at h1
    have h3 := congrArg β.symm h1
    rw [AddEquiv.symm_apply_apply] at h3
    have h4 : (a A) (Additive.toMul (β.symm (Pi.single i 1))) =
        Additive.toMul (β.symm (Pi.single (σ A i) 1)) := congrArg Additive.toMul h3
    rw [qtwoCoord, qtwoCoord, ← hga A, h4]
  have hY : ∀ S ⊆ Finset.univ.erase i₀, S.card = 4 →
      ((SixPlane.supp 6 S).subgroupOf (SixPlane.supp 6 (Finset.univ.erase i₀))).map φ₀ =
        qtwoFarY Bs M e β S := fun S hS hS4 =>
    qtwoFarSix_map_supp_eq e' hM β hβ hAe hamb hYc φ₀ hφ₀ hrange hrot hgen hS hS4
  have hYg : ∀ A : Finset (Fin 6), A.card = 5 → ∀ S ⊆ Finset.univ.erase i₀, S.card = 4 →
      (qtwoFarY Bs M e β S).map (MulAut.conj (g A)).toMonoidHom =
        qtwoFarY Bs M e β (S.map (σ A).toEmbedding) := fun A _ S _ _ =>
    qtwoFarY_map_conj β (haJ A) (hga A) (σ A) (hβa A) S
  obtain ⟨ψ, hinj, himg, htor, hrotψ, -, hSψ⟩ := SixPlane.exists_charts_of_lifts i₀ φ₀ hφ₀
    (qtwoCoord β) hrot σ hσ g hg (qtwoFarY Bs M e β) hY hYg
  refine qtwoFar_six_of_charts (qtwoRefl e e') ψ hinj himg htor ?_ i k j l hik hjl hij hil
    hkj hkl
  intro a b hab A hA hT
  have hfix : ∀ t : Fin 6, t = a ∨ t = b → ∀ s : Fin 6, s ∉ sixEdgeSupp a b →
      ggLin (p := 3) β (qtwoRefl e e' t) (Pi.single s 1) = Pi.single s 1 := by
    rintro t ht s hs
    have hlo : s ≠ simpleLo t := by
      rintro rfl
      apply hs
      rcases ht with rfl | rfl <;> simp [sixEdgeSupp]
    have hhi : s ≠ simpleHi t := by
      rintro rfl
      apply hs
      rcases ht with rfl | rfl <;> simp [sixEdgeSupp]
    exact qtwoFarSix_refl_fix β hβ hlo hhi
  obtain ⟨S, hTS, hSA, hS4⟩ := Finset.exists_subsuperset_card_eq (n := 4) hT
    (by rw [card_sixEdgeSupp a b hab]; norm_num) (by rw [hA]; norm_num)
  have hW : ggRankTwo Bs (qtwoRefl e e' a) (qtwoRefl e e' b) ≤ qtwoFarY Bs M e β S :=
    le_iSup_of_le (qtwoRefl e e' a) (le_iSup_of_le
      ⟨⟨1, e' a, by simp [qtwoRefl]⟩, fun s hs => hfix a (Or.inl rfl) s fun h => hs (hTS h)⟩
      (le_iSup_of_le (qtwoRefl e e' b) (le_iSup_of_le
        ⟨⟨1, e' b, by simp [qtwoRefl]⟩, fun s hs => hfix b (Or.inr rfl) s fun h => hs (hTS h)⟩
        (le_iSup_of_le (qtwoRefl_mul_ne e e' hM hab) le_rfl))))
  have hle : ggRankTwo Bs (qtwoRefl e e' a) (qtwoRefl e e' b) ≤ (ψ A hA).range := by
    refine hW.trans ?_
    rw [← hSψ A hA S hSA hS4]
    exact Subgroup.map_le_range _ _
  rw [qtwoW_of_edge _ hab]
  exact ggRankTwo_le_range_supp (ψ A hA) (hinj A hA) (qtwoCoord β) (hrotψ A hA) hT
    (fun s _ hs => ⟨qtwoCoord_mem_hyperplane β (hfix a (Or.inl rfl) s hs),
      qtwoCoord_mem_hyperplane β (hfix b (Or.inr rfl) s hs)⟩) hle

section Cfg

variable [Finite G]


theorem qtwoFarSix_coords (hRig : GGLabelRigidInput)
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {𝒦 : Finset (Subgroup G)} {ι : Type} {M : CoxeterMatrix ι}
    {e : M.Group ≃* ↥(ggAutomizerJoin L Bs 𝒦)} (hcfg : GGQTwoDCfg p B Bs x L D J 𝒦 M e)
    (e' : Fin 6 ≃ ι) (hM : M = (ggCoxeterMatrixD 6).reindex e') (hL : qtwoOrthL G L 𝒦)
    (hx : x ∈ Bs) :
    p = 3 ∧ ∃ (β : Additive ↥Bs ≃+ DVec 6) (i₀ : Fin 6) (c : ZMod 3),
      (∀ (t : Fin 6) (s : ↥Bs),
        β (Additive.ofMul (((e (M.simple (e' t)) : ↥(ggAutomizerJoin L Bs 𝒦)) : MulAut ↥Bs) s)) =
          dTau 6 (decide (t.val + 1 = 6)) (simpleLo t) (simpleHi t) (β (Additive.ofMul s))) ∧
      c ≠ 0 ∧ β (Additive.ofMul ⟨x, hx⟩) = c • Pi.single i₀ 1 ∧
      (ggAutomizer L Bs).map (ggLin (p := 3) β) = dEvenStab 6 (Pi.single i₀ 1) := by
  obtain ⟨r, hr, hrc, h6⟩ := hcfg.2.2.2.2
  have hp : p = 3 := ggQTwo_p_eq_three hcfg.1 M e hcfg.2.2.2.1 hr hrc h6
  subst hp
  obtain ⟨β, hβ⟩ := ggQTwoDSelModuleInputOn_of_selectedModule (R := fun m => m = 6)
    (fun m (hm : m = 6) => by omega) hTBF hWI G 3 B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM
  have hW : GGWeylOfType 3 (ggCoxeterMatrixD 5) (ggAutomizer L Bs) :=
    ggQTwoDOrthBase_weylD hRig hTBF hWI hcfg e' (by norm_num) hM hL
  have hA : ∀ a ∈ ggAutomizer L Bs, ggLin (p := 3) β a ∈ dEven 6 := fun a ha => by
    rw [← qtwoD_image_eq (by norm_num) hM β hβ]
    exact ⟨a, ggAutomizer_le_ggAutomizerJoin (Or.inl rfl) ha, rfl⟩
  obtain ⟨-, -, -, hLx, -⟩ := hcfg.1.1.1.tableB_facts
  have hx1 : x ≠ 1 := by
    intro h1
    have h := hcfg.1.1.1.orderOf_x
    rw [h1, orderOf_one] at h
    omega
  have hv₀ : β (Additive.ofMul ⟨x, hx⟩) ≠ 0 := by
    rw [Ne, AddEquiv.map_eq_zero_iff]
    intro h0
    exact hx1 (congrArg Subtype.val (ofMul_eq_zero.mp h0))
  have hfix : ∀ a ∈ ggAutomizer L Bs,
      ggLin (p := 3) β a (β (Additive.ofMul ⟨x, hx⟩)) = β (Additive.ofMul ⟨x, hx⟩) := by
    intro a ha
    rw [← ggLin_fix_iff]
    obtain ⟨g, hgL, -, hga⟩ := mem_ggAutomizer_iff.mp ha
    have hxg : x * g = g * x := Subgroup.mem_centralizer_iff.mp (hLx hgL) x (Set.mem_singleton x)
    apply Subtype.ext
    rw [hga]
    change g * x * g⁻¹ = x
    rw [← hxg, mul_inv_cancel_right]
  obtain ⟨i₀, c, hc, hxc, hmap⟩ := exists_native_of_weylD5 β hA hW hv₀ hfix
  exact ⟨rfl, β, i₀, c, hβ, hc, hxc, hmap⟩

theorem ggQTwoFarInputOn_six_orth
    (hTBF : GGTBFixInput) (hWI : GGNbrInnerWeylInput)
    (hEdge : GGQTwoEdgeAmbientInputOn fun m => m = 6) (hgen : GGQTwoSixPlaneGenInput) :
    GGQTwoFarInputOn (fun m => m = 6) qtwoOrthL := by
  classical
  intro G _ _ p B Bs x L D J 𝒦 ι M e hcfg m e' hm hM hc i k j l hik hjl hij hil hkj hkl
  subst hm
  obtain ⟨-, -, hxBs, hLx, -⟩ := hcfg.1.1.1.tableB_facts
  obtain ⟨hp3, β, i₀, c, hβ, hc0, hxc, hAe⟩ :=
    qtwoFarSix_coords ggLabelRigidInput_holds hTBF hWI hcfg e' hM hc hxBs
  subst hp3
  obtain ⟨Φ, hF, -, hZ⟩ := qtwoDL1Chart_orth_L_on (R := fun m => m = 6)
    (ggQTwoFrameInput_of_inputs (fun m hm => by omega) ggLabelRigidInput_holds hTBF hWI)
    hcfg 6 e' rfl (by norm_num) hM hc
  obtain ⟨φ₀, hφ₀, hrange, hrot⟩ :=
    qtwoFarSix_exists_chart hcfg e' hM β hβ hc0 hxBs hxc hAe Φ hF hZ
  have hamb : ∀ r ∈ ggAutomizer L Bs, r ∈ ggCoxRefl M e → ∀ r' ∈ ggAutomizer L Bs,
      r' ∈ ggCoxRefl M e → r * r' ≠ r' * r → ggRankTwo Bs r r' ≤ L :=
    fun r hr hrc r' hr' hr'c hne =>
      (hEdge G 3 B Bs x L D J 𝒦 ι M e hcfg 6 e' rfl hM L (Or.inl rfl) r hr hrc r' hr' hr'c
        hne).le.trans ((ggOTwoPrime_le _).trans inf_le_left)
  exact qtwoFarSix_of_chart e' hM β hβ hAe.ge hamb (le_centralizer_qtwoCoord β hxBs hc0 hxc hLx)
    φ₀ hφ₀ hrange hrot hgen i k j l hik hjl hij hil hkj hkl

end Cfg

end Orth

end CFSG.StandardType.QTwo

end

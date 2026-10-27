module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.TwoThreeTransport
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22wi
public import CFSG.LocalAnalysis.EvenBN.GMSK.SzFacts
public import CFSG.Adapters.LieModelSimple
public import CFSG.GroupTheory.StronglyClosedTI.OddCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.Quasithin Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

section Image

variable {A K : Subgroup G}

private theorem pCore_le_ker_barSubHom (hA : IsElemAbelian 2 A) (hKstab : K ≤ stabTil ⊥ A)
    (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥) :
    CFSG.pCore 2 ↥K ≤ (barSubHom hA K hKstab).ker := by
  intro x hx
  rw [MonoidHom.mem_ker]
  apply Subtype.ext
  have hxP : (x : G) ∈ CFSG.Open.pCoreOf 2 K := ⟨x, hx, rfl⟩
  have h1 : actTil ⊥ A hA ⟨(x : G), hKstab x.2⟩ ∈ barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) :=
    actTil_mem_barSub ⊥ A hA hxP (hKstab x.2)
  rw [h2, Subgroup.mem_bot] at h1
  rw [barSubHom_apply]
  exact h1

private noncomputable def quotHom (hA : IsElemAbelian 2 A) (hKstab : K ≤ stabTil ⊥ A)
    (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥) : Bar2 K →* ↥(barSub ⊥ A hA K) :=
  QuotientGroup.lift (CFSG.pCore 2 ↥K) (barSubHom hA K hKstab) (pCore_le_ker_barSubHom hA hKstab h2)

private theorem quotHom_mk (hA : IsElemAbelian 2 A) (hKstab : K ≤ stabTil ⊥ A)
    (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥) (l : ↥K) :
    ((quotHom hA hKstab h2 (QuotientGroup.mk l) : ↥(barSub ⊥ A hA K)) :
      MulAut (Vtil ⊥ A hA)) = actTil ⊥ A hA ⟨(l : G), hKstab l.2⟩ := by
  rw [quotHom, QuotientGroup.lift_mk, barSubHom_apply]

private theorem quotHom_surjective (hA : IsElemAbelian 2 A) (hKstab : K ≤ stabTil ⊥ A)
    (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥) :
    Function.Surjective (quotHom hA hKstab h2) := by
  intro y
  obtain ⟨x, rfl⟩ := barSubHom_surjective hA K hKstab y
  exact ⟨QuotientGroup.mk x, by rw [quotHom, QuotientGroup.lift_mk]⟩

private theorem ker_quotHom_le_center (hA : IsElemAbelian 2 A) (hKstab : K ≤ stabTil ⊥ A)
    (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥) (hK1 : barSub ⊥ A hA K ≠ ⊥)
    (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    (quotHom hA hKstab h2).ker ≤ Subgroup.center (Bar2 K) := by
  have hnt : ∃ k : Bar2 K, quotHom hA hKstab h2 k ≠ 1 := by
    have : Nontrivial ↥(barSub ⊥ A hA K) := (Subgroup.nontrivial_iff_ne_bot _).2 hK1
    obtain ⟨g, hg⟩ := exists_ne (1 : ↥(barSub ⊥ A hA K))
    obtain ⟨k, hk⟩ := quotHom_surjective hA hKstab h2 g
    exact ⟨k, fun h1 => hg (by rw [← hk, h1])⟩
  exact CFSG.LieType.CurtisTits.ker_le_center_of_isQuasisimple
    ((CFSG.Foundations.SteinbergCA.quasisimple_iff (Bar2 K)).2.2.1.mpr hKq) hnt

theorem pCore_barSub_eq_bot_of_quasisimple (hA : IsElemAbelian 2 A) (hKstab : K ≤ stabTil ⊥ A)
    (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥) (hK1 : barSub ⊥ A hA K ≠ ⊥)
    (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    CFSG.pCore 2 ↥(barSub ⊥ A hA K) = ⊥ := by
  let q := quotHom hA hKstab h2
  have hker : q.ker ≤ Subgroup.center (Bar2 K) := ker_quotHom_le_center hA hKstab h2 hK1 hKq
  have hX : CFSG.pCore 2 (Bar2 K) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hbot : CFSG.pCore 2 (Bar2 K ⧸ q.ker) = ⊥ :=
    CFSG.GroupTheory.StronglyClosedTI.pCore_quotient_eq_bot hker hX
  have e : (Bar2 K ⧸ q.ker) ≃* ↥(barSub ⊥ A hA K) :=
    QuotientGroup.quotientKerEquivOfSurjective q (quotHom_surjective hA hKstab h2)
  have hmap := CFSG.pCore_map_iso 2 e
  rw [hbot, Subgroup.map_bot] at hmap
  exact hmap.symm

theorem actsNontrivOnDiagramIn_barSub (hA : IsElemAbelian 2 A) (hKstab : K ≤ stabTil ⊥ A)
    (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥) (hK1 : barSub ⊥ A hA K ≠ ⊥)
    (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) {t : G}
    (ht : t ∈ stabTil ⊥ A) (h : ActsNontrivOnDiagram K t) :
    ActsNontrivOnDiagramIn (barSub ⊥ A hA K) (actTil ⊥ A hA ⟨t, ht⟩) := by
  obtain ⟨htN, θ, hθ, hnot⟩ := h
  let q := quotHom hA hKstab h2
  have hq : Function.Surjective q := quotHom_surjective hA hKstab h2
  have hqC : CFSG.IsQuasisimple (Bar2 K) :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff (Bar2 K)).2.2.1.mpr hKq
  have hker : q.ker ≤ Subgroup.center (Bar2 K) := ker_quotHom_le_center hA hKstab h2 hK1 hKq
  have hcen := CFSG.LieType.CurtisTits.center_eq_map_center_of_isQuasisimple hqC hq hker
  let ψ : Bar2 K →* ↥(barSub ⊥ A hA K) ⧸ Subgroup.center ↥(barSub ⊥ A hA K) :=
    (QuotientGroup.mk' (Subgroup.center ↥(barSub ⊥ A hA K))).comp q
  have hψ : Function.Surjective ψ := (QuotientGroup.mk'_surjective _).comp hq
  have hkerψ : ψ.ker = Subgroup.center (Bar2 K) := by
    ext k
    rw [MonoidHom.mem_ker, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.eq_one_iff, hcen]
    constructor
    · rintro ⟨k', hk', hkk'⟩
      have hker' : k'⁻¹ * k ∈ q.ker := by
        rw [MonoidHom.mem_ker, map_mul, map_inv, hkk', inv_mul_cancel]
      have := (Subgroup.center (Bar2 K)).mul_mem hk' (hker hker')
      simpa using this
    · intro hk
      exact ⟨k, hk, rfl⟩
  let φ : Bar2 K ⧸ Subgroup.center (Bar2 K) ≃*
      ↥(barSub ⊥ A hA K) ⧸ Subgroup.center ↥(barSub ⊥ A hA K) :=
    (QuotientGroup.quotientMulEquivOfEq hkerψ.symm).trans
      (QuotientGroup.quotientKerEquivOfSurjective ψ hψ)
  have hφ : ∀ x : Bar2 K, φ (QuotientGroup.mk x) = QuotientGroup.mk (q x) := fun _ => rfl
  have htK : ∀ l : ↥K, t * (l : G) * t⁻¹ ∈ K := fun l =>
    (Subgroup.mem_normalizer_iff.mp htN (l : G)).mp l.2
  set tb := actTil ⊥ A hA ⟨t, ht⟩ with htb
  refine ⟨?_, MulAut.congr φ θ, ?_, ?_⟩
  ·
    rw [Subgroup.mem_normalizer_iff]
    intro y
    constructor
    · intro hy
      obtain ⟨g, hgK, rfl⟩ := (mem_barSub ⊥ A hA K y).1 hy
      have hgK' : t * (g : G) * t⁻¹ ∈ K := htK ⟨g, hgK⟩
      have : (⟨t * (g : G) * t⁻¹, hKstab hgK'⟩ : ↥(stabTil ⊥ A)) =
          ⟨t, ht⟩ * g * (⟨t, ht⟩ : ↥(stabTil ⊥ A))⁻¹ := rfl
      have hmem := actTil_mem_barSub ⊥ A hA hgK' (hKstab hgK')
      rw [this, map_mul, map_mul, map_inv] at hmem
      exact hmem
    · intro hy
      obtain ⟨g, hgK, hg⟩ := (mem_barSub ⊥ A hA K _).1 hy
      have htK' : t⁻¹ * (g : G) * t ∈ K := by
        have := (Subgroup.mem_normalizer_iff.mp (Subgroup.inv_mem _ htN) (g : G)).mp hgK
        simpa using this
      have hmem := actTil_mem_barSub ⊥ A hA htK' (hKstab htK')
      have : (⟨t⁻¹ * (g : G) * t, hKstab htK'⟩ : ↥(stabTil ⊥ A)) =
          (⟨t, ht⟩ : ↥(stabTil ⊥ A))⁻¹ * g * ⟨t, ht⟩ := rfl
      rw [this, map_mul, map_mul, map_inv, hg] at hmem
      simpa [htb, mul_assoc] using hmem
  ·
    intro a a' ha'
    obtain ⟨x, rfl⟩ := hq a
    obtain ⟨l, rfl⟩ := QuotientGroup.mk_surjective x
    let l' : ↥K := ⟨t * (l : G) * t⁻¹, htK l⟩
    have hll' : a' = q (QuotientGroup.mk l') := by
      apply Subtype.ext
      rw [ha', quotHom_mk hA hKstab h2 l, quotHom_mk hA hKstab h2 l']
      have : (⟨t * (l : G) * t⁻¹, hKstab (htK l)⟩ : ↥(stabTil ⊥ A)) =
          ⟨t, ht⟩ * ⟨(l : G), hKstab l.2⟩ * (⟨t, ht⟩ : ↥(stabTil ⊥ A))⁻¹ := rfl
      rw [this, map_mul, map_mul, map_inv]
    rw [hll', MulAut.congr_apply, ← hφ, MulEquiv.trans_apply, MulEquiv.trans_apply,
      MulEquiv.symm_apply_apply, hθ l l' rfl, hφ]
  · intro hIDF
    exact hnot ((uc22p22wi_isInnDiagFieldAut_congr φ θ).1 hIDF)

theorem isComponentOf_barSub_of_isSubnormal (hA : IsElemAbelian 2 A) (hKstab : K ≤ stabTil ⊥ A)
    (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥) (hK1 : barSub ⊥ A hA K ≠ ⊥)
    {H : Subgroup G} (hKH : CFSG.Open.IsSubnormal K H) (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) :
    IsComponentOf (barSub ⊥ A hA K) (barSub ⊥ A hA H) :=
  ⟨barSub_mono ⊥ A hA (CFSG.Quasithin.A3.subnormal_le hKH),
    TwelveTwentyThree.isSubnormal_barSub (V₀ := ⊥) hA hKH,
    TwelveTwentyThree.isQuasisimple_barSub (V₀ := ⊥) hA hKstab hKq h2 hK1⟩

theorem shape417_barSub (hA : IsElemAbelian 2 A) (hKstab : K ≤ stabTil ⊥ A)
    (h2 : barSub ⊥ A hA (CFSG.Open.pCoreOf 2 K) = ⊥) (hK1 : barSub ⊥ A hA K ≠ ⊥)
    (hKq : CFSG.Open.IsQuasisimple (Bar2 K)) {T : Subgroup G}
    (hT : T ≤ stabTil ⊥ A) {n : ℕ}
    (h : IsL2 (Bar2 K) n ∨ IsSz (Bar2 K) n ∨ IsSU3 (Bar2 K) n ∨
      ((IsSL3 (Bar2 K) n ∨ IsSp4 (Bar2 K) n) ∧ ∃ t ∈ T, ActsNontrivOnDiagram K t)) :
    IsL2 ↥(barSub ⊥ A hA K) n ∨ IsSz ↥(barSub ⊥ A hA K) n ∨ IsSU3 ↥(barSub ⊥ A hA K) n ∨
      ((IsSL3 ↥(barSub ⊥ A hA K) n ∨ IsSp4 ↥(barSub ⊥ A hA K) n) ∧
        ∃ t ∈ barSub ⊥ A hA T, ActsNontrivOnDiagramIn (barSub ⊥ A hA K) t) := by
  rcases h with hL2 | hSz | hSU | ⟨hSLSp, t, htT, hdiag⟩
  · exact Or.inl (lieModel_barSub_of_isSimpleGroup hA hKstab h2 hK1
      (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hL2) hL2)
  · exact Or.inr (Or.inl (lieModel_barSub_of_isSimpleGroup hA hKstab h2 hK1
      (CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_twistedB2 hSz) hSz))
  · exact Or.inr (Or.inr (Or.inl (isSU3_barSub hA hKstab h2 hK1 hSU)))
  · refine Or.inr (Or.inr (Or.inr ⟨?_, actTil ⊥ A hA ⟨t, hT htT⟩,
      actTil_mem_barSub ⊥ A hA htT (hT htT),
      actsNontrivOnDiagramIn_barSub hA hKstab h2 hK1 hKq (hT htT) hdiag⟩))
    rcases hSLSp with hSL | hSp
    · exact Or.inl (isSL3_barSub hA hKstab h2 hK1 hSL)
    · exact Or.inr (lieModel_barSub_of_isSimpleGroup hA hKstab h2 hK1
        (CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hSp) hSp)

end Image

end CFSG.LocalAnalysis.UniquenessCase.UC22

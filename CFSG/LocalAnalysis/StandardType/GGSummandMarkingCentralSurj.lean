module

public import CFSG.LocalAnalysis.StandardType.GGSummandStructBasic

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem largeEvenMarking_of_central_surj {A B : Type*} [Group A] [Group B] (g : A →* B)
    (hg : Function.Surjective g) (hker : g.ker ≤ Subgroup.center A) (hA : commutator A = ⊤)
    {ιA ιB : Type*} (PA : ιA → Prop) (PB : ιB → Prop) (tag : LargeEvenLabel → Prop)
    (relA : ιA → A → A → Prop) (relB : ιB → B → B → Prop)
    (hrel : ∀ j, PB j → ∃ i, PA i ∧ ∀ b b' : B, relB j b b' →
      ∃ a a' : A, g a = b ∧ g a' = b' ∧ relA i a a')
    (h : LargeEvenMarking A (fun lab _ _ I _ θ => tag lab ∧ ∀ i, PA i → ∃ φ ∈ I,
      LargeEvenInduces θ (relA i) φ)) :
    LargeEvenMarking B (fun lab _ _ I _ θ => tag lab ∧ ∀ j, PB j → ∃ φ ∈ I,
      LargeEvenInduces θ (relB j) φ) := by
  have hperf : Group.IsPerfect A := ⟨hA⟩
  haveI : Group.IsPerfect A := hperf
  have hB : commutator B = ⊤ := (Group.IsPerfect.ofSurjective hg).commutator_eq_top
  have hcomap : (Subgroup.center B).comap g = Subgroup.center A :=
    CFSG.LocalCores.comap_center_eq_of_perfect hperf g hg hker
  let φ : A →* B ⧸ Subgroup.center B := (QuotientGroup.mk' (Subgroup.center B)).comp g
  have hφsurj : Function.Surjective φ :=
    (QuotientGroup.mk'_surjective (Subgroup.center B)).comp hg
  have hφker : Subgroup.center A = φ.ker := by
    dsimp only [φ]
    rw [← MonoidHom.comap_ker, QuotientGroup.ker_mk', hcomap]
  let e : A ⧸ Subgroup.center A ≃* B ⧸ Subgroup.center B :=
    QuotientGroup.liftEquiv (Subgroup.center A) (φ := φ) hφsurj hφker
  have he : ∀ a : A, e (QuotientGroup.mk a) = QuotientGroup.mk (g a) :=
    fun a => QuotientGroup.liftEquiv_mk (Subgroup.center A) (φ := φ) hφsurj hφker a
  obtain ⟨-, lab, hlab, hraw⟩ := h
  refine ⟨hB, lab, hlab, largeEvenRawDatum_mono ?_ hraw⟩
  rintro R _ I F ⟨hs, hna, θ, htag, hforall⟩
  refine ⟨hs, hna, e.symm.trans θ, htag, ?_⟩
  intro j hj
  obtain ⟨i, hi, hrelji⟩ := hrel j hj
  obtain ⟨φA, hφAI, hφA⟩ := hforall i hi
  refine ⟨φA, hφAI, ?_⟩
  intro b b' hbb'
  obtain ⟨a, a', hga, hga', hraa'⟩ := hrelji b b' hbb'
  have hb : e.symm (QuotientGroup.mk b) = QuotientGroup.mk a := by
    rw [← hga, ← he a, MulEquiv.symm_apply_apply]
  have hb' : e.symm (QuotientGroup.mk b') = QuotientGroup.mk a' := by
    rw [← hga', ← he a', MulEquiv.symm_apply_apply]
  calc φA ((e.symm.trans θ) (QuotientGroup.mk b))
      = φA (θ (e.symm (QuotientGroup.mk b))) := by rw [MulEquiv.trans_apply]
    _ = φA (θ (QuotientGroup.mk a)) := by rw [hb]
    _ = θ (QuotientGroup.mk a') := hφA a a' hraa'
    _ = θ (e.symm (QuotientGroup.mk b')) := by rw [hb']
    _ = (e.symm.trans θ) (QuotientGroup.mk b') := by rw [MulEquiv.trans_apply]

end CFSG.StandardType

module

public import Certificates.Kernel.Co2Census.CCFib
public import CFSG.Sporadic.Co2Smith.ClassCount

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section CC


theorem cls_le_gen {M : Type*} [Group M] [Finite M] (π : M →* K)
    (elt : ℕ → ℕ → M) (hπ : ∀ e n, π (elt e n) = sElt n) {F : ℕ → ℕ} {er nr nf slot : ℕ}
    (hinj : ∀ e e', e < 512 → e' < 512 → elt e nr = elt e' nr → e = e')
    (hlift : ∀ w ∈ S0, ∃ h : M, π h = w)
    (hslot : slot < 5) (hrep : s0Rep slot = sElt nr)
    (hfs : ∀ j < nf, fld21 (F j) 0 < 512 ∧ (j = 0 ∨ fld21 (F (j - 1)) 0 < fld21 (F j) 0) ∧
      elt (fld21 (F j) 1) (fld21 (F j) 2) * elt er nr =
        elt (fld21 (F j) 0) nr * elt (fld21 (F j) 1) (fld21 (F j) 2)) :
    s0Sizes.getD slot 0 * nf ≤ (conjSet (elt er nr)).ncard := by
  classical
  obtain ⟨hcl, hcard⟩ := s0_class hslot
  rw [hcl, hrep] at hcard
  set KS : Set K := {y | ∃ w ∈ S0, y = w * sElt nr * w⁻¹}
  set FS : Set ℕ := {j | j < nf}
  have hFS : FS.ncard = nf := by
    rw [show FS = (Finset.range nf : Set ℕ) by ext j; simp [FS], Set.ncard_coe_finset,
      Finset.card_range]
  have hl : ∀ s ∈ KS, ∃ h : M, π h * sElt nr * (π h)⁻¹ = s := by
    rintro s ⟨w, hw, rfl⟩
    obtain ⟨h, rfl⟩ := hlift w hw
    exact ⟨h, rfl⟩
  let lift : K → M := fun s => if h : ∃ h : M, π h * sElt nr * (π h)⁻¹ = s then
    h.choose else 1
  have hlift' : ∀ s ∈ KS, π (lift s) * sElt nr * (π (lift s))⁻¹ = s := by
    intro s hs
    simp only [lift, dif_pos (hl s hs)]
    exact (hl s hs).choose_spec
  let Φ : K × ℕ → M := fun p => lift p.1 * elt (fld21 (F p.2) 0) nr * (lift p.1)⁻¹
  have hmaps : Set.MapsTo Φ (KS ×ˢ FS) (conjSet (elt er nr)) := by
    rintro ⟨s, j⟩ ⟨_, hj⟩
    obtain ⟨-, -, hc⟩ := hfs j hj
    set u := elt (fld21 (F j) 1) (fld21 (F j) 2)
    refine ⟨lift s * u, ?_⟩
    have hy : elt (fld21 (F j) 0) nr = u * elt er nr * u⁻¹ := by
      rw [hc]
      group
    simp only [Φ]
    rw [hy]
    group
  have hinj' : Set.InjOn Φ (KS ×ˢ FS) := by
    rintro ⟨s, j⟩ ⟨hs, hj⟩ ⟨s', j'⟩ ⟨hs', hj'⟩ e
    simp only [Φ] at e
    have hpi := congrArg π e
    simp only [map_mul, map_inv, hπ] at hpi
    rw [hlift' s hs, hlift' s' hs'] at hpi
    subst hpi
    have e2 : elt (fld21 (F j) 0) nr = elt (fld21 (F j') 0) nr :=
      mul_left_cancel (mul_right_cancel e)
    have e3 := hinj _ _ (hfs j hj).1 (hfs j' hj').1 e2
    rw [roots_strict (fun j hj => (hfs j hj).2.1) j hj j' hj' e3]
  have := Set.ncard_le_ncard_of_injOn Φ hmaps hinj' (Set.toFinite _)
  rw [Set.ncard_prod, hcard, hFS] at this
  exact this

theorem cc_cls_le {QK : ℕ → ℕ}
    (hQK : ∀ e < 512, QK e = KernelCo2SmithS.nfS (e / 256) (e % 256)) {F : ℕ → ℕ}
    {er nr nf slot : ℕ} (her : er < 512) (hnr : nr < 1451520)
    (hslot : slot < 5) (hrep : s0Rep slot = sElt nr) (hF : ∀ j < nf, fibOKC QK F er nr j = true) :
    s0Sizes.getD slot 0 * nf ≤ (conjSet (cE er nr)).ncard :=
  cls_le_gen piC cE piC_cE (fun e e' he he' h => (cE_injOn he he' hnr hnr h).1)
    (fun w hw => ⟨⟨w, S0_le_Cz hw⟩, piC_S0 hw⟩) hslot hrep
    (fun j hj => fibOKC_spec hQK her (hF j hj))

end CC

end CertificateChecks.KernelCo2Census

end

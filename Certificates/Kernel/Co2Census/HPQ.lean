module

public import Certificates.Kernel.Co2Census.HPFib

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

theorem conjSteps_of {ngen : ℕ} {g : ℕ → K} {G GI : ℕ → ℕ}
    (hG : ∀ l < ngen, repK (g l) (G l))
    (hGI : ∀ l < ngen, mulV (G l) (GI l) = IDP ∧ GI l < 2 ^ 484) :
    ConjSteps repK (conjStep G GI) ngen g := by
  intro l hl x M hx
  exact repK_mul (repK_mul (hG l hl) hx) (repK_inv (hG l hl) (hGI l hl).2 (hGI l hl).1)

theorem hpPred_conj {M : Type*} [Group M] {r c w : M} (hr : w * r = r * w) (hc : w * c = c * w)
    (comm : Bool) (y : M) :
    ((comm = true → w * y * w⁻¹ * r = r * (w * y * w⁻¹)) ∧ w * y * w⁻¹ * (w * y * w⁻¹) = c) ↔
      ((comm = true → y * r = r * y) ∧ y * y = c) := by
  have fr : w * r * w⁻¹ = r := by rw [hr, mul_inv_cancel_right]
  have fc : w * c * w⁻¹ = c := by rw [hc, mul_inv_cancel_right]
  have key : ∀ a b : M, w * a * w⁻¹ * (w * b * w⁻¹) = w * (a * b) * w⁻¹ := fun a b => by group
  have inj : ∀ a b : M, w * a * w⁻¹ = w * b * w⁻¹ ↔ a = b := fun a b => by
    constructor
    · intro h
      exact mul_left_cancel (mul_right_cancel h)
    · rintro rfl
      rfl
  have e1 : w * y * w⁻¹ * r = w * (y * r) * w⁻¹ := by
    conv_lhs => rw [← fr]
    exact key y r
  have e2 : r * (w * y * w⁻¹) = w * (r * y) * w⁻¹ := by
    conv_lhs => rw [← fr]
    exact key r y
  rw [e1, e2, key, inj]
  conv_lhs => rw [← fc, inj]

section HP


theorem hpElt_eq_mk (e n : ℕ) : hpElt e n = mkHP (fpElt e n) := rfl

theorem genOK_spec (hz : Z0 < 2 ^ 484) {QK : ℕ → ℕ}
    (hQK : ∀ e < 512, QK e = KernelCo2SmithS.nfS (e / 256) (e % 256)) {G GR GI : ℕ → ℕ}
    {er nr l : ℕ} (her : er < 512) (h : genOK QK G GR GI er nr l = true) :
    hpElt (fld21 (G l) 0) (fld21 (G l) 1) * hpElt er nr =
        hpElt er nr * hpElt (fld21 (G l) 0) (fld21 (G l) 1) ∧
      repK (piK (hpElt (fld21 (G l) 0) (fld21 (G l) 1))) (GR l) ∧
      mulV (GR l) (GI l) = IDP ∧ GI l < 2 ^ 484 := by
  unfold genOK at h
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨he, hGR⟩, hinv⟩, hlt⟩, hcomm⟩, hk⟩, hnz⟩, hrows⟩ := h
  set e := fld21 (G l) 0
  set m := fld21 (G l) 1
  refine ⟨?_, by rw [piK_hpElt, hGR]; exact repK_sElt m, hinv, hlt⟩
  have hsc : sElt m * sElt nr = sElt nr * sElt m :=
    repK_fun (hcomm ▸ repK_mul (repK_sElt m) (repK_sElt nr)) (repK_mul (repK_sElt nr) (repK_sElt m))
  have hcov : covMap (pLift m * pLift nr) = covMap (pLift nr * pLift m) := by
    simp only [map_mul, covMap_pLift']
    exact Subtype.ext hsc
  have hk1 := sign_cases hcov (spin_prod m nr) (spin_prod nr m) (length_spinMV _ _) hnz hk
  have hW : repK (cElt e m) (mulV (SK m) (QK e)) := by rw [hQK e he]; exact repK_cElt he m
  have hR : repK (cElt er nr) (mulV (SK nr) (QK er)) := by rw [hQK er her]; exact repK_cElt her nr
  rw [hpElt_eq_mk, hpElt_eq_mk, ← map_mul, ← map_mul]
  refine (mkHP_iff_sign hz ?_ (repK_mul hW hR) (repK_mul hR hW)).2 hrows
  rcases hk1 with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · exact Or.inl ⟨h0, h1⟩
  · exact Or.inr ⟨h0, h1⟩

theorem rootOK_spec {Pt IX RT : ℕ → ℕ} {N nr nc : ℕ} {comm : Bool} {j : ℕ}
    (h : rootOK Pt IX RT N nr nc comm j = true) :
    fld21 (RT j) 0 < N ∧ rtOf IX (fld21 (RT j) 0) = fld21 (RT j) 0 ∧
      Pt (fld21 (RT j) 0) = SK (fld21 (RT j) 1) ∧ fld21 (RT j) 1 < 1451520 ∧
      fcOK (fld21 (RT j) 1) nr nc comm = true ∧
      (j = 0 ∨ fld21 (RT (j - 1)) 0 < fld21 (RT j) 0) := by
  unfold rootOK at h
  simp only [letB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem roots_strict {RT : ℕ → ℕ} {nroots : ℕ}
    (h : ∀ j < nroots, j = 0 ∨ fld21 (RT (j - 1)) 0 < fld21 (RT j) 0) :
    ∀ j < nroots, ∀ j' < nroots, fld21 (RT j) 0 = fld21 (RT j') 0 → j = j' := by
  have mono : ∀ a b, a < b → b < nroots → fld21 (RT a) 0 < fld21 (RT b) 0 := by
    intro a b hab hb
    induction b with
    | zero => omega
    | succ b ih =>
      have hs := (h (b + 1) hb).resolve_left (by omega)
      rw [Nat.add_sub_cancel] at hs
      rcases Nat.lt_succ_iff_lt_or_eq.1 hab with h1 | h1
      · exact (ih h1 (by omega)).trans hs
      · rw [h1]
        exact hs
  intro j hj j' hj' e
  rcases lt_trichotomy j j' with h1 | h1 | h1
  · exact absurd e (ne_of_lt (mono _ _ h1 hj'))
  · exact h1
  · exact absurd e.symm (ne_of_lt (mono _ _ h1 hj))

theorem coverRoot_spec {IX RT : ℕ → ℕ} {nroots i : ℕ} (h : coverRootK IX RT nroots i = true) :
    ∃ j < nroots, rtOf IX i = fld21 (RT j) 0 := by
  unfold coverRootK at h
  rw [List.any_eq_true] at h
  obtain ⟨j, hj, e⟩ := h
  exact ⟨j, List.mem_range.1 hj, Nat.eq_of_beq_eq_true e⟩

theorem card_hp_query (hz : Z0 < 2 ^ 484) {QK : ℕ → ℕ}
    (hQK : ∀ e < 512, QK e = KernelCo2SmithS.nfS (e / 256) (e % 256))
    {G GR GI Pt IX RT : ℕ → ℕ} {er nr ec nc N hi nroots : ℕ} (her : er < 512) (hec : ec < 512)
    (comm : Bool) (hcz : ∀ w : Hprime, w * hpElt er nr = hpElt er nr * w →
      w * hpElt ec nc = hpElt ec nc * w)
    (hgen : ∀ l < 6, genOK QK G GR GI er nr l = true)
    (htree : ∀ i < N, treeK (conjStep GR GI) 6 N Pt IX i = true)
    (hroot : ∀ j < nroots, rootOK Pt IX RT N nr nc comm j = true)
    (hcov : ∀ i < N, coverRootK IX RT nroots i = true)
    (hsupp : ∀ y, hpPred (hpElt er nr) (hpElt ec nc) comm y → ∃ i < N, repK (piK y) (Pt i))
    (hN : N ≤ 64 * hi) :
    Nat.card {y : Hprime // hpPred (hpElt er nr) (hpElt ec nc) comm y} =
      totalK QK IX RT N hi nroots nr nc (mulV (SK nr) (QK er)) (mulV (SK nc) (QK ec)) comm := by
  let w : ℕ → Hprime := fun l => hpElt (fld21 (G l) 0) (fld21 (G l) 1)
  have hs : ConjSteps repK (conjStep GR GI) 6 fun l => piK (w l) :=
    conjSteps_of (fun l hl => (genOK_spec hz hQK her (hgen l hl)).2.1)
      (fun l hl => (genOK_spec hz hQK her (hgen l hl)).2.2)
  have hw : ∀ l < 6, ∀ y, hpPred (hpElt er nr) (hpElt ec nc) comm (w l * y * (w l)⁻¹) ↔
      hpPred (hpElt er nr) (hpElt ec nc) comm y := by
    intro l hl y
    have h1 := (genOK_spec hz hQK her (hgen l hl)).1
    exact hpPred_conj h1 (hcz _ h1) comm y
  have hr := fun j hj => rootOK_spec (hroot j hj)
  rw [card_query piK _ (xr := fun j => sElt (fld21 (RT j) 1)) hs hw htree
    (fun i hi' => coverRoot_spec (hcov i hi'))
    (roots_strict fun j hj => (hr j hj).2.2.2.2.2)
    (fun j hj => ⟨(hr j hj).1, (hr j hj).2.1, by rw [(hr j hj).2.2.1]; exact repK_sElt _⟩)
    hsupp hN, totalK, ← sum_range_list]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  congr 1
  have hRR : repK (((fpElt er nr).1.1 : Cz) : K) (mulV (SK nr) (QK er)) := by
    rw [fpElt_fst, hQK er her]
    exact repK_cElt her nr
  have hCR : repK (((fpElt ec nc).1.1 : Cz) : K) (mulV (SK nc) (QK ec)) := by
    rw [fpElt_fst, hQK ec hec]
    exact repK_cElt hec nc
  exact fib_hp_eq hz hQK hRR (fpElt_snd _ _) hCR (fpElt_snd _ _) comm (hr j hj').2.2.2.1
    (hr j hj').2.2.2.2.1

end HP

end CertificateChecks.KernelCo2Census

end

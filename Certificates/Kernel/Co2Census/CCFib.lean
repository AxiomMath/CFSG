module

public import Certificates.Kernel.Co2Census.HPQ
public import Certificates.Kernel.Co2Census.CCDefs
public import CFSG.Sporadic.Co2Smith.CRep
public import Certificates.Kernel.Co2Census.S0Cent
public import Certificates.Kernel.Co2Census.S0Inv

public section

namespace CertificateChecks.KernelCo2Census

open CFSG.Sporadic.Co2Smith CFSG.Sporadic.Co2Cert CFSG.Sporadic.SmallF2 CFSG.KC.Co2InvS
  CFSG.KC.Co2Census CFSG.KC.Loop Matrix

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

set_option maxRecDepth 100000

section CC


@[expose] noncomputable def piC : Cz →* K := S0.subtype.comp cfgCz.rho

theorem piC_cE (e n : ℕ) : piC (cE e n) = sElt n := by
  show ((cfgCz.rho ⟨cElt e n, cElt_mem e n⟩ : S0) : K) = sElt n
  rw [rho_cElt]

theorem piC_mem (y : Cz) : piC y ∈ S0 := (cfgCz.rho y).2

theorem piC_S0 {s : K} (hs : s ∈ S0) : piC ⟨s, S0_le_Cz hs⟩ = s := by
  show ((cfgCz.rho ⟨s, S0_le_Cz hs⟩ : S0) : K) = s
  rw [rho_S0 hs]

theorem repK_cE {QK : ℕ → ℕ} (hQK : ∀ e < 512, QK e = KernelCo2SmithS.nfS (e / 256) (e % 256))
    {e : ℕ} (he : e < 512) (n : ℕ) : repK ((cE e n : Cz) : K) (mulV (SK n) (QK e)) := by
  rw [hQK e he]
  exact repK_cElt he n

theorem repK_czmul {x y : Cz} {X Y : ℕ} (hx : repK (x : K) X) (hy : repK (y : K) Y) :
    repK ((x * y : Cz) : K) (mulV X Y) := by
  rw [Subgroup.coe_mul]
  exact repK_mul hx hy

theorem cz_eq_iff {x y : Cz} {X Y : ℕ} (hx : repK (x : K) X) (hy : repK (y : K) Y) :
    x = y ↔ X = Y := by
  constructor
  · rintro rfl
    exact repK_unique hx hy
  · rintro rfl
    exact Subtype.ext (repK_fun hx hy)

@[expose] def ccPred (r c : Cz) (comm : Bool) (y : Cz) : Prop :=
  (comm = true → y * r = r * y) ∧ y * y = c

theorem fib_cc_eq {QK : ℕ → ℕ}
    (hQK : ∀ e < 512, QK e = KernelCo2SmithS.nfS (e / 256) (e % 256))
    {r c : Cz} {nr nc RR CR : ℕ} (hr : repK (r : K) RR) (hrπ : piC r = sElt nr)
    (hc : repK (c : K) CR) (hcπ : piC c = sElt nc) (comm : Bool) {n : ℕ} (hn : n < 1451520) :
    fib piC (ccPred r c comm) (sElt n) = fcC QK n nr nc RR CR comm := by
  classical
  rw [fib_elt (elt := cE) exists_cE (fun e e' n n' he he' hn hn' h => cE_injOn he he' hn hn' h)
    piC_cE _ hn]
  unfold fcC
  rw [strictN_eq', strictN_eq']
  by_cases hs : s0Cond n nr nc comm = true
  · rw [if_pos hs, strictN_eq', length_filter_range]
    apply congrArg Finset.card
    apply Finset.filter_congr
    intro e he
    have he := Finset.mem_range.1 he
    rw [letB_eq]
    have hy := repK_cE hQK he n
    have hsq := cz_eq_iff (repK_czmul hy hy) hc
    have hcm := cz_eq_iff (repK_czmul hy hr) (repK_czmul hr hy)
    unfold ccPred
    rw [Bool.and_eq_true, Nat.beq_eq, ← hsq]
    cases comm
    · simp
    · simp only [true_implies, Bool.not_true, Bool.false_or, Nat.beq_eq, ← hcm]
      exact and_comm
  · rw [if_neg hs, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
    intro e he hP
    apply hs
    obtain ⟨hcm, hsq⟩ := hP
    unfold s0Cond
    rw [Bool.and_eq_true, Nat.beq_eq]
    have h1 := congrArg piC hsq
    rw [map_mul, piC_cE, hcπ] at h1
    refine ⟨repK_unique (h1 ▸ repK_mul (repK_sElt n) (repK_sElt n)) (repK_sElt nc), ?_⟩
    cases hcc : comm
    · rfl
    · have h2 := congrArg piC (hcm hcc)
      rw [map_mul, map_mul, piC_cE, hrπ] at h2
      rw [Bool.not_true, Bool.false_or, Nat.beq_eq]
      exact repK_unique (h2 ▸ repK_mul (repK_sElt n) (repK_sElt nr))
        (repK_mul (repK_sElt nr) (repK_sElt n))

theorem genOKC_spec {QK : ℕ → ℕ}
    (hQK : ∀ e < 512, QK e = KernelCo2SmithS.nfS (e / 256) (e % 256)) {G GR GI : ℕ → ℕ}
    {er nr l : ℕ} (her : er < 512) (h : genOKC QK G GR GI er nr l = true) :
    cE (fld21 (G l) 0) (fld21 (G l) 1) * cE er nr = cE er nr * cE (fld21 (G l) 0) (fld21 (G l) 1) ∧
      repK (piC (cE (fld21 (G l) 0) (fld21 (G l) 1))) (GR l) ∧
      mulV (GR l) (GI l) = IDP ∧ GI l < 2 ^ 484 := by
  unfold genOKC at h
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  obtain ⟨⟨⟨⟨he, hGR⟩, hinv⟩, hlt⟩, hrows⟩ := h
  refine ⟨?_, by rw [piC_cE, hGR]; exact repK_sElt _, hinv, hlt⟩
  have hW := repK_cE hQK he (fld21 (G l) 1)
  have hR := repK_cE hQK her nr
  exact (cz_eq_iff (repK_czmul hW hR) (repK_czmul hR hW)).2 hrows

theorem rootOKC_spec {Pt IX RT : ℕ → ℕ} {N j : ℕ} (h : rootOKC Pt IX RT N j = true) :
    fld21 (RT j) 0 < N ∧ rtOf IX (fld21 (RT j) 0) = fld21 (RT j) 0 ∧
      Pt (fld21 (RT j) 0) = SK (fld21 (RT j) 1) ∧ fld21 (RT j) 1 < 1451520 ∧
      (j = 0 ∨ fld21 (RT (j - 1)) 0 < fld21 (RT j) 0) := by
  unfold rootOKC at h
  simp only [letB_eq, Bool.and_eq_true, Bool.or_eq_true, Nat.blt_eq, Nat.beq_eq] at h
  exact ⟨h.1.1.1.1, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem card_cc_query {QK : ℕ → ℕ}
    (hQK : ∀ e < 512, QK e = KernelCo2SmithS.nfS (e / 256) (e % 256))
    {G GR GI Pt IX RT : ℕ → ℕ} {er nr nc ngen N hi nroots CR : ℕ} {c : Cz} (her : er < 512)
    (hc : repK (c : K) CR) (hcπ : piC c = sElt nc) (comm : Bool)
    (hcz : ∀ w : Cz, w * cE er nr = cE er nr * w → w * c = c * w)
    (hgen : ∀ l < ngen, genOKC QK G GR GI er nr l = true)
    (htree : ∀ i < N, treeK (conjStep GR GI) ngen N Pt IX i = true)
    (hroot : ∀ j < nroots, rootOKC Pt IX RT N j = true)
    (hcov : ∀ i < N, coverRootK IX RT nroots i = true)
    (hsupp : ∀ y, ccPred (cE er nr) c comm y → ∃ i < N, repK (piC y) (Pt i))
    (hN : N ≤ 64 * hi) :
    Nat.card {y : Cz // ccPred (cE er nr) c comm y} =
      totalC QK IX RT N hi nroots nr nc (mulV (SK nr) (QK er)) CR comm := by
  let w : ℕ → Cz := fun l => cE (fld21 (G l) 0) (fld21 (G l) 1)
  have hs : ConjSteps repK (conjStep GR GI) ngen fun l => piC (w l) :=
    conjSteps_of (fun l hl => (genOKC_spec hQK her (hgen l hl)).2.1)
      (fun l hl => (genOKC_spec hQK her (hgen l hl)).2.2)
  have hw : ∀ l < ngen, ∀ y, ccPred (cE er nr) c comm (w l * y * (w l)⁻¹) ↔
      ccPred (cE er nr) c comm y := by
    intro l hl y
    have h1 := (genOKC_spec hQK her (hgen l hl)).1
    exact hpPred_conj h1 (hcz _ h1) comm y
  have hr := fun j hj => rootOKC_spec (hroot j hj)
  rw [card_query piC _ (xr := fun j => sElt (fld21 (RT j) 1)) hs hw htree
    (fun i hi' => coverRoot_spec (hcov i hi'))
    (roots_strict fun j hj => (hr j hj).2.2.2.2)
    (fun j hj => ⟨(hr j hj).1, (hr j hj).2.1, by rw [(hr j hj).2.2.1]; exact repK_sElt _⟩)
    hsupp hN, totalC, ← sum_range_list]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' := Finset.mem_range.1 hj
  congr 1
  exact fib_cc_eq hQK (repK_cE hQK her nr) (piC_cE er nr) hc hcπ comm (hr j hj').2.2.2.1

theorem suppZC {Pt Zc : ℕ → ℕ} {N nr er : ℕ}
    (hpos : ∀ j < 5104, posK (fun x => Nat.beq (mulV x (SK nr)) (mulV (SK nr) x)) LPt Pt Zc N j =
      true) {c : Cz} (hc : piC c = 1) :
    ∀ y, ccPred (cE er nr) c true y → ∃ i < N, repK (piC y) (Pt i) := by
  intro y hy
  have h1 := congrArg piC (hy.1 rfl)
  rw [map_mul, map_mul, piC_cE] at h1
  have h2 := congrArg piC hy.2
  rw [map_mul, hc] at h2
  obtain ⟨j, hj, hrep⟩ := s0_inv_iff.1 ⟨piC_mem y, h2⟩
  have ht : Nat.beq (mulV (LPt j) (SK nr)) (mulV (SK nr) (LPt j)) = true := by
    rw [Nat.beq_eq]
    exact repK_unique (h1 ▸ repK_mul hrep (repK_sElt nr)) (repK_mul (repK_sElt nr) hrep)
  obtain ⟨hp, he⟩ := posK_sound hpos j hj ht
  exact ⟨_, hp, he ▸ hrep⟩

theorem suppRC {CP Pt Rc : ℕ → ℕ} {NC N er nr : ℕ}
    (hcent : {y | ∃ i < NC, repK y (CP i)} = centS0 (sElt nr))
    (hpos : ∀ j < NC, posK (fun x => Nat.beq (mulV x x) (SK nr)) CP Pt Rc N j = true)
    (comm : Bool) :
    ∀ y, ccPred (cE er nr) (cE er nr) comm y → ∃ i < N, repK (piC y) (Pt i) := by
  intro y hy
  have h2 := congrArg piC hy.2
  rw [map_mul, piC_cE] at h2
  have hc : piC y ∈ centS0 (sElt nr) := ⟨piC_mem y, by rw [← h2, ← mul_assoc]⟩
  rw [← hcent] at hc
  obtain ⟨j, hj, hrep⟩ := hc
  have ht : Nat.beq (mulV (CP j) (CP j)) (SK nr) = true := by
    rw [Nat.beq_eq]
    exact repK_unique (h2 ▸ repK_mul hrep hrep) (repK_sElt nr)
  obtain ⟨hp, he⟩ := posK_sound hpos j hj ht
  exact ⟨_, hp, he ▸ hrep⟩

theorem fibOKC_spec {QK : ℕ → ℕ}
    (hQK : ∀ e < 512, QK e = KernelCo2SmithS.nfS (e / 256) (e % 256)) {F : ℕ → ℕ} {er nr j : ℕ}
    (her : er < 512) (h : fibOKC QK F er nr j = true) :
    fld21 (F j) 0 < 512 ∧ (j = 0 ∨ fld21 (F (j - 1)) 0 < fld21 (F j) 0) ∧
      cE (fld21 (F j) 1) (fld21 (F j) 2) * cE er nr =
        cE (fld21 (F j) 0) nr * cE (fld21 (F j) 1) (fld21 (F j) 2) := by
  unfold fibOKC at h
  simp only [letB_eq, Bool.and_eq_true, Nat.blt_eq, Nat.beq_eq, Bool.or_eq_true] at h
  obtain ⟨⟨⟨he2, heh⟩, hord⟩, hrows⟩ := h
  refine ⟨he2, hord, ?_⟩
  have hH := repK_cE hQK heh (fld21 (F j) 2)
  exact (cz_eq_iff (repK_czmul hH (repK_cE hQK her nr))
    (repK_czmul (repK_cE hQK he2 nr) hH)).2 hrows

end CC

end CertificateChecks.KernelCo2Census

end

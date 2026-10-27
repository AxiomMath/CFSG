module

public import CFSG.RankThree.PartOne.K159H.O3Class

public noncomputable section

namespace CFSG.RankThree.PartOne.K159H

open CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.LocalAnalysis.ComponentInitial.OrthogonalSplit
  CFSG.ClassicalGroups.Orthogonal QuadraticMap CFSG.LieType.Universal.Spin

variable {K : Type} [Field K] {A : Type} [AddCommGroup A] [Module K A] {r : ℕ}
  (qA : QuadraticForm K A) (S : Subgroup (Fin r → Kˣ))

@[expose] def CO : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) ⊓
    Subgroup.centralizer (torH K A r '' (S : Set (Fin r → Kˣ)))

variable {qA S}

theorem mem_CO {g : ((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)} :
    g ∈ CO qA S ↔ g ∈ TauCeti.QuadraticMap.orthogonalGroup (quadTail r qA) ∧
      ∀ d ∈ S, g * torH K A r d = torH K A r d * g := by
  rw [CO, Subgroup.mem_inf, Subgroup.mem_centralizer_iff]
  refine and_congr_right fun _ => ?_
  constructor
  · intro h d hd
    exact (h (torH K A r d) ⟨d, hd, rfl⟩).symm
  · rintro h _ ⟨d, hd, rfl⟩
    exact (h d hd).symm

variable (qA S)

@[expose] def rootSet : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  {g | (∃ (t : K) (j j' : Fin r ⊕ Fin r), coordIdx j ≠ coordIdx j' ∧ SimOn S j j' ∧ g = rEl qA t j j') ∨
    (∃ (j : Fin r ⊕ Fin r) (a : A), TrivOn S j ∧
      g = eichler (quadTail r qA) (hypVec K A j) ((0 : Fin r ⊕ Fin r → K), a))}

@[expose] def Rts : Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  Subgroup.closure (rootSet qA S)

@[expose] def Tor (K : Type) [Field K] (A : Type) [AddCommGroup A] [Module K A] (r : ℕ) :
    Subgroup (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] ((Fin r ⊕ Fin r → K) × A)) :=
  (torH K A r).range

variable {qA S}

theorem torH_conj_rEl (d : Fin r → Kˣ) (t : K) (j j' : Fin r ⊕ Fin r) :
    torH K A r d * rEl qA t j j' * (torH K A r d)⁻¹ =
      rEl qA (t * ((wt d j'.swap : K) * wt d j)) j j' := by
  unfold rEl
  rw [eichler_conj (torH_mem_orth qA d), map_smul, torH_hypVec, torH_hypVec, smul_smul,
    eichler_smul_left, smul_smul]
  congr 2
  ring

theorem rEl_comm_torH {j j' : Fin r ⊕ Fin r} (h : SimOn S j j') {d : Fin r → Kˣ} (hd : d ∈ S) (t : K) :
    rEl qA t j j' * torH K A r d = torH K A r d * rEl qA t j j' := by
  have h1 := torH_conj_rEl (qA := qA) d t j j'
  have h2 : (wt d j'.swap : K) * wt d j = 1 := by
    rw [wt_swap, ← h d hd]
    simp
  rw [h2, mul_one] at h1
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem torH_snd_zero (d : Fin r → Kˣ) (a : A) :
    torH K A r d ((0 : Fin r ⊕ Fin r → K), a) = ((0 : Fin r ⊕ Fin r → K), a) :=
  Prod.ext (funext fun c => by simp [torH_fst]) rfl

theorem eichler_tail_comm_torH {j : Fin r ⊕ Fin r} (hj : TrivOn S j) (a : A) {d : Fin r → Kˣ}
    (hd : d ∈ S) :
    eichler (quadTail r qA) (hypVec K A j) ((0 : Fin r ⊕ Fin r → K), a) * torH K A r d =
      torH K A r d * eichler (quadTail r qA) (hypVec K A j) ((0 : Fin r ⊕ Fin r → K), a) := by
  have h1 := eichler_conj (torH_mem_orth qA d) (hypVec K A j) ((0 : Fin r ⊕ Fin r → K), a)
  rw [torH_hypVec, torH_snd_zero, hj d hd, Units.val_one, one_smul] at h1
  rw [mul_inv_eq_iff_eq_mul] at h1
  exact h1.symm

theorem rootSet_le_CO : rootSet qA S ⊆ (CO qA S : Set (((Fin r ⊕ Fin r → K) × A) ≃ₗ[K] _)) := by
  rintro g (⟨t, j, j', -, hsim, rfl⟩ | ⟨j, a, hj, rfl⟩)
  · exact mem_CO.2 ⟨rEl_mem_orth qA t j j', fun d hd => rEl_comm_torH hsim hd t⟩
  · exact mem_CO.2 ⟨eichler_mem_orthogonalGroup _ _ _, fun d hd => eichler_tail_comm_torH hj a hd⟩

theorem Rts_le_CO : Rts qA S ≤ CO qA S := (Subgroup.closure_le _).2 rootSet_le_CO

theorem torH_mem_CO (d : Fin r → Kˣ) : torH K A r d ∈ CO qA S :=
  mem_CO.2 ⟨torH_mem_orth qA d, fun d' _ => by rw [← map_mul, ← map_mul, mul_comm]⟩

theorem rEl_mem_rootSet {t : K} {j j' : Fin r ⊕ Fin r} (h : coordIdx j ≠ coordIdx j') (hs : SimOn S j j') :
    rEl qA t j j' ∈ rootSet qA S := Or.inl ⟨t, j, j', h, hs, rfl⟩

theorem rEl_mem_Rts {t : K} {j j' : Fin r ⊕ Fin r} (h : coordIdx j ≠ coordIdx j') (hs : SimOn S j j') :
    rEl qA t j j' ∈ Rts qA S := Subgroup.subset_closure (rEl_mem_rootSet h hs)

theorem eichler_tail_mem_Rts {j : Fin r ⊕ Fin r} (hj : TrivOn S j) (a : A) :
    eichler (quadTail r qA) (hypVec K A j) ((0 : Fin r ⊕ Fin r → K), a) ∈ Rts qA S :=
  Subgroup.subset_closure (Or.inr ⟨j, a, hj, rfl⟩)

end CFSG.RankThree.PartOne.K159H

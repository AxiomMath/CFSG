module

public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Inv
public import CFSG.LocalAnalysis.ComponentClassification.CatFactsSmallPSp43Model
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42AutLists
public import CFSG.Assembly.QuasithinDefs
public import CFSG.Quasithin.Background.Basic
public import CFSG.Quasithin.Background.F2Equiv
public import CFSG.Quasithin.Vol2.GoldschmidtF431U42Pair5

public section

namespace CFSG.Quasithin.H13.F431.U42Aut

open CFSG.Quasithin U42F431 CFSG.Quasithin.H13.F431.U42
open CFSG.ComponentClassification.CatFactsSmall.PSp43 (QA45 QP45 f45)

theorem repL_f45 : RepL f45L f45 := by decide +kernel

theorem f45_sq : f45 * f45 = 1 := by
  refine eq_of_repL (l := comp f45L f45L) (repL_mul repL_f45 repL_f45) ?_
  have : comp f45L f45L = idL := by decide +kernel
  rw [this]
  exact repL_one 45

@[expose] def permL (σ : P45) : PL := (List.finRange 45).map fun i => (σ i : ℕ)

theorem repL_permL (σ : P45) : RepL (permL σ) σ := by
  refine ⟨by simp [permL], fun i => ?_⟩
  simp [permL, List.getD_eq_getElem?_getD]

theorem permL_eq_of_repL {l : PL} {σ : P45} (h : RepL l σ) : permL σ = l :=
  repL_unique (repL_permL σ) h

theorem card_A : Nat.card QA45.originalSubgroup = 51840 := by
  rw [← CFSG.Certificates.RawSchreierDatum.orderCertificate_eq_card _
    CFSG.ComponentClassification.CatFactsSmall.PSp43.QA45_ok]
  exact CFSG.ComponentClassification.CatFactsSmall.PSp43.QA45_valid.2

theorem QA45_closure_eq :
    QA45.originalSubgroup = Subgroup.closure ({x45, y45, f45} : Set P45) := by
  rw [CFSG.ComponentClassification.CatFactsSmall.PSp43.QA45_closure, ← x45_eq, ← y45_eq]

theorem Xs_le_A : Xs ≤ QA45.originalSubgroup := by
  rw [Xs, QA45_closure_eq]
  exact Subgroup.closure_mono (by intro g hg; rcases hg with rfl | rfl <;> simp)

theorem x45_mem_A : x45 ∈ QA45.originalSubgroup := Xs_le_A x45_mem

theorem y45_mem_A : y45 ∈ QA45.originalSubgroup := Xs_le_A y45_mem

theorem f45_mem_A : f45 ∈ QA45.originalSubgroup := by
  rw [QA45_closure_eq]
  exact Subgroup.subset_closure (by simp)

theorem t45_mem_A : t45 ∈ QA45.originalSubgroup := by
  rw [← wordP_t0W]
  exact Xs_le_A (wordP_mem _)

@[expose] def gAP (k : ℕ) : P45 :=
  if k % 4 = 0 then x45 else if k % 4 = 1 then y45 else if k % 4 = 2 then y45⁻¹ else f45

@[expose] def wordAP (w : List ℕ) : P45 := (w.map gAP).prod

theorem repL_gAP (k : ℕ) : RepL (gAL k) (gAP k) := by
  unfold gAL gAP
  split_ifs
  · exact repL_x
  · exact repL_y
  · exact repL_yi
  · exact repL_f45

theorem repL_wordAP (w : List ℕ) : RepL (evalAL w) (wordAP w) := by
  induction w with
  | nil => exact repL_one 45
  | cons k w ih => exact repL_mul (repL_gAP k) ih

theorem x45_inv : x45⁻¹ = x45 := inv_eq_of_mul_eq_one_right x45_mul_self

theorem f45_inv : f45⁻¹ = f45 := inv_eq_of_mul_eq_one_right f45_sq

theorem gAP_mem (k : ℕ) : gAP k ∈ QA45.originalSubgroup := by
  unfold gAP
  split_ifs
  · exact x45_mem_A
  · exact y45_mem_A
  · exact QA45.originalSubgroup.inv_mem y45_mem_A
  · exact f45_mem_A

theorem wordAP_mem (w : List ℕ) : wordAP w ∈ QA45.originalSubgroup :=
  Subgroup.list_prod_mem _ fun g hg => by
    obtain ⟨k, -, rfl⟩ := List.mem_map.1 hg
    exact gAP_mem k

theorem gAP_invLetA (k : ℕ) : gAP (invLetA k) = (gAP k)⁻¹ := by
  have h4 : k % 4 = 0 ∨ k % 4 = 1 ∨ k % 4 = 2 ∨ k % 4 = 3 := by omega
  rcases h4 with h | h | h | h
  · simp only [invLetA, gAP, h]
    simpa using eq_inv_of_mul_eq_one_left x45_mul_self
  · simp [invLetA, gAP, h]
  · simp [invLetA, gAP, h]
  · simp only [invLetA, gAP, h]
    simpa using eq_inv_of_mul_eq_one_left f45_sq

theorem wordAP_append (a b : List ℕ) : wordAP (a ++ b) = wordAP a * wordAP b := by
  simp [wordAP, List.map_append, List.prod_append]

theorem wordAP_invAL (w : List ℕ) : wordAP (invAL w) = (wordAP w)⁻¹ := by
  induction w with
  | nil => simp [invAL, wordAP]
  | cons k w ih =>
    have : invAL (k :: w) = invAL w ++ [invLetA k] := by simp [invAL]
    rw [this, wordAP_append, ih, show wordAP [invLetA k] = gAP (invLetA k) by simp [wordAP],
      gAP_invLetA, show wordAP (k :: w) = gAP k * wordAP w by simp [wordAP], mul_inv_rev]

@[expose] def fhat : P45 := f45 * t45

@[expose] def fhatL : PL := comp f45L t0L

theorem repL_fhat : RepL fhatL fhat := repL_mul repL_f45 repL_t45

theorem fhat_mem : fhat ∈ QA45.originalSubgroup :=
  QA45.originalSubgroup.mul_mem f45_mem_A t45_mem_A

theorem fhat_sq : fhat * fhat = 1 := by
  refine eq_of_repL (l := comp fhatL fhatL) (repL_mul repL_fhat repL_fhat) ?_
  have : comp fhatL fhatL = idL := by decide +kernel
  rw [this]
  exact repL_one 45

theorem fhat_zero : fhat 0 = 0 := by
  apply Fin.ext
  rw [← (repL_fhat.2 0)]
  decide +kernel

theorem fhat_line : fhat '' L0S = L0S := by
  rw [L0S, image_lineSet repL_fhat (by decide),
    lineSet_eq_of_sameSet (by decide +kernel : sameSet (imgSet fhatL L0) L0 = true)]

theorem sign_fhat : Equiv.Perm.sign fhat = -1 := by
  rw [fhat, map_mul]
  have h1 : Equiv.Perm.sign f45 = -1 := by decide +kernel
  have h2 : Equiv.Perm.sign t45 = 1 := by decide +kernel
  rw [h1, h2]
  rfl

theorem sign_of_mem_Xs {g : P45} (hg : g ∈ QP45.originalSubgroup) : Equiv.Perm.sign g = 1 := by
  have h : QP45.originalSubgroup ≤ (Equiv.Perm.sign : P45 →* ℤˣ).ker := by
    rw [CFSG.ComponentClassification.CatFactsSmall.PSp43.QP45_closure, Subgroup.closure_le]
    rintro g (rfl | rfl)
    · rw [← x45_eq]
      exact (MonoidHom.mem_ker).2 (by decide +kernel)
    · rw [← y45_eq]
      exact (MonoidHom.mem_ker).2 (by decide +kernel)
  exact (MonoidHom.mem_ker).1 (h hg)

theorem fhat_not_mem_QP45 : fhat ∉ QP45.originalSubgroup := fun h => by
  have := sign_of_mem_Xs h
  rw [sign_fhat] at this
  exact absurd this (by decide)

end CFSG.Quasithin.H13.F431.U42Aut

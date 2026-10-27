module

public import CFSG.Quasithin.Background.F7TwoInvExcBasic
public import CFSG.Quasithin.Background.F7TwoInvTitsInputs
public import CFSG.Sporadic.Schreier.TitsStab

public section

namespace CFSG.Quasithin.F7Two

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.Schreier.Tits

theorem rep_invTitsComm {c d : Array ℕ} {x y : Equiv.Perm (Fin 1755)} (hc : Rep 1755 c x)
    (hd : Rep 1755 d y) (hdi : isInvA 1755 d (invCand 1755 d) = true) :
    Rep 1755 (invTitsComm c d) (x * y * (x * y⁻¹)) :=
  rep_compA (rep_compA hc hd) (rep_compA hc (rep_inv_of_isInvA hd hdi))

theorem rep_invTitsPow {a : Array ℕ} {x : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a x) (k : ℕ) :
    Rep 1755 (invTitsPow a k) (x ^ k) := by
  induction k with
  | zero => simpa [invTitsPow] using (rep_idA : Rep 1755 (idA 1755) 1)
  | succ k ih => rw [invTitsPow, pow_succ']; exact rep_compA ha ih

theorem invTitsHasOrder_spec {a : Array ℕ} {x : Equiv.Perm (Fin 1755)} (ha : Rep 1755 a x)
    {p : ℕ} (h : invTitsHasOrder a p = true) : x ^ p = 1 ∧ x ≠ 1 := by
  simp only [invTitsHasOrder, Bool.and_eq_true, Bool.not_eq_true'] at h
  refine ⟨(eqA_iff (rep_invTitsPow ha p) rep_idA).1 h.1, fun h1 => ?_⟩
  have := (eqA_iff ha rep_idA).2 h1
  rw [h.2] at this
  exact Bool.false_ne_true this

theorem titsT_eq_titsDGen {j : ℕ} (hj : j < 2) :
    titsT j = titsDGen j :=
  titsDerived_perm hj

@[expose] noncomputable def titsGenD (j : ℕ) (hj : j < 2) : titsD :=
  ⟨titsT j, titsT_mem_titsD (by omega)⟩

theorem not_isPGroup_comm_titsD {r : titsD} {a : Array ℕ}
    (hra : Rep 1755 a (r : Equiv.Perm (Fin 1755))) (hsq : r * r = 1) {j : ℕ} (hj : j < 2)
    {k : ℕ} (hk : k.Prime) (hk2 : k ≠ 2)
    (h : invTitsHasOrder (invTitsComm a titsDerivedArrs[j]!) k = true) :
    ¬ IsPGroup 2 ↥(Subgroup.zpowers (r * titsGenD j hj * r⁻¹ * (titsGenD j hj)⁻¹)) := by
  have hdi : isInvA 1755 titsDerivedArrs[j]! (invCand 1755 titsDerivedArrs[j]!) = true :=
    isInvA_of_allPermsOK titsChains_check.2.2.2.2.2.2.1 (by rw [titsDerivedArrs_size]; omega)
  have hc := rep_invTitsComm hra (titsT_rep (by omega : j < 13)) hdi
  obtain ⟨hpow, hne⟩ := invTitsHasOrder_spec hc h
  have hr2 : (r : Equiv.Perm (Fin 1755)) * r = 1 :=
    congrArg (fun v : titsD => (v : Equiv.Perm (Fin 1755))) hsq
  have hinv : (r : Equiv.Perm (Fin 1755))⁻¹ = r := inv_eq_of_mul_eq_one_right hr2
  have hval : ((r * titsGenD j hj * r⁻¹ * (titsGenD j hj)⁻¹ : titsD) : Equiv.Perm (Fin 1755)) =
      (r : Equiv.Perm (Fin 1755)) * titsT j * ((r : Equiv.Perm (Fin 1755)) * (titsT j)⁻¹) := by
    simp only [titsGenD, Subgroup.coe_mul, Subgroup.coe_inv, hinv, mul_assoc]
  refine not_isPGroup_two_zpowers_of_pow_prime hk hk2 (Subtype.ext ?_) (fun h1 => hne ?_)
  · simp only [Subgroup.coe_pow, hval, Subgroup.coe_one]
    exact hpow
  · rw [← hval, h1]
    rfl

theorem invAutGen_titsD_conj_of_check {w gw : List ℤ} {p q : ℕ}
    (hp : p.Prime) (hp2 : p ≠ 2) (hq : q.Prime) (hq2 : q ≠ 2)
    (h : invTitsClassCheck w gw p q = true) {u : titsD}
    (hu : IsConj (⟨wordIn 13 titsT w, wordIn_titsT_mem_titsD w⟩ : titsD) u) :
    InvAutGen titsD (MulAut.conj u) := by
  simp only [invTitsClassCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨hw, hgw⟩, hgi⟩, hsq⟩, ho0⟩, ho1⟩ := h
  set gD : titsD := ⟨wordIn 13 titsT gw, wordIn_titsT_mem_titsD gw⟩ with hgD
  set zD : titsD := ⟨wordIn 13 titsT w, wordIn_titsT_mem_titsD w⟩ with hzD
  have hg := rep_wordArr_titsT (w := gw) hgw
  have hz := rep_wordArr_titsT (w := w) hw
  have hr : Rep 1755 (conjArr (wordArr 1755 titsDerivedArrs gw) (wordArr 1755 titsDerivedArrs w))
      ((gD * zD * gD⁻¹ : titsD) : Equiv.Perm (Fin 1755)) :=
    rep_compA (rep_compA hg hz) (rep_inv_of_isInvA hg hgi)
  have hsq' : (gD * zD * gD⁻¹) * (gD * zD * gD⁻¹) = 1 :=
    Subtype.ext (eq_of_eqA (rep_compA hr hr) rep_idA hsq)
  have hgen : Subgroup.closure ((↑) ⁻¹' (Set.range fun j : Fin 2 => titsDGen j) : Set titsD) =
      ⊤ := Subgroup.closure_closure_coe_preimage
  have hconj : InvAutGen titsD (MulAut.conj (gD * zD * gD⁻¹)) := by
    refine invAutGen_conj_of_generators (fun x hx => ?_) hgen
    obtain ⟨⟨j, hj⟩, hjx⟩ := hx
    have hx' : x = titsGenD j hj := Subtype.ext (hjx.symm.trans (titsT_eq_titsDGen hj).symm)
    rw [hx']
    interval_cases j
    · exact not_isPGroup_comm_titsD hr hsq' (by norm_num) hp hp2 ho0
    · exact not_isPGroup_comm_titsD hr hsq' (by norm_num) hq hq2 ho1
  obtain ⟨c, hc⟩ := isConj_iff.1 hu
  refine invAutGen_conj_of_isConj (r := gD * zD * gD⁻¹) (isConj_iff.2 ⟨c * gD⁻¹, ?_⟩) hconj
  rw [← hc]
  group

end CFSG.Quasithin.F7Two

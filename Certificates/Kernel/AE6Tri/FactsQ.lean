module

public import Certificates.Kernel.AE6Tri.FactsG
public import Certificates.Kernel.AE6Tri.ChecksC

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.AE6Tri CFSG.KD.AE6Tri
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.EvenSmallLie.OmegaEight (omegaT)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

theorem qw_get : ∀ x : Fin 4, qw.getD x.val [] = (ae6TriQWords x).map (List.map Fin.val) := by
  decide

theorem qw_len : qw.length = 4 := by decide

theorem qg_len : qg.length = 4 := by decide

theorem qg_len_eq (x : Nat) : (qg.getD x []).length = (qw.getD x []).length := by
  by_cases hx : x < 4
  · interval_cases x <;> decide
  · rw [List.getD_eq_default _ _ (by rw [qg_len]; omega),
      List.getD_eq_default _ _ (by rw [qw_len]; omega)]
    rfl

theorem delta_get' : ∀ (k : Fin 3) (i : Fin 8),
    (delta.getD k.val []).getD i.val [] = (ae6Delta k i).map Fin.val := by decide

theorem dg_len : dg.length = 3 := by decide

theorem delta_len : delta.length = 3 := by decide

theorem dg_len_eq (k : Nat) : (dg.getD k []).length = (delta.getD k []).length := by
  by_cases hk : k < 3
  · interval_cases k <;> decide
  · rw [List.getD_eq_default _ _ (by rw [dg_len]; omega),
      List.getD_eq_default _ _ (by rw [delta_len]; omega)]
    rfl

theorem dq_get : ∀ (k : Fin 3) (x : Fin 4), (dq.getD k.val []).getD x.val 0 = (ae6DeltaQ k x).val := by
  decide

theorem dq_len : dq.length = 3 := by decide

theorem ml_of : ∀ i : Fin 8, i ∈ ae6MLetters → ∃ t < 5, ml.getD t 0 = i.val := by decide

theorem ml_len : ml.length = 5 := by decide

@[expose] noncomputable def qP (x j : Nat) : Equiv.Perm (Fin 360) := wv gP ((qw.getD x []).getD j [])

theorem qRep : ∀ x j, Orb.PRep 360 9 ((qg.getD x []).getD j (pidn 360 9)) (qP x j) := by
  intro x j
  by_cases hj : j < (qw.getD x []).length
  · have hx : x < qw.length := by
      by_contra h
      rw [List.getD_eq_default _ _ (by omega)] at hj
      simp at hj
    exact pinOK_sound gRep kPinQ x hx j hj
  · rw [List.getD_eq_default _ _ (by rw [qg_len_eq]; omega), qP,
      List.getD_eq_default _ _ (by omega), wv_nil]
    exact Orb.prep_pidn (by norm_num) (by norm_num)

@[expose] noncomputable def dlP (k c : Nat) : Equiv.Perm (Fin 360) :=
  wv gP ((delta.getD k []).getD c [])

theorem dRepK : ∀ k c, Orb.PRep 360 9 ((dg.getD k []).getD c (pidn 360 9)) (dlP k c) := by
  intro k c
  by_cases hc : c < (delta.getD k []).length
  · have hk : k < delta.length := by
      by_contra h
      rw [List.getD_eq_default _ _ (by omega)] at hc
      simp at hc
    exact pinOK_sound gRep kPinD k hk c hc
  · rw [List.getD_eq_default _ _ (by rw [dg_len_eq]; omega), dlP,
      List.getD_eq_default _ _ (by omega), wv_nil]
    exact Orb.prep_pidn (by norm_num) (by norm_num)

theorem qP_word (x : Fin 4) (j : Nat) (hj : j < (ae6TriQWords x).length) :
    qP x.val j = ((ae6Word (ae6TriQWords x)[j] : AE6Om) : Equiv.Perm (Fin 360)) := by
  rw [qP, qw_get, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, coe_ae6Word]

theorem qP_mem (x : Fin 4) (j : Nat) : qP x.val j ∈ (ae6TriQ x).map omegaT.subtype := by
  by_cases hj : j < (ae6TriQWords x).length
  · rw [qP_word x j hj]
    exact ⟨_, Subgroup.subset_closure ⟨_, List.getElem_mem hj, rfl⟩, rfl⟩
  · rw [qP, qw_get, List.getD_eq_default _ _ (by simpa using hj), wv_nil]
    exact Subgroup.one_mem _

theorem prod_mem_Q (x : Fin 4) (u : List Nat) :
    (u.map (qP x.val)).prod ∈ (ae6TriQ x).map omegaT.subtype := by
  refine Subgroup.list_prod_mem _ fun y hy => ?_
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hy
  exact qP_mem x j

theorem mem_of_coe {H : Subgroup AE6Om} {g : AE6Om}
    (h : (g : Equiv.Perm (Fin 360)) ∈ H.map omegaT.subtype) : g ∈ H :=
  (Subgroup.mem_map_iff_mem omegaT.subtype_injective).1 h

theorem q_norm : ∀ x : Fin 4, ∀ w ∈ ae6TriQWords x, ∀ i ∈ ae6MLetters,
    A6.curtisGen i * ae6Word w * A6.curtisGen i ∈ ae6TriQ x := by
  intro x w hw i hi
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  obtain ⟨t, ht, hti⟩ := ml_of i hi
  have h := qnOK_sound gRep qRep kQNorm x.val (by rw [qw_len]; exact x.isLt) j
    (by rw [qw_get]; simpa using hj) t (by rw [ml_len]; exact ht)
    (by rw [qg_len_eq, qw_get]; simpa using hj)
  rw [hti, ← coe_curtisGen i, qP_word x j hj] at h
  apply mem_of_coe
  change (A6.curtisGen i : Equiv.Perm (Fin 360)) * (ae6Word (ae6TriQWords x)[j] : AE6Om) *
    (A6.curtisGen i : Equiv.Perm (Fin 360)) ∈ _
  rw [h]
  exact prod_mem_Q x _

theorem q_dist : ∀ x y : Fin 4, x ≠ y → ae6TriQ x ≠ ae6TriQ y := by
  intro x y hxy he
  obtain ⟨hc, hn⟩ := qzOK_sound gRep qRep qzJ_lt kQDist x.val (by rw [qw_len]; exact x.isLt)
    y.val (by rw [qw_len]; exact y.isLt) (Fin.val_injective.ne hxy)
  apply hn
  have hcomm : ∀ g ∈ (ae6TriQ y).map omegaT.subtype,
      wv gP (at2 qzW [] y.val x.val) * g = g * wv gP (at2 qzW [] y.val x.val) := by
    rw [ae6TriQ, MonoidHom.map_closure]
    refine comm_of_closure ?_
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
    have := hc j (by rw [qg_len_eq, qw_get]; simpa using hj)
    rw [qP_word y j hj] at this
    exact this
  apply hcomm
  rw [← he]
  exact qP_mem x _

theorem word_append (a b : List (Fin 8)) : ae6Word (a ++ b) = ae6Word a * ae6Word b := by
  simp [ae6Word, List.prod_append]

theorem dlP_eq (k : Fin 3) (c : Fin 8) :
    dlP k.val c.val = ((ae6Word (ae6Delta k c) : AE6Om) : Equiv.Perm (Fin 360)) := by
  rw [dlP, delta_get', coe_ae6Word]

theorem dW_eq (k : Fin 3) : ∀ w : List (Fin 8),
    ((w.map Fin.val).map (dlP k.val)).prod = ((ae6Word (ae6DeltaW k w) : AE6Om) : Equiv.Perm (Fin 360))
  | [] => by simp [ae6DeltaW, ae6Word]
  | c :: w => by
    have e : ae6DeltaW k (c :: w) = ae6Delta k c ++ ae6DeltaW k w := by simp [ae6DeltaW]
    rw [List.map_cons, List.map_cons, List.prod_cons, dW_eq k w, dlP_eq, e, word_append,
      Subgroup.coe_mul]

theorem q_delta : ∀ (k : Fin 3) (x : Fin 4), ∀ w ∈ ae6TriQWords x,
    ae6Word (ae6DeltaW k w) ∈ ae6TriQ (ae6DeltaQ k x) := by
  intro k x w hw
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hw
  have h := qdOK_sound dRepK qRep kQDelta k.val (by rw [dq_len]; exact k.isLt) x.val
    (by rw [qw_len]; exact x.isLt) j (by rw [qw_get]; simpa using hj)
  rw [qw_get, List.getD_eq_getElem _ _ (by simpa using hj), List.getElem_map, dW_eq, dq_get] at h
  apply mem_of_coe
  rw [h]
  exact prod_mem_Q (ae6DeltaQ k x) _

theorem kw_get : ∀ s : Fin 3, kw.getD s.val [] = (ae6KWord s).map Fin.val := by decide

theorem cw_get : ∀ k : Fin 3, cw.getD k.val [] = (ae6TriMemC k).map Fin.val := by decide

theorem kgw_words : kgw = [(ae6KWord 0).map Fin.val, (ae6KWord 1).map Fin.val] := by decide

theorem kw_len : kw.length = 3 := by decide

theorem kgw_mem (i : Nat) : wv gP (kgw.getD i []) ∈ ae6ModelK.map omegaT.subtype := by
  rw [kgw_words]
  rcases Nat.lt_or_ge i 2 with hi | hi
  · interval_cases i
    · rw [List.getD_cons_zero, ← coe_ae6Word]
      exact ⟨_, Subgroup.subset_closure (Set.mem_insert _ _), rfl⟩
    · rw [List.getD_cons_succ, List.getD_cons_zero, ← coe_ae6Word]
      exact ⟨_, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl), rfl⟩
  · rw [List.getD_eq_default _ _ (by simpa using hi), wv_nil]
    exact Subgroup.one_mem _

theorem td_k0 : ∀ k s : Fin 3,
    ae6Word (ae6DeltaW k (ae6KWord s)) ∈ CFSG.ClassicalInvolution.Generic.conjSub
      (ae6Word (ae6TriMemC k)) ae6ModelK := by
  intro k s
  have h := kcOK_sound gRep dRepK kKC k.val (by rw [kU_len]; exact k.isLt) s.val
    (by rw [kw_len]; exact s.isLt)
  rw [kw_get, cw_get, dW_eq, ← coe_ae6Word] at h
  rw [CFSG.ClassicalInvolution.Generic.mem_conjSub_iff]
  apply mem_of_coe
  have hu : (((kU.getD k.val []).getD s.val []).map fun i => wv gP (kgw.getD i [])).prod ∈
      ae6ModelK.map omegaT.subtype := by
    refine Subgroup.list_prod_mem _ fun y hy => ?_
    obtain ⟨i, -, rfl⟩ := List.mem_map.1 hy
    exact kgw_mem i
  have e : (((ae6Word (ae6TriMemC k))⁻¹ * ae6Word (ae6DeltaW k (ae6KWord s)) *
      ae6Word (ae6TriMemC k) : AE6Om) : Equiv.Perm (Fin 360)) =
      (((kU.getD k.val []).getD s.val []).map fun i => wv gP (kgw.getD i [])).prod := by
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, mul_assoc, h, ← mul_assoc,
      inv_mul_cancel, one_mul]
  rw [e]
  exact hu

end CertificateChecks.KernelAE6Tri

end

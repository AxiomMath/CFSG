module

public import Certificates.Kernel.AE6Tri.FactsTA2
public import Certificates.Certificate517532Base
public import Certificates.Kernel.AE6Tri.FactsQ
public import Certificates.Kernel.AE6Tri.FactsTA

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAE6Tri

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KC.AE6Tri CFSG.KD.AE6Tri CFSG.KD.AE6TA
open CertificateChecks.KernelAE6TriTA
open CFSG.ClassicalInvolution.Generic
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3
open CFSG.EvenSmallLie.OmegaEight (omegaT)
open CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpV3.A6S

theorem lettersIn_bit {L : Nat} : ∀ w : List Nat, lettersIn L w = true → ∀ c ∈ w, bit L c = true
  | [], _ => by simp
  | c :: w, h => by
    have h' : bAnd(bit L c, lettersIn L w) = true := h
    rw [Orb.bAnd_eq, Bool.and_eq_true] at h'
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · exact h'.1
    · exact lettersIn_bit w h'.2 d hd

theorem taB_eq : taB = Certificates.AE6CertB.triB 2 := by decide

theorem mem_stab_iff (x : AE6Om) :
    x ∈ Certificates.ae6TriStab 2 ↔ (x : Equiv.Perm (Fin 360)) ∈ setStab (finOfL taB) := by
  rw [taB_eq]
  exact Iff.rfl

theorem taPW_eq : taPW = ae6TriProf.map (List.map Fin.val) := by decide

theorem taPW_len : taPW.length = 15 := by decide

theorem prod_word (f : Nat → Equiv.Perm (Fin 360)) {F : Fin 8 → List (Fin 8)}
    (hf : ∀ c : Fin 8, f c.val = ((ae6Word (F c) : AE6Om) : Equiv.Perm (Fin 360))) :
    ∀ w : List (Fin 8),
      ((w.map Fin.val).map f).prod = ((ae6Word (w.flatMap F) : AE6Om) : Equiv.Perm (Fin 360))
  | [] => by simp [ae6Word]
  | c :: w => by
    rw [List.map_cons, List.map_cons, List.prod_cons, prod_word f hf w, hf c, List.flatMap_cons,
      word_append, Subgroup.coe_mul]

theorem gRepD (k : Nat) : GRep (nthD dg [] k) (dlP k) := by
  intro c
  rw [nthD_eq]
  exact dRepK k c

theorem dW' (k : Fin 3) (n : Nat) (hn : k.val = n) (w : List (Fin 8)) :
    ((w.map Fin.val).map (dlP n)).prod = ((ae6Word (ae6DeltaW k w) : AE6Om) : Equiv.Perm (Fin 360)) := by
  subst hn
  exact dW_eq k w

theorem delta_get'' (k : Fin 3) (n : Nat) (hn : k.val = n) (i : Fin 8) :
    (nthD delta [] n).getD i.val [] = (ae6Delta k i).map Fin.val := by
  subst hn
  rw [nthD_eq, delta_get']

theorem dd_word (k k' : Fin 3) (n n' : Nat) (hn : k.val = n) (hn' : k'.val = n') (c : Fin 8) :
    wv (dlP n) ((nthD delta [] n').getD c.val []) =
      ((ae6Word (ae6DeltaW k (ae6Delta k' c)) : AE6Om) : Equiv.Perm (Fin 360)) := by
  rw [delta_get'' k' n' hn', wv, dW' k n hn]

theorem ddd_word (c : Fin 8) :
    (((nthD delta [] 0).getD c.val []).map fun c' =>
      wv (dlP 0) ((nthD delta [] 1).getD c' [])).prod =
      ((ae6Word ((ae6Delta 0 c).flatMap fun c' => ae6DeltaW 0 (ae6Delta 1 c')) : AE6Om) :
        Equiv.Perm (Fin 360)) := by
  rw [delta_get'' 0 0 rfl c]
  exact prod_word (fun c' => wv (dlP 0) ((nthD delta [] 1).getD c' []))
    (fun c' => dd_word 0 1 0 1 rfl rfl c') _

theorem flat2 (k k' : Fin 3) (w : List (Fin 8)) :
    ae6DeltaW k (ae6DeltaW k' w) = w.flatMap fun c => ae6DeltaW k (ae6Delta k' c) := by
  simp only [ae6DeltaW, List.flatMap_assoc]

theorem rep_vals {ℓ : Nat → Equiv.Perm (Fin 360)} (hℓ : LRep taLL ℓ) (j : Nat) (hj : j < 6)
    (t : Fin 6) : ℓ (nthN (nthD taSI [] j) t.val) =
      ((ae6Word (ae6TriRep 0 ⟨j, hj⟩ (ae6TriGen₀ t)) : AE6Om) : Equiv.Perm (Fin 360)) := by
  have ht : t.val < tg0.length := by rw [tg0_len]; exact t.isLt
  interval_cases j
  · rw [(vOK_sound hℓ gRep kTaS0 t.val ht).2, tg0_get, ← coe_ae6Word]
    rfl
  · rw [(vOK_sound hℓ (gRepD 0) kTaS1 t.val ht).2, tg0_get, wv, dW' 0 0 rfl]
    rfl
  · rw [(vOK_sound hℓ (gRepD 1) kTaS2 t.val ht).2, tg0_get, wv, dW' 1 1 rfl]
    rfl
  · rw [(vOKd_sound hℓ (gRepD 1) kTaS3 t.val ht).2, tg0_get,
      prod_word (fun c => wv (dlP 1) ((nthD delta [] 0).getD c []))
        (fun c => dd_word 1 0 1 0 rfl rfl c)]
    have e : ae6TriRep 0 ⟨3, hj⟩ (ae6TriGen₀ t) = ae6DeltaW 1 (ae6DeltaW 0 (ae6TriGen₀ t)) := rfl
    rw [e, flat2]
  · rw [(vOKd_sound hℓ (gRepD 0) kTaS4 t.val ht).2, tg0_get,
      prod_word (fun c => wv (dlP 0) ((nthD delta [] 1).getD c []))
        (fun c => dd_word 0 1 0 1 rfl rfl c)]
    have e : ae6TriRep 0 ⟨4, hj⟩ (ae6TriGen₀ t) = ae6DeltaW 0 (ae6DeltaW 1 (ae6TriGen₀ t)) := rfl
    rw [e, flat2]
  · rw [(vOKdd_sound hℓ (gRepD 0) kTaS5 t.val ht).2, tg0_get,
      prod_word (fun c => (((nthD delta [] 0).getD c []).map fun c' =>
        wv (dlP 0) ((nthD delta [] 1).getD c' [])).prod) ddd_word]
    have e : ae6TriRep 0 ⟨5, hj⟩ (ae6TriGen₀ t) =
        ae6DeltaW 0 (ae6DeltaW 1 (ae6DeltaW 0 (ae6TriGen₀ t))) := rfl
    rw [e]
    simp only [ae6DeltaW, List.flatMap_assoc]

theorem prod_map_coe {ℓ : Nat → Equiv.Perm (Fin 360)} {z : Nat → Nat} {y : Fin 6 → AE6Om}
    (hz : ∀ i : Fin 6, ℓ (z i.val) = (y i : Equiv.Perm (Fin 360))) (u : List (Fin 6)) :
    ((u.map Fin.val).map fun j => ℓ (z j)).prod =
      (((u.map y).prod : AE6Om) : Equiv.Perm (Fin 360)) := by
  rw [coe_prod_map, List.map_map]
  congr 1
  exact List.map_congr_left fun i _ => hz i

theorem ta0 :
    (∀ i, ae6Word (ae6TriGen₀ i) ∈ taQ) ∧
    ∀ y : Fin 6 → AE6Om, (∀ i, y i ∈ taQ) →
      (∀ u ∈ ae6TriProf,
        orderOf (u.map y).prod = orderOf (u.map fun i => ae6Word (ae6TriGen₀ i)).prod ∧
        ((u.map y).prod ∈ Certificates.ae6TriStab 2 ↔
          (u.map fun i => ae6Word (ae6TriGen₀ i)).prod ∈ Certificates.ae6TriStab 2) ∧
        ((u.map y).prod ∈ taQ ↔ (u.map fun i => ae6Word (ae6TriGen₀ i)).prod ∈ taQ)) →
      ∃ m ∈ ae6LetterSub ↑ae6MLetters, ∃ j : Fin 6,
        ∀ i, y i = m * ae6Word (ae6TriRep 0 j (ae6TriGen₀ i)) * m⁻¹ := by
  obtain ⟨ℓ, hℓ, h0, hτ, hw, hK, hT, -, hP, hS⟩ := ta0_perm
  have hq := quat_iff hℓ h0 hτ hw hK hT hP
  have hgen : ∀ i : Fin 6, nthN taTI i.val < 168 ∧
      ℓ (nthN taTI i.val) = ((ae6Word (ae6TriGen₀ i) : AE6Om) : Equiv.Perm (Fin 360)) := by
    intro i
    obtain ⟨h1, h2⟩ := hT i.val (by rw [tg0_len]; exact i.isLt)
    refine ⟨h1, ?_⟩
    rw [h2, tg0_get, ← coe_ae6Word]
  refine ⟨fun i => (hq _).2 (mem_lset.2 ⟨_, (hgen i).1, (hgen i).2⟩), ?_⟩
  intro y hy hprof
  choose ai hai hayi using fun i => mem_lset.1 ((hq (y i)).1 (hy i))
  set z : Nat → Nat := fun t => if h : t < 6 then ai ⟨t, h⟩ else 0 with hzdef
  have hz6 : ∀ t < 6, z t < 168 := fun t ht => by
    simp only [hzdef, dif_pos ht]
    exact hai _
  have hzy : ∀ i : Fin 6, ℓ (z i.val) = (y i : Equiv.Perm (Fin 360)) := fun i => by
    simp only [hzdef, dif_pos i.2]
    exact hayi i
  have hgen' : ∀ i : Fin 6, ℓ (nthN taTI i.val) = ((ae6Word (ae6TriGen₀ i) : AE6Om) :
      Equiv.Perm (Fin 360)) := fun i => (hgen i).2
  have hPz : prof ℓ taB taPW taPO taPS taPM z := by
    intro a ha
    have ha15 : a < ae6TriProf.length := by
      rw [taPW_len] at ha
      exact ha
    have hu : taPW.getD a [] = ae6TriProf[a].map Fin.val := by
      rw [taPW_eq, List.getD_eq_getElem _ _ (by simpa using ha15)]
      simp
    obtain ⟨ho, hs, hm⟩ := hprof _ (List.getElem_mem ha15)
    obtain ⟨o1, s1, m1⟩ := hP a ha
    rw [hu, prod_map_coe hgen'] at o1 s1 m1
    rw [hu, prod_map_coe hzy]
    refine ⟨?_, ?_, ?_⟩
    · rw [Subgroup.orderOf_coe, ho, ← Subgroup.orderOf_coe]
      exact o1
    · rw [← s1, ← mem_stab_iff, ← mem_stab_iff]
      exact hs
    · rw [← m1, ← mem_lset, ← mem_lset, ← hq, ← hq]
      exact hm
  obtain ⟨w, hwM, j, hj, hjt⟩ := hS z hz6 hPz
  obtain ⟨m, hm, hmw⟩ := wv_letterSub (A := ↑ae6MLetters) w fun c hc => by
    have hb := lettersIn_bit w hwM c hc
    have hc8 : c < 8 := bit_lt8 (by norm_num) hb
    exact ⟨hc8, Finset.mem_coe.2 ((mask_iff ⟨c, hc8⟩).1.1 hb)⟩
  refine ⟨m, hm, ⟨j, hj⟩, fun i => Subtype.ext ?_⟩
  have h1 := hjt i.val i.isLt
  rw [hzy i, rep_vals hℓ j hj i, ← hmw] at h1
  rw [← h1, Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv]

end CertificateChecks.KernelAE6Tri

end

module

public import Certificates.Kernel.B433Alt.FiveOK
public import Certificates.Kernel.B433Alt.Base
public import CFSG.Certificates.Kernel.B433Alt.ChainCount
public import CFSG.Certificates.Kernel.B433Alt.Group

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.Certificates.CosetEnumeration
  CertificateChecks.KernelY442 CFSG.KC.Y333


@[expose] noncomputable def vw (l : List ℕ) : Equiv.Perm (Fin 31671) :=
  rho432F (evalWord (yGen 4 3 2) l)

@[expose] noncomputable def tv (W : ℕ → List ℕ) : List ℕ → Equiv.Perm (Fin 31671)
  | [] => 1
  | r :: rs => (if r % 2 = 1 then (vw (W (r / 2)))⁻¹ else vw (W (r / 2))) * tv W rs

theorem beq_one_true {r : ℕ} (h : r % 2 = 1) : Nat.beq (Nat.mod r 2) 1 = true := by
  change Nat.beq (r % 2) 1 = true
  rw [h]
  rfl

theorem beq_one_false {r : ℕ} (h : ¬ r % 2 = 1) : Nat.beq (Nat.mod r 2) 1 = false := by
  change Nat.beq (r % 2) 1 = false
  cases hb : Nat.beq (r % 2) 1
  · rfl
  · exact absurd (Nat.eq_of_beq_eq_true hb) h

theorem vw_nil : vw [] = 1 := by simp [vw, evalWord_nil]

theorem vw_cons (c : ℕ) (l : List ℕ) : vw (c :: l) = rho432F (yGen 4 3 2 c) * vw l := by
  rw [vw, vw, evalWord_cons, map_mul]

theorem vw_reverse (a : List ℕ) : vw a.reverse = (vw a)⁻¹ := by
  rw [vw, vw, evalWord_reverse (yGen_mul_self 4 3 2), map_inv]

theorem lettersOK_iff : ∀ {l : List ℕ}, CFSG.KC.B4A.lettersOK l = true ↔ ∀ c ∈ l, c < 10
  | [] => by simp [CFSG.KC.B4A.lettersOK]
  | c :: l => by
    change andB (Nat.blt c 10) (CFSG.KC.B4A.lettersOK l) = true ↔ _
    rw [andB_iff, lettersOK_iff, Nat.blt_eq]
    simp only [List.mem_cons, forall_eq_or_imp]

theorem evL_spec : ∀ (l : List ℕ), (∀ c ∈ l, c < 10) → ∀ (x : ℕ) (hx : x < 31671),
    (vw l ⟨x, hx⟩ : ℕ) = evL CFSG.KD.B4A.LP l x
  | [], _, x, hx => by rw [vw_nil]; rfl
  | [a], hl, x, hx => by
    rw [vw_cons, vw_nil, mul_one]
    exact tables.letter a (hl a (by simp)) ⟨x, hx⟩
  | a :: b :: t, hl, x, hx => by
    have ha := hl a (by simp)
    have hb := hl b (by simp)
    have ht : ∀ c ∈ t, c < 10 := fun c hc => hl c (by simp [hc])
    have ih := evL_spec t ht x hx
    rw [vw_cons, vw_cons, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply]
    change _ = pget (CFSG.KD.B4A.LP (10 + (10 * a + b))) (evL CFSG.KD.B4A.LP t x)
    have hy : evL CFSG.KD.B4A.LP t x < 31671 := by rw [← ih]; exact Fin.isLt _
    have e : vw t ⟨x, hx⟩ = ⟨_, hy⟩ := Fin.ext ih
    rw [e, tables.pair a ha b hb _ hy]
    have hz : pget (CFSG.KD.B4A.LP b) (evL CFSG.KD.B4A.LP t x) < 31671 := by
      rw [← tables.letter b hb ⟨_, hy⟩]; exact Fin.isLt _
    have e2 : rho432F (yGen 4 3 2 b) ⟨_, hy⟩ = ⟨_, hz⟩ := Fin.ext (tables.letter b hb _)
    rw [e2]
    exact tables.letter a ha _

theorem evR_spec : ∀ (l : List ℕ), (∀ c ∈ l, c < 10) → ∀ (x : ℕ) (hx : x < 31671),
    ((vw l)⁻¹ ⟨x, hx⟩ : ℕ) = evR CFSG.KD.B4A.LP l x
  | [], _, x, hx => by rw [vw_nil, inv_one]; rfl
  | [a], hl, x, hx => by
    rw [← vw_reverse, List.reverse_singleton, vw_cons, vw_nil, mul_one]
    exact tables.letter a (hl a (by simp)) ⟨x, hx⟩
  | a :: b :: t, hl, x, hx => by
    have ha := hl a (by simp)
    have hb := hl b (by simp)
    have ht : ∀ c ∈ t, c < 10 := fun c hc => hl c (by simp [hc])
    change _ = evR CFSG.KD.B4A.LP t (pget (CFSG.KD.B4A.LP (10 + (10 * b + a))) x)
    have h2 : ∀ c < 10, (rho432F (yGen 4 3 2 c))⁻¹ = rho432F (yGen 4 3 2 c) := fun c _ => by
      rw [← map_inv, yGen_inv]
    have hz : pget (CFSG.KD.B4A.LP a) x < 31671 := by
      rw [← tables.letter a ha ⟨x, hx⟩]; exact Fin.isLt _
    have hy : pget (CFSG.KD.B4A.LP (10 + (10 * b + a))) x < 31671 := by
      rw [tables.pair b hb a ha x hx, ← tables.letter b hb ⟨_, hz⟩]
      exact Fin.isLt _
    rw [← evR_spec t ht _ hy]
    rw [vw_cons, vw_cons, mul_inv_rev, mul_inv_rev, Equiv.Perm.mul_apply, Equiv.Perm.mul_apply,
      h2 b hb, h2 a ha]
    have e1 : rho432F (yGen 4 3 2 a) ⟨x, hx⟩ = ⟨_, hz⟩ := Fin.ext (tables.letter a ha _)
    have e2 : rho432F (yGen 4 3 2 b) ⟨_, hz⟩ = ⟨_, hy⟩ :=
      Fin.ext ((tables.letter b hb _).trans (tables.pair b hb a ha x hx).symm)
    rw [e1, e2]

theorem tv_cons (W : ℕ → List ℕ) (r : ℕ) (rs : List ℕ) :
    tv W (r :: rs) = (if r % 2 = 1 then (vw (W (r / 2)))⁻¹ else vw (W (r / 2))) * tv W rs := rfl

theorem evT_spec {W : ℕ → List ℕ} (hW : ∀ t, ∀ c ∈ W t, c < 10) : ∀ (refs : List ℕ)
    (x : ℕ) (hx : x < 31671), (tv W refs ⟨x, hx⟩ : ℕ) = evT CFSG.KD.B4A.LP W refs x
  | [], x, hx => rfl
  | r :: rs, x, hx => by
    have ih := evT_spec hW rs x hx
    have hy : evT CFSG.KD.B4A.LP W rs x < 31671 := by rw [← ih]; exact Fin.isLt _
    rw [tv_cons, Equiv.Perm.mul_apply]
    change _ = Bool.rec (motive := fun _ => ℕ) (evL CFSG.KD.B4A.LP (W (Nat.div r 2)) _)
      (evR CFSG.KD.B4A.LP (W (Nat.div r 2)) _) (Nat.beq (Nat.mod r 2) 1)
    have e : tv W rs ⟨x, hx⟩ = ⟨_, hy⟩ := Fin.ext ih
    rw [e]
    by_cases hr : r % 2 = 1
    · rw [if_pos hr, beq_one_true hr]
      exact evR_spec _ (hW _) _ hy
    · rw [if_neg hr, beq_one_false hr]
      exact evL_spec _ (hW _) _ hy

theorem evTI_spec {W : ℕ → List ℕ} (hW : ∀ t, ∀ c ∈ W t, c < 10) : ∀ (refs : List ℕ)
    (x : ℕ) (hx : x < 31671), ((tv W refs)⁻¹ ⟨x, hx⟩ : ℕ) = evTI CFSG.KD.B4A.LP W refs x
  | [], x, hx => by simp [tv]; rfl
  | r :: rs, x, hx => by
    rw [tv_cons, mul_inv_rev, Equiv.Perm.mul_apply]
    change _ = evTI CFSG.KD.B4A.LP W rs (Bool.rec (motive := fun _ => ℕ)
      (evR CFSG.KD.B4A.LP (W (Nat.div r 2)) x) (evL CFSG.KD.B4A.LP (W (Nat.div r 2)) x)
      (Nat.beq (Nat.mod r 2) 1))
    have key : ∃ hy : (Bool.rec (motive := fun _ => ℕ) (evR CFSG.KD.B4A.LP (W (Nat.div r 2)) x)
        (evL CFSG.KD.B4A.LP (W (Nat.div r 2)) x) (Nat.beq (Nat.mod r 2) 1)) < 31671,
        (if r % 2 = 1 then (vw (W (r / 2)))⁻¹ else vw (W (r / 2)))⁻¹ ⟨x, hx⟩ = ⟨_, hy⟩ := by
      by_cases hr : r % 2 = 1
      · rw [if_pos hr, inv_inv, beq_one_true hr]
        exact ⟨by rw [← evL_spec _ (hW _) x hx]; exact Fin.isLt _, Fin.ext (evL_spec _ (hW _) x hx)⟩
      · rw [if_neg hr, beq_one_false hr]
        exact ⟨by rw [← evR_spec _ (hW _) x hx]; exact Fin.isLt _, Fin.ext (evR_spec _ (hW _) x hx)⟩
    obtain ⟨hy, e⟩ := key
    rw [e]
    exact evTI_spec hW rs _ hy

theorem iter_spec {g : Equiv.Perm (Fin 31671)} {f : ℕ → ℕ}
    (hf : ∀ (x : ℕ) (hx : x < 31671), (g ⟨x, hx⟩ : ℕ) = f x) :
    ∀ (n x : ℕ) (hx : x < 31671), ((g ^ n) ⟨x, hx⟩ : ℕ) = iter f n x
  | 0, x, hx => rfl
  | n + 1, x, hx => by
    have ih := iter_spec hf n x hx
    have hy : iter f n x < 31671 := by rw [← ih]; exact Fin.isLt _
    rw [pow_succ', Equiv.Perm.mul_apply]
    have e : (g ^ n) ⟨x, hx⟩ = ⟨_, hy⟩ := Fin.ext ih
    rw [e]
    exact hf _ hy

theorem belowAll_iff (f : ℕ → Bool) : ∀ n, belowAll n f = true ↔ ∀ i < n, f i = true
  | 0 => by simp [belowAll]
  | n + 1 => by
    change andB (belowAll n f) (f n) = true ↔ _
    rw [andB_iff, belowAll_iff f n]
    constructor
    · rintro ⟨h1, h2⟩ i hi
      rcases Nat.lt_succ_iff_lt_or_eq.1 hi with hi | rfl
      · exact h1 i hi
      · exact h2
    · intro h
      exact ⟨fun i hi => h i (by omega), h n (by omega)⟩

section

theorem fix5_spec {g : Equiv.Perm (Fin 31671)} (hg : g ∈ rho432F.range) {f : ℕ → ℕ}
    (hf : ∀ (x : ℕ) (hx : x < 31671), (g ⟨x, hx⟩ : ℕ) = f x) (h : fix5 f = true) : g = 1 := by
  refine base_eq_one hg fun m hm => ?_
  unfold fix5 at h
  rw [belowAll_iff] at h
  have hb : β5 m = ⟨b5 m, b5_lt m hm⟩ := by rw [β5, dif_pos hm]
  rw [hb]
  apply Fin.ext
  rw [hf]
  exact Nat.eq_of_beq_eq_true (h m hm)

end

theorem vw_mem_range (l : List ℕ) : vw l ∈ rho432F.range := ⟨_, rfl⟩

theorem tv_mem_range (W : ℕ → List ℕ) : ∀ refs, tv W refs ∈ rho432F.range
  | [] => Subgroup.one_mem _
  | r :: rs => by
    rw [tv_cons]
    refine Subgroup.mul_mem _ ?_ (tv_mem_range W rs)
    split_ifs
    · exact Subgroup.inv_mem _ (vw_mem_range _)
    · exact vw_mem_range _

theorem tv_mem {M : Subgroup (Equiv.Perm (Fin 31671))} {W : ℕ → List ℕ}
    (hW : ∀ t, vw (W t) ∈ M) : ∀ refs : List ℕ, tv W refs ∈ M
  | [] => M.one_mem
  | r :: rs => by
    rw [tv_cons]
    refine M.mul_mem ?_ (tv_mem hW rs)
    split_ifs
    · exact M.inv_mem (hW _)
    · exact hW _

@[expose] noncomputable def recV (r : ℕ) : Equiv.Perm (Fin 31671) :=
  if r % 2 = 1 then (rho432F (wVal (yGen 4 3 2) (CFSG.KD.B4A.RW (r / 2))))⁻¹
  else rho432F (wVal (yGen 4 3 2) (CFSG.KD.B4A.RW (r / 2)))

@[expose] noncomputable def recP : List ℕ → Equiv.Perm (Fin 31671)
  | [] => 1
  | r :: rs => recV r * recP rs

theorem evRecI_spec : ∀ (refs : List ℕ), (∀ r ∈ refs, wInH (CFSG.KD.B4A.RW (r / 2)) = true) →
    ∀ (x : ℕ) (hx : x < 31671), ((recP refs)⁻¹ ⟨x, hx⟩ : ℕ) = CFSG.KD.B4AF.evRecI refs x
  | [], _, x, hx => by simp [recP]; rfl
  | r :: rs, hw, x, hx => by
    have hr := hw r (by simp)
    change _ = CFSG.KD.B4AF.evRecI rs (ev1 CFSG.KD.B4A.LP (Bool.rec (motive := fun _ => ℕ)
      (wRev (CFSG.KD.B4A.RW (Nat.div r 2))) (CFSG.KD.B4A.RW (Nat.div r 2))
      (Nat.beq (Nat.mod r 2) 1)) x)
    rw [recP, mul_inv_rev, Equiv.Perm.mul_apply]
    have key : ∃ hy : ev1 CFSG.KD.B4A.LP (Bool.rec (motive := fun _ => ℕ)
        (wRev (CFSG.KD.B4A.RW (Nat.div r 2))) (CFSG.KD.B4A.RW (Nat.div r 2))
        (Nat.beq (Nat.mod r 2) 1)) x < 31671, (recV r)⁻¹ ⟨x, hx⟩ = ⟨_, hy⟩ := by
      by_cases ho : r % 2 = 1
      · rw [recV, if_pos ho, inv_inv, beq_one_true ho]
        have e := ev1_spec tables hr hx
        change ∃ hy : ev1 CFSG.KD.B4A.LP (CFSG.KD.B4A.RW (r / 2)) x < 31671,
          (rho432F (wVal (yGen 4 3 2) (CFSG.KD.B4A.RW (r / 2)))) ⟨x, hx⟩ =
            ⟨ev1 CFSG.KD.B4A.LP (CFSG.KD.B4A.RW (r / 2)) x, hy⟩
        exact ⟨by rw [← e]; exact Fin.isLt _, Fin.ext e⟩
      · rw [recV, if_neg ho, beq_one_false ho]
        have e := ev1_spec tables (stL_wInH_rev hr) hx
        rw [wVal, stL_val_wRev (yGen_mul_self 4 3 2), map_inv] at e
        change ∃ hy : ev1 CFSG.KD.B4A.LP (wRev (CFSG.KD.B4A.RW (r / 2))) x < 31671,
          (rho432F (wVal (yGen 4 3 2) (CFSG.KD.B4A.RW (r / 2))))⁻¹ ⟨x, hx⟩ =
            ⟨ev1 CFSG.KD.B4A.LP (wRev (CFSG.KD.B4A.RW (r / 2))) x, hy⟩
        exact ⟨by rw [← e]; exact Fin.isLt _, Fin.ext e⟩
    obtain ⟨hy, e⟩ := key
    rw [e]
    exact evRecI_spec rs (fun r' h' => hw r' (by simp [h'])) _ hy

theorem nodupB_spec : ∀ (l : List ℕ) (used : ℕ), nodupB l used = true →
    l.Nodup ∧ ∀ p ∈ l, used.testBit p = false
  | [], _, _ => ⟨List.nodup_nil, fun _ h => absurd h List.not_mem_nil⟩
  | p :: l, used, h => by
    change andB (notB (Nat.beq (Nat.land (Nat.shiftRight used p) 1) 1))
      (nodupB l (Nat.lor used (Nat.shiftLeft 1 p))) = true at h
    rw [andB_iff] at h
    obtain ⟨h1, h2⟩ := h
    obtain ⟨hnd, hbits⟩ := nodupB_spec l _ h2
    have hp : used.testBit p = false := by
      have hb : Nat.beq (Nat.land (Nat.shiftRight used p) 1) 1 = false := by
        cases hb : Nat.beq (Nat.land (Nat.shiftRight used p) 1) 1
        · rfl
        · rw [hb] at h1
          exact absurd h1 (by decide)
      have hmod : (used >>> p) % 2 = 0 := by
        have e1 : Nat.land (Nat.shiftRight used p) 1 = (used >>> p) % 2 := by
          rw [CFSG.KC.Benes.nland, CFSG.KC.Benes.nshr, Nat.and_one_is_mod]
        rcases Nat.mod_two_eq_zero_or_one (used >>> p) with h0 | h0
        · exact h0
        · rw [e1, h0] at hb
          exact absurd hb (by decide)
      unfold Nat.testBit
      rw [Nat.and_comm, Nat.and_one_is_mod, hmod]
      rfl
    have hs : Nat.shiftLeft 1 p = 2 ^ p := (Nat.shiftLeft_eq 1 p).trans (Nat.one_mul _)
    refine ⟨List.nodup_cons.2 ⟨fun hm => ?_, hnd⟩, ?_⟩
    · have := hbits p hm
      rw [CFSG.KC.Benes.nlor, Nat.testBit_or, hs, Nat.testBit_two_pow_self, Bool.or_true] at this
      exact absurd this (by decide)
    · intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · have := hbits q hq
        rw [CFSG.KC.Benes.nlor, Nat.testBit_or, Bool.or_eq_false_iff] at this
        exact this.1

theorem orbListChk_spec {W : ℕ → List ℕ} (hW : ∀ t, ∀ c ∈ W t, c < 10) {gens : List (List ℕ)}
    {b : ℕ} {P Q I : List ℕ} (hb : b < 31671)
    (h : orbListChk (evT CFSG.KD.B4A.LP W) gens b P Q I = true) :
    P.length ≤ (MulAction.orbit (Subgroup.closure {σ | ∃ w ∈ gens, σ = tv W w})
      (⟨b, hb⟩ : Fin 31671)).ncard := by
  unfold orbListChk at h
  simp only [andB_iff] at h
  obtain ⟨h0, hpos, hnd, hall⟩ := h
  rw [belowAll_iff] at hall
  have hP0 : P.getD 0 0 = b := Nat.eq_of_beq_eq_true h0
  have hlen : 0 < P.length := Nat.blt_eq.mp hpos
  have hstep : ∀ i (hi : i < P.length), 0 < i → Q.getD i 0 < i ∧
      evT CFSG.KD.B4A.LP W (gens.getD (I.getD i 0) []) (P.getD (Q.getD i 0) 0) = P.getD i 0 := by
    intro i hi hi0
    have := hall i hi
    have hne : Nat.beq i 0 = false := by
      cases i with
      | zero => omega
      | succ n => rfl
    rw [hne] at this
    change andB _ _ = true at this
    rw [andB_iff] at this
    exact ⟨Nat.blt_eq.mp this.1, Nat.eq_of_beq_eq_true this.2⟩
  have hlt : ∀ i (hi : i < P.length), P[i] < 31671 := by
    intro i
    induction i using Nat.strong_induction_on with
    | _ i ih =>
      intro hi
      rcases Nat.eq_zero_or_pos i with rfl | hi0
      · rw [← List.getD_eq_getElem _ 0 hi, hP0]
        exact hb
      · obtain ⟨hq, hm⟩ := hstep i hi hi0
        have hq' : Q.getD i 0 < P.length := by omega
        have hx := ih _ hq hq'
        rw [← List.getD_eq_getElem _ 0 hq'] at hx
        rw [← List.getD_eq_getElem _ 0 hi, ← hm, ← evT_spec hW _ _ hx]
        exact Fin.isLt _
  have hltP : ∀ p ∈ P, p < 31671 := by
    intro p hp
    obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hp
    exact hlt i hi
  refine length_le_ncard_orbit _ b hb P hltP ?_ ?_ (nodupB_spec P 0 hnd).1
  · rw [List.head?_eq_getElem?, List.getElem?_eq_getElem hlen, ← List.getD_eq_getElem _ 0 hlen, hP0]
  · intro i hi hi0
    obtain ⟨hq, hm⟩ := hstep i hi hi0
    have hq' : Q.getD i 0 < P.length := by omega
    refine ⟨Q.getD i 0, hq, hq', tv W (gens.getD (I.getD i 0) []), ?_, ?_⟩
    · by_cases hI : I.getD i 0 < gens.length
      · exact Subgroup.subset_closure ⟨_, List.getD_eq_getElem _ _ hI ▸ List.getElem_mem hI, rfl⟩
      · rw [List.getD_eq_default _ _ (by omega)]
        exact Subgroup.one_mem _
    · have hx := hlt _ hq'
      have hx' : P.getD (Q.getD i 0) 0 < 31671 := by rw [List.getD_eq_getElem _ 0 hq']; exact hx
      have e := evT_spec hW (gens.getD (I.getD i 0) []) _ hx'
      rw [← List.getD_eq_getElem _ 0 hi, ← hm, ← e]
      congr 2
      exact Fin.ext (List.getD_eq_getElem _ 0 hq').symm

end CertificateChecks.KernelB433

end

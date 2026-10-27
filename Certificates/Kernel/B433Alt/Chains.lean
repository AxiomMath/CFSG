module

public import Certificates.Kernel.B433Alt.Base

set_option maxRecDepth 100000

public section

namespace CertificateChecks.KernelB433

open CFSG.KC.B4A CFSG.KC.B433Alt CFSG.YGroups CFSG.Certificates.CosetEnumeration CFSG.KD.B4AC

@[expose] def liveB (j : ℕ) : Bool := Nat.blt 0 (Nat.land 0xbe7fffe85f0efff (Nat.shiftLeft 1 j))

@[expose] noncomputable def lvlOK (j l : ℕ) : Bool :=
  (fun kk =>
    andB (Nat.blt (LB kk) 31671) (andB (Nat.ble (LN kk) 255)
    (andB ((List.range (LN kk)).all fun k =>
        Nat.blt 0 (genW CFSG.KD.B4A.RD CFSG.KD.B4A.RW EL EW j l (LG kk) (LN kk) k))
    (andB ((List.range (LK kk)).all fun i => Nat.beq (CL (LC kk + i)) kk)
    (andB (Nat.ble (LC kk + LK kk) 824)
    (andB (Bool.rec true (Nat.beq (CS (LC kk)) (orbInit (LB kk))) (Nat.blt 0 (LK kk)))
    (andB ((List.range (LK kk - 1)).all fun i => Nat.beq (CS (LC kk + i + 1)) (CT (LC kk + i)))
      (Nat.beq (orbCount (Bool.rec (CT (LC kk + LK kk - 1)) (orbInit (LB kk)) (Nat.beq (LK kk) 0)))
        (LO kk))))))))) (16 * j + l)

@[expose] noncomputable def nodeOK (j : ℕ) : Bool :=
  Bool.rec true
    (andB (Nat.blt (LF j) 16) (andB ((List.range (LF j)).all fun l => lvlOK j l)
      (Nat.beq (MJ j) ((List.range (LF j)).map fun l => LO (16 * j + l)).prod)))
    (liveB j)

theorem node_all : ∀ j < 64, nodeOK j = true := by decide +kernel

theorem prod_range_eq (f : ℕ → ℕ) : ∀ n,
    ((List.range n).map f).prod = ∏ i ∈ Finset.range n, f i
  | 0 => rfl
  | n + 1 => by
    rw [List.range_succ, List.map_append, List.prod_append, prod_range_eq f n,
      Finset.prod_range_succ]
    simp

theorem sN_eq' (v : ℕ) (k : ℕ → ℕ) : sN v k = k v := by cases v <;> rfl

theorem genW_spec {RD RW EL EW : ℕ → ℕ} {j l G nG k : ℕ} (h : 0 < genW RD RW EL EW j l G nG k) :
    (l = 0 → isStab (dKind (RD (fld G (20 * k) (ones 20)))) = true ∧
      dN2 (RD (fld G (20 * k) (ones 20))) = j ∧
      genWord RD RW EL EW j l G nG k = RW (fld G (20 * k) (ones 20))) ∧
    (l ≠ 0 → elJ (EL (fld G (20 * k) (ones 20))) = j ∧ elL (EL (fld G (20 * k) (ones 20))) = l ∧
      genWord RD RW EL EW j l G nG k = EW (fld G (20 * k) (ones 20))) := by
  unfold genWord
  unfold genW at h ⊢
  simp only [sN_eq'] at h ⊢
  cases h1 : Nat.blt k nG
  · simp only [h1] at h
    exact absurd h (lt_irrefl 0)
  · simp only [h1] at h
    by_cases hl : l = 0
    · subst hl
      have h2 : Nat.beq 0 0 = true := rfl
      rw [h2] at h ⊢
      cases h3 : andB (isStab (dKind (RD (fld G (Nat.mul 20 k) (ones 20)))))
          (Nat.beq (dN2 (RD (fld G (Nat.mul 20 k) (ones 20)))) j)
      · rw [h3] at h
        exact absurd h (lt_irrefl 0)
      · rw [andB_iff] at h3
        refine ⟨fun _ => ⟨h3.1, Nat.eq_of_beq_eq_true h3.2, ?_⟩, fun h => absurd rfl h⟩
        simp only [h1]
        rfl
    · have h2 : Nat.beq l 0 = false := by
        cases e : Nat.beq l 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hl
      rw [h2] at h ⊢
      cases h3 : andB (Nat.beq (elJ (EL (fld G (Nat.mul 20 k) (ones 20)))) j)
          (Nat.beq (elL (EL (fld G (Nat.mul 20 k) (ones 20)))) l)
      · rw [h3] at h
        exact absurd h (lt_irrefl 0)
      · rw [andB_iff] at h3
        refine ⟨fun h => absurd h hl, fun _ =>
          ⟨Nat.eq_of_beq_eq_true h3.1, Nat.eq_of_beq_eq_true h3.2, ?_⟩⟩
        simp only [h1]
        rfl

@[expose] noncomputable def nodeSub (j : ℕ) : Subgroup (YGroup 4 3 2) :=
  Subgroup.closure ((fun g => wVal (yGen 4 3 2) (CFSG.KD.B4A.RW g)) ''
    {g | isStab (dKind (CFSG.KD.B4A.RD g)) = true ∧ dN2 (CFSG.KD.B4A.RD g) = j})

@[expose] noncomputable def βn (j m : ℕ) : Fin 31671 :=
  if h : LB (16 * j + m) < 31671 then ⟨_, h⟩ else 0

theorem list_all_iff {f : ℕ → Bool} {n : ℕ} : (List.range n).all f = true ↔ ∀ i < n, f i = true := by
  simp [List.all_eq_true]

theorem shr4 (j l : ℕ) (hl : l < 16) : Nat.shiftRight (16 * j + l) 4 = j := by
  change (16 * j + l) >>> 4 = j
  rw [Nat.shiftRight_eq_div_pow]
  omega

theorem land15 (j l : ℕ) (hl : l < 16) : Nat.land (16 * j + l) 15 = l := by
  change (16 * j + l) &&& 15 = l
  have e : (15 : ℕ) = 2 ^ 4 - 1 := by norm_num
  rw [e, Nat.and_two_pow_sub_one_eq_mod]
  omega

theorem lvlOK_spec {j l : ℕ} (h : lvlOK j l = true) :
    LB (16 * j + l) < 31671 ∧
    (∀ k < LN (16 * j + l), 0 < genW CFSG.KD.B4A.RD CFSG.KD.B4A.RW EL EW j l (LG (16 * j + l))
      (LN (16 * j + l)) k) ∧
    (∀ i < LK (16 * j + l), CL (LC (16 * j + l) + i) = 16 * j + l) ∧
    LC (16 * j + l) + LK (16 * j + l) ≤ 824 ∧
    ChunkRun CS CT (LC (16 * j + l)) (LK (16 * j + l)) (orbInit (LB (16 * j + l))) ∧
    orbCount (if LK (16 * j + l) = 0 then orbInit (LB (16 * j + l))
      else CT (LC (16 * j + l) + LK (16 * j + l) - 1)) = LO (16 * j + l) := by
  unfold lvlOK at h
  simp only [andB_iff, list_all_iff] at h
  obtain ⟨h1, -, h3, h4, h5, h6, h7, h8⟩ := h
  refine ⟨Nat.blt_eq.mp h1, fun k hk => Nat.blt_eq.mp (h3 k hk),
    fun i hi => Nat.eq_of_beq_eq_true (h4 i hi), Nat.ble_eq.mp h5, ⟨fun hn => ?_,
      fun i hi => Nat.eq_of_beq_eq_true (h7 i hi)⟩, ?_⟩
  · have : Nat.blt 0 (LK (16 * j + l)) = true := Nat.blt_eq.mpr hn
    rw [this] at h6
    exact Nat.eq_of_beq_eq_true h6
  · by_cases hz : LK (16 * j + l) = 0
    · have : Nat.beq (LK (16 * j + l)) 0 = true := by rw [hz]; rfl
      rw [this] at h8
      rw [if_pos hz]
      exact Nat.eq_of_beq_eq_true h8
    · have : Nat.beq (LK (16 * j + l)) 0 = false := by
        cases e : Nat.beq (LK (16 * j + l)) 0
        · rfl
        · exact absurd (Nat.eq_of_beq_eq_true e) hz
      rw [this] at h8
      rw [if_neg hz]
      exact Nat.eq_of_beq_eq_true h8

section

theorem lvl {j l : ℕ} (hl : l < 16) (h : lvlOK j l = true)
    (hbs : ∀ m < l, LB (16 * j + m) < 31671) :
    (∀ k < LN (16 * j + l), wInH (genWord CFSG.KD.B4A.RD CFSG.KD.B4A.RW EL EW j l (LG (16 * j + l))
      (LN (16 * j + l)) k) = true ∧
      ∀ m (hm : m < l), (rho432F (wVal (yGen 4 3 2) (genWord CFSG.KD.B4A.RD CFSG.KD.B4A.RW EL EW j l
        (LG (16 * j + l)) (LN (16 * j + l)) k)) ⟨LB (16 * j + m), hbs m hm⟩ : ℕ) = LB (16 * j + m)) ∧
    LO (16 * j + l) ≤ (MulAction.orbit (Subgroup.closure ((fun k => rho432F (wVal (yGen 4 3 2)
      (genWord CFSG.KD.B4A.RD CFSG.KD.B4A.RW EL EW j l (LG (16 * j + l)) (LN (16 * j + l)) k))) ''
      {k | k < LN (16 * j + l)})) (⟨LB (16 * j + l), (lvlOK_spec h).1⟩ : Fin 31671)).ncard := by
  obtain ⟨hb, hgen, hcl, hle, hrun, hcnt⟩ := lvlOK_spec h
  exact level_sound (ρ := rho432F) (j := j) (l := l) (G := LG (16 * j + l)) (nG := LN (16 * j + l))
    (bs := fun m => LB (16 * j + m)) (CN := CN) (CR := CR) (CS := CS) (CT := CT)
    (k₀ := LC (16 * j + l)) (n := LK (16 * j + l)) (o := LO (16 * j + l)) tables hb rw_stab
    (fun e hj hl' hl0 => by
      have he : EL e ≠ 0 := fun h0 => by
        rw [h0] at hl'
        exact hl0 hl'.symm
      have := el_ok e he
      rw [hj, hl'] at this
      exact this)
    hgen (fun i hi => by
      have hk : LC (16 * j + l) + i < 824 := by omega
      have h := orb_all (LC (16 * j + l) + i) hk
      unfold orbChk at h
      rw [sB_eq, hcl i hi, shr4 j l hl, land15 j l hl] at h
      exact Nat.eq_of_beq_eq_true h) hrun hcnt hbs

theorem node_card {j : ℕ} (hj : j < 64) (hlive : liveB j = true) :
    MJ j ≤ Nat.card ((nodeSub j).map rho432F) := by
  have hn := node_all j hj
  unfold nodeOK at hn
  rw [hlive] at hn
  simp only [andB_iff] at hn
  obtain ⟨hLF, hlv, hmj⟩ := hn
  rw [list_all_iff] at hlv
  rw [Nat.eq_of_beq_eq_true hmj, prod_range_eq]
  have hmem := member_sound_bdd (ρ := rho432F) (LP := CFSG.KD.B4A.LP) (RD := CFSG.KD.B4A.RD)
    (RW := CFSG.KD.B4A.RW) (EL := EL) (EW := EW) (bs := fun j l => LB (16 * j + l)) rw_stab
    (fun g _ => rw_len g) (fun e _ => ew_len e) (fun w hw h => isOne_rho hw h)
    (fun e he => el_ok e he)
  have hLF' : LF j < 16 := Nat.blt_eq.mp hLF
  have hbs : ∀ m < LF j, LB (16 * j + m) < 31671 := fun m hm => (lvlOK_spec (hlv m hm)).1
  have hβ : ∀ m (hm : m < LF j), βn j m = ⟨LB (16 * j + m), hbs m hm⟩ := fun m hm => by
    rw [βn, dif_pos (hbs m hm)]
  refine CFSG.YGroups.card_ge_of_chain _ (LF j) (βn j)
    (fun l => (fun k => rho432F (wVal (yGen 4 3 2)
      (genWord CFSG.KD.B4A.RD CFSG.KD.B4A.RW EL EW j l (LG (16 * j + l)) (LN (16 * j + l)) k))) ''
        {k | k < LN (16 * j + l)}) ?_ ?_ (fun l => LO (16 * j + l)) ?_
  · rintro l hl _ ⟨k, hk, rfl⟩
    have hg := (lvlOK_spec (hlv l hl)).2.1 k hk
    obtain ⟨h0, h1⟩ := genW_spec hg
    dsimp only
    by_cases hl0 : l = 0
    · obtain ⟨hs, hn, he⟩ := h0 hl0
      rw [he]
      exact Subgroup.mem_map_of_mem _ (Subgroup.subset_closure ⟨_, ⟨hs, hn⟩, rfl⟩)
    · obtain ⟨hj', hl', he⟩ := h1 hl0
      rw [he]
      have hne : EL (fld (LG (16 * j + l)) (20 * k) (ones 20)) ≠ 0 := fun h0 => by
        rw [h0] at hl'
        exact hl0 hl'.symm
      have := hmem _ hne
      rw [hj'] at this
      exact this
  · rintro l hl _ ⟨k, hk, rfl⟩ m hm
    rw [hβ m (by omega)]
    exact Fin.ext ((lvl (by omega) (hlv l hl) (fun m' hm' => hbs m' (by omega))).1 k hk |>.2 m hm)
  · intro l hl
    rw [hβ l hl]
    exact (lvl (by omega) (hlv l hl) (fun m' hm' => hbs m' (by omega))).2

end

end CertificateChecks.KernelB433

end

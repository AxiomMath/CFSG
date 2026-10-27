module

public import CFSG.Sporadic.Schreier.LySylowCertificate
public import Certificates.Certificate3085
public import CFSG.Sporadic.Schreier.LyCover

public noncomputable section

namespace CFSG.Sporadic.LySchreier

open CFSG.Sporadic.Ly CFSG.Sporadic.Ly.Native CFSG.Sporadic.LySchreier.Native
open CFSG.Sporadic.He.Native Matrix
open CFSG.Sporadic.Th (allIn_eq_true)

@[expose] def CanonM (X : Mat) : Prop :=
  X.size = 111 ∧ ∀ r < 111, (X[r]!).size = 111 ∧ ∀ c < 111, (X[r]!)[c]! < 5

theorem canonM_mulM (X Y : Mat) : CanonM (mulM 5 111 X Y) := by
  have hsz : (mulM 5 111 X Y).size = 111 := by simp [mulM]
  refine ⟨hsz, fun r hr => ⟨?_, fun c hc => ?_⟩⟩
  · rw [mulM, getElem!_ofFn _ hr]
    simp
  · rw [mulM, getElem!_ofFn _ hr, getElem!_ofFn _ hc]
    exact Nat.mod_lt _ (by norm_num)

theorem canonM_idM : CanonM (idM 111) := by
  have hsz : (idM 111).size = 111 := by simp [idM]
  refine ⟨hsz, fun r hr => ⟨?_, fun c hc => ?_⟩⟩
  · rw [idM, getElem!_ofFn _ hr]
    simp
  · rw [idM, getElem!_ofFn _ hr, getElem!_ofFn _ hc]
    split_ifs <;> norm_num

theorem eq_of_toMat_eq {X Y : Mat} (hX : CanonM X) (hY : CanonM Y)
    (h : toMat 5 111 X = toMat 5 111 Y) : X = Y := by
  apply Array.ext (by rw [hX.1, hY.1])
  intro r h1 h2
  have hr : r < 111 := by rw [← hX.1]; exact h1
  apply Array.ext (by rw [← getElem!_pos X r h1, ← getElem!_pos Y r h2, (hX.2 r hr).1,
    (hY.2 r hr).1])
  intro c h3 h4
  have hc : c < 111 := by
    have := (hX.2 r hr).1
    rw [getElem!_pos X r h1] at this
    rw [← this]; exact h3
  have e := congrFun (congrFun h ⟨r, hr⟩) ⟨c, hc⟩
  rw [toMat_apply, toMat_apply] at e
  have := (ZMod.natCast_eq_natCast_iff' _ _ 5).1 e
  rw [Nat.mod_eq_of_lt ((hX.2 r hr).2 c hc), Nat.mod_eq_of_lt ((hY.2 r hr).2 c hc)] at this
  rw [getElem!_pos X r h1, getElem!_pos Y r h2] at this
  rw [getElem!_pos _ c h3, getElem!_pos _ c h4] at this
  exact this

@[expose] def syGenArr : Array Mat := sylowGens csArr

@[expose] def sBFS : Array Mat × Array ℕ × Array ℕ × Array (Array ℕ) := sylowBFS syGenArr 256

abbrev sPts : Array Mat := sBFS.1
abbrev sPar : Array ℕ := sBFS.2.1
abbrev sLab : Array ℕ := sBFS.2.2.1
abbrev sLam : Array (Array ℕ) := sBFS.2.2.2

@[expose] def sTab : Array (Array ℕ) := mulTabOf 256 sPar sLab sLam

@[expose] def sDT : Array ℕ × Array ℕ × Array ℕ × Array ℕ := derivedTree sTab 256

@[expose] def sEA (k : ℕ) : List (List ℕ) := (nextEA sTab 256)^[k] [[0]]

theorem sylow_parts :
    sylowEnumOK syGenArr 256 sBFS = true ∧ sPts[6]! = matA ∧
    mulTabOK sTab 256 sPar sLab sLam = true ∧
    tableOK sTab 256 sDT.1 sDT.2.1 sDT.2.2.1 sDT.2.2.2 (sEA 1) (sEA 2) (sEA 3) (sEA 4) 38 =
      true ∧
    localOK (powM 5 111 matB 4) csArr syGenArr sTab sPts = true := by
  have h := ly_sylow_certificate
  unfold sylowCertificate at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  rw [← csArr_def] at h
  obtain ⟨⟨⟨⟨⟨⟨_, _⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h3, h4, h5, h6, h7⟩

theorem enum_parts :
    sPts.size = 256 ∧ sPar.size = 256 ∧ sLab.size = 256 ∧ sLam.size = 6 ∧
    (∀ k < 6, (sLam[k]!).size = 256 ∧ ∀ i < 256, (sLam[k]!)[i]! < 256) ∧ sPts[0]! = idM 111 ∧
    (∀ i < 256, ∀ j < 256, sPts[i]! = sPts[j]! → i = j) ∧
    (∀ i < 256, ∀ k < 6, mulM 5 111 syGenArr[k]! sPts[i]! = sPts[(sLam[k]!)[i]!]!) ∧
    (∀ j, 1 ≤ j → j < 256 → sPar[j]! < j ∧ sLab[j]! < 6 ∧ (sLam[sLab[j]!]!)[sPar[j]!]! = j) ∧
    (∀ j, 1 ≤ j → j + 1 < 256 → sylowPos sPar sLab j < sylowPos sPar sLab (j + 1)) ∧
    (∀ i < 256, ∀ k < 6, (sLam[k]!)[i]! = 0 ∨ sylowPos sPar sLab (sLam[k]!)[i]! ≤ 6 * i + k) := by
  have h := sylow_parts.1
  unfold sylowEnumOK at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨_, h1⟩, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩, h11⟩ := h
  refine ⟨h1, h2, h3, h4, fun k hk => ?_, h6, fun i hi j hj hij => ?_, fun i hi k hk => ?_,
    fun j hj1 hj2 => ?_, fun j hj1 hj2 => ?_, fun i hi k hk => ?_⟩
  · rw [Array.all_eq_true] at h5
    have := h5 k (by rw [h4]; exact hk)
    simp only [Bool.and_eq_true, beq_iff_eq, Array.all_eq_true, decide_eq_true_eq] at this
    refine ⟨by rw [getElem!_pos sLam k (by rw [h4]; exact hk)]; exact this.1, fun i hi => ?_⟩
    have h' := this.2 i (by rw [this.1]; exact hi)
    rwa [getElem!_pos sLam k (by rw [h4]; exact hk), getElem!_pos _ i (by rw [this.1]; exact hi)]
  · have e1 := (allIn_eq_true.1 h7) i (Nat.zero_le _) hi
    have e2 := (allIn_eq_true.1 h7) j (Nat.zero_le _) hj
    simp only [beq_iff_eq] at e1 e2
    rw [← e1, ← e2, hij]
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 h8) i (Nat.zero_le _) hi)) k (Nat.zero_le _) hk
    simpa using this
  · have := (allIn_eq_true.1 h9) j hj1 hj2
    simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at this
    exact ⟨this.1.1, this.1.2, this.2⟩
  · have := (allIn_eq_true.1 h10) j hj1 (by omega)
    simpa using this
  · have := (allIn_eq_true.1 ((allIn_eq_true.1 h11) i (Nat.zero_le _) hi)) k (Nat.zero_le _) hk
    simpa [Bool.or_eq_true, beq_iff_eq, decide_eq_true_eq] using this

theorem syGenArr_size : syGenArr.size = 6 := by simp [syGenArr, sylowGens]

theorem repM_syGen
    (k : Fin 6) : RepM syGenArr[k.val]! (sylowGen k) := by
  rw [getElem!_pos syGenArr k.val (by rw [syGenArr_size]; exact k.isLt)]
  simp only [syGenArr, sylowGens, Array.getElem_push, Array.size_ofFn, Array.getElem_ofFn]
  unfold sylowGen
  by_cases hk : k.val < 5
  · rw [dite_eq_left hk, ite_eq_left hk]
    exact repM_evalWordM (fun i => (repM_csArr i).1) (fun i => (repM_csArr i).2) _
  · rw [dite_eq_right hk, ite_eq_right hk]
    exact repM_matA

@[expose] def sTree (i : ℕ) : J :=
  if h : 0 < i ∧ sPar[i]! < i then
    sylowGen ⟨sLab[i]! % 6, Nat.mod_lt _ (by norm_num)⟩ * sTree sPar[i]!
  else 1
termination_by i
decreasing_by exact h.2

theorem sTree_zero : sTree 0 = 1 := by
  rw [sTree]; simp

theorem sTree_succ
    {i : ℕ} (hi1 : 1 ≤ i) (hi : i < 256) :
    sTree i =
      sylowGen ⟨sLab[i]!, (enum_parts.2.2.2.2.2.2.2.2.1 i hi1 hi).2.1⟩ * sTree sPar[i]! := by
  have h := enum_parts.2.2.2.2.2.2.2.2.1 i hi1 hi
  have e : (⟨sLab[i]! % 6, Nat.mod_lt _ (by norm_num)⟩ : Fin 6) = ⟨sLab[i]!, h.2.1⟩ :=
    Fin.ext (Nat.mod_eq_of_lt h.2.1)
  rw [sTree, dite_eq_left ⟨by omega, h.1⟩, e]

theorem repM_sTree :
    ∀ i < 256, RepM sPts[i]! (sTree i) ∧ CanonM sPts[i]! := by
  intro i
  induction i using Nat.strong_induction_on with
  | _ i ih =>
    intro hi
    rcases Nat.eq_zero_or_pos i with rfl | hpos
    · rw [enum_parts.2.2.2.2.2.1, sTree_zero]
      exact ⟨repM_id, canonM_idM⟩
    · obtain ⟨hp, hl, hlam⟩ := enum_parts.2.2.2.2.2.2.2.2.1 i hpos hi
      have e := enum_parts.2.2.2.2.2.2.2.1 sPar[i]! (by omega) sLab[i]! hl
      rw [hlam] at e
      rw [← e, sTree_succ hpos hi]
      exact ⟨(repM_syGen ⟨sLab[i]!, hl⟩).mul (ih _ hp (by omega)).1, canonM_mulM _ _⟩

theorem sTree_inj
    {i j : ℕ} (hi : i < 256) (hj : j < 256) (h : sTree i = sTree j) : i = j := by
  obtain ⟨hri, hci⟩ := repM_sTree i hi
  obtain ⟨hrj, hcj⟩ := repM_sTree j hj
  apply enum_parts.2.2.2.2.2.2.1 i hi j hj
  apply eq_of_toMat_eq hci hcj
  rw [show toMat 5 111 sPts[i]! = mat (sTree i) from hri,
    show toMat 5 111 sPts[j]! = mat (sTree j) from hrj, h]

theorem sylowGen_mul_sTree
    (k : Fin 6) {i : ℕ} (hi : i < 256) :
    sylowGen k * sTree i = sTree ((sLam[k.val]!)[i]!) := by
  have hlt := (enum_parts.2.2.2.2.1 k.val k.isLt).2 i hi
  have e := enum_parts.2.2.2.2.2.2.2.1 i hi k.val k.isLt
  have h1 := (repM_syGen k).mul (repM_sTree i hi).1
  rw [e] at h1
  exact h1.unique (repM_sTree _ hlt).1

end CFSG.Sporadic.LySchreier

module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusLabel
public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCensusLin
import CFSG.LocalAnalysis.StandardType.GGCartanALinear

public section

namespace CFSG.StandardType.GGQ2Frame.ExcRaw

open Module

noncomputable section

variable {m : Fin 6} {T : Chk.Tabs} {w : Chk.LinW}

private theorem ambOK_components {cv cz ℓ k : ℕ} {W : Chk.AmbW}
    (h : Chk.ambOK T m cv cz ℓ k W = true) :
    Chk.linOK T (nroots m) W.w = true ∧
      Chk.genOK T (nroots m) (Chk.nodeMask W.w fun i => i != W.w.a) k W.Lk = true ∧
      Chk.lineOK T (dim m) (nroots m) (Chk.nodeList W.w fun i => i != W.w.a) cz W.Bk = true ∧
      Chk.joinOK T (nroots m) ℓ k (Chk.nodeN W.w W.w.a) W.La = true ∧
      cv < 3 ^ dim m ∧
      (∀ t ∈ Chk.nodeList W.w (fun i => (i != W.w.a) && (i != W.w.b)),
        (T.zm[cv]!).testBit t = true) ∧
      Chk.basisOK T (dim m) W.w W.Bb = true ∧
      Chk.notB2 m ℓ = true ∧ Chk.notB2 m k = true := by
  simp only [Chk.ambOK, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, and_assoc] at h
  exact h

private theorem bne_iff_ne_node_a (_hT : Chk.tabsOK m T = true) {W : Chk.AmbW}
    {hw : Chk.linOK T (nroots m) W.w = true} (i : Fin (Chk.rkN W.w.tc W.w.n)) :
    ((i.val != W.w.a) = true) ↔ i ≠ (⟨W.w.a, linOK_a_lt hw⟩ : Fin (Chk.rkN W.w.tc W.w.n)) := by
  simp only [bne_iff_ne, ne_eq, Fin.ext_iff]

private theorem bne_iff_ne_node_b (_hT : Chk.tabsOK m T = true) {W : Chk.AmbW}
    {hw : Chk.linOK T (nroots m) W.w = true} (i : Fin (Chk.rkN W.w.tc W.w.n)) :
    ((i.val != W.w.b) = true) ↔ i ≠ (⟨W.w.b, linOK_b_lt hw⟩ : Fin (Chk.rkN W.w.tc W.w.n)) := by
  simp only [bne_iff_ne, ne_eq, Fin.ext_iff]

private theorem set_ne_node_a (hT : Chk.tabsOK m T = true) {W : Chk.AmbW}
    {hw : Chk.linOK T (nroots m) W.w = true} :
    ({i : Fin (Chk.rkN W.w.tc W.w.n) | i ≠
        (⟨W.w.a, linOK_a_lt hw⟩ : Fin (Chk.rkN W.w.tc W.w.n))} : Set _)
      = {i : Fin (Chk.rkN W.w.tc W.w.n) | (fun j : ℕ => j != W.w.a) ↑i = true} := by
  ext i
  simp only [Set.mem_setOf_eq]
  exact (bne_iff_ne_node_a (hw := hw) hT i).symm

private theorem val_succAbove_offN {n : ℕ} (a : ℕ) (ha : a < n + 1) (i : Fin n) :
    ((finSuccAboveEquiv (⟨a, ha⟩ : Fin (n + 1))) i).val = Chk.offN a i.val := by
  rw [finSuccAboveEquiv_apply]
  simp only [Fin.succAbove]
  split_ifs with h
  · have h' : i.val < a := by simp only [Fin.lt_def, Fin.val_castSucc] at h; exact h
    simp [Chk.offN, h']
  · have h' : ¬ i.val < a := by simp only [Fin.lt_def, Fin.val_castSucc] at h; exact h
    simp [Chk.offN, h']

private theorem nat_all_true {n : ℕ} {f : (i : ℕ) → i < n → Bool} :
    Nat.all n f = true ↔ ∀ i (h : i < n), f i h = true := by
  rw [Nat.all_eq_finRange_all, List.all_eq_true]
  constructor
  · intro h i hi
    exact h ⟨i, hi⟩ (List.mem_finRange _)
  · intro h x _
    exact h x.1 x.2

private theorem typeOK_pairing {r : ℕ} {w : Chk.LinW} (h : Chk.typeOK T r w = true)
    (i j : Fin (Chk.rkN w.tc w.n)) :
    Chk.sgnN w i * Chk.sgnN w j * (T.pair[Chk.nodeN w i]!)[Chk.nodeN w j]! =
      Chk.cartanN w.tc w.n i j := by
  have hh := h
  simp only [Chk.typeOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at hh
  have h1 := (nat_all_true.mp hh.2 i i.isLt)
  have h2 := (nat_all_true.mp h1 j j.isLt)
  simpa only [beq_iff_eq] using h2

private theorem sgnN_eq_one_of_unsignedN {w : Chk.LinW} (h : Chk.unsignedN w = true) (i : ℕ) :
    Chk.sgnN w i = 1 := by
  have hget : w.neg.getD i false = false := by
    by_cases hi : i < w.neg.length
    · have hmem : w.neg[i] ∈ w.neg := List.getElem_mem hi
      have h1 : (!(w.neg[i])) = true := List.all_eq_true.mp h _ hmem
      have h2 : w.neg[i] = false := by simpa using h1
      have h3 : w.neg.getD i false = w.neg[i] := List.getD_eq_getElem w.neg false hi
      rw [h3]
      exact h2
    · rw [List.getD_eq_default _ _ (by omega)]
  simp only [Chk.sgnN, hget]
  decide

private theorem ambDOK_components {cv cz ℓ k : ℕ} {W : Chk.AmbW} {perm : List ℕ} {half : ℕ}
    (h : Chk.ambDOK T m cv cz ℓ k W perm half = true) :
    Chk.ambOK T m cv cz ℓ k W = true ∧ 3 ≤ half ∧
      Chk.rkN W.w.tc W.w.n = 2 * half + 1 ∧ perm.length = 2 * half ∧ perm.Nodup ∧
      (∀ x ∈ perm, x < Chk.rkN W.w.tc W.w.n ∧ x ≠ W.w.a) ∧
      (Nat.all (2 * half) fun i _ => Nat.all (2 * half) fun j _ =>
        Chk.cartanN W.w.tc W.w.n (perm.getD i 0) (perm.getD j 0) ==
          Chk.cartanN 3 (2 * half) i j) = true := by
  simp only [Chk.ambDOK, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq, bne_iff_ne,
    List.all_eq_true, and_assoc] at h
  exact h

private theorem d5OK_components {cv cz ℓ j k : ℕ} {W : Chk.AmbW} {Lj : List (ℕ × ℕ)}
    (h : Chk.d5OK T m cv cz ℓ j k W Lj = true) :
    Chk.ambOK T m cv cz ℓ k W = true ∧ W.w.tc = 3 ∧ W.w.n = 5 ∧ W.w.a = 0 ∧
      (W.w.b = 1 ∨ W.w.b = 3 ∨ W.w.b = 4) ∧
      Chk.genOK T (nroots m) (Chk.nodeMask W.w fun i => i != W.w.a && i != W.w.b) j Lj = true ∧
      Chk.notB2 m j = true ∧
      (Chk.labelOf T m j = (1, 3, 1) ∨ Chk.labelOf T m j = (5, 3, 1)) := by
  simp only [Chk.d5OK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, and_assoc, or_assoc] at h
  exact h

private theorem selE6OK_components {k : ℕ} {L : List (ℕ × ℕ)}
    (h : Chk.selE6OK T m k w L = true) :
    w.tc = 4 ∧ Chk.unsignedN w = true ∧ Chk.typeOK T (nroots m) w = true ∧
      Chk.genOK T (nroots m) (Chk.nodeMask w fun _ => true) k L = true ∧
      Chk.notB2 m k = true := by
  simp only [Chk.selE6OK, Bool.and_eq_true, beq_iff_eq, and_assoc] at h
  exact h

private theorem selD6OK_components {j k : ℕ} {L L' : List (ℕ × ℕ)}
    (h : Chk.selD6OK T m j k w L L' = true) :
    w.tc = 3 ∧ w.n = 6 ∧ (w.b = 4 ∨ w.b = 5) ∧
      Chk.typeOK T (nroots m) w = true ∧
      Chk.genOK T (nroots m) (Chk.nodeMask w fun _ => true) k L = true ∧
      Chk.genOK T (nroots m) (Chk.nodeMask w fun i => i != w.b) j L' = true ∧
      Chk.notB2 m j = true ∧ Chk.notB2 m k = true := by
  simp only [Chk.selD6OK, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, and_assoc] at h
  exact h

private theorem det_submatrix_offN_eq {rk : ℕ} {M : ℕ → ℕ → ℤ} {a : ℕ} (ha : a < rk) :
    (((Matrix.of fun i j : Fin rk => M i j).submatrix
        (fun i : {i : Fin rk // i ≠ (⟨a, ha⟩ : Fin rk)} => (i : Fin rk))
        (fun i : {i : Fin rk // i ≠ (⟨a, ha⟩ : Fin rk)} => (i : Fin rk))).det : ZMod 3)
      = ((Matrix.of fun p q : Fin (rk - 1) => M (Chk.offN a p) (Chk.offN a q)).det : ZMod 3) := by
  obtain ⟨n, rfl⟩ := Nat.exists_eq_succ_of_ne_zero (by omega : rk ≠ 0)
  let e := finSuccAboveEquiv (⟨a, ha⟩ : Fin (n + 1))
  let B : Matrix {i : Fin (n + 1) // i ≠ (⟨a, ha⟩ : Fin (n + 1))}
      {i : Fin (n + 1) // i ≠ (⟨a, ha⟩ : Fin (n + 1))} ℤ := Matrix.of fun i j => M i j
  have hCB : B.submatrix e e = Matrix.of fun p q : Fin n => M (Chk.offN a p) (Chk.offN a q) := by
    ext p q
    simp only [Matrix.submatrix_apply, Matrix.of_apply, B, e, val_succAbove_offN a ha p,
      val_succAbove_offN a ha q]
  show ((B.det : ℤ) : ZMod 3) = ((Matrix.of fun p q : Fin n => M (Chk.offN a p)
    (Chk.offN a q)).det : ZMod 3)
  rw [← hCB, Matrix.det_submatrix_equiv_self]

theorem ambAt_linOf (hT : Chk.tabsOK m T = true) {cv cz ℓ k : ℕ} {W : Chk.AmbW}
    (h : Chk.ambOK T m cv cz ℓ k W = true) :
    (linOf m T hT W.w (ambOK_linOK h)).toLin.parab {i | i ≠ (linOf m T hT W.w (ambOK_linOK h)).a} = normalizerGroup m (ofMask m k) ∧
      (linOf m T hT W.w (ambOK_linOK h)).toLin.simpleRefl (linOf m T hT W.w (ambOK_linOK h)).a ∈ normalizerGroup m (ofMask m ℓ) ⊔ normalizerGroup m (ofMask m k) ∧
      (∀ v, (∀ i ∈ {i | i ≠ (linOf m T hT W.w (ambOK_linOK h)).a}, (linOf m T hT W.w (ambOK_linOK h)).root i v = 0) ↔ v ∈ Submodule.span (ZMod 3) {(vec m cz)}) ∧
      (∀ i, i ≠ (linOf m T hT W.w (ambOK_linOK h)).a → i ≠ (linOf m T hT W.w (ambOK_linOK h)).b → (linOf m T hT W.w (ambOK_linOK h)).root i (vec m cv) = 0) ∧ (linOf m T hT W.w (ambOK_linOK h)).toLin.Basis := by
  obtain ⟨-, hgen, hline, hjoin, hcv, hall, hbasis, hnotℓ, hnotk⟩ := ambOK_components h
  have hseta := set_ne_node_a (m := m) (T := T) (W := W) hT (hw := ambOK_linOK h)
  have h1 := linOf_parab_eq hT (ambOK_linOK h) hgen hnotk
  have h1' : (linOf m T hT W.w (ambOK_linOK h)).toLin.parab
      {i : Fin (Chk.rkN W.w.tc W.w.n) | i ≠
        (⟨W.w.a, linOK_a_lt (ambOK_linOK h)⟩ : Fin (Chk.rkN W.w.tc W.w.n))}
      = normalizerGroup m (ofMask m k) := by
    rwa [← hseta] at h1
  have h2 : (linOf m T hT W.w (ambOK_linOK h)).toLin.simpleRefl
      (linOf m T hT W.w (ambOK_linOK h)).a
      ∈ normalizerGroup m (ofMask m ℓ) ⊔ normalizerGroup m (ofMask m k) := by
    have h1s : (linOf m T hT W.w (ambOK_linOK h)).toLin.simpleRefl
        (linOf m T hT W.w (ambOK_linOK h)).a
        = reflection m (nodeRoot m W.w (typeOK_node_lt (linOK_typeOK (ambOK_linOK h)))
            ⟨W.w.a, linOK_a_lt (ambOK_linOK h)⟩) := by
      rw [show (linOf m T hT W.w (ambOK_linOK h)).a = (⟨W.w.a,
        linOK_a_lt (ambOK_linOK h)⟩ : Fin (Chk.rkN W.w.tc W.w.n)) from rfl]
      exact linOf_simpleRefl hT (ambOK_linOK h) _
    have h2s : reflection m (nodeRoot m W.w (typeOK_node_lt (linOK_typeOK (ambOK_linOK h)))
          ⟨W.w.a, linOK_a_lt (ambOK_linOK h)⟩)
        ∈ weyl m (ofMask m ℓ) ⊔ weyl m (ofMask m k) := by
      simpa [nodeRoot] using joinOK_sound hT hjoin
    rw [h1s, normalizerGroup_ofMask hnotℓ, normalizerGroup_ofMask hnotk]
    exact h2s
  have h3 : ∀ v : V m, (∀ i ∈ ({i : Fin (Chk.rkN W.w.tc W.w.n) | i ≠
      (⟨W.w.a, linOK_a_lt (ambOK_linOK h)⟩ : Fin (Chk.rkN W.w.tc W.w.n))} : Set _),
      (linOf m T hT W.w (ambOK_linOK h)).root i v = 0) ↔
      v ∈ Submodule.span (ZMod 3) {vec m cz} := by
    intro v
    have hk := linOf_kernel hT (ambOK_linOK h) (p := fun i : ℕ => i != W.w.a) hline v
    rwa [← hseta] at hk
  have h4 : ∀ i : Fin (Chk.rkN W.w.tc W.w.n), i ≠
      (⟨W.w.a, linOK_a_lt (ambOK_linOK h)⟩ : Fin (Chk.rkN W.w.tc W.w.n)) →
      i ≠ (⟨W.w.b, linOK_b_lt (ambOK_linOK h)⟩ : Fin (Chk.rkN W.w.tc W.w.n)) →
      (linOf m T hT W.w (ambOK_linOK h)).root i (vec m cv) = 0 := by
    intro i hi hj
    have hia : (i.val != W.w.a) = true := (bne_iff_ne_node_a (hw := ambOK_linOK h) hT i).mpr hi
    have hib : (i.val != W.w.b) = true := (bne_iff_ne_node_b (hw := ambOK_linOK h) hT i).mpr hj
    have hp : (fun i : ℕ => (i != W.w.a) && (i != W.w.b)) i.val = true := by
      rw [Bool.and_eq_true]
      exact ⟨hia, hib⟩
    have hmem : Chk.nodeN W.w i.val ∈ Chk.nodeList W.w
        (fun i : ℕ => (i != W.w.a) && (i != W.w.b)) :=
      (mem_nodeList (w := W.w) (p := fun i : ℕ => (i != W.w.a) && (i != W.w.b))
        (Chk.nodeN W.w i.val)).mpr ⟨i, hp, rfl⟩
    obtain ⟨_, hroot⟩ := (tabsOK_zm hT hcv (Chk.nodeN W.w i.val)).mp (hall _ hmem)
    have hroot' : root m (nodeRoot m W.w (typeOK_node_lt (linOK_typeOK (ambOK_linOK h))) i)
        (vec m cv) = 0 := hroot
    rw [linOf_root]
    show (Chk.sgnN W.w i : ZMod 3) • root m (nodeRoot m W.w
      (typeOK_node_lt (linOK_typeOK (ambOK_linOK h))) i) (vec m cv) = 0
    rw [hroot', smul_zero]
  exact ⟨h1', h2, h3, h4, linOf_basis hT (ambOK_linOK h) hbasis⟩

theorem ambientWitness_of_ambientOK (hT : Chk.tabsOK m T = true) {cv cz ℓ k : ℕ} {W : Chk.AmbW}
    {B B' : Array (Array ℤ)} (h : Chk.ambientOK T m cv cz ℓ k W B B' = true) :
    AmbientWitness (excRaw m) (vec m cv) (vec m cz) (ofMask m ℓ) (ofMask m k) := by
  simp only [excRaw]
  obtain ⟨hamb, hdet⟩ : Chk.ambOK T m cz cv k ℓ W = true ∧ Chk.detOK W.w B B' = true := by
    simpa only [Chk.ambientOK, Bool.and_eq_true] using h
  obtain ⟨-, hgen, hline, hjoin, hcv, hall, hbasis, hnotℓ, hnotk⟩ := ambOK_components hamb
  obtain ⟨hdet1, hdet2⟩ : Chk.invOK (Chk.rkN W.w.tc W.w.n) (Chk.cartanN W.w.tc W.w.n) B = true ∧
      Chk.invOK (Chk.rkN W.w.tc W.w.n - 1)
        (fun p q => Chk.cartanN W.w.tc W.w.n (Chk.offN W.w.a p) (Chk.offN W.w.a q)) B' = true := by
    simpa only [Chk.detOK, Bool.and_eq_true] using hdet
  have hat := ambAt_linOf hT hamb
  obtain ⟨ha1, -, ha3, ha4, ha5⟩ := hat
  have hlin := ambOK_linOK hamb
  have hdetcartan := linOf_det_ne_zero hT hlin hdet1
  have hdetsub : (((Matrix.of fun i j : Fin (Chk.rkN W.w.tc W.w.n) =>
      Chk.cartanN W.w.tc W.w.n i j).submatrix
      (fun i : {i : Fin (Chk.rkN W.w.tc W.w.n) //
        i ≠ (⟨W.w.a, linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n))} => (i : Fin _))
      (fun i : {i : Fin (Chk.rkN W.w.tc W.w.n) //
        i ≠ (⟨W.w.a, linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n))} => (i : Fin _))).det
      : ZMod 3) ≠ 0 := by
    rw [det_submatrix_offN_eq (M := fun i j : ℕ => Chk.cartanN W.w.tc W.w.n i j)
      (a := W.w.a) (linOK_a_lt hlin)]
    exact invOK_det_ne_zero hdet2
  refine ⟨linOf m T hT W.w hlin, ha1, ?_, ha3, ha4, ha5, hdetcartan, hdetsub⟩
  have h1s : (linOf m T hT W.w hlin).toLin.simpleRefl (linOf m T hT W.w hlin).a
      = reflection m (nodeRoot m W.w (typeOK_node_lt (linOK_typeOK hlin))
          ⟨W.w.a, linOK_a_lt hlin⟩) := by
    rw [show (linOf m T hT W.w hlin).a = (⟨W.w.a,
      linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n)) from rfl]
    exact linOf_simpleRefl hT hlin _
  have h2s : reflection m (nodeRoot m W.w (typeOK_node_lt (linOK_typeOK hlin))
        ⟨W.w.a, linOK_a_lt hlin⟩) ∈ weyl m (ofMask m ℓ) ⊔ weyl m (ofMask m k) := by
    simpa [nodeRoot, sup_comm] using joinOK_sound hT hjoin
  rw [h1s]
  change reflection m (nodeRoot m W.w (typeOK_node_lt (linOK_typeOK hlin))
      ⟨W.w.a, linOK_a_lt hlin⟩) ∈ normalizerGroup m (ofMask m ℓ) ⊔ normalizerGroup m (ofMask m k)
  rw [normalizerGroup_ofMask hnotℓ, normalizerGroup_ofMask hnotk]
  exact h2s

theorem extAmbDAt_of_ambDOK (hT : Chk.tabsOK m T = true) {cv cz ℓ k : ℕ} {W : Chk.AmbW}
    {perm : List ℕ} {half : ℕ} (h : Chk.ambDOK T m cv cz ℓ k W perm half = true) :
    ExtAmbDAt (excRaw m) (vec m cv) (vec m cz) (ofMask m ℓ) (ofMask m k) := by
  simp only [excRaw]
  obtain ⟨hamb, h3, hrk, hlen, hnodup, hall, hcart⟩ := ambDOK_components h
  have hat := ambAt_linOf hT hamb
  obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := hat
  have hlin := ambOK_linOK hamb
  have hmem_of : ∀ i : Fin (2 * half), perm.getD i.val 0 ∈ perm := by
    intro i
    have hi : i.val < perm.length := by omega
    exact (List.getD_eq_getElem perm 0 hi) ▸ List.getElem_mem hi
  let g : Fin (2 * half) → {i : Fin (Chk.rkN W.w.tc W.w.n) //
      i ≠ (⟨W.w.a, linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n))} := fun i =>
    ⟨⟨perm.getD i.val 0, (hall _ (hmem_of i)).1⟩,
      fun hh => (hall _ (hmem_of i)).2 (by simpa using congrArg Fin.val hh)⟩
  have hinj : Function.Injective g := by
    intro i i' hii
    have hii' : perm.getD i.val 0 = perm.getD i'.val 0 :=
      congrArg (fun x : {i : Fin (Chk.rkN W.w.tc W.w.n) //
        i ≠ (⟨W.w.a, linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n))} =>
        (x : Fin (Chk.rkN W.w.tc W.w.n)).val) hii
    rw [List.getD_eq_getElem perm 0 (by omega : i.val < perm.length),
      List.getD_eq_getElem perm 0 (by omega : i'.val < perm.length)] at hii'
    exact Fin.ext (hnodup.getElem_inj_iff.mp hii')
  have hcard : Fintype.card (Fin (2 * half)) = Fintype.card {i : Fin (Chk.rkN W.w.tc W.w.n) //
      i ≠ (⟨W.w.a, linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n))} := by
    rw [Fintype.card_fin]
    have h := Set.card_ne_eq (⟨W.w.a, linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n))
    rw [Fintype.card_fin] at h
    rw [show Fintype.card {i : Fin (Chk.rkN W.w.tc W.w.n) // i ≠
        (⟨W.w.a, linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n))} =
      Fintype.card (↥{x : Fin (Chk.rkN W.w.tc W.w.n) |
        x ≠ (⟨W.w.a, linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n))}) from rfl]
    omega
  let f : Fin (2 * half) ≃ {i : Fin (Chk.rkN W.w.tc W.w.n) //
      i ≠ (⟨W.w.a, linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n))} :=
    Equiv.ofBijective g (Fintype.bijective_iff_injective_and_card g |>.mpr ⟨hinj, hcard⟩)
  have hentries : ∀ i j, (linOf m T hT W.w hlin).cartan
      ((g i : Fin (Chk.rkN W.w.tc W.w.n))) ((g j : Fin (Chk.rkN W.w.tc W.w.n))) =
      CartanMatrix.D (2 * half) i j := by
    intro i j
    have hp := hcart
    have h1 := (nat_all_true.mp hp i i.isLt)
    have h2 := (nat_all_true.mp h1 j j.isLt)
    have h2' : Chk.cartanN W.w.tc W.w.n (perm.getD i.val 0) (perm.getD j.val 0) =
        Chk.cartanN 3 (2 * half) i.val j.val := by
      simpa only [beq_iff_eq] using h2
    rw [linOf_cartan]
    show Chk.cartanN W.w.tc W.w.n (perm.getD i.val 0) (perm.getD j.val 0) =
      CartanMatrix.D (2 * half) i j
    rw [h2']
    exact cartanOf_D (2 * half) i j
  refine ⟨linOf m T hT W.w hlin, ha1, ha2, ha3, ha4, ha5, half, h3, f, ?_⟩
  intro i j
  simp only [f]
  exact hentries i j

private theorem inside_eq_span_of_genOK (hT : Chk.tabsOK m T = true) {c gens : ℕ}
    {L : List (ℕ × ℕ)} {h : Fin 3 → Root m}
    (hgen : Chk.genOK T (nroots m) gens c L = true)
    (hrange : (↑(ofMask m gens) : Set (Root m)) = Set.range h) :
    inside m (ofMask m c) = Submodule.span (ZMod 3) (Set.range (fun i => coroot m (h i))) := by
  have hgen' : weyl m (ofMask m c) = Subgroup.closure (reflection m '' Set.range h) := by
    rw [← genOK_sound hT hgen, hrange]
  let X : Submodule (ZMod 3) (V m) := Submodule.span (ZMod 3) (Set.range fun i => coroot m (h i))
  let P : (V m ≃ₗ[ZMod 3] V m) → Prop := fun g => (∀ x ∈ X, g x ∈ X) ∧ ∀ v, g v - v ∈ X
  have hXmem : ∀ i, coroot m (h i) ∈ X := fun i => Submodule.subset_span ⟨i, rfl⟩
  have hgen1 : ∀ g ∈ reflection m '' Set.range h, P g := by
    rintro g ⟨i, ⟨k, rfl⟩, rfl⟩
    refine ⟨?_, ?_⟩
    · intro x hx
      rw [reflection_apply]
      exact X.sub_mem hx (X.smul_mem _ (hXmem k))
    · intro v
      rw [reflection_apply]
      have h : v - root m (h k) v • coroot m (h k) - v =
          -(root m (h k) v • coroot m (h k)) := by abel
      rw [h]
      exact X.neg_mem (X.smul_mem _ (hXmem k))
  have hall : ∀ {g : V m ≃ₗ[ZMod 3] V m},
      g ∈ Subgroup.closure (reflection m '' Set.range h) → P g :=
    Subgroup.closure_induction (k := reflection m '' Set.range h) (p := fun g _ => P g)
      hgen1
      ⟨by intro x hx; simpa using hx, by intro v; simp⟩
      (by
        intro x y _ _ hxP hyP
        obtain ⟨hxX, hxd⟩ := hxP
        obtain ⟨hyX, hyd⟩ := hyP
        refine ⟨fun z hz => hxX _ (hyX z hz), fun v => ?_⟩
        have h1 : x (y v) - v = x (y v - v) + (x v - v) := by rw [map_sub]; abel
        rw [show (x * y) v = x (y v) from rfl, h1]
        exact X.add_mem (hxX _ (hyd v)) (hxd v))
      (by
        intro x _ hxP
        obtain ⟨hxX, hxd⟩ := hxP
        refine ⟨fun z hz => ?_, fun v => ?_⟩
        · have h1 : x (x⁻¹ z) - x⁻¹ z ∈ X := hxd (x⁻¹ z)
          rw [show x (x⁻¹ z) = z from by simp] at h1
          have h2 : x⁻¹ z = z - (z - x⁻¹ z) := by abel
          rw [h2]
          exact X.sub_mem hz h1
        · have h1 : x (x⁻¹ v) - x⁻¹ v ∈ X := hxd (x⁻¹ v)
          rw [show x (x⁻¹ v) = v from by simp] at h1
          have h2 : x⁻¹ v - v = -(v - x⁻¹ v) := by abel
          rw [h2]
          exact X.neg_mem h1)
  refine le_antisymm ?_ ?_
  · rw [inside]
    refine Submodule.span_le.mpr ?_
    rintro x ⟨t, ht, rfl⟩
    have hst : reflection m t ∈ Subgroup.closure (reflection m '' Set.range h) := by
      rw [← hgen']
      exact Subgroup.subset_closure ⟨t, ht, rfl⟩
    have hmem := (hall (g := reflection m t) hst).2 (coroot m t)
    have hdisp : reflection m t (coroot m t) - coroot m t =
        -((2 : ZMod 3) • coroot m t) := by
      rw [reflection_apply, root_coroot]
      module
    rw [hdisp, ← neg_smul] at hmem
    have hx : coroot m t ∈ X := by
      refine (Submodule.smul_mem_iff X ?_).mp hmem
      decide +kernel
    exact hx
  · intro x hx
    refine Submodule.span_le.mpr ?_ hx
    rintro y ⟨i, rfl⟩
    refine Submodule.subset_span ⟨h i, ?_, rfl⟩
    exact genOK_subset hgen (Finset.mem_coe.mp (hrange.symm ▸ Set.mem_range_self i))

private theorem cent_eq_iInf_of_genOK (hT : Chk.tabsOK m T = true) {c gens : ℕ}
    {L : List (ℕ × ℕ)} {h : Fin 3 → Root m}
    (hgen : Chk.genOK T (nroots m) gens c L = true)
    (hrange : (↑(ofMask m gens) : Set (Root m)) = Set.range h) :
    cent m (ofMask m c) = ⨅ i, LinearMap.ker (root m (h i)) := by
  have hgen' : weyl m (ofMask m c) = Subgroup.closure (reflection m '' Set.range h) := by
    rw [← genOK_sound hT hgen, hrange]
  have hsub : ∀ i, h i ∈ ofMask m c := fun i =>
    genOK_subset hgen (Finset.mem_coe.mp (hrange.symm ▸ Set.mem_range_self i))
  refine le_antisymm ?_ ?_
  · intro v hv
    rw [Submodule.mem_iInf]
    intro i
    rw [LinearMap.mem_ker]
    simp only [cent, Submodule.mem_iInf, LinearMap.mem_ker] at hv
    exact hv (h i) (hsub i)
  · intro v hv
    rw [Submodule.mem_iInf] at hv
    rw [cent, Submodule.mem_iInf]
    intro t
    rw [Submodule.mem_iInf]
    intro ht
    rw [LinearMap.mem_ker]
    have hall : ∀ {g : V m ≃ₗ[ZMod 3] V m},
        g ∈ Subgroup.closure (reflection m '' Set.range h) → g v = v := by
      refine Subgroup.closure_induction (k := reflection m '' Set.range h)
        (p := fun g _ => g v = v) ?_ ?_ ?_ ?_
      · rintro g ⟨i, ⟨k, rfl⟩, rfl⟩
        rw [reflection_apply, LinearMap.mem_ker.mp (hv k), zero_smul]
        simp
      · rfl
      · intro x y _ _ hx hy
        rw [show (x * y) v = x (y v) from rfl, hy, hx]
      · intro x _ hx
        calc x⁻¹ v = x⁻¹ (x v) := by rw [hx]
          _ = v := by simp
    have hst : reflection m t ∈ Subgroup.closure (reflection m '' Set.range h) := by
      rw [← hgen']
      exact Subgroup.subset_closure ⟨t, ht, rfl⟩
    have hfixv := hall (g := reflection m t) hst
    rw [reflection_apply] at hfixv
    have h0 : root m t v • coroot m t = 0 := sub_eq_self.mp hfixv
    rcases smul_eq_zero.mp h0 with h1 | h1
    · exact h1
    · exfalso
      have h2 : root m t (coroot m t) = 2 := root_coroot m t
      rw [h1, map_zero] at h2
      exact absurd h2 (by decide +kernel)

private theorem span_coroot_smul_eq {h : Fin 3 → Root m} {s : Fin 3 → ZMod 3} (hs : ∀ i, s i ≠ 0) :
    Submodule.span (ZMod 3) (Set.range (fun i => s i • coroot m (h i))) =
      Submodule.span (ZMod 3) (Set.range (fun i => coroot m (h i))) := by
  refine le_antisymm ?_ ?_
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · refine Submodule.span_le.mpr ?_
    rintro _ ⟨i, rfl⟩
    show coroot m (h i) ∈
      Submodule.span (ZMod 3) (Set.range (fun j => s j • coroot m (h j)))
    have h1 : (s i)⁻¹ • (s i • coroot m (h i)) = coroot m (h i) := by
      rw [smul_smul, inv_mul_cancel₀ (hs i), one_smul]
    rw [← h1]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

private theorem iInf_ker_smul_eq {h : Fin 3 → Root m} {s : Fin 3 → ZMod 3} (hs : ∀ i, s i ≠ 0) :
    (⨅ i, LinearMap.ker (s i • root m (h i))) = ⨅ i, LinearMap.ker (root m (h i)) := by
  ext v
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.smul_apply, smul_eq_mul]
  constructor
  · intro hv i
    rcases mul_eq_zero.mp (hv i) with h | h
    · exact absurd h (hs i)
    · exact h
  · intro hv i
    rw [hv i, mul_zero]

private theorem span_inf_iInf_ker_eq_bot {α : Fin 3 → Module.Dual (ZMod 3) (V m)}
    {c : Fin 3 → V m} (hpair : ∀ i j, α i (c j) = (CartanMatrix.A 3 i j : ZMod 3)) :
    Submodule.span (ZMod 3) (Set.range c) ⊓ (⨅ i, LinearMap.ker (α i)) = ⊥ := by
  rw [Submodule.eq_bot_iff]
  intro v hv
  obtain ⟨hvX, hvY⟩ := Submodule.mem_inf.mp hv
  obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod 3)).mp hvX
  have hd : d = 0 := by
    refine cartanA_eq_zero_of_mulVec (p := 3) (r := 3) (by decide) fun i => ?_
    have hi : α i (∑ j, d j • c j) = 0 := by
      rw [Submodule.mem_iInf] at hvY
      exact LinearMap.mem_ker.mp (hvY i)
    rw [map_sum] at hi
    simpa only [map_smul, smul_eq_mul, hpair, mul_comm] using hi
  rw [hd]
  simp
private theorem exists_d5_nodes {b rk : ℕ} (hrk : rk = 5)
    (hb : b = 1 ∨ b = 3 ∨ b = 4) :
    ∃ n : Fin 3 → Fin rk, Function.Injective n ∧
      (∀ i : Fin rk, (i.val ≠ 0 ∧ i.val ≠ b) ↔ ∃ k : Fin 3, (n k).val = i.val) ∧
      (∀ i j : Fin 3, (Chk.cartanN 3 5 (n i) (n j) : ZMod 3) =
        (CartanMatrix.A 3 i j : ZMod 3)) := by
  subst rk
  rcases hb with h | h | h <;> subst b
  · refine ⟨![3, 2, 4], by decide, ?_, ?_⟩
    · intro i; fin_cases i <;> decide
    · intro i j; fin_cases i <;> fin_cases j <;> decide
  · refine ⟨![1, 2, 4], by decide, ?_, ?_⟩
    · intro i; fin_cases i <;> decide
    · intro i j; fin_cases i <;> fin_cases j <;> decide
  · refine ⟨![1, 2, 3], by decide, ?_, ?_⟩
    · intro i; fin_cases i <;> decide
    · intro i j; fin_cases i <;> fin_cases j <;> decide

private theorem d5_inside_eq_span (hT : Chk.tabsOK m T = true) {j : ℕ} {Lj : List (ℕ × ℕ)}
    {W : Chk.AmbW} (hlin : Chk.linOK T (nroots m) W.w = true)
    (hgenj : Chk.genOK T (nroots m)
      (Chk.nodeMask W.w fun i => i != 0 && i != W.w.b) j Lj = true)
    {n : Fin 3 → Fin (Chk.rkN W.w.tc W.w.n)} {sc : Fin 3 → V m}
    (hsc : ∀ k, sc k = (Chk.sgnN W.w (n k) : ZMod 3) •
      coroot m (nodeRoot m W.w (typeOK_node_lt (linOK_typeOK hlin)) (n k)))
    (hn_iff : ∀ i : Fin (Chk.rkN W.w.tc W.w.n),
      (i.val ≠ 0 ∧ i.val ≠ W.w.b) ↔ ∃ k : Fin 3, (n k).val = i.val) :
    inside m (ofMask m j) = Submodule.span (ZMod 3) (Set.range sc) := by
  have hw : ∀ i : Fin (Chk.rkN W.w.tc W.w.n), Chk.nodeN W.w i < nroots m :=
    typeOK_node_lt (linOK_typeOK hlin)
  let h : Fin 3 → Root m := fun k => nodeRoot m W.w hw (n k)
  have hrange : (↑(ofMask m (Chk.nodeMask W.w fun i => i != 0 && i != W.w.b)) :
      Set (Root m)) = Set.range h := by
    ext t
    rw [Finset.mem_coe, mem_ofMask_nodeMask hw (fun i => i != 0 && i != W.w.b),
      Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : i.val ≠ 0 ∧ i.val ≠ W.w.b := by
        simpa only [Bool.and_eq_true, bne_iff_ne, ne_eq] using hi
      obtain ⟨k, hk⟩ := (hn_iff i).mp hi'
      refine ⟨k, Fin.ext ?_⟩
      change Chk.nodeN W.w ↑(n k) = Chk.nodeN W.w ↑i
      rw [hk]
    · rintro ⟨k, rfl⟩
      refine ⟨n k, ?_, rfl⟩
      have hk : (n k).val ≠ 0 ∧ (n k).val ≠ W.w.b := (hn_iff (n k)).mpr ⟨k, rfl⟩
      simpa only [Bool.and_eq_true, bne_iff_ne, ne_eq] using hk
  rw [inside_eq_span_of_genOK hT hgenj hrange]
  let s : Fin 3 → ZMod 3 := fun k => (Chk.sgnN W.w (n k) : ZMod 3)
  have hs : ∀ k, s k ≠ 0 := by
    intro k
    simp only [s, Chk.sgnN]
    split_ifs <;> simp
  rw [show sc = fun k => s k • coroot m (h k) from funext hsc]
  exact (span_coroot_smul_eq (h := h) (s := s) hs).symm

private theorem d5_cent_eq_iInf (hT : Chk.tabsOK m T = true) {j : ℕ} {Lj : List (ℕ × ℕ)}
    {W : Chk.AmbW} (hlin : Chk.linOK T (nroots m) W.w = true)
    (hgenj : Chk.genOK T (nroots m)
      (Chk.nodeMask W.w fun i => i != 0 && i != W.w.b) j Lj = true)
    {n : Fin 3 → Fin (Chk.rkN W.w.tc W.w.n)}
    {sr : Fin 3 → Module.Dual (ZMod 3) (V m)}
    (hsr : ∀ k, sr k = (Chk.sgnN W.w (n k) : ZMod 3) •
      root m (nodeRoot m W.w (typeOK_node_lt (linOK_typeOK hlin)) (n k)))
    (hn_iff : ∀ i : Fin (Chk.rkN W.w.tc W.w.n),
      (i.val ≠ 0 ∧ i.val ≠ W.w.b) ↔ ∃ k : Fin 3, (n k).val = i.val) :
    cent m (ofMask m j) = ⨅ k, LinearMap.ker (sr k) := by
  have hw : ∀ i : Fin (Chk.rkN W.w.tc W.w.n), Chk.nodeN W.w i < nroots m :=
    typeOK_node_lt (linOK_typeOK hlin)
  let h : Fin 3 → Root m := fun k => nodeRoot m W.w hw (n k)
  have hrange : (↑(ofMask m (Chk.nodeMask W.w fun i => i != 0 && i != W.w.b)) :
      Set (Root m)) = Set.range h := by
    ext t
    rw [Finset.mem_coe, mem_ofMask_nodeMask hw (fun i => i != 0 && i != W.w.b),
      Set.mem_range]
    constructor
    · rintro ⟨i, hi, rfl⟩
      have hi' : i.val ≠ 0 ∧ i.val ≠ W.w.b := by
        simpa only [Bool.and_eq_true, bne_iff_ne, ne_eq] using hi
      obtain ⟨k, hk⟩ := (hn_iff i).mp hi'
      refine ⟨k, Fin.ext ?_⟩
      change Chk.nodeN W.w ↑(n k) = Chk.nodeN W.w ↑i
      rw [hk]
    · rintro ⟨k, rfl⟩
      refine ⟨n k, ?_, rfl⟩
      have hk : (n k).val ≠ 0 ∧ (n k).val ≠ W.w.b := (hn_iff (n k)).mpr ⟨k, rfl⟩
      simpa only [Bool.and_eq_true, bne_iff_ne, ne_eq] using hk
  rw [cent_eq_iInf_of_genOK hT hgenj hrange]
  let s : Fin 3 → ZMod 3 := fun k => (Chk.sgnN W.w (n k) : ZMod 3)
  have hs : ∀ k, s k ≠ 0 := by
    intro k
    simp only [s, Chk.sgnN]
    split_ifs <;> simp
  rw [show sr = fun k => s k • root m (h k) from funext hsr]
  exact (iInf_ker_smul_eq (h := h) (s := s) hs).symm

private theorem d5_inside_finrank {j : ℕ} {sc : Fin 3 → V m}
    {sr : Fin 3 → Module.Dual (ZMod 3) (V m)}
    (hinside : inside m (ofMask m j) = Submodule.span (ZMod 3) (Set.range sc))
    (hpair : ∀ i j, sr i (sc j) = (CartanMatrix.A 3 i j : ZMod 3)) :
    finrank (ZMod 3) (inside m (ofMask m j)) = 3 := by
  have hli : LinearIndependent (ZMod 3) sc :=
    cartanA_linearIndependent (p := 3) (r := 3) (by decide) hpair
  rw [hinside, finrank_span_eq_card hli, Fintype.card_fin]

private theorem d5_inside_inf_cent_eq_bot {j : ℕ} {sc : Fin 3 → V m}
    {sr : Fin 3 → Module.Dual (ZMod 3) (V m)}
    (hinside : inside m (ofMask m j) = Submodule.span (ZMod 3) (Set.range sc))
    (hcent : cent m (ofMask m j) = ⨅ k, LinearMap.ker (sr k))
    (hpair : ∀ i j, sr i (sc j) = (CartanMatrix.A 3 i j : ZMod 3)) :
    inside m (ofMask m j) ⊓ cent m (ofMask m j) = ⊥ := by
  rw [hinside, hcent]
  exact span_inf_iInf_ker_eq_bot (α := sr) (c := sc) hpair

private theorem d5_sup_eq_top {j : ℕ} {sr : Fin 3 → Module.Dual (ZMod 3) (V m)}
    (hdim : dim m = 5)
    (hcent : cent m (ofMask m j) = ⨅ k, LinearMap.ker (sr k))
    (hbot : inside m (ofMask m j) ⊓ cent m (ofMask m j) = ⊥)
    (hfin : finrank (ZMod 3) (inside m (ofMask m j)) = 3) :
    inside m (ofMask m j) ⊔ cent m (ofMask m j) = ⊤ := by
  let Φ : V m →ₗ[ZMod 3] (Fin 3 → ZMod 3) := LinearMap.pi sr
  have hker : cent m (ofMask m j) = LinearMap.ker Φ := by
    rw [hcent]
    ext v
    rw [Submodule.mem_iInf]
    constructor
    · intro hv
      rw [LinearMap.mem_ker]
      funext i
      simpa only [Φ, LinearMap.pi_apply, Pi.zero_apply, LinearMap.mem_ker] using hv i
    · intro hv
      rw [LinearMap.mem_ker] at hv
      intro i
      rw [LinearMap.mem_ker]
      simpa only [Φ, LinearMap.pi_apply, Pi.zero_apply] using congrFun hv i
  have hfrV : finrank (ZMod 3) (V m) = 5 := by
    rw [Module.finrank_fin_fun]
    exact hdim
  have hrange_le : finrank (ZMod 3) ↥(LinearMap.range Φ) ≤ 3 := by
    have h1 := Submodule.finrank_le (LinearMap.range Φ)
    rwa [Module.finrank_fin_fun] at h1
  have hcent_ge : 2 ≤ finrank (ZMod 3) ↥(cent m (ofMask m j)) := by
    rw [hker]
    let a := finrank (ZMod 3) ↥(LinearMap.range Φ)
    let b := finrank (ZMod 3) ↥(LinearMap.ker Φ)
    let c := finrank (ZMod 3) (V m)
    have h : a + b = c := LinearMap.finrank_range_add_finrank_ker Φ
    have ha : a ≤ 3 := hrange_le
    have hc : c = 5 := hfrV
    show 2 ≤ b
    omega
  have hsup_fin : finrank (ZMod 3)
      ↥(inside m (ofMask m j) ⊔ cent m (ofMask m j)) = 5 := by
    let x := finrank (ZMod 3) ↥(inside m (ofMask m j) ⊔ cent m (ofMask m j))
    let y := finrank (ZMod 3) ↥(inside m (ofMask m j) ⊓ cent m (ofMask m j))
    let z := finrank (ZMod 3) ↥(inside m (ofMask m j))
    let w := finrank (ZMod 3) ↥(cent m (ofMask m j))
    have h : x + y = z + w :=
      Submodule.finrank_sup_add_finrank_inf_eq (inside m (ofMask m j)) (cent m (ofMask m j))
    have hy : y = 0 := by
      show finrank (ZMod 3)
        ↥(inside m (ofMask m j) ⊓ cent m (ofMask m j)) = 0
      rw [hbot]
      simp
    have hz : z = 3 := hfin
    have hw : 2 ≤ w := hcent_ge
    have hxle : x ≤ 5 := by
      have h1 := Submodule.finrank_le (inside m (ofMask m j) ⊔ cent m (ofMask m j))
      rw [hfrV] at h1
      exact h1
    show x = 5
    omega
  refine Submodule.eq_top_of_finrank_eq ?_
  exact hsup_fin.trans hfrV.symm

private theorem d5_inside_cent_of_nodes (hT : Chk.tabsOK m T = true) {j : ℕ}
    {Lj : List (ℕ × ℕ)} {W : Chk.AmbW} (hlin : Chk.linOK T (nroots m) W.w = true)
    (hdim : dim m = 5)
    (hgenj : Chk.genOK T (nroots m)
      (Chk.nodeMask W.w fun i => i != 0 && i != W.w.b) j Lj = true)
    {n : Fin 3 → Fin (Chk.rkN W.w.tc W.w.n)}
    (hn_iff : ∀ i : Fin (Chk.rkN W.w.tc W.w.n),
      (i.val ≠ 0 ∧ i.val ≠ W.w.b) ↔ ∃ k : Fin 3, (n k).val = i.val)
    (hcartan : ∀ i j : Fin 3, (Chk.cartanN W.w.tc W.w.n (n i) (n j) : ZMod 3) =
      (CartanMatrix.A 3 i j : ZMod 3)) :
    inside m (ofMask m j) ⊓ cent m (ofMask m j) = ⊥ ∧
      inside m (ofMask m j) ⊔ cent m (ofMask m j) = ⊤ ∧
      finrank (ZMod 3) (inside m (ofMask m j)) = 3 := by
  have hw : ∀ i : Fin (Chk.rkN W.w.tc W.w.n), Chk.nodeN W.w i < nroots m :=
    typeOK_node_lt (linOK_typeOK hlin)
  let h : Fin 3 → Root m := fun k => nodeRoot m W.w hw (n k)
  let s : Fin 3 → ZMod 3 := fun k => (Chk.sgnN W.w (n k) : ZMod 3)
  let sc : Fin 3 → V m := fun k => s k • coroot m (h k)
  let sr : Fin 3 → Module.Dual (ZMod 3) (V m) := fun k => s k • root m (h k)
  have hpair : ∀ i j, sr i (sc j) = (CartanMatrix.A 3 i j : ZMod 3) := by
    intro i j
    have hp := linOf_pairing hT (linOK_typeOK hlin) (n i) (n j)
    rw [hp]
    exact hcartan i j
  have hinside := d5_inside_eq_span hT hlin hgenj (sc := sc) (by intro k; rfl) hn_iff
  have hcent := d5_cent_eq_iInf hT hlin hgenj (sr := sr) (by intro k; rfl) hn_iff
  have hbot := d5_inside_inf_cent_eq_bot hinside hcent hpair
  have hfin := d5_inside_finrank hinside hpair
  have htop := d5_sup_eq_top hdim hcent hbot hfin
  exact ⟨hbot, htop, hfin⟩

private theorem d5_inside_cent_of_d5OK (hT : Chk.tabsOK m T = true) {cv cz ℓ j k : ℕ}
    {W : Chk.AmbW} {Lj : List (ℕ × ℕ)} (h : Chk.d5OK T m cv cz ℓ j k W Lj = true) :
    inside m (ofMask m j) ⊓ cent m (ofMask m j) = ⊥ ∧
      inside m (ofMask m j) ⊔ cent m (ofMask m j) = ⊤ ∧
      finrank (ZMod 3) (inside m (ofMask m j)) = 3 := by
  obtain ⟨hamb, htc, hn5, ha0, hb, hgenj, -, -⟩ := d5OK_components h
  have hlin := ambOK_linOK hamb
  obtain ⟨-, -, -, -, -, -, hbasis, -, -⟩ := ambOK_components hamb
  have hrk : Chk.rkN W.w.tc W.w.n = 5 := by rw [htc, hn5]; rfl
  have hdim_eq : Chk.rkN W.w.tc W.w.n = dim m := by
    have hb' := hbasis
    simp only [Chk.basisOK, Bool.and_eq_true, beq_iff_eq] at hb'
    exact hb'.1
  have hdim5 : dim m = 5 := by omega
  have hgenj0 : Chk.genOK T (nroots m)
      (Chk.nodeMask W.w fun i => i != 0 && i != W.w.b) j Lj = true := by
    simpa only [ha0] using hgenj
  obtain ⟨n, -, hn_iff, hn_cartan⟩ :=
    exists_d5_nodes (b := W.w.b) (rk := Chk.rkN W.w.tc W.w.n) hrk hb
  have hcartan : ∀ i j : Fin 3, (Chk.cartanN W.w.tc W.w.n (n i) (n j) : ZMod 3) =
      (CartanMatrix.A 3 i j : ZMod 3) := by
    intro i j
    set x : ℕ := (n i).val with hx
    set y : ℕ := (n j).val with hy
    have hxy : Chk.cartanN W.w.tc W.w.n x y = Chk.cartanN 3 5 x y := by rw [htc, hn5]
    rw [hxy, hx, hy]
    exact hn_cartan i j
  exact d5_inside_cent_of_nodes hT hlin hdim5 hgenj0 hn_iff hcartan

private theorem d5_cartan_of_e (hT : Chk.tabsOK m T = true) {W : Chk.AmbW}
    (hlin : Chk.linOK T (nroots m) W.w = true) (htc : W.w.tc = 3) (hn5 : W.w.n = 5)
    {e : Fin 5 ≃ Fin (Chk.rkN W.w.tc W.w.n)}
    (he : ∀ i : Fin 5, (e i).val = i.val) :
    ∀ i j : Fin 5, (linOf m T hT W.w hlin).cartan (e i) (e j) =
      CartanMatrix.D 5 i j := by
  intro i j
  set x : ℕ := (e i).val with hx
  set y : ℕ := (e j).val with hy
  have hxy : Chk.cartanN W.w.tc W.w.n x y = Chk.cartanN 3 5 x y := by rw [htc, hn5]
  have hcart : (linOf m T hT W.w hlin).cartan (e i) (e j) =
      Chk.cartanN W.w.tc W.w.n x y := by
    rw [hx, hy]
    rfl
  rw [hcart, hxy, hx, hy, he i, he j]
  exact cartanOf_D 5 i j

private theorem d5_parabj_of_d5OK (hT : Chk.tabsOK m T = true) {j : ℕ}
    {Lj : List (ℕ × ℕ)} {W : Chk.AmbW} (hlin : Chk.linOK T (nroots m) W.w = true)
    (hgenj : Chk.genOK T (nroots m)
      (Chk.nodeMask W.w fun i => i != W.w.a && i != W.w.b) j Lj = true)
    (hnotj : Chk.notB2 m j = true) :
    (linOf m T hT W.w hlin).toLin.parab {i : Fin (Chk.rkN W.w.tc W.w.n) |
      i ≠ (⟨W.w.a, linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n)) ∧
      i ≠ (⟨W.w.b, linOK_b_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n))} =
      normalizerGroup m (ofMask m j) := by
  have hsetab : ({i : Fin (Chk.rkN W.w.tc W.w.n) |
      i ≠ (⟨W.w.a, linOK_a_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n)) ∧
      i ≠ (⟨W.w.b, linOK_b_lt hlin⟩ : Fin (Chk.rkN W.w.tc W.w.n))} : Set _) =
      {i : Fin (Chk.rkN W.w.tc W.w.n) |
        (fun j : ℕ => (j != W.w.a) && (j != W.w.b)) ↑i = true} := by
    ext i
    simp only [Set.mem_setOf_eq, Bool.and_eq_true]
    exact and_congr (bne_iff_ne_node_a (hw := hlin) hT i).symm
      (bne_iff_ne_node_b (hw := hlin) hT i).symm
  have h1 := linOf_parab_eq hT hlin hgenj hnotj
  rwa [← hsetab] at h1

private theorem d5_label_of_d5OK (hT : Chk.tabsOK m T = true) {j : ℕ}
    (hlabel : Chk.labelOf T m j = (1, 3, 1) ∨ Chk.labelOf T m j = (5, 3, 1)) :
    ∃ lab : CFSG.Assembly.LargeEvenLabel,
      (lab = ⟨.twA, 3, 1⟩ ∨ lab = ⟨.twD, 3, 1⟩) ∧
        GGLabelIso lab (label m (ofMask m j)) := by
  let lab : CFSG.Assembly.LargeEvenLabel := label m (ofMask m j)
  refine ⟨lab, ?_, Or.inl rfl⟩
  rcases hlabel with h | h
  · left
    have h' : encL lab = (1, 3, 1) := (labelOf_eq hT j).symm.trans h
    obtain ⟨tag, rank, nn⟩ := lab
    cases tag <;> (simp [encL, tagIdx] at h' ⊢; try exact h')
  · right
    have h' : encL lab = (5, 3, 1) := (labelOf_eq hT j).symm.trans h
    obtain ⟨tag, rank, nn⟩ := lab
    cases tag <;> (simp [encL, tagIdx] at h' ⊢; try exact h')

theorem extD5At_of_d5OK (hT : Chk.tabsOK m T = true) {cv cz ℓ j k : ℕ} {W : Chk.AmbW}
    {Lj : List (ℕ × ℕ)} (h : Chk.d5OK T m cv cz ℓ j k W Lj = true) :
    ExtD5At (excRaw m) (vec m cv) (vec m cz) (ofMask m ℓ) (ofMask m j) (ofMask m k) := by
  simp only [excRaw]
  obtain ⟨hamb, htc, hn5, ha0, hb, hgenj, hnotj, hlabel⟩ := d5OK_components h
  have hlin := ambOK_linOK hamb
  obtain ⟨ha1, ha2, ha3, ha4, ha5⟩ := ambAt_linOf hT hamb
  have hrk : Chk.rkN W.w.tc W.w.n = 5 := by rw [htc, hn5]; rfl
  obtain ⟨hbot, htop, hfin⟩ := d5_inside_cent_of_d5OK hT h
  let Wl := linOf m T hT W.w hlin
  let e : Fin 5 ≃ Fin (Chk.rkN W.w.tc W.w.n) :=
    { toFun := fun i => Fin.cast hrk.symm i
      invFun := fun i => Fin.cast hrk i
      left_inv := by intro i; ext; rfl
      right_inv := by intro i; ext; rfl }
  have he : ∀ i : Fin 5, (e i).val = i.val := fun i => rfl
  have hentries : ∀ i j, Wl.cartan (e i) (e j) = CartanMatrix.D 5 i j :=
    d5_cartan_of_e hT hlin htc hn5 he
  have hae : Wl.a = e 0 := by
    apply Fin.ext
    rw [show (Wl.a).val = W.w.a from rfl, ha0]
    rfl
  have hbe : Wl.b = e 1 ∨ Wl.b = e 3 ∨ Wl.b = e 4 := by
    rcases hb with hb1 | hb3 | hb4
    · left; apply Fin.ext
      rw [show (Wl.b).val = W.w.b from rfl, hb1]
      rfl
    · right; left; apply Fin.ext
      rw [show (Wl.b).val = W.w.b from rfl, hb3]
      rfl
    · right; right; apply Fin.ext
      rw [show (Wl.b).val = W.w.b from rfl, hb4]
      rfl
  obtain ⟨lab, hlab, hiso⟩ := d5_label_of_d5OK hT hlabel
  exact ⟨Wl, ha1, ha2, ha3, ha4, ha5, ⟨e, hentries, hae, hbe⟩,
    d5_parabj_of_d5OK hT hlin hgenj hnotj, ⟨lab, hlab, hiso, hbot, htop, hfin⟩⟩

theorem inLSelDetRaw_of_selE6OK (hT : Chk.tabsOK m T = true) {k : ℕ} {L : List (ℕ × ℕ)}
    (h : Chk.selE6OK T m k w L = true) : InLSelDetRaw (excRaw m) (ofMask m k) := by
  simp only [excRaw]
  obtain ⟨htc, hun, htype, hgen, hnotk⟩ := selE6OK_components h
  have hrk : Chk.rkN w.tc w.n = 6 := by rw [htc]; rfl
  have hw : ∀ i : Fin (Chk.rkN w.tc w.n), Chk.nodeN w i < nroots m := typeOK_node_lt htype
  let e : Fin 6 → Root m := fun i => nodeRoot m w hw (Fin.cast hrk.symm i)
  have hs : ∀ j, Chk.sgnN w j = 1 := sgnN_eq_one_of_unsignedN hun
  have hpairs : ∀ i i' : Fin 6, (T.pair[(e i).val]!)[(e i').val]! =
      Chk.cartanN w.tc w.n (Fin.cast hrk.symm i) (Fin.cast hrk.symm i') := by
    intro i i'
    have hpair := typeOK_pairing (T := T) htype (Fin.cast hrk.symm i) (Fin.cast hrk.symm i')
    rw [hs, hs, one_mul, one_mul] at hpair
    exact hpair
  have hrange : (↑(ofMask m (Chk.nodeMask w fun _ => true)) : Set (Root m)) = Set.range e := by
    ext t
    rw [Finset.mem_coe, mem_ofMask_nodeMask hw (fun _ => true), Set.mem_range]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact ⟨Fin.cast hrk i, by simp [e]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hrk.symm i, rfl, rfl⟩
  refine ⟨e, ?_, ?_⟩
  · intro i i'
    change pairing m (e i) (e i') = CartanMatrix.E 6 i i'
    rw [← tabsOK_pair hT (e i) (e i'), hpairs i i']
    have h4 : Chk.cartanN w.tc w.n (Fin.cast hrk.symm i : ℕ) (Fin.cast hrk.symm i' : ℕ) =
        CartanMatrix.E 6 i i' := by
      rw [show Chk.cartanN w.tc w.n (Fin.cast hrk.symm i : ℕ) (Fin.cast hrk.symm i' : ℕ)
          = Chk.cartanN 4 w.n (i : ℕ) (i' : ℕ) from by simp only [htc, Fin.coe_cast]]
      exact cartanOf_E w.n i i'
    exact h4
  · change normalizerGroup m (ofMask m k) = Subgroup.closure (reflection m '' Set.range e)
    rw [normalizerGroup_ofMask hnotk, ← genOK_sound hT hgen, hrange]

theorem inLSelD6Raw_of_selD6OK (hT : Chk.tabsOK m T = true) {j k : ℕ} {L L' : List (ℕ × ℕ)}
    (h : Chk.selD6OK T m j k w L L' = true) :
    InLSelD6Raw (excRaw m) (ofMask m j) (ofMask m k) := by
  simp only [excRaw]
  obtain ⟨htc, hn, hb45, htype, hgenk, hgenj, hnotj, hnotk⟩ := selD6OK_components h
  have hrk : Chk.rkN w.tc w.n = 6 := by rw [htc, hn]; rfl
  have hw : ∀ i : Fin (Chk.rkN w.tc w.n), Chk.nodeN w i < nroots m := typeOK_node_lt htype
  let e : Fin 6 → Root m := fun i => nodeRoot m w hw (Fin.cast hrk.symm i)
  have hb6 : w.b < 6 := by omega
  let b : Fin 6 := ⟨w.b, hb6⟩
  let ε : Fin 6 → ℤˣ := fun i =>
    if w.neg.getD (Fin.cast hrk.symm i) false then -1 else 1
  have hε : ∀ i, ((ε i : ℤˣ) : ℤ) = Chk.sgnN w (Fin.cast hrk.symm i) := by
    intro i
    simp only [ε, Chk.sgnN]
    split_ifs <;> simp
  have hpairs : ∀ i i' : Fin 6,
      Chk.sgnN w (Fin.cast hrk.symm i) * Chk.sgnN w (Fin.cast hrk.symm i') *
        pairing m (e i) (e i') = CartanMatrix.D 6 i i' := by
    intro i i'
    have hpair := typeOK_pairing (T := T) htype (Fin.cast hrk.symm i) (Fin.cast hrk.symm i')
    have htabs : (T.pair[Chk.nodeN w (Fin.cast hrk.symm i)]!)[
        Chk.nodeN w (Fin.cast hrk.symm i')]! = pairing m (e i) (e i') :=
      tabsOK_pair hT (e i) (e i')
    rw [htabs] at hpair
    have h4 : Chk.cartanN w.tc w.n (Fin.cast hrk.symm i : ℕ) (Fin.cast hrk.symm i' : ℕ) =
        CartanMatrix.D 6 i i' := by
      rw [show Chk.cartanN w.tc w.n (Fin.cast hrk.symm i : ℕ) (Fin.cast hrk.symm i' : ℕ)
          = Chk.cartanN 3 6 (i : ℕ) (i' : ℕ) from by simp only [htc, hn, Fin.coe_cast]]
      exact cartanOf_D 6 i i'
    rwa [h4] at hpair
  have hrangek : (↑(ofMask m (Chk.nodeMask w fun _ => true)) : Set (Root m)) = Set.range e := by
    ext t
    rw [Finset.mem_coe, mem_ofMask_nodeMask hw (fun _ => true), Set.mem_range]
    constructor
    · rintro ⟨i, -, rfl⟩
      exact ⟨Fin.cast hrk i, by simp [e]⟩
    · rintro ⟨i, rfl⟩
      exact ⟨Fin.cast hrk.symm i, rfl, rfl⟩
  have hrangej : (↑(ofMask m (Chk.nodeMask w fun i => i != w.b)) : Set (Root m)) =
      e '' {i : Fin 6 | i ≠ b} := by
    ext t
    rw [Finset.mem_coe, mem_ofMask_nodeMask hw (fun i => i != w.b), Set.mem_image]
    constructor
    · rintro ⟨i, hi, rfl⟩
      refine ⟨Fin.cast hrk i, ?_, ?_⟩
      · simp only [Set.mem_setOf_eq]
        rw [ne_eq, Fin.ext_iff, Fin.coe_cast]
        exact bne_iff_ne.mp hi
      · simp [e]
    · rintro ⟨i, hi, rfl⟩
      refine ⟨Fin.cast hrk.symm i, ?_, ?_⟩
      · rw [bne_iff_ne, Fin.coe_cast]
        intro hc
        exact hi (Fin.ext hc)
      · rfl
  refine ⟨e, ε, b, ?_, ?_, ?_, ?_⟩
  · rcases hb45 with h | h
    · left; exact Fin.ext h
    · right; exact Fin.ext h
  · intro i i'
    rw [hε i, hε i']
    exact hpairs i i'
  · change normalizerGroup m (ofMask m k) = Subgroup.closure (reflection m '' Set.range e)
    rw [normalizerGroup_ofMask hnotk, ← genOK_sound hT hgenk, hrangek]
  · change normalizerGroup m (ofMask m j) =
      Subgroup.closure (reflection m '' (e '' {i : Fin 6 | i ≠ b}))
    rw [normalizerGroup_ofMask hnotj, ← genOK_sound hT hgenj, hrangej]

end

end CFSG.StandardType.GGQ2Frame.ExcRaw

end

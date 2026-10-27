module

public import CFSG.Monster.B.Fischer.ArrCert
public import CFSG.Monster.B.Co2.PermArr
public import CFSG.RankThree.Native.DerivedGenerators

public section

namespace CFSG.RankThree.Native

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Monster.B.Fischer
open scoped commutatorElement

variable {n : ℕ}

theorem permOfArr_eq_of_rep {t : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g) :
    permOfArr n t = g := by
  have hc : (∀ i < n, t[i]! < n) ∧ ∀ i < n, ∀ j < n, t[i]! = t[j]! → i = j := by
    refine ⟨fun i hi => ht.lt hi, fun i hi j hj hij => ?_⟩
    rw [ht.apply hi, ht.apply hj] at hij
    exact congrArg Fin.val (g.injective (Fin.ext hij))
  refine Equiv.ext fun x => Fin.ext ?_
  rw [permOfArr, dite_eq_left hc]
  exact ht x

theorem rep_of_eqA {t u : Array ℕ} {g : Equiv.Perm (Fin n)} (ht : Rep n t g)
    (h : eqA n t u = true) : Rep n u g := fun x => by
  have := allLt_spec h x.2
  rw [beq_iff_eq] at this
  rw [← this]
  exact ht x

@[expose] def validA (n : ℕ) (a : Array ℕ) : Bool := isInvA n a (invCand n a)

theorem rep_of_validA {a : Array ℕ} (h : validA n a = true) : Rep n a (permOfArr n a) :=
  (rep_permOfArr h).1

theorem rep_inv_of_validA {a : Array ℕ} (h : validA n a = true) :
    Rep n (invCand n a) (permOfArr n a)⁻¹ :=
  (rep_permOfArr h).2

@[expose] def keyA (n : ℕ) (ps : List ℕ) (a : Array ℕ) : ℕ :=
  Nat.ofDigits n (ps.map fun p => a[p]!)

theorem keyA_eq {ps : List ℕ} (hps : ∀ p ∈ ps, p < n) {a b : Array ℕ} (ha : validA n a = true)
    (hb : validA n b = true) (hab : permOfArr n a = permOfArr n b) :
    keyA n ps a = keyA n ps b := by
  unfold keyA
  congr 1
  apply List.map_congr_left
  intro p hp
  rw [(rep_of_validA ha).apply (hps p hp), (rep_of_validA hb).apply (hps p hp), hab]

@[expose] def leftA (n : ℕ) (gs : Array (Array ℕ)) (k : ℕ) (a : Array ℕ) : Array ℕ :=
  compA n gs[k]! a

@[expose] noncomputable def permsA (n : ℕ) (gs : Array (Array ℕ)) : Set (Equiv.Perm (Fin n)) :=
  (fun k => permOfArr n gs[k]!) '' {k | k < gs.size}

@[expose] def enumOK (n : ℕ) (gs : Array (Array ℕ)) (ps : List ℕ) (c : ArrCert) : Bool :=
  allLt gs.size (fun k => validA n gs[k]!) &&
    arrCertOK (leftA n gs) gs.size (validA n) (keyA n ps) (idA n) c

@[expose] def enumBfs (n : ℕ) (gs : Array (Array ℕ)) (ps : List ℕ) (fuel : ℕ) : ArrCert :=
  arrBfs (leftA n gs) gs.size (keyA n ps) (idA n) fuel

theorem enumOK_gens_valid {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (h : enumOK n gs ps c = true) {k : ℕ} (hk : k < gs.size) : validA n gs[k]! = true := by
  simp only [enumOK, Bool.and_eq_true] at h
  exact allLt_spec h.1 hk

theorem enumOK_spec {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (h : enumOK n gs ps c = true) :
    (∀ x, x ∈ Subgroup.closure (permsA n gs) ↔ ∃ i < c.pts.size, permOfArr n c.pts[i]! = x) ∧
    Nat.card (Subgroup.closure (permsA n gs)) = c.pts.size ∧
    ∀ i < c.pts.size, validA n c.pts[i]! = true := by
  simp only [enumOK, Bool.and_eq_true] at h
  obtain ⟨hgs, hc⟩ := h
  have hact : ∀ k < gs.size, ∀ a, validA n a = true →
      permOfArr n (leftA n gs k a) = permOfArr n gs[k]! * permOfArr n a := by
    intro k hk a ha
    exact permOfArr_eq_of_rep (rep_compA (rep_of_validA (allLt_spec hgs hk)) (rep_of_validA ha))
  have hkey : ∀ a b, validA n a = true → validA n b = true → permOfArr n a = permOfArr n b →
      keyA n ps a = keyA n ps b := fun a b ha hb hab => keyA_eq hps ha hb hab
  obtain ⟨hmem, hcard⟩ := card_closure_of_arrCertOK (G := Equiv.Perm (Fin n)) (dec := permOfArr n)
    (gens := fun k => permOfArr n gs[k]!) hc hact hkey (permOfArr_eq_of_rep rep_idA)
  exact ⟨hmem, hcard, fun i hi => arrCertOK_valid hc hi⟩

theorem enumOK_exists_rep {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (h : enumOK n gs ps c = true) {x : Equiv.Perm (Fin n)}
    (hx : x ∈ Subgroup.closure (permsA n gs)) : ∃ i < c.pts.size, Rep n c.pts[i]! x := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps h
  obtain ⟨i, hi, rfl⟩ := (hmem x).1 hx
  exact ⟨i, hi, rep_of_validA (hval i hi)⟩

theorem enumOK_mem {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert} (hps : ∀ p ∈ ps, p < n)
    (h : enumOK n gs ps c = true) {x : Equiv.Perm (Fin n)} {i : ℕ} (hi : i < c.pts.size)
    (hx : Rep n c.pts[i]! x) : x ∈ Subgroup.closure (permsA n gs) := by
  obtain ⟨hmem, -, hval⟩ := enumOK_spec hps h
  exact (hmem x).2 ⟨i, hi, (rep_of_validA (hval i hi)).unique hx⟩

theorem enumOK_mem_of_any {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (h : enumOK n gs ps c = true) {t : Array ℕ}
    {x : Equiv.Perm (Fin n)} (ht : Rep n t x) (hany : c.pts.toList.any (eqA n t) = true) :
    x ∈ Subgroup.closure (permsA n gs) := by
  rw [List.any_eq_true] at hany
  obtain ⟨a, ha, he⟩ := hany
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem ha
  have hi' : i < c.pts.size := by simpa using hi
  refine enumOK_mem hps h hi' (rep_of_eqA ht ?_)
  rw [Array.getElem_toList] at he
  rwa [getElem!_pos c.pts i hi']

theorem enumOK_mem_of_mem {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (h : enumOK n gs ps c = true) {t : Array ℕ}
    {x : Equiv.Perm (Fin n)} (ht : Rep n t x) (hmem : t ∈ c.pts.toList) :
    x ∈ Subgroup.closure (permsA n gs) := by
  obtain ⟨i, hi, rfl⟩ := List.getElem_of_mem hmem
  have hi' : i < c.pts.size := by simpa using hi
  refine enumOK_mem hps h hi' ?_
  rw [Array.getElem_toList] at ht
  rwa [getElem!_pos c.pts i hi']

@[expose] def conjA (n : Nat) (g y : Array Nat) : Array Nat :=
  compA n g (compA n y (invCand n g))

@[expose] def conjInvA (n : Nat) (g y : Array Nat) : Array Nat :=
  compA n (invCand n g) (compA n y g)

@[expose] def commutatorA (n : Nat) (g h : Array Nat) : Array Nat :=
  compA n (compA n g h) (compA n (invCand n g) (invCand n h))

theorem rep_conjA {g y : Array ℕ} {Y : Equiv.Perm (Fin n)} (hg : validA n g = true)
    (hy : Rep n y Y) : Rep n (conjA n g y) (permOfArr n g * Y * (permOfArr n g)⁻¹) := by
  rw [mul_assoc]
  exact rep_compA (rep_of_validA hg) (rep_compA hy (rep_inv_of_validA hg))

theorem rep_conjInvA {g y : Array ℕ} {Y : Equiv.Perm (Fin n)} (hg : validA n g = true)
    (hy : Rep n y Y) : Rep n (conjInvA n g y) ((permOfArr n g)⁻¹ * Y * permOfArr n g) := by
  rw [mul_assoc]
  exact rep_compA (rep_inv_of_validA hg) (rep_compA hy (rep_of_validA hg))

theorem rep_commutatorA {g h : Array ℕ} (hg : validA n g = true) (hh : validA n h = true) :
    Rep n (commutatorA n g h) ⁅permOfArr n g, permOfArr n h⁆ := by
  rw [commutatorElement_def, mul_assoc (permOfArr n g * permOfArr n h)]
  exact rep_compA (rep_compA (rep_of_validA hg) (rep_of_validA hh))
    (rep_compA (rep_inv_of_validA hg) (rep_inv_of_validA hh))

theorem mem_permsA {gs : Array (Array ℕ)} {k : ℕ} (hk : k < gs.size) :
    permOfArr n gs[k]! ∈ permsA n gs := ⟨k, hk, rfl⟩

@[expose] def conjGens (n : ℕ) (c : ArrCert) (k : ℕ) : Array (Array ℕ) :=
  c.pts.map fun g => conjA n g c.pts[k]!

@[expose] def conjPointOK (n : ℕ) (ps : List ℕ) (c : ArrCert) (k : ℕ) (ck : ArrCert) : Bool :=
  enumOK n (conjGens n c k) ps ck && ck.pts.size == c.pts.size

@[expose] def conjSimpleOK (n : ℕ) (ps : List ℕ) (c : ArrCert) : Bool :=
  allLt c.pts.size fun k => eqA n c.pts[k]! (idA n) ||
    conjPointOK n ps c k (enumBfs n (conjGens n c k) ps (c.pts.size + 1))

theorem conjGens_size (c : ArrCert) (k : ℕ) : (conjGens n c k).size = c.pts.size := by
  simp [conjGens]

theorem conjGens_get {c : ArrCert} {k j : ℕ} (hj : j < c.pts.size) :
    (conjGens n c k)[j]! = conjA n c.pts[j]! c.pts[k]! := by
  rw [getElem!_pos _ j (by rw [conjGens_size]; exact hj), getElem!_pos c.pts j hj]
  simp [conjGens]

theorem isSimpleGroup_of_conjSimpleOK {gs : Array (Array ℕ)} {ps : List ℕ} {c : ArrCert}
    (hps : ∀ p ∈ ps, p < n) (hc : enumOK n gs ps c = true) (hnt : 1 < c.pts.size)
    (h : conjSimpleOK n ps c = true) : IsSimpleGroup (Subgroup.closure (permsA n gs)) := by
  obtain ⟨hmem, hcard, hval⟩ := enumOK_spec hps hc
  set D := Subgroup.closure (permsA n gs)
  apply isSimpleGroup_of_conj_closure
  · by_contra hall
    simp only [not_exists, not_and, not_not] at hall
    have hsub : (D : Set (Equiv.Perm (Fin n))) ⊆ {1} := fun g hg => hall g hg
    have h1 : Nat.card D ≤ 1 := by
      calc Nat.card D = (D : Set (Equiv.Perm (Fin n))).ncard := (Nat.card_coe_set_eq _).symm
        _ ≤ ({1} : Set (Equiv.Perm (Fin n))).ncard := Set.ncard_le_ncard hsub (Set.toFinite _)
        _ = 1 := Set.ncard_singleton _
    omega
  · intro e he he1
    obtain ⟨k, hk, rfl⟩ := (hmem e).1 he
    have hck := allLt_spec h hk
    simp only [Bool.or_eq_true] at hck
    rcases hck with hid | hck
    · exact absurd ((eqA_iff (rep_of_validA (hval k hk)) rep_idA).1 hid) he1
    · simp only [conjPointOK, Bool.and_eq_true, beq_iff_eq] at hck
      obtain ⟨hE, hS⟩ := hck
      obtain ⟨-, hcardk, -⟩ := enumOK_spec hps hE
      set K := Subgroup.closure (permsA n (conjGens n c k))
      have hgen : ∀ j < c.pts.size, permOfArr n (conjGens n c k)[j]! =
          permOfArr n c.pts[j]! * permOfArr n c.pts[k]! * (permOfArr n c.pts[j]!)⁻¹ := by
        intro j hj
        rw [conjGens_get hj]
        exact permOfArr_eq_of_rep (rep_conjA (hval j hj) (rep_of_validA (hval k hk)))
      have hKD : K ≤ D := by
        rw [Subgroup.closure_le]
        rintro _ ⟨j, hj, rfl⟩
        have hj' : j < c.pts.size := by rw [← conjGens_size (n := n) c k]; exact hj
        dsimp only
        rw [SetLike.mem_coe, hgen j hj']
        exact D.mul_mem (D.mul_mem ((hmem _).2 ⟨j, hj', rfl⟩) ((hmem _).2 ⟨k, hk, rfl⟩))
          (D.inv_mem ((hmem _).2 ⟨j, hj', rfl⟩))
      have hKeq : K = D := Subgroup.eq_of_le_of_card_ge hKD (by rw [hcardk, hS, hcard])
      refine le_trans hKeq.symm.le ?_
      rw [Subgroup.closure_le]
      rintro _ ⟨j, hj, rfl⟩
      have hj' : j < c.pts.size := by rw [← conjGens_size (n := n) c k]; exact hj
      dsimp only
      rw [SetLike.mem_coe, hgen j hj']
      exact Subgroup.subset_closure ⟨_, (hmem _).2 ⟨j, hj', rfl⟩, rfl⟩

end CFSG.RankThree.Native

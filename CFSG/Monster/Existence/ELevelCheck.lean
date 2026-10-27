module

public import CFSG.Monster.Existence.ELevelBits
public import CFSG.Monster.Existence.ELevelConv

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Existence

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.B CFSG.Monster.B.Short
  CFSG.Monster.B.Rep4371 CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel
  CFSG.Monster.B.TwoA.Census

@[expose] def findAll (p : ℕ → Bool) : ℕ → List ℕ → List ℕ
  | 0, acc => acc
  | n + 1, acc => findAll p n (if p n then n :: acc else acc)

theorem mem_findAll {p : ℕ → Bool} (n : ℕ) :
    ∀ (acc : List ℕ) (a : ℕ), a ∈ findAll p n acc ↔ (a < n ∧ p a = true) ∨ a ∈ acc := by
  induction n with
  | zero => intro acc a; simp [findAll]
  | succ n ih =>
    intro acc a
    rw [findAll, ih]
    by_cases hp : p n = true
    · simp only [hp, ite_true, List.mem_cons]
      constructor
      · rintro (⟨h1, h2⟩ | h | h)
        · exact Or.inl ⟨Nat.lt_succ_of_lt h1, h2⟩
        · exact Or.inl ⟨by rw [h]; exact Nat.lt_succ_self n, by rw [h]; exact hp⟩
        · exact Or.inr h
      · rintro (⟨h1, h2⟩ | h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | h1
          · exact Or.inl ⟨h1, h2⟩
          · exact Or.inr (Or.inl h1)
        · exact Or.inr (Or.inr h)
    · have hp' : p n = false := by simpa using hp
      simp only [hp', Bool.false_eq_true, ite_false]
      constructor
      · rintro (⟨h1, h2⟩ | h)
        · exact Or.inl ⟨Nat.lt_succ_of_lt h1, h2⟩
        · exact Or.inr h
      · rintro (⟨h1, h2⟩ | h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h1 | h1
          · exact Or.inl ⟨h1, h2⟩
          · exact absurd (h1 ▸ h2) hp
        · exact Or.inr h

@[expose] def foundCodes : List ℕ :=
  findAll (fun a => Native.rd8 Native.shortTables.klev a != 0) (2 ^ 24) []

@[expose] def shortPacked : List ℕ := foundCodes.map (actRows convInvRows)

@[expose] def isShortX (x : ℕ) : Bool :=
  Native.rd8 Native.shortTables.klev (actRows convRows x) != 0

theorem vecX_eq_mod (x : ℕ) : vecX x = phi0 (toC (x % 4096), toD (x / 4096 % 4096)) := by
  unfold vecX
  rw [toC_mod_4096, Nat.shiftRight_eq_div_pow, show (2 : ℕ) ^ 12 = 4096 by norm_num,
    toD_mod_4096]

theorem isShortX_iff
    {x : ℕ} (hx : x < 2 ^ 24) : isShortX x = true ↔ vecX x ∈ shortSet := by
  rw [vecX_eq_mod]
  have h1 := isShortCoord_toC_toD_iff hx
  have h2 : IsShortCoord (toC (x % 4096), toD (x / 4096 % 4096)) ↔
      phi0 (toC (x % 4096), toD (x / 4096 % 4096)) ∈ shortSet := Iff.rfl
  rw [← h2, h1]
  unfold isShortX
  exact bne_iff_ne

theorem mem_shortPacked {S : L2} (hS : S ∈ shortSet) :
    ∃ x ∈ shortPacked, x < 2 ^ 24 ∧ vecX x = S := by
  rw [shortSet_eq_image_shortFound] at hS
  obtain ⟨a, ha, rfl⟩ := hS
  have ha' : a ∈ shortFound Native.shortTables := ha
  simp only [shortFound, Finset.mem_filter, Finset.mem_range] at ha'
  have hmem : a ∈ foundCodes := by
    unfold foundCodes
    rw [mem_findAll]
    exact Or.inl ⟨ha'.1, by simpa using ha'.2⟩
  refine ⟨actRows convInvRows a, List.mem_map.2 ⟨a, hmem, rfl⟩, actRows_convInvRows_lt a, ?_⟩
  rw [vecX_eq_mod]
  exact phi0_convInvRows ha'.1

theorem vecX_injective_lt {x y : ℕ} (hx : x < 2 ^ 24) (hy : y < 2 ^ 24)
    (h : vecX x = vecX y) : x = y := by
  rw [vecX_eq_mod, vecX_eq_mod] at h
  have h1 := phi0_injective h
  simp only [Prod.mk.injEq] at h1
  have e1 : x % 4096 = y % 4096 :=
    toC_injective (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1.1
  have e2 : x / 4096 % 4096 = y / 4096 % 4096 :=
    toD_injective (Nat.mod_lt _ (by norm_num)) (Nat.mod_lt _ (by norm_num)) h1.2
  have hx' : x < 16777216 := by simpa using hx
  have hy' : y < 16777216 := by simpa using hy
  omega

@[expose] def reduceVec (piv : List (ℕ × ℕ)) (v u : ℕ) : ℕ × ℕ :=
  piv.foldl (fun vu mp => if vu.1 ^^^ mp.1 < vu.1 then (vu.1 ^^^ mp.1, vu.2 ^^^ mp.2) else vu)
    (v, u)

@[expose] def insertPiv (mp : ℕ × ℕ) : List (ℕ × ℕ) → List (ℕ × ℕ)
  | [] => [mp]
  | q :: qs => if q.1 < mp.1 then mp :: q :: qs else q :: insertPiv mp qs

@[expose] def elimGo (M : ℕ → ℕ) : ℕ → List (ℕ × ℕ) → List ℕ → List (ℕ × ℕ) × List ℕ
  | 0, piv, ker => (piv, ker)
  | k + 1, piv, ker =>
    let vu := reduceVec piv (M (2 ^ k)) (2 ^ k)
    if vu.1 == 0 then elimGo M k piv (vu.2 :: ker) else elimGo M k (insertPiv vu piv) ker

@[expose] def elim (tt td : Array Model.Pauli) : List (ℕ × ℕ) × List ℕ :=
  elimGo (MX tt td) 24 [] []

@[expose] def fixBasisX (tt td : Array Model.Pauli) : List ℕ := (elim tt td).2

@[expose] def solveX (piv : List (ℕ × ℕ)) (v : ℕ) : Option ℕ :=
  let r := reduceVec piv v 0
  if r.1 == 0 then some r.2 else none

@[expose] def checkX (sl : List ℕ) (tt td : Array Model.Pauli) (xw : ℕ) : Bool :=
  let e := elim tt td
  let fb := e.2
  let candS := sl.filter fun xS => fb.all fun f => !bX f (xS ^^^ xw)
  let candV := sl.filter fun xv => kapX tt td xv == xv
  fb.all (fun f => kapX tt td f == f) &&
    candV.all fun xv =>
      let su := solveX e.1 xv
      candS.all fun xS => bX xS xv || !isShortX (xS ^^^ xv) ||
        (match su with
          | none => false
          | some u => MX tt td u == xv && (bX (xS ^^^ xw) u != csX tt td xv))

theorem checkX_sound {sl : List ℕ} {tt td : Array Model.Pauli} {xw : ℕ}
    (h : checkX sl tt td xw = true) :
    (∀ f ∈ fixBasisX tt td, kapX tt td f = f) ∧
      ∀ xS ∈ sl, ∀ xv ∈ sl, kapX tt td xv = xv →
        (∀ f ∈ fixBasisX tt td, bX f (xS ^^^ xw) = false) → bX xS xv = false →
        isShortX (xS ^^^ xv) = true →
        ∃ u, MX tt td u = xv ∧ bX (xS ^^^ xw) u ≠ csX tt td xv := by
  unfold checkX at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_filter, Bool.not_eq_true',
    beq_iff_eq] at h
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun f hf => h1 f hf, fun xS hxS xv hxv hk hf hb hs => ?_⟩
  have h3 := h2 xv ⟨hxv, hk⟩ xS ⟨hxS, fun f hfb => by simpa using hf f hfb⟩
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h3
  rcases h3 with (h3 | h3) | h3
  · rw [hb] at h3
    exact absurd h3 (by simp)
  · rw [hs] at h3
    exact absurd h3 (by simp)
  · cases hsu : solveX (elim tt td).1 xv with
    | none => rw [hsu] at h3; exact absurd h3 (by simp)
    | some u =>
      rw [hsu] at h3
      simp only [Bool.and_eq_true, beq_iff_eq, bne_iff_ne, ne_eq] at h3
      exact ⟨u, h3.1, h3.2⟩

theorem kapX_lt (tt td : Array Model.Pauli) (x : ℕ) : kapX tt td x < 2 ^ 24 := by
  unfold kapX packP
  have h1 := Nat.mod_lt (actP tt td x).2.1 (show 0 < 4096 by norm_num)
  have h2 := Nat.mod_lt (actP tt td x).2.2 (show 0 < 4096 by norm_num)
  have : (2 : ℕ) ^ 24 = 16777216 := by norm_num
  omega

theorem exists_toC_toD (a : C) (δ : Cocode) : ∃ A < 4096, ∃ D < 4096, toC A = a ∧ toD D = δ := by
  obtain ⟨s, -, A, hA, D, hD, hq⟩ := exists_qP (spinEquiv (⟨0, a, δ⟩ : SpinCoord))
  refine ⟨A, by simpa using hA, D, by simpa using hD, ?_⟩
  have h := congrArg coordOf hq
  simp only [qP, coordOf_pauliQ, Griess.coordOf_spinEquiv] at h
  exact ⟨congrArg Prod.fst h, congrArg Prod.snd h⟩

theorem exists_packed (v : L2) : ∃ x < 2 ^ 24, vecX x = v := by
  obtain ⟨⟨a, δ⟩, hp⟩ := phi0_bijective.2 v
  obtain ⟨A, hA, D, hD, hAa, hDδ⟩ := exists_toC_toD a δ
  refine ⟨packP (false, A, D), ?_, ?_⟩
  · unfold packP
    have h1 := Nat.mod_lt A (show 0 < 4096 by norm_num)
    have h2 := Nat.mod_lt D (show 0 < 4096 by norm_num)
    have : (2 : ℕ) ^ 24 = 16777216 := by norm_num
    show A % 4096 + 4096 * (D % 4096) < 2 ^ 24
    omega
  · rw [vecX_packP]
    show phi0 (toC A, toD D) = v
    rw [hAa, hDδ]
    exact hp

noncomputable def packOf (v : L2) : ℕ := Classical.choose (exists_packed v)

theorem packOf_lt (v : L2) : packOf v < 2 ^ 24 := (Classical.choose_spec (exists_packed v)).1

theorem vecX_packOf (v : L2) : vecX (packOf v) = v := (Classical.choose_spec (exists_packed v)).2

theorem packOf_vecX {x : ℕ} (hx : x < 2 ^ 24) : packOf (vecX x) = x :=
  vecX_injective_lt (packOf_lt _) hx (vecX_packOf _)

theorem centralCoord_pauliQ (y : Model.Pauli) : centralCoord (pauliQ y) = boolZ y.1 :=
  Griess.centralCoord_spinEquiv _

theorem conj_pow_mul_aux {G : Type*} [Group G] (φ : G ≃* G) {z : G} (hz : φ z = z) {r : G}
    {s : ℕ} (hr : φ r = z ^ s * r) (e : ℕ) : φ (z ^ e * r) = z ^ s * (z ^ e * r) := by
  rw [map_mul, map_pow, hz, hr, ← mul_assoc, ← mul_assoc, (Commute.pow_pow_self z e s).eq]

theorem conjQ_of_fixed
    (i : ℕ) {q' : Q}
    (hfix : modTwoEnd (cosetPair i).1.2 (phi0 (coordOf q')) = phi0 (coordOf q')) :
    conjQ (cosetPair i) q' =
      zQ ^ (boolZ (csX (tT i) (tD i) (packOf (phi0 (coordOf q'))))).val * q' := by
  set x₀ := packOf (phi0 (coordOf q')) with hx₀
  have hv : vecX x₀ = phi0 (coordOf q') := vecX_packOf _
  have hc : coordOf (pauliQ (pauliOf x₀)) = coordOf q' :=
    phi0_injective ((phi0_coordOf_pauliOf x₀).trans hv)
  have hcc : centralCoord (pauliQ (pauliOf x₀)) = 0 := (centralCoord_pauliQ _).trans boolZ_false
  have hrep : pauliQ (pauliOf x₀) = Griess.rep (coordOf q') :=
    (Griess.eq_zQ_pow_mul_rep (pauliQ (pauliOf x₀))).trans (by
      simp only [hcc, hc, ZMod.val_zero, pow_zero, one_mul])
  have hq' : q' = zQ ^ (centralCoord q').val * pauliQ (pauliOf x₀) :=
    (Griess.eq_zQ_pow_mul_rep q').trans (congrArg (fun r : Q => zQ ^ (centralCoord q').val * r)
      hrep.symm)
  have hact := conjQ_pauliOf i x₀
  have hfix' : coordOf (pauliQ (actP (tT i) (tD i) x₀)) = coordOf q' := by
    apply phi0_injective
    rw [← hact, phi0_conjQ, phi0_coordOf_pauliOf, hv, hfix]
  have hrep' : pauliQ (actP (tT i) (tD i) x₀) =
      zQ ^ (boolZ (csX (tT i) (tD i) x₀)).val * pauliQ (pauliOf x₀) :=
    (Griess.eq_zQ_pow_mul_rep (pauliQ (actP (tT i) (tD i) x₀))).trans (by
      simp only [centralCoord_pauliQ, hfix', ← hrep]
      rfl)
  have hconj : conjQ (cosetPair i) (pauliQ (pauliOf x₀)) =
      zQ ^ (boolZ (csX (tT i) (tD i) x₀)).val * pauliQ (pauliOf x₀) := hact.trans hrep'
  calc conjQ (cosetPair i) q'
      = conjQ (cosetPair i) (zQ ^ (centralCoord q').val * pauliQ (pauliOf x₀)) :=
        congrArg (fun r : Q => conjQ (cosetPair i) r) hq'
    _ = zQ ^ (boolZ (csX (tT i) (tD i) x₀)).val *
          (zQ ^ (centralCoord q').val * pauliQ (pauliOf x₀)) :=
        conj_pow_mul_aux (conjQ (cosetPair i)) (conjQ_zQ (cosetPair i)) hconj _
    _ = zQ ^ (boolZ (csX (tT i) (tD i) x₀)).val * q' :=
        congrArg (fun r : Q => zQ ^ (boolZ (csX (tT i) (tD i) x₀)).val * r) hq'.symm

theorem coordOf_cosetW_phi0 (i : ℕ) : phi0 (coordOf (cosetW i)) = vecX (packP (wP i)) := by
  rw [← pauliQ_wP, coordOf_pauliQ, vecX_packP]

theorem checkSpec_of_checkX
    {i : ℕ}
    (h : checkX shortPacked (tT i) (tD i) (packP (wP i)) = true) : CheckSpec i := by
  obtain ⟨hfix, hmain⟩ := checkX_sound h
  refine ⟨(fixBasisX (tT i) (tD i)).map vecX,
    fun v => boolZ (csX (tT i) (tD i) (packOf v)), ?_, ?_, ?_⟩
  · intro f hf
    obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hf
    rw [modTwoEnd_vecX, hfix x hx]
  · intro q' hq'
    exact conjQ_of_fixed i hq'
  · intro S v hS hv hSv hκv hbSv hFb
    obtain ⟨xS, hxS, hxS24, rfl⟩ := mem_shortPacked hS
    obtain ⟨xv, hxv, hxv24, rfl⟩ := mem_shortPacked hv
    rw [coordOf_cosetW_phi0] at hFb ⊢
    have hxor24 : xS ^^^ xv < 2 ^ 24 := Nat.xor_lt_two_pow (n := 24) hxS24 hxv24
    have hk : kapX (tT i) (tD i) xv = xv := by
      refine vecX_injective_lt (kapX_lt _ _ _) hxv24 ?_
      rw [← modTwoEnd_vecX, hκv]
    have hb : bX xS xv = false := by
      rw [← boolZ_eq_zero_iff, ← bL_vecX]
      exact hbSv
    have hw24 : packP (wP i) < 2 ^ 24 := by
      unfold packP
      have h1 := Nat.mod_lt (wP i).2.1 (show 0 < 4096 by norm_num)
      have h2 := Nat.mod_lt (wP i).2.2 (show 0 < 4096 by norm_num)
      omega
    have hF : ∀ f ∈ fixBasisX (tT i) (tD i), bX f (xS ^^^ packP (wP i)) = false := by
      intro f hf
      have := hFb (vecX f) (List.mem_map.2 ⟨f, hf, rfl⟩)
      rw [← vecX_xor, bL_vecX, boolZ_eq_zero_iff] at this
      exact this
    have hs : isShortX (xS ^^^ xv) = true := by
      rw [isShortX_iff hxor24, vecX_xor]
      exact hSv
    obtain ⟨u, hu1, hu2⟩ := hmain xS hxS xv hxv hk hF hb hs
    refine ⟨vecX u, ?_, ?_⟩
    · rw [modTwoEnd_vecX, ← vecX_xor, ← hu1, MX, Nat.xor_comm]
    · show bL _ (vecX u) ≠ boolZ (csX (tT i) (tD i) (packOf (vecX xv)))
      rw [← vecX_xor, bL_vecX, packOf_vecX hxv24]
      intro heq
      exact hu2 (boolZ_injective heq)

end CFSG.Monster.Existence

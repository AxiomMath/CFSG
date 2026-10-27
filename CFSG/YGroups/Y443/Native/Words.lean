module

public import CFSG.YGroups.Y443.Native.Witness
public import Certificates.Data.CFSGNative.YGroups.Y443.MonsterWords

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.YGroups.Y443

open CFSG.Monster CFSG.Monster.AxisCount CFSG.Monster.Griess CFSG.Monster.Generated
  CFSG.YGroups.Y443Native

@[expose] def toGen (r : Array ℕ) : Native.Gen :=
  match r[0]! with
  | 0 => .rho (r[1]! != 0, r[2]!, r[3]!)
  | 1 => .perm perms[r[2]!]!
  | 2 => .xi
  | _ => .tau

@[expose] def L (k : ℕ) : List Native.Gen := (wordLetters k).map toGen

@[expose] noncomputable def M (k : ℕ) : SpaceB ≃ₗ[ℚ] SpaceB := wordLin (L k)

theorem M_mem (k : ℕ) : M k ∈ Gmat := wordLin_mem_Gmat _

@[expose] def ordI (k : ℕ) : ℕ := if k = 0 ∨ k = 4 ∨ k = 8 then 3 else 2

@[expose] def mI (k l : ℕ) : ℕ :=
  if (k, l) = (0, 1) ∨ (k, l) = (1, 2) ∨ (k, l) = (2, 3) ∨ (k, l) = (4, 5) ∨ (k, l) = (5, 6) ∨
    (k, l) = (6, 7) ∨ (k, l) = (8, 9) ∨ (k, l) = (9, 10) then 3 else 2

@[expose] def powL (k : ℕ) (w : List Native.Gen) : List Native.Gen := (List.replicate k w).flatten

theorem wordLin_powL (k : ℕ) (w : List Native.Gen) : wordLin (powL k w) = (wordLin w) ^ k := by
  induction k with
  | zero => rfl
  | succ k ih =>
    rw [powL, List.replicate_succ, List.flatten_cons, wordLin_append, ← powL, ih, pow_succ]

@[expose] def orderWord (k : ℕ) : List Native.Gen := powL (ordI k) (L k)

@[expose] def pairWord (k l : ℕ) : List Native.Gen :=
  powL (mI k l) (powL (ordI l - 1) (L l) ++ L k)

@[expose] def pairsOf (ks : List ℕ) : List (ℕ × ℕ) :=
  ks.flatMap fun k => ((List.range 11).filter fun l => k < l).map fun l => (k, l)

@[expose] def pairWords (ks : List ℕ) : List (List Native.Gen) :=
  (pairsOf ks).map fun kl => pairWord kl.1 kl.2

theorem mem_pairWords {ks : List ℕ} {k l : ℕ} (hk : k ∈ ks) (hkl : k < l) (hl : l < 11) :
    pairWord k l ∈ pairWords ks := by
  refine List.mem_map.2 ⟨(k, l), ?_, rfl⟩
  refine List.mem_flatMap.2 ⟨k, hk, ?_⟩
  exact List.mem_map.2 ⟨l, List.mem_filter.2 ⟨List.mem_range.2 hl, by simpa using hkl⟩, rfl⟩

@[expose] def invW (k : ℕ) : List Native.Gen := powL (ordI k - 1) (L k)

@[expose] def spiderFactors : List (List Native.Gen) :=
  [invW 0, L 1, L 4, invW 5, invW 8, L 9, L 0, invW 1, invW 4, L 5, L 8, invW 9]

@[expose] def spiderWord : List Native.Gen := powL 5 spiderFactors.reverse.flatten

theorem wordLin_flatten_reverse (ws : List (List Native.Gen)) :
    wordLin ws.reverse.flatten = (ws.map wordLin).prod := by
  induction ws with
  | nil => rfl
  | cons w ws ih =>
    rw [List.reverse_cons, List.flatten_append, List.flatten_cons, List.flatten_nil,
      List.append_nil, wordLin_append, ih, List.map_cons, List.prod_cons]

@[expose] def fixAll (ws : List (List Native.Gen)) (v : Native.DVec) : Bool :=
  Native.checkWords (ws.map fun w => (w, v, v))

theorem fixAll_sound
    {ws : List (List Native.Gen)} {v : Native.DVec} (h : fixAll ws v = true) :
    ∀ w ∈ ws, wordLin w (interp v) = interp v := by
  intro w hw
  exact checkWords_sound h (w, v, v) (List.mem_map.2 ⟨w, hw, rfl⟩)

theorem wordLin_eq_one
    {w : List Native.Gen}
    (ha : wordLin w (interp (aV ())) = interp (aV ()))
    (hb : wordLin w (interp (bV ())) = interp (bV ()))
    (hw : wordLin w (interp (wV ())) = interp (wV ())) : wordLin w = 1 :=
  separation_witnesses _ (wordLin_mem_Gmat w) ha hb hw

theorem wordLin_eq_one_of_fixAll
    {ws : List (List Native.Gen)}
    (ha : fixAll ws (aV ()) = true) (hb : fixAll ws (bV ()) = true)
    (hw : fixAll ws (wV ()) = true) : ∀ w ∈ ws, wordLin w = 1 := fun w hmem =>
  wordLin_eq_one (fixAll_sound ha w hmem) (fixAll_sound hb w hmem) (fixAll_sound hw w hmem)

theorem pairRel_of_fixAll
    {ks : List ℕ} (ha : fixAll (pairWords ks) (aV ()) = true)
    (hb : fixAll (pairWords ks) (bV ()) = true) (hw : fixAll (pairWords ks) (wV ()) = true)
    {k l : ℕ} (hk : k ∈ ks) (hkl : k < l) (hl : l < 11) :
    (M k * M l ^ (ordI l - 1)) ^ mI k l = 1 := by
  have h := wordLin_eq_one_of_fixAll ha hb hw (pairWord k l) (mem_pairWords hk hkl hl)
  rw [pairWord, wordLin_powL, wordLin_append, wordLin_powL] at h
  exact h

end CFSG.YGroups.Y443

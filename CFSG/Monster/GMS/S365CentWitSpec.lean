module

public import CFSG.Monster.GMS.S365CentPathSpec
public import CFSG.Monster.GMS.S365CentRootSpec
public import CFSG.Monster.GMS.S365CentDefs
public import Certificates.Data.CFSGNative.Co1.S365CentWit
public import CFSG.Monster.GMS.S365CentWitSpecInputs
public import Certificates.Certificate10040
public meta import CFSG.Sporadic.Co1.Module.PairsCheck
public meta import CFSG.Sporadic.Co1.Module.InvData
public meta import CFSG.Monster.GMS.S365CosetSpec
public meta import CFSG.Monster.GMS.S365Root
public meta import Certificates.Data.CFSGNative.Co1.S365CentRoot
public meta import Certificates.Data.CFSGNative.Co1.S365CentWit

public section

namespace CFSG.Monster.GMS

open CFSG.Blueprint.NativeSporadic

namespace S365

open scoped Matrix
open CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native CFSG.Sporadic.Co1.Module
  CFSG.Sporadic.Co1.Module.Pairs CFSG.Sporadic.Co1.S365Native CFSG.Sporadic.Co1.InvNative
  CFSG.Sporadic.Co1.S365CentNative

theorem witCheckRef_ok : witCheckRef = true :=
  Certificates.certificate10040.1

theorem lbl_three_iff
    {w : ℕ} (hw : w < 2 ^ 24) :
    tyLab (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 w = 3 ↔
      toVecD 24 w ∈ co1Orbit 0 := by
  rw [co1Orbit_zero, orbit_Co1_eq]
  exact tyLab_spec w hw 3 (by norm_num)

theorem pat0_iff
    {x : ℕ} (hx : x < 2 ^ 24) :
    pat0 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40 x = true ↔
      Pat0 (toVecD 24 2) (toVecD 24 4) (toVecD 24 40) (toVecD 24 x) := by
  unfold pat0 Pat0
  simp only [Bool.and_eq_true, beq_iff_eq, tyLabN_eq]
  have h2 : (2 : ℕ) < 2 ^ 24 := by norm_num
  have h4 : (4 : ℕ) < 2 ^ 24 := by norm_num
  have h40 : (40 : ℕ) < 2 ^ 24 := by norm_num
  have hx2 := Nat.xor_lt_two_pow hx h2
  have hx4 := Nat.xor_lt_two_pow hx h4
  have hx24 := Nat.xor_lt_two_pow hx2 h4
  have hy := Nat.xor_lt_two_pow hx h40
  have hy2 := Nat.xor_lt_two_pow hy h2
  have hy4 := Nat.xor_lt_two_pow hy h4
  have hy24 := Nat.xor_lt_two_pow hy2 h4
  rw [lbl_one_iff hx, lbl_three_iff hx2, lbl_three_iff hx4, lbl_three_iff hx24, lbl_one_iff hy,
    lbl_one_iff hy2, lbl_one_iff hy4, lbl_one_iff hy24]
  simp only [toVecD_xor]
  constructor
  · rintro ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩
    exact ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
  · rintro ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩
    exact ⟨⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩, h8⟩

theorem witness_ref :
    ∃ g₁ g₂ : Co1,
    (g₁ • toVecD 24 2 = toVecD 24 2 ∧ g₁ • toVecD 24 4 = toVecD 24 4 ∧
      g₁ • toVecD 24 40 = toVecD 24 40) ∧
    (g₂ • toVecD 24 2 = toVecD 24 2 ∧ g₂ • toVecD 24 4 = toVecD 24 4 ∧
      g₂ • toVecD 24 40 = toVecD 24 40) ∧
    ∀ ν, Pat0 (toVecD 24 2) (toVecD 24 4) (toVecD 24 40) ν → ν ≠ toVecD 24 1 →
      ∃ g ∈ ({g₁, g₂} : Set Co1), ν + g • ν ≠ 0 ∧
        ¬ Pat0 (toVecD 24 2) (toVecD 24 4) (toVecD 24 40) (ν + g • ν) := by
  obtain ⟨gl, hgl⟩ := exists_cosetElems
  have hc := witCheckRef_ok
  unfold witCheckRef witCheck at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨hA40, hB40⟩, hcnt⟩ := hc
  have h3 : cosetRowsT.size = 3 := by decide
  have hsA : ∀ l ∈ wordA, l < cosetRowsT.size := by rw [h3]; decide
  have hsB : ∀ l ∈ wordB, l < cosetRowsT.size := by rw [h3]; decide
  have hstab := cosetElems_fix hgl
  have hfix2 := pathElem_fix (fun l hl => (hstab l hl).1)
  have hfix4 := pathElem_fix (fun l hl => (hstab l hl).2)
  have hωA : pathElem gl wordA • toVecD 24 40 = toVecD 24 40 := by
    rw [pathElem_smul hgl _ hsA, hA40]
  have hωB : pathElem gl wordB • toVecD 24 40 = toVecD 24 40 := by
    rw [pathElem_smul hgl _ hsB, hB40]
  have key : ∀ (path : List ℕ), (∀ l ∈ path, l < cosetRowsT.size) → ∀ x : ℕ, x < 2 ^ 24 →
      (decide (x ^^^ applyPath cosetRowsT path x < 16777216) &&
        (x ^^^ applyPath cosetRowsT path x) != 0 &&
        !pat0 qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40
          (x ^^^ applyPath cosetRowsT path x)) = true →
      toVecD 24 x + pathElem gl path • toVecD 24 x ≠ 0 ∧
        ¬ Pat0 (toVecD 24 2) (toVecD 24 4) (toVecD 24 40)
          (toVecD 24 x + pathElem gl path • toVecD 24 x) := by
    intro path hpath x hx hk
    simp only [Bool.and_eq_true, decide_eq_true_eq, bne_iff_ne, ne_eq, Bool.not_eq_true'] at hk
    obtain ⟨⟨hlt, hne0⟩, hnp⟩ := hk
    have e : toVecD 24 x + pathElem gl path • toVecD 24 x =
        toVecD 24 (x ^^^ applyPath cosetRowsT path x) := by
      rw [pathElem_smul hgl path hpath, toVecD_xor]
    rw [e]
    refine ⟨fun h0 => hne0 ?_, fun hP => ?_⟩
    · exact toVecD_injective hlt (by norm_num) (h0.trans (toVecD_zero 24).symm)
    · have := (pat0_iff hlt).2 hP
      rw [this] at hnp
      exact absurd hnp (by decide)
  refine ⟨pathElem gl wordA, pathElem gl wordB,
    ⟨hfix2 _ hsA, hfix4 _ hsA, hωA⟩, ⟨hfix2 _ hsB, hfix4 _ hsB, hωB⟩, ?_⟩
  intro ν hν hne
  obtain ⟨x, hx, rfl⟩ : ν ∈ toVecD 24 '' Set.Iio (2 ^ 24) := by
    rw [toVecD_image_Iio]
    trivial
  have hx' : x < 2 ^ 24 := hx
  have hxne : x ≠ 1 := fun h => hne (by rw [h])
  have hp := (pat0_iff hx').2 hν
  have hz := (countBelow_eq_zero_iff _ _).1 hcnt x hx'
  have hx1 : (x != 1) = true := by simpa using hxne
  have hk : (killed qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40
      cosetRowsT wordA x || killed qRows (orbitOf 2 98280).pts
        (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40 cosetRowsT wordB x) = true := by
    by_contra hnot
    have hf : (killed qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40
        cosetRowsT wordA x || killed qRows (orbitOf 2 98280).pts
          (posTable 24 (orbitOf 2 98280).pts) 98280 2 4 40 cosetRowsT wordB x) = false := by
      simpa using hnot
    rw [hp, hf, hx1] at hz
    simp at hz
  rw [Bool.or_eq_true] at hk
  rcases hk with hkA | hkB
  · exact ⟨pathElem gl wordA, Set.mem_insert _ _, key wordA hsA x hx' hkA⟩
  · exact ⟨pathElem gl wordB, Set.mem_insert_of_mem _ rfl, key wordB hsB x hx' hkB⟩

theorem fix_conj {g₀ g : Co1} {u v : Fin 24 → ZMod 2} (hu : g₀ • u = v) (hg : g • u = u) :
    (g₀ * g * g₀⁻¹) • v = v := by
  rw [← hu, ← mul_smul, show g₀ * g * g₀⁻¹ * g₀ = g₀ * g by group, mul_smul, hg]

theorem co1WitnessS :
    Co1WitnessS := by
  intro a b ω hP
  obtain ⟨g₁, g₂, hg₁, hg₂, hmain⟩ := witness_ref
  obtain ⟨g₀, hg₀a, hg₀b, hg₀ω⟩ := co1FourTV _ _ _ a b ω refPattern hP
  have ha : g₀ • toVecD 24 2 = a := hg₀a
  have hb : g₀ • toVecD 24 4 = b := hg₀b
  have hω : g₀ • toVecD 24 40 = ω := hg₀ω
  refine ⟨g₀ • toVecD 24 1, g₀ * g₁ * g₀⁻¹, g₀ * g₂ * g₀⁻¹,
    ⟨fix_conj ha hg₁.1, fix_conj hb hg₁.2.1, fix_conj hω hg₁.2.2⟩,
    ⟨fix_conj ha hg₂.1, fix_conj hb hg₂.2.1, fix_conj hω hg₂.2.2⟩, ?_⟩
  intro ν hν hne
  have hPat : Pat0 (toVecD 24 2) (toVecD 24 4) (toVecD 24 40) (g₀⁻¹ • ν) := by
    refine (Pat0.map_iff g₀).1 ?_
    rw [ha, hb, hω, smul_inv_smul]
    exact hν
  have hne₀ : g₀⁻¹ • ν ≠ toVecD 24 1 := by
    intro h
    apply hne
    rw [← h, smul_inv_smul]
  obtain ⟨g, hgmem, hne0, hnP⟩ := hmain _ hPat hne₀
  have hsum : ∀ g' : Co1, ν + (g₀ * g' * g₀⁻¹) • ν = g₀ • (g₀⁻¹ • ν + g' • g₀⁻¹ • ν) := by
    intro g'
    rw [smul_add, smul_inv_smul, ← mul_smul, ← mul_smul]
  have hfin : ∀ g' : Co1, g' ∈ ({g₁, g₂} : Set Co1) → g = g' →
      ν + (g₀ * g' * g₀⁻¹) • ν ≠ 0 ∧ ¬ Pat0 a b ω (ν + (g₀ * g' * g₀⁻¹) • ν) := by
    intro g' _ hgg
    subst hgg
    refine ⟨?_, fun hP' => hnP ?_⟩
    · rw [hsum, Ne, smul_eq_zero_iff_eq]
      exact hne0
    · rw [hsum, ← ha, ← hb, ← hω] at hP'
      exact (Pat0.map_iff g₀).1 hP'
  rcases hgmem with rfl | hg2
  · exact ⟨g₀ * g * g₀⁻¹, Set.mem_insert _ _, hfin g (Set.mem_insert _ _) rfl⟩
  · have hg2' : g = g₂ := hg2
    subst hg2'
    exact ⟨g₀ * g * g₀⁻¹, Set.mem_insert_of_mem _ rfl,
      hfin g (Set.mem_insert_of_mem _ rfl) rfl⟩

theorem noPatRef_ok : noPatRef = true :=
  Certificates.certificate10040.2

theorem mem_collectLt (p : ℕ → Bool) (n : ℕ) (acc : List ℕ) (x : ℕ) :
    x ∈ collectLt p n acc ↔ x ∈ acc ∨ (x < n ∧ p x = true) := by
  induction n generalizing acc with
  | zero => simp [collectLt]
  | succ n ih =>
    rw [collectLt, ih]
    by_cases hp : p n = true
    · simp only [hp, ↓reduceIte, List.mem_cons]
      constructor
      · rintro ((h | h) | ⟨h1, h2⟩)
        · exact Or.inr ⟨by omega, by rw [h]; exact hp⟩
        · exact Or.inl h
        · exact Or.inr ⟨by omega, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl (Or.inr h)
        · rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
          · exact Or.inr ⟨h, h2⟩
          · exact Or.inl (Or.inl h)
    · simp only [hp, Bool.false_eq_true, ↓reduceIte]
      constructor
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · exact Or.inr ⟨by omega, h2⟩
      · rintro (h | ⟨h1, h2⟩)
        · exact Or.inl h
        · rcases Nat.lt_succ_iff_lt_or_eq.1 h1 with h | h
          · exact Or.inr ⟨h, h2⟩
          · subst h; exact absurd h2 hp

theorem noPat_spec
    {a b ω : Fin 24 → ZMod 2} (hP : FourPattern a b ω)
    (ha : ∀ c ∈ rootFix, bil₀ a (toVecD 24 c) = 0) (hb : ∀ c ∈ rootFix, bil₀ b (toVecD 24 c) = 0)
    (hω : ∀ c ∈ rootFix, bil₀ ω (toVecD 24 c) = 0) : False := by
  have hcheck := noPatRef_ok
  unfold noPatRef noPat at hcheck
  obtain ⟨xa, hxa, rfl⟩ : a ∈ toVecD 24 '' Set.Iio (2 ^ 24) := by
    rw [toVecD_image_Iio]
    trivial
  obtain ⟨xb, hxb, rfl⟩ : b ∈ toVecD 24 '' Set.Iio (2 ^ 24) := by
    rw [toVecD_image_Iio]
    trivial
  obtain ⟨xω, hxω, rfl⟩ : ω ∈ toVecD 24 '' Set.Iio (2 ^ 24) := by
    rw [toVecD_image_Iio]
    trivial
  have hxa' : xa < 2 ^ 24 := hxa
  have hxb' : xb < 2 ^ 24 := hxb
  have hxω' : xω < 2 ^ 24 := hxω
  have hmem : ∀ x : ℕ, x < 2 ^ 24 → (∀ c ∈ rootFix, bil₀ (toVecD 24 x) (toVecD 24 c) = 0) →
      x ∈ collectLt (orthAllN rootGs) 16777216 [] := by
    intro x hx h
    rw [mem_collectLt]
    exact Or.inr ⟨hx, orthAllN_iff.2 h⟩
  obtain ⟨h1, h2, h3, h4, h5, h6, h7⟩ := hP
  have hxab : xa ^^^ xb < 2 ^ 24 := Nat.xor_lt_two_pow hxa' hxb'
  have hxωa : xω ^^^ xa < 2 ^ 24 := Nat.xor_lt_two_pow hxω' hxa'
  have hxωb : xω ^^^ xb < 2 ^ 24 := Nat.xor_lt_two_pow hxω' hxb'
  have hxωab : xω ^^^ xa ^^^ xb < 2 ^ 24 := Nat.xor_lt_two_pow hxωa hxb'
  have l_a : tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 xa = 3 :=
    (lbl_three_iff hxa').2 h1
  have l_b : tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 xb = 3 :=
    (lbl_three_iff hxb').2 h2
  have l_ab : tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
      (xa ^^^ xb) = 3 := (lbl_three_iff hxab).2 (by rw [toVecD_xor]; exact h3)
  have l_ω : tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 xω = 1 :=
    (lbl_one_iff hxω').2 h4
  have l_ωa : tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
      (xω ^^^ xa) = 1 := (lbl_one_iff hxωa).2 (by rw [toVecD_xor]; exact h5)
  have l_ωb : tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
      (xω ^^^ xb) = 1 := (lbl_one_iff hxωb).2 (by rw [toVecD_xor]; exact h6)
  have l_ωab : tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
      (xω ^^^ xa ^^^ xb) = 1 :=
    (lbl_one_iff hxωab).2 (by rw [toVecD_xor, toVecD_xor]; exact h7)
  have h1' := List.all_eq_true.1 hcheck xa (hmem xa hxa' ha)
  simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h1'
  rcases h1' with h1' | h1'
  · exact h1' l_a
  · have h2' := List.all_eq_true.1 h1' xb (hmem xb hxb' hb)
    simp only [Bool.or_eq_true, bne_iff_ne, ne_eq] at h2'
    rcases h2' with (h2' | h2') | h2'
    · exact h2' l_b
    · exact h2' l_ab
    · have h3' := List.all_eq_true.1 h2' xω (hmem xω hxω' hω)
      have h4' : (tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280 xω
          == 1 && tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
          (xω ^^^ xa) == 1 && tyLabN qRows (orbitOf 2 98280).pts
          (posTable 24 (orbitOf 2 98280).pts) 98280 (xω ^^^ xb) == 1 &&
          tyLabN qRows (orbitOf 2 98280).pts (posTable 24 (orbitOf 2 98280).pts) 98280
          (xω ^^^ xa ^^^ xb) == 1) = true := by
        simp [l_ω, l_ωa, l_ωb, l_ωab]
      rw [h4'] at h3'
      exact absurd h3' (by decide)

theorem orth_of_inIm
    {sA : Co1} (hs : matHom sA = rowsMatrix 24 rowsSA) {u : Fin 24 → ZMod 2}
    (hu : ∃ v, u = v + co1Act sA v) : ∀ c ∈ rootFix, bil₀ u (toVecD 24 c) = 0 := by
  have hfix := rootFixOK_ok
  unfold rootFixOK at hfix
  obtain ⟨v, hv⟩ := hu
  intro c hc
  have hc' := List.all_eq_true.1 hfix c hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc'
  have hfv : sA • toVecD 24 c = toVecD 24 c := by
    rw [act_packed sA rowsSA hs c]
    exact congrArg (toVecD 24) (beq_iff_eq.1 hc'.2)
  rw [hv]
  exact bil₀_add_smul_fixed hfv v

theorem co1NoPatternIm :
    Co1NoPatternIm := by
  intro s hs a b ω hP ha hb hω
  obtain ⟨sA, hsA⟩ := exists_sA
  obtain ⟨hsA2, hsAf⟩ := sA_facts hsA
  have hrf : (co1Fix s).ncard = 2 ^ 16 := (co1InvolutionFacts.1 s hs.1).2 hs.2
  obtain ⟨c₀, hc₀⟩ := isConj_iff.1 (isConj_of_fix hs.1 hrf hsA2 hsAf)
  have hcs : sA * c₀ = c₀ * s := by
    rw [← hc₀]
    group
  have key : ∀ u, InIm s u → ∃ v, c₀ • u = v + co1Act sA v := by
    rintro u ⟨p, hp⟩
    refine ⟨c₀ • p, ?_⟩
    have hkey : c₀ • co1Act s p = co1Act sA (c₀ • p) := by
      show c₀ • (s • p) = sA • (c₀ • p)
      calc c₀ • (s • p) = (c₀ * s) • p := (mul_smul c₀ s p).symm
        _ = (sA * c₀) • p := congrArg (fun g : Co1 => g • p) hcs.symm
        _ = sA • (c₀ • p) := mul_smul sA c₀ p
    rw [hp, smul_add, hkey]
  exact noPat_spec (hP.map c₀) (orth_of_inIm hsA (key a ha)) (orth_of_inIm hsA (key b hb))
    (orth_of_inIm hsA (key ω hω))

end S365

end CFSG.Monster.GMS

module

public import CFSG.Quasithin.AppendixH.H16.OctadBetaMask

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.ASVolI.H16

open CFSG.ASVolI.ChH CFSG.Quasithin CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf
  CFSG.Quasithin.H.ModChk CFSG.Quasithin.H.Coc CFSG.Quasithin.H.FixSyl CFSG.Quasithin.H.LU24
  CFSG.Monster.Code CFSG.ASVolI.AppH CFSG.Quasithin.H156

@[expose] def isoTriples : List (ℕ × ℕ × ℕ) :=
  [(1, 4, 16), (1, 36, 24), (9, 6, 16), (9, 38, 24), (33, 4, 18), (33, 36, 26), (41, 6, 18),
    (41, 38, 26)]

@[expose] def isoCols (v₀ v₂ v₄ : ℕ) : List ℕ := [v₀, 2, v₂, 8, v₄, 32]

private theorem qMask6_le_one (y : ℕ) : qMask6 y ≤ 1 :=
  Bool.toNat_le _

private theorem qMask6_eq_of_cast {a b : ℕ} (ha : a ≤ 1) (hb : b ≤ 1)
    (h : (a : ZMod 2) = (b : ZMod 2)) : a = b := by
  have h2 := congrArg ZMod.val h
  rw [ZMod.val_natCast_of_lt (by omega : a < 2), ZMod.val_natCast_of_lt (by omega : b < 2)] at h2
  exact h2

private theorem list_length_six {α : Type*} {l : List α} (h : l.length = 6) :
    ∃ a b c d e f, l = [a, b, c, d, e, f] := by
  match l, h with
  | [], h => simp at h
  | [_], h => simp at h
  | [_, _], h => simp at h
  | [_, _, _], h => simp at h
  | [_, _, _, _], h => simp at h
  | [_, _, _, _, _], h => simp at h
  | [a, b, c, d, e, f], _ => exact ⟨a, b, c, d, e, f, rfl⟩
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => simp at h

private def isoPairs12 : List (ℕ × ℕ) :=
  [(1, 4), (1, 36), (9, 6), (9, 38), (33, 4), (33, 36), (41, 6), (41, 38)]

private theorem iso_stage1 : ∀ v₀ < 64,
    (∀ x ∈ [1, 3, 9, 33], qMask6 (actM (isoCols v₀ 0 0) x) = qMask6 x) →
    v₀ ∈ [1, 9, 33, 41] := by
  decide +kernel

private theorem iso_stage2 : ∀ v₀ : ℕ, v₀ ∈ [1, 9, 33, 41] →
    ∀ v₂ < 64, (∀ x ∈ [4, 6, 12, 36, 5], qMask6 (actM (isoCols v₀ v₂ 0) x) = qMask6 x) →
    (v₀, v₂) ∈ isoPairs12 := by
  intro v₀ hv₀
  simp only [List.mem_cons, List.mem_nil_iff, or_false] at hv₀
  rcases hv₀ with rfl | rfl | rfl | rfl <;> decide +kernel

private theorem iso_stage3 : ∀ p : ℕ × ℕ, p ∈ isoPairs12 →
    ∀ v₄ < 64,
      (∀ x ∈ [16, 18, 24, 48, 17, 20], qMask6 (actM (isoCols p.1 p.2 v₄) x) = qMask6 x) →
      (p.1, p.2, v₄) ∈ isoTriples := by
  intro p hp
  simp only [isoPairs12, List.mem_cons, List.mem_nil_iff, or_false] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> decide +kernel

theorem iso_enum : ∀ v₀ < 64,
    (∀ x ∈ [1, 3, 9, 33], qMask6 (actM (isoCols v₀ 0 0) x) = qMask6 x) →
    ∀ v₂ < 64, (∀ x ∈ [4, 6, 12, 36, 5], qMask6 (actM (isoCols v₀ v₂ 0) x) = qMask6 x) →
    ∀ v₄ < 64, (∀ x ∈ [16, 18, 24, 48, 17, 20], qMask6 (actM (isoCols v₀ v₂ v₄) x) = qMask6 x) →
      (v₀, v₂, v₄) ∈ isoTriples := by
  intro v₀ hv₀ h1 v₂ hv₂ h2 v₄ hv₄ h3
  exact iso_stage3 (v₀, v₂) (iso_stage2 v₀ (iso_stage1 v₀ hv₀ h1) v₂ hv₂ h2) v₄ hv₄ h3

private theorem lt64_mem1 : ∀ x ∈ [1, 3, 9, 33], x < 64 := by decide
private theorem lt64_mem2 : ∀ x ∈ [4, 6, 12, 36, 5], x < 64 := by decide
private theorem lt64_mem3 : ∀ x ∈ [16, 18, 24, 48, 17, 20], x < 64 := by decide

theorem iso_stages {v₀ v₂ v₄ : ℕ}
    (h : ∀ x < 64, qMask6 (actM (isoCols v₀ v₂ v₄) x) = qMask6 x) :
    (∀ x ∈ [1, 3, 9, 33], qMask6 (actM (isoCols v₀ 0 0) x) = qMask6 x) ∧
      (∀ x ∈ [4, 6, 12, 36, 5], qMask6 (actM (isoCols v₀ v₂ 0) x) = qMask6 x) ∧
      (∀ x ∈ [16, 18, 24, 48, 17, 20], qMask6 (actM (isoCols v₀ v₂ v₄) x) = qMask6 x) := by
  have key1 : ∀ x ∈ [1, 3, 9, 33], actM (isoCols v₀ 0 0) x = actM (isoCols v₀ v₂ v₄) x := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl <;> simp [isoCols, actM]
  have key2 : ∀ x ∈ [4, 6, 12, 36, 5], actM (isoCols v₀ v₂ 0) x = actM (isoCols v₀ v₂ v₄) x := by
    intro x hx
    simp only [List.mem_cons, List.mem_nil_iff, or_false] at hx
    rcases hx with rfl | rfl | rfl | rfl | rfl <;> simp [isoCols, actM]
  refine ⟨?_, ?_, ?_⟩
  · intro x hx; rw [key1 x hx]; exact h x (lt64_mem1 x hx)
  · intro x hx; rw [key2 x hx]; exact h x (lt64_mem2 x hx)
  · intro x hx; exact h x (lt64_mem3 x hx)

theorem exists_actsBy_cols {n : ℕ} (f : MulAut (Wn n)) :
    ∃ c : List ℕ, c.length = n ∧ (∀ a ∈ c, a < 2 ^ n) ∧ ActsBy f c := by
  let fm : ℕ → ℕ := fun m => CFSG.Quasithin.H.Parab.maskOf n (f (toW n m))
  have hlt : ∀ m, fm m < 2 ^ n :=
    fun m => (CFSG.Quasithin.H.Parab.maskOf_spec (f (toW n m))).1
  have hfm : ∀ m, f (toW n m) = toW n (fm m) :=
    fun m => (CFSG.Quasithin.H.Parab.maskOf_spec (f (toW n m))).2.symm
  have hXor : XorLin fm := by
    intro a b
    refine toW_inj (hlt _) (Nat.xor_lt_two_pow (hlt a) (hlt b)) ?_
    calc toW n (fm (a ^^^ b)) = f (toW n (a ^^^ b)) := (hfm (a ^^^ b)).symm
      _ = f (toW n a * toW n b) := by rw [toW_xor]
      _ = f (toW n a) * f (toW n b) := map_mul f _ _
      _ = toW n (fm a) * toW n (fm b) := by rw [hfm a, hfm b]
      _ = toW n (fm a ^^^ fm b) := (toW_xor n (fm a) (fm b)).symm
  refine ⟨matOf n fm, length_matOf n fm, ?_, actsBy_of_xorLin hXor hfm⟩
  intro a ha
  simp only [matOf, List.mem_map, List.mem_range] at ha
  obtain ⟨j, -, rfl⟩ := ha
  exact hlt _

private theorem actsBy_isoCols_of_mem {f : MulAut (Wn 6)}
    (hf : (∀ x : Fin 6 → ZMod 2, qPlus6 (Multiplicative.toAdd (f (Multiplicative.ofAdd x))) = qPlus6 x) ∧
      f (toW 6 2) = toW 6 2 ∧ f (toW 6 8) = toW 6 8 ∧ f (toW 6 32) = toW 6 32) :
    ActsBy f (isoCols (CFSG.Quasithin.H.Parab.maskOf 6 (f (toW 6 1)))
      (CFSG.Quasithin.H.Parab.maskOf 6 (f (toW 6 4)))
      (CFSG.Quasithin.H.Parab.maskOf 6 (f (toW 6 16)))) := by
  obtain ⟨c, hclen, hclt, hc⟩ := exists_actsBy_cols f
  obtain ⟨c₀, c₁, c₂, c₃, c₄, c₅, rfl⟩ := list_length_six hclen
  have h2 : actM [c₀, c₁, c₂, c₃, c₄, c₅] 2 = 2 :=
    toW_inj (actM_lt hclt 2) (by norm_num) ((hc 2).symm.trans hf.2.1)
  have h8 : actM [c₀, c₁, c₂, c₃, c₄, c₅] 8 = 8 :=
    toW_inj (actM_lt hclt 8) (by norm_num) ((hc 8).symm.trans hf.2.2.1)
  have h32 : actM [c₀, c₁, c₂, c₃, c₄, c₅] 32 = 32 :=
    toW_inj (actM_lt hclt 32) (by norm_num) ((hc 32).symm.trans hf.2.2.2)
  have hc1 : c₁ = 2 := by simpa [actM] using h2
  have hc3 : c₃ = 8 := by simpa [actM] using h8
  have hc5 : c₅ = 32 := by simpa [actM] using h32
  have hv0 : CFSG.Quasithin.H.Parab.maskOf 6 (f (toW 6 1)) = c₀ := by
    rw [hc 1, CFSG.Quasithin.H.Parab.maskOf_toW (actM_lt hclt 1)]
    simp [actM]
  have hv2 : CFSG.Quasithin.H.Parab.maskOf 6 (f (toW 6 4)) = c₂ := by
    rw [hc 4, CFSG.Quasithin.H.Parab.maskOf_toW (actM_lt hclt 4)]
    simp [actM]
  have hv4 : CFSG.Quasithin.H.Parab.maskOf 6 (f (toW 6 16)) = c₄ := by
    rw [hc 16, CFSG.Quasithin.H.Parab.maskOf_toW (actM_lt hclt 16)]
    simp [actM]
  have hceq : [c₀, c₁, c₂, c₃, c₄, c₅] =
      isoCols (CFSG.Quasithin.H.Parab.maskOf 6 (f (toW 6 1)))
        (CFSG.Quasithin.H.Parab.maskOf 6 (f (toW 6 4)))
        (CFSG.Quasithin.H.Parab.maskOf 6 (f (toW 6 16))) := by
    rw [hv0, hv2, hv4, hc1, hc3, hc5]
    rfl
  intro m
  rw [hc m, hceq]

theorem card_iso_fix_le :
    Nat.card {f : MulAut (Wn 6) //
      (∀ x : Fin 6 → ZMod 2, qPlus6 (Multiplicative.toAdd (f (Multiplicative.ofAdd x))) = qPlus6 x) ∧
        f (toW 6 2) = toW 6 2 ∧ f (toW 6 8) = toW 6 8 ∧ f (toW 6 32) = toW 6 32} ≤ 8 := by
  classical
  let P : MulAut (Wn 6) → Prop := fun f =>
    (∀ x : Fin 6 → ZMod 2, qPlus6 (Multiplicative.toAdd (f (Multiplicative.ofAdd x))) = qPlus6 x) ∧
      f (toW 6 2) = toW 6 2 ∧ f (toW 6 8) = toW 6 8 ∧ f (toW 6 32) = toW 6 32
  let F : {f : MulAut (Wn 6) // P f} → ℕ × ℕ × ℕ := fun f =>
    (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 1)),
     CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 4)),
     CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 16)))
  have hlt : ∀ (m : ℕ) (f : MulAut (Wn 6)),
      CFSG.Quasithin.H.Parab.maskOf 6 (f (toW 6 m)) < 64 :=
    fun m f => by simpa using (CFSG.Quasithin.H.Parab.maskOf_spec (f (toW 6 m))).1
  have hstage : ∀ f : {f : MulAut (Wn 6) // P f}, ∀ x < 64,
      qMask6 (actM (isoCols (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 1)))
        (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 4)))
        (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 16)))) x) = qMask6 x := by
    intro f x hx
    have hc := actsBy_isoCols_of_mem f.2
    have hsrc : qPlus6 (Multiplicative.toAdd (f.1 (toW 6 x))) = qPlus6 (bvec 6 x) := by
      simpa only [toW] using f.2.1 (bvec 6 x)
    have hcast : (qMask6 (actM (isoCols (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 1)))
        (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 4)))
        (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 16)))) x) : ZMod 2) = (qMask6 x : ZMod 2) := by
      have h2 : (qMask6 (actM (isoCols (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 1)))
          (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 4)))
          (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 16)))) x) : ZMod 2) = qPlus6 (bvec 6 x) := by
        rw [hc x, qPlus6_toW] at hsrc
        exact hsrc
      exact h2.trans (qPlus6_toW x)
    exact qMask6_eq_of_cast (qMask6_le_one _) (qMask6_le_one _) hcast
  have hmem : ∀ f : {f : MulAut (Wn 6) // P f}, F f ∈ isoTriples := by
    intro f
    obtain ⟨hs1, hs2, hs3⟩ := iso_stages (hstage f)
    change (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 1)),
      CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 4)),
      CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 16))) ∈ isoTriples
    exact iso_enum _ (hlt 1 f.1) hs1 _ (hlt 4 f.1) hs2 _ (hlt 16 f.1) hs3
  have hinj : Function.Injective F := by
    intro f g hfg
    have h₀ : CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 1)) =
        CFSG.Quasithin.H.Parab.maskOf 6 (g.1 (toW 6 1)) := by
      simpa only [F] using congrArg Prod.fst hfg
    have h₂ : CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 4)) =
        CFSG.Quasithin.H.Parab.maskOf 6 (g.1 (toW 6 4)) := by
      simpa only [F] using congrArg (fun t : ℕ × ℕ × ℕ => t.2.1) hfg
    have h₄ : CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 16)) =
        CFSG.Quasithin.H.Parab.maskOf 6 (g.1 (toW 6 16)) := by
      simpa only [F] using congrArg (fun t : ℕ × ℕ × ℕ => t.2.2) hfg
    apply Subtype.ext
    apply MulEquiv.ext
    intro w
    obtain ⟨m, -, rfl⟩ := toW_surj 6 w
    have hcf := actsBy_isoCols_of_mem f.2
    have hcg := actsBy_isoCols_of_mem g.2
    calc f.1 (toW 6 m) = toW 6 (actM (isoCols (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 1)))
          (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 4)))
          (CFSG.Quasithin.H.Parab.maskOf 6 (f.1 (toW 6 16)))) m) := hcf m
      _ = toW 6 (actM (isoCols (CFSG.Quasithin.H.Parab.maskOf 6 (g.1 (toW 6 1)))
          (CFSG.Quasithin.H.Parab.maskOf 6 (g.1 (toW 6 4)))
          (CFSG.Quasithin.H.Parab.maskOf 6 (g.1 (toW 6 16)))) m) := by rw [h₀, h₂, h₄]
      _ = g.1 (toW 6 m) := (hcg m).symm
  let T : Finset (ℕ × ℕ × ℕ) := isoTriples.toFinset
  haveI : Fintype ↥T := Finset.fintypeCoeSort T
  let G : {f : MulAut (Wn 6) // P f} → ↥T := fun f =>
    ⟨F f, by
      change F f ∈ isoTriples.toFinset
      rw [List.mem_toFinset]
      exact hmem f⟩
  have hGinj : Function.Injective G := by
    intro f g h
    exact hinj (congrArg Subtype.val h)
  have hle : Nat.card {f : MulAut (Wn 6) // P f} ≤ Nat.card ↥T :=
    Nat.card_le_card_of_injective G hGinj
  have hcard : Nat.card ↥T ≤ 8 := by
    rw [Nat.card_eq_fintype_card, Fintype.card_coe]
    calc T.card ≤ isoTriples.length := List.toFinset_card_le isoTriples
      _ = 8 := rfl
  exact hle.trans hcard

end CFSG.ASVolI.H16

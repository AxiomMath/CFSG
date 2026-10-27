module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporGenArr
public import Certificates.Data.Item434SporWords

public section

namespace CFSG.RankThree.PartTwo.Sec4.Item434SporGen

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.RankThree.Asc83Table
open scoped commutatorElement

variable {n : ℕ}

@[expose] def genAB (A B : Equiv.Perm (Fin n)) : ℕ → Equiv.Perm (Fin n) :=
  fun h => if h = 0 then A else B

theorem rep_wab {A B : Equiv.Perm (Fin n)} {ga gb : Array ℕ} (hA : Rep n ga A) (hB : Rep n gb B)
    (hiA : isInvA n ga (invCand n ga) = true) (hiB : isInvA n gb (invCand n gb) = true)
    {w : List ℤ} (hw : lettersOK 2 w = true) :
    Rep n (wab n ga gb w)
      (Quiver.SchreierGraph.evalWord (fun h : Fin 2 => genAB A B h) (toLetters 2 w)) := by
  refine rep_wordA (gs := genAB A B) (j := 2) ?_ ?_ w hw
  · intro h hh
    interval_cases h
    · simpa [genAB] using hA
    · simpa [genAB] using hB
  · intro h hh
    interval_cases h
    · simpa [genAB] using rep_inv_of_isInvA hA hiA
    · simpa [genAB] using rep_inv_of_isInvA hB hiB

theorem evalWord_genAB_mem (A B : Equiv.Perm (Fin n)) (w : List (Fin 2 × Bool)) :
    Quiver.SchreierGraph.evalWord (fun h : Fin 2 => genAB A B h) w ∈
      Subgroup.closure ({A, B} : Set (Equiv.Perm (Fin n))) := by
  refine Subgroup.closure_mono ?_ (Quiver.SchreierGraph.evalWord_mem_closure _ w)
  rintro _ ⟨h, rfl⟩
  fin_cases h <;> simp [genAB]

theorem exists_rep_wab {A B : Equiv.Perm (Fin n)} {ga gb : Array ℕ} (hA : Rep n ga A)
    (hB : Rep n gb B) (hiA : isInvA n ga (invCand n ga) = true)
    (hiB : isInvA n gb (invCand n gb) = true) {X : Subgroup (Equiv.Perm (Fin n))}
    (hX : X = Subgroup.closure {A, B}) {w : List ℤ} (hw : lettersOK 2 w = true) :
    ∃ g : X, Rep n (wab n ga gb w) (g : Equiv.Perm (Fin n)) :=
  ⟨⟨_, hX ▸ evalWord_genAB_mem A B _⟩, rep_wab hA hB hiA hiB hw⟩

theorem fixGen_of_fixWordsCheck {A B : Equiv.Perm (Fin n)} {ga gb : Array ℕ} (hA : Rep n ga A)
    (hB : Rep n gb B) {X : Subgroup (Equiv.Perm (Fin n))} (hX : X = Subgroup.closure {A, B})
    {sw : List (List ℤ)} {ords : List ℕ} {ps : List (ℕ × ℕ)} {e₁ e₂ : Array ℕ} {wa wb : List ℤ}
    {g₁ g₂ : X} (h₁ : Rep n e₁ (g₁ : Equiv.Perm (Fin n)))
    (h₂ : Rep n e₂ (g₂ : Equiv.Perm (Fin n)))
    (h : fixWordsCheck n ga gb sw ords ps e₁ e₂ wa wb = true) :
    Nat.card (Subgroup.closure ({g₁, g₂} : Set X)) = 9 ∧
      FixGen (Subgroup.closure ({g₁, g₂} : Set X)) := by
  simp only [fixWordsCheck, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hiA, hiB⟩, hsw⟩, hinv⟩, hwa⟩, hwb⟩, hgA⟩, hgB⟩, he9⟩, hsig⟩ := h
  set Sg := wabs n ga gb sw with hSg
  set Si := Sg.map (invCand n) with hSi
  have hsz : Sg.size = sw.length := by simp [hSg, wabs]
  have hrep : ∀ i < Sg.size, Rep n Sg[i]! (permOfArr n Sg[i]!) ∧
      Rep n Si[i]! (permOfArr n Sg[i]!)⁻¹ := fun i hi => rep_permOfArr (allLt_spec hinv hi)
  have hmem : ∀ i < Sg.size, permOfArr n Sg[i]! ∈ X := by
    intro i hi
    have hi' : i < sw.length := hsz ▸ hi
    have hget : Sg[i]! = wab n ga gb sw[i] := by
      simp [hSg, wabs, getElem!_pos, hi']
    have hsi : lettersOK 2 sw[i] = true := by
      simp only [wordsOK, List.all_eq_true] at hsw
      exact hsw _ (List.getElem_mem hi')
    obtain ⟨g, hg⟩ := exists_rep_wab hA hB hiA hiB hX hsi
    have : permOfArr n Sg[i]! = (g : Equiv.Perm (Fin n)) :=
      (hrep i hi).1.unique (hget ▸ hg)
    exact this ▸ g.2
  have hσX : Subgroup.closure
      (Set.range fun i : Fin Sg.size => permOfArr n Sg[(i : ℕ)]!) = X := by
    apply le_antisymm
    · rw [Subgroup.closure_le]
      rintro _ ⟨i, rfl⟩
      exact hmem i i.2
    · have key : ∀ {t : Array ℕ} {C : Equiv.Perm (Fin n)}, Rep n t C → ∀ {w : List ℤ},
          lettersOK Sg.size w = true → eqA n t (wordA n Sg Si w) = true →
          C ∈ Subgroup.closure (Set.range fun i : Fin Sg.size => permOfArr n Sg[(i : ℕ)]!) := by
        intro t C ht w hw he
        have hw' := rep_wordA (gs := fun i => permOfArr n Sg[i]!) (S := Sg) (Sinv := Si)
          (j := Sg.size) (fun i hi => (hrep i hi).1) (fun i hi => (hrep i hi).2) w hw
        rw [eq_of_eqA ht hw' he]
        exact Quiver.SchreierGraph.evalWord_mem_closure _ _
      rw [hX, Subgroup.closure_le]
      rintro _ (rfl | rfl)
      · exact key hA hwa hgA
      · exact key hB hwb hgB
  have hσ : ∀ i : Fin Sg.size, Rep n Sg[(i : ℕ)]! (permOfArr n Sg[(i : ℕ)]!) :=
    fun i => (hrep i i.2).1
  exact ⟨card_closure_of_e9Check h₁ h₂ he9, fixGen_of_sigCheck hσX hσ h₁ h₂ hsig⟩

section Ex27

variable {A B : Equiv.Perm (Fin n)} {ga gb : Array ℕ} {X : Subgroup (Equiv.Perm (Fin n))}

theorem rep_cmA {x y : Equiv.Perm (Fin n)} {xa ya : Array ℕ} (hx : Rep n xa x) (hy : Rep n ya y)
    (hix : isInvA n xa (invCand n xa) = true) (hiy : isInvA n ya (invCand n ya) = true) :
    Rep n (cmA n xa ya) ⁅x, y⁆ := by
  have h := rep_compA (rep_compA hx hy)
    (rep_compA (rep_inv_of_isInvA hx hix) (rep_inv_of_isInvA hy hiy))
  rw [commutatorElement_def, show x * y * x⁻¹ * y⁻¹ = x * y * (x⁻¹ * y⁻¹) by group]
  exact h

theorem rep_ex27E2 {x y : Equiv.Perm (Fin n)} {xa ya : Array ℕ} (hx : Rep n xa x)
    (hy : Rep n ya y) (i : Fin 4) : Rep n (ex27E2 n xa ya i) (ex27Rep x y i) := by
  fin_cases i
  · simpa [ex27E2, ex27Rep] using hx
  · simpa [ex27E2, ex27Rep] using hy
  · simpa [ex27E2, ex27Rep] using rep_compA hx hy
  · simpa [ex27E2, ex27Rep] using rep_compA hx (rep_powN hy 2)

theorem heis_of_heisCheck {x y : Equiv.Perm (Fin n)} {xa ya : Array ℕ} (hx : Rep n xa x)
    (hy : Rep n ya y) (h : heisCheck n xa ya = true) :
    Rep n (cmA n xa ya) ⁅x, y⁆ ∧ x ^ 3 = 1 ∧ y ^ 3 = 1 ∧ Commute ⁅x, y⁆ x ∧ Commute ⁅x, y⁆ y ∧
      ⁅x, y⁆ ≠ 1 := by
  simp only [heisCheck, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨⟨⟨⟨hix, hiy⟩, h3x⟩, h3y⟩, hcx⟩, hcy⟩, hne⟩ := h
  have hz := rep_cmA hx hy hix hiy
  refine ⟨hz, eq_of_eqA (rep_powN hx 3) rep_idA h3x, eq_of_eqA (rep_powN hy 3) rep_idA h3y,
    (mul_comm_of_commN hz hx hcx), (mul_comm_of_commN hz hy hcy), fun h1 => ?_⟩
  have := (eqA_iff hz rep_idA).2 h1
  rw [this] at hne
  exact Bool.noConfusion hne

end Ex27

theorem kill9_of_ex27 {Y : Type*} [Group Y] [Finite Y] {x y : Y} (hx : x ^ 3 = 1)
    (hy : y ^ 3 = 1) (hzx : Commute ⁅x, y⁆ x) (hzy : Commute ⁅x, y⁆ y) (hz1 : ⁅x, y⁆ ≠ 1)
    (hL : (Nat.card Y).factorization 3 = 3)
    (hF : ∀ i : Fin 4, FixGen (Subgroup.closure ({⁅x, y⁆, ex27Rep x y i} : Set Y)))
    (P : Subgroup Y) (hP9 : Nat.card P = 9) : FixGen P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  have hcard := ex27_card hx hy hzx hzy hz1
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card
    (ex27_card_sylow hx hy hzx hzy hz1 hL) hPp
  set Pm := P.map (MulAut.conj g⁻¹).toMonoidHom with hPm
  have hle : Pm ≤ Subgroup.closure ({x, y} : Set Y) := Item434AltPerm.map_conj_inv_le hg
  have h9 : Nat.card Pm = 9 := by
    rw [hPm, Subgroup.card_map_of_injective (MulAut.conj g⁻¹).injective, hP9]
  have hP : P = Pm.map (MulAut.conj g).toMonoidHom := by
    rw [hPm, Item434AltPerm.map_conj_map_conj_inv]
  rw [hP]
  refine FixGen.map_conj ?_ g
  rcases eq_of_le_of_card_eq_nine hx hy hzx hzy hcard hle h9 with h | h | h | h
  · rw [h]; exact hF 0
  · rw [h]; exact hF 1
  · rw [h]; exact hF 2
  · rw [h]; exact hF 3

theorem fixGen_of_ex27Check {A B : Equiv.Perm (Fin n)} {ga gb : Array ℕ} (hA : Rep n ga A)
    (hB : Rep n gb B) {X : Subgroup (Equiv.Perm (Fin n))} (hX : X = Subgroup.closure {A, B})
    [Finite X] (hL : (Nat.card X).factorization 3 = 3) {xw yw : List ℤ}
    {c₀ c₁ c₂ c₃ : FixData} (h : ex27Check n ga gb xw yw c₀ c₁ c₂ c₃ = true) (P : Subgroup X)
    (hP9 : Nat.card P = 9) : FixGen P := by
  simp only [ex27Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨hiA, hiB⟩, hxw⟩, hyw⟩, hheis⟩, h0⟩, h1⟩, h2⟩, h3⟩ := h
  obtain ⟨x, hx⟩ := exists_rep_wab hA hB hiA hiB hX hxw
  obtain ⟨y, hy⟩ := exists_rep_wab hA hB hiA hiB hX hyw
  obtain ⟨hz, hx3, hy3, hzx, hzy, hz1⟩ := heis_of_heisCheck hx hy hheis
  have hx3' : x ^ 3 = 1 := Subtype.ext hx3
  have hy3' : y ^ 3 = 1 := Subtype.ext hy3
  have hzx' : Commute ⁅x, y⁆ x := Subtype.ext hzx.eq
  have hzy' : Commute ⁅x, y⁆ y := Subtype.ext hzy.eq
  have hz1' : ⁅x, y⁆ ≠ 1 := fun h1 => hz1 (congrArg Subtype.val h1)
  have hrep : ∀ i : Fin 4, Rep n (ex27E2 n (wab n ga gb xw) (wab n ga gb yw) i)
      ((ex27Rep x y i : X) : Equiv.Perm (Fin n)) := by
    intro i
    fin_cases i
    · exact rep_ex27E2 hx hy 0
    · exact rep_ex27E2 hx hy 1
    · exact rep_ex27E2 hx hy 2
    · exact rep_ex27E2 hx hy 3
  refine kill9_of_ex27 hx3' hy3' hzx' hzy' hz1' hL (fun i => ?_) P hP9
  fin_cases i
  · exact (fixGen_of_fixWordsCheck hA hB hX (g₁ := ⁅x, y⁆) (g₂ := ex27Rep x y 0) hz (hrep 0)
      h0).2
  · exact (fixGen_of_fixWordsCheck hA hB hX (g₁ := ⁅x, y⁆) (g₂ := ex27Rep x y 1) hz (hrep 1)
      h1).2
  · exact (fixGen_of_fixWordsCheck hA hB hX (g₁ := ⁅x, y⁆) (g₂ := ex27Rep x y 2) hz (hrep 2)
      h2).2
  · exact (fixGen_of_fixWordsCheck hA hB hX (g₁ := ⁅x, y⁆) (g₂ := ex27Rep x y 3) hz (hrep 3)
      h3).2

theorem fixGen_of_sylow9Check {A B : Equiv.Perm (Fin n)} {ga gb : Array ℕ} (hA : Rep n ga A)
    (hB : Rep n gb B) {X : Subgroup (Equiv.Perm (Fin n))} (hX : X = Subgroup.closure {A, B})
    [Finite X] (hL : (Nat.card X).factorization 3 = 2) {e1w e2w : List ℤ} {c : FixData}
    (h : sylow9Check n ga gb e1w e2w c = true) (P : Subgroup X) (hP9 : Nat.card P = 9) :
    FixGen P := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  simp only [sylow9Check, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hiA, hiB⟩, h1⟩, h2⟩, hc⟩ := h
  obtain ⟨g₁, hg₁⟩ := exists_rep_wab hA hB hiA hiB hX h1
  obtain ⟨g₂, hg₂⟩ := exists_rep_wab hA hB hiA hiB hX h2
  obtain ⟨hcard, hF⟩ := fixGen_of_fixWordsCheck hA hB hX hg₁ hg₂ hc
  have hE : Nat.card (Subgroup.closure ({g₁, g₂} : Set X)) =
      3 ^ (Nat.card X).factorization 3 := by
    rw [hcard, hL]
    norm_num
  have hPp : IsPGroup 3 P := IsPGroup.of_card (n := 2) (by rw [hP9]; norm_num)
  obtain ⟨g, hg⟩ := Item434AltPerm.exists_le_map_conj_of_card hE hPp
  have hcard' : Nat.card ((Subgroup.closure ({g₁, g₂} : Set X)).map
      (MulAut.conj g).toMonoidHom) ≤ Nat.card P := by
    rw [Subgroup.card_map_of_injective (MulAut.conj g).injective, hcard, hP9]
  rw [Subgroup.eq_of_le_of_card_ge hg hcard']
  exact hF.map_conj g

end CFSG.RankThree.PartTwo.Sec4.Item434SporGen

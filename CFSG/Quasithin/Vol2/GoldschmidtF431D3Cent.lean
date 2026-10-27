module

public import CFSG.Quasithin.Vol2.GoldschmidtF431D3Base
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4AutLn
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4LocMain
public import Certificates.Certificate4240

public section

namespace CFSG.Quasithin.D4Hex

open CFSG.LargeExtraspecial.S63 CFSG.Quasithin CFSG.D4Hex CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native

section Z

theorem mem_d4H_iff_comm (x : D) : x ∈ d4H ↔ x * d4z = d4z * x :=
  Subgroup.mem_centralizer_singleton_iff


theorem mem_autStab_H_of_fix {α : MulAut D} (h : α d4z = d4z) : α ∈ autStab d4H := by
  show ∀ x, x ∈ d4H ↔ α x ∈ d4H
  intro x
  rw [mem_d4H_iff_comm, mem_d4H_iff_comm]
  constructor
  · intro hx
    have h1 := congrArg α hx
    rw [map_mul, map_mul, h] at h1
    exact h1
  · intro hx
    apply α.injective
    rw [map_mul, map_mul, h]
    exact hx


theorem fix_of_mem_autStab_H (hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z)
    {α : MulAut D} (h : α ∈ autStab d4H) : α d4z = d4z := by
  have hy : α d4z ∈ d4H := (h d4z).1 d4z_mem_d4H
  have hcomm : ∀ x ∈ d4H, x * α d4z = α d4z * x := by
    intro x hx
    have hx' : α⁻¹ x ∈ d4H := (h (α⁻¹ x)).2 (by rw [MulAut.apply_inv_self]; exact hx)
    have h1 := congrArg α ((mem_d4H_iff_comm _).1 hx')
    rw [map_mul, map_mul, MulAut.apply_inv_self] at h1
    exact h1
  rcases hCU (α d4z) (fun u hu => (hcomm u (d4U_le_d4H hu)).symm) with h1 | h1
  · exfalso
    apply d4z_sq.2
    have h2 : α d4z = α 1 := by rw [h1, map_one]
    exact α.injective h2
  · exact h1

theorem mem_autStab_H_iff_cu (hCU : ∀ x : D, (∀ u ∈ d4U, x * u = u * x) → x = 1 ∨ x = d4z)
    {α : MulAut D} : α ∈ autStab d4H ↔ α d4z = d4z :=
  ⟨fix_of_mem_autStab_H hCU, mem_autStab_H_of_fix⟩

end Z

section Lines


theorem lineAct_zero_of_mem_d4N {x : D} (hx : x ∈ d4N) : x • (0 : Fin 2457) = 0 := by
  apply lineSet_injective
  rw [lineSet_smul, lineSet_zero]
  exact (mem_d4N_iff_image x).1 hx

theorem lineMoved_parts : ∀ l < 2457, l = 0 ∨
    ∃ k < cWords.length, stabsLine (locWordArr (cWords.getD k [])) l = false := by
  have h := Certificates.certificate4240
  simp only [autCheck, Bool.and_eq_true] at h
  have h1 := h.1
  unfold lineMoved at h1
  intro l hl
  have h2 := allLt_spec h1 hl
  simp only [Bool.or_eq_true, beq_iff_eq, List.any_eq_true, List.mem_range,
    Bool.not_eq_true'] at h2
  exact h2

theorem autQ_parts : (∀ k ∈ autQWord, k < 8) ∧ (locWordArr autQWord)[0]! = 0 ∧
    ∀ i < locET.El.size,
      memR locET.El locET.idx
        (conjI (wordR d4Gens autQWord.reverse) (wordR d4Gens autQWord) locET.El[i]!) = false ∨
      memR locEQ.El locEQ.idx locET.El[i]! = true := by
  have h := Certificates.certificate4240
  simp only [autCheck, Bool.and_eq_true] at h
  have h2 := h.2
  unfold autQCheck at h2
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq, beq_iff_eq] at h2
  obtain ⟨⟨h1, h3⟩, h4⟩ := h2
  refine ⟨h1, h3, fun i hi => ?_⟩
  have h5 := allLt_spec h4 hi
  simp only [Bool.or_eq_true, Bool.not_eq_true'] at h5
  exact h5

theorem eq_zero_of_fix_gens (l : Fin 2457) (h : ∀ k < cGens.size, cGH k • l = l) : l = 0 := by
  by_contra hl0
  have hl0' : l.1 ≠ 0 := fun e => hl0 (Fin.ext e)
  obtain ⟨k, hk, hmov⟩ := (lineMoved_parts l.1 l.2).resolve_left hl0'
  have hk4 : k < cGens.size := by
    rw [cGens_size]
    simpa [cWords] using hk
  have hfix := h k hk4
  have hwlt : ∀ j ∈ cWords.getD k [], j < 8 := by
    have hmem := cWords_mem (show k < 4 by simpa [cWords] using hk)
    revert hmem
    generalize cWords.getD k [] = w
    intro hmem
    have : ∀ w ∈ cWords, ∀ j ∈ w, j < 8 := by decide
    exact this w hmem
  have hrep := rep_d4WordArr (cWords.getD k []) hwlt
  have hset : lineSet l = (lineSet l).image (act (cGH k)) := by
    have := lineSet_smul (cGH k) l
    rwa [hfix] at this
  have hpt : ∀ p : Fin 819, p ∈ lineSet l →
      ∃ q : ℕ, q = (d4WordArr (cWords.getD k []))[p.1]! ∧
        (q = lnPt l 0 ∨ q = lnPt l 1 ∨ q = lnPt l 2) := by
    intro p hp
    refine ⟨_, rfl, ?_⟩
    rw [hrep p]
    have hmem : act (cGH k) p ∈ lineSet l := by
      rw [hset]
      exact Finset.mem_image_of_mem _ hp
    exact (mem_lineSet_iff _ _).1 hmem
  obtain ⟨q0, rfl, h0⟩ := hpt (lpt0 l) (by simp [lineSet])
  obtain ⟨q1, rfl, h1⟩ := hpt (lpt1 l) (by simp [lineSet])
  obtain ⟨q2, rfl, h2⟩ := hpt (lpt2 l) (by simp [lineSet])
  have hall : stabsLine (locWordArr (cWords.getD k [])) l = true := by
    show (onLine l ((d4WordArr (cWords.getD k []))[lnPt l 0]!) &&
      onLine l ((d4WordArr (cWords.getD k []))[lnPt l 1]!) &&
      onLine l ((d4WordArr (cWords.getD k []))[lnPt l 2]!)) = true
    simp only [onLine, Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, or_assoc]
    exact ⟨⟨h0, h1⟩, h2⟩
  rw [hall] at hmov
  exact absurd hmov (by simp)

theorem eq_zero_of_fix_d4Ct (l : Fin 2457) (h : ∀ g ∈ d4Ct, g • l = l) : l = 0 :=
  eq_zero_of_fix_gens l fun _ hk => h _ (gen_mem_Ct hk)

theorem autLn_zero_of_fix_t {α : MulAut D} (h : α d4t = d4t) : autLn α 0 = 0 := by
  apply eq_zero_of_fix_d4Ct
  intro g hg
  have hgc : g * d4t = d4t * g := Subgroup.mem_centralizer_singleton_iff.1 (d4Ct_le_centralizer hg)
  have hg' : α⁻¹ g ∈ d4Ct := by
    rw [← centralizer_d4t_eq, Subgroup.mem_centralizer_singleton_iff]
    apply α.injective
    rw [map_mul, map_mul, MulAut.apply_inv_self, h]
    exact hgc
  have e : (MulAut.conj g : MulAut D) * α = α * MulAut.conj (α⁻¹ g) := by
    calc (MulAut.conj g : MulAut D) * α
        = (α * MulAut.conj (α⁻¹ g) * α⁻¹) * α := by
          rw [aut_mul_conj_inv, MulAut.apply_inv_self]
      _ = α * MulAut.conj (α⁻¹ g) := by group
  show lineAct g (autLn α 0) = autLn α 0
  rw [← autLn_conj, ← Equiv.Perm.mul_apply, ← map_mul, e, map_mul, Equiv.Perm.mul_apply,
    autLn_conj]
  exact congrArg (autLn α) (lineAct_zero_of_mem_d4N (d4Ct_le_d4N hg'))

theorem image_line0_autPt {α : MulAut D} (h : α d4t = d4t) : line0.image (autPt α) = line0 := by
  have h1 := lineSet_autLn α 0
  rw [autLn_zero_of_fix_t h, lineSet_zero] at h1
  exact h1.symm

end Lines

theorem image_conj_perm_eq {X : Type*} [DecidableEq X] (S : Finset X) (σ π : Equiv.Perm X)
    (hσ : S.image σ = S) : S.image (σ * π * σ⁻¹) = S ↔ S.image π = S := by
  have h1 : S.image (σ⁻¹ : Equiv.Perm X) = S := by
    calc S.image (σ⁻¹ : Equiv.Perm X) = (S.image σ).image (σ⁻¹ : Equiv.Perm X) := by rw [hσ]
      _ = S.image ((σ⁻¹ : Equiv.Perm X) ∘ σ) := Finset.image_image
      _ = S := by
        have : ((σ⁻¹ : Equiv.Perm X) ∘ σ) = id := funext fun x => by simp
        rw [this, Finset.image_id]
  have h2 : S.image (σ * π * σ⁻¹) = (S.image π).image σ := by
    rw [Equiv.Perm.coe_mul, Equiv.Perm.coe_mul, ← Finset.image_image, ← Finset.image_image, h1]
  rw [h2]
  constructor
  · intro h
    apply Finset.image_injective σ.injective
    rw [h, hσ]
  · intro h
    rw [h, hσ]

section N


theorem mem_autStab_N_of_fix_t {α : MulAut D} (h : α d4t = d4t) : α ∈ autStab d4N := by
  show ∀ x, x ∈ d4N ↔ α x ∈ d4N
  intro x
  have hσ := image_line0_autPt h
  have hconj : act (α x) = autPt α * act x * (autPt α)⁻¹ := by
    rw [← autPt_conj, ← aut_mul_conj_inv, map_mul, map_mul, map_inv, autPt_conj]
  rw [mem_d4N_iff_image, mem_d4N_iff_image, hconj]
  exact (image_conj_perm_eq line0 (autPt α) (act x) hσ).symm

theorem autPt_mem_line0 {α : MulAut D} (h : α d4t = d4t) {p : Fin 819} (hp : p ∈ line0) :
    autPt α p ∈ line0 := by
  have h1 : autPt α p ∈ line0.image (autPt α) := Finset.mem_image_of_mem _ hp
  rwa [image_line0_autPt h] at h1

end N

end CFSG.Quasithin.D4Hex

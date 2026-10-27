module

public import CFSG.LargeExtraspecial.S63CD4Model
public import CFSG.Quasithin.Background.Harris.R1.D4Q2Check

public section

namespace CFSG.Quasithin.Background.Harris.R1.D4Vert

open CFSG.LargeExtraspecial.S63 CFSG.Sporadic.SmallF2 CFSG.Sporadic.SmallF2.Native
  CFSG.Monster.B.Co2.Native CFSG.Quasithin
open CFSG.Monster.B.Co2 (allLt_spec)

@[expose] def Gd (A : Array ℕ) (g : trialityGroup8) : Prop := RepE d4E A g ∧ validR A = true

theorem Gd.mul {A B : Array ℕ} {g h : trialityGroup8} (hA : Gd A g) (hB : Gd B h) :
    Gd (mulR A B) (g * h) :=
  ⟨repE_mul hA.1 hB.1, validR_mulR (size_of_validR hA.2) hB.2⟩

theorem gd_one : Gd oneR (1 : trialityGroup8) := ⟨repE_one, validR_oneR⟩

theorem Gd.pow {A : Array ℕ} {g : trialityGroup8} (h : Gd A g) (e : ℕ) :
    Gd (powRows 24 A e) (g ^ e) :=
  ⟨repE_powRows h.1 e, validR_powRows h.2 e⟩

theorem Gd.eq_iff {A B : Array ℕ} {g h : trialityGroup8} (hA : Gd A g) (hB : Gd B h) :
    A = B ↔ g = h :=
  eq_iff_of_repE hA.2 hB.2 hA.1 hB.1

theorem gd_word {w : List ℕ} (hw : ∀ k ∈ w, k < 8) : Gd (wordR d4Gens w) (d4Word w) :=
  ⟨repE_d4Word hw, validR_d4Word hw⟩

theorem repE_inv_of_mul {A B : Array ℕ} {g : trialityGroup8} (hA : RepE d4E A g)
    (h : mulR A B = oneR) : RepE d4E B g⁻¹ := by
  have h1 : rowsMatrix 24 (mulR A B) = rowsMatrix 24 oneR := by rw [h]
  have h2 : d4E g * rowsMatrix 24 B = 1 := by
    unfold mulR oneR at h1
    rw [rowsMatrix_mulRows, rowsMatrix_idRows] at h1
    rwa [show rowsMatrix 24 A = d4E g from hA] at h1
  unfold RepE
  calc rowsMatrix 24 B = (d4E g⁻¹ * d4E g) * rowsMatrix 24 B := by
        rw [← map_mul, inv_mul_cancel, map_one, one_mul]
    _ = d4E g⁻¹ := by rw [mul_assoc, h2, mul_one]

theorem Gd.inv_of_mul {A B : Array ℕ} {g : trialityGroup8} (hA : Gd A g) (hB : validR B = true)
    (h : mulR A B = oneR) : Gd B g⁻¹ :=
  ⟨repE_inv_of_mul hA.1 h, hB⟩

theorem memR_mem {T : Array (Array ℕ)} {idx : Array ℕ → ℕ} {y : Array ℕ}
    (h : memR T idx y = true) : y ∈ T := by
  obtain ⟨h1, h2⟩ := memR_spec h
  rw [← h2, getElem!_pos T _ h1]
  exact Array.getElem_mem h1

theorem good_getD {H : Subgroup trialityGroup8} {a : Array (Array ℕ)}
    (h : ∀ x ∈ a, ∃ σ ∈ H, Gd x σ) (i : ℕ) : ∃ σ ∈ H, Gd (a.getD i oneR) σ := by
  rw [Array.getD_eq_getD_getElem?]
  cases hi : a[i]? with
  | none => exact ⟨1, H.one_mem, gd_one⟩
  | some x => exact h x (Array.mem_of_getElem? hi)

theorem good_foldl {H : Subgroup trialityGroup8} {gs : Array (Array ℕ)}
    (hgs : ∀ x ∈ gs, ∃ σ ∈ H, Gd x σ) (pl : List (ℕ × ℕ)) :
    ∀ acc : Array (Array ℕ), (∀ x ∈ acc, ∃ σ ∈ H, Gd x σ) →
      ∀ x ∈ pl.foldl (fun (acc : Array (Array ℕ)) (pr : ℕ × ℕ) =>
        acc.push (mulR (acc.getD pr.1 oneR) (gs.getD pr.2 oneR))) acc, ∃ σ ∈ H, Gd x σ := by
  induction pl with
  | nil => intro acc h; simpa using h
  | cons pr pl ih =>
    intro acc h
    refine ih _ ?_
    intro x hx
    rw [Array.mem_push] at hx
    rcases hx with hx | rfl
    · exact h x hx
    · obtain ⟨σ, hσ, hs⟩ := good_getD h pr.1
      obtain ⟨τ, hτ, ht⟩ := good_getD hgs pr.2
      exact ⟨σ * τ, H.mul_mem hσ hτ, hs.mul ht⟩

theorem oneR_mem_foldl (gs : Array (Array ℕ)) (pl : List (ℕ × ℕ)) :
    ∀ acc : Array (Array ℕ), oneR ∈ acc →
      oneR ∈ pl.foldl (fun (acc : Array (Array ℕ)) (pr : ℕ × ℕ) =>
        acc.push (mulR (acc.getD pr.1 oneR) (gs.getD pr.2 oneR))) acc := by
  induction pl with
  | nil => intro acc h; simpa using h
  | cons pr pl ih =>
    intro acc h
    exact ih _ (by rw [Array.mem_push]; exact Or.inl h)

theorem oneR_mem_buildTabR (gs : Array (Array ℕ)) (pl : List (ℕ × ℕ)) :
    oneR ∈ buildTabR gs pl := by
  unfold buildTabR
  exact oneR_mem_foldl gs pl _ (by simp)

theorem good_buildTabR {H : Subgroup trialityGroup8} {gs : Array (Array ℕ)}
    (hgs : ∀ x ∈ gs, ∃ σ ∈ H, Gd x σ) (pl : List (ℕ × ℕ)) :
    ∀ x ∈ buildTabR gs pl, ∃ σ ∈ H, Gd x σ := by
  unfold buildTabR
  refine good_foldl hgs pl #[oneR] fun x hx => ?_
  rw [show x = oneR by simpa using hx]
  exact ⟨1, H.one_mem, gd_one⟩

theorem tabOKOn_parts {gs gi T : Array (Array ℕ)} {idx : Array ℕ → ℕ} {N : ℕ}
    (h : tabOKOn gs gi T idx N = true) :
    T.size = N ∧ (∀ i < T.size, idx T[i]! = i) ∧
      (∀ i < gs.size, mulR gs[i]! gi[i]! = oneR) ∧
      ∀ j < T.size, ∀ i < gs.size, memR T idx (mulR T[j]! gs[i]!) = true ∧
        memR T idx (mulR T[j]! gi[i]!) = true := by
  simp only [tabOKOn, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨h1, fun i hi => ?_, fun i hi => ?_, fun j hj i hi => ?_⟩
  · simpa using allLt_spec h2 hi
  · simpa using allLt_spec h3 hi
  · have := allLt_spec (allLt_spec h4 hj) hi
    simpa only [Bool.and_eq_true] using this

theorem card_eq_of_tab {H : Subgroup trialityGroup8} {T : Array (Array ℕ)} {idx : Array ℕ → ℕ}
    (hg : ∀ x ∈ T, ∃ σ ∈ H, Gd x σ) (hidx : ∀ i < T.size, idx T[i]! = i)
    (hc : ∀ τ ∈ H, ∃ x ∈ T, RepE d4E x τ) : Nat.card H = T.size := by
  classical
  have hg' : ∀ i : Fin T.size, ∃ σ ∈ H, Gd T[i.1] σ := fun i => hg _ (Array.getElem_mem i.2)
  choose σ hσ hgd using hg'
  let f : Fin T.size → H := fun i => ⟨σ i, hσ i⟩
  have hf : Function.Bijective f := by
    constructor
    · intro i j hij
      have hij' : σ i = σ j := congrArg Subtype.val hij
      have h1 : T[i.1] = T[j.1] := (Gd.eq_iff (hgd i) (hgd j)).2 hij'
      apply Fin.ext
      have a := hidx i i.2
      have b := hidx j j.2
      rw [getElem!_pos T i.1 i.2] at a
      rw [getElem!_pos T j.1 j.2] at b
      rw [← a, ← b, h1]
    · rintro ⟨τ, hτ⟩
      obtain ⟨x, hx, rx⟩ := hc τ hτ
      obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 hx
      exact ⟨⟨k, hk⟩, Subtype.ext (eq_of_repE d4E_injective (hgd ⟨k, hk⟩).1 rx)⟩
  rw [← Nat.card_eq_of_bijective f hf, Nat.card_fin]

theorem tab_complete_R {S : Set trialityGroup8} {gs gi T : Array (Array ℕ)} {idx : Array ℕ → ℕ}
    {N : ℕ} (hS : ∀ σ ∈ S, ∃ i < gs.size, RepE d4E gs[i]! σ) (h0 : oneR ∈ T)
    (h : tabOKOn gs gi T idx N = true) :
    ∀ τ ∈ Subgroup.closure S, ∃ x ∈ T, RepE d4E x τ := by
  obtain ⟨-, -, hinv, hcl⟩ := tabOKOn_parts h
  set P : trialityGroup8 → Prop := fun τ => ∃ x ∈ T, RepE d4E x τ with hP
  let K : Subgroup trialityGroup8 :=
    { carrier := {σ | ∀ τ, P τ → P (τ * σ) ∧ P (τ * σ⁻¹)}
      mul_mem' := by
        intro a b ha hb τ hτ
        refine ⟨?_, ?_⟩
        · have := (hb _ (ha τ hτ).1).1
          rwa [mul_assoc] at this
        · have := (ha _ (hb τ hτ).2).2
          rwa [mul_inv_rev, ← mul_assoc]
      one_mem' := by
        intro τ hτ
        exact ⟨by simpa using hτ, by simpa using hτ⟩
      inv_mem' := by
        intro a ha τ hτ
        simpa using (ha τ hτ).symm }
  have hSK : S ⊆ K := by
    intro σ hσ τ ⟨x, hx, rx⟩
    obtain ⟨i, hi, ri⟩ := hS σ hσ
    have rinv : RepE d4E gi[i]! σ⁻¹ := repE_inv_of_mul ri (hinv i hi)
    obtain ⟨j, hj, rfl⟩ := Array.mem_iff_getElem.1 hx
    obtain ⟨h1, h2⟩ := hcl j hj i hi
    rw [← getElem!_pos T j hj] at rx
    exact ⟨⟨_, memR_mem h1, repE_mul rx ri⟩, ⟨_, memR_mem h2, repE_mul rx rinv⟩⟩
  intro τ hτ
  have hτK : τ ∈ K := Subgroup.closure_le K |>.2 hSK hτ
  have := (hτK 1 ⟨oneR, h0, repE_one⟩).1
  rwa [one_mul] at this

end CFSG.Quasithin.Background.Harris.R1.D4Vert

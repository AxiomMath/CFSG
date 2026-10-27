module

public import CFSG.Quasithin.H13.GoldschmidtC137U33S2Act

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit

@[expose] def chainReach (cl : List (List ℕ)) : List (ℕ × ℕ × ℕ) → List ℕ → Option (List ℕ)
  | [], acc => some acc
  | (c, p, j) :: rest, acc =>
      if p ∈ acc ∧ j < cl.length ∧ mact (cl.getD j []) p = c then
        chainReach cl rest (c :: acc)
      else none

theorem chainReach_sound (H : Subgroup Gam) (gl : List Gam) (hgl : ∀ x ∈ gl, x ∈ H) :
    ∀ (steps : List (ℕ × ℕ × ℕ)) (acc acc' : List ℕ), (∀ c ∈ acc, ∃ h ∈ H, act h 8 = c) →
      chainReach (gl.map fun x => matCode x.1) steps acc = some acc' →
        ∀ c ∈ acc', ∃ h ∈ H, act h 8 = c := by
  intro steps
  induction steps with
  | nil =>
    intro acc acc' hacc h
    simp only [chainReach, Option.some.injEq] at h
    subst h
    exact hacc
  | cons st rest ih =>
    intro acc acc' hacc h
    obtain ⟨c, p, j⟩ := st
    simp only [chainReach] at h
    split_ifs at h with hcond
    obtain ⟨hp, hj, hc⟩ := hcond
    refine ih (c :: acc) acc' ?_ h
    intro d hd
    rcases List.mem_cons.1 hd with rfl | hd
    · obtain ⟨h0, hh0, hh0p⟩ := hacc p hp
      have hj' : j < gl.length := by simpa using hj
      refine ⟨gl[j] * h0, mul_mem (hgl _ (List.getElem_mem hj')) hh0, ?_⟩
      rw [act_mul _ _ (by norm_num : 8 < 256), hh0p]
      rw [List.getD_eq_getElem _ _ (by simpa using hj)] at hc
      simpa [act] using hc
    · exact hacc d hd

theorem chain_start (H : Subgroup Gam) : ∀ c ∈ [8], ∃ h ∈ H, act h 8 = c := by
  intro c hc
  rw [List.mem_singleton] at hc
  exact ⟨1, one_mem H, by rw [hc]; exact act_one (by norm_num)⟩

theorem orbit_of_chain (H : Subgroup Gam) (gl : List Gam) (hgl : ∀ x ∈ gl, x ∈ H)
    (steps : List (ℕ × ℕ × ℕ)) (acc : List ℕ)
    (h : chainReach (gl.map fun x => matCode x.1) steps [8] = some acc) :
    ∀ c ∈ acc, ∃ h ∈ H, act h 8 = c :=
  chainReach_sound H gl hgl steps [8] acc (chain_start H) h

theorem act_gprod (gl : List Gam) (w : List ℕ) (hw : ∀ j ∈ w, j < gl.length) (c : ℕ) :
    act (gprod gl w) c = mact (gcode (gl.map fun x => matCode x.1) w) c := by
  unfold act
  rw [matCode_gprod gl w hw]

@[expose] def chainCovers (cl : List (List ℕ)) (steps : List (ℕ × ℕ × ℕ)) (target : List ℕ) :
    Bool :=
  match chainReach cl steps [8] with
  | some acc => target.all fun c => acc.contains c
  | none => false

theorem chainCovers_sound (H : Subgroup Gam) (gl : List Gam) (hgl : ∀ x ∈ gl, x ∈ H)
    (steps : List (ℕ × ℕ × ℕ)) (target : List ℕ)
    (h : chainCovers (gl.map fun x => matCode x.1) steps target = true) :
    ∀ c ∈ target, ∃ h ∈ H, act h 8 = c := by
  unfold chainCovers at h
  split at h
  · rename_i acc hacc
    intro c hc
    refine orbit_of_chain H gl hgl steps acc hacc c ?_
    simpa using (List.all_eq_true.1 h c hc)
  · exact absurd h (by simp)

end CFSG.Quasithin.H13.U3.GC137.S2

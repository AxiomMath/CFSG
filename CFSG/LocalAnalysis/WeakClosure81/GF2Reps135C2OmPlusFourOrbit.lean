module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQOrbit

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.LieType.Universal.Spin
open CFSG.StandardType

private theorem w183_four_orbit {v : Fin 4 → ℤ} {t : Fin 4 → ℤ} (hv : toStdD 4 v = t)
    (T : Fin 4 → Equiv.Perm (Fin 4) × (Fin 4 → ℤ))
    (hT : ∀ i, SpIsSign (T i).2 ∧ ∏ a, (T i).2 a = 1)
    (d : Fin 4 → Fin 4 → ℤ)
    (hd : ∀ i, d i = fun b => (T i).2 ((T i).1.symm b) * t ((T i).1.symm b))
    {x : (coxeterMatrix (isFiniteType_cartanD 4)).Group} {π : Equiv.Perm (Fin 4)}
    {s : Fin 4 → ℤ} (hxr : OmRealizes 4 x π s)
    (hinj : Function.Injective d)
    (hsep : ∀ i l, d i ≠ fun b => s (π.symm b) * d l (π.symm b)) :
    ∃ u : Fin 4 → Fin 4 → ℤ,
      (∀ i, ∃ w, u i = weylAction (isFiniteType_cartanD 4) w v) ∧
      Function.Injective u ∧
      ∀ i l, u i ≠ weylAction (isFiniteType_cartanD 4) x (u l) := by
  choose w hw using fun i =>
    exists_omRealizes_of_even (n := 4) (by norm_num) (T i).1 (hT i).1 (hT i).2
  let u : Fin 4 → Fin 4 → ℤ := fun i => weylAction (isFiniteType_cartanD 4) (w i) v
  have hu : ∀ i, toStdD 4 (u i) = d i := by
    intro i
    change toStdD 4 (weylAction (isFiniteType_cartanD 4) (w i) v) = d i
    rw [hw i v, hv]
    exact (hd i).symm
  refine ⟨u, fun i => ⟨w i, rfl⟩, ?_, ?_⟩
  · intro i l hil
    have key := congrArg (toStdD 4) hil
    rw [hu i, hu l] at key
    exact hinj key
  · intro i l hil
    have key := congrArg (toStdD 4) hil
    rw [hu i, hxr (u l), hu l] at key
    exact hsep i l key

private theorem w183_sep (d : Fin 4 → Fin 4 → ℤ) (c : ℤ)
    {π : Equiv.Perm (Fin 4)} {s : Fin 4 → ℤ} (hs : SpIsSign s)
    (hx : (π (0 : Fin 4) = 0 ∧ s (0 : Fin 4) = -1) ∨
      (π (0 : Fin 4) = 1 ∧ π (1 : Fin 4) = 0 ∧ s (0 : Fin 4) = s (1 : Fin 4)))
    (hc : c ≠ 0) (h0 : ∀ i, d i 0 = c)
    (hne : ∀ l, ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ε * d l 1 ≠ c) :
    ∀ i l, d i ≠ fun b => s (π.symm b) * d l (π.symm b) := by
  intro i l hcontra
  have h0' := congrFun hcontra (0 : Fin 4)
  rcases hx with ⟨hπ0, hs0⟩ | ⟨hπ0, hπ1, hs01⟩
  · have hsymi : π.symm (0 : Fin 4) = 0 := (Equiv.symm_apply_eq π).2 hπ0.symm
    rw [hsymi, h0 i, h0 l, hs0] at h0'
    exact hc (by linarith)
  · have hsymi : π.symm (0 : Fin 4) = 1 := (Equiv.symm_apply_eq π).2 hπ1.symm
    rw [hsymi, h0 i] at h0'
    exact hne l (s 1) (hs 1) h0'.symm

private def w183_tOne : Fin 4 → ℤ := ![2, 2, 0, 0]

private def w183_TOne : Fin 4 → Equiv.Perm (Fin 4) × (Fin 4 → ℤ) :=
  ![((Equiv.swap 1 2, ![1, 1, 1, 1])),
    ((Equiv.swap 1 2, ![1, -1, -1, 1])),
    ((Equiv.swap 1 3, ![1, 1, 1, 1])),
    ((Equiv.swap 1 3, ![1, -1, 1, -1]))]

private def w183_dOne : Fin 4 → Fin 4 → ℤ :=
  ![![2, 0, 2, 0], ![2, 0, -2, 0], ![2, 0, 0, 2], ![2, 0, 0, -2]]

private theorem w183_hvOne : toStdD 4 (omExtWt 4 1) = w183_tOne := by
  rw [show omExtWt 4 1 = omFromStdD2 4 (fun a => if a.val ≤ 1 then (1 : ℤ) else 0) from rfl,
    toStdD_omFromStdD2 (n := 4) (by norm_num)]
  funext b
  fin_cases b <;> simp [w183_tOne]

private theorem w183_hTOne : ∀ i, SpIsSign (w183_TOne i).2 ∧
    ∏ a, (w183_TOne i).2 a = 1 := by
  intro i
  fin_cases i <;>
    exact ⟨by intro a; fin_cases a <;> decide,
      by rw [Fin.prod_univ_four]; simp [w183_TOne]⟩

private theorem w183_hdOne : ∀ i, w183_dOne i =
    fun b => (w183_TOne i).2 ((w183_TOne i).1.symm b) * w183_tOne ((w183_TOne i).1.symm b) := by
  intro i
  fin_cases i <;> funext b <;> fin_cases b <;>
    simp [w183_dOne, w183_TOne, w183_tOne, Equiv.symm_swap, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]

private theorem w183_hinjOne : Function.Injective w183_dOne := by
  intro i l hil
  have h2 : w183_dOne i 2 = w183_dOne l 2 := by rw [hil]
  have h3 : w183_dOne i 3 = w183_dOne l 3 := by rw [hil]
  fin_cases i <;> fin_cases l <;> simp_all [w183_dOne]

private theorem w183_hneOne : ∀ l, ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ε * w183_dOne l 1 ≠ 2 := by
  intro l ε _
  have hl : w183_dOne l 1 = 0 := by fin_cases l <;> simp [w183_dOne]
  rw [hl, mul_zero]
  norm_num

private theorem w183_node_one_orbit
    {x : (coxeterMatrix (isFiniteType_cartanD 4)).Group} {π : Equiv.Perm (Fin 4)}
    {s : Fin 4 → ℤ} (hxr : OmRealizes 4 x π s) (hs : SpIsSign s)
    (hx : (π (0 : Fin 4) = 0 ∧ s (0 : Fin 4) = -1) ∨
      (π (0 : Fin 4) = 1 ∧ π (1 : Fin 4) = 0 ∧ s (0 : Fin 4) = s (1 : Fin 4))) :
    ∃ u : Fin 4 → Fin 4 → ℤ,
      (∀ l, ∃ w, u l = weylAction (isFiniteType_cartanD 4) w (omExtWt 4 1)) ∧
      Function.Injective u ∧
      ∀ l l', u l ≠ weylAction (isFiniteType_cartanD 4) x (u l') :=
  w183_four_orbit w183_hvOne w183_TOne w183_hTOne w183_dOne w183_hdOne hxr w183_hinjOne
    (w183_sep w183_dOne 2 hs hx (by norm_num)
      (fun i => by fin_cases i <;> simp [w183_dOne]) w183_hneOne)

private def w183_tPair02 : Fin 4 → ℤ := ![4, 2, 2, -2]

private def w183_TPair02 : Fin 4 → Equiv.Perm (Fin 4) × (Fin 4 → ℤ) :=
  ![((Equiv.refl (Fin 4), ![1, 1, 1, 1])),
    ((Equiv.refl (Fin 4), ![1, 1, -1, -1])),
    ((Equiv.refl (Fin 4), ![1, -1, 1, -1])),
    ((Equiv.refl (Fin 4), ![1, -1, -1, 1]))]

private def w183_dPair02 : Fin 4 → Fin 4 → ℤ :=
  ![![4, 2, 2, -2], ![4, 2, -2, 2], ![4, -2, 2, 2], ![4, -2, -2, -2]]

private def w183_tPair03 : Fin 4 → ℤ := ![4, 2, 2, 2]

private def w183_TPair03 : Fin 4 → Equiv.Perm (Fin 4) × (Fin 4 → ℤ) :=
  ![((Equiv.refl (Fin 4), ![1, 1, 1, 1])),
    ((Equiv.refl (Fin 4), ![1, 1, -1, -1])),
    ((Equiv.refl (Fin 4), ![1, -1, 1, -1])),
    ((Equiv.refl (Fin 4), ![1, -1, -1, 1]))]

private def w183_dPair03 : Fin 4 → Fin 4 → ℤ :=
  ![![4, 2, 2, 2], ![4, 2, -2, -2], ![4, -2, 2, -2], ![4, -2, -2, 2]]

private def w183_tPair23 : Fin 4 → ℤ := ![4, 4, 4, 0]

private def w183_TPair23 : Fin 4 → Equiv.Perm (Fin 4) × (Fin 4 → ℤ) :=
  ![((Equiv.swap 1 3, ![1, 1, 1, 1])),
    ((Equiv.swap 1 3, ![1, -1, 1, -1])),
    ((Equiv.swap 1 3, ![1, 1, -1, -1])),
    ((Equiv.swap 1 3, ![1, -1, -1, 1]))]

private def w183_dPair23 : Fin 4 → Fin 4 → ℤ :=
  ![![4, 0, 4, 4], ![4, 0, 4, -4], ![4, 0, -4, 4], ![4, 0, -4, -4]]

private theorem w183_hvPair02 :
    toStdD 4 (omNatWt 4 + omHalfSpin2 4 ⟨2, by omega⟩) = w183_tPair02 := by
  rw [toStdD_add,
    show omNatWt 4 = omFromStdD2 4 (fun a => if a.val = 0 then (1 : ℤ) else 0) from rfl,
    toStdD_omFromStdD2 (n := 4) (by norm_num),
    show omHalfSpin2 4 ⟨2, by omega⟩ =
      omFromStdD2 4 (fun a => if 2 + 2 = 4 ∧ a.val + 1 = 4 then (-1 : ℤ) else 1) from rfl,
    toStdD_omFromStdD2 (n := 4) (by norm_num)]
  funext b
  fin_cases b <;> simp [w183_tPair02]

private theorem w183_hvPair03 :
    toStdD 4 (omNatWt 4 + omHalfSpin2 4 ⟨3, by omega⟩) = w183_tPair03 := by
  rw [toStdD_add,
    show omNatWt 4 = omFromStdD2 4 (fun a => if a.val = 0 then (1 : ℤ) else 0) from rfl,
    toStdD_omFromStdD2 (n := 4) (by norm_num),
    show omHalfSpin2 4 ⟨3, by omega⟩ =
      omFromStdD2 4 (fun a => if 3 + 2 = 4 ∧ a.val + 1 = 4 then (-1 : ℤ) else 1) from rfl,
    toStdD_omFromStdD2 (n := 4) (by norm_num)]
  funext b
  fin_cases b <;> simp [w183_tPair03]

private theorem w183_hvPair23 :
    toStdD 4 (omHalfSpin2 4 ⟨2, by omega⟩ + omHalfSpin2 4 ⟨3, by omega⟩) = w183_tPair23 := by
  rw [toStdD_add,
    show omHalfSpin2 4 ⟨2, by omega⟩ =
      omFromStdD2 4 (fun a => if 2 + 2 = 4 ∧ a.val + 1 = 4 then (-1 : ℤ) else 1) from rfl,
    toStdD_omFromStdD2 (n := 4) (by norm_num),
    show omHalfSpin2 4 ⟨3, by omega⟩ =
      omFromStdD2 4 (fun a => if 3 + 2 = 4 ∧ a.val + 1 = 4 then (-1 : ℤ) else 1) from rfl,
    toStdD_omFromStdD2 (n := 4) (by norm_num)]
  funext b
  fin_cases b <;> simp [w183_tPair23]

private theorem w183_hTPair02 : ∀ i, SpIsSign (w183_TPair02 i).2 ∧
    ∏ a, (w183_TPair02 i).2 a = 1 := by
  intro i
  fin_cases i <;>
    exact ⟨by intro a; fin_cases a <;> decide,
      by rw [Fin.prod_univ_four]; simp [w183_TPair02]⟩

private theorem w183_hTPair03 : ∀ i, SpIsSign (w183_TPair03 i).2 ∧
    ∏ a, (w183_TPair03 i).2 a = 1 := by
  intro i
  fin_cases i <;>
    exact ⟨by intro a; fin_cases a <;> decide,
      by rw [Fin.prod_univ_four]; simp [w183_TPair03]⟩

private theorem w183_hTPair23 : ∀ i, SpIsSign (w183_TPair23 i).2 ∧
    ∏ a, (w183_TPair23 i).2 a = 1 := by
  intro i
  fin_cases i <;>
    exact ⟨by intro a; fin_cases a <;> decide,
      by rw [Fin.prod_univ_four]; simp [w183_TPair23]⟩

private theorem w183_hdPair02 : ∀ i, w183_dPair02 i = fun b =>
    (w183_TPair02 i).2 ((w183_TPair02 i).1.symm b) * w183_tPair02 ((w183_TPair02 i).1.symm b) := by
  intro i
  fin_cases i <;> funext b <;> fin_cases b <;>
    simp [w183_dPair02, w183_TPair02, w183_tPair02]

private theorem w183_hdPair03 : ∀ i, w183_dPair03 i = fun b =>
    (w183_TPair03 i).2 ((w183_TPair03 i).1.symm b) * w183_tPair03 ((w183_TPair03 i).1.symm b) := by
  intro i
  fin_cases i <;> funext b <;> fin_cases b <;>
    simp [w183_dPair03, w183_TPair03, w183_tPair03]

private theorem w183_hdPair23 : ∀ i, w183_dPair23 i = fun b =>
    (w183_TPair23 i).2 ((w183_TPair23 i).1.symm b) * w183_tPair23 ((w183_TPair23 i).1.symm b) := by
  intro i
  fin_cases i <;> funext b <;> fin_cases b <;>
    simp [w183_dPair23, w183_TPair23, w183_tPair23, Equiv.symm_swap, Equiv.swap_apply_left,
      Equiv.swap_apply_right, Equiv.swap_apply_of_ne_of_ne]

private theorem w183_hinjPair02 : Function.Injective w183_dPair02 := by
  intro i l hil
  have h1 : w183_dPair02 i 1 = w183_dPair02 l 1 := by rw [hil]
  have h2 : w183_dPair02 i 2 = w183_dPair02 l 2 := by rw [hil]
  fin_cases i <;> fin_cases l <;> simp_all [w183_dPair02]

private theorem w183_hinjPair03 : Function.Injective w183_dPair03 := by
  intro i l hil
  have h1 : w183_dPair03 i 1 = w183_dPair03 l 1 := by rw [hil]
  have h2 : w183_dPair03 i 2 = w183_dPair03 l 2 := by rw [hil]
  fin_cases i <;> fin_cases l <;> simp_all [w183_dPair03]

private theorem w183_hinjPair23 : Function.Injective w183_dPair23 := by
  intro i l hil
  have h2 : w183_dPair23 i 2 = w183_dPair23 l 2 := by rw [hil]
  have h3 : w183_dPair23 i 3 = w183_dPair23 l 3 := by rw [hil]
  fin_cases i <;> fin_cases l <;> simp_all [w183_dPair23]

private theorem w183_hnePair02 :
    ∀ l, ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ε * w183_dPair02 l 1 ≠ 4 := by
  intro l ε hε
  have hl : w183_dPair02 l 1 = 2 ∨ w183_dPair02 l 1 = -2 := by
    fin_cases l <;> simp [w183_dPair02]
  rcases hl with h | h <;> rw [h] <;> rcases hε with h1 | h1 <;> rw [h1] <;> norm_num

private theorem w183_hnePair03 :
    ∀ l, ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ε * w183_dPair03 l 1 ≠ 4 := by
  intro l ε hε
  have hl : w183_dPair03 l 1 = 2 ∨ w183_dPair03 l 1 = -2 := by
    fin_cases l <;> simp [w183_dPair03]
  rcases hl with h | h <;> rw [h] <;> rcases hε with h1 | h1 <;> rw [h1] <;> norm_num

private theorem w183_hnePair23 :
    ∀ l, ∀ ε : ℤ, (ε = 1 ∨ ε = -1) → ε * w183_dPair23 l 1 ≠ 4 := by
  intro l ε _
  have hl : w183_dPair23 l 1 = 0 := by fin_cases l <;> simp [w183_dPair23]
  rw [hl, mul_zero]
  norm_num

private theorem w183_pair_02
    {x : (coxeterMatrix (isFiniteType_cartanD 4)).Group} {π : Equiv.Perm (Fin 4)}
    {s : Fin 4 → ℤ} (hxr : OmRealizes 4 x π s) (hs : SpIsSign s)
    (hx : (π (0 : Fin 4) = 0 ∧ s (0 : Fin 4) = -1) ∨
      (π (0 : Fin 4) = 1 ∧ π (1 : Fin 4) = 0 ∧ s (0 : Fin 4) = s (1 : Fin 4))) :
    ∃ v : Fin 4 → ℤ,
      (∀ k : Fin 4, k ≠ (0 : Fin 4) → k ≠ (2 : Fin 4) →
        weylAction (isFiniteType_cartanD 4)
          ((coxeterMatrix (isFiniteType_cartanD 4)).toCoxeterSystem.simple k) v = v) ∧
      ∃ u : Fin 4 → Fin 4 → ℤ,
        (∀ l, ∃ w, u l = weylAction (isFiniteType_cartanD 4) w v) ∧
        Function.Injective u ∧
        ∀ l l', u l ≠ weylAction (isFiniteType_cartanD 4) x (u l') := by
  refine ⟨omNatWt 4 + omHalfSpin2 4 ⟨2, by omega⟩, ?_, ?_⟩
  · intro k hk0 hk2
    rw [map_add,
      weylAction_simple_omNatWt (n := 4) (by norm_num) (fun h => hk0 (Fin.ext h)),
      weylAction_simple_omHalfSpin2 (n := 4) (h := ⟨2, by omega⟩) (by norm_num) (by norm_num) hk2]
  · exact w183_four_orbit w183_hvPair02 w183_TPair02 w183_hTPair02 w183_dPair02 w183_hdPair02
      hxr w183_hinjPair02
      (w183_sep w183_dPair02 4 hs hx (by norm_num)
        (fun i => by fin_cases i <;> simp [w183_dPair02]) w183_hnePair02)

private theorem w183_pair_03
    {x : (coxeterMatrix (isFiniteType_cartanD 4)).Group} {π : Equiv.Perm (Fin 4)}
    {s : Fin 4 → ℤ} (hxr : OmRealizes 4 x π s) (hs : SpIsSign s)
    (hx : (π (0 : Fin 4) = 0 ∧ s (0 : Fin 4) = -1) ∨
      (π (0 : Fin 4) = 1 ∧ π (1 : Fin 4) = 0 ∧ s (0 : Fin 4) = s (1 : Fin 4))) :
    ∃ v : Fin 4 → ℤ,
      (∀ k : Fin 4, k ≠ (0 : Fin 4) → k ≠ (3 : Fin 4) →
        weylAction (isFiniteType_cartanD 4)
          ((coxeterMatrix (isFiniteType_cartanD 4)).toCoxeterSystem.simple k) v = v) ∧
      ∃ u : Fin 4 → Fin 4 → ℤ,
        (∀ l, ∃ w, u l = weylAction (isFiniteType_cartanD 4) w v) ∧
        Function.Injective u ∧
        ∀ l l', u l ≠ weylAction (isFiniteType_cartanD 4) x (u l') := by
  refine ⟨omNatWt 4 + omHalfSpin2 4 ⟨3, by omega⟩, ?_, ?_⟩
  · intro k hk0 hk3
    rw [map_add,
      weylAction_simple_omNatWt (n := 4) (by norm_num) (fun h => hk0 (Fin.ext h)),
      weylAction_simple_omHalfSpin2 (n := 4) (h := ⟨3, by omega⟩) (by norm_num) (by norm_num) hk3]
  · exact w183_four_orbit w183_hvPair03 w183_TPair03 w183_hTPair03 w183_dPair03 w183_hdPair03
      hxr w183_hinjPair03
      (w183_sep w183_dPair03 4 hs hx (by norm_num)
        (fun i => by fin_cases i <;> simp [w183_dPair03]) w183_hnePair03)

private theorem w183_pair_23
    {x : (coxeterMatrix (isFiniteType_cartanD 4)).Group} {π : Equiv.Perm (Fin 4)}
    {s : Fin 4 → ℤ} (hxr : OmRealizes 4 x π s) (hs : SpIsSign s)
    (hx : (π (0 : Fin 4) = 0 ∧ s (0 : Fin 4) = -1) ∨
      (π (0 : Fin 4) = 1 ∧ π (1 : Fin 4) = 0 ∧ s (0 : Fin 4) = s (1 : Fin 4))) :
    ∃ v : Fin 4 → ℤ,
      (∀ k : Fin 4, k ≠ (2 : Fin 4) → k ≠ (3 : Fin 4) →
        weylAction (isFiniteType_cartanD 4)
          ((coxeterMatrix (isFiniteType_cartanD 4)).toCoxeterSystem.simple k) v = v) ∧
      ∃ u : Fin 4 → Fin 4 → ℤ,
        (∀ l, ∃ w, u l = weylAction (isFiniteType_cartanD 4) w v) ∧
        Function.Injective u ∧
        ∀ l l', u l ≠ weylAction (isFiniteType_cartanD 4) x (u l') := by
  refine ⟨omHalfSpin2 4 ⟨2, by omega⟩ + omHalfSpin2 4 ⟨3, by omega⟩, ?_, ?_⟩
  · intro k hk2 hk3
    rw [map_add,
      weylAction_simple_omHalfSpin2 (n := 4) (h := ⟨2, by omega⟩) (by norm_num) (by norm_num) hk2,
      weylAction_simple_omHalfSpin2 (n := 4) (h := ⟨3, by omega⟩) (by norm_num) (by norm_num) hk3]
  · exact w183_four_orbit w183_hvPair23 w183_TPair23 w183_hTPair23 w183_dPair23 w183_hdPair23
      hxr w183_hinjPair23
      (w183_sep w183_dPair23 4 hs hx (by norm_num)
        (fun i => by fin_cases i <;> simp [w183_dPair23]) w183_hnePair23)

theorem exists_four_orbit_omPlus_four_node_one
    {x : (coxeterMatrix (isFiniteType_cartanD 4)).Group} {π : Equiv.Perm (Fin 4)}
    {s : Fin 4 → ℤ} (hxr : OmRealizes 4 x π s) (hs : SpIsSign s) (hprod : ∏ a, s a = 1)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) :
    ∃ v : Fin 4 → ℤ,
      (∀ k : Fin 4, k.val ≠ 1 →
        weylAction (isFiniteType_cartanD 4)
          ((coxeterMatrix (isFiniteType_cartanD 4)).toCoxeterSystem.simple k) v = v) ∧
      ∃ u : Fin 4 → Fin 4 → ℤ,
        (∀ l, ∃ w, u l = weylAction (isFiniteType_cartanD 4) w v) ∧
        Function.Injective u ∧
        ∀ l l', u l ≠ weylAction (isFiniteType_cartanD 4) x (u l') := by
  refine ⟨omExtWt 4 1, ?_, ?_⟩
  · intro k hk
    exact weylAction_simple_omExtWt (n := 4) (j := 1) (by norm_num) (by norm_num) hk
  · exact w183_node_one_orbit hxr hs (by simpa using hx)

theorem exists_four_orbit_omPlus_four_pair {i j : Fin 4} (hij : i ≠ j) (hi : i.val ≠ 1)
    (hj : j.val ≠ 1)
    {x : (coxeterMatrix (isFiniteType_cartanD 4)).Group} {π : Equiv.Perm (Fin 4)}
    {s : Fin 4 → ℤ} (hxr : OmRealizes 4 x π s) (hs : SpIsSign s) (hprod : ∏ a, s a = 1)
    (hx : (π ⟨0, by omega⟩ = ⟨0, by omega⟩ ∧ s ⟨0, by omega⟩ = -1) ∨
      (π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧ π ⟨1, by omega⟩ = ⟨0, by omega⟩ ∧
        s ⟨0, by omega⟩ = s ⟨1, by omega⟩)) :
    ∃ v : Fin 4 → ℤ,
      (∀ k : Fin 4, k ≠ i → k ≠ j →
        weylAction (isFiniteType_cartanD 4)
          ((coxeterMatrix (isFiniteType_cartanD 4)).toCoxeterSystem.simple k) v = v) ∧
      ∃ u : Fin 4 → Fin 4 → ℤ,
        (∀ l, ∃ w, u l = weylAction (isFiniteType_cartanD 4) w v) ∧
        Function.Injective u ∧
        ∀ l l', u l ≠ weylAction (isFiniteType_cartanD 4) x (u l') := by
  have hx' : (π (0 : Fin 4) = 0 ∧ s (0 : Fin 4) = -1) ∨
      (π (0 : Fin 4) = 1 ∧ π (1 : Fin 4) = 0 ∧ s (0 : Fin 4) = s (1 : Fin 4)) := by
    simpa using hx
  have hdisp : (i = (0 : Fin 4) ∧ j = (2 : Fin 4)) ∨ (i = (2 : Fin 4) ∧ j = (0 : Fin 4)) ∨
      (i = (0 : Fin 4) ∧ j = (3 : Fin 4)) ∨ (i = (3 : Fin 4) ∧ j = (0 : Fin 4)) ∨
      (i = (2 : Fin 4) ∧ j = (3 : Fin 4)) ∨ (i = (3 : Fin 4) ∧ j = (2 : Fin 4)) := by
    fin_cases i <;> fin_cases j <;> simp_all
  rcases hdisp with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
  · exact w183_pair_02 hxr hs hx'
  · obtain ⟨v, hfix, hu⟩ := w183_pair_02 hxr hs hx'
    exact ⟨v, fun k h2 h0 => hfix k h0 h2, hu⟩
  · exact w183_pair_03 hxr hs hx'
  · obtain ⟨v, hfix, hu⟩ := w183_pair_03 hxr hs hx'
    exact ⟨v, fun k h3 h0 => hfix k h0 h3, hu⟩
  · exact w183_pair_23 hxr hs hx'
  · obtain ⟨v, hfix, hu⟩ := w183_pair_23 hxr hs hx'
    exact ⟨v, fun k h3 h2 => hfix k h2 h3, hu⟩

end CFSG.LocalAnalysis.WeakClosure81

module

public import Certificates.Data.E68Spor.Chk
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporGr
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtE68SporOrb
public import CFSG.Quasithin.EmptyFaithful.S151S9TLat

public section

namespace CFSG.Quasithin.E6.Spor

open CFSG.QuasithinUnique.Ch1.SporLat CFSG.QuasithinUnique.K1.SporadicPerm
  CFSG.Quasithin.S151S9T CFSG.Quasithin.S151S9T.LatAux

theorem classChk_sound {n : ℕ} {ta tb zT : Array ℕ} {s : ℕ} (h : classChk n ta tb zT s = true) :
    (∀ p < n, zT.getD p 0 < n) ∧ ∃ O : OmegaData (List ℕ),
      OmegaSpec (grAct n) #[ta, tb] (grLabel n zT) O ∧ O.lbl.size = s := by
  unfold classChk at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq,
    beq_iff_eq, and_assoc] at h
  obtain ⟨h1, h2, h3⟩ := h
  exact ⟨h1, _, h2, h3⟩

section Words

variable {Γ : Type} [Group Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]

theorem comm_of_tab {x z : Γ} {xT zT : Array ℕ} (hx : (tab n x).toArray = xT)
    (hz : (tab n z).toArray = zT)
    (h : wordTabA #[xT, zT] n [0, 1] = wordTabA #[xT, zT] n [1, 0]) : x * z = z * x := by
  have hel := hel_two (n := n) (x := x) (y := z) hx.symm hz.symm
  have h1 := wordTabA_eq (n := n) #[x, z] #[xT, zT] hel [0, 1] (by simp)
  have h2 := wordTabA_eq (n := n) #[x, z] #[xT, zT] hel [1, 0] (by simp)
  rw [h1, h2] at h
  have := eq_of_tab_eq h
  simpa [evalElt] using this

omit [FaithfulSMul Γ (Fin n)] in
theorem not_comm_of_tab {x z : Γ} {xT zT : Array ℕ} (hx : (tab n x).toArray = xT)
    (hz : (tab n z).toArray = zT)
    (h : wordTabA #[xT, zT] n [0, 1] ≠ wordTabA #[xT, zT] n [1, 0]) : x * z ≠ z * x := by
  intro hc
  apply h
  have hel := hel_two (n := n) (x := x) (y := z) hx.symm hz.symm
  have h1 := wordTabA_eq (n := n) #[x, z] #[xT, zT] hel [0, 1] (by simp)
  have h2 := wordTabA_eq (n := n) #[x, z] #[xT, zT] hel [1, 0] (by simp)
  rw [h1, h2]
  have h3 : evalElt (#[x, z] : Array Γ) [0, 1] = evalElt (#[x, z] : Array Γ) [1, 0] := by
    simpa [evalElt] using hc
  rw [h3]

omit [FaithfulSMul Γ (Fin n)] in
theorem not_central_of_ncChk {x z : Γ} {xT zT : Array ℕ} (hx : (tab n x).toArray = xT)
    (hz : (tab n z).toArray = zT) (h : ncChk n xT zT = true) : ¬ ∀ g : Γ, g * z = z * g :=
  fun hc => not_comm_of_tab hx hz (bne_iff_ne.mp h) (hc x)

theorem orderOf_eq_of_tab {y : Γ} {yT : Array ℕ} (hy : (tab n y).toArray = yT) {r : ℕ}
    (hr : r.Prime) (hp : wordTabA #[yT] n (List.replicate r 0) = idTab' n)
    (hne : yT ≠ idTab' n) : orderOf y = r := by
  have : Fact r.Prime := ⟨hr⟩
  have hel := hel_one (n := n) (x := y) hy.symm
  have h1 := wordTabA_eq (n := n) #[y] #[yT] hel (List.replicate r 0)
    (fun l hl => by simp [List.eq_of_mem_replicate hl])
  have h2 : evalElt (#[y] : Array Γ) (List.replicate r 0) = y ^ r := by
    simp [evalElt, List.map_replicate, List.prod_replicate]
  rw [h1, h2] at hp
  have hid : (tab n (1 : Γ)).toArray = idTab' n := tab_one_arr
  have hyr : y ^ r = 1 := eq_of_tab_eq (hp.trans hid.symm)
  refine orderOf_eq_prime hyr fun h => hne ?_
  rw [← hy, h]
  exact hid

end Words

section R

variable {Γ : Type} [Group Γ] [Finite Γ] {n : ℕ} [MulAction Γ (Fin n)] [FaithfulSMul Γ (Fin n)]
  {Lab : Type} [DecidableEq Lab] [Hashable Lab] [Inhabited Lab]

@[expose] def RWit (C : LatCtx Γ n Lab) (z₀ : Γ) (r m : ℕ) : Prop :=
  ∃ (us : List Γ) (uTabs : List (Array ℕ)) (OH : OmegaData Lab) (y x : Γ),
    genTabs n us = uTabs ∧ (∀ u ∈ us, u * z₀ = z₀ * u) ∧
    OmegaSpec C.A.act (C.D.sTabs ++ uTabs).toArray C.Δ OH ∧ OH.lbl.size = m ∧
    y * z₀ = z₀ * y ∧ orderOf y = r ∧ x ∈ C.S ∧
    (∀ i < OH.lbl.size, C.A.act (tab n x).toArray OH.lbl[i]! = OH.lbl[i]!) ∧ y * x ≠ x * y

theorem rChk_sound (C : LatCtx Γ n Lab) {sTabs : List (Array ℕ)} (hS : C.D.sTabs = sTabs)
    {z₀ : Γ} {zT : Array ℕ} (hzT : (tab n z₀).toArray = zT) {uWords : List (List ℕ)}
    {yw nw : List ℕ} {r m : ℕ} (hr : r.Prime)
    (h : rChk n C.A.act C.Δ sTabs C.ta C.tb zT uWords yw nw r m = true) : RWit C z₀ r m := by
  unfold rChk at h
  simp only [Bool.and_eq_true, List.all_eq_true, List.mem_range, decide_eq_true_eq, beq_iff_eq,
    bne_iff_ne, ne_eq, and_assoc, lettersLt, List.mem_map] at h
  obtain ⟨hu, hy, hn, hO, hm, hcomm, hord, hyne, hyc, hfix, hyn⟩ := h
  have hel := C.hel0' (Γ := Γ)
  have hsz : (#[C.a, C.b] : Array Γ).size = 2 := rfl
  have hwtab : ∀ w : List ℕ, (∀ l ∈ w, l < 2) →
      wordTabA #[C.ta, C.tb] n w = (tab n (evalElt (#[C.a, C.b] : Array Γ) w)).toArray :=
    fun w hw => wordTabA_eq _ _ hel w (by rwa [hsz])
  have hus : genTabs n (uWords.map (evalElt (#[C.a, C.b] : Array Γ))) =
      uWords.map (wordTabA #[C.ta, C.tb] n) := by
    unfold genTabs
    rw [List.map_map]
    apply List.map_congr_left
    intro w hw
    exact (hwtab w (hu w hw)).symm
  have hucomm : ∀ u ∈ uWords.map (evalElt (#[C.a, C.b] : Array Γ)), u * z₀ = z₀ * u := by
    intro u hu'
    obtain ⟨w, hw, rfl⟩ := List.mem_map.mp hu'
    exact comm_of_tab (hwtab w (hu w hw)).symm hzT (hcomm _ ⟨w, hw, rfl⟩)
  set us := uWords.map (evalElt (#[C.a, C.b] : Array Γ)) with hus_def
  set uTabs := uWords.map (wordTabA #[C.ta, C.tb] n) with huTabs_def
  have hlet : (genTabs n (C.sg ++ us)).toArray = (C.D.sTabs ++ uTabs).toArray := by
    rw [genTabs_sg_us hus]
  have hel2 : ∀ l < (C.sg ++ us).toArray.size, (C.D.sTabs ++ uTabs).toArray.getD l #[] =
      (tab n ((C.sg ++ us).toArray.getD l 1)).toArray := by
    intro l hl
    rw [← hlet]
    exact genTabs_hel (C.sg ++ us) l hl
  have hsgl : C.sg.length = sTabs.length := by
    rw [← hS, ← C.hsg, genTabs_length]
  have hlen : (C.sg ++ us).toArray.size = sTabs.length + uWords.length := by
    simp [hsgl, hus_def]
  have hytab : wordTabA (sTabs ++ uTabs).toArray n yw =
      (tab n (evalElt (C.sg ++ us).toArray yw)).toArray := by
    rw [← hS]
    exact wordTabA_eq _ _ hel2 yw (by rw [hlen]; exact hy)
  have hyz : evalElt (C.sg ++ us).toArray yw * z₀ = z₀ * evalElt (C.sg ++ us).toArray yw :=
    comm_of_tab hytab.symm hzT hyc
  have hyorder : orderOf (evalElt (C.sg ++ us).toArray yw) = r :=
    orderOf_eq_of_tab hytab.symm hr hord hyne
  obtain ⟨x, hxS, hxtab⟩ := exists_sElt C (w := nw) (by rw [hS]; exact hn)
  rw [hS] at hxtab
  refine ⟨us, uTabs,
    (buildOmega C.A.act (sTabs ++ uTabs).toArray C.Δ (m + 1)).1,
    evalElt (C.sg ++ us).toArray yw, x, hus, hucomm, ?_, hm, hyz, hyorder, hxS, ?_, ?_⟩
  · rw [hS]
    exact hO
  · intro i hi
    rw [← hxtab]
    exact hfix i hi
  · exact not_comm_of_tab hytab.symm hxtab.symm hyn

end R

end CFSG.Quasithin.E6.Spor

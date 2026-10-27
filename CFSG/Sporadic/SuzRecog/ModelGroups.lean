module

public import CFSG.Sporadic.SuzRecog.ModelGroupsKit
public import CFSG.Sporadic.SuzRecog.ModelGroupsCert
public import CFSG.Sporadic.SuzRecog.ModelGroupsDefs
public import CFSG.Sporadic.SuzRecog.C1ModelJ0
public import CFSG.Sporadic.SuzRecog.LevelTwoDefs

public noncomputable section

namespace CFSG.Sporadic.SuzRecog.ModelGroups

open Subgroup CFSG.Sporadic.SuzOddCore CFSG.Sporadic.SuzRecog.Model CFSG.Monster.B.Co2
  CFSG.Monster.B.Co2.Native CFSG.Certificates CFSG.Certificates.Native
  CFSG.Sporadic.SuzRecog.ModelGroupsCheck CFSG.Sporadic.SuzRecog.ModelGroupsData
  CFSG.Sporadic.SuzRecog.LevelTwoData

@[expose] def c1a : Equiv.Perm (Fin 1782) := permC 1782 aA

@[expose] def c1b : Equiv.Perm (Fin 1782) := permC 1782 bA

section Reps

theorem permsOK_parts :
    permOK rhoArr = true ∧ permOK w0Arr = true ∧ permOK aA = true ∧
    permOK bA = true ∧ permOK s1Arr = true ∧ permOK s2Arr = true := by
  have h := perms_check
  simp only [permsOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6⟩

theorem rep_rho1 :
    Rep 1782 rhoArr rho1 := (rep_permC permsOK_parts.1).1

theorem rep_w0 :
    Rep 1782 w0Arr w0 := (rep_permC permsOK_parts.2.1).1

theorem rep_t1 : Rep 1782 t1A (suzInv 1) := rep_suzInv (by norm_num)

theorem rep_zJ0 :
    Rep 1782 zA C1Model.zJ0 := fun x => C1Model.tabRep_zJ0.2 x

theorem rep_tau0 :
    Rep 1782 tauA C1Model.tau0 := fun x => C1Model.tabRep_tau0.2 x

theorem rep_c1a :
    Rep 1782 aA c1a := (rep_permC permsOK_parts.2.2.1).1

theorem rep_c1b :
    Rep 1782 bA c1b := (rep_permC permsOK_parts.2.2.2.1).1

theorem rep_s1 :
    Rep 1782 s1Arr s1 := (rep_permC permsOK_parts.2.2.2.2.1).1

theorem rep_s2 :
    Rep 1782 s2Arr s2 := (rep_permC permsOK_parts.2.2.2.2.2).1

theorem rep_r1 :
    Rep 1782 w1A C1Model.r1 := rep_conjA rep_rho1 rep_w0

theorem rep_r2 :
    Rep 1782 w2A C1Model.r2 := by
  rw [C1Model.r2_eq]
  exact rep_compA rep_w0 rep_r1

theorem rep_rho2 : Rep 1782 rho2A rho2 := rep_conjA rep_w0 rep_rho1

theorem basic_facts :
    rho1 ^ 3 = 1 ∧ rho1 ≠ 1 ∧ rho1 * rho2⁻¹ = C1Model.r2 ∧
    ¬ (rho1 = rho2 ∨ rho1 = rho2 * rho2) := by
  have h := basic_check
  simp only [basicOK, Bool.and_eq_true, Bool.not_eq_true'] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
  refine ⟨eq_of_eqA (rep_powA rep_rho1 3) rep_idA h1, fun e => ?_,
    eq_of_eqA (rep_compA rep_rho1 (rep_invCand rep_rho2)) rep_r2 h3, fun e => ?_⟩
  · rw [(eqA_iff rep_rho1 rep_idA).2 e] at h2
    exact Bool.noConfusion h2
  · rw [(inZ_iff rep_rho2 rep_rho1).2 e] at h4
    exact Bool.noConfusion h4

theorem rho1_pow_three :
    rho1 ^ 3 = 1 := basic_facts.1

theorem rho1_ne_one :
    rho1 ≠ 1 := basic_facts.2.1

theorem rho1_mul_rho2_inv :
    rho1 * rho2⁻¹ = C1Model.r2 := basic_facts.2.2.1

theorem rho1_inv :
    rho1⁻¹ = rho1 * rho1 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_three]
  exact rho1_pow_three

theorem tau0_conj_rho1' :
    C1Model.tau0 * rho1 * C1Model.tau0⁻¹ = rho1 * rho1 := by
  rw [C1Model.tau0_conj_rho1, rho1_inv]

end Reps

section Members

theorem membersOK_parts :
    inM rhoArr = true ∧ inM w0Arr = true ∧ inM t1A = true ∧
    inM aA = true ∧ inM bA = true ∧ inM s1Arr = true ∧ inM s2Arr = true := by
  have h := members_check
  simp only [membersOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩ := h
  exact ⟨h1, h2, h3, h4, h5, h6, h7⟩

theorem rho1_mem_suzM :
    rho1 ∈ suzM := (inM_iff rep_rho1).1 membersOK_parts.1

theorem w0_mem_suzM :
    w0 ∈ suzM := (inM_iff rep_w0).1 membersOK_parts.2.1

theorem t1_mem_suzM :
    suzInv 1 ∈ suzM := (inM_iff rep_t1).1 membersOK_parts.2.2.1

theorem c1a_mem_suzM :
    c1a ∈ suzM := (inM_iff rep_c1a).1 membersOK_parts.2.2.2.1

theorem c1b_mem_suzM :
    c1b ∈ suzM := (inM_iff rep_c1b).1 membersOK_parts.2.2.2.2.1

theorem s1_mem_suzM :
    s1 ∈ suzM := (inM_iff rep_s1).1 membersOK_parts.2.2.2.2.2.1

theorem s2_mem_suzM :
    s2 ∈ suzM := (inM_iff rep_s2).1 membersOK_parts.2.2.2.2.2.2

theorem tau0_mem_suzM :
    C1Model.tau0 ∈ suzM := C1Model.invE_le_suzM C1Model.tau0_mem_invE

theorem comm_facts :
    suzInv 1 * rho1 = rho1 * suzInv 1 ∧ c1a * rho1 = rho1 * c1a ∧
    c1a * suzInv 1 = suzInv 1 * c1a ∧ c1b * suzInv 1 = suzInv 1 * c1b ∧
    s1 * suzInv 1 = suzInv 1 * s1 ∧ s2 * suzInv 1 = suzInv 1 * s2 := by
  have h := comm_check
  simp only [commOK, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩ := h
  exact ⟨(commA_iff rep_t1 rep_rho1).1 h1, (commA_iff rep_c1a rep_rho1).1 h2,
    (commA_iff rep_c1a rep_t1).1 h3, (commA_iff rep_c1b rep_t1).1 h4,
    (commA_iff rep_s1 rep_t1).1 h5, (commA_iff rep_s2 rep_t1).1 h6⟩

end Members

section R0

theorem inR0_iff
    {x : Array ℕ} {X : Equiv.Perm (Fin 1782)} (hx : Rep 1782 x X) :
    inR0 x = true ↔ X = w0 ∨ X = C1Model.r1 ∨ X = C1Model.r2 := by
  rw [inR0, Bool.or_eq_true, Bool.or_eq_true, eqA_iff hx rep_w0, eqA_iff hx rep_r1,
    eqA_iff hx rep_r2, or_assoc]

theorem mem_normalizer_R0_of_normR0
    {g : Array ℕ} {G : Equiv.Perm (Fin 1782)}
    (hg : Rep 1782 g G) (h : normR0 g = true) :
    G ∈ normalizer (R0 : Set (Equiv.Perm (Fin 1782))) := by
  simp only [normR0, Bool.and_eq_true] at h
  have hw : ∀ X : Equiv.Perm (Fin 1782), (X = w0 ∨ X = C1Model.r1 ∨ X = C1Model.r2) →
      X ∈ R0 := by
    rintro X (rfl | rfl | rfl)
    · exact C1Model.w0_mem_R0
    · exact C1Model.r1_mem_R0
    · exact C1Model.r2_mem_R0
  exact C1Model.mem_normalizer_R0 (hw _ ((inR0_iff (rep_conjA hg rep_w0)).1 h.1))
    (hw _ ((inR0_iff (rep_conjA hg rep_r1)).1 h.2))

theorem mem_normalizer_R0_of_mem_centralizer {g : Equiv.Perm (Fin 1782)}
    (hg : g ∈ centralizer (R0 : Set (Equiv.Perm (Fin 1782)))) :
    g ∈ normalizer (R0 : Set (Equiv.Perm (Fin 1782))) := by
  rw [mem_normalizer_iff]
  intro h
  constructor
  · intro hh
    rwa [conj_eq_of_mul_comm (mem_centralizer_iff.1 hg h hh).symm]
  · intro hh
    have e := conj_eq_of_mul_comm (mem_centralizer_iff.1 (inv_mem hg) _ hh).symm
    rw [show g⁻¹ * (g * h * g⁻¹) * g⁻¹⁻¹ = h by group] at e
    rwa [← e] at hh

theorem mem_NR0 {g : Equiv.Perm (Fin 1782)} :
    g ∈ NR0 ↔ g ∈ suzM ∧ g ∈ normalizer (R0 : Set (Equiv.Perm (Fin 1782))) := mem_inf

theorem rho1_mem_NR0 :
    rho1 ∈ NR0 :=
  mem_NR0.2 ⟨rho1_mem_suzM, (mem_inf.1 C1Model.rho1_mem_B0).2⟩

theorem w0_mem_NR0 :
    w0 ∈ NR0 := mem_NR0.2 ⟨w0_mem_suzM, le_normalizer C1Model.w0_mem_R0⟩

theorem t1_mem_NR0 :
    suzInv 1 ∈ NR0 :=
  mem_NR0.2 ⟨t1_mem_suzM, mem_normalizer_R0_of_mem_centralizer
    (C1Model.J0_le_centralizer_R0 C1Model.suzInv_one_mem_J0)⟩

theorem zJ0_mem_NR0 :
    C1Model.zJ0 ∈ NR0 :=
  mem_NR0.2 ⟨C1Model.zJ0_mem_suzM, mem_normalizer_R0_of_mem_centralizer
    (C1Model.J0_le_centralizer_R0 C1Model.zJ0_mem_J0)⟩

theorem tau0_mem_NR0 :
    C1Model.tau0 ∈ NR0 :=
  mem_NR0.2 ⟨tau0_mem_suzM, (mem_inf.1 C1Model.tau0_mem_B0).2⟩

theorem R0_le_NR0 :
    R0 ≤ NR0 := by
  rw [C1Model.R0_eq, closure_le]
  rintro x (rfl | rfl)
  · exact w0_mem_NR0
  · exact mul_mem (mul_mem rho1_mem_NR0 w0_mem_NR0) (inv_mem rho1_mem_NR0)

theorem inv_mul_mem_centralizer {c h w : Equiv.Perm (Fin 1782)}
    (e : h * w * h⁻¹ = c * w * c⁻¹) : c⁻¹ * h ∈ centralizer ({w} : Set _) := by
  rw [mem_centralizer_singleton_iff]
  calc c⁻¹ * h * w = c⁻¹ * (h * w * h⁻¹) * h := by group
    _ = c⁻¹ * (c * w * c⁻¹) * h := by rw [e]
    _ = w * (c⁻¹ * h) := by group

theorem card_NR0_le :
    Nat.card NR0 ≤ 483840 := by
  have hw0ne := C1Model.w0_ne_one
  have hcov : Nat.card NR0 ≤
      3 * Nat.card ↥(NR0 ⊓ centralizer ({w0} : Set (Equiv.Perm (Fin 1782)))) := by
    refine card_le_mul_of_cover ![1, rho1, rho1 * rho1] fun h hh => ?_
    have hc : h * w0 * h⁻¹ ∈ R0 := (mem_normalizer_iff.1 (mem_NR0.1 hh).2 w0).1 C1Model.w0_mem_R0
    rcases C1Model.mem_R0_iff.1 hc with h1 | h1 | h1 | h1
    · refine absurd ?_ hw0ne
      have := congrArg (fun x => h⁻¹ * x * h) h1
      simpa [mul_assoc] using this
    · refine ⟨0, mem_inf.2 ⟨by simpa using hh, ?_⟩⟩
      simpa using inv_mul_mem_centralizer (c := 1) (by rw [h1]; group)
    · refine ⟨1, mem_inf.2 ⟨mul_mem (inv_mem rho1_mem_NR0) hh, ?_⟩⟩
      exact inv_mul_mem_centralizer (by rw [h1]; rfl)
    · refine ⟨2, mem_inf.2 ⟨mul_mem (inv_mem (mul_mem rho1_mem_NR0 rho1_mem_NR0)) hh, ?_⟩⟩
      refine inv_mul_mem_centralizer ?_
      show h * w0 * h⁻¹ = rho1 * rho1 * w0 * (rho1 * rho1)⁻¹
      rw [h1, C1Model.r2, C1Model.r1]
      group
  have hK : Nat.card ↥(NR0 ⊓ centralizer ({w0} : Set (Equiv.Perm (Fin 1782)))) ≤ 161280 := by
    rw [← C1Model.card_centralizer_w0]
    refine card_le_of_le fun k hk => mem_inf.2 ⟨(mem_inf.1 hk).2, (mem_NR0.1 (mem_inf.1 hk).1).1⟩
  omega

theorem card_closure_nr0 :
    Nat.card (closure {suzInv 1, C1Model.zJ0, w0, rho1, C1Model.tau0}) = 483840 := by
  have h := nr0_check
  simp only [nr0OK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨hsz, hc⟩, e0⟩, e1⟩, e2⟩, e3⟩, e4⟩ := h
  have hS : ∀ j (hj : j < 9), nr0StrongArrs[j]! = nr0Strong j := fun j hj =>
    getElem!_ofFn_arr (fun i : Fin 9 => nr0Strong i.val) hj
  have := card_closure_of_chainOK (S := nr0StrongArrs) (k := 5) (by rw [hsz]; norm_num)
    (by decide) (by decide) hc ![suzInv 1, C1Model.zJ0, w0, rho1, C1Model.tau0] (fun i => ?_)
  · rw [range_five] at this
    rw [this]
    rfl
  · fin_cases i
    · show Rep 1782 nr0StrongArrs[0]! (suzInv 1)
      rw [hS 0 (by norm_num)]
      exact rep_of_eqA e0 rep_t1
    · show Rep 1782 nr0StrongArrs[1]! C1Model.zJ0
      rw [hS 1 (by norm_num)]
      exact rep_of_eqA e1 rep_zJ0
    · show Rep 1782 nr0StrongArrs[2]! w0
      rw [hS 2 (by norm_num)]
      exact rep_of_eqA e2 rep_w0
    · show Rep 1782 nr0StrongArrs[3]! rho1
      rw [hS 3 (by norm_num)]
      exact rep_of_eqA e3 rep_rho1
    · show Rep 1782 nr0StrongArrs[4]! C1Model.tau0
      rw [hS 4 (by norm_num)]
      exact rep_of_eqA e4 rep_tau0

theorem closure_nr0_le_NR0 :
    closure {suzInv 1, C1Model.zJ0, w0, rho1, C1Model.tau0} ≤ NR0 := by
  rw [closure_le]
  rintro x (rfl | rfl | rfl | rfl | rfl)
  · exact t1_mem_NR0
  · exact zJ0_mem_NR0
  · exact w0_mem_NR0
  · exact rho1_mem_NR0
  · exact tau0_mem_NR0

theorem NR0_eq_closure :
    NR0 = closure {suzInv 1, C1Model.zJ0, w0, rho1, C1Model.tau0} :=
  (eq_of_le_of_card_ge closure_nr0_le_NR0 (by rw [card_closure_nr0]; exact card_NR0_le)).symm

theorem card_NR0 :
    Nat.card NR0 = 483840 := by
  rw [NR0_eq_closure, card_closure_nr0]

end R0

section Rho

theorem orderOf_rho1 :
    orderOf rho1 = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime rho1_pow_three rho1_ne_one

theorem rho1_mul_rho1_sq :
    rho1 * rho1 * (rho1 * rho1) = rho1 := by
  calc rho1 * rho1 * (rho1 * rho1) = rho1 ^ 3 * rho1 := by rw [pow_three]; simp only [mul_assoc]
    _ = rho1 := by rw [rho1_pow_three, one_mul]

theorem rho2_pow_three :
    rho2 ^ 3 = 1 := by
  rw [rho2, conj_pow, rho1_pow_three, mul_one, mul_inv_cancel]

theorem rho2_ne_one :
    rho2 ≠ 1 := fun h => rho1_ne_one (by
  rw [rho2, mul_inv_eq_one, mul_eq_left] at h
  exact h)

theorem rho2_inv :
    rho2⁻¹ = rho2 * rho2 := by
  rw [inv_eq_iff_mul_eq_one, ← pow_three]
  exact rho2_pow_three

theorem zpowers_mul_self {x : Equiv.Perm (Fin 1782)} (hx : x ^ 3 = 1) :
    zpowers (x * x) = zpowers x := by
  apply le_antisymm
  · rw [zpowers_le]
    exact mul_mem (mem_zpowers x) (mem_zpowers x)
  · rw [zpowers_le]
    have h4 : x * x * (x * x) = x := by
      calc x * x * (x * x) = x ^ 3 * x := by rw [pow_three]; simp only [mul_assoc]
        _ = x := by rw [hx, one_mul]
    have hmem : x * x * (x * x) ∈ zpowers (x * x) := mul_mem (mem_zpowers _) (mem_zpowers _)
    rwa [h4] at hmem

theorem conjMap_zpowers_eq_of {g x y : Equiv.Perm (Fin 1782)} (hy : y ^ 3 = 1)
    (h : g * x * g⁻¹ = y ∨ g * x * g⁻¹ = y * y) : conjMap g (zpowers x) = zpowers y := by
  rw [conjMap_zpowers]
  rcases h with h | h
  · rw [h]
  · rw [h, zpowers_mul_self hy]

theorem conj_eq_of_conjMap_eq {g x y : Equiv.Perm (Fin 1782)} (hx : x ≠ 1) (hy : orderOf y = 3)
    (h : conjMap g (zpowers x) = zpowers y) : g * x * g⁻¹ = y ∨ g * x * g⁻¹ = y * y := by
  rw [conjMap_zpowers] at h
  have hmem : g * x * g⁻¹ ∈ zpowers y := h ▸ mem_zpowers _
  rcases (mem_zpowers_of_orderOf_eq_three hy).1 hmem with h1 | h1 | h1
  · exact absurd (by rw [mul_inv_eq_one, mul_eq_left] at h1; exact h1) hx
  · exact Or.inl h1
  · exact Or.inr h1

theorem mem_Nrho1_iff {g : Equiv.Perm (Fin 1782)} :
    g ∈ Nrho1 ↔ conjMap g (zpowers rho1) = zpowers rho1 ∧ g ∈ suzM := by
  rw [Nrho1, mem_inf, mem_normalizer_iff_map_conj_eq]
  rfl

theorem conj_rho1_of_mem_Nrho1
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ Nrho1) :
    g * rho1 * g⁻¹ = rho1 ∨ g * rho1 * g⁻¹ = rho1 * rho1 :=
  conj_eq_of_conjMap_eq rho1_ne_one orderOf_rho1 (mem_Nrho1_iff.1 hg).1

theorem mem_Crho1_iff {g : Equiv.Perm (Fin 1782)} :
    g ∈ Crho1 ↔ g * rho1 = rho1 * g ∧ g ∈ suzM := by
  rw [Crho1, mem_inf, mem_centralizer_singleton_iff]

theorem Crho1_le_Nrho1 :
    Crho1 ≤ Nrho1 := fun g hg => by
  obtain ⟨h1, h2⟩ := mem_Crho1_iff.1 hg
  exact mem_Nrho1_iff.2 ⟨conjMap_zpowers_eq_of rho1_pow_three (Or.inl (conj_eq_of_mul_comm h1)),
    h2⟩

theorem tau0_mem_Nrho1 :
    C1Model.tau0 ∈ Nrho1 :=
  mem_Nrho1_iff.2 ⟨conjMap_zpowers_eq_of rho1_pow_three (Or.inr tau0_conj_rho1'),
    tau0_mem_suzM⟩

theorem tau0_not_mem_Crho1 :
    C1Model.tau0 ∉ Crho1 := fun h => by
  have e := conj_eq_of_mul_comm (mem_Crho1_iff.1 h).1
  rw [tau0_conj_rho1'] at e
  exact rho1_ne_one (by
    have := congrArg (fun z => rho1⁻¹ * z) e
    simpa using this)

theorem mul_tau0_mem_Crho1
    {g : Equiv.Perm (Fin 1782)} (hgM : g ∈ suzM)
    (h : g * rho1 * g⁻¹ = rho1 * rho1) : g * C1Model.tau0 ∈ Crho1 := by
  refine mem_Crho1_iff.2 ⟨mul_comm_of_conj_eq ?_, mul_mem hgM tau0_mem_suzM⟩
  calc g * C1Model.tau0 * rho1 * (g * C1Model.tau0)⁻¹ =
      g * (C1Model.tau0 * rho1 * C1Model.tau0⁻¹) * g⁻¹ := by group
    _ = (g * rho1 * g⁻¹) * (g * rho1 * g⁻¹) := by rw [tau0_conj_rho1']; group
    _ = rho1 := by rw [h, rho1_mul_rho1_sq]

theorem tau0_mul_mem_Crho1
    {g : Equiv.Perm (Fin 1782)} (hgM : g ∈ suzM)
    (h : g * rho1 * g⁻¹ = rho1 * rho1) : C1Model.tau0 * g ∈ Crho1 := by
  refine mem_Crho1_iff.2 ⟨mul_comm_of_conj_eq ?_, mul_mem tau0_mem_suzM hgM⟩
  calc C1Model.tau0 * g * rho1 * (C1Model.tau0 * g)⁻¹ =
      C1Model.tau0 * (g * rho1 * g⁻¹) * C1Model.tau0⁻¹ := by group
    _ = (C1Model.tau0 * rho1 * C1Model.tau0⁻¹) * (C1Model.tau0 * rho1 * C1Model.tau0⁻¹) := by
      rw [h]; group
    _ = rho1 := by rw [tau0_conj_rho1', rho1_mul_rho1_sq]

theorem Nrho1_eq_sup :
    Nrho1 = Crho1 ⊔ zpowers C1Model.tau0 := by
  apply le_antisymm
  · intro g hg
    rcases conj_rho1_of_mem_Nrho1 hg with h | h
    · exact mem_sup_left (mem_Crho1_iff.2 ⟨mul_comm_of_conj_eq h, (mem_Nrho1_iff.1 hg).2⟩)
    · have hgt := mul_tau0_mem_Crho1 (mem_Nrho1_iff.1 hg).2 h
      have : g = g * C1Model.tau0 * C1Model.tau0⁻¹ := by group
      rw [this]
      exact mul_mem (mem_sup_left hgt) (inv_mem (mem_sup_right (mem_zpowers _)))
  · exact sup_le Crho1_le_Nrho1 ((zpowers_le).2 tau0_mem_Nrho1)

theorem card_Nrho1_eq_two_mul :
    Nat.card Nrho1 = 2 * Nat.card Crho1 := by
  refine card_eq_two_mul Crho1_le_Nrho1 tau0_mem_Nrho1 fun b hb => ?_
  constructor
  · intro hbC hτb
    apply tau0_not_mem_Crho1
    have : C1Model.tau0 = C1Model.tau0 * b * b⁻¹ := by group
    rw [this]
    exact mul_mem hτb (inv_mem hbC)
  · intro hτb
    rcases conj_rho1_of_mem_Nrho1 hb with h | h
    · exact mem_Crho1_iff.2 ⟨mul_comm_of_conj_eq h, (mem_Nrho1_iff.1 hb).2⟩
    · exact absurd (tau0_mul_mem_Crho1 (mem_Nrho1_iff.1 hb).2 h) hτb

end Rho

@[expose] def r0Elt (r : ℕ) : Equiv.Perm (Fin 1782) :=
  if r = 0 then 1 else if r = 1 then w0 else if r = 2 then C1Model.r1 else C1Model.r2

@[expose] def a4Elt (i : ℕ) : Equiv.Perm (Fin 1782) := r0Elt (i / 3) * rho1 ^ (i % 3)

@[expose] def e8Elt (i : ℕ) : Equiv.Perm (Fin 1782) := r0Elt (i / 2) * C1Model.tau0 ^ (i % 2)

section A4

theorem rep_r0Elt
    (r : ℕ) : Rep 1782 (r0A r) (r0Elt r) := by
  unfold r0A r0Elt
  split_ifs
  · exact rep_idA
  · exact rep_w0
  · exact rep_r1
  · exact rep_r2

theorem rep_a4Elt
    (i : ℕ) : Rep 1782 (a4A i) (a4Elt i) :=
  rep_compA (rep_r0Elt _) (rep_powA rep_rho1 _)

theorem rep_e8Elt
    (i : ℕ) : Rep 1782 (e8A i) (e8Elt i) :=
  rep_compA (rep_r0Elt _) (rep_powA rep_tau0 _)

theorem r0Elt_mem_R0
    (r : ℕ) : r0Elt r ∈ R0 := by
  unfold r0Elt
  split_ifs
  · exact one_mem _
  · exact C1Model.w0_mem_R0
  · exact C1Model.r1_mem_R0
  · exact C1Model.r2_mem_R0

theorem a4_facts :
    (∀ i < 12, ∃ j < 12, rho1 * a4Elt i = a4Elt j) ∧
    (∀ i < 12, ∃ j < 12, rho2 * a4Elt i = a4Elt j) ∧
    (∀ i < 12, a4Elt i * a4Elt i = 1 → i % 3 = 0) ∧
    (∀ i < 12, ∀ j < 12, i ≠ j →
      ¬ ((a4Elt j * rho1 * (a4Elt j)⁻¹ = a4Elt i * rho1 * (a4Elt i)⁻¹ ∨
          a4Elt j * rho1 * (a4Elt j)⁻¹ =
            a4Elt i * rho1 * (a4Elt i)⁻¹ * (a4Elt i * rho1 * (a4Elt i)⁻¹)) ∧
        (a4Elt j * rho2 * (a4Elt j)⁻¹ = a4Elt i * rho2 * (a4Elt i)⁻¹ ∨
          a4Elt j * rho2 * (a4Elt j)⁻¹ =
            a4Elt i * rho2 * (a4Elt i)⁻¹ * (a4Elt i * rho2 * (a4Elt i)⁻¹)))) := by
  have h := a4_check
  simp only [a4OK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hP : ∀ i < 12, _ := fun i hi => by
    have := allLt_spec h1 hi
    simp only [Bool.and_eq_true, decide_eq_true_eq, Bool.or_eq_true, beq_iff_eq,
      Bool.not_eq_true'] at this
    exact this
  refine ⟨fun i hi => ?_, fun i hi => ?_, fun i hi hsq => ?_, fun i hi j hj hij => ?_⟩
  · obtain ⟨⟨⟨⟨⟨-, hlt⟩, he⟩, -⟩, -⟩, -⟩ := hP i hi
    exact ⟨_, hlt, eq_of_eqA (rep_compA rep_rho1 (rep_a4Elt i)) (rep_a4Elt _) he⟩
  · obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, hlt⟩, he⟩, -⟩ := hP i hi
    exact ⟨_, hlt, eq_of_eqA (rep_compA rep_rho2 (rep_a4Elt i)) (rep_a4Elt _) he⟩
  · obtain ⟨⟨⟨⟨⟨-, -⟩, -⟩, -⟩, -⟩, h3 | h3⟩ := hP i hi
    · exact h3
    · rw [(eqA_iff (rep_compA (rep_a4Elt i) (rep_a4Elt i)) rep_idA).2 hsq] at h3
      exact Bool.noConfusion h3
  · have := allLt_spec (allLt_spec h2 hi) hj
    simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
    rintro ⟨hA, hB⟩
    rcases this with (h3 | h3) | h3
    · exact hij h3
    · rw [(inZ_iff (rep_conjA (rep_a4Elt i) rep_rho1) (rep_conjA (rep_a4Elt j) rep_rho1)).2 hA]
        at h3
      exact Bool.noConfusion h3
    · rw [(inZ_iff (rep_conjA (rep_a4Elt i) rep_rho2) (rep_conjA (rep_a4Elt j) rep_rho2)).2 hB]
        at h3
      exact Bool.noConfusion h3

theorem exists_eq_a4Elt
    {x : Equiv.Perm (Fin 1782)} (hx : x ∈ closure {rho1, rho2}) :
    ∃ i < 12, x = a4Elt i := by
  obtain ⟨hL1, hL2, -, -⟩ := a4_facts
  induction hx using closure_induction_left with
  | one => exact ⟨0, by norm_num, by simp [a4Elt, r0Elt]⟩
  | mul_left x hx y _ ih =>
    obtain ⟨i, hi, rfl⟩ := ih
    rcases hx with rfl | rfl
    · obtain ⟨j, hj, e⟩ := hL1 i hi
      exact ⟨j, hj, e⟩
    · obtain ⟨j, hj, e⟩ := hL2 i hi
      exact ⟨j, hj, e⟩
  | inv_mul_cancel x hx y _ ih =>
    obtain ⟨i, hi, rfl⟩ := ih
    rcases hx with rfl | rfl
    · obtain ⟨j, hj, e⟩ := hL1 i hi
      obtain ⟨k, hk, e'⟩ := hL1 j hj
      exact ⟨k, hk, by rw [rho1_inv, mul_assoc, e, e']⟩
    · obtain ⟨j, hj, e⟩ := hL2 i hi
      obtain ⟨k, hk, e'⟩ := hL2 j hj
      exact ⟨k, hk, by rw [rho2_inv, mul_assoc, e, e']⟩

theorem mem_R0_of_mem_A4
    {x : Equiv.Perm (Fin 1782)} (hx : x ∈ closure {rho1, rho2})
    (hxx : x * x = 1) : x ∈ R0 := by
  obtain ⟨i, hi, rfl⟩ := exists_eq_a4Elt hx
  have h3 := a4_facts.2.2.1 i hi hxx
  rw [a4Elt, h3, pow_zero, mul_one]
  exact r0Elt_mem_R0 _

theorem rho1_mem_A4 : rho1 ∈ closure {rho1, rho2} := subset_closure (Set.mem_insert _ _)

theorem rho2_mem_A4 : rho2 ∈ closure {rho1, rho2} := subset_closure (Set.mem_insert_of_mem _ rfl)

theorem R0_le_A4 :
    R0 ≤ closure {rho1, rho2} := by
  have h2 : C1Model.r2 ∈ closure {rho1, rho2} := by
    rw [← rho1_mul_rho2_inv]
    exact mul_mem rho1_mem_A4 (inv_mem rho2_mem_A4)
  have h0 : w0 ∈ closure {rho1, rho2} := by
    rw [← C1Model.rho1_conj_r2]
    exact mul_mem (mul_mem rho1_mem_A4 h2) (inv_mem rho1_mem_A4)
  rw [C1Model.R0_eq, closure_le]
  rintro x (rfl | rfl)
  · exact h0
  · exact mul_mem (mul_mem rho1_mem_A4 h0) (inv_mem rho1_mem_A4)

end A4

section Stab

theorem mem_NR0_of_conj_mem_A4
    {H : Subgroup (Equiv.Perm (Fin 1782))}
    (hH : ∀ c ∈ H, c * rho1 * c⁻¹ ∈ closure {rho1, rho2} ∧ c * rho2 * c⁻¹ ∈ closure {rho1, rho2})
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ H) (hgM : g ∈ suzM) : g ∈ NR0 := by
  refine mem_NR0.2 ⟨hgM, ?_⟩
  have key : ∀ c ∈ H, ∀ x ∈ R0, c * x * c⁻¹ ∈ R0 := by
    intro c hc x hx
    refine mem_R0_of_mem_A4 (conj_mem_closure (by
      rintro y (rfl | rfl)
      exacts [(hH c hc).1, (hH c hc).2]) (R0_le_A4 hx)) ?_
    calc c * x * c⁻¹ * (c * x * c⁻¹) = c * (x * x) * c⁻¹ := by group
      _ = 1 := by rw [C1Model.mul_self_of_mem_R0 hx, mul_one, mul_inv_cancel]
  rw [mem_normalizer_iff]
  intro x
  refine ⟨key g hg x, fun hx => ?_⟩
  have := key g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

theorem conjMap_mem_of_mem_conjSetStab {𝒮 : Set (Subgroup (Equiv.Perm (Fin 1782)))}
    {g : Equiv.Perm (Fin 1782)} (hg : g ∈ conjSetStab 𝒮) {P : Subgroup (Equiv.Perm (Fin 1782))}
    (hP : P ∈ 𝒮) : conjMap g P ∈ 𝒮 := by
  rw [mem_conjSetStab] at hg
  rw [← hg]
  exact Set.mem_image_of_mem _ hP

theorem conjSetStab_inf_le_NR0
    {𝒮 : Set (Subgroup (Equiv.Perm (Fin 1782)))}
    (h1 : zpowers rho1 ∈ 𝒮) (h2 : zpowers rho2 ∈ 𝒮) (hA : ∀ P ∈ 𝒮, P ≤ closure {rho1, rho2}) :
    conjSetStab 𝒮 ⊓ suzM ≤ NR0 := by
  intro g hg
  have hc : ∀ c ∈ conjSetStab 𝒮, ∀ x, zpowers x ∈ 𝒮 → c * x * c⁻¹ ∈ closure {rho1, rho2} := by
    intro c hc x hx
    have hmem : c * x * c⁻¹ ∈ conjMap c (zpowers x) := by
      rw [conjMap_zpowers]
      exact mem_zpowers _
    exact hA _ (conjMap_mem_of_mem_conjSetStab hc hx) hmem
  exact mem_NR0_of_conj_mem_A4 (H := conjSetStab 𝒮) (fun c hc' => ⟨hc c hc' rho1 h1,
    hc c hc' rho2 h2⟩) (mem_inf.1 hg).1 (mem_inf.1 hg).2

theorem pairStab_le_NR0 :
    pairStab ≤ NR0 :=
  conjSetStab_inf_le_NR0 (Set.mem_insert _ _) (Set.mem_insert_of_mem _ rfl) (by
    rintro P (rfl | rfl)
    exacts [zpowers_le.2 rho1_mem_A4, zpowers_le.2 rho2_mem_A4])

theorem triStab_le_NR0
    {u : Equiv.Perm (Fin 1782)} (hu : u ∈ closure {rho1, rho2}) :
    triStab u ≤ NR0 :=
  conjSetStab_inf_le_NR0 (Set.mem_insert _ _) (Set.mem_insert_of_mem _ (Set.mem_insert _ _)) (by
    rintro P (rfl | rfl | rfl)
    exacts [zpowers_le.2 rho1_mem_A4, zpowers_le.2 rho2_mem_A4, zpowers_le.2 hu])

theorem triStab_rho2_mul_rho1_le_NR0 :
    triStab (rho2 * rho1) ≤ NR0 :=
  triStab_le_NR0 (mul_mem rho2_mem_A4 rho1_mem_A4)

theorem mem_pairStab_iff {g : Equiv.Perm (Fin 1782)} :
    g ∈ pairStab ↔ g ∈ suzM ∧
      ((conjMap g (zpowers rho1) = zpowers rho1 ∧ conjMap g (zpowers rho2) = zpowers rho2) ∨
        (conjMap g (zpowers rho1) = zpowers rho2 ∧ conjMap g (zpowers rho2) = zpowers rho1)) := by
  rw [pairStab, mem_inf, mem_conjSetStab, Set.image_pair, Set.pair_eq_pair_iff, and_comm]

theorem mem_pairStab_of_pairA
    {g : Array ℕ} {G : Equiv.Perm (Fin 1782)} (hg : Rep 1782 g G)
    (hGM : G ∈ suzM) (h : pairA g = true) : G ∈ pairStab := by
  simp only [pairA, Bool.or_eq_true, Bool.and_eq_true] at h
  refine mem_pairStab_iff.2 ⟨hGM, ?_⟩
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact Or.inl ⟨conjMap_zpowers_eq_of rho1_pow_three
      ((inZ_iff rep_rho1 (rep_conjA hg rep_rho1)).1 h1),
      conjMap_zpowers_eq_of rho2_pow_three ((inZ_iff rep_rho2 (rep_conjA hg rep_rho2)).1 h2)⟩
  · exact Or.inr ⟨conjMap_zpowers_eq_of rho2_pow_three
      ((inZ_iff rep_rho2 (rep_conjA hg rep_rho1)).1 h1),
      conjMap_zpowers_eq_of rho1_pow_three ((inZ_iff rep_rho1 (rep_conjA hg rep_rho2)).1 h2)⟩

theorem pair_facts :
    C1Model.tau0 ∈ pairStab ∧ c1b ∈ pairStab ∧ s2 ∈ pairStab := by
  have h := pair_check
  simp only [pairOK, Bool.and_eq_true] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  exact ⟨mem_pairStab_of_pairA rep_tau0 tau0_mem_suzM h1,
    mem_pairStab_of_pairA rep_c1b c1b_mem_suzM h2, mem_pairStab_of_pairA rep_s2 s2_mem_suzM h3⟩

theorem e8Elt_mem_NR0
    (i : ℕ) : e8Elt i ∈ NR0 :=
  mul_mem (R0_le_NR0 (r0Elt_mem_R0 _)) (pow_mem tau0_mem_NR0 _)

theorem cos8_facts :
    ∀ i < 8, ∀ j < 8, i ≠ j →
    e8Elt i * rho1 * (e8Elt i)⁻¹ ≠ e8Elt j * rho1 * (e8Elt j)⁻¹ := by
  have h := cos8_check
  simp only [cos8OK, Bool.and_eq_true] at h
  intro i hi j hj hij e
  have := allLt_spec (allLt_spec h.2 hi) hj
  simp only [Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true'] at this
  rcases this with h3 | h3
  · exact hij h3
  · rw [(eqA_iff (rep_conjA (rep_e8Elt i) rep_rho1) (rep_conjA (rep_e8Elt j) rep_rho1)).2 e] at h3
    exact Bool.noConfusion h3

theorem card_Crho1_inf_NR0_le :
    Nat.card ↥(Crho1 ⊓ NR0) ≤ 60480 := by
  have h8 := mul_card_le_of_inv_mul_mem (K := Crho1 ⊓ NR0) inf_le_right
    (fun i : Fin 8 => e8Elt i) (fun i => e8Elt_mem_NR0 i) (fun i j hij => ?_)
  · rw [card_NR0] at h8
    omega
  · by_contra hne
    apply cos8_facts i i.2 j j.2 (fun e => hne (Fin.ext e))
    have hc := conj_eq_of_mul_comm (mem_Crho1_iff.1 (mem_inf.1 hij).1).1
    calc e8Elt i * rho1 * (e8Elt i)⁻¹ =
        e8Elt i * ((e8Elt i)⁻¹ * e8Elt j * rho1 * ((e8Elt i)⁻¹ * e8Elt j)⁻¹) * (e8Elt i)⁻¹ := by
          rw [hc]
      _ = e8Elt j * rho1 * (e8Elt j)⁻¹ := by group

end Stab

section J0

theorem J0_le_Crho1 :
    C1Model.J0 ≤ Crho1 := fun _ hg =>
  mem_Crho1_iff.2 ⟨mem_centralizer_singleton_iff.1 (C1Model.J0_le_centralizer_rho1 hg),
    C1Model.J0_le_suzM hg⟩

theorem card_closure_j0rho :
    Nat.card (closure {suzInv 1, C1Model.zJ0, rho1}) = 60480 := by
  have h := j0rho_check
  simp only [j0rhoOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨hsz, hc⟩, e0⟩, e1⟩, e2⟩ := h
  have hS : ∀ j (hj : j < 7), j0rhoStrongArrs[j]! = j0rhoStrong j := fun j hj =>
    getElem!_ofFn_arr (fun i : Fin 7 => j0rhoStrong i.val) hj
  have := card_closure_of_chainOK (S := j0rhoStrongArrs) (k := 3) (by rw [hsz]; norm_num)
    (by decide) (by decide) hc ![suzInv 1, C1Model.zJ0, rho1] (fun i => ?_)
  · rw [range_three] at this
    rw [this]
    rfl
  · fin_cases i
    · show Rep 1782 j0rhoStrongArrs[0]! (suzInv 1)
      rw [hS 0 (by norm_num)]
      exact rep_of_eqA e0 rep_t1
    · show Rep 1782 j0rhoStrongArrs[1]! C1Model.zJ0
      rw [hS 1 (by norm_num)]
      exact rep_of_eqA e1 rep_zJ0
    · show Rep 1782 j0rhoStrongArrs[2]! rho1
      rw [hS 2 (by norm_num)]
      exact rep_of_eqA e2 rep_rho1

theorem J0_sup_rho1_eq_closure :
    C1Model.J0 ⊔ zpowers rho1 = closure {suzInv 1, C1Model.zJ0, rho1} := by
  rw [C1Model.J0_eq, zpowers_eq_closure, ← Subgroup.closure_union, Set.insert_union,
    Set.singleton_union]

theorem Crho1_inf_NR0 :
    Crho1 ⊓ NR0 = C1Model.J0 ⊔ zpowers rho1 := by
  rw [J0_sup_rho1_eq_closure]
  refine (eq_of_le_of_card_ge ?_ ?_).symm
  · rw [closure_le]
    rintro x (rfl | rfl | rfl)
    · exact mem_inf.2 ⟨mem_Crho1_iff.2 ⟨comm_facts.1, t1_mem_suzM⟩, t1_mem_NR0⟩
    · exact mem_inf.2 ⟨J0_le_Crho1 C1Model.zJ0_mem_J0, zJ0_mem_NR0⟩
    · exact mem_inf.2 ⟨mem_Crho1_iff.2 ⟨rfl, rho1_mem_suzM⟩, rho1_mem_NR0⟩
  · rw [card_closure_j0rho]
    exact card_Crho1_inf_NR0_le

theorem card_Crho1_inf_NR0 :
    Nat.card ↥(Crho1 ⊓ NR0) = 60480 := by
  rw [Crho1_inf_NR0, J0_sup_rho1_eq_closure, card_closure_j0rho]

end J0

section C1

theorem mem_invE_one_iff
    {g : Equiv.Perm (Fin 1782)} :
    g ∈ invE 1 ↔ g * suzInv 1 = suzInv 1 * g ∧ g ∈ suzM := by
  rw [invE_eq_centM (by norm_num : 1 < 4), centM, mem_inf, mem_centralizer_singleton_iff]

theorem s1_mem_invE :
    s1 ∈ invE 1 := mem_invE_one_iff.2 ⟨comm_facts.2.2.2.2.1, s1_mem_suzM⟩

theorem s2_mem_invE :
    s2 ∈ invE 1 := mem_invE_one_iff.2 ⟨comm_facts.2.2.2.2.2, s2_mem_suzM⟩

theorem card_closure_c1 :
    Nat.card (closure {c1a, c1b}) = 3317760 := by
  have h := c1_check
  simp only [c1OK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨hsz, hc⟩ := h
  have hS : ∀ j (hj : j < 11), c1StrongArrs[j]! = c1Strong j := fun j hj =>
    getElem!_ofFn_arr (fun i : Fin 11 => c1Strong i.val) hj
  have := card_closure_of_chainOK (S := c1StrongArrs) (k := 2) (by rw [hsz]; norm_num)
    (by decide) (by decide) hc ![c1a, c1b] (fun i => ?_)
  · rw [range_two] at this
    rw [this]
    rfl
  · fin_cases i
    · show Rep 1782 c1StrongArrs[0]! c1a
      rw [hS 0 (by norm_num)]
      exact rep_c1a
    · show Rep 1782 c1StrongArrs[1]! c1b
      rw [hS 1 (by norm_num)]
      exact rep_c1b

theorem invE_eq_sup :
    invE 1 = (invE 1 ⊓ Crho1) ⊔ (invE 1 ⊓ pairStab) := by
  have hle : closure {c1a, c1b} ≤ (invE 1 ⊓ Crho1) ⊔ (invE 1 ⊓ pairStab) := by
    rw [closure_le]
    rintro x (rfl | rfl)
    · exact mem_sup_left (mem_inf.2 ⟨mem_invE_one_iff.2 ⟨comm_facts.2.2.1, c1a_mem_suzM⟩,
        mem_Crho1_iff.2 ⟨comm_facts.2.1, c1a_mem_suzM⟩⟩)
    · exact mem_sup_right (mem_inf.2 ⟨mem_invE_one_iff.2 ⟨comm_facts.2.2.2.1, c1b_mem_suzM⟩,
        pair_facts.2.1⟩)
  have hsup : (invE 1 ⊓ Crho1) ⊔ (invE 1 ⊓ pairStab) ≤ invE 1 := sup_le inf_le_left inf_le_left
  have heq : closure {c1a, c1b} = invE 1 := eq_of_le_of_card_ge (hle.trans hsup) (by
    rw [card_closure_c1, card_invE (by norm_num : 1 < 4)]
    rfl)
  exact le_antisymm (heq ▸ hle) hsup

theorem card_closure_csplit :
    Nat.card (closure {suzInv 1, C1Model.zJ0, rho1, c1a}) = 9797760 := by
  have h := csplit_check
  simp only [csplitOK, Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨hsz, hc⟩, e0⟩, e1⟩, e2⟩, e3⟩ := h
  have hS : ∀ j (hj : j < 9), csplitStrongArrs[j]! = csplitStrong j := fun j hj =>
    getElem!_ofFn_arr (fun i : Fin 9 => csplitStrong i.val) hj
  have := card_closure_of_chainOK (S := csplitStrongArrs) (k := 4) (by rw [hsz]; norm_num)
    (by decide) (by decide) hc ![suzInv 1, C1Model.zJ0, rho1, c1a] (fun i => ?_)
  · rw [range_four] at this
    rw [this]
    rfl
  · fin_cases i
    · show Rep 1782 csplitStrongArrs[0]! (suzInv 1)
      rw [hS 0 (by norm_num)]
      exact rep_of_eqA e0 rep_t1
    · show Rep 1782 csplitStrongArrs[1]! C1Model.zJ0
      rw [hS 1 (by norm_num)]
      exact rep_of_eqA e1 rep_zJ0
    · show Rep 1782 csplitStrongArrs[2]! rho1
      rw [hS 2 (by norm_num)]
      exact rep_of_eqA e2 rep_rho1
    · show Rep 1782 csplitStrongArrs[3]! c1a
      rw [hS 3 (by norm_num)]
      exact rep_of_eqA e3 rep_c1a

theorem Crho1_eq_sup_of_card_le
    (hC : Nat.card Crho1 ≤ 9797760) :
    Crho1 = (Crho1 ⊓ invE 1) ⊔ (Crho1 ⊓ NR0) := by
  have hle : closure {suzInv 1, C1Model.zJ0, rho1, c1a} ≤ (Crho1 ⊓ invE 1) ⊔ (Crho1 ⊓ NR0) := by
    rw [closure_le]
    rintro x (rfl | rfl | rfl | rfl)
    · exact mem_sup_left (mem_inf.2 ⟨mem_Crho1_iff.2 ⟨comm_facts.1, t1_mem_suzM⟩,
        mem_invE_one_iff.2 ⟨rfl, t1_mem_suzM⟩⟩)
    · exact mem_sup_right (mem_inf.2 ⟨J0_le_Crho1 C1Model.zJ0_mem_J0, zJ0_mem_NR0⟩)
    · exact mem_sup_right (mem_inf.2 ⟨mem_Crho1_iff.2 ⟨rfl, rho1_mem_suzM⟩, rho1_mem_NR0⟩)
    · exact mem_sup_left (mem_inf.2 ⟨mem_Crho1_iff.2 ⟨comm_facts.2.1, c1a_mem_suzM⟩,
        mem_invE_one_iff.2 ⟨comm_facts.2.2.1, c1a_mem_suzM⟩⟩)
  have hsup : (Crho1 ⊓ invE 1) ⊔ (Crho1 ⊓ NR0) ≤ Crho1 := sup_le inf_le_left inf_le_left
  have heq : closure {suzInv 1, C1Model.zJ0, rho1, c1a} = Crho1 :=
    eq_of_le_of_card_ge (hle.trans hsup) (by rw [card_closure_csplit]; exact hC)
  exact le_antisymm (heq ▸ hle) hsup

end C1

section Crho1

theorem card_Crho1 :
    Nat.card Crho1 = 9797760 := by
  rw [← LevelTwo.xGroup_eq_Crho1, LevelTwo.card_xGroup]

theorem Crho1_eq_sup :
    Crho1 = (Crho1 ⊓ invE 1) ⊔ (Crho1 ⊓ NR0) :=
  Crho1_eq_sup_of_card_le card_Crho1.le

theorem card_Nrho1 :
    Nat.card Nrho1 = 19595520 := by
  rw [card_Nrho1_eq_two_mul, card_Crho1]

end Crho1

end CFSG.Sporadic.SuzRecog.ModelGroups
